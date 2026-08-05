use std::collections::HashSet;

use r2ssa::SSAVar;

use super::*;

#[derive(Debug, Clone, PartialEq)]
struct CertifiedLinearAddress {
    base: CExpr,
    index: Option<CertifiedLinearIndex>,
    offset: i64,
}

#[derive(Debug, Clone, PartialEq)]
struct CertifiedLinearIndex {
    expr: CExpr,
    stride: i64,
}

impl<'a> FoldingContext<'a> {
    fn certified_pointer_parameter_expr(&self, expr: &CExpr) -> bool {
        let expr = match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => inner.as_ref(),
            _ => expr,
        };
        let CExpr::Var(name) = expr else {
            return false;
        };
        self.inputs
            .function_facts
            .type_facts()
            .render_authorized_signature()
            .is_some_and(|signature| {
                signature.params.iter().any(|param| {
                    param.name.eq_ignore_ascii_case(name)
                        && param.ty.as_ref().is_some_and(|ty| {
                            matches!(
                                crate::type_like_to_ctype(ty),
                                CType::Pointer(_) | CType::Array(_, _)
                            )
                        })
                })
            })
    }

    fn certified_expr_contains_pointer_parameter(&self, expr: &CExpr) -> bool {
        let mut contains = false;
        expr.visit(&mut |node| {
            if !contains && self.certified_pointer_parameter_expr(node) {
                contains = true;
            }
        });
        contains
    }

    fn collect_certified_address_terms(
        &self,
        expr: &CExpr,
        sign: i64,
        constant: &mut i64,
        terms: &mut Vec<(i64, CExpr)>,
    ) -> Option<()> {
        match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.collect_certified_address_terms(inner, sign, constant, terms)
            }
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                self.collect_certified_address_terms(left, sign, constant, terms)?;
                self.collect_certified_address_terms(right, sign, constant, terms)
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                self.collect_certified_address_terms(left, sign, constant, terms)?;
                self.collect_certified_address_terms(right, sign.checked_neg()?, constant, terms)
            }
            _ => {
                if let Some(value) = self.literal_to_i64(expr) {
                    *constant = constant.checked_add(value.checked_mul(sign)?)?;
                } else {
                    terms.push((sign, expr.clone()));
                }
                Some(())
            }
        }
    }

    fn certified_index_atom_and_coefficient(&self, expr: &CExpr) -> Option<(CExpr, i64)> {
        match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.certified_index_atom_and_coefficient(inner)
            }
            CExpr::Unary {
                op: UnaryOp::Neg,
                operand,
            } => {
                let (atom, coefficient) = self.certified_index_atom_and_coefficient(operand)?;
                Some((atom, coefficient.checked_neg()?))
            }
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if let Some(multiplier) = self.literal_to_i64(left) {
                    let (atom, coefficient) = self.certified_index_atom_and_coefficient(right)?;
                    return Some((atom, coefficient.checked_mul(multiplier)?));
                }
                let multiplier = self.literal_to_i64(right)?;
                let (atom, coefficient) = self.certified_index_atom_and_coefficient(left)?;
                Some((atom, coefficient.checked_mul(multiplier)?))
            }
            CExpr::Binary {
                op: BinaryOp::Shl,
                left,
                right,
            } => {
                let shift = self.literal_to_i64(right)?;
                if !(0..=62).contains(&shift) {
                    return None;
                }
                let (atom, coefficient) = self.certified_index_atom_and_coefficient(left)?;
                Some((
                    atom,
                    coefficient.checked_mul(1_i64.checked_shl(shift as u32)?)?,
                ))
            }
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => {
                let (left_atom, left_coefficient) =
                    self.certified_index_atom_and_coefficient(left)?;
                let (right_atom, right_coefficient) =
                    self.certified_index_atom_and_coefficient(right)?;
                if left_atom != right_atom {
                    return None;
                }
                let coefficient = if matches!(
                    expr,
                    CExpr::Binary {
                        op: BinaryOp::Add,
                        ..
                    }
                ) {
                    left_coefficient.checked_add(right_coefficient)?
                } else {
                    left_coefficient.checked_sub(right_coefficient)?
                };
                Some((left_atom, coefficient))
            }
            _ if self.literal_to_i64(expr).is_some()
                || self.certified_expr_contains_pointer_parameter(expr) =>
            {
                None
            }
            _ => Some((expr.clone(), 1)),
        }
    }

    fn certified_linear_address_components(&self, expr: &CExpr) -> Option<CertifiedLinearAddress> {
        let mut constant = 0_i64;
        let mut terms = Vec::new();
        self.collect_certified_address_terms(expr, 1, &mut constant, &mut terms)?;

        let mut base = None;
        let mut index = None::<(CExpr, i64)>;
        for (sign, term) in terms {
            if self.certified_pointer_parameter_expr(&term) {
                if sign != 1 || base.replace(term).is_some() {
                    return None;
                }
                continue;
            }
            let (atom, coefficient) = self.certified_index_atom_and_coefficient(&term)?;
            let coefficient = coefficient.checked_mul(sign)?;
            match &mut index {
                Some((existing_atom, existing_coefficient)) if *existing_atom == atom => {
                    *existing_coefficient = existing_coefficient.checked_add(coefficient)?;
                }
                Some(_) => return None,
                None => index = Some((atom, coefficient)),
            }
        }
        Some(CertifiedLinearAddress {
            base: base?,
            index: index.map(|(expr, stride)| CertifiedLinearIndex { expr, stride }),
            offset: constant,
        })
    }

    fn certified_member_fact_for_memory(
        &self,
        memory: &r2types::MemoryAccessRenderFact,
    ) -> Option<&r2types::MemberAccessRenderFact> {
        let facts = self.inputs.render_facts()?.member_accesses_by_op.get(&(
            memory.block_addr,
            memory.op_index,
            memory.is_write,
        ))?;
        let mut matching = facts.iter().filter(|fact| {
            fact.access == memory.access
                && fact.object == memory.object
                && fact.access_width == memory.width
        });
        let first = matching.next()?;
        matching.next().is_none().then_some(first)
    }

    fn certified_array_fact_for_memory(
        &self,
        memory: &r2types::MemoryAccessRenderFact,
    ) -> Option<&r2types::ArrayAccessRenderFact> {
        let facts = self.inputs.render_facts()?.array_accesses_by_op.get(&(
            memory.block_addr,
            memory.op_index,
            memory.is_write,
        ))?;
        let mut matching = facts.iter().filter(|fact| {
            fact.access == memory.access
                && fact.object == memory.object
                && fact.access_width == memory.width
                && fact.element_stride > 0
        });
        let first = matching.next()?;
        matching.next().is_none().then_some(first)
    }

    fn render_certified_structured_memory_expr(
        &self,
        memory: &r2types::MemoryAccessRenderFact,
        address: &CExpr,
    ) -> Option<CExpr> {
        let member = self.certified_member_fact_for_memory(memory);
        let array = self.certified_array_fact_for_memory(memory);
        if member.is_none() && array.is_none() {
            return None;
        }
        let CertifiedLinearAddress {
            base,
            index,
            offset,
        } = self.certified_linear_address_components(address)?;

        if let Some(array) = array {
            let expected_offset = i64::try_from(array.field_offset).ok()?;
            let expected_stride = i64::try_from(array.element_stride).ok()?;
            let CertifiedLinearIndex {
                expr: index,
                stride,
            } = index?;
            if offset != expected_offset || stride != expected_stride {
                return None;
            }
            let indexed = CExpr::Subscript {
                base: Box::new(base),
                index: Box::new(index),
            };
            return match member {
                Some(member)
                    if member.field_offset == array.field_offset
                        && member.access == array.access =>
                {
                    Some(self.member_access_expr(indexed, member.field_name.clone()))
                }
                None if array.field_offset == 0 => Some(indexed),
                _ => None,
            };
        }

        let member = member?;
        if index.is_some() || offset != i64::try_from(member.field_offset).ok()? {
            return None;
        }
        Some(self.member_access_expr(base, member.field_name.clone()))
    }

    fn expr_is_store_target_candidate(expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(_)
            | CExpr::Deref(_)
            | CExpr::Subscript { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. } => true,
            CExpr::Paren(inner) => Self::expr_is_store_target_candidate(inner),
            _ => false,
        }
    }

    fn byte_indexed_pointer_add_expr(&self, expr: &CExpr) -> Option<CExpr> {
        self.indexed_pointer_add_expr(expr, &CType::u8())
    }

    pub(super) fn indexed_pointer_add_expr(&self, expr: &CExpr, elem_ty: &CType) -> Option<CExpr> {
        if self.requires_certified_rendering() {
            return None;
        }
        let CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } = expr
        else {
            return None;
        };

        for (base, index) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            let normalized_base = self.normalize_pointer_base_expr(base, 0);
            if !(self.looks_like_pointer(&normalized_base)
                || self.is_non_index_pointer_expr(&normalized_base))
            {
                continue;
            }
            if self.looks_like_pointer(index) || self.is_non_index_pointer_expr(index) {
                continue;
            }
            let elem_ty = match self.expr_type_hint(&normalized_base) {
                Some(CType::Pointer(inner)) | Some(CType::Array(inner, _)) => *inner,
                _ => elem_ty.clone(),
            };
            let elem_size = elem_ty
                .bits()
                .map(|bits| bits.div_ceil(8).max(1))
                .unwrap_or(1);
            let Some(index) = self.scaled_index_expr(index, elem_size) else {
                continue;
            };
            let index = self.normalize_index_expr(&index, 0).unwrap_or(index);
            let base_source_ty = self.expr_type_hint(&normalized_base);
            let normalized_base = self.cast_expr_if_needed(
                normalized_base,
                CType::ptr(elem_ty),
                base_source_ty.as_ref(),
            );
            return Some(CExpr::Subscript {
                base: Box::new(normalized_base),
                index: Box::new(index),
            });
        }

        None
    }

    fn scaled_index_expr(&self, expr: &CExpr, elem_size: u32) -> Option<CExpr> {
        if elem_size <= 1 {
            return Some(expr.clone());
        }

        match expr {
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if self.literal_to_i64(right) == Some(i64::from(elem_size)) {
                    return Some((**left).clone());
                }
                if self.literal_to_i64(left) == Some(i64::from(elem_size)) {
                    return Some((**right).clone());
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Shl,
                left,
                right,
            } => {
                let shift = self.literal_to_i64(right)?;
                if !(0..=30).contains(&shift) {
                    return None;
                }
                (1u32.checked_shl(shift as u32)? == elem_size).then(|| (**left).clone())
            }
            _ => None,
        }
    }

    fn has_authoritative_memory_semantics(&self, name: &str) -> bool {
        matches!(
            self.lookup_semantic_value(name),
            Some(analysis::SemanticValue::Address(_)) | Some(analysis::SemanticValue::Load { .. })
        )
    }

    pub(crate) fn render_certified_value_expr_for_var(&self, var: &SSAVar) -> Option<CExpr> {
        if var.is_const() {
            let value = parse_const_value(&var.name)?;
            return Some(if value > 0x7fff_ffff {
                CExpr::UIntLit(value)
            } else {
                CExpr::IntLit(value as i64)
            });
        }

        let value = self.prepared_value_id_for_var(var)?;
        if !self
            .certified_render_context()
            .is_some_and(|proof| proof.expression_is_renderable(value))
        {
            return None;
        }
        if let Some(expr) = self.certified_parameter_expr_for_value(value) {
            return Some(expr);
        }
        if let Some(expr) =
            self.render_certified_stack_param_value_expr(value, 0, &mut HashSet::new())
        {
            return Some(expr);
        }
        if let Some(expr) = self.render_certified_scalar_expr_for_var(var, 0, &mut HashSet::new()) {
            return Some(expr);
        }
        if var.version == 0 && var.is_register() && self.stable_semantic_ids_are_required() {
            return None;
        }
        let rendered = self.var_name(var);
        Some(
            self.arg_alias_for_rendered_name(&rendered)
                .map(CExpr::Var)
                .unwrap_or_else(|| CExpr::Var(rendered)),
        )
    }

    fn render_certified_scalar_expr_for_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        if var.is_const() {
            return self.render_certified_value_expr_for_var(var);
        }
        let value = self.prepared_value_id_for_var(var)?;
        if !self
            .certified_render_context()
            .is_some_and(|proof| proof.expression_is_renderable(value))
        {
            return None;
        }
        if let Some(expr) = self.certified_parameter_expr_for_value(value) {
            return Some(expr);
        }
        if !visited.insert(value) {
            return None;
        }

        let result = (|| {
            let prepared = self.prepared_ssa()?;
            let inst_id = prepared.graph().def_inst(value)?;
            let inst = prepared.graph().inst(inst_id)?;
            let r2ssa::InstPayload::Op(op) = &inst.payload else {
                return None;
            };
            match op {
                SSAOp::Copy { src, .. }
                | SSAOp::New { src, .. }
                | SSAOp::Subpiece { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. } => {
                    self.render_certified_scalar_expr_for_var(src, depth + 1, visited)
                }
                SSAOp::Cast { src, .. } => {
                    self.render_certified_scalar_expr_for_var(src, depth + 1, visited)
                }
                SSAOp::Load { dst, .. } => {
                    let (block_addr, op_idx) = prepared.inst_op_site(inst_id)?;
                    let proof = self.certified_render_context()?;
                    let fact = proof.memory_access_for_op(block_addr, op_idx, false)?;
                    if fact.value != Some(value) {
                        return None;
                    }
                    let elem_ty = self
                        .type_hint_for_var(dst)
                        .unwrap_or_else(|| type_from_size(dst.size));
                    self.render_certified_memory_expr_for_fact(fact, elem_ty)
                }
                SSAOp::IntAdd { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Add,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntSub { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Sub,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntMult { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Mul,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntAnd { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::BitAnd,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntOr { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::BitOr,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntXor { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::BitXor,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntLeft { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Shl,
                    self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntRight { a, b, .. } | SSAOp::IntSRight { a, b, .. } => {
                    Some(CExpr::binary(
                        BinaryOp::Shr,
                        self.render_certified_scalar_expr_for_var(a, depth + 1, visited)?,
                        self.render_certified_scalar_expr_for_var(b, depth + 1, visited)?,
                    ))
                }
                SSAOp::IntNegate { src, .. } => Some(CExpr::unary(
                    UnaryOp::Neg,
                    self.render_certified_scalar_expr_for_var(src, depth + 1, visited)?,
                )),
                SSAOp::IntNot { src, .. } => Some(CExpr::unary(
                    UnaryOp::BitNot,
                    self.render_certified_scalar_expr_for_var(src, depth + 1, visited)?,
                )),
                _ => None,
            }
        })();

        visited.remove(&value);
        result
    }

    fn render_certified_stack_param_value_expr(
        &self,
        value: r2ssa::ValueId,
        depth: u32,
        visited: &mut HashSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH || !visited.insert(value) {
            return None;
        }

        let result = (|| {
            let prepared = self.prepared_ssa()?;
            if let Some(expr) = self.certified_parameter_expr_for_value(value) {
                return Some(expr);
            }
            let inst_id = prepared.graph().def_inst(value)?;
            let inst = prepared.graph().inst(inst_id)?;
            let r2ssa::InstPayload::Op(op) = &inst.payload else {
                return None;
            };
            match op {
                SSAOp::Copy { src, .. }
                | SSAOp::New { src, .. }
                | SSAOp::Cast { src, .. }
                | SSAOp::Subpiece { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. } => {
                    let src_value = self.prepared_value_id_for_var(src)?;
                    self.render_certified_stack_param_value_expr(src_value, depth + 1, visited)
                }
                SSAOp::Load { .. } => {
                    let (block_addr, op_idx) = prepared.inst_op_site(inst_id)?;
                    let proof = self.certified_render_context()?;
                    let fact = proof.memory_access_for_op(block_addr, op_idx, false)?;
                    if fact.value != Some(value) {
                        return None;
                    }
                    self.certified_stack_owner_expr_for_memory_fact(fact)
                }
                _ => None,
            }
        })();

        visited.remove(&value);
        result
    }

    pub(super) fn certified_memory_address_expr(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
    ) -> Option<(SSAVar, CExpr)> {
        let prepared = self.prepared_ssa()?;
        let addr = prepared.value_var(fact.address)?.clone();
        let expr = self
            .render_certified_address_expr_for_var(&addr, 0, &mut HashSet::new())
            .or_else(|| self.render_certified_value_expr_for_var(&addr))?;
        if self.expr_contains_raw_stack_base_arithmetic(&expr) {
            return None;
        }
        if self.certified_return_expr_contains_raw_storage_name(&expr)
            && self
                .control_facts()
                .is_none_or(|facts| facts.loops.is_empty() && facts.switches.is_empty())
        {
            return None;
        }
        Some((addr, expr))
    }

    fn render_certified_address_expr_for_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        if var.is_const() {
            return self.render_certified_value_expr_for_var(var);
        }
        let prepared = self.prepared_ssa()?;
        let value = self.prepared_value_id_for_var(var)?;
        if var.version == 0 && var.is_register() {
            if let Some(expr) = self.certified_parameter_expr_for_value(value) {
                return Some(expr);
            }
            if self.stable_semantic_ids_are_required() {
                return None;
            }
            let rendered = self.var_name(var);
            return Some(
                self.arg_alias_for_rendered_name(&rendered)
                    .or_else(|| self.certified_signature_arg_alias_for_register(&rendered))
                    .map(CExpr::Var)
                    .unwrap_or_else(|| CExpr::Var(rendered)),
            );
        }

        if !visited.insert(value) {
            return None;
        }

        let result = (|| {
            let inst_id = prepared.graph().def_inst(value)?;
            let inst = prepared.graph().inst(inst_id)?;
            let r2ssa::InstPayload::Op(op) = &inst.payload else {
                return None;
            };
            match op {
                SSAOp::Copy { src, .. }
                | SSAOp::New { src, .. }
                | SSAOp::Cast { src, .. }
                | SSAOp::Subpiece { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. } => {
                    self.render_certified_address_expr_for_var(src, depth + 1, visited)
                }
                SSAOp::Load { .. } => {
                    let (block_addr, op_idx) = prepared.inst_op_site(inst_id)?;
                    let proof = self.certified_render_context()?;
                    let fact = proof.memory_access_for_op(block_addr, op_idx, false)?;
                    if fact.value != Some(value) {
                        return None;
                    }
                    self.certified_stack_owner_expr_for_memory_fact(fact)
                }
                SSAOp::IntAdd { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Add,
                    self.render_certified_address_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_address_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntSub { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Sub,
                    self.render_certified_address_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_address_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntMult { a, b, .. } => Some(CExpr::binary(
                    BinaryOp::Mul,
                    self.render_certified_address_expr_for_var(a, depth + 1, visited)?,
                    self.render_certified_address_expr_for_var(b, depth + 1, visited)?,
                )),
                SSAOp::IntLeft { a, b, .. } => {
                    let shift = self.certified_const_value_for_address_var(b, 0)?;
                    if shift > 63 {
                        return None;
                    }
                    Some(CExpr::binary(
                        BinaryOp::Shl,
                        self.render_certified_address_expr_for_var(a, depth + 1, visited)?,
                        CExpr::IntLit(shift as i64),
                    ))
                }
                SSAOp::PtrAdd {
                    base,
                    index,
                    element_size,
                    ..
                } => {
                    let index =
                        self.render_certified_address_expr_for_var(index, depth + 1, visited)?;
                    let scaled = if *element_size == 1 {
                        index
                    } else {
                        CExpr::binary(
                            BinaryOp::Mul,
                            index,
                            CExpr::IntLit(i64::from(*element_size)),
                        )
                    };
                    Some(CExpr::binary(
                        BinaryOp::Add,
                        self.render_certified_address_expr_for_var(base, depth + 1, visited)?,
                        scaled,
                    ))
                }
                SSAOp::PtrSub {
                    base,
                    index,
                    element_size,
                    ..
                } => {
                    let index =
                        self.render_certified_address_expr_for_var(index, depth + 1, visited)?;
                    let scaled = if *element_size == 1 {
                        index
                    } else {
                        CExpr::binary(
                            BinaryOp::Mul,
                            index,
                            CExpr::IntLit(i64::from(*element_size)),
                        )
                    };
                    Some(CExpr::binary(
                        BinaryOp::Sub,
                        self.render_certified_address_expr_for_var(base, depth + 1, visited)?,
                        scaled,
                    ))
                }
                _ => None,
            }
        })();

        visited.remove(&value);
        result
    }

    pub(super) fn certified_signature_arg_alias_for_register(
        &self,
        reg_name: &str,
    ) -> Option<String> {
        if !self.requires_certified_rendering() {
            return None;
        }
        let reg_name = reg_name.to_ascii_lowercase();
        let index = self.inputs.arch.arg_regs.iter().position(|arg_reg| {
            crate::register_alias_names(arg_reg)
                .into_iter()
                .any(|alias| alias.eq_ignore_ascii_case(&reg_name))
        })?;
        self.inputs
            .function_facts
            .type_facts()
            .render_authorized_signature()
            .and_then(|signature| signature.params.get(index))
            .map(|param| param.name.clone())
            .filter(|name| !name.trim().is_empty())
    }

    pub(super) fn render_certified_memory_expr_for_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
        elem_ty: CType,
    ) -> Option<CExpr> {
        if let Some(expr) = self.certified_stack_owner_expr_for_memory_fact(fact) {
            return Some(expr);
        }
        let (addr, addr_expr) = self.certified_memory_address_expr(fact)?;
        if let Some(rendered) = self.render_certified_structured_memory_expr(fact, &addr_expr) {
            return Some(rendered);
        }
        if matches!(addr_expr, CExpr::Binary { .. }) {
            return None;
        }
        let ptr_ty = CType::ptr(elem_ty);
        let casted = self.cast_addr_expr_to_ptr_if_needed(&addr, addr_expr, &ptr_ty);
        Some(CExpr::Deref(Box::new(casted)))
    }

    fn certified_stack_owner_expr_for_memory_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
    ) -> Option<CExpr> {
        if fact.width == 0 {
            return None;
        }
        if let Some(plan) = self
            .certified_render_context()
            .and_then(|proof| self.certified_render_plan(proof))
            && let Some(expr) = plan.stack_param_expr_for_memory_fact(fact)
        {
            return Some(expr);
        }
        let offset = self
            .inputs
            .render_facts()?
            .stack_slot_offsets
            .get(&fact.object)
            .copied()?;
        let name = self
            .certified_stack_var_name_for_object_offset(fact.object, offset)
            .unwrap_or_else(|| {
                format!(
                    "var_{}h",
                    if offset >= 0 {
                        format!("{:x}", offset)
                    } else {
                        format!("{:x}", -offset)
                    }
                )
            });
        Some(CExpr::Var(name))
    }

    pub(super) fn certified_memory_render_refusal_for_current_op(&self, is_write: bool) -> String {
        let Some(block_addr) = self.current_block_addr.get() else {
            return "missing current block".to_string();
        };
        let Some(op_idx) = self.current_op_idx.get() else {
            return "missing current op".to_string();
        };
        let Some(_fact) = self.certified_memory_access_for_current_op(is_write) else {
            return format!("missing FunctionRenderFacts memory fact at 0x{block_addr:x}:{op_idx}");
        };
        let (array_fact_count, member_fact_count) = self
            .inputs
            .render_facts()
            .map(|render| {
                (
                    render
                        .array_accesses_by_op
                        .get(&(block_addr, op_idx, is_write))
                        .map_or(0, Vec::len),
                    render
                        .member_accesses_by_op
                        .get(&(block_addr, op_idx, is_write))
                        .map_or(0, Vec::len),
                )
            })
            .unwrap_or((0, 0));
        format!(
            "memory access lacks exact typed stack owner or array/member render proof; array_facts {} member_facts {}",
            array_fact_count, member_fact_count
        )
    }

    fn certified_const_value_for_address_var(&self, var: &SSAVar, depth: u32) -> Option<u64> {
        if depth > 4 {
            return None;
        }
        if let Some(value) = parse_const_value(&var.name) {
            return Some(value);
        }
        let prepared = self.prepared_ssa()?;
        let value = self.prepared_value_id_for_var(var)?;
        let inst_id = prepared.graph().def_inst(value)?;
        let inst = prepared.graph().inst(inst_id)?;
        let r2ssa::InstPayload::Op(op) = &inst.payload else {
            return None;
        };
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. } => {
                self.certified_const_value_for_address_var(src, depth + 1)
            }
            SSAOp::IntAnd { a, b, .. } => Some(
                self.certified_const_value_for_address_var(a, depth + 1)?
                    & self.certified_const_value_for_address_var(b, depth + 1)?,
            ),
            _ => None,
        }
    }

    pub(super) fn render_authoritative_memory_access_by_name(
        &self,
        name: &str,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Memory, name) {
            return None;
        }

        let semantic = self.render_memory_access_by_name(name, elem_size, depth, visited);
        let result = if semantic.is_some() || self.has_authoritative_memory_semantics(name) {
            semantic
        } else {
            self.lookup_definition(name).and_then(|expr| {
                self.render_memory_access_from_visible_expr(&expr, elem_size, depth, visited)
            })
        };

        self.leave_resolution_guard(ResolutionPhase::Memory, name);
        result
    }

    pub(super) fn render_canonical_load_expr(
        &self,
        dst: &SSAVar,
        addr: &SSAVar,
        elem_ty: CType,
    ) -> CExpr {
        let pointee_load = dst.size < addr.size;
        let fallback_addr_expr = self
            .lookup_definition(&addr.display_name())
            .or_else(|| self.definition_for_name(&addr.display_name()).cloned())
            .unwrap_or_else(|| self.get_expr(addr));
        let mut semantic_visited = HashSet::new();
        let mut best = self.render_authoritative_memory_access_by_name(
            &dst.display_name(),
            dst.size,
            0,
            &mut semantic_visited,
        );
        best = self.choose_preferred_visible_expr(
            best,
            self.render_authoritative_memory_access_by_name(
                &addr.display_name(),
                dst.size,
                0,
                &mut semantic_visited,
            ),
        );
        let fallback_rendered = self.render_memory_access_from_visible_expr(
            &fallback_addr_expr,
            dst.size,
            0,
            &mut semantic_visited,
        );
        if let Some(fallback_structured) = fallback_rendered
            .as_ref()
            .filter(|expr| Self::expr_is_structured_memory_candidate(expr))
            .cloned()
            && !best
                .as_ref()
                .is_some_and(Self::expr_is_structured_memory_candidate)
        {
            best = Some(fallback_structured);
        }
        best = self.choose_preferred_visible_expr(best, fallback_rendered);
        best = self
            .choose_preferred_visible_expr(best, self.prepared_named_memory_expr_for_current_op());
        if let Some(expr) = best {
            if let CExpr::Deref(inner) = &expr
                && let Some(indexed) = self.indexed_pointer_add_expr(inner, &elem_ty)
            {
                return indexed;
            }
            if !Self::expr_is_scalar_memory_candidate(&expr)
                && !matches!(elem_ty, CType::Pointer(_) | CType::Array(_, _))
                && self.normalized_addr_from_visible_expr(&expr, 0).is_some()
            {
                return self.typed_deref_expr(addr, expr, elem_ty);
            }
            return expr;
        }

        if pointee_load {
            let ptr_ty = CType::ptr(elem_ty.clone());
            let casted = self.cast_addr_expr_to_ptr_if_needed(addr, self.get_expr(addr), &ptr_ty);
            return CExpr::Deref(Box::new(casted));
        }

        if dst.size >= addr.size
            && let Some(stack_var) = self.stack_var_for_addr_var(addr)
        {
            return CExpr::Var(stack_var);
        }

        if addr.is_const() {
            let direct = self.get_expr(addr);
            if matches!(direct, CExpr::Var(_) | CExpr::StringLit(_)) {
                return direct;
            }
        }

        if let Some(exact) = self.resolve_literalish_call_arg_expr(&fallback_addr_expr) {
            return exact;
        }

        self.typed_deref_expr(addr, fallback_addr_expr, elem_ty)
    }

    pub(super) fn render_canonical_store_target_expr(
        &self,
        addr: &SSAVar,
        value_size: u32,
        elem_ty: CType,
    ) -> CExpr {
        let fallback_addr_expr = self
            .lookup_definition(&addr.display_name())
            .or_else(|| self.definition_for_name(&addr.display_name()).cloned())
            .unwrap_or_else(|| self.get_expr(addr));
        let mut semantic_visited = HashSet::new();
        let mut best = self.render_authoritative_memory_access_by_name(
            &addr.display_name(),
            value_size,
            0,
            &mut semantic_visited,
        );
        let fallback_rendered = self.render_memory_access_from_visible_expr(
            &fallback_addr_expr,
            value_size,
            0,
            &mut semantic_visited,
        );
        if let Some(fallback_structured) = fallback_rendered
            .as_ref()
            .filter(|expr| Self::expr_is_structured_memory_candidate(expr))
            .cloned()
            && !best
                .as_ref()
                .is_some_and(Self::expr_is_structured_memory_candidate)
        {
            best = Some(fallback_structured);
        }
        best = self.choose_preferred_visible_expr(best, fallback_rendered);
        best = self.choose_preferred_visible_expr(
            best,
            self.prepared_named_memory_def_expr_for_current_op(),
        );
        if let Some(expr) = best.filter(Self::expr_is_store_target_candidate) {
            return expr;
        }

        if let Some(stack_var) = self.stack_var_for_addr_var(addr) {
            return CExpr::Var(stack_var);
        }

        if addr.is_const() {
            let direct = self.get_expr(addr);
            if matches!(direct, CExpr::Var(_) | CExpr::StringLit(_)) {
                return direct;
            }
        }

        if let Some(exact) = self.resolve_literalish_call_arg_expr(&fallback_addr_expr) {
            return exact;
        }

        if value_size == 1
            && let Some(indexed) = self.byte_indexed_pointer_add_expr(&fallback_addr_expr)
        {
            return indexed;
        }

        self.typed_deref_expr(addr, fallback_addr_expr, elem_ty)
    }

    pub(super) fn render_memory_access_from_visible_expr(
        &self,
        expr: &CExpr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        self.render_memory_access_from_visible_expr_with_direction(
            expr, elem_size, false, depth, visited,
        )
    }

    fn render_memory_access_from_visible_expr_with_direction(
        &self,
        expr: &CExpr,
        elem_size: u32,
        is_write: bool,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let mut try_render = |candidate: &CExpr, ctx: &FoldingContext<'_>| {
            let canonical = ctx.canonicalize_visible_address_expr(candidate, depth + 1);
            let addr = ctx.normalized_addr_from_visible_expr(&canonical, depth + 1)?;
            ctx.render_access_expr_from_addr(&addr, elem_size, is_write, depth + 1, visited)
        };

        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(expr, depth + 1, &mut semantic_visited);
        let preferred = if self.prefers_visible_expr(expr, &semanticized) {
            semanticized
        } else {
            expr.clone()
        };
        if let Some(rendered) = try_render(&preferred, self).or_else(|| try_render(expr, self)) {
            return Some(rendered);
        }
        let elem_ty = type_from_size(elem_size);
        if let Some(indexed) = self.indexed_pointer_add_expr(&preferred, &elem_ty) {
            return Some(indexed);
        }
        if preferred != *expr
            && let Some(indexed) = self.indexed_pointer_add_expr(expr, &elem_ty)
        {
            return Some(indexed);
        }

        None
    }
}
