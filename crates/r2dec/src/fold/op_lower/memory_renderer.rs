use std::collections::{BTreeSet, HashSet};

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
    fn certified_pointer_base_expr(&self, expr: &CExpr) -> bool {
        let expr = match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => inner.as_ref(),
            _ => expr,
        };
        let CExpr::Var(name) = expr else {
            return false;
        };
        if self
            .inputs
            .function_facts
            .type_facts()
            .render_authorized_signature()
            .is_some_and(|signature| {
                signature.params.iter().any(|param| {
                    param.name.eq_ignore_ascii_case(&self.spelling(*name))
                        && param.ty.as_ref().is_some_and(|ty| {
                            matches!(
                                crate::type_like_to_ctype(ty),
                                CType::Pointer(_) | CType::Array(_, _)
                            )
                        })
                })
            })
        {
            return true;
        }
        self.inputs.render_facts().is_some_and(|render| {
            render.loop_carriers().any(|entity| {
                let r2types::CertifiedEntity::LoopCarrier { phi, ty, .. } = entity else {
                    return false;
                };
                crate::certified_loop_carrier_name(*phi).eq_ignore_ascii_case(&self.spelling(*name))
                    && ty.as_ref().is_some_and(|ty| {
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
            if !contains && self.certified_pointer_base_expr(node) {
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
            if self.certified_pointer_base_expr(&term) {
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

    fn render_certified_semantic_array_expr(
        &self,
        memory: &r2types::MemoryAccessRenderFact,
    ) -> Option<CExpr> {
        let array = self.certified_array_fact_for_memory(memory)?;
        let (Some(base), Some(index)) = (array.base, array.index) else {
            return None;
        };
        let r2ssa::SemanticId::Parameter(slot) = base else {
            return None;
        };
        let r2ssa::SemanticId::Expression(index) = index else {
            return None;
        };
        let render = self.inputs.render_facts()?;
        let slot = usize::try_from(slot).ok()?;
        if render.parameter_values(slot).next().is_none()
            || !render
                .certified_expr_for_value(index)
                .is_some_and(|expr| expr.fact.renderable)
        {
            return None;
        }
        let base = self
            .inputs
            .function_facts
            .type_facts()
            .render_authorized_signature()?
            .params
            .get(slot)
            .map(|param| param.name.trim())
            .filter(|name| !name.is_empty())?;
        let index_var = self.prepared_ssa()?.value_var(index)?;
        let index = self.render_certified_value_expr_for_var(index_var)?;
        let indexed = CExpr::Subscript {
            base: Box::new(self.name_ref(&base.to_string())),
            index: Box::new(index),
        };
        match self.certified_member_fact_for_memory(memory) {
            Some(member)
                if member.field_offset == array.field_offset && member.access == array.access =>
            {
                Some(self.member_access_expr(indexed, member.field_name.clone()))
            }
            None if array.field_offset == 0 => Some(indexed),
            _ => None,
        }
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

    /// Whether a type says the expression is a pointer, when it says either.
    ///
    /// `None` means the type answers nothing -- it is missing, or opaque, or a
    /// shape that is neither addressable nor countable -- and the caller must
    /// look elsewhere.
    fn expr_type_answers_pointer(&self, expr: &CExpr) -> Option<bool> {
        match self.expr_type_hint(expr)? {
            CType::Pointer(_) | CType::Array(_, _) => Some(true),
            CType::Int(_) | CType::UInt(_) | CType::Bool | CType::Enum(_) | CType::Typedef(_) => {
                Some(false)
            }
            _ => None,
        }
    }

    fn subscript_expr_for_base_and_index(
        &self,
        base: CExpr,
        index: &CExpr,
        elem_ty: &CType,
    ) -> Option<CExpr> {
        let base_source_ty = self.expr_type_hint(&base);
        // The pointee names the element only when it is a type an element can
        // have. `void *` says nothing about what one step is, so the width the
        // access itself asks for stands.
        let elem_ty = match &base_source_ty {
            Some(CType::Pointer(inner)) | Some(CType::Array(inner, _))
                if !matches!(inner.as_ref(), CType::Void | CType::Unknown) =>
            {
                inner.as_ref().clone()
            }
            _ => elem_ty.clone(),
        };
        let elem_size = elem_ty
            .bits()
            .map(|bits| bits.div_ceil(8).max(1))
            .unwrap_or(1);
        let index = self.scaled_index_expr(index, elem_size)?;
        let index = self.normalize_index_expr(&index, 0).unwrap_or(index);
        let base = self.cast_expr_if_needed(base, CType::ptr(elem_ty), base_source_ty.as_ref());
        Some(CExpr::Subscript {
            base: Box::new(base),
            index: Box::new(index),
        })
    }

    pub(super) fn indexed_pointer_add_expr(&self, expr: &CExpr, elem_ty: &CType) -> Option<CExpr> {
        let CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } = expr
        else {
            return None;
        };

        let orientations = [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ];

        // Which operand is the pointer is a question the types answer whenever
        // both are typed, and then there is nothing to weigh. `looks_like_pointer`
        // otherwise falls back to the shape of the name, and on a binary with no
        // symbols every name is invented in a shape it accepts: `buf + len` read
        // as two pointers, the first orientation that got past the checks below
        // decided it, and `buf[len] = 0` came out as `len[buf] = 0` -- a write
        // through a length. So the typed reading is settled first, and the
        // name-shaped one only answers what the types leave open.
        for (base, index) in orientations {
            let normalized_base = self.normalize_pointer_base_expr(base, 0);
            if self.expr_type_answers_pointer(&normalized_base) == Some(true)
                && self.expr_type_answers_pointer(index) == Some(false)
                && let Some(indexed) =
                    self.subscript_expr_for_base_and_index(normalized_base, index, elem_ty)
            {
                return Some(indexed);
            }
        }

        for (base, index) in orientations {
            let normalized_base = self.normalize_pointer_base_expr(base, 0);
            if !(self.looks_like_pointer(&normalized_base)
                || self.is_non_index_pointer_expr(&normalized_base))
            {
                continue;
            }
            if self.looks_like_pointer(index) || self.is_non_index_pointer_expr(index) {
                continue;
            }
            let Some(indexed) =
                self.subscript_expr_for_base_and_index(normalized_base, index, elem_ty)
            else {
                continue;
            };
            return Some(indexed);
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
        let symbols = &self.symbols;

        if var.is_const() {
            let value = parse_const_value(&var.name)?;
            return Some(if value > 0x7fff_ffff {
                CExpr::UIntLit(value)
            } else {
                CExpr::IntLit(value as i64)
            });
        }

        let value = self.prepared_value_id_for_var(var)?;
        if let Some(name) = self.certified_loop_carrier_name_for_value(value) {
            return Some(self.name_ref(&name));
        }
        if let Some(name) = self.certified_memory_result_name_for_value(value) {
            return Some(self.name_ref(&name));
        }
        if self.prepared_ssa().is_some_and(|prepared| {
            prepared
                .call_result_certificate_for_value(value)
                .is_some_and(|result| result.relation.is_identity())
        }) {
            return self.certified_call_result_expr_for_value(value);
        }
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
        if let Some(expr) = self.certified_structural_expr_for_value(value, 0, &mut BTreeSet::new())
        {
            return Some(expr);
        }
        if var.version == 0 && var.is_register() && self.stable_semantic_ids_are_required() {
            return None;
        }
        let rendered = self.var_name(var);
        Some(
            self.arg_alias_for_rendered_name(&rendered)
                .map(|n| crate::symbol::var_ref(&symbols, n))
                .unwrap_or_else(|| self.name_ref(&rendered)),
        )
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
        let symbols = &self.symbols;

        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        if var.is_const() {
            return self.render_certified_value_expr_for_var(var);
        }
        let prepared = self.prepared_ssa()?;
        let value = self.prepared_value_id_for_var(var)?;
        if let Some(name) = self.certified_loop_carrier_name_for_value(value) {
            return Some(self.name_ref(&name));
        }
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
                    .map(|n| crate::symbol::var_ref(&symbols, n))
                    .unwrap_or_else(|| self.name_ref(&rendered)),
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
        None
    }

    pub(super) fn render_certified_memory_expr_for_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
        elem_ty: CType,
    ) -> Option<CExpr> {
        if fact.space != r2il::SpaceId::Ram {
            return None;
        }
        if let Some(expr) = self.certified_stack_owner_expr_for_memory_fact(fact) {
            return Some(expr);
        }
        if let Some(array) = self.certified_array_fact_for_memory(fact)
            && (array.base.is_some() || array.index.is_some())
        {
            return self.render_certified_semantic_array_expr(fact);
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
        let offset = self.inputs.render_facts()?.stack_slot_offset(fact.object)?;
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
        Some(self.name_ref(&name))
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
        let memo_key = self
            .prepared_value_id_for_var(dst)
            .map(|value| (value, elem_ty.to_string()));
        if let Some(cached) = memo_key
            .as_ref()
            .and_then(|key| self.load_expr_memo.borrow().get(key).cloned())
        {
            return cached;
        }
        let rendered = self.render_canonical_load_expr_uncached(dst, addr, elem_ty.clone());
        // A subscript on an integer base does not say what it reads, and the
        // width is known here. Left unstated, every consumer invents one: the
        // corpus harness rewrites `x[i]` as `((unsigned char *)x)[i]`, so
        // murmur3's dword read became a byte read and the hash came out wrong.
        let rendered = self.typed_subscript_access(rendered, &elem_ty);
        if let Some(key) = memo_key {
            self.load_expr_memo
                .borrow_mut()
                .insert(key, rendered.clone());
        }
        rendered
    }

    /// State the pointee an integer-based subscript reads.
    ///
    /// The index counts bytes -- the lifter scaled it when it built the address
    /// -- so widening the pointee means dividing that scaling back out, or the
    /// read moves: `((uint32_t *)data)[i * 4]` lands at `i * 16`.
    fn typed_subscript_access(&self, expr: CExpr, elem_ty: &CType) -> CExpr {
        let CExpr::Subscript { base, index } = expr else {
            return expr;
        };
        let elem_bytes = match elem_ty {
            CType::Int(bits) | CType::UInt(bits) | CType::Float(bits) => bits / 8,
            _ => 0,
        };
        let already_typed = matches!(
            base.as_ref(),
            CExpr::Cast {
                ty: CType::Pointer(_),
                ..
            }
        );
        if elem_bytes <= 1 || already_typed {
            return CExpr::Subscript { base, index };
        }
        let scaled = match index.as_ref() {
            CExpr::Var(name) => self
                .definition_of(&self.spelling(*name))
                .unwrap_or_else(|| (*index).clone()),
            other => other.clone(),
        };
        match Self::index_in_elements(&scaled, elem_bytes) {
            Some(unscaled) => CExpr::Subscript {
                base: Box::new(CExpr::cast(CType::ptr(elem_ty.clone()), *base)),
                index: Box::new(unscaled),
            },
            None => CExpr::Deref(Box::new(CExpr::cast(
                CType::ptr(elem_ty.clone()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::cast(CType::ptr(CType::UInt(8)), *base),
                    *index,
                ),
            ))),
        }
    }

    /// A byte-counting index expressed in elements, when it divides exactly.
    fn index_in_elements(index: &CExpr, elem_bytes: u32) -> Option<CExpr> {
        match index {
            CExpr::Paren(inner) => Self::index_in_elements(inner, elem_bytes),
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => match (left.as_ref(), right.as_ref()) {
                (other, CExpr::IntLit(value)) | (CExpr::IntLit(value), other)
                    if *value == i64::from(elem_bytes) =>
                {
                    Some(other.clone())
                }
                _ => None,
            },
            CExpr::IntLit(value) if value % i64::from(elem_bytes) == 0 => {
                Some(CExpr::IntLit(value / i64::from(elem_bytes)))
            }
            _ => None,
        }
    }

    fn render_canonical_load_expr_uncached(
        &self,
        dst: &SSAVar,
        addr: &SSAVar,
        elem_ty: CType,
    ) -> CExpr {
        if let Some(named) = self.prepared_named_memory_expr_for_value(dst) {
            return named;
        }
        let pointee_load = dst.size < addr.size;
        // One resolver. `get_expr` already tries forwarding, then semantic
        // values, then the recorded definition, then the name, and the two
        // lookups that used to run ahead of it are the third and a variant of
        // it -- so putting them first meant an address was resolved by a rule
        // that had not been told what the value forwards to, while the decision
        // to leave that value's statement out was taken by a rule that had.
        let fallback_addr_expr = self.get_expr(addr);
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
            return self.name_ref(&stack_var);
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
        // One resolver. `get_expr` already tries forwarding, then semantic
        // values, then the recorded definition, then the name, and the two
        // lookups that used to run ahead of it are the third and a variant of
        // it -- so putting them first meant an address was resolved by a rule
        // that had not been told what the value forwards to, while the decision
        // to leave that value's statement out was taken by a rule that had.
        let fallback_addr_expr = self.get_expr(addr);
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
            return self.name_ref(&stack_var);
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
