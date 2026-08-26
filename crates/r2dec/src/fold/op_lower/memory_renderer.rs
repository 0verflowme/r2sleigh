use std::collections::{BTreeSet, HashSet};

use r2ssa::SSAVar;

use super::*;

/// Opaque proof that one rendered lvalue came from the exact source-owned
/// structured memory-access fact for the current operation.
///
/// The fields stay private to this module so an arbitrary contextual AST
/// cannot be presented as a certified address occurrence downstream.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct CertifiedMemoryAccessExpr {
    access: r2ssa::StructuredAccessId,
    address: r2ssa::ValueId,
    is_write: bool,
    expr: CExpr,
}

impl CertifiedMemoryAccessExpr {
    pub(super) const fn access(&self) -> r2ssa::StructuredAccessId {
        self.access
    }

    pub(super) const fn address(&self) -> r2ssa::ValueId {
        self.address
    }

    pub(super) const fn is_write(&self) -> bool {
        self.is_write
    }

    pub(super) const fn expr(&self) -> &CExpr {
        &self.expr
    }

    pub(super) fn into_expr(self) -> CExpr {
        self.expr
    }
}

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
    fn certified_memory_access_expr(
        &self,
        address: r2ssa::ValueId,
        value: r2ssa::ValueId,
        width: u32,
        is_write: bool,
        elem_ty: CType,
    ) -> OpLoweringResult<CertifiedMemoryAccessExpr> {
        let (block_addr, op_idx) = self
            .current_source_op_site()
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        let fact = self
            .certified_memory_access_for_current_op(is_write)
            .filter(|fact| {
                fact.block_addr == block_addr
                    && fact.op_index == op_idx
                    && fact.space == r2il::SpaceId::Ram
                    && fact.address == address
                    && fact.value == Some(value)
                    && fact.is_write == is_write
                    && fact.width == width
            })
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        let expr = self
            .render_certified_memory_expr_for_fact(fact, elem_ty.clone())
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        let expr = if is_write {
            Self::expr_is_store_target_candidate(&expr)
                .then_some(expr)
                .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?
        } else {
            self.typed_subscript_access(expr, &elem_ty)
        };
        Ok(CertifiedMemoryAccessExpr {
            access: fact.access,
            address: fact.address,
            is_write: fact.is_write,
            expr,
        })
    }

    pub(super) fn render_certified_load_access_expr(
        &self,
        dst: &SSAVar,
        addr: &SSAVar,
        elem_ty: CType,
    ) -> OpLoweringResult<CertifiedMemoryAccessExpr> {
        let address = self
            .prepared_value_id_for_var(addr)
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        let value = self
            .prepared_value_id_for_var(dst)
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        self.certified_memory_access_expr(address, value, dst.size, false, elem_ty)
    }

    pub(super) fn render_certified_store_access_expr(
        &self,
        addr: &SSAVar,
        val: &SSAVar,
        elem_ty: CType,
    ) -> OpLoweringResult<CertifiedMemoryAccessExpr> {
        let address = self
            .prepared_value_id_for_var(addr)
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        let value = self
            .prepared_value_id_for_var(val)
            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
        self.certified_memory_access_expr(address, value, val.size, true, elem_ty)
    }

    fn certified_pointer_base_expr(&self, expr: &CExpr) -> bool {
        let expr = match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => inner.as_ref(),
            _ => expr,
        };
        let CExpr::Var(name) = expr else {
            return false;
        };
        let role = self.symbols.borrow().get(*name).role;
        if let crate::symbol::SymbolRole::Parameter(slot) = role {
            return self.inputs.render_facts().is_some_and(|render| {
                matches!(
                    render
                        .certified_entities
                        .get(&r2ssa::SemanticId::Parameter(slot)),
                    Some(r2types::CertifiedEntity::Parameter {
                        slot: entity_slot,
                        ty: Some(ty),
                        ..
                    }) if *entity_slot == slot
                        && matches!(
                            crate::type_like_to_ctype(ty),
                            CType::Pointer(_) | CType::Array(_, _)
                        )
                )
            });
        }
        let Some(names) = self.inputs.binding_names else {
            return false;
        };
        self.inputs.render_facts().is_some_and(|render| {
            render.loop_carriers().any(|entity| {
                let r2types::CertifiedEntity::LoopCarrier { phi, ty, .. } = entity else {
                    return false;
                };
                matches!(
                    names.require_value(*phi),
                    Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) if symbol == *name
                ) && ty.as_ref().is_some_and(|ty| {
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
        let base_value = render.parameter_values(slot).next()?;
        if !render
            .certified_expr_for_value(index)
            .is_some_and(|expr| expr.fact.renderable)
        {
            return None;
        }
        let base = self.certified_parameter_expr_for_value(base_value)?;
        let index_var = self.prepared_ssa()?.value_var(index)?;
        let index = self.render_certified_value_expr_for_var(index_var)?;
        let indexed = CExpr::Subscript {
            base: Box::new(base),
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
        match Self::index_in_elements(&index, elem_bytes) {
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

    pub(crate) fn render_certified_value_expr_for_var(&self, var: &SSAVar) -> Option<CExpr> {
        if let Some(value) = self.certified_const_bits(var) {
            return Some(if value > 0x7fff_ffff {
                CExpr::UIntLit(value)
            } else {
                CExpr::IntLit(value as i64)
            });
        }

        let value = self.prepared_value_id_for_var(var)?;
        if let Some(expr) = self.certified_loop_carrier_expr_for_value(value) {
            return Some(expr);
        }
        if let Some(expr) = self.certified_memory_result_expr_for_value(value) {
            return Some(expr);
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
        match self.planned_value_expr(value) {
            Ok(expr) => Some(expr),
            Err(error) => {
                self.retain_first_observation_error(error);
                self.retain_first_lowering_refusal(
                    OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
                None
            }
        }
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
        if self.certified_const_bits(var).is_some() {
            return self.render_certified_value_expr_for_var(var);
        }
        let prepared = self.prepared_ssa()?;
        let value = self.prepared_value_id_for_var(var)?;
        if let Some(expr) = self.certified_loop_carrier_expr_for_value(value) {
            return Some(expr);
        }
        if var.version == 0 && var.is_register() {
            if let Some(expr) = self.certified_parameter_expr_for_value(value) {
                return Some(expr);
            }
            if self.stable_semantic_ids_are_required() {
                return None;
            }
            return match self.planned_value_expr(value) {
                Ok(expr) => Some(expr),
                Err(error) => {
                    self.retain_first_observation_error(error);
                    self.retain_first_lowering_refusal(
                        OpLoweringRefusal::MissingProgramVariableAuthorization,
                    );
                    None
                }
            };
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
            && let Some(expr) = self
                .inputs
                .binding_names
                .and_then(|names| plan.stack_param_expr_for_memory_fact(fact, names))
        {
            return Some(expr);
        }
        self.inputs.render_facts()?.stack_slot_offset(fact.object)?;
        self.certified_stack_var_expr_for_object(fact.object)
    }

    fn certified_const_value_for_address_var(&self, var: &SSAVar, depth: u32) -> Option<u64> {
        if depth > 4 {
            return None;
        }
        if let Some(value) = self.certified_const_bits(var) {
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
}
