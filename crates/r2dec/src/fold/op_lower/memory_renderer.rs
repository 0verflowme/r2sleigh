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
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
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
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        let expr = self
            .render_certified_memory_expr_for_fact(fact, elem_ty.clone())
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        if is_write && !Self::expr_is_store_target_candidate(&expr) {
            return Err(OpLoweringRefusal::missing_machine_projection());
        }
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
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        let value = self
            .prepared_value_id_for_var(dst)
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
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
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        let value = self
            .prepared_value_id_for_var(val)
            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
        self.certified_memory_access_expr(address, value, val.size, true, elem_ty)
    }

    /// Whether a rendered operand names an object declared a pointer.
    ///
    /// An object declared a pointer is a pointer wherever it is read, and
    /// the declaration is the one place that says so: it already agrees with
    /// the certificate that typed the parameter or the carrier, because it
    /// was made from it. This is only consulted where a declared aggregate
    /// fact says the address is a member or element and the C address has to
    /// be split around the base; an element the rewriter proves is spelled
    /// from its term and never comes here.
    fn declared_pointer_expr(&self, expr: &CExpr) -> bool {
        let expr = match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => inner.as_ref(),
            _ => expr,
        };
        let CExpr::Var(name) = expr else {
            return false;
        };
        matches!(
            self.symbols.borrow().get(*name).ty,
            CType::Pointer(_) | CType::Array(_, _)
        )
    }

    fn certified_expr_contains_declared_pointer(&self, expr: &CExpr) -> bool {
        let mut contains = false;
        expr.visit(&mut |node| {
            if !contains && self.declared_pointer_expr(node) {
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
                || self.certified_expr_contains_declared_pointer(expr) =>
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
            if self.declared_pointer_expr(&term) {
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

    /// Spell an exact linear machine address without claiming an array or
    /// member projection. Casting the certified base to a byte pointer before
    /// applying the proved stride keeps C from scaling the addition by an
    /// inferred pointee type. The result remains a raw dereference; source-like
    /// subscript/member syntax is reserved for the upstream facts above.
    fn render_certified_linear_byte_address(&self, address: &CExpr) -> Option<CExpr> {
        let CertifiedLinearAddress {
            base,
            index,
            offset,
        } = self.certified_linear_address_components(address)?;
        let mut result = CExpr::cast(
            CType::ptr(CType::Int {
                bits: 8,
                signedness: r2types::Signedness::Unsigned,
            }),
            base,
        );
        if let Some(CertifiedLinearIndex { expr, stride }) = index
            && stride != 0
        {
            let magnitude = stride.checked_abs()?;
            let delta = if magnitude == 1 {
                expr
            } else {
                CExpr::binary(BinaryOp::Mul, expr, CExpr::IntLit(magnitude))
            };
            result = CExpr::binary(
                if stride > 0 {
                    BinaryOp::Add
                } else {
                    BinaryOp::Sub
                },
                result,
                delta,
            );
        }
        if offset != 0 {
            let magnitude = offset.checked_abs()?;
            result = CExpr::binary(
                if offset > 0 {
                    BinaryOp::Add
                } else {
                    BinaryOp::Sub
                },
                result,
                CExpr::IntLit(magnitude),
            );
        }
        Some(result)
    }

    fn integerize_certified_address_expr(expr: &CExpr, pointer_bits: u32) -> Option<CExpr> {
        let integer = CType::Int {
            bits: pointer_bits,
            signedness: r2types::Signedness::Unsigned,
        };
        Some(match expr {
            CExpr::Observed { id, expr } => CExpr::Observed {
                id: *id,
                expr: Box::new(Self::integerize_certified_address_expr(expr, pointer_bits)?),
            },
            CExpr::IntLit(value) => CExpr::IntLit(*value),
            CExpr::UIntLit(value) => CExpr::UIntLit(*value),
            CExpr::Var(symbol) => CExpr::cast(integer, CExpr::Var(*symbol)),
            CExpr::Unary { op, operand } if matches!(op, UnaryOp::Neg | UnaryOp::BitNot) => {
                CExpr::Unary {
                    op: *op,
                    operand: Box::new(Self::integerize_certified_address_expr(
                        operand,
                        pointer_bits,
                    )?),
                }
            }
            CExpr::Binary { op, left, right }
                if matches!(
                    op,
                    BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Shl
                        | BinaryOp::Shr
                        | BinaryOp::BitAnd
                        | BinaryOp::BitOr
                        | BinaryOp::BitXor
                ) =>
            {
                CExpr::binary(
                    *op,
                    Self::integerize_certified_address_expr(left, pointer_bits)?,
                    Self::integerize_certified_address_expr(right, pointer_bits)?,
                )
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(Self::integerize_certified_address_expr(
                inner,
                pointer_bits,
            )?)),
            CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::Unary { .. }
            | CExpr::Binary { .. }
            | CExpr::External { .. }
            | CExpr::Ternary { .. }
            | CExpr::Cast { .. }
            | CExpr::Call { .. }
            | CExpr::Subscript { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. }
            | CExpr::Sizeof(_)
            | CExpr::SizeofType(_)
            | CExpr::AddrOf(_)
            | CExpr::Deref(_)
            | CExpr::Comma(_) => return None,
        })
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
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
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
        if self.prepared_value_id_for_var(&addr) != Some(fact.address) {
            return None;
        }
        let expr = match self.planned_value_expr(fact.address) {
            Ok(expr) => expr,
            Err(error) => {
                self.retain_first_observation_error(error);
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                return None;
            }
        };
        // An address is an operand like any other, and reading it is a read of
        // the value. This path builds the operand's expression itself rather
        // than going through the operand-observation path, so the read went
        // unmarked -- invisible while the address is a computation whose parts
        // are observed on their way here, and fatal when it is a bare literal,
        // which is then a planned inline value that no rendered occurrence
        // accounts for and the journal refuses the function over.
        let site = self
            .current_source_op_site()
            .and_then(|(block_addr, op_idx)| self.normalized_site(block_addr, op_idx));
        let input_idx = self
            .prepared_ssa()
            .and_then(|prepared| prepared.graph().inst(fact.access.inst))
            .and_then(|inst| inst.inputs.iter().position(|input| *input == fact.address));
        let expr = match (site, input_idx) {
            (Some(_), Some(input_idx)) => {
                self.observe_optional_normalized_input_value_expr(site, input_idx, expr)
            }
            _ => expr,
        };
        Some((addr, expr))
    }

    /// The access as C, by whichever authority answers for it first: a
    /// declared aggregate's element, the rewriter's proven subscript, a stack
    /// slot's name, a declared member split out of the address, and last the
    /// address itself dereferenced. Each is one lookup; none takes an
    /// expression apart to decide.
    pub(super) fn render_certified_memory_expr_for_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
        elem_ty: CType,
    ) -> Option<CExpr> {
        if fact.space != r2il::SpaceId::Ram {
            return None;
        }
        if let Some(array) = self.certified_array_fact_for_memory(fact)
            && (array.base.is_some() || array.index.is_some())
        {
            return self.render_certified_semantic_array_expr(fact);
        }
        if let Some(expr) = self.certified_subscript_expr_for_fact(fact, &elem_ty) {
            return Some(expr);
        }
        if let Some(expr) = self.certified_stack_owner_expr_for_memory_fact(fact) {
            return Some(expr);
        }
        let (addr, addr_expr) = self.certified_memory_address_expr(fact)?;
        if let Some(rendered) = self.render_certified_structured_memory_expr(fact, &addr_expr) {
            return Some(rendered);
        }
        if matches!(addr_expr, CExpr::Binary { .. }) {
            let pointer_bits = self.inputs.arch.ptr_size.checked_mul(8)?;
            let byte_address = self
                .render_certified_linear_byte_address(&addr_expr)
                .or_else(|| Self::integerize_certified_address_expr(&addr_expr, pointer_bits))?;
            return Some(CExpr::Deref(Box::new(CExpr::cast(
                CType::ptr(elem_ty),
                byte_address,
            ))));
        }
        let ptr_ty = CType::ptr(elem_ty);
        let casted = self.cast_addr_expr_to_ptr_if_needed(&addr, addr_expr, &ptr_ty);
        Some(CExpr::Deref(Box::new(casted)))
    }

    /// The slot's name, for an access that sits at the slot's own offset.
    ///
    /// An access at an offset the machine computes is inside the slot and
    /// not at it, so the name alone would read the first element for every
    /// element; that access is the subscript path's or, failing it, the
    /// address's.
    fn certified_stack_owner_expr_for_memory_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
    ) -> Option<CExpr> {
        if fact.width == 0 {
            return None;
        }
        if self
            .prepared_ssa()
            .is_some_and(|prepared| prepared.objects().address_is_indexed(fact.address))
        {
            return None;
        }
        self.inputs.render_facts()?.stack_slot_offset(fact.object)?;
        self.certified_stack_var_expr_for_object(fact.object)
    }
}
