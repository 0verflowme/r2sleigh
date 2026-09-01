/// A C type the renderer is allowed to decide a conversion from.
///
/// Property 2 asks that inference be unrepresentable rather than merely
/// avoided. A cast is a statement that one type becomes another, and the
/// renderer may only make it from types something recorded. So the source of a
/// conversion is this type, whose field is private to this module and whose
/// constructors each name the evidence they come from: a binding's emitted
/// declaration, a certified upstream fact, the operation's own requirement, or
/// a callee's recorded signature.
///
/// A caller that has none of those cannot manufacture one. It has to pass
/// `None`, and every `None` is therefore a site the compiler points at -- which
/// is the enumeration Track B's first stage asks for, kept honest by the type
/// rather than by a convention.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RecordedType(CType);

impl RecordedType {
    /// The type the emitted declaration gives this object.
    fn from_declaration(ty: CType) -> Self {
        Self(ty)
    }

    /// A type upstream certified for this value.
    fn from_certified_fact(ty: CType) -> Self {
        Self(ty)
    }

    /// The type the operation itself requires of its operands and result.
    ///
    /// `IntSLess` and `IntLess` differ only in the signedness of what they
    /// compare, so this is the operation's meaning, not a reading of its
    /// operands.
    fn from_operation(ty: CType) -> Self {
        Self(ty)
    }

    /// The return type recorded for the callee a call names.
    fn from_callee_signature(ty: CType) -> Self {
        Self(ty)
    }

    /// The type of the machine expression the plan inlines for a value.
    ///
    /// A value the plan inlines has no declaration, so it has no declared
    /// type, and it was previously left with no source at all. It is not
    /// typeless: the sealed machine projection holds the expression that will
    /// be rendered in its place, and that expression has a width and a
    /// signedness. That is a recorded fact about the value, not a reading of
    /// the C the renderer is about to emit.
    ///
    /// An address is taken at its machine width. Without a recorded pointee
    /// there is nothing to say about what it points at, and saying the width
    /// is the honest half of the answer.
    fn from_inline_expression(ty: &r2ssa::MachineType) -> Self {
        Self(match ty {
            r2ssa::MachineType::Bool { .. } => CType::Bool,
            r2ssa::MachineType::Integer {
                width_bits,
                signedness,
            } => match signedness {
                r2ssa::MachineSignedness::Signed => CType::Int { bits: *width_bits, signedness: r2types::Signedness::Signed },
                r2ssa::MachineSignedness::Unsigned => CType::Int { bits: *width_bits, signedness: r2types::Signedness::Unsigned },
            },
            r2ssa::MachineType::Address { width_bits, .. } => CType::Int { bits: *width_bits, signedness: r2types::Signedness::Unsigned },
        })
    }


    /// A source for a fixture, which has no upstream to record one.
    ///
    /// Deliberately test-only: production must name the evidence.
    #[cfg(test)]
    pub(crate) fn for_test(ty: CType) -> Self {
        Self(ty)
    }

    pub(crate) fn get(&self) -> &CType {
        &self.0
    }

    fn into_inner(self) -> CType {
        self.0
    }
}

impl<'a> FoldingContext<'a> {
    fn certified_parameter_expr_for_value(&self, value: r2ssa::ValueId) -> Option<CExpr> {
        let slot = self
            .certified_render_context()?
            .render_facts
            .exact_parameter_slot_for_value(value)?;
        let names = self.inputs.binding_names?;
        match names.require_parameter_slot(slot as u32) {
            Ok(crate::binding_plan::PlannedParameterSymbol::Bound { symbol, .. }) => {
                Some(CExpr::Var(symbol))
            }
            Err(_) => {
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                None
            }
        }
    }

    fn stable_semantic_ids_are_required(&self) -> bool {
        self.certified_render_context()
            .is_some_and(|proof| !proof.render_facts.certified_exprs.is_empty())
    }

    pub(super) fn certified_const_bits(&self, var: &SSAVar) -> Option<u64> {
        let value = var.constant_bits()?;
        let storage = self
            .prepared_ssa()?
            .graph()
            .canonical_storage_for_var(var)?;
        (storage.space == r2ssa::CanonicalStorageSpace::Constant).then_some(value)
    }

    fn certified_const_expr(&self, var: &SSAVar) -> Option<CExpr> {
        let value = self.certified_const_bits(var)?;
        Some(if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        })
    }

    const MAX_SEMANTIC_RENDER_DEPTH: u32 = 16;

    fn use_info(&self) -> &analysis::UseInfo {
        self.state.analysis_ctx.semantic()
    }

    fn prepared_ssa(&self) -> Option<&SsaArtifact> {
        self.inputs.prepared_ssa
    }

    pub(crate) fn certified_render_context(&self) -> Option<CertifiedRenderContext<'_>> {
        Some(CertifiedRenderContext::new(
            self.prepared_ssa()?,
            self.inputs.render_facts()?,
        ))
    }

    pub(crate) fn certified_render_plan<'b>(
        &'b self,
        proof: CertifiedRenderContext<'b>,
    ) -> Option<CertifiedRenderPlan<'b>> {
        Some(CertifiedRenderPlan::new(
            self.inputs.function_facts,
            self.prepared_semantic_view()?,
            proof,
        ))
    }

    pub(crate) fn certified_residual_comment(&self, reason: impl Into<String>) -> CStmt {
        CStmt::Comment(format!("r2sleigh residual: {}", reason.into()))
    }

    pub(super) fn certified_loop_carrier_expr_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<CExpr> {
        let r2types::CertifiedEntity::LoopCarrier { .. } = self
            .certified_render_context()?
            .render_facts
            .loop_carrier_for_value(value)?
        else {
            return None;
        };
        match self.planned_value_expr(value) {
            Ok(expr @ CExpr::Var(_)) => Some(expr),
            Ok(_) => {
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                None
            }
            Err(error) => {
                self.retain_first_observation_error(error);
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                None
            }
        }
    }

    pub(super) fn certified_memory_result_expr_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<CExpr> {
        self.certified_render_context()?
            .exact_memory_read_for_value(value)?;
        match self.planned_value_expr(value) {
            Ok(expr @ CExpr::Var(_)) => Some(expr),
            Ok(_) => None,
            Err(error) => {
                self.retain_first_observation_error(error);
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                None
            }
        }
    }

    pub(crate) fn certified_callsite_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&r2types::CallsiteArgumentFacts> {
        self.inputs
            .callsite_facts()?
            .arguments_for_site(r2types::CallsiteKey {
                block_addr,
                op_index: op_idx,
            })
    }

    pub(crate) fn certified_call_render_fact_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&r2types::CallsiteRenderFact> {
        self.inputs
            .call_render_facts()?
            .fact_for_site(r2types::CallsiteKey {
                block_addr,
                op_index: op_idx,
            })
    }

    pub(crate) fn certified_memory_access_for_current_op(
        &self,
        is_write: bool,
    ) -> Option<&r2types::MemoryAccessRenderFact> {
        let (block_addr, op_idx) = self.current_source_op_site()?;
        self.certified_render_context()?
            .memory_access_for_op(block_addr, op_idx, is_write)
    }

    pub(crate) fn certified_return_for_normalized_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&ReturnValueRenderFact> {
        let (block_addr, op_idx) = self.source_op_site_for_normalized_op(block_addr, op_idx)?;
        self.certified_render_context()?
            .return_for_op(block_addr, op_idx)
    }

    fn source_return_boundary_for_normalized_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<(r2ssa::InstId, &r2ssa::SourceReturnBoundaryFact)> {
        let source_inst = self.source_inst_for_normalized_op(block_addr, op_idx)?;
        let boundary = self
            .prepared_ssa()?
            .facts()
            .boundaries
            .returns
            .get(&source_inst)?;
        Some((source_inst, boundary))
    }

    fn certified_expr_for_prepared_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if var.is_const() {
            return self.certified_const_expr(var);
        }
        let value = self.prepared_value_id_for_var(var)?;
        self.certified_structural_expr_for_value(value, depth + 1, visited)
    }

    fn certified_structural_expr_for_value(
        &self,
        value: r2ssa::ValueId,
        depth: u32,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if let Some(expr) = self.certified_loop_carrier_expr_for_value(value) {
            return Some(expr);
        }
        if let Some(expr) = self.certified_memory_result_expr_for_value(value) {
            return Some(expr);
        }
        if !visited.insert(value) {
            return None;
        }

        let result = (|| {
            let prepared = self.prepared_ssa()?;
            let var = prepared.value_var(value)?;
            if var.is_const() {
                return self.certified_const_expr(var);
            }
            // A value the callee returned used to render as the call itself,
            // because the result had no name to render as. Where the call site
            // owns the result it has one now, and every use that re-rendered
            // the call was a second evaluation of it -- which is what the
            // single-evaluation check refuses.
            if let Some(result) = prepared.call_result_certificate_for_value(value)
                && result.relation.is_identity()
            {
                let site = (result.block_addr, result.op_index);
                if !self.call_site_assigns_its_own_result(site) {
                    return self.certified_call_result_expr_for_value(value);
                }
            }
            let expression_renderable = self
                .certified_render_context()
                .is_some_and(|proof| proof.expression_is_renderable(value));
            if var.version == 0 && var.is_register() {
                if !expression_renderable {
                    return None;
                }
                if let Some(expr) = self.certified_parameter_expr_for_value(value) {
                    return Some(expr);
                }
                if self.stable_semantic_ids_are_required() {
                    return None;
                }
                self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                return None;
            }

            let inst_id = prepared.graph().def_inst(value)?;
            let inst = prepared.graph().inst(inst_id)?;
            let transparent_value_forward = matches!(
                &inst.payload,
                r2ssa::InstPayload::Op(
                    SSAOp::Copy { .. }
                        | SSAOp::New { .. }
                        | SSAOp::Cast { .. }
                        | SSAOp::Subpiece { .. }
                        | SSAOp::IntZExt { .. }
                        | SSAOp::IntSExt { .. }
                        | SSAOp::Trunc { .. }
                )
            );
            let is_memory_load =
                matches!(&inst.payload, r2ssa::InstPayload::Op(SSAOp::Load { .. }));
            if !expression_renderable && !is_memory_load && !transparent_value_forward {
                return None;
            }
            match &inst.payload {
                r2ssa::InstPayload::Phi { predecessors } => {
                    if let Some(guarded) = self
                        .certified_render_context()
                        .and_then(|render| render.render_facts.guarded_phi_for_value(value))
                    {
                        let expected_sources = inst
                            .inputs
                            .iter()
                            .copied()
                            .map(r2ssa::SemanticId::expression)
                            .collect::<BTreeSet<_>>();
                        let rendered_sources = guarded
                            .when_true
                            .sources
                            .iter()
                            .chain(&guarded.when_false.sources)
                            .copied()
                            .collect::<BTreeSet<_>>();
                        let r2ssa::SemanticId::Predicate(predicate) = guarded.predicate else {
                            return None;
                        };
                        let r2ssa::SemanticId::Expression(when_true) = guarded.when_true.rendered
                        else {
                            return None;
                        };
                        let r2ssa::SemanticId::Expression(when_false) = guarded.when_false.rendered
                        else {
                            return None;
                        };
                        if expected_sources != rendered_sources
                            || guarded.when_true.sources.is_empty()
                            || guarded.when_false.sources.is_empty()
                        {
                            return None;
                        }
                        return Some(CExpr::Ternary {
                            cond: Box::new(self.certified_predicate_expr_for_id(predicate)?),
                            then_expr: Box::new(self.certified_structural_expr_for_value(
                                when_true,
                                depth + 1,
                                visited,
                            )?),
                            else_expr: Box::new(self.certified_structural_expr_for_value(
                                when_false,
                                depth + 1,
                                visited,
                            )?),
                        });
                    }
                    let compute_latch = |pred_addr: u64| {
                        self.control_facts().and_then(|facts| {
                            facts
                                .loops
                                .values()
                                .find_map(|fact| fact.latches.contains(&pred_addr).then_some(true))
                        })
                    };
                    let mut rendered: Vec<(Option<bool>, CExpr)> = Vec::new();
                    for (i, input) in inst.inputs.iter().enumerate() {
                        let Some(expr) =
                            self.certified_structural_expr_for_value(*input, depth + 1, visited)
                        else {
                            continue;
                        };
                        let is_latch = predecessors
                            .get(i)
                            .and_then(|pred_id| prepared.graph().block(*pred_id))
                            .map(|block| block.addr)
                            .and_then(compute_latch)
                            .unwrap_or(false);
                        rendered.push((Some(is_latch), expr));
                    }
                    let latch_exprs: Vec<_> = rendered
                        .iter()
                        .filter(|(is_latch, _)| is_latch.unwrap_or(false))
                        .map(|(_, expr)| expr)
                        .collect();
                    let unique_exprs: Vec<_> = rendered.iter().map(|(_, expr)| expr).fold(
                        Vec::<&CExpr>::new(),
                        |mut acc, expr| {
                            if !acc.contains(&expr) {
                                acc.push(expr);
                            }
                            acc
                        },
                    );
                    if latch_exprs.len() == 1 {
                        Some(latch_exprs[0].clone())
                    } else if unique_exprs.len() == 1 {
                        Some(unique_exprs[0].clone())
                    } else {
                        None
                    }
                }
                r2ssa::InstPayload::Op(op) => match op {
                    SSAOp::Copy { src, .. } => {
                        self.certified_expr_for_prepared_var(src, depth + 1, visited)
                    }
                    SSAOp::Load { addr: _, .. } => {
                        let (block_addr, op_idx) = prepared.inst_op_site(inst_id)?;
                        let fact = self
                            .certified_render_context()?
                            .memory_access_for_op(block_addr, op_idx, false)?;
                        if fact.value != Some(value) {
                            return None;
                        }
                        let rendered = self.render_certified_memory_expr_for_fact(
                            fact,
                            type_from_size(fact.width),
                        )?;
                        let obligations = self.exact_effect_obligations_for_source_memory(
                            EffectOccurrenceKind::MemoryRead,
                            block_addr,
                            op_idx,
                            fact.space,
                            Some(fact.address),
                            fact.value,
                        );
                        Some(self.observe_effect_expr(&obligations, rendered))
                    }
                    SSAOp::IntAdd { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Add, a, b, depth, visited)
                    }
                    SSAOp::IntSub { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Sub, a, b, depth, visited)
                    }
                    SSAOp::IntMult { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Mul, a, b, depth, visited)
                    }
                    SSAOp::IntDiv { a, b, .. } | SSAOp::IntSDiv { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Div, a, b, depth, visited)
                    }
                    SSAOp::IntRem { a, b, .. } | SSAOp::IntSRem { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Mod, a, b, depth, visited)
                    }
                    SSAOp::IntAnd { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitAnd, a, b, depth, visited)
                    }
                    SSAOp::IntOr { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitOr, a, b, depth, visited)
                    }
                    SSAOp::IntXor { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitXor, a, b, depth, visited)
                    }
                    SSAOp::IntLeft { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Shl, a, b, depth, visited)
                    }
                    SSAOp::IntRight { a, b, .. } | SSAOp::IntSRight { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Shr, a, b, depth, visited)
                    }
                    SSAOp::IntEqual { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Eq, a, b, depth, visited)
                    }
                    SSAOp::IntNotEqual { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Ne, a, b, depth, visited)
                    }
                    SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Lt, a, b, depth, visited)
                    }
                    SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Le, a, b, depth, visited)
                    }
                    SSAOp::BoolAnd { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::And, a, b, depth, visited)
                    }
                    SSAOp::BoolOr { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Or, a, b, depth, visited)
                    }
                    SSAOp::BoolXor { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitXor, a, b, depth, visited)
                    }
                    SSAOp::IntNegate { src, .. } => self
                        .certified_expr_for_prepared_var(src, depth + 1, visited)
                        .map(|expr| CExpr::unary(UnaryOp::Neg, expr)),
                    SSAOp::IntNot { src, .. } => self
                        .certified_expr_for_prepared_var(src, depth + 1, visited)
                        .map(|expr| CExpr::unary(UnaryOp::BitNot, expr)),
                    SSAOp::BoolNot { src, .. } => self
                        .certified_expr_for_prepared_var(src, depth + 1, visited)
                        .map(|expr| CExpr::unary(UnaryOp::Not, expr)),
                    SSAOp::Select {
                        cond,
                        if_true,
                        if_false,
                        ..
                    } => {
                        let cond_value = self.prepared_value_id_for_var(cond)?;
                        if let Some(truth) =
                            self.certified_value_truth_in_current_control_domain(cond_value)
                        {
                            return self.certified_expr_for_prepared_var(
                                if truth { if_true } else { if_false },
                                depth + 1,
                                visited,
                            );
                        }
                        Some(CExpr::Ternary {
                            cond: Box::new(self.certified_expr_for_prepared_var(
                                cond,
                                depth + 1,
                                visited,
                            )?),
                            then_expr: Box::new(self.certified_expr_for_prepared_var(
                                if_true,
                                depth + 1,
                                visited,
                            )?),
                            else_expr: Box::new(self.certified_expr_for_prepared_var(
                                if_false,
                                depth + 1,
                                visited,
                            )?),
                        })
                    }
                    SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src }
                    | SSAOp::Cast { dst, src } => {
                        let expr = self.certified_expr_for_prepared_var(src, depth + 1, visited)?;
                        let source_already_matches_return = depth == 0
                            && dst.size > src.size
                            // 64 is what `CType::bits` assumed for a pointer
                            // before the two type models were folded together.
                            // The fold context carries no target width, so the
                            // assumption is kept here rather than silently
                            // changed; it only matters for a pointer return.
                            && self
                                .inputs
                                .function_return_type
                                .and_then(|ty| ty.bits(64))
                                == Some(src.size.saturating_mul(8));
                        Some(if source_already_matches_return {
                            expr
                        } else {
                            CExpr::cast(type_from_size(dst.size), expr)
                        })
                    }
                    SSAOp::Subpiece { dst, src, offset } => {
                        let expr = self.certified_expr_for_prepared_var(src, depth + 1, visited)?;
                        if *offset == 0 {
                            Some(CExpr::cast(uint_type_from_size(dst.size), expr))
                        } else {
                            let shift_bits = offset.saturating_mul(8);
                            let shifted = CExpr::binary(
                                BinaryOp::Shr,
                                CExpr::cast(uint_type_from_size(src.size), expr),
                                CExpr::IntLit(shift_bits as i64),
                            );
                            Some(CExpr::cast(uint_type_from_size(dst.size), shifted))
                        }
                    }
                    _ => None,
                },
            }
        })();

        visited.remove(&value);
        result
    }

    fn certified_value_truth_in_current_control_domain(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<bool> {
        let block_addr = self.current_block_addr.get()?;
        let facts = self.control_facts()?;
        if !facts
            .control_domain_for_block(block_addr)
            .is_some_and(|domain| domain.complete)
        {
            return None;
        }
        let target_compare = self.certified_compare_for_value(value);
        let mut proven = None;
        for assumption in facts.assumptions_for_block(block_addr) {
            let Some(predicate) = facts
                .branch_predicates
                .values()
                .find(|predicate| predicate.id == assumption.predicate)
            else {
                continue;
            };
            let implied = if predicate.condition == value {
                Some(assumption.truth)
            } else {
                let Some(target_compare) = target_compare else {
                    continue;
                };
                let Some(comparison) = predicate.comparison.as_ref() else {
                    continue;
                };
                let Some(predicate_compare) = self.certified_canonical_compare(
                    comparison.kind,
                    comparison.lhs,
                    comparison.rhs,
                ) else {
                    continue;
                };
                certified_compare_truth_relation(target_compare, predicate_compare)
                    .map(|same_truth| assumption.truth == same_truth)
            };
            let Some(implied) = implied else {
                continue;
            };
            if proven.is_some_and(|existing| existing != implied) {
                return None;
            }
            proven = Some(implied);
        }
        proven
    }

    fn certified_compare_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<(r2ssa::CompareKind, r2ssa::SemanticId, r2ssa::SemanticId)> {
        let prepared = self.prepared_ssa()?;
        let inst = prepared.graph().inst(prepared.graph().def_inst(value)?)?;
        let r2ssa::InstPayload::Op(op) = &inst.payload else {
            return None;
        };
        let (kind, lhs, rhs) = match op {
            SSAOp::IntEqual { a, b, .. } => (r2ssa::CompareKind::Equal, a, b),
            SSAOp::IntNotEqual { a, b, .. } => (r2ssa::CompareKind::NotEqual, a, b),
            SSAOp::IntLess { a, b, .. } => (r2ssa::CompareKind::Less, a, b),
            SSAOp::IntSLess { a, b, .. } => (r2ssa::CompareKind::SignedLess, a, b),
            SSAOp::IntLessEqual { a, b, .. } => (r2ssa::CompareKind::LessEqual, a, b),
            SSAOp::IntSLessEqual { a, b, .. } => (r2ssa::CompareKind::SignedLessEqual, a, b),
            _ => return None,
        };
        Some((
            kind,
            self.certified_canonical_value(lhs)?,
            self.certified_canonical_value(rhs)?,
        ))
    }

    fn certified_canonical_compare(
        &self,
        kind: r2ssa::CompareKind,
        lhs: r2ssa::ValueId,
        rhs: r2ssa::ValueId,
    ) -> Option<(r2ssa::CompareKind, r2ssa::SemanticId, r2ssa::SemanticId)> {
        let prepared = self.prepared_ssa()?;
        Some((
            kind,
            self.certified_canonical_value(prepared.value_var(lhs)?)?,
            self.certified_canonical_value(prepared.value_var(rhs)?)?,
        ))
    }

    fn certified_canonical_value(&self, var: &SSAVar) -> Option<r2ssa::SemanticId> {
        let prepared = self.prepared_ssa()?;
        let mut value = self.prepared_value_id_for_var(var)?;
        let mut visited = BTreeSet::new();
        for _ in 0..32 {
            if !visited.insert(value) {
                return None;
            }
            if let Some(reload) = prepared.stack_reload_certificate_for_value(value)
                && reload.canonical_source != value
            {
                value = reload.canonical_source;
                continue;
            }
            let current = prepared.value_var(value)?;
            if current.version == 0 && current.is_register() {
                let certified = self
                    .certified_render_context()?
                    .render_facts
                    .certified_expr_for_value(value)?;
                let mut parameters = certified
                    .bindings
                    .iter()
                    .filter(|binding| matches!(binding, r2ssa::SemanticId::Parameter(_)));
                let parameter = *parameters.next()?;
                if parameters.next().is_none() {
                    return Some(parameter);
                }
                return None;
            }
            if let Some(object) = prepared.object_for_var(current, r2il::SpaceId::Ram) {
                let identity = r2ssa::SemanticId::stack_slot(object);
                if self
                    .certified_render_context()?
                    .render_facts
                    .certified_entities
                    .contains_key(&identity)
                {
                    return Some(identity);
                }
            }
            let Some(root) = self.prepared_canonical_value_root(current) else {
                return Some(r2ssa::SemanticId::expression(value));
            };
            let Some(root_value) = self.prepared_value_id_for_var(&root) else {
                return Some(r2ssa::SemanticId::expression(value));
            };
            if root_value == value {
                return Some(r2ssa::SemanticId::expression(value));
            }
            value = root_value;
        }
        None
    }

    fn certified_binary_return_expr(
        &self,
        op: BinaryOp,
        a: &SSAVar,
        b: &SSAVar,
        depth: u32,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        Some(CExpr::binary(
            op,
            self.certified_expr_for_prepared_var(a, depth + 1, visited)?,
            self.certified_expr_for_prepared_var(b, depth + 1, visited)?,
        ))
    }

    fn certified_call_result_fact_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&r2types::CallResultFact> {
        let fact = self.inputs.call_result_facts()?.result_for_value(value)?;
        (fact.value == value).then_some(fact)
    }

    pub(crate) fn certified_call_result_expr_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<CExpr> {
        let prepared = self.prepared_ssa()?;
        let prepared_result = prepared.call_result_certificate_for_value(value)?;
        let fact = self.certified_call_result_fact_for_value(value)?;
        if fact.call_site_id != prepared_result.call_site
            || fact.relation != prepared_result.relation
            || !fact.relation.is_identity()
        {
            return None;
        }
        let binding = r2ssa::SemanticId::call(fact.call_site_id);
        let certified = self
            .certified_render_context()?
            .render_facts
            .certified_expr_for_value(value)?;
        if !certified.fact.renderable || !certified.bindings.contains(&binding) {
            return None;
        }
        let source_call = (fact.callsite.block_addr, fact.callsite.op_index);
        if let Some(owner) = self.certified_assigned_call_result_owner_expr_for_source(source_call)
        {
            return Some(owner);
        }
        if let r2ssa::ReturnCarrier::StackSlot { object, .. } = &fact.carrier {
            let stack_binding = r2ssa::SemanticId::stack_slot(*object);
            if !certified.bindings.contains(&stack_binding) {
                return None;
            }
            return self.certified_stack_var_expr_for_object(*object);
        }
        self.synthesized_call_expr_for_source_call(source_call)
    }

    /// The canonical value behind a variable, for recording what a render owns.
    fn value_id_for_rendered_op(&self, var: &SSAVar) -> Option<ValueId> {
        self.inputs
            .prepared_ssa
            .and_then(|prepared| prepared.graph().value_id_for_var(var))
    }

    pub(crate) fn prepared_semantic_view(&self) -> Option<&analysis::PreparedSemanticView> {
        if let Some(view) = self.inputs.prepared_semantic_view {
            return Some(view);
        }

        #[cfg(not(test))]
        return None;

        #[cfg(test)]
        {
            let prepared = self.inputs.prepared_ssa?;
            Some(self.prepared_semantic_view_cache.get_or_init(|| {
                analysis::PreparedSemanticView::build(
                    &self.symbols,
                    analysis::PreparedSemanticViewInputs {
                        prepared,
                        stack_slots: self.inputs.stack_slots,
                        visible_bindings: self.inputs.visible_bindings,
                        function_facts: self.inputs.function_facts,
                        #[cfg(test)]
                        certified_rendering_required: false,
                    },
                )
            }))
        }
    }

    pub(crate) fn control_facts(&self) -> Option<&r2types::FunctionControlFacts> {
        self.inputs.control_facts()
    }

    pub(crate) fn prepared_decompile_prep_facts(&self) -> Option<&DecompilePrepFacts> {
        self.prepared_ssa()
            .and_then(|prepared| prepared.function().decompile_prep_facts())
    }

    pub(crate) fn prepared_call_view_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&analysis::PreparedCallView> {
        self.prepared_semantic_view()
            .and_then(|view| view.call_view_for_site((block_addr, op_idx)))
    }

    pub(crate) fn prepared_var_for_value_id(&self, value_id: r2ssa::ValueId) -> Option<&SSAVar> {
        self.inputs.prepared_ssa?.value_var(value_id)
    }

    pub(crate) fn prepared_value_id_for_var(&self, var: &SSAVar) -> Option<r2ssa::ValueId> {
        self.inputs.prepared_ssa?.graph().value_id_for_var(var)
    }

    pub(crate) fn prepared_canonical_value_root(&self, var: &SSAVar) -> Option<SSAVar> {
        let facts = self.prepared_decompile_prep_facts()?;
        let mut current = var.clone();
        for _ in 0..32 {
            let Some(next) = facts.canonical_root_of(&current) else {
                break;
            };
            if next == &current {
                break;
            }
            current = next.clone();
        }
        Some(current)
    }

    pub(crate) fn callee_identity_for_direct_target(&self, addr: u64) -> CalleeIdentity {
        self.inputs
            .callee_resolution()
            .and_then(|facts| facts.identity_for_direct_addr(addr))
            .cloned()
            .unwrap_or_else(|| CalleeIdentity::from_name(&format!("const:{addr:x}")))
    }
    pub(crate) fn call_result_exprs_map(&self) -> &std::collections::BTreeMap<(u64, usize), CExpr> {
        &self.use_info().call_result_exprs
    }
    /// Fixture-only spelling constructor. Native rendering has no generic
    /// identifier mint: program variables come from BindingNameResolution and
    /// external names use `CExpr::External`.
    #[cfg(test)]
    #[track_caller]
    pub(crate) fn name_ref(&self, name: &str) -> CExpr {
        CExpr::Var(crate::symbol::declare(&self.symbols, name))
    }

    /// How a reference is spelled.
    ///
    /// Returns an owned name so the borrow ends here. A caller that held one
    /// while building an expression would deadlock against the mint, and
    /// building expressions is what these callers do next.
    pub(crate) fn spelling(&self, id: crate::symbol::SymbolId) -> std::rc::Rc<str> {
        self.symbols.borrow().spelling(id)
    }

    #[cfg(test)]
    pub fn set_function_names(&mut self, names: HashMap<u64, String>) {
        self.inputs.function_names = Box::leak(Box::new(names));
    }

    #[cfg(test)]
    pub fn set_known_function_signatures<T>(&mut self, signatures: HashMap<String, T>)
    where
        T: Into<r2types::FunctionType>,
    {
        let normalized = signatures
            .into_iter()
            .map(|(name, sig)| (normalize_callee_name(&name), sig.into()))
            .collect::<HashMap<_, _>>();
        let ctx = r2types::CalleeIdentityContext {
            #[cfg(test)]
            function_names: self.inputs.function_names,
            #[cfg(test)]
            symbols: self.inputs.binary_symbols,
            callee_facts: self.inputs.callee_facts(),
            known_function_signatures: &normalized,
        };
        let mut resolution = self.inputs.callee_resolution().cloned().unwrap_or_default();
        resolution.index_context(&ctx);
        let mut function_facts = self.inputs.function_facts.clone();
        function_facts.set_callee_resolution(resolution);
        self.inputs.function_facts = Box::leak(Box::new(function_facts));
    }

    /// Analyze multiple blocks (for function-level folding).
    #[cfg(test)]
    pub(crate) fn analyze_blocks(&mut self, blocks: &[SSABlock]) {
        let execution = r2ssa::SsaExecutionControl::default();
        let control =
            crate::DecompileWorkControl::new(&execution, crate::DecompileWorkPhase::Structuring);
        self.analyze_blocks_with_control(blocks, control)
            .expect("default decompiler work control cannot stop");
    }

    pub(crate) fn analyze_blocks_with_control(
        &mut self,
        blocks: &[SSABlock],
        control: crate::DecompileWorkControl<'_>,
    ) -> Result<(), analysis::PreparedRuntimeFactsError> {
        control.poll()?;
        // A fact the analysis could not key is a fact it lost. It used to be
        // counted and discarded, which reads as accounting while leaving a
        // table quietly incomplete and nothing downstream able to tell. The
        // count is zero on every corpus configuration, so refusing here costs
        // nothing and turns a silent loss into a stated one.
        if self.inputs.prepared_ssa.is_some()
            && let Some(kind) = self.use_info().dropped_unkeyed_fact
        {
            if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                eprintln!("analysis dropped an unkeyed {kind} fact");
            }
            return Err(analysis::PreparedRuntimeFactsError::Lowering(
                crate::analysis::lower::OpLoweringRefusal::missing_program_variable(),
            ));
        }
        let symbols = &self.symbols;

        if let Some(prepared) = self.inputs.prepared_ssa {
            let prepared_view = self
                .prepared_semantic_view()
                .cloned()
                .expect("prepared folding requires one prebuilt semantic view");
            let normalization_origins = self
                .inputs
                .normalization_origins
                .expect("prepared folding requires sealed normalization origins");
            self.state.analysis_ctx = analysis::build_prepared_runtime_facts_with_control(
                symbols,
                blocks,
                prepared,
                &prepared_view,
                normalization_origins,
                control,
            )?;
            return Ok(());
        }

        // There is no second, renderer-owned analysis path. Without the exact
        // prepared source artifact, operation lowering has no authority for
        // machine projections or value identities and must refuse in release
        // builds just as it does in debug builds.
        Err(OpLoweringRefusal::missing_machine_projection().into())
    }

    pub(super) fn synthesized_call_expr_for_source_call(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        self.certified_synthesized_call_expr_for_source_call(source_call)
            .map(|call| call.expr)
    }

    pub(super) fn certified_synthesized_call_expr_for_source_call(
        &self,
        source_call: (u64, usize),
    ) -> Option<CertifiedCallExpr> {
        let (block_addr, op_idx) = source_call;
        let cert = self.certified_callsite_for_op(block_addr, op_idx)?;
        let render_fact = self.certified_call_render_fact_for_op(block_addr, op_idx)?;
        if matches!(
            render_fact.disposition,
            r2types::CallsiteRenderDisposition::Suppressed
                | r2types::CallsiteRenderDisposition::Residualized
        ) {
            return None;
        }
        let proof = self.certified_render_context()?;
        let target_is_certified =
            proof.expression_is_renderable(cert.target) || cert.direct_target.is_some();
        if !target_is_certified {
            return None;
        }
        let func = self.retain_lowering_result(self.resolve_call_target_for_site(
            block_addr,
            op_idx,
            self.prepared_var_for_value_id(cert.target)?,
        ))?;
        let certified_args = match self.certified_call_args_for_site(block_addr, op_idx) {
            Ok(args) => args,
            Err(refusal) => {
                self.retain_first_lowering_refusal(refusal);
                return None;
            }
        };
        let func = self
            .resolved_callee_identity_expr_for_site(block_addr, op_idx)
            .unwrap_or(func);
        let expr = CExpr::call_at(source_call, func, certified_args.args);
        Some(CertifiedCallExpr {
            expr,
            target: cert.target,
            values: certified_args.values,
        })
    }

    /// A definition may disappear only when the sealed exact-value plan owns
    /// the corresponding inline proof. Legacy use counts, expression shape,
    /// register class, and cached spellings are not admission evidence.
    fn should_inline(&self, var: &SSAVar) -> bool {
        let Some(value) = self.prepared_value_id_for_var(var) else {
            return false;
        };
        let Some(names) = self.inputs.binding_names else {
            return false;
        };
        matches!(
            names.disposition_for_value(value),
            Some(crate::binding_plan::ValueDisposition::Inline { .. })
        )
    }

    pub fn is_dead(&self, var: &SSAVar) -> bool {
        let Some(value) = self.prepared_value_id_for_var(var) else {
            return false;
        };
        self.inputs.binding_names.is_some_and(|names| {
            matches!(
                names.disposition_for_value(value),
                Some(crate::binding_plan::ValueDisposition::Elided { .. })
            )
        })
    }

    pub fn get_expr(&self, var: &SSAVar) -> OpLoweringResult<CExpr> {
        let answer = self.get_expr_inner(var);
        // Trace the sealed exact-value answer, never a spelling-recovered
        // definition candidate.
        if let Ok(want) = std::env::var("R2SLEIGH_TRACE_NAME")
            && var.display_name().eq_ignore_ascii_case(&want)
        {
            eprintln!("GETEXPR key={} answer={answer:?}", var.display_name());
        }
        answer
    }

    pub(super) fn retain_lowering_result<T>(&self, result: OpLoweringResult<T>) -> Option<T> {
        match result {
            Ok(value) => Some(value),
            Err(refusal) => {
                self.retain_first_lowering_refusal(refusal);
                None
            }
        }
    }

    fn get_expr_inner(&self, var: &SSAVar) -> OpLoweringResult<CExpr> {
        let Some(value) = self.prepared_value_id_for_var(var) else {
            return Err(OpLoweringRefusal::missing_program_variable());
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(OpLoweringRefusal::missing_program_variable());
        };
        if names.disposition_for_value(value).is_none() {
            return Err(OpLoweringRefusal::missing_program_variable());
        }
        let expr = match self.planned_value_expr(value) {
            Ok(expr) => expr,
            Err(error) => {
                self.retain_first_observation_error(error);
                return Err(OpLoweringRefusal::missing_program_variable());
            }
        };
        Ok(expr)
    }

    fn op_to_expr_impl(&self, op: &SSAOp, frame: &LowerFrame) -> OpLoweringResult<Option<CExpr>> {
        if let SSAOp::Copy { src, .. } = op {
            return Ok(Some(self.observed_input(frame, 0, self.get_expr(src)?)));
        }

        if let Some(stmt) = self.op_to_stmt_impl(op, frame)? {
            return Ok(match Self::lowered_from_stmt(stmt) {
                LoweredOp::Assign { rhs, .. } => Some(rhs),
                LoweredOp::FinalizedStmt(CStmt::Expr(CExpr::Binary {
                    op: BinaryOp::Assign,
                    right,
                    ..
                })) => Some(*right),
                LoweredOp::FinalizedStmt(CStmt::Expr(expr)) => Some(expr),
                LoweredOp::FinalizedStmt(CStmt::Return(Some(expr))) => Some(expr),
                LoweredOp::FinalizedStmt(_) => None,
                LoweredOp::Expr(expr) => Some(expr),
                LoweredOp::None => None,
            });
        }

        Ok(match op {
            // These ops do not lower to statements but still need expression form.
            SSAOp::CBranch { .. } => {
                let block_addr = self
                    .current_block_addr
                    .get()
                    .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
                let op_idx = self
                    .current_op_idx
                    .get()
                    .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
                Some(self.planned_input_expr_at(block_addr, op_idx, 1)?)
            }
            SSAOp::Return { .. } => {
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
            _ => None,
        })
    }

    fn is_literal_zero_expr(&self, expr: &CExpr) -> bool {
        matches!(expr.unobserved(), CExpr::IntLit(0) | CExpr::UIntLit(0))
    }

    fn is_one_expr(&self, expr: &CExpr) -> bool {
        matches!(expr.unobserved(), CExpr::IntLit(1) | CExpr::UIntLit(1))
    }

    fn is_all_ones_mask_expr(&self, expr: &CExpr, width_bytes: u32) -> bool {
        if width_bytes == 0 || width_bytes > 8 {
            return false;
        }
        let bits = width_bytes.saturating_mul(8);
        let mask = if bits == 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };

        match expr.unobserved() {
            CExpr::UIntLit(v) => *v == mask,
            CExpr::IntLit(v) => *v == -1 || u64::try_from(*v).map(|n| n == mask).unwrap_or(false),
            CExpr::Paren(inner) => self.is_all_ones_mask_expr(inner, width_bytes),
            CExpr::Cast { expr: inner, .. } => self.is_all_ones_mask_expr(inner, width_bytes),
            _ => false,
        }
    }

    fn identity_simplify_binary(
        &self,
        op: BinaryOp,
        left: CExpr,
        right: CExpr,
        width_bytes: Option<u32>,
    ) -> CExpr {
        self.identity_simplify_binary_semantic(op, left, right, width_bytes)
    }

    fn finish_nonpositional_identity_rewrite(
        op: BinaryOp,
        left: CExpr,
        right: CExpr,
        replacement: Option<CExpr>,
    ) -> CExpr {
        let source = CExpr::binary(op, left, right);
        match replacement {
            Some(replacement) if !source.transparently_eq(&replacement) => replacement,
            Some(_) | None => source,
        }
    }

    /// Simplify one binary expression only when it owns no exact source
    /// occurrences.
    ///
    /// A constant fold or identity rewrite is semantically valid but does not
    /// prove that an eliminated [`UseSite`](r2ssa::UseSite) has a non-rendered
    /// disposition. Moving its marker onto the replacement would falsely call
    /// the replacement that exact occurrence. Native audited lowering therefore
    /// keeps the source operation intact; marker-free presentation paths may
    /// still apply the ordinary simplifier.
    fn identity_simplify_binary_semantic(
        &self,
        op: BinaryOp,
        left: CExpr,
        right: CExpr,
        width_bytes: Option<u32>,
    ) -> CExpr {
        if crate::ast::expr_has_render_observations(&left)
            || crate::ast::expr_has_render_observations(&right)
        {
            return CExpr::binary(op, left, right);
        }
        if let Some(value) = self.literal_binary_value(op, &left, &right) {
            return CExpr::IntLit(value);
        }
        match op {
            BinaryOp::Sub if self.is_literal_zero_expr(&right) => left,
            BinaryOp::Sub => {
                let replacement = self.simplify_linear_subtraction(
                    &left.clone_without_render_observations(),
                    &right.clone_without_render_observations(),
                );
                Self::finish_nonpositional_identity_rewrite(op, left, right, replacement)
            }
            BinaryOp::Add => {
                if self.is_literal_zero_expr(&right) {
                    left
                } else if self.is_literal_zero_expr(&left) {
                    right
                } else {
                    let replacement = self.simplify_linear_addition(
                        &left.clone_without_render_observations(),
                        &right.clone_without_render_observations(),
                    );
                    Self::finish_nonpositional_identity_rewrite(op, left, right, replacement)
                }
            }
            BinaryOp::BitOr | BinaryOp::BitXor => {
                if op == BinaryOp::BitXor && left.transparently_eq(&right) {
                    CExpr::IntLit(0)
                } else if self.is_literal_zero_expr(&right) {
                    left
                } else if self.is_literal_zero_expr(&left) {
                    right
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Mul => {
                if self.is_one_expr(&right) {
                    left
                } else if self.is_one_expr(&left) {
                    right
                } else if let Some(coeff) = self.literal_to_i64(&right) {
                    let replacement = self
                        .simplify_linear_scale(&left.clone_without_render_observations(), coeff);
                    Self::finish_nonpositional_identity_rewrite(op, left, right, replacement)
                } else if let Some(coeff) = self.literal_to_i64(&left) {
                    let replacement = self
                        .simplify_linear_scale(&right.clone_without_render_observations(), coeff);
                    Self::finish_nonpositional_identity_rewrite(op, left, right, replacement)
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Div => {
                if self.is_one_expr(&right) {
                    left
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::BitAnd => {
                if let Some(width) = width_bytes {
                    if self.is_all_ones_mask_expr(&right, width) {
                        return left;
                    }
                    if self.is_all_ones_mask_expr(&left, width) {
                        return right;
                    }
                }
                CExpr::binary(op, left, right)
            }
            BinaryOp::Shl => {
                if self.is_literal_zero_expr(&right) {
                    left
                } else if let Some(shift) = self.literal_to_i64(&right)
                    && (0..=62).contains(&shift)
                {
                    let replacement = self.simplify_linear_scale(
                        &left.clone_without_render_observations(),
                        1i64 << shift,
                    );
                    Self::finish_nonpositional_identity_rewrite(op, left, right, replacement)
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Shr if self.is_literal_zero_expr(&right) => left,
            _ => CExpr::binary(op, left, right),
        }
    }

    fn literal_binary_value(&self, op: BinaryOp, left: &CExpr, right: &CExpr) -> Option<i64> {
        let left = self.literal_to_i64(left)?;
        let right = self.literal_to_i64(right)?;
        match op {
            BinaryOp::Add => left.checked_add(right),
            BinaryOp::Sub => left.checked_sub(right),
            BinaryOp::Mul => left.checked_mul(right),
            BinaryOp::Div => (right != 0).then(|| left.checked_div(right)).flatten(),
            BinaryOp::Mod => (right != 0).then(|| left.checked_rem(right)).flatten(),
            BinaryOp::BitAnd => Some(left & right),
            BinaryOp::BitOr => Some(left | right),
            BinaryOp::BitXor => Some(left ^ right),
            BinaryOp::Shl => {
                if !(0..=62).contains(&right) {
                    return None;
                }
                left.checked_mul(1i64 << right)
            }
            BinaryOp::Shr => {
                if !(0..=62).contains(&right) {
                    return None;
                }
                Some(left >> right)
            }
            _ => None,
        }
    }

    fn simplify_linear_subtraction(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let mut terms = Vec::new();
        let mut constant = 0i64;
        self.collect_linear_add_terms(left, 1, &mut terms, &mut constant)?;
        self.collect_linear_add_terms(right, -1, &mut terms, &mut constant)?;
        self.linear_expr_from_terms(terms, constant)
    }

    fn simplify_linear_scale(&self, expr: &CExpr, scale: i64) -> Option<CExpr> {
        let mut terms = Vec::new();
        let mut constant = 0i64;
        self.collect_linear_add_terms(expr, scale, &mut terms, &mut constant)?;
        self.linear_expr_from_terms(terms, constant)
    }

    fn simplify_linear_addition(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let mut terms = Vec::new();
        let mut constant = 0i64;
        self.collect_linear_add_terms(left, 1, &mut terms, &mut constant)?;
        self.collect_linear_add_terms(right, 1, &mut terms, &mut constant)?;
        self.linear_expr_from_terms(terms, constant)
    }

    fn linear_expr_from_terms(&self, mut terms: Vec<(CExpr, i64)>, constant: i64) -> Option<CExpr> {
        terms.retain(|(_, coeff)| *coeff != 0);
        terms.sort_by_key(|(term, _)| self.linear_term_order_key(term));

        let mut pieces: Vec<CExpr> = terms
            .into_iter()
            .map(|(term, coeff)| linear_coeff_expr(term, coeff))
            .collect::<Option<Vec<_>>>()?;
        if constant != 0 {
            pieces.push(CExpr::IntLit(constant));
        }

        let mut iter = pieces.into_iter();
        let first = iter.next().unwrap_or(CExpr::IntLit(0));
        Some(iter.fold(first, |acc, expr| CExpr::binary(BinaryOp::Add, acc, expr)))
    }

    fn collect_linear_add_terms(
        &self,
        expr: &CExpr,
        scale: i64,
        terms: &mut Vec<(CExpr, i64)>,
        constant: &mut i64,
    ) -> Option<()> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                self.collect_linear_add_terms(left, scale, terms, constant)?;
                self.collect_linear_add_terms(right, scale, terms, constant)
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                self.collect_linear_add_terms(left, scale, terms, constant)?;
                self.collect_linear_add_terms(right, scale.checked_neg()?, terms, constant)
            }
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if let Some(coeff) = self.literal_to_i64(right)
                    && let Some(term) = self.linear_atom_expr(left)
                {
                    return push_linear_term(terms, term, scale.checked_mul(coeff)?);
                }
                if let Some(coeff) = self.literal_to_i64(left)
                    && let Some(term) = self.linear_atom_expr(right)
                {
                    return push_linear_term(terms, term, scale.checked_mul(coeff)?);
                }
                None
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
                self.collect_linear_add_terms(
                    left,
                    scale.checked_mul(1i64 << shift)?,
                    terms,
                    constant,
                )
            }
            CExpr::IntLit(value) => {
                *constant = constant.checked_add(scale.checked_mul(*value)?)?;
                Some(())
            }
            CExpr::UIntLit(value) => {
                let value = i64::try_from(*value).ok()?;
                *constant = constant.checked_add(scale.checked_mul(value)?)?;
                Some(())
            }
            CExpr::Paren(inner) => self.collect_linear_add_terms(inner, scale, terms, constant),
            _ => {
                let term = self.linear_atom_expr(expr)?;
                push_linear_term(terms, term, scale)
            }
        }
    }

    fn linear_atom_expr(&self, expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::Var(name) if self.linear_var_is_integer_scalar(*name) => Some(expr.clone()),
            CExpr::Paren(inner) => self.linear_atom_expr(inner),
            CExpr::Cast { ty, expr: inner }
                if ty.is_integer() && self.linear_atom_expr(inner).is_some() =>
            {
                Some(expr.clone())
            }
            _ => None,
        }
    }

    fn linear_var_is_integer_scalar(&self, name: crate::symbol::SymbolId) -> bool {
        let _ = name;
        false
    }

    fn linear_term_order_key(&self, expr: &CExpr) -> (u8, usize, String) {
        match expr {
            CExpr::Var(name) => (
                0,
                self.param_rank_for_visible_name(&self.spelling(*name))
                    .unwrap_or(usize::MAX),
                self.spelling(*name).to_string(),
            ),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.linear_term_order_key(inner)
            }
            _ => (1, usize::MAX, format!("{expr:?}")),
        }
    }

    fn param_rank_for_visible_name(&self, name: &str) -> Option<usize> {
        let lower = name.to_ascii_lowercase();
        self.inputs
            .arch
            .arg_regs
            .iter()
            .enumerate()
            .find_map(|(idx, reg)| {
                let reg_lower = reg.to_ascii_lowercase();
                (lower == reg_lower).then_some(idx)
            })
    }

    /// The identity rules, for a caller outside the fold that renders expressions
    /// the fold never routed through a stored value.
    pub(crate) fn simplify_identities(&self, expr: CExpr) -> CExpr {
        self.identity_simplify_expr(expr)
    }

    /// Apply the identity rules bottom-up, so a rule reaches an identity that sits
    /// under a cast or inside a larger term rather than only at the top.
    fn identity_simplify_expr(&self, mut expr: CExpr) -> CExpr {
        for child in crate::single_evaluation::children_mut(&mut expr) {
            let taken = std::mem::replace(child, CExpr::IntLit(0));
            *child = self.identity_simplify_expr(taken);
        }
        match expr {
            CExpr::Binary { op, left, right } => {
                self.identity_simplify_binary_semantic(op, *left, *right, None)
            }
            other => other,
        }
    }

    fn assign_stmt(&self, lhs: CExpr, rhs: CExpr) -> Option<CStmt> {
        if self.inlined_definition.get() {
            // The result is read where it is computed, so there is nothing to
            // assign it to; the expression is the whole of the answer.
            return Some(CStmt::Expr(rhs));
        }
        // Both sides are exact occurrence projections. Identity-looking text
        // is not an elision proof: distinct SSA values may intentionally share
        // one rendered binding, and a write may still be an observable effect.
        Some(CStmt::Expr(CExpr::assign(lhs, rhs)))
    }

    fn assignment_lhs_expr(&self, _dst: &SSAVar) -> OpLoweringResult<CExpr> {
        if self.inlined_definition.get() {
            // Discarded by `assign_stmt` under the same flag. Asking the plan
            // for a symbol it deliberately withheld would refuse the lowering.
            return Ok(CExpr::IntLit(0));
        }
        match self.planned_current_output_expr() {
            Ok(Some(planned)) => Ok(planned),
            Ok(None) => Err(OpLoweringRefusal::missing_program_variable()),
            Err(error) => {
                self.retain_first_observation_error(error);
                Err(OpLoweringRefusal::missing_program_variable())
            }
        }
    }

    fn ptr_arith_expr(
        &self,
        frame: &LowerFrame,
        base: &SSAVar,
        index: &SSAVar,
        element_size: u32,
        is_sub: bool,
    ) -> OpLoweringResult<CExpr> {
        let base_expr = self.observed_input(frame, 0, self.get_expr(base)?);
        let index_expr = self.observed_input(frame, 1, self.get_expr(index)?);
        let scaled = if element_size <= 1 {
            index_expr
        } else {
            CExpr::binary(
                BinaryOp::Mul,
                index_expr,
                CExpr::IntLit(element_size as i64),
            )
        };
        let op = if is_sub { BinaryOp::Sub } else { BinaryOp::Add };
        Ok(CExpr::binary(op, base_expr, scaled))
    }

    fn looks_like_pointer(&self, expr: &CExpr) -> bool {
        if self.expr_type_hint(expr).is_some_and(|ty| {
            matches!(
                ty,
                CType::Pointer(_) | CType::Array(_, _) | CType::Struct(_) | CType::Union(_)
            )
        }) {
            return true;
        }

        match expr.unobserved() {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_) => true,
            CExpr::Subscript { .. } | CExpr::Member { .. } | CExpr::PtrMember { .. } => true,
            CExpr::Var(_) => false,
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => self.looks_like_pointer(left) || self.looks_like_pointer(right),
            _ => false,
        }
    }

    fn member_access_expr(&self, base_expr: CExpr, member: String) -> CExpr {
        let base_expr = self.canonical_member_base_expr(base_expr);
        match base_expr {
            CExpr::Subscript { .. } | CExpr::Member { .. } => CExpr::Member {
                base: Box::new(base_expr),
                member,
            },
            _ => CExpr::PtrMember {
                base: Box::new(base_expr),
                member,
            },
        }
    }

    fn canonical_member_base_expr(&self, base_expr: CExpr) -> CExpr {
        base_expr
    }

    /// The C type the emitted declaration gives the name this value renders as.
    ///
    /// This is not a hint and not a belief about what the value means. The
    /// binding plan seals a `declaration_type` per binding and `placement.rs`
    /// emits the declaration with exactly that type, so an operand spelled as
    /// that name has exactly this type in the program the compiler reads.
    ///
    /// A value the plan inlines has no declaration and so has no type here.
    /// That is an honest absence: the operand is an expression, not a name.
    /// The declared type of the object a value is bound to.
    ///
    /// The same fact `declared_type_for_var` reports, asked of a value rather
    /// than of a spelling, for the places that hold one -- a call result's
    /// carrier is named by its certificate, not by a variable.
    fn declared_type_for_value(&self, value: r2ssa::ValueId) -> Option<RecordedType> {
        let names = self.inputs.binding_names?;
        let crate::binding_plan::ValueDisposition::Bound { binding } =
            names.disposition_for_value(value)?
        else {
            return None;
        };
        Some(RecordedType::from_declaration(
            names.plan().binding(*binding)?.declaration_type().clone(),
        ))
    }

    fn declared_type_for_var(&self, var: &SSAVar) -> Option<RecordedType> {
        let value = self.prepared_value_id_for_var(var)?;
        let names = self.inputs.binding_names?;
        let crate::binding_plan::ValueDisposition::Bound { binding } =
            names.disposition_for_value(value)?
        else {
            return None;
        };
        Some(RecordedType::from_declaration(
            names.plan().binding(*binding)?.declaration_type().clone(),
        ))
    }

    /// The recorded type of an operand, for deciding whether a cast is needed.
    ///
    /// The declaration wins over the certified hint, because the two answer
    /// different questions and only one of them is about the emitted C. Every
    /// binding is declared at `CType::machine_bits`, i.e. unsigned, while
    /// `type_hint_for_var` reports what upstream proved the value *means* --
    /// signed, a pointer, a typedef. Deciding a cast from the meaning while
    /// the compiler reads the declaration is how a value declared `uint32_t`
    /// and believed `int32_t` reached a comparison with no cast and was
    /// compared unsigned, which is the shape of the sign-flag defect that made
    /// `crc32_bitwise` return a CRC of nothing while compiling cleanly.
    fn source_type_for_var(&self, var: &SSAVar) -> Option<RecordedType> {
        self.declared_type_for_var(var)
            .or_else(|| self.type_hint_for_var(var).map(RecordedType::from_certified_fact))
            .or_else(|| self.inline_expression_type_for_var(var))
    }

    /// The recorded type of the expression the plan inlines for this value.
    fn inline_expression_type_for_var(&self, var: &SSAVar) -> Option<RecordedType> {
        let value = self.prepared_value_id_for_var(var)?;
        let names = self.inputs.binding_names?;
        let crate::binding_plan::ValueDisposition::Inline { expr, .. } =
            names.disposition_for_value(value)?
        else {
            return None;
        };
        Some(RecordedType::from_inline_expression(
            names.inline_expr(*expr)?.ty(),
        ))
    }


    fn type_hint_for_var(&self, var: &SSAVar) -> Option<CType> {
        let value = self.prepared_value_id_for_var(var)?;
        let render = self.inputs.render_facts()?;
        let signature = self
            .inputs
            .function_facts
            .type_facts()
            .render_authorized_signature();
        let mut candidates = Vec::new();
        if let Some(slot) = render.exact_parameter_slot_for_value(value)
            && let Some(ty) = signature
                .and_then(|signature| signature.params.get(slot))
                .and_then(|parameter| parameter.ty.as_ref())
        {
            candidates.push(ty.clone());
        }
        if let Some(r2types::CertifiedEntity::LoopCarrier { ty: Some(ty), .. }) =
            render.loop_carrier_for_value(value)
        {
            candidates.push(ty.clone());
        }
        if let Some(memory) = self
            .certified_render_context()
            .and_then(|proof| proof.exact_memory_read_for_value(value))
            && let Some(ty) = render.memory_value_type(memory.access)
        {
            candidates.push(ty.clone());
        }
        if render.return_effects().any(|effect| effect.value == value)
            && let Some(ty) = signature.and_then(|signature| signature.ret_type.as_ref())
        {
            candidates.push(ty.clone());
        }
        let ty = candidates.first()?.clone();
        if candidates.iter().any(|candidate| *candidate != ty) {
            return None;
        }
        Some(ty)
    }

    pub(crate) fn should_materialize_call_result_at_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        self.certified_assigned_call_result_owner_expr_for_source(source_call)
    }

    pub(crate) fn materializable_call_result_expr_for_call_expr(
        &self,
        source_call: (u64, usize),
        _call: &CExpr,
    ) -> Option<CExpr> {
        if let Some(owner) = self.should_materialize_call_result_at_source(source_call) {
            return Some(owner);
        }
        None
    }

    fn certified_call_result_owner_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<&r2ssa::ValueOwner> {
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        self.inputs.call_result_facts()?.owner_for_site(callsite)
    }

    fn certified_call_result_owner_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        match self.certified_call_result_owner_for_source(source_call)? {
            r2ssa::ValueOwner::StackSlot { object, .. } => {
                self.certified_stack_var_expr_for_object(*object)
            }
            r2ssa::ValueOwner::Value(value) => match self.planned_value_expr(*value) {
                Ok(expr) => Some(expr),
                Err(error) => {
                    self.retain_first_observation_error(error);
                    self.retain_first_lowering_refusal(OpLoweringRefusal::missing_program_variable());
                    None
                }
            },
        }
    }

    fn certified_assigned_call_result_owner_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        let render_fact = self.inputs.call_render_facts()?.fact_for_site(callsite)?;
        (render_fact.disposition == r2types::CallsiteRenderDisposition::AssignedResult)
            .then(|| self.certified_call_result_owner_expr_for_source(source_call))?
    }

    /// The name a call result carries, for a definition that is a slice of it.
    ///
    /// A `Derived` call-result certificate says this value is the call's result
    /// seen at another width, not a second result. Rendering it from the
    /// carrier's binding keeps the call to one evaluation.
    fn derived_call_result_carrier_expr(&self, dst: &SSAVar) -> Option<(ValueId, CExpr)> {
        let value = self.prepared_value_id_for_var(dst)?;
        let view = self.prepared_semantic_view()?;
        let cert = view.call_result_facts_by_value.get(&value);
        let cert = cert?;
        if cert.relation.is_identity() {
            return None;
        }
        let carrier = view
            .call_result_facts_by_value
            .values()
            .find(|other| other.callsite == cert.callsite && other.relation.is_identity())?
            .value;
        // Whatever the call statement wrote is what this slice reads. Taking
        // `symbol_for_value` instead gave a name the statement does not
        // necessarily assign -- the site owns its result through the owner
        // expression -- so the lane mentioned a variable nothing declared.
        let owner = self.certified_call_result_owner_expr_for_source((
            cert.callsite.block_addr,
            cert.callsite.op_index,
        ))?;
        Some((carrier, owner))
    }

    /// Whether the call statement at this site renders the assignment itself.
    pub(super) fn call_site_assigns_its_own_result(&self, site: (u64, usize)) -> bool {
        self.materializable_call_result_expr_for_call_expr(site, &CExpr::IntLit(0))
            .is_some()
    }

    /// The value a call site's certified result carries.
    ///
    /// A `Call` has no output of its own, so an occurrence at the call site
    /// names no value, and the call-result obligation the site owns matches
    /// nothing. What the statement assigns is this value, and naming it is what
    /// lets the obligation be discharged by the statement that renders it.
    pub(super) fn certified_call_result_value(&self, site: (u64, usize)) -> Option<ValueId> {
        let view = self.prepared_semantic_view()?;
        view.call_result_facts_by_value
            .values()
            .find(|cert| {
                (cert.callsite.block_addr, cert.callsite.op_index) == site
                    && cert.relation.is_identity()
            })
            .map(|cert| cert.value)
    }

    /// Where the definition of this call site's certified result lives.
    ///
    /// One statement implements two instructions: the call supplies the effect
    /// and the `CallDefine` owns the write. A `Call` has no output, so
    /// observing the statement against its own site asks for a write target
    /// that cannot exist and leaves the assignment unaccounted.
    pub(super) fn certified_call_result_definition_site(
        &self,
        site: (u64, usize),
    ) -> Option<(u64, usize)> {
        let view = self.prepared_semantic_view()?;
        let cert = view.call_result_facts_by_value.values().find(|cert| {
            (cert.callsite.block_addr, cert.callsite.op_index) == site
                && cert.relation.is_identity()
        })?;
        let graph = self.inputs.prepared_ssa?.graph();
        graph.op_site_for_inst(graph.def_inst(cert.value)?)
    }

    pub(crate) fn call_result_source_for_var(&self, var: &SSAVar) -> Option<(u64, usize)> {
        self.prepared_semantic_view()?
            .call_result_source_for_var(var)
    }

    /// The type a name takes from the call whose result it owns.
    ///
    /// A local that owns a call result holds what the callee returned, so the
    /// callee's prototype types it. Often that is the only thing that types it
    /// at all: on a binary with no symbols nothing else in the function says
    /// what `malloc` handed back, and the slot then reads as a plain integer,
    /// which is enough to lose which side of `buf + len` is the pointer.
    /// The aggregate a type names, through any pointer or array wrapping it.
    fn expr_type_hint(&self, expr: &CExpr) -> Option<CType> {
        match expr.unobserved() {
            CExpr::Var(_) => None,
            CExpr::Call {
                site: Some((block_addr, op_idx)),
                ..
            } => self
                .known_signature_for_site(*block_addr, *op_idx)
                .map(|sig| sig.return_type.clone()),
            CExpr::Call { site: None, .. } => None,
            CExpr::Cast { ty, .. } => Some(ty.clone()),
            CExpr::Paren(inner) => self.expr_type_hint(inner),
            _ => None,
        }
    }

    #[cfg(test)]
    fn expr_type_hint_for_source_call(
        &self,
        source_call: (u64, usize),
        expr: &CExpr,
    ) -> Option<CType> {
        match expr.unobserved() {
            CExpr::Call { .. } => self
                .known_signature_for_site(source_call.0, source_call.1)
                .map(|sig| sig.return_type.clone()),
            CExpr::Cast { ty, .. } => Some(ty.clone()),
            CExpr::Paren(inner) => self.expr_type_hint_for_source_call(source_call, inner),
            _ => self.expr_type_hint(expr),
        }
    }

    fn cast_addr_expr_to_ptr_if_needed(
        &self,
        addr: &SSAVar,
        addr_expr: CExpr,
        target_ptr_ty: &CType,
    ) -> CExpr {
        if let CExpr::Cast { ty, .. } = &addr_expr
            && ty == target_ptr_ty
        {
            return addr_expr;
        }

        // The declaration first, for the same reason as every other cast: it
        // is what the compiler reads. Taking the certified hint alone said
        // `RDI_0` was a pointer while its declaration said `uint64_t`, so no
        // cast was emitted and the load rendered as `*RDI_0` -- a dereference
        // of an integer, which does not compile.
        let source_ty = self
            .expr_type_hint(&addr_expr)
            .map(RecordedType::from_certified_fact)
            .or_else(|| self.source_type_for_var(addr));
        if let Some(source_ty) = source_ty {
            return self.cast_expr_if_needed(addr_expr, target_ptr_ty.clone(), Some(&source_ty));
        }

        if self.looks_like_pointer(&addr_expr) {
            return addr_expr;
        }

        CExpr::cast(target_ptr_ty.clone(), addr_expr)
    }

    fn int_meta(&self, ty: &CType) -> Option<(bool, u32)> {
        match ty {
            CType::Int { bits, signedness: r2types::Signedness::Signed } => Some((true, *bits)),
            CType::Int { bits, signedness: r2types::Signedness::Unsigned } => Some((false, *bits)),
            CType::Bool => Some((false, 1)),
            CType::Typedef(name) => self.typedef_int_meta(name),
            _ => None,
        }
    }

    fn typedef_int_meta(&self, name: &str) -> Option<(bool, u32)> {
        let normalized = name
            .to_ascii_lowercase()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        match normalized.as_str() {
            "signed char" | "int8_t" => Some((true, 8)),
            "unsigned char" | "uint8_t" => Some((false, 8)),
            "short" | "short int" | "signed short" | "signed short int" | "int16_t" => {
                Some((true, 16))
            }
            "unsigned short" | "unsigned short int" | "uint16_t" => Some((false, 16)),
            "int" | "signed" | "signed int" | "int32_t" => Some((true, 32)),
            "unsigned" | "unsigned int" | "uint32_t" => Some((false, 32)),
            "long long"
            | "long long int"
            | "signed long long"
            | "signed long long int"
            | "int64_t"
            | "intmax_t" => Some((true, 64)),
            "unsigned long long" | "unsigned long long int" | "uint64_t" | "uintmax_t" => {
                Some((false, 64))
            }
            "long" | "long int" | "signed long" | "signed long int" => {
                Some((true, self.inputs.arch.ptr_size.saturating_mul(8)))
            }
            "unsigned long" | "unsigned long int" | "size_t" | "uintptr_t" => {
                Some((false, self.inputs.arch.ptr_size.saturating_mul(8)))
            }
            "ssize_t" | "intptr_t" | "ptrdiff_t" => {
                Some((true, self.inputs.arch.ptr_size.saturating_mul(8)))
            }
            _ => None,
        }
    }
    fn cast_needed(&self, target: &CType, source: Option<&RecordedType>) -> bool {
        let Some(source) = source.map(RecordedType::get) else {
            return false;
        };

        if target == source {
            return false;
        }

        if let (Some((dst_signed, dst_bits)), Some((src_signed, src_bits))) =
            (self.int_meta(target), self.int_meta(source))
        {
            return dst_signed != src_signed || dst_bits != src_bits;
        }

        // Two pointers that are not the same pointer still need the
        // conversion spelled: `target == source` was already excluded above,
        // so reaching here with both pointers means they point at different
        // things and the load or store would read the wrong width.
        matches!(
            (target, source),
            (
                CType::Pointer(_),
                CType::Int { bits: _, signedness: r2types::Signedness::Signed } | CType::Int { bits: _, signedness: r2types::Signedness::Unsigned } | CType::Bool | CType::Pointer(_)
            ) | (CType::Int { bits: _, signedness: r2types::Signedness::Signed } | CType::Int { bits: _, signedness: r2types::Signedness::Unsigned }, CType::Pointer(_))
        )
    }

    /// Cast to exactly this type unless the expression already says so.
    ///
    /// Unlike `cast_expr_if_needed` this does not consult a source hint: it is
    /// for a type the operation requires rather than one the renderer is free
    /// to leave implicit.
    fn cast_expr_to(expr: CExpr, target: CType) -> CExpr {
        if let CExpr::Cast { ty, .. } = expr.unobserved()
            && *ty == target
        {
            return expr;
        }
        CExpr::cast(target, expr)
    }

    fn cast_expr_if_needed(
        &self,
        expr: CExpr,
        target: CType,
        source: Option<&RecordedType>,
    ) -> CExpr {
        if let CExpr::Cast { ty, .. } = expr.unobserved()
            && *ty == target
        {
            return expr;
        }
        if self.cast_needed(&target, source) {
            CExpr::cast(target, expr)
        } else {
            expr
        }
    }

    fn assignment_rhs_with_type_policy(
        &self,
        dst: &SSAVar,
        src: Option<&SSAVar>,
        rhs: CExpr,
    ) -> CExpr {
        self.assignment_rhs_from_source_type(dst, src.and_then(|var| self.source_type_for_var(var)), rhs)
    }

    /// The assignment cast policy, from a source type rather than a variable.
    ///
    /// Some operations know the type of the expression they produce without
    /// there being a variable to ask: a binary operation whose operands were
    /// both cast to a stated type produces that type. Passing `None` there
    /// meant the policy decided from not knowing, which is what property 2
    /// forbids.
    fn assignment_rhs_from_source_type(
        &self,
        dst: &SSAVar,
        src_ty: Option<RecordedType>,
        rhs: CExpr,
    ) -> CExpr {
        // The target is the declared type for the same reason the source is:
        // a cast is a statement about the emitted C, and the declaration is
        // what the compiler reads. Casting to what upstream believes the value
        // means, while the declaration says otherwise, produced
        // `X1_0 = (int64_t)(...)` for an object declared `uint64_t` -- correct
        // arithmetic that will not compile under `-Wsign-conversion`.
        let Some(dst_ty) = self.source_type_for_var(dst).map(RecordedType::into_inner) else {
            return rhs;
        };

        let rhs = self.cast_expr_if_needed(rhs, dst_ty.clone(), src_ty.as_ref());
        self.rewrite_typed_assignment_literal_expr(rhs, &dst_ty)
    }

    fn rewrite_typed_assignment_literal_expr(&self, expr: CExpr, dst_ty: &CType) -> CExpr {
        let Some((is_signed, bits)) = self.int_meta(dst_ty) else {
            return expr;
        };
        if bits == 0 || bits > 64 {
            return expr;
        }
        match expr {
            CExpr::Observed { id, expr } => CExpr::observed(
                id,
                self.rewrite_typed_assignment_literal_expr(*expr, dst_ty),
            ),
            CExpr::UIntLit(value) => crate::typed_integer_literal_expr(value, is_signed, bits),
            CExpr::IntLit(value) if value >= 0 => {
                crate::typed_integer_literal_expr(value as u64, is_signed, bits)
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(
                self.rewrite_typed_assignment_literal_expr(*inner, dst_ty),
            )),
            other => other,
        }
    }

    fn literal_to_i64(&self, expr: &CExpr) -> Option<i64> {
        match expr.unobserved() {
            CExpr::IntLit(v) => Some(*v),
            CExpr::UIntLit(v) => i64::try_from(*v).ok(),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => self.literal_to_i64(inner),
            CExpr::Binary { op, left, right } => {
                let left = self.literal_to_i64(left)?;
                let right = self.literal_to_i64(right)?;
                match op {
                    BinaryOp::Add => left.checked_add(right),
                    BinaryOp::Sub => left.checked_sub(right),
                    BinaryOp::Mul => left.checked_mul(right),
                    BinaryOp::BitAnd => Some(left & right),
                    BinaryOp::BitOr => Some(left | right),
                    BinaryOp::BitXor => Some(left ^ right),
                    BinaryOp::Shl => {
                        if !(0..=62).contains(&right) {
                            return None;
                        }
                        left.checked_mul(1i64 << right)
                    }
                    BinaryOp::Shr => {
                        if !(0..=62).contains(&right) {
                            return None;
                        }
                        Some(left >> right)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(crate) fn fold_block(
        &self,
        block: &SSABlock,
        current_block_addr: u64,
    ) -> OpLoweringResult<Vec<CStmt>> {
        self.current_block_addr.set(Some(current_block_addr));
        self.current_block_id.set(
            self.inputs
                .prepared_ssa
                .and_then(|prepared| prepared.graph().block_id_for_addr(current_block_addr)),
        );
        self.current_op_idx.set(None);
        self.folded_blocks.borrow_mut().insert(block.addr);
        let mut stmts = Vec::new();

        for (op_idx, op) in block.ops.iter().enumerate() {
            self.current_op_idx.set(Some(op_idx));
            if self.is_inlined_single_use_call_result(block, op_idx, op) {
                continue;
            }

            if self
                .source_inst_for_normalized_op(block.addr, op_idx)
                .is_some_and(|inst| {
                    self.prepared_ssa().is_some_and(|prepared| {
                        prepared
                            .certificates()
                            .stack_frame_round_trip_by_inst
                            .contains_key(&inst)
                            // Every instruction a return-control certificate
                            // answers for, not only the ones it claims
                            // exclusively: the prologue's save of the return
                            // address is shared with the frame's own setup and
                            // with every other return, so it is deliberately
                            // claimed by none of them, and asking only about
                            // exclusive claims left it to be rendered as a
                            // store to a slot the plan had already elided.
                            || crate::binding_plan::certified_return_control_insts(prepared)
                                .contains(&inst)
                            || prepared
                                .certificates()
                                .stack_geometry
                                .insts
                                .contains(&inst)
                            // The copy that puts a callee's address in a
                            // temporary before the call. The call spells the
                            // callee's name, so this assigns an object the
                            // plan has elided and no statement can name.
                            || crate::binding_plan::certified_direct_call_target_insts(prepared)
                                .contains(&inst)
                            // The push that records where the call comes back
                            // to. The call statement is the transfer.
                            || crate::binding_plan::certified_call_return_address_insts(prepared)
                                .contains(&inst)
                    })
                })
            {
                continue;
            }

            if let SSAOp::Return { .. } = op {
                let (source_inst, boundary) = self
                    .source_return_boundary_for_normalized_op(block.addr, op_idx)
                    .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
                if boundary.at != source_inst
                    || !boundary.complete
                    || !boundary.register_compositions.is_empty()
                {
                    r2il::refusal_evidence!(
                        "return-boundary",
                        "at_mismatch={} incomplete={} compositions={} values={}",
                        boundary.at != source_inst,
                        !boundary.complete,
                        boundary.register_compositions.len(),
                        boundary.values.len()
                    );
                    return Err(OpLoweringRefusal::missing_machine_projection());
                }

                let (return_value, stmt) = match boundary.values.as_slice() {
                    [] => {
                        if self
                            .certified_return_for_normalized_op(block.addr, op_idx)
                            .is_some()
                        {
                            return Err(OpLoweringRefusal::missing_machine_projection());
                        }
                        (None, CStmt::Return(None))
                    }
                    [_] => {
                        let prepared = self
                            .prepared_ssa()
                            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
                        let (source_block, source_op) = prepared
                            .inst_op_site(source_inst)
                            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
                        let certificate = prepared
                            .return_certificate_for_op(source_block, source_op)
                            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
                        let certified = self
                            .certified_return_for_normalized_op(block.addr, op_idx)
                            .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
                        if certificate.at != source_inst
                            || certificate.block_addr != source_block
                            || certificate.op_index != source_op
                            || certified.block_addr != source_block
                            || certified.op_index != source_op
                            || certified.value != certificate.value
                            || certified.width != certificate.width
                        {
                            return Err(OpLoweringRefusal::missing_machine_projection());
                        }
                        let expr = match self.planned_value_expr(certified.value) {
                            Ok(expr) => expr,
                            Err(error) => {
                                self.retain_first_observation_error(error);
                                return Err(OpLoweringRefusal::missing_machine_projection());
                            }
                        };
                        let expr = self.observe_certified_value_read_expr(
                            certified.value,
                            certificate.at,
                            expr,
                        );
                        (Some(certified.value), CStmt::Return(Some(expr)))
                    }
                    _ => return Err(OpLoweringRefusal::missing_machine_projection()),
                };
                let obligations = self.exact_effect_obligations_for_normalized_value(
                    EffectOccurrenceKind::Return,
                    block.addr,
                    op_idx,
                    return_value,
                );
                stmts.push(self.observe_effect_stmt(&obligations, stmt));

                break;
            }

            // Skip operations that produce dead values
            if let Some(dst) = op.dst() {
                if self.is_dead(dst) {
                    continue;
                }

                // Skip if this will be inlined
                if self.should_inline(dst) {
                    // The exact ValueId disposition is the complete admission
                    // proof. Its machine expression is rendered directly by
                    // `planned_value_expr`; no spelling-keyed definition cache
                    // participates in the decision or in later reads.
                    continue;
                }
            }

            if let Some(stmt) = self.op_to_stmt_with_args(op, block.addr, op_idx)? {
                let is_return = matches!(stmt.unobserved(), CStmt::Return(_));
                stmts.push(stmt);
                if is_return {
                    break;
                }
            }
        }

        let trace = std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some();
        if trace {
            eprintln!("FOLDPOST block={:#x} built={}", block.addr, stmts.len());
        }
        self.current_block_addr.set(None);
        self.current_block_id.set(None);
        self.current_op_idx.set(None);
        Ok(stmts)
    }

    fn is_inlined_single_use_call_result(
        &self,
        _block: &SSABlock,
        _op_idx: usize,
        op: &SSAOp,
    ) -> bool {
        if !matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
            return false;
        }

        false
    }


    /// A call renders as a statement of its own only when nothing names its
    /// result.
    ///
    /// Where a `CallDefine` names it, that operation renders the call as the
    /// right-hand side of the assignment that defines the register, and
    /// emitting it here as well would call the function twice.
    fn call_statement_unless_result_is_named(&self, call: CExpr) -> Option<CStmt> {
        let site = (self.current_block_addr.get()?, self.current_op_idx.get()?);
        if self.call_result_exprs_map().contains_key(&site) {
            return None;
        }
        Some(CStmt::Expr(call))
    }

    fn op_to_stmt_impl(&self, op: &SSAOp, frame: &LowerFrame) -> OpLoweringResult<Option<CStmt>> {
        let input = |input_idx: usize, var: &SSAVar| -> OpLoweringResult<CExpr> {
            Ok(self.observed_input(frame, input_idx, self.get_expr(var)?))
        };
        Ok(match op {
            SSAOp::CallOther { .. } | SSAOp::CpuId { .. } => {
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
            SSAOp::Load { space, .. } if *space != r2il::SpaceId::Ram => {
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
            SSAOp::Copy { dst, src } => {
                if self.current_copy_has_coalesced_carrier_elision() {
                    return Ok(None);
                }
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs_base = self.get_expr(src)?;
                let rhs = self.resolve_predicate_rhs_for_var(src, rhs_base);
                let rhs = self.assignment_rhs_with_type_policy(dst, Some(src), rhs);
                let rhs = self.observed_input(frame, 0, rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Load { dst, addr, space } => {
                if *space != r2il::SpaceId::Ram {
                    return Ok(Some(self.certified_residual_comment(format!(
                        "unsupported exact memory load space {} at 0x{:x}:{}",
                        space,
                        self.current_block_addr.get().unwrap_or_default(),
                        self.current_op_idx.get().unwrap_or_default()
                    ))));
                }
                let lhs = self.assignment_lhs_expr(dst)?;
                // A load is unsigned unless something sign-extends it, and
                // Sleigh says so explicitly with `IntSExt` when it does. Giving
                // a bare byte load a signed pointee makes C sign-extend where
                // the machine does not: `pearson` reads its table with
                // `mov al, byte [rax + rcx]`, and rendering that as `int8_t*`
                // turns any entry at or above 0x80 negative, which then corrupts
                // the next index.
                let elem_ty = self
                    .type_hint_for_var(dst)
                    .unwrap_or_else(|| uint_type_from_size(dst.size));
                let rhs = self.render_certified_load_access_expr(dst, addr, elem_ty)?;
                let rhs = self.observed_memory_input(frame, 0, rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Store { addr, val, space } => {
                if *space != r2il::SpaceId::Ram {
                    return Ok(Some(self.certified_residual_comment(format!(
                        "unsupported exact memory store space {} at 0x{:x}:{}",
                        space,
                        self.current_block_addr.get().unwrap_or_default(),
                        self.current_op_idx.get().unwrap_or_default()
                    ))));
                }
                let elem_ty = self
                    .type_hint_for_var(val)
                    .unwrap_or_else(|| type_from_size(val.size));
                let certified_lhs =
                    self.render_certified_store_access_expr(addr, val, elem_ty.clone())?;
                // A use of a call result used to re-render the call, because
                // the result had no name of its own. It has one now: the site
                // assigns it, and rendering the call here as well would call
                // the function a second time.
                let mut rhs = if let Some(source_call) = self
                    .call_result_source_for_var(val)
                    .filter(|site| !self.call_site_assigns_its_own_result(*site))
                {
                    match self
                        .call_result_exprs_map()
                        .get(&source_call)
                        .cloned()
                        .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
                    {
                        Some(expr) => expr,
                        None => self.get_expr(val)?,
                    }
                } else {
                    self.get_expr(val)?
                };
                if let Some(val_ty) = self.type_hint_for_var(val)
                    && matches!(val_ty, CType::Pointer(_))
                    && !self.looks_like_pointer(&rhs)
                {
                    rhs = CExpr::cast(val_ty, rhs);
                }
                let lhs = self.observed_memory_input(frame, 0, certified_lhs);
                let rhs = self.observed_input(frame, 1, rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Fence { ordering } => Some(CStmt::Expr(CExpr::call(
                CExpr::External {
                    name: "memory_fence".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
                vec![CExpr::StringLit(memory_ordering_name(ordering).to_string())],
            ))),
            SSAOp::LoadLinked {
                dst,
                space,
                addr,
                ordering,
            } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let call = CExpr::call(
                    CExpr::External {
                        name: "load_linked".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![
                        CExpr::StringLit(space.to_string()),
                        input(0, addr)?,
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::StoreConditional {
                result,
                space,
                addr,
                val,
                ordering,
            } => {
                let call = CExpr::call(
                    CExpr::External {
                        name: "store_conditional".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![
                        CExpr::StringLit(space.to_string()),
                        input(0, addr)?,
                        input(1, val)?,
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                if let Some(dst) = result {
                    let lhs = self.assignment_lhs_expr(dst)?;
                    Some(CStmt::Expr(CExpr::assign(lhs, call)))
                } else {
                    Some(CStmt::Expr(call))
                }
            }
            SSAOp::AtomicCAS {
                dst,
                space,
                addr,
                expected,
                replacement,
                ordering,
            } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let call = CExpr::call(
                    CExpr::External {
                        name: "atomic_cas".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![
                        CExpr::StringLit(space.to_string()),
                        input(0, addr)?,
                        input(1, expected)?,
                        input(2, replacement)?,
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::LoadGuarded {
                dst,
                space,
                addr,
                guard,
                ordering,
            } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let call = CExpr::call(
                    CExpr::External {
                        name: "load_guarded".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![
                        CExpr::StringLit(space.to_string()),
                        input(0, addr)?,
                        input(1, guard)?,
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::StoreGuarded {
                space,
                addr,
                val,
                guard,
                ordering,
            } => Some(CStmt::Expr(CExpr::call(
                CExpr::External {
                    name: "store_guarded".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
                vec![
                    CExpr::StringLit(space.to_string()),
                    input(0, addr)?,
                    input(1, val)?,
                    input(2, guard)?,
                    CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                ],
            ))),
            SSAOp::IntAdd { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Add),
            SSAOp::IntSub { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Sub),
            SSAOp::IntMult { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Mul),
            SSAOp::IntDiv { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Div,
                Some(uint_type_from_size(dst.size)),
            ),
            SSAOp::IntSDiv { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Div,
                Some(type_from_size(dst.size)),
            ),
            SSAOp::IntRem { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Mod,
                Some(uint_type_from_size(dst.size)),
            ),
            SSAOp::IntSRem { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Mod,
                Some(type_from_size(dst.size)),
            ),
            SSAOp::IntAnd { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::BitAnd),
            SSAOp::IntOr { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::BitOr),
            SSAOp::IntXor { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::BitXor),
            SSAOp::IntLeft { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Shl),
            SSAOp::IntRight { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Shr,
                Some(uint_type_from_size(dst.size)),
            ),
            SSAOp::IntSRight { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Shr,
                Some(type_from_size(dst.size)),
            ),
            SSAOp::IntLess { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Lt,
                Some(uint_type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntSLess { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Lt,
                Some(type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntLessEqual { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Le,
                Some(uint_type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntSLessEqual { dst, a, b } => self.binary_stmt_typed(
                frame,
                dst,
                a,
                b,
                BinaryOp::Le,
                Some(type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntEqual { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Eq),
            SSAOp::IntNotEqual { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Ne),
            SSAOp::IntCarry { dst, a, b } => {
                return self.arithmetic_flag_stmt(frame, dst, a, b, "carry");
            }
            SSAOp::IntSCarry { dst, a, b } => {
                return self.arithmetic_flag_stmt(frame, dst, a, b, "scarry");
            }
            SSAOp::IntSBorrow { dst, a, b } => {
                return self.arithmetic_flag_stmt(frame, dst, a, b, "sborrow");
            }
            SSAOp::IntNegate { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::unary(UnaryOp::Neg, input(0, src)?);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::IntNot { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::unary(UnaryOp::BitNot, input(0, src)?);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::PopCount { dst, src } if (1..=8).contains(&src.size) => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "__builtin_popcountll".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![CExpr::cast(CType::Int { bits: 64, signedness: r2types::Signedness::Unsigned }, input(0, src)?)],
                );
                let rhs = CExpr::cast(uint_type_from_size(dst.size), rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::BoolAnd { dst, a, b } => self.boolean_stmt(frame, dst, BinaryOp::And, a, b),
            SSAOp::BoolOr { dst, a, b } => self.boolean_stmt(frame, dst, BinaryOp::Or, a, b),
            SSAOp::BoolXor { dst, a, b } => self.boolean_stmt(frame, dst, BinaryOp::BitXor, a, b),
            SSAOp::BoolNot { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = self
                    .resolve_predicate_rhs_for_var(dst, CExpr::unary(UnaryOp::Not, input(0, src)?));
                self.assign_stmt(lhs, rhs)
            }
            // A destination is declared as the unsigned machine word of its own
            // width, so that is what an assignment to it must produce. The
            // signed intermediate a sign extension needs is already inside the
            // operand expression; casting the whole result to the signed type
            // again made the value's type disagree with the object holding it,
            // which a strict compile rejects as a signedness-changing
            // conversion. Zero extension and truncation were never signed.
            SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let ty = uint_type_from_size(dst.size);
                let rhs = self.resolve_predicate_rhs_for_var(dst, CExpr::cast(ty, input(0, src)?));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Trunc { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let ty = uint_type_from_size(dst.size);
                let rhs = self.resolve_predicate_rhs_for_var(dst, CExpr::cast(ty, input(0, src)?));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Piece { dst, hi, lo } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let shift_bits = lo.size.saturating_mul(8);
                let dst_ty = uint_type_from_size(dst.size);
                let hi_cast = CExpr::cast(dst_ty.clone(), input(0, hi)?);
                let lo_cast = CExpr::cast(dst_ty.clone(), input(1, lo)?);
                let shifted = if shift_bits == 0 {
                    hi_cast
                } else {
                    CExpr::binary(BinaryOp::Shl, hi_cast, CExpr::IntLit(shift_bits as i64))
                };
                let rhs = CExpr::binary(BinaryOp::BitOr, shifted, lo_cast);
                // A composition narrower than `int` is computed in `int`,
                // because that is what C promotes the shift and the or to, and
                // assigning the result back narrows it. The value always fits --
                // the operands are exactly the destination's bytes -- but the
                // strict dialect this renders for treats the implicit narrowing
                // as an error, so the conversion is written down.
                let rhs = if dst.size.saturating_mul(8) < 32 {
                    CExpr::cast(dst_ty, rhs)
                } else {
                    rhs
                };
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Subpiece { dst, src, offset } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let src_expr = input(0, src)?;
                let rhs = if *offset == 0 && dst.size == src.size {
                    src_expr
                } else if *offset == 0 {
                    CExpr::cast(uint_type_from_size(dst.size), src_expr)
                } else {
                    let shift_bits = offset.saturating_mul(8);
                    let src_cast = CExpr::cast(uint_type_from_size(src.size), src_expr);
                    let shifted =
                        CExpr::binary(BinaryOp::Shr, src_cast, CExpr::IntLit(shift_bits as i64));
                    CExpr::cast(uint_type_from_size(dst.size), shifted)
                };
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatAdd { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Add),
            SSAOp::FloatSub { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Sub),
            SSAOp::FloatMult { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Mul),
            SSAOp::FloatDiv { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Div),
            SSAOp::FloatNeg { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::unary(UnaryOp::Neg, input(0, src)?);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatAbs { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "fabs".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![input(0, src)?],
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatSqrt { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "sqrt".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![input(0, src)?],
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatCeil { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "ceil".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![input(0, src)?],
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatFloor { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "floor".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![input(0, src)?],
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatRound { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "round".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![input(0, src)?],
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatNaN { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(
                    CExpr::External {
                        name: "isnan".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    },
                    vec![input(0, src)?],
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatLess { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Lt),
            SSAOp::FloatLessEqual { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Le),
            SSAOp::FloatEqual { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Eq),
            SSAOp::FloatNotEqual { dst, a, b } => self.binary_stmt(frame, dst, a, b, BinaryOp::Ne),
            SSAOp::Int2Float { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::cast(CType::Float(dst.size), input(0, src)?);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Float2Int { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::cast(type_from_size(dst.size), input(0, src)?);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatFloat { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::cast(CType::Float(dst.size), input(0, src)?);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Call { target } => {
                // Note: Call arguments are handled by op_to_stmt_with_args().

                let func_expr = match (self.current_block_addr.get(), self.current_op_idx.get()) {
                    (Some(block_addr), Some(op_idx)) => {
                        self.resolve_call_target_for_site(block_addr, op_idx, target)
                    }
                    _ => self.resolve_call_target(target),
                }?;
                // Deliberately not an observed input. The callee's name is not
                // a read of the target operand's value -- it is the symbol the
                // call site resolves to -- and the plan elides that value for
                // the same reason. Marking it read would claim the function
                // holds the callee's address in an object it never declares.
                let call = CExpr::call(func_expr, vec![]);
                self.call_statement_unless_result_is_named(call)
            }
            SSAOp::CallInd { target } => {
                // Note: Call arguments are handled by op_to_stmt_with_args().

                let func_expr = match (self.current_block_addr.get(), self.current_op_idx.get()) {
                    (Some(block_addr), Some(op_idx)) => self
                        .resolved_callee_identity_expr_for_site(block_addr, op_idx)
                        .map(Ok)
                        .unwrap_or_else(|| {
                            self.get_expr(target)
                                .map(|expr| CExpr::Deref(Box::new(expr)))
                        })?,
                    _ => CExpr::Deref(Box::new(input(0, target)?)),
                };
                let func_expr = self.observed_input(frame, 0, func_expr);
                let call = CExpr::call(func_expr, vec![]);
                self.call_statement_unless_result_is_named(call)
            }
            SSAOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = self.ptr_arith_expr(frame, base, index, *element_size, false)?;
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = self.ptr_arith_expr(frame, base, index, *element_size, true)?;
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Cast { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = self.resolve_predicate_rhs_for_var(
                    dst,
                    CExpr::cast(type_from_size(dst.size), input(0, src)?),
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Select {
                dst,
                cond,
                if_true,
                if_false,
            } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::Ternary {
                    cond: Box::new(input(0, cond)?),
                    then_expr: Box::new(input(1, if_true)?),
                    else_expr: Box::new(input(2, if_false)?),
                };
                // A ternary's type is the type of its arms. Where they are
                // recorded at the same one that is what this produces; where
                // they disagree there is nothing to state, and saying nothing
                // is the honest answer rather than a guess.
                let arms = self
                    .source_type_for_var(if_true)
                    .filter(|arm| Some(arm) == self.source_type_for_var(if_false).as_ref());
                let rhs = self.assignment_rhs_from_source_type(dst, arms, rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Return { .. } => {
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::BranchInd { .. } => {
                // Handled by control flow structuring
                None
            }
            SSAOp::Phi { .. } => {
                // Phi nodes handled separately
                None
            }
            // The operation that gives a call's result a name.
            //
            // The call itself renders as a bare expression statement and
            // assigns nothing, so this is what defines the register the callee
            // returned in. Having no lowering for it refused every function
            // that used a call's result at all -- `murmur3_32` at -O0 calls
            // `memcpy` and was refused for that.
            //
            // The call expression is rendered here rather than by the call, so
            // the call's own arm renders nothing when a result is recorded for
            // its site. Otherwise the call would appear twice and be made
            // twice.
            SSAOp::CallDefine { dst } => {
                // Not every `CallDefine` is the call's result. A call defines
                // one of these for every register it may have destroyed, and
                // upstream certifies exactly the one the callee returned in --
                // `murmur3_32` at -O0 has nine clobbers to one result at a
                // single `memcpy`. Refusing for want of a call-result source
                // therefore refused every function that called anything, on
                // account of the registers the call did *not* return in.
                //
                // What a clobber holds afterwards is not knowable, and no C
                // statement says so. Rendering nothing is the honest answer,
                // and it is not a silent one: the binding is left unassigned,
                // so anything that goes on to read it is caught by the
                // declaration placement audit and refuses there, naming the
                // read rather than the call.
                let Some(source_call) = self.call_result_source_for_var(dst) else {
                    return Ok(None);
                };
                let lhs = self.assignment_lhs_expr(dst)?;
                // A call also defines the lane its prototype is declared at --
                // an `int` returned in `rax` gives a `CallDefine` for `RAX` and
                // one for `EAX`. The lane is that result sliced, which is what
                // its certificate says, so it renders from the carrier's name
                // rather than calling the function again.
                if let Some((carrier_value, carrier)) =
                    self.derived_call_result_carrier_expr(dst)
                {
                    let carrier = self
                        .value_id_for_rendered_op(dst)
                        .and_then(|value| {
                            self.inputs.prepared_ssa?.graph().def_inst(value)
                        })
                        .map_or(carrier.clone(), |at| {
                            self.observe_certified_value_read_expr(carrier_value, at, carrier)
                        });
                    // The expression is the carrier's own name, so the type it
                    // has is the type that object is declared with. Passing
                    // nothing here let the cast policy decide from not knowing,
                    // which is the thing property 2 forbids.
                    let carrier_ty = self.declared_type_for_value(carrier_value);
                    let rhs = self.assignment_rhs_from_source_type(dst, carrier_ty, carrier);
                    return Ok(self.assign_stmt(lhs, rhs));
                }
                // Where the call site owns its result the call statement
                // assigns it, so rendering here would evaluate the call twice.
                if self.call_site_assigns_its_own_result(source_call) {
                    return Ok(None);
                }
                let call = self
                    .call_result_exprs_map()
                    .get(&source_call)
                    .cloned()
                    .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
                    .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
                // The callee's recorded return type is what the call
                // produces, and it is a fact rather than a shape read off the
                // expression.
                let returned = self
                    .known_signature_for_site(source_call.0, source_call.1)
                    .map(|signature| {
                        RecordedType::from_callee_signature(signature.return_type.clone())
                    });
                let rhs = self.assignment_rhs_from_source_type(dst, returned, call);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Nop => None,
            // A trap. `__builtin_trap` is a real compiler builtin, so the
            // emitted C still compiles standalone with nothing declared, and it
            // is `noreturn`, which is what the operation means: control leaves
            // for an exception handler and does not come back.
            SSAOp::Breakpoint => Some(CStmt::Expr(CExpr::call(
                CExpr::External {
                    name: "__builtin_trap".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
                Vec::new(),
            ))),
            SSAOp::Unimplemented => Some(CStmt::comment("Unimplemented operation")),
            // No statement lowering for this operation. Saying which one is
            // the difference between a class of refused functions and a
            // one-line fix, so the operation is named rather than swallowed.
            unhandled => {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    eprintln!(
                        "no statement lowering for {}",
                        format!("{unhandled:?}").chars().take(160).collect::<String>()
                    );
                }
                return Err(OpLoweringRefusal::unrepresentable_operation());
            }
        })
    }

    /// Create a binary operation statement.
    fn binary_stmt(
        &self,
        frame: &LowerFrame,
        dst: &SSAVar,
        a: &SSAVar,
        b: &SSAVar,
        op: BinaryOp,
    ) -> Option<CStmt> {
        self.binary_stmt_typed(frame, dst, a, b, op, None)
    }

    /// Render a typed machine arithmetic flag through the external C prelude.
    ///
    /// The helper evaluates each projected source operand once and performs
    /// the overflow algebra in an unsigned carrier, so the emitted program has
    /// neither duplicated use occurrences nor signed-overflow UB.
    fn arithmetic_flag_stmt(
        &self,
        frame: &LowerFrame,
        dst: &SSAVar,
        a: &SSAVar,
        b: &SSAVar,
        operation: &str,
    ) -> OpLoweringResult<Option<CStmt>> {
        if a.size != b.size || !matches!(a.size, 1 | 2 | 4 | 8 | 16) {
            return Err(OpLoweringRefusal::missing_machine_projection());
        }
        let lhs = self.assignment_lhs_expr(dst)?;
        let operand_ty = uint_type_from_size(a.size);
        let left = CExpr::cast(
            operand_ty.clone(),
            self.observed_input(frame, 0, self.get_expr(a)?),
        );
        let right = CExpr::cast(
            operand_ty,
            self.observed_input(frame, 1, self.get_expr(b)?),
        );
        let helper = format!("r2sleigh_int_{operation}_{}", a.size * 8);
        let rhs = CExpr::call(
            CExpr::External {
                name: helper,
                kind: crate::symbol::ExternalKind::Intrinsic,
            },
            vec![left, right],
        );
        let rhs = CExpr::cast(uint_type_from_size(dst.size), rhs);
        let rhs = self.resolve_predicate_rhs_for_var(dst, rhs);
        Ok(self.assign_stmt(lhs, rhs))
    }

    fn binary_stmt_typed(
        &self,
        frame: &LowerFrame,
        dst: &SSAVar,
        a: &SSAVar,
        b: &SSAVar,
        op: BinaryOp,
        operand_ty: Option<CType>,
    ) -> Option<CStmt> {
        let lhs = self.retain_lowering_result(self.assignment_lhs_expr(dst))?;
        if matches!(op, BinaryOp::BitAnd | BinaryOp::BitOr)
            && let (Some(left_source), Some(right_source)) = (
                self.call_result_source_for_var(a),
                self.call_result_source_for_var(b),
            )
            && left_source == right_source
            && !self.call_site_assigns_its_own_result(left_source)
            && let Some(call_expr) = self
                .call_result_exprs_map()
                .get(&left_source)
                .cloned()
                .or_else(|| self.synthesized_call_expr_for_source_call(left_source))
        {
            let call_expr = self.observed_input(frame, 0, call_expr);
            let call_expr = self.observed_input(frame, 1, call_expr);
            let rhs = self.assignment_rhs_with_type_policy(dst, None, call_expr);
            return self.assign_stmt(lhs, rhs);
        }
        let mut lhs_expr =
            self.observed_input(frame, 0, self.retain_lowering_result(self.get_expr(a))?);
        let mut rhs_expr =
            self.observed_input(frame, 1, self.retain_lowering_result(self.get_expr(b))?);
        let produced_ty = operand_ty.clone();
        if let Some(ty) = operand_ty {
            // Stated, not hinted. This type is the operation: `IntSLess` and
            // `IntLess` differ only in the signedness of the operands they
            // compare, so leaving it off changes what the comparison means.
            //
            // `cast_expr_if_needed` decides from the source type hint, and an
            // absent hint made it conclude no cast was needed -- which is a
            // conclusion drawn from not knowing. The x86 sign flag is
            // `IntSLess(result, 0)`, and its operands carried no hint, so it
            // rendered as `(uint32_t)result < (uint32_t)0`: false for every
            // input. `cmp k, 8; jge` then exited on entry and the CRC inner
            // loop never ran once.
            lhs_expr = Self::cast_expr_to(lhs_expr, ty.clone());
            rhs_expr = Self::cast_expr_to(rhs_expr, ty);
        }
        let rhs_raw = self.identity_simplify_binary(
            op,
            lhs_expr,
            rhs_expr,
            (dst.size > 0).then_some(dst.size),
        );
        let rhs = if matches!(
            op,
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
        ) {
            self.resolve_predicate_rhs_for_var(dst, rhs_raw)
        } else {
            rhs_raw
        };
        // Both operands were cast to the stated operand type, so that is the
        // type of the expression this produces -- except for a comparison,
        // whose value in C is an `int`. Either way it is stated rather than
        // guessed, which is what the policy needs.
        let produced = if matches!(
            op,
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
        ) {
            Some(RecordedType::from_operation(CType::Int { bits: 32, signedness: r2types::Signedness::Signed }))
        } else {
            // No stated operand type means the operation did not require one,
            // not that the expression has no type. Where both operands are
            // recorded at the same type, the wrapping arithmetic C performs on
            // them produces that type, and that is a derivation rather than a
            // guess. Where they disagree there is nothing to state.
            produced_ty
                .map(RecordedType::from_operation)
                .or_else(|| {
                    let left = self.source_type_for_var(a)?;
                    let right = self.source_type_for_var(b)?;
                    if right == left {
                        return Some(left);
                    }
                    // Both operands are recorded and they differ. C says what
                    // the expression's type is then -- the usual arithmetic
                    // conversions -- so it is still stated, from two recorded
                    // facts and a rule in the standard, rather than guessed.
                    // Leaving it unstated let the cast policy decide from not
                    // knowing, which is the last place on the render path that
                    // did.
                    let (left_signed, left_bits) = self.int_meta(left.get())?;
                    let (right_signed, right_bits) = self.int_meta(right.get())?;
                    let bits = left_bits.max(right_bits);
                    let signed = if left_bits == right_bits {
                        left_signed && right_signed
                    } else if left_bits > right_bits {
                        left_signed
                    } else {
                        right_signed
                    };
                    let converted = if signed {
                        CType::Int { bits, signedness: r2types::Signedness::Signed }
                    } else {
                        CType::Int { bits, signedness: r2types::Signedness::Unsigned }
                    };
                    Some(RecordedType::from_operation(converted))
                })
        };
        let rhs = self.assignment_rhs_from_source_type(dst, produced, rhs);
        self.assign_stmt(lhs, rhs)
    }

    fn boolean_stmt(
        &self,
        frame: &LowerFrame,
        dst: &SSAVar,
        op: BinaryOp,
        a: &SSAVar,
        b: &SSAVar,
    ) -> Option<CStmt> {
        let lhs = self.retain_lowering_result(self.assignment_lhs_expr(dst))?;
        let rhs = self.resolve_predicate_rhs_for_var(
            dst,
            CExpr::binary(
                op,
                self.observed_input(frame, 0, self.retain_lowering_result(self.get_expr(a))?),
                self.observed_input(frame, 1, self.retain_lowering_result(self.get_expr(b))?),
            ),
        );
        self.assign_stmt(lhs, rhs)
    }
}

#[cfg(test)]
#[test]
fn a_breakpoint_lowers_to_a_trap_that_needs_no_declaration() {
    let ctx = FoldingContext::new(64);
    let frame = LowerFrame::for_expr();

    let stmt = ctx
        .op_to_stmt_impl(&SSAOp::Breakpoint, &frame)
        .expect("a breakpoint is representable")
        .expect("a breakpoint is a statement, not an elision");

    // `__builtin_trap` rather than a declared helper: it is a real compiler
    // builtin, so the emitted C compiles standalone with nothing added to the
    // externs, and it is `noreturn`, which is what the operation means.
    let CStmt::Expr(CExpr::Call { func, args, .. }) = &stmt else {
        panic!("expected a call statement, got {stmt:?}");
    };
    assert!(args.is_empty());
    assert_eq!(
        **func,
        CExpr::External {
            name: "__builtin_trap".to_string(),
            kind: crate::symbol::ExternalKind::Intrinsic,
        }
    );
}

#[cfg(test)]
#[test]
fn opaque_operations_are_typed_refusals_before_ast_lowering() {
    let ctx = FoldingContext::new(64);
    let input = SSAVar::new("X30", 0, 8);
    let output = SSAVar::new("X30", 1, 8);
    let frame = LowerFrame::for_expr();

    let opaque = [
        SSAOp::CallOther {
            output: Some(output.clone()),
            userop: u32::MAX,
            inputs: vec![input.clone()],
        },
        SSAOp::CallOther {
            output: None,
            userop: 7,
            inputs: vec![input],
        },
        SSAOp::CpuId {
            dst: SSAVar::new("EAX", 1, 4),
        },
    ];

    for op in opaque {
        assert_eq!(
            ctx.op_to_stmt_impl(&op, &frame),
            Err(OpLoweringRefusal::missing_machine_projection()),
            "opaque operations must never manufacture an executable AST node"
        );
    }
}

#[cfg(test)]
#[test]
fn unsupported_live_definition_is_a_typed_refusal() {
    let ctx = FoldingContext::new(64);
    let frame = LowerFrame::for_expr();
    let unsupported = SSAOp::Lzcount {
        dst: SSAVar::new("tmp", 1, 8),
        src: SSAVar::new("tmp", 0, 8),
    };

    assert_eq!(
        ctx.op_to_stmt_impl(&unsupported, &frame),
        Err(OpLoweringRefusal::unrepresentable_operation()),
        "an operation the renderer has no lowering for is unrepresentable, \
         not a machine projection this renderer was denied"
    );
}

#[cfg(test)]
#[test]
fn unsigned_flag_formulas_match_exhaustive_i8_arithmetic() {
    for left in u8::MIN..=u8::MAX {
        for right in u8::MIN..=u8::MAX {
            let sum = left.wrapping_add(right);
            let difference = left.wrapping_sub(right);
            let carry = u8::from(sum < left);
            let signed_carry = ((!(left ^ right) & (left ^ sum)) >> 7) & 1;
            let signed_borrow = (((left ^ right) & (left ^ difference)) >> 7) & 1;

            assert_eq!(carry != 0, left.checked_add(right).is_none());
            assert_eq!(
                signed_carry != 0,
                (left as i8).checked_add(right as i8).is_none()
            );
            assert_eq!(
                signed_borrow != 0,
                (left as i8).checked_sub(right as i8).is_none()
            );
        }
    }
}

#[cfg(test)]
#[path = "../tests/lowering.rs"]
mod lowering_tests;

include!("../tests/pipeline.rs");
