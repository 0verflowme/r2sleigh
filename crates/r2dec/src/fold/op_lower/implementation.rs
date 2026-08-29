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
                self.retain_first_lowering_refusal(
                    OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
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
                self.retain_first_lowering_refusal(
                    OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
                None
            }
            Err(error) => {
                self.retain_first_observation_error(error);
                self.retain_first_lowering_refusal(
                    OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
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
                self.retain_first_lowering_refusal(
                    OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
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
            if prepared
                .call_result_certificate_for_value(value)
                .is_some_and(|result| result.relation.is_identity())
            {
                return self.certified_call_result_expr_for_value(value);
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
                self.retain_first_lowering_refusal(
                    OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
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
                            && self.inputs.function_return_type.and_then(CType::bits)
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
                        param_register_aliases: analysis::no_carrier_aliases(),
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

    pub(crate) fn to_pass_env(&self) -> analysis::PassEnv<'_> {
        analysis::PassEnv {
            binding_names: self.inputs.binding_names.map(std::rc::Rc::as_ref),
            symbols: &self.symbols,
            string_literals: self.inputs.display_names.strings(),
            ptr_size: self.inputs.arch.ptr_size,
            sp_name: &self.inputs.arch.sp_name,
            fp_name: &self.inputs.arch.fp_name,
            ret_reg_name: &self.inputs.arch.ret_reg_name,
            flag_regs: &self.inputs.arch.flag_regs,
            #[cfg(test)]
            function_names: self.inputs.function_names,
            #[cfg(test)]
            strings: self.inputs.strings,
            #[cfg(test)]
            binary_symbols: self.inputs.binary_symbols,
            callee_facts: self.inputs.callee_facts(),
            callee_resolution: self.inputs.callee_resolution(),
            summary_view: self.inputs.summary_view(),
            arg_regs: &self.inputs.arch.arg_regs,
            #[cfg(test)]
            param_register_aliases: analysis::no_carrier_aliases(),
            #[cfg(test)]
            carrier_aliases: analysis::no_carrier_aliases(),
            caller_saved_regs: &self.inputs.arch.caller_saved_regs,
            type_oracle: self.inputs.type_oracle,
        }
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
        if self.inputs.prepared_ssa.is_some()
            && std::env::var_os("R2SLEIGH_DEBUG_UNKEYED").is_some()
        {
            let unkeyed = &self.use_info().unkeyed_writes;
            let total: usize = unkeyed.values().sum();
            eprintln!("UNKEYED total={total} by_store={unkeyed:?}");
        }
        let symbols = &self.symbols;

        if let Some(prepared) = self.inputs.prepared_ssa {
            let env = self.to_pass_env();
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
                &env,
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
        Err(OpLoweringRefusal::MissingMachineProjectionAuthorization.into())
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
            return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
        };
        if names.disposition_for_value(value).is_none() {
            return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
        }
        let expr = match self.planned_value_expr(value) {
            Ok(expr) => expr,
            Err(error) => {
                self.retain_first_observation_error(error);
                return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
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
                    .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)?;
                let op_idx = self
                    .current_op_idx
                    .get()
                    .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)?;
                Some(self.planned_input_expr_at(block_addr, op_idx, 1)?)
            }
            SSAOp::Return { .. } => {
                return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
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
        // Both sides are exact occurrence projections. Identity-looking text
        // is not an elision proof: distinct SSA values may intentionally share
        // one rendered binding, and a write may still be an observable effect.
        Some(CStmt::Expr(CExpr::assign(lhs, rhs)))
    }

    fn assignment_lhs_expr(&self, _dst: &SSAVar) -> OpLoweringResult<CExpr> {
        match self.planned_current_output_expr() {
            Ok(Some(planned)) => Ok(planned),
            Ok(None) => Err(OpLoweringRefusal::MissingProgramVariableAuthorization),
            Err(error) => {
                self.retain_first_observation_error(error);
                Err(OpLoweringRefusal::MissingProgramVariableAuthorization)
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
            candidates.push(crate::variable::type_like_to_ctype(ty));
        }
        if let Some(r2types::CertifiedEntity::LoopCarrier { ty: Some(ty), .. }) =
            render.loop_carrier_for_value(value)
        {
            candidates.push(crate::variable::type_like_to_ctype(ty));
        }
        if let Some(memory) = self
            .certified_render_context()
            .and_then(|proof| proof.exact_memory_read_for_value(value))
            && let Some(ty) = render.memory_value_type(memory.access)
        {
            candidates.push(crate::variable::type_like_to_ctype(ty));
        }
        if render.return_effects().any(|effect| effect.value == value)
            && let Some(ty) = signature.and_then(|signature| signature.ret_type.as_ref())
        {
            candidates.push(crate::variable::type_like_to_ctype(ty));
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
                    self.retain_first_lowering_refusal(
                        OpLoweringRefusal::MissingProgramVariableAuthorization,
                    );
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
                .map(|sig| crate::variable::type_like_to_ctype(&sig.return_type)),
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
                .map(|sig| crate::variable::type_like_to_ctype(&sig.return_type)),
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

        let source_ty = self
            .expr_type_hint(&addr_expr)
            .or_else(|| self.type_hint_for_var(addr));
        if let Some(source_ty) = source_ty.as_ref() {
            return self.cast_expr_if_needed(addr_expr, target_ptr_ty.clone(), Some(source_ty));
        }

        if self.looks_like_pointer(&addr_expr) {
            return addr_expr;
        }

        CExpr::cast(target_ptr_ty.clone(), addr_expr)
    }

    fn int_meta(&self, ty: &CType) -> Option<(bool, u32)> {
        match ty {
            CType::Int(bits) => Some((true, *bits)),
            CType::UInt(bits) => Some((false, *bits)),
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
    fn cast_needed(&self, target: &CType, source: Option<&CType>) -> bool {
        let Some(source) = source else {
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

        matches!(
            (target, source),
            (
                CType::Pointer(_),
                CType::Int(_) | CType::UInt(_) | CType::Bool
            ) | (CType::Int(_) | CType::UInt(_), CType::Pointer(_))
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

    fn cast_expr_if_needed(&self, expr: CExpr, target: CType, source: Option<&CType>) -> CExpr {
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
        let Some(dst_ty) = self.type_hint_for_var(dst) else {
            return rhs;
        };

        let src_ty = src.and_then(|var| self.type_hint_for_var(var));
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
                            || prepared
                                .certificates()
                                .machine_return_control_by_inst
                                .contains_key(&inst)
                            || prepared
                                .certificates()
                                .stack_geometry
                                .insts
                                .contains(&inst)
                    })
                })
            {
                continue;
            }

            if let SSAOp::Return { .. } = op {
                let (source_inst, boundary) = self
                    .source_return_boundary_for_normalized_op(block.addr, op_idx)
                    .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
                if boundary.at != source_inst
                    || !boundary.complete
                    || !boundary.register_compositions.is_empty()
                {
                    return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
                }

                let (return_value, stmt) = match boundary.values.as_slice() {
                    [] => {
                        if self
                            .certified_return_for_normalized_op(block.addr, op_idx)
                            .is_some()
                        {
                            return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
                        }
                        (None, CStmt::Return(None))
                    }
                    [_] => {
                        let prepared = self
                            .prepared_ssa()
                            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
                        let (source_block, source_op) = prepared
                            .inst_op_site(source_inst)
                            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
                        let certificate = prepared
                            .return_certificate_for_op(source_block, source_op)
                            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
                        let certified = self
                            .certified_return_for_normalized_op(block.addr, op_idx)
                            .ok_or(OpLoweringRefusal::MissingMachineProjectionAuthorization)?;
                        if certificate.at != source_inst
                            || certificate.block_addr != source_block
                            || certificate.op_index != source_op
                            || certified.block_addr != source_block
                            || certified.op_index != source_op
                            || certified.value != certificate.value
                            || certified.width != certificate.width
                        {
                            return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
                        }
                        let expr = match self.planned_value_expr(certified.value) {
                            Ok(expr) => expr,
                            Err(error) => {
                                self.retain_first_observation_error(error);
                                return Err(
                                    OpLoweringRefusal::MissingMachineProjectionAuthorization,
                                );
                            }
                        };
                        let expr = self.observe_certified_value_read_expr(
                            certified.value,
                            certificate.at,
                            expr,
                        );
                        (Some(certified.value), CStmt::Return(Some(expr)))
                    }
                    _ => return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization),
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

    fn op_to_stmt_impl(&self, op: &SSAOp, frame: &LowerFrame) -> OpLoweringResult<Option<CStmt>> {
        let input = |input_idx: usize, var: &SSAVar| -> OpLoweringResult<CExpr> {
            Ok(self.observed_input(frame, input_idx, self.get_expr(var)?))
        };
        Ok(match op {
            SSAOp::CallOther { .. } | SSAOp::CpuId { .. } => {
                return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
            }
            SSAOp::Load { space, .. } if *space != r2il::SpaceId::Ram => {
                return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
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
                let mut rhs = if let Some(source_call) = self.call_result_source_for_var(val) {
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
                    vec![CExpr::cast(CType::UInt(64), input(0, src)?)],
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
                let func_expr = self.observed_input(frame, 0, func_expr);
                let call = CExpr::call(func_expr, vec![]);
                Some(CStmt::Expr(call))
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
                Some(CStmt::Expr(call))
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
                let rhs = self.assignment_rhs_with_type_policy(dst, None, rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Return { .. } => {
                return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
            }
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::BranchInd { .. } => {
                // Handled by control flow structuring
                None
            }
            SSAOp::Phi { .. } => {
                // Phi nodes handled separately
                None
            }
            SSAOp::Nop => None,
            SSAOp::Unimplemented => Some(CStmt::comment("Unimplemented operation")),
            _ => return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization),
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
            return Err(OpLoweringRefusal::MissingMachineProjectionAuthorization);
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
        let rhs = self.assignment_rhs_with_type_policy(dst, None, rhs);
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
            Err(OpLoweringRefusal::MissingMachineProjectionAuthorization),
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
        Err(OpLoweringRefusal::MissingMachineProjectionAuthorization)
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
