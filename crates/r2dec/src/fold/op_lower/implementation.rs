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

    fn certified_const_expr(&self, var: &SSAVar) -> Option<CExpr> {
        let value = parse_const_value(&var.name)?;
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

    fn stack_info(&self) -> &analysis::StackInfo {
        self.state.analysis_ctx.stack()
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

    pub(crate) fn stable_stack_value_for_offset(
        &self,
        offset: i64,
    ) -> Option<&analysis::SemanticValue> {
        self.use_info().stable_stack_values.get(&offset)
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
        self
            .certified_render_context()?
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
                    // First pass: try non-raw inputs only
                    let mut rendered: Vec<(Option<bool>, CExpr)> = Vec::new();
                    for (i, input) in inst.inputs.iter().enumerate() {
                        let Some(expr) =
                            self.certified_structural_expr_for_value(*input, depth + 1, visited)
                        else {
                            continue;
                        };
                        if self.certified_return_expr_contains_raw_storage_name(&expr) {
                            continue;
                        }
                        let is_latch = predecessors
                            .get(i)
                            .and_then(|pred_id| prepared.graph().block(*pred_id))
                            .map(|block| block.addr)
                            .and_then(compute_latch)
                            .unwrap_or(false);
                        rendered.push((Some(is_latch), expr));
                    }
                    // Second pass: if empty and structurally backed, accept raw inputs
                    let has_raw_fallback = rendered.is_empty()
                        && self.control_facts().is_some_and(|facts| {
                            !facts.loops.is_empty() || !facts.switches.is_empty()
                        });
                    if has_raw_fallback {
                        for (i, input) in inst.inputs.iter().enumerate() {
                            let Some(expr) = self.certified_structural_expr_for_value(
                                *input,
                                depth + 1,
                                visited,
                            ) else {
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
                    } else if !rendered.is_empty() && has_raw_fallback {
                        rendered.into_iter().next().map(|(_, expr)| expr)
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
                        if self.expr_contains_raw_stack_base_arithmetic(&rendered)
                            || self.certified_return_expr_contains_raw_storage_name(&rendered)
                        {
                            return None;
                        }
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

    fn certified_return_expr_contains_raw_storage_name(&self, expr: &CExpr) -> bool {
        let mut contains_raw = false;
        expr.visit(&mut |node| {
            if contains_raw {
                return;
            }
            if let CExpr::Var(name) = node {
                let name = &self.spelling(*name);
                let lower = name.to_ascii_lowercase();
                contains_raw = self.is_raw_register_public_call_arg_name(name)
                    || self.inputs.arch.is_stack_base_name(&lower)
                    || self.inputs.arch.is_return_register_name(&lower)
                    || self.is_transient_visible_name(name)
                    || self.is_low_signal_visible_name(name);
            }
        });
        contains_raw
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
            analysis::PreparedSemanticView::build(&self.symbols, analysis::PreparedSemanticViewInputs {
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

    fn prepared_facts(&self) -> Option<&PreparedFunctionFacts> {
        self.prepared_ssa().map(SsaArtifact::facts)
    }

    pub(crate) fn prepared_objects(&self) -> Option<&ObjectModel> {
        self.prepared_facts()
            .map(|facts| &facts.objects)
            .or(self.inputs.prepared_objects)
    }

    pub(crate) fn control_facts(&self) -> Option<&r2types::FunctionControlFacts> {
        self.inputs.control_facts()
    }

    pub(crate) fn prepared_decompile_prep_facts(&self) -> Option<&DecompilePrepFacts> {
        self.prepared_ssa()
            .and_then(|prepared| prepared.function().decompile_prep_facts())
    }

    fn enter_resolution_guard(&self, phase: ResolutionPhase, name: &str) -> bool {

        self.resolution_guard
            .borrow_mut()
            .insert(ResolutionGuardKey {
                phase,
                name: name.to_string(),
            })
    }

    fn leave_resolution_guard(&self, phase: ResolutionPhase, name: &str) {

        self.resolution_guard
            .borrow_mut()
            .remove(&ResolutionGuardKey {
                phase,
                name: name.to_string(),
            });
    }

    fn resolution_cycle_fallback(&self, name: &str) -> Option<CExpr> {
        self.direct_definition_expr(name)
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

    /// What defines a value, asked by one of its names.
    #[cfg(test)]
    pub(crate) fn definition_of(&self, name: &str) -> Option<CExpr> {
        self.use_info().definition_for_name(name).cloned()
    }
    #[cfg(not(test))]
    pub(crate) fn definition_of(&self, _name: &str) -> Option<CExpr> {
        None
    }
    pub(crate) fn ptr_members_map(&self) -> &HashMap<String, (SSAVar, i64)> {
        &self.use_info().ptr_members
    }
    pub(crate) fn definition_for_value_id(&self, value_id: r2ssa::ValueId) -> Option<&CExpr> {
        self.use_info().definition_for_value(value_id)
    }
    #[cfg(test)]
    pub(crate) fn value_id_for_name(&self, name: &str) -> Option<r2ssa::ValueId> {
        self.use_info().value_id_for_name(name)
    }
    #[cfg(not(test))]
    pub(crate) fn value_id_for_name(&self, _name: &str) -> Option<r2ssa::ValueId> {
        None
    }
    pub(crate) fn semantic_value_for_value_id(
        &self,
        value_id: r2ssa::ValueId,
    ) -> Option<&analysis::SemanticValue> {
        self.use_info().semantic_value_for_value(value_id)
    }
    #[cfg(test)]
    pub(crate) fn semantic_value_for_name(&self, name: &str) -> Option<&analysis::SemanticValue> {
        self.use_info().render_semantic_value_for_name(name)
    }
    #[cfg(not(test))]
    pub(crate) fn semantic_value_for_name(
        &self,
        _name: &str,
    ) -> Option<&analysis::SemanticValue> {
        None
    }
    pub(crate) fn forwarded_value_for_value_id(
        &self,
        value_id: r2ssa::ValueId,
    ) -> Option<&analysis::ValueProvenance> {
        self.use_info().forwarded_value_for_value(value_id)
    }
    #[cfg(test)]
    pub(crate) fn forwarded_value_for_name(
        &self,
        name: &str,
    ) -> Option<&analysis::ValueProvenance> {
        self.use_info().render_forwarded_value_for_name(name)
    }
    #[cfg(not(test))]
    pub(crate) fn forwarded_value_for_name(
        &self,
        _name: &str,
    ) -> Option<&analysis::ValueProvenance> {
        None
    }

    pub(crate) fn callee_identity_for_direct_target(&self, addr: u64) -> CalleeIdentity {
        self.inputs
            .callee_resolution()
            .and_then(|facts| facts.identity_for_direct_addr(addr))
            .cloned()
            .unwrap_or_else(|| CalleeIdentity::from_name(&format!("const:{addr:x}")))
    }
    pub(crate) fn callee_identity_for_name(&self, name: &str) -> CalleeIdentity {
        if let Some(identity) = self
            .inputs
            .callee_resolution()
            .and_then(|facts| facts.identity_for_name(name))
        {
            return identity.clone();
        }
        CalleeIdentity::from_name(name)
    }
    pub(crate) fn callee_identity_for_expr(&self, expr: &CExpr) -> Option<CalleeIdentity> {
        call_arg_callee_name(&self.symbols, expr).map(|name| self.callee_identity_for_name(&*name))
    }

    #[cfg(test)]
    pub(crate) fn callee_target_policy_for_identity(
        &self,
        identity: &CalleeIdentity,
    ) -> r2types::CalleeTargetPolicyDecision {
        identity.target_policy_decision(self.inputs.callee_resolution(), self.inputs.callee_facts())
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

    pub(crate) fn stack_vars_map(&self) -> &HashMap<i64, String> {
        &self.stack_info().stack_vars
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

    #[cfg(test)]
    pub fn set_external_stack_vars(
        &mut self,
        stack_vars: HashMap<i64, r2types::ExternalStackVarSpec>,
    ) {
        self.inputs.external_stack_vars = Box::leak(Box::new(stack_vars));
        let stack_slots = self
            .inputs
            .external_stack_vars
            .iter()
            .map(|(offset, slot)| {
                (
                    StackSlotKey {
                        base: slot.base.clone(),
                        offset: *offset,
                    },
                    slot.clone(),
                )
            })
            .collect();
        self.inputs.stack_slots = Box::leak(Box::new(stack_slots));
    }

    pub(crate) fn analyze_function_structure(&mut self, _func: &SSAFunction) {
    }

    pub(crate) fn stack_slot_offset_for_var(&self, var: &SSAVar) -> Option<i64> {
        self.prepared_stack_offset_for_var(var)
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
        if self.inputs.prepared_ssa.is_some() {
            if std::env::var_os("R2SLEIGH_DEBUG_UNKEYED").is_some() {
                let unkeyed = &self.use_info().unkeyed_writes;
                let total: usize = unkeyed.values().sum();
                eprintln!("UNKEYED total={total} by_store={unkeyed:?}");
            }
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
                &symbols,
                blocks,
                &env,
                prepared,
                &prepared_view,
                normalization_origins,
                control,
            )?;
            return Ok(());
        }

        // Every shipped decompile carries the prepared artifact the branch above
        // consumes. Analysing without one was a second pass order over the same
        // blocks, and a fact added to one builder was invisible to the other.
        debug_assert!(
            self.inputs.prepared_ssa.is_some(),
            "analysis requires the prepared artifact"
        );
        Ok(control.poll()?)
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

    fn op_to_expr_impl(
        &self,
        op: &SSAOp,
        frame: &LowerFrame,
    ) -> OpLoweringResult<Option<CExpr>> {
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

    /// Simplify one binary expression while retaining only observations whose
    /// exact operand occurrence survives the rewrite.
    ///
    /// Returning an original operand preserves that operand's markers. An
    /// identity operand or folded constant that disappears takes its markers
    /// with it, leaving the journal obligation unaccounted unless upstream had
    /// already certified a non-rendered disposition.
    fn identity_simplify_binary_semantic(
        &self,
        op: BinaryOp,
        left: CExpr,
        right: CExpr,
        width_bytes: Option<u32>,
    ) -> CExpr {
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
                } else if let Some(coeff) = self.literal_to_i64(&right)
                {
                    let replacement = self.simplify_linear_scale(
                        &left.clone_without_render_observations(),
                        coeff);
                    Self::finish_nonpositional_identity_rewrite(op, left, right, replacement)
                } else if let Some(coeff) = self.literal_to_i64(&left)
                {
                    let replacement = self.simplify_linear_scale(
                        &right.clone_without_render_observations(),
                        coeff);
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
                self.param_rank_for_visible_name(&self.spelling(*name)).unwrap_or(usize::MAX),
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

    fn lookup_semantic_value(&self, name: &str) -> Option<&analysis::SemanticValue> {
        self.semantic_value_for_name(name)
    }

    fn resolution_name_key(&self, prefix: &str, name: &str) -> String {
        format!("{prefix}:name:{name}")
    }

    fn render_semantic_value_by_name(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Semantic, name) {
            return self.resolution_cycle_fallback(name);
        }
        let visit_key = self.resolution_name_key("sem", name);
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH || !visited.insert(visit_key.clone()) {
            self.leave_resolution_guard(ResolutionPhase::Semantic, name);
            return None;
        }
        let in_progress_key = self.resolution_name_key("sem-progress", name);
        {
            let mut in_progress = self.semantic_render_in_progress.borrow_mut();
            if !in_progress.insert(in_progress_key.clone()) {
                visited.remove(&visit_key);
                self.leave_resolution_guard(ResolutionPhase::Semantic, name);
                return None;
            }
        }
        let rendered = self
            .lookup_semantic_value(name)
            .and_then(|value| self.render_semantic_value(value, depth + 1, visited));
        self.semantic_render_in_progress
            .borrow_mut()
            .remove(&in_progress_key);
        self.leave_resolution_guard(ResolutionPhase::Semantic, name);
        visited.remove(&visit_key);
        rendered
    }

    pub(crate) fn render_semantic_value(
        &self,
        value: &analysis::SemanticValue,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        match value {
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => {
                Some(expr.clone())
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(value)) => {
                self.render_value_ref(value, depth, visited)
            }
            analysis::SemanticValue::Address(shape) => {
                self.render_address_expr_from_addr(shape, depth, visited)
            }
            analysis::SemanticValue::Load { space, addr, size } => {
                self.render_semantic_load(*space, addr, *size, depth, visited)
            }
            analysis::SemanticValue::Unknown => None,
        }
    }

    fn render_value_ref(
        &self,
        value: &analysis::ValueRef,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        let name = value.display_name();
        let visit_key = format!("val:{name}");
        if !visited.insert(visit_key.clone()) {
            return None;
        }
        {
            let mut in_progress = self.value_render_in_progress.borrow_mut();
            if !in_progress.insert(name.clone()) {
                visited.remove(&visit_key);
                return None;
            }
        }

        if let Some(owner) = self.stable_owned_call_result_expr_for_var(&value.var) {
            self.value_render_in_progress.borrow_mut().remove(&name);
            visited.remove(&visit_key);
            return Some(owner);
        }

        let forwarded = value
            .value_id()
            .and_then(|value_id| self.forwarded_value_for_value_id(value_id))
            .and_then(|prov| {
                prov.source_var.clone().map(|source| {
                    self.render_value_ref(&analysis::ValueRef::from(source), depth + 1, visited)
                })
            })
            .flatten();
        let fallback = if value.var.constant_bits().is_some() {
            self.retain_lowering_result(self.const_to_expr(&value.var))
        } else {
            value
                .value_id()
                .and_then(|value_id| match self.planned_value_expr(value_id) {
                    Ok(expr) => Some(expr),
                    Err(error) => {
                        self.retain_first_observation_error(error);
                        self.retain_first_lowering_refusal(
                            OpLoweringRefusal::MissingProgramVariableAuthorization,
                        );
                        None
                    }
                })
        };
        let rendered = match value
            .value_id()
            .and_then(|value_id| self.semantic_value_for_value_id(value_id))
        {
            Some(analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr))) => {
                self.render_scalar_value_ref(value, expr.clone(), fallback.clone())
            }
            Some(analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(root))) => {
                self.render_value_ref(root, depth + 1, visited)
            }
            Some(analysis::SemanticValue::Address(shape)) => {
                self.render_address_expr_from_addr(shape, depth + 1, visited)
            }
            Some(analysis::SemanticValue::Load { space, addr, size }) => {
                self.render_semantic_load(*space, addr, *size, depth + 1, visited)
            }
            Some(analysis::SemanticValue::Unknown) | None => None,
        }
        .or(fallback);
        let rendered = self.choose_preferred_visible_expr(rendered, forwarded);

        self.value_render_in_progress.borrow_mut().remove(&name);
        visited.remove(&visit_key);
        rendered
    }

    fn render_base_ref_expr(
        &self,
        base: &analysis::BaseRef,
        as_address: bool,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        match base {
            analysis::BaseRef::Value(value) => self.render_value_ref(value, depth + 1, visited),
            analysis::BaseRef::StackSlot(offset) => {
                let _ = as_address;
                let _ = self.refuse_missing_stack_object_origin(*offset);
                None
            }
            analysis::BaseRef::Raw(expr) => Some(expr.clone()),
        }
    }

    fn prepared_named_expr_for_memory_location(&self, location: &MemoryLocation) -> Option<CExpr> {
        let object = self.prepared_objects()?.object(location.object)?;
        match &object.kind {
            ObjectKind::Global { .. } => None,
            ObjectKind::StackSlot { offset, .. } | ObjectKind::FrameObject { offset, .. }
                if location.address.exact_offset() == Some(0) =>
            {
                let _ = offset;
                self.certified_stack_var_expr_for_object(location.object)
            }
            _ => None,
        }
    }

    fn prepared_named_memory_expr_for_value(&self, var: &SSAVar) -> Option<CExpr> {
        let prepared = self.inputs.prepared_ssa?;
        let value = prepared.graph().value_id_for_var(var)?;
        let inst = prepared.graph().def_inst(value)?;
        let (block_addr, op_idx) = prepared.inst_op_site(inst)?;
        let uses = prepared.memory_uses_for_op_site(block_addr, op_idx)?;
        (uses.len() == 1)
            .then_some(&uses[0])
            .and_then(|fact| self.prepared_named_expr_for_memory_location(&fact.location))
    }

    fn prepared_named_object_expr_for_addr(
        &self,
        addr: &analysis::NormalizedAddr,
    ) -> Option<CExpr> {
        if addr.index.is_some() {
            return None;
        }

        match &addr.base {
            analysis::BaseRef::Value(base_ref) if addr.offset_bytes == 0 => {
                let prepared = self.inputs.prepared_ssa?;
                let object = prepared
                    .object_for_var(&base_ref.var, r2il::SpaceId::Ram)
                    .or_else(|| {
                        self.prepared_canonical_value_root(&base_ref.var)
                            .and_then(|root| prepared.object_for_var(&root, r2il::SpaceId::Ram))
                    })?;
                self.prepared_named_expr_for_memory_location(&MemoryLocation {
                    space: r2il::SpaceId::Ram,
                    object,
                    address: r2ssa::RelativeMemoryAddress::Exact(0),
                    size: 0,
                })
            }
            _ => None,
        }
    }

    fn allow_exact_named_object_expr_for_load_addr(&self, addr: &analysis::NormalizedAddr) -> bool {
        let analysis::BaseRef::Value(base_ref) = &addr.base else {
            return true;
        };
        if addr.index.is_some() || addr.offset_bytes != 0 {
            return true;
        }

        let mut visited = HashSet::new();
        let root = self
            .semantic_root_var(&base_ref.var, 0, &mut visited)
            .unwrap_or_else(|| base_ref.var.clone());
        !matches!(
            self.type_hint_for_var(&root)
                .or_else(|| self.type_hint_for_var(&base_ref.var)),
            Some(CType::Pointer(_)) | Some(CType::Array(_, _))
        )
    }

    fn exact_named_object_expr_for_addr(&self, addr: &analysis::NormalizedAddr) -> Option<CExpr> {
        self.prepared_named_object_expr_for_addr(addr)
    }

    fn render_scalar_value_ref(
        &self,
        value: &analysis::ValueRef,
        semantic: CExpr,
        fallback: Option<CExpr>,
    ) -> Option<CExpr> {
        if !value.var.is_const()
            && (matches!(semantic, CExpr::IntLit(0) | CExpr::UIntLit(0))
                || self.expr_contains_synthetic_stack_placeholder(&semantic)
                || self.is_uninitialized_return_reg(&semantic))
        {
            fallback
        } else {
            Some(semantic)
        }
    }

    fn expr_contains_synthetic_stack_placeholder(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Observed { expr, .. } => self.expr_contains_synthetic_stack_placeholder(expr),
            CExpr::External { .. } => false,
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                lower == "stack" || lower == "saved_fp" || lower.starts_with("stack_")
            }
            CExpr::Paren(inner) | CExpr::AddrOf(inner) | CExpr::Deref(inner) => {
                self.expr_contains_synthetic_stack_placeholder(inner)
            }
            CExpr::Cast { expr: inner, .. } | CExpr::Unary { operand: inner, .. } => {
                self.expr_contains_synthetic_stack_placeholder(inner)
            }
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_synthetic_stack_placeholder(left)
                    || self.expr_contains_synthetic_stack_placeholder(right)
            }
            CExpr::Subscript { base, index } => {
                self.expr_contains_synthetic_stack_placeholder(base)
                    || self.expr_contains_synthetic_stack_placeholder(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_synthetic_stack_placeholder(base)
            }
            CExpr::Call { func, args, .. } => {
                self.expr_contains_synthetic_stack_placeholder(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_contains_synthetic_stack_placeholder(arg))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_contains_synthetic_stack_placeholder(cond)
                    || self.expr_contains_synthetic_stack_placeholder(then_expr)
                    || self.expr_contains_synthetic_stack_placeholder(else_expr)
            }
            CExpr::Comma(exprs) => exprs
                .iter()
                .any(|inner| self.expr_contains_synthetic_stack_placeholder(inner)),
            CExpr::Sizeof(inner) => self.expr_contains_synthetic_stack_placeholder(inner),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn stack_offset_for_normalized_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        _depth: u32,
        _visited: &mut HashSet<String>,
    ) -> Option<i64> {
        if addr.index.is_none()
            && let analysis::BaseRef::StackSlot(base) = addr.base
        {
            return base.checked_add(addr.offset_bytes);
        }
        None
    }

    fn render_address_expr_from_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        let stack_slot_addr_alias = |ctx: &FoldingContext<'_>, offset: i64| {
            let _ = ctx.refuse_missing_stack_object_origin(offset);
            None
        };

        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_addr_alias(self, full_offset)
        {
            return Some(alias);
        }

        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
            && Self::expr_supports_addr_of(&rendered)
        {
            return Some(CExpr::AddrOf(Box::new(rendered)));
        }

        let effective_addr = addr.clone();
        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_addr_alias(self, full_offset)
        {
            return Some(alias);
        }
        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
            && Self::expr_supports_addr_of(&rendered)
        {
            return Some(CExpr::AddrOf(Box::new(rendered)));
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(alias) = stack_slot_addr_alias(self, full_offset)
        {
            return Some(alias);
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
            && Self::expr_supports_addr_of(&rendered)
        {
            return Some(CExpr::AddrOf(Box::new(rendered)));
        }

        let mut expr = self.render_base_ref_expr(&effective_addr.base, true, depth + 1, visited)?;
        if let Some(index) = &effective_addr.index {
            let index_expr = self.render_value_ref(index, depth + 1, visited)?;
            let scaled = if effective_addr.scale_bytes.unsigned_abs() <= 1 {
                index_expr
            } else {
                CExpr::binary(
                    BinaryOp::Mul,
                    index_expr,
                    CExpr::IntLit(effective_addr.scale_bytes.unsigned_abs() as i64),
                )
            };
            expr = CExpr::binary(
                if effective_addr.scale_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                expr,
                scaled,
            );
        }
        if effective_addr.offset_bytes != 0 {
            expr = CExpr::binary(
                if effective_addr.offset_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                expr,
                CExpr::IntLit(effective_addr.offset_bytes.unsigned_abs() as i64),
            );
        }
        Some(expr)
    }

    fn expr_supports_addr_of(expr: &CExpr) -> bool {
        matches!(
            expr,
            CExpr::Var(_)
                | CExpr::Subscript { .. }
                | CExpr::Member { .. }
                | CExpr::PtrMember { .. }
        )
    }

    fn oracle_field_name_for_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        access_size: Option<u32>,
    ) -> Option<String> {
        if addr.offset_bytes < 0 {
            return None;
        }
        let offset = addr.offset_bytes as u64;

        match &addr.base {
            analysis::BaseRef::Value(base_ref) => {
                let mut visited = HashSet::new();
                if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited)
                    && let Some(field) = self
                        .field_name_from_type_hint_for_var(&root, offset, access_size)
                        .or_else(|| {
                            self.field_name_from_type_hint_for_var(
                                &base_ref.var,
                                offset,
                                access_size,
                            )
                        })
                {
                    return Some(field);
                }

                if let Some(field) =
                    self.field_name_from_type_hint_for_var(&base_ref.var, offset, access_size)
                {
                    return Some(field);
                }

                if let Some(oracle) = self.inputs.type_oracle
                    && let Some(field) = oracle
                        .field_name(oracle.type_of(&base_ref.var), offset)
                        .map(|field| field.to_string())
                {
                    return Some(field);
                }

                let mut visited = HashSet::new();
                if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited)
                    && let Some(oracle) = self.inputs.type_oracle
                    && let Some(field) = oracle
                        .field_name(oracle.type_of(&root), offset)
                        .map(|field| field.to_string())
                {
                    return Some(field);
                }
            }
            analysis::BaseRef::Raw(CExpr::Var(_)) => {}
            analysis::BaseRef::StackSlot(_) | analysis::BaseRef::Raw(_) => {}
        }

        None
    }
    fn field_name_from_type_hint_for_var(
        &self,
        var: &SSAVar,
        offset: u64,
        access_size: Option<u32>,
    ) -> Option<String> {
        let hint = self.type_hint_for_var(var)?;
        self.field_name_from_type_hint(&hint, offset, access_size)
    }

    fn field_name_from_type_hint(
        &self,
        ty: &CType,
        offset: u64,
        access_size: Option<u32>,
    ) -> Option<String> {
        match ty {
            CType::Pointer(inner) | CType::Array(inner, _) => {
                self.field_name_from_type_hint(inner, offset, access_size)
            }
            CType::Struct(name) | CType::Union(name) | CType::Typedef(name) => {
                self.lookup_external_field_name(name, offset, access_size)
            }
            _ => None,
        }
    }

    fn certified_field_name_for_offset(
        &self,
        field_name: String,
        _offset: i64,
        _access_size: Option<u32>,
        _is_write: bool,
    ) -> Option<String> {
        Some(field_name)
    }

    pub(super) fn certified_member_field_name_for_current_op_offset(
        &self,
        _offset: i64,
        _access_size: Option<u32>,
        _is_write: bool,
    ) -> Option<String> {
        None
    }

    fn certified_array_access_for_current_op(
        &self,
        _field_offset: i64,
        _element_stride: u64,
        _access_size: Option<u32>,
        _is_write: bool,
    ) -> bool {
        true
    }
    fn lookup_external_field_name(
        &self,
        type_name: &str,
        offset: u64,
        access_size: Option<u32>,
    ) -> Option<String> {
        let key = type_name.trim().to_ascii_lowercase();
        if let Some(st) = self.inputs.external_type_db.structs.get(&key)
            && let Some(field) = external_struct_field_name_for_offset(
                st,
                offset,
                access_size,
                self.inputs.arch.ptr_size,
            )
        {
            return Some(field);
        }
        if let Some(un) = self.inputs.external_type_db.unions.get(&key)
            && let Some(field) = external_union_field_name_for_offset(
                un,
                offset,
                access_size,
                self.inputs.arch.ptr_size,
            )
        {
            return Some(field);
        }
        let normalized = normalize_external_type_name(type_name);
        if normalized != key {
            let normalized_key = normalized.trim().to_ascii_lowercase();
            if let Some(st) = self.inputs.external_type_db.structs.get(&normalized_key)
                && let Some(field) = external_struct_field_name_for_offset(
                    st,
                    offset,
                    access_size,
                    self.inputs.arch.ptr_size,
                )
            {
                return Some(field);
            }
            if let Some(un) = self.inputs.external_type_db.unions.get(&normalized_key)
                && let Some(field) = external_union_field_name_for_offset(
                    un,
                    offset,
                    access_size,
                    self.inputs.arch.ptr_size,
                )
            {
                return Some(field);
            }
        }
        None
    }
    fn semantic_root_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<SSAVar> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        let value_id = self.prepared_value_id_for_var(var)?;
        let visit_key = format!("value:{value_id:?}");
        if !visited.insert(visit_key.clone()) {
            return None;
        }

        let resolved = self
            .forwarded_value_for_value_id(value_id)
            .and_then(|provenance| provenance.source_var.clone())
            .and_then(|source| {
                self.semantic_root_var(&source, depth + 1, visited)
                    .or(Some(source))
            })
            .or_else(|| match self.semantic_value_for_value_id(value_id) {
                Some(analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(root))) => self
                    .semantic_root_var(&root.var, depth + 1, visited)
                    .or_else(|| Some(root.var.clone())),
                Some(analysis::SemanticValue::Address(analysis::NormalizedAddr {
                    base: analysis::BaseRef::Value(root),
                    ..
                })) => self
                    .semantic_root_var(&root.var, depth + 1, visited)
                    .or_else(|| Some(root.var.clone())),
                _ => None,
            });

        visited.remove(&visit_key);
        resolved
    }

    fn render_access_expr_from_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        elem_size: u32,
        is_write: bool,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let stack_slot_access_alias = |ctx: &FoldingContext<'_>, offset: i64| {
            let _ = ctx.refuse_missing_stack_object_origin(offset);
            None
        };

        if let Some(exact) = self.exact_named_object_expr_for_addr(addr) {
            if !matches!(addr.base, analysis::BaseRef::StackSlot(_))
                && addr.index.is_none()
                && let Some(field) = self
                    .oracle_field_name_for_addr(addr, Some(elem_size))
                    .or_else(|| {
                        self.oracle_member_name(None, &exact, addr.offset_bytes, Some(elem_size))
                    })
                    .and_then(|field| {
                        self.certified_field_name_for_offset(
                            field,
                            addr.offset_bytes,
                            Some(elem_size),
                            is_write,
                        )
                    })
            {
                return Some(self.member_access_expr(exact, field));
            }
            return Some(exact);
        }

        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }

        if let Some(full_offset) = self.stack_offset_for_normalized_addr(addr, depth + 1, visited)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }

        if addr.index.is_none()
            && let Some(full_offset) = match addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }
        if addr.index.is_none()
            && let Some(full_offset) = match addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(addr.offset_bytes),
                _ => None,
            }
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }

        let raw_base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
        let effective_addr = addr.clone();
        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }
        if let Some(full_offset) =
            self.stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }
        let base_expr = if effective_addr != *addr {
            self.render_base_ref_expr(&effective_addr.base, false, depth + 1, visited)
                .unwrap_or_else(|| raw_base_expr.clone())
        } else {
            raw_base_expr
        };
        let field_name = if matches!(effective_addr.base, analysis::BaseRef::StackSlot(_)) {
            None
        } else {
            self.oracle_field_name_for_addr(&effective_addr, Some(elem_size))
                .or_else(|| {
                    self.expr_type_hint(&base_expr).and_then(|ty| {
                        self.field_name_from_type_hint(
                            &ty,
                            effective_addr.offset_bytes as u64,
                            Some(elem_size),
                        )
                    })
                })
                .or_else(|| {
                    self.certified_member_field_name_for_current_op_offset(
                        effective_addr.offset_bytes,
                        Some(elem_size),
                        is_write,
                    )
                })
                .or_else(|| {
                    self.oracle_member_name(
                        None,
                        &base_expr,
                        effective_addr.offset_bytes,
                        Some(elem_size),
                    )
                })
                .and_then(|field| {
                    self.certified_field_name_for_offset(
                        field,
                        effective_addr.offset_bytes,
                        Some(elem_size),
                        is_write,
                    )
                })
        };

        if let Some(index) = &effective_addr.index {
            let scale = effective_addr.scale_bytes.unsigned_abs() as u32;

            let mut index_expr = self.render_value_ref(index, depth + 1, visited)?;
            let mut elem_ty =
                self.infer_elem_type_from_base_ref(&effective_addr.base, scale.max(elem_size));
            let mut normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
            if effective_addr.scale_bytes >= 0
                && self.should_swap_indexed_access_base(&normalized_base, &index_expr)
            {
                std::mem::swap(&mut normalized_base, &mut index_expr);
                if let Some(swapped_ty) =
                    self.expr_type_hint(&normalized_base)
                        .and_then(|ty| match ty {
                            CType::Pointer(inner) | CType::Array(inner, _) => Some(*inner),
                            _ => None,
                        })
                {
                    elem_ty = swapped_ty;
                }
            }
            let base_source_ty = self.expr_type_hint(&normalized_base);
            let base_cast = self.cast_expr_if_needed(
                normalized_base,
                CType::ptr(elem_ty),
                base_source_ty.as_ref(),
            );
            let index_final = if effective_addr.scale_bytes < 0 {
                CExpr::unary(UnaryOp::Neg, index_expr)
            } else {
                index_expr
            };
            let indexed = CExpr::Subscript {
                base: Box::new(base_cast),
                index: Box::new(index_final),
            };
            if let Some(field) = field_name {
                return Some(self.member_access_expr(indexed, field));
            }
            if effective_addr.offset_bytes == 0 {
                return Some(indexed);
            }
        }

        if effective_addr.index.is_none()
            && effective_addr.offset_bytes != 0
            && field_name.is_none()
            && !matches!(effective_addr.base, analysis::BaseRef::StackSlot(_))
            && Self::expr_is_simple_constant_offset_base(&base_expr)
        {
            let elem_ty = self.infer_elem_type_from_base_ref(&effective_addr.base, elem_size);
            let elem_bytes = elem_ty
                .bits()
                .map(|bits| bits.div_ceil(8).max(1))
                .unwrap_or(elem_size.max(1));
            if self.can_render_constant_offset_as_subscript(&elem_ty)
                && elem_bytes > 0
                && effective_addr.offset_bytes % i64::from(elem_bytes) == 0
                && self.certified_array_access_for_current_op(
                    0,
                    u64::from(elem_bytes),
                    Some(elem_size),
                    is_write,
                )
            {
                let normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
                let base_source_ty = self.expr_type_hint(&normalized_base);
                let base_cast = self.cast_expr_if_needed(
                    normalized_base,
                    CType::ptr(elem_ty),
                    base_source_ty.as_ref(),
                );
                let index = effective_addr.offset_bytes / i64::from(elem_bytes);
                let index_expr = if index < 0 {
                    CExpr::unary(UnaryOp::Neg, CExpr::IntLit(index.unsigned_abs() as i64))
                } else {
                    CExpr::IntLit(index)
                };
                return Some(CExpr::Subscript {
                    base: Box::new(base_cast),
                    index: Box::new(index_expr),
                });
            }
        }

        if let Some(field) = field_name {
            return Some(self.member_access_expr(base_expr, field));
        }

        if matches!(effective_addr.base, analysis::BaseRef::StackSlot(_))
            && effective_addr.index.is_none()
            && effective_addr.offset_bytes == 0
        {
            return Some(base_expr);
        }

        None
    }

    /// Whether an expression reads memory, so it can stand in for a dereference.
    fn expr_is_simple_constant_offset_base(expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(_) => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_simple_constant_offset_base(inner)
            }
            _ => false,
        }
    }

    fn can_render_constant_offset_as_subscript(&self, elem_ty: &CType) -> bool {
        match elem_ty {
            CType::Unknown | CType::Void => false,
            CType::Struct(_) | CType::Union(_) => false,
            CType::Pointer(_) | CType::Array(_, _) => true,
            _ => true,
        }
    }

    fn should_render_zero_offset_load_as_subscript(
        &self,
        base_expr: &CExpr,
        elem_ty: &CType,
    ) -> bool {
        let has_subscriptable_base = match self.expr_type_hint(base_expr) {
            Some(CType::Array(_, _)) => true,
            Some(CType::Pointer(inner)) => {
                matches!(inner.as_ref(), CType::Pointer(_) | CType::Array(_, _))
            }
            _ => false,
        };
        has_subscriptable_base && self.can_render_constant_offset_as_subscript(elem_ty)
    }

    fn render_semantic_load(
        &self,
        space: r2il::SpaceId,
        addr: &analysis::NormalizedAddr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if space != r2il::SpaceId::Ram {
            // Semantic values are an advisory expression cache. The sealed
            // MachineProjection is the only authority that may admit a load;
            // omitting this cache entry cannot create executable fallback C.
            return None;
        }
        self.render_load_from_addr(addr, elem_size, depth, visited)
    }

    fn render_load_from_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if let Some(index) = &addr.index
            && addr.offset_bytes >= 0
            && !matches!(addr.base, analysis::BaseRef::StackSlot(_))
            && self.certified_array_access_for_current_op(
                addr.offset_bytes,
                addr.scale_bytes
                    .unsigned_abs()
                    .max(u64::from(elem_size).max(1)),
                Some(elem_size),
                false,
            )
            && let Some(field) = self
                .oracle_field_name_for_addr(addr, Some(elem_size))
                .and_then(|field| {
                    self.certified_field_name_for_offset(
                        field,
                        addr.offset_bytes,
                        Some(elem_size),
                        false,
                    )
                })
        {
            let base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
            let index_expr = self.render_value_ref(index, depth + 1, visited)?;
            let elem_ty = self.infer_elem_type_from_base_ref(
                &addr.base,
                (addr.scale_bytes.unsigned_abs() as u32).max(elem_size),
            );
            let normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
            let base_source_ty = self.expr_type_hint(&normalized_base);
            let base_cast = self.cast_expr_if_needed(
                normalized_base,
                CType::ptr(elem_ty),
                base_source_ty.as_ref(),
            );
            let index_final = if addr.scale_bytes < 0 {
                CExpr::unary(UnaryOp::Neg, index_expr)
            } else {
                index_expr
            };
            let indexed = CExpr::Subscript {
                base: Box::new(base_cast),
                index: Box::new(index_final),
            };
            return Some(self.member_access_expr(indexed, field));
        }

        let direct_access = if self.allow_exact_named_object_expr_for_load_addr(addr) {
            self.render_access_expr_from_addr(addr, elem_size, false, depth, visited)
        } else if let Some(probe) = self.exact_named_object_expr_for_addr(addr) {
            let probe_base = self.render_base_ref_expr(&addr.base, false, depth + 1, visited);
            (probe_base.as_ref() != Some(&probe))
                .then(|| self.render_access_expr_from_addr(addr, elem_size, false, depth, visited))
                .flatten()
        } else {
            self.render_access_expr_from_addr(addr, elem_size, false, depth, visited)
        };

        direct_access
            .or_else(|| {
                if addr.index.is_some()
                    || addr.offset_bytes != 0
                    || matches!(addr.base, analysis::BaseRef::StackSlot(_))
                {
                    return None;
                }

                let base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
                let normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
                let elem_ty = self.infer_elem_type_from_base_ref(&addr.base, elem_size.max(1));
                let elem_bytes = elem_ty
                    .bits()
                    .map(|bits| bits.div_ceil(8).max(1))
                    .unwrap_or(elem_size.max(1));
                if !self.certified_array_access_for_current_op(
                    0,
                    u64::from(elem_bytes),
                    Some(elem_size),
                    false,
                ) {
                    return None;
                }
                if !self.should_render_zero_offset_load_as_subscript(&normalized_base, &elem_ty) {
                    return None;
                }
                let base_source_ty = self.expr_type_hint(&normalized_base);
                let base_cast = self.cast_expr_if_needed(
                    normalized_base,
                    CType::ptr(elem_ty),
                    base_source_ty.as_ref(),
                );
                Some(CExpr::Subscript {
                    base: Box::new(base_cast),
                    index: Box::new(CExpr::IntLit(0)),
                })
            })
            .or_else(|| {
                self.render_address_expr_from_addr(addr, depth + 1, visited)
                    .map(|expr| CExpr::Deref(Box::new(expr)))
            })
    }
    fn render_memory_access_by_name(
        &self,
        name: &str,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let value = self.lookup_semantic_value(name)?;
        match value {
            analysis::SemanticValue::Load { space, addr, size } => {
                self.render_semantic_load(*space, addr, *size, depth, visited)
            }
            analysis::SemanticValue::Address(shape) => {
                self.render_load_from_addr(shape, elem_size, depth, visited)
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => {
                Some(expr.clone())
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(value_ref)) => {
                self.render_value_ref(value_ref, depth, visited)
            }
            analysis::SemanticValue::Unknown => None,
        }
    }

    fn infer_elem_type_from_base_ref(&self, base: &analysis::BaseRef, element_size: u32) -> CType {
        match base {
            analysis::BaseRef::Value(base_ref) => {
                if let Some(CType::Pointer(inner) | CType::Array(inner, _)) =
                    self.type_hint_for_var(&base_ref.var)
                {
                    return *inner;
                }
                if let Some(oracle) = self.inputs.type_oracle {
                    let mut visited = HashSet::new();
                    if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited) {
                        if let Some(CType::Pointer(inner) | CType::Array(inner, _)) =
                            self.type_hint_for_var(&root)
                        {
                            return *inner;
                        }
                        let ty = oracle.type_of(&root);
                        if (oracle.is_array(ty) || oracle.is_pointer(ty))
                            && let Some(CType::Pointer(inner) | CType::Array(inner, _)) =
                                self.type_hint_for_var(&root)
                        {
                            return *inner;
                        }
                    }
                }
                self.infer_subscript_elem_type(&base_ref.var, element_size)
            }
            analysis::BaseRef::Raw(CExpr::Var(_)) => uint_type_from_size(element_size),
            analysis::BaseRef::StackSlot(_) | analysis::BaseRef::Raw(_) => {
                uint_type_from_size(element_size)
            }
        }
    }

    fn infer_subscript_elem_type(&self, base: &SSAVar, element_size: u32) -> CType {
        if let Some(oracle) = self.inputs.type_oracle {
            let base_ty = oracle.type_of(base);
            if (oracle.is_array(base_ty) || oracle.is_pointer(base_ty))
                && let Some(hint) = self.type_hint_for_var(base)
            {
                match hint {
                    CType::Pointer(inner) | CType::Array(inner, _) => return *inner,
                    _ => {}
                }
            }
        }
        uint_type_from_size(element_size)
    }

    /// The member an address names, given how wide the access through it is.
    ///
    /// An offset alone does not identify a member. Without the access width an
    /// eight-byte pointer load at offset zero took the name of the four-byte
    /// member sharing that offset, so `return head` rendered as
    /// `return head->value`, a dereference the machine never performed.
    fn oracle_member_name(
        &self,
        addr: Option<&SSAVar>,
        base_expr: &CExpr,
        offset: i64,
        access_size: Option<u32>,
    ) -> Option<String> {
        if offset < 0 {
            return None;
        }
        let offset = offset as u64;

        if let Some(name) = self.visible_pointer_root_field_name(base_expr, offset, access_size, 0)
        {
            return Some(name);
        }

        // Best-effort: prefer base pointer identities captured during analysis.
        if let Some(addr) = addr
            && let Some((base, mapped_offset)) = self.ptr_members_map().get(&addr.display_name())
            && *mapped_offset == offset as i64
        {
            if let Some(oracle) = self.inputs.type_oracle {
                let base_ty = oracle.type_of(base);
                if let Some(name) = oracle.field_name(base_ty, offset) {
                    return Some(name.to_string());
                }
            }
            if let Some(name) = self.field_name_from_type_hint_for_var(base, offset, access_size) {
                return Some(name);
            }
        }

        if let Some(addr) = addr
            && offset == 0
            && let Some(name) = self
                .inputs
                .type_oracle
                .and_then(|oracle| oracle.field_name(oracle.type_of(addr), offset))
        {
            return Some(name.to_string());
        }

        None
    }

    fn visible_pointer_root_field_name(
        &self,
        expr: &CExpr,
        offset: u64,
        access_size: Option<u32>,
        depth: u32,
    ) -> Option<String> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        match expr {
            CExpr::Var(_) => None,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.visible_pointer_root_field_name(inner, offset, access_size, depth + 1)
            }
            CExpr::Binary { left, right, .. } => self
                .visible_pointer_root_field_name(left, offset, access_size, depth + 1)
                .or_else(|| {
                    self.visible_pointer_root_field_name(right, offset, access_size, depth + 1)
                }),
            CExpr::Subscript { base, .. }
            | CExpr::Member { base, .. }
            | CExpr::PtrMember { base, .. } => {
                self.visible_pointer_root_field_name(base, offset, access_size, depth + 1)
            }
            CExpr::Deref(inner) | CExpr::AddrOf(inner) | CExpr::Sizeof(inner) => {
                self.visible_pointer_root_field_name(inner, offset, access_size, depth + 1)
            }
            CExpr::Unary { operand, .. } => {
                self.visible_pointer_root_field_name(operand, offset, access_size, depth + 1)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => self
                .visible_pointer_root_field_name(cond, offset, access_size, depth + 1)
                .or_else(|| {
                    self.visible_pointer_root_field_name(then_expr, offset, access_size, depth + 1)
                })
                .or_else(|| {
                    self.visible_pointer_root_field_name(else_expr, offset, access_size, depth + 1)
                }),
            CExpr::Comma(items) => items.iter().find_map(|item| {
                self.visible_pointer_root_field_name(item, offset, access_size, depth + 1)
            }),
            _ => None,
        }
    }

    pub(crate) fn stack_offset_for_visible_storage_name(&self, name: &str) -> Option<i64> {

        let lower = name.to_ascii_lowercase();
        if lower == "stack" {
            return Some(0);
        }
        if lower == "saved_fp" {
            return Some(0);
        }
        if let Some(rest) = lower.strip_prefix("stack_")
            && let Ok(offset) = i64::from_str_radix(rest, 16)
        {
            return Some(offset);
        }
        if let Some(rest) = lower.strip_prefix("local_")
            && let Ok(offset) = i64::from_str_radix(rest, 16)
        {
            return Some(-offset);
        }
        if let Some(rest) = lower.strip_prefix("arg_")
            && let Ok(offset) = i64::from_str_radix(rest, 16)
        {
            return Some(-offset);
        }
        if let Some((offset, _)) = self
            .stack_vars_map()
            .iter()
            .find(|(_, candidate)| candidate.eq_ignore_ascii_case(name))
        {
            return Some(*offset);
        }
        self.canonical_stack_offset_for_visible_storage_name(name)
    }

    fn canonical_stack_offset_for_visible_storage_name(&self, name: &str) -> Option<i64> {
        if let Some(offset) = self
            .inputs
            .visible_bindings
            .iter()
            .find(|binding| binding.name.eq_ignore_ascii_case(name))
            .and_then(|binding| binding.stack_slot.as_ref())
            .map(|slot| match slot.base {
                ExternalStackBase::FramePointer => -slot.offset,
                _ => slot.offset,
            })
        {
            return Some(offset);
        }
        if let Some(offset) = self
            .inputs
            .stack_slots
            .iter()
            .find(|(_, var)| var.name.eq_ignore_ascii_case(name))
            .map(|(slot_key, _)| match slot_key.base {
                ExternalStackBase::FramePointer => -slot_key.offset,
                _ => slot_key.offset,
            })
        {
            return Some(offset);
        }
        None
    }

    fn stack_offsets_for_visible_storage_name(&self, name: crate::symbol::SymbolId) -> Vec<i64> {
        let name_id = name;
        let name = &self.spelling(name_id);

        let mut offsets = Vec::new();
        if let Some(offset) = self.stack_offset_for_visible_storage_name(&self.spelling(name_id)) {
            offsets.push(offset);
        }

        if let Some(offset) = self.canonical_stack_offset_for_visible_storage_name(name)
            && !offsets.contains(&offset)
        {
            offsets.push(offset);
        }
        offsets
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

    fn normalize_pointer_base_expr(&self, expr: &CExpr, depth: u32) -> CExpr {
        if depth > 4 {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => self
                .lookup_definition(&self.spelling(*name))
                .map(|inner| self.normalize_pointer_base_expr(&inner, depth + 1))
                .filter(|inner| self.looks_like_pointer(inner))
                .unwrap_or_else(|| expr.clone()),
            CExpr::Paren(inner) => {
                CExpr::Paren(Box::new(self.normalize_pointer_base_expr(inner, depth + 1)))
            }
            CExpr::Cast { ty, expr: inner } => CExpr::Cast {
                ty: ty.clone(),
                expr: Box::new(self.normalize_pointer_base_expr(inner, depth + 1)),
            },
            _ => expr.clone(),
        }
    }

    fn should_swap_indexed_access_base(&self, base_expr: &CExpr, index_expr: &CExpr) -> bool {
        let base_pointer =
            self.looks_like_pointer(base_expr) || self.is_non_index_pointer_expr(base_expr);
        let index_pointer =
            self.looks_like_pointer(index_expr) || self.is_non_index_pointer_expr(index_expr);
        !base_pointer && index_pointer
    }

    fn is_non_index_pointer_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_) | CExpr::Subscript { .. } | CExpr::PtrMember { .. } => true,
            CExpr::Var(_) => false,
            CExpr::Paren(inner) => self.is_non_index_pointer_expr(inner),
            CExpr::Unary { operand, .. } => self.is_non_index_pointer_expr(operand),
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
            r2ssa::ValueOwner::Value(value) => {
                match self.planned_value_expr(*value) {
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

    pub(super) fn stable_owned_call_result_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        self.certified_assigned_call_result_owner_expr_for_source(source_call)
    }

    pub(crate) fn call_result_source_for_var(&self, var: &SSAVar) -> Option<(u64, usize)> {
        self.prepared_semantic_view()?.call_result_source_for_var(var)
    }

    pub(super) fn stable_owned_call_result_expr_for_var(
        &self,
        var: &SSAVar,
    ) -> Option<CExpr> {
        let source_call = self.call_result_source_for_var(var)?;
        self.stable_owned_call_result_expr_for_source(source_call)
    }

    fn expr_is_stack_base_like(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Observed { expr, .. } => self.expr_is_stack_base_like(expr),
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                self.inputs.arch.is_stack_base_name(&lower)
                    || self.inputs.arch.is_frame_pointer_name(&lower)
                    || lower == "stack"
                    || lower == "saved_fp"
                    || is_generic_stack_placeholder_alias(&self.spelling(*name))
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.expr_is_stack_base_like(inner)
            }
            CExpr::Unary { operand, .. } => self.expr_is_stack_base_like(operand),
            _ => false,
        }
    }

    fn expr_contains_raw_stack_base_arithmetic(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Observed { expr, .. } => self.expr_contains_raw_stack_base_arithmetic(expr),
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => {
                self.expr_is_stack_base_like(left)
                    || self.expr_is_stack_base_like(right)
                    || self.expr_contains_raw_stack_base_arithmetic(left)
                    || self.expr_contains_raw_stack_base_arithmetic(right)
            }
            CExpr::Paren(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Deref(inner)
            | CExpr::Cast { expr: inner, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(inner)
            }
            CExpr::Unary { operand, .. } => self.expr_contains_raw_stack_base_arithmetic(operand),
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(left)
                    || self.expr_contains_raw_stack_base_arithmetic(right)
            }
            CExpr::Subscript { base, index } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
                    || self.expr_contains_raw_stack_base_arithmetic(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
            }
            CExpr::Call { func, args, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_contains_raw_stack_base_arithmetic(arg))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_contains_raw_stack_base_arithmetic(cond)
                    || self.expr_contains_raw_stack_base_arithmetic(then_expr)
                    || self.expr_contains_raw_stack_base_arithmetic(else_expr)
            }
            CExpr::Comma(exprs) => exprs
                .iter()
                .any(|inner| self.expr_contains_raw_stack_base_arithmetic(inner)),
            CExpr::Sizeof(inner) => self.expr_contains_raw_stack_base_arithmetic(inner),
            _ => false,
        }
    }

    pub(super) fn expr_is_address_artifact_in_scalar_context(&self, expr: &CExpr) -> bool {
        let expr = expr.unobserved();
        match expr {
            CExpr::AddrOf(_) => true,
            CExpr::Deref(inner) => self.expr_contains_raw_stack_base_arithmetic(inner),
            CExpr::Subscript { base, index } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
                    || self.expr_contains_raw_stack_base_arithmetic(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
            }
            CExpr::Var(_) => false,
            CExpr::Cast { ty, expr: inner } => {
                matches!(ty, CType::Pointer(_))
                    || self.expr_is_address_artifact_in_scalar_context(inner)
            }
            CExpr::Paren(inner) => self.expr_is_address_artifact_in_scalar_context(inner),
            CExpr::Unary { operand, .. } => {
                self.expr_is_address_artifact_in_scalar_context(operand)
            }
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(expr)
                    || self.expr_is_address_artifact_in_scalar_context(left)
                    || self.expr_is_address_artifact_in_scalar_context(right)
            }
            CExpr::Call { func, args, .. } => {
                self.expr_is_address_artifact_in_scalar_context(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_is_address_artifact_in_scalar_context(arg))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_is_address_artifact_in_scalar_context(cond)
                    || self.expr_is_address_artifact_in_scalar_context(then_expr)
                    || self.expr_is_address_artifact_in_scalar_context(else_expr)
            }
            CExpr::Comma(exprs) => exprs
                .iter()
                .any(|inner| self.expr_is_address_artifact_in_scalar_context(inner)),
            CExpr::Sizeof(inner) => self.expr_is_address_artifact_in_scalar_context(inner),
            _ => false,
        }
    }

    pub(crate) fn prefers_visible_expr(&self, current: &CExpr, candidate: &CExpr) -> bool {
        self.prefers_visible_expr_in_context(current, candidate, VisibleExprContext::Generic)
    }

    fn prefers_visible_expr_in_context(
        &self,
        current: &CExpr,
        candidate: &CExpr,
        context: VisibleExprContext,
    ) -> bool {
        self.visible_expr_quality_in_context(candidate, context)
            > self.visible_expr_quality_in_context(current, context)
    }

    pub(super) fn choose_preferred_visible_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            current,
            candidate,
            VisibleExprContext::Generic,
        )
    }
    fn choose_preferred_visible_expr_in_context(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        context: VisibleExprContext,
    ) -> Option<CExpr> {
        match (current, candidate) {
            (None, other) => other,
            (some @ Some(_), None) => some,
            (Some(current_expr), Some(candidate_expr)) => {
                if self.prefers_visible_expr_in_context(&current_expr, &candidate_expr, context) {
                    Some(candidate_expr)
                } else {
                    Some(current_expr)
                }
            }
        }
    }

    fn should_preserve_address_like_visible_name(&self, name: crate::symbol::SymbolId) -> bool {
        let name_id = name;
        let name = &self.spelling(name_id);

        let Some(stripped) = name.strip_prefix('&') else {
            return false;
        };
        !stripped.is_empty()
            && !self.is_low_signal_visible_name(stripped)
            && !self.is_transient_visible_name(stripped)
            && !is_generic_stack_placeholder_alias(stripped)
    }

    fn visible_expr_quality_in_context(
        &self,
        expr: &CExpr,
        context: VisibleExprContext,
    ) -> VisibleExprQuality {
        let mut quality = VisibleExprQuality::default();
        self.accumulate_visible_expr_quality(expr, &mut quality, 0, context);
        quality
    }

    #[cfg(test)]
    fn debug_visible_expr_quality(
        &self,
        expr: &CExpr,
        context: VisibleExprContext,
    ) -> VisibleExprQuality {
        self.visible_expr_quality_in_context(expr, context)
    }

    fn accumulate_visible_expr_quality(
        &self,
        expr: &CExpr,
        quality: &mut VisibleExprQuality,
        depth: u32,
        context: VisibleExprContext,
    ) {
        if depth > MAX_SIMPLE_EXPR_DEPTH {
            return;
        }

        if let CExpr::Observed { expr, .. } = expr {
            self.accumulate_visible_expr_quality(expr, quality, depth, context);
            return;
        }
        quality.node_penalty -= 1;
        match expr {
            CExpr::Observed { .. } => unreachable!("observation handled before semantic scoring"),
            CExpr::External { .. } => {}
            CExpr::Var(name) => {
                if is_generic_stack_placeholder_alias(&self.spelling(*name)) {
                    quality.generic_stack_penalty -= 8;
                } else if self.is_transient_visible_name(&self.spelling(*name)) {
                    quality.transient_reg_penalty -= 6;
                } else if self.is_low_signal_visible_name(&self.spelling(*name)) {
                    quality.temp_penalty -= 4;
                } else {
                    quality.semantic_names += 3;
                }
            }
            CExpr::Subscript { base, index } => {
                quality.semantic_shapes += 6;
                quality.stable_pointer_shapes += 2;
                if self.is_non_index_pointer_expr(index) {
                    quality.transient_reg_penalty -= 10;
                }
                self.accumulate_visible_expr_quality(base, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(index, quality, depth + 1, context);
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                quality.semantic_shapes += 7;
                quality.stable_pointer_shapes += 2;
                self.accumulate_visible_expr_quality(base, quality, depth + 1, context);
            }
            CExpr::Deref(inner) | CExpr::AddrOf(inner) => {
                quality.stable_pointer_shapes += 1;
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
            }
            CExpr::Cast { expr: inner, .. } => {
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
            }
            CExpr::Paren(inner) | CExpr::Unary { operand: inner, .. } => {
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
            }
            CExpr::Binary { op, left, right } => {
                if matches!(op, BinaryOp::Add | BinaryOp::Sub)
                    && (self.literal_to_i64(left).is_some_and(|lit| lit == 0)
                        || self.literal_to_i64(right).is_some_and(|lit| lit == 0))
                {
                    quality.zero_offset_penalty -= 10;
                }
                self.accumulate_visible_expr_quality(left, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(right, quality, depth + 1, context);
            }
            CExpr::Call { func, args, .. } => {
                self.accumulate_visible_expr_quality(func, quality, depth + 1, context);
                for arg in args {
                    self.accumulate_visible_expr_quality(arg, quality, depth + 1, context);
                }
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.accumulate_visible_expr_quality(cond, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(then_expr, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(else_expr, quality, depth + 1, context);
            }
            CExpr::Comma(exprs) => {
                for inner in exprs {
                    self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
                }
            }
            CExpr::Sizeof(inner) => {
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context)
            }
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => {}
        }
    }

    pub(super) fn is_low_signal_visible_name(&self, name: &str) -> bool {

        let lower = name.to_ascii_lowercase();
        let storage_kind = SSAVarNameKind::classify(&lower);
        let is_temp_family = |prefix: char| {
            lower
                .strip_prefix(prefix)
                .and_then(|rest| {
                    let (head, tail) = rest.split_once('_').unwrap_or((rest, ""));
                    head.chars()
                        .all(|ch| ch.is_ascii_hexdigit())
                        .then_some(tail)
                })
                .is_some_and(|tail| tail.is_empty() || tail.chars().all(|ch| ch.is_ascii_digit()))
        };
        matches!(
            storage_kind,
            SSAVarNameKind::Temporary | SSAVarNameKind::Constant | SSAVarNameKind::Memory
        ) || lower.starts_with("tmp")
            || is_temp_family('t')
            || is_temp_family('v')
    }

    pub(super) fn is_transient_visible_name(&self, name: &str) -> bool {
        if self.is_low_signal_visible_name(name) {
            return false;
        }

        let lower = name.to_ascii_lowercase();
        if self.inputs.arch.is_flag_name(&lower) {
            return true;
        }

        let base = lower.split('_').next().unwrap_or(lower.as_str());
        self.inputs.arch.is_register_like_base_name(base)
            && !Self::is_semantic_binding_name(base)
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
            CExpr::Call { func, .. } => self
                .known_signature_for_callee_expr(func)
                .map(|sig| crate::variable::type_like_to_ctype(&sig.return_type)),
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

    fn should_preserve_indirect_local_deref(&self, expr: &CExpr) -> bool {
        matches!(
            self.expr_type_hint(expr),
            Some(CType::Pointer(_)) | Some(CType::Array(_, _))
        )
    }

    fn typed_deref_expr(&self, addr: &SSAVar, addr_expr: CExpr, elem_ty: CType) -> CExpr {
        if let Some(indexed) = self.indexed_pointer_add_expr(&addr_expr, &elem_ty) {
            return indexed;
        }
        let ptr_ty = CType::ptr(elem_ty);
        let casted = self.cast_addr_expr_to_ptr_if_needed(addr, addr_expr, &ptr_ty);
        CExpr::Deref(Box::new(casted))
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

    fn collapse_scalar_stack_addr_artifact(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::AddrOf(inner) => {
                if let CExpr::Var(name) = inner.as_ref()
                    && !is_generic_stack_placeholder_alias(&self.spelling(*name))
                    && self.stack_offset_for_visible_storage_name(&self.spelling(*name)).is_some()
                {
                    return CExpr::Var(*name);
                }
                CExpr::AddrOf(Box::new(self.collapse_scalar_stack_addr_artifact(*inner)))
            }
            CExpr::Paren(inner) => {
                CExpr::Paren(Box::new(self.collapse_scalar_stack_addr_artifact(*inner)))
            }
            CExpr::Cast { ty, expr: inner } => {
                CExpr::cast(ty, self.collapse_scalar_stack_addr_artifact(*inner))
            }
            other => {
                other.map_children(&mut |child| self.collapse_scalar_stack_addr_artifact(child))
            }
        }
    }

    fn scalar_stack_placeholder_offset_expr(&self, expr: &CExpr) -> Option<i64> {
        match expr {
            CExpr::Var(name) if should_replace_preserved_stack_alias(&self.spelling(*name)) => {
                self.stack_offset_for_visible_storage_name(&self.spelling(*name))
            }
            CExpr::AddrOf(inner) | CExpr::Paren(inner) => {
                self.scalar_stack_placeholder_offset_expr(inner)
            }
            CExpr::Cast { expr: inner, .. } => self.scalar_stack_placeholder_offset_expr(inner),
            _ => None,
        }
    }

    fn rewrite_scalar_stack_placeholder_rhs(&self, lhs: &CExpr, rhs: CExpr) -> CExpr {
        let CExpr::Var(lhs_name) = lhs else {
            return rhs;
        };
        if is_generic_stack_placeholder_alias(&self.spelling(*lhs_name)) {
            return rhs;
        }
        let Some(lhs_offset) = self.stack_offset_for_visible_storage_name(&self.spelling(*lhs_name)) else {
            return rhs;
        };
        let Some(rhs_offset) = self.scalar_stack_placeholder_offset_expr(&rhs) else {
            return rhs;
        };

        let delta = rhs_offset - lhs_offset;
        if delta == 0 {
            return CExpr::Var(lhs_name.clone());
        }
        rhs
    }

    fn producer_for_value(&self, value: &SSAVar) -> Option<&SSAOp> {
        let prepared = self.prepared_ssa()?;
        let value = prepared.graph().value_id_for_var(value)?;
        let inst = prepared.graph().def_inst(value)?;
        match &prepared.graph().inst(inst)?.payload {
            r2ssa::InstPayload::Op(op) => Some(op),
            r2ssa::InstPayload::Phi { .. } => None,
        }
    }

    fn stack_slot_load_offset_for_value(&self, value: &SSAVar, depth: usize) -> Option<i64> {
        if depth > 8 {
            return None;
        }
        match self.producer_for_value(value)? {
            SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            } => self.stack_slot_offset_for_var(addr),
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. } => self.stack_slot_load_offset_for_value(src, depth + 1),
            _ => None,
        }
    }

    fn value_loads_from_store_addr(
        &self,
        value: &SSAVar,
        store_addr: &SSAVar,
        depth: usize,
    ) -> bool {
        if depth > 8 {
            return false;
        }
        match self.producer_for_value(value) {
            Some(SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            }) => {
                addr == store_addr
                    || self.stack_slot_offset_for_var(addr).is_some()
                        && self.stack_slot_offset_for_var(addr)
                            == self.stack_slot_offset_for_var(store_addr)
            }
            Some(
                SSAOp::Copy { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. }
                | SSAOp::Trunc { src, .. }
                | SSAOp::Cast { src, .. }
                | SSAOp::Subpiece { src, .. },
            ) => self.value_loads_from_store_addr(src, store_addr, depth + 1),
            _ => false,
        }
    }

    fn small_const_delta(value: &SSAVar) -> Option<i64> {
        let raw = parse_const_value(&value.name)?;
        (raw <= 0x1000).then_some(raw as i64)
    }

    fn stack_rmw_rhs_operand_expr(&self, value: &SSAVar) -> Option<CExpr> {
        if let Some(delta) = Self::small_const_delta(value) {
            return Some(CExpr::IntLit(delta));
        }

        let candidate = match self.producer_for_value(value) {
            Some(SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            }) => {
                let elem_ty = self
                    .type_hint_for_var(value)
                    .unwrap_or_else(|| type_from_size(value.size));
                match self.render_canonical_load_expr(value, addr, elem_ty) {
                    Ok(expr) => expr,
                    Err(refusal) => {
                        self.retain_first_lowering_refusal(refusal);
                        return None;
                    }
                }
            }
            _ => self.retain_lowering_result(self.get_expr(value))?,
        };
        (!expr_contains_call(&candidate)).then_some(candidate)
    }

    fn stack_read_modify_write_rhs(
        &self,
        lhs: &CExpr,
        store_addr: &SSAVar,
        val: &SSAVar,
    ) -> Option<CExpr> {
        let CExpr::Var(lhs_name) = lhs else {
            return None;
        };
        let producer = self.producer_for_value(val)?;
        match producer {
            SSAOp::IntAdd { a, b, .. } => {
                if self.value_loads_from_store_addr(a, store_addr, 0) {
                    let rhs = self.stack_rmw_rhs_operand_expr(b)?;
                    if rhs != CExpr::IntLit(0) {
                        return Some(CExpr::binary(
                            BinaryOp::Add,
                            CExpr::Var(*lhs_name),
                            rhs,
                        ));
                    }
                } else if self.value_loads_from_store_addr(b, store_addr, 0) {
                    let rhs = self.stack_rmw_rhs_operand_expr(a)?;
                    if rhs != CExpr::IntLit(0) {
                        return Some(CExpr::binary(
                            BinaryOp::Add,
                            CExpr::Var(*lhs_name),
                            rhs,
                        ));
                    }
                }
            }
            SSAOp::IntSub { a, b, .. } if self.value_loads_from_store_addr(a, store_addr, 0) => {
                let delta = Self::small_const_delta(b)?;
                if delta != 0 {
                    return Some(CExpr::binary(
                        BinaryOp::Sub,
                            CExpr::Var(*lhs_name),
                        CExpr::IntLit(delta),
                    ));
                }
            }
            _ => {}
        }

        for lhs_offset in self.stack_offsets_for_visible_storage_name(*lhs_name) {
            let (base, delta, is_sub) = match producer {
                SSAOp::IntAdd { a, b, .. } => {
                    if self.stack_slot_load_offset_for_value(a, 0) == Some(lhs_offset) {
                        (a, Self::small_const_delta(b)?, false)
                    } else if self.stack_slot_load_offset_for_value(b, 0) == Some(lhs_offset) {
                        (b, Self::small_const_delta(a)?, false)
                    } else {
                        continue;
                    }
                }
                SSAOp::IntSub { a, b, .. } => {
                    if self.stack_slot_load_offset_for_value(a, 0) == Some(lhs_offset) {
                        (a, Self::small_const_delta(b)?, true)
                    } else {
                        continue;
                    }
                }
                _ => return None,
            };
            if delta == 0 || self.stack_slot_load_offset_for_value(base, 0) != Some(lhs_offset) {
                continue;
            }
            let max_delta = self
                .type_hint_for_var(base)
                .and_then(|ty| c_type_size_bytes(&ty, self.inputs.arch.ptr_size))
                .unwrap_or(1)
                .max(1);
            if delta.unsigned_abs() > max_delta {
                continue;
            }
            return Some(CExpr::binary(
                if is_sub { BinaryOp::Sub } else { BinaryOp::Add },
                            CExpr::Var(*lhs_name),
                CExpr::IntLit(delta),
            ));
        }
        None
    }

    fn is_pointer_typed_var(&self, var: &SSAVar) -> bool {
        self.type_hint_for_var(var)
            .is_some_and(|ty| matches!(ty, CType::Pointer(_)))
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

    /// Check if `expr` is a version-0 return register (e.g. `RAX_0`, `EAX_0`,
    /// `XMM0_0`).  These appear in exit blocks when phi nodes merge uninitialized
    /// entry values and should be replaced by the last meaningful computed value.
    pub(crate) fn is_uninitialized_return_reg(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_lowercase();
                lower.ends_with("_0")
                    && self
                        .inputs
                        .arch
                        .is_return_register_name(lower.trim_end_matches("_0"))
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_uninitialized_return_reg(inner)
            }
            _ => false,
        }
    }

    pub(super) fn lookup_definition(&self, name: &str) -> Option<CExpr> {

        if !self.enter_resolution_guard(ResolutionPhase::Definition, name) {
            return self.resolution_cycle_fallback(name);
        }
        let result = self.lookup_definition_with_depth(name, 0, &mut HashSet::new());
        self.leave_resolution_guard(ResolutionPhase::Definition, name);
        result
    }

    fn render_candidate_rank(source: RenderCandidateSource) -> usize {
        match source {
            RenderCandidateSource::ExactNameDefinition => 0,
            RenderCandidateSource::SemanticValue => 1,
            RenderCandidateSource::ForwardedValue => 2,
            RenderCandidateSource::ValueDefinition => 3,
            RenderCandidateSource::RawDefinition => 4,
        }
    }

    fn choose_preferred_render_candidate(
        &self,
        current: Option<RenderCandidate>,
        candidate: Option<RenderCandidate>,
        context: VisibleExprContext,
    ) -> Option<RenderCandidate> {
        match (current, candidate) {
            (None, None) => None,
            (Some(current), None) => Some(current),
            (None, Some(candidate)) => Some(candidate),
            (Some(current), Some(candidate)) => {
                let chosen = self.choose_preferred_visible_expr_in_context(
                    Some(current.expr.clone()),
                    Some(candidate.expr.clone()),
                    context,
                );
                match chosen {
                    Some(expr) if expr == current.expr && expr != candidate.expr => Some(current),
                    Some(expr) if expr == candidate.expr && expr != current.expr => Some(candidate),
                    Some(_) => {
                        if Self::render_candidate_rank(candidate.source)
                            < Self::render_candidate_rank(current.source)
                        {
                            Some(candidate)
                        } else {
                            Some(current)
                        }
                    }
                    None => None,
                }
            }
        }
    }

    fn render_candidate_for_value_id_with_depth(
        &self,
        value_id: r2ssa::ValueId,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<RenderCandidate> {
        let mut best =
            self.definition_for_value_id(value_id)
                .cloned()
                .map(|expr| RenderCandidate {
                    expr,
                    source: RenderCandidateSource::ValueDefinition,
                });

        let mut semantic_visited = visited.clone();
        let semantic = self
            .semantic_value_for_value_id(value_id)
            .and_then(|value| self.render_semantic_value(value, depth, &mut semantic_visited))
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::SemanticValue,
            });
        best = self.choose_preferred_render_candidate(best, semantic, VisibleExprContext::Generic);

        let forwarded = self
            .forwarded_value_for_value_id(value_id)
            .and_then(|prov| self.lookup_definition_with_depth(&prov.source, depth + 1, visited))
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::ForwardedValue,
            });
        self.choose_preferred_render_candidate(best, forwarded, VisibleExprContext::Generic)
    }

    #[cfg(test)]
    fn direct_definition_expr(&self, name: &str) -> Option<CExpr> {
        self.use_info().render_definition_for_name(name).cloned()
    }
    #[cfg(not(test))]
    fn direct_definition_expr(&self, _name: &str) -> Option<CExpr> {
        None
    }

    fn lookup_definition_with_depth(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let visit_key = self.resolution_name_key("def", name);
        if depth > MAX_SIMPLE_EXPR_DEPTH || !visited.insert(visit_key.clone()) {
            return None;
        }
        let in_progress_key = self.resolution_name_key("def-progress", name);
        {
            let mut in_progress = self.definition_lookup_in_progress.borrow_mut();
            if !in_progress.insert(in_progress_key.clone()) {
                visited.remove(&visit_key);
                return self.direct_definition_expr(name);
            }
        }

        let mut best = self.value_id_for_name(name).and_then(|value_id| {
            self.render_candidate_for_value_id_with_depth(value_id, depth, visited)
        });

        let exact = self
            .direct_definition_expr(name)
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::ExactNameDefinition,
            });
        best = self.choose_preferred_render_candidate(best, exact, VisibleExprContext::Generic);

        let semantic = self
            .render_semantic_value_by_name(name, depth, visited)
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::SemanticValue,
            });
        best = self.choose_preferred_render_candidate(best, semantic, VisibleExprContext::Generic);

        let raw = self
            .lookup_definition_raw_with_depth(name, depth + 1, visited)
            .map(|expr| {
                let expr = if matches!(&expr, CExpr::Var(raw_name) if self.should_preserve_address_like_visible_name(*raw_name))
                    || matches!(&expr, CExpr::AddrOf(inner) if matches!(inner.as_ref(), CExpr::Var(raw_name) if !self.is_low_signal_visible_name(&self.spelling(*raw_name)) && !self.is_transient_visible_name(&self.spelling(*raw_name))))
                {
                    expr
                } else {
                    let semanticized = self.semanticize_visible_expr(&expr, depth + 1, visited);
                    if (Self::expr_is_scalar_memory_candidate(&expr)
                        || Self::expr_is_structured_memory_candidate(&expr))
                        && !Self::expr_is_scalar_memory_candidate(&semanticized)
                        && !Self::expr_is_structured_memory_candidate(&semanticized)
                    {
                        expr
                    } else if self.prefers_visible_expr(&expr, &semanticized) {
                        semanticized
                    } else {
                        expr
                    }
                };
                RenderCandidate {
                    expr,
                    source: RenderCandidateSource::RawDefinition,
                }
            });
        best = self.choose_preferred_render_candidate(best, raw, VisibleExprContext::Generic);

        if let Some(prov) = self.forwarded_value_for_name(name) {
            let resolved = self
                .lookup_definition_with_depth(&prov.source, depth + 1, visited);
            best = self.choose_preferred_render_candidate(
                best,
                resolved.map(|expr| RenderCandidate {
                    expr,
                    source: RenderCandidateSource::ForwardedValue,
                }),
                VisibleExprContext::Generic,
            );
        }

        self.definition_lookup_in_progress
            .borrow_mut()
            .remove(&in_progress_key);
        visited.remove(&visit_key);
        best.map(|candidate| candidate.expr)
    }

    pub(super) fn lookup_definition_raw(&self, name: &str) -> Option<CExpr> {

        if !self.enter_resolution_guard(ResolutionPhase::DefinitionRaw, name) {
            return self.resolution_cycle_fallback(name);
        }
        let result = self.lookup_definition_raw_with_depth(name, 0, &mut HashSet::new());
        self.leave_resolution_guard(ResolutionPhase::DefinitionRaw, name);
        result
    }

    fn lookup_definition_raw_with_depth(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {

        let visit_key = self.resolution_name_key("defraw", name);
        if depth > MAX_ALIAS_REWRITE_DEPTH || !visited.insert(visit_key.clone()) {
            return None;
        }
        let in_progress_key = self.resolution_name_key("defraw-progress", name);
        {
            let mut in_progress = self.definition_raw_in_progress.borrow_mut();
            if !in_progress.insert(in_progress_key.clone()) {
                visited.remove(&visit_key);
                return self.direct_definition_expr(name);
            }
        }

        let mut best = self
            .direct_definition_expr(name)
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::ExactNameDefinition,
            });
        if let Some(value_id) = self.value_id_for_name(name) {
            best = self.choose_preferred_render_candidate(
                best,
                self.definition_for_value_id(value_id)
                    .cloned()
                    .map(|expr| RenderCandidate {
                        expr,
                        source: RenderCandidateSource::ValueDefinition,
                    }),
                VisibleExprContext::Generic,
            );
        }
        self.definition_raw_in_progress
            .borrow_mut()
            .remove(&in_progress_key);
        visited.remove(&visit_key);
        best.map(|candidate| candidate.expr)
    }

    fn expr_states_its_pointee(expr: &CExpr) -> bool {
        let target = match expr {
            CExpr::Observed { expr, .. } => return Self::expr_states_its_pointee(expr),
            CExpr::Deref(inner) => inner.as_ref(),
            CExpr::Subscript { base, .. } => base.as_ref(),
            _ => return false,
        };
        matches!(
            target,
            CExpr::Cast {
                ty: CType::Pointer(_),
                ..
            }
        )
    }

    fn semanticize_visible_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return expr.clone();
        }

        // An access that already states its pointee is finished. Re-deriving it
        // from the address reaches the same place by a route that has forgotten
        // the width, turning `*(uint32_t *)((uint8_t *)data + i)` back into
        // `data[i]` -- and an untyped subscript makes every reader invent a
        // width, which is how murmur3's dword read became a byte read.
        if Self::expr_states_its_pointee(expr) {
            return expr.clone();
        }

        match expr {
            CExpr::Observed { id, expr } => {
                CExpr::observed(*id, self.semanticize_visible_expr(expr, depth, visited))
            }
            CExpr::External { .. } => return expr.clone(),
            CExpr::Var(name) => {
                if self.should_preserve_address_like_visible_name(*name) {
                    return expr.clone();
                }
                if let Some(semantic) = self
                    .render_semantic_value_by_name(&self.spelling(*name), depth + 1, visited)
                    && (self.prefers_visible_expr(expr, &semantic)
                        || (self.is_low_signal_visible_name(&self.spelling(*name))
                            && matches!(
                                semantic,
                                CExpr::Subscript { .. }
                                    | CExpr::Member { .. }
                                    | CExpr::PtrMember { .. }
                                    | CExpr::Deref(_)
                            )))
                {
                    return semantic;
                }
                let visit_key = format!("vis:{}", self.spelling(*name));
                if visited.insert(visit_key.clone()) {
                    if let Some(def) =
                        self.lookup_definition_raw_with_depth(&self.spelling(*name), depth + 1, visited,
                    )
                        && !matches!(&def, CExpr::Var(inner) if inner == name)
                    {
                        let semanticized = self.semanticize_visible_expr(&def, depth + 1, visited);
                        let best = self
                            .choose_preferred_visible_expr(Some(def.clone()), Some(semanticized))
                            .unwrap_or(def);
                        if self.prefers_visible_expr(expr, &best) {
                            visited.remove(&visit_key);
                            return best;
                        }
                    }
                    visited.remove(&visit_key);
                }
                expr.clone()
            }
            CExpr::Deref(inner) => {
                let semantic_inner = self.semanticize_visible_expr(inner, depth + 1, visited);
                if self.should_preserve_indirect_local_deref(&semantic_inner) {
                    return CExpr::Deref(Box::new(semantic_inner));
                }
                if let Some(access) = self.render_memory_access_from_visible_expr(
                    &semantic_inner,
                    0,
                    depth + 1,
                    visited,
                ) {
                    return access;
                }
                CExpr::Deref(Box::new(semantic_inner))
            }
            CExpr::Cast { ty, expr: inner } => CExpr::cast(
                ty.clone(),
                self.semanticize_visible_expr(inner, depth + 1, visited),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.semanticize_visible_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Unary { op, operand } => CExpr::unary(
                *op,
                self.semanticize_visible_expr(operand, depth + 1, visited),
            ),
            CExpr::Binary { op, left, right } => {
                if matches!(op, BinaryOp::BitAnd | BinaryOp::BitOr)
                    && let (Some(left_source), Some(right_source)) = (
                        self.call_result_source_for_idempotent_operand(left),
                        self.call_result_source_for_idempotent_operand(right),
                    )
                    && left_source == right_source
                    && let Some(call_expr) = self
                        .call_result_exprs_map()
                        .get(&left_source)
                        .cloned()
                        .or_else(|| self.synthesized_call_expr_for_source_call(left_source))
                {
                    return call_expr;
                }
                CExpr::binary(
                    *op,
                    self.semanticize_visible_expr(left, depth + 1, visited),
                    self.semanticize_visible_expr(right, depth + 1, visited),
                )
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(self.semanticize_visible_expr(cond, depth + 1, visited)),
                then_expr: Box::new(self.semanticize_visible_expr(then_expr, depth + 1, visited)),
                else_expr: Box::new(self.semanticize_visible_expr(else_expr, depth + 1, visited)),
            },
            CExpr::Call { func, args, site } => CExpr::Call {
                site: *site,
                func: Box::new(self.semanticize_visible_expr(func, depth + 1, visited)),
                args: args
                    .iter()
                    .map(|arg| self.semanticize_visible_expr(arg, depth + 1, visited))
                    .collect(),
            },
            CExpr::Subscript { .. } => expr.clone(),
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(self.semanticize_visible_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(self.semanticize_visible_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::Sizeof(inner) => CExpr::Sizeof(Box::new(self.semanticize_visible_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::AddrOf(inner) => {
                if matches!(
                    inner.as_ref(),
                    CExpr::Var(name)
                        if !self.is_low_signal_visible_name(&self.spelling(*name))
                            && !self.is_transient_visible_name(&self.spelling(*name))
                            && !is_generic_stack_placeholder_alias(&self.spelling(*name))
                ) {
                    return expr.clone();
                }
                CExpr::AddrOf(Box::new(self.semanticize_visible_expr(
                    inner,
                    depth + 1,
                    visited,
                )))
            }
            CExpr::Comma(items) => CExpr::Comma(
                items
                    .iter()
                    .map(|item| self.semanticize_visible_expr(item, depth + 1, visited))
                    .collect(),
            ),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => expr.clone(),
        }
    }
    fn call_result_source_for_idempotent_operand(&self, expr: &CExpr) -> Option<(u64, usize)> {
        match expr {
            // A rendered binding may cover several SSA values. Without the
            // exact source value, a binding symbol cannot identify one call.
            CExpr::Var(_) => None,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.call_result_source_for_idempotent_operand(inner)
            }
            _ => None,
        }
    }

    fn is_raw_register_public_call_arg_name(&self, name: &str) -> bool {

        let lower = name.to_ascii_lowercase();
        let base = lower
            .rsplit_once('_')
            .filter(|(_, version)| version.chars().all(|ch| ch.is_ascii_digit()))
            .map(|(base, _)| base)
            .unwrap_or(lower.as_str());
        self.inputs.arch.is_register_like_base_name(base) && !Self::is_semantic_binding_name(base)
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

    fn op_to_stmt_impl(
        &self,
        op: &SSAOp,
        frame: &LowerFrame,
    ) -> OpLoweringResult<Option<CStmt>> {
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
                if self.is_carrier_self_copy(dst, src) {
                    return Ok(None);
                }
                let lhs = self.assignment_lhs_expr(dst)?;
                let certified_rhs: Option<CExpr> = None;
                let rhs_base = if let Some(certified) = certified_rhs {
                    certified
                } else if dst.is_memory() {
                    let raw = self.lookup_definition_raw(&src.display_name());
                    let direct = self.direct_definition_expr(&src.display_name());
                    let preferred = if raw
                        .as_ref()
                        .is_some_and(|expr| self.expr_is_address_artifact_in_scalar_context(expr))
                    {
                        self.choose_preferred_visible_expr(
                            raw.clone(),
                            direct.filter(|expr| {
                                !self.expr_is_address_artifact_in_scalar_context(expr)
                            }),
                        )
                    } else {
                        self.choose_preferred_visible_expr(raw.clone(), direct)
                    };
                    match preferred {
                        Some(expr) => expr,
                        None => self.get_expr(src)?,
                    }
                } else {
                    self.get_expr(src)?
                };
                let rhs = self.resolve_predicate_rhs_for_var(src, rhs_base);
                let rhs = if !self.is_pointer_typed_var(src) && !self.is_pointer_typed_var(dst) {
                    self.collapse_scalar_stack_addr_artifact(rhs)
                } else {
                    rhs
                };
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
                let lhs = certified_lhs.expr().clone();
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
                let lhs_is_pointer_typed = false;
                if let Some(rmw_rhs) = self.stack_read_modify_write_rhs(&lhs, addr, val) {
                    rhs = rmw_rhs;
                } else {
                    if !self.is_pointer_typed_var(val) || !lhs_is_pointer_typed {
                        rhs = self.collapse_scalar_stack_addr_artifact(rhs);
                    }
                    if !lhs_is_pointer_typed {
                        rhs = self.rewrite_scalar_stack_placeholder_rhs(&lhs, rhs);
                    }
                }

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
                CExpr::External { name: "memory_fence".to_string(), kind: crate::symbol::ExternalKind::Intrinsic },
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
                    CExpr::External { name: "load_linked".to_string(), kind: crate::symbol::ExternalKind::Intrinsic },
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
                    CExpr::External { name: "store_conditional".to_string(), kind: crate::symbol::ExternalKind::Intrinsic },
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
                    CExpr::External { name: "atomic_cas".to_string(), kind: crate::symbol::ExternalKind::Intrinsic },
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
                    CExpr::External { name: "load_guarded".to_string(), kind: crate::symbol::ExternalKind::Intrinsic },
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
                CExpr::External { name: "store_guarded".to_string(), kind: crate::symbol::ExternalKind::Intrinsic },
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
            SSAOp::IntSRight { dst, a, b } => self.binary_stmt_typed(frame, dst, a, b, BinaryOp::Shr, Some(type_from_size(dst.size)),
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
            SSAOp::BoolAnd { dst, a, b } => self.boolean_stmt(frame, dst, BinaryOp::And, a, b),
            SSAOp::BoolOr { dst, a, b } => self.boolean_stmt(frame, dst, BinaryOp::Or, a, b),
            SSAOp::BoolXor { dst, a, b } => self.boolean_stmt(frame, dst, BinaryOp::BitXor, a, b),
            SSAOp::BoolNot { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = self.resolve_predicate_rhs_for_var(
                    dst,
                    CExpr::unary(UnaryOp::Not, input(0, src)?));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let ty = type_from_size(dst.size);
                let rhs =
                    self.resolve_predicate_rhs_for_var(dst, CExpr::cast(ty, input(0, src)?));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Trunc { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let ty = type_from_size(dst.size);
                let rhs =
                    self.resolve_predicate_rhs_for_var(dst, CExpr::cast(ty, input(0, src)?));
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
                let rhs = CExpr::call(CExpr::External { name: "fabs".to_string(), kind: crate::symbol::ExternalKind::Intrinsic }, vec![input(0, src)?]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatSqrt { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(CExpr::External { name: "sqrt".to_string(), kind: crate::symbol::ExternalKind::Intrinsic }, vec![input(0, src)?]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatCeil { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(CExpr::External { name: "ceil".to_string(), kind: crate::symbol::ExternalKind::Intrinsic }, vec![input(0, src)?]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatFloor { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(CExpr::External { name: "floor".to_string(), kind: crate::symbol::ExternalKind::Intrinsic }, vec![input(0, src)?]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatRound { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(CExpr::External { name: "round".to_string(), kind: crate::symbol::ExternalKind::Intrinsic }, vec![input(0, src)?]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatNaN { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst)?;
                let rhs = CExpr::call(CExpr::External { name: "isnan".to_string(), kind: crate::symbol::ExternalKind::Intrinsic }, vec![input(0, src)?]);
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
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } => {
                // Handled by control flow structuring
                None
            }
            SSAOp::Phi { .. } => {
                // Phi nodes handled separately
                None
            }
            SSAOp::Nop => None,
            SSAOp::Unimplemented => Some(CStmt::comment("Unimplemented operation")),
            _ => None,
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
        let mut lhs_expr = self.observed_input(
            frame,
            0,
            self.retain_lowering_result(self.get_expr(a))?,
        );
        let mut rhs_expr = self.observed_input(
            frame,
            1,
            self.retain_lowering_result(self.get_expr(b))?,
        );
        if let Some(ty) = operand_ty {
            let a_hint = self.type_hint_for_var(a);
            let b_hint = self.type_hint_for_var(b);
            lhs_expr = self.cast_expr_if_needed(lhs_expr, ty.clone(), a_hint.as_ref());
            rhs_expr = self.cast_expr_if_needed(rhs_expr, ty, b_hint.as_ref());
        }
        if dst.size <= 4 && !self.is_pointer_typed_var(dst) {
            lhs_expr = self.collapse_scalar_stack_addr_artifact(lhs_expr);
            rhs_expr = self.collapse_scalar_stack_addr_artifact(rhs_expr);
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
                self.observed_input(
                    frame,
                    0,
                    self.retain_lowering_result(self.get_expr(a))?,
                ),
                self.observed_input(
                    frame,
                    1,
                    self.retain_lowering_result(self.get_expr(b))?,
                ),
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
#[path = "../tests/lowering.rs"]
mod lowering_tests;

include!("../tests/pipeline.rs");
