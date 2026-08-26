use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CertifiedCallArgs {
    pub(super) args: Vec<CExpr>,
    pub(super) values: Vec<r2ssa::ValueId>,
}


impl<'a> FoldingContext<'a> {
    const UNRESOLVED_CALL_ARG_EXPR_NAME: &'static str = "__r2dec_unresolved_call_arg";

    pub(super) fn unresolved_call_arg_expr(&self) -> CExpr {
        CExpr::External {
            name: Self::UNRESOLVED_CALL_ARG_EXPR_NAME.to_string(),
            kind: crate::symbol::ExternalKind::Intrinsic,
        }
    }

    pub(super) fn call_arg_expr_is_unresolved_fallback(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Observed { expr, .. } => self.call_arg_expr_is_unresolved_fallback(expr),
            // Local bindings retain their SymbolId identity. Their spelling
            // cannot turn them into an intrinsic sentinel.
            CExpr::Var(_) => false,
            CExpr::External { name, .. } => name == Self::UNRESOLVED_CALL_ARG_EXPR_NAME,
            CExpr::Unary { operand, .. }
            | CExpr::Cast { expr: operand, .. }
            | CExpr::Deref(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Sizeof(operand)
            | CExpr::Paren(operand) => self.call_arg_expr_is_unresolved_fallback(operand),
            CExpr::Binary { left, right, .. } => {
                self.call_arg_expr_is_unresolved_fallback(left)
                    || self.call_arg_expr_is_unresolved_fallback(right)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.call_arg_expr_is_unresolved_fallback(cond)
                    || self.call_arg_expr_is_unresolved_fallback(then_expr)
                    || self.call_arg_expr_is_unresolved_fallback(else_expr)
            }
            CExpr::Call { func, args, .. } => {
                self.call_arg_expr_is_unresolved_fallback(func)
                    || args.iter().any(|a| self.call_arg_expr_is_unresolved_fallback(a))
            }
            CExpr::Subscript { base, index } => {
                self.call_arg_expr_is_unresolved_fallback(base)
                    || self.call_arg_expr_is_unresolved_fallback(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.call_arg_expr_is_unresolved_fallback(base)
            }
            CExpr::Comma(items) => items.iter().any(|a| self.call_arg_expr_is_unresolved_fallback(a)),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    pub(super) fn prepared_direct_call_target(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<u64> {
        self.inputs
            .callsite_facts()?
            .arguments_for_site(r2types::CallsiteKey {
                block_addr,
                op_index: op_idx,
            })?
            .direct_target
    }

    /// A reference to the function being called.
    ///
    /// This names something outside the function, so it is an external rather
    /// than a variable. Spelling it as a variable is what let a machine name
    /// look exactly like a local, and it leaves the reader a name no
    /// declaration accounts for.
    fn callee_identity_expr(&self, identity: &CalleeIdentity) -> CExpr {
        let name = identity
            .display_name
            .clone()
            .unwrap_or_else(|| identity.primary_key());
        CExpr::External {
            name,
            kind: external_kind_for_callee(identity.class),
        }
    }

    fn resolved_callee_target(
        &self,
        source_call: Option<(u64, usize)>,
        prepared_direct_target: Option<u64>,
    ) -> Option<r2types::ResolvedCalleeTarget> {
        let callsite = source_call.map(|(block_addr, op_idx)| r2types::CallsiteKey {
            block_addr,
            op_index: op_idx,
        });
        let prepared_call_view = source_call
            .and_then(|(block_addr, op_idx)| self.prepared_call_view_for_site(block_addr, op_idx));
        let prepared_identity = prepared_call_view.and_then(|view| view.callee_identity.as_ref());
        let prepared_direct_target = prepared_direct_target
            .or_else(|| prepared_call_view.and_then(|view| view.direct_target))
            .or_else(|| {
                source_call.and_then(|(block_addr, op_idx)| {
                    self.prepared_direct_call_target(block_addr, op_idx)
                })
            });
        r2types::CalleeResolutionFacts::resolve_target_policy(
            r2types::CalleeTargetResolutionRequest {
                identity: r2types::CalleeTargetIdentityRequest {
                    resolution: self.inputs.callee_resolution(),
                    callsite,
                    prepared_identity,
                    prepared_direct_target,
                    direct_target_context: None,
                },
                callee_facts: self.inputs.callee_facts(),
            },
        )
    }

    #[cfg(test)]
    pub(super) fn resolved_callee_target_for_optional_site(
        &self,
        source_call: Option<(u64, usize)>,
        callee: &CExpr,
    ) -> Option<r2types::ResolvedCalleeTarget> {
        let prepared_direct_target = source_call
            .is_none()
            .then(|| self.direct_target_addr_from_callee_expr(callee))
            .flatten();
        self.resolved_callee_target(source_call, prepared_direct_target)
    }

    pub(super) fn resolved_callee_target_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<r2types::ResolvedCalleeTarget> {
        self.resolved_callee_target(Some((block_addr, op_idx)), None)
    }

    pub(super) fn resolved_callee_target_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        direct_target: Option<u64>,
    ) -> Option<r2types::ResolvedCalleeTarget> {
        self.resolved_callee_target(Some((block_addr, op_idx)), direct_target)
    }

    pub(super) fn callee_identity_for_callsite(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CalleeIdentity> {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .map(|target| target.identity)
    }

    pub(super) fn resolved_callee_identity_expr_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CExpr> {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .map(|target| self.callee_identity_expr(&target.identity))
    }

    pub(super) fn resolve_call_target_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        target: &SSAVar,
    ) -> OpLoweringResult<CExpr> {
        if let Some(resolved) = self.resolved_callee_identity_expr_for_site(block_addr, op_idx) {
            return Ok(resolved);
        }
        self.resolve_call_target(target)
    }

    pub(super) fn certified_call_args_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CertifiedCallArgs> {
        self.certified_call_args_for_site_with_direct_target(block_addr, op_idx, None)
    }

    pub(super) fn certified_call_args_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        direct_target: Option<u64>,
    ) -> Option<CertifiedCallArgs> {
        let cert = self.certified_callsite_for_op(block_addr, op_idx)?;
        let proof = self.certified_render_context()?;
        let mut expected_values = cert.canonical_argument_values();
        if let Some(max_arity) = self.non_variadic_call_arity_for_site_with_direct_target(
            block_addr,
            op_idx,
            direct_target,
        ) {
            expected_values.truncate(max_arity);
        }

        let render_plan = self.certified_render_plan(proof);
        let args = expected_values
            .iter()
            .copied()
            .map(|value| {
                self.certified_call_arg_expr_for_value_at_site(
                    (block_addr, op_idx),
                    value,
                    &proof,
                    render_plan.as_ref(),
                )
            })
            .collect::<Option<Vec<_>>>()?;
        if args.iter().any(|a| self.call_arg_expr_is_unresolved_fallback(a)) {
            return None;
        }

        Some(CertifiedCallArgs {
            args,
            values: expected_values,
        })
    }

    fn certified_call_arg_expr_for_value(
        &self,
        value: r2ssa::ValueId,
        proof: &CertifiedRenderContext<'_>,
    ) -> Option<CExpr> {
        if let Some(literal) = proof.render_facts.string_literal_for_value(value) {
            return Some(CExpr::StringLit(literal.text.clone()));
        }

        if !proof.expression_is_renderable(value) {
            return None;
        }

        if let Some(call_result) = self
            .inputs
            .call_result_facts()
            .and_then(|facts| facts.result_for_value(value))
            && let Some(owner) = self.stable_owned_call_result_expr_for_source((
                call_result.callsite.block_addr,
                call_result.callsite.op_index,
            ))
        {
            return Some(owner);
        }

        let expr = self.certified_structural_expr_for_value(value, 0, &mut BTreeSet::new())?;
        Some(expr)
    }

    fn certified_call_arg_expr_for_value_at_site(
        &self,
        site: (u64, usize),
        value: r2ssa::ValueId,
        proof: &CertifiedRenderContext<'_>,
        render_plan: Option<&CertifiedRenderPlan<'_>>,
    ) -> Option<CExpr> {
        if proof.memory_read_for_value_dependency(value).is_some() {
            return render_plan?.call_arg_expr(site, value, |expr| {
                self.certified_return_expr_contains_raw_storage_name(expr)
            });
        }
        if let Some(expr) = self.certified_call_arg_expr_for_value(value, proof) {
            return Some(expr);
        }
        render_plan?.call_arg_expr(site, value, |expr| {
            self.certified_return_expr_contains_raw_storage_name(expr)
        })
    }

    #[cfg(test)]
    pub(super) fn known_signature_for_callee_name(
        &self,
        callee_name: &str,
    ) -> Option<r2types::FunctionType> {
        self.callee_identity_for_name(callee_name)
            .known_signature()
            .cloned()
    }

    pub(super) fn known_signature_for_callee_expr(
        &self,
        callee: &CExpr,
    ) -> Option<r2types::FunctionType> {
        self.callee_identity_for_expr(callee)
            .and_then(|identity| identity.known_signature().cloned())
    }

    #[cfg(test)]
    pub(super) fn known_signature_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<r2types::FunctionType> {
        self.callee_identity_for_callsite(block_addr, op_idx)
            .and_then(|identity| identity.known_signature().cloned())
    }

    #[cfg(test)]
    pub(super) fn extract_callee_name(&self, expr: &CExpr) -> Option<std::rc::Rc<str>> {
        match expr {
            CExpr::Observed { expr, .. } => self.extract_callee_name(expr),
            CExpr::Var(name) => Some(self.spelling(*name)),
            // A callee is an external, and it still names something.
            CExpr::External { name, .. } => Some(std::rc::Rc::from(name.as_str())),
            CExpr::Deref(inner) | CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
                self.extract_callee_name(inner)
            }
            CExpr::Cast { expr: inner, .. } => self.extract_callee_name(inner),
            _ => None,
        }
    }

    #[cfg(test)]
    pub(super) fn non_variadic_call_arity(&self, callee: &CExpr) -> Option<usize> {
        let identity = self.callee_identity_for_expr(callee)?;
        self.non_variadic_call_arity_for_identity(&identity)
    }

    pub(super) fn non_variadic_call_arity_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<usize> {
        self.non_variadic_call_arity_for_site_with_direct_target(block_addr, op_idx, None)
    }

    pub(super) fn non_variadic_call_arity_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        direct_target: Option<u64>,
    ) -> Option<usize> {
        let identity = self
            .resolved_callee_target_for_site_with_direct_target(block_addr, op_idx, direct_target)?
            .identity;
        self.non_variadic_call_arity_for_identity(&identity)
    }

    pub(super) fn non_variadic_call_arity_for_optional_site(
        &self,
        source_call: Option<(u64, usize)>,
    ) -> Option<usize> {
        source_call.and_then(|(block_addr, op_idx)| {
            self.non_variadic_call_arity_for_site(block_addr, op_idx)
        })
    }

    pub(super) fn imported_or_modeled_call_target_for_optional_site(
        &self,
        source_call: Option<(u64, usize)>,
    ) -> bool {
        source_call
            .and_then(|(block_addr, op_idx)| {
                self.resolved_callee_target_for_site(block_addr, op_idx)
            })
            .is_some_and(|target| {
                target.policy.arg_policy() == r2types::CalleeCallArgPolicy::ImportedLike
            })
    }

    fn non_variadic_call_arity_for_identity(&self, identity: &CalleeIdentity) -> Option<usize> {
        identity
            .non_variadic_arity_decision(
                self.summary_view(),
                &self.signature_registry,
                self.inputs.arch.ptr_size,
            )
            .map(|decision| decision.arity)
    }

    pub(super) fn resolve_call_target(&self, target: &SSAVar) -> OpLoweringResult<CExpr> {
        if let Some(addr) = target.constant_bits() {
            return Ok(
                self.callee_identity_expr(&self.callee_identity_for_direct_target(addr))
            );
        }
        if target.name_kind().is_constant() {
            return Err(OpLoweringRefusal::MissingProgramVariableAuthorization);
        }
        if let Some(addr) = parse_address_from_var_name(&target.name) {
            return Ok(self.callee_identity_expr(&self.callee_identity_for_direct_target(addr)));
        }
        let value = self
            .prepared_value_id_for_var(target)
            .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)?;
        match self.planned_value_expr(value) {
            Ok(expr) => Ok(expr),
            Err(error) => {
                self.retain_first_observation_error(error);
                Err(OpLoweringRefusal::MissingProgramVariableAuthorization)
            }
        }
    }

    #[cfg(test)]
    pub(super) fn is_modeled_call_target(&self, callee: &CExpr) -> bool {
        self.resolved_callee_target_for_optional_site(None, callee)
            .is_some_and(|target| target.policy.modeled)
    }

    #[cfg(test)]
    pub(super) fn is_modeled_call_target_for_site(&self, block_addr: u64, op_idx: usize) -> bool {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .is_some_and(|target| target.policy.modeled)
    }

    pub(super) fn expr_for_semantic_call_arg_fallback(
        &self,
        value: &analysis::SemanticValue,
    ) -> OpLoweringResult<CExpr> {
        match value {
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => {
                Ok(expr.clone())
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(value_ref)) => {
                if value_ref.var.constant_bits().is_some() {
                    self.const_to_expr(&value_ref.var)
                } else {
                    let value = self
                        .prepared_value_id_for_var(&value_ref.var)
                        .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)?;
                    match self.planned_value_expr(value) {
                        Ok(expr) => Ok(expr),
                        Err(error) => {
                            self.retain_first_observation_error(error);
                            Err(OpLoweringRefusal::MissingProgramVariableAuthorization)
                        }
                    }
                }
            }
            analysis::SemanticValue::Address(addr) => {
                let mut visited = HashSet::new();
                self.render_address_expr_from_addr(addr, 0, &mut visited)
                    .or_else(|| self.render_base_ref_expr(&addr.base, true, 0, &mut visited))
                    .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)
            }
            analysis::SemanticValue::Load { space, addr, size } => {
                let mut visited = HashSet::new();
                self.render_semantic_load(*space, addr, *size, 0, &mut visited)
                    .or_else(|| {
                        (*space == r2il::SpaceId::Ram).then_some(())?;
                        let addr_expr =
                            self.render_address_expr_from_addr(addr, 0, &mut visited)?;
                        Some(CExpr::Deref(Box::new(addr_expr)))
                    })
                    .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)
            }
            analysis::SemanticValue::Unknown => {
                Err(OpLoweringRefusal::MissingProgramVariableAuthorization)
            }
        }
    }

    pub(super) fn normalize_imported_call_arg_expr(
        &self,
        expr: CExpr,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
        allow_string_like_resolution: bool,
    ) -> CExpr {
        let expr = match self.source_proof_for_call_expr(expr.unobserved()) {
            CallExprSourceProof::Exact(source_call) => {
                let normalized = self.normalize_call_expr_for_source_call(
                    source_call,
                    expr.unobserved().clone(),
                    FinalExprNormalizeContext::DefinitionRoot,
                );
                crate::ast::carry_outer_expr_observations(&expr, normalized)
            }
            CallExprSourceProof::ContradictedOrAmbiguous | CallExprSourceProof::None => expr,
        };
        let expr =
            self.rewrite_imported_call_arg_expr_with_prepared_owners(expr, 0, &mut HashSet::new());
        let rewritten = self.rewrite_stack_expr(expr);
        let mut best = Some(rewritten.clone());
        let mut expanded_visited = HashSet::new();
        let expanded = self.expand_call_arg_expr(&rewritten, 0, &mut expanded_visited);
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(expanded.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&expanded, 0, &mut semantic_visited);
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(semanticized.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        let call_normalized = self.normalize_final_call_expr(semanticized.clone());
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(call_normalized.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        let mut imported_visited = HashSet::new();
        let imported_resolved =
            self.resolve_imported_call_arg_expr(&call_normalized, 0, &mut imported_visited);
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(imported_resolved.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        let memoryized = match &imported_resolved {
            CExpr::Deref(inner) => {
                let mut memory_visited = HashSet::new();
                self.render_memory_access_from_visible_expr(
                    inner,
                    self.inputs.arch.ptr_size.max(1),
                    0,
                    &mut memory_visited,
                )
                .or_else(|| self.promote_constant_indexed_call_arg(inner))
                .unwrap_or_else(|| imported_resolved.clone())
            }
            _ => imported_resolved.clone(),
        };
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(memoryized.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );

        let literalized = self
            .resolve_literalish_call_arg_expr(&memoryized)
            .unwrap_or(memoryized);
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(literalized.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        if allow_string_like_resolution {
            let mut string_visited = HashSet::new();
            if let Some(string_like) = self.resolve_string_like_imported_call_arg_expr(
                &literalized,
                0,
                &mut string_visited,
            ) {
                best = self.choose_preferred_imported_call_arg_expr(
                    best,
                    Some(string_like),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                );
            }
        }

        let best = best.unwrap_or(rewritten.clone());
        if preserve_stable_input_slot
            && self.is_preservable_named_stack_slot_expr(&rewritten)
            && self.is_direct_constish_visible_expr(&best, 0)
        {
            return self.sanitize_public_call_arg_expr(rewritten);
        }
        let rewritten_best = self.rewrite_stack_expr(best.clone());
        let normalized = self
            .choose_preferred_imported_call_arg_expr(
                Some(best.clone()),
                Some(rewritten_best),
                preserve_stable_input_slot,
                preserve_explicit_call_expr,
            )
            .unwrap_or(best);
        self.sanitize_public_call_arg_expr(normalized)
    }

    fn rewrite_imported_call_arg_expr_with_prepared_owners(
        &self,
        expr: CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return expr;
        }

        match expr {
            CExpr::Observed { id, expr } => CExpr::observed(
                id,
                self.rewrite_imported_call_arg_expr_with_prepared_owners(
                    *expr,
                    depth,
                    visited,
                ),
            ),
            // SymbolId does not identify a unique SSA value. Owner projection
            // must happen while the exact ValueId is still present.
            CExpr::Var(name) => CExpr::Var(name),
            other => other.map_children(&mut |child| {
                self.rewrite_imported_call_arg_expr_with_prepared_owners(child, depth + 1, visited)
            }),
        }
    }

    fn choose_preferred_imported_call_arg_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
    ) -> Option<CExpr> {
        if preserve_explicit_call_expr
            && current
                .as_ref()
                .is_some_and(|expr| matches!(expr.unobserved(), CExpr::Call { .. }))
            && candidate
                .as_ref()
                .is_some_and(|expr| !matches!(expr.unobserved(), CExpr::Call { .. }))
        {
            if current
                .as_ref()
                .and_then(|expr| self.proven_source_for_public_call_arg_call(expr))
                .is_some()
            {
                return current;
            }
            return candidate;
        }

        if preserve_stable_input_slot
            && let (Some(current_expr), Some(candidate_expr)) = (&current, &candidate)
            && self.is_preserved_imported_input_expr(current_expr)
            && self.expr_is_generic_entry_arg_like(candidate_expr)
        {
            return current;
        }

        self.choose_preferred_call_arg_expr_with_slot_policy(
            current,
            candidate,
            true,
            preserve_stable_input_slot,
        )
    }

    /// Convert an SSA operation to a C statement.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn op_to_stmt(&self, op: &SSAOp) -> OpLoweringResult<Option<CStmt>> {
        let mut frame = LowerFrame::for_stmt(None, Some((0, 0)), false);
        Ok(self.lowered_to_stmt(self.lower_op(op, &mut frame)?))
    }
}

/// What kind of outside thing a call names.
///
/// The identity already classified it, so the rendering says what the analysis
/// concluded rather than guessing from how the name is spelled.
fn external_kind_for_callee(class: r2types::CalleeClass) -> crate::symbol::ExternalKind {
    match class {
        r2types::CalleeClass::Imported => crate::symbol::ExternalKind::Import,
        r2types::CalleeClass::ExternalSymbol => crate::symbol::ExternalKind::Global,
        _ => crate::symbol::ExternalKind::Function,
    }
}
