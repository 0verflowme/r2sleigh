use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CertifiedCallArgs {
    pub(super) args: Vec<CExpr>,
    pub(super) values: Vec<r2ssa::ValueId>,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct PreparedCallArgs {
    pub(super) args: Vec<CExpr>,
    pub(super) values: Vec<r2ssa::ValueId>,
}

fn certified_callsite_argument_values(cert: &r2ssa::CallsiteCertificate) -> Vec<r2ssa::ValueId> {
    cert.argument_values
        .iter()
        .copied()
        .chain(
            cert.argument_certificates
                .iter()
                .filter(|arg| matches!(&arg.location, r2ssa::CallArgumentLocation::Stack { .. }))
                .map(|arg| arg.value),
        )
        .collect()
}

impl<'a> FoldingContext<'a> {
    const UNRESOLVED_CALL_ARG_EXPR_NAME: &'static str = "__r2dec_unresolved_call_arg";

    pub(super) fn unresolved_call_arg_expr() -> CExpr {
        CExpr::Var(Self::UNRESOLVED_CALL_ARG_EXPR_NAME.to_string())
    }

    pub(super) fn call_arg_expr_is_unresolved_fallback(expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => name == Self::UNRESOLVED_CALL_ARG_EXPR_NAME,
            CExpr::Unary { operand, .. }
            | CExpr::Cast { expr: operand, .. }
            | CExpr::Deref(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Sizeof(operand)
            | CExpr::Paren(operand) => Self::call_arg_expr_is_unresolved_fallback(operand),
            CExpr::Binary { left, right, .. } => {
                Self::call_arg_expr_is_unresolved_fallback(left)
                    || Self::call_arg_expr_is_unresolved_fallback(right)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                Self::call_arg_expr_is_unresolved_fallback(cond)
                    || Self::call_arg_expr_is_unresolved_fallback(then_expr)
                    || Self::call_arg_expr_is_unresolved_fallback(else_expr)
            }
            CExpr::Call { func, args } => {
                Self::call_arg_expr_is_unresolved_fallback(func)
                    || args.iter().any(Self::call_arg_expr_is_unresolved_fallback)
            }
            CExpr::Subscript { base, index } => {
                Self::call_arg_expr_is_unresolved_fallback(base)
                    || Self::call_arg_expr_is_unresolved_fallback(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                Self::call_arg_expr_is_unresolved_fallback(base)
            }
            CExpr::Comma(items) => items.iter().any(Self::call_arg_expr_is_unresolved_fallback),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn prepared_call_target_var(&self, target: r2ssa::ValueId) -> Option<&SSAVar> {
        self.inputs.prepared_ssa?.value_var(target)
    }

    pub(super) fn prepared_direct_call_target(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<u64> {
        let call_site = self.prepared_call_site_for_op(block_addr, op_idx)?;
        call_site.direct_target.or_else(|| {
            self.prepared_call_target_var(call_site.target)
                .and_then(|target| {
                    parse_address_from_var_name(&target.name).or_else(|| {
                        self.prepared_canonical_value_root(target)
                            .as_ref()
                            .and_then(|root| parse_address_from_var_name(&root.name))
                    })
                })
        })
    }

    fn callee_identity_expr(identity: &CalleeIdentity) -> CExpr {
        identity
            .display_name
            .clone()
            .map(CExpr::Var)
            .unwrap_or_else(|| CExpr::Var(identity.primary_key()))
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
                    resolution: self.inputs.callee_resolution,
                    callsite,
                    prepared_identity,
                    prepared_direct_target,
                    direct_target_context: None,
                },
                callee_facts: self.inputs.callee_facts,
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
            .map(|target| Self::callee_identity_expr(&target.identity))
    }

    pub(super) fn resolve_call_target_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        target: &SSAVar,
    ) -> CExpr {
        if let Some(resolved) = self.resolved_callee_identity_expr_for_site(block_addr, op_idx) {
            return resolved;
        }
        self.resolve_call_target(target)
    }

    #[cfg(test)]
    pub(super) fn render_call_args_for_callee(
        &self,
        callee: &CExpr,
        raw_args: Vec<analysis::CallArgBinding>,
    ) -> Vec<CExpr> {
        if self.is_imported_call_target(callee) || self.is_modeled_call_target(callee) {
            let mut rendered = raw_args
                .iter()
                .cloned()
                .map(|binding| self.render_imported_call_arg(binding))
                .collect::<Vec<_>>();
            if let Some(max_arity) = self.non_variadic_call_arity(callee) {
                rendered.truncate(max_arity);
            }
            return rendered;
        }

        let mut rendered = raw_args
            .into_iter()
            .map(|binding| self.render_call_arg_for_callee(callee, binding))
            .collect::<Vec<_>>();
        if let Some(max_arity) = self.non_variadic_call_arity(callee) {
            rendered.truncate(max_arity);
        }
        rendered
    }

    #[cfg(test)]
    pub(super) fn render_call_args_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        callee: &CExpr,
        raw_args: Vec<analysis::CallArgBinding>,
    ) -> Vec<CExpr> {
        self.render_call_args_for_site_with_direct_target(
            block_addr, op_idx, callee, None, raw_args,
        )
    }

    pub(super) fn render_call_args_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        _callee: &CExpr,
        direct_target: Option<u64>,
        raw_args: Vec<analysis::CallArgBinding>,
    ) -> Vec<CExpr> {
        let imported_or_modeled = self
            .resolved_callee_target_for_site_with_direct_target(block_addr, op_idx, direct_target)
            .is_some_and(|target| {
                target.policy.arg_policy() == r2types::CalleeCallArgPolicy::ImportedLike
            });
        if imported_or_modeled {
            let mut rendered = raw_args
                .iter()
                .cloned()
                .map(|binding| self.render_imported_call_arg(binding))
                .collect::<Vec<_>>();
            if let Some(max_arity) = self.non_variadic_call_arity_for_site_with_direct_target(
                block_addr,
                op_idx,
                direct_target,
            ) {
                rendered.truncate(max_arity);
            }
            return rendered;
        }

        let mut rendered = raw_args
            .into_iter()
            .map(|binding| self.render_non_imported_call_arg(binding))
            .collect::<Vec<_>>();
        if let Some(max_arity) = self.non_variadic_call_arity_for_site_with_direct_target(
            block_addr,
            op_idx,
            direct_target,
        ) {
            rendered.truncate(max_arity);
        }
        rendered
    }

    pub(super) fn prepared_call_args_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        callee: &CExpr,
        direct_target: Option<u64>,
    ) -> Option<PreparedCallArgs> {
        let view = self.prepared_call_view_for_site(block_addr, op_idx)?;
        if view.authoritative_args.is_empty()
            || view.authoritative_args.len() != view.authoritative_arg_values.len()
        {
            return None;
        }

        let args = self.normalize_prepared_call_args_for_site_with_direct_target(
            block_addr,
            op_idx,
            callee,
            direct_target,
            view.authoritative_args.clone(),
        );
        let values = view
            .authoritative_arg_values
            .iter()
            .take(args.len())
            .copied()
            .collect::<Vec<_>>();
        (values.len() == args.len()).then_some(PreparedCallArgs { args, values })
    }

    #[cfg(test)]
    pub(super) fn normalize_prepared_call_args_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        callee: &CExpr,
        args: Vec<CExpr>,
    ) -> Vec<CExpr> {
        self.normalize_prepared_call_args_for_site_with_direct_target(
            block_addr, op_idx, callee, None, args,
        )
    }

    pub(super) fn normalize_prepared_call_args_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        _callee: &CExpr,
        direct_target: Option<u64>,
        args: Vec<CExpr>,
    ) -> Vec<CExpr> {
        let imported_or_modeled = self
            .resolved_callee_target_for_site_with_direct_target(block_addr, op_idx, direct_target)
            .is_some_and(|target| {
                target.policy.arg_policy() == r2types::CalleeCallArgPolicy::ImportedLike
            });
        let mut normalized = args
            .into_iter()
            .map(|arg| {
                if imported_or_modeled {
                    self.normalize_imported_call_arg_expr(arg, true, true, true)
                } else {
                    self.normalize_prepared_call_arg_expr(arg)
                }
            })
            .collect::<Vec<_>>();
        if let Some(max_arity) = self.non_variadic_call_arity_for_site_with_direct_target(
            block_addr,
            op_idx,
            direct_target,
        ) {
            normalized.truncate(max_arity);
        }
        normalized
    }

    fn normalize_prepared_call_arg_expr(&self, arg: CExpr) -> CExpr {
        let original_param_home = match &arg {
            CExpr::Var(name) if self.is_static_param_home_alias_name(name) => Some(name.clone()),
            _ => None,
        };
        let rewritten = self.rewrite_imported_call_arg_expr_with_prepared_owners(
            arg.clone(),
            0,
            &mut HashSet::new(),
        );
        let normalized = self.sanitize_public_call_arg_expr(self.rewrite_stack_expr(rewritten));
        if let Some(name) = original_param_home
            && matches!(&normalized, CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(inner_name) if inner_name.eq_ignore_ascii_case(&name)))
        {
            return arg;
        }
        normalized
    }

    pub(super) fn certified_call_args_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        callee: &CExpr,
        raw_args: Vec<analysis::CallArgBinding>,
    ) -> Option<CertifiedCallArgs> {
        self.certified_call_args_for_site_with_direct_target(
            block_addr, op_idx, callee, None, raw_args,
        )
    }

    pub(super) fn certified_call_args_for_site_with_direct_target(
        &self,
        block_addr: u64,
        op_idx: usize,
        callee: &CExpr,
        direct_target: Option<u64>,
        raw_args: Vec<analysis::CallArgBinding>,
    ) -> Option<CertifiedCallArgs> {
        if !self.requires_certified_rendering() {
            if raw_args
                .iter()
                .any(|binding| !self.call_arg_binding_has_render_authority(binding))
            {
                return None;
            }
            return Some(CertifiedCallArgs {
                args: self.render_call_args_for_site_with_direct_target(
                    block_addr,
                    op_idx,
                    callee,
                    direct_target,
                    raw_args,
                ),
                values: Vec::new(),
            });
        }

        let cert = self.certified_callsite_for_op(block_addr, op_idx)?;
        let proof = self.certified_render_context()?;
        let expected_values = certified_callsite_argument_values(cert);

        let prepared_view = self.prepared_call_view_for_site(block_addr, op_idx);
        let prepared_view_present = prepared_view.is_some();
        let prepared_view_has_authoritative_args =
            prepared_view.is_some_and(|view| !view.authoritative_args.is_empty());
        if let Some(prepared_args) = self.prepared_call_args_for_site_with_direct_target(
            block_addr,
            op_idx,
            callee,
            direct_target,
        ) {
            if prepared_args.values.len() <= expected_values.len()
                && !prepared_args
                    .args
                    .iter()
                    .any(Self::call_arg_expr_is_unresolved_fallback)
                && prepared_args
                    .values
                    .iter()
                    .copied()
                    .zip(expected_values.iter().copied())
                    .all(|(actual, expected)| {
                        actual == expected && proof.expression_is_renderable(actual)
                    })
            {
                return Some(CertifiedCallArgs {
                    values: prepared_args.values,
                    args: prepared_args.args,
                });
            }
            return None;
        }
        if prepared_view_present {
            if !prepared_view_has_authoritative_args
                && raw_args.is_empty()
                && expected_values.is_empty()
            {
                return Some(CertifiedCallArgs {
                    args: Vec::new(),
                    values: Vec::new(),
                });
            }
            return None;
        }

        if raw_args.is_empty() {
            return cert
                .argument_values
                .is_empty()
                .then_some(CertifiedCallArgs {
                    args: Vec::new(),
                    values: Vec::new(),
                });
        }

        let args = self.render_call_args_for_site_with_direct_target(
            block_addr,
            op_idx,
            callee,
            direct_target,
            raw_args.clone(),
        );
        if args.iter().any(Self::call_arg_expr_is_unresolved_fallback) {
            return None;
        }
        let values = raw_args
            .iter()
            .take(args.len())
            .enumerate()
            .map(|(index, binding)| {
                self.certified_call_arg_binding_value(binding, &expected_values, &proof, index)
            })
            .collect::<Option<Vec<_>>>()?;

        Some(CertifiedCallArgs { args, values })
    }

    fn call_arg_binding_has_render_authority(&self, binding: &analysis::CallArgBinding) -> bool {
        if binding.source_value_id.is_some() {
            return true;
        }
        binding
            .source_var_name
            .as_deref()
            .is_some_and(|name| self.source_var_name_has_prepared_call_arg_authority(name))
    }

    fn source_var_name_has_prepared_call_arg_authority(&self, name: &str) -> bool {
        let Some(prepared) = self.prepared_semantic_view() else {
            return false;
        };

        if self
            .use_info()
            .value_id_for_name(name)
            .is_some_and(|value_id| {
                prepared.var_for_value_id(value_id).is_some()
                    || prepared.owner_expr_for_value_id(value_id).is_some()
            })
        {
            return true;
        }
        if prepared.owner_expr_for_name(name).is_some() {
            return true;
        }

        self.find_ssa_name_for_rendered_alias(name)
            .as_deref()
            .is_some_and(|resolved| {
                prepared.owner_expr_for_name(resolved).is_some()
                    || self
                        .use_info()
                        .value_id_for_name(resolved)
                        .is_some_and(|value_id| {
                            prepared.var_for_value_id(value_id).is_some()
                                || prepared.owner_expr_for_value_id(value_id).is_some()
                        })
            })
    }

    fn certified_call_arg_binding_value(
        &self,
        binding: &analysis::CallArgBinding,
        expected_values: &[r2ssa::ValueId],
        proof: &CertifiedRenderContext<'_>,
        index: usize,
    ) -> Option<r2ssa::ValueId> {
        let expected = *expected_values.get(index)?;
        match &binding.arg {
            analysis::SemanticCallArg::StringAddr(addr) => self
                .certified_string_addr_matches_value(*addr, expected, proof)
                .then_some(expected),
            analysis::SemanticCallArg::Semantic(_) | analysis::SemanticCallArg::FallbackExpr(_) => {
                binding
                    .source_value_id
                    .filter(|value| *value == expected && proof.expression_is_renderable(*value))
            }
        }
    }

    fn certified_string_addr_matches_value(
        &self,
        addr: u64,
        expected: r2ssa::ValueId,
        proof: &CertifiedRenderContext<'_>,
    ) -> bool {
        if !proof.expression_is_renderable(expected) {
            return false;
        }
        let mut visited = std::collections::BTreeSet::new();
        self.certified_value_resolves_to_const_addr(expected, addr, proof, 0, &mut visited)
    }

    fn certified_value_resolves_to_const_addr(
        &self,
        value: r2ssa::ValueId,
        addr: u64,
        proof: &CertifiedRenderContext<'_>,
        depth: usize,
        visited: &mut std::collections::BTreeSet<r2ssa::ValueId>,
    ) -> bool {
        if depth > 8 || !visited.insert(value) {
            return false;
        }
        if self.certified_value_const_addr(value) == Some(addr) {
            return true;
        }
        proof
            .prepared
            .certificates()
            .expressions
            .get(&value)
            .is_some_and(|cert| {
                cert.inputs.iter().copied().any(|input| {
                    self.certified_value_resolves_to_const_addr(
                        input,
                        addr,
                        proof,
                        depth + 1,
                        visited,
                    )
                })
            })
    }

    fn certified_value_const_addr(&self, value: r2ssa::ValueId) -> Option<u64> {
        let var = self.prepared_var_for_value_id(value)?;
        parse_const_value(&var.name).or_else(|| {
            self.prepared_canonical_value_root(var)
                .and_then(|root| parse_const_value(&root.name))
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

    pub(super) fn known_signature_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<r2types::FunctionType> {
        self.callee_identity_for_callsite(block_addr, op_idx)
            .and_then(|identity| identity.known_signature().cloned())
    }

    #[cfg(test)]
    pub(super) fn extract_callee_name(expr: &CExpr) -> Option<&str> {
        match expr {
            CExpr::Var(name) => Some(name.as_str()),
            CExpr::Deref(inner) | CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
                Self::extract_callee_name(inner)
            }
            CExpr::Cast { expr: inner, .. } => Self::extract_callee_name(inner),
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

    pub(super) fn resolve_call_target(&self, target: &SSAVar) -> CExpr {
        if let Some(addr) = parse_address_from_var_name(&target.name)
            && let Some(name) = self.callee_identity_for_direct_target(addr).display_name
        {
            return CExpr::Var(name);
        }
        self.get_expr(target)
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

    #[cfg(test)]
    pub(super) fn render_call_arg_for_callee(
        &self,
        callee: &CExpr,
        binding: analysis::CallArgBinding,
    ) -> CExpr {
        if self.is_imported_call_target(callee) || self.is_modeled_call_target(callee) {
            return self.render_imported_call_arg(binding);
        }

        match binding.arg {
            analysis::SemanticCallArg::Semantic(value) => {
                let mut visited = HashSet::new();
                let expr = self
                    .render_semantic_value(&value, 0, &mut visited)
                    .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(&value));
                self.normalize_call_arg_expr_for_callee(callee, expr)
            }
            analysis::SemanticCallArg::StringAddr(addr) => self
                .lookup_string(addr)
                .map(|s| CExpr::StringLit(s.clone()))
                .or_else(|| {
                    self.lookup_symbol(addr)
                        .map(|name| CExpr::Var(name.clone()))
                })
                .unwrap_or(CExpr::UIntLit(addr)),
            analysis::SemanticCallArg::FallbackExpr(expr) => {
                self.normalize_call_arg_expr_for_callee(callee, expr)
            }
        }
    }

    fn render_non_imported_call_arg(&self, binding: analysis::CallArgBinding) -> CExpr {
        match binding.arg {
            analysis::SemanticCallArg::Semantic(value) => {
                let mut visited = HashSet::new();
                let expr = self
                    .render_semantic_value(&value, 0, &mut visited)
                    .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(&value));
                self.normalize_call_arg_expr_with_import_policy(expr, false)
            }
            analysis::SemanticCallArg::StringAddr(addr) => self
                .lookup_string(addr)
                .map(|s| CExpr::StringLit(s.clone()))
                .or_else(|| {
                    self.lookup_symbol(addr)
                        .map(|name| CExpr::Var(name.clone()))
                })
                .unwrap_or(CExpr::UIntLit(addr)),
            analysis::SemanticCallArg::FallbackExpr(expr) => {
                self.normalize_call_arg_expr_with_import_policy(expr, false)
            }
        }
    }

    fn render_imported_call_arg(&self, binding: analysis::CallArgBinding) -> CExpr {
        let allow_string_like_resolution =
            !self.imported_input_binding_prefers_pointer_identity(&binding);
        if let Some(param_home_alias) = self.param_home_alias_expr_for_call_arg_binding(&binding) {
            return param_home_alias;
        }
        if let Some((block_addr, op_idx)) = binding.source_call
            && binding.role == analysis::CallArgRole::Result
            && let Some(owner) =
                self.stable_result_call_arg_owner_expr_for_source((block_addr, op_idx))
        {
            return self.sanitize_public_call_arg_expr(owner);
        }
        if let Some((block_addr, op_idx)) = binding.source_call
            && binding.role == analysis::CallArgRole::Result
            && let analysis::SemanticCallArg::FallbackExpr(CExpr::Call {
                func,
                args: original_args,
            }) = binding.arg.clone()
        {
            let should_rebuild = original_args.iter().any(|arg| {
                self.call_arg_contains_transient_name(arg, 0)
                    || self.call_arg_contains_stack_placeholder(arg, 0)
                    || self.call_arg_requires_result_rebuild(arg)
                    || self.expr_is_generic_entry_arg_like(arg)
            });
            if !should_rebuild {
                let mut args = original_args
                    .into_iter()
                    .map(|arg| {
                        self.normalize_imported_call_arg_expr(
                            arg,
                            false,
                            true,
                            allow_string_like_resolution,
                        )
                    })
                    .collect::<Vec<_>>();
                if let Some(max_arity) = self.non_variadic_call_arity_for_site(block_addr, op_idx) {
                    args.truncate(max_arity);
                }
                let call = self.canonicalize_call_expr_for_source_call(
                    (block_addr, op_idx),
                    CExpr::call(*func, args),
                );
                return self.sanitize_public_call_arg_expr(call);
            }
            let mut args = self.render_authoritative_source_args_for_call((block_addr, op_idx));
            if let Some(max_arity) = self.non_variadic_call_arity_for_site(block_addr, op_idx) {
                args.truncate(max_arity);
            }
            let call = self.canonicalize_call_expr_for_source_call(
                (block_addr, op_idx),
                CExpr::call(*func, args),
            );
            return self.sanitize_public_call_arg_expr(call);
        }

        let preserve_stable_input_slot = binding.role == analysis::CallArgRole::Input;
        let preserve_explicit_call_expr = binding.role == analysis::CallArgRole::Result
            || matches!(
                binding.arg,
                analysis::SemanticCallArg::FallbackExpr(CExpr::Call { .. })
            );
        let recovered_source_expr = self.recover_call_arg_expr_from_source_var(&binding);
        match binding.arg {
            analysis::SemanticCallArg::Semantic(value) => {
                if preserve_stable_input_slot
                    && Self::semantic_value_has_negative_stack_slot(&value)
                    && let Some(expr) = self
                        .render_imported_semantic_arg_value(&value, !allow_string_like_resolution)
                    && self.is_preservable_named_stack_slot_expr(&expr)
                {
                    return expr;
                }
                let expr = self
                    .render_imported_semantic_arg_value(&value, !allow_string_like_resolution)
                    .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(&value));
                let recovered_source_expr = if self
                    .entry_arg_alias_for_pointer_identity_value(&value)
                    .is_some()
                {
                    None
                } else if matches!(
                    value,
                    analysis::SemanticValue::Load { .. } | analysis::SemanticValue::Address(_)
                ) {
                    recovered_source_expr.clone()
                } else if self.is_direct_constish_visible_expr(&expr, 0) {
                    None
                } else {
                    recovered_source_expr.clone()
                };
                let expr = self
                    .choose_preferred_imported_call_arg_expr(
                        Some(expr.clone()),
                        recovered_source_expr.clone(),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(expr);
                let finalized = self.finalize_authoritative_imported_call_arg_expr(
                    expr,
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                    allow_string_like_resolution,
                );
                let chosen = self
                    .choose_preferred_imported_call_arg_expr(
                        Some(finalized.clone()),
                        recovered_source_expr.clone(),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(finalized);
                self.sanitize_public_call_arg_expr(chosen)
            }
            analysis::SemanticCallArg::StringAddr(addr) => self
                .lookup_string(addr)
                .map(|s| CExpr::StringLit(s.clone()))
                .or_else(|| {
                    self.lookup_symbol(addr)
                        .map(|name| CExpr::Var(name.clone()))
                })
                .unwrap_or(CExpr::UIntLit(addr)),
            analysis::SemanticCallArg::FallbackExpr(expr) => {
                let recovered_source_expr = if self.is_direct_constish_visible_expr(&expr, 0) {
                    None
                } else {
                    recovered_source_expr
                };
                let normalized = self.normalize_imported_call_arg_expr(
                    recovered_source_expr
                        .clone()
                        .map(|candidate| {
                            if self.call_arg_contains_transient_name(&expr, 0)
                                || self.call_arg_contains_stack_placeholder(&expr, 0)
                            {
                                candidate
                            } else {
                                self.choose_preferred_imported_call_arg_expr(
                                    Some(expr.clone()),
                                    Some(candidate),
                                    preserve_stable_input_slot,
                                    preserve_explicit_call_expr,
                                )
                                .unwrap_or(expr.clone())
                            }
                        })
                        .unwrap_or(expr),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                    allow_string_like_resolution,
                );
                let chosen = self
                    .choose_preferred_imported_call_arg_expr(
                        recovered_source_expr.clone(),
                        Some(normalized.clone()),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(normalized);
                self.sanitize_public_call_arg_expr(chosen)
            }
        }
    }

    fn call_arg_requires_result_rebuild(&self, expr: &CExpr) -> bool {
        let CExpr::Call { args, .. } = expr else {
            return false;
        };
        match self.source_proof_for_call_expr(expr) {
            CallExprSourceProof::Exact(source_call) => {
                if !self.imported_or_modeled_call_target_for_optional_site(Some(source_call)) {
                    return true;
                }
            }
            CallExprSourceProof::ContradictedOrAmbiguous => return true,
            CallExprSourceProof::None => return true,
        }
        args.iter().any(|arg| {
            self.call_arg_contains_transient_name(arg, 0)
                || self.call_arg_contains_stack_placeholder(arg, 0)
                || matches!(arg, CExpr::Call { .. })
                || self.expr_is_generic_entry_arg_like(arg)
        })
    }

    fn render_authoritative_source_call_arg(&self, binding: analysis::CallArgBinding) -> CExpr {
        let allow_string_like_resolution =
            !self.imported_input_binding_prefers_pointer_identity(&binding);
        let preserve_stable_input_slot = binding.role == analysis::CallArgRole::Input;
        let preserve_explicit_call_expr = binding.role == analysis::CallArgRole::Result
            || matches!(
                binding.arg,
                analysis::SemanticCallArg::FallbackExpr(CExpr::Call { .. })
            );
        let recovered_source_expr = self.recover_call_arg_expr_from_source_var(&binding);
        if let Some((block_addr, op_idx)) = binding.source_call
            && binding.role == analysis::CallArgRole::Result
            && let Some(owner) =
                self.stable_result_call_arg_owner_expr_for_source((block_addr, op_idx))
        {
            return self.sanitize_public_call_arg_expr(owner);
        }
        if let analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, args }) = &binding.arg {
            let should_preserve_direct_call = !args.iter().any(|arg| {
                self.call_arg_contains_transient_name(arg, 0)
                    || self.call_arg_contains_stack_placeholder(arg, 0)
                    || matches!(arg, CExpr::Call { .. })
                    || self.expr_is_generic_entry_arg_like(arg)
            });
            if should_preserve_direct_call {
                let mut args = args
                    .iter()
                    .cloned()
                    .map(|arg| {
                        self.normalize_imported_call_arg_expr(
                            arg,
                            false,
                            true,
                            allow_string_like_resolution,
                        )
                    })
                    .collect::<Vec<_>>();
                if let Some(max_arity) =
                    self.non_variadic_call_arity_for_optional_site(binding.source_call)
                {
                    args.truncate(max_arity);
                }
                let call = CExpr::call((**func).clone(), args);
                let call = binding
                    .source_call
                    .map(|source_call| {
                        self.canonicalize_call_expr_for_source_call(source_call, call.clone())
                    })
                    .unwrap_or(call);
                return self.sanitize_public_call_arg_expr(call);
            }
        }

        match binding.arg {
            analysis::SemanticCallArg::Semantic(value) => {
                if preserve_stable_input_slot
                    && Self::semantic_value_has_negative_stack_slot(&value)
                    && let Some(expr) = self
                        .render_imported_semantic_arg_value(&value, !allow_string_like_resolution)
                    && self.is_preservable_named_stack_slot_expr(&expr)
                {
                    return expr;
                }
                let expr = self
                    .render_imported_semantic_arg_value(&value, !allow_string_like_resolution)
                    .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(&value));
                let recovered_source_expr = if self
                    .entry_arg_alias_for_pointer_identity_value(&value)
                    .is_some()
                {
                    None
                } else {
                    recovered_source_expr
                };
                let expr = self
                    .choose_preferred_imported_call_arg_expr(
                        Some(expr.clone()),
                        recovered_source_expr.clone(),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(expr);
                let finalized = self.finalize_authoritative_imported_call_arg_expr(
                    expr,
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                    allow_string_like_resolution,
                );
                let chosen = self
                    .choose_preferred_imported_call_arg_expr(
                        Some(finalized.clone()),
                        recovered_source_expr.clone(),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(finalized);
                self.sanitize_public_call_arg_expr(chosen)
            }
            analysis::SemanticCallArg::StringAddr(addr) => self
                .lookup_string(addr)
                .map(|s| CExpr::StringLit(s.clone()))
                .or_else(|| {
                    self.lookup_symbol(addr)
                        .map(|name| CExpr::Var(name.clone()))
                })
                .unwrap_or(CExpr::UIntLit(addr)),
            analysis::SemanticCallArg::FallbackExpr(expr) => {
                let normalized = self.normalize_imported_call_arg_expr(
                    recovered_source_expr
                        .clone()
                        .map(|candidate| {
                            if self.call_arg_contains_transient_name(&expr, 0)
                                || self.call_arg_contains_stack_placeholder(&expr, 0)
                            {
                                candidate
                            } else {
                                self.choose_preferred_imported_call_arg_expr(
                                    Some(expr.clone()),
                                    Some(candidate),
                                    preserve_stable_input_slot,
                                    preserve_explicit_call_expr,
                                )
                                .unwrap_or(expr.clone())
                            }
                        })
                        .unwrap_or(expr),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                    allow_string_like_resolution,
                );
                let chosen = self
                    .choose_preferred_imported_call_arg_expr(
                        recovered_source_expr.clone(),
                        Some(normalized.clone()),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(normalized);
                self.sanitize_public_call_arg_expr(chosen)
            }
        }
    }

    pub(super) fn render_authoritative_source_args_for_call(
        &self,
        source_call: (u64, usize),
    ) -> Vec<CExpr> {
        if let Some(prepared) = self.inputs.prepared_ssa
            && let Some(call_site) = self.prepared_call_site_for_op(source_call.0, source_call.1)
            && let Some(target) = prepared.value_var(call_site.target)
            && let Some(args) = self.prepared_call_args_for_site_with_direct_target(
                source_call.0,
                source_call.1,
                &self.resolve_call_target_for_site(source_call.0, source_call.1, target),
                prepared
                    .resolved_call_target(call_site)
                    .or_else(|| parse_address_from_var_name(&target.name)),
            )
        {
            return args
                .args
                .into_iter()
                .map(|arg| self.sanitize_public_call_arg_expr(self.rewrite_stack_expr(arg)))
                .collect();
        }
        if self
            .prepared_call_view_for_site(source_call.0, source_call.1)
            .is_some()
        {
            return Vec::new();
        }
        if let Some(cached) = self
            .authoritative_source_args_cache
            .borrow()
            .get(&source_call)
            .cloned()
        {
            return cached;
        }

        let args = self
            .call_args_map()
            .get(&source_call)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .map(|binding| self.render_authoritative_source_call_arg(binding))
            .collect::<Vec<_>>();

        self.authoritative_source_args_cache
            .borrow_mut()
            .insert(source_call, args.clone());
        args
    }

    pub(super) fn recover_call_arg_expr_from_source_var(
        &self,
        binding: &analysis::CallArgBinding,
    ) -> Option<CExpr> {
        if binding.role == analysis::CallArgRole::Result
            && let Some(source_call) = binding.source_call
            && let Some(owner) = self.stable_result_call_arg_owner_expr_for_source(source_call)
        {
            return Some(owner);
        }
        let source_value_id = binding.source_value_id.or_else(|| {
            binding
                .source_var_name
                .as_deref()
                .and_then(|name| self.use_info().value_id_for_name(name))
        });
        let source_var_name = binding.source_var_name.clone().or_else(|| {
            source_value_id.and_then(|value_id| self.use_info().display_name_for_value_id(value_id))
        })?;
        let source_var_name = source_var_name.as_str();
        let preserve_stable_input_slot = binding.role == analysis::CallArgRole::Input;
        if preserve_stable_input_slot
            && let analysis::SemanticCallArg::Semantic(analysis::SemanticValue::Load {
                addr, ..
            }) = &binding.arg
            && addr.index.is_none()
            && addr.offset_bytes == 0
            && addr.scale_bytes == 0
            && let analysis::BaseRef::StackSlot(offset) = addr.base
            && let Some(alias) = self.resolve_stack_var(offset)
        {
            return Some(CExpr::Var(alias));
        }
        let prefer = |current: Option<CExpr>, candidate: Option<CExpr>| {
            self.choose_preferred_imported_call_arg_expr(
                current,
                candidate,
                preserve_stable_input_slot,
                false,
            )
        };
        let mut best = None;
        let prepared_expr = self
            .prepared_semantic_view()
            .and_then(|prepared| {
                source_value_id
                    .and_then(|value_id| prepared.owner_expr_for_value_id(value_id))
                    .or_else(|| prepared.owner_expr_for_name(source_var_name))
                    .or_else(|| {
                        self.find_ssa_name_for_rendered_alias(source_var_name)
                            .as_deref()
                            .and_then(|resolved| prepared.owner_expr_for_name(resolved))
                    })
                    .cloned()
            })
            .filter(|expr| !matches!(expr, CExpr::AddrOf(_)));
        let mut owned_visited = HashSet::new();
        let source_owned_expr =
            self.recover_source_owned_expr_for_name(source_var_name, 0, &mut owned_visited);

        if best.is_none()
            && let Some(owner) = self.stable_owned_call_result_expr_for_name(source_var_name, true)
        {
            return Some(owner);
        }
        best = prefer(best, source_owned_expr.clone());

        let raw_expr = source_value_id
            .and_then(|value_id| self.definition_for_value_id(value_id).cloned())
            .or_else(|| self.lookup_definition_raw(source_var_name))
            .map(|raw| {
                let mut imported_visited = HashSet::new();
                self.resolve_imported_call_arg_expr(&raw, 0, &mut imported_visited)
            });
        best = prefer(best, raw_expr.clone());

        let visible_expr = source_value_id
            .and_then(|value_id| {
                self.use_info()
                    .render_definition_for_value(value_id)
                    .cloned()
            })
            .or_else(|| self.lookup_definition(source_var_name))
            .map(|visible_def| {
                let mut imported_visited = HashSet::new();
                self.resolve_imported_call_arg_expr(&visible_def, 0, &mut imported_visited)
            });
        best = prefer(best, visible_expr.clone());

        best = prefer(best, self.best_visible_definition(source_var_name));
        best = prefer(best, source_owned_expr.clone());

        let best_is_low_signal = best.as_ref().is_none_or(|expr| {
            self.call_arg_contains_transient_name(expr, 0)
                || self.call_arg_contains_stack_placeholder(expr, 0)
                || self.call_arg_contains_low_quality_name(expr, 0)
        });
        if best_is_low_signal {
            best = prefer(best, prepared_expr.clone());
            let mut semantic_visited = HashSet::new();
            best = prefer(
                best,
                source_value_id
                    .and_then(|value_id| self.use_info().render_semantic_value_for_value(value_id))
                    .and_then(|value| self.render_semantic_value(value, 0, &mut semantic_visited))
                    .or_else(|| {
                        self.render_semantic_value_by_name(
                            source_var_name,
                            0,
                            &mut semantic_visited,
                        )
                    }),
            );
        } else if best.is_none() {
            best = prefer(best, prepared_expr.clone());
        }

        let recovered = best?;
        let rewritten = self.rewrite_stack_expr(recovered.clone());
        let best = prefer(Some(recovered), Some(rewritten.clone())).unwrap_or(rewritten);
        if matches!(&best, CExpr::Var(name) if self.is_autogenerated_stack_home_name(name))
            && let Some(raw_best) = self
                .lookup_definition_raw(source_var_name)
                .or_else(|| self.lookup_definition(source_var_name))
            && self.is_recovered_imported_call_arg_expr(&raw_best)
        {
            return Some(raw_best);
        }
        self.is_recovered_imported_call_arg_expr(&best)
            .then_some(best)
    }

    fn stable_result_call_arg_owner_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        let owner = self.stable_owned_call_result_expr_for_source(source_call)?;
        if let CExpr::Var(name) = &owner {
            let lower = name.to_ascii_lowercase();
            if is_generic_arg_name(name)
                || lower.starts_with("local_")
                || lower.starts_with("stack_")
                || lower.starts_with("arg_")
                || self.stack_offset_for_visible_storage_name(name).is_some()
            {
                return None;
            }
        }
        Some(owner)
    }

    fn is_recovered_imported_call_arg_expr(&self, expr: &CExpr) -> bool {
        !self.call_arg_contains_transient_name(expr, 0)
            && !self.call_arg_contains_stack_placeholder(expr, 0)
            && !self.call_arg_contains_low_quality_name(expr, 0)
    }

    fn recover_source_owned_expr_for_name(
        &self,
        source_var_name: &str,
        depth: usize,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > 16 || !visited.insert(source_var_name.to_string()) {
            return None;
        }
        if let Some(source_call) = self
            .call_result_source_for_ssa_name(source_var_name)
            .or_else(|| self.local_post_call_source_for_ssa_name(source_var_name))
            && let Some(owner) = self.stable_owned_call_result_expr_for_source(source_call)
        {
            return Some(owner);
        }

        let producer = self.use_info().producers.get(source_var_name)?;
        match producer {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. } => {
                Some(self.recover_source_owned_operand_expr(src, depth + 1, visited))
            }
            SSAOp::IntAdd { dst, a, b } => Some(self.identity_simplify_binary(
                BinaryOp::Add,
                self.recover_source_owned_operand_expr(a, depth + 1, visited),
                self.recover_source_owned_operand_expr(b, depth + 1, visited),
                (dst.size > 0).then_some(dst.size),
            )),
            SSAOp::IntSub { dst, a, b } => Some(self.identity_simplify_binary(
                BinaryOp::Sub,
                self.recover_source_owned_operand_expr(a, depth + 1, visited),
                self.recover_source_owned_operand_expr(b, depth + 1, visited),
                (dst.size > 0).then_some(dst.size),
            )),
            _ => None,
        }
    }

    fn recover_source_owned_operand_expr(
        &self,
        var: &SSAVar,
        depth: usize,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if var.is_const() {
            return self.const_to_expr(var);
        }
        self.recover_source_owned_expr_for_name(&var.display_name(), depth, visited)
            .unwrap_or_else(|| self.get_expr(var))
    }

    pub(super) fn expr_for_semantic_call_arg_fallback(
        &self,
        value: &analysis::SemanticValue,
    ) -> CExpr {
        match value {
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => expr.clone(),
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(value_ref)) => {
                if value_ref.var.is_const() {
                    self.const_to_expr(&value_ref.var)
                } else {
                    let rendered = self.var_name(&value_ref.var);
                    self.arg_alias_for_rendered_name(&rendered)
                        .map(CExpr::Var)
                        .unwrap_or_else(|| CExpr::Var(rendered))
                }
            }
            analysis::SemanticValue::Address(addr) => {
                let mut visited = HashSet::new();
                self.render_address_expr_from_addr(addr, 0, &mut visited)
                    .or_else(|| self.render_base_ref_expr(&addr.base, true, 0, &mut visited))
                    .unwrap_or_else(Self::unresolved_call_arg_expr)
            }
            analysis::SemanticValue::Load { addr, size } => {
                let mut visited = HashSet::new();
                self.render_load_from_addr(addr, *size, 0, &mut visited)
                    .or_else(|| {
                        let addr_expr =
                            self.render_address_expr_from_addr(addr, 0, &mut visited)?;
                        Some(CExpr::Deref(Box::new(addr_expr)))
                    })
                    .unwrap_or_else(Self::unresolved_call_arg_expr)
            }
            analysis::SemanticValue::Unknown => Self::unresolved_call_arg_expr(),
        }
    }

    pub(super) fn normalize_imported_call_arg_expr(
        &self,
        expr: CExpr,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
        allow_string_like_resolution: bool,
    ) -> CExpr {
        let expr = match self.source_proof_for_call_expr(&expr) {
            CallExprSourceProof::Exact(source_call) => self.normalize_call_expr_for_source_call(
                source_call,
                expr,
                FinalExprNormalizeContext::DefinitionRoot,
            ),
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

    fn finalize_authoritative_imported_call_arg_expr(
        &self,
        expr: CExpr,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
        allow_string_like_resolution: bool,
    ) -> CExpr {
        let expr =
            self.rewrite_imported_call_arg_expr_with_prepared_owners(expr, 0, &mut HashSet::new());
        let rewritten = self.rewrite_stack_expr(expr);
        let mut best = Some(rewritten.clone());
        let mut imported_visited = HashSet::new();
        let imported_resolved =
            self.resolve_imported_call_arg_expr(&rewritten, 0, &mut imported_visited);
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(imported_resolved.clone()),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        let call_normalized = self.normalize_final_call_expr(imported_resolved.clone());
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(call_normalized.clone()),
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
                .unwrap_or_else(|| call_normalized.clone())
            }
            _ => call_normalized.clone(),
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
        let finalized = if allow_string_like_resolution {
            let mut string_visited = HashSet::new();
            self.resolve_string_like_imported_call_arg_expr(&literalized, 0, &mut string_visited)
                .unwrap_or(literalized)
        } else {
            literalized
        };
        best = self.choose_preferred_imported_call_arg_expr(
            best,
            Some(finalized),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        );
        let best = best.unwrap_or(rewritten.clone());
        if preserve_stable_input_slot
            && self.is_preservable_named_stack_slot_expr(&rewritten)
            && self.is_direct_constish_visible_expr(&best, 0)
        {
            return self.sanitize_public_call_arg_expr(rewritten);
        }
        self.sanitize_public_call_arg_expr(self.rewrite_stack_expr(best))
    }

    fn param_home_alias_expr_for_call_arg_binding(
        &self,
        binding: &analysis::CallArgBinding,
    ) -> Option<CExpr> {
        if binding.role != analysis::CallArgRole::Input {
            return None;
        }

        let mut offsets = std::collections::BTreeSet::new();
        if let Some(offset) = binding.stack_offset {
            offsets.insert(offset);
        }
        if let Some(value_id) = binding.source_value_id {
            if let Some(slot) = self.use_info().stack_slots_by_value.get(&value_id) {
                offsets.insert(slot.offset);
            }
            if let Some(prov) = self.use_info().forwarded_values_by_value.get(&value_id)
                && let Some(offset) = prov.stack_slot
            {
                offsets.insert(offset);
            }
        }
        if let Some(name) = binding.source_var_name.as_deref() {
            if let Some(slot) = self.stack_slot_provenance_for_name(name) {
                offsets.insert(slot.offset);
            }
            if let Some(prov) = self.forwarded_value_for_name(name)
                && let Some(offset) = prov.stack_slot
            {
                offsets.insert(offset);
            }
        }

        match &binding.arg {
            analysis::SemanticCallArg::Semantic(
                analysis::SemanticValue::Load { addr, .. } | analysis::SemanticValue::Address(addr),
            ) => {
                if addr.index.is_none()
                    && addr.offset_bytes == 0
                    && addr.scale_bytes == 0
                    && let analysis::BaseRef::StackSlot(offset) = addr.base
                {
                    offsets.insert(offset);
                }
            }
            analysis::SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
                if let Some(slot) = self.stack_slot_provenance_for_name(name) {
                    offsets.insert(slot.offset);
                }
                if let Some(prov) = self.forwarded_value_for_name(name)
                    && let Some(offset) = prov.stack_slot
                {
                    offsets.insert(offset);
                }
            }
            _ => {}
        }

        offsets
            .into_iter()
            .find_map(|offset| self.param_home_alias_for_stack_offset(offset))
            .map(CExpr::Var)
    }

    fn imported_input_binding_prefers_pointer_identity(
        &self,
        binding: &analysis::CallArgBinding,
    ) -> bool {
        if binding.role != analysis::CallArgRole::Input {
            return false;
        }

        if let Some(expr) = self.recover_call_arg_expr_from_source_var(binding) {
            return self.is_preserved_imported_input_expr(&expr)
                && !self.is_direct_constish_visible_expr(&expr, 0);
        }

        match &binding.arg {
            analysis::SemanticCallArg::Semantic(analysis::SemanticValue::Load { addr, .. })
            | analysis::SemanticCallArg::Semantic(analysis::SemanticValue::Address(addr)) => {
                if let analysis::BaseRef::StackSlot(offset) = addr.base
                    && let Some(name) = self.resolve_stack_var(offset)
                {
                    let expr = CExpr::Var(name);
                    return self.is_preserved_imported_input_expr(&expr)
                        && !self.is_direct_constish_visible_expr(&expr, 0);
                }
                false
            }
            analysis::SemanticCallArg::FallbackExpr(expr) => {
                self.is_preserved_imported_input_expr(expr)
                    && !self.is_direct_constish_visible_expr(expr, 0)
            }
            _ => false,
        }
    }

    fn semantic_value_has_negative_stack_slot(value: &analysis::SemanticValue) -> bool {
        match value {
            analysis::SemanticValue::Load { addr, .. } | analysis::SemanticValue::Address(addr) => {
                matches!(addr.base, analysis::BaseRef::StackSlot(offset) if offset < 0)
            }
            _ => false,
        }
    }

    fn render_imported_semantic_arg_value(
        &self,
        value: &analysis::SemanticValue,
        preserve_pointer_identity: bool,
    ) -> Option<CExpr> {
        if let Some(alias) = self.entry_arg_alias_for_pointer_identity_value(value) {
            return Some(CExpr::Var(alias));
        }

        if let analysis::SemanticValue::Load { addr, .. } = value
            && addr.index.is_none()
            && addr.offset_bytes == 0
            && addr.scale_bytes == 0
            && let analysis::BaseRef::StackSlot(offset) = addr.base
            && let Some(alias) = self.param_home_alias_for_stack_offset(offset)
        {
            return Some(CExpr::Var(alias));
        }

        if let Some(expr) =
            self.prepared_imported_semantic_arg_expr(value, preserve_pointer_identity)
        {
            return Some(expr);
        }

        if preserve_pointer_identity {
            if let analysis::SemanticValue::Address(addr) = value
                && let Some(expr) = self.render_stable_stack_offset_scalar_expr(addr)
            {
                return Some(expr);
            }
            match value {
                analysis::SemanticValue::Address(addr)
                    if matches!(addr.base, analysis::BaseRef::StackSlot(_)) =>
                {
                    let mut visited = HashSet::new();
                    return self
                        .render_address_expr_from_addr(addr, 0, &mut visited)
                        .or_else(|| self.render_stack_slot_address_expr_fallback(addr, 0));
                }
                analysis::SemanticValue::Load { addr, size }
                    if matches!(addr.base, analysis::BaseRef::StackSlot(_)) =>
                {
                    if let analysis::BaseRef::StackSlot(offset) = addr.base
                        && addr.index.is_none()
                        && addr.offset_bytes == 0
                        && let Some(expr) = self.render_stable_stack_scalar_expr(offset)
                    {
                        return Some(expr);
                    }
                    let mut visited = HashSet::new();
                    return self
                        .render_load_from_addr(addr, *size, 0, &mut visited)
                        .or_else(|| {
                            self.render_address_expr_from_addr(addr, 0, &mut visited)
                                .or_else(|| self.render_stack_slot_address_expr_fallback(addr, 0))
                                .map(|expr| match expr {
                                    CExpr::AddrOf(inner)
                                        if addr.index.is_none() && addr.offset_bytes == 0 =>
                                    {
                                        *inner
                                    }
                                    other => CExpr::Deref(Box::new(other)),
                                })
                        });
                }
                _ => {}
            }
        }

        if let analysis::SemanticValue::Address(addr) = value
            && addr.index.is_none()
            && addr.offset_bytes == 0
            && matches!(addr.base, analysis::BaseRef::Value(_))
        {
            if let analysis::BaseRef::Value(base_value) = &addr.base
                && let Some(expr) = self.best_visible_definition(&base_value.display_name())
                && !matches!(expr, CExpr::StringLit(_))
            {
                return Some(expr);
            }
            let mut visited = HashSet::new();
            if let Some(expr) = self.render_base_ref_expr(&addr.base, false, 0, &mut visited) {
                return Some(expr);
            }
        }

        let mut visited = HashSet::new();
        self.render_semantic_value(value, 0, &mut visited)
    }

    fn entry_arg_alias_for_pointer_identity_value(
        &self,
        value: &analysis::SemanticValue,
    ) -> Option<String> {
        let analysis::SemanticValue::Address(addr) = value else {
            return None;
        };
        if addr.index.is_some() || addr.offset_bytes != 0 || addr.scale_bytes != 0 {
            return None;
        }
        let analysis::BaseRef::Value(root) = &addr.base else {
            return None;
        };
        (root.var.version == 0)
            .then(|| self.arg_alias_for_register_name(&root.var.name))
            .flatten()
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
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return CExpr::Var(name);
                }
                let resolved = self
                    .prepared_semantic_view()
                    .and_then(|prepared| prepared.owner_expr_for_name(&name))
                    .cloned()
                    .filter(|inner| {
                        inner != &CExpr::Var(name.clone()) && !matches!(inner, CExpr::AddrOf(_))
                    })
                    .map(|inner| {
                        self.rewrite_imported_call_arg_expr_with_prepared_owners(
                            inner,
                            depth + 1,
                            visited,
                        )
                    })
                    .or_else(|| {
                        self.stack_offset_for_visible_storage_name(&name)
                            .and_then(|offset| self.resolve_stack_var(offset))
                            .filter(|alias| !alias.eq_ignore_ascii_case(&name))
                            .map(CExpr::Var)
                    })
                    .unwrap_or_else(|| CExpr::Var(name.clone()));
                visited.remove(&name);
                resolved
            }
            other => other.map_children(&mut |child| {
                self.rewrite_imported_call_arg_expr_with_prepared_owners(child, depth + 1, visited)
            }),
        }
    }

    fn expr_contains_prepared_owner_alias(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }

        let Some(prepared) = self.prepared_semantic_view() else {
            return false;
        };

        match expr {
            CExpr::Var(name) => prepared.owner_expr_for_name(name).is_some(),
            CExpr::Deref(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Paren(inner)
            | CExpr::Cast { expr: inner, .. }
            | CExpr::Unary { operand: inner, .. }
            | CExpr::Sizeof(inner) => self.expr_contains_prepared_owner_alias(inner, depth + 1),
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_prepared_owner_alias(left, depth + 1)
                    || self.expr_contains_prepared_owner_alias(right, depth + 1)
            }
            CExpr::Subscript { base, index } => {
                self.expr_contains_prepared_owner_alias(base, depth + 1)
                    || self.expr_contains_prepared_owner_alias(index, depth + 1)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_prepared_owner_alias(base, depth + 1)
            }
            CExpr::Call { func, args } => {
                self.expr_contains_prepared_owner_alias(func, depth + 1)
                    || args
                        .iter()
                        .any(|arg| self.expr_contains_prepared_owner_alias(arg, depth + 1))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_contains_prepared_owner_alias(cond, depth + 1)
                    || self.expr_contains_prepared_owner_alias(then_expr, depth + 1)
                    || self.expr_contains_prepared_owner_alias(else_expr, depth + 1)
            }
            CExpr::Comma(items) => items
                .iter()
                .any(|item| self.expr_contains_prepared_owner_alias(item, depth + 1)),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    pub(super) fn prepared_imported_semantic_arg_expr(
        &self,
        value: &analysis::SemanticValue,
        preserve_pointer_identity: bool,
    ) -> Option<CExpr> {
        let prepared = self.prepared_semantic_view()?;
        let owner_for_var = |var: &r2ssa::SSAVar| {
            let preferred = prepared
                .owner_expr_for_var(var)
                .cloned()
                .filter(|expr| preserve_pointer_identity || !matches!(expr, CExpr::AddrOf(_)))
                .map(|expr| self.rewrite_stack_expr(expr))
                .filter(|expr| {
                    !self.call_arg_contains_transient_name(expr, 0)
                        && !self.call_arg_contains_stack_placeholder(expr, 0)
                        && !self.call_arg_contains_low_quality_name(expr, 0)
                        && !matches!(
                            expr,
                            CExpr::Var(name)
                                if self.is_autogenerated_stack_home_name(name)
                                    || self.is_generic_stack_local_owner_name(name)
                        )
                });

            preferred
                .or_else(|| {
                    let rendered = self.var_name(var);
                    self.arg_alias_for_rendered_name(&rendered).map(CExpr::Var)
                })
                .or_else(|| {
                    prepared
                        .stack_offset_for_var(var)
                        .and_then(|offset| self.resolve_stack_var(offset))
                        .map(CExpr::Var)
                })
        };

        match value {
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(root)) => {
                owner_for_var(&root.var).or_else(|| {
                    prepared
                        .call_result_source_for_var(&root.var)
                        .and_then(|source_call| {
                            self.stable_owned_call_result_expr_for_source(source_call)
                                .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
                        })
                })
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => {
                let original = self.rewrite_stack_expr(expr.clone());
                let should_try_prepared_owner_rewrite =
                    self.expr_contains_prepared_owner_alias(expr, 0);
                if !self.call_arg_contains_transient_name(&original, 0)
                    && !self.call_arg_contains_stack_placeholder(&original, 0)
                    && !self.call_arg_contains_low_quality_name(&original, 0)
                    && !should_try_prepared_owner_rewrite
                {
                    return Some(original);
                }
                let rewritten = self.rewrite_imported_call_arg_expr_with_prepared_owners(
                    expr.clone(),
                    0,
                    &mut HashSet::new(),
                );
                let rewritten = self.rewrite_stack_expr(rewritten);
                self.choose_preferred_imported_call_arg_expr(
                    Some(original),
                    Some(rewritten.clone()),
                    true,
                    false,
                )
                .or(Some(rewritten))
            }
            analysis::SemanticValue::Address(addr) => match &addr.base {
                analysis::BaseRef::Value(root)
                    if addr.index.is_none() && addr.offset_bytes == 0 && addr.scale_bytes == 0 =>
                {
                    owner_for_var(&root.var)
                }
                analysis::BaseRef::StackSlot(offset)
                    if addr.index.is_none() && addr.offset_bytes == 0 && addr.scale_bytes == 0 =>
                {
                    self.resolve_stack_var(*offset).map(CExpr::Var).map(|expr| {
                        if preserve_pointer_identity {
                            CExpr::AddrOf(Box::new(expr))
                        } else {
                            expr
                        }
                    })
                }
                _ => None,
            },
            analysis::SemanticValue::Load { addr, .. } => match &addr.base {
                analysis::BaseRef::Value(root)
                    if addr.index.is_none() && addr.offset_bytes == 0 && addr.scale_bytes == 0 =>
                {
                    owner_for_var(&root.var)
                }
                analysis::BaseRef::StackSlot(offset)
                    if addr.index.is_none() && addr.offset_bytes == 0 && addr.scale_bytes == 0 =>
                {
                    self.resolve_stack_var(*offset).map(CExpr::Var)
                }
                _ => None,
            },
            analysis::SemanticValue::Unknown => None,
        }
    }

    fn render_stable_stack_scalar_expr(&self, offset: i64) -> Option<CExpr> {
        let value = self.use_info().stable_stack_values.get(&offset)?;
        let mut visited = HashSet::new();
        let rendered = self.render_semantic_value(value, 0, &mut visited)?;
        let rewritten = self.rewrite_stack_expr(rendered.clone());
        let best = self
            .choose_preferred_visible_expr(Some(rendered), Some(rewritten.clone()))
            .unwrap_or(rewritten);
        (!matches!(best, CExpr::AddrOf(_) | CExpr::Deref(_))).then_some(best)
    }

    fn render_stable_stack_offset_scalar_expr(
        &self,
        addr: &analysis::NormalizedAddr,
    ) -> Option<CExpr> {
        let analysis::BaseRef::StackSlot(base_offset) = addr.base else {
            return None;
        };
        if addr.index.is_some() || addr.offset_bytes == 0 {
            return None;
        }

        let base_expr = self.render_stable_stack_scalar_expr(base_offset)?;
        let magnitude = addr.offset_bytes.unsigned_abs() as i64;
        Some(if addr.offset_bytes < 0 {
            CExpr::binary(
                crate::ast::BinaryOp::Sub,
                base_expr,
                CExpr::IntLit(magnitude),
            )
        } else {
            CExpr::binary(
                crate::ast::BinaryOp::Add,
                base_expr,
                CExpr::IntLit(magnitude),
            )
        })
    }

    fn render_stack_slot_address_expr_fallback(
        &self,
        addr: &analysis::NormalizedAddr,
        depth: u32,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        let analysis::BaseRef::StackSlot(base_offset) = addr.base else {
            return None;
        };

        let base_name = self
            .resolve_stack_var(base_offset)
            .unwrap_or_else(|| stack_slot_synthetic_name(base_offset));
        let mut expr = CExpr::AddrOf(Box::new(CExpr::Var(base_name)));

        if let Some(index) = &addr.index {
            let mut visited = HashSet::new();
            let index_expr = self.render_value_ref(index, depth + 1, &mut visited)?;
            let scaled = if addr.scale_bytes.unsigned_abs() <= 1 {
                index_expr
            } else {
                CExpr::binary(
                    crate::ast::BinaryOp::Mul,
                    index_expr,
                    CExpr::IntLit(addr.scale_bytes.unsigned_abs() as i64),
                )
            };
            expr = CExpr::binary(
                if addr.scale_bytes < 0 {
                    crate::ast::BinaryOp::Sub
                } else {
                    crate::ast::BinaryOp::Add
                },
                expr,
                scaled,
            );
        }

        if addr.offset_bytes != 0 {
            expr = CExpr::binary(
                if addr.offset_bytes < 0 {
                    crate::ast::BinaryOp::Sub
                } else {
                    crate::ast::BinaryOp::Add
                },
                expr,
                CExpr::IntLit(addr.offset_bytes.unsigned_abs() as i64),
            );
        }

        Some(expr)
    }

    fn choose_preferred_imported_call_arg_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
    ) -> Option<CExpr> {
        if preserve_explicit_call_expr
            && let (Some(CExpr::Call { .. }), Some(candidate_expr)) = (&current, &candidate)
            && !matches!(candidate_expr, CExpr::Call { .. })
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
    pub(crate) fn op_to_stmt(&self, op: &SSAOp) -> Option<CStmt> {
        let mut frame = LowerFrame::for_stmt(0, 0, false);
        self.lowered_to_stmt(self.lower_op(op, &mut frame))
    }
}

fn stack_slot_synthetic_name(offset: i64) -> String {
    if offset < 0 {
        format!("local_{:x}", (-offset) as u64)
    } else {
        format!("stack_{:x}", offset as u64)
    }
}
