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
    fn prepared_call_target_var(&self, target: r2ssa::ValueId) -> Option<&SSAVar> {
        self.inputs.prepared_ssa?.value_var(target)
    }

    fn prepared_constish_target_addr(&self, target: &SSAVar) -> Option<u64> {
        extract_call_address(&target.name)
            .or_else(|| {
                target
                    .is_const()
                    .then(|| parse_const_value(&target.name))
                    .flatten()
            })
            .or_else(|| {
                self.prepared_canonical_value_root(target)
                    .as_ref()
                    .and_then(|root| {
                        extract_call_address(&root.name).or_else(|| {
                            root.is_const()
                                .then(|| parse_const_value(&root.name))
                                .flatten()
                        })
                    })
            })
    }

    fn prepared_direct_call_target(&self, block_addr: u64, op_idx: usize) -> Option<u64> {
        let call_site = self.prepared_call_site_for_op(block_addr, op_idx)?;
        call_site.direct_target.or_else(|| {
            self.prepared_call_target_var(call_site.target)
                .and_then(|target| self.prepared_constish_target_addr(target))
        })
    }

    pub(super) fn resolve_call_target_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        target: &SSAVar,
    ) -> CExpr {
        if let Some(name) = self
            .prepared_call_view_for_site(block_addr, op_idx)
            .and_then(|view| view.callee_name.clone())
        {
            return CExpr::Var(name);
        }
        if let Some(addr) = self.prepared_direct_call_target(block_addr, op_idx)
            && let Some(name) = self.callee_identity_for_direct_target(addr).display_name
        {
            return CExpr::Var(name);
        }
        self.resolve_call_target(target)
    }

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
            } else if let Some(max_arity) = self.printf_literal_variadic_arity(callee, &rendered) {
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

    pub(super) fn prepared_call_args_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        callee: &CExpr,
    ) -> Option<PreparedCallArgs> {
        let view = self.prepared_call_view_for_site(block_addr, op_idx)?;
        if view.authoritative_args.is_empty()
            || view.authoritative_args.len() != view.authoritative_arg_values.len()
        {
            return None;
        }

        let args =
            self.normalize_prepared_call_args_for_callee(callee, view.authoritative_args.clone());
        let values = view
            .authoritative_arg_values
            .iter()
            .take(args.len())
            .copied()
            .collect::<Vec<_>>();
        (values.len() == args.len()).then_some(PreparedCallArgs { args, values })
    }

    pub(super) fn normalize_prepared_call_args_for_callee(
        &self,
        callee: &CExpr,
        args: Vec<CExpr>,
    ) -> Vec<CExpr> {
        let imported_or_modeled =
            self.is_imported_call_target(callee) || self.is_modeled_call_target(callee);
        let mut normalized = if imported_or_modeled {
            args.into_iter()
                .map(|arg| self.normalize_imported_call_arg_expr(arg, true, false, true))
                .collect::<Vec<_>>()
        } else {
            args.into_iter()
                .map(|arg| self.normalize_call_arg_expr_for_callee(callee, arg))
                .collect::<Vec<_>>()
        };
        if let Some(max_arity) = self.non_variadic_call_arity(callee) {
            normalized.truncate(max_arity);
        } else if imported_or_modeled
            && let Some(max_arity) = self.printf_literal_variadic_arity(callee, &normalized)
        {
            normalized.truncate(max_arity);
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
        if !self.requires_certified_rendering() {
            return Some(CertifiedCallArgs {
                args: self.render_call_args_for_callee(callee, raw_args),
                values: Vec::new(),
            });
        }

        let cert = self.certified_callsite_for_op(block_addr, op_idx)?;
        let proof = self.certified_render_context()?;
        let expected_values = certified_callsite_argument_values(cert);

        let prepared_view_has_args = self
            .prepared_call_view_for_site(block_addr, op_idx)
            .is_some_and(|view| !view.authoritative_args.is_empty());
        if let Some(prepared_args) = self.prepared_call_args_for_site(block_addr, op_idx, callee) {
            if prepared_args.values.len() <= expected_values.len()
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
        if prepared_view_has_args {
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

        let args = self.render_call_args_for_callee(callee, raw_args.clone());
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

    fn certified_call_arg_binding_value(
        &self,
        binding: &analysis::CallArgBinding,
        expected_values: &[r2ssa::ValueId],
        proof: &CertifiedRenderContext<'_>,
        index: usize,
    ) -> Option<r2ssa::ValueId> {
        let expected = *expected_values.get(index)?;
        match &binding.arg {
            analysis::SemanticCallArg::StringAddr(_) => {
                proof.expression_is_renderable(expected).then_some(expected)
            }
            analysis::SemanticCallArg::Semantic(_) | analysis::SemanticCallArg::FallbackExpr(_) => {
                binding
                    .source_value_id
                    .filter(|value| *value == expected && proof.expression_is_renderable(*value))
            }
        }
    }

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

    pub(super) fn non_variadic_call_arity(&self, callee: &CExpr) -> Option<usize> {
        let identity = self.callee_identity_for_expr(callee)?;
        let cache_key = identity.primary_key();
        if let Some(cached) = self
            .non_variadic_call_arity_cache
            .borrow()
            .get(&cache_key)
            .copied()
        {
            return cached;
        }

        let known_arity = identity.non_variadic_known_arity();
        let summary_arity = identity
            .aliases
            .iter()
            .find_map(|alias| self.summary_helper_view_for_name(alias))
            .and_then(|summary| summary.arg_count_hint);

        let mut arena = TypeArena::default();
        let mut registry_arity = None;
        for candidate in identity.aliases.iter().map(String::as_str) {
            if let Some(resolved) =
                self.signature_registry
                    .resolve(candidate, &mut arena, self.inputs.arch.ptr_size)
            {
                registry_arity = (!resolved.variadic).then_some(resolved.params.len());
                break;
            }
        }

        let result = [known_arity, summary_arity, registry_arity]
            .into_iter()
            .flatten()
            .min();
        self.non_variadic_call_arity_cache
            .borrow_mut()
            .insert(cache_key, result);
        result
    }

    pub(super) fn resolve_call_target(&self, target: &SSAVar) -> CExpr {
        if let Some(addr) = self.prepared_constish_target_addr(target)
            && let Some(name) = self.callee_identity_for_direct_target(addr).display_name
        {
            return CExpr::Var(name);
        }
        self.get_expr(target)
    }

    pub(super) fn is_modeled_call_target(&self, callee: &CExpr) -> bool {
        let Some(identity) = self.callee_identity_for_expr(callee) else {
            return false;
        };

        if identity
            .aliases
            .iter()
            .any(|alias| self.summary_helper_view_for_name(alias).is_some())
        {
            return true;
        }

        self.callee_facts_map()
            .keys()
            .any(|addr| identity.matches_identity(&self.callee_identity_for_direct_target(*addr)))
    }

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

    fn render_imported_call_arg(&self, binding: analysis::CallArgBinding) -> CExpr {
        let allow_string_like_resolution =
            !self.imported_input_binding_prefers_pointer_identity(&binding);
        if let Some(param_home_alias) = self.param_home_alias_expr_for_call_arg_binding(&binding) {
            return param_home_alias;
        }
        if let Some((block_addr, op_idx)) = binding.source_call
            && binding.role == analysis::CallArgRole::Result
            && let analysis::SemanticCallArg::FallbackExpr(CExpr::Var(name)) = &binding.arg
            && let Some(owner_name) =
                self.stable_owned_call_result_name_for_source((block_addr, op_idx))
            && !owner_name.eq_ignore_ascii_case(name)
        {
            return CExpr::Var(owner_name);
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
                if let Some(max_arity) = self.non_variadic_call_arity(&func) {
                    args.truncate(max_arity);
                }
                return CExpr::call(*func, args);
            }
            let mut args = self.render_authoritative_source_args_for_call((block_addr, op_idx));
            if let Some(max_arity) = self.non_variadic_call_arity(&func) {
                args.truncate(max_arity);
            }
            return CExpr::call(*func, args);
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
                } else if self.is_direct_constish_visible_expr(&expr, 0)
                    && !self.call_arg_contains_transient_name(&expr, 0)
                    && !self.call_arg_contains_stack_placeholder(&expr, 0)
                    && !self.expr_is_generic_entry_arg_like(&expr)
                {
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
                self.choose_preferred_imported_call_arg_expr(
                    Some(finalized.clone()),
                    recovered_source_expr.clone(),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                )
                .unwrap_or(finalized)
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
                let recovered_source_expr = if self.is_direct_constish_visible_expr(&expr, 0)
                    && !self.call_arg_contains_transient_name(&expr, 0)
                    && !self.call_arg_contains_stack_placeholder(&expr, 0)
                    && !self.expr_is_generic_entry_arg_like(&expr)
                    && !matches!(expr, CExpr::Call { .. })
                {
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
                self.choose_preferred_imported_call_arg_expr(
                    recovered_source_expr.clone(),
                    Some(normalized.clone()),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                )
                .unwrap_or(normalized)
            }
        }
    }

    fn call_arg_requires_result_rebuild(&self, expr: &CExpr) -> bool {
        let CExpr::Call { func, args } = expr else {
            return false;
        };
        if !self.is_imported_call_target(func) && !self.is_modeled_call_target(func) {
            return true;
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
            && let Some(owner) = self.stable_owned_call_result_expr_for_source((block_addr, op_idx))
        {
            return owner;
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
                if let Some(max_arity) = self.non_variadic_call_arity(func) {
                    args.truncate(max_arity);
                }
                return CExpr::call((**func).clone(), args);
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
                self.choose_preferred_imported_call_arg_expr(
                    Some(finalized.clone()),
                    recovered_source_expr.clone(),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                )
                .unwrap_or(finalized)
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
                self.choose_preferred_imported_call_arg_expr(
                    recovered_source_expr.clone(),
                    Some(normalized.clone()),
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                )
                .unwrap_or(normalized)
            }
        }
    }

    pub(super) fn render_authoritative_source_args_for_call(
        &self,
        source_call: (u64, usize),
    ) -> Vec<CExpr> {
        if let Some(call_site) = self.prepared_call_site_for_op(source_call.0, source_call.1)
            && let Some(target) = self.prepared_call_target_var(call_site.target)
            && let Some(args) = self.prepared_call_args_for_site(
                source_call.0,
                source_call.1,
                &self.resolve_call_target_for_site(source_call.0, source_call.1, target),
            )
        {
            return args
                .args
                .into_iter()
                .map(|arg| self.sanitize_public_call_arg_expr(self.rewrite_stack_expr(arg)))
                .collect();
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

    fn recover_call_arg_expr_from_source_var(
        &self,
        binding: &analysis::CallArgBinding,
    ) -> Option<CExpr> {
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

        if best.is_none()
            && let Some(owner) = self.stable_owned_call_result_expr_for_name(source_var_name, true)
        {
            return Some(owner);
        }

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

        let best_is_low_signal = best.as_ref().is_none_or(|expr| {
            self.call_arg_contains_transient_name(expr, 0)
                || self.call_arg_contains_stack_placeholder(expr, 0)
                || self.call_arg_contains_low_quality_name(expr, 0)
                || matches!(expr, CExpr::Var(name) if self.is_autogenerated_stack_home_name(name))
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
            && !matches!(&raw_best, CExpr::Var(raw_name) if self.is_autogenerated_stack_home_name(raw_name))
        {
            return Some(raw_best);
        }
        (!self.call_arg_contains_transient_name(&best, 0)
            && !self.call_arg_contains_stack_placeholder(&best, 0))
        .then_some(best)
    }

    pub(super) fn printf_literal_variadic_arity(
        &self,
        callee: &CExpr,
        rendered_args: &[CExpr],
    ) -> Option<usize> {
        let identity = self.callee_identity_for_expr(callee)?;
        if !identity.matches_normalized_name("printf") {
            return None;
        }
        let format_string = self.resolved_printf_format_string(rendered_args.first()?)?;
        Some(1 + count_printf_placeholders(&format_string))
    }

    fn resolved_printf_format_string(&self, expr: &CExpr) -> Option<String> {
        match expr {
            CExpr::StringLit(text) => Some(text.clone()),
            other => self
                .resolve_literalish_call_arg_expr(other)
                .and_then(|resolved| match resolved {
                    CExpr::StringLit(text) => Some(text),
                    _ => None,
                })
                .or_else(|| {
                    let mut visited = HashSet::new();
                    self.resolve_string_like_imported_call_arg_expr(other, 0, &mut visited)
                        .and_then(|resolved| match resolved {
                            CExpr::StringLit(text) => Some(text),
                            _ => None,
                        })
                }),
        }
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
                    .unwrap_or(CExpr::UIntLit(0))
            }
            analysis::SemanticValue::Load { addr, size } => {
                let mut visited = HashSet::new();
                self.render_load_from_addr(addr, *size, 0, &mut visited)
                    .or_else(|| {
                        let addr_expr =
                            self.render_address_expr_from_addr(addr, 0, &mut visited)?;
                        Some(CExpr::Deref(Box::new(addr_expr)))
                    })
                    .unwrap_or(CExpr::UIntLit(0))
            }
            analysis::SemanticValue::Unknown => CExpr::UIntLit(0),
        }
    }

    pub(super) fn normalize_imported_call_arg_expr(
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
            return current;
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

fn count_printf_placeholders(format_string: &str) -> usize {
    let mut count = 0;
    let mut chars = format_string.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '%' {
            continue;
        }
        if matches!(chars.peek(), Some('%')) {
            chars.next();
            continue;
        }
        count += 1;
    }
    count
}
