use super::*;
use r2types::FunctionType;

impl<'a> FoldingContext<'a> {
    pub(super) fn render_call_args_for_callee(
        &self,
        callee: &CExpr,
        raw_args: Vec<analysis::CallArgBinding>,
    ) -> Vec<CExpr> {
        if self.is_imported_call_target(callee) {
            let mut rendered = raw_args
                .iter()
                .cloned()
                .map(|binding| self.render_imported_call_arg(binding))
                .collect::<Vec<_>>();
            self.repair_imported_result_source_sibling_args(&raw_args, &mut rendered);
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

    pub(super) fn lookup_known_signature(&self, callee_name: &str) -> Option<&FunctionType> {
        let normalized = normalize_callee_name(callee_name);
        self.inputs.known_function_signatures.get(&normalized)
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
        let name = Self::extract_callee_name(callee)?;
        if let Some(cached) = self
            .non_variadic_call_arity_cache
            .borrow()
            .get(name)
            .copied()
        {
            return cached;
        }

        let known_arity = self
            .lookup_known_signature(name)
            .and_then(|sig| (!sig.variadic).then_some(sig.params.len()));

        let normalized = normalize_callee_name(name);
        let mut arena = TypeArena::default();
        let mut registry_arity = None;
        for candidate in [name, normalized.as_str()] {
            if let Some(resolved) =
                self.signature_registry
                    .resolve(candidate, &mut arena, self.inputs.arch.ptr_size)
            {
                registry_arity = (!resolved.variadic).then_some(resolved.params.len());
                break;
            }
        }

        let result = match (known_arity, registry_arity) {
            (Some(known), Some(registry)) => Some(known.min(registry)),
            (Some(known), None) => Some(known),
            (None, Some(registry)) => Some(registry),
            (None, None) => None,
        };
        self.non_variadic_call_arity_cache
            .borrow_mut()
            .insert(name.to_string(), result);
        result
    }

    pub(super) fn resolve_call_target(&self, target: &SSAVar) -> CExpr {
        if let Some(addr) = extract_call_address(&target.name) {
            if let Some(name) = self.lookup_function(addr) {
                return CExpr::Var(name.clone());
            }
            if let Some(name) = self.lookup_symbol(addr) {
                return CExpr::Var(name.clone());
            }
        } else if target.is_const()
            && let Some(addr) = parse_const_value(&target.name)
        {
            if let Some(name) = self.lookup_function(addr) {
                return CExpr::Var(name.clone());
            }
            if let Some(name) = self.lookup_symbol(addr) {
                return CExpr::Var(name.clone());
            }
        }
        self.get_expr(target)
    }

    pub(super) fn render_call_arg_for_callee(
        &self,
        callee: &CExpr,
        binding: analysis::CallArgBinding,
    ) -> CExpr {
        if self.is_imported_call_target(callee) {
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
        if let Some((block_addr, op_idx)) = binding.source_call
            && binding.role == analysis::CallArgRole::Result
            && let Some(owner) = self.stable_owned_call_result_expr_for_source((block_addr, op_idx))
        {
            return owner;
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
                let recovered_source_expr = if matches!(
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
                        recovered_source_expr,
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(expr);
                self.finalize_authoritative_imported_call_arg_expr(
                    expr,
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                    allow_string_like_resolution,
                )
            }
            analysis::SemanticCallArg::StringAddr(addr) => self
                .lookup_string(addr)
                .map(|s| CExpr::StringLit(s.clone()))
                .or_else(|| {
                    self.lookup_symbol(addr)
                        .map(|name| CExpr::Var(name.clone()))
                })
                .unwrap_or(CExpr::UIntLit(addr)),
            analysis::SemanticCallArg::FallbackExpr(expr) => self.normalize_imported_call_arg_expr(
                if self.is_direct_constish_visible_expr(&expr, 0)
                    && !self.call_arg_contains_transient_name(&expr, 0)
                    && !self.call_arg_contains_stack_placeholder(&expr, 0)
                    && !self.expr_is_generic_entry_arg_like(&expr)
                    && !matches!(expr, CExpr::Call { .. })
                {
                    None
                } else {
                    recovered_source_expr
                }
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
            ),
        }
    }

    fn call_arg_requires_result_rebuild(&self, expr: &CExpr) -> bool {
        let CExpr::Call { func, args } = expr else {
            return false;
        };
        if !self.is_imported_call_target(func) {
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
                let expr = self
                    .choose_preferred_imported_call_arg_expr(
                        Some(expr.clone()),
                        recovered_source_expr.clone(),
                        preserve_stable_input_slot,
                        preserve_explicit_call_expr,
                    )
                    .unwrap_or(expr);
                self.finalize_authoritative_imported_call_arg_expr(
                    expr,
                    preserve_stable_input_slot,
                    preserve_explicit_call_expr,
                    allow_string_like_resolution,
                )
            }
            analysis::SemanticCallArg::StringAddr(addr) => self
                .lookup_string(addr)
                .map(|s| CExpr::StringLit(s.clone()))
                .or_else(|| {
                    self.lookup_symbol(addr)
                        .map(|name| CExpr::Var(name.clone()))
                })
                .unwrap_or(CExpr::UIntLit(addr)),
            analysis::SemanticCallArg::FallbackExpr(expr) => self.normalize_imported_call_arg_expr(
                recovered_source_expr
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
            ),
        }
    }

    fn render_authoritative_source_args_for_call(&self, source_call: (u64, usize)) -> Vec<CExpr> {
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
        let source_var_name = binding.source_var_name.as_deref()?;
        if let Some(owner) = self.stable_owned_call_result_expr_for_name(source_var_name, true) {
            return Some(owner);
        }
        let mut best = None;

        let mut semantic_visited = HashSet::new();
        best = self.choose_preferred_visible_expr(
            best,
            self.render_semantic_value_by_name(source_var_name, 0, &mut semantic_visited),
        );

        if let Some(raw) = self.lookup_definition_raw(source_var_name) {
            let mut imported_visited = HashSet::new();
            let resolved = self.resolve_imported_call_arg_expr(&raw, 0, &mut imported_visited);
            best = self.choose_preferred_visible_expr(best, Some(resolved));
        }

        if let Some(visible_def) = self.lookup_definition(source_var_name) {
            let mut imported_visited = HashSet::new();
            let resolved =
                self.resolve_imported_call_arg_expr(&visible_def, 0, &mut imported_visited);
            best = self.choose_preferred_visible_expr(best, Some(resolved));
        }

        best =
            self.choose_preferred_visible_expr(best, self.best_visible_definition(source_var_name));

        let recovered = best?;
        let rewritten = self.rewrite_stack_expr(recovered.clone());
        let best = self
            .choose_preferred_visible_expr(Some(recovered), Some(rewritten.clone()))
            .unwrap_or(rewritten);
        (!self.call_arg_contains_transient_name(&best, 0)
            && !self.call_arg_contains_stack_placeholder(&best, 0))
        .then_some(best)
    }

    fn repair_imported_result_source_sibling_args(
        &self,
        raw_args: &[analysis::CallArgBinding],
        rendered_args: &mut Vec<CExpr>,
    ) {
        let Some(format_string) = rendered_args.first().and_then(|expr| match expr {
            CExpr::StringLit(text) => Some(text.as_str()),
            _ => None,
        }) else {
            return;
        };
        let Some(result_binding) = raw_args.last() else {
            return;
        };
        let Some((source_block_addr, source_op_idx)) = result_binding.source_call else {
            return;
        };
        if result_binding.role != analysis::CallArgRole::Result || rendered_args.len() < 2 {
            return;
        }

        let placeholder_count = count_printf_placeholders(format_string);
        if placeholder_count == 0 {
            return;
        }

        let final_result_idx = rendered_args.len().saturating_sub(1);
        let needs_repair = rendered_args.len() > placeholder_count + 1
            || rendered_args[1..final_result_idx]
                .iter()
                .enumerate()
                .any(|(idx, expr)| {
                    let rendered_idx = idx + 1;
                    rendered_args
                        .get(rendered_idx.saturating_sub(1))
                        .is_some_and(|previous| *previous == *expr)
                        || self.call_arg_contains_transient_name(expr, 0)
                        || self.call_arg_contains_stack_placeholder(expr, 0)
                        || matches!(expr, CExpr::Call { .. })
                });
        if !needs_repair {
            let sibling_inputs = rendered_args[1..final_result_idx].to_vec();
            if let Some(CExpr::Call { func, args }) = rendered_args.get(final_result_idx).cloned()
                && args.len() == sibling_inputs.len()
                && !sibling_inputs.is_empty()
                && args != sibling_inputs
            {
                rendered_args[final_result_idx] = CExpr::call(*func, sibling_inputs);
            }
            return;
        }

        let source_args =
            self.render_authoritative_source_args_for_call((source_block_addr, source_op_idx));

        let expected_input_count = source_args.len();
        if source_args.is_empty()
            || rendered_args.len() < expected_input_count + 2
            || placeholder_count != expected_input_count + 1
        {
            return;
        }

        if rendered_args.len() > expected_input_count + 2 {
            let final_result_idx = rendered_args.len().saturating_sub(1);
            rendered_args.drain(1 + expected_input_count..final_result_idx);
        }

        let final_result_idx = rendered_args.len().saturating_sub(1);
        let current_siblings = rendered_args[1..final_result_idx].to_vec();
        let final_result_disagrees = rendered_args
            .get(final_result_idx)
            .and_then(|expr| match expr {
                CExpr::Call { args, .. } => Some(args.as_slice() != current_siblings.as_slice()),
                _ => None,
            })
            .unwrap_or(false);
        let should_sync_all_siblings = current_siblings != source_args && final_result_disagrees;

        for (idx, source_arg) in source_args.into_iter().enumerate() {
            let target_idx = idx + 1;
            if target_idx >= rendered_args.len().saturating_sub(1) {
                break;
            }
            let should_replace = should_sync_all_siblings
                || rendered_args.get(target_idx - 1).is_some_and(|previous| {
                    rendered_args[target_idx] == *previous
                        && rendered_args[target_idx] != source_arg
                })
                || self.call_arg_contains_transient_name(&rendered_args[target_idx], 0)
                || self.call_arg_contains_stack_placeholder(&rendered_args[target_idx], 0);
            let should_replace = should_replace
                || (self.is_direct_constish_visible_expr(&rendered_args[target_idx], 0)
                    && self.is_preservable_named_stack_slot_expr(&source_arg))
                || (matches!(rendered_args[target_idx], CExpr::Call { .. })
                    && !matches!(source_arg, CExpr::Call { .. }));
            if should_replace {
                rendered_args[target_idx] = source_arg;
            }
        }

        let final_result_idx = rendered_args.len().saturating_sub(1);
        let sibling_inputs = rendered_args[1..final_result_idx].to_vec();
        if let Some(CExpr::Call { func, args }) = rendered_args.get(final_result_idx).cloned()
            && args.len() == sibling_inputs.len()
            && !sibling_inputs.is_empty()
        {
            rendered_args[final_result_idx] = CExpr::call(*func, sibling_inputs);
        }
    }

    pub(super) fn printf_literal_variadic_arity(
        &self,
        callee: &CExpr,
        rendered_args: &[CExpr],
    ) -> Option<usize> {
        let callee_name = Self::extract_callee_name(callee)?;
        if normalize_callee_name(callee_name) != "printf" {
            return None;
        }
        let format_string = match rendered_args.first()? {
            CExpr::StringLit(text) => text,
            _ => return None,
        };
        Some(1 + count_printf_placeholders(format_string))
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

    fn normalize_imported_call_arg_expr(
        &self,
        expr: CExpr,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
        allow_string_like_resolution: bool,
    ) -> CExpr {
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
            return rewritten;
        }
        let rewritten_best = self.rewrite_stack_expr(best.clone());
        self.choose_preferred_imported_call_arg_expr(
            Some(best.clone()),
            Some(rewritten_best),
            preserve_stable_input_slot,
            preserve_explicit_call_expr,
        )
        .unwrap_or(best)
    }

    fn finalize_authoritative_imported_call_arg_expr(
        &self,
        expr: CExpr,
        preserve_stable_input_slot: bool,
        preserve_explicit_call_expr: bool,
        allow_string_like_resolution: bool,
    ) -> CExpr {
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
            return rewritten;
        }
        self.rewrite_stack_expr(best)
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
