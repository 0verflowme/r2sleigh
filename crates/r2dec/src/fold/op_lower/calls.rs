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
            return rendered;
        }

        raw_args
            .into_iter()
            .map(|binding| self.render_call_arg_for_callee(callee, binding))
            .collect()
    }

    fn lookup_known_signature(&self, callee_name: &str) -> Option<&FunctionType> {
        let normalized = normalize_callee_name(callee_name);
        self.inputs.known_function_signatures.get(&normalized)
    }

    fn extract_callee_name(expr: &CExpr) -> Option<&str> {
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

        match (known_arity, registry_arity) {
            (Some(known), Some(registry)) => Some(known.min(registry)),
            (Some(known), None) => Some(known),
            (None, Some(registry)) => Some(registry),
            (None, None) => None,
        }
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
            && let analysis::SemanticCallArg::FallbackExpr(CExpr::Call { func, .. }) =
                binding.arg.clone()
        {
            let mut args = self
                .call_args_map()
                .get(&(block_addr, op_idx))
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .map(|arg| self.render_authoritative_source_call_arg(arg))
                .collect::<Vec<_>>();
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
        match binding.arg {
            analysis::SemanticCallArg::Semantic(value) => {
                let expr = self
                    .render_imported_semantic_arg_value(&value, !allow_string_like_resolution)
                    .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(&value));
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
                expr,
                preserve_stable_input_slot,
                preserve_explicit_call_expr,
                allow_string_like_resolution,
            ),
        }
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

        match binding.arg {
            analysis::SemanticCallArg::Semantic(value) => {
                let expr = self
                    .render_imported_semantic_arg_value(&value, !allow_string_like_resolution)
                    .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(&value));
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
                expr,
                preserve_stable_input_slot,
                preserve_explicit_call_expr,
                allow_string_like_resolution,
            ),
        }
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

        let source_args = self
            .call_args_map()
            .get(&(source_block_addr, source_op_idx))
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .map(|binding| self.render_authoritative_source_call_arg(binding))
            .collect::<Vec<_>>();

        let expected_input_count = source_args.len();
        if source_args.is_empty()
            || rendered_args.len() < expected_input_count + 2
            || count_printf_placeholders(format_string) != expected_input_count + 1
        {
            return;
        }

        if rendered_args.len() > expected_input_count + 2 {
            let final_result_idx = rendered_args.len().saturating_sub(1);
            rendered_args.drain(1 + expected_input_count..final_result_idx);
        }

        for (idx, source_arg) in source_args.into_iter().enumerate() {
            let target_idx = idx + 1;
            if target_idx >= rendered_args.len().saturating_sub(1) {
                break;
            }
            let should_replace = rendered_args.get(target_idx - 1).is_some_and(|previous| {
                rendered_args[target_idx] == *previous && rendered_args[target_idx] != source_arg
            }) || self
                .call_arg_contains_transient_name(&rendered_args[target_idx], 0)
                || self.call_arg_contains_stack_placeholder(&rendered_args[target_idx], 0);
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
        let mut imported_visited = HashSet::new();
        let imported_resolved =
            self.resolve_imported_call_arg_expr(&semanticized, 0, &mut imported_visited);
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

        let best = best.unwrap_or(rewritten);
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
        self.rewrite_stack_expr(best.unwrap_or(rewritten))
    }

    fn imported_input_binding_prefers_pointer_identity(
        &self,
        binding: &analysis::CallArgBinding,
    ) -> bool {
        if binding.role != analysis::CallArgRole::Input {
            return false;
        }

        match &binding.arg {
            analysis::SemanticCallArg::Semantic(analysis::SemanticValue::Load { addr, .. })
            | analysis::SemanticCallArg::Semantic(analysis::SemanticValue::Address(addr)) => {
                matches!(addr.base, analysis::BaseRef::StackSlot(_))
            }
            analysis::SemanticCallArg::FallbackExpr(expr) => {
                self.call_arg_contains_stack_placeholder(expr, 0)
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
