use std::collections::HashSet;

use r2ssa::SSAVar;

use super::*;

impl<'a> FoldingContext<'a> {
    fn has_authoritative_memory_semantics(&self, name: &str) -> bool {
        matches!(
            self.lookup_semantic_value(name),
            Some(analysis::SemanticValue::Address(_)) | Some(analysis::SemanticValue::Load { .. })
        )
    }

    pub(super) fn render_authoritative_memory_access_by_name(
        &self,
        name: &str,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Memory, name) {
            return None;
        }

        let semantic = self.render_memory_access_by_name(name, elem_size, depth, visited);
        let result = if semantic.is_some() || self.has_authoritative_memory_semantics(name) {
            semantic
        } else {
            self.lookup_definition(name)
                .and_then(|expr| {
                    self.render_memory_access_from_visible_expr(&expr, elem_size, depth, visited)
                })
                .or_else(|| {
                    self.definitions_map().get(name).and_then(|expr| {
                        self.render_memory_access_from_visible_expr(expr, elem_size, depth, visited)
                    })
                })
        };

        self.leave_resolution_guard(ResolutionPhase::Memory, name);
        result
    }

    pub(super) fn render_canonical_load_expr(
        &self,
        dst: &SSAVar,
        addr: &SSAVar,
        elem_ty: CType,
    ) -> CExpr {
        let pointee_load = dst.size < addr.size;
        let fallback_addr_expr = self
            .lookup_definition(&addr.display_name())
            .or_else(|| self.definitions_map().get(&addr.display_name()).cloned())
            .unwrap_or_else(|| self.get_expr(addr));
        let mut semantic_visited = HashSet::new();
        let mut best = self.render_authoritative_memory_access_by_name(
            &dst.display_name(),
            dst.size,
            0,
            &mut semantic_visited,
        );
        best = self.choose_preferred_visible_expr(
            best,
            self.render_authoritative_memory_access_by_name(
                &addr.display_name(),
                dst.size,
                0,
                &mut semantic_visited,
            ),
        );
        let fallback_rendered = self.render_memory_access_from_visible_expr(
            &fallback_addr_expr,
            dst.size,
            0,
            &mut semantic_visited,
        );
        if let Some(fallback_structured) = fallback_rendered
            .as_ref()
            .filter(|expr| Self::expr_is_structured_memory_candidate(expr))
            .cloned()
            && !best
                .as_ref()
                .is_some_and(Self::expr_is_structured_memory_candidate)
        {
            best = Some(fallback_structured);
        }
        best = self.choose_preferred_visible_expr(best, fallback_rendered);
        best = self
            .choose_preferred_visible_expr(best, self.prepared_named_memory_expr_for_current_op());
        if let Some(expr) = best {
            return expr;
        }

        if pointee_load {
            let ptr_ty = CType::ptr(elem_ty.clone());
            let casted = self.cast_addr_expr_to_ptr_if_needed(addr, self.get_expr(addr), &ptr_ty);
            return CExpr::Deref(Box::new(casted));
        }

        if addr.name.starts_with("ram:")
            && let Some(address) = extract_call_address(&addr.name)
        {
            if let Some(sym) = self.lookup_symbol(address) {
                return CExpr::Var(sym.clone());
            }
            if let Some(name) = self.lookup_function(address) {
                return CExpr::Var(name.clone());
            }
            if let Some(s) = self.lookup_string(address) {
                return CExpr::StringLit(s.clone());
            }
        }

        if dst.size >= addr.size
            && let Some(stack_var) = self.stack_var_for_addr_var(addr)
        {
            return CExpr::Var(stack_var);
        }

        if addr.is_const() {
            let direct = self.get_expr(addr);
            if matches!(direct, CExpr::Var(_) | CExpr::StringLit(_)) {
                return direct;
            }
        }

        if let Some(exact) = self.resolve_literalish_call_arg_expr(&fallback_addr_expr) {
            return exact;
        }

        self.typed_deref_expr(addr, fallback_addr_expr, elem_ty)
    }

    pub(super) fn render_canonical_store_target_expr(
        &self,
        addr: &SSAVar,
        value_size: u32,
        elem_ty: CType,
    ) -> CExpr {
        let fallback_addr_expr = self
            .lookup_definition(&addr.display_name())
            .or_else(|| self.definitions_map().get(&addr.display_name()).cloned())
            .unwrap_or_else(|| self.get_expr(addr));
        let mut semantic_visited = HashSet::new();
        let mut best = self.render_authoritative_memory_access_by_name(
            &addr.display_name(),
            value_size,
            0,
            &mut semantic_visited,
        );
        let fallback_rendered = self.render_memory_access_from_visible_expr(
            &fallback_addr_expr,
            value_size,
            0,
            &mut semantic_visited,
        );
        if let Some(fallback_structured) = fallback_rendered
            .as_ref()
            .filter(|expr| Self::expr_is_structured_memory_candidate(expr))
            .cloned()
            && !best
                .as_ref()
                .is_some_and(Self::expr_is_structured_memory_candidate)
        {
            best = Some(fallback_structured);
        }
        best = self.choose_preferred_visible_expr(best, fallback_rendered);
        best = self.choose_preferred_visible_expr(
            best,
            self.prepared_named_memory_def_expr_for_current_op(),
        );
        if let Some(expr) = best {
            return expr;
        }

        if addr.name.starts_with("ram:")
            && let Some(address) = extract_call_address(&addr.name)
            && let Some(sym) = self.lookup_symbol(address)
        {
            return CExpr::Var(sym.clone());
        }

        if let Some(stack_var) = self.stack_var_for_addr_var(addr) {
            return CExpr::Var(stack_var);
        }

        if addr.is_const() {
            let direct = self.get_expr(addr);
            if matches!(direct, CExpr::Var(_) | CExpr::StringLit(_)) {
                return direct;
            }
        }

        if let Some(exact) = self.resolve_literalish_call_arg_expr(&fallback_addr_expr) {
            return exact;
        }

        self.typed_deref_expr(addr, fallback_addr_expr, elem_ty)
    }

    pub(super) fn render_memory_access_from_visible_expr(
        &self,
        expr: &CExpr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let mut try_render = |candidate: &CExpr, ctx: &FoldingContext<'_>| {
            let canonical = ctx.canonicalize_visible_address_expr(candidate, depth + 1);
            let addr = ctx.normalized_addr_from_visible_expr(&canonical, depth + 1)?;
            ctx.render_access_expr_from_addr(&addr, elem_size, depth + 1, visited)
        };

        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(expr, depth + 1, &mut semantic_visited);
        let preferred = if self.prefers_visible_expr(expr, &semanticized) {
            semanticized
        } else {
            expr.clone()
        };

        try_render(&preferred, self).or_else(|| try_render(expr, self))
    }
}
