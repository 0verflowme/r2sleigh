use std::collections::HashSet;

use r2ssa::SSAVar;

use super::*;

impl<'a> FoldingContext<'a> {
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

    fn byte_indexed_pointer_add_expr(&self, expr: &CExpr) -> Option<CExpr> {
        self.indexed_pointer_add_expr(expr, &CType::u8())
    }

    pub(super) fn indexed_pointer_add_expr(&self, expr: &CExpr, elem_ty: &CType) -> Option<CExpr> {
        let CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } = expr
        else {
            return None;
        };

        for (base, index) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            let normalized_base = self.normalize_pointer_base_expr(base, 0);
            if !(self.looks_like_pointer(&normalized_base)
                || self.is_non_index_pointer_expr(&normalized_base))
            {
                continue;
            }
            if self.looks_like_pointer(index) || self.is_non_index_pointer_expr(index) {
                continue;
            }
            let elem_ty = match self.expr_type_hint(&normalized_base) {
                Some(CType::Pointer(inner)) | Some(CType::Array(inner, _)) => *inner,
                _ => elem_ty.clone(),
            };
            let elem_size = elem_ty
                .bits()
                .map(|bits| bits.div_ceil(8).max(1))
                .unwrap_or(1);
            let Some(index) = self.scaled_index_expr(index, elem_size) else {
                continue;
            };
            let index = self.normalize_index_expr(&index, 0).unwrap_or(index);
            let base_source_ty = self.expr_type_hint(&normalized_base);
            let normalized_base = self.cast_expr_if_needed(
                normalized_base,
                CType::ptr(elem_ty),
                base_source_ty.as_ref(),
            );
            return Some(CExpr::Subscript {
                base: Box::new(normalized_base),
                index: Box::new(index),
            });
        }

        None
    }

    fn scaled_index_expr(&self, expr: &CExpr, elem_size: u32) -> Option<CExpr> {
        if elem_size <= 1 {
            return Some(expr.clone());
        }

        match expr {
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if self.literal_to_i64(right) == Some(i64::from(elem_size)) {
                    return Some((**left).clone());
                }
                if self.literal_to_i64(left) == Some(i64::from(elem_size)) {
                    return Some((**right).clone());
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Shl,
                left,
                right,
            } => {
                let shift = self.literal_to_i64(right)?;
                if !(0..=30).contains(&shift) {
                    return None;
                }
                (1u32.checked_shl(shift as u32)? == elem_size).then(|| (**left).clone())
            }
            _ => None,
        }
    }

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
            self.lookup_definition(name).and_then(|expr| {
                self.render_memory_access_from_visible_expr(&expr, elem_size, depth, visited)
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
            .or_else(|| self.definition_for_name(&addr.display_name()).cloned())
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
            if let CExpr::Deref(inner) = &expr
                && let Some(indexed) = self.indexed_pointer_add_expr(inner, &elem_ty)
            {
                return indexed;
            }
            if !Self::expr_is_scalar_memory_candidate(&expr)
                && !matches!(elem_ty, CType::Pointer(_) | CType::Array(_, _))
                && self.normalized_addr_from_visible_expr(&expr, 0).is_some()
            {
                return self.typed_deref_expr(addr, expr, elem_ty);
            }
            return expr;
        }

        if pointee_load {
            let ptr_ty = CType::ptr(elem_ty.clone());
            let casted = self.cast_addr_expr_to_ptr_if_needed(addr, self.get_expr(addr), &ptr_ty);
            return CExpr::Deref(Box::new(casted));
        }

        if addr.is_memory()
            && let Some(address) = parse_address_from_var_name(&addr.name)
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
            .or_else(|| self.definition_for_name(&addr.display_name()).cloned())
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
        if let Some(expr) = best.filter(Self::expr_is_store_target_candidate) {
            return expr;
        }

        if addr.is_memory()
            && let Some(address) = parse_address_from_var_name(&addr.name)
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

        if value_size == 1
            && let Some(indexed) = self.byte_indexed_pointer_add_expr(&fallback_addr_expr)
        {
            return indexed;
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
        if let Some(rendered) = try_render(&preferred, self).or_else(|| try_render(expr, self)) {
            return Some(rendered);
        }
        let elem_ty = type_from_size(elem_size);
        if let Some(indexed) = self.indexed_pointer_add_expr(&preferred, &elem_ty) {
            return Some(indexed);
        }
        if preferred != *expr
            && let Some(indexed) = self.indexed_pointer_add_expr(expr, &elem_ty)
        {
            return Some(indexed);
        }

        None
    }
}
