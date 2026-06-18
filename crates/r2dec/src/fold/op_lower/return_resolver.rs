use super::*;
use crate::analysis::utils::{is_temporary_or_constant_name, ssa_render_base_name};

impl<'a> FoldingContext<'a> {
    fn typed_integer_literal_expr_in_context(
        &self,
        value: u64,
        context: VisibleExprContext,
    ) -> CExpr {
        if matches!(context, VisibleExprContext::ScalarReturn)
            && let Some((is_signed, bits)) = self.function_return_int_meta()
            && bits > 0
            && bits <= 64
        {
            let mask = if bits == 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            };
            let truncated = value & mask;
            if is_signed {
                let sign_bit = 1u64 << (bits - 1);
                if truncated & sign_bit != 0 {
                    return CExpr::IntLit((truncated | (!mask)) as i64);
                }
                return CExpr::IntLit(truncated as i64);
            }
            return if bits == 64 || truncated > 0x7fff_ffff {
                CExpr::UIntLit(truncated)
            } else {
                CExpr::IntLit(truncated as i64)
            };
        }

        if value > 0x7fffffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        }
    }

    fn rewrite_typed_return_literal_expr(&self, expr: CExpr, context: VisibleExprContext) -> CExpr {
        match expr {
            CExpr::UIntLit(value) => self.typed_integer_literal_expr_in_context(value, context),
            CExpr::IntLit(value) if value >= 0 => {
                self.typed_integer_literal_expr_in_context(value as u64, context)
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(
                self.rewrite_typed_return_literal_expr(*inner, context),
            )),
            CExpr::Cast { ty, expr: inner } => CExpr::Cast {
                ty,
                expr: Box::new(self.rewrite_typed_return_literal_expr(*inner, context)),
            },
            other => other,
        }
    }

    pub(super) fn expr_is_structured_memory_candidate(expr: &CExpr) -> bool {
        match expr {
            CExpr::Member { .. } | CExpr::PtrMember { .. } | CExpr::Subscript { .. } => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_structured_memory_candidate(inner)
            }
            _ => false,
        }
    }

    pub(super) fn expr_is_scalar_memory_candidate(expr: &CExpr) -> bool {
        match expr {
            CExpr::Deref(_)
            | CExpr::Subscript { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. } => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_scalar_memory_candidate(inner)
            }
            _ => false,
        }
    }

    fn refine_low_signal_semantic_candidate(&self, name: &str, candidate: CExpr) -> CExpr {
        if self.is_low_signal_visible_name(name)
            && matches!(candidate, CExpr::Var(_))
            && let Some(deref) = self.semantic_deref_candidate_for_name(name)
            && deref != candidate
        {
            return deref;
        }
        candidate
    }

    fn semanticized_raw_definition_candidate_in_context(
        &self,
        name: &str,
        context: VisibleExprContext,
    ) -> Option<CExpr> {
        let raw = self.lookup_definition_raw(name)?;
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&raw, 0, &mut semantic_visited);
        if (Self::expr_is_scalar_memory_candidate(&raw)
            || Self::expr_is_structured_memory_candidate(&raw))
            && !Self::expr_is_scalar_memory_candidate(&semanticized)
            && !Self::expr_is_structured_memory_candidate(&semanticized)
        {
            return Some(raw);
        }
        self.choose_preferred_visible_expr_in_context(Some(raw), Some(semanticized), context)
    }

    fn return_context_for_slot_offset(&self, slot_offset: i64) -> VisibleExprContext {
        self.stack_slots()
            .find(|slot| slot.offset == slot_offset && slot.is_scalar_return_carrier())
            .map(|_| VisibleExprContext::ScalarReturn)
            .unwrap_or(VisibleExprContext::Generic)
    }

    fn current_return_context(&self) -> VisibleExprContext {
        if self
            .state
            .return_stack_slots
            .iter()
            .copied()
            .any(|slot_offset| {
                self.return_context_for_slot_offset(slot_offset) == VisibleExprContext::ScalarReturn
            })
            || self.function_return_int_bits().is_some()
        {
            VisibleExprContext::ScalarReturn
        } else {
            VisibleExprContext::Generic
        }
    }

    fn return_context_for_name(&self, name: &str) -> VisibleExprContext {
        if self
            .stack_slot_provenance_for_name(name)
            .is_some_and(|slot| slot.is_scalar_return_carrier())
        {
            return VisibleExprContext::ScalarReturn;
        }

        let lower = name.to_ascii_lowercase();
        if self.inputs.arch.is_return_register_name(&lower) {
            return self.current_return_context();
        }

        self.current_return_context()
    }

    fn return_context_for_expr(&self, expr: &CExpr) -> VisibleExprContext {
        match expr {
            CExpr::Var(name) => self.return_context_for_name(name),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.return_context_for_expr(inner)
            }
            _ => self.current_return_context(),
        }
    }

    fn return_context_for_candidates(
        &self,
        current: Option<&CExpr>,
        candidate: Option<&CExpr>,
    ) -> VisibleExprContext {
        if current.is_some_and(|expr| {
            self.return_context_for_expr(expr) == VisibleExprContext::ScalarReturn
        }) || candidate.is_some_and(|expr| {
            self.return_context_for_expr(expr) == VisibleExprContext::ScalarReturn
        }) {
            VisibleExprContext::ScalarReturn
        } else {
            self.current_return_context()
        }
    }

    fn expr_is_bad_return_candidate_in_context(
        &self,
        expr: &CExpr,
        context: VisibleExprContext,
    ) -> bool {
        self.expr_contains_generic_stack_alias(expr)
            || self.is_uninitialized_return_reg(expr)
            || self.expr_is_transient_return_artifact(expr)
            || (matches!(context, VisibleExprContext::ScalarReturn)
                && self.expr_is_address_artifact_in_scalar_context(expr))
    }

    pub(crate) fn expr_contains_generic_stack_alias(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => is_generic_stack_placeholder_alias(name),
            CExpr::Paren(inner) => self.expr_contains_generic_stack_alias(inner),
            CExpr::Cast { expr: inner, .. } => self.expr_contains_generic_stack_alias(inner),
            CExpr::Unary { operand, .. } => self.expr_contains_generic_stack_alias(operand),
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_generic_stack_alias(left)
                    || self.expr_contains_generic_stack_alias(right)
            }
            CExpr::Deref(inner) | CExpr::AddrOf(inner) => {
                self.expr_contains_generic_stack_alias(inner)
            }
            CExpr::Subscript { base, index } => {
                self.expr_contains_generic_stack_alias(base)
                    || self.expr_contains_generic_stack_alias(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_generic_stack_alias(base)
            }
            CExpr::Call { func, args } => {
                self.expr_contains_generic_stack_alias(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_contains_generic_stack_alias(arg))
            }
            _ => false,
        }
    }

    fn predicate_return_candidate(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return None;
        }

        match expr {
            CExpr::Var(name) => {
                if self.is_transient_visible_name(name) || self.is_low_signal_visible_name(name) {
                    return None;
                }
                if !visited.insert(name.clone()) {
                    return None;
                }

                let candidate = self
                    .lookup_predicate_expr(name)
                    .map(|pred| self.simplify_condition_expr(pred))
                    .or_else(|| {
                        self.lookup_definition_raw(name).and_then(|def| {
                            self.predicate_return_candidate(&def, depth + 1, visited)
                                .or_else(|| {
                                    self.is_assignment_predicate_expr(&def)
                                        .then(|| self.simplify_condition_expr(def))
                                })
                        })
                    });

                visited.remove(name);
                candidate
            }
            CExpr::Paren(inner) => self
                .predicate_return_candidate(inner, depth + 1, visited)
                .map(|resolved| CExpr::Paren(Box::new(resolved))),
            CExpr::Cast { ty, expr: inner } => self
                .predicate_return_candidate(inner, depth + 1, visited)
                .map(|resolved| CExpr::cast(ty.clone(), resolved)),
            _ => self
                .is_assignment_predicate_expr(expr)
                .then(|| self.simplify_condition_expr(expr.clone())),
        }
    }

    fn semantic_return_candidate_for_name(&self, name: &str) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Return, name) {
            return None;
        }
        let context = self.return_context_for_name(name);
        let lower = name.to_ascii_lowercase();
        let mut best = if self.inputs.arch.is_return_register_name(&lower)
            && let Some(block_addr) = self.current_block_addr.get()
        {
            self.merged_return_candidate_for_current_block(block_addr)
        } else {
            None
        };

        if let Some(candidate) =
            self.scalar_context_root_candidate_for_name(name, VisibleExprContext::ScalarReturn)
        {
            best = self.preferred_return_candidate_in_context(best, Some(candidate), context);
        }

        if let Some(candidate) = self.scalar_context_root_candidate_for_name(name, context) {
            best = self.preferred_return_candidate_in_context(best, Some(candidate), context);
        }

        let merged = self
            .stack_slot_provenance_for_name(name)
            .filter(|slot| self.state.return_stack_slots.contains(&slot.offset))
            .and_then(|slot| {
                self.current_block_addr.get().and_then(|block_addr| {
                    self.merged_return_candidate_for_block_slot(block_addr, slot.offset)
                })
            });
        best = self.preferred_return_candidate_in_context(best, merged, context);

        if let Some(candidate) = self.stable_owned_call_result_expr_for_name(name, true) {
            best = self.preferred_return_candidate_in_context(best, Some(candidate), context);
        }

        let mut semantic_visited = HashSet::new();
        let candidate = self.preferred_return_candidate_in_context(
            best,
            self.render_semantic_value_by_name(name, 0, &mut semantic_visited)
                .map(|candidate| self.refine_low_signal_semantic_candidate(name, candidate)),
            context,
        );
        self.leave_resolution_guard(ResolutionPhase::Return, name);
        candidate
    }

    pub(crate) fn resolve_return_candidate(&self, expr: &CExpr) -> CExpr {
        self.resolve_return_candidate_in_context(expr, self.return_context_for_expr(expr))
    }

    pub(crate) fn certified_raw_carrier_definition(&self, name: &str) -> Option<CExpr> {
        let mut candidates = vec![name.to_string()];
        if let Some((base, version)) = name.rsplit_once('_')
            && !base.is_empty()
            && version.bytes().all(|byte| byte.is_ascii_digit())
        {
            candidates.push(format!("{}_{}", base.to_ascii_uppercase(), version));
        }
        candidates.into_iter().find_map(|candidate| {
            let context = self.return_context_for_name(&candidate);
            self.semanticized_raw_definition_candidate_in_context(&candidate, context)
                .or_else(|| self.lookup_definition(&candidate))
                .or_else(|| self.best_visible_definition_in_context(&candidate, context))
                .map(|expr| self.resolve_return_candidate_in_context(&expr, context))
        })
    }

    fn resolve_return_candidate_in_context(
        &self,
        expr: &CExpr,
        context: VisibleExprContext,
    ) -> CExpr {
        let mut best = expr.clone();
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(expr, 0, &mut semantic_visited);
        if self.prefers_visible_expr_in_context(&best, &semanticized, context) {
            best = semanticized;
        }
        let mut has_semantic_root = false;
        if let CExpr::Var(name) = expr {
            if self
                .materialized_call_result_source_for_visible_name(name)
                .is_some()
            {
                return expr.clone();
            }
            if let Some(candidate) = self.semantic_deref_candidate_for_name(name) {
                let should_promote = if matches!(context, VisibleExprContext::Generic) {
                    Self::expr_is_structured_memory_candidate(&candidate)
                        && !Self::expr_is_structured_memory_candidate(&best)
                } else if matches!(context, VisibleExprContext::ScalarReturn) {
                    Self::expr_is_scalar_memory_candidate(&candidate)
                        && !self.expr_is_address_artifact_in_scalar_context(&candidate)
                } else {
                    false
                };
                if should_promote
                    && self.prefers_visible_expr_in_context(&best, &candidate, context)
                {
                    best = candidate;
                }
            }
            if let Some(candidate) = self
                .scalar_context_root_candidate_for_name(name, VisibleExprContext::ScalarReturn)
                .or_else(|| self.scalar_context_root_candidate_for_name(name, context))
                && self.prefers_visible_expr_in_context(&best, &candidate, context)
            {
                best = candidate;
            }
            if let Some(semantic) = self.semantic_return_candidate_for_name(name) {
                has_semantic_root = true;
                if self.prefers_visible_expr_in_context(&best, &semantic, context) {
                    best = semantic;
                }
            }
            if let Some(candidate) =
                self.semanticized_raw_definition_candidate_in_context(name, context)
                && self.prefers_visible_expr_in_context(&best, &candidate, context)
            {
                best = candidate;
            }
        }
        if !has_semantic_root {
            let mut visited = HashSet::new();
            if let Some(predicate) = self.predicate_return_candidate(expr, 0, &mut visited)
                && self.prefers_visible_expr_in_context(&best, &predicate, context)
            {
                best = predicate;
            }

            visited.clear();
            if let Some(resolved) = self.resolve_return_expr_from_defs(expr, 0, &mut visited)
                && self.prefers_visible_expr_in_context(&best, &resolved, context)
            {
                best = resolved;
            }

            if let CExpr::Var(name) = expr
                && let Some(def) = self.lookup_definition(name)
                && self.prefers_visible_expr_in_context(&best, &def, context)
            {
                best = def;
            }

            if let CExpr::Var(name) = expr
                && let Some(def) = self.best_visible_definition_in_context(name, context)
                && self.prefers_visible_expr_in_context(&best, &def, context)
            {
                best = def;
            }
        }

        best
    }

    pub(super) fn preferred_return_candidate(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        let context = self.return_context_for_candidates(current.as_ref(), candidate.as_ref());
        self.preferred_return_candidate_in_context(current, candidate, context)
    }

    fn preferred_return_candidate_in_context(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        context: VisibleExprContext,
    ) -> Option<CExpr> {
        match (current, candidate) {
            (None, other) => other,
            (some @ Some(_), None) => some,
            (Some(current_expr), Some(candidate_expr)) => {
                let current_expr = self.resolve_return_candidate_in_context(&current_expr, context);
                let candidate_expr =
                    self.resolve_return_candidate_in_context(&candidate_expr, context);
                let current_bad =
                    self.expr_is_bad_return_candidate_in_context(&current_expr, context);
                let candidate_bad =
                    self.expr_is_bad_return_candidate_in_context(&candidate_expr, context);
                if current_bad && !candidate_bad {
                    return Some(candidate_expr);
                }
                if candidate_bad && !current_bad {
                    return Some(current_expr);
                }
                self.choose_preferred_visible_expr_in_context(
                    Some(current_expr),
                    Some(candidate_expr),
                    context,
                )
            }
        }
    }

    pub(crate) fn merged_return_candidate_for_block_slot(
        &self,
        block_addr: u64,
        slot_offset: i64,
    ) -> Option<CExpr> {
        let mut best = None;
        let context = self.return_context_for_slot_offset(slot_offset);
        for summary in self.frame_slot_merges_map().values() {
            if summary.slot_offset != slot_offset {
                continue;
            }
            let Some(value) = summary.incoming.get(&block_addr) else {
                continue;
            };
            let mut visited = HashSet::new();
            let rendered = self
                .render_semantic_value(value, 0, &mut visited)
                .map(|expr| self.resolve_return_candidate_in_context(&expr, context));
            best = self.preferred_return_candidate_in_context(best, rendered, context);
        }
        best
    }

    fn merged_return_candidate_for_current_block(&self, block_addr: u64) -> Option<CExpr> {
        let mut best = None;
        for slot_offset in &self.state.return_stack_slots {
            best = self.preferred_return_candidate(
                best,
                self.merged_return_candidate_for_block_slot(block_addr, *slot_offset),
            );
        }
        best
    }

    pub(crate) fn merged_return_register_candidate_for_block(
        &self,
        block_addr: u64,
    ) -> Option<CExpr> {
        let func = self
            .inputs
            .prepared_ssa
            .map(|prepared| prepared.function())?;
        let block = func.get_block(block_addr)?;
        let mut best = None;

        for phi in &block.phis {
            if !self
                .inputs
                .arch
                .is_return_register_name(&phi.dst.name.to_ascii_lowercase())
            {
                continue;
            }

            let phi_name = phi.dst.display_name();
            let mut visited = HashSet::new();
            let candidate = self
                .resolve_expr_from_phi_sources(&phi_name, 0, &mut visited, false)
                .or_else(|| self.best_visible_definition(&phi_name));
            best = self.preferred_return_candidate(best, candidate);
        }

        best
    }

    pub(crate) fn merged_return_register_candidate_for_block_predecessor_with_proof(
        &self,
        block_addr: u64,
        pred_addr: u64,
    ) -> Option<(CExpr, u64, usize, r2ssa::ValueId)> {
        let func = self
            .inputs
            .prepared_ssa
            .map(|prepared| prepared.function())?;
        let prepared = self.inputs.prepared_ssa?;
        let block = func.get_block(block_addr)?;
        let mut best = None;

        for phi in &block.phis {
            if !self
                .inputs
                .arch
                .is_return_register_name(&phi.dst.name.to_ascii_lowercase())
            {
                continue;
            }

            for (source_pred, source) in &phi.sources {
                if *source_pred != pred_addr {
                    continue;
                }
                let candidate =
                    self.return_register_candidate_for_phi_source_in_predecessor(pred_addr, source);
                let Some(expr) = candidate else {
                    continue;
                };
                let Some(value) = self.prepared_value_id_for_var(source) else {
                    continue;
                };
                let Some(cert) = prepared
                    .certificates()
                    .returns
                    .iter()
                    .find(|cert| cert.block_addr == pred_addr && cert.value == value)
                else {
                    continue;
                };
                let candidate = Some((expr, cert.block_addr, cert.op_index, cert.value));
                best = match (best, candidate) {
                    (None, next) => next,
                    (Some(current), None) => Some(current),
                    (
                        Some((current_expr, current_block, current_op, current_value)),
                        Some((next_expr, next_block, next_op, next_value)),
                    ) => {
                        let preferred = self.preferred_return_candidate(
                            Some(current_expr.clone()),
                            Some(next_expr.clone()),
                        );
                        if preferred.as_ref() == Some(&next_expr) {
                            Some((next_expr, next_block, next_op, next_value))
                        } else {
                            Some((current_expr, current_block, current_op, current_value))
                        }
                    }
                };
            }
        }

        best
    }

    pub(crate) fn predecessor_return_register_candidate_with_proof(
        &self,
        pred_addr: u64,
    ) -> Option<(CExpr, u64, usize, r2ssa::ValueId)> {
        let prepared = self.inputs.prepared_ssa?;
        let cert = prepared
            .certificates()
            .returns
            .iter()
            .filter(|cert| cert.block_addr == pred_addr)
            .max_by_key(|cert| cert.op_index)?;
        let source = prepared.value_var(cert.value)?;
        let expr = self
            .return_register_candidate_from_predecessor_definition(pred_addr, source)
            .or_else(|| self.return_register_candidate_for_phi_source(source))?;
        Some((expr, cert.block_addr, cert.op_index, cert.value))
    }

    fn return_register_candidate_for_phi_source_in_predecessor(
        &self,
        pred_addr: u64,
        source: &SSAVar,
    ) -> Option<CExpr> {
        self.return_register_candidate_for_phi_source(source)
            .or_else(|| {
                self.return_register_candidate_from_predecessor_definition(pred_addr, source)
            })
    }

    fn return_register_candidate_from_predecessor_definition(
        &self,
        pred_addr: u64,
        source: &SSAVar,
    ) -> Option<CExpr> {
        let func = self.inputs.prepared_ssa?.function();
        let block = func.get_block(pred_addr)?;
        let (_, op) = block
            .ops
            .iter()
            .enumerate()
            .find(|(_, op)| op.dst().is_some_and(|dst| dst == source))?;
        let candidate = match op {
            SSAOp::Copy { src, .. } => self.get_return_expr(src),
            SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src } => {
                self.tracked_return_cast_expr(dst, src, self.tracked_return_source_expr(src))
            }
            _ => {
                let mut visited = HashSet::new();
                let raw = self.op_to_expr(op);
                let expanded = self.expand_return_expr(&raw, 0, &mut visited);
                let mut semantic_visited = HashSet::new();
                let semanticized =
                    self.semanticize_visible_expr(&expanded, 0, &mut semantic_visited);
                if self.is_predicate_like_expr(&semanticized) {
                    self.simplify_condition_expr(semanticized)
                } else {
                    semanticized
                }
            }
        };
        let normalized = self.normalize_final_return_candidate(candidate.clone());
        let sanitized = self.sanitize_final_return_expr(normalized, candidate);
        (!self
            .expr_is_bad_return_candidate_in_context(&sanitized, VisibleExprContext::ScalarReturn))
        .then_some(sanitized)
    }

    fn return_register_candidate_for_phi_source(&self, source: &SSAVar) -> Option<CExpr> {
        let source_name = source.display_name();
        let mut visited = HashSet::new();
        let candidate = self
            .render_semantic_value_by_name(&source_name, 0, &mut visited)
            .or_else(|| {
                self.lookup_definition_raw_with_depth(&source_name, 0, &mut visited)
                    .map(|expr| self.semanticize_visible_expr(&expr, 0, &mut visited))
            })
            .or_else(|| {
                self.render_value_ref(&analysis::ValueRef::from(source.clone()), 0, &mut visited)
            })
            .or_else(|| self.lookup_definition_with_depth(&source_name, 0, &mut visited))
            .or_else(|| self.best_visible_definition_with_depth(&source_name, 0, &mut visited))
            .or_else(|| Some(self.tracked_return_source_expr(source)));

        candidate
            .map(|expr| self.resolve_return_candidate(&expr))
            .filter(|expr| !self.expr_is_transient_return_artifact(expr))
            .map(|expr| {
                let normalized = self.normalize_final_return_candidate(expr.clone());
                self.sanitize_final_return_expr(normalized, expr)
            })
            .filter(|expr| {
                !self
                    .expr_is_bad_return_candidate_in_context(expr, VisibleExprContext::ScalarReturn)
            })
    }

    pub(super) fn expr_is_transient_return_artifact(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                self.is_transient_visible_name(name) || self.is_low_signal_visible_name(name)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.expr_is_transient_return_artifact(inner)
            }
            _ => false,
        }
    }

    pub(super) fn semantic_deref_candidate_for_name(&self, name: &str) -> Option<CExpr> {
        let mut visited = HashSet::new();
        self.render_authoritative_memory_access_by_name(name, 0, 0, &mut visited)
            .or_else(|| {
                self.find_ssa_name_for_rendered_alias(name)
                    .and_then(|ssa_name| {
                        (ssa_name != name).then(|| {
                            let mut alias_visited = HashSet::new();
                            self.render_authoritative_memory_access_by_name(
                                &ssa_name,
                                0,
                                0,
                                &mut alias_visited,
                            )
                        })?
                    })
            })
    }

    fn should_inline_in_return(&self, var_name: &str, depth: u32) -> bool {
        if depth > MAX_RETURN_INLINE_DEPTH {
            return false;
        }

        let ssa_name = self
            .find_ssa_name_for_rendered_alias(var_name)
            .filter(|ssa_name| ssa_name != var_name);
        let semantic_name = ssa_name.as_deref().unwrap_or(var_name);
        if is_temporary_or_constant_name(var_name) || is_temporary_or_constant_name(semantic_name) {
            return true;
        }

        let lower = var_name.to_lowercase();
        let semantic_lower = semantic_name.to_lowercase();
        if self.inputs.arch.is_return_register_name(&lower) {
            return true;
        }
        if self.inputs.arch.is_return_register_name(&semantic_lower) {
            return true;
        }

        let is_pinned = self.pinned_set().contains(var_name)
            || self.pinned_set().contains(&lower)
            || self.pinned_set().contains(semantic_name)
            || self.pinned_set().contains(&semantic_lower)
            || var_name
                .rsplit_once('_')
                .map(|(base, ver)| {
                    self.pinned_set()
                        .contains(&format!("{}_{}", base.to_lowercase(), ver))
                        || self
                            .pinned_set()
                            .contains(&format!("{}_{}", base.to_uppercase(), ver))
                })
                .unwrap_or(false);
        if is_pinned {
            return false;
        }

        let use_count = self
            .use_counts_map()
            .get(var_name)
            .copied()
            .or_else(|| self.use_counts_map().get(&lower).copied())
            .or_else(|| {
                var_name.rsplit_once('_').and_then(|(base, ver)| {
                    self.use_counts_map()
                        .get(&format!("{}_{}", base.to_lowercase(), ver))
                        .copied()
                        .or_else(|| {
                            self.use_counts_map()
                                .get(&format!("{}_{}", base.to_uppercase(), ver))
                                .copied()
                        })
                })
            })
            .or_else(|| self.use_counts_map().get(semantic_name).copied())
            .or_else(|| self.use_counts_map().get(&semantic_lower).copied())
            .unwrap_or(0);
        if use_count == 0 || use_count > 3 {
            return false;
        }

        self.lookup_definition(semantic_name)
            .map(|expr| self.is_return_inline_candidate(&expr, 0))
            .unwrap_or(false)
    }

    fn is_return_inline_candidate(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > MAX_RETURN_INLINE_CANDIDATE_DEPTH {
            return false;
        }

        match expr {
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_) => true,
            CExpr::Var(_) => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_return_inline_candidate(inner, depth + 1)
            }
            CExpr::Unary { operand, .. } => self.is_return_inline_candidate(operand, depth + 1),
            CExpr::Binary { op, left, right } => {
                matches!(
                    op,
                    BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Mod
                        | BinaryOp::Shl
                        | BinaryOp::Shr
                        | BinaryOp::BitAnd
                        | BinaryOp::BitOr
                        | BinaryOp::BitXor
                        | BinaryOp::And
                        | BinaryOp::Or
                        | BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::Lt
                        | BinaryOp::Le
                        | BinaryOp::Gt
                        | BinaryOp::Ge
                ) && self.is_return_inline_candidate(left, depth + 1)
                    && self.is_return_inline_candidate(right, depth + 1)
            }
            CExpr::Deref(inner) => self
                .resolve_stack_alias_from_addr_expr(inner, 0)
                .filter(|alias| !is_generic_stack_placeholder_alias(alias))
                .is_some(),
            _ => false,
        }
    }

    pub(crate) fn stack_alias_from_deref_expr(&self, expr: &CExpr) -> Option<String> {
        match expr {
            CExpr::Deref(inner) => self
                .resolve_stack_alias_from_addr_expr(inner, 0)
                .filter(|alias| !is_generic_stack_placeholder_alias(alias)),
            CExpr::Paren(inner) => self.stack_alias_from_deref_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.stack_alias_from_deref_expr(inner),
            _ => None,
        }
    }

    pub(super) fn expand_return_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        self.expand_return_expr_in_context(expr, depth, visited, self.return_context_for_expr(expr))
    }

    fn expand_return_expr_in_context(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
        context: VisibleExprContext,
    ) -> CExpr {
        if depth > MAX_RETURN_EXPR_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => {
                if let Some(val) = parse_const_value(name) {
                    return self.typed_integer_literal_expr_in_context(val, context);
                }
                if let Some(alias) = self.arg_alias_for_rendered_name(name) {
                    return CExpr::Var(alias);
                }
                if self.lookup_predicate_expr(name).is_some() {
                    return self.simplify_condition_expr(CExpr::Var(name.clone()));
                }
                if let Some(candidate) = self
                    .scalar_context_root_candidate_for_name(name, VisibleExprContext::ScalarReturn)
                    .or_else(|| self.scalar_context_root_candidate_for_name(name, context))
                {
                    if !visited.insert(name.clone()) {
                        return candidate;
                    }
                    let resolved =
                        self.expand_return_expr_in_context(&candidate, depth + 1, visited, context);
                    visited.remove(name);
                    return if self.is_predicate_like_expr(&resolved) {
                        self.simplify_condition_expr(resolved)
                    } else {
                        resolved
                    };
                }

                let mut semantic_visited = HashSet::new();
                if let Some(semantic) = self
                    .render_semantic_value_by_name(name, 0, &mut semantic_visited)
                    .map(|candidate| self.refine_low_signal_semantic_candidate(name, candidate))
                    && (self.prefers_visible_expr_in_context(
                        &CExpr::Var(name.clone()),
                        &semantic,
                        context,
                    ) || (self.is_low_signal_visible_name(name)
                        && matches!(
                            semantic,
                            CExpr::Subscript { .. }
                                | CExpr::Member { .. }
                                | CExpr::PtrMember { .. }
                                | CExpr::Deref(_)
                        )))
                {
                    if !visited.insert(name.clone()) {
                        return semantic;
                    }
                    let resolved =
                        self.expand_return_expr_in_context(&semantic, depth + 1, visited, context);
                    visited.remove(name);
                    return if self.is_predicate_like_expr(&resolved) {
                        self.simplify_condition_expr(resolved)
                    } else {
                        resolved
                    };
                }

                if self.is_low_signal_visible_name(name)
                    && let Some(candidate) = self.semantic_deref_candidate_for_name(name)
                    && self.prefers_visible_expr_in_context(
                        &CExpr::Var(name.clone()),
                        &candidate,
                        context,
                    )
                {
                    if !visited.insert(name.clone()) {
                        return candidate;
                    }
                    let resolved =
                        self.expand_return_expr_in_context(&candidate, depth + 1, visited, context);
                    visited.remove(name);
                    return if self.is_predicate_like_expr(&resolved) {
                        self.simplify_condition_expr(resolved)
                    } else {
                        resolved
                    };
                }

                if let Some(candidate) =
                    self.semanticized_raw_definition_candidate_in_context(name, context)
                    && self.prefers_visible_expr_in_context(
                        &CExpr::Var(name.clone()),
                        &candidate,
                        context,
                    )
                {
                    if !visited.insert(name.clone()) {
                        return candidate;
                    }
                    let resolved =
                        self.expand_return_expr_in_context(&candidate, depth + 1, visited, context);
                    visited.remove(name);
                    return if self.is_predicate_like_expr(&resolved) {
                        self.simplify_condition_expr(resolved)
                    } else {
                        resolved
                    };
                }

                if !self.should_inline_in_return(name, depth) || !visited.insert(name.clone()) {
                    return CExpr::Var(name.clone());
                }

                let resolved = self
                    .choose_preferred_visible_expr_in_context(
                        self.lookup_definition(name),
                        self.choose_preferred_visible_expr_in_context(
                            self.semanticized_raw_definition_candidate_in_context(name, context),
                            self.best_visible_definition_in_context(name, context),
                            context,
                        ),
                        context,
                    )
                    .map(|inner| {
                        self.expand_return_expr_in_context(&inner, depth + 1, visited, context)
                    })
                    .unwrap_or_else(|| CExpr::Var(name.clone()));

                visited.remove(name);
                if self.is_predicate_like_expr(&resolved) {
                    self.simplify_condition_expr(resolved)
                } else {
                    resolved
                }
            }
            CExpr::Deref(inner) => {
                if let CExpr::Var(name) = inner.as_ref()
                    && let Some(candidate) = self.semantic_deref_candidate_for_name(name)
                    && (!matches!(context, VisibleExprContext::ScalarReturn)
                        || !self.expr_is_address_artifact_in_scalar_context(&candidate))
                {
                    return candidate;
                }
                if let Some(stack_var) = self
                    .resolve_stack_alias_from_addr_expr(inner, 0)
                    .filter(|alias| !is_generic_stack_placeholder_alias(alias))
                {
                    CExpr::Var(stack_var)
                } else {
                    let expanded_inner =
                        self.expand_return_expr_in_context(inner, depth + 1, visited, context);
                    let mut semantic_visited = HashSet::new();
                    self.render_memory_access_from_visible_expr(
                        &expanded_inner,
                        0,
                        depth + 1,
                        &mut semantic_visited,
                    )
                    .unwrap_or_else(|| CExpr::Deref(Box::new(expanded_inner)))
                }
            }
            CExpr::Binary { op, left, right } => {
                let rebuilt = CExpr::binary(
                    *op,
                    self.expand_return_expr_in_context(left, depth + 1, visited, context),
                    self.expand_return_expr_in_context(right, depth + 1, visited, context),
                );
                if self.is_predicate_like_expr(&rebuilt) {
                    self.simplify_condition_expr(rebuilt)
                } else {
                    rebuilt
                }
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.expand_return_expr_in_context(
                inner,
                depth + 1,
                visited,
                context,
            ))),
            CExpr::Cast { ty, expr: inner } => {
                let expanded_inner =
                    self.expand_return_expr_in_context(inner, depth + 1, visited, context);
                let simplified_inner = if self.is_predicate_like_expr(&expanded_inner) {
                    self.simplify_condition_expr(expanded_inner)
                } else {
                    expanded_inner
                };
                CExpr::Cast {
                    ty: ty.clone(),
                    expr: Box::new(simplified_inner),
                }
            }
            _ => expr.clone().map_children(&mut |child| {
                self.expand_return_expr_in_context(&child, depth + 1, visited, context)
            }),
        }
    }

    pub(super) fn get_return_expr(&self, var: &SSAVar) -> CExpr {
        if var.is_const() {
            return self.rewrite_typed_return_literal_expr(
                self.const_to_expr(var),
                self.current_return_context(),
            );
        }

        let mut visited = HashSet::new();
        let root_name = var.display_name();
        let context = self.return_context_for_name(&root_name);
        let unresolved = CExpr::Var(self.var_name(var));
        let raw_definition =
            self.semanticized_raw_definition_candidate_in_context(&root_name, context);
        let semantic_root = match (
            self.semantic_return_candidate_for_name(&root_name),
            raw_definition.clone(),
        ) {
            (Some(current), Some(raw))
                if (Self::expr_is_scalar_memory_candidate(&raw)
                    || Self::expr_is_structured_memory_candidate(&raw))
                    && !Self::expr_is_scalar_memory_candidate(&current)
                    && !Self::expr_is_structured_memory_candidate(&current) =>
            {
                Some(raw)
            }
            (current, _) => current,
        };
        let base_root = if let Some(semantic_root) = semantic_root.clone() {
            let best = self
                .preferred_return_candidate_in_context(
                    Some(semantic_root),
                    raw_definition.clone(),
                    context,
                )
                .unwrap_or_else(|| unresolved.clone());
            self.preferred_return_candidate_in_context(
                Some(best),
                Some(unresolved.clone()),
                context,
            )
            .unwrap_or_else(|| unresolved.clone())
        } else {
            let best = self
                .preferred_return_candidate_in_context(
                    self.lookup_definition(&root_name),
                    raw_definition.clone(),
                    context,
                )
                .and_then(|expr| {
                    self.preferred_return_candidate_in_context(
                        Some(expr),
                        self.best_visible_definition_in_context(&root_name, context),
                        context,
                    )
                })
                .or_else(|| self.lookup_definition(&root_name))
                .or_else(|| self.best_visible_definition_in_context(&root_name, context))
                .unwrap_or_else(|| unresolved.clone());
            self.preferred_return_candidate_in_context(
                Some(best),
                Some(unresolved.clone()),
                context,
            )
            .unwrap_or_else(|| unresolved.clone())
        };
        let root = if semantic_root.is_some() {
            base_root
        } else {
            let predicate_root = self.predicate_return_candidate(&unresolved, 0, &mut visited);
            self.preferred_return_candidate_in_context(
                self.choose_preferred_visible_expr_in_context(
                    self.predicate_candidate_for_var(var),
                    predicate_root,
                    context,
                ),
                Some(base_root),
                context,
            )
            .unwrap_or_else(|| unresolved.clone())
        };
        let root = self.resolve_predicate_rhs_for_var(var, root);
        let raw = self.expand_return_expr_in_context(&root, 0, &mut visited, context);
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&raw, 0, &mut semantic_visited);
        let raw = if (Self::expr_is_scalar_memory_candidate(&raw)
            || Self::expr_is_structured_memory_candidate(&raw))
            && !Self::expr_is_scalar_memory_candidate(&semanticized)
            && !Self::expr_is_structured_memory_candidate(&semanticized)
        {
            raw
        } else {
            semanticized
        };
        let simplified = if self.is_predicate_like_expr(&raw) {
            self.simplify_condition_expr(raw)
        } else {
            raw
        };
        let sanitized = self.sanitize_return_expr_in_context(simplified, root, unresolved, context);
        self.rewrite_typed_return_literal_expr(sanitized, context)
    }

    #[cfg(test)]
    pub(crate) fn debug_return_expr_stages(&self, var: &SSAVar) -> (CExpr, CExpr, CExpr) {
        let mut visited = HashSet::new();
        let root_name = var.display_name();
        let context = self.return_context_for_name(&root_name);
        let unresolved = CExpr::Var(self.var_name(var));
        let semantic_root = self.semantic_return_candidate_for_name(&root_name);
        let base_root = if let Some(semantic_root) = semantic_root.clone() {
            let best = self
                .preferred_return_candidate_in_context(
                    Some(semantic_root),
                    self.semanticized_raw_definition_candidate_in_context(&root_name, context),
                    context,
                )
                .unwrap_or_else(|| unresolved.clone());
            self.preferred_return_candidate_in_context(
                Some(best),
                Some(unresolved.clone()),
                context,
            )
            .unwrap_or_else(|| unresolved.clone())
        } else {
            let best = self
                .preferred_return_candidate_in_context(
                    self.lookup_definition(&root_name),
                    self.semanticized_raw_definition_candidate_in_context(&root_name, context),
                    context,
                )
                .and_then(|expr| {
                    self.preferred_return_candidate_in_context(
                        Some(expr),
                        self.best_visible_definition_in_context(&root_name, context),
                        context,
                    )
                })
                .or_else(|| self.lookup_definition(&root_name))
                .or_else(|| self.best_visible_definition_in_context(&root_name, context))
                .unwrap_or_else(|| unresolved.clone());
            self.preferred_return_candidate_in_context(
                Some(best),
                Some(unresolved.clone()),
                context,
            )
            .unwrap_or_else(|| unresolved.clone())
        };
        let root = if semantic_root.is_some() {
            base_root
        } else {
            let predicate_root = self.predicate_return_candidate(&unresolved, 0, &mut visited);
            self.preferred_return_candidate_in_context(
                self.choose_preferred_visible_expr_in_context(
                    self.predicate_candidate_for_var(var),
                    predicate_root,
                    context,
                ),
                Some(base_root),
                context,
            )
            .unwrap_or_else(|| unresolved.clone())
        };
        let root = self.resolve_predicate_rhs_for_var(var, root);
        let raw = self.expand_return_expr_in_context(&root, 0, &mut visited, context);
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&raw, 0, &mut semantic_visited);
        (root, raw, semanticized)
    }

    fn sanitize_return_expr_in_context(
        &self,
        expr: CExpr,
        fallback: CExpr,
        unresolved: CExpr,
        context: VisibleExprContext,
    ) -> CExpr {
        self.preferred_return_candidate_in_context(
            self.preferred_return_candidate_in_context(
                Some(unresolved.clone()),
                Some(fallback),
                context,
            ),
            Some(expr),
            context,
        )
        .unwrap_or(unresolved)
    }

    pub(super) fn sanitize_final_return_expr(&self, expr: CExpr, fallback: CExpr) -> CExpr {
        let context = self.return_context_for_candidates(Some(&expr), Some(&fallback));
        self.preferred_return_candidate_in_context(
            Some(self.resolve_return_candidate_in_context(&fallback, context)),
            Some(self.resolve_return_candidate_in_context(&expr, context)),
            context,
        )
        .map(|expr| {
            let expr = self.rewrite_typed_return_literal_expr(expr, context);
            self.strip_widening_cast_for_function_return(expr)
        })
        .unwrap_or_else(|| CExpr::Var("return".to_string()))
    }

    fn strip_widening_cast_for_function_return(&self, expr: CExpr) -> CExpr {
        let CExpr::Cast { ty, expr: inner } = expr else {
            return expr;
        };
        let Some(return_bits) = self.function_return_int_bits() else {
            return CExpr::Cast { ty, expr: inner };
        };
        let Some(cast_bits) = ty.bits() else {
            return CExpr::Cast { ty, expr: inner };
        };
        if ty.is_integer() && cast_bits > return_bits {
            *inner
        } else {
            CExpr::Cast { ty, expr: inner }
        }
    }

    /// Convert an SSA variable to a C variable name.
    pub fn var_name(&self, var: &SSAVar) -> String {
        if var.is_const() {
            // Return the constant value directly
            let val = parse_const_value(&var.name).unwrap_or(0);
            if val > 0xffff {
                return format!("0x{:x}", val);
            } else {
                return format!("{}", val);
            }
        }

        if let Some(addr) = extract_call_address(&var.name) {
            if let Some(sym) = self.lookup_symbol(addr) {
                return sym.clone();
            }
            if let Some(name) = self.lookup_function(addr) {
                return name.clone();
            }
        }

        // Check if coalescing mapped this SSA name to a merged name
        let display = var.display_name();
        if let Some(alias) = self.var_aliases_map().get(&display) {
            return self
                .canonicalize_stack_name(alias)
                .unwrap_or_else(|| alias.clone());
        }

        if var.version == 0
            && let Some(alias) = self.arg_alias_for_register_name(&var.name)
        {
            return alias;
        }

        let base = ssa_render_base_name(var);

        if var.version > 0 {
            format!("{}_{}", base, var.version)
        } else {
            base
        }
    }

    /// Convert a constant variable to a C expression.
    pub(crate) fn const_to_expr(&self, var: &SSAVar) -> CExpr {
        let val = parse_const_value(&var.name).unwrap_or(0);

        // Only resolve addresses that are plausibly code/data (not small literals)
        if val > 0xff {
            // Check if this is a function address (e.g., for lea rdi, [main])
            if let Some(name) = self.lookup_function(val) {
                return CExpr::Var(name.clone());
            }

            // Check if this is a string address
            if let Some(s) = self.lookup_string(val) {
                return CExpr::StringLit(s.clone());
            }

            // Check if this is a symbol address
            if let Some(s) = self.lookup_symbol(val) {
                return CExpr::Var(s.clone());
            }
        }

        if val > 0x7fffffff {
            CExpr::UIntLit(val)
        } else {
            CExpr::IntLit(val as i64)
        }
    }
}
