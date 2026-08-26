use r2ssa::{FunctionSSABlock, SSAOp, SSAVar};

use super::MAX_PREDICATE_OPERAND_DEPTH;
use super::context::FoldingContext;
use crate::ast::{BinaryOp, CExpr, UnaryOp};
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CompareContext {
    Eq,
    Ne,
    SignedNegative,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CompareTuple {
    lhs: CExpr,
    rhs: CExpr,
    context: CompareContext,
}

impl<'a> FoldingContext<'a> {
    fn exact_branch_input_expr(&self, block_addr: u64, branch_idx: usize) -> Option<CExpr> {
        match self.planned_input_expr_at(block_addr, branch_idx, 1) {
            Ok(expr) => Some(expr),
            Err(refusal) => {
                self.retain_first_lowering_refusal(refusal);
                None
            }
        }
    }

    pub fn extract_condition_from_block(&self, block: &FunctionSSABlock) -> Option<CExpr> {
        self.certified_branch_condition_from_block(block)
            .map(|(expr, _, _)| expr)
    }

    pub(super) fn certified_branch_condition_from_block(
        &self,
        block: &FunctionSSABlock,
    ) -> Option<(CExpr, r2ssa::PredicateId, r2ssa::ValueId)> {
        let (branch_idx, cond) = Self::unique_terminal_branch_condition(block)?;
        let predicate = self.control_facts()?.branch_for_block(block.addr)?;
        if self.prepared_value_id_for_var(cond) != Some(predicate.condition) {
            return None;
        }
        let expr = self.exact_branch_input_expr(block.addr, branch_idx)?;
        Some((expr, predicate.id, predicate.condition))
    }

    fn unique_terminal_branch_condition(block: &FunctionSSABlock) -> Option<(usize, &SSAVar)> {
        let terminal_idx = block.ops.len().checked_sub(1)?;
        let mut branches = block
            .ops
            .iter()
            .enumerate()
            .filter_map(|(idx, op)| match op {
                SSAOp::CBranch { cond, .. } => Some((idx, cond)),
                _ => None,
            });
        let (branch_idx, cond) = branches.next()?;
        (branches.next().is_none() && branch_idx == terminal_idx).then_some((branch_idx, cond))
    }

    pub(super) fn certified_predicate_expr_for_id(
        &self,
        predicate_id: r2ssa::PredicateId,
    ) -> Option<CExpr> {
        let predicate = self
            .control_facts()?
            .branch_predicates
            .values()
            .find(|predicate| predicate.id == predicate_id)?;
        let block = self
            .inputs
            .prepared_ssa?
            .function()
            .get_block(predicate.block_addr)?;
        let (branch_idx, cond) = Self::unique_terminal_branch_condition(block)?;
        if self.prepared_value_id_for_var(cond) != Some(predicate.condition) {
            return None;
        }
        self.exact_branch_input_expr(predicate.block_addr, branch_idx)
    }

    pub(super) fn resolve_predicate_rhs_for_var(&self, _src: &SSAVar, fallback: CExpr) -> CExpr {
        // `fallback` was assembled from the current normalized operation's
        // exact planned inputs. Preserve those source UseSites verbatim.
        fallback
    }

    #[cfg(test)]
    fn prepared_predicate_candidate_for_branch_block(
        &self,
        block_addr: u64,
        var: &SSAVar,
    ) -> Option<CExpr> {
        let facts = self.control_facts()?;
        let predicate = facts
            .branch_for_block(block_addr)
            .filter(|predicate| Some(predicate.condition) == self.prepared_value_id_for_var(var))
            .or_else(|| {
                facts
                    .block_assumptions
                    .values()
                    .flat_map(|assumptions| assumptions.iter())
                    .find(|assumption| assumption.predecessor == block_addr)
                    .and_then(|assumption| {
                        facts
                            .branch_predicates
                            .values()
                            .find(|predicate| predicate.id == assumption.predicate)
                    })
            })?;
        let block = self.inputs.prepared_ssa?.function().get_block(block_addr)?;
        self.certified_branch_condition_from_block(block)
            .filter(|(_, predicate_id, _)| *predicate_id == predicate.id)
            .map(|(expr, _, _)| expr)
    }

    #[cfg(test)]
    pub(super) fn prepared_predicate_candidate_for_branch_block_for_test(
        &self,
        block_addr: u64,
        var: &SSAVar,
    ) -> Option<CExpr> {
        self.prepared_predicate_candidate_for_branch_block(block_addr, var)
    }
    pub(super) fn negate_condition_expr(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => *operand,
            CExpr::Binary { op, left, right } => {
                let negated = match op {
                    BinaryOp::Eq => Some(BinaryOp::Ne),
                    BinaryOp::Ne => Some(BinaryOp::Eq),
                    BinaryOp::Lt => Some(BinaryOp::Ge),
                    BinaryOp::Le => Some(BinaryOp::Gt),
                    BinaryOp::Gt => Some(BinaryOp::Le),
                    BinaryOp::Ge => Some(BinaryOp::Lt),
                    _ => None,
                };

                if let Some(op) = negated {
                    CExpr::Binary { op, left, right }
                } else {
                    CExpr::unary(UnaryOp::Not, CExpr::Binary { op, left, right })
                }
            }
            other => CExpr::unary(UnaryOp::Not, other),
        }
    }
    pub(super) fn is_zero_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Paren(inner) => self.is_zero_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.is_zero_expr(inner),
            CExpr::IntLit(0) | CExpr::UIntLit(0) => true,
            CExpr::Var(name) => {
                &*self.spelling(*name) == "0" || &*self.spelling(*name) == "elf_header"
            }
            _ => false,
        }
    }

    /// Try to reconstruct a high-level comparison from x86 flag patterns.
    /// Handles patterns like:
    /// - BoolNot(ZF) -> a != b
    /// - ZF -> a == b  
    /// - !ZF && (OF == SF) -> a > b (signed, JG)
    /// - OF == SF -> a >= b (signed, JGE)
    /// - OF != SF -> a < b (signed, JL)
    /// - ZF || (OF != SF) -> a <= b (signed, JLE)
    /// - !CF && !ZF -> a > b (unsigned, JA)
    /// - !CF -> a >= b (unsigned, JAE)
    /// - CF -> a < b (unsigned, JB)
    /// - CF || ZF -> a <= b (unsigned, JBE)
    pub(crate) fn try_reconstruct_condition(&self, expr: &CExpr) -> Option<CExpr> {
        let semantic = expr.clone_without_render_observations();
        let rewritten = self.try_reconstruct_condition_semantic(&semantic)?;
        Some(crate::ast::carry_outer_expr_observations(
            expr,
            rewritten.clone_without_render_observations(),
        ))
    }

    fn try_reconstruct_condition_semantic(&self, expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::And,
                left,
                right,
            } => self
                .reconstruct_signed_gt_from_and(left, right)
                .or_else(|| self.reconstruct_signed_gt_from_and(right, left)),
            CExpr::Binary {
                op: BinaryOp::Or,
                left,
                right,
            } => self
                .reconstruct_signed_le_from_or(left, right)
                .or_else(|| self.reconstruct_signed_le_from_or(right, left)),
            CExpr::Binary {
                op: BinaryOp::Eq, ..
            } => self.reconstruct_signed_ge_from_eq(expr),
            CExpr::Binary {
                op: BinaryOp::Ne, ..
            } => self.reconstruct_signed_lt_from_ne(expr),
            CExpr::Paren(inner) => self.try_reconstruct_condition_semantic(inner),
            CExpr::Cast { ty, expr: inner } => {
                self.try_reconstruct_condition_semantic(inner)
                    .map(|reconstructed| CExpr::Cast {
                        ty: ty.clone(),
                        expr: Box::new(reconstructed),
                    })
            }
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => self
                .try_reconstruct_condition_semantic(operand)
                .map(|inner| self.negate_condition_expr(inner)),
            _ => None,
        }
    }

    // ========== Helper functions for flag pattern detection ==========

    pub(super) fn extract_flag_name(&self, expr: &CExpr, flag: &str) -> Option<String> {
        if let CExpr::Var(name) = expr
            && is_specific_flag_name(&self.spelling(*name), flag)
        {
            return Some(self.spelling(*name).to_string());
        }
        None
    }

    /// Extract OF variable name from an expression (if it's an OF flag reference).
    pub(super) fn extract_of(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "of")
    }

    pub(super) fn reconstruct_signed_gt_from_and(
        &self,
        cmp_expr: &CExpr,
        of_sf_expr: &CExpr,
    ) -> Option<CExpr> {
        let cmp = self.canonical_compare_tuple(cmp_expr)?;
        if cmp.context != CompareContext::Ne {
            return None;
        }

        let (_, sf_expr) = self.extract_of_sf_pair(of_sf_expr, false)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        if !self.compare_tuple_operands_match(&cmp, &sf_cmp) {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Gt, cmp.lhs, cmp.rhs))
    }

    pub(super) fn reconstruct_signed_le_from_or(
        &self,
        cmp_expr: &CExpr,
        of_sf_expr: &CExpr,
    ) -> Option<CExpr> {
        let cmp = self.canonical_compare_tuple(cmp_expr)?;
        if cmp.context != CompareContext::Eq {
            return None;
        }

        let (_, sf_expr) = self.extract_of_sf_pair(of_sf_expr, true)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        if !self.compare_tuple_operands_match(&cmp, &sf_cmp) {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Le, cmp.lhs, cmp.rhs))
    }

    pub(super) fn reconstruct_signed_ge_from_eq(&self, expr: &CExpr) -> Option<CExpr> {
        let (_of_name, sf_expr) = self.extract_of_sf_pair(expr, false)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Ge, sf_cmp.lhs, sf_cmp.rhs))
    }

    pub(super) fn reconstruct_signed_lt_from_ne(&self, expr: &CExpr) -> Option<CExpr> {
        let (_of_name, sf_expr) = self.extract_of_sf_pair(expr, true)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Lt, sf_cmp.lhs, sf_cmp.rhs))
    }

    pub(super) fn extract_of_sf_pair<'b>(
        &self,
        expr: &'b CExpr,
        want_ne: bool,
    ) -> Option<(String, &'b CExpr)> {
        let op_match = if want_ne { BinaryOp::Ne } else { BinaryOp::Eq };
        if let CExpr::Binary { op, left, right } = expr {
            if *op != op_match {
                return None;
            }
            if let Some(of_name) = self.extract_of(left) {
                return Some((of_name, right));
            }
            if let Some(of_name) = self.extract_of(right) {
                return Some((of_name, left));
            }
        }
        None
    }

    pub(super) fn canonical_compare_tuple(&self, expr: &CExpr) -> Option<CompareTuple> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Eq,
                left,
                right,
            } => Some(self.normalize_compare_tuple(CompareTuple {
                lhs: self.resolve_predicate_operand(left, 0),
                rhs: self.resolve_predicate_operand(right, 0),
                context: CompareContext::Eq,
            })),
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => Some(self.normalize_compare_tuple(CompareTuple {
                lhs: self.resolve_predicate_operand(left, 0),
                rhs: self.resolve_predicate_operand(right, 0),
                context: CompareContext::Ne,
            })),
            CExpr::Binary {
                op: BinaryOp::Lt,
                left,
                right,
            } if self.is_zero_expr(right) => {
                if let Some((sub_lhs, sub_rhs)) = self.extract_sub_operands(left) {
                    return Some(self.normalize_compare_tuple(CompareTuple {
                        lhs: self.resolve_predicate_operand(&sub_lhs, 0),
                        rhs: self.resolve_predicate_operand(&sub_rhs, 0),
                        context: CompareContext::SignedNegative,
                    }));
                }
                Some(self.normalize_compare_tuple(CompareTuple {
                    lhs: self.resolve_predicate_operand(left, 0),
                    rhs: CExpr::IntLit(0),
                    context: CompareContext::SignedNegative,
                }))
            }
            CExpr::Paren(inner) => self.canonical_compare_tuple(inner),
            CExpr::Cast { expr: inner, .. } => self.canonical_compare_tuple(inner),
            _ => None,
        }
    }

    pub(super) fn extract_sub_operands(&self, expr: &CExpr) -> Option<(CExpr, CExpr)> {
        self.extract_sub_operands_with_depth(expr, 0)
    }

    fn extract_sub_operands_with_depth(&self, expr: &CExpr, depth: u32) -> Option<(CExpr, CExpr)> {
        if depth > 32 {
            return None;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => Some((left.as_ref().clone(), right.as_ref().clone())),
            CExpr::Paren(inner) => self.extract_sub_operands_with_depth(inner, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.extract_sub_operands_with_depth(inner, depth + 1)
            }
            CExpr::Var(_) => None,
            _ => None,
        }
    }

    pub(super) fn normalize_compare_tuple(&self, mut tuple: CompareTuple) -> CompareTuple {
        if matches!(tuple.context, CompareContext::Eq | CompareContext::Ne)
            && self.is_literal_expr(&tuple.lhs)
            && !self.is_literal_expr(&tuple.rhs)
        {
            std::mem::swap(&mut tuple.lhs, &mut tuple.rhs);
        }
        tuple
    }

    pub(super) fn compare_tuple_operands_match(&self, a: &CompareTuple, b: &CompareTuple) -> bool {
        a.lhs.transparently_eq(&b.lhs) && a.rhs.transparently_eq(&b.rhs)
    }

    pub(super) fn resolve_predicate_operand(&self, expr: &CExpr, depth: u32) -> CExpr {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Paren(inner) => self.resolve_predicate_operand(inner, depth + 1),
            CExpr::Cast { expr: inner, .. } => self.resolve_predicate_operand(inner, depth + 1),
            CExpr::Deref(_) => expr.clone(),
            // SymbolId is a rendered binding identity, never a definition or
            // literal oracle. Exact predicate operands arrive from planned
            // ValueId/UseSite projections before this shape-only simplifier.
            CExpr::Var(name) => CExpr::Var(*name),
            _ => expr.clone(),
        }
    }

    pub(super) fn is_literal_expr(&self, expr: &CExpr) -> bool {
        matches!(
            expr,
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_)
        )
    }
}

fn is_specific_flag_name(name: &str, flag: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if flag_name_matches(&lower, flag) {
        return true;
    }

    let Some((base, suffix)) = lower.split_once('_') else {
        return false;
    };

    flag_name_matches(base, flag)
        && !suffix.is_empty()
        && suffix.chars().all(|ch| ch.is_ascii_digit())
}

fn flag_name_matches(base: &str, flag: &str) -> bool {
    if base == flag {
        return true;
    }

    matches!(
        (base, flag),
        ("cy" | "tmpcy", "cf")
            | ("zr" | "tmpzr", "zf")
            | ("ng" | "tmpng", "sf")
            | ("ov" | "tmpov", "of")
    )
}
