use std::collections::HashSet;

use r2ssa::{FunctionSSABlock, SSAOp, SSAVar};

use super::context::FoldingContext;
use super::op_lower::parse_const_value;
use super::{MAX_PREDICATE_OPERAND_DEPTH, MAX_SF_SURROGATE_DEPTH, MAX_SUB_LIKE_DEPTH};
use crate::analysis::{FlagCompareKind, FlagCompareProvenance, utils};
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
    fn compare_const_expr_from_name(&self, name: &str) -> Option<CExpr> {
        let raw = name.strip_prefix("const:")?;
        let raw = raw.split('_').next().unwrap_or(raw);

        let value = if let Some(dec) = raw.strip_prefix("0d").or_else(|| raw.strip_prefix("0D")) {
            dec.parse::<u64>().ok()?
        } else if let Some(hex) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
            u64::from_str_radix(hex, 16).ok()?
        } else if raw.len() > 1 && raw.chars().all(|c| c.is_ascii_hexdigit()) {
            u64::from_str_radix(raw, 16).ok()?
        } else {
            raw.parse::<u64>().ok()?
        };

        Some(if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        })
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
            // Pattern: Binary AND - check for signed greater than: !ZF && (OF == SF)
            CExpr::Binary {
                op: BinaryOp::And,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_gt_from_and(left, right) {
                    return Some(rel);
                }
                if let Some(rel) = self.reconstruct_signed_gt_from_and(right, left) {
                    return Some(rel);
                }

                // Try !ZF && (OF == SF) -> a > b (signed)
                if let (Some(zf_name), true) = (self.extract_not_zf(left), self.is_of_eq_sf(right))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(
                        BinaryOp::Gt,
                        self.origin_name_to_expr(&a)?,
                        self.origin_name_to_expr(&b)?,
                    ));
                }
                // Try reversed: (OF == SF) && !ZF
                if let (Some(zf_name), true) = (self.extract_not_zf(right), self.is_of_eq_sf(left))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(
                        BinaryOp::Gt,
                        self.origin_name_to_expr(&a)?,
                        self.origin_name_to_expr(&b)?,
                    ));
                }

                // Try !CF && !ZF -> a > b (unsigned, JA)
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_not_cf(left), self.extract_not_zf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Gt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Gt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }
                // Try reversed
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_not_cf(right), self.extract_not_zf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Gt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Gt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }

                None
            }

            // Pattern: Binary OR - check for unsigned less-equal: CF || ZF
            CExpr::Binary {
                op: BinaryOp::Or,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_le_from_or(left, right) {
                    return Some(rel);
                }
                if let Some(rel) = self.reconstruct_signed_le_from_or(right, left) {
                    return Some(rel);
                }

                // Try CF || ZF -> a <= b (unsigned, JBE)
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_cf(left), self.extract_zf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Le,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Le,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }
                // Try reversed
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_cf(right), self.extract_zf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Le,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Le,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }

                // Try ZF || (OF != SF) -> a <= b (signed, JLE)
                if let (Some(zf_name), true) = (self.extract_zf(left), self.is_of_ne_sf(right))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(
                        BinaryOp::Le,
                        self.origin_name_to_expr(&a)?,
                        self.origin_name_to_expr(&b)?,
                    ));
                }
                // Try reversed
                if let (Some(zf_name), true) = (self.extract_zf(right), self.is_of_ne_sf(left))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(
                        BinaryOp::Le,
                        self.origin_name_to_expr(&a)?,
                        self.origin_name_to_expr(&b)?,
                    ));
                }

                None
            }

            // Pattern: Binary Eq - check for OF == SF (signed >=)
            // AND temp == 0 patterns (TEST/CMP reconstruction)
            CExpr::Binary {
                op: BinaryOp::Eq,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_ge_from_eq(expr) {
                    return Some(rel);
                }

                // OF == SF -> a >= b (signed, JGE)
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(left), self.extract_sf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Ge,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Ge,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }
                // Try reversed
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(right), self.extract_sf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Ge,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Ge,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }
                // Fallback: temp == 0 where temp is from TEST/CMP
                if let Some(result) = self.try_reconstruct_cmp_zero(left, right, BinaryOp::Eq) {
                    return Some(result);
                }
                // Also try reversed (0 == temp)
                if let Some(result) = self.try_reconstruct_cmp_zero(right, left, BinaryOp::Eq) {
                    return Some(result);
                }
                None
            }

            // Pattern: Binary Ne - check for OF != SF (signed <)
            // AND temp != 0 patterns (TEST/CMP reconstruction)
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_lt_from_ne(expr) {
                    return Some(rel);
                }

                // OF != SF -> a < b (signed, JL)
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(left), self.extract_sf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Lt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Lt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }
                // Try reversed
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(right), self.extract_sf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Lt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(
                            BinaryOp::Lt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }
                // Fallback: temp != 0 where temp is from TEST/CMP
                if let Some(result) = self.try_reconstruct_cmp_zero(left, right, BinaryOp::Ne) {
                    return Some(result);
                }
                if let Some(result) = self.try_reconstruct_cmp_zero(right, left, BinaryOp::Ne) {
                    return Some(result);
                }
                None
            }

            CExpr::Paren(inner) => self.try_reconstruct_condition_semantic(inner),

            CExpr::Cast { ty, expr: inner } => {
                self.try_reconstruct_condition_semantic(inner)
                    .map(|reconstructed| CExpr::Cast {
                        ty: ty.clone(),
                        expr: Box::new(reconstructed),
                    })
            }

            // Pattern: !ZF (BoolNot of ZF) means "not equal"
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                if let CExpr::Var(flag_name) = operand.as_ref() {
                    if let Some(prov) =
                        self.lookup_flag_compare_provenance(&self.spelling(*flag_name))
                        && let Some(expr) = self.compare_provenance_expr(&prov)
                    {
                        return Some(self.negate_condition_expr(expr));
                    }

                    let flag_lower = self.spelling(*flag_name).to_lowercase();
                    if flag_lower.contains("zf") {
                        // !ZF means a != b
                        if let Some((left, right)) =
                            self.lookup_flag_origin(&self.spelling(*flag_name))
                        {
                            return Some(CExpr::binary(
                                BinaryOp::Ne,
                                self.origin_name_to_expr(&left)?,
                                self.origin_name_to_expr(&right)?,
                            ));
                        }
                    }
                    // !CF means a >= b (unsigned, JAE)
                    if flag_lower.contains("cf")
                        && let Some((left, right)) =
                            self.lookup_flag_origin(&self.spelling(*flag_name))
                    {
                        return Some(CExpr::binary(
                            BinaryOp::Ge,
                            self.origin_name_to_expr(&left)?,
                            self.origin_name_to_expr(&right)?,
                        ));
                    }
                }

                // Try !(CF || ZF) -> a > b (unsigned, JA) - negation of JBE
                if let CExpr::Binary {
                    op: BinaryOp::Or,
                    left: or_left,
                    right: or_right,
                } = operand.as_ref()
                {
                    if let (Some(cf_name), Some(_zf_name)) =
                        (self.extract_cf(or_left), self.extract_zf(or_right))
                        && let Some((a, b)) = self.lookup_flag_origin(&cf_name)
                    {
                        return Some(CExpr::binary(
                            BinaryOp::Gt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                    // Try reversed
                    if let (Some(cf_name), Some(_zf_name)) =
                        (self.extract_cf(or_right), self.extract_zf(or_left))
                        && let Some((a, b)) = self.lookup_flag_origin(&cf_name)
                    {
                        return Some(CExpr::binary(
                            BinaryOp::Gt,
                            self.origin_name_to_expr(&a)?,
                            self.origin_name_to_expr(&b)?,
                        ));
                    }
                }

                // Try to recurse into the operand and negate the result
                if let Some(inner) = self.try_reconstruct_condition_semantic(operand) {
                    // Negate comparison operators directly instead of wrapping in !()
                    return Some(match inner {
                        CExpr::Binary {
                            op: BinaryOp::Eq,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Ne,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Ne,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Eq,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Lt,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Ge,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Ge,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Lt,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Gt,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Le,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Le,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Gt,
                            left,
                            right,
                        },
                        other => CExpr::unary(UnaryOp::Not, other),
                    });
                }
                None
            }

            // Pattern: ZF directly means "equal"
            CExpr::Var(flag_name) => {
                if let Some(prov) = self.lookup_flag_compare_provenance(&self.spelling(*flag_name))
                    && let Some(expr) = self.compare_provenance_expr(&prov)
                {
                    return Some(expr);
                }

                let flag_lower = self.spelling(*flag_name).to_lowercase();
                if flag_lower.contains("zf")
                    && let Some((left, right)) = self.lookup_flag_origin(&self.spelling(*flag_name))
                {
                    return Some(CExpr::binary(
                        BinaryOp::Eq,
                        self.origin_name_to_expr(&left)?,
                        self.origin_name_to_expr(&right)?,
                    ));
                }
                // CF directly means a < b (unsigned, JB)
                if flag_lower.contains("cf")
                    && let Some((left, right)) = self.lookup_flag_origin(&self.spelling(*flag_name))
                {
                    return Some(CExpr::binary(
                        BinaryOp::Lt,
                        self.origin_name_to_expr(&left)?,
                        self.origin_name_to_expr(&right)?,
                    ));
                }
                None
            }

            _ => None,
        }
    }

    /// Try to reconstruct a comparison from `temp == 0` or `temp != 0` patterns.
    ///
    /// For `TEST reg, reg; JZ/JNZ`:
    ///   - `t1 = IntAnd(RBX, RBX)` -> `ZF = (t1 == 0)` -> CBranch(ZF)
    ///   - When we see `Var(t1) == IntLit(0)`, trace t1's definition:
    ///     - If `BitAnd(a, b)` where a == b (TEST): produce `a == 0` / `a != 0`
    ///     - If `Sub(a, b)` (CMP): produce `a == b` / `a != b`
    pub(super) fn try_reconstruct_cmp_zero(
        &self,
        var_side: &CExpr,
        zero_side: &CExpr,
        cmp_op: BinaryOp,
    ) -> Option<CExpr> {
        let _ = (var_side, zero_side, cmp_op);
        // At this point the SSA identity has been projected to a SymbolId. A
        // binding may cover several SSA values, so looking up a definition by
        // spelling (or by symbol) cannot prove which comparison produced it.
        None
    }

    // ========== Helper functions for flag pattern detection ==========

    pub(super) fn extract_flag_name(&self, expr: &CExpr, flag: &str) -> Option<String> {
        if let CExpr::Var(name) = expr {
            if is_specific_flag_name(&self.spelling(*name), flag) {
                return Some(self.spelling(*name).to_string());
            }
        }
        None
    }

    /// Extract ZF variable name from an expression (if it's a ZF flag reference).
    pub(super) fn extract_zf(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "zf")
    }

    /// Extract CF variable name from an expression (if it's a CF flag reference).
    pub(super) fn extract_cf(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "cf")
    }

    /// Extract SF variable name from an expression (if it's a SF flag reference).
    pub(super) fn extract_sf(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "sf")
    }

    /// Extract OF variable name from an expression (if it's an OF flag reference).
    pub(super) fn extract_of(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "of")
    }

    /// Extract ZF variable name from a !ZF expression.
    pub(super) fn extract_not_zf(&self, expr: &CExpr) -> Option<String> {
        if let CExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } = expr
        {
            return self.extract_zf(operand);
        }
        None
    }

    /// Extract CF variable name from a !CF expression.
    pub(super) fn extract_not_cf(&self, expr: &CExpr) -> Option<String> {
        if let CExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } = expr
        {
            return self.extract_cf(operand);
        }
        None
    }

    /// Check if expression is OF == SF.
    pub(super) fn is_of_eq_sf(&self, expr: &CExpr) -> bool {
        if let CExpr::Binary {
            op: BinaryOp::Eq,
            left,
            right,
        } = expr
        {
            let has_of_sf = self.extract_of(left).is_some() && self.is_sf_like_expr(right);
            let has_sf_of = self.is_sf_like_expr(left) && self.extract_of(right).is_some();
            return has_of_sf || has_sf_of;
        }
        false
    }

    /// Check if expression is OF != SF.
    pub(super) fn is_of_ne_sf(&self, expr: &CExpr) -> bool {
        if let CExpr::Binary {
            op: BinaryOp::Ne,
            left,
            right,
        } = expr
        {
            let has_of_sf = self.extract_of(left).is_some() && self.is_sf_like_expr(right);
            let has_sf_of = self.is_sf_like_expr(left) && self.extract_of(right).is_some();
            return has_of_sf || has_sf_of;
        }
        // Also check for !(OF == SF)
        if let CExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } = expr
        {
            return self.is_of_eq_sf(operand);
        }
        false
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

        let (of_name, sf_expr) = self.extract_of_sf_pair(of_sf_expr, false)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        if !self.compare_tuple_operands_match(&cmp, &sf_cmp) {
            return None;
        }
        if !self.compare_tuple_matches_flag_origin(&cmp, &of_name) {
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

        let (of_name, sf_expr) = self.extract_of_sf_pair(of_sf_expr, true)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        if !self.compare_tuple_operands_match(&cmp, &sf_cmp) {
            return None;
        }
        if !self.compare_tuple_matches_flag_origin(&cmp, &of_name) {
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
                lhs: self.resolve_predicate_operand(left, 0, &mut HashSet::new()),
                rhs: self.resolve_predicate_operand(right, 0, &mut HashSet::new()),
                context: CompareContext::Eq,
            })),
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => Some(self.normalize_compare_tuple(CompareTuple {
                lhs: self.resolve_predicate_operand(left, 0, &mut HashSet::new()),
                rhs: self.resolve_predicate_operand(right, 0, &mut HashSet::new()),
                context: CompareContext::Ne,
            })),
            CExpr::Binary {
                op: BinaryOp::Lt,
                left,
                right,
            } if self.is_zero_expr(right) => {
                if let Some((sub_lhs, sub_rhs)) = self.extract_sub_operands(left) {
                    return Some(self.normalize_compare_tuple(CompareTuple {
                        lhs: self.resolve_predicate_operand(&sub_lhs, 0, &mut HashSet::new()),
                        rhs: self.resolve_predicate_operand(&sub_rhs, 0, &mut HashSet::new()),
                        context: CompareContext::SignedNegative,
                    }));
                }
                Some(self.normalize_compare_tuple(CompareTuple {
                    lhs: self.resolve_predicate_operand(left, 0, &mut HashSet::new()),
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
        self.extract_sub_operands_with_seen(expr, 0, &mut HashSet::new())
    }

    fn extract_sub_operands_with_seen(
        &self,
        expr: &CExpr,
        depth: u32,
        seen: &mut HashSet<String>,
    ) -> Option<(CExpr, CExpr)> {
        if depth > 32 {
            return None;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => Some((left.as_ref().clone(), right.as_ref().clone())),
            CExpr::Paren(inner) => self.extract_sub_operands_with_seen(inner, depth + 1, seen),
            CExpr::Cast { expr: inner, .. } => {
                self.extract_sub_operands_with_seen(inner, depth + 1, seen)
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

    pub(super) fn compare_tuple_matches_flag_origin(
        &self,
        tuple: &CompareTuple,
        of_name: &str,
    ) -> bool {
        let Some(origin) = self.compare_tuple_from_flag_origin(of_name) else {
            return true;
        };

        // If either side still contains opaque temporaries, treat origin matching as
        // advisory only. Local tuple consistency (cmp vs SF-surrogate) remains mandatory.
        if self.expr_contains_opaque_temp(&tuple.lhs)
            || self.expr_contains_opaque_temp(&tuple.rhs)
            || self.expr_contains_opaque_temp(&origin.lhs)
            || self.expr_contains_opaque_temp(&origin.rhs)
            || self.expr_contains_unresolved_memory(&tuple.lhs)
            || self.expr_contains_unresolved_memory(&tuple.rhs)
            || self.expr_contains_unresolved_memory(&origin.lhs)
            || self.expr_contains_unresolved_memory(&origin.rhs)
        {
            return true;
        }

        tuple.lhs == origin.lhs && tuple.rhs == origin.rhs
    }

    pub(super) fn compare_tuple_from_flag_origin(&self, flag_name: &str) -> Option<CompareTuple> {
        let prov = self.lookup_flag_compare_provenance(flag_name)?;
        let lhs_origin = self.origin_name_to_expr(&prov.lhs)?;
        let rhs_origin = self.origin_name_to_expr(&prov.rhs)?;
        let lhs = self.resolve_predicate_operand(&lhs_origin, 0, &mut HashSet::new());
        let rhs = self.resolve_predicate_operand(&rhs_origin, 0, &mut HashSet::new());

        Some(self.normalize_compare_tuple(CompareTuple {
            lhs,
            rhs,
            context: match prov.kind {
                FlagCompareKind::Equality => CompareContext::Eq,
                FlagCompareKind::UnsignedLess
                | FlagCompareKind::SignedNegative
                | FlagCompareKind::Overflow => CompareContext::SignedNegative,
            },
        }))
    }

    /// A spelling-only origin can authorize only a literal. Program variables
    /// require the original `SSAVar`/`ValueId`; absent that identity this legacy
    /// provenance is advisory and yields no candidate.
    pub(super) fn origin_name_to_expr(&self, name: &str) -> Option<CExpr> {
        self.parse_expr_from_name(name)
    }

    pub(super) fn parse_expr_from_name(&self, name: &str) -> Option<CExpr> {
        if let Some(expr) = self.compare_const_expr_from_name(name) {
            return Some(expr);
        }

        if let Some(val) = parse_const_value(name) {
            return Some(if val > 0x7fffffff {
                CExpr::UIntLit(val)
            } else {
                CExpr::IntLit(val as i64)
            });
        }

        if let Some(dec) = name.strip_prefix("0d").or_else(|| name.strip_prefix("0D"))
            && let Ok(val) = dec.parse::<i64>()
        {
            return Some(CExpr::IntLit(val));
        }

        if let Some(hex) = name.strip_prefix("0x").or_else(|| name.strip_prefix("0X"))
            && let Ok(val) = u64::from_str_radix(hex, 16)
        {
            return Some(if val > 0x7fffffff {
                CExpr::UIntLit(val)
            } else {
                CExpr::IntLit(val as i64)
            });
        }

        if name.chars().all(|c| c.is_ascii_hexdigit()) {
            let has_alpha = name.chars().any(|c| c.is_ascii_alphabetic());
            let has_digit = name.chars().any(|c| c.is_ascii_digit());
            if has_alpha && (has_digit || name.len() > 4) {
                if let Ok(val) = u64::from_str_radix(name, 16) {
                    return Some(if val > 0x7fffffff {
                        CExpr::UIntLit(val)
                    } else {
                        CExpr::IntLit(val as i64)
                    });
                }
            } else if let Ok(dec) = name.parse::<i64>() {
                return Some(CExpr::IntLit(dec));
            }
        }

        if let Ok(dec) = name.parse::<i64>() {
            return Some(CExpr::IntLit(dec));
        }

        None
    }

    pub(super) fn resolve_predicate_operand(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Paren(inner) => self.resolve_predicate_operand(inner, depth + 1, visited),
            CExpr::Cast { expr: inner, .. } => {
                self.resolve_predicate_operand(inner, depth + 1, visited)
            }
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

    pub(super) fn is_opaque_temp_name(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        if lower.starts_with("tmp_") || utils::is_temporary_name(name) {
            return true;
        }
        if name.starts_with("var_") {
            return true;
        }
        if let Some(rest) = name.strip_prefix('t') {
            // A lifter temporary is spelled `t` followed by whatever the
            // lifter called it, which is an offset into the unique space,
            // `t11f80`, or a register-alias slot, `tregalias:100000704:2:0`.
            // Only the first was recognised here, so a dead assignment to the
            // second survived this prune and reached the page under a name no
            // C function declares.
            return rest.starts_with(|ch: char| ch.is_ascii_digit()) || rest.contains(':');
        }
        false
    }

    pub(super) fn expr_contains_opaque_temp(&self, expr: &CExpr) -> bool {
        let mut found = false;
        expr.visit(&mut |node| {
            if let CExpr::Var(name) = node
                && self.is_opaque_temp_name(&self.spelling(*name))
            {
                found = true;
            }
        });
        found
    }

    pub(super) fn expr_contains_unresolved_memory(&self, expr: &CExpr) -> bool {
        let mut found = false;
        expr.visit(&mut |node| {
            if matches!(node, CExpr::Deref(_)) {
                found = true;
            }
        });
        found
    }

    pub(super) fn is_sf_like_expr(&self, expr: &CExpr) -> bool {
        self.extract_sf(expr).is_some() || self.is_sf_surrogate(expr)
    }

    pub(super) fn is_sf_surrogate(&self, expr: &CExpr) -> bool {
        let mut visited = HashSet::new();
        self.is_sf_surrogate_inner(expr, &mut visited, 0)
    }

    pub(super) fn is_sf_surrogate_inner(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
        depth: usize,
    ) -> bool {
        // Guard against deeply nested/cyclic definitions from large CFGs.
        if depth > MAX_SF_SURROGATE_DEPTH {
            return false;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Lt,
                left,
                right,
            } if self.is_zero_expr(right) => self.is_sub_like_expr_inner(left, visited, depth + 1),
            CExpr::Paren(inner) => self.is_sf_surrogate_inner(inner, visited, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.is_sf_surrogate_inner(inner, visited, depth + 1)
            }
            CExpr::Var(_) => false,
            _ => false,
        }
    }

    pub(super) fn is_sub_like_expr_inner(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
        depth: usize,
    ) -> bool {
        if depth > MAX_SUB_LIKE_DEPTH {
            return false;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub, ..
            } => true,
            CExpr::Paren(inner) => self.is_sub_like_expr_inner(inner, visited, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.is_sub_like_expr_inner(inner, visited, depth + 1)
            }
            CExpr::Var(_) => false,
            _ => false,
        }
    }

    /// Look up the original comparison operands for a flag variable.
    pub(super) fn lookup_flag_origin(&self, _flag_name: &str) -> Option<(String, String)> {
        None
    }

    pub(super) fn lookup_flag_compare_provenance(
        &self,
        _flag_name: &str,
    ) -> Option<FlagCompareProvenance> {
        None
    }

    pub(super) fn compare_provenance_expr(&self, prov: &FlagCompareProvenance) -> Option<CExpr> {
        let lhs_origin = self.origin_name_to_expr(&prov.lhs)?;
        let rhs_origin = self.origin_name_to_expr(&prov.rhs)?;
        let lhs = self.resolve_predicate_operand(&lhs_origin, 0, &mut HashSet::new());
        let rhs = self.resolve_predicate_operand(&rhs_origin, 0, &mut HashSet::new());

        match prov.kind {
            FlagCompareKind::Equality => Some(CExpr::binary(BinaryOp::Eq, lhs, rhs)),
            FlagCompareKind::UnsignedLess => Some(CExpr::binary(BinaryOp::Lt, lhs, rhs)),
            FlagCompareKind::SignedNegative => Some(CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(BinaryOp::Sub, lhs, rhs),
                CExpr::IntLit(0),
            )),
            FlagCompareKind::Overflow => None,
        }
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
