use r2ssa::{FunctionSSABlock, SSAOp, SSAVar};

use super::context::FoldingContext;
use crate::ast::CExpr;
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
    // ========== Helper functions for flag pattern detection ==========
}
