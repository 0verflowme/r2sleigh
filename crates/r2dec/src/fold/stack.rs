use crate::ast::CExpr;
use r2ssa::ObjectId;

use super::context::FoldingContext;

impl<'a> FoldingContext<'a> {
    pub(super) fn certified_stack_var_expr_for_object(&self, object: ObjectId) -> Option<CExpr> {
        let names = self.inputs.binding_names?;
        match names.require_stack(object) {
            Ok(crate::binding_plan::PlannedStackSymbol::Bound(symbol)) => Some(CExpr::Var(symbol)),
            Err(_) => {
                self.retain_first_lowering_refusal(crate::analysis::lower::refusal(
                    super::op_lower::OpLoweringRefusal::MissingProgramVariableAuthorization,
                ));
                None
            }
        }
    }

    /// Whether a certified synthetic copy restates a carrier update the block
    /// has already rendered.
    ///
    /// Materialising a merge replaces it with a copy on every predecessor edge,
    /// so a loop carries its update back to the header as `X8_2 = X8_3`. Once the
    /// alias map covers what materialisation introduced, both sides are spelled
    /// by the carrier's one name and the copy says `x8 = x8`, which the statement
    /// that computed the update has already said.
    ///
    /// An original program `Copy` can acquire the same spelling on both sides
    /// after carrier coalescing.  It remains a real definition and use, so the
    /// sealed normalization origin is required before any suppression.  The
    /// edge into the loop is also kept because a version-0 source has no
    /// defining statement of its own.
    pub(super) fn current_copy_has_coalesced_carrier_elision(&self) -> bool {
        let (Some(block), Some(op_idx), Some(journal)) = (
            self.current_block_id.get(),
            self.current_op_idx.get(),
            self.inputs.observation_journal,
        ) else {
            return false;
        };
        journal
            .borrow()
            .is_coalesced_carrier_copy(crate::normalize::NormalizedOpSite { block, op_idx })
    }
}
