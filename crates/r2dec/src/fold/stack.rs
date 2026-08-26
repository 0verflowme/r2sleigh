use crate::ast::CExpr;
use r2ssa::{ObjectId, SSAVar};

use super::context::FoldingContext;

impl<'a> FoldingContext<'a> {
    pub(super) fn certified_stack_var_expr_for_object(&self, object: ObjectId) -> Option<CExpr> {
        let names = self.inputs.binding_names?;
        match names.require_stack(object) {
            Ok(crate::binding_plan::PlannedStackSymbol::Bound(symbol)) => Some(CExpr::Var(symbol)),
            Err(_) => {
                self.retain_first_lowering_refusal(
                    super::op_lower::OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
                None
            }
        }
    }

    /// Resolve a stack offset only from the prepared source-owned object model.
    /// Whether a copy restates a carrier update the block has already rendered.
    ///
    /// Materialising a merge replaces it with a copy on every predecessor edge,
    /// so a loop carries its update back to the header as `X8_2 = X8_3`. Once the
    /// alias map covers what materialisation introduced, both sides are spelled
    /// by the carrier's one name and the copy says `x8 = x8`, which the statement
    /// that computed the update has already said.
    ///
    /// The edge into the loop is the same kind of copy and must be kept, because
    /// nothing else introduces the carrier there. The two are told apart by
    /// whether the source is an entry value: a version-0 source is the value the
    /// function was called with and has no defining statement of its own, so the
    /// copy is the only place the carrier is given it.
    pub(super) fn is_carrier_self_copy(&self, dst: &SSAVar, src: &SSAVar) -> bool {
        if src.version == 0 {
            return false;
        }
        let (Some(dst_value), Some(src_value), Some(names), Some(render)) = (
            self.prepared_value_id_for_var(dst),
            self.prepared_value_id_for_var(src),
            self.inputs.binding_names,
            self.inputs.render_facts(),
        ) else {
            return false;
        };
        if render.loop_carrier_for_value(dst_value).is_none()
            || render.loop_carrier_for_value(src_value).is_none()
        {
            return false;
        }
        matches!(
            (names.require_value(dst_value), names.require_value(src_value)),
            (
                Ok(crate::binding_plan::PlannedValueSymbol::Bound(dst_symbol)),
                Ok(crate::binding_plan::PlannedValueSymbol::Bound(src_symbol)),
            ) if dst_symbol == src_symbol
        )
    }
}
