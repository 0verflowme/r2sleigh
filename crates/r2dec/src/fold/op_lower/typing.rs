//! Where the renderer's types come from.
//!
//! Every conversion the renderer spells is made from two facts: what the
//! expression has and what the boundary requires. Both are read from the
//! typed boundaries the binding plan derives over the arena, keyed by the
//! value read or by the operation lowered and the operand's position, and
//! neither is ever read off the rendered text.

use r2rewrite::{CValue, TypedBoundaries};
use r2ssa::{MachineExprId, ValueId};

use super::{FoldingContext, LowerFrame};
use crate::ast::{CExpr, CType};

impl FoldingContext<'_> {
    /// The typed boundaries of the function being rendered, where a plan
    /// exists to derive them from.
    pub(super) fn typed_boundaries(&self) -> Option<&TypedBoundaries> {
        Some(self.inputs.binding_names?.plan().typed_boundaries())
    }

    /// The width of an address on the target.
    pub(super) fn pointer_bits(&self) -> u32 {
        self.inputs
            .prepared_ssa
            .map(|prepared| {
                prepared
                    .machine_context()
                    .memory_model()
                    .default_address_bits()
            })
            .unwrap_or_else(|| self.inputs.arch.ptr_size.saturating_mul(8))
    }

    /// Convert `expr`, which has `from`, to `to`. The one emitter.
    pub(super) fn convert(&self, expr: CExpr, from: &CValue, to: &CType) -> CExpr {
        super::convert::convert(expr, from, to, self.pointer_bits())
    }

    /// Convert where what the expression has may be unrecorded.
    ///
    /// Nothing is recorded only where there is no plan to record it, and
    /// then the one conversion that is still certain is the one C never
    /// performs on its own: an integer does not become a pointer unless the
    /// program says so.
    pub(super) fn convert_from(&self, expr: CExpr, from: Option<&CValue>, to: &CType) -> CExpr {
        match from {
            Some(from) => self.convert(expr, from, to),
            None if matches!(to, CType::Pointer(_)) => CExpr::cast(to.clone(), expr),
            None => expr,
        }
    }

    /// What a read of `value` renders as, before any use projection.
    pub(super) fn value_type(&self, value: ValueId) -> Option<CValue> {
        self.typed_boundaries()?.value_type(value).cloned()
    }

    /// The arena root of the value the operation at `frame` defines.
    pub(super) fn root_at(&self, frame: &LowerFrame) -> Option<MachineExprId> {
        let site = frame.normalized_site?;
        let output = self.normalized_output_projection(site).ok()?;
        let names = self.inputs.binding_names?;
        Some(
            names
                .plan()
                .machine_projection()
                .entity_for_output(output.value)?
                .root(),
        )
    }

    /// What the operation at `frame` requires of its operand at `index`.
    pub(super) fn required_at(&self, frame: &LowerFrame, index: usize) -> Option<CType> {
        let root = self.root_at(frame)?;
        self.typed_boundaries()?.required(root, index).cloned()
    }

    /// What the expression the operation at `frame` renders has.
    pub(super) fn produced_at(&self, frame: &LowerFrame) -> Option<CValue> {
        let root = self.root_at(frame)?;
        self.typed_boundaries()?.produced(root).cloned()
    }
}
