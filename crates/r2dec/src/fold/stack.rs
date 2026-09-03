use crate::ast::{CExpr, CType};
use r2ssa::ObjectId;

use super::context::FoldingContext;

fn frame_object_address_expr(object_expr: CExpr, ty: CType) -> (CExpr, CType) {
    match ty {
        CType::Array(_, _) => (object_expr, ty),
        _ => (CExpr::addr_of(object_expr), CType::Pointer(Box::new(ty))),
    }
}

impl<'a> FoldingContext<'a> {
    pub(super) fn certified_stack_var_expr_for_object(&self, object: ObjectId) -> Option<CExpr> {
        let names = self.inputs.binding_names?;
        match names.require_stack(object) {
            Ok(crate::binding_plan::PlannedStackSymbol::Bound(symbol)) => Some(CExpr::Var(symbol)),
            Err(error) => {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    eprintln!("stack object {object:?} has no program variable: {error:?}");
                }
                self.retain_first_lowering_refusal(
                    super::op_lower::OpLoweringRefusal::missing_program_variable(),
                );
                None
            }
        }
    }

    /// Spell the base address of one certified frame object and the C type
    /// that spelling actually has.
    ///
    /// Arrays decay from their bare object name. Every other object needs an
    /// explicit address-of, so the call and the later stack access visibly
    /// name the same program object rather than unrelated stack arithmetic.
    pub(super) fn certified_stack_address_expr_for_object(
        &self,
        object: ObjectId,
    ) -> Option<(CExpr, CType)> {
        let names = self.inputs.binding_names?;
        let crate::binding_plan::StackObjectDisposition::Bound { binding } =
            names.plan().stack_object_disposition(object)?
        else {
            self.retain_first_lowering_refusal(
                super::op_lower::OpLoweringRefusal::missing_program_variable(),
            );
            return None;
        };
        let ty = names.plan().binding(binding)?.declaration_type().clone();
        let object_expr = self.certified_stack_var_expr_for_object(object)?;
        Some(frame_object_address_expr(object_expr, ty))
    }

    /// Whether a copy restates a write the block has already rendered.
    ///
    /// Materialising a merge replaces it with a copy on every predecessor edge,
    /// so a loop carries its update back to the header as `X8_2 = X8_3`. Once the
    /// alias map covers what materialisation introduced, both sides are spelled
    /// by the carrier's one name and the copy says `x8 = x8`, which the statement
    /// that computed the update has already said. One of the program's own
    /// copies acquires the same spelling once carrier coalescing puts its two
    /// sides in one object, and says as little.
    ///
    /// The answer is the journal's sealed one, never a comparison of the two
    /// spellings here: a copy whose sides share a name but not a whole write
    /// -- a narrowing into a lane -- is a real operation and keeps its
    /// statement, and only the journal has the projection to tell the two
    /// apart.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::{SymbolRole, SymbolTable};

    #[test]
    fn frame_object_addresses_use_address_of_except_for_array_decay() {
        let mut symbols = SymbolTable::new();
        let scalar = CType::uint(64);
        let scalar_symbol = symbols.declare("scalar", scalar.clone(), SymbolRole::StackLocal(-8));
        let (scalar_expr, scalar_address_ty) =
            frame_object_address_expr(CExpr::Var(scalar_symbol), scalar.clone());
        assert_eq!(scalar_expr, CExpr::addr_of(CExpr::Var(scalar_symbol)));
        assert_eq!(scalar_address_ty, CType::Pointer(Box::new(scalar)));

        let array = CType::Array(Box::new(CType::uint(8)), Some(160));
        let array_symbol = symbols.declare("buffer", array.clone(), SymbolRole::StackLocal(-160));
        let (array_expr, array_address_ty) =
            frame_object_address_expr(CExpr::Var(array_symbol), array.clone());
        assert_eq!(array_expr, CExpr::Var(array_symbol));
        assert_eq!(array_address_ty, array);
    }
}
