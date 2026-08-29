pub(crate) mod context;
pub(crate) mod flags;
pub(crate) mod op_lower;
pub(crate) mod stack;

use crate::ast::CStmt;
pub(crate) use context::FoldingContext;
pub(crate) type SSABlock = r2ssa::FunctionSSABlock;
use r2ssa::SSAOp;

pub(super) const MAX_PREDICATE_OPERAND_DEPTH: u32 = 12;

/// Residualize raw SSA operations for public block-level exports.
///
/// Executable C lowering requires an engine-prepared `DecompilerInput` with
/// `FunctionFacts` route and render proof. This raw helper is kept only for
/// diagnostic/export surfaces that do not have that contract.
pub fn lower_ssa_ops_to_stmts(_ptr_size: u32, ops: &[SSAOp]) -> Vec<CStmt> {
    ops.iter()
        .enumerate()
        .map(|(idx, op)| {
            CStmt::Comment(format!(
                "r2dec residual: raw SSA op {idx} requires r2engine FunctionFacts render proof; executable C suppressed: {op:?}"
            ))
        })
        .collect()
}
