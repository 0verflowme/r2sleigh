pub(crate) mod arch;
pub(crate) mod context;
pub(crate) mod flags;
pub(crate) mod op_lower;
pub(crate) mod stack;

use crate::ast::CStmt;
pub(crate) use context::FoldingContext;
pub(crate) type SSABlock = r2ssa::FunctionSSABlock;
use r2ssa::SSAOp;

pub(super) const MAX_STACK_OFFSET_DEPTH: u32 = 8;
pub(super) const MAX_STACK_ALIAS_DEPTH: u32 = 8;
pub(super) const MAX_SIMPLE_EXPR_DEPTH: u32 = 2;
pub(super) const MAX_RETURN_EXPR_DEPTH: u32 = 8;
pub(super) const MAX_ALIAS_REWRITE_DEPTH: u32 = 32;
pub(super) const MAX_COND_STACK_ALIAS_DEPTH: u32 = 8;
pub(super) const MAX_PREDICATE_SIMPLIFY_DEPTH: u32 = 6;
pub(super) const MAX_PREDICATE_OPERAND_DEPTH: u32 = 12;
pub(super) const MAX_SF_SURROGATE_DEPTH: usize = 128;
pub(super) const MAX_SUB_LIKE_DEPTH: usize = 128;

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
