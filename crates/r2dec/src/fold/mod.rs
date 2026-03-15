pub(crate) mod arch;
pub(crate) mod context;
pub(crate) mod flags;
pub(crate) mod op_lower;
pub(crate) mod stack;

use crate::ast::CStmt;
pub use context::FoldingContext;
pub(crate) use context::{PtrArith, SSABlock};
use r2ssa::SSAOp;

pub(super) const MAX_STACK_OFFSET_DEPTH: u32 = 8;
pub(super) const MAX_STACK_ALIAS_DEPTH: u32 = 8;
pub(super) const MAX_SIMPLE_EXPR_DEPTH: u32 = 2;
pub(super) const MAX_RETURN_INLINE_DEPTH: u32 = 8;
pub(super) const MAX_RETURN_INLINE_CANDIDATE_DEPTH: u32 = 5;
pub(super) const MAX_RETURN_EXPR_DEPTH: u32 = 8;
pub(super) const MAX_ALIAS_REWRITE_DEPTH: u32 = 32;
pub(super) const MAX_COND_STACK_ALIAS_DEPTH: u32 = 8;
pub(super) const MAX_PREDICATE_SIMPLIFY_DEPTH: u32 = 6;
pub(super) const MAX_PREDICATE_OPERAND_DEPTH: u32 = 12;
pub(super) const MAX_SF_SURROGATE_DEPTH: usize = 128;
pub(super) const MAX_SUB_LIKE_DEPTH: usize = 128;

/// Lower a sequence of SSA operations to C statements using fold lowering.
///
/// This helper is intentionally stateless and uses default fold context
/// configuration, matching block-level lowering behavior used by the plugin.
pub fn lower_ssa_ops_to_stmts(ptr_size: u32, ops: &[SSAOp]) -> Vec<CStmt> {
    let ctx = FoldingContext::new(ptr_size);
    ops.iter().filter_map(|op| ctx.op_to_stmt(op)).collect()
}
