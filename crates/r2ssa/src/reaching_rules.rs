//! The rule both backward walks over a register's definitions obey.
//!
//! Two passes ask what value reaches a function's return register.
//! `liveout::FunctionLiveOut` asks it to recover the interface, before any
//! machine context exists; `semantic::reaching_abi_return_register_in_block`
//! asks it again at the return boundary, with one. Asking twice is not the
//! problem -- an interface recovered without a machine context and a boundary
//! checked with one are genuinely different questions about different inputs.
//!
//! Answering with two different rules is. The two disagreed, and the weaker
//! answer fed the recovered interface: the liveout walk read only each
//! operation's destination and so passed straight through a call, naming
//! whatever had been put in the register before it. For a function whose last
//! act is `warnx(fmt, ...)` that is the format string, recovered as the value
//! the function returns. Nothing rendered it only because the stricter walk
//! refused the boundary afterwards, which is luck rather than design.
//!
//! So the rule lives here, once, and both walks call it while keeping their own
//! traversals. That is the same arrangement the binding plan's construction and
//! seal already use, and for the same reason: two independent derivations of
//! one answer are a cross-check, two independently written statements of one
//! rule are two answerers that drift.

use crate::op::SSAOp;

/// Whether an operation overwrites the register a backward search is following.
///
/// A call owns the result register. The convention names the same register for
/// a callee's result and for its caller's, so a call reached walking backwards
/// has overwritten what came before it, and its predecessors cannot answer
/// either -- they run before the call. A user operation is opaque and may write
/// anything, which is the same situation without a convention to appeal to.
///
/// Two operations are deliberately not here, and both were in one of the two
/// walks before this rule was shared.
///
/// `Return` is a boundary, not a writer. Each walk already knows where its own
/// boundary is -- the return-boundary walk slices the operations before it, the
/// liveout walk starts at the returning block's last operation, which *is* the
/// return -- so treating it as a stop made the liveout walk halt on its own
/// starting point and find nothing at all.
///
/// `CallDefine` is the operation that gives a call's result a name, so it *is*
/// the definition a walk is looking for. Stopping on it refuses to see the
/// value a function returning `f(x)` hands back.
pub(crate) const fn op_ends_reaching_walk(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::CallOther { .. }
    )
}
