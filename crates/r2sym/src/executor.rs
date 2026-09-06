//! Symbolic executor for SSA operations.
//!
//! This module implements the core symbolic execution logic,
//! stepping through SSA operations and updating state.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use r2il::SpaceId;
use r2ssa::{CanonicalStorageSpace, FunctionSSABlock, SSAOp, SSAVar};
use z3::Context;
use z3::ast::BV;

use crate::SymResult;
use crate::control::SymExecutionControl;
use crate::state::{ExitStatus, RuntimeValueProvenance, SymState};
use crate::value::SymValue;

/// Result of a call hook.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallHookResult {
    /// Continue execution (fallthrough).
    Fallthrough,
    /// Jump to a new program counter.
    Jump(u64),
    /// Terminate the state.
    Terminate(ExitStatus),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// The shared prefix is the point: these name Windows API entry points, and
// dropping it would leave variants like `RaiseException` that read as ours.
#[allow(clippy::enum_variant_names)]
pub enum CallHookTag {
    WindowsAddVectoredExceptionHandler,
    WindowsRaiseException,
    WindowsVirtualAlloc,
    WindowsVirtualProtect,
    WindowsHeapAlloc,
}

/// A call hook for intercepting direct calls.
pub type CallHook<'ctx> = Box<dyn Fn(&mut SymState<'ctx>) -> SymResult<CallHookResult> + 'ctx>;

fn block_execution_should_stop(
    op: &SSAOp,
    generation_before_op: u64,
    generation_after_op: u64,
) -> bool {
    match op {
        SSAOp::Branch { .. } | SSAOp::BranchInd { .. } | SSAOp::Return { .. } => true,
        SSAOp::CBranch { .. } | SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
            generation_after_op != generation_before_op
        }
        _ => false,
    }
}

fn zero_equality_from_known_facts<'ctx>(
    state: &SymState<'ctx>,
    lhs: &SymValue<'ctx>,
    rhs: &SymValue<'ctx>,
) -> Option<bool> {
    if rhs.as_concrete() == Some(0) {
        if state.value_known_zero(lhs) {
            return Some(true);
        }
        if state.value_known_nonzero(lhs) {
            return Some(false);
        }
    }
    if lhs.as_concrete() == Some(0) {
        if state.value_known_zero(rhs) {
            return Some(true);
        }
        if state.value_known_nonzero(rhs) {
            return Some(false);
        }
    }
    None
}

fn require_ram_memory_space(state: &mut SymState<'_>, space: SpaceId) -> bool {
    if space == SpaceId::Ram {
        true
    } else {
        state.terminate(ExitStatus::Unimplemented);
        false
    }
}

struct RegisteredCallHook<'ctx> {
    tag: Option<CallHookTag>,
    hook: CallHook<'ctx>,
}

/// Symbolic executor for SSA functions.
pub struct SymExecutor<'ctx> {
    /// The Z3 context.
    ctx: &'ctx Context,
    /// Registered call hooks (address -> handler).
    call_hooks: HashMap<u64, RegisteredCallHook<'ctx>>,
    /// Direct-call targets that should be forked as interprocedural successors.
    direct_call_fork_targets: Option<HashSet<u64>>,
    /// Cooperative request control polled by executor worklists.
    execution: SymExecutionControl,
}

struct ConcreteCopyLoopPlan<'a> {
    counter_phi: &'a SSAVar,
    src_base: u64,
    dst_base: u64,
    limit: u64,
}

impl<'ctx> SymExecutor<'ctx> {
    /// Create a new symbolic executor.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self::with_execution_control(ctx, SymExecutionControl::default())
    }

    /// Create an executor with cooperative cancellation and deadline control.
    pub fn with_execution_control(ctx: &'ctx Context, execution: SymExecutionControl) -> Self {
        Self {
            ctx,
            call_hooks: HashMap::new(),
            direct_call_fork_targets: None,
            execution,
        }
    }

    /// Replace the direct-call fork target whitelist and return the previous value.
    pub fn replace_direct_call_fork_targets(
        &mut self,
        targets: Option<HashSet<u64>>,
    ) -> Option<HashSet<u64>> {
        std::mem::replace(&mut self.direct_call_fork_targets, targets)
    }

    /// Register a call hook for a target address.
    pub fn register_call_hook<F>(&mut self, addr: u64, hook: F)
    where
        F: Fn(&mut SymState<'ctx>) -> SymResult<CallHookResult> + 'ctx,
    {
        self.call_hooks.insert(
            addr,
            RegisteredCallHook {
                tag: None,
                hook: Box::new(hook),
            },
        );
    }

    pub fn register_tagged_call_hook<F>(&mut self, addr: u64, tag: CallHookTag, hook: F)
    where
        F: Fn(&mut SymState<'ctx>) -> SymResult<CallHookResult> + 'ctx,
    {
        self.call_hooks.insert(
            addr,
            RegisteredCallHook {
                tag: Some(tag),
                hook: Box::new(hook),
            },
        );
    }

    pub fn call_hook_tag(&self, addr: u64) -> Option<CallHookTag> {
        self.call_hooks.get(&addr).and_then(|binding| binding.tag)
    }

    /// Execute a single SSA operation on the given state.
    ///
    /// Returns a list of successor states (multiple for branches).
    pub fn step(&self, state: &mut SymState<'ctx>, op: &SSAOp) -> SymResult<Vec<SymState<'ctx>>> {
        use SSAOp::*;

        match op {
            // ==================== Data Movement ====================
            Copy { dst, src } => {
                let carrier = self.read_var_carrier(state, src);
                self.write_var(state, dst, carrier.value);
                self.propagate_var_provenance(state, dst, carrier.provenance);
                Ok(vec![])
            }

            Select {
                dst,
                cond,
                if_true,
                if_false,
            } => {
                let cond_value = self.read_var(state, cond);
                let true_carrier = self.read_var_carrier(state, if_true);
                let false_carrier = self.read_var_carrier(state, if_false);
                let true_value = true_carrier.value;
                let false_value = false_carrier.value;
                let value = if let Some(concrete) = cond_value.as_concrete() {
                    if concrete != 0 {
                        true_value.clone()
                    } else {
                        false_value.clone()
                    }
                } else {
                    let cond_bv = cond_value.to_bv(self.ctx);
                    let zero = BV::from_i64(0, cond_value.bits());
                    let cond_bool = cond_bv.eq(&zero).not();
                    let merged =
                        cond_bool.ite(&true_value.to_bv(self.ctx), &false_value.to_bv(self.ctx));
                    SymValue::symbolic_tainted(
                        merged,
                        true_value.bits(),
                        true_value.get_taint() | false_value.get_taint(),
                    )
                };
                self.write_var(state, dst, value);
                let provenance = if let Some(concrete) = cond_value.as_concrete() {
                    if concrete != 0 {
                        true_carrier.provenance
                    } else {
                        false_carrier.provenance
                    }
                } else {
                    let true_provenance = true_carrier.provenance;
                    let false_provenance = false_carrier.provenance;
                    (true_provenance == false_provenance)
                        .then_some(true_provenance)
                        .flatten()
                };
                self.propagate_var_provenance(state, dst, provenance);
                Ok(vec![])
            }

            CallDefine { dst } => {
                let value = SymValue::new_symbolic(
                    self.ctx,
                    &format!("calldef_{}", dst.display_name()),
                    dst.size * 8,
                );
                self.write_var(state, dst, value);
                Ok(vec![])
            }

            // The callee handed this carrier back unchanged, so the value is
            // the one the caller had. That is a copy, and it carries the
            // provenance with it: the whole point of the operation is that the
            // stack pointer after a call still addresses the caller's frame.
            CallRestore { dst, src } => {
                let carrier = self.read_var_carrier(state, src);
                self.write_var(state, dst, carrier.value);
                self.propagate_var_provenance(state, dst, carrier.provenance);
                Ok(vec![])
            }

            Load { dst, addr, space } => {
                if !require_ram_memory_space(state, *space) {
                    return Ok(vec![]);
                }
                let addr_val = self.read_var(state, addr);
                let size = dst.size;
                let value = state.mem_read(&addr_val, size);
                self.write_var(state, dst, value);
                let provenance = addr_val
                    .as_concrete()
                    .map(|source_addr| RuntimeValueProvenance { source_addr, size });
                self.propagate_var_provenance(state, dst, provenance);
                Ok(vec![])
            }

            Store { addr, val, space } => {
                if !require_ram_memory_space(state, *space) {
                    return Ok(vec![]);
                }
                let addr_val = self.read_var(state, addr);
                let carrier = self.read_var_carrier(state, val);
                let size = val.size;
                state.mem_write(&addr_val, &carrier.value, size);
                if let Some(store_addr) = addr_val.as_concrete() {
                    state.note_runtime_store_copy(store_addr, size, carrier.provenance.as_ref());
                }
                Ok(vec![])
            }
            Fence { .. } => Ok(vec![]),
            LoadLinked {
                dst: _,
                addr: _,
                space: _,
                ordering: _,
            } => {
                // Reservation and interference are part of LL/SC semantics.
                // An ordinary load would fabricate success possibilities.
                state.terminate(ExitStatus::Unimplemented);
                Ok(vec![])
            }
            StoreConditional {
                result: _,
                addr: _,
                val: _,
                space: _,
                ordering: _,
            } => {
                state.terminate(ExitStatus::Unimplemented);
                Ok(vec![])
            }
            AtomicCAS {
                dst,
                addr,
                expected,
                replacement,
                space,
                ordering: _,
            } => {
                if !require_ram_memory_space(state, *space) {
                    return Ok(vec![]);
                }
                let addr_val = self.read_var(state, addr);
                let expected_val = self.read_var(state, expected);
                let replacement_val = self.read_var(state, replacement);
                let old_val = state.mem_read(&addr_val, dst.size);
                let cond = old_val.eq(self.ctx, &expected_val);
                let new_val = if let Some(v) = cond.as_concrete() {
                    if v != 0 {
                        replacement_val.clone()
                    } else {
                        old_val.clone()
                    }
                } else {
                    let cond_bv = cond.to_bv(self.ctx);
                    let zero = BV::from_i64(0, cond.bits());
                    let cond_bool = cond_bv.eq(&zero).not();
                    let old_bv = old_val.to_bv(self.ctx);
                    let repl_bv = replacement_val.to_bv(self.ctx);
                    let merged = cond_bool.ite(&repl_bv, &old_bv);
                    SymValue::symbolic(merged, old_val.bits())
                };
                state.mem_write(&addr_val, &new_val, dst.size);
                self.write_var(state, dst, old_val);
                Ok(vec![])
            }
            LoadGuarded {
                dst,
                addr,
                guard,
                space,
                ordering: _,
            } => {
                if !require_ram_memory_space(state, *space) {
                    return Ok(vec![]);
                }
                let addr_val = self.read_var(state, addr);
                let guard_val = self.read_var(state, guard);
                let loaded = state.mem_read(&addr_val, dst.size);
                let result = if let Some(g) = guard_val.as_concrete() {
                    if g != 0 {
                        loaded
                    } else {
                        SymValue::unknown(dst.size.saturating_mul(8))
                    }
                } else {
                    let cond_bv = guard_val.to_bv(self.ctx);
                    let zero = BV::from_i64(0, guard_val.bits());
                    let cond_bool = cond_bv.eq(&zero).not();
                    let loaded_bv = loaded.to_bv(self.ctx);
                    let fallback = SymValue::unknown(dst.size.saturating_mul(8));
                    let fallback_bv = fallback.to_bv(self.ctx);
                    let merged = cond_bool.ite(&loaded_bv, &fallback_bv);
                    SymValue::symbolic(merged, loaded.bits())
                };
                self.write_var(state, dst, result);
                Ok(vec![])
            }
            StoreGuarded {
                addr,
                val,
                guard,
                space,
                ordering: _,
            } => {
                if !require_ram_memory_space(state, *space) {
                    return Ok(vec![]);
                }
                let addr_val = self.read_var(state, addr);
                let value = self.read_var(state, val);
                let guard_val = self.read_var(state, guard);
                let size = val.size;
                if let Some(g) = guard_val.as_concrete() {
                    if g != 0 {
                        state.mem_write(&addr_val, &value, size);
                    }
                } else {
                    let old_val = state.mem_read(&addr_val, size);
                    let cond_bv = guard_val.to_bv(self.ctx);
                    let zero = BV::from_i64(0, guard_val.bits());
                    let cond_bool = cond_bv.eq(&zero).not();
                    let old_bv = old_val.to_bv(self.ctx);
                    let new_bv = value.to_bv(self.ctx);
                    let merged = cond_bool.ite(&new_bv, &old_bv);
                    let merged_val = SymValue::symbolic(merged, old_val.bits());
                    state.mem_write(&addr_val, &merged_val, size);
                }
                Ok(vec![])
            }

            // ==================== Integer Arithmetic ====================
            IntAdd { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.add(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSub { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.sub(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntMult { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.mul(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntDiv { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.udiv(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSDiv { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.sdiv(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntRem { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.urem(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSRem { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.srem(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntNegate { dst, src } => {
                let val = self.read_var(state, src);
                let result = val.neg(self.ctx);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntCarry { dst, a, b } => {
                // Carry flag: result < a (unsigned overflow)
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let sum = a_val.add(self.ctx, &b_val);
                let carry = sum.ult(self.ctx, &a_val);
                self.write_var(state, dst, carry);
                Ok(vec![])
            }

            IntSCarry { dst, a, b } => {
                // Signed carry (overflow)
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                // Signed overflow occurs when signs of operands are same but result sign differs
                let a_bits = a_val.bits().max(1);
                let b_bits = b_val.bits().max(1);
                let (a_bv, b_bv, bits) = if a_bits == b_bits {
                    (a_val.to_bv(self.ctx), b_val.to_bv(self.ctx), a_bits)
                } else if a_bits > b_bits {
                    (
                        a_val.to_bv(self.ctx),
                        b_val.to_bv(self.ctx).sign_ext(a_bits - b_bits),
                        a_bits,
                    )
                } else {
                    (
                        a_val.to_bv(self.ctx).sign_ext(b_bits - a_bits),
                        b_val.to_bv(self.ctx),
                        b_bits,
                    )
                };
                let sum_bv = a_bv.bvadd(&b_bv);
                let a_sign = a_bv.extract(bits - 1, bits - 1);
                let b_sign = b_bv.extract(bits - 1, bits - 1);
                let sum_sign = sum_bv.extract(bits - 1, bits - 1);
                let same_signs = a_sign.eq(&b_sign);
                let diff_result = a_sign.eq(&sum_sign).not();
                let overflow = same_signs & diff_result;
                let one = BV::from_i64(1, 1);
                let zero = BV::from_i64(0, 1);
                let result = SymValue::symbolic(overflow.ite(&one, &zero), 1);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSBorrow { dst, a, b } => {
                // Signed borrow
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let a_bits = a_val.bits().max(1);
                let b_bits = b_val.bits().max(1);
                let (a_bv, b_bv, bits) = if a_bits == b_bits {
                    (a_val.to_bv(self.ctx), b_val.to_bv(self.ctx), a_bits)
                } else if a_bits > b_bits {
                    (
                        a_val.to_bv(self.ctx),
                        b_val.to_bv(self.ctx).sign_ext(a_bits - b_bits),
                        a_bits,
                    )
                } else {
                    (
                        a_val.to_bv(self.ctx).sign_ext(b_bits - a_bits),
                        b_val.to_bv(self.ctx),
                        b_bits,
                    )
                };
                let diff_bv = a_bv.bvsub(&b_bv);
                let a_sign = a_bv.extract(bits - 1, bits - 1);
                let b_sign = b_bv.extract(bits - 1, bits - 1);
                let diff_sign = diff_bv.extract(bits - 1, bits - 1);
                let diff_signs = a_sign.eq(&b_sign).not();
                let diff_result = a_sign.eq(&diff_sign).not();
                let borrow = diff_signs & diff_result;
                let one = BV::from_i64(1, 1);
                let zero = BV::from_i64(0, 1);
                let result = SymValue::symbolic(borrow.ite(&one, &zero), 1);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            // ==================== Bitwise Operations ====================
            IntAnd { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.and(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntOr { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.or(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntXor { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.xor(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntNot { dst, src } => {
                let val = self.read_var(state, src);
                let result = val.not(self.ctx);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            // ==================== Shift Operations ====================
            IntLeft { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.shl(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntRight { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.lshr(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSRight { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.ashr(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            // ==================== Comparison Operations ====================
            IntEqual { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result =
                    if let Some(equal) = zero_equality_from_known_facts(state, &a_val, &b_val) {
                        SymValue::concrete(if equal { 1 } else { 0 }, 1)
                    } else {
                        a_val.eq(self.ctx, &b_val)
                    };
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntNotEqual { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let eq = if let Some(equal) = zero_equality_from_known_facts(state, &a_val, &b_val)
                {
                    SymValue::concrete(if equal { 1 } else { 0 }, 1)
                } else {
                    a_val.eq(self.ctx, &b_val)
                };
                // NOT of equality
                let result = match eq.as_concrete() {
                    Some(v) => SymValue::concrete(if v == 0 { 1 } else { 0 }, 1),
                    None => {
                        let bv = eq.to_bv(self.ctx);
                        let zero = BV::from_i64(0, 1);
                        let one = BV::from_i64(1, 1);
                        let is_zero = bv.eq(&zero);
                        SymValue::symbolic(is_zero.ite(&one, &zero), 1)
                    }
                };
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntLess { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.ult(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSLess { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.slt(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntLessEqual { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.ule(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSLessEqual { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.sle(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            // ==================== Extension Operations ====================
            IntZExt { dst, src } => {
                let carrier = self.read_var_carrier(state, src);
                let result = carrier.value.zero_extend(self.ctx, dst.size * 8);
                self.write_var(state, dst, result);
                self.propagate_var_provenance(state, dst, carrier.provenance);
                Ok(vec![])
            }

            IntSExt { dst, src } => {
                let carrier = self.read_var_carrier(state, src);
                let result = carrier.value.sign_extend(self.ctx, dst.size * 8);
                self.write_var(state, dst, result);
                self.propagate_var_provenance(state, dst, carrier.provenance);
                Ok(vec![])
            }

            // ==================== Boolean Operations ====================
            BoolNot { dst, src } => {
                let val = self.read_var(state, src);
                let result = val.bool_not(self.ctx);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            BoolAnd { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.and(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            BoolOr { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.or(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            BoolXor { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let result = a_val.xor(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            // ==================== Bit Manipulation ====================
            Piece { dst, hi, lo } => {
                let hi_val = self.read_var(state, hi);
                let lo_val = self.read_var(state, lo);
                let result = hi_val.concat(self.ctx, &lo_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            Subpiece { dst, src, offset } => {
                let carrier = self.read_var_carrier(state, src);
                let val = carrier.value;
                let low = offset.saturating_mul(8);
                let dst_bits = dst.size.saturating_mul(8).max(8);
                let src_bits = val.bits().max(1);
                let result = if low >= src_bits {
                    SymValue::unknown(dst_bits)
                } else {
                    let high = low
                        .saturating_add(dst_bits.saturating_sub(1))
                        .min(src_bits.saturating_sub(1));
                    let extracted = val.extract(self.ctx, high, low);
                    if extracted.bits() < dst_bits {
                        extracted.zero_extend(self.ctx, dst_bits)
                    } else {
                        extracted
                    }
                };
                self.write_var(state, dst, result);
                let provenance = if *offset == 0 {
                    carrier.provenance
                } else {
                    None
                };
                self.propagate_var_provenance(state, dst, provenance);
                Ok(vec![])
            }

            PopCount { dst, src } => {
                // Population count - count set bits
                let val = self.read_var(state, src);
                if let Some(v) = val.as_concrete() {
                    let count = v.count_ones() as u64;
                    self.write_var(state, dst, SymValue::concrete(count, dst.size * 8));
                } else {
                    // Symbolic popcount - create fresh symbolic
                    let result = SymValue::new_symbolic(self.ctx, "popcount", dst.size * 8);
                    self.write_var(state, dst, result);
                }
                Ok(vec![])
            }

            Lzcount { dst, src } => {
                // Leading zero count
                let val = self.read_var(state, src);
                if let Some(v) = val.as_concrete() {
                    let bits = val.bits();
                    let count = if bits >= 64 {
                        v.leading_zeros() as u64
                    } else {
                        let mask = (1u64 << bits) - 1;
                        let masked = v & mask;
                        if masked == 0 {
                            bits as u64
                        } else {
                            let used = 64 - masked.leading_zeros();
                            (bits - used) as u64
                        }
                    };
                    self.write_var(state, dst, SymValue::concrete(count, dst.size * 8));
                } else {
                    let result = SymValue::new_symbolic(self.ctx, "lzcount", dst.size * 8);
                    self.write_var(state, dst, result);
                }
                Ok(vec![])
            }

            // ==================== Control Flow ====================
            Branch { target } => {
                let target_val = self.read_control_target_var(state, target);
                if let Some(addr) = target_val.as_concrete() {
                    state.set_static_execution_pc(addr);
                } else {
                    state.terminate(ExitStatus::Error(
                        "Unresolved direct branch target".to_string(),
                    ));
                }
                Ok(vec![])
            }

            CBranch { target, cond } => {
                let target_val = self.read_control_target_var(state, target);
                let cond_val = self.read_var(state, cond);
                let Some(target_addr) = target_val.as_concrete() else {
                    state.terminate(ExitStatus::Error(
                        "Unresolved direct conditional branch target".to_string(),
                    ));
                    return Ok(vec![]);
                };

                // Check if condition is concrete
                if let Some(c) = cond_val.as_concrete() {
                    if c != 0 {
                        // Branch taken
                        state.set_static_execution_pc(target_addr);
                    }
                    // If c == 0, fall through (don't change PC)
                    Ok(vec![])
                } else if state.value_known_nonzero(&cond_val) {
                    state.set_static_execution_pc(target_addr);
                    Ok(vec![])
                } else if state.value_known_zero(&cond_val) {
                    Ok(vec![])
                } else {
                    // Symbolic condition - fork execution
                    // Create true branch state
                    let mut true_state = state.fork();
                    true_state.add_true_constraint(&cond_val);
                    true_state.set_static_execution_pc(target_addr);

                    // Current state becomes false branch
                    state.add_false_constraint(&cond_val);

                    Ok(vec![true_state])
                }
            }

            BranchInd { target } => {
                let target_val = self.read_control_target_var(state, target);
                if let Some(addr) = target_val.as_concrete() {
                    self.set_indirect_execution_pc(state, addr);
                } else {
                    // Indirect branch with symbolic target - terminate
                    state.terminate(ExitStatus::Error("Symbolic indirect branch".to_string()));
                }
                Ok(vec![])
            }

            Call { target } => {
                let target_val = self.read_control_target_var(state, target);
                if let Some(addr) = target_val.as_concrete() {
                    if let Some(binding) = self.call_hooks.get(&addr) {
                        match (binding.hook)(state)? {
                            CallHookResult::Fallthrough => {}
                            CallHookResult::Jump(new_pc) => {
                                self.set_indirect_execution_pc(state, new_pc)
                            }
                            CallHookResult::Terminate(status) => state.terminate(status),
                        }
                    } else if self
                        .direct_call_fork_targets
                        .as_ref()
                        .is_some_and(|targets| targets.contains(&addr))
                    {
                        let mut call_state = state.fork();
                        call_state.set_static_execution_pc(addr);
                        return Ok(vec![call_state]);
                    }
                }
                Ok(vec![])
            }

            CallInd { target } => {
                let target_carrier = self.read_control_target_carrier(state, target);
                if let Some(addr) = target_carrier.value.as_concrete() {
                    let provenance_addr = target_carrier
                        .provenance
                        .map(|provenance| provenance.source_addr);
                    if let Some(binding) = self
                        .call_hooks
                        .get(&addr)
                        .or_else(|| provenance_addr.and_then(|slot| self.call_hooks.get(&slot)))
                    {
                        match (binding.hook)(state)? {
                            CallHookResult::Fallthrough => {}
                            CallHookResult::Jump(new_pc) => {
                                self.set_indirect_execution_pc(state, new_pc)
                            }
                            CallHookResult::Terminate(status) => state.terminate(status),
                        }
                    } else {
                        // Fallthrough for direct known calls inside a function.
                    }
                } else {
                    state.terminate(ExitStatus::Error("Symbolic indirect call".to_string()));
                }
                Ok(vec![])
            }

            Return { target: _ } => {
                match state.resume_pending_exception_continuation() {
                    Ok(Some(resume_pc)) => self.set_indirect_execution_pc(state, resume_pc),
                    Ok(None) => state.terminate(ExitStatus::Return),
                    Err(reason) => state.terminate(ExitStatus::RuntimeBlocked(reason)),
                }
                Ok(vec![])
            }

            // ==================== Phi Nodes ====================
            Phi { .. } => Err(crate::SymError::UnsupportedOp(
                "phi execution requires an exact predecessor".to_string(),
            )),

            // ==================== Special Operations ====================
            Nop => Ok(vec![]),

            Unimplemented => {
                state.terminate(ExitStatus::Unimplemented);
                Ok(vec![])
            }

            Breakpoint => {
                state.terminate(ExitStatus::Error("Breakpoint".to_string()));
                Ok(vec![])
            }

            CpuId { dst } => {
                // Return symbolic CPUID result
                let result = SymValue::new_symbolic(self.ctx, "cpuid", dst.size * 8);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            CallOther { .. } => {
                // Without a source-owned effect contract, a userop may read or write
                // hidden architectural state, memory, or control state. Continuing
                // with only an unconstrained result would incorrectly assume purity.
                state.terminate(ExitStatus::Unimplemented);
                Ok(vec![])
            }

            PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => {
                let base_val = self.read_var(state, base);
                let index_val = self.read_var(state, index);
                let size_val = SymValue::concrete(*element_size as u64, index_val.bits());
                let offset = index_val.mul(self.ctx, &size_val);
                let result = base_val.add(self.ctx, &offset);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            PtrSub {
                dst,
                base,
                index,
                element_size,
            } => {
                let base_val = self.read_var(state, base);
                let index_val = self.read_var(state, index);
                let size_val = SymValue::concrete(*element_size as u64, index_val.bits());
                let offset = index_val.mul(self.ctx, &size_val);
                let result = base_val.sub(self.ctx, &offset);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            SegmentOp {
                dst,
                segment: _,
                offset,
            } => {
                // Simplified: just use offset
                let val = self.read_var(state, offset);
                self.write_var(state, dst, val);
                Ok(vec![])
            }

            New { dst, src: _ } => {
                // Allocation - return symbolic pointer
                let result = SymValue::new_symbolic(self.ctx, "alloc", dst.size * 8);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            Cast { dst, src } => {
                let carrier = self.read_var_carrier(state, src);
                let val = carrier.value;
                let dst_bits = dst.size.saturating_mul(8).max(1);
                let result = if dst_bits > val.bits() {
                    val.zero_extend(self.ctx, dst_bits)
                } else if dst_bits < val.bits() {
                    val.extract(self.ctx, dst_bits - 1, 0)
                } else {
                    val
                };
                self.write_var(state, dst, result);
                self.propagate_var_provenance(state, dst, carrier.provenance);
                Ok(vec![])
            }

            Extract { dst, src, position } => {
                let val = self.read_var(state, src);
                let pos = self.read_var(state, position);
                if let Some(p) = pos.as_concrete() {
                    let low = p as u32;
                    let dst_bits = dst.size.saturating_mul(8).max(1);
                    let src_bits = val.bits().max(1);
                    let result = if low >= src_bits {
                        SymValue::unknown(dst_bits)
                    } else {
                        let high = low
                            .saturating_add(dst_bits.saturating_sub(1))
                            .min(src_bits.saturating_sub(1));
                        let extracted = val.extract(self.ctx, high, low);
                        if extracted.bits() < dst_bits {
                            extracted.zero_extend(self.ctx, dst_bits)
                        } else {
                            extracted
                        }
                    };
                    self.write_var(state, dst, result);
                } else {
                    // Symbolic position - return symbolic
                    let result = SymValue::new_symbolic(self.ctx, "extract", dst.size * 8);
                    self.write_var(state, dst, result);
                }
                Ok(vec![])
            }

            Insert {
                dst,
                src,
                value: _,
                position: _,
            } => {
                // Bit field insertion - simplified
                let src_val = self.read_var(state, src);
                self.write_var(state, dst, src_val);
                Ok(vec![])
            }

            // Floating point operations - return symbolic for now
            FloatAdd { dst, .. }
            | FloatSub { dst, .. }
            | FloatMult { dst, .. }
            | FloatDiv { dst, .. }
            | FloatNeg { dst, .. }
            | FloatAbs { dst, .. }
            | FloatSqrt { dst, .. }
            | FloatCeil { dst, .. }
            | FloatFloor { dst, .. }
            | FloatRound { dst, .. }
            | FloatNaN { dst, .. }
            | FloatEqual { dst, .. }
            | FloatNotEqual { dst, .. }
            | FloatLess { dst, .. }
            | FloatLessEqual { dst, .. }
            | Int2Float { dst, .. }
            | Float2Int { dst, .. }
            | FloatFloat { dst, .. }
            | Trunc { dst, .. } => {
                let result = SymValue::new_symbolic(self.ctx, "float_op", dst.size * 8);
                self.write_var(state, dst, result);
                Ok(vec![])
            }
        }
    }

    /// Read an SSA variable from state.
    fn read_var(&self, state: &SymState<'ctx>, var: &SSAVar) -> SymValue<'ctx> {
        self.read_var_carrier(state, var).value
    }

    fn read_var_carrier(&self, state: &SymState<'ctx>, var: &SSAVar) -> ResolvedVarCarrier<'ctx> {
        if let Some(value) = var.constant_bits() {
            ResolvedVarCarrier {
                value: SymValue::concrete(value, var.size * 8),
                provenance: None,
            }
        } else if var.is_const() {
            ResolvedVarCarrier {
                value: self.stable_unknown_var(var),
                provenance: None,
            }
        } else if let Some(hex) = var.name.strip_prefix("ram:") {
            if let Ok(value) = u64::from_str_radix(hex, 16) {
                ResolvedVarCarrier {
                    value: state.mem_read(&SymValue::concrete(value, 64), var.size),
                    provenance: Some(RuntimeValueProvenance {
                        source_addr: value,
                        size: var.size,
                    }),
                }
            } else {
                ResolvedVarCarrier {
                    value: self.stable_unknown_var(var),
                    provenance: None,
                }
            }
        } else {
            let key = var.display_name();
            if let Some(value) = state.registers().get(&key).cloned() {
                return ResolvedVarCarrier {
                    value,
                    provenance: state
                        .value_provenance(&key)
                        .filter(|provenance| provenance.size == var.size)
                        .cloned(),
                };
            }
            if let Some(carrier) = resolve_alias_register_carrier(state, &key, self.ctx) {
                return carrier;
            }
            ResolvedVarCarrier {
                value: self.stable_unknown_var(var),
                provenance: None,
            }
        }
    }

    fn stable_unknown_var(&self, var: &SSAVar) -> SymValue<'ctx> {
        let encoded_name = var
            .name
            .as_bytes()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        SymValue::new_symbolic(
            self.ctx,
            &format!("unknown_ssa_n{encoded_name}_v{}_s{}", var.version, var.size),
            var.size.saturating_mul(8),
        )
    }

    fn read_control_target_var(&self, state: &SymState<'ctx>, var: &SSAVar) -> SymValue<'ctx> {
        self.read_control_target_carrier(state, var).value
    }

    fn read_control_target_carrier(
        &self,
        state: &SymState<'ctx>,
        var: &SSAVar,
    ) -> ResolvedVarCarrier<'ctx> {
        if let Some(addr) = parse_address_literal(var) {
            ResolvedVarCarrier {
                value: SymValue::concrete(addr, var.size * 8),
                provenance: None,
            }
        } else {
            self.read_var_carrier(state, var)
        }
    }

    fn set_indirect_execution_pc(&self, state: &mut SymState<'ctx>, pc: u64) {
        state.set_unresolved_indirect_execution_pc(pc);
    }

    /// Write an SSA variable to state.
    fn write_var(&self, state: &mut SymState<'ctx>, var: &SSAVar, value: SymValue<'ctx>) {
        if let Some(addr) = parse_ram_addr(var) {
            state.mem_write(&SymValue::concrete(addr, 64), &value, var.size);
            return;
        }
        let key = var.display_name();
        state.set_register(&key, value.clone());
        state.set_value_provenance(&key, None);
        if let Some((base, version)) = split_versioned_register(&key)
            && let Some(spec) = x86_register_alias_spec(base)
            && spec.offset_bits == 0
            && spec.width_bits == 32
            && var.size.checked_mul(8) == Some(32)
            && value.bits() == 32
            && spec.family.as_ref() != base
        {
            let family_key = format!("{}_{}", spec.family, version);
            state.set_register(&family_key, value.zero_extend(self.ctx, 64));
            state.set_value_provenance(&family_key, None);
        }
    }

    fn propagate_var_provenance(
        &self,
        state: &mut SymState<'ctx>,
        var: &SSAVar,
        provenance: Option<RuntimeValueProvenance>,
    ) {
        let key = var.display_name();
        state.set_value_provenance(&key, provenance);
    }

    #[cfg(test)]
    fn read_var_provenance(
        &self,
        state: &SymState<'ctx>,
        var: &SSAVar,
    ) -> Option<RuntimeValueProvenance> {
        self.read_var_carrier(state, var).provenance
    }

    /// Execute a block of SSA operations.
    pub fn execute_block(
        &self,
        state: &mut SymState<'ctx>,
        block: &FunctionSSABlock,
    ) -> SymResult<Vec<SymState<'ctx>>> {
        self.execution.poll()?;
        let mut forked_states = Vec::new();
        let incoming = (!block.phis.is_empty())
            .then(|| {
                state
                    .predecessor()
                    .map(|predecessor| predecessor.static_addr())
            })
            .flatten();
        if phi_destinations_overlap(block) {
            return Err(crate::SymError::UnsupportedOp(format!(
                "phi destinations at 0x{:x} overlap canonical storage",
                block.addr
            )));
        }

        // Resolve every Phi against the same predecessor state before any
        // destination or register-family alias is mutated.
        let mut resolved_phis = Vec::with_capacity(block.phis.len());
        for phi in &block.phis {
            self.execution.poll()?;
            // In single-path execution, we need to know which predecessor we came from
            let predecessor = incoming.ok_or_else(|| {
                crate::SymError::UnsupportedOp(format!(
                    "phi at 0x{:x} has no execution predecessor",
                    block.addr
                ))
            })?;
            let mut sources = phi.sources.iter().filter(|(pred, _)| *pred == predecessor);
            let src = sources.next().map(|(_, src)| src).ok_or_else(|| {
                crate::SymError::UnsupportedOp(format!(
                    "phi at 0x{:x} has no source for predecessor 0x{predecessor:x}",
                    block.addr
                ))
            })?;
            if sources.next().is_some() {
                return Err(crate::SymError::UnsupportedOp(format!(
                    "phi at 0x{:x} has duplicate sources for predecessor 0x{predecessor:x}",
                    block.addr
                )));
            }
            if src.size != phi.dst.size {
                return Err(crate::SymError::UnsupportedOp(format!(
                    "phi at 0x{:x} source/destination width mismatch",
                    block.addr
                )));
            }
            let carrier = self.read_var_carrier(state, src);
            resolved_phis.push((phi.dst.clone(), carrier.value, carrier.provenance));
        }
        for (dst, val, provenance) in resolved_phis {
            self.write_var(state, &dst, val);
            self.propagate_var_provenance(state, &dst, provenance);
        }

        if self
            .apply_concrete_copy_loop_runahead(state, block)
            .is_some()
        {
            // The runahead leaves the state poised for the final non-taken
            // iteration so the normal executor can materialize live-out defs.
        }
        self.execution.poll()?;

        // Execute operations
        for (op_idx, op) in block.ops.iter().enumerate() {
            self.execution.poll()?;
            if !state.active {
                break;
            }

            if self.try_merge_local_fallthrough_cbranch(state, block, op_idx, op)? {
                break;
            }

            let transfer_generation = state.control_transfer_generation();
            let new_states = self.step(state, op)?;
            forked_states.extend(new_states);
            state.step();
            if block_execution_should_stop(
                op,
                transfer_generation,
                state.control_transfer_generation(),
            ) {
                break;
            }
        }

        Ok(forked_states)
    }

    fn try_merge_local_fallthrough_cbranch(
        &self,
        state: &mut SymState<'ctx>,
        block: &FunctionSSABlock,
        op_idx: usize,
        op: &SSAOp,
    ) -> SymResult<bool> {
        let SSAOp::CBranch { target, cond } = op else {
            return Ok(false);
        };
        let Some(target_addr) = parse_address_literal(target) else {
            return Ok(false);
        };
        let block_end = block.addr.saturating_add(block.size as u64);
        if target_addr != block_end {
            return Ok(false);
        }
        let tail = &block.ops[op_idx.saturating_add(1)..];
        if tail.is_empty()
            || !tail
                .iter()
                .all(|tail_op| matches!(tail_op, SSAOp::Copy { .. }))
        {
            return Ok(false);
        }

        let cond_val = self.read_var(state, cond);
        if cond_val.as_concrete().is_some()
            || state.value_known_nonzero(&cond_val)
            || state.value_known_zero(&cond_val)
        {
            return Ok(false);
        }

        let mut skipped = state.fork();
        skipped.add_true_constraint(&cond_val);
        skipped.set_static_execution_pc(target_addr);
        skipped.step();
        for tail_op in tail {
            self.execution.poll()?;
            if let SSAOp::Copy { dst, .. } = tail_op {
                let preserved = self.read_var(state, dst);
                self.write_var(&mut skipped, dst, preserved);
            }
        }

        state.add_false_constraint(&cond_val);
        state.step();
        for tail_op in tail {
            self.execution.poll()?;
            let forked = self.step(state, tail_op)?;
            if !forked.is_empty() {
                return Err(crate::SymError::UnsupportedOp(
                    "local branch copy tail unexpectedly forked execution".to_string(),
                ));
            }
            state.step();
        }
        state.set_static_execution_pc(target_addr);

        let merged = state.merge_with(&skipped).ok_or_else(|| {
            crate::SymError::UnsupportedOp(
                "local branch states have incompatible predecessor identity".to_string(),
            )
        })?;
        *state = merged;
        Ok(true)
    }

    fn apply_concrete_copy_loop_runahead(
        &self,
        state: &mut SymState<'ctx>,
        block: &FunctionSSABlock,
    ) -> Option<()> {
        let plan = detect_concrete_copy_loop_plan(self, state, block)?;
        let counter = self
            .read_var(state, plan.counter_phi)
            .as_concrete()
            .filter(|counter| *counter < plan.limit)?;
        let bulk_count = plan.limit.saturating_sub(counter).saturating_sub(1);
        if bulk_count == 0 {
            return None;
        }

        let start_src = plan.src_base.checked_add(counter)?;
        let start_dst = plan.dst_base.checked_add(counter)?;
        for offset in 0..bulk_count {
            if self.execution.poll().is_err() {
                return None;
            }
            let src_addr = start_src.checked_add(offset)?;
            let dst_addr = start_dst.checked_add(offset)?;
            let byte = state.mem_read(&SymValue::concrete(src_addr, 64), 1);
            state.mem_write(&SymValue::concrete(dst_addr, 64), &byte, 1);
        }

        let bulk_size = u32::try_from(bulk_count).ok()?;
        state.note_runtime_store_copy(
            start_dst,
            bulk_size,
            Some(&RuntimeValueProvenance {
                source_addr: start_src,
                size: bulk_size,
            }),
        );
        state.set_concrete(
            &plan.counter_phi.display_name(),
            plan.limit.saturating_sub(1),
            plan.counter_phi.size.saturating_mul(8),
        );
        state.step_by(block.ops.len().saturating_mul(bulk_count as usize));
        Some(())
    }
}

fn detect_concrete_copy_loop_plan<'ctx, 'a>(
    executor: &SymExecutor<'ctx>,
    state: &SymState<'ctx>,
    block: &'a FunctionSSABlock,
) -> Option<ConcreteCopyLoopPlan<'a>> {
    let SSAOp::CBranch { target, cond } = block.ops.last()? else {
        return None;
    };
    let target_addr = parse_var_addr(target)?;
    if target_addr != block.addr {
        return None;
    }

    let (counter_next, limit) = find_loop_limit(block, cond)?;
    let counter_phi = find_loop_counter_phi(block, counter_next)?;
    let src_base = find_load_base(block, counter_phi)
        .and_then(|base| resolve_var_concrete(executor, state, base, block))?;
    let dst_base = find_store_base(block, counter_phi)
        .and_then(|base| resolve_var_concrete(executor, state, base, block))?;
    Some(ConcreteCopyLoopPlan {
        counter_phi,
        src_base,
        dst_base,
        limit,
    })
}

fn find_loop_limit<'a>(block: &'a FunctionSSABlock, cond: &SSAVar) -> Option<(&'a SSAVar, u64)> {
    let op = find_def(block, cond)?;
    match op {
        SSAOp::IntLess { a, b, .. } | SSAOp::IntLessEqual { a, b, .. } => {
            let limit = parse_const_u64(b)?;
            let counter_next = resolve_passthrough_var(a, block);
            Some((counter_next, limit))
        }
        _ => None,
    }
}

fn find_loop_counter_phi<'a>(
    block: &'a FunctionSSABlock,
    counter_next: &'a SSAVar,
) -> Option<&'a SSAVar> {
    block.phis.iter().find_map(|phi| {
        phi.sources
            .iter()
            .any(|(pred, src)| *pred == block.addr && var_equivalent(src, counter_next, block))
            .then_some(&phi.dst)
    })
}

fn find_load_base<'a>(block: &'a FunctionSSABlock, counter_phi: &SSAVar) -> Option<&'a SSAVar> {
    block.ops.iter().find_map(|op| match op {
        SSAOp::Load {
            dst,
            addr,
            space: SpaceId::Ram,
        } if dst.size == 1 => match_base_plus_counter(addr, counter_phi, block),
        _ => None,
    })
}

fn find_store_base<'a>(block: &'a FunctionSSABlock, counter_phi: &SSAVar) -> Option<&'a SSAVar> {
    block.ops.iter().find_map(|op| match op {
        SSAOp::Store {
            addr,
            val,
            space: SpaceId::Ram,
        } if val.size == 1 => match_base_plus_counter(addr, counter_phi, block),
        _ => None,
    })
}

fn find_def<'a>(block: &'a FunctionSSABlock, dst: &SSAVar) -> Option<&'a SSAOp> {
    block
        .ops
        .iter()
        .find(|op| op_def(op).is_some_and(|candidate| candidate == dst))
}

fn op_def(op: &SSAOp) -> Option<&SSAVar> {
    match op {
        SSAOp::Phi { dst, .. }
        | SSAOp::Copy { dst, .. }
        | SSAOp::Load { dst, .. }
        | SSAOp::LoadLinked { dst, .. }
        | SSAOp::AtomicCAS { dst, .. }
        | SSAOp::LoadGuarded { dst, .. }
        | SSAOp::IntAdd { dst, .. }
        | SSAOp::IntSub { dst, .. }
        | SSAOp::IntMult { dst, .. }
        | SSAOp::IntDiv { dst, .. }
        | SSAOp::IntSDiv { dst, .. }
        | SSAOp::IntRem { dst, .. }
        | SSAOp::IntSRem { dst, .. }
        | SSAOp::IntNegate { dst, .. }
        | SSAOp::IntCarry { dst, .. }
        | SSAOp::IntSCarry { dst, .. }
        | SSAOp::IntSBorrow { dst, .. }
        | SSAOp::IntAnd { dst, .. }
        | SSAOp::IntOr { dst, .. }
        | SSAOp::IntXor { dst, .. }
        | SSAOp::IntNot { dst, .. }
        | SSAOp::IntLeft { dst, .. }
        | SSAOp::IntRight { dst, .. }
        | SSAOp::IntSRight { dst, .. }
        | SSAOp::IntEqual { dst, .. }
        | SSAOp::IntNotEqual { dst, .. }
        | SSAOp::IntLess { dst, .. }
        | SSAOp::IntSLess { dst, .. }
        | SSAOp::IntLessEqual { dst, .. }
        | SSAOp::IntSLessEqual { dst, .. }
        | SSAOp::IntZExt { dst, .. }
        | SSAOp::IntSExt { dst, .. }
        | SSAOp::BoolNot { dst, .. }
        | SSAOp::BoolAnd { dst, .. }
        | SSAOp::BoolOr { dst, .. }
        | SSAOp::BoolXor { dst, .. }
        | SSAOp::Piece { dst, .. }
        | SSAOp::Subpiece { dst, .. }
        | SSAOp::Select { dst, .. }
        | SSAOp::PopCount { dst, .. }
        | SSAOp::Lzcount { dst, .. }
        | SSAOp::CallDefine { dst }
        | SSAOp::CallRestore { dst, .. }
        | SSAOp::FloatAdd { dst, .. }
        | SSAOp::FloatSub { dst, .. }
        | SSAOp::FloatMult { dst, .. }
        | SSAOp::FloatDiv { dst, .. }
        | SSAOp::FloatNeg { dst, .. }
        | SSAOp::FloatAbs { dst, .. }
        | SSAOp::FloatSqrt { dst, .. }
        | SSAOp::FloatCeil { dst, .. }
        | SSAOp::FloatFloor { dst, .. }
        | SSAOp::FloatRound { dst, .. }
        | SSAOp::FloatNaN { dst, .. } => Some(dst),
        SSAOp::StoreConditional {
            result: Some(dst), ..
        } => Some(dst),
        _ => None,
    }
}

fn resolve_passthrough_var<'a>(var: &'a SSAVar, block: &'a FunctionSSABlock) -> &'a SSAVar {
    match find_def(block, var) {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. }) => resolve_passthrough_var(src, block),
        _ => var,
    }
}

fn var_equivalent(var: &SSAVar, target: &SSAVar, block: &FunctionSSABlock) -> bool {
    if var == target {
        return true;
    }
    match find_def(block, var) {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. }) => var_equivalent(src, target, block),
        _ => false,
    }
}

fn var_matches_counter_term(var: &SSAVar, counter_phi: &SSAVar, block: &FunctionSSABlock) -> bool {
    if var == counter_phi {
        return true;
    }
    match find_def(block, var) {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. }) => var_matches_counter_term(src, counter_phi, block),
        Some(SSAOp::IntMult { a, b, .. }) => {
            (parse_const_u64(a) == Some(1) && var_matches_counter_term(b, counter_phi, block))
                || (parse_const_u64(b) == Some(1)
                    && var_matches_counter_term(a, counter_phi, block))
        }
        _ => false,
    }
}

fn match_base_plus_counter<'a>(
    addr: &'a SSAVar,
    counter_phi: &SSAVar,
    block: &'a FunctionSSABlock,
) -> Option<&'a SSAVar> {
    let op = find_def(block, addr)?;
    match op {
        SSAOp::IntAdd { a, b, .. } => {
            if var_matches_counter_term(a, counter_phi, block) {
                Some(b)
            } else if var_matches_counter_term(b, counter_phi, block) {
                Some(a)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn resolve_var_concrete<'ctx>(
    executor: &SymExecutor<'ctx>,
    state: &SymState<'ctx>,
    var: &SSAVar,
    block: &FunctionSSABlock,
) -> Option<u64> {
    if let Some(value) = parse_const_u64(var) {
        return Some(value);
    }
    match find_def(block, var) {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. }) => resolve_var_concrete(executor, state, src, block),
        _ => executor.read_var(state, var).as_concrete(),
    }
}

fn parse_const_u64(var: &SSAVar) -> Option<u64> {
    var.constant_bits()
}

fn parse_ram_addr(var: &SSAVar) -> Option<u64> {
    var.name
        .strip_prefix("ram:")
        .and_then(|value| u64::from_str_radix(value, 16).ok())
}

fn parse_address_literal(var: &SSAVar) -> Option<u64> {
    parse_const_u64(var).or_else(|| parse_ram_addr(var))
}

fn parse_var_addr(var: &SSAVar) -> Option<u64> {
    parse_address_literal(var)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RegisterAliasSpec {
    family: Cow<'static, str>,
    offset_bits: u32,
    width_bits: u32,
}

struct ResolvedVarCarrier<'ctx> {
    value: SymValue<'ctx>,
    provenance: Option<RuntimeValueProvenance>,
}

fn resolve_alias_register_carrier<'ctx>(
    state: &SymState<'ctx>,
    key: &str,
    ctx: &'ctx Context,
) -> Option<ResolvedVarCarrier<'ctx>> {
    let (requested_base, requested_version) = split_versioned_register(key)?;
    let requested = x86_register_alias_spec(requested_base)?;

    let mut best: Option<(RegisterAliasSpec, &str, SymValue<'ctx>)> = None;
    let mut best_is_ambiguous = false;
    for (candidate_key, candidate_value) in state.registers() {
        let Some((candidate_base, candidate_version)) = split_versioned_register(candidate_key)
        else {
            continue;
        };
        if candidate_version != requested_version {
            continue;
        }
        let Some(candidate) = x86_register_alias_spec(candidate_base) else {
            continue;
        };
        if candidate.family != requested.family {
            continue;
        }
        if candidate_value.bits() != candidate.width_bits {
            continue;
        }

        if !alias_candidate_can_supply(&requested, &candidate) {
            continue;
        }

        let candidate_rank = candidate.width_bits;
        let best_rank = best.as_ref().map(|(spec, _, _)| spec.width_bits);
        if best_rank.is_none_or(|rank| candidate_rank > rank) {
            best = Some((candidate, candidate_key.as_str(), candidate_value.clone()));
            best_is_ambiguous = false;
        } else if best_rank == Some(candidate_rank) {
            best_is_ambiguous = true;
        }
    }

    if best_is_ambiguous {
        return None;
    }
    let (candidate, candidate_key, value) = best?;
    let projected_value = project_alias_value(&requested, &candidate, value, ctx)?;
    let provenance = state
        .value_provenance(candidate_key)
        .cloned()
        .and_then(|provenance| project_alias_provenance(&requested, &candidate, provenance));
    Some(ResolvedVarCarrier {
        value: projected_value,
        provenance,
    })
}

fn project_alias_value<'ctx>(
    requested: &RegisterAliasSpec,
    candidate: &RegisterAliasSpec,
    value: SymValue<'ctx>,
    ctx: &'ctx Context,
) -> Option<SymValue<'ctx>> {
    let candidate_high = candidate.offset_bits.checked_add(candidate.width_bits)?;
    let requested_high = requested.offset_bits.checked_add(requested.width_bits)?;
    if candidate.offset_bits <= requested.offset_bits && candidate_high >= requested_high {
        let low = requested.offset_bits - candidate.offset_bits;
        let high = low.checked_add(requested.width_bits)?.checked_sub(1)?;
        let extracted = value.extract(ctx, high, low);
        (extracted.bits() == requested.width_bits).then_some(extracted)
    } else if candidate.offset_bits == 0
        && requested.offset_bits == 0
        && candidate.width_bits == 32
        && requested.width_bits == 64
    {
        Some(value.zero_extend(ctx, 64))
    } else {
        None
    }
}

fn alias_candidate_can_supply(
    requested: &RegisterAliasSpec,
    candidate: &RegisterAliasSpec,
) -> bool {
    let candidate_low = candidate.offset_bits;
    let Some(candidate_high) = candidate.offset_bits.checked_add(candidate.width_bits) else {
        return false;
    };
    let requested_low = requested.offset_bits;
    let Some(requested_high) = requested.offset_bits.checked_add(requested.width_bits) else {
        return false;
    };
    let covers_requested = candidate_low <= requested_low && candidate_high >= requested_high;
    let can_zero_extend = candidate_low == 0
        && requested_low == 0
        && candidate.width_bits == 32
        && requested.width_bits == 64;
    covers_requested || can_zero_extend
}

fn alias_candidate_covers(requested: &RegisterAliasSpec, candidate: &RegisterAliasSpec) -> bool {
    let Some(candidate_high) = candidate.offset_bits.checked_add(candidate.width_bits) else {
        return false;
    };
    let Some(requested_high) = requested.offset_bits.checked_add(requested.width_bits) else {
        return false;
    };
    candidate.offset_bits <= requested.offset_bits && candidate_high >= requested_high
}

fn project_alias_provenance(
    requested: &RegisterAliasSpec,
    candidate: &RegisterAliasSpec,
    provenance: RuntimeValueProvenance,
) -> Option<RuntimeValueProvenance> {
    if !alias_candidate_covers(requested, candidate)
        || !candidate.offset_bits.is_multiple_of(8)
        || !candidate.width_bits.is_multiple_of(8)
        || !requested.offset_bits.is_multiple_of(8)
        || !requested.width_bits.is_multiple_of(8)
    {
        return None;
    }
    let source_offset = requested
        .offset_bits
        .checked_sub(candidate.offset_bits)?
        .checked_div(8)?;
    let requested_size = requested.width_bits.checked_div(8)?;
    let candidate_size = candidate.width_bits.checked_div(8)?;
    let covered_end = source_offset.checked_add(requested_size)?;
    if provenance.size > candidate_size || covered_end > provenance.size {
        return None;
    }
    Some(RuntimeValueProvenance {
        source_addr: provenance
            .source_addr
            .checked_add(u64::from(source_offset))?,
        size: requested_size,
    })
}

fn phi_destinations_overlap(block: &FunctionSSABlock) -> bool {
    let mut exact_destinations = HashSet::new();
    for (index, phi) in block.phis.iter().enumerate() {
        if !exact_destinations.insert(phi.dst.display_name()) {
            return true;
        }
        for other in &block.phis[..index] {
            if canonical_storage_ranges_overlap(phi.canonical_storage, other.canonical_storage)
                || x86_alias_destinations_overlap(&phi.dst, &other.dst)
            {
                return true;
            }
        }
    }
    false
}

fn canonical_storage_ranges_overlap(
    left: Option<r2ssa::CanonicalStorageId>,
    right: Option<r2ssa::CanonicalStorageId>,
) -> bool {
    let (Some(left), Some(right)) = (left, right) else {
        return false;
    };
    if left.space != right.space
        || matches!(left.space, CanonicalStorageSpace::Unknown)
        || left.size == 0
        || right.size == 0
    {
        return false;
    }
    let Some(left_end) = left.offset.checked_add(u64::from(left.size)) else {
        return true;
    };
    let Some(right_end) = right.offset.checked_add(u64::from(right.size)) else {
        return true;
    };
    left.offset < right_end && right.offset < left_end
}

fn x86_alias_destinations_overlap(left: &SSAVar, right: &SSAVar) -> bool {
    let left_key = left.display_name();
    let right_key = right.display_name();
    let Some((left_base, left_version)) = split_versioned_register(&left_key) else {
        return false;
    };
    let Some((right_base, right_version)) = split_versioned_register(&right_key) else {
        return false;
    };
    if left_version != right_version {
        return false;
    }
    let Some(left) = x86_register_alias_spec(left_base) else {
        return false;
    };
    let Some(right) = x86_register_alias_spec(right_base) else {
        return false;
    };
    if left.family != right.family {
        return false;
    }
    let Some(left_end) = left.offset_bits.checked_add(left.width_bits) else {
        return true;
    };
    let Some(right_end) = right.offset_bits.checked_add(right.width_bits) else {
        return true;
    };
    left.offset_bits < right_end && right.offset_bits < left_end
}

fn split_versioned_register(name: &str) -> Option<(&str, u32)> {
    let (base, version) = name.rsplit_once('_')?;
    if version.is_empty() || !version.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    Some((base, version.parse().ok()?))
}

fn x86_register_alias_spec(base: &str) -> Option<RegisterAliasSpec> {
    let upper = base.to_ascii_uppercase();
    let base = upper.as_str();
    let fixed = match base {
        "AL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "AH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "AX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EAX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RAX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RAX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "BL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "BH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "BX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EBX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RBX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "CL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "CH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "CX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "ECX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RCX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RCX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "DL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "DH" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 8,
            width_bits: 8,
        }),
        "DX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EDX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RDX" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDX"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "SIL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "SI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "ESI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RSI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSI"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "DIL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "DI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EDI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RDI" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RDI"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "BPL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "BP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "EBP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RBP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RBP"),
            offset_bits: 0,
            width_bits: 64,
        }),
        "SPL" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 8,
        }),
        "SP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 16,
        }),
        "ESP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 32,
        }),
        "RSP" => Some(RegisterAliasSpec {
            family: Cow::Borrowed("RSP"),
            offset_bits: 0,
            width_bits: 64,
        }),
        _ => None,
    };
    if fixed.is_some() {
        return fixed;
    }

    parse_numbered_x86_register_alias(base)
}

fn parse_numbered_x86_register_alias(base: &str) -> Option<RegisterAliasSpec> {
    let (family, width_bits) = if let Some(family) = base.strip_suffix('B') {
        (family.to_string(), 8)
    } else if let Some(family) = base.strip_suffix('W') {
        (family.to_string(), 16)
    } else if let Some(family) = base.strip_suffix('D') {
        (family.to_string(), 32)
    } else {
        (base.to_string(), 64)
    };

    if !family.starts_with('R') {
        return None;
    }
    let digits = &family[1..];
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }

    Some(RegisterAliasSpec {
        family: Cow::Owned(family),
        offset_bits: 0,
        width_bits,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MemoryRegionKind;

    #[test]
    fn test_copy_op() {
        let ctx = Context::thread_local();

        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        // Set up source variable (uppercase because display_name() uppercases named registers)
        state.set_register("SRC_0", SymValue::concrete(42, 64));

        let op = SSAOp::Copy {
            dst: SSAVar::new("dst", 1, 8),
            src: SSAVar::new("src", 0, 8),
        };

        let _ = executor.step(&mut state, &op);

        let dst_val = state.get_register("DST_1");
        assert_eq!(dst_val.as_concrete(), Some(42));
    }

    #[test]
    fn test_select_concrete_and_symbolic() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let select = SSAOp::Select {
            dst: SSAVar::new("result", 1, 8),
            cond: SSAVar::new("cond", 0, 1),
            if_true: SSAVar::new("when_true", 0, 8),
            if_false: SSAVar::new("when_false", 0, 8),
        };

        let mut concrete = SymState::new(&ctx, 0x1000);
        concrete.set_register("COND_0", SymValue::concrete(1, 8));
        concrete.set_register("WHEN_TRUE_0", SymValue::concrete(42, 64));
        concrete.set_register("WHEN_FALSE_0", SymValue::concrete(7, 64));
        executor
            .step(&mut concrete, &select)
            .expect("concrete select should execute");
        assert_eq!(concrete.get_register("RESULT_1").as_concrete(), Some(42));

        let mut symbolic = SymState::new(&ctx, 0x1000);
        symbolic.set_register("COND_0", SymValue::new_symbolic(&ctx, "cond", 8));
        symbolic.set_register("WHEN_TRUE_0", SymValue::concrete(42, 64));
        symbolic.set_register("WHEN_FALSE_0", SymValue::concrete(7, 64));
        executor
            .step(&mut symbolic, &select)
            .expect("symbolic select should execute");
        let result = symbolic.get_register("RESULT_1").to_bv(&ctx);
        let solver = z3::Solver::new();
        solver.assert(
            symbolic
                .get_register("COND_0")
                .to_bv(&ctx)
                .eq(BV::from_u64(1, 8)),
        );
        solver.assert(result.ne(BV::from_u64(42, 64)));
        assert_eq!(solver.check(), z3::SatResult::Unsat);
    }

    #[test]
    fn test_ram_copy_operands_use_memory_not_address_literals() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        let region =
            state.define_memory_region(MemoryRegionKind::Global, "global", Some(0x2000), Some(8));
        state.seed_region_bytes(region, 0, &0x1122_3344_5566_7788u64.to_le_bytes());

        executor
            .step(
                &mut state,
                &SSAOp::Copy {
                    dst: SSAVar::new("dst", 1, 8),
                    src: SSAVar::new("ram:2000", 0, 8),
                },
            )
            .expect("global load should execute");
        assert_eq!(
            state.get_register("DST_1").as_concrete(),
            Some(0x1122_3344_5566_7788)
        );

        state.set_register("SRC_0", SymValue::concrete(0xaabb_ccdd_eeff_0011, 64));
        executor
            .step(
                &mut state,
                &SSAOp::Copy {
                    dst: SSAVar::new("ram:2000", 1, 8),
                    src: SSAVar::new("src", 0, 8),
                },
            )
            .expect("global store should execute");
        assert_eq!(
            state
                .mem_read(&SymValue::concrete(0x2000, 64), 8)
                .as_concrete(),
            Some(0xaabb_ccdd_eeff_0011)
        );
    }

    #[test]
    fn unmodeled_userops_fail_closed_for_output_and_hidden_effects() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        executor
            .step(
                &mut state,
                &SSAOp::CallOther {
                    output: Some(SSAVar::new("RAX", 1, 8)),
                    userop: 74,
                    inputs: vec![],
                },
            )
            .expect("unmodeled result-bearing userop should terminate cleanly");
        assert_eq!(state.exit_status, Some(ExitStatus::Unimplemented));

        let mut state = SymState::new(&ctx, 0x1000);
        executor
            .step(
                &mut state,
                &SSAOp::CallOther {
                    output: None,
                    userop: 0x1234,
                    inputs: vec![],
                },
            )
            .expect("unmodeled effect-only userop should terminate cleanly");
        assert_eq!(state.exit_status, Some(ExitStatus::Unimplemented));
    }

    #[test]
    fn breakpoint_terminates_instead_of_falling_through() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        executor
            .step(&mut state, &SSAOp::Breakpoint)
            .expect("breakpoint should terminate cleanly");
        assert_eq!(
            state.exit_status,
            Some(ExitStatus::Error("Breakpoint".to_string()))
        );
    }

    #[test]
    fn unresolved_direct_branch_targets_fail_closed() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);

        let mut branch = SymState::new(&ctx, 0x1000);
        executor
            .step(
                &mut branch,
                &SSAOp::Branch {
                    target: SSAVar::new("MISSING", 0, 8),
                },
            )
            .expect("unresolved branch should terminate cleanly");
        assert!(matches!(branch.exit_status, Some(ExitStatus::Error(_))));

        let mut conditional = SymState::new(&ctx, 0x1000);
        conditional.set_register("COND_0", SymValue::concrete(1, 8));
        executor
            .step(
                &mut conditional,
                &SSAOp::CBranch {
                    target: SSAVar::new("MISSING", 0, 8),
                    cond: SSAVar::new("COND", 0, 1),
                },
            )
            .expect("unresolved taken branch should terminate cleanly");
        assert!(matches!(
            conditional.exit_status,
            Some(ExitStatus::Error(_))
        ));
    }

    #[test]
    fn same_address_taken_cbranch_stops_block_tail() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("COND_0", SymValue::concrete(1, 8));
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::CBranch {
                    target: SSAVar::constant(0x1000, 8),
                    cond: SSAVar::new("COND", 0, 1),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("TAIL", 1, 8),
                    src: SSAVar::constant(0x55, 8),
                },
            ],
        };

        executor
            .execute_block(&mut state, &block)
            .expect("same-address branch should execute");
        assert_eq!(state.pc(), 0x1000);
        assert!(state.get_register("TAIL_1").is_unknown());
    }

    #[test]
    fn standalone_phi_refuses_without_exact_predecessor() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        let error = executor
            .step(
                &mut state,
                &SSAOp::Phi {
                    dst: SSAVar::new("RAX", 1, 8),
                    sources: vec![SSAVar::new("RAX", 0, 8)],
                },
            )
            .expect_err("standalone phi must not guess its source");
        assert!(matches!(error, crate::SymError::UnsupportedOp(_)));
    }

    #[test]
    fn linked_memory_operations_terminate_without_mutation() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let initial = 0x1122_3344_5566_7788u64;

        let mut load_state = SymState::new(&ctx, 0x1000);
        let region = load_state.define_memory_region(
            MemoryRegionKind::Global,
            "atomic",
            Some(0x2000),
            Some(8),
        );
        load_state.seed_region_bytes(region, 0, &initial.to_le_bytes());
        load_state.set_register("ADDR_0", SymValue::concrete(0x2000, 64));
        load_state.set_register("VALUE_1", SymValue::concrete(0xa5a5, 64));
        executor
            .step(
                &mut load_state,
                &SSAOp::LoadLinked {
                    dst: SSAVar::new("VALUE", 1, 8),
                    space: r2il::SpaceId::Ram,
                    addr: SSAVar::new("ADDR", 0, 8),
                    ordering: r2il::MemoryOrdering::Acquire,
                },
            )
            .expect("load-linked refusal should terminate cleanly");
        assert_eq!(load_state.exit_status, Some(ExitStatus::Unimplemented));
        assert_eq!(
            load_state.get_register("VALUE_1").as_concrete(),
            Some(0xa5a5)
        );
        assert_eq!(
            load_state
                .mem_read(&SymValue::concrete(0x2000, 64), 8)
                .as_concrete(),
            Some(initial)
        );

        let mut store_state = SymState::new(&ctx, 0x1000);
        let region = store_state.define_memory_region(
            MemoryRegionKind::Global,
            "atomic",
            Some(0x2000),
            Some(8),
        );
        store_state.seed_region_bytes(region, 0, &initial.to_le_bytes());
        store_state.set_register("ADDR_0", SymValue::concrete(0x2000, 64));
        store_state.set_register("INPUT_0", SymValue::concrete(u64::MAX, 64));
        store_state.set_register("STATUS_1", SymValue::concrete(0x5a, 8));
        executor
            .step(
                &mut store_state,
                &SSAOp::StoreConditional {
                    result: Some(SSAVar::new("STATUS", 1, 1)),
                    space: r2il::SpaceId::Ram,
                    addr: SSAVar::new("ADDR", 0, 8),
                    val: SSAVar::new("INPUT", 0, 8),
                    ordering: r2il::MemoryOrdering::Release,
                },
            )
            .expect("store-conditional refusal should terminate cleanly");
        assert_eq!(store_state.exit_status, Some(ExitStatus::Unimplemented));
        assert_eq!(
            store_state.get_register("STATUS_1").as_concrete(),
            Some(0x5a)
        );
        assert_eq!(
            store_state
                .mem_read(&SymValue::concrete(0x2000, 64), 8)
                .as_concrete(),
            Some(initial)
        );
    }

    #[test]
    fn custom_memory_operations_do_not_alias_ram_at_the_same_address() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let initial = 0x1122_3344_5566_7788u64;
        let addr = SSAVar::new("ADDR", 0, 8);
        let dst = SSAVar::new("DST", 1, 8);
        let input = SSAVar::new("INPUT", 0, 8);
        let expected = SSAVar::new("EXPECTED", 0, 8);
        let replacement = SSAVar::new("REPLACEMENT", 0, 8);
        let guard = SSAVar::new("GUARD", 0, 1);

        let mut ram_state = SymState::new(&ctx, 0x1000);
        let region =
            ram_state.define_memory_region(MemoryRegionKind::Global, "ram", Some(0x2000), Some(8));
        ram_state.seed_region_bytes(region, 0, &initial.to_le_bytes());
        ram_state.set_register("ADDR_0", SymValue::concrete(0x2000, 64));
        executor
            .step(
                &mut ram_state,
                &SSAOp::Load {
                    dst: dst.clone(),
                    space: SpaceId::Ram,
                    addr: addr.clone(),
                },
            )
            .expect("Ram load should remain supported");
        assert_eq!(ram_state.get_register("DST_1").as_concrete(), Some(initial));

        let custom_ops = [
            SSAOp::Load {
                dst: dst.clone(),
                space: SpaceId::Custom(7),
                addr: addr.clone(),
            },
            SSAOp::Store {
                space: SpaceId::Custom(7),
                addr: addr.clone(),
                val: input.clone(),
            },
            SSAOp::AtomicCAS {
                dst: dst.clone(),
                space: SpaceId::Custom(7),
                addr: addr.clone(),
                expected,
                replacement,
                ordering: r2il::MemoryOrdering::SeqCst,
            },
            SSAOp::LoadGuarded {
                dst: dst.clone(),
                space: SpaceId::Custom(7),
                addr: addr.clone(),
                guard: guard.clone(),
                ordering: r2il::MemoryOrdering::Acquire,
            },
            SSAOp::StoreGuarded {
                space: SpaceId::Custom(7),
                addr,
                val: input,
                guard,
                ordering: r2il::MemoryOrdering::Release,
            },
        ];

        for op in custom_ops {
            let mut state = SymState::new(&ctx, 0x1000);
            let region =
                state.define_memory_region(MemoryRegionKind::Global, "ram", Some(0x2000), Some(8));
            state.seed_region_bytes(region, 0, &initial.to_le_bytes());
            state.set_register("ADDR_0", SymValue::concrete(0x2000, 64));
            state.set_register("DST_1", SymValue::concrete(0x5a, 64));
            state.set_register("INPUT_0", SymValue::concrete(u64::MAX, 64));
            state.set_register("EXPECTED_0", SymValue::concrete(initial, 64));
            state.set_register("REPLACEMENT_0", SymValue::concrete(0xa5, 64));
            state.set_register("GUARD_0", SymValue::concrete(1, 8));

            executor
                .step(&mut state, &op)
                .expect("unsupported Custom memory should terminate cleanly");
            assert_eq!(state.exit_status, Some(ExitStatus::Unimplemented));
            assert_eq!(state.get_register("DST_1").as_concrete(), Some(0x5a));
            assert_eq!(
                state
                    .mem_read(&SymValue::concrete(0x2000, 64), 8)
                    .as_concrete(),
                Some(initial)
            );
        }
    }

    #[test]
    fn semantic_constant_bits_precede_presentation_names() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let state = SymState::new(&ctx, 0x1000);

        let mut constant = SSAVar::constant(0x1234, 8);
        constant.name = "ram:deadbeef".to_string();
        assert_eq!(
            executor.read_var(&state, &constant).as_concrete(),
            Some(0x1234)
        );
        assert_eq!(
            executor
                .read_control_target_var(&state, &constant)
                .as_concrete(),
            Some(0x1234)
        );
        assert_eq!(executor.read_var_provenance(&state, &constant), None);

        let presentation_only = SSAVar::new("const:beef", 0, 8);
        assert!(executor.read_var(&state, &presentation_only).is_symbolic());
    }

    #[test]
    fn unresolved_ssa_values_have_stable_exact_identity() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let state = SymState::new(&ctx, 0x1000);
        let exact = SSAVar::new("missing:value", 3, 8);
        let other_version = SSAVar::new("missing:value", 4, 8);

        let first = executor.read_var(&state, &exact);
        let second = executor.read_var(&state, &exact);
        let other = executor.read_var(&state, &other_version);
        assert!(first.is_symbolic());
        assert!(first.to_bv(&ctx).ast_eq(second.to_bv(&ctx)));
        assert!(!first.to_bv(&ctx).ast_eq(other.to_bv(&ctx)));
    }

    #[test]
    fn register_alias_reads_are_exact_and_version_scoped() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);

        let mut exact = SymState::new(&ctx, 0x1000);
        exact.set_register("EAX_1", SymValue::concrete(0x33, 32));
        exact.set_register("RAX_1", SymValue::concrete(0x1111, 64));
        exact.set_value_provenance(
            "EAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x401000,
                size: 4,
            }),
        );
        exact.set_value_provenance(
            "RAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x402000,
                size: 8,
            }),
        );
        assert_eq!(
            executor
                .read_var(&exact, &SSAVar::new("EAX", 1, 4))
                .as_concrete(),
            Some(0x33)
        );
        assert_eq!(
            executor.read_var_provenance(&exact, &SSAVar::new("EAX", 1, 4)),
            Some(RuntimeValueProvenance {
                source_addr: 0x401000,
                size: 4,
            })
        );

        let mut aliases = SymState::new(&ctx, 0x1000);
        aliases.set_register("RAX_1", SymValue::concrete(0xaaaa_1111, 64));
        aliases.set_register("RAX_2", SymValue::concrete(0xbbbb_2222, 64));
        aliases.set_value_provenance(
            "RAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x411000,
                size: 8,
            }),
        );
        aliases.set_value_provenance(
            "RAX_2",
            Some(RuntimeValueProvenance {
                source_addr: 0x422000,
                size: 8,
            }),
        );
        assert_eq!(
            executor
                .read_var(&aliases, &SSAVar::new("EAX", 1, 4))
                .as_concrete(),
            Some(0xaaaa_1111)
        );
        assert_eq!(
            executor.read_var_provenance(&aliases, &SSAVar::new("EAX", 1, 4)),
            Some(RuntimeValueProvenance {
                source_addr: 0x411000,
                size: 4,
            })
        );
        assert_eq!(
            executor.read_var_provenance(&aliases, &SSAVar::new("AH", 1, 1)),
            Some(RuntimeValueProvenance {
                source_addr: 0x411001,
                size: 1,
            })
        );

        let mut split_carrier = SymState::new(&ctx, 0x1000);
        split_carrier.set_register("RAX_1", SymValue::concrete(0x1122_3344, 64));
        split_carrier.set_value_provenance(
            "EAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x499000,
                size: 4,
            }),
        );
        let carrier = executor.read_var_carrier(&split_carrier, &SSAVar::new("EAX", 1, 4));
        assert_eq!(carrier.value.as_concrete(), Some(0x1122_3344));
        assert_eq!(
            carrier.provenance, None,
            "value and provenance must come from one exact alias carrier"
        );

        let mut malformed_exact = SymState::new(&ctx, 0x1000);
        malformed_exact.set_register("EAX_1", SymValue::concrete(0x55, 32));
        malformed_exact.set_value_provenance(
            "EAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x4aa000,
                size: 8,
            }),
        );
        let carrier = executor.read_var_carrier(&malformed_exact, &SSAVar::new("EAX", 1, 4));
        assert_eq!(carrier.value.as_concrete(), Some(0x55));
        assert_eq!(carrier.provenance, None);

        let mut non_overlapping = SymState::new(&ctx, 0x1000);
        non_overlapping.set_value_provenance(
            "AL_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x433000,
                size: 1,
            }),
        );
        assert_eq!(
            executor.read_var_provenance(&non_overlapping, &SSAVar::new("AH", 1, 1)),
            None,
            "non-overlapping aliases must not share provenance"
        );

        for narrow_name in ["AL_1", "AX_1"] {
            let mut narrow = SymState::new(&ctx, 0x1000);
            let bits = if narrow_name == "AL_1" { 8 } else { 16 };
            narrow.set_register(narrow_name, SymValue::concrete(0x55, bits));
            narrow.set_value_provenance(
                narrow_name,
                Some(RuntimeValueProvenance {
                    source_addr: 0x444000,
                    size: bits / 8,
                }),
            );
            assert!(
                executor
                    .read_var(&narrow, &SSAVar::new("RAX", 1, 8))
                    .is_symbolic()
            );
            assert_eq!(
                executor.read_var_provenance(&narrow, &SSAVar::new("RAX", 1, 8)),
                None,
                "8/16-bit writes do not define the upper register bits"
            );
        }

        let mut zero_extending = SymState::new(&ctx, 0x1000);
        zero_extending.set_register("EAX_1", SymValue::concrete(0x1234, 32));
        zero_extending.set_value_provenance(
            "EAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x455000,
                size: 4,
            }),
        );
        assert_eq!(
            executor
                .read_var(&zero_extending, &SSAVar::new("RAX", 1, 8))
                .as_concrete(),
            Some(0x1234)
        );
        assert_eq!(
            executor.read_var_provenance(&zero_extending, &SSAVar::new("RAX", 1, 8)),
            None,
            "zero-extension adds non-source bits and cannot retain whole-value provenance"
        );

        let mut ambiguous = SymState::new(&ctx, 0x1000);
        ambiguous.set_register("RAX_1", SymValue::concrete(0x11, 64));
        ambiguous.set_register("rax_1", SymValue::concrete(0x22, 64));
        ambiguous.set_value_provenance(
            "RAX_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x466000,
                size: 8,
            }),
        );
        ambiguous.set_value_provenance(
            "rax_1",
            Some(RuntimeValueProvenance {
                source_addr: 0x477000,
                size: 8,
            }),
        );
        assert!(
            executor
                .read_var(&ambiguous, &SSAVar::new("AL", 1, 1))
                .is_symbolic(),
            "equal-rank aliases must not be selected by HashMap iteration order"
        );
        assert_eq!(
            executor.read_var_provenance(&ambiguous, &SSAVar::new("AL", 1, 1)),
            None
        );

        let mut width_conflict = SymState::new(&ctx, 0x1000);
        executor.write_var(
            &mut width_conflict,
            &SSAVar::new("EAX", 1, 8),
            SymValue::concrete(0x1234, 64),
        );
        assert!(
            width_conflict.registers().get("RAX_1").is_none(),
            "presentation name alone must not trigger the 32-bit architectural write rule"
        );
    }

    #[test]
    fn execute_block_phi_uses_exact_source_and_provenance() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x2000);
        state.set_prev_pc(Some(0x1000));
        state.set_register("SRC_0", SymValue::concrete(0x42, 64));
        state.set_value_provenance(
            "SRC_0",
            Some(RuntimeValueProvenance {
                source_addr: 0x401000,
                size: 8,
            }),
        );
        state.set_register("MERGED_1", SymValue::concrete(0xff, 64));
        state.set_value_provenance(
            "MERGED_1",
            Some(RuntimeValueProvenance {
                source_addr: 0xdeadbeef,
                size: 8,
            }),
        );
        let block = FunctionSSABlock {
            addr: 0x2000,
            size: 1,
            phis: vec![r2ssa::PhiNode {
                dst: SSAVar::new("MERGED", 1, 8),
                sources: vec![
                    (0x1000, SSAVar::new("SRC", 0, 8)),
                    (0x3000, SSAVar::constant(0x99, 8)),
                ],
                canonical_storage: None,
            }],
            ops: Vec::new(),
        };

        executor
            .execute_block(&mut state, &block)
            .expect("exact predecessor should select its Phi source");
        assert_eq!(state.get_register("MERGED_1").as_concrete(), Some(0x42));
        assert_eq!(
            state.value_provenance("MERGED_1"),
            Some(&RuntimeValueProvenance {
                source_addr: 0x401000,
                size: 8,
            })
        );
    }

    #[test]
    fn execute_block_phi_rejects_missing_and_duplicate_predecessors() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let phi = |sources| FunctionSSABlock {
            addr: 0x2000,
            size: 1,
            phis: vec![r2ssa::PhiNode {
                dst: SSAVar::new("MERGED", 1, 8),
                sources,
                canonical_storage: None,
            }],
            ops: Vec::new(),
        };

        let mut missing = SymState::new(&ctx, 0x2000);
        missing.set_prev_pc(Some(0x1000));
        let error = executor
            .execute_block(&mut missing, &phi(vec![(0x3000, SSAVar::constant(1, 8))]))
            .expect_err("missing predecessor must be refused");
        assert!(matches!(error, crate::SymError::UnsupportedOp(_)));

        let mut duplicate = SymState::new(&ctx, 0x2000);
        duplicate.set_prev_pc(Some(0x1000));
        let error = executor
            .execute_block(
                &mut duplicate,
                &phi(vec![
                    (0x1000, SSAVar::constant(1, 8)),
                    (0x1000, SSAVar::constant(2, 8)),
                ]),
            )
            .expect_err("duplicate predecessor sources must be refused");
        assert!(matches!(error, crate::SymError::UnsupportedOp(_)));
    }

    #[test]
    fn execute_block_phi_resolution_is_transactional_and_parallel() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut parallel = SymState::new(&ctx, 0x2000);
        parallel.set_prev_pc(Some(0x1000));
        parallel.set_register("LOW_0", SymValue::concrete(0x11, 32));
        parallel.set_register("RAX_1", SymValue::concrete(0xaaaa, 64));
        let block = FunctionSSABlock {
            addr: 0x2000,
            size: 1,
            phis: vec![
                r2ssa::PhiNode {
                    dst: SSAVar::new("EAX", 1, 4),
                    sources: vec![(0x1000, SSAVar::new("LOW", 0, 4))],
                    canonical_storage: None,
                },
                r2ssa::PhiNode {
                    dst: SSAVar::new("RESULT", 1, 8),
                    sources: vec![(0x1000, SSAVar::new("RAX", 1, 8))],
                    canonical_storage: None,
                },
            ],
            ops: Vec::new(),
        };
        executor
            .execute_block(&mut parallel, &block)
            .expect("all Phi sources should be snapshotted before writes");
        assert_eq!(
            parallel.get_register("RESULT_1").as_concrete(),
            Some(0xaaaa)
        );

        let mut invalid = SymState::new(&ctx, 0x2000);
        invalid.set_prev_pc(Some(0x1000));
        invalid.set_register("KEEP_1", SymValue::concrete(0x55, 64));
        let block = FunctionSSABlock {
            addr: 0x2000,
            size: 1,
            phis: vec![
                r2ssa::PhiNode {
                    dst: SSAVar::new("KEEP", 1, 8),
                    sources: vec![(0x1000, SSAVar::constant(0x99, 8))],
                    canonical_storage: None,
                },
                r2ssa::PhiNode {
                    dst: SSAVar::new("BAD", 1, 8),
                    sources: vec![
                        (0x1000, SSAVar::constant(1, 8)),
                        (0x1000, SSAVar::constant(2, 8)),
                    ],
                    canonical_storage: None,
                },
            ],
            ops: Vec::new(),
        };
        assert!(executor.execute_block(&mut invalid, &block).is_err());
        assert_eq!(invalid.get_register("KEEP_1").as_concrete(), Some(0x55));
    }

    #[test]
    fn execute_block_phi_refuses_overlapping_alias_destinations_in_either_order() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let phi = |dst: SSAVar, value: u64| {
            let size = dst.size;
            r2ssa::PhiNode {
                dst,
                sources: vec![(0x1000, SSAVar::constant(value, size))],
                canonical_storage: None,
            }
        };

        for phis in [
            vec![
                phi(SSAVar::new("RAX", 1, 8), 0x1111),
                phi(SSAVar::new("EAX", 1, 4), 0x2222),
            ],
            vec![
                phi(SSAVar::new("EAX", 1, 4), 0x2222),
                phi(SSAVar::new("RAX", 1, 8), 0x1111),
            ],
        ] {
            let mut state = SymState::new(&ctx, 0x2000);
            state.set_prev_pc(Some(0x1000));
            state.set_register("RAX_1", SymValue::concrete(0xaaaa, 64));
            state.set_register("EAX_1", SymValue::concrete(0xbbbb, 32));
            let block = FunctionSSABlock {
                addr: 0x2000,
                size: 1,
                phis,
                ops: Vec::new(),
            };
            assert!(matches!(
                executor.execute_block(&mut state, &block),
                Err(crate::SymError::UnsupportedOp(_))
            ));
            assert_eq!(state.get_register("RAX_1").as_concrete(), Some(0xaaaa));
            assert_eq!(state.get_register("EAX_1").as_concrete(), Some(0xbbbb));
        }
    }

    #[test]
    fn execute_block_phi_refuses_overlapping_canonical_destinations() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x2000);
        state.set_prev_pc(Some(0x1000));
        state.set_register("LEFT_1", SymValue::concrete(0xaaaa, 64));
        let block = FunctionSSABlock {
            addr: 0x2000,
            size: 1,
            phis: vec![
                r2ssa::PhiNode {
                    dst: SSAVar::new("LEFT", 1, 8),
                    sources: vec![(0x1000, SSAVar::constant(0x1111, 8))],
                    canonical_storage: Some(r2ssa::CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: 0,
                        size: 8,
                    }),
                },
                r2ssa::PhiNode {
                    dst: SSAVar::new("RIGHT", 2, 4),
                    sources: vec![(0x1000, SSAVar::constant(0x2222, 4))],
                    canonical_storage: Some(r2ssa::CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: 4,
                        size: 4,
                    }),
                },
            ],
            ops: Vec::new(),
        };

        assert!(matches!(
            executor.execute_block(&mut state, &block),
            Err(crate::SymError::UnsupportedOp(_))
        ));
        assert_eq!(state.get_register("LEFT_1").as_concrete(), Some(0xaaaa));
        assert!(state.get_register("RIGHT_2").is_unknown());
    }

    #[test]
    fn execute_block_phi_uses_tagged_runtime_predecessor() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x8020);
        state.register_runtime_region_alias(0x8000, 0x100, true);
        state.note_runtime_store_copy(
            0x8000,
            0x100,
            Some(&RuntimeValueProvenance {
                source_addr: 0x1000,
                size: 0x100,
            }),
        );
        assert_eq!(state.resolve_runtime_pc(0x8010), Some(0x1010));
        state.set_runtime_predecessor(0x8010, 0x1010);
        let block = FunctionSSABlock {
            addr: 0x1020,
            size: 1,
            phis: vec![r2ssa::PhiNode {
                dst: SSAVar::new("MERGED", 1, 8),
                sources: vec![(0x1010, SSAVar::constant(0x77, 8))],
                canonical_storage: None,
            }],
            ops: Vec::new(),
        };

        executor
            .execute_block(&mut state, &block)
            .expect("runtime predecessor should match the static Phi source");
        assert_eq!(state.get_register("MERGED_1").as_concrete(), Some(0x77));
    }

    #[test]
    fn execute_block_phi_does_not_remap_overlapping_static_predecessor() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1020);
        state.register_runtime_region_alias(0x1000, 0x100, true);
        state.note_runtime_store_copy(
            0x1000,
            0x100,
            Some(&RuntimeValueProvenance {
                source_addr: 0x3000,
                size: 0x100,
            }),
        );
        assert_eq!(state.resolve_runtime_pc(0x1010), Some(0x3010));
        state.set_prev_pc(Some(0x1010));
        let block = FunctionSSABlock {
            addr: 0x1020,
            size: 1,
            phis: vec![r2ssa::PhiNode {
                dst: SSAVar::new("MERGED", 1, 8),
                sources: vec![
                    (0x1010, SSAVar::constant(0x77, 8)),
                    (0x3010, SSAVar::constant(0x99, 8)),
                ],
                canonical_storage: None,
            }],
            ops: Vec::new(),
        };

        executor
            .execute_block(&mut state, &block)
            .expect("a tagged static predecessor must not be remapped by numeric overlap");
        assert_eq!(state.get_register("MERGED_1").as_concrete(), Some(0x77));
    }

    #[test]
    fn test_add_op() {
        let ctx = Context::thread_local();

        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        state.set_register("A_0", SymValue::concrete(10, 64));
        state.set_register("B_0", SymValue::concrete(20, 64));

        let op = SSAOp::IntAdd {
            dst: SSAVar::new("result", 1, 8),
            a: SSAVar::new("a", 0, 8),
            b: SSAVar::new("b", 0, 8),
        };

        let _ = executor.step(&mut state, &op);

        let result = state.get_register("RESULT_1");
        assert_eq!(result.as_concrete(), Some(30));
    }

    #[test]
    fn test_cbranch_concrete() {
        let ctx = Context::thread_local();

        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        // Condition is true (non-zero, uppercase for display_name compatibility)
        state.set_register("COND_0", SymValue::concrete(1, 1));

        let op = SSAOp::CBranch {
            target: SSAVar::constant(0x2000, 8),
            cond: SSAVar::new("cond", 0, 1),
        };

        let forked = executor.step(&mut state, &op).unwrap();
        assert!(forked.is_empty()); // No fork for concrete condition
        assert_eq!(state.pc(), 0x2000); // Branch taken
    }

    #[test]
    fn test_cbranch_ram_target_stays_address_literal() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("COND_0", SymValue::concrete(1, 1));

        let forked = executor
            .step(
                &mut state,
                &SSAOp::CBranch {
                    target: SSAVar::new("ram:3000", 0, 8),
                    cond: SSAVar::new("cond", 0, 1),
                },
            )
            .expect("branch should execute");

        assert!(forked.is_empty());
        assert_eq!(state.pc(), 0x3000);
    }

    #[test]
    fn test_cbranch_symbolic() {
        let ctx = Context::thread_local();

        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        // Symbolic condition (uppercase for display_name compatibility)
        state.make_symbolic("COND", 1);

        let op = SSAOp::CBranch {
            target: SSAVar::constant(0x2000, 8),
            cond: SSAVar::new("cond", 0, 1),
        };

        let forked = executor.step(&mut state, &op).unwrap();
        assert_eq!(forked.len(), 1); // Fork created
        assert_eq!(forked[0].pc(), 0x2000); // True branch goes to target
        // Original state is false branch (PC unchanged in this test)
    }

    #[test]
    fn test_read_var_does_not_guess_cross_version_x86_subregister_alias() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        state.set_register("EAX_4", SymValue::concrete(0x6b, 32));

        let al = SSAVar::new("AL", 0, 1);
        let value = executor.read_var(&state, &al);
        assert!(value.is_symbolic());
        assert_eq!(value.bits(), 8);
    }

    #[test]
    fn test_realistic_al_compare_path_forks_on_loaded_byte() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x401c6d);

        let addr = SymValue::concrete(0x2ff6, 64);
        let byte = SymValue::new_symbolic(&ctx, "stdin_byte", 8);
        state.mem_write(&addr, &byte, 1);
        state.set_register("tmp:4700_5", addr.clone());

        let ops = vec![
            SSAOp::Load {
                dst: SSAVar::new("tmp:11e00", 1, 1),
                addr: SSAVar::new("tmp:4700", 5, 8),
                space: r2il::SpaceId::Ram,
            },
            SSAOp::IntZExt {
                dst: SSAVar::new("EAX", 4, 4),
                src: SSAVar::new("tmp:11e00", 1, 1),
            },
            SSAOp::IntZExt {
                dst: SSAVar::new("RAX", 6, 8),
                src: SSAVar::new("EAX", 4, 4),
            },
            SSAOp::IntLess {
                dst: SSAVar::new("CF", 6, 1),
                a: SSAVar::new("AL", 0, 1),
                b: SSAVar::constant(0x6b, 1),
            },
            SSAOp::IntSBorrow {
                dst: SSAVar::new("OF", 6, 1),
                a: SSAVar::new("AL", 0, 1),
                b: SSAVar::constant(0x6b, 1),
            },
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:3de00", 1, 1),
                a: SSAVar::new("AL", 0, 1),
                b: SSAVar::constant(0x6b, 1),
            },
            SSAOp::IntSLess {
                dst: SSAVar::new("SF", 6, 1),
                a: SSAVar::new("tmp:3de00", 1, 1),
                b: SSAVar::constant(0, 1),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("ZF", 6, 1),
                a: SSAVar::new("tmp:3de00", 1, 1),
                b: SSAVar::constant(0, 1),
            },
            SSAOp::BoolNot {
                dst: SSAVar::new("tmp:12800", 1, 1),
                src: SSAVar::new("ZF", 6, 1),
            },
            SSAOp::CBranch {
                target: SSAVar::constant(0x401c86, 8),
                cond: SSAVar::new("tmp:12800", 1, 1),
            },
        ];

        let mut forked = Vec::new();
        for op in &ops {
            let new_states = executor.step(&mut state, op).unwrap();
            forked.extend(new_states);
        }

        assert_eq!(forked.len(), 1, "true branch should fork to the target");
        assert_eq!(forked[0].pc(), 0x401c86);
        assert!(
            state.get_register("tmp:12800_1").as_concrete().is_none(),
            "false branch condition should remain symbolic"
        );
    }

    #[test]
    fn test_callind_uses_provenance_source_for_hook_lookup() {
        let ctx = Context::thread_local();
        let mut executor = SymExecutor::new(&ctx);
        executor.register_call_hook(0x401000, |state| {
            state.set_concrete("RAX_0", 0x99, 64);
            Ok(CallHookResult::Fallthrough)
        });

        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("TMP_0", SymValue::concrete(0x12345678, 64));
        state.set_value_provenance(
            "TMP_0",
            Some(RuntimeValueProvenance {
                source_addr: 0x401000,
                size: 8,
            }),
        );

        let op = SSAOp::CallInd {
            target: SSAVar::new("tmp", 0, 8),
        };

        executor
            .step(&mut state, &op)
            .expect("callind should execute");
        assert_eq!(state.get_register("RAX_0").as_concrete(), Some(0x99));
    }

    #[test]
    fn test_direct_call_fork_requires_whitelist() {
        let ctx = Context::thread_local();
        let mut executor = SymExecutor::new(&ctx);
        let op = SSAOp::Call {
            target: SSAVar::constant(0x401000, 8),
        };

        let mut state = SymState::new(&ctx, 0x1000);
        let forks = executor
            .step(&mut state, &op)
            .expect("direct call should execute");
        assert!(
            forks.is_empty(),
            "direct calls should remain fallthrough-only by default"
        );

        let mut targets = HashSet::new();
        targets.insert(0x401000);
        executor.replace_direct_call_fork_targets(Some(targets));

        let mut state = SymState::new(&ctx, 0x1000);
        let forks = executor
            .step(&mut state, &op)
            .expect("direct call should execute");
        assert_eq!(forks.len(), 1);
        assert_eq!(forks[0].pc(), 0x401000);
        assert_eq!(state.pc(), 0x1000, "caller fallthrough state is preserved");
    }

    #[test]
    fn executor_observes_cancellation_triggered_mid_block() {
        let ctx = Context::thread_local();
        let cancellation = crate::SymCancellationToken::default();
        let execution = crate::SymExecutionControl::with_cancellation(cancellation.clone());
        let mut executor = SymExecutor::with_execution_control(&ctx, execution);
        executor.register_call_hook(0x401000, move |_| {
            cancellation.cancel();
            Ok(CallHookResult::Fallthrough)
        });
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 2,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Call {
                    target: SSAVar::constant(0x401000, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("RAX", 1, 8),
                    src: SSAVar::constant(0x42, 8),
                },
            ],
        };
        let mut state = SymState::new(&ctx, 0x1000);

        let error = executor
            .execute_block(&mut state, &block)
            .expect_err("the operation after cancellation must not execute");

        assert!(matches!(error, crate::SymError::Cancelled));
        assert!(state.get_register("RAX_1").as_concrete().is_none());
    }

    #[test]
    fn test_execute_block_skips_local_cbranch_tail_without_inventing_alias() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("COND_0", SymValue::concrete(1, 1));
        state.set_register("RAX_0", SymValue::concrete(0x11, 64));
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::CBranch {
                    target: SSAVar::new("ram:1004", 0, 8),
                    cond: SSAVar::new("cond", 0, 1),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("rax", 1, 8),
                    src: SSAVar::constant(0x22, 8),
                },
            ],
        };

        let forks = executor
            .execute_block(&mut state, &block)
            .expect("block should execute");

        assert!(forks.is_empty());
        assert_eq!(state.pc(), 0x1004);
        assert_eq!(state.get_register("RAX_0").as_concrete(), Some(0x11));
        assert!(
            executor
                .read_var(&state, &SSAVar::new("rax", 1, 8))
                .is_symbolic(),
            "a skipped SSA definition must not borrow a different version by name"
        );
    }

    #[test]
    fn test_execute_block_merges_symbolic_local_cbranch_tail() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("COND_0", SymValue::new_symbolic(&ctx, "cond", 1));
        state.set_register("RAX_0", SymValue::concrete(0x11, 64));
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::CBranch {
                    target: SSAVar::new("ram:1004", 0, 8),
                    cond: SSAVar::new("cond", 0, 1),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("rax", 1, 8),
                    src: SSAVar::constant(0x22, 8),
                },
            ],
        };

        let forks = executor
            .execute_block(&mut state, &block)
            .expect("block should execute");

        assert!(forks.is_empty());
        assert_eq!(state.pc(), 0x1004);
        assert!(
            executor
                .read_var(&state, &SSAVar::new("rax", 1, 8))
                .as_concrete()
                .is_none(),
            "symbolic local branch should become predicated dataflow, not a path fork"
        );
    }

    #[test]
    fn test_callind_uses_direct_ram_source_provenance_for_import_hook_lookup() {
        let ctx = Context::thread_local();
        let mut executor = SymExecutor::new(&ctx);
        executor.register_call_hook(0x401000, |state| {
            state.set_concrete("RAX_0", 0x1234, 64);
            Ok(CallHookResult::Fallthrough)
        });

        let mut state = SymState::new(&ctx, 0x1000);
        executor
            .step(
                &mut state,
                &SSAOp::Copy {
                    dst: SSAVar::new("tmp:import", 0, 8),
                    src: SSAVar::new("ram:401000", 0, 8),
                },
            )
            .expect("import slot load should execute");
        executor
            .step(
                &mut state,
                &SSAOp::CallInd {
                    target: SSAVar::new("tmp:import", 0, 8),
                },
            )
            .expect("callind should execute through source provenance");

        assert_eq!(state.get_register("RAX_0").as_concrete(), Some(0x1234));
    }

    #[test]
    fn test_execute_block_runahead_collapses_concrete_copy_loop() {
        let ctx = Context::thread_local();
        let executor = SymExecutor::new(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);

        let source_region =
            state.define_memory_region(MemoryRegionKind::Global, "blob", Some(0x2000), Some(4));
        state.seed_region_bytes(source_region, 0, &[0x41, 0x42, 0x43, 0x44]);

        let (_region_id, runtime_base) = state.allocate_heap_region("jit_blob", 4);
        state.register_runtime_region_alias(runtime_base, 4, true);
        state.set_concrete("RBX_0", runtime_base, 64);
        state.set_prev_pc(Some(0x0));

        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 7,
            phis: vec![r2ssa::PhiNode {
                dst: SSAVar::new("RCX", 1, 8),
                sources: vec![
                    (0x0, SSAVar::constant(0, 8)),
                    (0x1000, SSAVar::new("RCX", 2, 8)),
                ],
                canonical_storage: None,
            }],
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:src", 0, 8),
                    a: SSAVar::constant(0x2000, 8),
                    b: SSAVar::new("RCX", 1, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:byte", 0, 1),
                    addr: SSAVar::new("tmp:src", 0, 8),
                    space: r2il::SpaceId::Ram,
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:dst", 0, 8),
                    a: SSAVar::new("RBX", 0, 8),
                    b: SSAVar::new("RCX", 1, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: SSAVar::new("tmp:dst", 0, 8),
                    val: SSAVar::new("tmp:byte", 0, 1),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("RCX", 2, 8),
                    a: SSAVar::new("RCX", 1, 8),
                    b: SSAVar::constant(1, 8),
                },
                SSAOp::IntLess {
                    dst: SSAVar::new("CF", 0, 1),
                    a: SSAVar::new("RCX", 2, 8),
                    b: SSAVar::constant(4, 8),
                },
                SSAOp::CBranch {
                    target: SSAVar::new("ram:1000", 0, 8),
                    cond: SSAVar::new("CF", 0, 1),
                },
            ],
        };

        let forked = executor
            .execute_block(&mut state, &block)
            .expect("copy loop block should execute");
        assert!(forked.is_empty());
        assert_eq!(state.pc(), 0x1000);
        assert_eq!(state.get_register("RCX_2").as_concrete(), Some(4));
        assert_eq!(
            state
                .mem_read(&SymValue::concrete(runtime_base, 64), 4)
                .as_concrete(),
            Some(0x4443_4241)
        );
        let region = state
            .runtime_region_for_pc(runtime_base)
            .expect("runtime alias should remain registered");
        assert_eq!(region.source_base, Some(0x2000));
        assert!(state.depth >= block.ops.len() * 4);

        let mut custom_state = SymState::new(&ctx, 0x1000);
        let source_region = custom_state.define_memory_region(
            MemoryRegionKind::Global,
            "blob",
            Some(0x2000),
            Some(4),
        );
        custom_state.seed_region_bytes(source_region, 0, &[0x41, 0x42, 0x43, 0x44]);
        let (_region_id, custom_base) = custom_state.allocate_heap_region("custom_dst", 4);
        custom_state.mem_write(
            &SymValue::concrete(custom_base, 64),
            &SymValue::concrete(0, 32),
            4,
        );
        custom_state.set_concrete("RBX_0", custom_base, 64);
        custom_state.set_prev_pc(Some(0x0));
        let mut custom_block = block.clone();
        let SSAOp::Load { space, .. } = &mut custom_block.ops[1] else {
            unreachable!("copy-loop fixture must contain a load")
        };
        *space = SpaceId::Custom(7);

        executor
            .execute_block(&mut custom_state, &custom_block)
            .expect("Custom copy loop should terminate cleanly");
        assert_eq!(
            custom_state.exit_status,
            Some(ExitStatus::Unimplemented),
            "copy runahead must not bypass the exact memory-space gate"
        );
        assert_eq!(
            custom_state
                .mem_read(&SymValue::concrete(custom_base, 64), 4)
                .as_concrete(),
            Some(0)
        );
    }
}
