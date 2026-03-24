//! Symbolic executor for SSA operations.
//!
//! This module implements the core symbolic execution logic,
//! stepping through SSA operations and updating state.

use std::collections::HashMap;

use r2ssa::{FunctionSSABlock, SSAOp, SSAVar};
use z3::Context;
use z3::ast::BV;

use crate::SymResult;
use crate::state::{ExitStatus, SymState};
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

/// A call hook for intercepting direct calls.
pub type CallHook<'ctx> = Box<dyn Fn(&mut SymState<'ctx>) -> SymResult<CallHookResult> + 'ctx>;

/// Symbolic executor for SSA functions.
pub struct SymExecutor<'ctx> {
    /// The Z3 context.
    ctx: &'ctx Context,
    /// Registered call hooks (address -> handler).
    call_hooks: HashMap<u64, CallHook<'ctx>>,
}

impl<'ctx> SymExecutor<'ctx> {
    /// Create a new symbolic executor.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            call_hooks: HashMap::new(),
        }
    }

    /// Register a call hook for a target address.
    pub fn register_call_hook<F>(&mut self, addr: u64, hook: F)
    where
        F: Fn(&mut SymState<'ctx>) -> SymResult<CallHookResult> + 'ctx,
    {
        self.call_hooks.insert(addr, Box::new(hook));
    }

    /// Execute a single SSA operation on the given state.
    ///
    /// Returns a list of successor states (multiple for branches).
    pub fn step(&self, state: &mut SymState<'ctx>, op: &SSAOp) -> SymResult<Vec<SymState<'ctx>>> {
        use SSAOp::*;

        match op {
            // ==================== Data Movement ====================
            Copy { dst, src } => {
                let value = self.read_var(state, src);
                self.write_var(state, dst, value);
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

            Load {
                dst,
                addr,
                space: _,
            } => {
                let addr_val = self.read_var(state, addr);
                let size = dst.size;
                let value = state.mem_read(&addr_val, size);
                self.write_var(state, dst, value);
                Ok(vec![])
            }

            Store {
                addr,
                val,
                space: _,
            } => {
                let addr_val = self.read_var(state, addr);
                let value = self.read_var(state, val);
                let size = val.size;
                state.mem_write(&addr_val, &value, size);
                Ok(vec![])
            }
            Fence { .. } => Ok(vec![]),
            LoadLinked {
                dst,
                addr,
                space: _,
                ordering: _,
            } => {
                let addr_val = self.read_var(state, addr);
                let size = dst.size;
                let value = state.mem_read(&addr_val, size);
                self.write_var(state, dst, value);
                Ok(vec![])
            }
            StoreConditional {
                result,
                addr,
                val,
                space: _,
                ordering: _,
            } => {
                let addr_val = self.read_var(state, addr);
                let value = self.read_var(state, val);
                let size = val.size;
                state.mem_write(&addr_val, &value, size);
                if let Some(dst) = result {
                    let bits = dst.size.saturating_mul(8).max(1);
                    let status = if addr_val.as_concrete().is_some() {
                        SymValue::concrete(0, bits)
                    } else {
                        SymValue::new_symbolic(self.ctx, "store_conditional", bits)
                    };
                    self.write_var(state, dst, status);
                }
                Ok(vec![])
            }
            AtomicCAS {
                dst,
                addr,
                expected,
                replacement,
                space: _,
                ordering: _,
            } => {
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
                space: _,
                ordering: _,
            } => {
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
                space: _,
                ordering: _,
            } => {
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
                let result = a_val.eq(self.ctx, &b_val);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntNotEqual { dst, a, b } => {
                let a_val = self.read_var(state, a);
                let b_val = self.read_var(state, b);
                let eq = a_val.eq(self.ctx, &b_val);
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
                let val = self.read_var(state, src);
                let result = val.zero_extend(self.ctx, dst.size * 8);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            IntSExt { dst, src } => {
                let val = self.read_var(state, src);
                let result = val.sign_extend(self.ctx, dst.size * 8);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            // ==================== Boolean Operations ====================
            BoolNot { dst, src } => {
                let val = self.read_var(state, src);
                let result = match val.as_concrete() {
                    Some(v) => SymValue::concrete(if v == 0 { 1 } else { 0 }, 1),
                    None => val.not(self.ctx),
                };
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
                let val = self.read_var(state, src);
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
                let target_val = self.read_var(state, target);
                if let Some(addr) = target_val.as_concrete() {
                    state.pc = addr;
                }
                Ok(vec![])
            }

            CBranch { target, cond } => {
                let target_val = self.read_var(state, target);
                let cond_val = self.read_var(state, cond);

                // Check if condition is concrete
                if let Some(c) = cond_val.as_concrete() {
                    if c != 0 {
                        // Branch taken
                        if let Some(addr) = target_val.as_concrete() {
                            state.pc = addr;
                        }
                    }
                    // If c == 0, fall through (don't change PC)
                    Ok(vec![])
                } else {
                    // Symbolic condition - fork execution
                    let target_addr = target_val.as_concrete();

                    // Create true branch state
                    let mut true_state = state.fork();
                    true_state.add_true_constraint(&cond_val);
                    if let Some(addr) = target_addr {
                        true_state.pc = addr;
                    }

                    // Current state becomes false branch
                    state.add_false_constraint(&cond_val);

                    Ok(vec![true_state])
                }
            }

            BranchInd { target } => {
                let target_val = self.read_var(state, target);
                if let Some(addr) = target_val.as_concrete() {
                    state.pc = addr;
                } else {
                    // Indirect branch with symbolic target - terminate
                    state.terminate(ExitStatus::Error("Symbolic indirect branch".to_string()));
                }
                Ok(vec![])
            }

            Call { target } => {
                let target_val = self.read_var(state, target);
                if let Some(addr) = target_val.as_concrete()
                    && let Some(hook) = self.call_hooks.get(&addr)
                {
                    match hook(state)? {
                        CallHookResult::Fallthrough => {}
                        CallHookResult::Jump(new_pc) => state.pc = new_pc,
                        CallHookResult::Terminate(status) => state.terminate(status),
                    }
                }
                Ok(vec![])
            }

            CallInd { target } => {
                let target_val = self.read_var(state, target);
                if let Some(addr) = target_val.as_concrete() {
                    if let Some(hook) = self.call_hooks.get(&addr) {
                        match hook(state)? {
                            CallHookResult::Fallthrough => {}
                            CallHookResult::Jump(new_pc) => state.pc = new_pc,
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
                state.terminate(ExitStatus::Return);
                Ok(vec![])
            }

            // ==================== Phi Nodes ====================
            Phi { dst, sources } => {
                // In symbolic execution, phi nodes are handled by the path explorer
                // For a single path, we just pick the first source
                if let Some(src) = sources.first() {
                    let val = self.read_var(state, src);
                    self.write_var(state, dst, val);
                }
                Ok(vec![])
            }

            // ==================== Special Operations ====================
            Nop => Ok(vec![]),

            Unimplemented => {
                state.terminate(ExitStatus::Unimplemented);
                Ok(vec![])
            }

            Breakpoint => {
                // Could add breakpoint handling here
                Ok(vec![])
            }

            CpuId { dst } => {
                // Return symbolic CPUID result
                let result = SymValue::new_symbolic(self.ctx, "cpuid", dst.size * 8);
                self.write_var(state, dst, result);
                Ok(vec![])
            }

            CallOther {
                output,
                userop: _,
                inputs: _,
            } => {
                // User-defined operation - return symbolic result
                if let Some(dst) = output {
                    let result = SymValue::new_symbolic(self.ctx, "callother", dst.size * 8);
                    self.write_var(state, dst, result);
                }
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
                let val = self.read_var(state, src);
                let dst_bits = dst.size.saturating_mul(8).max(1);
                let result = if dst_bits > val.bits() {
                    val.zero_extend(self.ctx, dst_bits)
                } else if dst_bits < val.bits() {
                    val.extract(self.ctx, dst_bits - 1, 0)
                } else {
                    val
                };
                self.write_var(state, dst, result);
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
        if var.is_const() {
            // Parse constant value from name
            if let Some(hex) = var.name.strip_prefix("const:")
                && let Ok(value) = u64::from_str_radix(hex, 16)
            {
                return SymValue::concrete(value, var.size * 8);
            }
            SymValue::concrete(0, var.size * 8)
        } else if let Some(hex) = var.name.strip_prefix("ram:") {
            // Treat RAM addresses as concrete branch targets.
            if let Ok(value) = u64::from_str_radix(hex, 16) {
                SymValue::concrete(value, var.size * 8)
            } else {
                SymValue::concrete(0, var.size * 8)
            }
        } else {
            let key = var.display_name();
            state.get_register_sized(&key, var.size * 8)
        }
    }

    /// Write an SSA variable to state.
    fn write_var(&self, state: &mut SymState<'ctx>, var: &SSAVar, value: SymValue<'ctx>) {
        let key = var.display_name();
        state.set_register(&key, value);
    }

    /// Execute a block of SSA operations.
    pub fn execute_block(
        &self,
        state: &mut SymState<'ctx>,
        block: &FunctionSSABlock,
    ) -> SymResult<Vec<SymState<'ctx>>> {
        let mut forked_states = Vec::new();
        let incoming = state.prev_pc();

        // Execute phi nodes first
        for phi in &block.phis {
            // In single-path execution, we need to know which predecessor we came from
            let src = incoming
                .and_then(|prev| phi.sources.iter().find(|(pred, _)| *pred == prev))
                .map(|(_, src)| src)
                .or_else(|| phi.sources.first().map(|(_, src)| src));
            if let Some(src) = src {
                let val = self.read_var(state, src);
                let key = phi.dst.display_name();
                state.set_register(&key, val);
            }
        }

        // Execute operations
        for op in &block.ops {
            if !state.active {
                break;
            }

            let new_states = self.step(state, op)?;
            forked_states.extend(new_states);
            state.step();
        }

        Ok(forked_states)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(state.pc, 0x2000); // Branch taken
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
        assert_eq!(forked[0].pc, 0x2000); // True branch goes to target
        // Original state is false branch (PC unchanged in this test)
    }
}
