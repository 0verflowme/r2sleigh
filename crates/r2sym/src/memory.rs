//! Symbolic memory model for symbolic execution.
//!
//! This module provides a sparse memory model that can handle both
//! concrete and symbolic addresses and values.

use std::collections::{BTreeSet, HashMap};

use z3::ast::{BV, Bool};
use z3::{Context, SatResult, Solver};

use crate::value::SymValue;

/// A symbolic memory model.
///
/// Memory is modeled as a sparse map from addresses to byte values.
/// For symbolic addresses, we concretize a bounded set of targets and
/// build an ITE chain to select the correct value.
pub struct SymMemory<'ctx> {
    /// The Z3 context.
    ctx: &'ctx Context,
    /// Concrete memory (address -> byte value).
    concrete: HashMap<u64, u8>,
    /// Symbolic memory regions (for symbolic writes).
    /// Each entry represents a write: (address, value, size).
    symbolic_writes: Vec<(SymValue<'ctx>, SymValue<'ctx>, u32)>,
    /// Default value for uninitialized memory (0 or symbolic).
    default_symbolic: bool,
    /// Maximum number of symbolic address targets to enumerate.
    max_symbolic_targets: usize,
}

impl<'ctx> SymMemory<'ctx> {
    const DEFAULT_MAX_SYMBOLIC_TARGETS: usize = 256;

    /// Create a new empty memory.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            concrete: HashMap::new(),
            symbolic_writes: Vec::new(),
            default_symbolic: false,
            max_symbolic_targets: Self::DEFAULT_MAX_SYMBOLIC_TARGETS,
        }
    }

    /// Create memory with symbolic default values.
    pub fn new_symbolic(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            concrete: HashMap::new(),
            symbolic_writes: Vec::new(),
            default_symbolic: true,
            max_symbolic_targets: Self::DEFAULT_MAX_SYMBOLIC_TARGETS,
        }
    }

    /// Set the maximum number of symbolic targets to enumerate.
    pub fn set_max_symbolic_targets(&mut self, max: usize) {
        self.max_symbolic_targets = max;
    }

    pub(crate) fn merge_addrs(&self) -> Vec<u64> {
        let mut addrs = BTreeSet::new();
        addrs.extend(self.concrete.keys().copied());
        for (addr, _value, size) in &self.symbolic_writes {
            if let Some(base) = addr.as_concrete() {
                for offset in 0..*size {
                    addrs.insert(base.wrapping_add(offset as u64));
                }
            }
        }
        addrs.into_iter().collect()
    }

    pub(crate) fn symbolic_writes(&self) -> &[(SymValue<'ctx>, SymValue<'ctx>, u32)] {
        &self.symbolic_writes
    }

    pub(crate) fn push_symbolic_write(
        &mut self,
        addr: SymValue<'ctx>,
        value: SymValue<'ctx>,
        size: u32,
    ) {
        self.symbolic_writes.push((addr, value, size));
    }

    /// Read a value from memory.
    ///
    /// # Arguments
    /// * `addr` - The address to read from
    /// * `size` - The size in bytes to read
    pub fn read(&self, addr: &SymValue<'ctx>, size: u32) -> SymValue<'ctx> {
        self.read_with_constraints(addr, size, &[])
    }

    /// Read a value from memory with path constraints.
    pub fn read_with_constraints(
        &self,
        addr: &SymValue<'ctx>,
        size: u32,
        constraints: &[Bool],
    ) -> SymValue<'ctx> {
        if let Some(concrete_addr) = addr.as_concrete() {
            return self.read_concrete(concrete_addr, size);
        }

        let bits = size * 8;
        let addr_taint = addr.get_taint();
        let mut result = if self.default_symbolic {
            let ast = BV::fresh_const("mem_sym", bits);
            SymValue::symbolic_tainted(ast, bits, addr_taint)
        } else {
            SymValue::concrete_tainted(0, bits, addr_taint)
        };

        let (targets, _truncated) = self.enumerate_symbolic_addresses(addr, constraints);
        if targets.is_empty() {
            return result;
        }

        let addr_bv = addr.to_bv(self.ctx);
        for target in targets {
            let value = self.read_concrete(target, size).with_taint(addr_taint);
            let cond = addr_bv.eq(BV::from_u64(target, addr.bits()));
            let taint = value.get_taint() | result.get_taint();
            let merged = SymValue::symbolic_tainted(
                cond.ite(&value.to_bv(self.ctx), &result.to_bv(self.ctx)),
                bits,
                taint,
            );
            result = merged;
        }

        result
    }

    fn enumerate_symbolic_addresses(
        &self,
        addr: &SymValue<'ctx>,
        constraints: &[Bool],
    ) -> (Vec<u64>, bool) {
        if self.max_symbolic_targets == 0 {
            return (Vec::new(), true);
        }

        let solver = Solver::new();
        for constraint in constraints {
            solver.assert(constraint);
        }

        let addr_bv = addr.to_bv(self.ctx);
        let mut targets = Vec::new();
        let mut truncated = false;

        while targets.len() < self.max_symbolic_targets {
            if solver.check() != SatResult::Sat {
                break;
            }
            let model = match solver.get_model() {
                Some(model) => model,
                None => break,
            };
            let Some(value) = model.eval(&addr_bv, true).and_then(|v| v.as_u64()) else {
                truncated = true;
                break;
            };

            targets.push(value);
            let neq = addr_bv.eq(BV::from_u64(value, addr.bits())).not();
            solver.assert(&neq);
        }

        if targets.len() == self.max_symbolic_targets && solver.check() == SatResult::Sat {
            truncated = true;
        }

        (targets, truncated)
    }

    fn read_concrete(&self, concrete_addr: u64, size: u32) -> SymValue<'ctx> {
        // Check symbolic writes for this address (most recent first).
        for (write_addr, write_val, write_size) in self.symbolic_writes.iter().rev() {
            if let Some(wa) = write_addr.as_concrete() {
                let write_end = wa.checked_add(*write_size as u64);
                let read_end = concrete_addr.checked_add(size as u64);
                if let (Some(write_end), Some(read_end)) = (write_end, read_end)
                    && wa <= concrete_addr
                    && write_end >= read_end
                {
                    let offset = concrete_addr - wa;
                    if offset == 0 && *write_size == size {
                        return write_val.clone();
                    }
                    let low_bit = (offset * 8) as u32;
                    let high_bit = low_bit + (size * 8) - 1;
                    return write_val.extract(self.ctx, high_bit, low_bit);
                }
            }
        }

        let mut all_concrete = true;
        let mut value: u64 = 0;

        for i in 0..size {
            let byte_addr = concrete_addr.wrapping_add(i as u64);
            if let Some(&byte) = self.concrete.get(&byte_addr) {
                value |= (byte as u64) << (i * 8);
            } else {
                all_concrete = false;
                break;
            }
        }

        if all_concrete {
            return SymValue::concrete(value, size * 8);
        }

        if self.default_symbolic {
            SymValue::new_symbolic(self.ctx, &format!("mem_{:x}", concrete_addr), size * 8)
        } else {
            SymValue::concrete(0, size * 8)
        }
    }

    /// Write a value to memory.
    ///
    /// # Arguments
    /// * `addr` - The address to write to
    /// * `value` - The value to write
    /// * `size` - The size in bytes to write
    pub fn write(&mut self, addr: &SymValue<'ctx>, value: &SymValue<'ctx>, size: u32) {
        self.write_with_constraints(addr, value, size, &[]);
    }

    /// Write a value to memory with path constraints.
    pub fn write_with_constraints(
        &mut self,
        addr: &SymValue<'ctx>,
        value: &SymValue<'ctx>,
        size: u32,
        constraints: &[Bool],
    ) {
        let bits = size * 8;
        let value = adjust_bits(self.ctx, value, bits);

        if let Some(concrete_addr) = addr.as_concrete() {
            if let Some(concrete_value) = value.as_concrete() {
                for i in 0..size {
                    let byte_addr = concrete_addr.wrapping_add(i as u64);
                    let byte_value = ((concrete_value >> (i * 8)) & 0xFF) as u8;
                    self.concrete.insert(byte_addr, byte_value);
                }
            }
            self.symbolic_writes
                .push((addr.clone(), value.clone(), size));
            return;
        }

        let (targets, truncated) = self.enumerate_symbolic_addresses(addr, constraints);
        if targets.is_empty() {
            self.symbolic_writes
                .push((addr.clone(), value.clone(), size));
            return;
        }

        let addr_bv = addr.to_bv(self.ctx);
        for target in targets {
            let existing = self.read_concrete(target, size);
            let existing = adjust_bits(self.ctx, &existing, bits);
            let cond = addr_bv.eq(BV::from_u64(target, addr.bits()));
            let taint = existing.get_taint() | value.get_taint() | addr.get_taint();
            let merged = SymValue::symbolic_tainted(
                cond.ite(&value.to_bv(self.ctx), &existing.to_bv(self.ctx)),
                bits,
                taint,
            );
            let target_addr = SymValue::concrete(target, addr.bits());
            self.symbolic_writes.push((target_addr, merged, size));
        }

        if truncated {
            self.symbolic_writes
                .push((addr.clone(), value.clone(), size));
        }
    }

    /// Write concrete bytes to memory.
    pub fn write_bytes(&mut self, addr: u64, bytes: &[u8]) {
        for (i, &byte) in bytes.iter().enumerate() {
            self.concrete.insert(addr + i as u64, byte);
        }
    }

    /// Read concrete bytes from memory.
    pub fn read_bytes(&self, addr: u64, size: usize) -> Option<Vec<u8>> {
        let mut bytes = Vec::with_capacity(size);
        for i in 0..size {
            if let Some(&byte) = self.concrete.get(&(addr + i as u64)) {
                bytes.push(byte);
            } else {
                return None;
            }
        }
        Some(bytes)
    }

    /// Check if an address range is fully concrete.
    pub fn is_concrete_range(&self, addr: u64, size: u32) -> bool {
        for i in 0..size {
            if !self.concrete.contains_key(&(addr + i as u64)) {
                return false;
            }
        }
        true
    }

    /// Get the number of concrete bytes stored.
    pub fn concrete_size(&self) -> usize {
        self.concrete.len()
    }

    /// Get the number of symbolic writes.
    pub fn symbolic_writes_count(&self) -> usize {
        self.symbolic_writes.len()
    }

    /// Clone the memory state (for forking).
    pub fn fork(&self) -> Self {
        Self {
            ctx: self.ctx,
            concrete: self.concrete.clone(),
            symbolic_writes: self.symbolic_writes.clone(),
            default_symbolic: self.default_symbolic,
            max_symbolic_targets: self.max_symbolic_targets,
        }
    }

    /// Clear all memory.
    pub fn clear(&mut self) {
        self.concrete.clear();
        self.symbolic_writes.clear();
    }
}

fn adjust_bits<'ctx>(ctx: &'ctx Context, value: &SymValue<'ctx>, bits: u32) -> SymValue<'ctx> {
    if value.bits() == bits {
        return value.clone();
    }
    if value.bits() < bits {
        value.zero_extend(ctx, bits)
    } else {
        value.extract(ctx, bits - 1, 0)
    }
}

impl<'ctx> std::fmt::Debug for SymMemory<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymMemory")
            .field("concrete_bytes", &self.concrete.len())
            .field("symbolic_writes", &self.symbolic_writes.len())
            .field("default_symbolic", &self.default_symbolic)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::BV;
    use z3::{SatResult, Solver};

    #[test]
    fn test_concrete_read_write() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);

        let addr = SymValue::concrete(0x1000, 64);
        let value = SymValue::concrete(0xDEADBEEF, 32);

        mem.write(&addr, &value, 4);

        let read_value = mem.read(&addr, 4);
        assert_eq!(read_value.as_concrete(), Some(0xDEADBEEF));
    }

    #[test]
    fn test_byte_access() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);

        mem.write_bytes(0x1000, &[0x11, 0x22, 0x33, 0x44]);

        let bytes = mem.read_bytes(0x1000, 4).unwrap();
        assert_eq!(bytes, vec![0x11, 0x22, 0x33, 0x44]);

        let addr = SymValue::concrete(0x1000, 64);
        let value = mem.read(&addr, 4);
        assert_eq!(value.as_concrete(), Some(0x44332211)); // Little-endian
    }

    #[test]
    fn test_uninitialized_read() {
        let ctx = Context::thread_local();
        let mem = SymMemory::new(&ctx);

        let addr = SymValue::concrete(0x2000, 64);
        let value = mem.read(&addr, 4);
        // Default is concrete 0
        assert_eq!(value.as_concrete(), Some(0));
    }

    #[test]
    fn test_symbolic_default() {
        let ctx = Context::thread_local();
        let mem = SymMemory::new_symbolic(&ctx);

        let addr = SymValue::concrete(0x2000, 64);
        let value = mem.read(&addr, 4);
        // Default is symbolic
        assert!(value.is_symbolic());
    }

    #[test]
    fn test_symbolic_address_write_then_read() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);

        let idx = SymValue::new_symbolic(&ctx, "idx", 64);
        let addr_bv = idx.to_bv(&ctx);
        let eq1 = addr_bv.eq(BV::from_u64(0x1000, 64));
        let eq2 = addr_bv.eq(BV::from_u64(0x2000, 64));
        let constraint = eq1.clone() | eq2.clone();

        let value = SymValue::concrete(0xCAFEBABE, 32);
        mem.write_with_constraints(&idx, &value, 4, std::slice::from_ref(&constraint));

        let read_val = mem.read_with_constraints(&idx, 4, &[constraint]);
        assert!(read_val.is_symbolic());

        let solver = Solver::new();
        solver.assert(&eq1);
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let result_bv = read_val.to_bv(&ctx);
        let val = model.eval(&result_bv, true).unwrap().as_u64().unwrap();
        assert_eq!(val, 0xCAFEBABE);

        let solver = Solver::new();
        solver.assert(&eq2);
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let val = model.eval(&result_bv, true).unwrap().as_u64().unwrap();
        assert_eq!(val, 0xCAFEBABE);
    }

    #[test]
    fn test_merge_addrs_are_sorted() {
        let ctx = Context::thread_local();
        let mut mem = SymMemory::new(&ctx);

        mem.write_bytes(0x1003, &[0xaa]);
        mem.write_bytes(0x1000, &[0xbb]);
        mem.push_symbolic_write(
            SymValue::concrete(0x1001, 64),
            SymValue::concrete(0x1122, 16),
            2,
        );

        assert_eq!(mem.merge_addrs(), vec![0x1000, 0x1001, 0x1002, 0x1003]);
    }
}
