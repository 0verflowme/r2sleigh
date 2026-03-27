//! Symbolic execution state.
//!
//! This module provides the `SymState` type which represents the state
//! of the program during symbolic execution.

use std::collections::{HashMap, HashSet};

use z3::Context;
use z3::ast::{Ast, BV, Bool};

use crate::memory::{MemoryRegionId, MemoryRegionKind, SymMemory};
use crate::value::SymValue;

/// A tracked symbolic memory region (usually an input buffer).
#[derive(Debug, Clone)]
pub struct SymbolicMemoryRegion<'ctx> {
    /// Canonical region backing this symbolic buffer.
    pub region_id: MemoryRegionId,
    /// Name of the symbolic buffer.
    pub name: String,
    /// Concrete address of the buffer.
    pub addr: u64,
    /// Size in bytes.
    pub size: u32,
    /// Symbolic value representing the buffer contents.
    pub value: SymValue<'ctx>,
}

/// A tracked symbolic input stream for a file descriptor.
#[derive(Debug, Clone)]
pub struct SymbolicFdInput<'ctx> {
    /// Stable user-facing name of the stream.
    pub name: String,
    /// File descriptor identifier.
    pub fd: i32,
    /// Symbolic bytes available to the runtime model.
    pub bytes: Vec<SymValue<'ctx>>,
    /// Current read cursor.
    pub cursor: usize,
}

/// Runtime policy carried with each symbolic state.
#[derive(Debug, Clone, Default)]
pub struct RuntimeState {
    /// File descriptors that should report tty=true via isatty().
    pub tty_fds: HashSet<i32>,
    /// Whether sleep-family calls should become zero-cost no-ops.
    pub skip_sleep_calls: bool,
}

/// The state of a symbolic execution.
///
/// Contains registers, memory, path constraints, and program counter.
pub struct SymState<'ctx> {
    /// The Z3 context.
    ctx: &'ctx Context,
    /// Register values (register name -> value).
    registers: HashMap<String, SymValue<'ctx>>,
    /// Memory state.
    pub memory: SymMemory<'ctx>,
    /// Path constraints (conditions that must be true for this path).
    constraints: Vec<Bool>,
    /// Current program counter.
    pub pc: u64,
    /// Previous program counter (block predecessor).
    prev_pc: Option<u64>,
    /// Whether this state is still active (not terminated).
    pub active: bool,
    /// Exit status (if terminated).
    pub exit_status: Option<ExitStatus>,
    /// Execution depth (number of steps taken).
    pub depth: usize,
    /// Named symbolic inputs (registers or buffers).
    symbolic_inputs: HashMap<String, SymValue<'ctx>>,
    /// Tracked symbolic memory regions.
    symbolic_memory: Vec<SymbolicMemoryRegion<'ctx>>,
    /// Symbolic external input streams keyed by file descriptor.
    symbolic_fd_inputs: HashMap<i32, SymbolicFdInput<'ctx>>,
    /// Runtime policy/state for summaries.
    runtime: RuntimeState,
}

/// Exit status of a symbolic execution path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExitStatus {
    /// Normal return.
    Return,
    /// Program called exit() with the given code.
    Exit(u64),
    /// Hit an error/exception.
    Error(String),
    /// Hit an unimplemented operation.
    Unimplemented,
    /// Reached maximum depth.
    MaxDepth,
    /// Path is infeasible (constraints unsatisfiable).
    Infeasible,
}

impl<'ctx> SymState<'ctx> {
    /// Create a new symbolic state.
    pub fn new(ctx: &'ctx Context, entry_pc: u64) -> Self {
        Self {
            ctx,
            registers: HashMap::new(),
            memory: SymMemory::new(ctx),
            constraints: Vec::new(),
            pc: entry_pc,
            prev_pc: None,
            active: true,
            exit_status: None,
            depth: 0,
            symbolic_inputs: HashMap::new(),
            symbolic_memory: Vec::new(),
            symbolic_fd_inputs: HashMap::new(),
            runtime: RuntimeState::default(),
        }
    }

    /// Create a new state with symbolic memory.
    pub fn new_symbolic(ctx: &'ctx Context, entry_pc: u64) -> Self {
        Self {
            ctx,
            registers: HashMap::new(),
            memory: SymMemory::new_symbolic(ctx),
            constraints: Vec::new(),
            pc: entry_pc,
            prev_pc: None,
            active: true,
            exit_status: None,
            depth: 0,
            symbolic_inputs: HashMap::new(),
            symbolic_memory: Vec::new(),
            symbolic_fd_inputs: HashMap::new(),
            runtime: RuntimeState::default(),
        }
    }

    /// Get the Z3 context.
    pub fn context(&self) -> &'ctx Context {
        self.ctx
    }

    /// Get a register value.
    pub fn get_register(&self, name: &str) -> SymValue<'ctx> {
        self.get_register_sized(name, 64)
    }

    /// Get a register value with an expected bit width.
    pub fn get_register_sized(&self, name: &str, bits: u32) -> SymValue<'ctx> {
        self.registers
            .get(name)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(bits))
    }

    /// Set a register value.
    pub fn set_register(&mut self, name: &str, value: SymValue<'ctx>) {
        self.registers.insert(name.to_string(), value);
    }

    /// Make a register symbolic with a given name.
    pub fn make_symbolic(&mut self, reg_name: &str, bits: u32) {
        let sym_name = format!("sym_{}", reg_name);
        self.make_symbolic_named(reg_name, &sym_name, bits);
    }

    /// Make a register symbolic with an explicit symbol name.
    pub fn make_symbolic_named(&mut self, reg_name: &str, sym_name: &str, bits: u32) {
        let value = SymValue::new_symbolic(self.ctx, sym_name, bits);
        self.registers.insert(reg_name.to_string(), value.clone());
        self.symbolic_inputs.insert(sym_name.to_string(), value);
    }

    /// Set a register to a concrete value.
    pub fn set_concrete(&mut self, reg_name: &str, value: u64, bits: u32) {
        self.registers
            .insert(reg_name.to_string(), SymValue::concrete(value, bits));
    }

    /// Get all register names.
    pub fn register_names(&self) -> impl Iterator<Item = &String> {
        self.registers.keys()
    }

    /// Get the previous program counter.
    pub(crate) fn prev_pc(&self) -> Option<u64> {
        self.prev_pc
    }

    /// Set the previous program counter.
    pub(crate) fn set_prev_pc(&mut self, prev_pc: Option<u64>) {
        self.prev_pc = prev_pc;
    }

    /// Get all registers.
    pub fn registers(&self) -> &HashMap<String, SymValue<'ctx>> {
        &self.registers
    }

    /// Get tracked symbolic inputs.
    pub fn symbolic_inputs(&self) -> &HashMap<String, SymValue<'ctx>> {
        &self.symbolic_inputs
    }

    /// Get tracked symbolic memory regions.
    pub fn symbolic_memory(&self) -> &[SymbolicMemoryRegion<'ctx>] {
        &self.symbolic_memory
    }

    /// Get tracked symbolic file-descriptor inputs.
    pub fn symbolic_fd_inputs(&self) -> &HashMap<i32, SymbolicFdInput<'ctx>> {
        &self.symbolic_fd_inputs
    }

    /// Get runtime policy/state.
    pub fn runtime(&self) -> &RuntimeState {
        &self.runtime
    }

    pub(crate) fn semantic_fingerprint(&self) -> String {
        let mut registers: Vec<_> = self
            .registers
            .iter()
            .map(|(name, value)| {
                (
                    name.clone(),
                    value.to_bv(self.ctx).simplify().to_string(),
                    value.get_taint(),
                )
            })
            .collect();
        registers.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let registers_repr = registers
            .into_iter()
            .map(|(name, value, taint)| format!("{name}={value}@{taint}"))
            .collect::<Vec<_>>()
            .join(",");

        let mut symbolic_inputs: Vec<_> = self
            .symbolic_inputs
            .iter()
            .map(|(name, value)| {
                (
                    name.clone(),
                    value.to_bv(self.ctx).simplify().to_string(),
                    value.get_taint(),
                )
            })
            .collect();
        symbolic_inputs.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let symbolic_inputs_repr = symbolic_inputs
            .into_iter()
            .map(|(name, value, taint)| format!("{name}={value}@{taint}"))
            .collect::<Vec<_>>()
            .join(",");

        let mut symbolic_regions: Vec<_> = self
            .symbolic_memory
            .iter()
            .map(|region| {
                (
                    region.region_id,
                    region.name.clone(),
                    region.addr,
                    region.size,
                    region.value.to_bv(self.ctx).simplify().to_string(),
                    region.value.get_taint(),
                )
            })
            .collect();
        symbolic_regions.sort_unstable_by(|a, b| {
            a.0.cmp(&b.0)
                .then(a.1.cmp(&b.1))
                .then(a.2.cmp(&b.2))
                .then(a.3.cmp(&b.3))
        });
        let symbolic_regions_repr = symbolic_regions
            .into_iter()
            .map(|(region_id, name, addr, size, value, taint)| {
                format!("{}:{name}@{addr:x}:{size}={value}@{taint}", region_id.0)
            })
            .collect::<Vec<_>>()
            .join(",");

        let mut fd_inputs: Vec<_> = self
            .symbolic_fd_inputs
            .iter()
            .map(|(fd, input)| {
                let bytes = input
                    .bytes
                    .iter()
                    .map(|byte| format!("{}@{}", byte.to_bv(self.ctx).simplify(), byte.get_taint()))
                    .collect::<Vec<_>>()
                    .join("|");
                (*fd, input.name.clone(), input.cursor, bytes)
            })
            .collect();
        fd_inputs.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
        let fd_inputs_repr = fd_inputs
            .into_iter()
            .map(|(fd, name, cursor, bytes)| format!("{fd}:{name}@{cursor}[{bytes}]"))
            .collect::<Vec<_>>()
            .join(",");

        let mut tty_fds: Vec<_> = self.runtime.tty_fds.iter().copied().collect();
        tty_fds.sort_unstable();
        let tty_repr = tty_fds
            .into_iter()
            .map(|fd| fd.to_string())
            .collect::<Vec<_>>()
            .join(",");

        format!(
            "pc={:x};active={};exit={:?};regs=[{}];memory=({});inputs=[{}];regions=[{}];fds=[{}];tty=[{}];skip_sleep={}",
            self.pc,
            self.active,
            self.exit_status,
            registers_repr,
            self.memory.semantic_fingerprint(),
            symbolic_inputs_repr,
            symbolic_regions_repr,
            fd_inputs_repr,
            tty_repr,
            self.runtime.skip_sleep_calls
        )
    }

    /// Read from memory.
    pub fn mem_read(&self, addr: &SymValue<'ctx>, size: u32) -> SymValue<'ctx> {
        self.memory
            .read_with_constraints(addr, size, &self.constraints)
    }

    /// Write to memory.
    pub fn mem_write(&mut self, addr: &SymValue<'ctx>, value: &SymValue<'ctx>, size: u32) {
        self.memory
            .write_with_constraints(addr, value, size, &self.constraints);
    }

    /// Set the maximum number of symbolic address targets to enumerate.
    pub fn set_max_symbolic_targets(&mut self, max: usize) {
        self.memory.set_max_symbolic_targets(max);
    }

    /// Compute the path condition (AND of all constraints).
    pub fn path_condition(&self) -> Bool {
        and_all(self.ctx, &self.constraints)
    }

    /// Merge this state with another state at the same program counter.
    pub fn merge_with(&self, other: &SymState<'ctx>) -> Self {
        let cond_self = self.path_condition();
        let cond_other = other.path_condition();
        let mut merged = self.fork();

        merged.pc = self.pc;
        merged.prev_pc = if self.prev_pc == other.prev_pc {
            self.prev_pc
        } else {
            None
        };
        merged.active = self.active && other.active;
        merged.exit_status = None;
        merged.depth = self.depth.max(other.depth);
        merged.constraints = vec![cond_self | cond_other.clone()];

        let mut keys = HashSet::new();
        keys.extend(self.registers.keys().cloned());
        keys.extend(other.registers.keys().cloned());

        let mut registers = HashMap::with_capacity(keys.len());
        for key in keys {
            let val_self = self
                .registers
                .get(&key)
                .cloned()
                .or_else(|| {
                    other
                        .registers
                        .get(&key)
                        .map(|v| SymValue::unknown(v.bits()))
                })
                .unwrap_or_else(|| SymValue::unknown(1));
            let val_other = other
                .registers
                .get(&key)
                .cloned()
                .or_else(|| Some(SymValue::unknown(val_self.bits())))
                .unwrap();

            let merged_val = merge_values(self.ctx, &cond_other, &val_self, &val_other);
            registers.insert(key, merged_val);
        }
        merged.registers = registers;

        merged.memory = self.memory.merge_with(
            &other.memory,
            &self.constraints,
            &other.constraints,
            &cond_other,
        );

        merged.symbolic_inputs = self.symbolic_inputs.clone();
        for (name, value) in &other.symbolic_inputs {
            merged
                .symbolic_inputs
                .entry(name.clone())
                .or_insert_with(|| value.clone());
        }

        merged.symbolic_memory = self.symbolic_memory.clone();
        for region in &other.symbolic_memory {
            let exists = merged.symbolic_memory.iter().any(|r| {
                r.region_id == region.region_id
                    && r.name == region.name
                    && r.addr == region.addr
                    && r.size == region.size
            });
            if !exists {
                merged.symbolic_memory.push(region.clone());
            }
        }

        merged.symbolic_fd_inputs = self.symbolic_fd_inputs.clone();
        for (fd, other_input) in &other.symbolic_fd_inputs {
            match merged.symbolic_fd_inputs.get_mut(fd) {
                Some(existing) => {
                    if existing.bytes.len() < other_input.bytes.len() {
                        existing.bytes = other_input.bytes.clone();
                    }
                    existing.cursor = existing.cursor.max(other_input.cursor);
                }
                None => {
                    merged.symbolic_fd_inputs.insert(*fd, other_input.clone());
                }
            }
        }

        merged.runtime = self.runtime.clone();
        merged.runtime.skip_sleep_calls |= other.runtime.skip_sleep_calls;
        merged
            .runtime
            .tty_fds
            .extend(other.runtime.tty_fds.iter().copied());

        merged
    }

    /// Add a path constraint.
    pub fn add_constraint(&mut self, constraint: Bool) {
        self.constraints.push(constraint);
    }

    /// Constrain a value to equal a concrete constant.
    pub fn constrain_eq(&mut self, value: &SymValue<'ctx>, rhs: u64) {
        let bv = value.to_bv(self.ctx);
        let rhs_bv = BV::from_u64(rhs, value.bits());
        self.add_constraint(bv.eq(&rhs_bv));
    }

    /// Constrain a value to not equal a concrete constant.
    pub fn constrain_ne(&mut self, value: &SymValue<'ctx>, rhs: u64) {
        let bv = value.to_bv(self.ctx);
        let rhs_bv = BV::from_u64(rhs, value.bits());
        self.add_constraint(bv.eq(&rhs_bv).not());
    }

    /// Constrain a value to be within an unsigned range [min, max].
    pub fn constrain_range(&mut self, value: &SymValue<'ctx>, min: u64, max: u64) {
        let bv = value.to_bv(self.ctx);
        let min_bv = BV::from_u64(min, value.bits());
        let max_bv = BV::from_u64(max, value.bits());
        let ge = bv.bvuge(&min_bv);
        let le = bv.bvule(&max_bv);
        self.add_constraint(ge & le);
    }

    /// Constrain bytes of a bitvector to an exact string or a simple pattern.
    ///
    /// Patterns use the form "[A-Za-z0-9]" and apply to every byte.
    pub fn constrain_bytes(&mut self, value: &SymValue<'ctx>, pattern: &str) {
        let bits = value.bits();
        if bits < 8 {
            return;
        }

        let bv = value.to_bv(self.ctx);
        let bytes = (bits / 8) as usize;

        let is_pattern = pattern.starts_with('[') && pattern.ends_with(']');
        if !is_pattern {
            let pat_bytes = pattern.as_bytes();
            let limit = std::cmp::min(bytes, pat_bytes.len());
            for (i, &pat_byte) in pat_bytes.iter().enumerate().take(limit) {
                let byte_bv = bv.extract((i as u32 + 1) * 8 - 1, (i as u32) * 8);
                let expected = BV::from_u64(pat_byte as u64, 8);
                self.add_constraint(byte_bv.eq(&expected));
            }
            return;
        }

        let content = &pattern[1..pattern.len() - 1];
        let ranges = parse_byte_ranges(content);
        if ranges.is_empty() {
            return;
        }

        for i in 0..bytes {
            let byte_bv = bv.extract((i as u32 + 1) * 8 - 1, (i as u32) * 8);
            let mut ors = Vec::with_capacity(ranges.len());
            for (lo, hi) in &ranges {
                let lo_bv = BV::from_u64(*lo as u64, 8);
                let hi_bv = BV::from_u64(*hi as u64, 8);
                if lo == hi {
                    ors.push(byte_bv.eq(&lo_bv));
                } else {
                    ors.push(byte_bv.bvuge(&lo_bv) & byte_bv.bvule(&hi_bv));
                }
            }
            self.add_constraint(or_all(self.ctx, &ors));
        }
    }

    /// Constrain a value to contain a substring.
    pub fn constrain_contains(&mut self, value: &SymValue<'ctx>, needle: &str) {
        self.constrain_contains_inner(value, needle, true);
    }

    /// Constrain a value to not contain a substring.
    pub fn constrain_not_contains(&mut self, value: &SymValue<'ctx>, needle: &str) {
        self.constrain_contains_inner(value, needle, false);
    }

    fn constrain_contains_inner(
        &mut self,
        value: &SymValue<'ctx>,
        needle: &str,
        must_contain: bool,
    ) {
        let needle_bytes = needle.as_bytes();
        if needle_bytes.is_empty() {
            return;
        }

        let total_bytes = (value.bits() / 8) as usize;
        if total_bytes < needle_bytes.len() {
            if must_contain {
                // Create a false constraint using the helper
                self.add_constraint(bool_false());
            }
            return;
        }

        let bv = value.to_bv(self.ctx);
        let mut matches = Vec::new();
        for offset in 0..=total_bytes - needle_bytes.len() {
            let mut ands = Vec::with_capacity(needle_bytes.len());
            for (i, byte) in needle_bytes.iter().enumerate() {
                let low = ((offset + i) as u32) * 8;
                let high = low + 7;
                let byte_bv = bv.extract(high, low);
                let expected = BV::from_u64(*byte as u64, 8);
                ands.push(byte_bv.eq(&expected));
            }
            matches.push(and_all(self.ctx, &ands));
        }

        let contains = or_all(self.ctx, &matches);
        if must_contain {
            self.add_constraint(contains);
        } else {
            self.add_constraint(contains.not());
        }
    }

    /// Add a constraint that a value is true (non-zero).
    pub fn add_true_constraint(&mut self, value: &SymValue<'ctx>) {
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_u64(0, value.bits());
        let cond = bv.eq(&zero).not();
        self.constraints.push(cond);
    }

    /// Add a constraint that a value is false (zero).
    pub fn add_false_constraint(&mut self, value: &SymValue<'ctx>) {
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_u64(0, value.bits());
        let cond = bv.eq(&zero);
        self.constraints.push(cond);
    }

    /// Get all path constraints.
    pub fn constraints(&self) -> &[Bool] {
        &self.constraints
    }

    /// Get the number of constraints.
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Terminate this state with the given status.
    pub fn terminate(&mut self, status: ExitStatus) {
        self.active = false;
        self.exit_status = Some(status);
    }

    /// Check if this state has terminated.
    pub fn is_terminated(&self) -> bool {
        !self.active
    }

    /// Increment the execution depth.
    pub fn step(&mut self) {
        self.depth += 1;
    }

    /// Fork this state (for branching).
    pub fn fork(&self) -> Self {
        Self {
            ctx: self.ctx,
            registers: self.registers.clone(),
            memory: self.memory.fork(),
            constraints: self.constraints.clone(),
            pc: self.pc,
            prev_pc: self.prev_pc,
            active: self.active,
            exit_status: self.exit_status.clone(),
            depth: self.depth,
            symbolic_inputs: self.symbolic_inputs.clone(),
            symbolic_memory: self.symbolic_memory.clone(),
            symbolic_fd_inputs: self.symbolic_fd_inputs.clone(),
            runtime: self.runtime.clone(),
        }
    }

    /// Create a forked state with an additional constraint.
    pub fn fork_with_constraint(&self, constraint: Bool) -> Self {
        let mut forked = self.fork();
        forked.add_constraint(constraint);
        forked
    }

    /// Create a named symbolic input value.
    pub fn new_symbolic_input(&mut self, name: &str, bits: u32) -> SymValue<'ctx> {
        let value = SymValue::new_symbolic(self.ctx, name, bits);
        self.symbolic_inputs.insert(name.to_string(), value.clone());
        value
    }

    /// Create a named symbolic input value with taint.
    pub fn new_symbolic_input_tainted(
        &mut self,
        name: &str,
        bits: u32,
        taint: u64,
    ) -> SymValue<'ctx> {
        let value = SymValue::new_symbolic_tainted(self.ctx, name, bits, taint);
        self.symbolic_inputs.insert(name.to_string(), value.clone());
        value
    }

    /// Create a symbolic buffer at a concrete address and track it.
    pub fn make_symbolic_memory(&mut self, addr: u64, size: u32, name: &str) -> SymValue<'ctx> {
        self.make_symbolic_memory_tainted(addr, size, name, 0)
    }

    /// Create a tainted symbolic buffer at a concrete address and track it.
    pub fn make_symbolic_memory_tainted(
        &mut self,
        addr: u64,
        size: u32,
        name: &str,
        taint: u64,
    ) -> SymValue<'ctx> {
        let value = if taint == 0 {
            SymValue::new_symbolic(self.ctx, name, size * 8)
        } else {
            SymValue::new_symbolic_tainted(self.ctx, name, size * 8, taint)
        };
        let region_id =
            self.define_memory_region(MemoryRegionKind::Input, name, Some(addr), Some(size as u64));
        let addr_val = SymValue::concrete(addr, 64);
        self.mem_write(&addr_val, &value, size);
        self.symbolic_inputs.insert(name.to_string(), value.clone());
        self.symbolic_memory.push(SymbolicMemoryRegion {
            region_id,
            name: name.to_string(),
            addr,
            size,
            value: value.clone(),
        });
        value
    }

    /// Define a canonical memory region for the symbolic state.
    pub fn define_memory_region(
        &mut self,
        kind: MemoryRegionKind,
        name: &str,
        base_addr: Option<u64>,
        extent: Option<u64>,
    ) -> MemoryRegionId {
        self.memory.define_region(kind, name, base_addr, extent)
    }

    /// Seed concrete bytes into an existing memory region.
    pub fn seed_region_bytes(&mut self, region_id: MemoryRegionId, offset: u64, bytes: &[u8]) {
        self.memory.seed_region_bytes(region_id, offset, bytes);
    }

    /// Allocate a deterministic heap region and return its concrete base pointer.
    pub fn allocate_heap_region(&mut self, name: &str, size: u64) -> (MemoryRegionId, u64) {
        self.memory.allocate_heap_region(name, size)
    }

    /// Configure tty behavior for a concrete file descriptor.
    pub fn set_tty_fd(&mut self, fd: i32, is_tty: bool) {
        if is_tty {
            self.runtime.tty_fds.insert(fd);
        } else {
            self.runtime.tty_fds.remove(&fd);
        }
    }

    /// Check whether a file descriptor should behave like a tty.
    pub fn is_tty_fd(&self, fd: i32) -> bool {
        self.runtime.tty_fds.contains(&fd)
    }

    /// Configure whether sleep-family calls should be skipped.
    pub fn set_skip_sleep_calls(&mut self, enabled: bool) {
        self.runtime.skip_sleep_calls = enabled;
    }

    /// Check whether sleep-family calls should be skipped.
    pub fn skip_sleep_calls(&self) -> bool {
        self.runtime.skip_sleep_calls
    }

    /// Register a symbolic byte stream for a file descriptor.
    pub fn add_symbolic_fd_input(
        &mut self,
        fd: i32,
        len: usize,
        name: &str,
        alphabet: Option<&str>,
    ) {
        let mut bytes = Vec::with_capacity(len);
        for idx in 0..len {
            let byte_name = format!("{}_{}", name, idx);
            let byte = SymValue::new_symbolic(self.ctx, &byte_name, 8);
            if let Some(alphabet) = alphabet {
                constrain_symbolic_byte_to_alphabet(self, &byte, alphabet);
            }
            self.symbolic_inputs.insert(byte_name, byte.clone());
            bytes.push(byte);
        }
        self.symbolic_fd_inputs.insert(
            fd,
            SymbolicFdInput {
                name: name.to_string(),
                fd,
                bytes,
                cursor: 0,
            },
        );
    }

    /// Read up to `count` bytes from a tracked symbolic file descriptor.
    pub fn read_symbolic_fd_bytes(&mut self, fd: i32, count: usize) -> Option<Vec<SymValue<'ctx>>> {
        let input = self.symbolic_fd_inputs.get_mut(&fd)?;
        if input.cursor >= input.bytes.len() {
            return Some(Vec::new());
        }
        let end = input.cursor.saturating_add(count).min(input.bytes.len());
        let bytes = input.bytes[input.cursor..end].to_vec();
        input.cursor = end;
        Some(bytes)
    }
}

fn constrain_symbolic_byte_to_alphabet<'ctx>(
    state: &mut SymState<'ctx>,
    value: &SymValue<'ctx>,
    alphabet: &str,
) {
    let allowed = alphabet.as_bytes();
    if allowed.is_empty() {
        return;
    }
    let byte_bv = value.to_bv(state.context());
    let ors: Vec<Bool> = allowed
        .iter()
        .map(|byte| byte_bv.eq(BV::from_u64(*byte as u64, 8)))
        .collect();
    state.add_constraint(or_all(state.context(), &ors));
}

fn parse_byte_ranges(pattern: &str) -> Vec<(u8, u8)> {
    let bytes = pattern.as_bytes();
    let mut ranges = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let start = bytes[i];
        if i + 2 < bytes.len() && bytes[i + 1] == b'-' {
            let end = bytes[i + 2];
            ranges.push((start, end));
            i += 3;
        } else {
            ranges.push((start, start));
            i += 1;
        }
    }
    ranges
}

fn bool_true() -> Bool {
    // Create true using z3 0.19 API (uses thread-local context)
    let one = BV::from_u64(1, 8);
    one.eq(&one)
}

fn bool_false() -> Bool {
    // Create false using z3 0.19 API (uses thread-local context)
    let zero = BV::from_u64(0, 8);
    let one = BV::from_u64(1, 8);
    zero.eq(&one)
}

fn and_all(_ctx: &Context, values: &[Bool]) -> Bool {
    if values.is_empty() {
        return bool_true();
    }
    // Chain with bitwise AND
    let mut acc = values[0].clone();
    for val in &values[1..] {
        acc &= val;
    }
    acc
}

fn or_all(_ctx: &Context, values: &[Bool]) -> Bool {
    if values.is_empty() {
        return bool_false();
    }
    // Chain with bitwise OR
    let mut acc = values[0].clone();
    for val in &values[1..] {
        acc |= val;
    }
    acc
}

fn merge_values<'ctx>(
    ctx: &'ctx Context,
    cond: &Bool,
    base: &SymValue<'ctx>,
    incoming: &SymValue<'ctx>,
) -> SymValue<'ctx> {
    let bits = base.bits().max(incoming.bits());
    let taint = base.get_taint() | incoming.get_taint();
    let base_bv = widen_value(ctx, base, bits);
    let incoming_bv = widen_value(ctx, incoming, bits);
    SymValue::symbolic_tainted(cond.ite(&incoming_bv, &base_bv), bits, taint)
}

fn widen_value<'ctx>(ctx: &'ctx Context, value: &SymValue<'ctx>, bits: u32) -> BV {
    let bv = value.to_bv(ctx);
    let value_bits = value.bits();
    if value_bits == bits {
        bv
    } else if value_bits < bits {
        bv.zero_ext(bits - value_bits)
    } else {
        bv.extract(bits - 1, 0)
    }
}

impl<'ctx> std::fmt::Debug for SymState<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymState")
            .field("pc", &format!("0x{:x}", self.pc))
            .field("prev_pc", &self.prev_pc.map(|pc| format!("0x{:x}", pc)))
            .field("registers", &self.registers.len())
            .field("constraints", &self.constraints.len())
            .field("depth", &self.depth)
            .field("symbolic_inputs", &self.symbolic_inputs.len())
            .field("symbolic_memory", &self.symbolic_memory.len())
            .field("active", &self.active)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::BV;
    use z3::{SatResult, Solver};

    #[test]
    fn test_state_creation() {
        let ctx = Context::thread_local();

        let state = SymState::new(&ctx, 0x1000);
        assert_eq!(state.pc, 0x1000);
        assert!(state.active);
        assert_eq!(state.depth, 0);
    }

    #[test]
    fn test_register_access() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);

        state.set_concrete("rax", 42, 64);
        let rax = state.get_register("rax");
        assert_eq!(rax.as_concrete(), Some(42));

        state.make_symbolic("rbx", 64);
        let rbx = state.get_register("rbx");
        assert!(rbx.is_symbolic());
    }

    #[test]
    fn test_memory_access() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);

        let addr = SymValue::concrete(0x2000, 64);
        let value = SymValue::concrete(0xDEADBEEF, 32);

        state.mem_write(&addr, &value, 4);
        let read = state.mem_read(&addr, 4);
        assert_eq!(read.as_concrete(), Some(0xDEADBEEF));
    }

    #[test]
    fn test_fork() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.set_concrete("rax", 42, 64);
        state.pc = 0x2000;

        let forked = state.fork();
        assert_eq!(forked.pc, 0x2000);
        assert_eq!(forked.get_register("rax").as_concrete(), Some(42));
    }

    #[test]
    fn test_constraints() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("rax", 64);

        let rax = state.get_register("rax");
        state.add_true_constraint(&rax);

        assert_eq!(state.num_constraints(), 1);
    }

    #[test]
    fn test_symbolic_memory_tracking() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        let sym = state.make_symbolic_memory(0x3000, 4, "input_buf");

        assert!(sym.is_symbolic());
        assert_eq!(state.symbolic_memory().len(), 1);
        assert!(state.symbolic_inputs().contains_key("input_buf"));
    }

    #[test]
    fn test_constrain_bytes_pattern() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        let sym = state.new_symbolic_input("sym", 16);
        state.constrain_bytes(&sym, "[A-Z]");

        assert_eq!(state.num_constraints(), 2);
    }

    #[test]
    fn test_merge_registers_with_constraints() {
        let ctx = Context::thread_local();

        let mut state_a = SymState::new(&ctx, 0x1000);
        let x_a = SymValue::new_symbolic(&ctx, "x", 32);
        state_a.set_register("x", x_a.clone());
        state_a.add_constraint(x_a.to_bv(&ctx).eq(BV::from_u64(0, 32)));
        state_a.set_register("rax", SymValue::concrete(1, 64));

        let mut state_b = SymState::new(&ctx, 0x1000);
        let x_b = SymValue::new_symbolic(&ctx, "x", 32);
        state_b.set_register("x", x_b.clone());
        state_b.add_constraint(x_b.to_bv(&ctx).eq(BV::from_u64(1, 32)));
        state_b.set_register("rax", SymValue::concrete(2, 64));

        let merged = state_a.merge_with(&state_b);
        let merged_rax = merged.get_register("rax");

        let solver = Solver::new();
        solver.assert(merged.path_condition());
        solver.assert(x_b.to_bv(&ctx).eq(BV::from_u64(0, 32)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let val = model
            .eval(&merged_rax.to_bv(&ctx), true)
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(val, 1);

        let solver = Solver::new();
        solver.assert(merged.path_condition());
        solver.assert(x_b.to_bv(&ctx).eq(BV::from_u64(1, 32)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let val = model
            .eval(&merged_rax.to_bv(&ctx), true)
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(val, 2);
    }

    #[test]
    fn test_merge_memory_preserves_region_only_present_on_one_side() {
        let ctx = Context::thread_local();

        let mut state_a = SymState::new(&ctx, 0x1000);
        let x_a = SymValue::new_symbolic(&ctx, "x", 32);
        state_a.set_register("x", x_a.clone());
        state_a.add_constraint(x_a.to_bv(&ctx).eq(BV::from_u64(0, 32)));

        let mut state_b = SymState::new(&ctx, 0x1000);
        let x_b = SymValue::new_symbolic(&ctx, "x", 32);
        state_b.set_register("x", x_b.clone());
        state_b.add_constraint(x_b.to_bv(&ctx).eq(BV::from_u64(1, 32)));
        state_b.define_memory_region(MemoryRegionKind::Replay, "replay", Some(0x9000), Some(0x10));
        state_b.mem_write(
            &SymValue::concrete(0x9000, 64),
            &SymValue::concrete(0xab, 8),
            1,
        );

        let merged = state_a.merge_with(&state_b);
        let merged_byte = merged.mem_read(&SymValue::concrete(0x9000, 64), 1);

        let solver = Solver::new();
        solver.assert(merged.path_condition());
        solver.assert(x_b.to_bv(&ctx).eq(BV::from_u64(0, 32)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let value = model
            .eval(&merged_byte.to_bv(&ctx), true)
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(value, 0);

        let solver = Solver::new();
        solver.assert(merged.path_condition());
        solver.assert(x_b.to_bv(&ctx).eq(BV::from_u64(1, 32)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let value = model
            .eval(&merged_byte.to_bv(&ctx), true)
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(value, 0xab);
    }
}
