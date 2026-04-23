//! Symbolic execution state.
//!
//! This module provides the `SymState` type which represents the state
//! of the program during symbolic execution.

use std::cell::OnceCell;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use z3::Context;
use z3::ast::{BV, Bool};

use crate::memory::{MemoryRegionId, MemoryRegionKind, SymMemory};
use crate::value::SymValue;

fn debug_runtime_continuation_log(message: &str) {
    if std::env::var_os("R2SLEIGH_DEBUG_RUNTIME_CONTINUATION").is_none() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_RUNTIME_CONTINUATION_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_runtime_continuation.log".to_string());
    if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        use std::io::Write;
        let _ = writeln!(file, "{message}");
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ConstraintCursorKey(usize);

impl ConstraintCursorKey {
    pub(crate) const ROOT: Self = Self(0);
}

#[derive(Clone, Default)]
struct ConstraintCursor {
    node: Option<Rc<ConstraintNode>>,
}

struct ConstraintNode {
    id: ConstraintCursorKey,
    parent: Option<Rc<ConstraintNode>>,
    constraint: Bool,
    depth: usize,
    hash: u64,
}

impl ConstraintCursor {
    fn key(&self) -> ConstraintCursorKey {
        self.node
            .as_ref()
            .map_or(ConstraintCursorKey::ROOT, |node| node.id)
    }

    fn depth(&self) -> usize {
        self.node.as_ref().map_or(0, |node| node.depth)
    }

    fn hash(&self) -> u64 {
        self.node.as_ref().map_or(0, |node| node.hash)
    }

    fn push(&self, constraint: Bool) -> Self {
        let constraint_hash = structural_hash(&constraint);
        let hash = mix_hash(self.hash(), constraint_hash);
        let depth = self.depth().saturating_add(1);
        Self {
            node: Some(Rc::new(ConstraintNode {
                id: next_constraint_cursor_key(),
                parent: self.node.clone(),
                constraint,
                depth,
                hash,
            })),
        }
    }

    fn materialize(&self) -> Vec<Bool> {
        let mut values = Vec::with_capacity(self.depth());
        let mut current = self.node.as_ref().cloned();
        while let Some(node) = current {
            values.push(node.constraint.clone());
            current = node.parent.clone();
        }
        values.reverse();
        values
    }

    fn is_descendant_of(&self, ancestor: &Self) -> bool {
        if ancestor.node.is_none() {
            return true;
        }
        let ancestor_key = ancestor.key();
        let mut current = self.node.as_ref().cloned();
        while let Some(node) = current {
            if node.id == ancestor_key {
                return true;
            }
            current = node.parent.clone();
        }
        false
    }

    fn suffix_from_key(
        &self,
        ancestor_key: ConstraintCursorKey,
    ) -> Option<Vec<(ConstraintCursorKey, Bool)>> {
        let mut suffix = Vec::new();
        let mut current = self.node.as_ref().cloned();
        while let Some(node) = current {
            if node.id == ancestor_key {
                suffix.reverse();
                return Some(suffix);
            }
            suffix.push((node.id, node.constraint.clone()));
            current = node.parent.clone();
        }
        if ancestor_key == ConstraintCursorKey::ROOT {
            suffix.reverse();
            Some(suffix)
        } else {
            None
        }
    }
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuntimeBlockReason {
    MissingExceptionHandler,
    MissingRuntimeMaterializedCode,
    MissingContinuationSeed,
    RuntimeRegionProvenanceUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RuntimeValueProvenance {
    pub source_addr: u64,
    pub size: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RuntimeRegionAlias {
    pub runtime_base: u64,
    pub size: u64,
    pub source_base: Option<u64>,
    pub executable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PendingExceptionContinuation {
    pub handler_addr: u64,
    pub exception_code: u64,
    pub exception_pointers_addr: u64,
    pub exception_record_addr: u64,
    pub context_addr: u64,
}

#[derive(Debug, Clone)]
pub struct RuntimeBreakpointContinuation<'ctx> {
    pub handler_addr: u64,
    pub exception_code: u64,
    pub breakpoint: SymValue<'ctx>,
}

/// Runtime policy carried with each symbolic state.
#[derive(Debug, Clone, Default)]
pub struct RuntimeState<'ctx> {
    /// File descriptors that should report tty=true via isatty().
    pub tty_fds: HashSet<i32>,
    /// Whether sleep-family calls should become zero-cost no-ops.
    pub skip_sleep_calls: bool,
    /// Registered exception handlers discovered by runtime hooks.
    pub exception_handlers: BTreeSet<u64>,
    /// Runtime regions that may alias materialized executable code.
    pub runtime_regions: BTreeMap<u64, RuntimeRegionAlias>,
    /// Provenance for recently loaded values used to detect copy loops.
    pub value_provenance: BTreeMap<String, RuntimeValueProvenance>,
    /// Pending exception continuation state that should resume on handler return.
    pub pending_exception: Option<PendingExceptionContinuation>,
    /// Active runtime breakpoint that re-enters an exception handler when reached.
    pub active_breakpoint: Option<RuntimeBreakpointContinuation<'ctx>>,
}

/// The state of a symbolic execution.
///
/// Contains registers, memory, path constraints, and program counter.
pub struct SymState<'ctx> {
    /// The Z3 context.
    ctx: &'ctx Context,
    /// Register values (register name -> value).
    registers: Rc<HashMap<String, SymValue<'ctx>>>,
    /// Memory state.
    pub memory: SymMemory<'ctx>,
    /// Path constraints (conditions that must be true for this path).
    constraints: ConstraintCursor,
    /// Materialized constraint list, populated lazily from the shared cursor chain.
    materialized_constraints: OnceCell<Vec<Bool>>,
    /// Syntactic value facts derived while adding constraints.
    known_zero_values: Rc<BTreeSet<String>>,
    known_nonzero_values: Rc<BTreeSet<String>>,
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
    symbolic_inputs: Rc<HashMap<String, SymValue<'ctx>>>,
    /// Tracked symbolic memory regions.
    symbolic_memory: Rc<Vec<SymbolicMemoryRegion<'ctx>>>,
    /// Symbolic external input streams keyed by file descriptor.
    symbolic_fd_inputs: Rc<HashMap<i32, SymbolicFdInput<'ctx>>>,
    /// Runtime policy/state for summaries.
    runtime: RuntimeState<'ctx>,
}

/// Exit status of a symbolic execution path.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExitStatus {
    /// Normal return.
    Return,
    /// Program called exit() with the given code.
    Exit(u64),
    /// Hit an error/exception.
    Error(String),
    /// Runtime execution was blocked because a required dynamic fact was missing.
    RuntimeBlocked(RuntimeBlockReason),
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
            registers: Rc::new(HashMap::new()),
            memory: SymMemory::new(ctx),
            constraints: ConstraintCursor::default(),
            materialized_constraints: OnceCell::new(),
            known_zero_values: Rc::new(BTreeSet::new()),
            known_nonzero_values: Rc::new(BTreeSet::new()),
            pc: entry_pc,
            prev_pc: None,
            active: true,
            exit_status: None,
            depth: 0,
            symbolic_inputs: Rc::new(HashMap::new()),
            symbolic_memory: Rc::new(Vec::new()),
            symbolic_fd_inputs: Rc::new(HashMap::new()),
            runtime: RuntimeState::default(),
        }
    }

    /// Create a new state with symbolic memory.
    pub fn new_symbolic(ctx: &'ctx Context, entry_pc: u64) -> Self {
        Self {
            ctx,
            registers: Rc::new(HashMap::new()),
            memory: SymMemory::new_symbolic(ctx),
            constraints: ConstraintCursor::default(),
            materialized_constraints: OnceCell::new(),
            known_zero_values: Rc::new(BTreeSet::new()),
            known_nonzero_values: Rc::new(BTreeSet::new()),
            pc: entry_pc,
            prev_pc: None,
            active: true,
            exit_status: None,
            depth: 0,
            symbolic_inputs: Rc::new(HashMap::new()),
            symbolic_memory: Rc::new(Vec::new()),
            symbolic_fd_inputs: Rc::new(HashMap::new()),
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
        Rc::make_mut(&mut self.registers).insert(name.to_string(), value);
    }

    /// Make a register symbolic with a given name.
    pub fn make_symbolic(&mut self, reg_name: &str, bits: u32) {
        let sym_name = format!("sym_{}", reg_name);
        self.make_symbolic_named(reg_name, &sym_name, bits);
    }

    /// Make a register symbolic with an explicit symbol name.
    pub fn make_symbolic_named(&mut self, reg_name: &str, sym_name: &str, bits: u32) {
        let value = SymValue::new_symbolic(self.ctx, sym_name, bits);
        Rc::make_mut(&mut self.registers).insert(reg_name.to_string(), value.clone());
        Rc::make_mut(&mut self.symbolic_inputs).insert(sym_name.to_string(), value);
    }

    /// Set a register to a concrete value.
    pub fn set_concrete(&mut self, reg_name: &str, value: u64, bits: u32) {
        Rc::make_mut(&mut self.registers)
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
        self.registers.as_ref()
    }

    /// Get tracked symbolic inputs.
    pub fn symbolic_inputs(&self) -> &HashMap<String, SymValue<'ctx>> {
        self.symbolic_inputs.as_ref()
    }

    /// Get tracked symbolic memory regions.
    pub fn symbolic_memory(&self) -> &[SymbolicMemoryRegion<'ctx>] {
        self.symbolic_memory.as_slice()
    }

    /// Return whether every byte in a concrete address range is known concrete.
    pub fn is_concrete_memory_range(&self, addr: u64, size: u32) -> bool {
        self.memory.is_concrete_range(addr, size)
    }

    /// Read concrete bytes from memory when the full range is concrete.
    pub fn read_memory_bytes(&self, addr: u64, size: usize) -> Option<Vec<u8>> {
        self.memory.read_bytes(addr, size)
    }

    /// Get tracked symbolic file-descriptor inputs.
    pub fn symbolic_fd_inputs(&self) -> &HashMap<i32, SymbolicFdInput<'ctx>> {
        self.symbolic_fd_inputs.as_ref()
    }

    /// Get runtime policy/state.
    pub fn runtime(&self) -> &RuntimeState<'ctx> {
        &self.runtime
    }

    pub fn register_exception_handler(&mut self, addr: u64) {
        self.runtime.exception_handlers.insert(addr);
    }

    pub fn primary_exception_handler(&self) -> Option<u64> {
        self.runtime.exception_handlers.iter().next().copied()
    }

    pub fn define_runtime_region(
        &mut self,
        name: &str,
        base_addr: u64,
        size: u64,
        executable: bool,
    ) -> MemoryRegionId {
        let region_id =
            self.define_memory_region(MemoryRegionKind::Heap, name, Some(base_addr), Some(size));
        self.runtime
            .runtime_regions
            .entry(base_addr)
            .or_insert(RuntimeRegionAlias {
                runtime_base: base_addr,
                size,
                source_base: None,
                executable,
            });
        region_id
    }

    pub fn register_runtime_region_alias(&mut self, base_addr: u64, size: u64, executable: bool) {
        self.runtime
            .runtime_regions
            .entry(base_addr)
            .and_modify(|region| {
                region.size = region.size.max(size);
                region.executable |= executable;
            })
            .or_insert(RuntimeRegionAlias {
                runtime_base: base_addr,
                size,
                source_base: None,
                executable,
            });
    }

    pub fn mark_runtime_region_executable(&mut self, base_addr: u64, size: u64) -> bool {
        let mut updated = false;
        for region in self.runtime.runtime_regions.values_mut() {
            let region_end = region.runtime_base.saturating_add(region.size);
            let end = base_addr.saturating_add(size);
            if base_addr < region_end && region.runtime_base < end {
                region.executable = true;
                updated = true;
            }
        }
        updated
    }

    pub fn runtime_region_for_pc(&self, pc: u64) -> Option<&RuntimeRegionAlias> {
        self.runtime.runtime_regions.values().find(|region| {
            pc >= region.runtime_base && pc < region.runtime_base.saturating_add(region.size)
        })
    }

    pub fn resolve_runtime_pc(&self, pc: u64) -> Option<u64> {
        let region = self.runtime_region_for_pc(pc)?;
        if !region.executable {
            return None;
        }
        let source_base = region.source_base?;
        let offset = pc.checked_sub(region.runtime_base)?;
        (offset < region.size).then_some(source_base.saturating_add(offset))
    }

    pub fn remap_static_pc_to_runtime(&self, static_pc: u64) -> Option<u64> {
        self.runtime.runtime_regions.values().find_map(|region| {
            let source_base = region.source_base?;
            let offset = static_pc.checked_sub(source_base)?;
            (offset < region.size && region.executable)
                .then_some(region.runtime_base.saturating_add(offset))
        })
    }

    pub fn set_value_provenance(&mut self, name: &str, provenance: Option<RuntimeValueProvenance>) {
        if let Some(provenance) = provenance {
            self.runtime
                .value_provenance
                .insert(name.to_string(), provenance);
        } else {
            self.runtime.value_provenance.remove(name);
        }
    }

    pub fn value_provenance(&self, name: &str) -> Option<&RuntimeValueProvenance> {
        self.runtime.value_provenance.get(name)
    }

    pub fn note_runtime_store_copy(
        &mut self,
        store_addr: u64,
        size: u32,
        provenance: Option<&RuntimeValueProvenance>,
    ) {
        let Some(provenance) = provenance else {
            return;
        };
        let Some(region_base) = self
            .runtime
            .runtime_regions
            .values()
            .find(|region| {
                store_addr >= region.runtime_base
                    && store_addr < region.runtime_base.saturating_add(region.size)
            })
            .map(|region| region.runtime_base)
        else {
            return;
        };
        let Some(region) = self.runtime.runtime_regions.get_mut(&region_base) else {
            return;
        };
        let Some(offset) = store_addr.checked_sub(region.runtime_base) else {
            return;
        };
        let Some(candidate_source_base) = provenance.source_addr.checked_sub(offset) else {
            return;
        };
        match region.source_base {
            None => region.source_base = Some(candidate_source_base),
            Some(existing) if existing == candidate_source_base => {}
            Some(_) => region.source_base = None,
        }
        let copied_extent = offset.saturating_add(size as u64);
        if copied_extent > region.size {
            region.size = copied_extent;
        }
    }

    pub fn set_pending_exception(&mut self, pending: PendingExceptionContinuation) {
        self.runtime.pending_exception = Some(pending);
    }

    pub fn pending_exception(&self) -> Option<&PendingExceptionContinuation> {
        self.runtime.pending_exception.as_ref()
    }

    pub(crate) fn clear_pending_exception(&mut self) {
        self.runtime.pending_exception = None;
    }

    fn write_u32(&mut self, addr: u64, value: u32) {
        self.mem_write(
            &SymValue::concrete(addr, 64),
            &SymValue::concrete(value as u64, 32),
            4,
        );
    }

    fn write_u64(&mut self, addr: u64, value: u64) {
        self.mem_write(
            &SymValue::concrete(addr, 64),
            &SymValue::concrete(value, 64),
            8,
        );
    }

    fn read_register_family(&self, base: &str) -> SymValue<'ctx> {
        let lower = base.to_ascii_lowercase();
        let mut best: Option<(u64, &String)> = None;
        for key in self.registers.keys() {
            let key_lower = key.to_ascii_lowercase();
            if let Some((prefix, suffix)) = key_lower.rsplit_once('_')
                && prefix == lower
                && let Ok(version) = suffix.parse::<u64>()
            {
                if best.is_none_or(|(best_version, _)| version > best_version) {
                    best = Some((version, key));
                }
            } else if key_lower == lower {
                return self.get_register_sized(key, 64);
            }
        }
        best.map_or_else(
            || SymValue::unknown(64),
            |(_, key)| self.get_register_sized(key, 64),
        )
    }

    fn write_register_to_context(&mut self, context_addr: u64, base: &str, offset: u64) {
        let value = self.read_register_family(base);
        self.mem_write(
            &SymValue::concrete(context_addr.saturating_add(offset), 64),
            &value,
            8,
        );
    }

    pub(crate) fn seed_exception_continuation(&mut self, exception_code: u64, handler_addr: u64) {
        let (_, record_addr) = self.allocate_heap_region("veh_exception_record", 0x20);
        let (_, context_addr) = self.allocate_heap_region("veh_exception_context", 0x400);
        let (_, pointers_addr) = self.allocate_heap_region("veh_exception_pointers", 0x10);

        self.write_u32(record_addr, exception_code as u32);
        self.write_u64(pointers_addr, record_addr);
        self.write_u64(pointers_addr.saturating_add(8), context_addr);
        self.write_register_to_context(context_addr, "RAX", 0x78);
        self.write_register_to_context(context_addr, "RCX", 0x80);
        self.write_register_to_context(context_addr, "RDX", 0x88);
        self.write_register_to_context(context_addr, "RBX", 0x90);
        self.write_register_to_context(context_addr, "RSP", 0x98);
        self.write_register_to_context(context_addr, "RBP", 0xA0);
        self.write_register_to_context(context_addr, "RSI", 0xA8);
        self.write_register_to_context(context_addr, "RDI", 0xB0);
        self.write_register_to_context(context_addr, "R8", 0xB8);
        self.write_register_to_context(context_addr, "R9", 0xC0);
        self.write_register_to_context(context_addr, "R10", 0xC8);
        self.write_register_to_context(context_addr, "R11", 0xD0);
        self.write_register_to_context(context_addr, "R12", 0xD8);
        self.write_register_to_context(context_addr, "R13", 0xE0);
        self.write_register_to_context(context_addr, "R14", 0xE8);
        self.write_register_to_context(context_addr, "R15", 0xF0);
        self.write_u64(context_addr.saturating_add(0xF8), self.pc);
        self.set_concrete("RCX_0", pointers_addr, 64);
        self.set_pending_exception(PendingExceptionContinuation {
            handler_addr,
            exception_code,
            exception_pointers_addr: pointers_addr,
            exception_record_addr: record_addr,
            context_addr,
        });
    }

    pub(crate) fn dispatch_runtime_breakpoint_if_ready(&mut self) -> bool {
        let Some(breakpoint) = self.runtime.active_breakpoint.clone() else {
            return false;
        };
        let Some(breakpoint_addr) = breakpoint.breakpoint.as_concrete() else {
            return false;
        };
        if self.pc != breakpoint_addr {
            return false;
        }
        self.runtime.active_breakpoint = None;
        self.seed_exception_continuation(breakpoint.exception_code, breakpoint.handler_addr);
        self.pc = breakpoint.handler_addr;
        debug_runtime_continuation_log(&format!(
            "runtime_breakpoint_dispatch pc=0x{:x} handler=0x{:x} code=0x{:x}",
            breakpoint_addr, breakpoint.handler_addr, breakpoint.exception_code
        ));
        true
    }

    pub(crate) fn fork_symbolic_runtime_breakpoint_at(&mut self, pc: u64) -> Option<Self> {
        let breakpoint = self.runtime.active_breakpoint.clone()?;
        if breakpoint.breakpoint.as_concrete().is_some() {
            return None;
        }
        self.runtime_region_for_pc(pc)?;

        let mut dispatched = self.fork();
        dispatched.constrain_eq(&breakpoint.breakpoint, pc);
        dispatched.runtime.active_breakpoint = None;
        dispatched.seed_exception_continuation(breakpoint.exception_code, breakpoint.handler_addr);
        dispatched.pc = breakpoint.handler_addr;
        self.constrain_ne(&breakpoint.breakpoint, pc);

        debug_runtime_continuation_log(&format!(
            "runtime_breakpoint_symbolic_fork pc=0x{:x} handler=0x{:x} code=0x{:x}",
            pc, breakpoint.handler_addr, breakpoint.exception_code
        ));
        Some(dispatched)
    }

    pub fn set_pending_exception_resume_pc(&mut self, resume_pc: u64) -> bool {
        let Some(pending) = self.runtime.pending_exception.as_ref() else {
            return false;
        };
        self.mem_write(
            &SymValue::concrete(pending.context_addr.saturating_add(0xF8), 64),
            &SymValue::concrete(resume_pc, 64),
            8,
        );
        true
    }

    pub fn resume_pending_exception_continuation(
        &mut self,
    ) -> Result<Option<u64>, RuntimeBlockReason> {
        let Some(pending) = self.runtime.pending_exception.clone() else {
            return Ok(None);
        };
        let read_u32 = |state: &Self, addr: u64| state.mem_read(&SymValue::concrete(addr, 64), 4);
        let read_u64 = |state: &Self, addr: u64| state.mem_read(&SymValue::concrete(addr, 64), 8);
        let restore_register = |state: &mut Self, name: &str, offset: u64| {
            let value = read_u64(state, pending.context_addr.saturating_add(offset));
            state.set_register(&format!("{name}_0"), value);
        };
        restore_register(self, "RAX", 0x78);
        restore_register(self, "RCX", 0x80);
        restore_register(self, "RDX", 0x88);
        restore_register(self, "RBX", 0x90);
        restore_register(self, "RSP", 0x98);
        restore_register(self, "RBP", 0xA0);
        restore_register(self, "RSI", 0xA8);
        restore_register(self, "RDI", 0xB0);
        restore_register(self, "R8", 0xB8);
        restore_register(self, "R9", 0xC0);
        restore_register(self, "R10", 0xC8);
        restore_register(self, "R11", 0xD0);
        restore_register(self, "R12", 0xD8);
        restore_register(self, "R13", 0xE0);
        restore_register(self, "R14", 0xE8);
        restore_register(self, "R15", 0xF0);
        let rip = read_u64(self, pending.context_addr.saturating_add(0xF8));
        let Some(rip) = rip.as_concrete() else {
            return Err(RuntimeBlockReason::MissingContinuationSeed);
        };
        let breakpoint = read_u64(self, pending.context_addr.saturating_add(0x48));
        let debug_context_requested = read_u32(self, pending.context_addr.saturating_add(0x30))
            .as_concrete()
            .is_some_and(|value| value & 0x10 != 0);
        let dr7_enabled = read_u64(self, pending.context_addr.saturating_add(0x70))
            .as_concrete()
            .is_some_and(|value| value != 0);
        let breakpoint_enabled = debug_context_requested || dr7_enabled;
        self.runtime.active_breakpoint = if pending.exception_code == 0x8000_0004
            && breakpoint_enabled
            && self.runtime_region_for_pc(rip).is_some()
            && !breakpoint.is_unknown()
        {
            Some(RuntimeBreakpointContinuation {
                handler_addr: pending.handler_addr,
                exception_code: pending.exception_code,
                breakpoint: breakpoint.clone(),
            })
        } else {
            None
        };
        debug_runtime_continuation_log(&format!(
            "runtime_resume handler=0x{:x} code=0x{:x} rip=0x{:x} breakpoint={} debug_context={} dr7={} active={}",
            pending.handler_addr,
            pending.exception_code,
            rip,
            breakpoint.as_concrete().map_or_else(
                || format!("symbolic:{}b", breakpoint.bits()),
                |value| format!("0x{value:x}")
            ),
            debug_context_requested,
            dr7_enabled,
            self.runtime.active_breakpoint.is_some()
        ));
        self.runtime.pending_exception = None;
        Ok(Some(rip))
    }

    pub(crate) fn semantic_fingerprint(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.pc.hash(&mut hasher);
        self.active.hash(&mut hasher);
        self.exit_status.hash(&mut hasher);
        self.memory.semantic_fingerprint().hash(&mut hasher);
        self.runtime.skip_sleep_calls.hash(&mut hasher);

        let mut tty_fds: Vec<_> = self.runtime.tty_fds.iter().copied().collect();
        tty_fds.sort_unstable();
        tty_fds.hash(&mut hasher);

        self.runtime.exception_handlers.hash(&mut hasher);
        for (base, region) in &self.runtime.runtime_regions {
            base.hash(&mut hasher);
            region.hash(&mut hasher);
        }
        let mut provenance = self.runtime.value_provenance.iter().collect::<Vec<_>>();
        provenance.sort_unstable_by(|a, b| a.0.cmp(b.0));
        for (name, source) in provenance {
            name.hash(&mut hasher);
            source.hash(&mut hasher);
        }
        self.runtime.pending_exception.hash(&mut hasher);
        if let Some(breakpoint) = &self.runtime.active_breakpoint {
            breakpoint.handler_addr.hash(&mut hasher);
            breakpoint.exception_code.hash(&mut hasher);
            hash_sym_value(self.ctx, &breakpoint.breakpoint, &mut hasher);
        }

        let mut register_names: Vec<_> = self.registers.keys().collect();
        register_names.sort_unstable();
        for name in register_names {
            name.hash(&mut hasher);
            hash_sym_value(self.ctx, &self.registers[name], &mut hasher);
        }

        self.known_zero_values.hash(&mut hasher);
        self.known_nonzero_values.hash(&mut hasher);

        let mut symbolic_input_names: Vec<_> = self.symbolic_inputs.keys().collect();
        symbolic_input_names.sort_unstable();
        for name in symbolic_input_names {
            name.hash(&mut hasher);
            hash_sym_value(self.ctx, &self.symbolic_inputs[name], &mut hasher);
        }

        for region in self.symbolic_memory.iter() {
            region.region_id.hash(&mut hasher);
            region.name.hash(&mut hasher);
            region.addr.hash(&mut hasher);
            region.size.hash(&mut hasher);
            hash_sym_value(self.ctx, &region.value, &mut hasher);
        }

        let mut fd_inputs: Vec<_> = self.symbolic_fd_inputs.iter().collect();
        fd_inputs.sort_unstable_by(|a, b| a.0.cmp(b.0));
        for (fd, input) in fd_inputs {
            fd.hash(&mut hasher);
            input.name.hash(&mut hasher);
            input.cursor.hash(&mut hasher);
            for byte in &input.bytes {
                hash_sym_value(self.ctx, byte, &mut hasher);
            }
        }

        hasher.finish()
    }

    /// Read from memory.
    pub fn mem_read(&self, addr: &SymValue<'ctx>, size: u32) -> SymValue<'ctx> {
        self.memory
            .read_with_constraints(addr, size, self.constraints())
    }

    /// Write to memory.
    pub fn mem_write(&mut self, addr: &SymValue<'ctx>, value: &SymValue<'ctx>, size: u32) {
        let constraints = self.constraints().to_vec();
        self.memory
            .write_with_constraints(addr, value, size, &constraints);
    }

    /// Set the maximum number of symbolic address targets to enumerate.
    pub fn set_max_symbolic_targets(&mut self, max: usize) {
        self.memory.set_max_symbolic_targets(max);
    }

    /// Compute the path condition (AND of all constraints).
    pub fn path_condition(&self) -> Bool {
        and_all(self.ctx, self.constraints())
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
        merged.constraints = ConstraintCursor::default();
        merged.materialized_constraints = OnceCell::new();
        merged.add_constraint(cond_self | cond_other.clone());
        merged.known_zero_values = Rc::new(
            self.known_zero_values
                .intersection(&other.known_zero_values)
                .cloned()
                .collect(),
        );
        merged.known_nonzero_values = Rc::new(
            self.known_nonzero_values
                .intersection(&other.known_nonzero_values)
                .cloned()
                .collect(),
        );

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
        merged.registers = Rc::new(registers);

        merged.memory = self.memory.merge_with(
            &other.memory,
            self.constraints(),
            other.constraints(),
            &cond_other,
        );

        merged.symbolic_inputs = self.symbolic_inputs.clone();
        for (name, value) in other.symbolic_inputs.iter() {
            Rc::make_mut(&mut merged.symbolic_inputs)
                .entry(name.clone())
                .or_insert_with(|| value.clone());
        }

        merged.symbolic_memory = self.symbolic_memory.clone();
        for region in other.symbolic_memory.iter() {
            let exists = merged.symbolic_memory.iter().any(|r| {
                r.region_id == region.region_id
                    && r.name == region.name
                    && r.addr == region.addr
                    && r.size == region.size
            });
            if !exists {
                Rc::make_mut(&mut merged.symbolic_memory).push(region.clone());
            }
        }

        merged.symbolic_fd_inputs = self.symbolic_fd_inputs.clone();
        for (fd, other_input) in other.symbolic_fd_inputs.iter() {
            let fd_inputs = Rc::make_mut(&mut merged.symbolic_fd_inputs);
            match fd_inputs.get_mut(fd) {
                Some(existing) => {
                    if existing.bytes.len() < other_input.bytes.len() {
                        existing.bytes = other_input.bytes.clone();
                    }
                    existing.cursor = existing.cursor.max(other_input.cursor);
                }
                None => {
                    fd_inputs.insert(*fd, other_input.clone());
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
            .runtime
            .exception_handlers
            .extend(other.runtime.exception_handlers.iter().copied());
        for (base, other_region) in &other.runtime.runtime_regions {
            match merged.runtime.runtime_regions.get_mut(base) {
                Some(existing) => {
                    existing.size = existing.size.max(other_region.size);
                    existing.executable |= other_region.executable;
                    if existing.source_base != other_region.source_base {
                        existing.source_base = None;
                    }
                }
                None => {
                    merged
                        .runtime
                        .runtime_regions
                        .insert(*base, other_region.clone());
                }
            }
        }
        merged.runtime.pending_exception = (self.runtime.pending_exception
            == other.runtime.pending_exception)
            .then(|| self.runtime.pending_exception.clone())
            .flatten();
        merged.runtime.active_breakpoint = match (
            &self.runtime.active_breakpoint,
            &other.runtime.active_breakpoint,
        ) {
            (Some(left), Some(right)) if runtime_breakpoint_equal(self.ctx, left, right) => {
                Some(left.clone())
            }
            _ => None,
        };
        merged.runtime.value_provenance.retain(|name, source| {
            other
                .runtime
                .value_provenance
                .get(name)
                .is_some_and(|other_source| other_source == source)
        });

        merged
    }

    /// Add a path constraint.
    pub fn add_constraint(&mut self, constraint: Bool) {
        self.constraints = self.constraints.push(constraint.clone());
        if let Some(mut cached) = self.materialized_constraints.take() {
            cached.push(constraint);
            let _ = self.materialized_constraints.set(cached);
        }
    }

    fn mark_value_zero(&mut self, value: &SymValue<'ctx>) {
        let Some(key) = value.symbolic_key() else {
            return;
        };
        Rc::make_mut(&mut self.known_nonzero_values).remove(&key);
        Rc::make_mut(&mut self.known_zero_values).insert(key);
    }

    fn mark_value_nonzero(&mut self, value: &SymValue<'ctx>) {
        let Some(key) = value.symbolic_key() else {
            return;
        };
        Rc::make_mut(&mut self.known_zero_values).remove(&key);
        Rc::make_mut(&mut self.known_nonzero_values).insert(key);
    }

    pub(crate) fn value_known_zero(&self, value: &SymValue<'ctx>) -> bool {
        value
            .symbolic_key()
            .is_some_and(|key| self.known_zero_values.contains(&key))
    }

    pub(crate) fn value_known_nonzero(&self, value: &SymValue<'ctx>) -> bool {
        value
            .symbolic_key()
            .is_some_and(|key| self.known_nonzero_values.contains(&key))
    }

    /// Constrain a value to equal a concrete constant.
    pub fn constrain_eq(&mut self, value: &SymValue<'ctx>, rhs: u64) {
        let bv = value.to_bv(self.ctx);
        let rhs_bv = BV::from_u64(rhs, value.bits());
        self.add_constraint(bv.eq(&rhs_bv));
        if rhs == 0 {
            self.mark_value_zero(value);
        }
    }

    /// Constrain a value to not equal a concrete constant.
    pub fn constrain_ne(&mut self, value: &SymValue<'ctx>, rhs: u64) {
        let bv = value.to_bv(self.ctx);
        let rhs_bv = BV::from_u64(rhs, value.bits());
        self.add_constraint(bv.eq(&rhs_bv).not());
        if rhs == 0 {
            self.mark_value_nonzero(value);
        }
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
        self.add_constraint(cond);
        self.mark_value_nonzero(value);
    }

    /// Add a constraint that a value is false (zero).
    pub fn add_false_constraint(&mut self, value: &SymValue<'ctx>) {
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_u64(0, value.bits());
        let cond = bv.eq(&zero);
        self.add_constraint(cond);
        self.mark_value_zero(value);
    }

    /// Get all path constraints.
    pub fn constraints(&self) -> &[Bool] {
        self.materialized_constraints
            .get_or_init(|| self.constraints.materialize())
            .as_slice()
    }

    /// Get the number of constraints.
    pub fn num_constraints(&self) -> usize {
        self.constraints.depth()
    }

    pub(crate) fn constraint_cursor_key(&self) -> ConstraintCursorKey {
        self.constraints.key()
    }

    pub(crate) fn constraints_imply_by_prefix(&self, other: &Self) -> bool {
        self.constraints.is_descendant_of(&other.constraints)
    }

    pub(crate) fn constraint_suffix_from_cursor(
        &self,
        ancestor: ConstraintCursorKey,
    ) -> Option<Vec<(ConstraintCursorKey, Bool)>> {
        self.constraints.suffix_from_key(ancestor)
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

    /// Increment the execution depth by a known number of concrete steps.
    pub fn step_by(&mut self, steps: usize) {
        self.depth = self.depth.saturating_add(steps);
    }

    /// Fork this state (for branching).
    pub fn fork(&self) -> Self {
        Self {
            ctx: self.ctx,
            registers: self.registers.clone(),
            memory: self.memory.fork(),
            constraints: self.constraints.clone(),
            materialized_constraints: OnceCell::new(),
            known_zero_values: self.known_zero_values.clone(),
            known_nonzero_values: self.known_nonzero_values.clone(),
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
        Rc::make_mut(&mut self.symbolic_inputs).insert(name.to_string(), value.clone());
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
        Rc::make_mut(&mut self.symbolic_inputs).insert(name.to_string(), value.clone());
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
        Rc::make_mut(&mut self.symbolic_inputs).insert(name.to_string(), value.clone());
        Rc::make_mut(&mut self.symbolic_memory).push(SymbolicMemoryRegion {
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
            Rc::make_mut(&mut self.symbolic_inputs).insert(byte_name, byte.clone());
            bytes.push(byte);
        }
        Rc::make_mut(&mut self.symbolic_fd_inputs).insert(
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
        let input = Rc::make_mut(&mut self.symbolic_fd_inputs).get_mut(&fd)?;
        if input.cursor >= input.bytes.len() {
            return Some(Vec::new());
        }
        let end = input.cursor.saturating_add(count).min(input.bytes.len());
        let bytes = input.bytes[input.cursor..end].to_vec();
        input.cursor = end;
        Some(bytes)
    }
}

fn mix_hash(seed: u64, value: u64) -> u64 {
    seed.rotate_left(7) ^ value.wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

fn next_constraint_cursor_key() -> ConstraintCursorKey {
    static NEXT_ID: AtomicUsize = AtomicUsize::new(1);
    ConstraintCursorKey(NEXT_ID.fetch_add(1, Ordering::Relaxed))
}

fn structural_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn runtime_breakpoint_equal<'ctx>(
    ctx: &'ctx Context,
    left: &RuntimeBreakpointContinuation<'ctx>,
    right: &RuntimeBreakpointContinuation<'ctx>,
) -> bool {
    if left.handler_addr != right.handler_addr || left.exception_code != right.exception_code {
        return false;
    }
    let mut left_hasher = DefaultHasher::new();
    hash_sym_value(ctx, &left.breakpoint, &mut left_hasher);
    let mut right_hasher = DefaultHasher::new();
    hash_sym_value(ctx, &right.breakpoint, &mut right_hasher);
    left_hasher.finish() == right_hasher.finish()
}

fn hash_sym_value<'ctx, H: Hasher>(ctx: &'ctx Context, value: &SymValue<'ctx>, hasher: &mut H) {
    value.bits().hash(hasher);
    value.get_taint().hash(hasher);
    value.to_bv(ctx).hash(hasher);
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
            .field("constraints", &self.num_constraints())
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

    #[test]
    fn test_runtime_region_copy_alias_resolves_runtime_pc() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);

        let _ = state.define_runtime_region("jit_blob", 0x6000_0000, 0x1000, true);
        state.note_runtime_store_copy(
            0x6000_0010,
            1,
            Some(&RuntimeValueProvenance {
                source_addr: 0x1400_1000,
                size: 1,
            }),
        );

        assert_eq!(state.resolve_runtime_pc(0x6000_0010), Some(0x1400_1000));
        assert_eq!(
            state.remap_static_pc_to_runtime(0x1400_1010),
            Some(0x6000_0020)
        );
    }

    #[test]
    fn test_resume_pending_exception_continuation_restores_rip() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let (_, context_addr) = state.allocate_heap_region("context", 0x400);
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0x80), 64),
            &SymValue::concrete(0x1122_3344_5566_7788, 64),
            8,
        );
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0xF8), 64),
            &SymValue::concrete(0x6000_1234, 64),
            8,
        );
        state.set_pending_exception(PendingExceptionContinuation {
            handler_addr: 0x401000,
            exception_code: 0x8000_0004,
            exception_pointers_addr: 0x7000_0000,
            exception_record_addr: 0x7000_0100,
            context_addr,
        });

        let resumed = state
            .resume_pending_exception_continuation()
            .expect("continuation should resume");

        assert_eq!(resumed, Some(0x6000_1234));
        assert_eq!(
            state.get_register("RCX_0").as_concrete(),
            Some(0x1122_3344_5566_7788)
        );
        assert!(state.pending_exception().is_none());
    }

    #[test]
    fn test_set_pending_exception_resume_pc_updates_context_rip() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let (_, context_addr) = state.allocate_heap_region("context", 0x400);
        state.set_pending_exception(PendingExceptionContinuation {
            handler_addr: 0x401000,
            exception_code: 0x8000_0004,
            exception_pointers_addr: 0x7000_0000,
            exception_record_addr: 0x7000_0100,
            context_addr,
        });

        assert!(state.set_pending_exception_resume_pc(0x6000_5678));
        assert_eq!(
            state
                .mem_read(
                    &SymValue::concrete(context_addr.saturating_add(0xF8), 64),
                    8
                )
                .as_concrete(),
            Some(0x6000_5678)
        );
    }

    #[test]
    fn test_runtime_breakpoint_continuation_reenters_handler() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let _ = state.define_runtime_region("jit", 0x6000_0000, 0x1000, true);
        state.note_runtime_store_copy(
            0x6000_0000,
            0x1000,
            Some(&RuntimeValueProvenance {
                source_addr: 0x1400_0000,
                size: 0x1000,
            }),
        );
        let (_, context_addr) = state.allocate_heap_region("context", 0x400);
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0x48), 64),
            &SymValue::concrete(0x6000_0020, 64),
            8,
        );
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0x70), 64),
            &SymValue::concrete(1, 64),
            8,
        );
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0xF8), 64),
            &SymValue::concrete(0x6000_0010, 64),
            8,
        );
        state.set_pending_exception(PendingExceptionContinuation {
            handler_addr: 0x401000,
            exception_code: 0x8000_0004,
            exception_pointers_addr: 0x7000_0000,
            exception_record_addr: 0x7000_0100,
            context_addr,
        });

        let resumed = state
            .resume_pending_exception_continuation()
            .expect("runtime continuation should resume");

        assert_eq!(resumed, Some(0x6000_0010));
        state.pc = 0x6000_0020;
        assert!(state.dispatch_runtime_breakpoint_if_ready());
        assert_eq!(state.pc, 0x401000);
        assert!(state.pending_exception().is_some());
    }

    #[test]
    fn test_runtime_breakpoint_continuation_accepts_debug_context_flag() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let _ = state.define_runtime_region("jit", 0x6000_0000, 0x1000, true);
        state.note_runtime_store_copy(
            0x6000_0000,
            0x1000,
            Some(&RuntimeValueProvenance {
                source_addr: 0x1400_0000,
                size: 0x1000,
            }),
        );
        let (_, context_addr) = state.allocate_heap_region("context", 0x400);
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0x30), 64),
            &SymValue::concrete(0x100010, 32),
            4,
        );
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0x48), 64),
            &SymValue::concrete(0x6000_0030, 64),
            8,
        );
        state.mem_write(
            &SymValue::concrete(context_addr.saturating_add(0xF8), 64),
            &SymValue::concrete(0x6000_0010, 64),
            8,
        );
        state.set_pending_exception(PendingExceptionContinuation {
            handler_addr: 0x401000,
            exception_code: 0x8000_0004,
            exception_pointers_addr: 0x7000_0000,
            exception_record_addr: 0x7000_0100,
            context_addr,
        });

        assert_eq!(
            state
                .resume_pending_exception_continuation()
                .expect("debug-register continuation should resume"),
            Some(0x6000_0010)
        );
        state.pc = 0x6000_0030;
        assert!(state.dispatch_runtime_breakpoint_if_ready());
        assert_eq!(state.pc, 0x401000);
        assert!(state.pending_exception().is_some());
    }
}
