//! Function summaries for common library calls.
//!
//! These summaries short-circuit into lightweight models to avoid
//! path explosion from libc implementations.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;
use std::sync::Arc;

use r2il::{AddressSpace, ArchSpec, Endianness, RegisterDef};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, FunctionSemanticSummary, InterprocFunctionId,
    InterprocFunctionInput, InterprocSolveConfig, InterprocSummarySet, MachineArchitectureFamily,
    MachineMemoryEndianness, PreparedInterprocFunctionInput, PreparedInterprocSummaryError,
    PreparedInterprocSummarySet, SsaArtifact, SsaArtifactProvenanceKind, SummaryMemoryEffectKind,
    SummaryMemoryRegion, SummaryReturnRelation, solve_interproc_summary_set,
    solve_prepared_interproc_summary_set,
};
use serde::{Deserialize, Serialize};
use z3::ast::{Ast, BV, Bool};

use crate::executor::{CallHookResult, SymExecutor};
use crate::path::PathExplorer;
use crate::solver::{SatResult, SymSolver};
use crate::state::{ExitStatus, RuntimeValueProvenance, SymState};
use crate::value::SymValue;

/// Default upper bound for string operations.
pub const DEFAULT_MAX_STRLEN: u64 = 0x1000;
/// Default upper bound for memory copy operations.
pub const DEFAULT_MAX_MEMCPY: u64 = 0x1000;
/// Default upper bound for memory set operations.
pub const DEFAULT_MAX_MEMSET: u64 = 0x1000;
/// Default upper bound for memcmp operations.
pub const DEFAULT_MAX_MEMCMP: u64 = 0x1000;
/// Default upper bound for basic printf/puts modeled return values.
pub const DEFAULT_MAX_PRINTF_SCAN: u64 = 0x400;
/// Default upper bound for generic interproc memory havoc windows.
pub const DEFAULT_MAX_INTERPROC_HAVOC: u64 = 0x40;
/// Path-listing upper bound for memory copy operations.
pub const PATH_LIST_MAX_MEMCPY: u64 = 0x40;
/// Path-listing upper bound for memory set operations.
pub const PATH_LIST_MAX_MEMSET: u64 = 0x40;
/// Path-listing upper bound for string operations.
pub const PATH_LIST_MAX_STRLEN: u64 = 0x80;
/// Path-listing upper bound for memcmp operations.
pub const PATH_LIST_MAX_MEMCMP: u64 = 0x40;
/// Path-listing upper bound for printf/puts modeled return values.
pub const PATH_LIST_MAX_PRINTF_SCAN: u64 = 0x40;
/// Path-listing precise-byte threshold before summaries switch to coarse modeling.
pub const PATH_LIST_PRECISE_BYTE_LIMIT: u64 = 0x10;
/// Default state budget for derived symbolic helper summaries.
pub const DEFAULT_DERIVED_SUMMARY_MAX_STATES: usize = 64;
/// Default path cap for derived helper summarization.
pub const DEFAULT_DERIVED_SUMMARY_MAX_PATHS: usize = 8;
/// Default depth budget for derived helper summarization.
pub const DEFAULT_DERIVED_SUMMARY_MAX_DEPTH: usize = 128;
/// Default bounded fixed-point iteration count for derived helper SCCs.
pub const DEFAULT_DERIVED_SUMMARY_MAX_ITERATIONS: usize = 8;

/// Summary profile used to install function summaries for different workflows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SummaryProfile {
    /// Default symbolic execution behavior.
    Default,
    /// Fast bounded modeling for path-listing workflows.
    PathListing,
}

#[derive(Debug, Clone, Copy)]
struct SummaryBudgets {
    max_strlen: u64,
    max_memcpy: u64,
    max_memset: u64,
    max_memcmp: u64,
    max_printf_scan: u64,
    byte_policy: ByteSummaryPolicy,
}

#[derive(Debug, Clone, Copy)]
struct ByteSummaryPolicy {
    summarize_symbolic: bool,
    summarize_large: bool,
    precise_limit: u64,
}

impl ByteSummaryPolicy {
    const fn precise(max_bytes: u64) -> Self {
        Self {
            summarize_symbolic: false,
            summarize_large: false,
            precise_limit: max_bytes,
        }
    }

    const fn summarized(precise_limit: u64) -> Self {
        Self {
            summarize_symbolic: true,
            summarize_large: true,
            precise_limit,
        }
    }

    fn use_precise_model(&self, n_concrete: Option<u64>) -> bool {
        match n_concrete {
            Some(len) => !self.summarize_large || len <= self.precise_limit,
            None => !self.summarize_symbolic,
        }
    }
}

impl SummaryProfile {
    fn budgets(self) -> SummaryBudgets {
        match self {
            SummaryProfile::Default => SummaryBudgets {
                max_strlen: DEFAULT_MAX_STRLEN,
                max_memcpy: DEFAULT_MAX_MEMCPY,
                max_memset: DEFAULT_MAX_MEMSET,
                max_memcmp: DEFAULT_MAX_MEMCMP,
                max_printf_scan: DEFAULT_MAX_PRINTF_SCAN,
                byte_policy: ByteSummaryPolicy::precise(DEFAULT_MAX_MEMCPY),
            },
            SummaryProfile::PathListing => SummaryBudgets {
                max_strlen: PATH_LIST_MAX_STRLEN,
                max_memcpy: PATH_LIST_MAX_MEMCPY,
                max_memset: PATH_LIST_MAX_MEMSET,
                max_memcmp: PATH_LIST_MAX_MEMCMP,
                max_printf_scan: PATH_LIST_MAX_PRINTF_SCAN,
                byte_policy: ByteSummaryPolicy::summarized(PATH_LIST_PRECISE_BYTE_LIMIT),
            },
        }
    }
}

/// Summary execution outcome.
pub enum SummaryEffect<'ctx> {
    /// Continue execution, optionally setting a return value.
    Return(Option<SymValue<'ctx>>),
    /// Terminate the path.
    Terminate(ExitStatus),
}

/// Call information passed to function summaries.
pub struct CallInfo<'ctx> {
    /// Argument values.
    pub args: Vec<SymValue<'ctx>>,
    /// Argument bit width.
    pub arg_bits: u32,
    /// Return value bit width.
    pub ret_bits: u32,
}

/// Function summary trait.
pub trait FunctionSummary<'ctx>: Send + Sync {
    /// Name of the function (e.g., "memcpy").
    fn name(&self) -> &'static str;
    /// Number of arguments expected.
    fn arity(&self) -> usize;
    /// Execute the summary, updating state and returning an effect.
    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx>;
}

/// Calling convention description for retrieving arguments and return values.
#[derive(Clone, Debug)]
pub struct CallConv {
    arg_registers: Vec<String>,
    ret_register: String,
    arg_bits: u32,
    ret_bits: u32,
}

impl CallConv {
    /// Create a calling convention with explicit registers and widths.
    pub fn new(
        arg_registers: Vec<&'static str>,
        ret_register: &'static str,
        arg_bits: u32,
        ret_bits: u32,
    ) -> Self {
        Self {
            arg_registers: arg_registers.into_iter().map(str::to_string).collect(),
            ret_register: ret_register.to_string(),
            arg_bits,
            ret_bits,
        }
    }

    /// x86-64 System V ABI (RDI, RSI, RDX, RCX, R8, R9; return in RAX).
    pub fn x86_64_sysv() -> Self {
        Self::new(vec!["RDI", "RSI", "RDX", "RCX", "R8", "R9"], "RAX", 64, 64)
    }

    /// x86-64 Windows ABI (RCX, RDX, R8, R9; return in RAX).
    pub fn x86_64_windows() -> Self {
        Self::new(vec!["RCX", "RDX", "R8", "R9"], "RAX", 64, 64)
    }

    /// Architecture-derived calling convention used by the symbolic runtime.
    pub fn for_arch_spec(arch: &ArchSpec) -> Option<Self> {
        if let Some(callconv) = source_owned_callconv_from_arch_projection(arch) {
            return callconv;
        }
        let arch_name = arch.name.to_ascii_lowercase();
        let looks_x86 = arch_name.contains("x86") || arch_name == "x64" || arch_name == "amd64";
        let looks_64 = arch.addr_size == 8 || arch.addr_size == 64 || arch_name.contains("64");
        if looks_x86 && looks_64 {
            return Some(Self::x86_64_sysv());
        }

        if arch_name.contains("riscv") || arch_name.starts_with("rv") {
            const RISCV_ARG_ABI: [&str; 8] = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"];
            const RISCV_ARG_NUMERIC: [&str; 8] =
                ["x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17"];
            let use_abi_names = arch_has_register(arch, "a0");
            let is_64 = arch.addr_size == 8 || arch_name.contains("64");
            let bits = if is_64 { 64 } else { 32 };
            if use_abi_names {
                return Some(Self::new(RISCV_ARG_ABI.to_vec(), "a0", bits, bits));
            }
            return Some(Self::new(RISCV_ARG_NUMERIC.to_vec(), "x10", bits, bits));
        }

        None
    }

    /// Architecture-derived calling convention with binary-environment hints.
    pub fn for_arch_spec_and_symbols(
        arch: &ArchSpec,
        symbol_map: &HashMap<u64, String>,
    ) -> Option<Self> {
        let _ = symbol_map;
        Self::for_arch_spec(arch)
    }

    pub(crate) fn collect_call_info<'ctx>(
        &self,
        state: &SymState<'ctx>,
        arity: usize,
    ) -> CallInfo<'ctx> {
        let mut args = Vec::with_capacity(arity);
        for i in 0..arity {
            if let Some(reg) = self.arg_registers.get(i) {
                args.push(self.read_register(state, reg));
            } else {
                args.push(SymValue::unknown(self.arg_bits));
            }
        }
        CallInfo {
            args,
            arg_bits: self.arg_bits,
            ret_bits: self.ret_bits,
        }
    }

    fn read_register<'ctx>(&self, state: &SymState<'ctx>, base: &str) -> SymValue<'ctx> {
        for alias in register_aliases(base) {
            if let Some(key) = find_register_key(state, alias) {
                return state.get_register_sized(&key, self.arg_bits);
            }
        }
        SymValue::unknown(self.arg_bits)
    }

    pub(crate) fn write_return<'ctx>(&self, state: &mut SymState<'ctx>, value: SymValue<'ctx>) {
        let mut keys = BTreeSet::new();
        for alias in register_aliases(&self.ret_register) {
            if let Some(key) = find_register_key(state, alias) {
                keys.insert(key);
            }
        }
        if keys.is_empty() {
            keys.insert(format!("{}_0", self.ret_register));
        }
        for key in keys {
            let key_bits = state
                .registers()
                .get(&key)
                .map(|existing| existing.bits())
                .unwrap_or(self.ret_bits);
            let adjusted = adjust_bits(state.context(), value.clone(), key_bits);
            state.set_register(&key, adjusted);
        }
    }

    pub(crate) fn arg_register_name(&self, index: usize) -> Option<&str> {
        self.arg_registers.get(index).map(String::as_str)
    }

    pub(crate) fn arg_capacity(&self) -> usize {
        self.arg_registers.len()
    }

    pub(crate) fn arg_bits(&self) -> u32 {
        self.arg_bits
    }

    pub(crate) fn ret_bits(&self) -> u32 {
        self.ret_bits
    }

    pub(crate) fn ret_register_name(&self) -> &str {
        &self.ret_register
    }

    pub(crate) fn return_value<'ctx>(&self, state: &SymState<'ctx>) -> SymValue<'ctx> {
        self.read_register(state, &self.ret_register)
    }
}

const SOURCE_ABI_VARIANT_PREFIX: &str = "r2sym-source-abi-v1:";
const SOURCE_ABI_UNAVAILABLE_VARIANT: &str = "r2sym-source-abi-v1:unavailable";

fn source_owned_callconv_from_arch_projection(arch: &ArchSpec) -> Option<Option<CallConv>> {
    if arch.variant == SOURCE_ABI_UNAVAILABLE_VARIANT {
        return Some(None);
    }
    let payload = arch.variant.strip_prefix(SOURCE_ABI_VARIANT_PREFIX)?;
    let mut fields = payload.split(';');
    let arguments = fields.next()?.strip_prefix("args=")?;
    let arg_bits = fields.next()?.strip_prefix("argbits=")?.parse().ok()?;
    let ret_register = fields.next()?.strip_prefix("ret=")?.trim();
    let ret_bits = fields.next()?.strip_prefix("retbits=")?.parse().ok()?;
    if fields.next().is_some() || arg_bits == 0 || ret_bits == 0 {
        return Some(None);
    }
    if ret_register.is_empty() {
        return Some(None);
    }
    let arg_registers = arguments
        .split(',')
        .filter(|name| !name.is_empty())
        .map(str::to_string)
        .collect::<Vec<_>>();
    Some(Some(CallConv {
        arg_registers,
        ret_register: ret_register.to_string(),
        arg_bits,
        ret_bits,
    }))
}

fn source_register_name(prepared: &SsaArtifact, storage: CanonicalStorageId) -> Option<String> {
    prepared
        .machine_context()
        .register_storages_by_name()
        .iter()
        .filter(|(_, candidate)| **candidate == storage)
        .map(|(name, _)| name)
        .cloned()
        .min()
}

fn source_endianness(endianness: MachineMemoryEndianness) -> Option<Endianness> {
    match endianness {
        MachineMemoryEndianness::Little => Some(Endianness::Little),
        MachineMemoryEndianness::Big => Some(Endianness::Big),
        MachineMemoryEndianness::Mixed => Some(Endianness::Mixed),
        MachineMemoryEndianness::Custom => Some(Endianness::Custom),
        MachineMemoryEndianness::Unknown => None,
    }
}

fn source_architecture_name(family: MachineArchitectureFamily) -> Option<&'static str> {
    match family {
        MachineArchitectureFamily::Unknown => None,
        MachineArchitectureFamily::X86 => Some("x86"),
        MachineArchitectureFamily::X86_64 => Some("x86-64"),
        MachineArchitectureFamily::Arm => Some("arm"),
        MachineArchitectureFamily::AArch64 => Some("aarch64"),
        MachineArchitectureFamily::RiscV32 => Some("riscv32"),
        MachineArchitectureFamily::RiscV64 => Some("riscv64"),
        MachineArchitectureFamily::Mips32 => Some("mips32"),
        MachineArchitectureFamily::Mips64 => Some("mips64"),
        MachineArchitectureFamily::PowerPc32 => Some("ppc32"),
        MachineArchitectureFamily::PowerPc64 => Some("ppc64"),
    }
}

/// Reconstruct the symbolic runtime's presentation profile exclusively from
/// the immutable machine context retained by `prepared`.
pub(crate) fn source_arch_spec(prepared: &SsaArtifact) -> Option<ArchSpec> {
    let context = prepared.machine_context();
    let memory = context.memory_model();
    if !memory.is_available() || !memory.is_coherent() {
        return None;
    }
    let name = source_architecture_name(context.architecture_family())?;
    let address_bits = memory.default_address_bits();
    if address_bits == 0 || !address_bits.is_multiple_of(8) {
        return None;
    }
    let mut arch = ArchSpec::new(name);
    arch.addr_size = address_bits / 8;
    arch.alignment = memory.alignment_bytes().max(1);
    arch.memory_endianness = source_endianness(memory.default_endianness())?;
    arch.instruction_endianness = arch.memory_endianness;
    arch.spaces = memory
        .spaces()
        .iter()
        .map(|space| {
            if space.address_bits() == 0 || !space.address_bits().is_multiple_of(8) {
                return None;
            }
            let mut projected = AddressSpace::new(
                space.space(),
                space.space().to_string(),
                space.address_bits() / 8,
            );
            projected.word_size = space.word_size_bytes();
            projected.is_default = space.space() == r2il::SpaceId::Ram;
            projected.endianness = Some(source_endianness(space.endianness())?);
            Some(projected)
        })
        .collect::<Option<Vec<_>>>()?;
    arch.registers = context
        .register_storages_by_name()
        .iter()
        .filter(|(_, storage)| storage.space == CanonicalStorageSpace::Register)
        .map(|(name, storage)| RegisterDef::new(name.clone(), storage.offset, storage.size))
        .collect();

    let abi = context.abi_model();
    arch.variant = if abi.is_available() && abi.is_coherent() {
        let argument_slots = abi.argument_registers();
        let arguments = argument_slots
            .iter()
            .map(|slot| source_register_name(prepared, slot.storage()))
            .collect::<Option<Vec<_>>>()?;
        let arg_bits = match argument_slots.first() {
            Some(slot) => slot.storage().size.checked_mul(8)?,
            None => address_bits,
        };
        if argument_slots
            .iter()
            .any(|slot| slot.storage().size.checked_mul(8) != Some(arg_bits))
        {
            return None;
        }
        let Some(returned_slot) = abi.return_registers().first() else {
            arch.variant = SOURCE_ABI_UNAVAILABLE_VARIANT.to_string();
            return Some(arch);
        };
        let returned = source_register_name(prepared, returned_slot.storage())?;
        let ret_bits = returned_slot.storage().size.checked_mul(8)?;
        format!(
            "{SOURCE_ABI_VARIANT_PREFIX}args={};argbits={arg_bits};ret={returned};retbits={ret_bits}",
            arguments.join(",")
        )
    } else {
        SOURCE_ABI_UNAVAILABLE_VARIANT.to_string()
    };
    Some(arch)
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SummaryInstallStats {
    pub attempted: usize,
    pub installed: usize,
    pub skipped_unknown: usize,
    pub duplicates: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScopedFunctionProvenance {
    Analyzed,
    RuntimeMaterialized,
}

#[derive(Debug, Clone)]
pub struct ScopedPreparedFunction {
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    pub prepared: Arc<SsaArtifact>,
}

#[derive(Debug, Clone)]
pub struct PreparedFunctionScope {
    root: InterprocFunctionId,
    functions: BTreeMap<InterprocFunctionId, ScopedPreparedFunction>,
    provenance: BTreeMap<InterprocFunctionId, ScopedFunctionProvenance>,
}

impl PreparedFunctionScope {
    pub fn new(root_addr: u64, functions: Vec<ScopedPreparedFunction>) -> Option<Self> {
        let provenance = functions
            .iter()
            .map(|function| (function.id, ScopedFunctionProvenance::Analyzed))
            .collect();
        Self::new_with_provenance(root_addr, functions, provenance)
    }

    pub fn new_with_provenance(
        root_addr: u64,
        functions: Vec<ScopedPreparedFunction>,
        provenance: BTreeMap<InterprocFunctionId, ScopedFunctionProvenance>,
    ) -> Option<Self> {
        let root = InterprocFunctionId(root_addr);
        let mut ids = BTreeSet::new();
        if functions.iter().any(|function| {
            function.id.0 != function.prepared.function().entry || !ids.insert(function.id)
        }) {
            return None;
        }
        if !block_ranges_are_disjoint(functions.iter().flat_map(|function| {
            function
                .prepared
                .function()
                .blocks()
                .map(|block| (block.addr, block.size))
        })) {
            return None;
        }
        let by_id = functions
            .into_iter()
            .map(|function| (function.id, function))
            .collect::<BTreeMap<_, _>>();
        if !by_id.contains_key(&root)
            || provenance.len() != by_id.len()
            || provenance.keys().any(|id| !by_id.contains_key(id))
        {
            return None;
        }
        let root_function = by_id.get(&root)?;
        if by_id.values().any(|function| {
            function.id != root
                && !scope_helper_is_source_coherent(
                    root_function,
                    function,
                    provenance.get(&function.id).copied(),
                )
        }) {
            return None;
        }
        Some(Self {
            root,
            functions: by_id,
            provenance,
        })
    }

    pub fn root_id(&self) -> InterprocFunctionId {
        self.root
    }

    pub fn root(&self) -> Option<&ScopedPreparedFunction> {
        self.functions.get(&self.root)
    }

    /// Return this scope only when its root is the exact SSA authority supplied
    /// by the caller. Equal entry addresses or independently rebuilt content do
    /// not authorize helper execution.
    pub fn exact_for_artifact(&self, artifact: &SsaArtifact) -> Option<&Self> {
        let root = self.root()?;
        (self.root == InterprocFunctionId(artifact.function().entry)
            && root.id == self.root
            && root.prepared.function().entry == artifact.function().entry
            && root.prepared.authority() == artifact.authority())
        .then_some(self)
    }

    pub(crate) fn source_authorized_for_semantics(
        &self,
        artifact: &Arc<SsaArtifact>,
    ) -> Option<Self> {
        self.exact_for_artifact(artifact.as_ref())?;
        let root = self.root()?.clone();
        if self.provenance_of(&root) != Some(ScopedFunctionProvenance::Analyzed) {
            return None;
        }
        let mut functions = vec![root];
        for helper in self.helper_functions() {
            match self.provenance_of(helper)? {
                ScopedFunctionProvenance::RuntimeMaterialized => continue,
                ScopedFunctionProvenance::Analyzed
                    if helper.prepared.provenance_kind()
                        == SsaArtifactProvenanceKind::TrustedSource =>
                {
                    functions.push(helper.clone());
                }
                ScopedFunctionProvenance::Analyzed => return None,
            }
        }
        let provenance = functions
            .iter()
            .map(|function| (function.id, ScopedFunctionProvenance::Analyzed))
            .collect();
        Self::new_with_provenance(self.root.0, functions, provenance)
    }

    pub(crate) fn matches_interproc_owners(&self, summaries: &PreparedInterprocSummarySet) -> bool {
        let Some(root) = self.root() else {
            return false;
        };
        summaries.matches_root(&root.prepared)
            && summaries.owners().len() == self.functions.len()
            && self.functions.iter().all(|(id, function)| {
                summaries
                    .owner(*id)
                    .is_some_and(|owner| Arc::ptr_eq(owner, &function.prepared))
            })
    }

    pub fn functions(&self) -> &BTreeMap<InterprocFunctionId, ScopedPreparedFunction> {
        &self.functions
    }

    pub fn provenance_of(
        &self,
        function: &ScopedPreparedFunction,
    ) -> Option<ScopedFunctionProvenance> {
        self.provenance.get(&function.id).copied()
    }

    pub fn function_containing_block(&self, pc: u64) -> Option<&ScopedPreparedFunction> {
        self.functions
            .values()
            .find(|function| function.prepared.get_block(pc).is_some())
    }

    pub fn contains_block(&self, pc: u64) -> bool {
        self.function_containing_block(pc).is_some()
    }

    pub fn helper_functions(&self) -> impl Iterator<Item = &ScopedPreparedFunction> {
        self.functions
            .values()
            .filter(move |function| function.id != self.root)
    }

    pub fn with_prepared_root(&self, prepared: Arc<SsaArtifact>) -> Option<Self> {
        let mut functions = self.functions.values().cloned().collect::<Vec<_>>();
        let root = functions
            .iter_mut()
            .find(|function| function.id == self.root)?;
        if root.name.is_none() {
            root.name = prepared.function().name.clone();
        }
        root.prepared = prepared;
        Self::new_with_provenance(self.root.0, functions, self.provenance.clone())
    }
}

fn block_ranges_are_disjoint(ranges: impl IntoIterator<Item = (u64, u32)>) -> bool {
    let mut checked = Vec::new();
    for (start, size) in ranges {
        let Some(end) = start.checked_add(u64::from(size)) else {
            return false;
        };
        if end == start {
            return false;
        }
        checked.push((start, end));
    }
    checked.sort_unstable();
    !checked.windows(2).any(|ranges| ranges[1].0 < ranges[0].1)
}

fn scope_helper_is_source_coherent(
    root: &ScopedPreparedFunction,
    helper: &ScopedPreparedFunction,
    provenance: Option<ScopedFunctionProvenance>,
) -> bool {
    let root_context = root.prepared.machine_context();
    let helper_context = helper.prepared.machine_context();
    if provenance.is_none()
        || root_context.architecture_family() != helper_context.architecture_family()
        || root_context.memory_model() != helper_context.memory_model()
        || root_context.register_storages_by_name() != helper_context.register_storages_by_name()
        || !root_context.call_site_interfaces_are_coherent()
        || !helper_context.call_site_interfaces_are_coherent()
    {
        return false;
    }
    if provenance == Some(ScopedFunctionProvenance::RuntimeMaterialized) {
        return true;
    }
    if root.prepared.provenance_kind() != helper.prepared.provenance_kind() {
        return false;
    }
    match (
        root_context.function_interface(),
        helper_context.function_interface(),
    ) {
        (Some(root_interface), Some(helper_interface)) => {
            root_interface.revision_identity() == helper_interface.revision_identity()
        }
        (None, None) => root.prepared.provenance_kind() == SsaArtifactProvenanceKind::Manual,
        _ => false,
    }
}

fn is_runtime_materialized_scope_function(
    scope: &PreparedFunctionScope,
    function: &ScopedPreparedFunction,
) -> bool {
    scope.provenance_of(function) == Some(ScopedFunctionProvenance::RuntimeMaterialized)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivedSummaryCompletion {
    Exact,
    OverApprox,
    BudgetExhausted,
    Unknown,
}

#[derive(Clone)]
pub struct DerivedSummaryInput<'ctx> {
    pub arg_index: usize,
    pub symbol: SymValue<'ctx>,
    pub size: u32,
}

#[derive(Clone)]
pub struct DerivedMemoryWrite<'ctx> {
    pub arg_index: usize,
    pub offset: i64,
    pub size: u32,
    pub value: SymValue<'ctx>,
}

#[derive(Clone)]
pub struct DerivedSummaryCase<'ctx> {
    pub guard: Bool,
    pub return_value: Option<SymValue<'ctx>>,
    pub memory_writes: Vec<DerivedMemoryWrite<'ctx>>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct DerivedSummaryGuidance {
    pub summary_known: bool,
    pub exact: bool,
    pub feasible_cases: usize,
    pub contradictory: bool,
}

#[derive(Debug, Clone, Copy, Default)]
struct PointerInputWindow {
    headroom: u32,
    forward_size: u32,
}

#[derive(Clone)]
pub struct DerivedFunctionSummary<'ctx> {
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    pub arg_count_hint: usize,
    pub arg_symbols: Vec<(usize, SymValue<'ctx>)>,
    pub memory_inputs: Vec<DerivedSummaryInput<'ctx>>,
    pub cases: Vec<DerivedSummaryCase<'ctx>>,
    pub completion: DerivedSummaryCompletion,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivedSummaryDiagnostics {
    pub attempted: usize,
    pub derived: usize,
    pub budget_exhausted: usize,
    pub skipped_core: usize,
    pub skipped_missing: usize,
    pub scc_count: usize,
    pub max_scc_size: usize,
    pub scc_converged: usize,
    pub scc_budget_exhausted: usize,
}

#[derive(Clone)]
pub struct DerivedSummarySet<'ctx> {
    pub interproc: InterprocSummarySet,
    pub summaries: BTreeMap<InterprocFunctionId, Rc<DerivedFunctionSummary<'ctx>>>,
    pub diagnostics: DerivedSummaryDiagnostics,
}

/// Summary registry that can install summaries as call hooks.
pub struct SummaryRegistry<'ctx> {
    summaries: HashMap<String, Arc<dyn FunctionSummary<'ctx> + 'ctx>>,
    callconv: CallConv,
}

impl<'ctx> SummaryRegistry<'ctx> {
    /// Create a new registry with the provided calling convention.
    pub fn new(callconv: CallConv) -> Self {
        Self {
            summaries: HashMap::new(),
            callconv,
        }
    }

    /// Create a registry pre-populated with core summaries.
    pub fn with_core(callconv: CallConv) -> Self {
        Self::with_profile(callconv, SummaryProfile::Default)
    }

    /// Create a registry pre-populated with summaries for a typed workflow profile.
    pub fn with_profile(callconv: CallConv, profile: SummaryProfile) -> Self {
        let budgets = profile.budgets();
        let mut registry = Self::new(callconv);
        registry.register_summary(MemcpySummary::with_policy(
            budgets.max_memcpy,
            budgets.byte_policy,
        ));
        registry.register_summary(KernelCopySummary::copyin(
            budgets.max_memcpy,
            budgets.byte_policy,
        ));
        registry.register_summary(KernelCopySummary::copyout(
            budgets.max_memcpy,
            budgets.byte_policy,
        ));
        registry.register_summary(MemsetSummary::with_policy(
            budgets.max_memset,
            budgets.byte_policy,
        ));
        registry.register_summary(StrlenSummary::new(budgets.max_strlen));
        registry.register_summary(StrcmpSummary::new());
        registry.register_summary(MemcmpSummary::new(budgets.max_memcmp));
        registry.register_summary(MallocSummary::new());
        registry.register_summary(FreeSummary::new());
        registry.register_summary(ArgReturnSummary::retain());
        registry.register_summary(NoopSummary::release());
        registry.register_summary(NoopSummary::lock());
        registry.register_summary(NoopSummary::unlock());
        registry.register_summary(PutsSummary::new(budgets.max_printf_scan));
        registry.register_summary(PrintfSummaryBasic::new(budgets.max_printf_scan));
        registry.register_summary(ReadSummary::new());
        registry.register_summary(IsattySummary::new());
        registry.register_summary(SleepSummary::sleep());
        registry.register_summary(SleepSummary::usleep());
        registry.register_summary(SleepSummary::nanosleep());
        registry.register_summary(ExitSummary::new());
        registry
    }

    /// Create a registry pre-populated with core summaries for a known architecture.
    pub fn with_core_for_arch(arch: &ArchSpec) -> Option<Self> {
        Some(Self::with_profile(
            CallConv::for_arch_spec(arch)?,
            SummaryProfile::Default,
        ))
    }

    /// Create a registry pre-populated with summaries for a typed workflow profile.
    pub fn with_profile_for_arch(arch: &ArchSpec, profile: SummaryProfile) -> Option<Self> {
        Some(Self::with_profile(CallConv::for_arch_spec(arch)?, profile))
    }

    /// Create a registry from the exact ABI carrier snapshot retained by one
    /// prepared artifact. Missing or incoherent source ABI data fails closed.
    pub(crate) fn with_profile_for_prepared(
        prepared: &SsaArtifact,
        profile: SummaryProfile,
    ) -> Option<Self> {
        let arch = source_arch_spec(prepared)?;
        Some(Self::with_profile(CallConv::for_arch_spec(&arch)?, profile))
    }

    /// Create a registry using symbol-map environment hints when the architecture is ambiguous.
    pub fn with_profile_for_arch_and_symbols(
        arch: &ArchSpec,
        symbol_map: &HashMap<u64, String>,
        profile: SummaryProfile,
    ) -> Option<Self> {
        Some(Self::with_profile(
            CallConv::for_arch_spec_and_symbols(arch, symbol_map)?,
            profile,
        ))
    }

    /// Register a function summary.
    pub fn register_summary<S>(&mut self, summary: S)
    where
        S: FunctionSummary<'ctx> + 'ctx,
    {
        self.summaries
            .insert(summary.name().to_string(), Arc::new(summary));
    }

    /// Install a summary as a call hook on a symbolic executor.
    pub fn install_for_executor(
        &self,
        executor: &mut SymExecutor<'ctx>,
        addr: u64,
        name: &str,
    ) -> bool {
        let Some(summary) = self.summaries.get(name).cloned() else {
            return false;
        };
        let callconv = self.callconv.clone();
        executor.register_call_hook(addr, move |state| {
            Ok(apply_summary(state, &*summary, &callconv))
        });
        true
    }

    /// Install a summary as a call hook on a path explorer.
    pub fn install_for_explorer(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        addr: u64,
        name: &str,
    ) -> bool {
        self.install_for_explorer_with_provenance(explorer, addr, name, ())
    }

    fn install_for_explorer_with_provenance<P>(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        addr: u64,
        name: &str,
        provenance: P,
    ) -> bool
    where
        P: 'ctx,
    {
        let Some(summary) = self.summaries.get(name).cloned() else {
            return false;
        };
        let callconv = self.callconv.clone();
        explorer.register_call_hook(addr, move |state| {
            let _retain_exact_provenance = &provenance;
            apply_summary(state, &*summary, &callconv)
        });
        true
    }

    /// Install matching core summaries for direct call sites in a prepared function.
    pub fn install_known_symbols_for_function(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &SsaArtifact,
        symbol_map: &HashMap<u64, String>,
    ) -> SummaryInstallStats {
        self.install_known_symbols_for_function_with_provenance(explorer, prepared, symbol_map, ())
    }

    fn install_known_symbols_for_function_with_provenance<P>(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &SsaArtifact,
        symbol_map: &HashMap<u64, String>,
        provenance: P,
    ) -> SummaryInstallStats
    where
        P: Clone + 'ctx,
    {
        let mut stats = SummaryInstallStats::default();
        let mut targets = BTreeSet::new();
        for call in prepared.call_sites().by_id.values() {
            if let Some(target) = call.direct_target {
                targets.insert(target);
            }
        }
        if targets.is_empty() {
            return stats;
        }

        let mut seen: BTreeSet<(u64, &'static str)> = BTreeSet::new();
        for target in targets {
            stats.attempted += 1;
            let Some(raw_name) = symbol_map.get(&target).map(String::as_str) else {
                stats.skipped_unknown += 1;
                continue;
            };
            let Some(summary_name) = normalize_core_summary_name(raw_name) else {
                stats.skipped_unknown += 1;
                continue;
            };
            if !seen.insert((target, summary_name)) {
                stats.duplicates += 1;
                continue;
            }
            if self.install_for_explorer_with_provenance(
                explorer,
                target,
                summary_name,
                provenance.clone(),
            ) {
                stats.installed += 1;
            } else {
                stats.skipped_unknown += 1;
            }
        }
        stats
    }

    /// Install generic direct-call hooks from typed interproc summaries.
    ///
    /// Manual core summaries keep precedence. Generic hooks are only installed
    /// for direct targets that have an interproc summary but no core-summary
    /// normalization match.
    ///
    /// Install interprocedural hooks only from a summary owner sealed to the
    /// exact prepared SSA allocation being explored.
    pub fn install_interproc_summaries_for_function(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &Arc<SsaArtifact>,
        summary_set: &PreparedInterprocSummarySet,
        symbol_map: &HashMap<u64, String>,
    ) -> Option<SummaryInstallStats> {
        if !summary_set.matches_root(prepared) {
            return None;
        }
        self.install_interproc_summary_report_for_function_with_provenance(
            explorer,
            prepared.as_ref(),
            summary_set.report(),
            symbol_map,
            summary_set.clone(),
        )
    }

    /// Install a detached report only for crate-local, synchronous exploration.
    /// Escaping installers must use an owner-retaining wrapper instead.
    pub(crate) fn install_interproc_summary_report_for_function(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &SsaArtifact,
        summary_set: &InterprocSummarySet,
        symbol_map: &HashMap<u64, String>,
    ) -> Option<SummaryInstallStats> {
        self.install_interproc_summary_report_for_function_with_provenance(
            explorer,
            prepared,
            summary_set,
            symbol_map,
            (),
        )
    }

    fn install_interproc_summary_report_for_function_with_provenance<P>(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &SsaArtifact,
        summary_set: &InterprocSummarySet,
        symbol_map: &HashMap<u64, String>,
        provenance: P,
    ) -> Option<SummaryInstallStats>
    where
        P: Clone + 'ctx,
    {
        summary_set.validate_current_schema().ok()?;
        let mut stats = SummaryInstallStats::default();
        let mut targets = BTreeSet::new();
        for call in prepared.call_sites().by_id.values() {
            if let Some(target) = call.direct_target {
                targets.insert(target);
            }
        }
        if targets.is_empty() {
            return Some(stats);
        }

        let mut seen = BTreeSet::new();
        for target in targets {
            stats.attempted += 1;
            if let Some(raw_name) = symbol_map.get(&target).map(String::as_str)
                && let Some(summary_name) = normalize_core_summary_name(raw_name)
                && self.summaries.contains_key(summary_name)
            {
                stats.skipped_unknown += 1;
                continue;
            }
            let Some(summary) = summary_set
                .summaries
                .get(&InterprocFunctionId(target))
                .cloned()
            else {
                stats.skipped_unknown += 1;
                continue;
            };
            if !seen.insert(target) {
                stats.duplicates += 1;
                continue;
            }
            let callconv = self.callconv.clone();
            let provenance = provenance.clone();
            explorer.register_call_hook(target, move |state| {
                let _retain_exact_provenance = &provenance;
                apply_interproc_summary(state, &summary, &callconv)
            });
            stats.installed += 1;
        }

        Some(stats)
    }

    pub fn has_core_summary_name(&self, name: &str) -> bool {
        normalize_core_summary_name(name)
            .is_some_and(|summary_name| self.summaries.contains_key(summary_name))
    }

    /// Derive report-only symbolic summaries for simulation and query hooks.
    ///
    /// The returned interprocedural report does not retain source authority and
    /// must not authorize a [`crate::SemanticArtifact`], type inference, or
    /// writeback. Source-owned semantic compilation must use
    /// [`Self::derive_source_owned_symbolic_summaries`] instead.
    pub fn derive_symbolic_summaries(
        &self,
        ctx: &'ctx z3::Context,
        scope: &PreparedFunctionScope,
        arch: Option<&ArchSpec>,
        symbol_map: &HashMap<u64, String>,
    ) -> DerivedSummarySet<'ctx> {
        let interproc = build_advisory_interproc_summary_set(scope, arch);
        self.derive_symbolic_summaries_from_interproc(ctx, scope, arch, symbol_map, interproc)
    }

    /// Derive summaries only after sealing the interprocedural solve to the
    /// exact prepared root and helper allocations.
    ///
    /// The returned [`DerivedSummarySet`] still contains only a detached report
    /// projection. Its use for semantic compilation is valid only while the
    /// caller retains the exact source-owned scope as artifact provenance.
    pub(crate) fn derive_source_owned_symbolic_summaries(
        &self,
        ctx: &'ctx z3::Context,
        scope: &PreparedFunctionScope,
        arch: Option<&ArchSpec>,
        symbol_map: &HashMap<u64, String>,
    ) -> Result<DerivedSummarySet<'ctx>, PreparedInterprocSummaryError> {
        let interproc = build_source_owned_interproc_summary_set(scope)?;
        Ok(self.derive_symbolic_summaries_from_interproc(
            ctx,
            scope,
            arch,
            symbol_map,
            interproc.report().clone(),
        ))
    }

    fn derive_symbolic_summaries_from_interproc(
        &self,
        ctx: &'ctx z3::Context,
        scope: &PreparedFunctionScope,
        arch: Option<&ArchSpec>,
        symbol_map: &HashMap<u64, String>,
        interproc: InterprocSummarySet,
    ) -> DerivedSummarySet<'ctx> {
        let mut summaries: BTreeMap<InterprocFunctionId, Rc<DerivedFunctionSummary<'ctx>>> =
            BTreeMap::new();
        let mut diagnostics = DerivedSummaryDiagnostics::default();

        let helper_scope = scope
            .helper_functions()
            .filter(|helper| !is_runtime_materialized_scope_function(scope, helper))
            .map(|helper| (helper.id, helper))
            .collect::<BTreeMap<_, _>>();
        let sccs = compute_derived_summary_sccs(&helper_scope);
        diagnostics.scc_count = sccs.len();

        for scc in sccs {
            diagnostics.max_scc_size = diagnostics.max_scc_size.max(scc.len());
            let mut converged = false;
            for _ in 0..DEFAULT_DERIVED_SUMMARY_MAX_ITERATIONS {
                let mut changed = false;
                for function_id in &scc {
                    let Some(helper) = helper_scope.get(function_id).copied() else {
                        continue;
                    };
                    diagnostics.attempted += 1;
                    if symbol_map
                        .get(&helper.id.0)
                        .is_some_and(|name| self.has_core_summary_name(name))
                    {
                        diagnostics.skipped_core += 1;
                        continue;
                    }

                    let Some(static_summary) = interproc.summaries.get(function_id).cloned() else {
                        diagnostics.skipped_missing += 1;
                        continue;
                    };

                    let derived = derive_symbolic_summary_for_function(DerivedSummaryBuildInputs {
                        ctx,
                        registry: self,
                        arch,
                        function: helper,
                        static_summary: &static_summary,
                        interproc: &interproc,
                        derived_summaries: &summaries,
                        symbol_map,
                    });
                    let next = Rc::new(derived);
                    let previous = summaries.get(function_id);
                    if previous.map(|current| derived_summary_fingerprint(current))
                        != Some(derived_summary_fingerprint(&next))
                    {
                        summaries.insert(*function_id, next);
                        changed = true;
                    }
                }
                if !changed {
                    converged = true;
                    diagnostics.scc_converged += 1;
                    break;
                }
            }

            if !converged {
                diagnostics.scc_budget_exhausted += 1;
                for function_id in &scc {
                    if let Some(summary) = summaries.get_mut(function_id) {
                        let next = with_budget_exhausted_completion(summary.as_ref());
                        *summary = Rc::new(next);
                    }
                }
            }
        }

        for summary in summaries.values() {
            match summary.completion {
                DerivedSummaryCompletion::BudgetExhausted => diagnostics.budget_exhausted += 1,
                DerivedSummaryCompletion::Unknown => diagnostics.skipped_missing += 1,
                _ => diagnostics.derived += 1,
            }
        }

        DerivedSummarySet {
            interproc,
            summaries,
            diagnostics,
        }
    }

    pub fn install_scope_summaries_for_explorer(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        ctx: &'ctx z3::Context,
        prepared: &SsaArtifact,
        scope: &PreparedFunctionScope,
        arch: Option<&ArchSpec>,
        symbol_map: &HashMap<u64, String>,
    ) -> DerivedSummaryDiagnostics {
        let Some(scope) = scope.exact_for_artifact(prepared) else {
            return DerivedSummaryDiagnostics::default();
        };
        let derived = self.derive_symbolic_summaries(ctx, scope, arch, symbol_map);
        if let Some(root) = scope.root() {
            let retained_scope = PreparedFunctionScope::clone(scope);
            let _ = self.install_interproc_summary_report_for_function_with_provenance(
                explorer,
                &root.prepared,
                &derived.interproc,
                symbol_map,
                retained_scope.clone(),
            );
            let _ = self.install_derived_summaries_for_function_with_provenance(
                explorer,
                &root.prepared,
                &derived.summaries,
                symbol_map,
                retained_scope.clone(),
            );
            let _ = self.install_known_symbols_for_function_with_provenance(
                explorer,
                &root.prepared,
                symbol_map,
                retained_scope,
            );
        }
        derived.diagnostics
    }

    pub(crate) fn install_derived_summaries_for_function(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &SsaArtifact,
        summaries: &BTreeMap<InterprocFunctionId, Rc<DerivedFunctionSummary<'ctx>>>,
        symbol_map: &HashMap<u64, String>,
    ) -> SummaryInstallStats {
        self.install_derived_summaries_for_function_with_provenance(
            explorer,
            prepared,
            summaries,
            symbol_map,
            (),
        )
    }

    fn install_derived_summaries_for_function_with_provenance<P>(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &SsaArtifact,
        summaries: &BTreeMap<InterprocFunctionId, Rc<DerivedFunctionSummary<'ctx>>>,
        symbol_map: &HashMap<u64, String>,
        provenance: P,
    ) -> SummaryInstallStats
    where
        P: Clone + 'ctx,
    {
        let mut stats = SummaryInstallStats::default();
        let mut targets = BTreeSet::new();
        for call in prepared.call_sites().by_id.values() {
            if let Some(target) = call.direct_target {
                targets.insert(target);
            }
        }
        for target in targets {
            stats.attempted += 1;
            if let Some(raw_name) = symbol_map.get(&target)
                && self.has_core_summary_name(raw_name)
            {
                stats.skipped_unknown += 1;
                continue;
            }
            let Some(summary) = summaries.get(&InterprocFunctionId(target)).cloned() else {
                stats.skipped_unknown += 1;
                continue;
            };
            if summary.cases.is_empty()
                || matches!(
                    summary.completion,
                    DerivedSummaryCompletion::Unknown | DerivedSummaryCompletion::BudgetExhausted
                )
            {
                stats.skipped_unknown += 1;
                continue;
            }
            let callconv = self.callconv.clone();
            let provenance = provenance.clone();
            explorer.register_derived_call_hook(
                target,
                summary.clone(),
                callconv.clone(),
                move |state| {
                    let _retain_exact_provenance = &provenance;
                    apply_derived_summary(state, &summary, &callconv)
                },
            );
            stats.installed += 1;
        }
        stats
    }
}

fn compute_derived_summary_sccs(
    helpers: &BTreeMap<InterprocFunctionId, &ScopedPreparedFunction>,
) -> Vec<Vec<InterprocFunctionId>> {
    let node_ids: Vec<InterprocFunctionId> = helpers.keys().copied().collect();
    let node_set = node_ids.iter().copied().collect::<BTreeSet<_>>();
    let mut succs = BTreeMap::<InterprocFunctionId, Vec<InterprocFunctionId>>::new();
    let mut rev = BTreeMap::<InterprocFunctionId, Vec<InterprocFunctionId>>::new();

    for node in &node_ids {
        succs.entry(*node).or_default();
        rev.entry(*node).or_default();
    }

    for (id, helper) in helpers {
        let mut out = helper
            .prepared
            .call_sites()
            .by_id
            .values()
            .filter_map(|call| call.direct_target.map(InterprocFunctionId))
            .filter(|target| node_set.contains(target))
            .collect::<Vec<_>>();
        out.sort_unstable();
        out.dedup();
        succs.insert(*id, out.clone());
        for succ in out {
            rev.entry(succ).or_default().push(*id);
        }
    }

    for preds in rev.values_mut() {
        preds.sort_unstable();
        preds.dedup();
    }

    let mut visited = BTreeSet::new();
    let mut order = Vec::new();
    for node in &node_ids {
        dfs_summary_postorder(*node, &succs, &mut visited, &mut order);
    }

    visited.clear();
    let mut sccs = Vec::new();
    while let Some(node) = order.pop() {
        if visited.contains(&node) {
            continue;
        }
        let mut component = Vec::new();
        dfs_summary_component(node, &rev, &mut visited, &mut component);
        component.sort_unstable();
        sccs.push(component);
    }

    sccs.reverse();
    sccs
}

fn dfs_summary_postorder(
    node: InterprocFunctionId,
    succs: &BTreeMap<InterprocFunctionId, Vec<InterprocFunctionId>>,
    visited: &mut BTreeSet<InterprocFunctionId>,
    order: &mut Vec<InterprocFunctionId>,
) {
    if !visited.insert(node) {
        return;
    }
    if let Some(nexts) = succs.get(&node) {
        for next in nexts {
            dfs_summary_postorder(*next, succs, visited, order);
        }
    }
    order.push(node);
}

fn dfs_summary_component(
    node: InterprocFunctionId,
    rev: &BTreeMap<InterprocFunctionId, Vec<InterprocFunctionId>>,
    visited: &mut BTreeSet<InterprocFunctionId>,
    component: &mut Vec<InterprocFunctionId>,
) {
    if !visited.insert(node) {
        return;
    }
    component.push(node);
    if let Some(preds) = rev.get(&node) {
        for pred in preds {
            dfs_summary_component(*pred, rev, visited, component);
        }
    }
}

fn derived_summary_fingerprint(summary: &DerivedFunctionSummary<'_>) -> Vec<String> {
    let mut out = vec![
        format!("{:?}", summary.completion),
        summary.arg_count_hint.to_string(),
        summary.arg_symbols.len().to_string(),
        summary.memory_inputs.len().to_string(),
        summary.cases.len().to_string(),
    ];
    out.extend(
        summary
            .arg_symbols
            .iter()
            .map(|(index, symbol)| format!("arg:{index}:{}", symbol)),
    );
    out.extend(
        summary
            .memory_inputs
            .iter()
            .map(|input| format!("mem:{}:{}:{}", input.arg_index, input.size, input.symbol)),
    );
    out.extend(summary.cases.iter().map(|case| {
        let writes = case
            .memory_writes
            .iter()
            .map(|write| {
                format!(
                    "{}:{}:{}:{}",
                    write.arg_index, write.offset, write.size, write.value
                )
            })
            .collect::<Vec<_>>()
            .join("|");
        format!(
            "case:{}:{}:{}",
            case.guard.simplify(),
            case.return_value
                .as_ref()
                .map(|value| value.to_string())
                .unwrap_or_else(|| "<void>".to_string()),
            writes
        )
    }));
    out
}

fn with_budget_exhausted_completion<'ctx>(
    summary: &DerivedFunctionSummary<'ctx>,
) -> DerivedFunctionSummary<'ctx> {
    let mut next = summary.clone();
    next.completion = DerivedSummaryCompletion::BudgetExhausted;
    next
}

fn build_advisory_interproc_summary_set(
    scope: &PreparedFunctionScope,
    arch: Option<&ArchSpec>,
) -> InterprocSummarySet {
    let Some(root) = scope.root() else {
        return InterprocSummarySet::default();
    };
    let inputs = scope
        .functions()
        .values()
        .filter(|function| !is_runtime_materialized_scope_function(scope, function))
        .map(|function| InterprocFunctionInput {
            id: function.id,
            name: function.name.clone(),
            prepared: function.prepared.as_ref(),
        })
        .collect::<Vec<_>>();

    solve_interproc_summary_set(
        &inputs,
        arch,
        Some(root.id),
        &BTreeMap::new(),
        InterprocSolveConfig::default(),
    )
    .unwrap_or_default()
}

fn build_source_owned_interproc_summary_set(
    scope: &PreparedFunctionScope,
) -> Result<PreparedInterprocSummarySet, PreparedInterprocSummaryError> {
    let root = scope
        .root()
        .ok_or(PreparedInterprocSummaryError::MissingRoot)?;
    let inputs = scope
        .functions()
        .values()
        .filter(|function| !is_runtime_materialized_scope_function(scope, function))
        .map(|function| PreparedInterprocFunctionInput {
            id: function.id,
            name: function.name.clone(),
            prepared: &function.prepared,
        })
        .collect::<Vec<_>>();

    solve_prepared_interproc_summary_set(
        Arc::clone(&root.prepared),
        &inputs,
        InterprocSolveConfig::default(),
    )
}

struct DerivedSummaryBuildInputs<'a, 'ctx> {
    ctx: &'ctx z3::Context,
    registry: &'a SummaryRegistry<'ctx>,
    arch: Option<&'a ArchSpec>,
    function: &'a ScopedPreparedFunction,
    static_summary: &'a FunctionSemanticSummary,
    interproc: &'a InterprocSummarySet,
    derived_summaries: &'a BTreeMap<InterprocFunctionId, Rc<DerivedFunctionSummary<'ctx>>>,
    symbol_map: &'a HashMap<u64, String>,
}

fn derive_symbolic_summary_for_function<'ctx>(
    inputs: DerivedSummaryBuildInputs<'_, 'ctx>,
) -> DerivedFunctionSummary<'ctx> {
    let DerivedSummaryBuildInputs {
        ctx,
        registry,
        arch,
        function,
        static_summary,
        interproc,
        derived_summaries,
        symbol_map,
    } = inputs;
    let mut state = SymState::new(ctx, function.prepared.entry);
    crate::runtime::seed_default_state_for_arch(&mut state, &function.prepared, arch);
    let defines_return_value = function_defines_return_value(function, &registry.callconv);
    let opaque_return = matches!(
        static_summary.return_relation,
        SummaryReturnRelation::Unknown
    ) && !defines_return_value;

    let mut arg_symbols = Vec::new();
    let helper_name = function
        .name
        .clone()
        .unwrap_or_else(|| format!("sub_{:x}", function.id.0));
    let mut memory_inputs = Vec::new();
    let pointer_inputs = collect_pointer_memory_windows(static_summary);

    for index in 0..registry.callconv.arg_capacity() {
        if let Some(reg) = registry.callconv.arg_register_name(index) {
            let key = find_register_key(&state, reg)
                .unwrap_or_else(|| format!("{}_0", reg.to_ascii_uppercase()));
            let arg_bits = static_summary_arg_bits(&registry.callconv);
            if let Some(window) = pointer_inputs.get(&index).copied() {
                let ptr_base = helper_arg_region_base(function.id, index);
                let region_start = ptr_base.saturating_sub(window.headroom as u64);
                let region_size = window.headroom.saturating_add(window.forward_size.max(1));
                let _ = state.make_symbolic_memory(
                    region_start,
                    region_size.max(1),
                    &format!("{}_arg{}_mem", helper_name, index),
                );
                let symbol = state.mem_read(
                    &SymValue::concrete(ptr_base, arg_bits),
                    window.forward_size.max(1),
                );
                state.set_register(&key, SymValue::concrete(ptr_base, arg_bits));
                memory_inputs.push(DerivedSummaryInput {
                    arg_index: index,
                    symbol,
                    size: window.forward_size.max(1),
                });
            } else {
                if !state.registers().contains_key(&key) {
                    state.make_symbolic_named(
                        &key,
                        &format!("{}_arg{}", helper_name, index),
                        arg_bits,
                    );
                }
                arg_symbols.push((index, state.get_register_sized(&key, arg_bits)));
            }
        }
    }

    let config = crate::path::ExploreConfig {
        max_states: DEFAULT_DERIVED_SUMMARY_MAX_STATES,
        max_completed_paths: Some(DEFAULT_DERIVED_SUMMARY_MAX_PATHS),
        max_depth: DEFAULT_DERIVED_SUMMARY_MAX_DEPTH,
        timeout: None,
        prune_infeasible: true,
        merge_states: true,
        subsumption_states: true,
        ..crate::path::ExploreConfig::default()
    };
    let mut explorer = PathExplorer::with_config(ctx, config);
    let _ = registry.install_interproc_summary_report_for_function(
        &mut explorer,
        &function.prepared,
        interproc,
        symbol_map,
    );
    let _ = registry.install_derived_summaries_for_function(
        &mut explorer,
        &function.prepared,
        derived_summaries,
        symbol_map,
    );
    let _ =
        registry.install_known_symbols_for_function(&mut explorer, &function.prepared, symbol_map);
    let summary = explorer.summarize_function(&function.prepared, state);

    let completion = if opaque_return {
        DerivedSummaryCompletion::Unknown
    } else if summary.stats.timed_out || summary.stats.max_states_exhausted {
        DerivedSummaryCompletion::BudgetExhausted
    } else if summary.paths.is_empty() {
        DerivedSummaryCompletion::Unknown
    } else if summary.paths.iter().all(|path| path.feasible) {
        DerivedSummaryCompletion::Exact
    } else {
        DerivedSummaryCompletion::OverApprox
    };

    let mut cases = Vec::new();
    let mut write_locations = collect_tracked_memory_writes(static_summary);
    write_locations.sort_unstable();
    write_locations.dedup();
    for path in summary.paths.iter().filter(|path| path.feasible) {
        let mut memory_writes = Vec::new();
        for (arg_index, offset, size) in &write_locations {
            let base_addr = helper_arg_region_base(function.id, *arg_index);
            let addr = SymValue::concrete(
                concrete_with_signed_offset(base_addr, *offset),
                static_summary_arg_bits(&registry.callconv),
            );
            let value = path.state.mem_read(&addr, *size);
            memory_writes.push(DerivedMemoryWrite {
                arg_index: *arg_index,
                offset: *offset,
                size: *size,
                value,
            });
        }
        memory_writes = coalesce_adjacent_memory_writes(ctx, memory_writes);

        let return_value = match static_summary.return_relation {
            SummaryReturnRelation::Void => None,
            SummaryReturnRelation::Unknown if opaque_return => None,
            _ => Some(registry.callconv.return_value(&path.state)),
        };
        cases.push(DerivedSummaryCase {
            guard: path.state.path_condition(),
            return_value,
            memory_writes,
        });
    }

    DerivedFunctionSummary {
        id: function.id,
        name: function.name.clone(),
        arg_count_hint: summary_arity(static_summary),
        arg_symbols,
        memory_inputs,
        cases,
        completion,
    }
}

fn function_defines_return_value(function: &ScopedPreparedFunction, callconv: &CallConv) -> bool {
    let aliases = register_aliases(callconv.ret_register_name());
    function.prepared.blocks().any(|block| {
        block.ops.iter().any(|op| {
            op.dst().is_some_and(|dst| {
                aliases
                    .iter()
                    .any(|alias| dst.name.eq_ignore_ascii_case(alias))
            })
        })
    })
}

fn coalesce_adjacent_memory_writes<'ctx>(
    ctx: &'ctx z3::Context,
    mut writes: Vec<DerivedMemoryWrite<'ctx>>,
) -> Vec<DerivedMemoryWrite<'ctx>> {
    writes.sort_by_key(|write| (write.arg_index, write.offset, write.size));

    let mut merged: Vec<DerivedMemoryWrite<'ctx>> = Vec::with_capacity(writes.len());
    for write in writes {
        if let Some(last) = merged.last_mut()
            && last.arg_index == write.arg_index
            && last.offset.checked_add(last.size as i64) == Some(write.offset)
            && let Some(new_size) = last.size.checked_add(write.size)
        {
            last.value = write.value.concat(ctx, &last.value);
            last.size = new_size;
            continue;
        }
        merged.push(write);
    }
    merged
}

fn helper_arg_region_base(function: InterprocFunctionId, arg_index: usize) -> u64 {
    0x5000_0000u64
        .wrapping_add((function.0 & 0xffff) << 12)
        .wrapping_add((arg_index as u64) << 8)
        .wrapping_add(0x80)
}

fn static_summary_arg_bits(callconv: &CallConv) -> u32 {
    callconv.arg_bits
}

fn collect_pointer_memory_windows(
    summary: &FunctionSemanticSummary,
) -> BTreeMap<usize, PointerInputWindow> {
    let mut inputs = BTreeMap::new();
    for (index, effect) in &summary.arg_effects {
        if !(effect.read || effect.write || effect.escape || effect.free) {
            continue;
        }
        let mut window = PointerInputWindow {
            headroom: 0,
            forward_size: DEFAULT_MAX_INTERPROC_HAVOC as u32,
        };
        let mut saw_precise_range = false;
        for effect in &summary.memory_effects {
            let SummaryMemoryRegion::Arg {
                index: effect_index,
            } = effect.location.region
            else {
                continue;
            };
            if effect_index != *index {
                continue;
            }
            let Some(range) = effect.location.range else {
                continue;
            };
            let width = range.width.unwrap_or(1).max(1);
            let start = range.offset_lo.min(range.offset_hi);
            let end = range.offset_hi.max(range.offset_lo);
            let forward = if end >= 0 {
                (end as u32).saturating_add(width)
            } else {
                width
            };
            let headroom = if start < 0 {
                start.checked_abs().unwrap_or(i64::MAX).min(u32::MAX as i64) as u32
            } else {
                0
            };
            window.forward_size = window.forward_size.max(forward.max(1));
            window.headroom = window.headroom.max(headroom);
            saw_precise_range = true;
        }
        if !saw_precise_range {
            window.forward_size = DEFAULT_MAX_INTERPROC_HAVOC as u32;
        }
        inputs.insert(*index, window);
    }
    for transfer in &summary.transfer_effects {
        for location in [transfer.dst, transfer.src] {
            let SummaryMemoryRegion::Arg { index } = location.region else {
                continue;
            };
            let window = inputs.entry(index).or_insert(PointerInputWindow {
                headroom: 0,
                forward_size: DEFAULT_MAX_INTERPROC_HAVOC as u32,
            });
            if let Some(range) = location.range {
                let start = range.offset_lo.min(range.offset_hi);
                let end = range.offset_hi.max(range.offset_lo);
                if start < 0 {
                    window.headroom = window
                        .headroom
                        .max(start.checked_abs().unwrap_or(i64::MAX).min(u32::MAX as i64) as u32);
                }
                if end >= 0 {
                    window.forward_size = window.forward_size.max((end as u32).saturating_add(1));
                }
            }
        }
    }
    inputs
}

fn collect_tracked_memory_writes(summary: &FunctionSemanticSummary) -> Vec<(usize, i64, u32)> {
    let mut writes = Vec::new();
    for effect in &summary.memory_effects {
        if !matches!(
            effect.kind,
            SummaryMemoryEffectKind::Write
                | SummaryMemoryEffectKind::Escape
                | SummaryMemoryEffectKind::Free
        ) {
            continue;
        }
        let SummaryMemoryRegion::Arg { index } = effect.location.region else {
            continue;
        };
        let range = effect.location.range.unwrap_or(r2ssa::SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(1),
        });
        let width = range.width.unwrap_or(1).max(1);
        let start = range.offset_lo.min(range.offset_hi);
        let end = range.offset_hi.max(range.offset_lo);
        let mut offset = start;
        while offset <= end {
            writes.push((index, offset, width));
            let Some(next) = offset.checked_add(width as i64) else {
                break;
            };
            offset = next;
        }
    }
    for transfer in &summary.transfer_effects {
        let SummaryMemoryRegion::Arg { index } = transfer.dst.region else {
            continue;
        };
        let width = match transfer.len {
            r2ssa::SummaryTransferLength::Const(value) => value
                .clamp(1, DEFAULT_MAX_INTERPROC_HAVOC)
                .min(u32::MAX as u64)
                as u32,
            _ => DEFAULT_MAX_INTERPROC_HAVOC as u32,
        };
        let offset = transfer
            .dst
            .range
            .map(|range| range.offset_lo.min(range.offset_hi))
            .unwrap_or(0);
        writes.push((index, offset, width));
    }
    writes.sort_unstable();
    writes.dedup();
    writes
}

fn apply_derived_summary<'ctx>(
    state: &mut SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    callconv: &CallConv,
) -> CallHookResult {
    let call =
        callconv.collect_call_info(state, summary.arg_count_hint.max(callconv.arg_capacity()));
    if summary.cases.is_empty() {
        return CallHookResult::Fallthrough;
    }
    if apply_derived_runtime_materialization_copy(state, summary, &call, callconv) {
        return CallHookResult::Fallthrough;
    }

    let substitutions = build_summary_substitutions(state, summary, &call);

    if summary.cases.iter().any(|case| case.return_value.is_some()) {
        let mut merged = SymValue::unknown(call.ret_bits);
        for case in summary.cases.iter().rev() {
            let Some(return_value) = &case.return_value else {
                continue;
            };
            let guard = substitute_bool(&case.guard, &substitutions);
            let value = substitute_value(state.context(), return_value, &substitutions);
            merged = ite_value(state.context(), &guard, &value, &merged);
        }
        callconv.write_return(state, merged);
    }

    let mut writes = BTreeMap::<(usize, i64, u32), Vec<(Bool, SymValue<'ctx>)>>::new();
    for case in &summary.cases {
        let guard = substitute_bool(&case.guard, &substitutions);
        for write in &case.memory_writes {
            let value = substitute_value(state.context(), &write.value, &substitutions);
            writes
                .entry((write.arg_index, write.offset, write.size))
                .or_default()
                .push((guard.clone(), value));
        }
    }

    for ((arg_index, offset, size), cases) in writes {
        let Some(base) = call.args.get(arg_index) else {
            continue;
        };
        let addr = add_signed_offset(state.context(), base, offset, call.arg_bits);
        let mut merged = state.mem_read(&addr, size);
        for (guard, value) in cases.into_iter().rev() {
            merged = ite_value(state.context(), &guard, &value, &merged);
        }
        state.mem_write(&addr, &merged, size);
    }

    CallHookResult::Fallthrough
}

const DERIVED_RUNTIME_COPY_MIN_SIZE: u32 = 0x100;

fn apply_derived_runtime_materialization_copy<'ctx>(
    state: &mut SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    call: &CallInfo<'ctx>,
    callconv: &CallConv,
) -> bool {
    let [case] = summary.cases.as_slice() else {
        return false;
    };
    if case.guard.simplify().as_bool() != Some(true) {
        return false;
    }
    let Some(write) = case
        .memory_writes
        .iter()
        .find(|write| write.arg_index == 0 && write.offset == 0)
    else {
        return false;
    };
    if write.size < DERIVED_RUNTIME_COPY_MIN_SIZE {
        return false;
    }
    if !summary
        .memory_inputs
        .iter()
        .any(|input| input.arg_index == 1 && input.size >= write.size)
    {
        return false;
    }
    let Some(dst) = call.args.first().and_then(SymValue::as_concrete) else {
        return false;
    };
    let Some(src) = call.args.get(1).and_then(SymValue::as_concrete) else {
        return false;
    };
    let len = call
        .args
        .get(2)
        .and_then(SymValue::as_concrete)
        .unwrap_or(write.size as u64);
    if len == 0 || len > write.size as u64 || len > u32::MAX as u64 {
        return false;
    }
    if state.runtime_region_for_pc(dst).is_none() {
        return false;
    }

    let provenance = RuntimeValueProvenance {
        source_addr: src,
        size: len as u32,
    };
    state.note_runtime_store_copy(dst, len as u32, Some(&provenance));
    if case.return_value.is_some() {
        callconv.write_return(state, SymValue::concrete(dst, call.ret_bits));
    }
    true
}

pub(crate) fn evaluate_derived_summary_guidance<'ctx>(
    state: &SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    callconv: &CallConv,
    solver: &SymSolver<'ctx>,
) -> DerivedSummaryGuidance {
    let exact = matches!(summary.completion, DerivedSummaryCompletion::Exact);
    if summary.cases.is_empty() {
        return DerivedSummaryGuidance {
            summary_known: true,
            exact,
            feasible_cases: 0,
            contradictory: false,
        };
    }

    let call =
        callconv.collect_call_info(state, summary.arg_count_hint.max(callconv.arg_capacity()));
    let substitutions = build_summary_substitutions(state, summary, &call);
    let mut feasible_cases = 0;
    let mut saw_unknown = false;

    for case in &summary.cases {
        let Some(guard) = try_substitute_bool(&case.guard, &substitutions) else {
            saw_unknown = true;
            continue;
        };
        match solver.sat_with_constraint(state, &guard) {
            SatResult::Sat => feasible_cases += 1,
            SatResult::Unknown => saw_unknown = true,
            SatResult::Unsat => {}
        }
    }

    DerivedSummaryGuidance {
        summary_known: true,
        exact,
        feasible_cases,
        contradictory: exact && feasible_cases == 0 && !saw_unknown,
    }
}

fn concrete_with_signed_offset(base: u64, offset: i64) -> u64 {
    if offset >= 0 {
        base.wrapping_add(offset as u64)
    } else {
        base.wrapping_sub(offset.unsigned_abs())
    }
}

fn add_signed_offset<'ctx>(
    ctx: &'ctx z3::Context,
    base: &SymValue<'ctx>,
    offset: i64,
    bits: u32,
) -> SymValue<'ctx> {
    if offset >= 0 {
        base.add(ctx, &SymValue::concrete(offset as u64, bits))
    } else {
        base.sub(ctx, &SymValue::concrete(offset.unsigned_abs(), bits))
    }
}

fn build_summary_substitutions<'ctx>(
    state: &SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    call: &CallInfo<'ctx>,
) -> Vec<(BV, BV)> {
    let mut substitutions = Vec::new();
    for (index, symbol) in &summary.arg_symbols {
        let Some(actual) = call.args.get(*index) else {
            continue;
        };
        let adjusted = adjust_bits(state.context(), actual.clone(), symbol.bits());
        substitutions.push((
            symbol.to_bv(state.context()),
            adjusted.to_bv(state.context()),
        ));
    }
    for input in &summary.memory_inputs {
        let Some(base) = call.args.get(input.arg_index) else {
            continue;
        };
        let actual = adjust_bits(
            state.context(),
            state.mem_read(base, input.size),
            input.symbol.bits(),
        );
        substitutions.push((
            input.symbol.to_bv(state.context()),
            actual.to_bv(state.context()),
        ));
    }
    substitutions
}

fn substitute_bool(ast: &Bool, substitutions: &[(BV, BV)]) -> Bool {
    if substitutions.is_empty() {
        return ast.clone();
    }
    let pairs = substitutions
        .iter()
        .map(|(from, to)| (from, to))
        .collect::<Vec<_>>();
    catch_unwind(AssertUnwindSafe(|| ast.substitute(&pairs)))
        .unwrap_or_else(|_| Bool::from_bool(true))
}

fn try_substitute_bool(ast: &Bool, substitutions: &[(BV, BV)]) -> Option<Bool> {
    catch_unwind(AssertUnwindSafe(|| substitute_bool(ast, substitutions))).ok()
}

fn substitute_value<'ctx>(
    _ctx: &'ctx z3::Context,
    value: &SymValue<'ctx>,
    substitutions: &[(BV, BV)],
) -> SymValue<'ctx> {
    if substitutions.is_empty() {
        return value.clone();
    }
    match value {
        SymValue::Concrete { .. } | SymValue::Unknown { .. } => value.clone(),
        SymValue::Symbolic {
            ast, bits, taint, ..
        } => {
            let pairs = substitutions
                .iter()
                .map(|(from, to)| (from, to))
                .collect::<Vec<_>>();
            catch_unwind(AssertUnwindSafe(|| ast.substitute(&pairs)))
                .map(|substituted| SymValue::symbolic_tainted(substituted, *bits, *taint))
                .unwrap_or_else(|_| SymValue::unknown(*bits))
        }
    }
}

fn ite_value<'ctx>(
    ctx: &'ctx z3::Context,
    guard: &Bool,
    when_true: &SymValue<'ctx>,
    when_false: &SymValue<'ctx>,
) -> SymValue<'ctx> {
    let bits = when_true.bits().max(when_false.bits());
    let taint = when_true.get_taint() | when_false.get_taint();
    let true_bv = adjust_bits(ctx, when_true.clone(), bits).to_bv(ctx);
    let false_bv = adjust_bits(ctx, when_false.clone(), bits).to_bv(ctx);
    SymValue::symbolic_tainted(guard.ite(&true_bv, &false_bv), bits, taint)
}

fn apply_summary<'ctx>(
    state: &mut SymState<'ctx>,
    summary: &dyn FunctionSummary<'ctx>,
    callconv: &CallConv,
) -> CallHookResult {
    let call = callconv.collect_call_info(state, summary.arity());
    match summary.execute(state, &call) {
        SummaryEffect::Return(ret) => {
            if let Some(value) = ret {
                callconv.write_return(state, value);
            }
            CallHookResult::Fallthrough
        }
        SummaryEffect::Terminate(status) => {
            state.terminate(status.clone());
            CallHookResult::Terminate(status)
        }
    }
}

fn apply_interproc_summary<'ctx>(
    state: &mut SymState<'ctx>,
    summary: &FunctionSemanticSummary,
    callconv: &CallConv,
) -> CallHookResult {
    let call = callconv.collect_call_info(state, summary_arity(summary));
    for effect in &summary.transfer_effects {
        apply_interproc_transfer_effect(state, &call, effect);
    }
    for effect in &summary.memory_effects {
        apply_interproc_memory_effect(state, &call, effect);
    }
    if let Some(value) = interproc_return_value(state, &call, summary) {
        callconv.write_return(state, value);
    }
    CallHookResult::Fallthrough
}

fn summary_arity(summary: &FunctionSemanticSummary) -> usize {
    let mut arity = summary.arg_count_hint.unwrap_or(0);
    if let SummaryReturnRelation::Arg(idx) = summary.return_relation {
        arity = arity.max(idx.saturating_add(1));
    }
    if let Some(max_idx) = summary.arg_effects.keys().copied().max() {
        arity = arity.max(max_idx.saturating_add(1));
    }
    for effect in &summary.memory_effects {
        if let SummaryMemoryRegion::Arg { index } = effect.location.region {
            arity = arity.max(index.saturating_add(1));
        }
    }
    for effect in &summary.transfer_effects {
        if let SummaryMemoryRegion::Arg { index } = effect.dst.region {
            arity = arity.max(index.saturating_add(1));
        }
        if let SummaryMemoryRegion::Arg { index } = effect.src.region {
            arity = arity.max(index.saturating_add(1));
        }
        if let r2ssa::SummaryTransferLength::Arg(index) = effect.len {
            arity = arity.max(index.saturating_add(1));
        }
    }
    for effect in &summary.lifetime_effects {
        arity = arity.max(effect.arg.saturating_add(1));
    }
    for effect in &summary.sync_effects {
        arity = arity.max(effect.arg.saturating_add(1));
    }
    arity
}

fn interproc_return_value<'ctx>(
    state: &mut SymState<'ctx>,
    call: &CallInfo<'ctx>,
    summary: &FunctionSemanticSummary,
) -> Option<SymValue<'ctx>> {
    match summary.return_relation {
        SummaryReturnRelation::Void => None,
        SummaryReturnRelation::Arg(idx) => call.args.get(idx).cloned(),
        SummaryReturnRelation::Const(value) => Some(SymValue::concrete(value, call.ret_bits)),
        SummaryReturnRelation::Global(address) => Some(SymValue::concrete(address, call.ret_bits)),
        SummaryReturnRelation::HeapAlloc => {
            let size = call
                .args
                .first()
                .and_then(SymValue::as_concrete)
                .filter(|size| *size > 0)
                .unwrap_or(0x100);
            let (_region, base_addr) = state.allocate_heap_region("interproc_heap", size);
            Some(SymValue::concrete(base_addr, call.ret_bits))
        }
        SummaryReturnRelation::Unknown => Some(SymValue::unknown(call.ret_bits)),
    }
}

fn apply_interproc_memory_effect<'ctx>(
    state: &mut SymState<'ctx>,
    call: &CallInfo<'ctx>,
    effect: &r2ssa::SummaryMemoryEffect,
) {
    match effect.location.region {
        SummaryMemoryRegion::Arg { index } => {
            let Some(base) = call.args.get(index).cloned() else {
                return;
            };
            apply_memory_effect_at_base(state, &base, call.arg_bits, effect);
        }
        SummaryMemoryRegion::Global { address } => {
            let base = SymValue::concrete(address, call.arg_bits);
            apply_memory_effect_at_base(state, &base, call.arg_bits, effect);
        }
        SummaryMemoryRegion::HeapReturn | SummaryMemoryRegion::Unknown => {}
    }
}

fn apply_interproc_transfer_effect<'ctx>(
    state: &mut SymState<'ctx>,
    call: &CallInfo<'ctx>,
    effect: &r2ssa::SummaryTransferEffect,
) {
    let Some(dst) = summary_location_value(state, call, effect.dst) else {
        return;
    };
    let Some(src) = summary_location_value(state, call, effect.src) else {
        return;
    };
    let len = match effect.len {
        r2ssa::SummaryTransferLength::Arg(index) => call
            .args
            .get(index)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits)),
        r2ssa::SummaryTransferLength::Const(value) => SymValue::concrete(value, call.arg_bits),
        r2ssa::SummaryTransferLength::Unknown => SymValue::unknown(call.arg_bits),
    };
    copy_bytes(
        state,
        &dst,
        &src,
        &len,
        DEFAULT_MAX_INTERPROC_HAVOC,
        ByteSummaryPolicy::summarized(DEFAULT_MAX_INTERPROC_HAVOC),
    );
}

fn summary_location_value<'ctx>(
    state: &mut SymState<'ctx>,
    call: &CallInfo<'ctx>,
    location: r2ssa::SummaryMemoryLocation,
) -> Option<SymValue<'ctx>> {
    let base = match location.region {
        SummaryMemoryRegion::Arg { index } => call.args.get(index).cloned()?,
        SummaryMemoryRegion::Global { address } => SymValue::concrete(address, call.arg_bits),
        SummaryMemoryRegion::HeapReturn | SummaryMemoryRegion::Unknown => return None,
    };
    let offset = location.range.map(|range| range.offset_lo).unwrap_or(0);
    if offset == 0 {
        Some(base)
    } else {
        Some(base.add(
            state.context(),
            &SymValue::concrete(offset as u64, call.arg_bits),
        ))
    }
}

fn apply_memory_effect_at_base<'ctx>(
    state: &mut SymState<'ctx>,
    base: &SymValue<'ctx>,
    ptr_bits: u32,
    effect: &r2ssa::SummaryMemoryEffect,
) {
    let width = effect
        .location
        .range
        .and_then(|range| range.width)
        .unwrap_or(DEFAULT_MAX_INTERPROC_HAVOC as u32)
        .min(DEFAULT_MAX_INTERPROC_HAVOC as u32)
        .max(1);
    let start_offset = effect
        .location
        .range
        .map(|range| range.offset_lo)
        .unwrap_or(0);
    let start = base.add(
        state.context(),
        &SymValue::concrete(start_offset as u64, ptr_bits),
    );

    match effect.kind {
        SummaryMemoryEffectKind::Read => {
            let _ = state.mem_read(&start, width);
        }
        SummaryMemoryEffectKind::Write
        | SummaryMemoryEffectKind::Escape
        | SummaryMemoryEffectKind::Free => {
            let taint = base.get_taint();
            for i in 0..width {
                let addr = start.add(state.context(), &SymValue::concrete(i as u64, ptr_bits));
                let byte =
                    SymValue::symbolic_tainted(BV::fresh_const("interproc_mem", 8), 8, taint);
                state.mem_write(&addr, &byte, 1);
            }
        }
    }
}

fn arch_has_register(arch: &ArchSpec, name: &str) -> bool {
    arch.registers
        .iter()
        .any(|reg| reg.name.eq_ignore_ascii_case(name))
}

fn register_aliases(base: &str) -> Vec<&str> {
    match base {
        "RAX" => vec!["RAX", "EAX"],
        "RDI" => vec!["RDI", "EDI"],
        "RSI" => vec!["RSI", "ESI"],
        "RDX" => vec!["RDX", "EDX"],
        "RCX" => vec!["RCX", "ECX"],
        "R8" => vec!["R8", "R8D"],
        "R9" => vec!["R9", "R9D"],
        "RSP" => vec!["RSP", "ESP"],
        "RBP" => vec!["RBP", "EBP"],
        _ => vec![base],
    }
}

fn normalize_core_summary_name(name: &str) -> Option<&'static str> {
    let normalized_owned = name.trim().to_ascii_lowercase();
    let mut normalized = normalized_owned.as_str();

    for prefix in ["sym.imp.", "sym.", "imp.", "reloc.", "dbg."] {
        while let Some(rest) = normalized.strip_prefix(prefix) {
            normalized = rest;
        }
    }

    while let Some(rest) = normalized.strip_suffix("@plt") {
        normalized = rest;
    }
    while let Some(rest) = normalized.strip_suffix(".plt") {
        normalized = rest;
    }
    if let Some((base, _)) = normalized.split_once('@') {
        normalized = base;
    }

    if let Some(rest) = normalized.strip_prefix("__isoc99_") {
        normalized = rest;
    }
    if let Some(rest) = normalized.strip_prefix("__gi_") {
        normalized = rest;
    }
    while let Some(rest) = normalized.strip_prefix('_') {
        normalized = rest;
    }

    match normalized {
        "strlen" | "__strlen_chk" => Some("strlen"),
        "strcmp" => Some("strcmp"),
        "memcmp" => Some("memcmp"),
        "memcpy" | "__memcpy_chk" => Some("memcpy"),
        "copyin" => Some("copyin"),
        "copyout" => Some("copyout"),
        "memset" => Some("memset"),
        "malloc" | "__libc_malloc" | "__gi___libc_malloc" => Some("malloc"),
        "free" => Some("free"),
        "os_ref_retain" | "osobject_retain" => Some("retain"),
        "os_ref_release" | "osobject_release" => Some("release"),
        "lck_mtx_lock" | "lck_rw_lock_shared" | "lck_rw_lock_exclusive" => Some("lock"),
        "lck_mtx_unlock" | "lck_rw_unlock_shared" | "lck_rw_unlock_exclusive" => Some("unlock"),
        "puts" => Some("puts"),
        "printf" | "__printf_chk" => Some("printf"),
        "read" | "__read_chk" => Some("read"),
        "isatty" => Some("isatty"),
        "sleep" => Some("sleep"),
        "usleep" => Some("usleep"),
        "nanosleep" => Some("nanosleep"),
        "exit" | "_exit" => Some("exit"),
        _ => None,
    }
}

fn find_register_key<'ctx>(state: &SymState<'ctx>, base: &str) -> Option<String> {
    let mut best: Option<(u32, String)> = None;
    for key in state.registers().keys() {
        if let Some((prefix, version)) = split_version(key) {
            if prefix.eq_ignore_ascii_case(base)
                && best
                    .as_ref()
                    .is_none_or(|(best_version, _)| version > *best_version)
            {
                best = Some((version, key.clone()));
            }
        } else if key.eq_ignore_ascii_case(base) {
            return Some(key.clone());
        }
    }
    best.map(|(_, key)| key)
}

fn split_version(name: &str) -> Option<(&str, u32)> {
    let (prefix, suffix) = name.rsplit_once('_')?;
    if suffix.is_empty() || !suffix.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let version = suffix.parse().ok()?;
    Some((prefix, version))
}

fn adjust_bits<'ctx>(ctx: &'ctx z3::Context, value: SymValue<'ctx>, bits: u32) -> SymValue<'ctx> {
    if value.bits() == bits {
        return value;
    }
    if value.bits() < bits {
        value.zero_extend(ctx, bits)
    } else {
        value.extract(ctx, bits - 1, 0)
    }
}

/// memcpy(dst, src, n) summary.
pub struct MemcpySummary {
    max_copy: u64,
    byte_policy: ByteSummaryPolicy,
}

impl MemcpySummary {
    /// Create a memcpy summary with an upper bound on copy size.
    pub fn new(max_copy: u64) -> Self {
        Self::with_policy(max_copy, ByteSummaryPolicy::precise(max_copy))
    }

    fn with_policy(max_copy: u64, byte_policy: ByteSummaryPolicy) -> Self {
        Self {
            max_copy,
            byte_policy,
        }
    }
}

impl<'ctx> FunctionSummary<'ctx> for MemcpySummary {
    fn name(&self) -> &'static str {
        "memcpy"
    }

    fn arity(&self) -> usize {
        3
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let dst = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let src = call
            .args
            .get(1)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let n = call
            .args
            .get(2)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        copy_bytes(state, &dst, &src, &n, self.max_copy, self.byte_policy);
        if let (Some(dst_addr), Some(src_addr), Some(n)) =
            (dst.as_concrete(), src.as_concrete(), n.as_concrete())
            && n > 0
            && n <= self.max_copy
            && n <= u32::MAX as u64
        {
            let provenance = RuntimeValueProvenance {
                source_addr: src_addr,
                size: n as u32,
            };
            state.note_runtime_store_copy(dst_addr, n as u32, Some(&provenance));
        }
        SummaryEffect::Return(Some(dst))
    }
}

/// copyin/copyout-style kernel summary.
///
/// The memory transfer is summarized on the success path, but the return value
/// remains symbolic and range-bounded so callers can still explore fault paths.
struct KernelCopySummary {
    name: &'static str,
    dst_arg: usize,
    src_arg: usize,
    len_arg: usize,
    max_copy: u64,
    byte_policy: ByteSummaryPolicy,
}

impl KernelCopySummary {
    fn copyin(max_copy: u64, byte_policy: ByteSummaryPolicy) -> Self {
        Self {
            name: "copyin",
            dst_arg: 1,
            src_arg: 0,
            len_arg: 2,
            max_copy,
            byte_policy,
        }
    }

    fn copyout(max_copy: u64, byte_policy: ByteSummaryPolicy) -> Self {
        Self {
            name: "copyout",
            dst_arg: 1,
            src_arg: 0,
            len_arg: 2,
            max_copy,
            byte_policy,
        }
    }
}

impl<'ctx> FunctionSummary<'ctx> for KernelCopySummary {
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        3
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let dst = call
            .args
            .get(self.dst_arg)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let src = call
            .args
            .get(self.src_arg)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let n = call
            .args
            .get(self.len_arg)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));

        copy_bytes(state, &dst, &src, &n, self.max_copy, self.byte_policy);
        let ret = SymValue::symbolic(BV::fresh_const(self.name, call.ret_bits), call.ret_bits);
        state.constrain_range(&ret, 0, 0x1000);
        SummaryEffect::Return(Some(ret))
    }
}

/// strlen(s) summary.
pub struct StrlenSummary {
    max_len: u64,
}

impl StrlenSummary {
    /// Create a strlen summary with an upper bound.
    pub fn new(max_len: u64) -> Self {
        Self { max_len }
    }
}

impl<'ctx> FunctionSummary<'ctx> for StrlenSummary {
    fn name(&self) -> &'static str {
        "strlen"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let arg = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let mem_taint = if arg.as_concrete().is_some() {
            state.mem_read(&arg, 1).get_taint()
        } else {
            0
        };
        let taint = arg.get_taint() | mem_taint;
        let ret_ast = BV::fresh_const("strlen_ret", call.ret_bits);
        let ret = SymValue::symbolic_tainted(ret_ast, call.ret_bits, taint);
        state.constrain_range(&ret, 0, self.max_len);
        SummaryEffect::Return(Some(ret))
    }
}

/// strcmp(a, b) summary.
#[derive(Default)]
pub struct StrcmpSummary;

impl StrcmpSummary {
    /// Create a strcmp summary.
    pub fn new() -> Self {
        Self
    }
}

impl<'ctx> FunctionSummary<'ctx> for StrcmpSummary {
    fn name(&self) -> &'static str {
        "strcmp"
    }

    fn arity(&self) -> usize {
        2
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let a = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let b = call
            .args
            .get(1)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let a_taint = if a.as_concrete().is_some() {
            state.mem_read(&a, 1).get_taint()
        } else {
            0
        };
        let b_taint = if b.as_concrete().is_some() {
            state.mem_read(&b, 1).get_taint()
        } else {
            0
        };
        let taint = a.get_taint() | b.get_taint() | a_taint | b_taint;

        let ret_ast = BV::fresh_const("strcmp_ret", call.ret_bits);
        let ret = SymValue::symbolic_tainted(ret_ast, call.ret_bits, taint);
        let ret_bv = ret.to_bv(state.context());
        let neg_one = BV::from_i64(-1, call.ret_bits);
        let zero = BV::from_u64(0, call.ret_bits);
        let one = BV::from_u64(1, call.ret_bits);
        let cond = ret_bv.eq(&neg_one) | ret_bv.eq(&zero) | ret_bv.eq(&one);
        state.add_constraint(cond);
        SummaryEffect::Return(Some(ret))
    }
}

/// memcmp(a, b, n) summary.
pub struct MemcmpSummary {
    max_cmp: u64,
}

impl MemcmpSummary {
    /// Create a memcmp summary with an upper bound on compared length.
    pub fn new(max_cmp: u64) -> Self {
        Self { max_cmp }
    }
}

impl<'ctx> FunctionSummary<'ctx> for MemcmpSummary {
    fn name(&self) -> &'static str {
        "memcmp"
    }

    fn arity(&self) -> usize {
        3
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let a = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let b = call
            .args
            .get(1)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let n = call
            .args
            .get(2)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));

        if n.as_concrete() == Some(0) {
            return SummaryEffect::Return(Some(SymValue::concrete(0, call.ret_bits)));
        }

        if n.as_concrete().is_none() {
            state.constrain_range(&n, 0, self.max_cmp);
        }

        let a_taint = if a.as_concrete().is_some() {
            state.mem_read(&a, 1).get_taint()
        } else {
            0
        };
        let b_taint = if b.as_concrete().is_some() {
            state.mem_read(&b, 1).get_taint()
        } else {
            0
        };
        let taint = a.get_taint() | b.get_taint() | n.get_taint() | a_taint | b_taint;

        let ret_ast = BV::fresh_const("memcmp_ret", call.ret_bits);
        let ret = SymValue::symbolic_tainted(ret_ast, call.ret_bits, taint);
        constrain_ret_tristate(state, &ret, call.ret_bits);
        SummaryEffect::Return(Some(ret))
    }
}

/// memset(dst, c, n) summary.
pub struct MemsetSummary {
    max_set: u64,
    byte_policy: ByteSummaryPolicy,
}

impl MemsetSummary {
    /// Create a memset summary with an upper bound on set size.
    pub fn new(max_set: u64) -> Self {
        Self::with_policy(max_set, ByteSummaryPolicy::precise(max_set))
    }

    fn with_policy(max_set: u64, byte_policy: ByteSummaryPolicy) -> Self {
        Self {
            max_set,
            byte_policy,
        }
    }
}

impl<'ctx> FunctionSummary<'ctx> for MemsetSummary {
    fn name(&self) -> &'static str {
        "memset"
    }

    fn arity(&self) -> usize {
        3
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let dst = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let c = call
            .args
            .get(1)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let n = call
            .args
            .get(2)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));

        set_bytes(state, &dst, &c, &n, self.max_set, self.byte_policy);
        SummaryEffect::Return(Some(dst))
    }
}

/// puts(s) summary.
pub struct PutsSummary {
    max_ret: u64,
}

impl PutsSummary {
    /// Create a puts summary.
    pub fn new(max_ret: u64) -> Self {
        Self { max_ret }
    }
}

impl<'ctx> FunctionSummary<'ctx> for PutsSummary {
    fn name(&self) -> &'static str {
        "puts"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let s = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let mem_taint = if s.as_concrete().is_some() {
            state.mem_read(&s, 1).get_taint()
        } else {
            0
        };
        let taint = s.get_taint() | mem_taint;
        let ret_ast = BV::fresh_const("puts_ret", call.ret_bits);
        let ret = SymValue::symbolic_tainted(ret_ast, call.ret_bits, taint);
        state.constrain_range(&ret, 0, self.max_ret);
        SummaryEffect::Return(Some(ret))
    }
}

/// Basic printf(fmt, ...) summary.
pub struct PrintfSummaryBasic {
    max_ret: u64,
}

impl PrintfSummaryBasic {
    /// Create a basic printf summary.
    pub fn new(max_ret: u64) -> Self {
        Self { max_ret }
    }
}

impl<'ctx> FunctionSummary<'ctx> for PrintfSummaryBasic {
    fn name(&self) -> &'static str {
        "printf"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let fmt = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let mem_taint = if fmt.as_concrete().is_some() {
            state.mem_read(&fmt, 1).get_taint()
        } else {
            0
        };
        let taint = fmt.get_taint() | mem_taint;
        let ret_ast = BV::fresh_const("printf_ret", call.ret_bits);
        let ret = SymValue::symbolic_tainted(ret_ast, call.ret_bits, taint);
        state.constrain_range(&ret, 0, self.max_ret);
        SummaryEffect::Return(Some(ret))
    }
}

/// read(fd, buf, count) summary.
#[derive(Default)]
pub struct ReadSummary;

impl ReadSummary {
    pub fn new() -> Self {
        Self
    }
}

impl<'ctx> FunctionSummary<'ctx> for ReadSummary {
    fn name(&self) -> &'static str {
        "read"
    }

    fn arity(&self) -> usize {
        3
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let fd = call
            .args
            .first()
            .and_then(SymValue::as_concrete)
            .map(|value| value as i32);
        let buf = call
            .args
            .get(1)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let count = call
            .args
            .get(2)
            .and_then(SymValue::as_concrete)
            .unwrap_or(0) as usize;

        let Some(fd) = fd else {
            let ret = SymValue::unknown(call.ret_bits);
            return SummaryEffect::Return(Some(ret));
        };

        let Some(bytes) = state.read_symbolic_fd_bytes(fd, count) else {
            return SummaryEffect::Return(Some(SymValue::concrete(0, call.ret_bits)));
        };

        if let Some(base) = buf.as_concrete() {
            for (idx, byte) in bytes.iter().enumerate() {
                let addr = SymValue::concrete(base.saturating_add(idx as u64), call.arg_bits);
                state.mem_write(&addr, byte, 1);
            }
        }

        SummaryEffect::Return(Some(SymValue::concrete(bytes.len() as u64, call.ret_bits)))
    }
}

/// isatty(fd) summary.
#[derive(Default)]
pub struct IsattySummary;

impl IsattySummary {
    pub fn new() -> Self {
        Self
    }
}

impl<'ctx> FunctionSummary<'ctx> for IsattySummary {
    fn name(&self) -> &'static str {
        "isatty"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let fd = call
            .args
            .first()
            .and_then(SymValue::as_concrete)
            .map(|value| value as i32)
            .unwrap_or(-1);
        let ret = if state.is_tty_fd(fd) { 1 } else { 0 };
        SummaryEffect::Return(Some(SymValue::concrete(ret, call.ret_bits)))
    }
}

/// sleep/usleep/nanosleep summary.
pub struct SleepSummary {
    name: &'static str,
    arity: usize,
}

impl SleepSummary {
    pub fn sleep() -> Self {
        Self {
            name: "sleep",
            arity: 1,
        }
    }

    pub fn usleep() -> Self {
        Self {
            name: "usleep",
            arity: 1,
        }
    }

    pub fn nanosleep() -> Self {
        Self {
            name: "nanosleep",
            arity: 2,
        }
    }
}

impl<'ctx> FunctionSummary<'ctx> for SleepSummary {
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        self.arity
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let ret = if state.skip_sleep_calls() {
            SymValue::concrete(0, call.ret_bits)
        } else {
            SymValue::unknown(call.ret_bits)
        };
        SummaryEffect::Return(Some(ret))
    }
}

/// malloc(size) summary.
#[derive(Default)]
pub struct MallocSummary;

impl MallocSummary {
    /// Create a malloc summary.
    pub fn new() -> Self {
        Self
    }
}

impl<'ctx> FunctionSummary<'ctx> for MallocSummary {
    fn name(&self) -> &'static str {
        "malloc"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let size = call
            .args
            .first()
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.arg_bits));
        let taint = size.get_taint();
        let ret_ast = BV::fresh_const("malloc_ptr", call.ret_bits);
        let ret = SymValue::symbolic_tainted(ret_ast, call.ret_bits, taint);
        state.constrain_ne(&ret, 0);
        SummaryEffect::Return(Some(ret))
    }
}

/// free(ptr) summary.
#[derive(Default)]
pub struct FreeSummary;

impl FreeSummary {
    /// Create a free summary.
    pub fn new() -> Self {
        Self
    }
}

impl<'ctx> FunctionSummary<'ctx> for FreeSummary {
    fn name(&self) -> &'static str {
        "free"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, _state: &mut SymState<'ctx>, _call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        SummaryEffect::Return(None)
    }
}

/// Return one argument unchanged, useful for retain-style helpers.
struct ArgReturnSummary {
    name: &'static str,
    arg_index: usize,
}

impl ArgReturnSummary {
    fn retain() -> Self {
        Self {
            name: "retain",
            arg_index: 0,
        }
    }
}

impl<'ctx> FunctionSummary<'ctx> for ArgReturnSummary {
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        self.arg_index + 1
    }

    fn execute(&self, state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let ret = call
            .args
            .get(self.arg_index)
            .cloned()
            .unwrap_or_else(|| SymValue::unknown(call.ret_bits));
        SummaryEffect::Return(Some(adjust_bits(state.context(), ret, call.ret_bits)))
    }
}

/// No-op helper summary for side-effect-only helpers whose exact state change
/// is intentionally not owned by the symbolic executor.
struct NoopSummary {
    name: &'static str,
}

impl NoopSummary {
    fn release() -> Self {
        Self { name: "release" }
    }

    fn lock() -> Self {
        Self { name: "lock" }
    }

    fn unlock() -> Self {
        Self { name: "unlock" }
    }
}

impl<'ctx> FunctionSummary<'ctx> for NoopSummary {
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, _state: &mut SymState<'ctx>, _call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        SummaryEffect::Return(None)
    }
}

/// exit(code) summary.
#[derive(Default)]
pub struct ExitSummary;

impl ExitSummary {
    /// Create an exit summary.
    pub fn new() -> Self {
        Self
    }
}

impl<'ctx> FunctionSummary<'ctx> for ExitSummary {
    fn name(&self) -> &'static str {
        "exit"
    }

    fn arity(&self) -> usize {
        1
    }

    fn execute(&self, _state: &mut SymState<'ctx>, call: &CallInfo<'ctx>) -> SummaryEffect<'ctx> {
        let code = call
            .args
            .first()
            .and_then(|val| val.as_concrete())
            .unwrap_or(0);
        SummaryEffect::Terminate(ExitStatus::Exit(code))
    }
}

fn copy_bytes<'ctx>(
    state: &mut SymState<'ctx>,
    dst: &SymValue<'ctx>,
    src: &SymValue<'ctx>,
    n: &SymValue<'ctx>,
    max_copy: u64,
    byte_policy: ByteSummaryPolicy,
) {
    let ctx = state.context();
    let n_concrete = n.as_concrete();
    if n_concrete == Some(0) {
        return;
    }
    let copy_len = n_concrete.unwrap_or(max_copy).min(max_copy);

    if n_concrete.is_none() {
        state.constrain_range(n, 0, max_copy);
    }

    if !byte_policy.use_precise_model(n_concrete) {
        let src_byte = if src.as_concrete().is_some() {
            let read = state.mem_read(src, 1);
            read.with_taint(read.get_taint() | src.get_taint() | n.get_taint())
        } else {
            SymValue::symbolic_tainted(
                BV::fresh_const("memcpy_byte", 8),
                8,
                src.get_taint() | n.get_taint(),
            )
        };
        state.mem_write(dst, &src_byte, 1);
        return;
    }

    for offset in 0..copy_len {
        let offset_val = SymValue::concrete(offset, dst.bits());
        let dst_addr = dst.add(ctx, &offset_val);
        let src_addr = src.add(ctx, &offset_val);
        let src_byte = state.mem_read(&src_addr, 1);
        if n_concrete.is_some() {
            state.mem_write(&dst_addr, &src_byte, 1);
        } else {
            let dst_old = state.mem_read(&dst_addr, 1);
            let idx_val = SymValue::concrete(offset, n.bits());
            let cond = idx_val.ult(ctx, n);
            let cond_bool = cond.to_bv(ctx).eq(BV::from_u64(1, 1));
            let taint = src_byte.get_taint() | dst_old.get_taint() | n.get_taint();
            let merged = SymValue::symbolic_tainted(
                cond_bool.ite(&src_byte.to_bv(ctx), &dst_old.to_bv(ctx)),
                8,
                taint,
            );
            state.mem_write(&dst_addr, &merged, 1);
        }
    }
}

fn set_bytes<'ctx>(
    state: &mut SymState<'ctx>,
    dst: &SymValue<'ctx>,
    c: &SymValue<'ctx>,
    n: &SymValue<'ctx>,
    max_set: u64,
    byte_policy: ByteSummaryPolicy,
) {
    let ctx = state.context();
    let n_concrete = n.as_concrete();
    if n_concrete == Some(0) {
        return;
    }
    let set_len = n_concrete.unwrap_or(max_set).min(max_set);

    if n_concrete.is_none() {
        state.constrain_range(n, 0, max_set);
    }

    let c_byte = if let Some(concrete) = c.as_concrete() {
        SymValue::concrete_tainted(concrete & 0xff, 8, c.get_taint())
    } else {
        c.extract(ctx, 7, 0).with_taint(c.get_taint())
    };

    if !byte_policy.use_precise_model(n_concrete) {
        state.mem_write(dst, &c_byte, 1);
        return;
    }

    for offset in 0..set_len {
        let offset_val = SymValue::concrete(offset, dst.bits());
        let dst_addr = dst.add(ctx, &offset_val);
        if n_concrete.is_some() {
            state.mem_write(&dst_addr, &c_byte, 1);
        } else {
            let dst_old = state.mem_read(&dst_addr, 1);
            let idx_val = SymValue::concrete(offset, n.bits());
            let cond = idx_val.ult(ctx, n);
            let cond_bool = cond.to_bv(ctx).eq(BV::from_u64(1, 1));
            let taint = c_byte.get_taint() | dst_old.get_taint() | n.get_taint();
            let merged = SymValue::symbolic_tainted(
                cond_bool.ite(&c_byte.to_bv(ctx), &dst_old.to_bv(ctx)),
                8,
                taint,
            );
            state.mem_write(&dst_addr, &merged, 1);
        }
    }
}

fn constrain_ret_tristate<'ctx>(state: &mut SymState<'ctx>, ret: &SymValue<'ctx>, ret_bits: u32) {
    let ret_bv = ret.to_bv(state.context());
    let neg_one = BV::from_i64(-1, ret_bits);
    let zero = BV::from_u64(0, ret_bits);
    let one = BV::from_u64(1, ret_bits);
    let cond = ret_bv.eq(&neg_one) | ret_bv.eq(&zero) | ret_bv.eq(&one);
    state.add_constraint(cond);
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch
    }

    fn const_vn(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    fn returning_artifact(addr: u64) -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: const_vn(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("returning artifact")
    }

    fn exact_interproc_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RSP", 0x08, 8));
        arch.add_register(RegisterDef::new("RIP", 0x10, 8));
        arch
    }

    fn exact_interproc_artifact(addr: u64, ops: Vec<R2ILOp>) -> Arc<SsaArtifact> {
        let arch = exact_interproc_arch();
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2sym-interproc-hook-owner".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0x00),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x08)))
        .and_then(|interface| interface.with_return_address_storage(storage(0x10)))
        .expect("exact interproc hook interface");
        Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[R2ILBlock {
                    addr,
                    size: 1,
                    ops,
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&arch),
                interface,
            )
            .expect("exact interproc hook root"),
        )
    }

    fn exact_interproc_root(addr: u64) -> Arc<SsaArtifact> {
        exact_interproc_artifact(
            addr,
            vec![R2ILOp::Return {
                target: const_vn(0, 8),
            }],
        )
    }

    #[test]
    fn interproc_hook_installation_requires_exact_owner_and_current_schema() {
        let root = exact_interproc_root(0x401000);
        let input = PreparedInterprocFunctionInput {
            id: InterprocFunctionId(root.function().entry),
            name: Some("root".to_string()),
            prepared: &root,
        };
        let summaries = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[input],
            InterprocSolveConfig::default(),
        )
        .expect("source-owned interproc report");
        let foreign = exact_interproc_root(0x401000);
        let ctx = z3::Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let registry = SummaryRegistry::new(CallConv::x86_64_sysv());
        let symbols = HashMap::new();

        assert!(
            registry
                .install_interproc_summaries_for_function(
                    &mut explorer,
                    &root,
                    &summaries,
                    &symbols,
                )
                .is_some()
        );
        assert!(
            registry
                .install_interproc_summaries_for_function(
                    &mut explorer,
                    &foreign,
                    &summaries,
                    &symbols,
                )
                .is_none()
        );

        let mut stale = summaries.report().clone();
        stale.schema_version = stale.schema_version.saturating_sub(1);
        assert!(
            registry
                .install_interproc_summary_report_for_function(
                    &mut explorer,
                    root.as_ref(),
                    &stale,
                    &symbols,
                )
                .is_none()
        );
    }

    #[test]
    fn installed_interproc_hook_retains_exact_owner_until_explorer_drop() {
        let root_addr = 0x401000;
        let root = exact_interproc_artifact(
            root_addr,
            vec![
                R2ILOp::Call {
                    target: const_vn(root_addr, 8),
                },
                R2ILOp::Return {
                    target: const_vn(0, 8),
                },
            ],
        );
        let weak = Arc::downgrade(&root);
        let summaries = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(root_addr),
                name: None,
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("source-owned recursive summary");
        let ctx = z3::Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let registry = SummaryRegistry::new(CallConv::x86_64_sysv());
        let installed = registry
            .install_interproc_summaries_for_function(
                &mut explorer,
                &root,
                &summaries,
                &HashMap::new(),
            )
            .expect("matching prepared summary");
        assert_eq!(installed.installed, 1);

        drop(summaries);
        drop(root);
        assert!(weak.upgrade().is_some());
        drop(explorer);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn installed_scope_hook_retains_exact_helper_until_explorer_drop() {
        let root_addr = 0x401000;
        let helper_addr = 0x402000;
        let root = exact_interproc_artifact(
            root_addr,
            vec![
                R2ILOp::Call {
                    target: const_vn(helper_addr, 8),
                },
                R2ILOp::Return {
                    target: const_vn(0, 8),
                },
            ],
        );
        let helper = exact_interproc_root(helper_addr);
        let helper_weak = Arc::downgrade(&helper);
        let scope = PreparedFunctionScope::new(
            root_addr,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(root_addr),
                    name: None,
                    prepared: Arc::clone(&root),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(helper_addr),
                    name: None,
                    prepared: Arc::clone(&helper),
                },
            ],
        )
        .expect("exact manual scope");
        let report = r2ssa::solve_interproc_summary_set(
            &[
                r2ssa::InterprocFunctionInput {
                    id: InterprocFunctionId(root_addr),
                    name: None,
                    prepared: &root,
                },
                r2ssa::InterprocFunctionInput {
                    id: InterprocFunctionId(helper_addr),
                    name: None,
                    prepared: &helper,
                },
            ],
            Some(&exact_interproc_arch()),
            Some(InterprocFunctionId(root_addr)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        )
        .expect("current advisory interproc report");
        let ctx = z3::Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let registry = SummaryRegistry::new(CallConv::x86_64_sysv());
        let installed = registry
            .install_interproc_summary_report_for_function_with_provenance(
                &mut explorer,
                root.as_ref(),
                &report,
                &HashMap::new(),
                scope.clone(),
            )
            .expect("current report");
        assert_eq!(installed.installed, 1);

        drop(report);
        drop(scope);
        drop(helper);
        drop(root);
        assert!(helper_weak.upgrade().is_some());
        drop(explorer);
        assert!(helper_weak.upgrade().is_none());
    }

    #[test]
    fn installed_scope_core_hook_retains_exact_helper_until_explorer_drop() {
        let root_addr = 0x401000;
        let helper_addr = 0x402000;
        let root = exact_interproc_artifact(
            root_addr,
            vec![
                R2ILOp::Call {
                    target: const_vn(helper_addr, 8),
                },
                R2ILOp::Return {
                    target: const_vn(0, 8),
                },
            ],
        );
        let helper = exact_interproc_root(helper_addr);
        let helper_weak = Arc::downgrade(&helper);
        let scope = PreparedFunctionScope::new(
            root_addr,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(root_addr),
                    name: None,
                    prepared: Arc::clone(&root),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(helper_addr),
                    name: None,
                    prepared: Arc::clone(&helper),
                },
            ],
        )
        .expect("exact manual scope");
        let ctx = z3::Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let registry = SummaryRegistry::with_core(CallConv::x86_64_sysv());
        let symbols = HashMap::from([(helper_addr, "memcpy".to_string())]);
        let _ = registry.install_scope_summaries_for_explorer(
            &mut explorer,
            &ctx,
            root.as_ref(),
            &scope,
            Some(&exact_interproc_arch()),
            &symbols,
        );

        drop(scope);
        drop(helper);
        drop(root);
        assert!(helper_weak.upgrade().is_some());
        drop(explorer);
        assert!(helper_weak.upgrade().is_none());
    }

    #[test]
    fn advisory_derivation_does_not_promote_manual_scope_or_name_seeds() {
        let root_addr = 0x401000;
        let helper_addr = 0x402000;
        let root = exact_interproc_artifact(
            root_addr,
            vec![
                R2ILOp::Call {
                    target: const_vn(helper_addr, 8),
                },
                R2ILOp::Return {
                    target: const_vn(0, 8),
                },
            ],
        );
        let helper = exact_interproc_root(helper_addr);
        let scope = PreparedFunctionScope::new(
            root_addr,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(root_addr),
                    name: Some("root".to_string()),
                    prepared: root,
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(helper_addr),
                    name: Some("memcpy".to_string()),
                    prepared: helper,
                },
            ],
        )
        .expect("exact manual scope");
        let ctx = z3::Context::thread_local();
        let registry = SummaryRegistry::new(CallConv::x86_64_sysv());
        let arch = exact_interproc_arch();
        let derived =
            registry.derive_symbolic_summaries(&ctx, &scope, Some(&arch), &HashMap::new());
        let helper_summary = derived
            .interproc
            .summaries
            .get(&InterprocFunctionId(helper_addr))
            .expect("advisory helper report");

        assert_eq!(derived.interproc.root, Some(InterprocFunctionId(root_addr)));
        assert!(helper_summary.memory_effects.is_empty());
        assert!(helper_summary.transfer_effects.is_empty());
        assert!(helper_summary.allocation_effects.is_empty());
        assert!(matches!(
            registry.derive_source_owned_symbolic_summaries(
                &ctx,
                &scope,
                Some(&arch),
                &HashMap::new(),
            ),
            Err(PreparedInterprocSummaryError::ManualFunction)
                | Err(PreparedInterprocSummaryError::ManualRootWithHelpers)
        ));
    }

    #[test]
    fn empty_summary_substitutions_are_identity() {
        let ctx = z3::Context::thread_local();
        let var = BV::fresh_const("empty_summary_substitution", 64);
        let guard = var.eq(&var);
        let value = SymValue::symbolic(var.clone(), 64);

        assert_eq!(substitute_bool(&guard, &[]).to_string(), guard.to_string());
        assert_eq!(
            substitute_value(&ctx, &value, &[]).to_bv(&ctx).to_string(),
            value.to_bv(&ctx).to_string()
        );
    }

    #[test]
    fn callconv_accepts_x86_64_arch_specs_with_bit_sized_addr_width() {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 64;
        assert!(CallConv::for_arch_spec(&arch).is_some());
        assert!(SummaryRegistry::with_core_for_arch(&arch).is_some());
        assert!(
            SummaryRegistry::with_profile_for_arch(&arch, SummaryProfile::PathListing).is_some()
        );
    }

    #[test]
    fn imported_names_do_not_select_a_detached_calling_convention() {
        let arch = test_arch();
        let imported = HashMap::from([(0x2000, "kernel32.dll_VirtualAlloc".to_string())]);
        let empty = HashMap::new();
        let with_import =
            CallConv::for_arch_spec_and_symbols(&arch, &imported).expect("x86 callconv");
        let without_import =
            CallConv::for_arch_spec_and_symbols(&arch, &empty).expect("x86 callconv");

        assert_eq!(with_import.arg_registers, without_import.arg_registers);
        assert_eq!(with_import.ret_register, without_import.ret_register);
    }

    #[test]
    fn kernel_helper_names_normalize_to_semantic_summaries() {
        let cases = [
            ("sym._copyin", Some("copyin")),
            ("sym._copyout", Some("copyout")),
            ("sym._IOMalloc", None),
            ("sym._kalloc_type_impl", None),
            ("sym._IOFree", None),
            ("sym._os_ref_retain", Some("retain")),
            ("sym._os_ref_release", Some("release")),
            ("sym._lck_mtx_lock", Some("lock")),
            ("sym._lck_mtx_unlock", Some("unlock")),
            ("sym._clock_gettime", None),
        ];
        for (name, expected) in cases {
            assert_eq!(normalize_core_summary_name(name), expected, "{name}");
        }
    }

    #[test]
    fn kernel_copyin_summary_copies_success_path_and_keeps_symbolic_status() {
        let ctx = z3::Context::thread_local();
        let mut state = SymState::new(&ctx, 0);
        let src = SymValue::concrete(0x1000, 64);
        let dst = SymValue::concrete(0x2000, 64);
        state.mem_write(
            &src,
            &SymValue::symbolic_tainted(BV::fresh_const("copyin_src", 8), 8, 0x80),
            1,
        );

        let summary = KernelCopySummary::copyin(0x40, ByteSummaryPolicy::precise(0x40));
        let ret = summary.execute(
            &mut state,
            &CallInfo {
                args: vec![src, dst.clone(), SymValue::concrete(1, 64)],
                arg_bits: 64,
                ret_bits: 32,
            },
        );

        let copied = state.mem_read(&dst, 1);
        assert_eq!(copied.get_taint(), 0x80);
        match ret {
            SummaryEffect::Return(Some(value)) => assert!(value.as_concrete().is_none()),
            _ => panic!("expected symbolic copyin status"),
        }
    }

    #[test]
    fn memcpy_summary_path_listing_summarizes_symbolic_lengths() {
        let ctx = z3::Context::thread_local();
        let src = SymValue::concrete(0x1000, 64);
        let dst = SymValue::concrete(0x2000, 64);
        let n = SymValue::symbolic(BV::fresh_const("n", 64), 64);

        let mut precise_state = SymState::new(&ctx, 0);
        precise_state.mem_write(
            &src,
            &SymValue::symbolic_tainted(BV::fresh_const("src_base", 8), 8, 0x20),
            1,
        );
        let src_far = src.add(&ctx, &SymValue::concrete(5, 64));
        precise_state.mem_write(
            &src_far,
            &SymValue::symbolic_tainted(BV::fresh_const("src_far", 8), 8, 0x40),
            1,
        );
        let precise_summary = MemcpySummary::new(0x40);
        let call = CallInfo {
            args: vec![dst.clone(), src.clone(), n.clone()],
            arg_bits: 64,
            ret_bits: 64,
        };
        let _ = precise_summary.execute(&mut precise_state, &call);
        let precise_far = precise_state.mem_read(&dst.add(&ctx, &SymValue::concrete(5, 64)), 1);
        assert_eq!(precise_far.get_taint(), 0x40);

        let mut path_listing_state = SymState::new(&ctx, 0);
        path_listing_state.mem_write(
            &src,
            &SymValue::symbolic_tainted(BV::fresh_const("src_base_pl", 8), 8, 0x20),
            1,
        );
        let src_far = src.add(&ctx, &SymValue::concrete(5, 64));
        path_listing_state.mem_write(
            &src_far,
            &SymValue::symbolic_tainted(BV::fresh_const("src_far_pl", 8), 8, 0x40),
            1,
        );
        let path_listing_summary = MemcpySummary::with_policy(
            0x40,
            ByteSummaryPolicy::summarized(PATH_LIST_PRECISE_BYTE_LIMIT),
        );
        let _ = path_listing_summary.execute(&mut path_listing_state, &call);
        let path_listing_far =
            path_listing_state.mem_read(&dst.add(&ctx, &SymValue::concrete(5, 64)), 1);
        assert_eq!(path_listing_far.get_taint(), 0);
        let path_listing_base = path_listing_state.mem_read(&dst, 1);
        assert_eq!(path_listing_base.get_taint(), 0x20);
    }

    #[test]
    fn memcpy_summary_records_runtime_materialization_provenance() {
        let ctx = z3::Context::thread_local();
        let mut state = SymState::new(&ctx, 0);
        let (_region, runtime_base) = state.allocate_heap_region("jit", 0x1000);
        state.register_runtime_region_alias(runtime_base, 0x1000, true);

        let summary = MemcpySummary::new(0x1000);
        let call = CallInfo {
            args: vec![
                SymValue::concrete(runtime_base, 64),
                SymValue::concrete(0x14009c000, 64),
                SymValue::concrete(0x1000, 64),
            ],
            arg_bits: 64,
            ret_bits: 64,
        };
        let _ = summary.execute(&mut state, &call);

        let region = state
            .runtime_region_for_pc(runtime_base)
            .expect("runtime region should remain registered");
        assert_eq!(region.source_base, Some(0x14009c000));
    }

    #[test]
    fn prepared_function_scope_with_prepared_root_rebinds_root_only() {
        let blocks_a = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: const_vn(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let blocks_b = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: const_vn(1, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let helper_blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: const_vn(2, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let root_a =
            Arc::new(SsaArtifact::for_symbolic(&blocks_a, Some(&test_arch())).expect("root a"));
        let root_b =
            Arc::new(SsaArtifact::for_symbolic(&blocks_b, Some(&test_arch())).expect("root b"));
        let helper = Arc::new(
            SsaArtifact::for_symbolic(&helper_blocks, Some(&test_arch())).expect("helper"),
        );

        let scope = PreparedFunctionScope::new(
            0x1000,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: None,
                    prepared: root_a,
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("helper".to_string()),
                    prepared: Arc::clone(&helper),
                },
            ],
        )
        .expect("scope");

        let rebound = scope
            .with_prepared_root(Arc::clone(&root_b))
            .expect("rebound scope");
        let rebound_root = rebound.root().expect("rebound root");
        assert!(Arc::ptr_eq(&rebound_root.prepared, &root_b));
        assert!(Arc::ptr_eq(
            &rebound
                .functions()
                .get(&InterprocFunctionId(0x2000))
                .expect("helper")
                .prepared,
            &helper,
        ));
        assert_eq!(rebound_root.prepared.entry, root_b.entry);
        assert_eq!(rebound_root.prepared.function().blocks().count(), 1);
        assert_eq!(
            rebound
                .functions()
                .get(&InterprocFunctionId(0x2000))
                .expect("helper")
                .prepared
                .entry,
            helper.entry
        );
    }

    #[test]
    fn scoped_function_provenance_not_display_name_controls_runtime_exclusion() {
        let root = Arc::new(returning_artifact(0x1000));
        let helper = Arc::new(
            returning_artifact(0x2000).with_name("runtime.materialized.display-only".to_string()),
        );
        let runtime =
            Arc::new(returning_artifact(0x3000).with_name("ordinary-display-name".to_string()));
        let root_id = InterprocFunctionId(0x1000);
        let helper_id = InterprocFunctionId(0x2000);
        let runtime_id = InterprocFunctionId(0x3000);
        let scope = PreparedFunctionScope::new_with_provenance(
            root_id.0,
            vec![
                ScopedPreparedFunction {
                    id: root_id,
                    name: Some("root".to_string()),
                    prepared: Arc::clone(&root),
                },
                ScopedPreparedFunction {
                    id: helper_id,
                    name: Some("runtime.materialized.display-only".to_string()),
                    prepared: helper,
                },
                ScopedPreparedFunction {
                    id: runtime_id,
                    name: Some("ordinary-display-name".to_string()),
                    prepared: Arc::clone(&runtime),
                },
            ],
            BTreeMap::from([
                (root_id, ScopedFunctionProvenance::Analyzed),
                (helper_id, ScopedFunctionProvenance::Analyzed),
                (runtime_id, ScopedFunctionProvenance::RuntimeMaterialized),
            ]),
        )
        .expect("typed scope");

        let helper = scope.functions().get(&helper_id).expect("helper");
        let runtime = scope.functions().get(&runtime_id).expect("runtime source");
        assert!(!is_runtime_materialized_scope_function(&scope, helper));
        assert!(is_runtime_materialized_scope_function(&scope, runtime));

        let runtime_only = PreparedFunctionScope::new_with_provenance(
            root_id.0,
            vec![
                ScopedPreparedFunction {
                    id: root_id,
                    name: None,
                    prepared: Arc::clone(&root),
                },
                ScopedPreparedFunction {
                    id: runtime_id,
                    name: None,
                    prepared: Arc::clone(&runtime.prepared),
                },
            ],
            BTreeMap::from([
                (root_id, ScopedFunctionProvenance::Analyzed),
                (runtime_id, ScopedFunctionProvenance::RuntimeMaterialized),
            ]),
        )
        .expect("runtime-only scope");
        let semantic_scope = runtime_only
            .source_authorized_for_semantics(&root)
            .expect("runtime materialization is excluded, not promoted");
        assert_eq!(semantic_scope.functions().len(), 1);
        assert!(semantic_scope.functions().contains_key(&root_id));
    }

    #[test]
    fn prepared_function_scope_rejects_duplicate_or_mislabeled_functions() {
        let root = Arc::new(returning_artifact(0x1000));
        let duplicate = PreparedFunctionScope::new(
            0x1000,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: Arc::clone(&root),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("duplicate".to_string()),
                    prepared: root,
                },
            ],
        );
        assert!(duplicate.is_none());

        let mislabeled = PreparedFunctionScope::new(
            0x1000,
            vec![ScopedPreparedFunction {
                id: InterprocFunctionId(0x1000),
                name: Some("mislabeled".to_string()),
                prepared: Arc::new(returning_artifact(0x2000)),
            }],
        );
        assert!(mislabeled.is_none());

        let helper = |entry, shared| {
            Arc::new(
                SsaArtifact::for_symbolic(
                    &[
                        R2ILBlock {
                            addr: entry,
                            size: 1,
                            ops: vec![R2ILOp::Branch {
                                target: const_vn(shared, 8),
                            }],
                            switch_info: None,
                            op_metadata: Default::default(),
                        },
                        R2ILBlock {
                            addr: shared,
                            size: 1,
                            ops: vec![R2ILOp::Return {
                                target: const_vn(0, 8),
                            }],
                            switch_info: None,
                            op_metadata: Default::default(),
                        },
                    ],
                    Some(&test_arch()),
                )
                .expect("helper artifact"),
            )
        };
        let overlapping = PreparedFunctionScope::new(
            0x1000,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: Arc::new(returning_artifact(0x1000)),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("helper_a".to_string()),
                    prepared: helper(0x2000, 0x4000),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x3000),
                    name: Some("helper_b".to_string()),
                    prepared: helper(0x3000, 0x4000),
                },
            ],
        );
        assert!(overlapping.is_none());

        let partial_overlap = PreparedFunctionScope::new(
            0x1000,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("wide_root".to_string()),
                    prepared: Arc::new(
                        SsaArtifact::for_symbolic(
                            &[R2ILBlock {
                                addr: 0x1000,
                                size: 8,
                                ops: vec![R2ILOp::Return {
                                    target: const_vn(0, 8),
                                }],
                                switch_info: None,
                                op_metadata: Default::default(),
                            }],
                            Some(&test_arch()),
                        )
                        .expect("wide root"),
                    ),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1004),
                    name: Some("interior_helper".to_string()),
                    prepared: Arc::new(returning_artifact(0x1004)),
                },
            ],
        );
        assert!(partial_overlap.is_none());

        assert!(!block_ranges_are_disjoint([(u64::MAX, 1)]));
    }

    #[test]
    fn prepared_function_scope_rejects_helper_machine_context_mismatch() {
        let root = Arc::new(returning_artifact(0x1000));
        let mut foreign_arch = ArchSpec::new("aarch64");
        foreign_arch.addr_size = 8;
        foreign_arch.add_register(RegisterDef::new("x0", 0, 8));
        let foreign_helper = Arc::new(
            SsaArtifact::for_symbolic(
                &[R2ILBlock {
                    addr: 0x2000,
                    size: 1,
                    ops: vec![R2ILOp::Return {
                        target: const_vn(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&foreign_arch),
            )
            .expect("foreign helper"),
        );

        assert!(
            PreparedFunctionScope::new(
                0x1000,
                vec![
                    ScopedPreparedFunction {
                        id: InterprocFunctionId(0x1000),
                        name: Some("root".to_string()),
                        prepared: root,
                    },
                    ScopedPreparedFunction {
                        id: InterprocFunctionId(0x2000),
                        name: Some("foreign".to_string()),
                        prepared: foreign_helper,
                    },
                ],
            )
            .is_none()
        );
    }

    #[test]
    fn import_like_name_cannot_promote_an_abi_incoherent_scope() {
        let root = Arc::new(
            SsaArtifact::for_symbolic(
                &[R2ILBlock {
                    addr: 0x1000,
                    size: 1,
                    ops: vec![R2ILOp::Return {
                        target: const_vn(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&test_arch()),
            )
            .expect("root"),
        );
        let helper = Arc::new(
            SsaArtifact::for_symbolic(
                &[R2ILBlock {
                    addr: 0x2000,
                    size: 1,
                    ops: vec![R2ILOp::Return {
                        target: const_vn(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&test_arch()),
            )
            .expect("helper"),
        );
        let scope = PreparedFunctionScope::new(
            0x1000,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root,
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("malloc".to_string()),
                    prepared: helper,
                },
            ],
        )
        .expect("scope");
        assert!(
            build_source_owned_interproc_summary_set(&scope).is_err(),
            "manual import-like helpers must not become source-owned summaries"
        );
    }

    #[test]
    fn derived_summary_guidance_adjusts_arg_widths_before_substitution() {
        let ctx = z3::Context::thread_local();
        let mut state = SymState::new(&ctx, 0);
        state.set_register(
            "RDI_0",
            SymValue::symbolic(BV::fresh_const("call_arg", 64), 64),
        );

        let helper_arg = SymValue::symbolic(BV::fresh_const("helper_arg", 32), 32);
        let summary = DerivedFunctionSummary {
            id: InterprocFunctionId(0x401000),
            name: Some("sym.helper_symbolic_zero".to_string()),
            arg_count_hint: 1,
            arg_symbols: vec![(0, helper_arg.clone())],
            memory_inputs: Vec::new(),
            cases: vec![DerivedSummaryCase {
                guard: helper_arg.to_bv(&ctx).eq(helper_arg.to_bv(&ctx)),
                return_value: Some(SymValue::concrete(0, 32)),
                memory_writes: Vec::new(),
            }],
            completion: DerivedSummaryCompletion::Exact,
        };

        let guidance = evaluate_derived_summary_guidance(
            &state,
            &summary,
            &CallConv::x86_64_sysv(),
            &SymSolver::new(&ctx),
        );

        assert!(guidance.summary_known);
        assert_eq!(guidance.feasible_cases, 1);
        assert!(!guidance.contradictory);
    }
}
