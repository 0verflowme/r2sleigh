//! Function summaries for common library calls.
//!
//! These summaries short-circuit into lightweight models to avoid
//! path explosion from libc implementations.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use r2il::{AddressSpace, ArchSpec, Endianness, RegisterDef};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, MachineArchitectureFamily, MachineMemoryEndianness,
    SsaArtifact,
};
use z3::ast::BV;

use crate::executor::{CallHookResult, SymExecutor};
use crate::path::PathExplorer;
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

#[derive(Clone, Debug, PartialEq, Eq)]
enum CallConvRegisters {
    /// Compatibility surface for callers that have architecture advice only.
    AdvisoryNames {
        argument_names: Vec<String>,
        result_name: String,
    },
    /// Exact ABI identity retained from one prepared artifact.
    SourceOwned {
        argument_storages: Vec<CanonicalStorageId>,
        result_storage: Option<CanonicalStorageId>,
        register_storages_by_name: BTreeMap<String, CanonicalStorageId>,
    },
}

/// Calling convention description for retrieving arguments and return values.
#[derive(Clone, Debug)]
pub struct CallConv {
    registers: CallConvRegisters,
    arg_bits: u32,
    ret_bits: u32,
}

impl CallConv {
    /// Create a legacy/advisory calling convention from presentation names.
    ///
    /// Exact prepared workflows must use [`Self::for_prepared`] so register
    /// spellings never become ABI identity.
    pub fn new(
        arg_registers: Vec<&'static str>,
        ret_register: &'static str,
        arg_bits: u32,
        ret_bits: u32,
    ) -> Self {
        Self {
            registers: CallConvRegisters::AdvisoryNames {
                argument_names: arg_registers.into_iter().map(str::to_string).collect(),
                result_name: ret_register.to_string(),
            },
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

    /// Legacy/advisory architecture-derived calling convention.
    ///
    /// This constructor intentionally remains name-based for callers without a
    /// prepared artifact. It must not be used to reconstruct exact source ABI
    /// identity.
    pub fn for_arch_spec(arch: &ArchSpec) -> Option<Self> {
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

    /// Retain the exact source-owned ABI storages from one prepared artifact.
    pub(crate) fn for_prepared(prepared: &SsaArtifact) -> Option<Self> {
        let context = prepared.machine_context();
        if context.effective_abi_class() == r2ssa::SourceAbiClass::Unknown {
            return None;
        }
        let abi = context.abi_model();
        if !abi.is_available() || !abi.is_coherent() {
            return None;
        }

        let argument_storages = abi
            .argument_registers()
            .iter()
            .enumerate()
            .map(|(index, slot)| (slot.index() as usize == index).then_some(slot.storage()))
            .collect::<Option<Vec<_>>>()?;
        let result_storage = match abi.return_registers() {
            [] => None,
            [result_slot] => Some(result_slot.storage()),
            _ => return None,
        };
        if argument_storages
            .iter()
            .chain(result_storage.iter())
            .any(|storage| {
                storage.space != CanonicalStorageSpace::Register
                    || storage.size == 0
                    || storage.size.checked_mul(8).is_none()
            })
        {
            return None;
        }

        let memory = context.memory_model();
        if !memory.is_available() || !memory.is_coherent() {
            return None;
        }
        let address_bits = memory.default_address_bits();
        let arg_bits = match argument_storages.first() {
            Some(storage) => storage.size.checked_mul(8)?,
            None => address_bits,
        };
        if arg_bits == 0
            || argument_storages
                .iter()
                .any(|storage| storage.size.checked_mul(8) != Some(arg_bits))
        {
            return None;
        }
        let ret_bits = result_storage
            .map(|storage| storage.size.checked_mul(8))
            .unwrap_or(Some(address_bits))?;

        Some(Self {
            registers: CallConvRegisters::SourceOwned {
                argument_storages,
                result_storage,
                register_storages_by_name: context.register_storages_by_name().clone(),
            },
            arg_bits,
            ret_bits,
        })
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
            args.push(
                self.read_argument(state, i)
                    .unwrap_or_else(|| SymValue::unknown(self.arg_bits)),
            );
        }
        CallInfo {
            args,
            arg_bits: self.arg_bits,
            ret_bits: self.ret_bits,
        }
    }

    fn read_named_register<'ctx>(&self, state: &SymState<'ctx>, base: &str) -> SymValue<'ctx> {
        for alias in register_aliases(base) {
            if let Some(key) = find_register_key(state, alias) {
                return state.get_register_sized(&key, self.arg_bits);
            }
        }
        SymValue::unknown(self.arg_bits)
    }

    pub(crate) fn read_argument<'ctx>(
        &self,
        state: &SymState<'ctx>,
        index: usize,
    ) -> Option<SymValue<'ctx>> {
        match &self.registers {
            CallConvRegisters::AdvisoryNames { argument_names, .. } => argument_names
                .get(index)
                .map(|name| self.read_named_register(state, name)),
            CallConvRegisters::SourceOwned {
                argument_storages,
                register_storages_by_name,
                ..
            } => argument_storages.get(index).map(|storage| {
                source_state_key(state, register_storages_by_name, *storage)
                    .map(|key| state.get_register_sized(&key, self.arg_bits))
                    .unwrap_or_else(|| SymValue::unknown(self.arg_bits))
            }),
        }
    }

    pub(crate) fn write_return<'ctx>(&self, state: &mut SymState<'ctx>, value: SymValue<'ctx>) {
        let keys = match &self.registers {
            CallConvRegisters::AdvisoryNames { result_name, .. } => {
                let mut keys = BTreeSet::new();
                for alias in register_aliases(result_name) {
                    if let Some(key) = find_register_key(state, alias) {
                        keys.insert(key);
                    }
                }
                if keys.is_empty() {
                    keys.insert(format!("{result_name}_0"));
                }
                keys
            }
            CallConvRegisters::SourceOwned {
                result_storage,
                register_storages_by_name,
                ..
            } => {
                let Some(result_storage) = *result_storage else {
                    return;
                };
                let mut keys = source_state_keys(state, register_storages_by_name, result_storage);
                if keys.is_empty()
                    && let Some(name) =
                        source_presentation_name(register_storages_by_name, result_storage)
                {
                    keys.insert(format!("{}_0", name.to_ascii_uppercase()));
                }
                keys
            }
        };
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

    pub(crate) fn arg_capacity(&self) -> usize {
        match &self.registers {
            CallConvRegisters::AdvisoryNames { argument_names, .. } => argument_names.len(),
            CallConvRegisters::SourceOwned {
                argument_storages, ..
            } => argument_storages.len(),
        }
    }

    pub(crate) fn argument_storage(&self, index: usize) -> Option<CanonicalStorageId> {
        match &self.registers {
            CallConvRegisters::AdvisoryNames { .. } => None,
            CallConvRegisters::SourceOwned {
                argument_storages, ..
            } => argument_storages.get(index).copied(),
        }
    }
}

fn source_presentation_name(
    register_storages_by_name: &BTreeMap<String, CanonicalStorageId>,
    storage: CanonicalStorageId,
) -> Option<&str> {
    register_storages_by_name
        .iter()
        .filter(|(_, candidate)| **candidate == storage)
        .map(|(name, _)| name)
        .min()
        .map(String::as_str)
}

fn source_state_keys<'ctx>(
    state: &SymState<'ctx>,
    register_storages_by_name: &BTreeMap<String, CanonicalStorageId>,
    storage: CanonicalStorageId,
) -> BTreeSet<String> {
    register_storages_by_name
        .iter()
        .filter(|(_, candidate)| **candidate == storage)
        .filter_map(|(name, _)| find_register_key(state, name))
        .collect()
}

fn source_state_key<'ctx>(
    state: &SymState<'ctx>,
    register_storages_by_name: &BTreeMap<String, CanonicalStorageId>,
    storage: CanonicalStorageId,
) -> Option<String> {
    source_state_keys(state, register_storages_by_name, storage)
        .into_iter()
        .max_by(|left, right| {
            let left_version = split_version(left).map(|(_, version)| version).unwrap_or(0);
            let right_version = split_version(right)
                .map(|(_, version)| version)
                .unwrap_or(0);
            left_version
                .cmp(&right_version)
                .then_with(|| left.cmp(right))
        })
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
    Some(arch)
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SummaryInstallStats {
    pub attempted: usize,
    pub installed: usize,
    pub skipped_unknown: usize,
    pub duplicates: usize,
}

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

    fn exact_callconv_artifact() -> SsaArtifact {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        for (name, offset, size) in [
            ("RDI", 0x00, 8),
            ("EDI", 0x00, 4),
            ("RAX", 0x08, 8),
            ("EAX", 0x08, 4),
            ("RSP", 0x10, 8),
            ("RIP", 0x18, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        let storage = |offset, size| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2sym-exact-callconv-owner".to_vec(),
            "exact-test-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, storage(0x00, 8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0x08, 8),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x10, 8)))
        .and_then(|interface| interface.with_return_address_storage(storage(0x18, 8)))
        .expect("exact callconv interface");
        SsaArtifact::for_decompile_with_interface(
            &[R2ILBlock {
                addr: 0x401000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: const_vn(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&arch),
            interface,
        )
        .expect("exact callconv artifact")
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
    fn prepared_callconv_retains_storage_identity_without_arch_variant_encoding() {
        let prepared = exact_callconv_artifact();
        let argument = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x00,
            size: 8,
        };
        let projected = source_arch_spec(&prepared).expect("source presentation profile");
        let callconv = CallConv::for_prepared(&prepared).expect("exact source-owned callconv");

        assert_eq!(projected.variant, "default");
        assert_eq!(callconv.argument_storage(0), Some(argument));
    }

    #[test]
    fn prepared_callconv_projects_state_keys_only_after_storage_selection() {
        let prepared = exact_callconv_artifact();
        let callconv = CallConv::for_prepared(&prepared).expect("exact source-owned callconv");
        let ctx = z3::Context::thread_local();
        let mut state = SymState::new(&ctx, prepared.entry);

        state.set_register("EDI_7", SymValue::concrete(0x11, 32));
        state.set_register("EAX_9", SymValue::concrete(0x22, 32));
        assert!(callconv.collect_call_info(&state, 1).args[0].is_unknown());

        state.set_register("RDI_3", SymValue::concrete(0x33, 64));
        state.set_register("RAX_4", SymValue::concrete(0x44, 64));
        assert_eq!(
            callconv.collect_call_info(&state, 1).args[0].as_concrete(),
            Some(0x33)
        );
        callconv.write_return(&mut state, SymValue::concrete(0x55, 64));
        assert_eq!(
            state
                .registers()
                .get("RAX_4")
                .and_then(SymValue::as_concrete),
            Some(0x55)
        );
        assert_eq!(
            state
                .registers()
                .get("EAX_9")
                .and_then(SymValue::as_concrete),
            Some(0x22)
        );
    }

    #[test]
    fn source_owned_callconv_keeps_storage_when_no_presentation_alias_exists() {
        let argument = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x20,
            size: 8,
        };
        let callconv = CallConv {
            registers: CallConvRegisters::SourceOwned {
                argument_storages: vec![argument],
                result_storage: Some(CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset: 0x28,
                    size: 8,
                }),
                register_storages_by_name: BTreeMap::new(),
            },
            arg_bits: 64,
            ret_bits: 64,
        };
        let ctx = z3::Context::thread_local();
        let mut state = SymState::new(&ctx, 0x401000);

        assert_eq!(callconv.argument_storage(0), Some(argument));
        assert!(callconv.collect_call_info(&state, 1).args[0].is_unknown());

        callconv.write_return(&mut state, SymValue::concrete(7, 64));
        assert!(state.registers().is_empty());
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

        assert_eq!(with_import.registers, without_import.registers);
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
}
