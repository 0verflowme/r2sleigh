//! Function summaries for common library calls.
//!
//! These summaries short-circuit into lightweight models to avoid
//! path explosion from libc implementations.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use r2il::ArchSpec;
use r2ssa::PreparedFunctionSSA;
use z3::ast::BV;

use crate::executor::{CallHookResult, SymExecutor};
use crate::path::PathExplorer;
use crate::state::{ExitStatus, SymState};
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
    arg_registers: Vec<&'static str>,
    ret_register: &'static str,
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
            arg_registers,
            ret_register,
            arg_bits,
            ret_bits,
        }
    }

    /// x86-64 System V ABI (RDI, RSI, RDX, RCX, R8, R9; return in RAX).
    pub fn x86_64_sysv() -> Self {
        Self::new(vec!["RDI", "RSI", "RDX", "RCX", "R8", "R9"], "RAX", 64, 64)
    }

    /// Architecture-derived calling convention used by the symbolic runtime.
    pub fn for_arch_spec(arch: &ArchSpec) -> Option<Self> {
        let arch_name = arch.name.to_ascii_lowercase();
        if arch.addr_size == 8 && arch_name.contains("x86") {
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

    fn collect_call_info<'ctx>(&self, state: &SymState<'ctx>, arity: usize) -> CallInfo<'ctx> {
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
        if let Some(key) = find_register_key(state, base) {
            state.get_register_sized(&key, self.arg_bits)
        } else {
            SymValue::unknown(self.arg_bits)
        }
    }

    fn write_return<'ctx>(&self, state: &mut SymState<'ctx>, value: SymValue<'ctx>) {
        let key = find_register_key(state, self.ret_register)
            .unwrap_or_else(|| format!("{}_0", self.ret_register));
        let adjusted = adjust_bits(state.context(), value, self.ret_bits);
        state.set_register(&key, adjusted);
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SummaryInstallStats {
    pub attempted: usize,
    pub installed: usize,
    pub skipped_unknown: usize,
    pub duplicates: usize,
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
        let mut registry = Self::new(callconv);
        registry.register_summary(MemcpySummary::new(DEFAULT_MAX_MEMCPY));
        registry.register_summary(MemsetSummary::new(DEFAULT_MAX_MEMSET));
        registry.register_summary(StrlenSummary::new(DEFAULT_MAX_STRLEN));
        registry.register_summary(StrcmpSummary::new());
        registry.register_summary(MemcmpSummary::new(DEFAULT_MAX_MEMCMP));
        registry.register_summary(MallocSummary::new());
        registry.register_summary(FreeSummary::new());
        registry.register_summary(PutsSummary::new(DEFAULT_MAX_PRINTF_SCAN));
        registry.register_summary(PrintfSummaryBasic::new(DEFAULT_MAX_PRINTF_SCAN));
        registry.register_summary(ExitSummary::new());
        registry
    }

    /// Create a registry pre-populated with core summaries for a known architecture.
    pub fn with_core_for_arch(arch: &ArchSpec) -> Option<Self> {
        Some(Self::with_core(CallConv::for_arch_spec(arch)?))
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
        let Some(summary) = self.summaries.get(name).cloned() else {
            return false;
        };
        let callconv = self.callconv.clone();
        explorer.register_call_hook(addr, move |state| {
            apply_summary(state, &*summary, &callconv)
        });
        true
    }

    /// Install matching core summaries for direct call sites in a prepared function.
    pub fn install_known_symbols_for_function(
        &self,
        explorer: &mut PathExplorer<'ctx>,
        prepared: &PreparedFunctionSSA,
        symbol_map: &HashMap<u64, String>,
    ) -> SummaryInstallStats {
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
            if self.install_for_explorer(explorer, target, summary_name) {
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

    match normalized {
        "strlen" | "__strlen_chk" => Some("strlen"),
        "strcmp" => Some("strcmp"),
        "memcmp" => Some("memcmp"),
        "memcpy" | "__memcpy_chk" => Some("memcpy"),
        "memset" => Some("memset"),
        "malloc" | "__libc_malloc" | "__gi___libc_malloc" => Some("malloc"),
        "free" => Some("free"),
        "puts" => Some("puts"),
        "printf" | "__printf_chk" => Some("printf"),
        "exit" | "_exit" => Some("exit"),
        _ => {
            if normalized.starts_with("strlen") {
                Some("strlen")
            } else if normalized.starts_with("strcmp") {
                Some("strcmp")
            } else if normalized.starts_with("memcmp") {
                Some("memcmp")
            } else if normalized.starts_with("memcpy") {
                Some("memcpy")
            } else if normalized.starts_with("memset") {
                Some("memset")
            } else if normalized.starts_with("printf") || normalized == "__printf_chk" {
                Some("printf")
            } else if normalized.starts_with("puts") {
                Some("puts")
            } else if normalized == "malloc" || normalized.ends_with("malloc") {
                Some("malloc")
            } else if normalized == "free" || normalized.ends_with("free") {
                Some("free")
            } else if normalized.starts_with("exit") {
                Some("exit")
            } else {
                None
            }
        }
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
}

impl MemcpySummary {
    /// Create a memcpy summary with an upper bound on copy size.
    pub fn new(max_copy: u64) -> Self {
        Self { max_copy }
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
        copy_bytes(state, &dst, &src, &n, self.max_copy);
        SummaryEffect::Return(Some(dst))
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
}

impl MemsetSummary {
    /// Create a memset summary with an upper bound on set size.
    pub fn new(max_set: u64) -> Self {
        Self { max_set }
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

        set_bytes(state, &dst, &c, &n, self.max_set);
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
) {
    let ctx = state.context();
    let n_concrete = n.as_concrete();
    let copy_len = n_concrete.unwrap_or(max_copy).min(max_copy);

    if n_concrete.is_none() {
        state.constrain_range(n, 0, max_copy);
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
) {
    let ctx = state.context();
    let n_concrete = n.as_concrete();
    let set_len = n_concrete.unwrap_or(max_set).min(max_set);

    if n_concrete.is_none() {
        state.constrain_range(n, 0, max_set);
    }

    let c_byte = if let Some(concrete) = c.as_concrete() {
        SymValue::concrete_tainted(concrete & 0xff, 8, c.get_taint())
    } else {
        c.extract(ctx, 7, 0).with_taint(c.get_taint())
    };

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
