//! Interprocedural semantic summaries built on top of prepared SSA.
//!
//! This layer stays summary-based on purpose. It reuses the canonical
//! intraprocedural facts in [`PreparedFunctionSSA`] and solves a deterministic
//! fixpoint over direct-call reachable functions without introducing a second
//! whole-program SSA graph.

use std::collections::{BTreeMap, BTreeSet};

use r2il::ArchSpec;
use serde::{Deserialize, Serialize};

use crate::function::{DefLocation, PreparedFunctionSSA, SSAFunction};
use crate::op::SSAOp;
use crate::semantic::ObjectKind;
use crate::{CallSiteId, SSAVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InterprocFunctionId(pub u64);

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryArgEffect {
    pub read: bool,
    pub write: bool,
    pub escape: bool,
    pub free: bool,
}

impl SummaryArgEffect {
    fn merge_from(&mut self, other: &Self) -> bool {
        let before = self.clone();
        self.read |= other.read;
        self.write |= other.write;
        self.escape |= other.escape;
        self.free |= other.free;
        *self != before
    }

    fn mark_read(&mut self) {
        self.read = true;
    }

    fn mark_write(&mut self) {
        self.write = true;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SummaryReturnRelation {
    Unknown,
    Void,
    Arg(usize),
    Const(u64),
    HeapAlloc,
    Global(u64),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSemanticSummary {
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    #[serde(default)]
    pub arg_count_hint: Option<usize>,
    pub direct_callees: BTreeSet<u64>,
    pub callsite_count: usize,
    pub has_unknown_calls: bool,
    pub arg_effects: BTreeMap<usize, SummaryArgEffect>,
    pub return_relation: SummaryReturnRelation,
    pub reads_global_memory: bool,
    pub writes_global_memory: bool,
    pub touches_unknown_memory: bool,
}

impl FunctionSemanticSummary {
    pub fn unknown(id: InterprocFunctionId, name: Option<String>) -> Self {
        Self {
            id,
            name,
            arg_count_hint: None,
            direct_callees: BTreeSet::new(),
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            return_relation: SummaryReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        }
    }

    pub fn seed_for_name(id: InterprocFunctionId, name: &str) -> Option<Self> {
        let normalized = normalize_seed_name(name)?;
        let mut arg_effects = BTreeMap::new();
        let mut effect = |idx: usize, read: bool, write: bool, escape: bool, free: bool| {
            arg_effects.insert(
                idx,
                SummaryArgEffect {
                    read,
                    write,
                    escape,
                    free,
                },
            );
        };

        let return_relation = match normalized {
            "malloc" => SummaryReturnRelation::HeapAlloc,
            "free" => {
                effect(0, false, false, true, true);
                SummaryReturnRelation::Void
            }
            "memcpy" => {
                effect(0, false, true, true, false);
                effect(1, true, false, false, false);
                SummaryReturnRelation::Arg(0)
            }
            "memset" => {
                effect(0, false, true, true, false);
                SummaryReturnRelation::Arg(0)
            }
            "strlen" => {
                effect(0, true, false, false, false);
                SummaryReturnRelation::Unknown
            }
            "strcmp" | "memcmp" => {
                effect(0, true, false, false, false);
                effect(1, true, false, false, false);
                SummaryReturnRelation::Unknown
            }
            "puts" | "printf" => {
                effect(0, true, false, false, false);
                SummaryReturnRelation::Unknown
            }
            "exit" => SummaryReturnRelation::Void,
            _ => return None,
        };

        Some(Self {
            id,
            name: Some(normalized.to_string()),
            arg_count_hint: Some(match normalized {
                "malloc" | "free" | "strlen" | "puts" | "printf" | "exit" => 1,
                "strcmp" | "memcmp" => 2,
                "memcpy" | "memset" => 3,
                _ => 0,
            }),
            direct_callees: BTreeSet::new(),
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects,
            return_relation,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        })
    }

    pub fn seed_or_unknown(id: InterprocFunctionId, name: &str) -> Self {
        Self::seed_for_name(id, name).unwrap_or_else(|| Self::unknown(id, Some(name.to_string())))
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterprocSummaryDiagnostics {
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_size: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterprocSummarySet {
    pub root: Option<InterprocFunctionId>,
    pub summaries: BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
    pub diagnostics: InterprocSummaryDiagnostics,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterprocSolveConfig {
    pub max_iterations: usize,
}

impl Default for InterprocSolveConfig {
    fn default() -> Self {
        Self { max_iterations: 8 }
    }
}

#[derive(Debug, Clone)]
pub struct InterprocFunctionInput<'a> {
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    pub prepared: &'a PreparedFunctionSSA,
}

#[derive(Debug, Clone)]
struct AbiSlot {
    primary: String,
    size: u32,
}

#[derive(Debug, Clone, Default)]
pub struct AbiProfile {
    args: Vec<AbiSlot>,
    ret_aliases: BTreeSet<String>,
    alias_to_arg: BTreeMap<String, usize>,
    alias_is_ret: BTreeSet<String>,
}

impl AbiProfile {
    pub fn from_arch(arch: Option<&ArchSpec>) -> Self {
        let Some(arch) = arch else {
            return Self::default();
        };
        let lower = arch.name.to_ascii_lowercase();
        match lower.as_str() {
            "x86-64" | "x86_64" | "x64" | "amd64" => Self::new(
                vec![
                    ("rdi", 8, &["edi", "di", "dil"][..]),
                    ("rsi", 8, &["esi", "si", "sil"][..]),
                    ("rdx", 8, &["edx", "dx", "dl"][..]),
                    ("rcx", 8, &["ecx", "cx", "cl"][..]),
                    ("r8", 8, &["r8d", "r8w", "r8b"][..]),
                    ("r9", 8, &["r9d", "r9w", "r9b"][..]),
                ],
                &[("rax", &["eax", "ax", "al"][..])],
            ),
            "x86" | "x86-32" | "i386" | "i686" => {
                Self::new(Vec::new(), &[("eax", &["ax", "al"][..])])
            }
            "arm" if arch.addr_size == 4 => Self::new(
                vec![
                    ("r0", 4, &[]),
                    ("r1", 4, &[]),
                    ("r2", 4, &[]),
                    ("r3", 4, &[]),
                ],
                &[("r0", &[])],
            ),
            "aarch64" | "arm64" => Self::new(
                vec![
                    ("x0", 8, &["w0"][..]),
                    ("x1", 8, &["w1"][..]),
                    ("x2", 8, &["w2"][..]),
                    ("x3", 8, &["w3"][..]),
                    ("x4", 8, &["w4"][..]),
                    ("x5", 8, &["w5"][..]),
                    ("x6", 8, &["w6"][..]),
                    ("x7", 8, &["w7"][..]),
                ],
                &[("x0", &["w0"][..])],
            ),
            "riscv32" | "riscv" if arch.addr_size == 4 => Self::new(
                vec![
                    ("a0", 4, &["x10"][..]),
                    ("a1", 4, &["x11"][..]),
                    ("a2", 4, &["x12"][..]),
                    ("a3", 4, &["x13"][..]),
                    ("a4", 4, &["x14"][..]),
                    ("a5", 4, &["x15"][..]),
                    ("a6", 4, &["x16"][..]),
                    ("a7", 4, &["x17"][..]),
                ],
                &[("a0", &["x10"][..])],
            ),
            "riscv64" | "riscv" => Self::new(
                vec![
                    ("a0", 8, &["x10"][..]),
                    ("a1", 8, &["x11"][..]),
                    ("a2", 8, &["x12"][..]),
                    ("a3", 8, &["x13"][..]),
                    ("a4", 8, &["x14"][..]),
                    ("a5", 8, &["x15"][..]),
                    ("a6", 8, &["x16"][..]),
                    ("a7", 8, &["x17"][..]),
                ],
                &[("a0", &["x10"][..])],
            ),
            _ => Self::default(),
        }
    }

    fn new(
        args: Vec<(&'static str, u32, &'static [&'static str])>,
        rets: &[(&'static str, &'static [&'static str])],
    ) -> Self {
        let mut out = Self::default();
        for (idx, (primary, size, aliases)) in args.into_iter().enumerate() {
            out.args.push(AbiSlot {
                primary: primary.to_string(),
                size,
            });
            out.alias_to_arg.insert(primary.to_string(), idx);
            for alias in aliases {
                out.alias_to_arg.insert((*alias).to_string(), idx);
            }
        }
        for (primary, aliases) in rets {
            out.ret_aliases.insert((*primary).to_string());
            out.alias_is_ret.insert((*primary).to_string());
            for alias in *aliases {
                out.ret_aliases.insert((*alias).to_string());
                out.alias_is_ret.insert((*alias).to_string());
            }
        }
        out
    }

    fn arg_index_for_name(&self, name: &str) -> Option<usize> {
        self.alias_to_arg.get(&name.to_ascii_lowercase()).copied()
    }

    fn is_ret_name(&self, name: &str) -> bool {
        self.alias_is_ret.contains(&name.to_ascii_lowercase())
    }

    fn default_arg_var(&self, idx: usize) -> Option<SSAVar> {
        let slot = self.args.get(idx)?;
        Some(SSAVar::initial(&slot.primary, slot.size))
    }

    fn arg_len(&self) -> usize {
        self.args.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SummaryOperand {
    Arg(usize),
    Const(u64),
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SummaryValueObservation {
    Arg(usize),
    Const(u64),
    Global(u64),
    Call(CallObservation),
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CallObservation {
    target: u64,
    args: Vec<SummaryOperand>,
}

#[derive(Debug, Clone)]
struct LocalSummaryFacts {
    arg_count_hint: Option<usize>,
    direct_callees: BTreeSet<u64>,
    callsite_count: usize,
    has_unknown_calls: bool,
    arg_effects: BTreeMap<usize, SummaryArgEffect>,
    reads_global_memory: bool,
    writes_global_memory: bool,
    touches_unknown_memory: bool,
    return_observations: Vec<SummaryValueObservation>,
    call_observations: BTreeMap<CallSiteId, CallObservation>,
}

pub fn solve_interproc_summary_set(
    functions: &[InterprocFunctionInput<'_>],
    arch: Option<&ArchSpec>,
    root: Option<InterprocFunctionId>,
    seed_summaries: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
    config: InterprocSolveConfig,
) -> InterprocSummarySet {
    let abi = AbiProfile::from_arch(arch);
    let mut locals = BTreeMap::new();
    let mut current = seed_summaries.clone();

    for function in functions {
        let local = collect_local_summary_facts(function.prepared, &abi);
        current
            .entry(function.id)
            .or_insert_with(|| initial_summary(function.id, function.name.clone(), &local));
        locals.insert(function.id, (function.name.clone(), local));
    }

    let max_iterations = config.max_iterations.max(1);
    let mut iterations = 0usize;
    let mut converged = false;

    while iterations < max_iterations {
        iterations += 1;
        let mut changed = false;

        for function in functions {
            let Some((name, local)) = locals.get(&function.id) else {
                continue;
            };
            let next = resolve_summary(function.id, name.clone(), local, &current);
            if current.get(&function.id) != Some(&next) {
                current.insert(function.id, next);
                changed = true;
            }
        }

        if !changed {
            converged = true;
            break;
        }
    }

    InterprocSummarySet {
        root,
        summaries: current,
        diagnostics: InterprocSummaryDiagnostics {
            iterations,
            max_iterations,
            converged,
            scope_size: functions.len(),
        },
    }
}

fn initial_summary(
    id: InterprocFunctionId,
    name: Option<String>,
    local: &LocalSummaryFacts,
) -> FunctionSemanticSummary {
    FunctionSemanticSummary {
        id,
        name,
        arg_count_hint: local.arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls: local.has_unknown_calls,
        arg_effects: local.arg_effects.clone(),
        return_relation: resolve_return_relation(&local.return_observations, &BTreeMap::new()),
        reads_global_memory: local.reads_global_memory,
        writes_global_memory: local.writes_global_memory,
        touches_unknown_memory: local.touches_unknown_memory,
    }
}

fn resolve_summary(
    id: InterprocFunctionId,
    name: Option<String>,
    local: &LocalSummaryFacts,
    current: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> FunctionSemanticSummary {
    let mut arg_effects = local.arg_effects.clone();
    for call in local.call_observations.values() {
        let Some(callee) = current.get(&InterprocFunctionId(call.target)) else {
            continue;
        };
        for (idx, effect) in &callee.arg_effects {
            let Some(actual) = call.args.get(*idx) else {
                continue;
            };
            let SummaryOperand::Arg(caller_idx) = actual else {
                continue;
            };
            arg_effects
                .entry(*caller_idx)
                .or_default()
                .merge_from(effect);
        }
    }

    FunctionSemanticSummary {
        id,
        name,
        arg_count_hint: local.arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls: local.has_unknown_calls,
        arg_effects,
        return_relation: resolve_return_relation(&local.return_observations, current),
        reads_global_memory: local.reads_global_memory,
        writes_global_memory: local.writes_global_memory,
        touches_unknown_memory: local.touches_unknown_memory,
    }
}

fn resolve_return_relation(
    observations: &[SummaryValueObservation],
    current: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> SummaryReturnRelation {
    let mut relation: Option<SummaryReturnRelation> = None;
    for observation in observations {
        let next = match observation {
            SummaryValueObservation::Arg(idx) => SummaryReturnRelation::Arg(*idx),
            SummaryValueObservation::Const(value) => SummaryReturnRelation::Const(*value),
            SummaryValueObservation::Global(address) => SummaryReturnRelation::Global(*address),
            SummaryValueObservation::Unknown => SummaryReturnRelation::Unknown,
            SummaryValueObservation::Call(call) => {
                let Some(callee) = current.get(&InterprocFunctionId(call.target)) else {
                    return SummaryReturnRelation::Unknown;
                };
                match &callee.return_relation {
                    SummaryReturnRelation::Arg(idx) => match call.args.get(*idx) {
                        Some(SummaryOperand::Arg(arg_idx)) => SummaryReturnRelation::Arg(*arg_idx),
                        Some(SummaryOperand::Const(value)) => SummaryReturnRelation::Const(*value),
                        _ => SummaryReturnRelation::Unknown,
                    },
                    SummaryReturnRelation::Const(value) => SummaryReturnRelation::Const(*value),
                    SummaryReturnRelation::HeapAlloc => SummaryReturnRelation::HeapAlloc,
                    SummaryReturnRelation::Global(address) => {
                        SummaryReturnRelation::Global(*address)
                    }
                    SummaryReturnRelation::Void => SummaryReturnRelation::Void,
                    SummaryReturnRelation::Unknown => SummaryReturnRelation::Unknown,
                }
            }
        };

        match &relation {
            None => relation = Some(next),
            Some(current) if *current == next => {}
            _ => return SummaryReturnRelation::Unknown,
        }
    }

    relation.unwrap_or(SummaryReturnRelation::Void)
}

fn collect_local_summary_facts(
    prepared: &PreparedFunctionSSA,
    abi: &AbiProfile,
) -> LocalSummaryFacts {
    let function = prepared.function();
    let state_by_call = collect_call_arg_state(prepared, abi);
    let mut out = LocalSummaryFacts {
        arg_count_hint: Some(0),
        direct_callees: BTreeSet::new(),
        callsite_count: prepared.call_sites().by_id.len(),
        has_unknown_calls: false,
        arg_effects: BTreeMap::new(),
        reads_global_memory: false,
        writes_global_memory: false,
        touches_unknown_memory: false,
        return_observations: Vec::new(),
        call_observations: BTreeMap::new(),
    };

    for (call_id, call) in &prepared.call_sites().by_id {
        match call.direct_target {
            Some(target) => {
                out.direct_callees.insert(target);
                let args = state_by_call
                    .get(call_id)
                    .cloned()
                    .unwrap_or_else(|| (0..abi.arg_len()).map(SummaryOperand::Arg).collect());
                out.call_observations
                    .insert(*call_id, CallObservation { target, args });
            }
            None => out.has_unknown_calls = true,
        }
    }

    for uses in prepared.memory().uses_by_op.values() {
        for fact in uses {
            match prepared
                .objects()
                .object(fact.location.object)
                .map(|object| &object.kind)
            {
                Some(ObjectKind::Global { .. }) => out.reads_global_memory = true,
                Some(ObjectKind::EscapedUnknown) | None => out.touches_unknown_memory = true,
                _ => {}
            }
        }
    }
    for defs in prepared.memory().defs_by_op.values() {
        for fact in defs {
            match prepared
                .objects()
                .object(fact.location.object)
                .map(|object| &object.kind)
            {
                Some(ObjectKind::Global { .. }) => out.writes_global_memory = true,
                Some(ObjectKind::EscapedUnknown) | None => out.touches_unknown_memory = true,
                _ => {}
            }
        }
    }

    for block in function.blocks() {
        for phi in &block.phis {
            for (_, src) in &phi.sources {
                record_arg_count_hint(prepared, function, abi, src, &mut out.arg_count_hint);
            }
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            for src in op.sources() {
                record_arg_count_hint(prepared, function, abi, src, &mut out.arg_count_hint);
            }
            match op {
                SSAOp::Load { addr, .. }
                | SSAOp::LoadLinked { addr, .. }
                | SSAOp::LoadGuarded { addr, .. }
                | SSAOp::AtomicCAS { addr, .. } => {
                    if let SummaryOperand::Arg(idx) =
                        classify_addr_operand(prepared, function, abi, addr, 0)
                    {
                        out.arg_effects.entry(idx).or_default().mark_read();
                    }
                }
                SSAOp::Store { addr, .. }
                | SSAOp::StoreConditional { addr, .. }
                | SSAOp::StoreGuarded { addr, .. } => {
                    if let SummaryOperand::Arg(idx) =
                        classify_addr_operand(prepared, function, abi, addr, 0)
                    {
                        out.arg_effects.entry(idx).or_default().mark_write();
                    }
                }
                SSAOp::Return { target } => {
                    out.return_observations.push(classify_return_target(
                        prepared,
                        function,
                        abi,
                        block.addr,
                        op_idx,
                        target,
                        &out.call_observations,
                    ));
                }
                _ => {}
            }
        }
    }

    out
}

fn record_arg_count_hint(
    prepared: &PreparedFunctionSSA,
    function: &SSAFunction,
    abi: &AbiProfile,
    var: &SSAVar,
    hint: &mut Option<usize>,
) {
    let SummaryOperand::Arg(idx) = classify_value_operand(prepared, function, abi, var, 0) else {
        return;
    };
    let count = idx.saturating_add(1);
    match hint {
        Some(current) => *current = (*current).max(count),
        None => *hint = Some(count),
    }
}

fn collect_call_arg_state(
    prepared: &PreparedFunctionSSA,
    abi: &AbiProfile,
) -> BTreeMap<CallSiteId, Vec<SummaryOperand>> {
    let function = prepared.function();
    let mut in_states = BTreeMap::<u64, BTreeMap<usize, SSAVar>>::new();
    let mut out_states = BTreeMap::<u64, BTreeMap<usize, SSAVar>>::new();
    let mut changed = true;
    let mut iterations = 0usize;
    while changed && iterations < 64 {
        iterations += 1;
        changed = false;
        for &block_addr in function.block_addrs() {
            let preds = function.predecessors(block_addr);
            let mut state = if preds.is_empty() {
                BTreeMap::new()
            } else {
                merge_pred_states(&out_states, &preds)
            };
            let Some(block) = function.get_block(block_addr) else {
                continue;
            };
            for phi in &block.phis {
                if let Some(idx) = abi.arg_index_for_name(&phi.dst.name) {
                    state.insert(idx, phi.dst.clone());
                }
            }
            let old = in_states.insert(block_addr, state.clone());
            if old.as_ref() != Some(&state) {
                changed = true;
            }

            for op in &block.ops {
                if let Some(dst) = op.dst()
                    && let Some(idx) = abi.arg_index_for_name(&dst.name)
                {
                    state.insert(idx, dst.clone());
                }
            }
            let new_state = state;
            let old = out_states.insert(block_addr, new_state.clone());
            if old.as_ref() != Some(&new_state) {
                changed = true;
            }
        }
    }

    let mut by_call = BTreeMap::new();
    for (&call_id, call) in &function_call_site_map(function) {
        let Some(block) = function.get_block(call.0) else {
            continue;
        };
        let mut state = in_states.get(&call.0).cloned().unwrap_or_default();
        for phi in &block.phis {
            if let Some(idx) = abi.arg_index_for_name(&phi.dst.name) {
                state.insert(idx, phi.dst.clone());
            }
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            if op_idx == call.1 {
                let args = (0..abi.arg_len())
                    .map(|idx| {
                        state
                            .get(&idx)
                            .cloned()
                            .or_else(|| abi.default_arg_var(idx))
                            .map(|var| classify_value_operand(prepared, function, abi, &var, 0))
                            .unwrap_or(SummaryOperand::Unknown)
                    })
                    .collect::<Vec<_>>();
                by_call.insert(call_id, args);
                break;
            }
            if let Some(dst) = op.dst()
                && let Some(idx) = abi.arg_index_for_name(&dst.name)
            {
                state.insert(idx, dst.clone());
            }
        }
    }

    by_call
}

fn function_call_site_map(function: &SSAFunction) -> BTreeMap<CallSiteId, (u64, usize)> {
    let mut out = BTreeMap::new();
    let mut next_id = 0u32;
    for &block_addr in function.block_addrs() {
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        for (op_idx, op) in block.ops.iter().enumerate() {
            if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                out.insert(CallSiteId(next_id), (block_addr, op_idx));
                next_id = next_id.saturating_add(1);
            }
        }
    }
    out
}

fn merge_pred_states(
    in_states: &BTreeMap<u64, BTreeMap<usize, SSAVar>>,
    preds: &[u64],
) -> BTreeMap<usize, SSAVar> {
    let mut out = BTreeMap::new();
    let mut keys = BTreeSet::new();
    for pred in preds {
        if let Some(state) = in_states.get(pred) {
            keys.extend(state.keys().copied());
        }
    }
    for key in keys {
        let mut value: Option<&SSAVar> = None;
        let mut same = true;
        for pred in preds {
            let cur = in_states.get(pred).and_then(|state| state.get(&key));
            match (value, cur) {
                (None, Some(cur)) => value = Some(cur),
                (Some(existing), Some(cur)) if existing == cur => {}
                _ => {
                    same = false;
                    break;
                }
            }
        }
        if same && let Some(value) = value {
            out.insert(key, value.clone());
        }
    }
    out
}

fn classify_return_target(
    prepared: &PreparedFunctionSSA,
    function: &SSAFunction,
    abi: &AbiProfile,
    block_addr: u64,
    return_op_idx: usize,
    target: &SSAVar,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> SummaryValueObservation {
    let rooted = canonical_root(prepared, target);
    if is_instruction_pointer_like(&rooted.name)
        && let Some(observation) = recover_return_observation_from_epilogue(
            prepared,
            function,
            abi,
            block_addr,
            return_op_idx,
            calls,
        )
    {
        return observation;
    }
    match classify_value_operand(prepared, function, abi, &rooted, 0) {
        SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
        SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
        SummaryOperand::Unknown => {
            if let Some(call_id) = return_call_site_for_var(function, abi, &rooted)
                && let Some(call) = calls.get(&call_id)
            {
                return SummaryValueObservation::Call(call.clone());
            }
            if let Some(address) = global_address_for_value(prepared, &rooted) {
                return SummaryValueObservation::Global(address);
            }
            SummaryValueObservation::Unknown
        }
    }
}

fn is_instruction_pointer_like(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "rip" | "eip" | "ip" | "pc"
    )
}

fn recover_return_observation_from_epilogue(
    prepared: &PreparedFunctionSSA,
    function: &SSAFunction,
    abi: &AbiProfile,
    block_addr: u64,
    return_op_idx: usize,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> Option<SummaryValueObservation> {
    let block = function.get_block(block_addr)?;
    for scan_idx in (0..return_op_idx).rev() {
        let op = block.ops.get(scan_idx)?;
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                let call_site_map = function_call_site_map(function);
                let call_id = call_site_map
                    .into_iter()
                    .find_map(|(id, site)| (site == (block_addr, scan_idx)).then_some(id))?;
                return calls
                    .get(&call_id)
                    .cloned()
                    .map(SummaryValueObservation::Call);
            }
            _ => {
                let Some(dst) = op.dst() else {
                    continue;
                };
                if !abi.is_ret_name(&dst.name) {
                    continue;
                }
                let rooted = canonical_root(prepared, dst);
                return Some(
                    match classify_value_operand(prepared, function, abi, &rooted, 0) {
                        SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
                        SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
                        SummaryOperand::Unknown => {
                            if let Some(call_id) = return_call_site_for_var(function, abi, &rooted)
                                && let Some(call) = calls.get(&call_id)
                            {
                                SummaryValueObservation::Call(call.clone())
                            } else if let Some(address) =
                                global_address_for_value(prepared, &rooted)
                            {
                                SummaryValueObservation::Global(address)
                            } else {
                                SummaryValueObservation::Unknown
                            }
                        }
                    },
                );
            }
        }
    }
    None
}

fn return_call_site_for_var(
    function: &SSAFunction,
    abi: &AbiProfile,
    var: &SSAVar,
) -> Option<CallSiteId> {
    fn single_call_site(function: &SSAFunction) -> Option<CallSiteId> {
        let call_map = function_call_site_map(function);
        (call_map.len() == 1)
            .then(|| call_map.keys().next().copied())
            .flatten()
    }

    if !abi.is_ret_name(&var.name) {
        return None;
    }
    let Some((def_block_addr, def_site)) = function.find_def(var) else {
        return single_call_site(function);
    };
    let DefLocation::Op(op_idx) = def_site else {
        return single_call_site(function);
    };
    let block = function.get_block(def_block_addr)?;
    let mut call_idx = op_idx;
    loop {
        let op = block.ops.get(call_idx)?;
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => break,
            SSAOp::CallDefine { .. } if call_idx > 0 => {
                call_idx -= 1;
            }
            _ => return single_call_site(function),
        }
    }
    let mut next_id = 0u32;
    for &block_addr in function.block_addrs() {
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        for (idx, op) in block.ops.iter().enumerate() {
            if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                let id = CallSiteId(next_id);
                if block_addr == def_block_addr && idx == call_idx {
                    return Some(id);
                }
                next_id = next_id.saturating_add(1);
            }
        }
    }
    single_call_site(function)
}

fn classify_addr_operand(
    prepared: &PreparedFunctionSSA,
    function: &SSAFunction,
    abi: &AbiProfile,
    var: &SSAVar,
    depth: u32,
) -> SummaryOperand {
    classify_value_operand(prepared, function, abi, var, depth)
}

fn classify_value_operand(
    prepared: &PreparedFunctionSSA,
    function: &SSAFunction,
    abi: &AbiProfile,
    var: &SSAVar,
    depth: u32,
) -> SummaryOperand {
    if depth > 8 {
        return SummaryOperand::Unknown;
    }
    let rooted = canonical_root(prepared, var);
    if rooted.is_const() {
        return parse_const(&rooted).map_or(SummaryOperand::Unknown, SummaryOperand::Const);
    }
    if let Some(idx) = abi.arg_index_for_name(&rooted.name) {
        return SummaryOperand::Arg(idx);
    }

    let Some((def_block_addr, def_site)) = function.find_def(&rooted) else {
        return SummaryOperand::Unknown;
    };
    let DefLocation::Op(op_idx) = def_site else {
        return SummaryOperand::Unknown;
    };
    let Some(block) = function.get_block(def_block_addr) else {
        return SummaryOperand::Unknown;
    };
    let Some(op) = block.ops.get(op_idx) else {
        return SummaryOperand::Unknown;
    };
    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            classify_value_operand(prepared, function, abi, src, depth + 1)
        }
        SSAOp::IntAdd { a, b, .. }
        | SSAOp::IntSub { a, b, .. }
        | SSAOp::PtrAdd {
            base: a, index: b, ..
        }
        | SSAOp::PtrSub {
            base: a, index: b, ..
        } => {
            let left = classify_value_operand(prepared, function, abi, a, depth + 1);
            let right = classify_value_operand(prepared, function, abi, b, depth + 1);
            match (left, right) {
                (SummaryOperand::Arg(idx), SummaryOperand::Const(_))
                | (SummaryOperand::Const(_), SummaryOperand::Arg(idx)) => SummaryOperand::Arg(idx),
                (SummaryOperand::Arg(idx), SummaryOperand::Unknown) => SummaryOperand::Arg(idx),
                (SummaryOperand::Unknown, SummaryOperand::Arg(idx)) => SummaryOperand::Arg(idx),
                _ => SummaryOperand::Unknown,
            }
        }
        _ => SummaryOperand::Unknown,
    }
}

fn canonical_root(prepared: &PreparedFunctionSSA, var: &SSAVar) -> SSAVar {
    let Some(facts) = prepared.function().decompile_prep_facts() else {
        return var.clone();
    };
    let mut current = var.clone();
    for _ in 0..32 {
        let Some(next) = facts.canonical_root_of(&current) else {
            break;
        };
        if next == &current {
            break;
        }
        current = next.clone();
    }
    current
}

fn global_address_for_value(prepared: &PreparedFunctionSSA, var: &SSAVar) -> Option<u64> {
    let object = prepared.objects().object_for_value(var)?;
    let object = prepared.objects().object(object)?;
    match object.kind {
        ObjectKind::Global { address, .. } => Some(address),
        _ => None,
    }
}

fn parse_const(var: &SSAVar) -> Option<u64> {
    var.name
        .strip_prefix("const:")
        .and_then(|value| u64::from_str_radix(value.trim_start_matches("0x"), 16).ok())
}

fn normalize_seed_name(name: &str) -> Option<&'static str> {
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
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PreparedFunctionSSA;
    use r2il::{R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn x86_64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch
    }

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn tmp(name: u64, size: u32) -> Varnode {
        Varnode::unique(name, size)
    }

    fn c(value: u64, size: u32) -> Varnode {
        Varnode::constant(value, size)
    }

    fn block(addr: u64, ops: Vec<R2ILOp>) -> R2ILBlock {
        R2ILBlock {
            addr,
            size: 4,
            ops,
            switch_info: None,
            op_metadata: Default::default(),
        }
    }

    #[test]
    fn seed_summary_models_malloc_and_memcpy() {
        let malloc =
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(1), "sym.imp.malloc")
                .expect("malloc seed");
        assert_eq!(malloc.return_relation, SummaryReturnRelation::HeapAlloc);
        let memcpy = FunctionSemanticSummary::seed_for_name(InterprocFunctionId(2), "memcpy")
            .expect("memcpy seed");
        assert_eq!(memcpy.return_relation, SummaryReturnRelation::Arg(0));
        assert!(memcpy.arg_effects.get(&0).expect("dst").write);
        assert!(memcpy.arg_effects.get(&1).expect("src").read);
    }

    #[test]
    fn solve_summary_set_propagates_heap_alloc_and_returned_arg() {
        let arch = x86_64_arch();
        let alloc_block = block(
            0x1000,
            vec![
                R2ILOp::Call {
                    target: c(0x2000, 8),
                },
                R2ILOp::Return { target: reg(0, 8) },
            ],
        );
        let wrapper_block = block(
            0x3000,
            vec![
                R2ILOp::Call {
                    target: c(0x1000, 8),
                },
                R2ILOp::Return { target: reg(0, 8) },
            ],
        );

        let alloc = PreparedFunctionSSA::for_decompile(&[alloc_block], Some(&arch))
            .expect("alloc ssa")
            .with_name("alloc_wrapper");
        let wrapper = PreparedFunctionSSA::for_decompile(&[wrapper_block], Some(&arch))
            .expect("wrapper ssa")
            .with_name("wrapper");

        let mut seeds = BTreeMap::new();
        seeds.insert(
            InterprocFunctionId(0x2000),
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(0x2000), "malloc")
                .expect("malloc"),
        );

        let set = solve_interproc_summary_set(
            &[
                InterprocFunctionInput {
                    id: InterprocFunctionId(0x1000),
                    name: Some("alloc_wrapper".to_string()),
                    prepared: &alloc,
                },
                InterprocFunctionInput {
                    id: InterprocFunctionId(0x3000),
                    name: Some("wrapper".to_string()),
                    prepared: &wrapper,
                },
            ],
            Some(&arch),
            Some(InterprocFunctionId(0x3000)),
            &seeds,
            InterprocSolveConfig::default(),
        );

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x1000))
                .expect("alloc summary")
                .return_relation,
            SummaryReturnRelation::HeapAlloc
        );
        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x3000))
                .expect("wrapper summary")
                .return_relation,
            SummaryReturnRelation::HeapAlloc
        );
    }

    #[test]
    fn solve_summary_set_recovers_wrapper_return_through_ip_return_op() {
        let arch = x86_64_arch();
        let alloc_block = block(
            0x1000,
            vec![
                R2ILOp::Call {
                    target: c(0x2000, 8),
                },
                R2ILOp::Return { target: reg(16, 8) },
            ],
        );

        let alloc = PreparedFunctionSSA::for_decompile(&[alloc_block], Some(&arch))
            .expect("alloc ssa")
            .with_name("alloc_wrapper");

        let mut seeds = BTreeMap::new();
        seeds.insert(
            InterprocFunctionId(0x2000),
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(0x2000), "malloc")
                .expect("malloc"),
        );

        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x1000),
                name: Some("alloc_wrapper".to_string()),
                prepared: &alloc,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x1000)),
            &seeds,
            InterprocSolveConfig::default(),
        );

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x1000))
                .expect("alloc summary")
                .return_relation,
            SummaryReturnRelation::HeapAlloc
        );
    }

    #[test]
    fn direct_pointer_load_marks_argument_read() {
        let arch = x86_64_arch();
        let blk = block(
            0x4000,
            vec![
                R2ILOp::Load {
                    dst: tmp(1, 4),
                    space: SpaceId::Ram,
                    addr: reg(8, 8),
                },
                R2ILOp::Return { target: c(0, 4) },
            ],
        );
        let prepared = PreparedFunctionSSA::for_decompile(&[blk], Some(&arch)).expect("ssa");
        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: Some("read_arg".to_string()),
                prepared: &prepared,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x4000)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        );
        assert!(
            set.summaries
                .get(&InterprocFunctionId(0x4000))
                .and_then(|summary| summary.arg_effects.get(&0))
                .is_some_and(|effect| effect.read)
        );
    }
}
