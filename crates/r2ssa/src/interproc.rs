//! Interprocedural semantic summaries built on top of prepared SSA.
//!
//! This layer stays summary-based on purpose. It reuses the canonical
//! intraprocedural facts in [`SsaArtifact`] and solves a deterministic
//! fixpoint over direct-call reachable functions without introducing a second
//! whole-program SSA graph.

use std::collections::{BTreeMap, BTreeSet};

use r2il::ArchSpec;
use serde::{Deserialize, Serialize};

use crate::function::{SSAFunction, SsaArtifact};
use crate::graph::{InstPayload, ValueId};
use crate::op::SSAOp;
use crate::semantic::ObjectKind;
use crate::{CallSiteId, SSAVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InterprocFunctionId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummaryMemoryEffectKind {
    Read,
    Write,
    Escape,
    Free,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummaryMemoryRegion {
    Arg { index: usize },
    Global { address: u64 },
    HeapReturn,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryMemoryRange {
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub width: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryMemoryLocation {
    pub region: SummaryMemoryRegion,
    pub range: Option<SummaryMemoryRange>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryMemoryEffect {
    pub kind: SummaryMemoryEffectKind,
    pub location: SummaryMemoryLocation,
}

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
    #[serde(default)]
    pub memory_effects: Vec<SummaryMemoryEffect>,
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
            memory_effects: Vec::new(),
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
            memory_effects: Vec::new(),
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
    pub scc_count: usize,
    pub max_scc_size: usize,
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
    pub prepared: &'a SsaArtifact,
}

#[derive(Debug, Clone)]
struct AbiSlot {
    _primary: String,
    _size: u32,
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
                _primary: primary.to_string(),
                _size: size,
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
    memory_effects: BTreeSet<SummaryMemoryEffect>,
    return_observations: Vec<SummaryValueObservation>,
    call_observations: BTreeMap<CallSiteId, CallObservation>,
}

fn exact_range(offset: i64, size: u32) -> Option<SummaryMemoryRange> {
    if size == 0 {
        return None;
    }
    Some(SummaryMemoryRange {
        offset_lo: offset,
        offset_hi: offset.saturating_add(size as i64).saturating_sub(1),
        width: Some(size),
    })
}

fn arg_location(index: usize, offset: Option<i64>, width: Option<u32>) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Arg { index },
        range: match (offset, width) {
            (Some(offset), Some(width)) => exact_range(offset, width),
            _ => None,
        },
    }
}

fn global_location(address: u64, offset: Option<i64>, width: Option<u32>) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Global { address },
        range: match (offset, width) {
            (Some(offset), Some(width)) => exact_range(offset, width),
            _ => None,
        },
    }
}

fn unknown_location() -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Unknown,
        range: None,
    }
}

fn shifted_range(
    range: Option<SummaryMemoryRange>,
    delta: i64,
    width: u32,
) -> Option<SummaryMemoryRange> {
    match range {
        Some(range) => Some(SummaryMemoryRange {
            offset_lo: range.offset_lo.saturating_add(delta),
            offset_hi: range.offset_hi.saturating_add(delta),
            width: range.width.or(Some(width)),
        }),
        None => exact_range(delta, width),
    }
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

    let sccs = compute_summary_sccs(&locals);
    let max_iterations = config.max_iterations.max(1);
    let mut iterations = 0usize;
    let mut converged = true;
    let mut max_scc_size = 0usize;

    for scc in &sccs {
        max_scc_size = max_scc_size.max(scc.len());
        let mut scc_converged = false;
        for _ in 0..max_iterations {
            iterations += 1;
            let mut changed = false;
            for function_id in scc {
                let Some((name, local)) = locals.get(function_id) else {
                    continue;
                };
                let next = resolve_summary(*function_id, name.clone(), local, &current);
                if current.get(function_id) != Some(&next) {
                    current.insert(*function_id, next);
                    changed = true;
                }
            }
            if !changed {
                scc_converged = true;
                break;
            }
        }
        converged &= scc_converged;
    }

    InterprocSummarySet {
        root,
        summaries: current,
        diagnostics: InterprocSummaryDiagnostics {
            iterations,
            max_iterations,
            converged,
            scope_size: functions.len(),
            scc_count: sccs.len(),
            max_scc_size,
        },
    }
}

fn compute_summary_sccs(
    locals: &BTreeMap<InterprocFunctionId, (Option<String>, LocalSummaryFacts)>,
) -> Vec<Vec<InterprocFunctionId>> {
    let node_ids: Vec<InterprocFunctionId> = locals.keys().copied().collect();
    let node_set: BTreeSet<InterprocFunctionId> = node_ids.iter().copied().collect();
    let mut succs = BTreeMap::<InterprocFunctionId, Vec<InterprocFunctionId>>::new();
    let mut rev = BTreeMap::<InterprocFunctionId, Vec<InterprocFunctionId>>::new();

    for node in &node_ids {
        succs.entry(*node).or_default();
        rev.entry(*node).or_default();
    }
    for (node, (_, local)) in locals {
        let mut out = local
            .direct_callees
            .iter()
            .map(|target| InterprocFunctionId(*target))
            .filter(|target| node_set.contains(target))
            .collect::<Vec<_>>();
        out.sort_unstable();
        out.dedup();
        succs.insert(*node, out.clone());
        for succ in out {
            rev.entry(succ).or_default().push(*node);
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

    // Edges point caller -> callee, but summary propagation wants callee SCCs
    // solved before dependent caller SCCs when the graph is acyclic.
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
    if let Some(children) = succs.get(&node) {
        for succ in children {
            dfs_summary_postorder(*succ, succs, visited, order);
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

fn initial_summary(
    id: InterprocFunctionId,
    name: Option<String>,
    local: &LocalSummaryFacts,
) -> FunctionSemanticSummary {
    let (reads_global_memory, writes_global_memory, touches_unknown_memory) =
        summarize_memory_effect_flags(&local.memory_effects);
    FunctionSemanticSummary {
        id,
        name,
        arg_count_hint: local.arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls: local.has_unknown_calls,
        arg_effects: local.arg_effects.clone(),
        memory_effects: local.memory_effects.iter().copied().collect(),
        return_relation: resolve_return_relation(&local.return_observations, &BTreeMap::new()),
        reads_global_memory,
        writes_global_memory,
        touches_unknown_memory,
    }
}

fn resolve_summary(
    id: InterprocFunctionId,
    name: Option<String>,
    local: &LocalSummaryFacts,
    current: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> FunctionSemanticSummary {
    let mut arg_effects = local.arg_effects.clone();
    let mut memory_effects = local.memory_effects.clone();
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
        for effect in &callee.memory_effects {
            memory_effects.insert(remap_memory_effect(effect, &call.args));
        }
    }
    let (reads_global_memory, writes_global_memory, touches_unknown_memory) =
        summarize_memory_effect_flags(&memory_effects);

    FunctionSemanticSummary {
        id,
        name,
        arg_count_hint: local.arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls: local.has_unknown_calls,
        arg_effects,
        memory_effects: memory_effects.iter().copied().collect(),
        return_relation: resolve_return_relation(&local.return_observations, current),
        reads_global_memory,
        writes_global_memory,
        touches_unknown_memory,
    }
}

fn summarize_memory_effect_flags(effects: &BTreeSet<SummaryMemoryEffect>) -> (bool, bool, bool) {
    let mut reads_global_memory = false;
    let mut writes_global_memory = false;
    let mut touches_unknown_memory = false;
    for effect in effects {
        match (effect.kind, effect.location.region) {
            (SummaryMemoryEffectKind::Read, SummaryMemoryRegion::Global { .. }) => {
                reads_global_memory = true
            }
            (
                SummaryMemoryEffectKind::Write
                | SummaryMemoryEffectKind::Escape
                | SummaryMemoryEffectKind::Free,
                SummaryMemoryRegion::Global { .. },
            ) => writes_global_memory = true,
            (_, SummaryMemoryRegion::Unknown) => touches_unknown_memory = true,
            _ => {}
        }
    }
    (
        reads_global_memory,
        writes_global_memory,
        touches_unknown_memory,
    )
}

fn remap_memory_effect(
    effect: &SummaryMemoryEffect,
    args: &[SummaryOperand],
) -> SummaryMemoryEffect {
    let location = match effect.location.region {
        SummaryMemoryRegion::Arg { index } => match args.get(index) {
            Some(SummaryOperand::Arg(caller_idx)) => SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: *caller_idx },
                range: effect.location.range,
            },
            Some(SummaryOperand::Const(value)) => SummaryMemoryLocation {
                region: SummaryMemoryRegion::Global { address: *value },
                range: effect.location.range,
            },
            _ => SummaryMemoryLocation {
                region: SummaryMemoryRegion::Unknown,
                range: None,
            },
        },
        other => SummaryMemoryLocation {
            region: other,
            range: effect.location.range,
        },
    };
    SummaryMemoryEffect {
        kind: effect.kind,
        location,
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

fn collect_local_summary_facts(prepared: &SsaArtifact, abi: &AbiProfile) -> LocalSummaryFacts {
    let function = prepared.function();
    let state_by_call = collect_call_arg_state(prepared, abi);
    let mut out = LocalSummaryFacts {
        arg_count_hint: Some(0),
        direct_callees: BTreeSet::new(),
        callsite_count: prepared.call_sites().by_id.len(),
        has_unknown_calls: false,
        arg_effects: BTreeMap::new(),
        memory_effects: BTreeSet::new(),
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
            None => {
                out.has_unknown_calls = true;
                if let Some(args) = state_by_call.get(call_id) {
                    for actual in args {
                        if let SummaryOperand::Arg(idx) = actual {
                            let effect = out.arg_effects.entry(*idx).or_default();
                            effect.mark_read();
                            effect.mark_write();
                            effect.escape = true;
                            out.memory_effects.insert(SummaryMemoryEffect {
                                kind: SummaryMemoryEffectKind::Read,
                                location: arg_location(*idx, None, None),
                            });
                            out.memory_effects.insert(SummaryMemoryEffect {
                                kind: SummaryMemoryEffectKind::Write,
                                location: arg_location(*idx, None, None),
                            });
                            out.memory_effects.insert(SummaryMemoryEffect {
                                kind: SummaryMemoryEffectKind::Escape,
                                location: arg_location(*idx, None, None),
                            });
                        }
                    }
                }
                out.memory_effects.insert(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: unknown_location(),
                });
                out.memory_effects.insert(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Write,
                    location: unknown_location(),
                });
            }
        }
    }

    for block in function.blocks() {
        for phi in &block.phis {
            for (_, src) in &phi.sources {
                record_arg_count_hint(prepared, abi, src, &mut out.arg_count_hint);
            }
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            for src in op.sources() {
                record_arg_count_hint(prepared, abi, src, &mut out.arg_count_hint);
            }
            match op {
                SSAOp::Load { addr, dst, .. }
                | SSAOp::LoadLinked { addr, dst, .. }
                | SSAOp::LoadGuarded { addr, dst, .. } => {
                    let operand = prepared
                        .graph()
                        .value_id_for_var(addr)
                        .map(|value_id| classify_value_operand(prepared, abi, value_id, 0))
                        .unwrap_or_else(|| classify_var_operand(prepared, abi, addr, 0));
                    if let SummaryOperand::Arg(idx) = operand {
                        out.arg_effects.entry(idx).or_default().mark_read();
                        out.memory_effects.insert(SummaryMemoryEffect {
                            kind: SummaryMemoryEffectKind::Read,
                            location: arg_location(idx, None, None),
                        });
                    }
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location: classify_memory_access_location(prepared, abi, addr, dst.size),
                    });
                }
                SSAOp::AtomicCAS { addr, expected, .. } => {
                    let operand = prepared
                        .graph()
                        .value_id_for_var(addr)
                        .map(|value_id| classify_value_operand(prepared, abi, value_id, 0))
                        .unwrap_or_else(|| classify_var_operand(prepared, abi, addr, 0));
                    if let SummaryOperand::Arg(idx) = operand {
                        out.arg_effects.entry(idx).or_default().mark_read();
                        out.memory_effects.insert(SummaryMemoryEffect {
                            kind: SummaryMemoryEffectKind::Read,
                            location: arg_location(idx, None, None),
                        });
                    }
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location: classify_memory_access_location(
                            prepared,
                            abi,
                            addr,
                            expected.size,
                        ),
                    });
                }
                SSAOp::Store { addr, val, .. }
                | SSAOp::StoreConditional { addr, val, .. }
                | SSAOp::StoreGuarded { addr, val, .. } => {
                    let operand = prepared
                        .graph()
                        .value_id_for_var(addr)
                        .map(|value_id| classify_value_operand(prepared, abi, value_id, 0))
                        .unwrap_or_else(|| classify_var_operand(prepared, abi, addr, 0));
                    if let SummaryOperand::Arg(idx) = operand {
                        out.arg_effects.entry(idx).or_default().mark_write();
                        out.memory_effects.insert(SummaryMemoryEffect {
                            kind: SummaryMemoryEffectKind::Write,
                            location: arg_location(idx, None, None),
                        });
                    }
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Write,
                        location: classify_memory_access_location(prepared, abi, addr, val.size),
                    });
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

fn classify_memory_access_location(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    addr: &SSAVar,
    width: u32,
) -> SummaryMemoryLocation {
    let Some(value_id) = prepared.graph().value_id_for_var(addr) else {
        return unknown_location();
    };
    classify_memory_access_location_value(prepared, abi, value_id, width, 0)
}

fn classify_memory_access_location_value(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
    width: u32,
    depth: u32,
) -> SummaryMemoryLocation {
    if depth > 8 {
        return unknown_location();
    }

    let rooted = canonical_root_value(prepared, value_id);
    if let Some(var) = prepared.value_var(rooted) {
        if let Some(idx) = abi.arg_index_for_name(&var.name) {
            return arg_location(idx, Some(0), Some(width));
        }
        if let Some(address) = parse_const_name(&var.name) {
            return global_location(address, Some(0), Some(width));
        }
    }

    if let Some(object_id) = prepared.objects().object_for_value(rooted)
        && let Some(object) = prepared.objects().object(object_id)
    {
        match object.kind {
            ObjectKind::Global { address, .. } => {
                return global_location(address, Some(0), Some(width));
            }
            ObjectKind::HeapAlloc { .. } => {
                return SummaryMemoryLocation {
                    region: SummaryMemoryRegion::HeapReturn,
                    range: exact_range(0, width),
                };
            }
            ObjectKind::EscapedUnknown => return unknown_location(),
            _ => {}
        }
    }

    let Some(def_inst) = prepared.graph().def_inst(rooted) else {
        return unknown_location();
    };
    let Some(inst) = prepared.graph().inst(def_inst) else {
        return unknown_location();
    };
    let InstPayload::Op(op) = &inst.payload else {
        return unknown_location();
    };

    match op {
        SSAOp::Copy { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::IntSExt { .. }
        | SSAOp::Subpiece { .. } => inst
            .inputs
            .first()
            .copied()
            .map(|src| classify_memory_access_location_value(prepared, abi, src, width, depth + 1))
            .unwrap_or_else(unknown_location),
        SSAOp::IntAdd { .. } | SSAOp::PtrAdd { .. } => {
            let Some(&left_id) = inst.inputs.first() else {
                return unknown_location();
            };
            let Some(&right_id) = inst.inputs.get(1) else {
                return unknown_location();
            };
            classify_memory_additive_location(
                prepared,
                abi,
                left_id,
                right_id,
                AdditiveLocationCtx::new(width, depth + 1, 1, op),
            )
        }
        SSAOp::IntSub { .. } | SSAOp::PtrSub { .. } => {
            let Some(&left_id) = inst.inputs.first() else {
                return unknown_location();
            };
            let Some(&right_id) = inst.inputs.get(1) else {
                return unknown_location();
            };
            classify_memory_additive_location(
                prepared,
                abi,
                left_id,
                right_id,
                AdditiveLocationCtx::new(width, depth + 1, -1, op),
            )
        }
        _ => unknown_location(),
    }
}

#[derive(Clone, Copy)]
struct AdditiveLocationCtx {
    width: u32,
    depth: u32,
    sign: i64,
    element_scale: i64,
}

impl AdditiveLocationCtx {
    fn new(width: u32, depth: u32, sign: i64, op: &SSAOp) -> Self {
        let element_scale = match op {
            SSAOp::PtrAdd { element_size, .. } | SSAOp::PtrSub { element_size, .. } => {
                *element_size as i64
            }
            _ => 1,
        };
        Self {
            width,
            depth,
            sign,
            element_scale,
        }
    }
}

fn classify_memory_additive_location(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    left_id: ValueId,
    right_id: ValueId,
    ctx: AdditiveLocationCtx,
) -> SummaryMemoryLocation {
    let left_const = prepared
        .value_var(canonical_root_value(prepared, left_id))
        .and_then(|var| parse_const_name(&var.name));
    let right_const = prepared
        .value_var(canonical_root_value(prepared, right_id))
        .and_then(|var| parse_const_name(&var.name));

    if let Some(k) = right_const {
        let mut base =
            classify_memory_access_location_value(prepared, abi, left_id, ctx.width, ctx.depth);
        let delta = (k as i64)
            .saturating_mul(ctx.element_scale)
            .saturating_mul(ctx.sign);
        base.range = shifted_range(base.range, delta, ctx.width);
        return base;
    }
    if ctx.sign > 0
        && let Some(k) = left_const
    {
        let mut base =
            classify_memory_access_location_value(prepared, abi, right_id, ctx.width, ctx.depth);
        let delta = (k as i64).saturating_mul(ctx.element_scale);
        base.range = shifted_range(base.range, delta, ctx.width);
        return base;
    }
    unknown_location()
}

fn record_arg_count_hint(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    var: &SSAVar,
    hint: &mut Option<usize>,
) {
    if let Some(value_id) = prepared.graph().value_id_for_var(var) {
        record_arg_count_hint_value(prepared, abi, value_id, hint);
        return;
    }
    if let SummaryOperand::Arg(idx) = classify_var_operand(prepared, abi, var, 0) {
        let count = idx.saturating_add(1);
        match hint {
            Some(current) => *current = (*current).max(count),
            None => *hint = Some(count),
        }
    }
}

fn record_arg_count_hint_value(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
    hint: &mut Option<usize>,
) {
    if let SummaryOperand::Arg(idx) = classify_value_operand(prepared, abi, value_id, 0) {
        let count = idx.saturating_add(1);
        match hint {
            Some(current) => *current = (*current).max(count),
            None => *hint = Some(count),
        }
    }
}

fn collect_call_arg_state(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
) -> BTreeMap<CallSiteId, Vec<SummaryOperand>> {
    let function = prepared.function();
    let graph = prepared.graph();
    let mut in_states = BTreeMap::<u64, BTreeMap<usize, ValueId>>::new();
    let mut out_states = BTreeMap::<u64, BTreeMap<usize, ValueId>>::new();
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
                if let Some(idx) = abi.arg_index_for_name(&phi.dst.name)
                    && let Some(value_id) = graph.value_id_for_var(&phi.dst)
                {
                    state.insert(idx, value_id);
                }
            }
            let old = in_states.insert(block_addr, state.clone());
            if old.as_ref() != Some(&state) {
                changed = true;
            }

            for op in &block.ops {
                if let Some(dst) = op.dst()
                    && let Some(idx) = abi.arg_index_for_name(&dst.name)
                    && let Some(value_id) = graph.value_id_for_var(dst)
                {
                    state.insert(idx, value_id);
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
    for (&call_id, call) in &prepared.call_sites().by_id {
        let Some((block_addr, call_op_idx)) = prepared.inst_op_site(call.at) else {
            continue;
        };
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let mut state = in_states.get(&block_addr).cloned().unwrap_or_default();
        for phi in &block.phis {
            if let Some(idx) = abi.arg_index_for_name(&phi.dst.name)
                && let Some(value_id) = graph.value_id_for_var(&phi.dst)
            {
                state.insert(idx, value_id);
            }
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            if op_idx == call_op_idx {
                let args = (0..abi.arg_len())
                    .map(|idx| {
                        state
                            .get(&idx)
                            .cloned()
                            .map(|value_id| classify_value_operand(prepared, abi, value_id, 0))
                            .unwrap_or(SummaryOperand::Arg(idx))
                    })
                    .collect::<Vec<_>>();
                by_call.insert(call_id, args);
                break;
            }
            if let Some(dst) = op.dst()
                && let Some(idx) = abi.arg_index_for_name(&dst.name)
                && let Some(value_id) = graph.value_id_for_var(dst)
            {
                state.insert(idx, value_id);
            }
        }
    }

    by_call
}

fn merge_pred_states(
    in_states: &BTreeMap<u64, BTreeMap<usize, ValueId>>,
    preds: &[u64],
) -> BTreeMap<usize, ValueId> {
    let mut out = BTreeMap::new();
    let mut keys = BTreeSet::new();
    for pred in preds {
        if let Some(state) = in_states.get(pred) {
            keys.extend(state.keys().copied());
        }
    }
    for key in keys {
        let mut value: Option<ValueId> = None;
        let mut same = true;
        for pred in preds {
            let cur = in_states
                .get(pred)
                .and_then(|state| state.get(&key))
                .copied();
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
            out.insert(key, value);
        }
    }
    out
}

fn classify_return_target(
    prepared: &SsaArtifact,
    function: &SSAFunction,
    abi: &AbiProfile,
    block_addr: u64,
    return_op_idx: usize,
    target: &SSAVar,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> SummaryValueObservation {
    if let Some(target_id) = prepared.graph().value_id_for_var(target) {
        let rooted_id = canonical_root_value(prepared, target_id);
        if prepared
            .value_var(rooted_id)
            .is_some_and(|rooted| is_instruction_pointer_like(&rooted.name))
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
        return classify_value_observation(prepared, abi, rooted_id, calls);
    }

    if is_instruction_pointer_like(&target.name)
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
    match classify_var_operand(prepared, abi, target, 0) {
        SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
        SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
        SummaryOperand::Unknown => SummaryValueObservation::Unknown,
    }
}

fn is_instruction_pointer_like(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "rip" | "eip" | "ip" | "pc"
    )
}

fn recover_return_observation_from_epilogue(
    prepared: &SsaArtifact,
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
                let call_id = prepared
                    .graph()
                    .inst_id_for_op_site(block_addr, scan_idx)
                    .and_then(|inst_id| prepared.call_sites().by_inst.get(&inst_id).copied())?;
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
                if let Some(dst_id) = prepared.graph().value_id_for_var(dst) {
                    let rooted_id = canonical_root_value(prepared, dst_id);
                    return Some(classify_value_observation(prepared, abi, rooted_id, calls));
                }
                return Some(match classify_var_operand(prepared, abi, dst, 0) {
                    SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
                    SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
                    SummaryOperand::Unknown => SummaryValueObservation::Unknown,
                });
            }
        }
    }
    None
}

fn classify_value_observation(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> SummaryValueObservation {
    match classify_value_operand(prepared, abi, value_id, 0) {
        SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
        SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
        SummaryOperand::Unknown => {
            if let Some(call_id) = return_call_site_for_value(prepared, abi, value_id)
                && let Some(call) = calls.get(&call_id)
            {
                SummaryValueObservation::Call(call.clone())
            } else if let Some(address) = global_address_for_value_id(prepared, value_id) {
                SummaryValueObservation::Global(address)
            } else {
                SummaryValueObservation::Unknown
            }
        }
    }
}

fn return_call_site_for_value(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
) -> Option<CallSiteId> {
    let single_call_site = || {
        (prepared.call_sites().by_id.len() == 1)
            .then(|| prepared.call_sites().by_id.keys().next().copied())
            .flatten()
    };
    let graph = prepared.graph();
    let var = prepared.value_var(value_id)?;
    if !abi.is_ret_name(&var.name) {
        return None;
    }

    let Some(def_inst) = graph.def_inst(value_id) else {
        return single_call_site();
    };
    let Some(inst) = graph.inst(def_inst) else {
        return single_call_site();
    };
    let Some(block) = graph.blocks.get(inst.block.0 as usize) else {
        return single_call_site();
    };
    let Some(inst_pos) = block.insts.iter().position(|id| *id == def_inst) else {
        return single_call_site();
    };

    for scan_pos in (0..=inst_pos).rev() {
        let scan_inst_id = block.insts[scan_pos];
        let Some(scan_inst) = graph.inst(scan_inst_id) else {
            continue;
        };
        let InstPayload::Op(op) = &scan_inst.payload else {
            continue;
        };
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                return prepared.call_sites().by_inst.get(&scan_inst_id).copied();
            }
            SSAOp::CallDefine { .. } => continue,
            _ => break,
        }
    }

    single_call_site()
}

fn classify_var_operand(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    var: &SSAVar,
    depth: u32,
) -> SummaryOperand {
    if depth > 8 {
        return SummaryOperand::Unknown;
    }
    if var.is_const() {
        return parse_const_name(&var.name).map_or(SummaryOperand::Unknown, SummaryOperand::Const);
    }
    if let Some(idx) = abi.arg_index_for_name(&var.name) {
        return SummaryOperand::Arg(idx);
    }
    let Some(value_id) = prepared.graph().value_id_for_var(var) else {
        return SummaryOperand::Unknown;
    };
    classify_value_operand(prepared, abi, value_id, depth)
}

fn classify_value_operand(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
    depth: u32,
) -> SummaryOperand {
    if depth > 8 {
        return SummaryOperand::Unknown;
    }
    let rooted = canonical_root_value(prepared, value_id);
    let Some(root_var) = prepared.value_var(rooted) else {
        return SummaryOperand::Unknown;
    };
    if root_var.is_const() {
        return parse_const_name(&root_var.name)
            .map_or(SummaryOperand::Unknown, SummaryOperand::Const);
    }
    if let Some(idx) = abi.arg_index_for_name(&root_var.name) {
        return SummaryOperand::Arg(idx);
    }

    let Some(def_inst) = prepared.graph().def_inst(rooted) else {
        return SummaryOperand::Unknown;
    };
    let Some(inst) = prepared.graph().inst(def_inst) else {
        return SummaryOperand::Unknown;
    };
    let InstPayload::Op(op) = &inst.payload else {
        return SummaryOperand::Unknown;
    };
    match op {
        SSAOp::Copy { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::IntSExt { .. }
        | SSAOp::Subpiece { .. } => inst
            .inputs
            .first()
            .copied()
            .map(|src| classify_value_operand(prepared, abi, src, depth + 1))
            .unwrap_or(SummaryOperand::Unknown),
        SSAOp::IntAdd { .. }
        | SSAOp::IntSub { .. }
        | SSAOp::PtrAdd { .. }
        | SSAOp::PtrSub { .. } => {
            let Some(&left_id) = inst.inputs.first() else {
                return SummaryOperand::Unknown;
            };
            let Some(&right_id) = inst.inputs.get(1) else {
                return SummaryOperand::Unknown;
            };
            let left = classify_value_operand(prepared, abi, left_id, depth + 1);
            let right = classify_value_operand(prepared, abi, right_id, depth + 1);
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

fn canonical_root_value(prepared: &SsaArtifact, value_id: ValueId) -> ValueId {
    let Some(facts) = prepared.function().decompile_prep_facts() else {
        return value_id;
    };
    let Some(start) = prepared.value_var(value_id) else {
        return value_id;
    };
    let mut current = start.clone();
    let mut current_id = value_id;
    for _ in 0..32 {
        let Some(next) = facts.canonical_root_of(&current) else {
            break;
        };
        if next == &current {
            break;
        }
        let Some(next_id) = prepared.graph().value_id_for_var(next) else {
            break;
        };
        current = next.clone();
        current_id = next_id;
    }
    current_id
}

fn global_address_for_value_id(prepared: &SsaArtifact, value_id: ValueId) -> Option<u64> {
    let object = prepared.objects().object_for_value(value_id)?;
    let object = prepared.objects().object(object)?;
    match object.kind {
        ObjectKind::Global { address, .. } => Some(address),
        _ => None,
    }
}

fn parse_const_name(name: &str) -> Option<u64> {
    name.strip_prefix("const:")
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
    use crate::SsaArtifact;
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

        let alloc = SsaArtifact::for_decompile(&[alloc_block], Some(&arch))
            .expect("alloc ssa")
            .with_name("alloc_wrapper");
        let wrapper = SsaArtifact::for_decompile(&[wrapper_block], Some(&arch))
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

        let alloc = SsaArtifact::for_decompile(&[alloc_block], Some(&arch))
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
        let prepared = SsaArtifact::for_decompile(&[blk], Some(&arch)).expect("ssa");
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
