//! Interprocedural semantic summaries built on top of prepared SSA.
//!
//! This layer stays summary-based on purpose. It reuses the canonical
//! intraprocedural facts in [`SsaArtifact`] and solves a deterministic
//! fixpoint over direct-call reachable functions without introducing a second
//! whole-program SSA graph.

use std::collections::{BTreeMap, BTreeSet};

use r2il::{ArchSpec, MemoryOrdering};
use serde::{Deserialize, Serialize};

use crate::abi::AbiProfile;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummaryTransferLength {
    Arg(usize),
    Const(u64),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryTransferEffect {
    pub dst: SummaryMemoryLocation,
    pub src: SummaryMemoryLocation,
    pub len: SummaryTransferLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryAllocationEffect {
    pub size_arg: Option<usize>,
    pub zeroed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummaryLifetimeOp {
    Free,
    Retain,
    Release,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryLifetimeEffect {
    pub arg: usize,
    pub op: SummaryLifetimeOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummarySyncOp {
    Lock,
    Unlock,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummarySyncEffect {
    pub arg: usize,
    pub op: SummarySyncOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummaryAtomicOp {
    LoadLinked,
    StoreConditional,
    CompareExchange,
    Fence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SummaryAtomicOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryAtomicEffect {
    pub op: SummaryAtomicOp,
    pub location: SummaryMemoryLocation,
    pub ordering: SummaryAtomicOrdering,
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

#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub enum FunctionSemanticLinkage {
    #[default]
    Unknown,
    Internal,
    Imported,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSemanticSummary {
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    #[serde(default)]
    pub linkage: FunctionSemanticLinkage,
    #[serde(default)]
    pub arg_count_hint: Option<usize>,
    pub direct_callees: BTreeSet<u64>,
    pub callsite_count: usize,
    pub has_unknown_calls: bool,
    pub arg_effects: BTreeMap<usize, SummaryArgEffect>,
    #[serde(default)]
    pub memory_effects: Vec<SummaryMemoryEffect>,
    #[serde(default)]
    pub transfer_effects: Vec<SummaryTransferEffect>,
    #[serde(default)]
    pub allocation_effects: Vec<SummaryAllocationEffect>,
    #[serde(default)]
    pub lifetime_effects: Vec<SummaryLifetimeEffect>,
    #[serde(default)]
    pub sync_effects: Vec<SummarySyncEffect>,
    #[serde(default)]
    pub atomic_effects: Vec<SummaryAtomicEffect>,
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
            linkage: FunctionSemanticLinkage::Unknown,
            arg_count_hint: None,
            direct_callees: BTreeSet::new(),
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            memory_effects: Vec::new(),
            transfer_effects: Vec::new(),
            allocation_effects: Vec::new(),
            lifetime_effects: Vec::new(),
            sync_effects: Vec::new(),
            atomic_effects: Vec::new(),
            return_relation: SummaryReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        }
    }

    #[cfg(test)]
    fn seed_for_name(id: InterprocFunctionId, name: &str) -> Option<Self> {
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
        let mut memory_effects = Vec::new();
        let mut transfer_effects = Vec::new();
        let mut allocation_effects = Vec::new();
        let mut lifetime_effects = Vec::new();
        let mut sync_effects = Vec::new();
        let atomic_effects = Vec::new();

        let return_relation = match normalized {
            "malloc" => {
                effect(0, true, false, false, false);
                allocation_effects.push(SummaryAllocationEffect {
                    size_arg: Some(0),
                    zeroed: false,
                });
                SummaryReturnRelation::HeapAlloc
            }
            "calloc" => {
                effect(0, true, false, false, false);
                effect(1, true, false, false, false);
                allocation_effects.push(SummaryAllocationEffect {
                    size_arg: Some(1),
                    zeroed: true,
                });
                SummaryReturnRelation::HeapAlloc
            }
            "free" => {
                effect(0, false, false, true, true);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Free,
                    location: arg_location(0, None, None),
                });
                lifetime_effects.push(SummaryLifetimeEffect {
                    arg: 0,
                    op: SummaryLifetimeOp::Free,
                });
                SummaryReturnRelation::Void
            }
            "memcpy" | "memmove" => {
                effect(0, false, true, true, false);
                effect(1, true, false, false, false);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Write,
                    location: arg_location(0, None, None),
                });
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: arg_location(1, None, None),
                });
                transfer_effects.push(SummaryTransferEffect {
                    dst: arg_location(0, None, None),
                    src: arg_location(1, None, None),
                    len: SummaryTransferLength::Arg(2),
                });
                SummaryReturnRelation::Arg(0)
            }
            "copyin" | "copyout" => {
                effect(0, true, false, false, false);
                effect(1, false, true, true, false);
                effect(2, true, false, false, false);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: arg_location(0, None, None),
                });
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Write,
                    location: arg_location(1, None, None),
                });
                transfer_effects.push(SummaryTransferEffect {
                    dst: arg_location(1, None, None),
                    src: arg_location(0, None, None),
                    len: SummaryTransferLength::Arg(2),
                });
                SummaryReturnRelation::Unknown
            }
            "memset" => {
                effect(0, false, true, true, false);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Write,
                    location: arg_location(0, None, None),
                });
                SummaryReturnRelation::Arg(0)
            }
            "strlen" => {
                effect(0, true, false, false, false);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: arg_location(0, None, None),
                });
                SummaryReturnRelation::Unknown
            }
            "strcmp" | "memcmp" => {
                effect(0, true, false, false, false);
                effect(1, true, false, false, false);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: arg_location(0, None, None),
                });
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: arg_location(1, None, None),
                });
                SummaryReturnRelation::Unknown
            }
            "puts" | "printf" => {
                effect(0, true, false, false, false);
                memory_effects.push(SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: arg_location(0, None, None),
                });
                SummaryReturnRelation::Unknown
            }
            "retain" => {
                effect(0, true, false, true, false);
                lifetime_effects.push(SummaryLifetimeEffect {
                    arg: 0,
                    op: SummaryLifetimeOp::Retain,
                });
                SummaryReturnRelation::Arg(0)
            }
            "release" => {
                effect(0, false, false, true, false);
                lifetime_effects.push(SummaryLifetimeEffect {
                    arg: 0,
                    op: SummaryLifetimeOp::Release,
                });
                SummaryReturnRelation::Void
            }
            "lock" => {
                effect(0, false, false, true, false);
                sync_effects.push(SummarySyncEffect {
                    arg: 0,
                    op: SummarySyncOp::Lock,
                });
                SummaryReturnRelation::Void
            }
            "unlock" => {
                effect(0, false, false, true, false);
                sync_effects.push(SummarySyncEffect {
                    arg: 0,
                    op: SummarySyncOp::Unlock,
                });
                SummaryReturnRelation::Void
            }
            "exit" => SummaryReturnRelation::Void,
            _ => return None,
        };

        Some(Self {
            id,
            name: Some(normalized.to_string()),
            linkage: FunctionSemanticLinkage::Unknown,
            arg_count_hint: Some(match normalized {
                "malloc" | "free" | "strlen" | "puts" | "printf" | "exit" | "retain"
                | "release" | "lock" | "unlock" => 1,
                "calloc" => 2,
                "strcmp" | "memcmp" => 2,
                "memcpy" | "memmove" | "copyin" | "copyout" | "memset" => 3,
                _ => 0,
            }),
            direct_callees: BTreeSet::new(),
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects,
            memory_effects,
            transfer_effects,
            allocation_effects,
            lifetime_effects,
            sync_effects,
            atomic_effects,
            return_relation,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        })
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

fn formal_arg_index_for_var(abi: &AbiProfile, var: &SSAVar) -> Option<usize> {
    abi.formal_argument_index(var)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SummaryOperand {
    Arg(usize),
    Const(u64),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CallArgObservation {
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
    transfer_effects: BTreeSet<SummaryTransferEffect>,
    allocation_effects: BTreeSet<SummaryAllocationEffect>,
    lifetime_effects: BTreeSet<SummaryLifetimeEffect>,
    sync_effects: BTreeSet<SummarySyncEffect>,
    atomic_effects: BTreeSet<SummaryAtomicEffect>,
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

fn summary_atomic_ordering(ordering: MemoryOrdering) -> SummaryAtomicOrdering {
    match ordering {
        MemoryOrdering::Relaxed => SummaryAtomicOrdering::Relaxed,
        MemoryOrdering::Acquire => SummaryAtomicOrdering::Acquire,
        MemoryOrdering::Release => SummaryAtomicOrdering::Release,
        MemoryOrdering::AcqRel => SummaryAtomicOrdering::AcqRel,
        MemoryOrdering::SeqCst => SummaryAtomicOrdering::SeqCst,
        MemoryOrdering::Unknown => SummaryAtomicOrdering::Unknown,
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

fn bump_arg_count_hint(hint: &mut Option<usize>, index: usize) {
    let count = index.saturating_add(1);
    match hint {
        Some(current) => *current = (*current).max(count),
        None => *hint = Some(count),
    }
}

fn bump_arg_count_hint_for_location(hint: &mut Option<usize>, location: SummaryMemoryLocation) {
    if let SummaryMemoryRegion::Arg { index } = location.region {
        bump_arg_count_hint(hint, index);
    }
}

struct SummaryArgCountInputs<'a> {
    base: Option<usize>,
    arg_effects: &'a BTreeMap<usize, SummaryArgEffect>,
    memory_effects: &'a BTreeSet<SummaryMemoryEffect>,
    transfer_effects: &'a BTreeSet<SummaryTransferEffect>,
    allocation_effects: &'a BTreeSet<SummaryAllocationEffect>,
    lifetime_effects: &'a BTreeSet<SummaryLifetimeEffect>,
    sync_effects: &'a BTreeSet<SummarySyncEffect>,
    atomic_effects: &'a BTreeSet<SummaryAtomicEffect>,
    return_relation: &'a SummaryReturnRelation,
}

fn summary_arg_count_hint(inputs: SummaryArgCountInputs<'_>) -> Option<usize> {
    let mut hint = inputs.base;
    for index in inputs.arg_effects.keys().copied() {
        bump_arg_count_hint(&mut hint, index);
    }
    for effect in inputs.memory_effects {
        bump_arg_count_hint_for_location(&mut hint, effect.location);
    }
    for effect in inputs.transfer_effects {
        bump_arg_count_hint_for_location(&mut hint, effect.dst);
        bump_arg_count_hint_for_location(&mut hint, effect.src);
        if let SummaryTransferLength::Arg(index) = effect.len {
            bump_arg_count_hint(&mut hint, index);
        }
    }
    for effect in inputs.allocation_effects {
        if let Some(index) = effect.size_arg {
            bump_arg_count_hint(&mut hint, index);
        }
    }
    for effect in inputs.lifetime_effects {
        bump_arg_count_hint(&mut hint, effect.arg);
    }
    for effect in inputs.sync_effects {
        bump_arg_count_hint(&mut hint, effect.arg);
    }
    for effect in inputs.atomic_effects {
        bump_arg_count_hint_for_location(&mut hint, effect.location);
    }
    if let SummaryReturnRelation::Arg(index) = inputs.return_relation {
        bump_arg_count_hint(&mut hint, *index);
    }
    hint
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
    let mut stack = vec![(node, false)];
    while let Some((node, expanded)) = stack.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        if !visited.insert(node) {
            continue;
        }
        stack.push((node, true));
        if let Some(children) = succs.get(&node) {
            for &succ in children.iter().rev() {
                stack.push((succ, false));
            }
        }
    }
}

fn dfs_summary_component(
    node: InterprocFunctionId,
    rev: &BTreeMap<InterprocFunctionId, Vec<InterprocFunctionId>>,
    visited: &mut BTreeSet<InterprocFunctionId>,
    component: &mut Vec<InterprocFunctionId>,
) {
    let mut stack = vec![node];
    while let Some(node) = stack.pop() {
        if !visited.insert(node) {
            continue;
        }
        component.push(node);
        if let Some(preds) = rev.get(&node) {
            for &pred in preds.iter().rev() {
                stack.push(pred);
            }
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
    let return_relation = resolve_return_relation(&local.return_observations, &BTreeMap::new());
    let arg_count_hint = summary_arg_count_hint(SummaryArgCountInputs {
        base: local.arg_count_hint,
        arg_effects: &local.arg_effects,
        memory_effects: &local.memory_effects,
        transfer_effects: &local.transfer_effects,
        allocation_effects: &local.allocation_effects,
        lifetime_effects: &local.lifetime_effects,
        sync_effects: &local.sync_effects,
        atomic_effects: &local.atomic_effects,
        return_relation: &return_relation,
    });
    FunctionSemanticSummary {
        id,
        name,
        linkage: FunctionSemanticLinkage::Unknown,
        arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls: local.has_unknown_calls,
        arg_effects: local.arg_effects.clone(),
        memory_effects: local.memory_effects.iter().copied().collect(),
        transfer_effects: local.transfer_effects.iter().copied().collect(),
        allocation_effects: local.allocation_effects.iter().copied().collect(),
        lifetime_effects: local.lifetime_effects.iter().copied().collect(),
        sync_effects: local.sync_effects.iter().copied().collect(),
        atomic_effects: local.atomic_effects.iter().copied().collect(),
        return_relation,
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
    let mut transfer_effects = local.transfer_effects.clone();
    let mut allocation_effects = local.allocation_effects.clone();
    let mut lifetime_effects = local.lifetime_effects.clone();
    let mut sync_effects = local.sync_effects.clone();
    let mut atomic_effects = local.atomic_effects.clone();
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
        for effect in &callee.transfer_effects {
            transfer_effects.insert(remap_transfer_effect(effect, &call.args));
        }
        allocation_effects.extend(callee.allocation_effects.iter().copied());
        for effect in &callee.lifetime_effects {
            if let Some(effect) = remap_lifetime_effect(effect, &call.args) {
                lifetime_effects.insert(effect);
            }
        }
        for effect in &callee.sync_effects {
            if let Some(effect) = remap_sync_effect(effect, &call.args) {
                sync_effects.insert(effect);
            }
        }
        for effect in &callee.atomic_effects {
            atomic_effects.insert(remap_atomic_effect(effect, &call.args));
        }
    }
    let (reads_global_memory, writes_global_memory, touches_unknown_memory) =
        summarize_memory_effect_flags(&memory_effects);
    let return_relation = resolve_return_relation_with_wrapper_fallback(local, current);
    let arg_count_hint = summary_arg_count_hint(SummaryArgCountInputs {
        base: local.arg_count_hint,
        arg_effects: &arg_effects,
        memory_effects: &memory_effects,
        transfer_effects: &transfer_effects,
        allocation_effects: &allocation_effects,
        lifetime_effects: &lifetime_effects,
        sync_effects: &sync_effects,
        atomic_effects: &atomic_effects,
        return_relation: &return_relation,
    });

    FunctionSemanticSummary {
        id,
        name,
        linkage: FunctionSemanticLinkage::Unknown,
        arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls: local.has_unknown_calls,
        arg_effects,
        memory_effects: memory_effects.iter().copied().collect(),
        transfer_effects: transfer_effects.iter().copied().collect(),
        allocation_effects: allocation_effects.iter().copied().collect(),
        lifetime_effects: lifetime_effects.iter().copied().collect(),
        sync_effects: sync_effects.iter().copied().collect(),
        atomic_effects: atomic_effects.iter().copied().collect(),
        return_relation,
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
    SummaryMemoryEffect {
        kind: effect.kind,
        location: remap_memory_location(effect.location, args),
    }
}

fn remap_memory_location(
    location: SummaryMemoryLocation,
    args: &[SummaryOperand],
) -> SummaryMemoryLocation {
    match location.region {
        SummaryMemoryRegion::Arg { index } => match args.get(index) {
            Some(SummaryOperand::Arg(caller_idx)) => SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: *caller_idx },
                range: location.range,
            },
            Some(SummaryOperand::Const(value)) => SummaryMemoryLocation {
                region: SummaryMemoryRegion::Global { address: *value },
                range: location.range,
            },
            _ => SummaryMemoryLocation {
                region: SummaryMemoryRegion::Unknown,
                range: None,
            },
        },
        other => SummaryMemoryLocation {
            region: other,
            range: location.range,
        },
    }
}

fn remap_transfer_effect(
    effect: &SummaryTransferEffect,
    args: &[SummaryOperand],
) -> SummaryTransferEffect {
    SummaryTransferEffect {
        dst: remap_memory_location(effect.dst, args),
        src: remap_memory_location(effect.src, args),
        len: remap_transfer_len(effect.len, args),
    }
}

fn remap_transfer_len(
    len: SummaryTransferLength,
    args: &[SummaryOperand],
) -> SummaryTransferLength {
    match len {
        SummaryTransferLength::Arg(index) => match args.get(index) {
            Some(SummaryOperand::Arg(caller_idx)) => SummaryTransferLength::Arg(*caller_idx),
            Some(SummaryOperand::Const(value)) => SummaryTransferLength::Const(*value),
            _ => SummaryTransferLength::Unknown,
        },
        other => other,
    }
}

fn remap_lifetime_effect(
    effect: &SummaryLifetimeEffect,
    args: &[SummaryOperand],
) -> Option<SummaryLifetimeEffect> {
    let Some(SummaryOperand::Arg(caller_arg)) = args.get(effect.arg) else {
        return None;
    };
    Some(SummaryLifetimeEffect {
        arg: *caller_arg,
        op: effect.op,
    })
}

fn remap_sync_effect(
    effect: &SummarySyncEffect,
    args: &[SummaryOperand],
) -> Option<SummarySyncEffect> {
    let Some(SummaryOperand::Arg(caller_arg)) = args.get(effect.arg) else {
        return None;
    };
    Some(SummarySyncEffect {
        arg: *caller_arg,
        op: effect.op,
    })
}

fn remap_atomic_effect(
    effect: &SummaryAtomicEffect,
    args: &[SummaryOperand],
) -> SummaryAtomicEffect {
    SummaryAtomicEffect {
        op: effect.op,
        location: remap_memory_location(effect.location, args),
        ordering: effect.ordering,
    }
}

fn resolve_return_relation(
    observations: &[SummaryValueObservation],
    current: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> SummaryReturnRelation {
    if observations.is_empty() {
        return SummaryReturnRelation::Unknown;
    }
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

    relation.unwrap_or(SummaryReturnRelation::Unknown)
}

fn resolve_single_call_wrapper_return_relation(
    local: &LocalSummaryFacts,
    current: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> Option<SummaryReturnRelation> {
    if local.has_unknown_calls || local.call_observations.len() != 1 {
        return None;
    }
    if !local
        .return_observations
        .iter()
        .all(|observation| matches!(observation, SummaryValueObservation::Unknown))
    {
        return None;
    }

    let call = local.call_observations.values().next()?;
    let callee = current.get(&InterprocFunctionId(call.target))?;
    match &callee.return_relation {
        SummaryReturnRelation::Arg(idx) => match call.args.get(*idx) {
            Some(SummaryOperand::Arg(arg_idx)) => Some(SummaryReturnRelation::Arg(*arg_idx)),
            Some(SummaryOperand::Const(value)) => Some(SummaryReturnRelation::Const(*value)),
            _ => None,
        },
        SummaryReturnRelation::Const(value) => Some(SummaryReturnRelation::Const(*value)),
        SummaryReturnRelation::HeapAlloc => Some(SummaryReturnRelation::HeapAlloc),
        SummaryReturnRelation::Global(address) => Some(SummaryReturnRelation::Global(*address)),
        SummaryReturnRelation::Void | SummaryReturnRelation::Unknown => None,
    }
}

fn resolve_return_relation_with_wrapper_fallback(
    local: &LocalSummaryFacts,
    current: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> SummaryReturnRelation {
    match resolve_return_relation(&local.return_observations, current) {
        SummaryReturnRelation::Unknown => {
            resolve_single_call_wrapper_return_relation(local, current)
                .unwrap_or(SummaryReturnRelation::Unknown)
        }
        relation => relation,
    }
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
        transfer_effects: BTreeSet::new(),
        allocation_effects: BTreeSet::new(),
        lifetime_effects: BTreeSet::new(),
        sync_effects: BTreeSet::new(),
        atomic_effects: BTreeSet::new(),
        return_observations: Vec::new(),
        call_observations: BTreeMap::new(),
    };

    for (call_id, call) in &prepared.call_sites().by_id {
        match call.direct_target {
            Some(target) => {
                out.direct_callees.insert(target);
                let args = state_by_call.get(call_id).cloned().unwrap_or_else(|| {
                    (0..abi.argument_count()).map(SummaryOperand::Arg).collect()
                });
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
        for (op_idx, op) in block.ops.iter().enumerate() {
            match op {
                SSAOp::Load { addr, dst, .. }
                | SSAOp::LoadLinked { addr, dst, .. }
                | SSAOp::LoadGuarded { addr, dst, .. } => {
                    if memory_access_is_local_stack(prepared, addr) {
                        continue;
                    }
                    let location = classify_memory_access_location(prepared, abi, addr, dst.size);
                    mark_location_arg_effect(&mut out.arg_effects, location, true, false);
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location,
                    });
                    if let SSAOp::LoadLinked { ordering, .. } = op {
                        out.atomic_effects.insert(SummaryAtomicEffect {
                            op: SummaryAtomicOp::LoadLinked,
                            location,
                            ordering: summary_atomic_ordering(*ordering),
                        });
                    }
                }
                SSAOp::AtomicCAS { addr, expected, .. } => {
                    if memory_access_is_local_stack(prepared, addr) {
                        continue;
                    }
                    let location =
                        classify_memory_access_location(prepared, abi, addr, expected.size);
                    mark_location_arg_effect(&mut out.arg_effects, location, true, true);
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location,
                    });
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Write,
                        location,
                    });
                    out.atomic_effects.insert(SummaryAtomicEffect {
                        op: SummaryAtomicOp::CompareExchange,
                        location,
                        ordering: if let SSAOp::AtomicCAS { ordering, .. } = op {
                            summary_atomic_ordering(*ordering)
                        } else {
                            SummaryAtomicOrdering::Unknown
                        },
                    });
                }
                SSAOp::StoreConditional { addr, val, .. } => {
                    if memory_access_is_local_stack(prepared, addr) {
                        continue;
                    }
                    let location = classify_memory_access_location(prepared, abi, addr, val.size);
                    mark_location_arg_effect(&mut out.arg_effects, location, true, true);
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location,
                    });
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Write,
                        location,
                    });
                    out.atomic_effects.insert(SummaryAtomicEffect {
                        op: SummaryAtomicOp::StoreConditional,
                        location,
                        ordering: if let SSAOp::StoreConditional { ordering, .. } = op {
                            summary_atomic_ordering(*ordering)
                        } else {
                            SummaryAtomicOrdering::Unknown
                        },
                    });
                }
                SSAOp::Fence { ordering } => {
                    out.atomic_effects.insert(SummaryAtomicEffect {
                        op: SummaryAtomicOp::Fence,
                        location: unknown_location(),
                        ordering: summary_atomic_ordering(*ordering),
                    });
                }
                SSAOp::Store { addr, val, .. } | SSAOp::StoreGuarded { addr, val, .. } => {
                    if memory_access_is_local_stack(prepared, addr) {
                        continue;
                    }
                    let location = classify_memory_access_location(prepared, abi, addr, val.size);
                    mark_location_arg_effect(&mut out.arg_effects, location, false, true);
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Write,
                        location,
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

fn memory_access_is_local_stack(prepared: &SsaArtifact, addr: &SSAVar) -> bool {
    prepared
        .object_for_var(addr)
        .and_then(|object| prepared.objects().object(object))
        .is_some_and(|object| {
            matches!(
                object.kind,
                ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. }
            )
        })
}

fn mark_location_arg_effect(
    effects: &mut BTreeMap<usize, SummaryArgEffect>,
    location: SummaryMemoryLocation,
    read: bool,
    write: bool,
) {
    let SummaryMemoryRegion::Arg { index } = location.region else {
        return;
    };
    let effect = effects.entry(index).or_default();
    if read {
        effect.mark_read();
    }
    if write {
        effect.mark_write();
    }
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
    let mut candidates = vec![value_id];
    if rooted != value_id {
        candidates.push(rooted);
    }

    for candidate in &candidates {
        if let Some(expression) = prepared.addresses().parameter_expression(*candidate) {
            return arg_location(
                expression.parameter,
                expression.terms.is_empty().then_some(expression.offset),
                expression.terms.is_empty().then_some(width),
            );
        }
        if let Some(var) = prepared.value_var(*candidate) {
            if let Some(idx) = formal_arg_index_for_var(abi, var) {
                return arg_location(idx, Some(0), Some(width));
            }
            if let Some(address) = parse_const_name(&var.name) {
                return global_location(address, Some(0), Some(width));
            }
        }

        if let Some(object_id) = prepared.objects().object_for_value(*candidate)
            && let Some(object) = prepared.objects().object(object_id)
        {
            match object.kind {
                ObjectKind::Parameter { index } => {
                    return arg_location(index, None, None);
                }
                ObjectKind::Global { address, .. } => {
                    return global_location(address, Some(0), Some(width));
                }
                ObjectKind::HeapAlloc { .. } => {
                    return SummaryMemoryLocation {
                        region: SummaryMemoryRegion::HeapReturn,
                        range: exact_range(0, width),
                    };
                }
                ObjectKind::EscapedUnknown => {}
                _ => {}
            }
        }
    }

    let Some((op_value_id, def_inst)) = candidates.iter().find_map(|candidate| {
        prepared
            .graph()
            .def_inst(*candidate)
            .map(|inst| (*candidate, inst))
    }) else {
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
        _ if op_value_id != value_id => {
            classify_memory_access_location_value(prepared, abi, value_id, width, depth + 1)
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
    let left_const = summary_const_value(prepared, abi, left_id, ctx.depth);
    let right_const = summary_const_value(prepared, abi, right_id, ctx.depth);

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

fn summary_const_value(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
    depth: u32,
) -> Option<u64> {
    match classify_value_operand(prepared, abi, value_id, depth) {
        SummaryOperand::Const(value) => Some(value),
        _ => prepared
            .value_var(canonical_root_value(prepared, value_id))
            .and_then(|var| parse_const_name(&var.name)),
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
                if let Some(idx) = abi.argument_index(&phi.dst.name)
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
                    && let Some(idx) = abi.argument_index(&dst.name)
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
            if let Some(idx) = abi.argument_index(&phi.dst.name)
                && let Some(value_id) = graph.value_id_for_var(&phi.dst)
            {
                state.insert(idx, value_id);
            }
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            if op_idx == call_op_idx {
                let args = (0..abi.argument_count())
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
                && let Some(idx) = abi.argument_index(&dst.name)
                && let Some(value_id) = graph.value_id_for_var(dst)
            {
                state.insert(idx, value_id);
            }
        }
    }

    by_call
}

pub fn observe_call_arguments(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
) -> BTreeMap<CallSiteId, Vec<CallArgObservation>> {
    collect_call_arg_state(prepared, abi)
        .into_iter()
        .map(|(call_id, args)| {
            let args = args
                .into_iter()
                .map(|arg| match arg {
                    SummaryOperand::Arg(idx) => CallArgObservation::Arg(idx),
                    SummaryOperand::Const(value) => CallArgObservation::Const(value),
                    SummaryOperand::Unknown => CallArgObservation::Unknown,
                })
                .collect();
            (call_id, args)
        })
        .collect()
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
                if !abi.is_return_register(&dst.name) {
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
    if !abi.is_return_register(&var.name) {
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
    if let Some(idx) = formal_arg_index_for_var(abi, var) {
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
    if let Some(idx) = formal_arg_index_for_var(abi, root_var) {
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

#[cfg(test)]
fn normalize_seed_name(name: &str) -> Option<&'static str> {
    let normalized_owned = name.trim().to_ascii_lowercase();
    let mut normalized = normalized_owned.as_str();
    let has_external_marker = ["sym.imp.", "imp.", "reloc."]
        .iter()
        .any(|prefix| normalized.strip_prefix(prefix).is_some())
        || normalized.ends_with("@plt")
        || normalized.ends_with(".plt");
    if !has_external_marker {
        return None;
    }
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
        "memmove" | "__memmove_chk" => Some("memmove"),
        "copyin" => Some("copyin"),
        "copyout" => Some("copyout"),
        "memset" => Some("memset"),
        "malloc" | "__libc_malloc" | "__gi___libc_malloc" => Some("malloc"),
        "calloc" | "__libc_calloc" => Some("calloc"),
        "free" => Some("free"),
        "os_ref_retain" | "osobject_retain" => Some("retain"),
        "os_ref_release" | "osobject_release" => Some("release"),
        "lck_mtx_lock" | "lck_rw_lock_shared" | "lck_rw_lock_exclusive" => Some("lock"),
        "lck_mtx_unlock" | "lck_rw_unlock_shared" | "lck_rw_unlock_exclusive" => Some("unlock"),
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
    use r2il::{MemoryOrdering, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn x86_64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch
    }

    fn windows_x64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rcx", 8, 8));
        arch.add_register(RegisterDef::new("rdx", 16, 8));
        arch.add_register(RegisterDef::new("r8", 24, 8));
        arch.add_register(RegisterDef::new("r9", 32, 8));
        arch.add_register(RegisterDef::new("rip", 40, 8));
        arch
    }

    fn x86_64_sysv_arg_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rsi", 16, 8));
        arch.add_register(RegisterDef::new("rdx", 24, 8));
        arch.add_register(RegisterDef::new("rcx", 32, 8));
        arch.add_register(RegisterDef::new("r8", 40, 8));
        arch.add_register(RegisterDef::new("r9", 48, 8));
        arch
    }

    fn empty_local_summary(direct_callees: BTreeSet<u64>) -> LocalSummaryFacts {
        LocalSummaryFacts {
            arg_count_hint: None,
            direct_callees,
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            memory_effects: BTreeSet::new(),
            transfer_effects: BTreeSet::new(),
            allocation_effects: BTreeSet::new(),
            lifetime_effects: BTreeSet::new(),
            sync_effects: BTreeSet::new(),
            atomic_effects: BTreeSet::new(),
            return_observations: Vec::new(),
            call_observations: BTreeMap::new(),
        }
    }

    #[test]
    fn summary_sccs_handle_deep_chains_and_cycles_deterministically() {
        const FUNCTION_COUNT: u64 = 8_192;

        let mut locals = BTreeMap::new();
        for node in 0..FUNCTION_COUNT {
            let direct_callees = (node + 1 < FUNCTION_COUNT)
                .then_some(node + 1)
                .into_iter()
                .collect();
            locals.insert(
                InterprocFunctionId(node),
                (None, empty_local_summary(direct_callees)),
            );
        }

        let chain_sccs = compute_summary_sccs(&locals);
        let chain_order = chain_sccs
            .iter()
            .map(|component| {
                assert_eq!(component.len(), 1);
                component[0].0
            })
            .collect::<Vec<_>>();
        assert_eq!(chain_order, (0..FUNCTION_COUNT).rev().collect::<Vec<_>>());

        locals
            .get_mut(&InterprocFunctionId(FUNCTION_COUNT - 1))
            .expect("last function")
            .1
            .direct_callees
            .insert(0);
        let cycle_sccs = compute_summary_sccs(&locals);
        assert_eq!(cycle_sccs.len(), 1);
        assert_eq!(
            cycle_sccs[0],
            (0..FUNCTION_COUNT)
                .map(InterprocFunctionId)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn sleigh_aarch64_arch_name_uses_arm64_abi_profile() {
        let mut arch = ArchSpec::new("AARCH64:LE:64:v8A");
        arch.addr_size = 8;
        let profile = AbiProfile::from_arch(Some(&arch));

        assert_eq!(profile.argument_index("x0"), Some(0));
        assert_eq!(profile.argument_index("w1"), Some(1));
    }

    #[test]
    fn sleigh_x86_64_arch_name_uses_amd64_abi_profile_without_addr_size() {
        let arch = ArchSpec::new("x86:LE:64:default");
        let profile = AbiProfile::from_arch(Some(&arch));

        assert_eq!(profile.argument_index("rdi"), Some(0));
        assert!(profile.is_return_register("rax"));
    }

    #[test]
    fn x86_64_arch_name_uses_amd64_abi_profile_without_addr_size() {
        let arch = ArchSpec::new("x86-64");
        let profile = AbiProfile::from_arch(Some(&arch));

        assert_eq!(profile.argument_index("rdi"), Some(0));
        assert_eq!(profile.argument_index("rsi"), Some(1));
        assert!(profile.is_return_register("rax"));
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

    fn ram(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Ram,
            offset,
            size,
            meta: None,
        }
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
        assert_eq!(
            malloc.allocation_effects,
            vec![SummaryAllocationEffect {
                size_arg: Some(0),
                zeroed: false,
            }]
        );
        let memcpy =
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(2), "sym.imp.memcpy")
                .expect("memcpy seed");
        assert_eq!(memcpy.return_relation, SummaryReturnRelation::Arg(0));
        assert!(memcpy.arg_effects.get(&0).expect("dst").write);
        assert!(memcpy.arg_effects.get(&1).expect("src").read);
        assert_eq!(
            memcpy.transfer_effects,
            vec![SummaryTransferEffect {
                dst: arg_location(0, None, None),
                src: arg_location(1, None, None),
                len: SummaryTransferLength::Arg(2),
            }]
        );
    }

    #[test]
    fn seed_summary_requires_external_marker() {
        for name in [
            "malloc",
            "memcpy",
            "sym.malloc",
            "dbg.memcpy",
            "sym._copyin",
        ] {
            assert!(
                FunctionSemanticSummary::seed_for_name(InterprocFunctionId(0xdead), name).is_none(),
                "test seed must not accept local/name-only semantic owner for {name}"
            );
        }
    }

    #[test]
    fn seed_summary_models_kernel_helpers_as_canonical_effects() {
        let copyin =
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(3), "sym.imp.copyin")
                .expect("copyin seed");
        assert_eq!(
            copyin.transfer_effects,
            vec![SummaryTransferEffect {
                dst: arg_location(1, None, None),
                src: arg_location(0, None, None),
                len: SummaryTransferLength::Arg(2),
            }]
        );
        assert!(copyin.arg_effects.get(&0).expect("src").read);
        assert!(copyin.arg_effects.get(&1).expect("dst").write);

        let retain =
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(4), "sym.imp.os_ref_retain")
                .expect("retain seed");
        assert_eq!(retain.return_relation, SummaryReturnRelation::Arg(0));
        assert_eq!(
            retain.lifetime_effects,
            vec![SummaryLifetimeEffect {
                arg: 0,
                op: SummaryLifetimeOp::Retain,
            }]
        );

        let lock =
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(5), "sym.imp.lck_mtx_lock")
                .expect("lock seed");
        assert_eq!(
            lock.sync_effects,
            vec![SummarySyncEffect {
                arg: 0,
                op: SummarySyncOp::Lock,
            }]
        );
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
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(0x2000), "sym.imp.malloc")
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
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(0x2000), "sym.imp.malloc")
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
    fn solve_summary_set_uses_single_call_wrapper_fallback_for_opaque_return_register() {
        let mut arch = ArchSpec::new("x86:LE:64:default");
        arch.addr_size = 8;
        let wrapper_block = block(
            0x401000,
            vec![
                R2ILOp::Call {
                    target: c(0x2000, 8),
                },
                R2ILOp::Return { target: reg(0, 8) },
            ],
        );
        let wrapper =
            SsaArtifact::for_symbolic(&[wrapper_block], Some(&arch)).expect("wrapper ssa");
        let mut seeds = BTreeMap::new();
        seeds.insert(
            InterprocFunctionId(0x2000),
            FunctionSemanticSummary::seed_for_name(InterprocFunctionId(0x2000), "sym.imp.malloc")
                .expect("malloc"),
        );

        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x401000),
                name: Some("sym.alloc_wrapper".to_string()),
                prepared: &wrapper,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x401000)),
            &seeds,
            InterprocSolveConfig::default(),
        );

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x401000))
                .expect("wrapper summary")
                .return_relation,
            SummaryReturnRelation::HeapAlloc
        );
    }

    #[test]
    fn branchind_trampoline_without_return_stays_unknown() {
        let arch = x86_64_arch();
        let trampoline = SsaArtifact::for_decompile(
            &[block(
                0x3500,
                vec![R2ILOp::BranchInd {
                    target: ram(0x406050, 8),
                }],
            )],
            Some(&arch),
        )
        .expect("trampoline ssa")
        .with_name("sym.imp.setlocale");

        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x3500),
                name: Some("sym.imp.setlocale".to_string()),
                prepared: &trampoline,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x3500)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        );

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x3500))
                .expect("trampoline summary")
                .return_relation,
            SummaryReturnRelation::Unknown
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

    #[test]
    fn overwritten_abi_register_is_not_a_formal_argument_read() {
        let arch = x86_64_sysv_arg_arch();
        let blk = block(
            0x4050,
            vec![
                R2ILOp::Copy {
                    dst: reg(24, 8),
                    src: c(0x5000, 8),
                },
                R2ILOp::Load {
                    dst: tmp(1, 1),
                    space: SpaceId::Ram,
                    addr: reg(24, 8),
                },
                R2ILOp::Return { target: c(0, 4) },
            ],
        );
        let prepared = SsaArtifact::for_decompile(&[blk], Some(&arch)).expect("ssa");
        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x4050),
                name: Some("scratch_load".to_string()),
                prepared: &prepared,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x4050)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        );
        let summary = set
            .summaries
            .get(&InterprocFunctionId(0x4050))
            .expect("summary");

        assert!(
            !summary.arg_effects.contains_key(&2),
            "rdx was overwritten before the load, so it is not caller arg2: {summary:?}"
        );
        assert_eq!(summary.arg_count_hint, Some(0));
        assert!(summary.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Global { address: 0x5000 },
                        ..
                    }
                }
            )
        }));
    }

    #[test]
    fn unused_entry_abi_register_source_does_not_inflate_arg_count_hint() {
        let arch = x86_64_sysv_arg_arch();
        let blk = block(
            0x4060,
            vec![
                R2ILOp::IntAdd {
                    dst: tmp(1, 8),
                    a: reg(24, 8),
                    b: c(1, 8),
                },
                R2ILOp::Return { target: c(0, 4) },
            ],
        );
        let prepared = SsaArtifact::for_decompile(&[blk], Some(&arch)).expect("ssa");
        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x4060),
                name: Some("scratch_arg_reg".to_string()),
                prepared: &prepared,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x4060)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        );
        let summary = set
            .summaries
            .get(&InterprocFunctionId(0x4060))
            .expect("summary");

        assert_eq!(
            summary.arg_count_hint,
            Some(0),
            "arg count must be derived from summary effects, not raw SSA register reads"
        );
        assert!(summary.arg_effects.is_empty());
    }

    #[test]
    fn store_conditional_marks_argument_read_and_write() {
        let arch = x86_64_arch();
        let blk = block(
            0x4100,
            vec![
                R2ILOp::StoreConditional {
                    result: Some(tmp(1, 1)),
                    space: SpaceId::Ram,
                    addr: reg(8, 8),
                    val: c(0x41, 1),
                    ordering: MemoryOrdering::SeqCst,
                },
                R2ILOp::Return { target: reg(16, 8) },
            ],
        );
        let prepared = SsaArtifact::for_decompile(&[blk], Some(&arch)).expect("ssa");
        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x4100),
                name: Some("store_conditional".to_string()),
                prepared: &prepared,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x4100)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        );
        let summary = set
            .summaries
            .get(&InterprocFunctionId(0x4100))
            .expect("summary");
        let arg0 = summary.arg_effects.get(&0).expect("arg effect");
        assert!(arg0.read);
        assert!(arg0.write);
        assert_eq!(
            summary.atomic_effects,
            vec![SummaryAtomicEffect {
                op: SummaryAtomicOp::StoreConditional,
                location: arg_location(0, Some(0), Some(1)),
                ordering: SummaryAtomicOrdering::SeqCst,
            }]
        );
        assert!(summary.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index: 0 },
                        ..
                    }
                }
            )
        }));
        assert!(summary.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Write,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index: 0 },
                        ..
                    }
                }
            )
        }));
    }

    #[test]
    fn atomic_cas_marks_argument_read_and_write() {
        let arch = x86_64_arch();
        let blk = block(
            0x4200,
            vec![
                R2ILOp::AtomicCAS {
                    dst: reg(0, 8),
                    space: SpaceId::Ram,
                    addr: reg(8, 8),
                    expected: c(1, 8),
                    replacement: c(2, 8),
                    ordering: MemoryOrdering::SeqCst,
                },
                R2ILOp::Return { target: reg(16, 8) },
            ],
        );
        let prepared = SsaArtifact::for_decompile(&[blk], Some(&arch)).expect("ssa");
        let set = solve_interproc_summary_set(
            &[InterprocFunctionInput {
                id: InterprocFunctionId(0x4200),
                name: Some("atomic_cas".to_string()),
                prepared: &prepared,
            }],
            Some(&arch),
            Some(InterprocFunctionId(0x4200)),
            &BTreeMap::new(),
            InterprocSolveConfig::default(),
        );
        let summary = set
            .summaries
            .get(&InterprocFunctionId(0x4200))
            .expect("summary");
        let arg0 = summary.arg_effects.get(&0).expect("arg effect");
        assert!(arg0.read);
        assert!(arg0.write);
        assert_eq!(
            summary.atomic_effects,
            vec![SummaryAtomicEffect {
                op: SummaryAtomicOp::CompareExchange,
                location: arg_location(0, Some(0), Some(8)),
                ordering: SummaryAtomicOrdering::SeqCst,
            }]
        );
        assert!(summary.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index: 0 },
                        ..
                    }
                }
            )
        }));
        assert!(summary.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Write,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index: 0 },
                        ..
                    }
                }
            )
        }));
    }

    #[test]
    fn symbolic_store_plus_constant_preserves_arg_offset_range() {
        let arch = x86_64_arch();
        let prepared = SsaArtifact::for_symbolic(
            &[block(
                0x4300,
                vec![
                    R2ILOp::IntAdd {
                        dst: reg(0x80, 8),
                        a: reg(8, 8),
                        b: c(2, 8),
                    },
                    R2ILOp::Store {
                        addr: reg(0x80, 8),
                        val: reg(16, 2),
                        space: SpaceId::Ram,
                    },
                    R2ILOp::Return { target: c(0, 8) },
                ],
            )],
            Some(&arch),
        )
        .expect("ssa");
        let abi = AbiProfile::from_arch(Some(&arch));
        let block = prepared.function().get_block(0x4300).expect("block");
        let SSAOp::Store { addr, val, .. } = &block.ops[1] else {
            panic!("expected store");
        };
        let addr_id = prepared
            .graph()
            .value_id_for_var(addr)
            .expect("store addr value id");
        let def_inst = prepared.graph().def_inst(addr_id).expect("store addr def");
        let inst = prepared.graph().inst(def_inst).expect("store addr inst");
        let [left_id, right_id] = match inst.inputs.as_slice() {
            [left, right] => [*left, *right],
            _ => panic!("expected additive store addr inputs"),
        };
        let InstPayload::Op(op) = &inst.payload else {
            panic!("expected op payload");
        };
        assert_eq!(summary_const_value(&prepared, &abi, right_id, 0), Some(2));
        assert_eq!(
            classify_memory_access_location_value(&prepared, &abi, left_id, val.size, 0),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(0, val.size),
            }
        );
        assert_eq!(
            classify_memory_additive_location(
                &prepared,
                &abi,
                left_id,
                right_id,
                AdditiveLocationCtx::new(val.size, 1, 1, op),
            ),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(2, val.size),
            }
        );
        assert_eq!(
            classify_memory_access_location_value(&prepared, &abi, addr_id, val.size, 0),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(2, val.size),
            }
        );
        let location = classify_memory_access_location(&prepared, &abi, addr, val.size);
        assert_eq!(
            location,
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(2, val.size),
            },
            "store address should resolve to arg0+2, got {location:?}; addr={addr:?}; ops={:?}",
            block.ops
        );
    }

    #[test]
    fn symbolic_store_minus_constant_preserves_arg_offset_range() {
        let arch = x86_64_arch();
        let prepared = SsaArtifact::for_symbolic(
            &[block(
                0x4310,
                vec![
                    R2ILOp::IntSub {
                        dst: reg(0x80, 8),
                        a: reg(8, 8),
                        b: c(1, 8),
                    },
                    R2ILOp::Store {
                        addr: reg(0x80, 8),
                        val: reg(16, 1),
                        space: SpaceId::Ram,
                    },
                    R2ILOp::Return { target: c(0, 8) },
                ],
            )],
            Some(&arch),
        )
        .expect("ssa");
        let abi = AbiProfile::from_arch(Some(&arch));
        let block = prepared.function().get_block(0x4310).expect("block");
        let SSAOp::Store { addr, val, .. } = &block.ops[1] else {
            panic!("expected store");
        };
        let addr_id = prepared
            .graph()
            .value_id_for_var(addr)
            .expect("store addr value id");
        let def_inst = prepared.graph().def_inst(addr_id).expect("store addr def");
        let inst = prepared.graph().inst(def_inst).expect("store addr inst");
        let [left_id, right_id] = match inst.inputs.as_slice() {
            [left, right] => [*left, *right],
            _ => panic!("expected additive store addr inputs"),
        };
        let InstPayload::Op(op) = &inst.payload else {
            panic!("expected op payload");
        };
        assert_eq!(summary_const_value(&prepared, &abi, right_id, 0), Some(1));
        assert_eq!(
            classify_memory_access_location_value(&prepared, &abi, left_id, val.size, 0),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(0, val.size),
            }
        );
        assert_eq!(
            classify_memory_additive_location(
                &prepared,
                &abi,
                left_id,
                right_id,
                AdditiveLocationCtx::new(val.size, 1, -1, op),
            ),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(-1, val.size),
            }
        );
        assert_eq!(
            classify_memory_access_location_value(&prepared, &abi, addr_id, val.size, 0),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(-1, val.size),
            }
        );
        let location = classify_memory_access_location(&prepared, &abi, addr, val.size);
        assert_eq!(
            location,
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(-1, val.size),
            },
            "store address should resolve to arg0-1, got {location:?}; addr={addr:?}; ops={:?}",
            block.ops
        );
    }

    #[test]
    fn windows_x64_call_arg_observer_tracks_registration_handler_constant() {
        let arch = windows_x64_arch();
        let prepared = SsaArtifact::for_symbolic(
            &[block(
                0x5000,
                vec![
                    R2ILOp::Copy {
                        dst: reg(8, 8),
                        src: c(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: reg(16, 8),
                        src: c(0x1400_3d0f, 8),
                    },
                    R2ILOp::Call {
                        target: c(0x1800_1000, 8),
                    },
                    R2ILOp::Return { target: c(0, 8) },
                ],
            )],
            Some(&arch),
        )
        .expect("ssa");

        let observations = observe_call_arguments(&prepared, &AbiProfile::windows_x64());
        let call_id = prepared
            .call_sites()
            .by_id
            .keys()
            .next()
            .copied()
            .expect("callsite");
        let args = observations.get(&call_id).expect("call args");
        assert_eq!(args.first(), Some(&CallArgObservation::Const(1)));
        assert_eq!(args.get(1), Some(&CallArgObservation::Const(0x1400_3d0f)));
    }
}
