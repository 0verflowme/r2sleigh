//! Interprocedural semantic summaries built on top of prepared SSA.
//!
//! This layer stays summary-based on purpose. It reuses the canonical
//! intraprocedural facts in [`SsaArtifact`] and solves a deterministic
//! fixpoint over direct-call reachable functions without introducing a second
//! whole-program SSA graph.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use r2il::{ArchSpec, MemoryOrdering, SpaceId};
use serde::{Deserialize, Serialize};

use crate::abi::AbiProfile;
use crate::function::SsaArtifact;
use crate::graph::{InstPayload, UseSite, ValueId};
use crate::op::SSAOp;
use crate::semantic::ObjectKind;
use crate::{CallSiteId, SSAVar};

/// Current serialized interprocedural report schema.
///
/// Version 1 denotes the historical unversioned encoding. Version 2 is the
/// first encoding that carries and mirrors an explicit schema stamp at both
/// the report-set and per-function levels.
pub const INTERPROC_SUMMARY_SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterprocSummarySchemaError {
    ReportSchemaVersion {
        found: u32,
    },
    FunctionSchemaVersion {
        id: InterprocFunctionId,
        found: u32,
    },
    FunctionIdentityMismatch {
        key: InterprocFunctionId,
        summary_id: InterprocFunctionId,
    },
}

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

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSemanticSummary {
    pub schema_version: u32,
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    pub linkage: FunctionSemanticLinkage,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub arg_count_hint: Option<usize>,
    pub direct_callees: BTreeSet<u64>,
    pub callsite_count: usize,
    pub has_unknown_calls: bool,
    pub arg_effects: BTreeMap<usize, SummaryArgEffect>,
    pub memory_effects: Vec<SummaryMemoryEffect>,
    pub transfer_effects: Vec<SummaryTransferEffect>,
    pub allocation_effects: Vec<SummaryAllocationEffect>,
    pub lifetime_effects: Vec<SummaryLifetimeEffect>,
    pub sync_effects: Vec<SummarySyncEffect>,
    pub atomic_effects: Vec<SummaryAtomicEffect>,
    pub return_relation: SummaryReturnRelation,
    pub reads_global_memory: bool,
    pub writes_global_memory: bool,
    pub touches_unknown_memory: bool,
}

impl FunctionSemanticSummary {
    /// Whether this report uses the current non-authoritative wire schema.
    pub const fn has_current_schema(&self) -> bool {
        self.schema_version == INTERPROC_SUMMARY_SCHEMA_VERSION
    }

    pub fn unknown(id: InterprocFunctionId, name: Option<String>) -> Self {
        Self {
            schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
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
            schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
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

/// Serializable interprocedural report data.
///
/// This value does not retain an SSA owner and therefore is not authority for
/// type writeback or certification. Consumers that need source-owned evidence
/// must use [`PreparedInterprocSummarySet`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterprocSummarySet {
    pub schema_version: u32,
    pub root: Option<InterprocFunctionId>,
    pub summaries: BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
    pub diagnostics: InterprocSummaryDiagnostics,
}

impl Default for InterprocSummarySet {
    fn default() -> Self {
        Self {
            schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
            root: None,
            summaries: BTreeMap::new(),
            diagnostics: InterprocSummaryDiagnostics::default(),
        }
    }
}

impl InterprocSummarySet {
    /// Validate the complete report projection against the current wire
    /// schema. This never upgrades or normalizes older report data.
    pub fn validate_current_schema(&self) -> Result<(), InterprocSummarySchemaError> {
        if self.schema_version != INTERPROC_SUMMARY_SCHEMA_VERSION {
            return Err(InterprocSummarySchemaError::ReportSchemaVersion {
                found: self.schema_version,
            });
        }
        validate_function_summary_map(&self.summaries)
    }

    /// Validate the complete report projection against the current wire
    /// schema, including each nested function summary and its map identity.
    pub fn has_current_schema(&self) -> bool {
        self.validate_current_schema().is_ok()
    }
}

fn validate_function_summary_map(
    summaries: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
) -> Result<(), InterprocSummarySchemaError> {
    for (key, summary) in summaries {
        if summary.schema_version != INTERPROC_SUMMARY_SCHEMA_VERSION {
            return Err(InterprocSummarySchemaError::FunctionSchemaVersion {
                id: *key,
                found: summary.schema_version,
            });
        }
        if *key != summary.id {
            return Err(InterprocSummarySchemaError::FunctionIdentityMismatch {
                key: *key,
                summary_id: summary.id,
            });
        }
    }
    Ok(())
}

/// Source-owned interprocedural evidence sealed to one exact SSA allocation.
///
/// The private fields deliberately prevent promoting a serialized
/// [`InterprocSummarySet`] back into authoritative evidence.
#[derive(Debug, Clone)]
pub struct PreparedInterprocSummarySet {
    root: InterprocFunctionId,
    owners: BTreeMap<InterprocFunctionId, Arc<SsaArtifact>>,
    /// Every function this evidence was derived from a body for, whether or
    /// not that body's allocation is still retained. Retention is a memory
    /// decision; which functions contributed evidence is a fact about the
    /// evidence, and a consumer asking "was there a body for this callee"
    /// is asking the second question.
    bodies: BTreeSet<InterprocFunctionId>,
    report: InterprocSummarySet,
}

impl PreparedInterprocSummarySet {
    /// Borrow the exact immutable SSA owner used to produce this evidence.
    pub fn root(&self) -> &Arc<SsaArtifact> {
        self.owners
            .get(&self.root)
            .expect("prepared interproc root owner is retained")
    }

    /// Borrow every exact immutable SSA owner used to produce this evidence.
    pub fn owners(&self) -> &BTreeMap<InterprocFunctionId, Arc<SsaArtifact>> {
        &self.owners
    }

    /// Borrow one exact immutable SSA owner by its function identity.
    pub fn owner(&self, id: InterprocFunctionId) -> Option<&Arc<SsaArtifact>> {
        self.owners.get(&id)
    }

    /// Whether this evidence was derived from a body for `id`.
    pub fn has_body(&self, id: InterprocFunctionId) -> bool {
        self.bodies.contains(&id)
    }

    /// Every function a body contributed evidence for.
    pub fn bodies(&self) -> &BTreeSet<InterprocFunctionId> {
        &self.bodies
    }

    /// Borrow the report projection produced from the retained root.
    pub fn report(&self) -> &InterprocSummarySet {
        &self.report
    }

    /// Return whether `root` is the exact retained SSA allocation.
    pub fn matches_root(&self, root: &Arc<SsaArtifact>) -> bool {
        Arc::ptr_eq(self.root(), root)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PreparedInterprocSummaryError {
    MissingRoot,
    DuplicateRoot,
    MislabeledRoot,
    ForeignRoot,
    DuplicateFunction,
    MislabeledFunction,
    ManualFunction,
    ForeignFunction,
    UnknownOrIncoherentMachineContext,
    ArchitectureMismatch,
    ManualRootWithHelpers,
    FunctionBlockRangeOverflow,
    OverlappingFunctionBlockRanges,
    NonConverged,
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

/// One exact owned input to an authoritative interprocedural solve.
///
/// Unlike [`InterprocFunctionInput`], this form retains the caller's `Arc`, so
/// every helper contributing evidence remains alive for the lifetime of the
/// returned [`PreparedInterprocSummarySet`].
#[derive(Debug, Clone)]
pub struct PreparedInterprocFunctionInput<'a> {
    pub id: InterprocFunctionId,
    pub name: Option<String>,
    pub prepared: &'a Arc<SsaArtifact>,
}

fn formal_arg_index_for_var(prepared: &SsaArtifact, var: &SSAVar) -> Option<usize> {
    let value = prepared.graph().value_id_for_var(var)?;
    prepared
        .facts()
        .boundaries
        .parameters
        .iter()
        .find_map(|(index, parameter)| {
            (parameter.value == value)
                .then(|| usize::try_from(*index).ok())
                .flatten()
        })
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
    result_storage: Option<crate::CanonicalStorageId>,
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
    call_carriers_converged: bool,
}

#[derive(Debug)]
struct CallArgumentState {
    by_call: BTreeMap<CallSiteId, Vec<SummaryOperand>>,
    converged: bool,
}

fn require_converged_call_carriers(
    local: &LocalSummaryFacts,
) -> Result<(), PreparedInterprocSummaryError> {
    local
        .call_carriers_converged
        .then_some(())
        .ok_or(PreparedInterprocSummaryError::NonConverged)
}

fn require_converged_summary_report(
    report: &InterprocSummarySet,
) -> Result<(), PreparedInterprocSummaryError> {
    report
        .diagnostics
        .converged
        .then_some(())
        .ok_or(PreparedInterprocSummaryError::NonConverged)
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

fn prepared_obligations_require_unknown_effects(prepared: &SsaArtifact) -> bool {
    let inventory = prepared.obligations();
    !inventory.is_complete()
        || inventory.obligations().values().any(|obligation| {
            obligation.id.kind == crate::SemanticObligationKind::VolatileOrUnknownEffect
        })
}

fn unknown_call_argument_state(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    converged: bool,
) -> CallArgumentState {
    CallArgumentState {
        by_call: prepared
            .call_sites()
            .by_id
            .keys()
            .map(|call_id| (*call_id, unknown_call_arguments(prepared, abi, *call_id)))
            .collect(),
        converged,
    }
}

fn mark_unknown_call_effects(
    has_unknown_calls: &mut bool,
    arg_effects: &mut BTreeMap<usize, SummaryArgEffect>,
    memory_effects: &mut BTreeSet<SummaryMemoryEffect>,
    args: Option<&[SummaryOperand]>,
) {
    *has_unknown_calls = true;
    if let Some(args) = args {
        for actual in args {
            let SummaryOperand::Arg(idx) = actual else {
                continue;
            };
            let effect = arg_effects.entry(*idx).or_default();
            effect.mark_read();
            effect.mark_write();
            effect.escape = true;
            for kind in [
                SummaryMemoryEffectKind::Read,
                SummaryMemoryEffectKind::Write,
                SummaryMemoryEffectKind::Escape,
            ] {
                memory_effects.insert(SummaryMemoryEffect {
                    kind,
                    location: arg_location(*idx, None, None),
                });
            }
        }
    }
    for kind in [
        SummaryMemoryEffectKind::Read,
        SummaryMemoryEffectKind::Write,
        SummaryMemoryEffectKind::Escape,
    ] {
        memory_effects.insert(SummaryMemoryEffect {
            kind,
            location: unknown_location(),
        });
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

/// Solve serializable report data without retaining source authority.
///
/// This entrypoint remains useful for simulation and reporting. Its result
/// must not authorize type writeback or certification.
pub fn solve_interproc_summary_set(
    functions: &[InterprocFunctionInput<'_>],
    arch: Option<&ArchSpec>,
    root: Option<InterprocFunctionId>,
    seed_summaries: &BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
    config: InterprocSolveConfig,
) -> Result<InterprocSummarySet, InterprocSummarySchemaError> {
    validate_function_summary_map(seed_summaries)?;
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

    Ok(solve_interproc_summary_set_from_locals(
        locals,
        current,
        root,
        config,
        functions.len(),
    ))
}

fn solve_interproc_summary_set_from_locals(
    locals: BTreeMap<InterprocFunctionId, (Option<String>, LocalSummaryFacts)>,
    mut current: BTreeMap<InterprocFunctionId, FunctionSemanticSummary>,
    root: Option<InterprocFunctionId>,
    config: InterprocSolveConfig,
    scope_size: usize,
) -> InterprocSummarySet {
    let sccs = compute_summary_sccs(&locals);
    // Convergence is proven by a pass that changes nothing, so a fixpoint needs
    // one pass to compute a summary and a second to confirm it. A budget of one
    // can only ever end mid-change, which reports every summary as unconverged
    // no matter how simple the function is.
    let max_iterations = config.max_iterations.max(2);
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
        schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
        root,
        summaries: current,
        diagnostics: InterprocSummaryDiagnostics {
            iterations,
            max_iterations,
            converged,
            scope_size,
            scc_count: sccs.len(),
            max_scc_size,
        },
    }
}

fn validate_prepared_interproc_block_ranges(
    functions: &[PreparedInterprocFunctionInput<'_>],
) -> Result<(), PreparedInterprocSummaryError> {
    validate_interproc_block_ranges(functions.iter().flat_map(|function| {
        function
            .prepared
            .function()
            .blocks()
            .map(move |block| (function.id, block.addr, block.size))
    }))
}

fn validate_interproc_block_ranges(
    blocks: impl IntoIterator<Item = (InterprocFunctionId, u64, u32)>,
) -> Result<(), PreparedInterprocSummaryError> {
    let mut ranges = blocks
        .into_iter()
        .map(|(owner, start, size)| {
            start
                .checked_add(u64::from(size))
                .map(|end| (start, end, owner))
                .ok_or(PreparedInterprocSummaryError::FunctionBlockRangeOverflow)
        })
        .collect::<Result<Vec<_>, _>>()?;
    ranges.sort_unstable();
    for (index, &(start, end, owner)) in ranges.iter().enumerate() {
        for &(other_start, _, other_owner) in &ranges[index + 1..] {
            if other_start >= end {
                break;
            }
            if owner != other_owner && start < end {
                return Err(PreparedInterprocSummaryError::OverlappingFunctionBlockRanges);
            }
        }
    }
    Ok(())
}

fn require_trusted_root_for_helper_scope(
    root_provenance: crate::SsaArtifactProvenanceKind,
    scope_size: usize,
) -> Result<(), PreparedInterprocSummaryError> {
    if scope_size > 1 && root_provenance != crate::SsaArtifactProvenanceKind::TrustedSource {
        return Err(PreparedInterprocSummaryError::ManualRootWithHelpers);
    }
    Ok(())
}

/// Solve interprocedural evidence owned by one exact prepared SSA root.
///
/// Exactly one input must identify the root by function id, entry, and
/// artifact authority. Independently rebuilt, omitted, duplicated, or
/// mislabeled roots are refused before any report is sealed. Every helper id
/// must equal its prepared entry and be unique. This authoritative path is
/// deliberately seedless; external and name-derived seeds remain report-only.
/// One callee's whole contribution to a caller's interprocedural solve.
///
/// Everything here is derived from that callee's own prepared body and
/// nothing else: the local effect summary the fixpoint iterates over, and the
/// facts the caller checks it against. So it can be derived once for a
/// function and used by every caller of it, which is what lets a caller reuse
/// the work without keeping the callee's whole SSA allocation alive to redo
/// it from.
#[derive(Debug, Clone)]
pub struct PreparedCalleeSummary {
    id: InterprocFunctionId,
    architecture_family: crate::MachineArchitectureFamily,
    revision_identity: Vec<u8>,
    blocks: Vec<(u64, u32)>,
    local: LocalSummaryFacts,
}

impl PreparedCalleeSummary {
    /// Derive a callee's contribution from the body that owns it. The body is
    /// read here and not retained.
    ///
    /// No name is taken. Names supplied by a scope are presentation advice
    /// rather than evidence the prepared owner retains, and an authoritative
    /// summary is invariant to them.
    pub fn derive(
        id: InterprocFunctionId,
        prepared: &Arc<SsaArtifact>,
    ) -> Result<Self, PreparedInterprocSummaryError> {
        if id.0 != prepared.function().entry {
            return Err(PreparedInterprocSummaryError::MislabeledFunction);
        }
        if prepared.provenance_kind() != crate::SsaArtifactProvenanceKind::TrustedSource {
            return Err(PreparedInterprocSummaryError::ManualFunction);
        }
        let abi = AbiProfile::from_machine_context(prepared.machine_context())
            .ok_or(PreparedInterprocSummaryError::UnknownOrIncoherentMachineContext)?;
        let revision_identity = prepared
            .machine_context()
            .function_interface()
            .map(|interface| interface.revision_identity().to_vec())
            .ok_or(PreparedInterprocSummaryError::UnknownOrIncoherentMachineContext)?;
        let local = collect_source_owned_summary_facts(prepared, &abi);
        require_converged_call_carriers(&local)?;
        Ok(Self {
            id,
            architecture_family: prepared.machine_context().architecture_family(),
            revision_identity,
            blocks: prepared
                .function()
                .blocks()
                .map(|block| (block.addr, block.size))
                .collect(),
            local,
        })
    }

    pub const fn id(&self) -> InterprocFunctionId {
        self.id
    }
}

/// Solve the summary set for one root against callee contributions already
/// derived from their own bodies.
///
/// The root still arrives as its exact allocation, because the evidence is
/// sealed to it. A callee arrives as what it contributes, which is all the
/// solve reads of it.
pub fn solve_prepared_interproc_summary_set_from_callee_summaries(
    root: Arc<SsaArtifact>,
    callees: &[PreparedCalleeSummary],
    config: InterprocSolveConfig,
) -> Result<PreparedInterprocSummarySet, PreparedInterprocSummaryError> {
    let root_id = InterprocFunctionId(root.function().entry);
    let mut seen = BTreeSet::new();
    seen.insert(root_id);
    for callee in callees {
        if callee.id == root_id {
            return Err(PreparedInterprocSummaryError::DuplicateRoot);
        }
        if !seen.insert(callee.id) {
            return Err(PreparedInterprocSummaryError::DuplicateFunction);
        }
    }

    let root_family = root.machine_context().architecture_family();
    let root_revision = root
        .machine_context()
        .function_interface()
        .map(|interface| interface.revision_identity().to_vec())
        .ok_or(PreparedInterprocSummaryError::UnknownOrIncoherentMachineContext)?;
    let root_abi = AbiProfile::from_machine_context(root.machine_context())
        .ok_or(PreparedInterprocSummaryError::UnknownOrIncoherentMachineContext)?;

    for callee in callees {
        if callee.architecture_family != root_family {
            return Err(PreparedInterprocSummaryError::ArchitectureMismatch);
        }
        if callee.revision_identity != root_revision {
            return Err(PreparedInterprocSummaryError::ForeignFunction);
        }
    }
    validate_interproc_block_ranges(
        root.function()
            .blocks()
            .map(|block| (root_id, block.addr, block.size))
            .chain(callees.iter().flat_map(|callee| {
                callee
                    .blocks
                    .iter()
                    .map(move |(addr, size)| (callee.id, *addr, *size))
            })),
    )?;

    let root_local = collect_source_owned_summary_facts(&root, &root_abi);
    require_converged_call_carriers(&root_local)?;
    require_trusted_root_for_helper_scope(root.provenance_kind(), callees.len() + 1)?;

    let mut owners = BTreeMap::new();
    let mut bodies = BTreeSet::new();
    let mut locals = BTreeMap::new();
    let mut current = BTreeMap::new();
    owners.insert(root_id, Arc::clone(&root));
    bodies.insert(root_id);
    current.insert(root_id, initial_summary(root_id, None, &root_local));
    locals.insert(root_id, (None, root_local));
    for callee in callees {
        bodies.insert(callee.id);
        current.insert(callee.id, initial_summary(callee.id, None, &callee.local));
        locals.insert(callee.id, (None, callee.local.clone()));
    }

    let report = solve_interproc_summary_set_from_locals(
        locals,
        current,
        Some(root_id),
        config,
        callees.len() + 1,
    );
    require_converged_summary_report(&report)?;
    Ok(PreparedInterprocSummarySet {
        root: root_id,
        owners,
        bodies,
        report,
    })
}

/// Solve from whole prepared bodies. Each non-root body is reduced to its
/// contribution first, which is all the solve reads of it.
pub fn solve_prepared_interproc_summary_set(
    root: Arc<SsaArtifact>,
    functions: &[PreparedInterprocFunctionInput<'_>],
    config: InterprocSolveConfig,
) -> Result<PreparedInterprocSummarySet, PreparedInterprocSummaryError> {
    let root_id = InterprocFunctionId(root.function().entry);
    let mut function_ids = BTreeSet::new();
    for function in functions {
        if function.id.0 != function.prepared.function().entry {
            return Err(if function.prepared.authority() == root.authority() {
                PreparedInterprocSummaryError::MislabeledRoot
            } else {
                PreparedInterprocSummaryError::MislabeledFunction
            });
        }
        if !function_ids.insert(function.id) {
            return Err(if function.id == root_id {
                PreparedInterprocSummaryError::DuplicateRoot
            } else {
                PreparedInterprocSummaryError::DuplicateFunction
            });
        }
    }
    let root_candidates = functions
        .iter()
        .filter(|function| {
            function.id == root_id
                || function.prepared.function().entry == root.function().entry
                || function.prepared.authority() == root.authority()
        })
        .collect::<Vec<_>>();

    if root_candidates.len() > 1 {
        return Err(PreparedInterprocSummaryError::DuplicateRoot);
    }
    let Some(root_input) = root_candidates.first() else {
        return Err(PreparedInterprocSummaryError::MissingRoot);
    };
    if root_input.id != root_id || root_input.prepared.function().entry != root.function().entry {
        return Err(PreparedInterprocSummaryError::MislabeledRoot);
    }
    if !Arc::ptr_eq(root_input.prepared, &root) {
        return Err(PreparedInterprocSummaryError::ForeignRoot);
    }
    // Refuse in the order this entry point always has. A body that is not
    // source-owned cannot contribute at all, but a scope that is the wrong
    // architecture or whose functions overlap is wrong about every body in
    // it, so those answers come first.
    let root_family = root.machine_context().architecture_family();
    for function in functions {
        if function.prepared.machine_context().architecture_family() != root_family {
            return Err(PreparedInterprocSummaryError::ArchitectureMismatch);
        }
    }
    validate_prepared_interproc_block_ranges(functions)?;

    let mut callees = Vec::new();
    for function in functions {
        if function.id == root_id {
            continue;
        }
        callees.push(PreparedCalleeSummary::derive(
            function.id,
            function.prepared,
        )?);
    }
    let mut set =
        solve_prepared_interproc_summary_set_from_callee_summaries(root, &callees, config)?;
    // This entry point was handed the bodies, so it can retain them.
    for function in functions {
        set.owners
            .insert(function.id, Arc::clone(function.prepared));
    }
    Ok(set)
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
        schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
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
    let mut has_unknown_calls = local.has_unknown_calls;
    let mut arg_effects = local.arg_effects.clone();
    let mut memory_effects = local.memory_effects.clone();
    let mut transfer_effects = local.transfer_effects.clone();
    let mut allocation_effects = local.allocation_effects.clone();
    let mut lifetime_effects = local.lifetime_effects.clone();
    let mut sync_effects = local.sync_effects.clone();
    let mut atomic_effects = local.atomic_effects.clone();
    let mut has_unresolved_direct_call = false;
    for call in local.call_observations.values() {
        let Some(callee) = current.get(&InterprocFunctionId(call.target)) else {
            has_unresolved_direct_call = true;
            mark_unknown_call_effects(
                &mut has_unknown_calls,
                &mut arg_effects,
                &mut memory_effects,
                Some(&call.args),
            );
            continue;
        };
        has_unknown_calls |= callee.has_unknown_calls;
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
    let return_relation = if local.has_unknown_calls || has_unresolved_direct_call {
        SummaryReturnRelation::Unknown
    } else {
        resolve_return_relation_with_wrapper_fallback(local, current)
    };
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
        schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
        id,
        name,
        linkage: FunctionSemanticLinkage::Unknown,
        arg_count_hint,
        direct_callees: local.direct_callees.clone(),
        callsite_count: local.callsite_count,
        has_unknown_calls,
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
    call.result_storage?;
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

fn exact_call_result_storage(
    prepared: &SsaArtifact,
    call_site: CallSiteId,
) -> Option<crate::CanonicalStorageId> {
    let interface = prepared.machine_context().call_site_interface(call_site)?;
    if !interface.is_complete() {
        return None;
    }
    match interface.result() {
        crate::SourceCallResult::Register { storage }
            if Some(storage) == exact_function_return_storage(prepared) =>
        {
            Some(storage)
        }
        crate::SourceCallResult::Register { .. } => None,
        crate::SourceCallResult::Void => None,
    }
}

fn exact_function_return_storage(prepared: &SsaArtifact) -> Option<crate::CanonicalStorageId> {
    match prepared
        .machine_context()
        .function_interface()?
        .return_kind()
    {
        crate::SourceFunctionReturn::Register { storage } => Some(storage),
        crate::SourceFunctionReturn::Void => None,
    }
}

fn collect_local_summary_facts(prepared: &SsaArtifact, abi: &AbiProfile) -> LocalSummaryFacts {
    collect_local_summary_facts_with_obligation_authority(prepared, abi, false)
}

fn collect_source_owned_summary_facts(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
) -> LocalSummaryFacts {
    collect_local_summary_facts_with_obligation_authority(prepared, abi, true)
}

fn collect_local_summary_facts_with_obligation_authority(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    source_owned: bool,
) -> LocalSummaryFacts {
    let function = prepared.function();
    let source_requires_unknown_effects =
        source_owned && prepared_obligations_require_unknown_effects(prepared);
    let observed_call_argument_state = collect_call_arg_state(prepared, abi);
    let call_argument_state = if source_requires_unknown_effects {
        unknown_call_argument_state(prepared, abi, observed_call_argument_state.converged)
    } else {
        observed_call_argument_state
    };
    let state_by_call = &call_argument_state.by_call;
    let mut has_volatile_or_unknown_effects = source_requires_unknown_effects;
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
        call_carriers_converged: call_argument_state.converged,
    };

    if source_requires_unknown_effects {
        let formal_arguments = (0..abi.argument_count())
            .map(SummaryOperand::Arg)
            .collect::<Vec<_>>();
        mark_unknown_call_effects(
            &mut out.has_unknown_calls,
            &mut out.arg_effects,
            &mut out.memory_effects,
            Some(&formal_arguments),
        );
    }

    for (call_id, call) in &prepared.call_sites().by_id {
        match call.direct_target {
            Some(target) => {
                out.direct_callees.insert(target);
                let args = state_by_call
                    .get(call_id)
                    .cloned()
                    .unwrap_or_else(|| unknown_call_arguments(prepared, abi, *call_id));
                out.call_observations.insert(
                    *call_id,
                    CallObservation {
                        target,
                        args,
                        result_storage: exact_call_result_storage(prepared, *call_id),
                    },
                );
            }
            None => {
                mark_unknown_call_effects(
                    &mut out.has_unknown_calls,
                    &mut out.arg_effects,
                    &mut out.memory_effects,
                    state_by_call.get(call_id).map(Vec::as_slice),
                );
            }
        }
    }

    for block in function.blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            match op {
                SSAOp::Load { addr, dst, space }
                | SSAOp::LoadLinked {
                    addr, dst, space, ..
                }
                | SSAOp::LoadGuarded {
                    addr, dst, space, ..
                } => {
                    if memory_access_is_local_stack(prepared, addr, *space) {
                        continue;
                    }
                    let location =
                        classify_memory_access_location(prepared, abi, addr, *space, dst.size);
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
                SSAOp::AtomicCAS {
                    addr,
                    expected,
                    space,
                    ..
                } => {
                    if memory_access_is_local_stack(prepared, addr, *space) {
                        continue;
                    }
                    let location =
                        classify_memory_access_location(prepared, abi, addr, *space, expected.size);
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
                SSAOp::StoreConditional {
                    addr, val, space, ..
                } => {
                    if memory_access_is_local_stack(prepared, addr, *space) {
                        continue;
                    }
                    let location =
                        classify_memory_access_location(prepared, abi, addr, *space, val.size);
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
                SSAOp::Store { addr, val, space }
                | SSAOp::StoreGuarded {
                    addr, val, space, ..
                } => {
                    if memory_access_is_local_stack(prepared, addr, *space) {
                        continue;
                    }
                    let location =
                        classify_memory_access_location(prepared, abi, addr, *space, val.size);
                    mark_location_arg_effect(&mut out.arg_effects, location, false, true);
                    out.memory_effects.insert(SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Write,
                        location,
                    });
                }
                SSAOp::Return { target } => {
                    out.return_observations.push(classify_return_target(
                        prepared,
                        block.addr,
                        op_idx,
                        target,
                        &out.call_observations,
                    ));
                }
                SSAOp::CallOther { inputs, .. } => {
                    has_volatile_or_unknown_effects = true;
                    let args = inputs
                        .iter()
                        .map(|input| classify_var_operand(prepared, input, 0))
                        .collect::<Vec<_>>();
                    mark_unknown_call_effects(
                        &mut out.has_unknown_calls,
                        &mut out.arg_effects,
                        &mut out.memory_effects,
                        Some(&args),
                    );
                }
                op if has_volatile_or_unknown_effect(op) => {
                    has_volatile_or_unknown_effects = true;
                    mark_unknown_call_effects(
                        &mut out.has_unknown_calls,
                        &mut out.arg_effects,
                        &mut out.memory_effects,
                        None,
                    );
                }
                _ => {}
            }
        }
    }

    if has_volatile_or_unknown_effects {
        out.return_observations.clear();
        out.return_observations
            .push(SummaryValueObservation::Unknown);
    }

    out
}

/// Keep this classification aligned with the operations for which obligation
/// collection emits `VolatileOrUnknownEffect`. None of these operations carry
/// exact preservation authority for call carriers or observable memory.
fn has_volatile_or_unknown_effect(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::CallOther { .. } | SSAOp::Unimplemented | SSAOp::CpuId { .. } | SSAOp::New { .. }
    )
}

fn apply_call_carrier_transfer(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    state: &mut CallCarrierMap,
    op: &SSAOp,
) {
    if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. })
        || has_volatile_or_unknown_effect(op)
    {
        state
            .values_mut()
            .for_each(|value| *value = CallCarrierState::Unknown);
    } else if let Some(dst) = op.dst() {
        update_call_carrier_state(prepared, abi, state, dst);
    }
}

fn memory_access_is_local_stack(prepared: &SsaArtifact, addr: &SSAVar, space: SpaceId) -> bool {
    prepared
        .object_for_var(addr, space)
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
    space: SpaceId,
    width: u32,
) -> SummaryMemoryLocation {
    if space != SpaceId::Ram {
        return unknown_location();
    }
    let Some(value_id) = prepared.graph().value_id_for_var(addr) else {
        return unknown_location();
    };
    classify_memory_access_location_value(prepared, abi, value_id, space, width, 0)
}

fn classify_memory_access_location_value(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    value_id: ValueId,
    space: SpaceId,
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
        if let Some(var) = prepared.value_var(*candidate)
            && let Some(idx) = formal_arg_index_for_var(prepared, var)
        {
            return arg_location(idx, Some(0), Some(width));
        }
        if let Some(expression) = prepared.addresses().parameter_expression(*candidate) {
            let parameter = match expression
                .parameter_storage
                .and_then(|storage| abi.exact_argument_index_for_storage(storage))
            {
                Some(parameter) => parameter,
                None if abi.is_source_owned() => return unknown_location(),
                None => expression.parameter,
            };
            return arg_location(
                parameter,
                expression.terms.is_empty().then_some(expression.offset),
                expression.terms.is_empty().then_some(width),
            );
        }
        if let Some(address) = exact_constant_value(prepared, *candidate) {
            return global_location(address, Some(0), Some(width));
        }

        if let Some(object_id) = prepared.objects().object_for_value(*candidate, space)
            && let Some(object) = prepared.objects().object(object_id)
        {
            match object.kind {
                ObjectKind::Parameter { index, .. } => {
                    if abi.is_source_owned() {
                        return unknown_location();
                    }
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
                ObjectKind::EscapedUnknown { .. } => {}
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
            .map(|src| {
                classify_memory_access_location_value(prepared, abi, src, space, width, depth + 1)
            })
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
                AdditiveLocationCtx::new(space, width, depth + 1, 1, op),
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
                AdditiveLocationCtx::new(space, width, depth + 1, -1, op),
            )
        }
        _ if op_value_id != value_id => {
            classify_memory_access_location_value(prepared, abi, value_id, space, width, depth + 1)
        }
        _ => unknown_location(),
    }
}

#[derive(Clone, Copy)]
struct AdditiveLocationCtx {
    space: SpaceId,
    width: u32,
    depth: u32,
    sign: i64,
    element_scale: i64,
}

impl AdditiveLocationCtx {
    fn new(space: SpaceId, width: u32, depth: u32, sign: i64, op: &SSAOp) -> Self {
        let element_scale = match op {
            SSAOp::PtrAdd { element_size, .. } | SSAOp::PtrSub { element_size, .. } => {
                *element_size as i64
            }
            _ => 1,
        };
        Self {
            space,
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
    let left_const = summary_const_value(prepared, left_id, ctx.depth);
    let right_const = summary_const_value(prepared, right_id, ctx.depth);

    if let Some(k) = right_const {
        let mut base = classify_memory_access_location_value(
            prepared, abi, left_id, ctx.space, ctx.width, ctx.depth,
        );
        let delta = (k as i64)
            .saturating_mul(ctx.element_scale)
            .saturating_mul(ctx.sign);
        base.range = shifted_range(base.range, delta, ctx.width);
        return base;
    }
    if ctx.sign > 0
        && let Some(k) = left_const
    {
        let mut base = classify_memory_access_location_value(
            prepared, abi, right_id, ctx.space, ctx.width, ctx.depth,
        );
        let delta = (k as i64).saturating_mul(ctx.element_scale);
        base.range = shifted_range(base.range, delta, ctx.width);
        return base;
    }
    unknown_location()
}

fn summary_const_value(prepared: &SsaArtifact, value_id: ValueId, depth: u32) -> Option<u64> {
    match classify_value_operand(prepared, value_id, depth) {
        SummaryOperand::Const(value) => Some(value),
        _ => exact_constant_value(prepared, canonical_root_value(prepared, value_id)),
    }
}

fn collect_call_arg_state(prepared: &SsaArtifact, abi: &AbiProfile) -> CallArgumentState {
    collect_call_arg_state_with_iteration_limit(prepared, abi, 64)
}

fn collect_call_arg_state_with_iteration_limit(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    max_iterations: usize,
) -> CallArgumentState {
    let function = prepared.function();
    let tracked = tracked_call_carriers(prepared, abi);
    let entry_state = tracked
        .iter()
        .map(|carrier| {
            let CallCarrierKey::Storage(storage) = carrier;
            let value = prepared
                .machine_context()
                .abi_model()
                .argument_registers()
                .iter()
                .find(|slot| slot.storage() == *storage)
                .map(|slot| CallCarrierState::EntryArg(slot.index() as usize))
                .unwrap_or(CallCarrierState::Unknown);
            (*carrier, value)
        })
        .collect::<BTreeMap<_, _>>();
    let unknown_state = tracked
        .iter()
        .map(|storage| (*storage, CallCarrierState::Unknown))
        .collect::<BTreeMap<_, _>>();
    let mut in_states = BTreeMap::<u64, CallCarrierMap>::new();
    let mut out_states = BTreeMap::<u64, CallCarrierMap>::new();
    let mut changed = true;
    let mut iterations = 0usize;
    while changed && iterations < max_iterations.max(1) {
        iterations += 1;
        changed = false;
        for &block_addr in function.block_addrs() {
            let preds = function.predecessors(block_addr);
            let mut state = if block_addr == function.entry {
                if preds.is_empty() {
                    entry_state.clone()
                } else {
                    let merged = merge_pred_states(&out_states, &preds, &tracked);
                    merge_call_carrier_states(&entry_state, &merged, &tracked)
                }
            } else if preds.is_empty() {
                unknown_state.clone()
            } else {
                merge_pred_states(&out_states, &preds, &tracked)
            };
            let Some(block) = function.get_block(block_addr) else {
                continue;
            };
            for phi in &block.phis {
                update_call_carrier_state(prepared, abi, &mut state, &phi.dst);
            }
            let old = in_states.insert(block_addr, state.clone());
            if old.as_ref() != Some(&state) {
                changed = true;
            }

            for op in &block.ops {
                apply_call_carrier_transfer(prepared, abi, &mut state, op);
            }
            let new_state = state;
            let old = out_states.insert(block_addr, new_state.clone());
            if old.as_ref() != Some(&new_state) {
                changed = true;
            }
        }
    }

    if changed {
        return unknown_call_argument_state(prepared, abi, false);
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
            update_call_carrier_state(prepared, abi, &mut state, &phi.dst);
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            if op_idx == call_op_idx {
                let args = call_argument_carriers(prepared, abi, call_id)
                    .map(|carriers| {
                        carriers
                            .into_iter()
                            .map(|carrier| match state.get(&carrier) {
                                Some(CallCarrierState::EntryArg(index)) => {
                                    SummaryOperand::Arg(*index)
                                }
                                Some(CallCarrierState::Value(value_id)) => {
                                    classify_value_operand(prepared, *value_id, 0)
                                }
                                Some(CallCarrierState::Unknown) | None => SummaryOperand::Unknown,
                            })
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_else(|| unknown_call_arguments(prepared, abi, call_id));
                by_call.insert(call_id, args);
                break;
            }
            apply_call_carrier_transfer(prepared, abi, &mut state, op);
        }
    }

    for call_id in prepared.call_sites().by_id.keys() {
        by_call
            .entry(*call_id)
            .or_insert_with(|| unknown_call_arguments(prepared, abi, *call_id));
    }

    CallArgumentState {
        by_call,
        converged: true,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CallCarrierState {
    EntryArg(usize),
    Value(ValueId),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum CallCarrierKey {
    Storage(crate::CanonicalStorageId),
}

type CallCarrierMap = BTreeMap<CallCarrierKey, CallCarrierState>;

fn tracked_call_carriers(prepared: &SsaArtifact, abi: &AbiProfile) -> BTreeSet<CallCarrierKey> {
    if !abi.is_source_owned() {
        return BTreeSet::new();
    }
    prepared
        .machine_context()
        .abi_model()
        .argument_registers()
        .iter()
        .map(|slot| CallCarrierKey::Storage(slot.storage()))
        .chain(
            prepared
                .machine_context()
                .call_site_interfaces()
                .values()
                .flat_map(|interface| interface.arguments())
                .map(|argument| CallCarrierKey::Storage(argument.storage())),
        )
        .collect()
}

fn storages_overlap(left: crate::CanonicalStorageId, right: crate::CanonicalStorageId) -> bool {
    if left.space != right.space || left.size == 0 || right.size == 0 {
        return false;
    }
    left.offset
        .checked_add(u64::from(left.size))
        .zip(right.offset.checked_add(u64::from(right.size)))
        .is_none_or(|(left_end, right_end)| left.offset < right_end && right.offset < left_end)
}

fn update_call_carrier_state(
    prepared: &SsaArtifact,
    _abi: &AbiProfile,
    state: &mut CallCarrierMap,
    var: &SSAVar,
) {
    let Some(value_id) = prepared.graph().value_id_for_var(var) else {
        return;
    };
    let storage = prepared
        .graph()
        .value(value_id)
        .and_then(|value| value.canonical_storage);
    for (carrier, value) in state.iter_mut() {
        match *carrier {
            CallCarrierKey::Storage(carrier) => {
                if storage == Some(carrier) {
                    *value = CallCarrierState::Value(value_id);
                } else if storage.is_some_and(|storage| storages_overlap(carrier, storage)) {
                    *value = CallCarrierState::Unknown;
                }
            }
        }
    }
}

fn call_argument_carriers(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    call_id: CallSiteId,
) -> Option<Vec<CallCarrierKey>> {
    let machine = prepared.machine_context();
    if !abi.is_source_owned() {
        return None;
    }
    let interface = machine.call_site_interface(call_id)?;
    interface.is_complete().then(|| {
        interface
            .arguments()
            .iter()
            .map(|argument| CallCarrierKey::Storage(argument.storage()))
            .collect()
    })
}

fn unknown_call_arguments(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
    call_id: CallSiteId,
) -> Vec<SummaryOperand> {
    let count = prepared
        .machine_context()
        .call_site_interface(call_id)
        .map(|interface| interface.arguments().len())
        .unwrap_or_else(|| abi.argument_count());
    (0..count).map(|_| SummaryOperand::Unknown).collect()
}

pub fn observe_call_arguments(
    prepared: &SsaArtifact,
    abi: &AbiProfile,
) -> BTreeMap<CallSiteId, Vec<CallArgObservation>> {
    collect_call_arg_state(prepared, abi)
        .by_call
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
    in_states: &BTreeMap<u64, CallCarrierMap>,
    preds: &[u64],
    tracked: &BTreeSet<CallCarrierKey>,
) -> CallCarrierMap {
    let unknown = tracked
        .iter()
        .map(|storage| (*storage, CallCarrierState::Unknown))
        .collect::<CallCarrierMap>();
    let mut states = preds
        .iter()
        .map(|pred| in_states.get(pred).unwrap_or(&unknown));
    let Some(first) = states.next() else {
        return unknown;
    };
    states.fold(first.clone(), |merged, state| {
        merge_call_carrier_states(&merged, state, tracked)
    })
}

fn merge_call_carrier_states(
    left: &CallCarrierMap,
    right: &CallCarrierMap,
    tracked: &BTreeSet<CallCarrierKey>,
) -> CallCarrierMap {
    tracked
        .iter()
        .map(|storage| {
            let left = left
                .get(storage)
                .copied()
                .unwrap_or(CallCarrierState::Unknown);
            let right = right
                .get(storage)
                .copied()
                .unwrap_or(CallCarrierState::Unknown);
            (
                *storage,
                if left == right {
                    left
                } else {
                    CallCarrierState::Unknown
                },
            )
        })
        .collect()
}

fn classify_return_target(
    prepared: &SsaArtifact,
    block_addr: u64,
    return_op_idx: usize,
    target: &SSAVar,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> SummaryValueObservation {
    if let Some(return_inst) = exact_return_address_use(prepared, block_addr, return_op_idx, target)
        && let Some(observation) = exact_return_boundary_observation(prepared, return_inst, calls)
    {
        return observation;
    }
    match classify_var_operand(prepared, target, 0) {
        SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
        SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
        SummaryOperand::Unknown => SummaryValueObservation::Unknown,
    }
}

fn exact_return_address_use(
    prepared: &SsaArtifact,
    block_addr: u64,
    return_op_idx: usize,
    target: &SSAVar,
) -> Option<crate::graph::InstId> {
    let graph = prepared.graph();
    let inst = graph.inst_id_for_op_site(block_addr, return_op_idx)?;
    let boundary = prepared.facts().boundaries.returns.get(&inst)?;
    let return_address = boundary.return_address?;
    let target_value = graph.value_id_for_var(target)?;
    let use_site = UseSite { inst, input_idx: 0 };
    (return_address.value == target_value
        && graph
            .inst(inst)
            .and_then(|return_inst| return_inst.inputs.first())
            == Some(&target_value)
        && graph.use_sites(target_value).contains(&use_site))
    .then_some(inst)
}

fn exact_return_boundary_observation(
    prepared: &SsaArtifact,
    return_inst: crate::graph::InstId,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> Option<SummaryValueObservation> {
    let expected_storage = exact_function_return_storage(prepared)?;
    let boundary = prepared.facts().boundaries.returns.get(&return_inst)?;
    if !boundary.complete {
        return None;
    }
    let values = boundary
        .values
        .iter()
        .filter_map(|value| match value.slot {
            crate::semantic::CallBoundarySlot::Register { storage, .. }
                if storage == expected_storage =>
            {
                Some(value.value)
            }
            crate::semantic::CallBoundarySlot::Register { .. }
            | crate::semantic::CallBoundarySlot::Stack(_) => None,
        })
        .collect::<Vec<_>>();
    let [value] = values.as_slice() else {
        return None;
    };
    Some(classify_value_observation(prepared, *value, calls))
}

fn classify_value_observation(
    prepared: &SsaArtifact,
    value_id: ValueId,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> SummaryValueObservation {
    match classify_value_operand(prepared, value_id, 0) {
        SummaryOperand::Arg(idx) => SummaryValueObservation::Arg(idx),
        SummaryOperand::Const(value) => SummaryValueObservation::Const(value),
        SummaryOperand::Unknown => {
            if let Some(call_id) = return_call_site_for_value(prepared, value_id, calls)
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
    value_id: ValueId,
    calls: &BTreeMap<CallSiteId, CallObservation>,
) -> Option<CallSiteId> {
    let single_call_site = || {
        (prepared.call_sites().by_id.len() == 1)
            .then(|| prepared.call_sites().by_id.keys().next().copied())
            .flatten()
    };
    let graph = prepared.graph();
    let return_storage = exact_function_return_storage(prepared)?;
    if graph.value(value_id)?.canonical_storage != Some(return_storage) {
        return None;
    }

    let exact_result_matches = |call_site: CallSiteId| {
        let result = calls.get(&call_site)?.result_storage?;
        let value_storage = graph.value(value_id)?.canonical_storage?;
        (result == value_storage).then_some(call_site)
    };

    let Some(def_inst) = graph.def_inst(value_id) else {
        return single_call_site().and_then(exact_result_matches);
    };
    let Some(inst) = graph.inst(def_inst) else {
        return single_call_site().and_then(exact_result_matches);
    };
    let Some(block) = graph.blocks.get(inst.block.0 as usize) else {
        return single_call_site().and_then(exact_result_matches);
    };
    let Some(inst_pos) = block.insts.iter().position(|id| *id == def_inst) else {
        return single_call_site().and_then(exact_result_matches);
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
                return prepared
                    .call_sites()
                    .by_inst
                    .get(&scan_inst_id)
                    .copied()
                    .and_then(exact_result_matches);
            }
            SSAOp::CallDefine { .. } => continue,
            _ => break,
        }
    }

    single_call_site().and_then(exact_result_matches)
}

fn classify_var_operand(prepared: &SsaArtifact, var: &SSAVar, depth: u32) -> SummaryOperand {
    if depth > 8 {
        return SummaryOperand::Unknown;
    }
    let Some(value_id) = prepared.graph().value_id_for_var(var) else {
        return SummaryOperand::Unknown;
    };
    if let Some(bits) = exact_constant_value(prepared, value_id) {
        return SummaryOperand::Const(bits);
    }
    if let Some(idx) = formal_arg_index_for_var(prepared, var) {
        return SummaryOperand::Arg(idx);
    }
    classify_value_operand(prepared, value_id, depth)
}

fn classify_value_operand(prepared: &SsaArtifact, value_id: ValueId, depth: u32) -> SummaryOperand {
    if depth > 8 {
        return SummaryOperand::Unknown;
    }
    let rooted = canonical_root_value(prepared, value_id);
    let Some(root_var) = prepared.value_var(rooted) else {
        return SummaryOperand::Unknown;
    };
    if let Some(bits) = exact_constant_value(prepared, rooted) {
        return SummaryOperand::Const(bits);
    }
    if let Some(idx) = formal_arg_index_for_var(prepared, root_var) {
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
            .map(|src| classify_value_operand(prepared, src, depth + 1))
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
            let left = classify_value_operand(prepared, left_id, depth + 1);
            let right = classify_value_operand(prepared, right_id, depth + 1);
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
    let object = prepared
        .objects()
        .object_for_value(value_id, SpaceId::Ram)?;
    let object = prepared.objects().object(object)?;
    match object.kind {
        ObjectKind::Global { address, .. } => Some(address),
        _ => None,
    }
}

fn exact_constant_value(prepared: &SsaArtifact, value_id: ValueId) -> Option<u64> {
    let value = prepared.graph().value(value_id)?;
    let bits = value.var.constant_bits()?;
    (value.canonical_storage
        == Some(crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Constant,
            offset: bits,
            size: value.var.size,
        }))
    .then_some(bits)
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
        arch.add_register(RegisterDef::new("rsp", 24, 8));
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
        arch.add_register(RegisterDef::new("rsp", 48, 8));
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
            call_carriers_converged: true,
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

    #[test]
    fn exact_return_boundary_ignores_misleading_carrier_names() {
        let mut arch = x86_64_arch();
        for register in &mut arch.registers {
            let renamed = match register.offset {
                0 => Some("rdi"),
                8 => Some("rax"),
                16 => Some("not_the_ip"),
                24 => Some("not_the_sp"),
                _ => None,
            };
            if let Some(renamed) = renamed {
                register.name = renamed.to_string();
            }
        }
        let storage = |offset| crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = crate::SourceFunctionInterface::new_exact(
            b"misleading-return-names".to_vec(),
            "sysv64",
            [],
            crate::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
        .expect("exact function interface");
        let prepared = SsaArtifact::for_decompile_with_interface(
            &[block(
                0x4100,
                vec![
                    R2ILOp::Copy {
                        dst: reg(0, 8),
                        src: c(7, 8),
                    },
                    R2ILOp::Return { target: reg(16, 8) },
                ],
            )],
            Some(&arch),
            interface,
        )
        .expect("exact return artifact");
        let abi =
            AbiProfile::from_machine_context(prepared.machine_context()).expect("source-owned ABI");

        let local = collect_local_summary_facts(&prepared, &abi);

        assert_eq!(
            local.return_observations,
            vec![SummaryValueObservation::Const(7)]
        );
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

    fn register_storage(offset: u64) -> crate::CanonicalStorageId {
        crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    /// Build an untyped fixture whose ABI and call carriers still come from
    /// exact source-owned storage identities. Interproc tests must not recover
    /// those facts from register or calling-convention names.
    fn exact_untyped_artifact(
        blocks: &[R2ILBlock],
        arch: &ArchSpec,
        revision: &[u8],
        calling_convention: &str,
        parameter_offsets: &[u64],
        return_address_offset: u64,
        stack_pointer_offset: u64,
    ) -> SsaArtifact {
        let parameters = parameter_offsets
            .iter()
            .copied()
            .enumerate()
            .map(|(index, offset)| {
                crate::SourceAbiParameterSpec::new(index as u32, register_storage(offset))
            })
            .collect::<Vec<_>>();
        let function_interface = crate::SourceFunctionInterface::new_exact(
            revision.to_vec(),
            calling_convention,
            parameters,
            crate::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| {
            interface.with_return_address_storage(register_storage(return_address_offset))
        })
        .and_then(|interface| {
            interface.with_stack_pointer_storage(register_storage(stack_pointer_offset))
        })
        .expect("exact untyped function interface");
        let call_arguments = || {
            parameter_offsets
                .iter()
                .copied()
                .enumerate()
                .map(|(index, offset)| {
                    crate::SourceCallArgumentSpec::new(index as u32, register_storage(offset))
                })
                .collect::<Vec<_>>()
        };
        let call_site_interfaces = blocks
            .iter()
            .flat_map(|block| {
                block
                    .ops
                    .iter()
                    .enumerate()
                    .filter_map(move |(op_index, op)| match op {
                        R2ILOp::Call { target } | R2ILOp::CallInd { target } => Some(
                            crate::SourceCallSiteInterface::new(
                                revision.to_vec(),
                                crate::SourceCallSiteIdentity::new(
                                    block.addr,
                                    op_index,
                                    crate::CanonicalStorageId::from_varnode(target),
                                ),
                                true,
                                calling_convention,
                                call_arguments(),
                                false,
                                false,
                                crate::SourceCallResult::Void,
                            )
                            .expect("exact untyped callsite interface"),
                        ),
                        _ => None,
                    })
            })
            .collect();

        SsaArtifact::for_decompile_with_interfaces(
            blocks,
            Some(arch),
            Some(function_interface),
            call_site_interfaces,
        )
        .expect("exact untyped SSA artifact")
    }

    fn prepared_owner(addr: u64, arch: &ArchSpec) -> Arc<SsaArtifact> {
        let storage = |offset| crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = crate::SourceFunctionInterface::new_exact(
            b"prepared-interproc-owner".to_vec(),
            "sysv64",
            [crate::SourceAbiParameterSpec::new(0, storage(8))],
            crate::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
        .expect("exact prepared interproc interface");
        Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[block(
                    addr,
                    vec![R2ILOp::Return {
                        target: Varnode::constant(0, 8),
                    }],
                )],
                Some(arch),
                interface,
            )
            .expect("prepared root"),
        )
    }

    #[test]
    fn prepared_summary_set_retains_exact_root_owner() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let weak = Arc::downgrade(&root);
        let independent = prepared_owner(0x4000, &arch);
        let prepared = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: Some("root".to_string()),
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("source-owned summary");

        assert!(prepared.matches_root(&root));
        assert!(!prepared.matches_root(&independent));
        assert!(Arc::ptr_eq(prepared.root(), &root));
        assert_eq!(prepared.owners().len(), 1);
        assert!(
            prepared
                .owner(InterprocFunctionId(0x4000))
                .is_some_and(|owner| Arc::ptr_eq(owner, &root))
        );
        assert_eq!(prepared.report().root, Some(InterprocFunctionId(0x4000)));
        drop(root);
        assert!(
            weak.upgrade()
                .is_some_and(|owner| Arc::ptr_eq(&owner, prepared.root()))
        );
        drop(prepared);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn prepared_summary_set_invalidates_incomplete_source_boundary() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4100, &arch);
        assert!(root.obligations().obligations().values().any(|obligation| {
            obligation.id.kind == crate::SemanticObligationKind::VolatileOrUnknownEffect
        }));

        let prepared = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4100),
                name: None,
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("source-owned summary remains conservatively representable");
        let summary = prepared
            .report()
            .summaries
            .get(&InterprocFunctionId(0x4100))
            .expect("root summary");

        assert!(summary.has_unknown_calls);
        assert!(summary.touches_unknown_memory);
        assert_eq!(summary.return_relation, SummaryReturnRelation::Unknown);
        for kind in [
            SummaryMemoryEffectKind::Read,
            SummaryMemoryEffectKind::Write,
            SummaryMemoryEffectKind::Escape,
        ] {
            assert!(summary.memory_effects.contains(&SummaryMemoryEffect {
                kind,
                location: unknown_location(),
            }));
        }
    }

    #[test]
    fn interproc_report_schema_round_trips_and_validates_nested_stamps() {
        let id = InterprocFunctionId(0x4100);
        let report = InterprocSummarySet {
            schema_version: INTERPROC_SUMMARY_SCHEMA_VERSION,
            root: Some(id),
            summaries: BTreeMap::from([(id, FunctionSemanticSummary::unknown(id, None))]),
            diagnostics: InterprocSummaryDiagnostics::default(),
        };
        assert!(report.has_current_schema());

        let encoded = serde_json::to_value(&report).expect("serialize interproc report");
        assert_eq!(
            encoded
                .get("schema_version")
                .and_then(|value| value.as_u64()),
            Some(u64::from(INTERPROC_SUMMARY_SCHEMA_VERSION))
        );
        let nested = encoded
            .get("summaries")
            .and_then(|value| value.as_object())
            .and_then(|summaries| summaries.values().next())
            .expect("serialized function summary");
        assert_eq!(
            nested
                .get("schema_version")
                .and_then(|value| value.as_u64()),
            Some(u64::from(INTERPROC_SUMMARY_SCHEMA_VERSION))
        );
        let decoded: InterprocSummarySet =
            serde_json::from_value(encoded.clone()).expect("deserialize current report");
        assert_eq!(decoded, report);
        assert!(decoded.has_current_schema());

        for required_field in [
            "linkage",
            "arg_count_hint",
            "memory_effects",
            "transfer_effects",
            "allocation_effects",
            "lifetime_effects",
            "sync_effects",
            "atomic_effects",
        ] {
            let mut missing_field = encoded.clone();
            missing_field
                .get_mut("summaries")
                .and_then(|value| value.as_object_mut())
                .and_then(|summaries| summaries.values_mut().next())
                .and_then(|summary| summary.as_object_mut())
                .expect("serialized function summary object")
                .remove(required_field)
                .unwrap_or_else(|| panic!("serialized summary must contain {required_field}"));
            assert!(
                serde_json::from_value::<InterprocSummarySet>(missing_field).is_err(),
                "current schema must require {required_field}"
            );
        }

        let mut stale_report = encoded.clone();
        stale_report["schema_version"] = serde_json::json!(1);
        let stale_report: InterprocSummarySet =
            serde_json::from_value(stale_report).expect("deserialize explicit old report schema");
        assert!(!stale_report.has_current_schema());

        let mut stale_summary = encoded.clone();
        *stale_summary
            .get_mut("summaries")
            .and_then(|value| value.as_object_mut())
            .and_then(|summaries| summaries.values_mut().next())
            .and_then(|summary| summary.get_mut("schema_version"))
            .expect("nested schema stamp") = serde_json::json!(1);
        let stale_summary: InterprocSummarySet =
            serde_json::from_value(stale_summary).expect("deserialize explicit old nested schema");
        assert!(!stale_summary.has_current_schema());

        let mut unversioned = encoded;
        unversioned
            .as_object_mut()
            .expect("serialized report object")
            .remove("schema_version");
        assert!(serde_json::from_value::<InterprocSummarySet>(unversioned).is_err());
    }

    #[test]
    fn report_only_solver_rejects_stale_or_mislabeled_seeds() {
        let id = InterprocFunctionId(0x4200);
        let mut stale = FunctionSemanticSummary::unknown(id, None);
        stale.schema_version = 1;
        assert_eq!(
            solve_interproc_summary_set(
                &[],
                None,
                None,
                &BTreeMap::from([(id, stale)]),
                InterprocSolveConfig::default(),
            ),
            Err(InterprocSummarySchemaError::FunctionSchemaVersion { id, found: 1 })
        );

        let foreign_id = InterprocFunctionId(0x4300);
        let mislabeled = FunctionSemanticSummary::unknown(foreign_id, None);
        assert_eq!(
            solve_interproc_summary_set(
                &[],
                None,
                None,
                &BTreeMap::from([(id, mislabeled)]),
                InterprocSolveConfig::default(),
            ),
            Err(InterprocSummarySchemaError::FunctionIdentityMismatch {
                key: id,
                summary_id: foreign_id,
            })
        );
    }

    #[test]
    fn prepared_summary_set_ignores_detached_name_advice() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let solve = |name| {
            solve_prepared_interproc_summary_set(
                Arc::clone(&root),
                &[PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name,
                    prepared: &root,
                }],
                InterprocSolveConfig::default(),
            )
            .expect("source-owned summary")
        };

        let first = solve(Some("sym.imp.malloc".to_string()));
        let second = solve(Some("renamed_advisory".to_string()));

        assert_eq!(first.report(), second.report());
        assert_eq!(
            first
                .report()
                .summaries
                .get(&InterprocFunctionId(0x4000))
                .expect("root summary")
                .name,
            None
        );
    }

    #[test]
    fn prepared_summary_set_models_missing_direct_callee_as_unknown() {
        let arch = x86_64_arch();
        let storage = |offset| crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let revision = b"prepared-interproc-missing-direct-callee";
        let function_interface = crate::SourceFunctionInterface::new_exact(
            revision.to_vec(),
            "sysv64",
            [crate::SourceAbiParameterSpec::new(0, storage(8))],
            crate::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
        .expect("exact function interface");
        let target = c(0x5000, 8);
        let call_interface = crate::SourceCallSiteInterface::new(
            revision.to_vec(),
            crate::SourceCallSiteIdentity::new(
                0x4000,
                0,
                crate::CanonicalStorageId::from_varnode(&target),
            ),
            true,
            "sysv64",
            [crate::SourceCallArgumentSpec::new(0, storage(8))],
            false,
            false,
            crate::SourceCallResult::Register {
                storage: storage(0),
            },
        )
        .expect("exact external callsite interface");
        let root = Arc::new(
            SsaArtifact::for_decompile_with_interfaces(
                &[block(
                    0x4000,
                    vec![
                        R2ILOp::Call {
                            target: target.clone(),
                        },
                        R2ILOp::Return { target: reg(0, 8) },
                    ],
                )],
                Some(&arch),
                Some(function_interface),
                vec![call_interface],
            )
            .expect("prepared external-call root"),
        );

        let prepared = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: None,
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("source-owned summary");
        let summary = prepared
            .report()
            .summaries
            .get(&InterprocFunctionId(0x4000))
            .expect("root summary");

        assert_eq!(summary.direct_callees, BTreeSet::from([0x5000]));
        assert!(summary.has_unknown_calls);
        assert!(summary.touches_unknown_memory);
        assert_eq!(summary.return_relation, SummaryReturnRelation::Unknown);
        assert_eq!(
            summary.arg_effects.get(&0),
            Some(&SummaryArgEffect {
                read: true,
                write: true,
                escape: true,
                free: false,
            })
        );
        for kind in [
            SummaryMemoryEffectKind::Read,
            SummaryMemoryEffectKind::Write,
        ] {
            assert!(summary.memory_effects.contains(&SummaryMemoryEffect {
                kind,
                location: unknown_location(),
            }));
        }
        for kind in [
            SummaryMemoryEffectKind::Read,
            SummaryMemoryEffectKind::Write,
            SummaryMemoryEffectKind::Escape,
        ] {
            assert!(summary.memory_effects.contains(&SummaryMemoryEffect {
                kind,
                location: arg_location(0, None, None),
            }));
        }
    }

    #[test]
    fn prepared_summary_set_refuses_foreign_independently_rebuilt_root() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let foreign = prepared_owner(0x4000, &arch);
        let error = solve_prepared_interproc_summary_set(
            root,
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: Some("foreign".to_string()),
                prepared: &foreign,
            }],
            InterprocSolveConfig::default(),
        )
        .expect_err("foreign root must refuse");

        assert_eq!(error, PreparedInterprocSummaryError::ForeignRoot);
    }

    #[test]
    fn prepared_summary_set_refuses_missing_root() {
        let arch = x86_64_arch();
        let error = solve_prepared_interproc_summary_set(
            prepared_owner(0x4000, &arch),
            &[],
            InterprocSolveConfig::default(),
        )
        .expect_err("missing root must refuse");

        assert_eq!(error, PreparedInterprocSummaryError::MissingRoot);
    }

    #[test]
    fn prepared_summary_set_refuses_duplicate_root() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: Some("root-a".to_string()),
                    prepared: &root,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: Some("root-b".to_string()),
                    prepared: &root,
                },
            ],
            InterprocSolveConfig::default(),
        )
        .expect_err("duplicate root must refuse");

        assert_eq!(error, PreparedInterprocSummaryError::DuplicateRoot);
    }

    #[test]
    fn prepared_summary_set_refuses_mislabeled_root() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x5000),
                name: Some("wrong-id".to_string()),
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect_err("mislabeled root must refuse");

        assert_eq!(error, PreparedInterprocSummaryError::MislabeledRoot);
    }

    #[test]
    fn prepared_summary_set_refuses_mislabeled_helper() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let helper = prepared_owner(0x5000, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: Some("root".to_string()),
                    prepared: &root,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x6000),
                    name: Some("wrong-helper-id".to_string()),
                    prepared: &helper,
                },
            ],
            InterprocSolveConfig::default(),
        )
        .expect_err("mislabeled helper must refuse");

        assert_eq!(error, PreparedInterprocSummaryError::MislabeledFunction);
    }

    #[test]
    fn prepared_summary_set_refuses_duplicate_helper_id() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let helper_a = prepared_owner(0x5000, &arch);
        let helper_b = prepared_owner(0x5000, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: Some("root".to_string()),
                    prepared: &root,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x5000),
                    name: Some("helper-a".to_string()),
                    prepared: &helper_a,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x5000),
                    name: Some("helper-b".to_string()),
                    prepared: &helper_b,
                },
            ],
            InterprocSolveConfig::default(),
        )
        .expect_err("duplicate helper id must refuse");

        assert_eq!(error, PreparedInterprocSummaryError::DuplicateFunction);
    }

    #[test]
    fn prepared_summary_set_refuses_manual_helper_owner() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let helper = prepared_owner(0x5000, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: Some("root".to_string()),
                    prepared: &root,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x5000),
                    name: Some("manual-helper".to_string()),
                    prepared: &helper,
                },
            ],
            InterprocSolveConfig::default(),
        )
        .expect_err("manual helper must not become prepared evidence");

        assert_eq!(error, PreparedInterprocSummaryError::ManualFunction);
    }

    #[test]
    fn prepared_summary_set_refuses_overlapping_function_ranges() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let helper = prepared_owner(0x4002, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: None,
                    prepared: &root,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4002),
                    name: None,
                    prepared: &helper,
                },
            ],
            InterprocSolveConfig::default(),
        )
        .expect_err("cross-function block overlap must refuse authoritative evidence");

        assert_eq!(
            error,
            PreparedInterprocSummaryError::OverlappingFunctionBlockRanges
        );
    }

    #[test]
    fn prepared_summary_set_refuses_function_range_overflow() {
        let error =
            validate_interproc_block_ranges([(InterprocFunctionId(u64::MAX - 1), u64::MAX - 1, 4)])
                .expect_err("overflowing block range must fail preflight");

        assert_eq!(
            error,
            PreparedInterprocSummaryError::FunctionBlockRangeOverflow
        );
    }

    #[test]
    fn prepared_summary_set_requires_trusted_root_for_helper_scope() {
        assert_eq!(
            require_trusted_root_for_helper_scope(crate::SsaArtifactProvenanceKind::Manual, 2,),
            Err(PreparedInterprocSummaryError::ManualRootWithHelpers)
        );
        assert_eq!(
            require_trusted_root_for_helper_scope(
                crate::SsaArtifactProvenanceKind::TrustedSource,
                2,
            ),
            Ok(())
        );
    }

    #[test]
    fn prepared_summary_set_does_not_promote_report_only_seeds() {
        let arch = x86_64_arch();
        let root = prepared_owner(0x4000, &arch);
        let root_input = InterprocFunctionInput {
            id: InterprocFunctionId(0x4000),
            name: Some("root".to_string()),
            prepared: root.as_ref(),
        };
        let seed_id = InterprocFunctionId(0x7000);
        let seed = FunctionSemanticSummary::unknown(seed_id, Some("external-seed".to_string()));
        let raw = solve_interproc_summary_set(
            std::slice::from_ref(&root_input),
            Some(&arch),
            Some(InterprocFunctionId(0x4000)),
            &BTreeMap::from([(seed_id, seed)]),
            InterprocSolveConfig::default(),
        )
        .expect("current report-only seed schema");
        let prepared = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: Some("root".to_string()),
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("seedless prepared summary");

        assert!(raw.summaries.contains_key(&seed_id));
        assert!(!prepared.report().summaries.contains_key(&seed_id));
    }

    #[test]
    fn prepared_summary_set_refuses_unknown_source_architecture() {
        let mut arch = x86_64_arch();
        arch.name = "unknown-64-bit-family".to_string();
        let root = prepared_owner(0x4000, &arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: Some("root".to_string()),
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect_err("unknown family must refuse authoritative summary");

        assert_eq!(
            error,
            PreparedInterprocSummaryError::UnknownOrIncoherentMachineContext
        );
    }

    #[test]
    fn prepared_summary_set_refuses_cross_family_helper() {
        let root_arch = x86_64_arch();
        let mut helper_arch = x86_64_arch();
        helper_arch.name = "aarch64".to_string();
        let root = prepared_owner(0x4000, &root_arch);
        let helper = prepared_owner(0x5000, &helper_arch);
        let error = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x4000),
                    name: Some("root".to_string()),
                    prepared: &root,
                },
                PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(0x5000),
                    name: Some("helper".to_string()),
                    prepared: &helper,
                },
            ],
            InterprocSolveConfig::default(),
        )
        .expect_err("cross-family helper must refuse authoritative summary");

        assert_eq!(error, PreparedInterprocSummaryError::ArchitectureMismatch);
    }

    #[test]
    fn prepared_summary_set_refuses_nonconverged_report() {
        let report = InterprocSummarySet {
            diagnostics: InterprocSummaryDiagnostics {
                converged: false,
                ..InterprocSummaryDiagnostics::default()
            },
            ..InterprocSummarySet::default()
        };

        assert_eq!(
            require_converged_summary_report(&report),
            Err(PreparedInterprocSummaryError::NonConverged),
            "partial fixed points must not be sealed"
        );
    }

    #[test]
    fn prepared_summary_uses_exact_abi_carrier_not_callconv_label() {
        let mut arch = x86_64_arch();
        arch.add_register(RegisterDef::new("rcx", 32, 8));
        let storage = |offset| crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = crate::SourceFunctionInterface::new_exact(
            b"prepared-interproc-exact-abi".to_vec(),
            "misleading-sysv-label",
            [crate::SourceAbiParameterSpec::new(0, storage(32))],
            crate::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
        .expect("exact prepared ABI interface");
        let root = Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[block(
                    0x4000,
                    vec![
                        R2ILOp::IntAdd {
                            dst: tmp(0x10, 8),
                            a: reg(32, 8),
                            b: Varnode::constant(4, 8),
                        },
                        R2ILOp::Store {
                            space: SpaceId::Ram,
                            addr: tmp(0x10, 8),
                            val: Varnode::constant(0, 1),
                        },
                        R2ILOp::Return {
                            target: Varnode::constant(0, 8),
                        },
                    ],
                )],
                Some(&arch),
                interface,
            )
            .expect("prepared exact ABI root"),
        );
        let prepared = solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[PreparedInterprocFunctionInput {
                id: InterprocFunctionId(0x4000),
                name: Some("root".to_string()),
                prepared: &root,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("source-owned summary");
        let summary = prepared
            .report()
            .summaries
            .get(&InterprocFunctionId(0x4000))
            .expect("root summary");

        assert!(summary.memory_effects.iter().any(|effect| {
            effect.kind == SummaryMemoryEffectKind::Write
                && effect.location.region == (SummaryMemoryRegion::Arg { index: 0 })
                && effect.location.range.is_some_and(|range| {
                    range.offset_lo == 4 && range.offset_hi == 4 && range.width == Some(1)
                })
        }));
        assert!(
            !summary.memory_effects.iter().any(|effect| {
                effect.location.region == (SummaryMemoryRegion::Arg { index: 3 })
            })
        );
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
    fn report_only_summary_does_not_promote_unbound_call_returns() {
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
        )
        .expect("current report-only seed schema");

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x1000))
                .expect("alloc summary")
                .return_relation,
            SummaryReturnRelation::Unknown
        );
        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x3000))
                .expect("wrapper summary")
                .return_relation,
            SummaryReturnRelation::Unknown
        );
    }

    #[test]
    fn report_only_ip_return_requires_exact_call_result_carrier() {
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
        )
        .expect("current report-only seed schema");

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x1000))
                .expect("alloc summary")
                .return_relation,
            SummaryReturnRelation::Unknown
        );
    }

    #[test]
    fn opaque_single_call_wrapper_does_not_promote_unbound_return() {
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
        )
        .expect("current report-only seed schema");

        assert_eq!(
            set.summaries
                .get(&InterprocFunctionId(0x401000))
                .expect("wrapper summary")
                .return_relation,
            SummaryReturnRelation::Unknown
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
        )
        .expect("current report-only seed schema");

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
        let prepared = exact_untyped_artifact(
            &[blk],
            &arch,
            b"direct-pointer-load",
            "sysv64",
            &[8],
            16,
            24,
        );
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
        )
        .expect("current report-only seed schema");
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
        )
        .expect("current report-only seed schema");
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
        )
        .expect("current report-only seed schema");
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
        let prepared =
            exact_untyped_artifact(&[blk], &arch, b"store-conditional", "sysv64", &[8], 16, 24);
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
        )
        .expect("current report-only seed schema");
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
        let prepared = exact_untyped_artifact(&[blk], &arch, b"atomic-cas", "sysv64", &[8], 16, 24);
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
        )
        .expect("current report-only seed schema");
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
        let blocks = [block(
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
        )];
        let prepared = exact_untyped_artifact(
            &blocks,
            &arch,
            b"symbolic-store-plus",
            "sysv64",
            &[8],
            16,
            24,
        );
        let abi = prepared.abi().expect("exact ABI");
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
        assert_eq!(summary_const_value(&prepared, right_id, 0), Some(2));
        assert_eq!(
            classify_memory_access_location_value(
                &prepared,
                &abi,
                left_id,
                SpaceId::Ram,
                val.size,
                0,
            ),
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
                AdditiveLocationCtx::new(SpaceId::Ram, val.size, 1, 1, op),
            ),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(2, val.size),
            }
        );
        assert_eq!(
            classify_memory_access_location_value(
                &prepared,
                &abi,
                addr_id,
                SpaceId::Ram,
                val.size,
                0,
            ),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(2, val.size),
            }
        );
        let location =
            classify_memory_access_location(&prepared, &abi, addr, SpaceId::Ram, val.size);
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
        let blocks = [block(
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
        )];
        let prepared = exact_untyped_artifact(
            &blocks,
            &arch,
            b"symbolic-store-minus",
            "sysv64",
            &[8],
            16,
            24,
        );
        let abi = prepared.abi().expect("exact ABI");
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
        assert_eq!(summary_const_value(&prepared, right_id, 0), Some(1));
        assert_eq!(
            classify_memory_access_location_value(
                &prepared,
                &abi,
                left_id,
                SpaceId::Ram,
                val.size,
                0,
            ),
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
                AdditiveLocationCtx::new(SpaceId::Ram, val.size, 1, -1, op),
            ),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(-1, val.size),
            }
        );
        assert_eq!(
            classify_memory_access_location_value(
                &prepared,
                &abi,
                addr_id,
                SpaceId::Ram,
                val.size,
                0,
            ),
            SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 0 },
                range: exact_range(-1, val.size),
            }
        );
        let location =
            classify_memory_access_location(&prepared, &abi, addr, SpaceId::Ram, val.size);
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
        let blocks = [block(
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
        )];
        let prepared = exact_untyped_artifact(
            &blocks,
            &arch,
            b"windows-handler-call",
            "windows-x64",
            &[8, 16, 24, 32],
            40,
            48,
        );

        let observations =
            observe_call_arguments(&prepared, &prepared.abi().expect("exact Windows ABI"));
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

    #[test]
    fn call_arg_observer_does_not_reuse_pre_call_carriers_after_call() {
        let arch = windows_x64_arch();
        let blocks = [block(
            0x6000,
            vec![
                R2ILOp::Copy {
                    dst: reg(8, 8),
                    src: c(7, 8),
                },
                R2ILOp::Call {
                    target: c(0x7000, 8),
                },
                R2ILOp::Call {
                    target: c(0x8000, 8),
                },
                R2ILOp::Return { target: c(0, 8) },
            ],
        )];
        let prepared = exact_untyped_artifact(
            &blocks,
            &arch,
            b"windows-two-call-carriers",
            "windows-x64",
            &[8, 16, 24, 32],
            40,
            48,
        );

        let observations =
            observe_call_arguments(&prepared, &prepared.abi().expect("exact Windows ABI"));
        let mut calls = prepared
            .call_sites()
            .by_id
            .iter()
            .map(|(id, call)| (call.at, *id))
            .collect::<Vec<_>>();
        calls.sort_by_key(|(at, _)| *at);
        let first = observations.get(&calls[0].1).expect("first call args");
        let second = observations.get(&calls[1].1).expect("second call args");

        assert_eq!(first.first(), Some(&CallArgObservation::Const(7)));
        assert_eq!(second.first(), Some(&CallArgObservation::Unknown));
    }

    #[test]
    fn volatile_or_unknown_effects_clobber_call_carriers_and_observable_state() {
        let arch = windows_x64_arch();
        let cases = [
            (
                "callother",
                R2ILOp::CallOther {
                    output: None,
                    userop: 7,
                    inputs: Vec::new(),
                },
            ),
            ("unimplemented", R2ILOp::Unimplemented),
            ("cpuid", R2ILOp::CpuId { dst: tmp(0x90, 8) }),
            (
                "new",
                R2ILOp::New {
                    dst: tmp(0x98, 8),
                    src: c(8, 8),
                },
            ),
        ];

        for (label, unknown_op) in cases {
            let prepared = SsaArtifact::for_symbolic(
                &[block(
                    0x6800,
                    vec![
                        R2ILOp::Copy {
                            dst: reg(8, 8),
                            src: c(7, 8),
                        },
                        unknown_op,
                        R2ILOp::Call {
                            target: c(0x7000, 8),
                        },
                        R2ILOp::Return { target: c(0, 8) },
                    ],
                )],
                Some(&arch),
            )
            .unwrap_or_else(|| panic!("{label} SSA"));
            let abi = AbiProfile::windows_x64();
            let observations = observe_call_arguments(&prepared, &abi);
            let call_id = prepared
                .call_sites()
                .by_id
                .keys()
                .next()
                .copied()
                .unwrap_or_else(|| panic!("{label} callsite"));
            let args = observations
                .get(&call_id)
                .unwrap_or_else(|| panic!("{label} args"));
            let local = collect_local_summary_facts(&prepared, &abi);

            assert_eq!(
                args.first(),
                Some(&CallArgObservation::Unknown),
                "{label} must not preserve the pre-effect carrier"
            );
            assert!(local.has_unknown_calls, "{label} must remain observable");
            for kind in [
                SummaryMemoryEffectKind::Read,
                SummaryMemoryEffectKind::Write,
            ] {
                assert!(
                    local.memory_effects.contains(&SummaryMemoryEffect {
                        kind,
                        location: unknown_location(),
                    }),
                    "{label} must carry unknown {kind:?} memory"
                );
            }
        }
    }

    #[test]
    fn volatile_or_unknown_effects_invalidate_pre_effect_return_relations() {
        let arch = windows_x64_arch();
        for (label, return_seed) in [("constant", c(1, 8)), ("entry argument", reg(8, 8))] {
            let prepared = SsaArtifact::for_symbolic(
                &[block(
                    0x6900,
                    vec![
                        R2ILOp::Copy {
                            dst: reg(0, 8),
                            src: return_seed,
                        },
                        R2ILOp::CallOther {
                            output: None,
                            userop: 9,
                            inputs: Vec::new(),
                        },
                        R2ILOp::Return { target: reg(0, 8) },
                    ],
                )],
                Some(&arch),
            )
            .unwrap_or_else(|| panic!("{label} return SSA"));
            let local = collect_local_summary_facts(&prepared, &AbiProfile::windows_x64());
            let summary = initial_summary(InterprocFunctionId(0x6900), None, &local);

            assert_eq!(
                local.return_observations,
                vec![SummaryValueObservation::Unknown],
                "{label} continuity must be erased"
            );
            assert_eq!(summary.return_relation, SummaryReturnRelation::Unknown);
        }
    }

    #[test]
    fn callother_maps_explicit_argument_and_unknown_escape() {
        let arch = x86_64_arch();
        let blocks = [block(
            0x69a0,
            vec![
                R2ILOp::CallOther {
                    output: None,
                    userop: 11,
                    inputs: vec![reg(8, 8)],
                },
                R2ILOp::Return { target: c(0, 8) },
            ],
        )];
        let prepared = exact_untyped_artifact(
            &blocks,
            &arch,
            b"callother-explicit-argument",
            "sysv64",
            &[8],
            16,
            24,
        );
        let local =
            collect_local_summary_facts(&prepared, &prepared.abi().expect("exact SysV ABI"));

        assert_eq!(
            local.arg_effects.get(&0),
            Some(&SummaryArgEffect {
                read: true,
                write: true,
                escape: true,
                free: false,
            })
        );
        assert!(local.memory_effects.contains(&SummaryMemoryEffect {
            kind: SummaryMemoryEffectKind::Escape,
            location: unknown_location(),
        }));
    }

    #[test]
    fn resolved_summary_propagates_transitive_unknown_calls() {
        let mut local = empty_local_summary(BTreeSet::from([0x7100]));
        local.call_observations.insert(
            CallSiteId(0),
            CallObservation {
                target: 0x7100,
                args: Vec::new(),
                result_storage: None,
            },
        );
        let mut callee = FunctionSemanticSummary::unknown(InterprocFunctionId(0x7100), None);
        callee.has_unknown_calls = true;
        let summary = resolve_summary(
            InterprocFunctionId(0x7000),
            None,
            &local,
            &BTreeMap::from([(callee.id, callee)]),
        );

        assert!(summary.has_unknown_calls);
    }

    #[test]
    fn call_return_relation_requires_complete_nonvoid_result_carrier() {
        let arch = x86_64_arch();
        let storage = |offset| crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let revision = b"interproc-exact-call-result";
        let target = c(0x7100, 8);
        let function_interface = || {
            crate::SourceFunctionInterface::new_exact(
                revision.to_vec(),
                "sysv64",
                [],
                crate::SourceFunctionReturn::Register {
                    storage: storage(0),
                },
                [],
            )
            .and_then(|interface| interface.with_return_address_storage(storage(16)))
            .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
            .expect("exact function interface")
        };
        for (label, complete, result, expected) in [
            (
                "exact",
                true,
                crate::SourceCallResult::Register {
                    storage: storage(0),
                },
                SummaryReturnRelation::Const(7),
            ),
            (
                "void",
                true,
                crate::SourceCallResult::Void,
                SummaryReturnRelation::Unknown,
            ),
            (
                "incomplete",
                false,
                crate::SourceCallResult::Register {
                    storage: storage(0),
                },
                SummaryReturnRelation::Unknown,
            ),
            (
                "foreign-carrier",
                true,
                crate::SourceCallResult::Register {
                    storage: storage(8),
                },
                SummaryReturnRelation::Unknown,
            ),
        ] {
            let call_interface = crate::SourceCallSiteInterface::new(
                revision.to_vec(),
                crate::SourceCallSiteIdentity::new(
                    0x7000,
                    0,
                    crate::CanonicalStorageId::from_varnode(&target),
                ),
                complete,
                "sysv64",
                [],
                false,
                false,
                result,
            )
            .expect("callsite interface");
            let prepared = SsaArtifact::for_decompile_with_interfaces(
                &[block(
                    0x7000,
                    vec![
                        R2ILOp::Call {
                            target: target.clone(),
                        },
                        R2ILOp::Return { target: reg(16, 8) },
                    ],
                )],
                Some(&arch),
                Some(function_interface()),
                vec![call_interface],
            )
            .unwrap_or_else(|| panic!("{label} prepared SSA"));
            let abi = AbiProfile::from_machine_context(prepared.machine_context())
                .unwrap_or_else(|| panic!("{label} ABI"));
            let local = collect_local_summary_facts(&prepared, &abi);
            let mut callee = FunctionSemanticSummary::unknown(InterprocFunctionId(0x7100), None);
            callee.return_relation = SummaryReturnRelation::Const(7);
            let summary = resolve_summary(
                InterprocFunctionId(0x7000),
                None,
                &local,
                &BTreeMap::from([(callee.id, callee)]),
            );

            assert_eq!(
                summary.return_relation, expected,
                "{label} call-result authority must control the return relation"
            );
        }
    }

    #[test]
    fn call_carrier_nonconvergence_degrades_all_observations() {
        let arch = x86_64_arch();
        let prepared = SsaArtifact::for_symbolic(
            &[
                block(
                    0x1000,
                    vec![R2ILOp::Branch {
                        target: c(0x1010, 8),
                    }],
                ),
                block(
                    0x1010,
                    vec![
                        R2ILOp::Call {
                            target: c(0x8000, 8),
                        },
                        R2ILOp::Return { target: c(0, 8) },
                    ],
                ),
            ],
            Some(&arch),
        )
        .expect("advisory SSA");
        let state = collect_call_arg_state_with_iteration_limit(
            &prepared,
            &AbiProfile::from_arch(Some(&arch)),
            1,
        );

        assert!(!state.converged);
        assert!(
            state
                .by_call
                .values()
                .flatten()
                .all(|arg| *arg == SummaryOperand::Unknown)
        );

        let mut local = empty_local_summary(BTreeSet::new());
        local.call_carriers_converged = state.converged;
        assert_eq!(
            require_converged_call_carriers(&local),
            Err(PreparedInterprocSummaryError::NonConverged),
            "authoritative sealing must refuse the degraded state"
        );
    }

    #[test]
    fn call_arg_observer_preserves_ambiguous_join_as_unknown() {
        let arch = windows_x64_arch();
        let prepared = SsaArtifact::for_symbolic(
            &[
                block(
                    0x6000,
                    vec![R2ILOp::CBranch {
                        target: c(0x6008, 8),
                        cond: c(1, 1),
                    }],
                ),
                block(
                    0x6004,
                    vec![
                        R2ILOp::Copy {
                            dst: reg(8, 8),
                            src: c(1, 8),
                        },
                        R2ILOp::Branch {
                            target: c(0x600c, 8),
                        },
                    ],
                ),
                block(
                    0x6008,
                    vec![
                        R2ILOp::Copy {
                            dst: reg(8, 8),
                            src: c(2, 8),
                        },
                        R2ILOp::Branch {
                            target: c(0x600c, 8),
                        },
                    ],
                ),
                block(
                    0x600c,
                    vec![
                        R2ILOp::Call {
                            target: c(0x7000, 8),
                        },
                        R2ILOp::Return { target: c(0, 8) },
                    ],
                ),
            ],
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

        assert_eq!(args.first(), Some(&CallArgObservation::Unknown));
    }

    #[test]
    fn source_owned_call_observer_requires_exact_complete_call_carriers() {
        let mut arch = x86_64_arch();
        arch.add_register(RegisterDef::new("rcx", 32, 8));
        let storage = |offset| crate::CanonicalStorageId {
            space: crate::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let revision = b"interproc-exact-call-carriers";
        let function_interface = || {
            crate::SourceFunctionInterface::new_exact(
                revision.to_vec(),
                "sysv64",
                [crate::SourceAbiParameterSpec::new(0, storage(8))],
                crate::SourceFunctionReturn::Void,
                [],
            )
            .and_then(|interface| interface.with_return_address_storage(storage(16)))
            .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
            .expect("exact function interface")
        };
        let target = c(0x7000, 8);
        let blocks = [block(
            0x6000,
            vec![
                R2ILOp::Copy {
                    dst: reg(32, 8),
                    src: c(9, 8),
                },
                R2ILOp::Call {
                    target: target.clone(),
                },
                R2ILOp::Return { target: c(0, 8) },
            ],
        )];
        let call_interface = |complete| {
            crate::SourceCallSiteInterface::new(
                revision.to_vec(),
                crate::SourceCallSiteIdentity::new(
                    0x6000,
                    1,
                    crate::CanonicalStorageId::from_varnode(&target),
                ),
                complete,
                "win64",
                [crate::SourceCallArgumentSpec::new(0, storage(32))],
                false,
                false,
                crate::SourceCallResult::Void,
            )
            .expect("callsite interface")
        };
        let complete = SsaArtifact::for_decompile_with_interfaces(
            &blocks,
            Some(&arch),
            Some(function_interface()),
            vec![call_interface(true)],
        )
        .expect("complete call carrier artifact");
        let incomplete = SsaArtifact::for_decompile_with_interfaces(
            &blocks,
            Some(&arch),
            Some(function_interface()),
            vec![call_interface(false)],
        )
        .expect("incomplete call carrier artifact");
        let complete_abi =
            AbiProfile::from_machine_context(complete.machine_context()).expect("source-owned ABI");
        let incomplete_abi = AbiProfile::from_machine_context(incomplete.machine_context())
            .expect("source-owned ABI");
        let complete_args = observe_call_arguments(&complete, &complete_abi)
            .into_values()
            .next()
            .expect("complete call args");
        let incomplete_args = observe_call_arguments(&incomplete, &incomplete_abi)
            .into_values()
            .next()
            .expect("incomplete call args");

        assert_eq!(complete_args.first(), Some(&CallArgObservation::Const(9)));
        assert_eq!(incomplete_args.first(), Some(&CallArgObservation::Unknown));
    }
}
