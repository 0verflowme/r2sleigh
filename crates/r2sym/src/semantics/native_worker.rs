use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    FunctionSemanticSummary, InterprocFunctionId, SSAOp, SSAVar, SSAVarNameKind, SsaArtifact,
    StackAddressRoot, SummaryAllocationEffect, SummaryArgEffect, SummaryAtomicEffect,
    SummaryLifetimeEffect, SummaryLifetimeOp, SummaryMemoryEffect, SummaryMemoryEffectKind,
    SummaryMemoryLocation, SummaryMemoryRange, SummaryMemoryRegion, SummaryReturnRelation,
    SummarySyncEffect, SummarySyncOp, SummaryTransferEffect, SummaryTransferLength,
};
use serde::{Deserialize, Serialize};

use crate::semantics::{
    NativeLoopSummary, NativeMemoryAccessKind, NativeMemoryAccessSummary, NativeParserKind,
    NativeParserReturnPredicate, NativeParserReturnPredicateKind, NativeParserSummary,
    NativeReductionSummary, NativeRegionSummary, NativeTableWalkSummary, NativeWorkerByteTransform,
    NativeWorkerFold, NativeWorkerFoldOperation, NativeWorkerLoopSummary, NativeWorkerPredicate,
    NativeWorkerRoleIdentity, NativeWorkerRoleSource, NativeWorkerSummary, NativeWorkerSummaryKind,
    NativeWorkerTerminator, ResidualReason, SemanticClaimSource, SemanticEvidence,
    SemanticEvidenceAmbiguity, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason, SummaryRouteCertificate, SummaryRouteCertificateKind,
};

mod hash;

use self::hash::{
    hash_fold_summary, hash_fold_summary_for_island, hash_statistics_worker_summaries,
    hash_table_family_worker_summaries, hash_table_worker_summaries, is_hash_table_family_name,
};

pub(super) const NATIVE_WORKER_SUMMARY_MAX: usize = 32;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NativeWorkerSummarySortKey {
    anchor: u64,
    priority: u8,
    kind: NativeWorkerSummaryKind,
    dst: Option<SummaryMemoryLocation>,
    src: Option<SummaryMemoryLocation>,
    memory: Option<SummaryMemoryLocation>,
    len: Option<SummaryTransferLength>,
    allocation: Option<SummaryAllocationEffect>,
    lifetime: Option<SummaryLifetimeEffect>,
    sync: Option<SummarySyncEffect>,
    atomic: Option<SummaryAtomicEffect>,
    parser: Option<NativeParserSummary>,
    loop_summary: Option<NativeWorkerLoopSummary>,
}

type NativeRegionSummarySortKey = (
    u64,
    NativeWorkerSummaryKind,
    BTreeSet<u64>,
    BTreeSet<u64>,
    BTreeSet<u64>,
    Option<NativeLoopSummary>,
    Vec<NativeMemoryAccessSummary>,
    Vec<NativeReductionSummary>,
    Option<NativeParserSummary>,
);

type NativeRegionSummaryJoinKey = (NativeWorkerSummaryKind, BTreeSet<u64>, Option<u64>);

type NativeMemoryLocationJoinKey = (SummaryMemoryRegion, Option<u32>);
type NativeMemoryAccessJoinKey = (
    NativeMemoryAccessKind,
    Option<NativeMemoryLocationJoinKey>,
    Option<NativeMemoryLocationJoinKey>,
    Option<NativeMemoryLocationJoinKey>,
    Option<SummaryTransferLength>,
    Option<u32>,
);
type LoadSourceAliasKey = (u32, u32, u32);
type LoadSourceAliasValues = BTreeMap<LoadSourceAliasKey, DataflowValue<LoadedSource>>;
type LoadSourceAliasIndex = BTreeMap<String, LoadSourceAliasValues>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum NativeWorkerSummaryApplicabilitySource {
    Structural,
    TypedContext,
    Callsite,
    ConstantPattern,
    LoopShape,
    MemoryEffect,
    TransferEffect,
    AllocationEffect,
    LifetimeEffect,
    SyncEffect,
    AtomicEffect,
    TrustedSymbol,
    NameHint,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeWorkerSummaryApplicability {
    pub normalized_name: Option<String>,
    pub worker_kinds: BTreeSet<NativeWorkerSummaryKind>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub route_evidence_kinds: BTreeSet<NativeWorkerSummaryKind>,
    pub sources: BTreeSet<NativeWorkerSummaryApplicabilitySource>,
    pub evidence: SemanticEvidence,
}

impl NativeWorkerSummaryApplicability {
    pub fn unsupported(normalized_name: Option<String>) -> Self {
        Self {
            normalized_name,
            worker_kinds: BTreeSet::new(),
            route_evidence_kinds: BTreeSet::new(),
            sources: BTreeSet::new(),
            evidence: SemanticEvidence::residual(SemanticEvidenceReason::ResidualSearchRequired),
        }
    }

    pub fn is_supported(&self) -> bool {
        !self.worker_kinds.is_empty()
    }

    pub fn is_name_hint_only(&self) -> bool {
        self.is_supported()
            && self.sources.len() == 1
            && self
                .sources
                .contains(&NativeWorkerSummaryApplicabilitySource::NameHint)
    }

    pub fn has_non_name_evidence(&self) -> bool {
        self.sources
            .iter()
            .any(|source| !matches!(source, NativeWorkerSummaryApplicabilitySource::NameHint))
    }

    pub fn has_route_evidence(&self) -> bool {
        self.is_supported() && self.has_non_name_evidence()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum NativeWorkerSummaryRouteKind {
    Standard,
    DirectSummary,
    PreferFull,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeWorkerSummaryRoutePolicy {
    pub kind: NativeWorkerSummaryRouteKind,
    pub applicability: NativeWorkerSummaryApplicability,
    pub reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub certificate: Option<SummaryRouteCertificate>,
}

impl NativeWorkerSummaryRoutePolicy {
    pub fn should_use_direct_summary(&self) -> bool {
        self.kind == NativeWorkerSummaryRouteKind::DirectSummary
            && self.has_certificate_for_kind(NativeWorkerSummaryRouteKind::DirectSummary)
    }

    pub fn should_prefer_full(&self) -> bool {
        self.kind == NativeWorkerSummaryRouteKind::PreferFull
            && self.has_certificate_for_kind(NativeWorkerSummaryRouteKind::PreferFull)
    }

    pub fn has_route_certificate(&self) -> bool {
        self.has_certificate_for_kind(self.kind)
    }

    fn has_certificate_for_kind(&self, kind: NativeWorkerSummaryRouteKind) -> bool {
        self.certificate.as_ref().is_some_and(|certificate| {
            certificate.route_kind == summary_route_certificate_kind(kind)
                && !matches!(certificate.source, SemanticClaimSource::NameHint)
                && certificate.evidence.is_usable()
        })
    }
}

#[derive(Debug, Clone, Copy)]
struct NativeWorkerSummaryRouteRegistryEntry {
    kind: NativeWorkerSummaryRouteKind,
    reason: &'static str,
    matcher: fn(&str) -> bool,
}

impl NativeWorkerSummaryRouteRegistryEntry {
    fn matches(&self, name: &str) -> bool {
        (self.matcher)(name)
    }
}

const NATIVE_WORKER_SUMMARY_ROUTE_REGISTRY: &[NativeWorkerSummaryRouteRegistryEntry] = &[
    NativeWorkerSummaryRouteRegistryEntry {
        kind: NativeWorkerSummaryRouteKind::PreferFull,
        reason: "semantic policy prefers native control reconstruction",
        matcher: should_prefer_full_native_worker_summary,
    },
    NativeWorkerSummaryRouteRegistryEntry {
        kind: NativeWorkerSummaryRouteKind::DirectSummary,
        reason: "semantic policy selected bounded native-worker summary",
        matcher: is_direct_native_worker_summary_role,
    },
];

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LoopIsland {
    header: u64,
    body: BTreeSet<u64>,
    entries: BTreeSet<u64>,
    exits: BTreeSet<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct LargeCfgMemoryTransfer {
    pub(super) block_addr: u64,
    pub(super) dst_arg: usize,
    pub(super) src_arg: usize,
    pub(super) size: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LoadedSource {
    location: SummaryMemoryLocation,
    size: u32,
    block_addr: u64,
    value_delta: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BytePredicateValue {
    source: LoadedSource,
    predicate: NativeWorkerPredicate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ZeroComparisonValue {
    value: SSAVar,
    branch_when_zero: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RegisterAliasSpec {
    family: String,
    offset_bits: u32,
    width_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DataflowValue<T> {
    Exact(T),
    Unknown,
}

impl<T> DataflowValue<T> {
    fn exact(&self) -> Option<&T> {
        match self {
            Self::Exact(value) => Some(value),
            Self::Unknown => None,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct WorkerDataflowState {
    roots: BTreeMap<SSAVar, DataflowValue<SummaryMemoryRegion>>,
    locations: BTreeMap<SSAVar, DataflowValue<SummaryMemoryLocation>>,
    load_sources: BTreeMap<SSAVar, DataflowValue<LoadedSource>>,
    load_source_aliases: LoadSourceAliasIndex,
    load_source_alias_members: BTreeMap<String, BTreeSet<SSAVar>>,
    control_sources: BTreeMap<SSAVar, DataflowValue<BTreeSet<usize>>>,
    byte_predicates: BTreeMap<SSAVar, DataflowValue<BytePredicateValue>>,
    zero_comparisons: BTreeMap<SSAVar, DataflowValue<ZeroComparisonValue>>,
    stack_values: BTreeMap<StackAddressRoot, DataflowValue<SummaryMemoryRegion>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ParserByteRange {
    lo: u8,
    hi: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScanObservation {
    anchor: u64,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FoldObservation {
    anchor: u64,
    source: LoadedSource,
    accumulator: String,
    operation: NativeWorkerFoldOperation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GlobalLoadObservation {
    anchor: u64,
    source: LoadedSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MemoryWriteObservation {
    anchor: u64,
    location: SummaryMemoryLocation,
    width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OptionStringReadObservation {
    anchor: u64,
    arg: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OptionStringWriteObservation {
    anchor: u64,
    arg: usize,
    value: u8,
    control_args: BTreeSet<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NumericTransformObservation {
    anchor: u64,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: String,
    bits: u32,
    operation: NativeWorkerFoldOperation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BytePredicateObservation {
    anchor: u64,
    source: LoadedSource,
    predicate: NativeWorkerPredicate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ZeroGuardObservation {
    anchor: u64,
    target: Option<u64>,
    value: SSAVar,
    branch_when_zero: bool,
    source: Option<LoadedSource>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReturnObservation {
    anchor: u64,
    field_plus_count: Option<(LoadedSource, String)>,
    negative_count_return: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ParserLoopEvidence {
    anchor: u64,
    byte_values: BTreeSet<u8>,
    byte_ranges: BTreeSet<ParserByteRange>,
    accepts_sign: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct BlockWorkerObservations {
    scans: Vec<ScanObservation>,
    folds: Vec<FoldObservation>,
    global_loads: Vec<GlobalLoadObservation>,
    memory_writes: Vec<MemoryWriteObservation>,
    option_string_reads: Vec<OptionStringReadObservation>,
    option_string_writes: Vec<OptionStringWriteObservation>,
    option_string_branch_controls: BTreeSet<usize>,
    numeric_transforms: Vec<NumericTransformObservation>,
    byte_predicates: Vec<BytePredicateObservation>,
    zero_guards: Vec<ZeroGuardObservation>,
    returns: Vec<ReturnObservation>,
    parser_comparisons: BTreeMap<usize, ParserLoopEvidence>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LoopEffectSummary {
    island: LoopIsland,
    natural_loop: bool,
    scans: Vec<ScanObservation>,
    folds: Vec<FoldObservation>,
    global_loads: Vec<GlobalLoadObservation>,
    memory_writes: Vec<MemoryWriteObservation>,
    numeric_transforms: Vec<NumericTransformObservation>,
    byte_predicates: Vec<BytePredicateObservation>,
    zero_guards: Vec<ZeroGuardObservation>,
    parser_comparisons: BTreeMap<usize, ParserLoopEvidence>,
}

pub(super) fn bounded_evidence() -> SemanticEvidence {
    SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget)
        .with_coverage(SemanticEvidenceCoverage::Bounded)
        .with_provenance(SemanticEvidenceProvenance::Stable)
        .with_budget_limited(true)
}

fn name_hint_evidence() -> SemanticEvidence {
    SemanticEvidence::heuristic(SemanticEvidenceReason::NameHint)
        .with_coverage(SemanticEvidenceCoverage::Bounded)
        .with_provenance(SemanticEvidenceProvenance::Ranked)
        .with_ambiguity(SemanticEvidenceAmbiguity::Ranked)
        .with_budget_limited(true)
}

fn mark_name_hint_summaries(mut summaries: Vec<NativeWorkerSummary>) -> Vec<NativeWorkerSummary> {
    let name_hint = name_hint_evidence();
    for summary in &mut summaries {
        summary.evidence = summary.evidence.combined_with(&name_hint);
    }
    summaries
}

fn applicability_sources_from_summary(
    summary: &FunctionSemanticSummary,
    worker_summaries: &[NativeWorkerSummary],
) -> BTreeSet<NativeWorkerSummaryApplicabilitySource> {
    let mut sources = BTreeSet::new();
    if worker_summaries.iter().any(|worker| {
        worker
            .evidence
            .reasons
            .iter()
            .any(|reason| matches!(reason, SemanticEvidenceReason::NameHint))
    }) {
        sources.insert(NativeWorkerSummaryApplicabilitySource::NameHint);
    }
    if summary.callsite_count > 0 || !summary.direct_callees.is_empty() || summary.has_unknown_calls
    {
        sources.insert(NativeWorkerSummaryApplicabilitySource::Callsite);
    }
    if !summary.transfer_effects.is_empty() {
        sources.insert(NativeWorkerSummaryApplicabilitySource::TransferEffect);
        sources.insert(NativeWorkerSummaryApplicabilitySource::MemoryEffect);
    }
    if !summary.memory_effects.is_empty() {
        sources.insert(NativeWorkerSummaryApplicabilitySource::MemoryEffect);
    }
    if !summary.allocation_effects.is_empty() {
        sources.insert(NativeWorkerSummaryApplicabilitySource::AllocationEffect);
    }
    if !summary.lifetime_effects.is_empty() {
        sources.insert(NativeWorkerSummaryApplicabilitySource::LifetimeEffect);
    }
    if !summary.sync_effects.is_empty() {
        sources.insert(NativeWorkerSummaryApplicabilitySource::SyncEffect);
    }
    if !summary.atomic_effects.is_empty() {
        sources.insert(NativeWorkerSummaryApplicabilitySource::AtomicEffect);
    }
    if worker_summaries.iter().any(|worker| {
        worker.loop_summary.is_some()
            && !worker
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
    }) {
        sources.insert(NativeWorkerSummaryApplicabilitySource::LoopShape);
    }
    if summary.return_relation != SummaryReturnRelation::Unknown {
        sources.insert(NativeWorkerSummaryApplicabilitySource::Structural);
    }
    sources
}

fn applicability_from_worker_summaries(
    summary: &FunctionSemanticSummary,
    worker_summaries: &[NativeWorkerSummary],
) -> NativeWorkerSummaryApplicability {
    let normalized_name = summary
        .name
        .as_deref()
        .and_then(normalize_native_worker_role_name);
    if worker_summaries.is_empty() {
        return NativeWorkerSummaryApplicability::unsupported(normalized_name);
    }
    let worker_kinds = worker_summaries
        .iter()
        .map(|worker| worker.kind)
        .collect::<BTreeSet<_>>();
    let route_evidence_kinds = worker_summaries
        .iter()
        .filter(|worker| worker.is_primary_non_name_summary())
        .map(|worker| worker.kind)
        .collect::<BTreeSet<_>>();
    let sources = applicability_sources_from_summary(summary, worker_summaries);
    let evidence = worker_summaries
        .iter()
        .map(|worker| worker.evidence.clone())
        .reduce(|acc, evidence| acc.combined_with(&evidence))
        .unwrap_or_else(bounded_evidence);
    NativeWorkerSummaryApplicability {
        normalized_name,
        worker_kinds,
        route_evidence_kinds,
        sources,
        evidence,
    }
}

pub fn native_worker_summary_applicability_for_summary(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> NativeWorkerSummaryApplicability {
    let worker_summaries =
        bounded_worker_summaries(summaries_from_interproc_summary_unbounded(anchor, summary));
    applicability_from_worker_summaries(summary, &worker_summaries)
}

pub fn function_semantic_summary_seed_for_name(
    id: InterprocFunctionId,
    name: &str,
) -> Option<FunctionSemanticSummary> {
    let normalized = normalize_semantic_summary_seed_name(name)?;
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
                location: arg_location(0),
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
                location: arg_location(0),
            });
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: arg_location(1),
            });
            transfer_effects.push(SummaryTransferEffect {
                dst: arg_location(0),
                src: arg_location(1),
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
                location: arg_location(0),
            });
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Write,
                location: arg_location(1),
            });
            transfer_effects.push(SummaryTransferEffect {
                dst: arg_location(1),
                src: arg_location(0),
                len: SummaryTransferLength::Arg(2),
            });
            SummaryReturnRelation::Unknown
        }
        "memset" => {
            effect(0, false, true, true, false);
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Write,
                location: arg_location(0),
            });
            SummaryReturnRelation::Arg(0)
        }
        "strlen" => {
            effect(0, true, false, false, false);
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: arg_location(0),
            });
            SummaryReturnRelation::Unknown
        }
        "strcmp" | "memcmp" => {
            effect(0, true, false, false, false);
            effect(1, true, false, false, false);
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: arg_location(0),
            });
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: arg_location(1),
            });
            SummaryReturnRelation::Unknown
        }
        "puts" | "printf" => {
            effect(0, true, false, false, false);
            memory_effects.push(SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: arg_location(0),
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

    Some(FunctionSemanticSummary {
        id,
        name: Some(normalized.to_string()),
        arg_count_hint: Some(match normalized {
            "malloc" | "free" | "strlen" | "puts" | "printf" | "exit" | "retain" | "release"
            | "lock" | "unlock" => 1,
            "calloc" | "strcmp" | "memcmp" => 2,
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

pub fn native_worker_summary_applicability_for_name(
    function_addr: u64,
    name: &str,
) -> NativeWorkerSummaryApplicability {
    let Some(normalized) = normalize_native_worker_role_name(name) else {
        return NativeWorkerSummaryApplicability::unsupported(None);
    };
    let summary =
        function_semantic_summary_seed_for_name(InterprocFunctionId(function_addr), &normalized)
            .unwrap_or_else(|| {
                FunctionSemanticSummary::unknown(
                    InterprocFunctionId(function_addr),
                    Some(normalized),
                )
            });
    native_worker_summary_applicability_for_summary(function_addr, &summary)
}

pub fn native_worker_summary_route_policy_for_name(
    function_addr: u64,
    name: &str,
) -> NativeWorkerSummaryRoutePolicy {
    let applicability = native_worker_summary_applicability_for_name(function_addr, name);
    let requested_name = normalize_native_worker_role_name(name);
    let route_name = requested_name.or_else(|| applicability.normalized_name.clone());
    native_worker_summary_route_policy_from_applicability(
        function_addr,
        route_name.as_deref(),
        applicability,
    )
}

pub fn native_worker_summary_route_policy_for_summary(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> NativeWorkerSummaryRoutePolicy {
    let applicability = native_worker_summary_applicability_for_summary(anchor, summary);
    let route_name = summary
        .name
        .as_deref()
        .and_then(normalize_native_worker_role_name)
        .or_else(|| applicability.normalized_name.clone());
    native_worker_summary_route_policy_from_applicability(
        anchor,
        route_name.as_deref(),
        applicability,
    )
}

fn native_worker_summary_route_policy_from_applicability(
    anchor: u64,
    route_name: Option<&str>,
    mut applicability: NativeWorkerSummaryApplicability,
) -> NativeWorkerSummaryRoutePolicy {
    if !applicability.has_route_evidence() {
        return NativeWorkerSummaryRoutePolicy {
            kind: NativeWorkerSummaryRouteKind::Standard,
            applicability,
            reason: None,
            certificate: None,
        };
    }

    if let Some(entry) = route_name.and_then(native_worker_summary_route_registry_entry) {
        match entry.kind {
            NativeWorkerSummaryRouteKind::PreferFull
                if route_name_has_compatible_evidence(route_name, entry.kind, &applicability) =>
            {
                let certificate = summary_route_certificate(
                    anchor,
                    entry.kind,
                    route_name,
                    &applicability,
                    entry.reason,
                );
                return NativeWorkerSummaryRoutePolicy {
                    kind: entry.kind,
                    applicability,
                    reason: Some(entry.reason.to_string()),
                    certificate: Some(certificate),
                };
            }
            NativeWorkerSummaryRouteKind::DirectSummary
                if route_name_has_compatible_evidence(route_name, entry.kind, &applicability) =>
            {
                applicability
                    .sources
                    .insert(NativeWorkerSummaryApplicabilitySource::TrustedSymbol);
                let certificate = summary_route_certificate(
                    anchor,
                    entry.kind,
                    route_name,
                    &applicability,
                    entry.reason,
                );
                return NativeWorkerSummaryRoutePolicy {
                    kind: entry.kind,
                    applicability,
                    reason: Some(entry.reason.to_string()),
                    certificate: Some(certificate),
                };
            }
            NativeWorkerSummaryRouteKind::PreferFull
            | NativeWorkerSummaryRouteKind::DirectSummary
            | NativeWorkerSummaryRouteKind::Standard => {}
        }
    }

    if route_name.is_some_and(route_name_requires_compatible_route_evidence)
        && !route_name_has_compatible_evidence(
            route_name,
            NativeWorkerSummaryRouteKind::Standard,
            &applicability,
        )
    {
        return NativeWorkerSummaryRoutePolicy {
            kind: NativeWorkerSummaryRouteKind::Standard,
            applicability,
            reason: None,
            certificate: None,
        };
    }

    let certificate = summary_route_certificate(
        anchor,
        NativeWorkerSummaryRouteKind::Standard,
        route_name,
        &applicability,
        "standard summary route with non-name evidence",
    );
    NativeWorkerSummaryRoutePolicy {
        kind: NativeWorkerSummaryRouteKind::Standard,
        applicability,
        reason: None,
        certificate: Some(certificate),
    }
}

fn route_name_requires_compatible_route_evidence(name: &str) -> bool {
    has_native_worker_summary_family(name)
        || native_worker_summary_route_registry_entry(name).is_some()
}

fn route_name_has_compatible_evidence(
    route_name: Option<&str>,
    route_kind: NativeWorkerSummaryRouteKind,
    applicability: &NativeWorkerSummaryApplicability,
) -> bool {
    let Some(route_name) = route_name else {
        return !applicability.route_evidence_kinds.is_empty();
    };
    if !route_name_requires_compatible_route_evidence(route_name) {
        return true;
    }
    applicability
        .route_evidence_kinds
        .iter()
        .any(|kind| route_name_allows_worker_kind(route_name, route_kind, *kind))
}

fn route_name_allows_worker_kind(
    route_name: &str,
    route_kind: NativeWorkerSummaryRouteKind,
    worker_kind: NativeWorkerSummaryKind,
) -> bool {
    if should_prefer_full_native_worker_summary(route_name) {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::DiagnosticWrapper
                | NativeWorkerSummaryKind::ProgramOrchestrator
                | NativeWorkerSummaryKind::FormatArgumentFetch
        );
    }
    if is_direct_allocation_wrapper(route_name) || is_xalloc_family_name(route_name) {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::Allocation
                | NativeWorkerSummaryKind::MemoryTransfer
                | NativeWorkerSummaryKind::StringScan
                | NativeWorkerSummaryKind::MetadataProbe
                | NativeWorkerSummaryKind::DiagnosticWrapper
        );
    }
    if is_direct_version_worker(route_name) || is_version_etc_family_name(route_name) {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::FormatRender
                | NativeWorkerSummaryKind::TableWalk
                | NativeWorkerSummaryKind::OutputStream
        );
    }
    if is_direct_hash_table_worker(route_name) || is_hash_table_family_name(route_name) {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::TableWalk
                | NativeWorkerSummaryKind::MetadataProbe
                | NativeWorkerSummaryKind::MemoryTransfer
        );
    }
    if is_direct_path_or_fts_worker(route_name)
        || is_path_family_name(route_name)
        || is_directory_family_name(route_name)
    {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::PathWalk
                | NativeWorkerSummaryKind::DirectoryTraversal
                | NativeWorkerSummaryKind::SortMerge
                | NativeWorkerSummaryKind::MetadataProbe
                | NativeWorkerSummaryKind::TableWalk
        );
    }
    if is_direct_regex_worker(route_name) || is_parser_family_name(route_name) {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::Parser
                | NativeWorkerSummaryKind::StringScan
                | NativeWorkerSummaryKind::TableWalk
        );
    }
    if is_direct_fileinfo_sort_comparator(route_name) {
        return matches!(
            worker_kind,
            NativeWorkerSummaryKind::MetadataProbe
                | NativeWorkerSummaryKind::SortMerge
                | NativeWorkerSummaryKind::StringScan
        );
    }
    match route_name {
        "argmatch" | "argmatch_exact" | "argmatch_valid" | "argmatch_to_argument" => matches!(
            worker_kind,
            NativeWorkerSummaryKind::TableWalk
                | NativeWorkerSummaryKind::StringScan
                | NativeWorkerSummaryKind::Parser
        ),
        "__xargmatch_internal"
        | "argmatch_invalid"
        | "error_tail"
        | "verror"
        | "verror_at_line"
        | "print_errno_message"
        | "usage" => matches!(
            worker_kind,
            NativeWorkerSummaryKind::DiagnosticWrapper
                | NativeWorkerSummaryKind::OutputStream
                | NativeWorkerSummaryKind::FormatRender
        ),
        "umaxtostr" | "imaxtostr" | "parse_field_count" | "posix2_version" | "next_prime" => {
            matches!(
                worker_kind,
                NativeWorkerSummaryKind::NumericTransform | NativeWorkerSummaryKind::Parser
            )
        }
        _ if matches!(route_kind, NativeWorkerSummaryRouteKind::Standard) => !matches!(
            worker_kind,
            NativeWorkerSummaryKind::MemoryRead
                | NativeWorkerSummaryKind::MemoryWrite
                | NativeWorkerSummaryKind::MemoryEscape
                | NativeWorkerSummaryKind::Unknown
        ),
        _ => false,
    }
}

fn summary_route_certificate(
    anchor: u64,
    kind: NativeWorkerSummaryRouteKind,
    route_name: Option<&str>,
    applicability: &NativeWorkerSummaryApplicability,
    reason: &str,
) -> SummaryRouteCertificate {
    SummaryRouteCertificate::new(
        anchor,
        summary_route_certificate_kind(kind),
        summary_route_claim_source(applicability),
        route_name
            .map(str::to_string)
            .or_else(|| applicability.normalized_name.clone()),
        applicability.route_evidence_kinds.clone(),
        applicability.evidence.clone(),
        reason,
    )
}

fn summary_route_certificate_kind(
    kind: NativeWorkerSummaryRouteKind,
) -> SummaryRouteCertificateKind {
    match kind {
        NativeWorkerSummaryRouteKind::Standard => SummaryRouteCertificateKind::Standard,
        NativeWorkerSummaryRouteKind::DirectSummary => SummaryRouteCertificateKind::DirectSummary,
        NativeWorkerSummaryRouteKind::PreferFull => SummaryRouteCertificateKind::PreferFull,
    }
}

fn summary_route_claim_source(
    applicability: &NativeWorkerSummaryApplicability,
) -> SemanticClaimSource {
    if applicability.is_name_hint_only() {
        SemanticClaimSource::NameHint
    } else if applicability
        .sources
        .contains(&NativeWorkerSummaryApplicabilitySource::TypedContext)
    {
        SemanticClaimSource::TypedContext
    } else if applicability
        .sources
        .contains(&NativeWorkerSummaryApplicabilitySource::Callsite)
    {
        SemanticClaimSource::InterprocSummary
    } else {
        SemanticClaimSource::Summary
    }
}

pub fn direct_native_worker_summary_applicability_for_name(
    function_addr: u64,
    name: &str,
) -> Option<NativeWorkerSummaryApplicability> {
    let policy = native_worker_summary_route_policy_for_name(function_addr, name);
    policy
        .should_use_direct_summary()
        .then_some(policy.applicability)
}

fn native_worker_summary_route_registry_entry(
    name: &str,
) -> Option<&'static NativeWorkerSummaryRouteRegistryEntry> {
    NATIVE_WORKER_SUMMARY_ROUTE_REGISTRY
        .iter()
        .find(|entry| entry.matches(name))
}

fn is_direct_native_worker_summary_role(name: &str) -> bool {
    if is_direct_fileinfo_sort_comparator(name)
        || is_direct_allocation_wrapper(name)
        || is_direct_hash_table_worker(name)
        || is_direct_hot_coreutils_worker(name)
        || is_direct_regex_worker(name)
        || is_direct_version_worker(name)
        || is_direct_path_or_fts_worker(name)
    {
        return true;
    }
    matches!(
        name,
        "alloc_ibuf"
            | "alloc_obuf"
            | "argmatch_to_argument"
            | "check_tuning"
            | "close_stream"
            | "compare"
            | "create_hard_link"
            | "calc_req_mask"
            | "cycle_check"
            | "__do_global_dtors_aux"
            | "deregister_tm_clones"
            | "entry.fini0"
            | "entry0"
            | "error_tail"
            | "exit_cleanup"
            | "emit_verbose"
            | "fadvise"
            | "fd_safer"
            | "file_prefixlen"
            | "filename_unescape"
            | "flush_stdout"
            | "fopen_safer"
            | "get_root_dev_ino"
            | "getuser"
            | "getgroup"
            | "format_user_or_group"
            | "getmonth"
            | "has_xattr"
            | "hwcap_allowed"
            | "imaxtostr"
            | "init_node"
            | "_init"
            | "localtime_rz"
            | "maybe_close_stdout"
            | "memcoll"
            | "mergefiles"
            | "num_processors_via_affinity_mask"
            | "open_safer"
            | "opendirat"
            | "operand_matches"
            | "parse_field_count"
            | "posix2_version"
            | "print_errno_message"
            | "process_signals"
            | "print_stats"
            | "quotearg_free"
            | "reap"
            | "record_file"
            | "register_tm_clones"
            | "rpl_fflush"
            | "rpl_fseeko"
            | "rpl_nanosleep"
            | "xnanosleep"
            | "rpl_obstack_allocated_p"
            | "rpl_obstack_free"
            | "save_token"
            | "set_file_security_ctx"
            | "settimeout"
            | "tzalloc"
            | "umaxtostr"
            | "yesno"
            | "xinmalloc"
            | "xget_version"
            | "xmemcoll"
            | "xnmalloc"
            | "xstrxfrm"
            | "xstrtol_fatal"
            | "xnrealloc"
            | "mcel_tocmp"
    )
}

fn is_direct_version_worker(name: &str) -> bool {
    matches!(
        name,
        "version_etc_arn"
            | "version_etc_ar"
            | "version_etc_va"
            | "version_etc"
            | "emit_bug_reporting_address"
    )
}

fn is_direct_path_or_fts_worker(name: &str) -> bool {
    matches!(
        name,
        "last_component"
            | "mdir_name"
            | "dir_name"
            | "fts_sort"
            | "cwd_advance_fd"
            | "restore_initial_cwd"
            | "clear_files"
            | "write_bytes"
            | "is_utf8_charset"
    )
}

fn is_direct_hash_table_worker(name: &str) -> bool {
    matches!(
        name,
        "hash_clear"
            | "hash_do_for_each"
            | "hash_free"
            | "hash_lookup"
            | "hash_get_entries"
            | "hash_get_max_bucket_length"
            | "hash_get_n_buckets"
            | "hash_get_n_buckets_used"
            | "hash_get_n_entries"
            | "hash_reset_tuning"
            | "hash_table_ok"
            | "heap_insert"
    )
}

fn is_direct_hot_coreutils_worker(name: &str) -> bool {
    matches!(
        name,
        "chown_files"
            | "dopass"
            | "factor_up"
            | "install_file_in_file"
            | "mp_factor_using_pollard_rho"
            | "parse_datetime_body"
            | "posixtime"
            | "process_field"
            | "randperm_new"
            | "readtoken"
            | "readtokens"
            | "read_utmp"
            | "re_string_reconstruct"
            | "seq_fast"
            | "tsort"
            | "who"
            | "yyparse"
    )
}

fn is_direct_regex_worker(name: &str) -> bool {
    matches!(
        name,
        "re_search_internal"
            | "re_compile_internal"
            | "parse_expression"
            | "build_trtable"
            | "update_cur_sifted_state"
            | "transit_state_bkref"
            | "build_charclass"
            | "check_arrival"
            | "peek_token"
            | "build_wcs_upper_buffer"
    )
}

fn is_direct_fileinfo_sort_comparator(name: &str) -> bool {
    name.starts_with("xstrcoll_df_")
        || name.starts_with("rev_xstrcoll_df_")
        || name.starts_with("strcmp_df_")
        || name.starts_with("rev_strcmp_df_")
}

fn is_direct_allocation_wrapper(name: &str) -> bool {
    matches!(
        name,
        "xmalloc"
            | "ximalloc"
            | "xcharalloc"
            | "xrealloc"
            | "xirealloc"
            | "xreallocarray"
            | "rpl_reallocarray"
            | "xnrealloc"
            | "xnmalloc"
            | "xinmalloc"
            | "x2realloc"
            | "x2nrealloc"
            | "xpalloc"
            | "xzalloc"
            | "xizalloc"
            | "xcalloc"
            | "xicalloc"
            | "xmemdup"
            | "ximemdup"
            | "ximemdup0"
            | "xstrdup"
            | "xalloc_die"
    )
}

fn should_prefer_full_native_worker_summary(name: &str) -> bool {
    matches!(name, "diagnose")
}

pub(super) fn role_identity_from_worker_summaries(
    summary_name: Option<&str>,
    worker_summaries: &[NativeWorkerSummary],
) -> Option<Box<NativeWorkerRoleIdentity>> {
    if worker_summaries.is_empty() {
        return None;
    }

    let summary_kinds = worker_summaries
        .iter()
        .map(|summary| summary.kind)
        .collect::<BTreeSet<_>>();
    let primary_summary = worker_summaries
        .iter()
        .filter(|summary| summary.is_primary_non_name_summary())
        .min_by_key(|summary| native_worker_summary_sort_key(summary))
        .or_else(|| {
            worker_summaries
                .iter()
                .filter(|summary| summary.is_primary_render_summary())
                .min_by_key(|summary| native_worker_summary_sort_key(summary))
        })
        .or_else(|| {
            worker_summaries
                .iter()
                .min_by_key(|summary| native_worker_summary_sort_key(summary))
        })?;
    let primary_kind = primary_summary.kind;
    let structural_name = primary_kind.canonical_role_name();
    let source_name = summary_name.and_then(normalize_native_worker_role_name);
    let has_name_hint_summary = worker_summaries.iter().any(|summary| {
        summary
            .evidence
            .reasons
            .iter()
            .any(|reason| matches!(reason, SemanticEvidenceReason::NameHint))
    });
    let source = if source_name.is_some() && has_name_hint_summary {
        NativeWorkerRoleSource::NameHint
    } else if source_name.is_some() {
        NativeWorkerRoleSource::SummarySeed
    } else {
        NativeWorkerRoleSource::Structural
    };
    let role_name = if matches!(source, NativeWorkerRoleSource::NameHint) {
        structural_name
    } else {
        source_name.as_deref().unwrap_or(structural_name)
    }
    .to_string();
    let evidence = worker_summaries
        .iter()
        .map(|summary| summary.evidence.clone())
        .reduce(|acc, evidence| acc.combined_with(&evidence))
        .unwrap_or_else(bounded_evidence);
    Some(Box::new(NativeWorkerRoleIdentity {
        role_name,
        source,
        confidence: evidence.tier,
        source_names: source_name.into_iter().collect(),
        summary_kinds,
        evidence,
    }))
}

fn native_worker_summary_sort_key(summary: &NativeWorkerSummary) -> NativeWorkerSummarySortKey {
    NativeWorkerSummarySortKey {
        anchor: summary.anchor,
        priority: native_worker_summary_priority(summary.kind),
        kind: summary.kind,
        dst: summary.dst,
        src: summary.src,
        memory: summary.memory,
        len: summary.len,
        allocation: summary.allocation,
        lifetime: summary.lifetime,
        sync: summary.sync,
        atomic: summary.atomic,
        parser: summary.parser.clone(),
        loop_summary: summary.loop_summary.clone(),
    }
}

fn native_worker_summary_priority(kind: NativeWorkerSummaryKind) -> u8 {
    match kind {
        NativeWorkerSummaryKind::ProgramOrchestrator
        | NativeWorkerSummaryKind::FileTransfer
        | NativeWorkerSummaryKind::StringScan
        | NativeWorkerSummaryKind::HashFold
        | NativeWorkerSummaryKind::TableWalk
        | NativeWorkerSummaryKind::PathWalk
        | NativeWorkerSummaryKind::DirectoryTraversal
        | NativeWorkerSummaryKind::RecordStream
        | NativeWorkerSummaryKind::FieldSelection
        | NativeWorkerSummaryKind::OutputStream
        | NativeWorkerSummaryKind::FormatRender
        | NativeWorkerSummaryKind::MetadataProbe
        | NativeWorkerSummaryKind::SortMerge
        | NativeWorkerSummaryKind::NumericTransform
        | NativeWorkerSummaryKind::Parser
        | NativeWorkerSummaryKind::DiagnosticWrapper
        | NativeWorkerSummaryKind::FormatArgumentFetch => 0,
        NativeWorkerSummaryKind::Allocation
        | NativeWorkerSummaryKind::Lifetime
        | NativeWorkerSummaryKind::Synchronization
        | NativeWorkerSummaryKind::Atomic => 1,
        NativeWorkerSummaryKind::MemoryTransfer => 2,
        NativeWorkerSummaryKind::MemoryRead | NativeWorkerSummaryKind::MemoryWrite => 3,
        NativeWorkerSummaryKind::MemoryEscape | NativeWorkerSummaryKind::MemoryFree => 4,
        NativeWorkerSummaryKind::Unknown => 5,
    }
}

pub(super) fn bounded_worker_summaries(
    mut summaries: Vec<NativeWorkerSummary>,
) -> Vec<NativeWorkerSummary> {
    summaries.sort_by_key(native_worker_summary_sort_key);
    summaries.dedup();
    if summaries.len() <= NATIVE_WORKER_SUMMARY_MAX {
        return summaries;
    }

    let mut selected = Vec::with_capacity(NATIVE_WORKER_SUMMARY_MAX);
    let mut selected_indices = BTreeSet::new();
    let mut coverage_keys = BTreeSet::new();

    for (idx, summary) in summaries.iter().enumerate() {
        if coverage_keys.insert(native_worker_summary_coverage_key(summary)) {
            selected.push(summary.clone());
            selected_indices.insert(idx);
            if selected.len() == NATIVE_WORKER_SUMMARY_MAX {
                selected.sort_by_key(native_worker_summary_sort_key);
                return selected;
            }
        }
    }

    for (idx, summary) in summaries.iter().enumerate() {
        if selected_indices.insert(idx) {
            selected.push(summary.clone());
            if selected.len() == NATIVE_WORKER_SUMMARY_MAX {
                break;
            }
        }
    }

    selected.sort_by_key(native_worker_summary_sort_key);
    selected
}

fn native_worker_summary_coverage_key(
    summary: &NativeWorkerSummary,
) -> (
    u64,
    NativeWorkerSummaryKind,
    Option<SummaryMemoryLocation>,
    Option<NativeParserKind>,
    Option<u64>,
) {
    (
        summary.anchor,
        summary.kind,
        summary.memory,
        summary.parser.as_ref().map(|parser| parser.kind),
        summary
            .loop_summary
            .as_ref()
            .map(|loop_summary| loop_summary.header),
    )
}

fn native_region_summary_sort_key(summary: &NativeRegionSummary) -> NativeRegionSummarySortKey {
    (
        summary.anchor,
        summary.kind,
        summary.blocks.clone(),
        summary.entries.clone(),
        summary.exits.clone(),
        summary.loop_summary.clone(),
        summary.memory_accesses.clone(),
        summary.reductions.clone(),
        summary.parser.clone(),
    )
}

fn native_region_summary_join_key(summary: &NativeRegionSummary) -> NativeRegionSummaryJoinKey {
    (
        summary.kind,
        summary.blocks.clone(),
        summary
            .loop_summary
            .as_ref()
            .map(|loop_summary| loop_summary.header),
    )
}

fn memory_location_join_key(
    location: Option<SummaryMemoryLocation>,
) -> Option<NativeMemoryLocationJoinKey> {
    location.map(|location| {
        (
            location.region,
            location.range.and_then(|range| range.width),
        )
    })
}

fn memory_access_join_key(access: &NativeMemoryAccessSummary) -> NativeMemoryAccessJoinKey {
    (
        access.kind,
        memory_location_join_key(access.location),
        memory_location_join_key(access.dst),
        memory_location_join_key(access.src),
        access.len,
        access.width,
    )
}

fn join_memory_range(
    left: Option<SummaryMemoryRange>,
    right: Option<SummaryMemoryRange>,
) -> Option<SummaryMemoryRange> {
    match (left, right) {
        (Some(left), Some(right)) => Some(SummaryMemoryRange {
            offset_lo: left.offset_lo.min(right.offset_lo),
            offset_hi: left.offset_hi.max(right.offset_hi),
            width: if left.width == right.width {
                left.width
            } else {
                None
            },
        }),
        _ => None,
    }
}

fn join_memory_location(
    left: Option<SummaryMemoryLocation>,
    right: Option<SummaryMemoryLocation>,
) -> Option<SummaryMemoryLocation> {
    match (left, right) {
        (Some(left), Some(right)) if left.region == right.region => Some(SummaryMemoryLocation {
            region: left.region,
            range: join_memory_range(left.range, right.range),
        }),
        (Some(left), None) => Some(SummaryMemoryLocation {
            region: left.region,
            range: None,
        }),
        (None, Some(right)) => Some(SummaryMemoryLocation {
            region: right.region,
            range: None,
        }),
        _ => None,
    }
}

fn canonical_memory_access_summaries(
    accesses: Vec<NativeMemoryAccessSummary>,
) -> Vec<NativeMemoryAccessSummary> {
    let mut joined = BTreeMap::<NativeMemoryAccessJoinKey, NativeMemoryAccessSummary>::new();
    for access in accesses {
        let key = memory_access_join_key(&access);
        if let Some(existing) = joined.get_mut(&key) {
            existing.location = join_memory_location(existing.location, access.location);
            existing.dst = join_memory_location(existing.dst, access.dst);
            existing.src = join_memory_location(existing.src, access.src);
        } else {
            joined.insert(key, access);
        }
    }
    joined.into_values().collect()
}

fn join_optional_exact<T: Eq>(left: &mut Option<T>, right: Option<T>) {
    match (left.as_ref(), right) {
        (Some(left_value), Some(right_value)) if *left_value == right_value => {}
        (None, None) => {}
        _ => *left = None,
    }
}

fn join_loop_summary(left: &mut Option<NativeLoopSummary>, right: Option<NativeLoopSummary>) {
    match (left.as_mut(), right) {
        (Some(left_summary), Some(right_summary)) => {
            left_summary.header = left_summary.header.min(right_summary.header);
            left_summary.body.extend(right_summary.body);
            left_summary.entries.extend(right_summary.entries);
            left_summary.exits.extend(right_summary.exits);
            join_optional_exact(&mut left_summary.iterations, right_summary.iterations);
            join_optional_exact(&mut left_summary.length_arg, right_summary.length_arg);
            join_optional_exact(&mut left_summary.stride, right_summary.stride);
            join_optional_exact(&mut left_summary.terminator, right_summary.terminator);
        }
        (Some(_), None) => *left = None,
        (None, Some(_)) | (None, None) => {}
    }
}

fn join_region_summary(left: &mut NativeRegionSummary, right: NativeRegionSummary) {
    left.anchor = left.anchor.min(right.anchor);
    left.blocks.extend(right.blocks);
    left.entries.extend(right.entries);
    left.exits.extend(right.exits);
    left.memory_accesses.extend(right.memory_accesses);
    left.memory_accesses =
        canonical_memory_access_summaries(std::mem::take(&mut left.memory_accesses));
    join_loop_summary(&mut left.loop_summary, right.loop_summary);
    left.reductions.extend(right.reductions);
    left.reductions.sort();
    left.reductions.dedup();
    join_optional_exact(&mut left.parser, right.parser);
    left.residual_reasons.extend(right.residual_reasons);
    left.residual_reasons.sort();
    left.residual_reasons.dedup();
    left.evidence = left
        .evidence
        .combined_with(&right.evidence)
        .with_ambiguity(SemanticEvidenceAmbiguity::Bounded);
    left.confidence = left.evidence.tier;
    left.stable_id = stable_region_summary_id(left.anchor, left.kind, &left.blocks);
}

pub(super) fn canonical_region_summaries(
    mut summaries: Vec<NativeRegionSummary>,
) -> Vec<NativeRegionSummary> {
    for summary in &mut summaries {
        summary.memory_accesses =
            canonical_memory_access_summaries(std::mem::take(&mut summary.memory_accesses));
        summary.reductions.sort();
        summary.reductions.dedup();
        summary.residual_reasons.sort();
        summary.residual_reasons.dedup();
    }
    let mut joined = BTreeMap::<NativeRegionSummaryJoinKey, NativeRegionSummary>::new();
    for summary in summaries {
        let key = native_region_summary_join_key(&summary);
        if let Some(existing) = joined.get_mut(&key) {
            join_region_summary(existing, summary);
        } else {
            joined.insert(key, summary);
        }
    }
    let mut summaries = joined.into_values().collect::<Vec<_>>();
    summaries.sort_by_key(native_region_summary_sort_key);
    summaries
}

fn worker_kind_rank(kind: NativeWorkerSummaryKind) -> u64 {
    match kind {
        NativeWorkerSummaryKind::ProgramOrchestrator => 1,
        NativeWorkerSummaryKind::MemoryTransfer => 2,
        NativeWorkerSummaryKind::FileTransfer => 3,
        NativeWorkerSummaryKind::MemoryRead => 4,
        NativeWorkerSummaryKind::MemoryWrite => 5,
        NativeWorkerSummaryKind::MemoryEscape => 6,
        NativeWorkerSummaryKind::MemoryFree => 7,
        NativeWorkerSummaryKind::StringScan => 8,
        NativeWorkerSummaryKind::HashFold => 9,
        NativeWorkerSummaryKind::TableWalk => 10,
        NativeWorkerSummaryKind::PathWalk => 11,
        NativeWorkerSummaryKind::DirectoryTraversal => 12,
        NativeWorkerSummaryKind::RecordStream => 13,
        NativeWorkerSummaryKind::FieldSelection => 14,
        NativeWorkerSummaryKind::OutputStream => 15,
        NativeWorkerSummaryKind::FormatRender => 16,
        NativeWorkerSummaryKind::MetadataProbe => 17,
        NativeWorkerSummaryKind::SortMerge => 18,
        NativeWorkerSummaryKind::NumericTransform => 19,
        NativeWorkerSummaryKind::Parser => 20,
        NativeWorkerSummaryKind::DiagnosticWrapper => 21,
        NativeWorkerSummaryKind::FormatArgumentFetch => 22,
        NativeWorkerSummaryKind::Allocation => 23,
        NativeWorkerSummaryKind::Lifetime => 24,
        NativeWorkerSummaryKind::Synchronization => 25,
        NativeWorkerSummaryKind::Atomic => 26,
        NativeWorkerSummaryKind::Unknown => 27,
    }
}

fn stable_region_summary_id(
    anchor: u64,
    kind: NativeWorkerSummaryKind,
    blocks: &BTreeSet<u64>,
) -> u64 {
    let mut id = anchor.rotate_left(13) ^ (worker_kind_rank(kind) << 56);
    id ^= (blocks.len() as u64).rotate_left(7);
    if let Some(first) = blocks.first() {
        id ^= first.rotate_left(23);
    }
    if let Some(last) = blocks.last() {
        id ^= last.rotate_left(37);
    }
    id
}

fn memory_effect_worker_kind(kind: SummaryMemoryEffectKind) -> NativeWorkerSummaryKind {
    match kind {
        SummaryMemoryEffectKind::Read => NativeWorkerSummaryKind::MemoryRead,
        SummaryMemoryEffectKind::Write => NativeWorkerSummaryKind::MemoryWrite,
        SummaryMemoryEffectKind::Escape => NativeWorkerSummaryKind::MemoryEscape,
        SummaryMemoryEffectKind::Free => NativeWorkerSummaryKind::MemoryFree,
    }
}

pub(super) fn transfer_worker_summary(
    anchor: u64,
    effect: SummaryTransferEffect,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MemoryTransfer,
        dst: Some(effect.dst),
        src: Some(effect.src),
        memory: None,
        len: Some(effect.len),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn memory_worker_summary(anchor: u64, effect: SummaryMemoryEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: memory_effect_worker_kind(effect.kind),
        dst: None,
        src: None,
        memory: Some(effect.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn arg_byte_location(index: usize) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Arg { index },
        range: Some(SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(1),
        }),
    }
}

fn arg_location(index: usize) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Arg { index },
        range: None,
    }
}

fn global_byte_location(address: u64) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Global { address },
        range: Some(SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(1),
        }),
    }
}

fn global_location(address: u64) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Global { address },
        range: None,
    }
}

pub fn normalize_native_worker_role_name(name: &str) -> Option<String> {
    let name = name
        .trim()
        .trim_start_matches("sym.")
        .trim_start_matches("dbg.")
        .trim_start_matches("fcn.")
        .trim_start_matches("sub.")
        .to_ascii_lowercase();
    let name = strip_known_compiler_suffixes(&name).to_string();
    (!name.is_empty()).then_some(name)
}

pub fn is_anonymous_semantic_route_name(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    let base = normalized
        .strip_prefix("sym.")
        .or_else(|| normalized.strip_prefix("dbg."))
        .unwrap_or(&normalized);
    base.starts_with("fcn.")
        || base.starts_with("fcn_")
        || base.starts_with("sub.")
        || base.starts_with("sub_")
}

pub fn is_autogenerated_semantic_function_name(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    let base = normalized
        .strip_prefix("sym.")
        .or_else(|| normalized.strip_prefix("dbg."))
        .unwrap_or(&normalized);
    let underscore_hex_addr = base
        .strip_prefix('_')
        .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_hexdigit()));
    base.is_empty()
        || base.starts_with("fcn.")
        || base.starts_with("fcn_")
        || base.starts_with("sub.")
        || base.starts_with("sub_")
        || base.starts_with("loc.")
        || underscore_hex_addr
}

fn normalize_semantic_summary_name(name: &str) -> Option<String> {
    normalize_native_worker_role_name(name)
}

fn normalize_semantic_summary_seed_name(name: &str) -> Option<&'static str> {
    let normalized_owned = name.trim().to_ascii_lowercase();
    let mut normalized = normalized_owned.as_str();
    semantic_summary_seed_marker(normalized)?;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SemanticSummarySeedMarker {
    Import,
    Relocation,
    Plt,
}

fn semantic_summary_seed_marker(normalized: &str) -> Option<SemanticSummarySeedMarker> {
    if normalized.strip_prefix("sym.imp.").is_some() || normalized.strip_prefix("imp.").is_some() {
        Some(SemanticSummarySeedMarker::Import)
    } else if normalized.strip_prefix("reloc.").is_some() {
        Some(SemanticSummarySeedMarker::Relocation)
    } else if normalized.ends_with("@plt") || normalized.ends_with(".plt") {
        Some(SemanticSummarySeedMarker::Plt)
    } else {
        None
    }
}

fn strip_known_compiler_suffixes(name: &str) -> &str {
    let mut current = name;
    while let Some(stripped) = strip_one_compiler_suffix(current) {
        current = stripped;
    }
    current
}

fn strip_one_compiler_suffix(name: &str) -> Option<&str> {
    if let Some(stripped) = name.strip_suffix(".cold")
        && !stripped.is_empty()
    {
        return Some(stripped);
    }
    for marker in [".isra.", ".constprop.", ".part.", ".llvm."] {
        let Some((prefix, suffix)) = name.rsplit_once(marker) else {
            continue;
        };
        if !prefix.is_empty() && !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()) {
            return Some(prefix);
        }
    }
    None
}

pub fn has_native_worker_summary_family(name: &str) -> bool {
    let Some(name) = normalize_semantic_summary_name(name) else {
        return false;
    };
    if name.starts_with("digest_file")
        || name.starts_with("shaxxx_stream")
        || name.starts_with("find_field")
        || name.starts_with("entry.init")
        || is_quotearg_family_name(&name)
        || is_quoting_options_family_name(&name)
        || is_version_etc_family_name(&name)
        || is_xalloc_family_name(&name)
        || is_hash_table_family_name(&name)
        || is_parser_family_name(&name)
        || is_path_family_name(&name)
        || is_directory_family_name(&name)
        || is_record_memory_family_name(&name)
        || is_fileinfo_sort_comparator_family_name(&name)
    {
        return true;
    }
    matches!(
        name.as_str(),
        "main"
            | "wmain"
            | "diagnose"
            | "usage"
            | "keycompare"
            | "_internal_fnwmatch"
            | "internal_fnwmatch"
            | "fnmatch"
            | "rpl_fnmatch"
            | "getopt"
            | "rpl_getopt"
            | "_getopt_internal"
            | "_getopt_internal_r"
            | "getopt_long"
            | "getopt_long_only"
            | "rpl_getopt_long"
            | "rpl_getopt_long_only"
            | "argmatch"
            | "argmatch_exact"
            | "argmatch_to_argument"
            | "argmatch_invalid"
            | "argmatch_valid"
            | "__xargmatch_internal"
            | "binop"
            | "binary_operator"
            | "unary_operator"
            | "chown_files"
            | "debug_print_current_time"
            | "debug_print_relative_time"
            | "dopass"
            | "factor_using_pollard_rho"
            | "factor_using_pollard_rho2"
            | "factor_up"
            | "install_file_in_file"
            | "mp_factor_using_pollard_rho"
            | "or"
            | "build_charclass"
            | "build_trtable"
            | "build_wcs_upper_buffer"
            | "check_arrival"
            | "parse_expression"
            | "peek_token"
            | "re_compile_internal"
            | "re_search_internal"
            | "randperm_new"
            | "read_utmp"
            | "transit_state_bkref"
            | "update_cur_sifted_state"
            | "seq_fast"
            | "tsort"
            | "three_arguments"
            | "who"
            | "write_counts"
            | "error_tail"
            | "verror_at_line"
            | "verror"
            | "print_errno_message"
            | "printf_fetchargs"
            | "printf_parse"
            | "oprintf_"
            | "print_formatted"
            | "print_esc"
            | "print_xfer_stats"
            | "vasnprintf"
            | "unicode_to_mb"
            | "readlinebuffer_delim"
            | "quotearg_buffer_restyled"
            | "rpl_mbrtoc32"
            | "mbrtoc32"
            | "rpl_mbrtowc"
            | "mbrtowc"
            | "entry0"
            | "entry.fini0"
            | "__do_global_dtors_aux"
            | "register_tm_clones"
            | "deregister_tm_clones"
            | "_init"
            | "xstrtoumax"
            | "xnumtoumax"
            | "xstrtoimax"
            | "vstrtoimax"
            | "strnumcmp"
            | "strintcmp"
            | "rpl_fopen"
            | "fopen_safer"
            | "fd_safer"
            | "rpl_fflush"
            | "open_safer"
            | "openat_safer"
            | "rpl_nanosleep"
            | "xnanosleep"
            | "rpl_fcntl"
            | "settimeout"
            | "freopen_safer"
            | "stream_open"
            | "close_stream"
            | "rpl_fseeko"
            | "maybe_close_stdout"
            | "gettext_quote"
            | "parse_long_options"
            | "parse_gnu_standard_options_only"
            | "human_options"
            | "parse_integer"
            | "parse_number"
            | "traverse_raw_number"
            | "save_token"
            | "filename_unescape"
            | "compare"
            | "memcoll"
            | "xmemcoll"
            | "print_stats"
            | "create_hard_link"
            | "record_file"
            | "calc_req_mask"
            | "reap"
            | "num_processors_via_affinity_mask"
            | "process_signals"
            | "exit_cleanup"
            | "clear_files"
            | "flush_stdout"
            | "indent"
            | "dired_dump_obstack"
            | "format_user_or_group"
            | "xstrtol_fatal"
            | "tzalloc"
            | "xget_version"
            | "rpl_obstack_free"
            | "rpl_obstack_allocated_p"
            | "_obstack_begin_worker"
            | "has_xattr"
            | "check_tuning"
            | "imaxtostr"
            | "umaxtostr"
            | "hwcap_allowed"
            | "file_prefixlen"
            | "getmonth"
            | "operand_matches"
            | "xstrxfrm"
            | "set_file_security_ctx"
            | "localtime_rz"
            | "locale_charset"
            | "current_timespec"
            | "rpl_obstack_memory_used"
            | "alloc_ibuf"
            | "alloc_obuf"
            | "synchronize_output"
            | "copy_with_unblock"
            | "copy_bytes"
            | "iwrite"
            | "iwrite.constprop.0"
            | "translate_charset"
            | "invalidate_cache"
            | "decode_preserve_arg"
            | "skip"
            | "wc"
            | "is_utf8_charset"
            | "canonicalize_filename_mode"
            | "skip_whitespace_run"
            | "scan_mb_blank_field"
            | "scan_mb_delim_field"
            | "mcel_scan"
            | "mcel_cmp"
            | "mcel_tocmp"
            | "mcel_scant"
            | "mcel_scanz"
            | "copy_file_data"
            | "create_hole"
            | "fadvise"
            | "sparse_copy"
            | "copy_internal"
            | "do_copy"
            | "copy"
            | "do_move"
            | "overwrite_ok"
            | "areadlink_with_size"
            | "areadlinkat_with_size"
            | "mfile_name_concat"
            | "set_owner"
            | "set_process_security_ctx"
            | "same_nameat"
            | "force_linkat"
            | "force_symlinkat"
            | "make_dir_parents_private"
            | "backupfile_internal"
            | "utimecmpat"
            | "fdutimensat"
            | "strmode"
            | "do_statx"
            | "getuidbyname"
            | "setlocale_null_r_unlocked"
            | "set_program_name"
            | "defaultcon"
            | "restorecon_private"
            | "restorecon"
            | "re_protect"
            | "renameatu"
            | "streamsavedir"
            | "rpl_fts_open"
            | "rpl_fts_read"
            | "rpl_fts_close"
            | "rpl_getfilecon"
            | "rpl_getfilecon_raw"
            | "rpl_lgetfilecon"
            | "rpl_lgetfilecon_raw"
            | "fts_build"
            | "fts_safe_changedir"
            | "oputs_"
            | "prompt"
            | "cut_characters_mode"
            | "cut_fields_mb_any"
            | "cut_fields_bytesearch"
            | "cut_file"
            | "cut_bytes"
            | "memchr2"
            | "begfield"
            | "limfield"
            | "set_fields"
            | "print_name_with_quoting"
            | "print_long_format"
            | "length_of_file_name_and_frills"
            | "print_filename"
            | "get_funky_string"
            | "abformat_init"
            | "signal_setup"
            | "quote_name_buf"
            | "quote_name"
            | "calculate_columns"
            | "print_current_files"
            | "print_file_name_and_frills"
            | "print_with_separator"
            | "verrevcmp"
            | "filenvercmp"
            | "mpsort_with_tmp"
            | "gobble_file"
            | "print_dir"
            | "extract_dirs_from_files"
            | "sort_files"
            | "fts_sort"
            | "fdfile_has_aclinfo"
            | "human_readable"
            | "__strftime_internal"
            | "nstrftime"
            | "c_nstrftime"
            | "mktime_z"
            | "rm"
            | "close_stdin"
            | "get_dir_status"
            | "leave_dir"
            | "find_entry"
            | "write_line"
            | "mergefps"
            | "sortlines"
            | "pipe_child"
            | "merge"
            | "mergefiles"
            | "cwd_advance_fd"
            | "restore_initial_cwd"
            | "init_node"
            | "fts_stat"
            | "rpl_fts_children"
            | "transfer_entries"
            | "hash_print_statistics"
            | "hash_insert_if_absent"
            | "hash_rehash"
            | "hash_clear"
            | "hash_free"
            | "heap_insert"
            | "heap_remove_top"
            | "hash_remove"
            | "get_root_dev_ino"
            | "getuser"
            | "getgroup"
            | "excise"
            | "fillbuf"
            | "maybe_create_temp"
            | "find_in_given_path"
            | "get_cgroup2_cpu_quota"
            | "isaac_refill"
            | "isaac_seed"
            | "wc_lines_avx2"
            | "wc_lines_avx512"
            | "mbsnwidth"
            | "readtokens0"
            | "add_range_pair"
            | "try_tempname_len"
            | "filesystem_type"
            | "close_stdout"
            | "rpl_fclose"
            | "write_bytes"
            | "yesno"
            | "posix2_version"
            | "error"
            | "error_at_line"
            | "emit_verbose"
            | "file_escape"
            | "zaptemp"
            | "sequential_sort"
            | "open_input_files"
            | "get_meminfo"
            | "randread_new"
            | "randread"
            | "_gl_scratch_buffer_grow"
            | "_gl_scratch_buffer_grow_preserve"
            | "gl_scratch_buffer_grow"
            | "gl_scratch_buffer_grow_preserve"
            | "argv_iter"
            | "argv_iter_init_argv"
            | "argv_iter_init_stream"
            | "argv_iter_n_args"
            | "argv_iter_free"
            | "gregorian_to_persian"
            | "gregorian_to_ethiopian"
            | "next_prime"
            | "num_processors"
            | "physmem_claimable"
            | "rpl_pipe2"
            | "cycle_check_init"
            | "cycle_check"
    )
}

pub fn has_program_orchestrator_summary_family(name: &str) -> bool {
    let Some(name) = normalize_semantic_summary_name(name) else {
        return false;
    };
    matches!(name.as_str(), "main" | "wmain" | "entry0" | "_start")
}

fn is_quotearg_family_name(name: &str) -> bool {
    matches!(
        name,
        "quotearg_buffer_restyled"
            | "quotearg_buffer"
            | "quotearg_alloc"
            | "quotearg_alloc_mem"
            | "quotearg_n_options"
            | "quotearg_n"
            | "quotearg"
            | "quotearg_n_mem"
            | "quotearg_mem"
            | "quotearg_n_style"
            | "quotearg_n_style_mem"
            | "quotearg_style"
            | "quotearg_style_mem"
            | "quotearg_char"
            | "quotearg_char_mem"
            | "quotearg_colon"
            | "quotearg_colon_mem"
            | "quotearg_n_style_colon"
            | "quotearg_n_custom"
            | "quotearg_n_custom_mem"
            | "quotearg_custom"
            | "quotearg_custom_mem"
            | "quote_n_mem"
            | "quote_mem"
            | "quote_n"
            | "quote"
            | "quotearg_free"
    )
}

fn is_quoting_options_family_name(name: &str) -> bool {
    matches!(
        name,
        "clone_quoting_options"
            | "get_quoting_style"
            | "set_quoting_style"
            | "set_char_quoting"
            | "set_quoting_flags"
            | "set_custom_quoting"
    )
}

fn is_version_etc_family_name(name: &str) -> bool {
    matches!(
        name,
        "version_etc_arn"
            | "version_etc_ar"
            | "version_etc_va"
            | "version_etc"
            | "emit_bug_reporting_address"
    )
}

fn is_xalloc_family_name(name: &str) -> bool {
    matches!(
        name,
        "xmalloc"
            | "ximalloc"
            | "xcharalloc"
            | "xrealloc"
            | "xirealloc"
            | "xreallocarray"
            | "xireallocarray"
            | "rpl_reallocarray"
            | "xnrealloc"
            | "xnmalloc"
            | "xinmalloc"
            | "x2realloc"
            | "x2nrealloc"
            | "xpalloc"
            | "xzalloc"
            | "xizalloc"
            | "xcalloc"
            | "xicalloc"
            | "xmemdup"
            | "ximemdup"
            | "ximemdup0"
            | "xstrdup"
            | "xalloc_die"
    )
}

fn is_parser_family_name(name: &str) -> bool {
    matches!(
        name,
        "decode_line_length"
            | "base32_decode_ctx"
            | "base32_encode"
            | "base64_decode_ctx"
            | "base64_encode"
            | "base58_encode_ctx_finalize"
            | "finalize_tab_stops"
            | "list_signal_handling"
            | "operand2sig"
            | "parse_additional_groups"
            | "parse_block_signal_params"
            | "parse_datetime_body"
            | "parse_field_count"
            | "parse_omp_threads"
            | "posixtime"
            | "parse_symbols"
            | "parse_tab_stops"
            | "process_field"
            | "re_string_reconstruct"
            | "readtoken"
            | "readtokens"
            | "sort_args"
            | "str2sig"
            | "strcoll_loop"
            | "yyparse"
    )
}

fn is_path_family_name(name: &str) -> bool {
    matches!(
        name,
        "concatenated_filename"
            | "chdir_long"
            | "last_component"
            | "dir_len"
            | "dir_name"
            | "dir_suffix"
            | "file_name_concat"
            | "find_backup_file_name"
            | "mdir_name"
            | "samedir_template"
            | "target_directory_operand"
    )
}

fn is_directory_family_name(name: &str) -> bool {
    matches!(
        name,
        "enter_dir"
            | "fts_alloc"
            | "fts_compare_ino"
            | "fts_palloc"
            | "opendirat"
            | "rpl_fts_children"
            | "rpl_fts_set"
            | "savedir"
            | "setup_dir"
    )
}

fn is_record_memory_family_name(name: &str) -> bool {
    matches!(
        name,
        "copy_with_block"
            | "full_read"
            | "full_write"
            | "iread"
            | "iread_fullblock"
            | "readtokens0_free"
            | "readtokens0_init"
            | "safe_read"
            | "safe_write"
            | "seek_records"
            | "skip_bytes"
            | "skip_records"
            | "write_output"
            | "write_zeros"
    )
}

fn is_fileinfo_sort_comparator_family_name(name: &str) -> bool {
    name.starts_with("xstrcoll_df_")
        || name.starts_with("rev_xstrcoll_df_")
        || name.starts_with("strcmp_df_")
        || name.starts_with("rev_strcmp_df_")
}

fn semantic_summary_name(summary: &FunctionSemanticSummary) -> Option<String> {
    summary
        .name
        .as_deref()
        .and_then(normalize_semantic_summary_name)
}

fn diagnostic_wrapper_summary(anchor: u64) -> NativeWorkerSummary {
    diagnostic_wrapper_summary_for_arg(anchor, 1)
}

fn diagnostic_wrapper_summary_for_arg(anchor: u64, format_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::DiagnosticWrapper,
        dst: None,
        src: None,
        memory: Some(arg_byte_location(format_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn usage_wrapper_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::DiagnosticWrapper,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn format_argument_fetch_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FormatArgumentFetch,
        dst: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: 1 },
            range: None,
        }),
        src: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: 0 },
            range: None,
        }),
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn table_compare_summary(anchor: u64) -> NativeWorkerSummary {
    table_walk_worker_summary(anchor, 0)
}

fn table_walk_worker_summary(anchor: u64, table_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::TableWalk,
        dst: None,
        src: None,
        memory: Some(arg_location(table_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn global_table_walk_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::TableWalk,
        dst: None,
        src: None,
        memory: Some(global_location(anchor)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn linebuffer_delimiter_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: 0 },
            range: None,
        }),
        src: None,
        memory: Some(arg_byte_location(1)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: Some(1),
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
            return_predicate: None,
        }),
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn string_scan_worker_summary(
    anchor: u64,
    memory_arg: usize,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::StringScan,
        dst: dst_arg.map(|index| SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index },
            range: None,
        }),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: Some(1),
            terminator: Some(terminator),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn token_parser_worker_summary(
    anchor: u64,
    memory_arg: usize,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: dst_arg.map(|index| SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index },
            range: None,
        }),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: Some(memory_arg),
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
            return_predicate: None,
        }),
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::LengthBound),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn global_token_parser_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(global_byte_location(anchor)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: None,
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
            return_predicate: None,
        }),
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn numeric_parser_worker_summary(anchor: u64, memory_arg: usize) -> NativeWorkerSummary {
    numeric_parser_worker_summary_with_dst(anchor, memory_arg, None)
}

fn numeric_parser_worker_summary_with_dst(
    anchor: u64,
    memory_arg: usize,
    dst_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Numeric,
            cursor_arg: Some(memory_arg),
            base: Some(10),
            digit_min: Some(b'0'),
            digit_max: Some(b'9'),
            accepts_sign: true,
            return_predicate: None,
        }),
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn argv_option_parser_worker_summary(anchor: u64, argv_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(arg_location(argv_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: Some(argv_arg),
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
            return_predicate: None,
        }),
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn file_transfer_worker_summary(
    anchor: u64,
    src_arg: usize,
    dst_arg: usize,
    length_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FileTransfer,
        dst: Some(arg_location(dst_arg)),
        src: Some(arg_location(src_arg)),
        memory: None,
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: None,
            terminator: Some(
                length_arg
                    .map(|_| NativeWorkerTerminator::LengthBound)
                    .unwrap_or(NativeWorkerTerminator::Unknown),
            ),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn memory_transfer_worker_summary(
    anchor: u64,
    dst_arg: usize,
    src_arg: usize,
    length_arg: usize,
) -> NativeWorkerSummary {
    transfer_worker_summary(
        anchor,
        SummaryTransferEffect {
            dst: arg_byte_location(dst_arg),
            src: arg_byte_location(src_arg),
            len: SummaryTransferLength::Arg(length_arg),
        },
    )
}

fn path_walk_worker_summary(anchor: u64, path_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::PathWalk,
        dst: None,
        src: None,
        memory: Some(arg_byte_location(path_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::ZeroByte),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn directory_traversal_worker_summary(
    anchor: u64,
    stream_arg: usize,
    entry_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::DirectoryTraversal,
        dst: entry_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(stream_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn record_stream_worker_summary(
    anchor: u64,
    stream_arg: usize,
    dst_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::RecordStream,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(stream_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::ByteEquals(b'\n')),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn field_selection_worker_summary(
    anchor: u64,
    spec_arg: usize,
    dst_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FieldSelection,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(arg_byte_location(spec_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn output_stream_worker_summary(
    anchor: u64,
    memory_arg: usize,
    stream_arg: Option<usize>,
) -> NativeWorkerSummary {
    output_stream_worker_summary_with_len(anchor, memory_arg, stream_arg, None)
}

fn output_stream_worker_summary_with_len(
    anchor: u64,
    memory_arg: usize,
    stream_arg: Option<usize>,
    length_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::OutputStream,
        dst: stream_arg.map(arg_location),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: Some(1),
            terminator: Some(
                length_arg
                    .map(|_| NativeWorkerTerminator::LengthBound)
                    .unwrap_or(NativeWorkerTerminator::ZeroByte),
            ),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn format_render_worker_summary(
    anchor: u64,
    input_arg: usize,
    output_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FormatRender,
        dst: output_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(input_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn metadata_probe_worker_summary(anchor: u64, subject_arg: usize) -> NativeWorkerSummary {
    metadata_probe_worker_summary_for_memory(anchor, Some(arg_location(subject_arg)))
}

fn metadata_probe_worker_summary_for_memory(
    anchor: u64,
    memory: Option<SummaryMemoryLocation>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MetadataProbe,
        dst: None,
        src: None,
        memory,
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn sort_merge_worker_summary(
    anchor: u64,
    files_arg: usize,
    output_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::SortMerge,
        dst: output_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(files_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
            table_walk: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn program_orchestrator_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::ProgramOrchestrator,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn fnmatch_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, None, None),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
    ]
}

fn getopt_worker_summaries(anchor: u64, long_options: bool) -> Vec<NativeWorkerSummary> {
    let mut summaries = vec![
        token_parser_worker_summary(anchor, 2, None, None),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::LengthBound),
    ];
    if long_options {
        summaries.push(table_walk_worker_summary(anchor, 3));
    }
    summaries
}

fn digest_stream_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        record_stream_worker_summary(anchor, 0, None),
    ]
}

fn shaxxx_stream_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![record_stream_worker_summary(anchor, 0, Some(1))]
}

fn expression_evaluator_worker_summaries(
    anchor: u64,
    operator_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    if let Some(operator_arg) = operator_arg {
        return vec![
            token_parser_worker_summary(anchor, operator_arg, None, None),
            table_walk_worker_summary(anchor, operator_arg),
        ];
    }
    vec![
        global_token_parser_worker_summary(anchor),
        global_table_walk_worker_summary(anchor),
    ]
}

fn argmatch_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 1),
        table_walk_worker_summary(anchor, 2),
    ]
}

fn argmatch_to_argument_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 1),
        table_walk_worker_summary(anchor, 2),
        memory_read_worker_summary(anchor, 0, None),
    ]
}

fn xargmatch_internal_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 2),
        table_walk_worker_summary(anchor, 3),
        diagnostic_wrapper_summary_for_arg(anchor, 0),
    ]
}

fn byte_stream_selection_worker_summaries(
    anchor: u64,
    stream_arg: usize,
) -> Vec<NativeWorkerSummary> {
    vec![
        record_stream_worker_summary(anchor, stream_arg, None),
        field_selection_worker_summary(anchor, stream_arg, None),
        output_stream_worker_summary(anchor, stream_arg, None),
    ]
}

fn memchr2_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            0,
            None,
            Some(3),
            NativeWorkerTerminator::LengthBound,
        ),
        token_parser_worker_summary(anchor, 0, None, Some(3)),
    ]
}

fn same_nameat_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 1),
        path_walk_worker_summary(anchor, 3),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
        string_scan_worker_summary(anchor, 3, None, None, NativeWorkerTerminator::ZeroByte),
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 2),
    ]
}

fn file_ownership_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        metadata_probe_worker_summary(anchor, 5),
        metadata_probe_worker_summary(anchor, 7),
    ]
}

fn security_context_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        table_walk_worker_summary(anchor, 4),
    ]
}

fn force_link_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
        metadata_probe_worker_summary(anchor, 4),
    ]
}

fn file_mode_render_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 0, Some(1)),
        output_stream_worker_summary(anchor, 1, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn stat_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        metadata_probe_worker_summary(anchor, 4),
    ]
}

fn multibyte_cell_scan_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            0,
            None,
            Some(1),
            NativeWorkerTerminator::LengthBound,
        ),
        token_parser_worker_summary(anchor, 0, None, Some(1)),
    ]
}

fn global_sort_files_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        sort_merge_worker_summary(anchor, 0, None),
        table_walk_worker_summary(anchor, 0),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn stream_open_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 1, None),
        record_stream_worker_summary(anchor, 0, None),
        output_stream_worker_summary(anchor, 0, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn directory_status_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        directory_traversal_worker_summary(anchor, 0, Some(1)),
        metadata_probe_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
    ]
}

fn file_name_concat_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, None, false),
        output_stream_worker_summary(anchor, 1, Some(2)),
    ]
}

fn user_id_lookup_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn merge_node_init_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        sort_merge_worker_summary(anchor, 1, Some(2)),
        table_walk_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn multibyte_cell_scant_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::Unknown),
        token_parser_worker_summary(anchor, 0, None, None),
    ]
}

fn file_version_compare_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            0,
            None,
            Some(1),
            NativeWorkerTerminator::LengthBound,
        ),
        string_scan_worker_summary(
            anchor,
            2,
            None,
            Some(3),
            NativeWorkerTerminator::LengthBound,
        ),
        numeric_parser_worker_summary(anchor, 0),
        numeric_parser_worker_summary(anchor, 2),
    ]
}

fn file_name_frills_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 0, Some(1)),
        output_stream_worker_summary(anchor, 0, None),
    ]
}

fn tempname_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        metadata_probe_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 2),
        table_walk_worker_summary(anchor, 3),
    ]
}

fn stream_close_worker_summaries(
    anchor: u64,
    stream_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let memory_arg = stream_arg.unwrap_or(0);
    vec![
        output_stream_worker_summary(anchor, memory_arg, stream_arg),
        metadata_probe_worker_summary(anchor, memory_arg),
        global_synchronization_worker_summary(anchor),
    ]
}

fn readlink_alloc_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, Some(2), false),
    ]
}

fn overwrite_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
        metadata_probe_worker_summary(anchor, 4),
    ]
}

fn byte_output_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        output_stream_worker_summary_with_len(anchor, 0, None, Some(1)),
        record_stream_worker_summary(anchor, 0, Some(1)),
    ]
}

fn file_escape_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        format_render_worker_summary(anchor, 0, None),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn temp_cleanup_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 0),
        global_lifetime_worker_summary(anchor),
    ]
}

fn sequential_sort_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        sort_merge_worker_summary(anchor, 0, Some(3)),
        record_stream_worker_summary(anchor, 0, Some(3)),
        table_walk_worker_summary(anchor, 0),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn open_input_files_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 0),
        record_stream_worker_summary(anchor, 0, Some(2)),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn get_meminfo_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        memory_write_worker_summary(anchor, 0, None),
        memory_write_worker_summary(anchor, 1, None),
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
    ]
}

fn randread_new_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, None, false),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn randread_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        memory_write_worker_summary(anchor, 1, Some(2)),
    ]
}

fn scratch_buffer_growth_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        allocation_role_worker_summary(anchor, None, false),
        memory_read_worker_summary(anchor, 0, None),
        memory_write_worker_summary(anchor, 0, None),
    ]
}

fn argv_iterator_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "argv_iter_init_argv" => vec![
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "argv_iter_init_stream" => vec![
            record_stream_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 0, None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "argv_iter" => vec![
            argv_option_parser_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "argv_iter_n_args" => vec![
            metadata_probe_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 0),
        ],
        "argv_iter_free" => vec![
            metadata_probe_worker_summary(anchor, 0),
            global_lifetime_worker_summary(anchor),
        ],
        _ => Vec::new(),
    }
}

fn stream_read_worker_summaries(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    vec![
        record_stream_worker_summary(anchor, memory_arg, None),
        memory_read_worker_summary(anchor, memory_arg, len_arg),
    ]
}

fn stream_write_worker_summaries(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    vec![
        output_stream_worker_summary_with_len(anchor, memory_arg, None, len_arg),
        memory_write_worker_summary(anchor, memory_arg, len_arg),
    ]
}

fn numeric_transform_worker_summary(
    anchor: u64,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: &str,
) -> NativeWorkerSummary {
    numeric_transform_worker_summary_with_loop(
        anchor,
        dst_arg,
        length_arg,
        accumulator.to_string(),
        64,
        NativeWorkerFoldOperation::Add,
        NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: None,
            terminator: Some(
                length_arg
                    .map(|_| NativeWorkerTerminator::LengthBound)
                    .unwrap_or(NativeWorkerTerminator::Unknown),
            ),
            fold: Some(NativeWorkerFold {
                accumulator: accumulator.to_string(),
                bits: 64,
                operation: NativeWorkerFoldOperation::Add,
                predicate: None,
                init: None,
                multiplier: None,
                byte_transform: None,
            }),
            table_walk: None,
        },
    )
}

fn numeric_transform_worker_summary_with_loop(
    anchor: u64,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: String,
    bits: u32,
    operation: NativeWorkerFoldOperation,
    loop_summary: NativeWorkerLoopSummary,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::NumericTransform,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: None,
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            fold: Some(NativeWorkerFold {
                accumulator,
                bits,
                operation,
                predicate: None,
                init: None,
                multiplier: None,
                byte_transform: None,
            }),
            ..loop_summary
        }),
        evidence: bounded_evidence(),
    }
}

fn calendar_transform_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![numeric_transform_worker_summary(
        anchor,
        Some(0),
        None,
        "calendar_date",
    )]
}

fn prime_search_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![numeric_transform_worker_summary(
        anchor,
        None,
        Some(0),
        "prime_candidate",
    )]
}

fn processor_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        numeric_transform_worker_summary(anchor, None, None, "processor_count"),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn pipe_wrapper_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        memory_write_worker_summary(anchor, 0, Some(1)),
    ]
}

fn directory_extraction_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        directory_traversal_worker_summary(anchor, 0, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn quote_name_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 0, Some(2)),
        table_walk_worker_summary(anchor, 3),
    ]
}

fn filename_output_worker_summaries(anchor: u64, filename_arg: usize) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, filename_arg),
        output_stream_worker_summary(anchor, filename_arg, None),
    ]
}

fn vector_line_count_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![record_stream_worker_summary(anchor, 0, None)]
}

fn parser_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "base32_encode" | "base64_encode" => vec![
            memory_transfer_worker_summary(anchor, 2, 0, 1),
            table_walk_worker_summary(anchor, 0),
        ],
        "base32_decode_ctx" | "base64_decode_ctx" => vec![
            memory_transfer_worker_summary(anchor, 3, 1, 2),
            memory_write_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 4, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "base58_encode_ctx_finalize" => vec![
            memory_write_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 1, None),
            memory_write_worker_summary(anchor, 2, None),
            allocation_role_worker_summary(anchor, Some(2), false),
        ],
        "parse_field_count" => vec![
            numeric_parser_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 1, None),
        ],
        "parse_tab_stops" | "parse_additional_groups" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            numeric_parser_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 1, None),
            memory_write_worker_summary(anchor, 2, None),
        ],
        "finalize_tab_stops" | "list_signal_handling" => vec![
            global_table_walk_worker_summary(anchor),
            global_synchronization_worker_summary(anchor),
        ],
        "operand2sig" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            numeric_parser_worker_summary(anchor, 0),
        ],
        "str2sig" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            memory_write_worker_summary(anchor, 1, None),
        ],
        "parse_block_signal_params" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            global_synchronization_worker_summary(anchor),
        ],
        "parse_datetime_body" => vec![
            token_parser_worker_summary(anchor, 1, None, None),
            memory_write_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 2),
            table_walk_worker_summary(anchor, 4),
        ],
        "posixtime" => vec![
            token_parser_worker_summary(anchor, 1, None, Some(2)),
            memory_write_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 2),
        ],
        "readtoken" => vec![
            record_stream_worker_summary(anchor, 0, Some(3)),
            token_parser_worker_summary(anchor, 0, Some(3), Some(2)),
            memory_write_worker_summary(anchor, 3, None),
        ],
        "readtokens" => vec![
            record_stream_worker_summary(anchor, 0, Some(4)),
            token_parser_worker_summary(anchor, 0, Some(4), Some(3)),
            allocation_role_worker_summary(anchor, Some(1), false),
            memory_write_worker_summary(anchor, 4, None),
            memory_write_worker_summary(anchor, 5, None),
        ],
        "process_field" => vec![
            numeric_parser_worker_summary(anchor, 0),
            field_selection_worker_summary(anchor, 1, None),
            format_render_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "parse_symbols" | "sort_args" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "strcoll_loop" => vec![
            string_scan_worker_summary(
                anchor,
                0,
                None,
                Some(1),
                NativeWorkerTerminator::LengthBound,
            ),
            string_scan_worker_summary(
                anchor,
                2,
                None,
                Some(3),
                NativeWorkerTerminator::LengthBound,
            ),
            numeric_transform_worker_summary(anchor, None, None, "collation_order"),
        ],
        _ => vec![numeric_parser_worker_summary(anchor, 0)],
    }
}

fn path_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "last_component" => vec![
            path_walk_worker_summary(anchor, 0),
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::Unknown),
        ],
        "mdir_name" | "dir_name" => vec![
            path_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "file_name_concat" | "concatenated_filename" => file_name_concat_worker_summaries(anchor),
        "find_backup_file_name" => vec![
            path_walk_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 1),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "target_directory_operand" => vec![
            path_walk_worker_summary(anchor, 0),
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "samedir_template" => vec![
            path_walk_worker_summary(anchor, 0),
            output_stream_worker_summary(anchor, 1, None),
        ],
        _ => vec![path_walk_worker_summary(anchor, 0)],
    }
}

fn directory_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "fts_alloc" | "fts_palloc" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "opendirat" => vec![
            path_walk_worker_summary(anchor, 1),
            directory_traversal_worker_summary(anchor, 1, None),
            memory_write_worker_summary(anchor, 3, None),
        ],
        "savedir" | "setup_dir" | "enter_dir" => vec![
            path_walk_worker_summary(anchor, 0),
            directory_traversal_worker_summary(anchor, 0, None),
        ],
        "fts_compare_ino" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            table_walk_worker_summary(anchor, 0),
        ],
        _ => vec![directory_traversal_worker_summary(anchor, 0, None)],
    }
}

fn record_memory_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "full_read" | "safe_read" | "iread" | "iread_fullblock" => {
            stream_read_worker_summaries(anchor, 1, Some(2))
        }
        "full_write" | "safe_write" => stream_write_worker_summaries(anchor, 1, Some(2)),
        "copy_with_block" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            output_stream_worker_summary_with_len(anchor, 1, None, Some(2)),
        ],
        "write_output" => stream_write_worker_summaries(anchor, 0, None),
        "write_zeros" => stream_write_worker_summaries(anchor, 0, Some(1)),
        "readtokens0_init" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "readtokens0_free" => vec![global_lifetime_worker_summary(anchor)],
        "seek_records" | "skip_records" => vec![
            record_stream_worker_summary(anchor, 0, None),
            numeric_transform_worker_summary(anchor, None, Some(1), "record_cursor"),
        ],
        "skip_bytes" => vec![
            memory_read_worker_summary(anchor, 0, Some(1)),
            numeric_transform_worker_summary(anchor, None, Some(1), "byte_cursor"),
        ],
        _ => Vec::new(),
    }
}

fn isaac_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![table_walk_worker_summary(anchor, 0)]
}

fn counter_output_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 5, None),
        output_stream_worker_summary(anchor, 5, None),
    ]
}

fn transfer_stats_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![format_render_worker_summary(anchor, 0, None)]
}

fn allocation_effect(size_arg: Option<usize>, zeroed: bool) -> SummaryAllocationEffect {
    SummaryAllocationEffect { size_arg, zeroed }
}

fn allocation_role_worker_summary(
    anchor: u64,
    size_arg: Option<usize>,
    zeroed: bool,
) -> NativeWorkerSummary {
    allocation_worker_summary(anchor, allocation_effect(size_arg, zeroed))
}

fn memory_read_worker_summary(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MemoryRead,
        dst: None,
        src: None,
        memory: Some(arg_location(memory_arg)),
        len: len_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn memory_write_worker_summary(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MemoryWrite,
        dst: None,
        src: None,
        memory: Some(arg_location(memory_arg)),
        len: len_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn global_lifetime_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Lifetime,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn quote_argument_worker_summaries(
    anchor: u64,
    arg_index: usize,
    len_arg: Option<usize>,
    options_arg: Option<usize>,
    output_arg: Option<usize>,
    allocation_size_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let terminator = if len_arg.is_some() {
        NativeWorkerTerminator::LengthBound
    } else {
        NativeWorkerTerminator::ZeroByte
    };
    let mut summaries = vec![
        string_scan_worker_summary(anchor, arg_index, output_arg, len_arg, terminator),
        format_render_worker_summary(anchor, arg_index, output_arg),
    ];
    if let Some(options_arg) = options_arg {
        summaries.push(table_walk_worker_summary(anchor, options_arg));
    }
    if let Some(size_arg) = allocation_size_arg {
        summaries.push(allocation_role_worker_summary(
            anchor,
            Some(size_arg),
            false,
        ));
    }
    summaries
}

fn quote_custom_worker_summaries(
    anchor: u64,
    left_arg: usize,
    right_arg: usize,
    value_arg: usize,
    len_arg: Option<usize>,
    allocation_size_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = quote_argument_worker_summaries(
        anchor,
        value_arg,
        len_arg,
        None,
        None,
        allocation_size_arg,
    );
    summaries.push(string_scan_worker_summary(
        anchor,
        left_arg,
        None,
        None,
        NativeWorkerTerminator::ZeroByte,
    ));
    summaries.push(string_scan_worker_summary(
        anchor,
        right_arg,
        None,
        None,
        NativeWorkerTerminator::ZeroByte,
    ));
    summaries
}

fn quote_options_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    quote_argument_worker_summaries(anchor, 1, Some(2), Some(3), None, None)
}

fn quote_worker_summaries_for_name(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "quotearg_buffer_restyled" => {
            let mut summaries =
                quote_argument_worker_summaries(anchor, 2, Some(3), None, Some(0), None);
            summaries.push(table_walk_worker_summary(anchor, 6));
            summaries
        }
        "quotearg_buffer" => {
            quote_argument_worker_summaries(anchor, 2, Some(3), Some(4), Some(0), None)
        }
        "quotearg_alloc" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), Some(2), None, Some(1))
        }
        "quotearg_alloc_mem" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), Some(3), None, Some(1))
        }
        "quotearg_n_options" => quote_options_worker_summaries(anchor),
        "quotearg_n" => quote_argument_worker_summaries(anchor, 1, None, None, None, None),
        "quotearg" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_n_mem" => quote_argument_worker_summaries(anchor, 1, Some(2), None, None, None),
        "quotearg_mem" => quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None),
        "quotearg_n_style" => quote_argument_worker_summaries(anchor, 2, None, None, None, None),
        "quotearg_n_style_mem" => {
            quote_argument_worker_summaries(anchor, 2, Some(3), None, None, None)
        }
        "quotearg_style" => quote_argument_worker_summaries(anchor, 1, None, None, None, None),
        "quotearg_style_mem" => {
            quote_argument_worker_summaries(anchor, 1, Some(2), None, None, None)
        }
        "quotearg_char" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_char_mem" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None)
        }
        "quotearg_colon" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_colon_mem" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None)
        }
        "quotearg_n_style_colon" => {
            quote_argument_worker_summaries(anchor, 2, None, None, None, None)
        }
        "quotearg_n_custom" => quote_custom_worker_summaries(anchor, 1, 2, 3, None, None),
        "quotearg_n_custom_mem" => quote_custom_worker_summaries(anchor, 1, 2, 3, Some(4), None),
        "quotearg_custom" => quote_custom_worker_summaries(anchor, 0, 1, 2, None, None),
        "quotearg_custom_mem" => quote_custom_worker_summaries(anchor, 0, 1, 2, Some(3), None),
        "quote_n_mem" => quote_argument_worker_summaries(anchor, 1, Some(2), None, None, None),
        "quote_mem" => quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None),
        "quote_n" => quote_argument_worker_summaries(anchor, 1, None, None, None, None),
        "quote" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_free" => vec![global_lifetime_worker_summary(anchor)],
        _ => Vec::new(),
    }
}

fn quoting_options_worker_summaries_for_name(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "clone_quoting_options" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "get_quoting_style" => vec![table_walk_worker_summary(anchor, 0)],
        "set_quoting_style" | "set_char_quoting" | "set_quoting_flags" => {
            vec![table_walk_worker_summary(anchor, 0)]
        }
        "set_custom_quoting" => vec![
            table_walk_worker_summary(anchor, 0),
            string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
            string_scan_worker_summary(anchor, 2, None, None, NativeWorkerTerminator::ZeroByte),
        ],
        _ => Vec::new(),
    }
}

fn selinux_path_worker_summaries(anchor: u64, path_arg: usize) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, path_arg),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn re_protect_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        path_walk_worker_summary(anchor, 3),
        table_walk_worker_summary(anchor, 4),
        metadata_probe_worker_summary(anchor, 5),
    ]
}

fn rename_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
    ]
}

fn streamsavedir_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        directory_traversal_worker_summary(anchor, 0, None),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn version_etc_worker_summaries(
    anchor: u64,
    authors_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = vec![
        format_render_worker_summary(anchor, 1, Some(0)),
        format_render_worker_summary(anchor, 2, Some(0)),
        format_render_worker_summary(anchor, 3, Some(0)),
    ];
    if let Some(authors_arg) = authors_arg {
        summaries.push(table_walk_worker_summary(anchor, authors_arg));
    }
    summaries
}

fn xalloc_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "xalloc_die" => vec![diagnostic_wrapper_summary(anchor)],
        "xmalloc" | "ximalloc" | "xcharalloc" => {
            vec![allocation_role_worker_summary(anchor, Some(0), false)]
        }
        "xzalloc" | "xizalloc" => vec![allocation_role_worker_summary(anchor, Some(0), true)],
        "xcalloc" | "xicalloc" => vec![allocation_role_worker_summary(anchor, None, true)],
        "xnmalloc" | "xinmalloc" => vec![allocation_role_worker_summary(anchor, None, false)],
        "xrealloc" | "xirealloc" => vec![
            allocation_role_worker_summary(anchor, Some(1), false),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "xreallocarray" | "xireallocarray" | "rpl_reallocarray" | "xnrealloc" => vec![
            allocation_role_worker_summary(anchor, None, false),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "x2realloc" => vec![
            allocation_role_worker_summary(anchor, None, false),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "x2nrealloc" => vec![
            allocation_role_worker_summary(anchor, Some(2), false),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "xpalloc" => vec![
            allocation_role_worker_summary(anchor, Some(4), false),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "xmemdup" | "ximemdup" | "ximemdup0" => vec![
            memory_read_worker_summary(anchor, 0, Some(1)),
            allocation_role_worker_summary(anchor, Some(1), false),
        ],
        "xstrdup" => vec![
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
            allocation_role_worker_summary(anchor, None, false),
        ],
        _ => Vec::new(),
    }
}

fn multibyte_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 1, Some(0), Some(2)),
        string_scan_worker_summary(
            anchor,
            1,
            Some(0),
            Some(2),
            NativeWorkerTerminator::LengthBound,
        ),
    ]
}

fn printf_parser_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, None, None),
        table_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 0, None),
    ]
}

fn regex_engine_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "re_search_internal" => vec![
            table_walk_worker_summary(anchor, 0),
            string_scan_worker_summary(
                anchor,
                1,
                Some(2),
                None,
                NativeWorkerTerminator::LengthBound,
            ),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "re_compile_internal" => vec![
            table_walk_worker_summary(anchor, 0),
            string_scan_worker_summary(
                anchor,
                1,
                Some(2),
                None,
                NativeWorkerTerminator::LengthBound,
            ),
            token_parser_worker_summary(anchor, 1, None, Some(2)),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "parse_expression" => vec![
            token_parser_worker_summary(anchor, 0, None, Some(1)),
            table_walk_worker_summary(anchor, 2),
            memory_write_worker_summary(anchor, 2, None),
        ],
        "build_trtable" => vec![
            table_walk_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 1),
            memory_write_worker_summary(anchor, 1, None),
        ],
        "update_cur_sifted_state" => vec![
            table_walk_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 1),
            numeric_transform_worker_summary(anchor, Some(2), None, "regex_sifted_state"),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "transit_state_bkref" => vec![
            table_walk_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 1),
            metadata_probe_worker_summary(anchor, 2),
            memory_write_worker_summary(anchor, 1, None),
        ],
        "build_charclass" => vec![
            token_parser_worker_summary(anchor, 1, None, None),
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "check_arrival" => vec![
            table_walk_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 1),
            numeric_transform_worker_summary(anchor, Some(2), None, "regex_arrival"),
        ],
        "peek_token" => vec![
            token_parser_worker_summary(anchor, 1, None, Some(2)),
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "build_wcs_upper_buffer" => vec![
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::LengthBound),
            memory_write_worker_summary(anchor, 0, None),
            token_parser_worker_summary(anchor, 0, None, None),
        ],
        _ => Vec::new(),
    }
}

fn libc_file_wrapper_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 1, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn locale_buffer_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        string_scan_worker_summary(
            anchor,
            1,
            Some(1),
            Some(2),
            NativeWorkerTerminator::LengthBound,
        ),
        memory_write_worker_summary(anchor, 1, Some(2)),
    ]
}

fn gettext_quote_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 1),
    ]
}

fn program_name_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        global_synchronization_worker_summary(anchor),
    ]
}

fn time_format_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 0, Some(1)),
        metadata_probe_worker_summary(anchor, 3),
    ]
}

fn time_zone_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
        numeric_transform_worker_summary(anchor, Some(1), None, "time_value"),
    ]
}

fn yesno_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, None, None),
        record_stream_worker_summary(anchor, 0, None),
    ]
}

fn token_buffer_finalize_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        memory_write_worker_summary(anchor, 0, None),
        global_lifetime_worker_summary(anchor),
    ]
}

fn filename_unescape_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, Some(0), Some(1)),
        string_scan_worker_summary(
            anchor,
            0,
            Some(0),
            Some(1),
            NativeWorkerTerminator::LengthBound,
        ),
        memory_write_worker_summary(anchor, 0, Some(1)),
    ]
}

fn line_compare_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
    ]
}

fn memory_collation_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        memory_read_worker_summary(anchor, 0, Some(1)),
        memory_read_worker_summary(anchor, 2, Some(3)),
        numeric_transform_worker_summary(anchor, None, None, "collation_order"),
    ]
}

fn dired_dump_obstack_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 0, None),
        table_walk_worker_summary(anchor, 1),
        output_stream_worker_summary(anchor, 0, None),
    ]
}

fn obstack_begin_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        memory_write_worker_summary(anchor, 0, None),
        allocation_role_worker_summary(anchor, Some(1), false),
    ]
}

fn create_hard_link_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
        path_walk_worker_summary(anchor, 5),
        metadata_probe_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 4),
        global_synchronization_worker_summary(anchor),
    ]
}

fn record_file_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        memory_write_worker_summary(anchor, 0, None),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn reap_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        global_synchronization_worker_summary(anchor),
        numeric_transform_worker_summary(anchor, None, None, "child_pid"),
    ]
}

fn format_user_or_group_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        numeric_transform_worker_summary(anchor, None, None, "user_or_group_id"),
        format_render_worker_summary(anchor, 0, None),
    ]
}

fn obstack_free_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
        global_lifetime_worker_summary(anchor),
    ]
}

fn obstack_allocated_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
        numeric_transform_worker_summary(anchor, None, None, "obstack_membership"),
    ]
}

fn has_xattr_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        metadata_probe_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
    ]
}

fn integer_to_string_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        numeric_transform_worker_summary(anchor, Some(1), None, "integer_string"),
        memory_write_worker_summary(anchor, 1, None),
    ]
}

fn time_zone_alloc_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        allocation_role_worker_summary(anchor, None, false),
        global_table_walk_worker_summary(anchor),
    ]
}

fn version_lookup_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
        global_table_walk_worker_summary(anchor),
    ]
}

fn file_prefixlen_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        memory_write_worker_summary(anchor, 1, None),
    ]
}

fn operand_match_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::Unknown),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::Unknown),
        token_parser_worker_summary(anchor, 0, None, None),
    ]
}

fn string_transform_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            1,
            Some(0),
            Some(2),
            NativeWorkerTerminator::LengthBound,
        ),
        memory_write_worker_summary(anchor, 0, Some(2)),
    ]
}

fn file_security_context_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 2),
    ]
}

fn localtime_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
        memory_write_worker_summary(anchor, 2, None),
    ]
}

fn locale_charset_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![global_table_walk_worker_summary(anchor)]
}

fn current_timespec_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![numeric_transform_worker_summary(
        anchor,
        None,
        None,
        "timespec_now",
    )]
}

fn timeout_scheduler_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        NativeWorkerSummary {
            anchor,
            kind: NativeWorkerSummaryKind::NumericTransform,
            dst: None,
            src: Some(arg_location(0)),
            memory: None,
            len: None,
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: None,
            evidence: bounded_evidence(),
        },
        global_synchronization_worker_summary(anchor),
    ]
}

fn obstack_memory_used_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        numeric_transform_worker_summary(anchor, Some(0), None, "obstack_bytes"),
    ]
}

fn allocation_buffer_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        allocation_role_worker_summary(anchor, None, false),
        global_table_walk_worker_summary(anchor),
    ]
}

fn fileinfo_sort_comparator_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::Unknown),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::Unknown),
    ]
}

fn semantic_family_worker_summaries(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> Vec<NativeWorkerSummary> {
    if !summary_has_semantic_role_evidence(summary) {
        return Vec::new();
    }
    let Some(name) = semantic_summary_name(summary) else {
        return Vec::new();
    };
    let summaries = match name.as_str() {
        "main" | "wmain" | "entry0" | "_start" => {
            vec![program_orchestrator_worker_summary(anchor)]
        }
        name if name.starts_with("entry.init") => vec![program_orchestrator_worker_summary(anchor)],
        "register_tm_clones"
        | "deregister_tm_clones"
        | "_init"
        | "entry.fini0"
        | "__do_global_dtors_aux" => {
            vec![global_lifetime_worker_summary(anchor)]
        }
        name if is_quotearg_family_name(name) => quote_worker_summaries_for_name(anchor, name),
        name if is_quoting_options_family_name(name) => {
            quoting_options_worker_summaries_for_name(anchor, name)
        }
        name if is_xalloc_family_name(name) => xalloc_worker_summaries(anchor, name),
        "diagnose" => vec![diagnostic_wrapper_summary(anchor)],
        "usage" => vec![usage_wrapper_summary(anchor)],
        "keycompare" => vec![table_compare_summary(anchor)],
        "_internal_fnwmatch" | "internal_fnwmatch" | "fnmatch" | "rpl_fnmatch" => {
            fnmatch_worker_summaries(anchor)
        }
        "getopt" | "rpl_getopt" => getopt_worker_summaries(anchor, false),
        "_getopt_internal"
        | "_getopt_internal_r"
        | "getopt_long"
        | "getopt_long_only"
        | "rpl_getopt_long"
        | "rpl_getopt_long_only" => getopt_worker_summaries(anchor, true),
        "argmatch" | "argmatch_exact" | "argmatch_valid" => argmatch_worker_summaries(anchor),
        "argmatch_to_argument" => argmatch_to_argument_worker_summaries(anchor),
        "__xargmatch_internal" => xargmatch_internal_worker_summaries(anchor),
        "argmatch_invalid" => vec![diagnostic_wrapper_summary_for_arg(anchor, 1)],
        name if name.starts_with("digest_file") => digest_stream_worker_summaries(anchor),
        name if name.starts_with("shaxxx_stream") => shaxxx_stream_worker_summaries(anchor),
        "binop" | "binary_operator" => expression_evaluator_worker_summaries(anchor, Some(0)),
        "unary_operator" | "or" | "three_arguments" => {
            expression_evaluator_worker_summaries(anchor, None)
        }
        "write_counts" => counter_output_worker_summaries(anchor),
        "error_tail" | "verror" => vec![diagnostic_wrapper_summary_for_arg(anchor, 2)],
        "verror_at_line" => vec![diagnostic_wrapper_summary_for_arg(anchor, 4)],
        "print_errno_message" => vec![usage_wrapper_summary(anchor)],
        "printf_fetchargs" => vec![format_argument_fetch_summary(anchor)],
        "printf_parse" | "print_formatted" | "print_esc" | "vasnprintf" => {
            printf_parser_worker_summaries(anchor)
        }
        "re_search_internal"
        | "re_compile_internal"
        | "parse_expression"
        | "build_trtable"
        | "update_cur_sifted_state"
        | "transit_state_bkref"
        | "build_charclass"
        | "check_arrival"
        | "peek_token"
        | "build_wcs_upper_buffer" => regex_engine_worker_summaries(anchor, &name),
        "oprintf_" => vec![
            format_render_worker_summary(anchor, 1, None),
            output_stream_worker_summary(anchor, 1, None),
        ],
        "print_xfer_stats" => transfer_stats_worker_summaries(anchor),
        "unicode_to_mb" => multibyte_worker_summaries(anchor),
        "readlinebuffer_delim" => vec![linebuffer_delimiter_summary(anchor)],
        "rpl_mbrtoc32" | "mbrtoc32" | "rpl_mbrtowc" | "mbrtowc" => {
            multibyte_worker_summaries(anchor)
        }
        "xstrtoumax" | "xnumtoumax" => vec![numeric_parser_worker_summary(anchor, 0)],
        "xstrtoimax" | "vstrtoimax" => vec![numeric_parser_worker_summary(anchor, 0)],
        "strnumcmp" => vec![
            numeric_parser_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 1),
        ],
        "strintcmp" => vec![
            numeric_parser_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 1),
        ],
        "rpl_fopen" | "freopen_safer" | "fopen_safer" => libc_file_wrapper_summaries(anchor),
        "fd_safer" => vec![metadata_probe_worker_summary(anchor, 0)],
        "rpl_fflush" => stream_close_worker_summaries(anchor, Some(0)),
        "open_safer" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "openat_safer" => vec![
            path_walk_worker_summary(anchor, 1),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "gettext_quote" => gettext_quote_worker_summaries(anchor),
        "rpl_nanosleep" => vec![
            metadata_probe_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 1),
            global_synchronization_worker_summary(anchor),
        ],
        "xnanosleep" => vec![
            metadata_probe_worker_summary(anchor, 0),
            global_synchronization_worker_summary(anchor),
        ],
        "settimeout" => timeout_scheduler_worker_summaries(anchor),
        "stream_open" => stream_open_worker_summaries(anchor),
        "close_stream" => stream_close_worker_summaries(anchor, Some(0)),
        "rpl_fseeko" => vec![
            metadata_probe_worker_summary(anchor, 0),
            numeric_transform_worker_summary(anchor, None, Some(1), "stream_seek"),
        ],
        "maybe_close_stdout" => vec![
            global_synchronization_worker_summary(anchor),
            metadata_probe_worker_summary_for_memory(anchor, None),
        ],
        "rpl_fcntl" => vec![metadata_probe_worker_summary(anchor, 0)],
        "parse_long_options" | "parse_gnu_standard_options_only" => {
            vec![argv_option_parser_worker_summary(anchor, 1)]
        }
        "human_options" | "parse_integer" | "parse_number" | "traverse_raw_number" => {
            vec![numeric_parser_worker_summary(anchor, 0)]
        }
        "save_token" => token_buffer_finalize_worker_summaries(anchor),
        "filename_unescape" => filename_unescape_worker_summaries(anchor),
        "compare" => line_compare_worker_summaries(anchor),
        "memcoll" | "xmemcoll" => memory_collation_worker_summaries(anchor),
        "print_stats" => transfer_stats_worker_summaries(anchor),
        "create_hard_link" => create_hard_link_worker_summaries(anchor),
        "record_file" => record_file_worker_summaries(anchor),
        "calc_req_mask" => vec![
            global_table_walk_worker_summary(anchor),
            numeric_transform_worker_summary(anchor, None, None, "statx_request_mask"),
        ],
        "reap" => reap_worker_summaries(anchor),
        "num_processors_via_affinity_mask" => processor_probe_worker_summaries(anchor),
        "process_signals" | "exit_cleanup" | "clear_files" | "flush_stdout" => {
            vec![global_synchronization_worker_summary(anchor)]
        }
        "indent" => vec![numeric_transform_worker_summary(
            anchor,
            Some(0),
            Some(1),
            "column_indent",
        )],
        "dired_dump_obstack" => dired_dump_obstack_worker_summaries(anchor),
        "format_user_or_group" => format_user_or_group_worker_summaries(anchor),
        "xstrtol_fatal" => vec![diagnostic_wrapper_summary_for_arg(anchor, 4)],
        "tzalloc" => time_zone_alloc_worker_summaries(anchor),
        "xget_version" => version_lookup_worker_summaries(anchor),
        "rpl_obstack_free" => obstack_free_worker_summaries(anchor),
        "rpl_obstack_allocated_p" => obstack_allocated_worker_summaries(anchor),
        "_obstack_begin_worker" => obstack_begin_worker_summaries(anchor),
        "has_xattr" => has_xattr_worker_summaries(anchor),
        "check_tuning" => vec![table_walk_worker_summary(anchor, 0)],
        "imaxtostr" | "umaxtostr" => integer_to_string_worker_summaries(anchor),
        "hwcap_allowed" => vec![
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
            global_table_walk_worker_summary(anchor),
        ],
        "file_prefixlen" => file_prefixlen_worker_summaries(anchor),
        "getmonth" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 1, None),
        ],
        "operand_matches" => operand_match_worker_summaries(anchor),
        "xstrxfrm" => string_transform_worker_summaries(anchor),
        "set_file_security_ctx" => file_security_context_worker_summaries(anchor),
        "localtime_rz" => localtime_worker_summaries(anchor),
        "locale_charset" => locale_charset_worker_summaries(anchor),
        "current_timespec" => current_timespec_worker_summaries(anchor),
        "rpl_obstack_memory_used" => obstack_memory_used_worker_summaries(anchor),
        "alloc_ibuf" | "alloc_obuf" => allocation_buffer_worker_summaries(anchor),
        "synchronize_output" => vec![global_synchronization_worker_summary(anchor)],
        "copy_with_unblock" => vec![output_stream_worker_summary_with_len(
            anchor,
            0,
            None,
            Some(1),
        )],
        "copy_bytes" => vec![memory_transfer_worker_summary(anchor, 0, 1, 2)],
        "iwrite" => vec![output_stream_worker_summary_with_len(
            anchor,
            1,
            None,
            Some(2),
        )],
        "debug_print_current_time" | "debug_print_relative_time" => vec![
            format_render_worker_summary(anchor, 0, None),
            table_walk_worker_summary(anchor, 1),
        ],
        "re_string_reconstruct" => vec![
            token_parser_worker_summary(anchor, 0, Some(0), None),
            memory_write_worker_summary(anchor, 0, None),
            numeric_transform_worker_summary(anchor, Some(1), Some(2), "regex_reconstruct"),
        ],
        "yyparse" => vec![
            token_parser_worker_summary(anchor, 0, Some(0), None),
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "install_file_in_file" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
            metadata_probe_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 4),
        ],
        "chown_files" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            table_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 6),
        ],
        "who" => vec![
            path_walk_worker_summary(anchor, 0),
            record_stream_worker_summary(anchor, 0, None),
            format_render_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "read_utmp" => vec![
            path_walk_worker_summary(anchor, 0),
            record_stream_worker_summary(anchor, 0, Some(2)),
            memory_write_worker_summary(anchor, 1, None),
            memory_write_worker_summary(anchor, 2, None),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "dopass" => vec![
            metadata_probe_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 3, None),
            table_walk_worker_summary(anchor, 5),
            numeric_transform_worker_summary(anchor, Some(6), Some(3), "overwrite_pass"),
            output_stream_worker_summary_with_len(anchor, 5, Some(0), Some(6)),
        ],
        "factor_up" => vec![
            memory_write_worker_summary(anchor, 0, None),
            numeric_transform_worker_summary(anchor, Some(2), Some(0), "factor_fold"),
            table_walk_worker_summary(anchor, 3),
        ],
        "factor_using_pollard_rho" => vec![
            memory_write_worker_summary(anchor, 0, None),
            numeric_transform_worker_summary(anchor, Some(1), Some(0), "pollard_rho"),
        ],
        "factor_using_pollard_rho2" => vec![
            memory_write_worker_summary(anchor, 0, None),
            numeric_transform_worker_summary(anchor, Some(2), Some(0), "pollard_rho2"),
        ],
        "mp_factor_using_pollard_rho" => vec![
            memory_write_worker_summary(anchor, 0, None),
            memory_read_worker_summary(anchor, 1, Some(2)),
            numeric_transform_worker_summary(anchor, Some(3), Some(0), "pollard_rho"),
        ],
        "seq_fast" => vec![
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
            string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
            numeric_transform_worker_summary(anchor, Some(2), None, "sequence_step"),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "tsort" => vec![
            path_walk_worker_summary(anchor, 0),
            token_parser_worker_summary(anchor, 0, None, None),
            table_walk_worker_summary(anchor, 0),
            sort_merge_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "translate_charset" => vec![table_walk_worker_summary(anchor, 0)],
        "invalidate_cache" => vec![metadata_probe_worker_summary(anchor, 0)],
        "decode_preserve_arg" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "skip" => vec![record_stream_worker_summary(anchor, 0, None)],
        name if name.starts_with("find_field") => {
            vec![field_selection_worker_summary(anchor, 0, None)]
        }
        "wc" => vec![
            record_stream_worker_summary(anchor, 0, None),
            numeric_parser_worker_summary(anchor, 1),
        ],
        "is_utf8_charset" => vec![global_synchronization_worker_summary(anchor)],
        "setlocale_null_r_unlocked" => locale_buffer_worker_summaries(anchor),
        "set_program_name" => program_name_worker_summaries(anchor),
        "canonicalize_filename_mode" => vec![string_scan_worker_summary(
            anchor,
            0,
            None,
            None,
            NativeWorkerTerminator::ZeroByte,
        )],
        "skip_whitespace_run" | "scan_mb_blank_field" | "scan_mb_delim_field" => {
            vec![token_parser_worker_summary(anchor, 0, None, None)]
        }
        "mcel_scan" => multibyte_cell_scan_worker_summaries(anchor),
        "mcel_cmp" => vec![numeric_transform_worker_summary(
            anchor, None, None, "mcel_cmp",
        )],
        "mcel_tocmp" => vec![
            metadata_probe_worker_summary(anchor, 0),
            numeric_transform_worker_summary(anchor, None, None, "mcel_tocmp"),
        ],
        "mcel_scant" => multibyte_cell_scant_worker_summaries(anchor),
        "mcel_scanz" => multibyte_cell_scan_worker_summaries(anchor),
        "copy_file_data" => vec![file_transfer_worker_summary(anchor, 0, 4, Some(8))],
        "create_hole" => vec![
            metadata_probe_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            numeric_transform_worker_summary(anchor, None, Some(2), "sparse_hole"),
        ],
        "fadvise" => vec![metadata_probe_worker_summary(anchor, 0)],
        "sparse_copy" => vec![file_transfer_worker_summary(anchor, 0, 1, Some(7))],
        "copy_internal" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
        ],
        "do_copy" => vec![
            directory_traversal_worker_summary(anchor, 1, None),
            file_transfer_worker_summary(anchor, 1, 2, None),
        ],
        "copy" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
            table_walk_worker_summary(anchor, 5),
        ],
        "do_move" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
            table_walk_worker_summary(anchor, 4),
        ],
        "overwrite_ok" => overwrite_probe_worker_summaries(anchor),
        "areadlink_with_size" => vec![
            path_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, Some(1), false),
        ],
        "areadlinkat_with_size" => readlink_alloc_worker_summaries(anchor),
        "mfile_name_concat" => file_name_concat_worker_summaries(anchor),
        "set_owner" => file_ownership_worker_summaries(anchor),
        "set_process_security_ctx" => security_context_worker_summaries(anchor),
        "same_nameat" => same_nameat_worker_summaries(anchor),
        "force_linkat" => force_link_worker_summaries(anchor),
        "force_symlinkat" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 2),
            metadata_probe_worker_summary(anchor, 4),
        ],
        "make_dir_parents_private" => vec![path_walk_worker_summary(anchor, 0)],
        "backupfile_internal" | "utimecmpat" => vec![path_walk_worker_summary(anchor, 1)],
        "fdutimensat" => vec![
            metadata_probe_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 2),
        ],
        "strmode" => file_mode_render_worker_summaries(anchor),
        "do_statx" => stat_probe_worker_summaries(anchor),
        "getuidbyname" => user_id_lookup_worker_summaries(anchor),
        "defaultcon" | "restorecon_private" | "restorecon" => {
            selinux_path_worker_summaries(anchor, 1)
        }
        "re_protect" => re_protect_worker_summaries(anchor),
        "renameatu" => rename_worker_summaries(anchor),
        "streamsavedir" => streamsavedir_worker_summaries(anchor),
        "rpl_fts_open" | "rpl_fts_read" | "rpl_fts_close" | "fts_build" => {
            vec![directory_traversal_worker_summary(anchor, 0, None)]
        }
        "rpl_getfilecon" | "rpl_getfilecon_raw" | "rpl_lgetfilecon" | "rpl_lgetfilecon_raw" => {
            vec![
                path_walk_worker_summary(anchor, 0),
                metadata_probe_worker_summary(anchor, 0),
                memory_write_worker_summary(anchor, 1, None),
            ]
        }
        "fts_safe_changedir" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            path_walk_worker_summary(anchor, 3),
        ],
        "version_etc_arn" => version_etc_worker_summaries(anchor, Some(4)),
        "version_etc_ar" | "version_etc_va" => version_etc_worker_summaries(anchor, Some(4)),
        "version_etc" => version_etc_worker_summaries(anchor, None),
        "emit_bug_reporting_address" => vec![usage_wrapper_summary(anchor)],
        "oputs_" => vec![output_stream_worker_summary(anchor, 0, None)],
        "prompt" => vec![format_render_worker_summary(anchor, 0, None)],
        "cut_characters_mode" => vec![
            record_stream_worker_summary(anchor, 0, None),
            field_selection_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "cut_fields_mb_any" | "cut_fields_bytesearch" => vec![
            record_stream_worker_summary(anchor, 0, None),
            field_selection_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "cut_file" => byte_stream_selection_worker_summaries(anchor, 0),
        "cut_bytes" => byte_stream_selection_worker_summaries(anchor, 0),
        "memchr2" => memchr2_worker_summaries(anchor),
        "begfield" | "limfield" => vec![
            field_selection_worker_summary(anchor, 0, None),
            token_parser_worker_summary(anchor, 0, None, None),
            numeric_parser_worker_summary(anchor, 0),
        ],
        "set_fields" => vec![field_selection_worker_summary(anchor, 0, None)],
        "print_name_with_quoting" => vec![
            format_render_worker_summary(anchor, 0, Some(2)),
            path_walk_worker_summary(anchor, 0),
        ],
        "length_of_file_name_and_frills" => file_name_frills_worker_summaries(anchor),
        "print_long_format" => vec![
            format_render_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "print_filename" => filename_output_worker_summaries(anchor, 0),
        "get_funky_string" => quote_name_worker_summaries(anchor),
        "abformat_init" => vec![
            table_walk_worker_summary(anchor, 0),
            format_render_worker_summary(anchor, 0, None),
        ],
        "signal_setup" => vec![
            global_synchronization_worker_summary(anchor),
            table_walk_worker_summary(anchor, 0),
        ],
        "quote_name_buf" | "quote_name" => quote_name_worker_summaries(anchor),
        "print_file_name_and_frills" => file_name_frills_worker_summaries(anchor),
        "print_with_separator" => vec![format_render_worker_summary(anchor, 0, None)],
        "calculate_columns" | "print_current_files" => vec![
            table_walk_worker_summary(anchor, 0),
            format_render_worker_summary(anchor, 0, None),
        ],
        "verrevcmp" => vec![
            string_scan_worker_summary(
                anchor,
                0,
                None,
                Some(1),
                NativeWorkerTerminator::LengthBound,
            ),
            string_scan_worker_summary(
                anchor,
                2,
                None,
                Some(3),
                NativeWorkerTerminator::LengthBound,
            ),
            numeric_parser_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 2),
        ],
        "filenvercmp" => file_version_compare_worker_summaries(anchor),
        "mpsort_with_tmp" => vec![
            sort_merge_worker_summary(anchor, 0, Some(3)),
            table_walk_worker_summary(anchor, 0),
        ],
        "gobble_file" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "print_dir" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "extract_dirs_from_files" => directory_extraction_worker_summaries(anchor),
        "sort_files" => global_sort_files_worker_summaries(anchor),
        "fts_sort" => vec![
            sort_merge_worker_summary(anchor, 0, None),
            directory_traversal_worker_summary(anchor, 0, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "fdfile_has_aclinfo" => vec![
            metadata_probe_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 1),
        ],
        "human_readable" => vec![format_render_worker_summary(anchor, 0, Some(1))],
        "nstrftime" | "c_nstrftime" => time_format_worker_summaries(anchor),
        "mktime_z" => time_zone_worker_summaries(anchor),
        "__strftime_internal" => vec![
            format_render_worker_summary(anchor, 2, Some(0)),
            record_stream_worker_summary(anchor, 2, Some(0)),
        ],
        "rm" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            path_walk_worker_summary(anchor, 0),
        ],
        "close_stdin" => stream_close_worker_summaries(anchor, None),
        "get_dir_status" => directory_status_worker_summaries(anchor),
        "leave_dir" | "find_entry" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "write_line" => vec![
            output_stream_worker_summary(anchor, 0, Some(1)),
            record_stream_worker_summary(anchor, 0, Some(1)),
        ],
        "mergefps" => vec![
            sort_merge_worker_summary(anchor, 0, Some(3)),
            record_stream_worker_summary(anchor, 0, Some(3)),
        ],
        "sortlines" => vec![
            sort_merge_worker_summary(anchor, 0, Some(5)),
            record_stream_worker_summary(anchor, 0, Some(5)),
        ],
        "pipe_child" => vec![format_render_worker_summary(anchor, 0, Some(1))],
        "merge" => vec![sort_merge_worker_summary(anchor, 0, None)],
        "mergefiles" => vec![
            sort_merge_worker_summary(anchor, 0, Some(3)),
            record_stream_worker_summary(anchor, 0, Some(3)),
        ],
        "cwd_advance_fd" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 1),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "restore_initial_cwd" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "init_node" => merge_node_init_worker_summaries(anchor),
        "fts_stat" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "rpl_fts_children" => vec![directory_traversal_worker_summary(anchor, 0, None)],
        "transfer_entries" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            directory_traversal_worker_summary(anchor, 1, None),
        ],
        "hash_print_statistics" => hash_statistics_worker_summaries(anchor),
        "hash_insert_if_absent" => hash_table_worker_summaries(anchor, 0, Some(1)),
        "hash_rehash" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, Some(1), false),
        ],
        "hash_clear" | "hash_free" => vec![
            table_walk_worker_summary(anchor, 0),
            global_lifetime_worker_summary(anchor),
        ],
        "heap_insert" => vec![
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "heap_remove_top" => vec![
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "hash_remove" => hash_table_worker_summaries(anchor, 0, Some(1)),
        "get_root_dev_ino" => vec![
            metadata_probe_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
            path_walk_worker_summary(anchor, 0),
        ],
        "getuser" | "getgroup" => vec![
            table_walk_worker_summary(anchor, 0),
            global_table_walk_worker_summary(anchor),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "excise" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            path_walk_worker_summary(anchor, 1),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "fillbuf" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            memory_read_worker_summary(anchor, 1, Some(2)),
        ],
        "maybe_create_temp" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "find_in_given_path" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
        ],
        "get_cgroup2_cpu_quota" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 0),
        ],
        "isaac_refill" | "isaac_seed" => isaac_worker_summaries(anchor),
        "wc_lines_avx2" | "wc_lines_avx512" => vector_line_count_worker_summaries(anchor),
        "mbsnwidth" => multibyte_cell_scan_worker_summaries(anchor),
        "readtokens0" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            token_parser_worker_summary(anchor, 0, Some(1), None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "add_range_pair" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "try_tempname_len" => tempname_probe_worker_summaries(anchor),
        "filesystem_type" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 1),
            table_walk_worker_summary(anchor, 0),
        ],
        "close_stdout" => stream_close_worker_summaries(anchor, None),
        "rpl_fclose" => stream_close_worker_summaries(anchor, Some(0)),
        "write_bytes" => byte_output_worker_summaries(anchor),
        "yesno" => yesno_worker_summaries(anchor),
        "posix2_version" => vec![metadata_probe_worker_summary_for_memory(anchor, None)],
        "error" => vec![diagnostic_wrapper_summary_for_arg(anchor, 2)],
        "error_at_line" => vec![diagnostic_wrapper_summary_for_arg(anchor, 4)],
        "emit_verbose" => vec![
            format_render_worker_summary(anchor, 0, None),
            path_walk_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 2),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "file_escape" => file_escape_worker_summaries(anchor),
        "zaptemp" => temp_cleanup_worker_summaries(anchor),
        "sequential_sort" => sequential_sort_worker_summaries(anchor),
        "open_input_files" => open_input_files_worker_summaries(anchor),
        "get_meminfo" => get_meminfo_worker_summaries(anchor),
        "randread_new" => randread_new_worker_summaries(anchor),
        "randperm_new" => vec![
            allocation_role_worker_summary(anchor, Some(1), false),
            table_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "randread" => randread_worker_summaries(anchor),
        "_gl_scratch_buffer_grow"
        | "_gl_scratch_buffer_grow_preserve"
        | "gl_scratch_buffer_grow"
        | "gl_scratch_buffer_grow_preserve" => scratch_buffer_growth_worker_summaries(anchor),
        "argv_iter"
        | "argv_iter_init_argv"
        | "argv_iter_init_stream"
        | "argv_iter_n_args"
        | "argv_iter_free" => argv_iterator_worker_summaries(anchor, &name),
        "gregorian_to_persian" | "gregorian_to_ethiopian" => {
            calendar_transform_worker_summaries(anchor)
        }
        "next_prime" => prime_search_worker_summaries(anchor),
        "num_processors" | "physmem_claimable" => processor_probe_worker_summaries(anchor),
        "rpl_pipe2" => pipe_wrapper_worker_summaries(anchor),
        "cycle_check_init" => vec![
            metadata_probe_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "cycle_check" => vec![
            metadata_probe_worker_summary(anchor, 1),
            memory_read_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 0, None),
        ],
        name if is_hash_table_family_name(name) => hash_table_family_worker_summaries(anchor, name),
        name if is_parser_family_name(name) => parser_family_worker_summaries(anchor, name),
        name if is_path_family_name(name) => path_family_worker_summaries(anchor, name),
        name if is_directory_family_name(name) => directory_family_worker_summaries(anchor, name),
        name if is_fileinfo_sort_comparator_family_name(name) => {
            fileinfo_sort_comparator_worker_summaries(anchor)
        }
        name if is_record_memory_family_name(name) => {
            record_memory_family_worker_summaries(anchor, name)
        }
        _ => Vec::new(),
    };
    mark_name_hint_summaries(summaries)
}

fn summary_has_semantic_role_evidence(summary: &FunctionSemanticSummary) -> bool {
    summary.return_relation != SummaryReturnRelation::Unknown
        || !summary.arg_effects.is_empty()
        || !summary.transfer_effects.is_empty()
        || !summary.memory_effects.is_empty()
        || !summary.allocation_effects.is_empty()
        || !summary.lifetime_effects.is_empty()
        || !summary.sync_effects.is_empty()
        || !summary.atomic_effects.is_empty()
}

fn structural_worker_summaries_from_interproc_summary(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = Vec::new();

    if matches!(summary.return_relation, SummaryReturnRelation::HeapAlloc)
        && summary.allocation_effects.is_empty()
    {
        summaries.push(allocation_role_worker_summary(anchor, None, false));
    }

    let known_lifetime_frees = summary
        .lifetime_effects
        .iter()
        .filter(|effect| effect.op == SummaryLifetimeOp::Free)
        .map(|effect| effect.arg)
        .collect::<BTreeSet<_>>();
    let free_args = summary
        .memory_effects
        .iter()
        .filter(|effect| effect.kind == SummaryMemoryEffectKind::Free)
        .filter_map(|effect| match effect.location.region {
            SummaryMemoryRegion::Arg { index } => Some(index),
            SummaryMemoryRegion::Global { .. }
            | SummaryMemoryRegion::HeapReturn
            | SummaryMemoryRegion::Unknown => None,
        })
        .chain(
            summary
                .arg_effects
                .iter()
                .filter(|(_, effect)| effect.free)
                .map(|(arg, _)| *arg),
        )
        .collect::<BTreeSet<_>>();
    for arg in free_args.difference(&known_lifetime_frees) {
        summaries.push(lifetime_worker_summary(
            anchor,
            SummaryLifetimeEffect {
                arg: *arg,
                op: SummaryLifetimeOp::Free,
            },
        ));
    }

    let read_effects = summary
        .memory_effects
        .iter()
        .filter(|effect| effect.kind == SummaryMemoryEffectKind::Read)
        .collect::<Vec<_>>();
    let has_runtime_effects = summary.writes_global_memory
        || summary.touches_unknown_memory
        || summary.has_unknown_calls
        || summary
            .memory_effects
            .iter()
            .any(|effect| !matches!(effect.kind, SummaryMemoryEffectKind::Read));
    let mut global_reads = BTreeSet::new();
    let mut byte_arg_reads = BTreeSet::new();
    for effect in read_effects {
        match effect.location.region {
            SummaryMemoryRegion::Global { .. } => {
                global_reads.insert(effect.location);
            }
            SummaryMemoryRegion::Arg { index } => {
                if effect
                    .location
                    .range
                    .and_then(|range| range.width)
                    .is_some_and(|width| width == 1)
                {
                    byte_arg_reads.insert(index);
                }
            }
            SummaryMemoryRegion::HeapReturn | SummaryMemoryRegion::Unknown => {}
        }
    }
    if summary.reads_global_memory {
        for location in global_reads {
            summaries.push(metadata_probe_worker_summary_for_memory(
                anchor,
                Some(location),
            ));
        }
    }
    if has_runtime_effects {
        for arg in byte_arg_reads {
            summaries.push(path_walk_worker_summary(anchor, arg));
        }
    }

    summaries
}

fn allocation_worker_summary(anchor: u64, effect: SummaryAllocationEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Allocation,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: Some(effect),
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn lifetime_worker_summary(anchor: u64, effect: SummaryLifetimeEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Lifetime,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: Some(effect),
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn sync_worker_summary(anchor: u64, effect: SummarySyncEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Synchronization,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: Some(effect),
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn global_synchronization_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Synchronization,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn atomic_worker_summary(anchor: u64, effect: SummaryAtomicEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Atomic,
        dst: None,
        src: None,
        memory: Some(effect.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: Some(effect),
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

pub(super) fn summaries_from_interproc_summary_unbounded(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> Vec<NativeWorkerSummary> {
    let mut worker_summaries = Vec::new();
    worker_summaries.extend(semantic_family_worker_summaries(anchor, summary));
    worker_summaries.extend(structural_worker_summaries_from_interproc_summary(
        anchor, summary,
    ));
    worker_summaries.extend(
        summary
            .transfer_effects
            .iter()
            .copied()
            .map(|effect| transfer_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .memory_effects
            .iter()
            .copied()
            .map(|effect| memory_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .allocation_effects
            .iter()
            .copied()
            .map(|effect| allocation_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .lifetime_effects
            .iter()
            .copied()
            .map(|effect| lifetime_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .sync_effects
            .iter()
            .copied()
            .map(|effect| sync_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .atomic_effects
            .iter()
            .copied()
            .map(|effect| atomic_worker_summary(anchor, effect)),
    );
    worker_summaries
}

fn parse_hexish_u64(text: &str) -> Option<u64> {
    let trimmed = text.trim();
    let hex = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
        .unwrap_or(trimmed);
    u64::from_str_radix(hex, 16).ok()
}

fn const_value(var: &SSAVar) -> Option<u64> {
    let raw = var.name.strip_prefix("const:")?;
    let value = raw
        .rsplit_once('_')
        .filter(|(_, suffix)| suffix.bytes().all(|byte| byte.is_ascii_digit()))
        .map(|(value, _)| value)
        .unwrap_or(raw);
    parse_hexish_u64(value)
}

fn resolved_const_value(func: &SsaArtifact, var: &SSAVar) -> Option<u64> {
    fn resolve(func: &SsaArtifact, var: &SSAVar, depth: usize) -> Option<u64> {
        if let Some(value) = const_value(var) {
            return Some(value);
        }
        if depth == 0 {
            return None;
        }
        let (block_addr, r2ssa::function::DefLocation::Op(op_idx)) =
            func.function().find_def(var)?
        else {
            return None;
        };
        let block = func.function().get_block(block_addr)?;
        let op = block.ops.get(op_idx)?;
        let src = match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Trunc { src, .. } => src,
            _ => return None,
        };
        resolve(func, src, depth - 1)
    }

    resolve(func, var, 4)
}

fn ram_address(var: &SSAVar) -> Option<u64> {
    var.name.strip_prefix("ram:").and_then(parse_hexish_u64)
}

fn register_base_name(var: &SSAVar) -> &str {
    var.name
        .strip_prefix("reg:")
        .unwrap_or(var.name.as_str())
        .trim_start_matches('_')
}

fn x86_register_alias_spec(base: &str) -> Option<RegisterAliasSpec> {
    let upper = base.to_ascii_uppercase();
    let fixed = match upper.as_str() {
        "AL" => Some(("RAX", 0, 8)),
        "AH" => Some(("RAX", 8, 8)),
        "AX" => Some(("RAX", 0, 16)),
        "EAX" => Some(("RAX", 0, 32)),
        "RAX" => Some(("RAX", 0, 64)),
        "BL" => Some(("RBX", 0, 8)),
        "BH" => Some(("RBX", 8, 8)),
        "BX" => Some(("RBX", 0, 16)),
        "EBX" => Some(("RBX", 0, 32)),
        "RBX" => Some(("RBX", 0, 64)),
        "CL" => Some(("RCX", 0, 8)),
        "CH" => Some(("RCX", 8, 8)),
        "CX" => Some(("RCX", 0, 16)),
        "ECX" => Some(("RCX", 0, 32)),
        "RCX" => Some(("RCX", 0, 64)),
        "DL" => Some(("RDX", 0, 8)),
        "DH" => Some(("RDX", 8, 8)),
        "DX" => Some(("RDX", 0, 16)),
        "EDX" => Some(("RDX", 0, 32)),
        "RDX" => Some(("RDX", 0, 64)),
        "SIL" => Some(("RSI", 0, 8)),
        "SI" => Some(("RSI", 0, 16)),
        "ESI" => Some(("RSI", 0, 32)),
        "RSI" => Some(("RSI", 0, 64)),
        "DIL" => Some(("RDI", 0, 8)),
        "DI" => Some(("RDI", 0, 16)),
        "EDI" => Some(("RDI", 0, 32)),
        "RDI" => Some(("RDI", 0, 64)),
        "BPL" => Some(("RBP", 0, 8)),
        "BP" => Some(("RBP", 0, 16)),
        "EBP" => Some(("RBP", 0, 32)),
        "RBP" => Some(("RBP", 0, 64)),
        "SPL" => Some(("RSP", 0, 8)),
        "SP" => Some(("RSP", 0, 16)),
        "ESP" => Some(("RSP", 0, 32)),
        "RSP" => Some(("RSP", 0, 64)),
        _ => None,
    };
    if let Some((family, offset_bits, width_bits)) = fixed {
        return Some(RegisterAliasSpec {
            family: family.to_string(),
            offset_bits,
            width_bits,
        });
    }

    let (family, width_bits) = if let Some(family) = upper.strip_suffix('B') {
        (family.to_string(), 8)
    } else if let Some(family) = upper.strip_suffix('W') {
        (family.to_string(), 16)
    } else if let Some(family) = upper.strip_suffix('D') {
        (family.to_string(), 32)
    } else {
        (upper, 64)
    };
    if !family.starts_with('R') {
        return None;
    }
    let digits = &family[1..];
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    Some(RegisterAliasSpec {
        family,
        offset_bits: 0,
        width_bits,
    })
}

fn x86_alias_covers(candidate: &RegisterAliasSpec, requested: &RegisterAliasSpec) -> bool {
    candidate.family == requested.family
        && candidate.offset_bits <= requested.offset_bits
        && candidate.offset_bits + candidate.width_bits
            >= requested.offset_bits + requested.width_bits
}

fn x86_alias_tuple(var: &SSAVar) -> Option<(String, u32, u32, u32)> {
    let spec = x86_register_alias_spec(register_base_name(var))?;
    Some((spec.family, spec.offset_bits, spec.width_bits, var.version))
}

fn abi_pointer_arg_index(var: &SSAVar) -> Option<usize> {
    let name = register_base_name(var).to_ascii_lowercase();
    match name.as_str() {
        "x0" | "w0" | "rdi" | "edi" | "di" | "dil" | "a0" => Some(0),
        "x1" | "w1" | "rsi" | "esi" | "si" | "sil" | "a1" => Some(1),
        "x2" | "w2" | "rdx" | "edx" | "dx" | "dl" | "a2" => Some(2),
        "x3" | "w3" | "rcx" | "ecx" | "cx" | "cl" | "a3" => Some(3),
        "x4" | "w4" | "r8" | "r8d" | "r8w" | "r8b" | "a4" => Some(4),
        "x5" | "w5" | "r9" | "r9d" | "r9w" | "r9b" | "a5" => Some(5),
        "x6" | "w6" | "a6" => Some(6),
        "x7" | "w7" | "a7" => Some(7),
        _ => None,
    }
}

fn abi_input_arg_index(var: &SSAVar) -> Option<usize> {
    (var.version == 0)
        .then(|| abi_pointer_arg_index(var))
        .flatten()
}

fn is_return_value_var(var: &SSAVar) -> bool {
    matches!(
        register_base_name(var).to_ascii_uppercase().as_str(),
        "AL" | "AX" | "EAX" | "RAX" | "W0" | "X0" | "A0"
    )
}

fn rooted_region(
    var: &SSAVar,
    roots: &BTreeMap<SSAVar, SummaryMemoryRegion>,
) -> Option<SummaryMemoryRegion> {
    abi_input_arg_index(var)
        .map(|index| SummaryMemoryRegion::Arg { index })
        .or_else(|| ram_address(var).map(|address| SummaryMemoryRegion::Global { address }))
        .or_else(|| roots.get(var).copied())
}

fn rooted_arg_var(var: &SSAVar, roots: &BTreeMap<SSAVar, SummaryMemoryRegion>) -> Option<usize> {
    match rooted_region(var, roots)? {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    }
}

fn location_from_region(region: SummaryMemoryRegion, width: u32) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region,
        range: Some(SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(width),
        }),
    }
}

fn pointer_location_from_region(region: SummaryMemoryRegion) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region,
        range: None,
    }
}

fn location_with_access_width(
    mut location: SummaryMemoryLocation,
    width: u32,
) -> SummaryMemoryLocation {
    let range = location.range.unwrap_or(SummaryMemoryRange {
        offset_lo: 0,
        offset_hi: 0,
        width: None,
    });
    location.range = Some(SummaryMemoryRange {
        width: Some(width),
        ..range
    });
    location
}

fn offset_location(location: SummaryMemoryLocation, delta: i64) -> Option<SummaryMemoryLocation> {
    let range = location.range.unwrap_or(SummaryMemoryRange {
        offset_lo: 0,
        offset_hi: 0,
        width: None,
    });
    Some(SummaryMemoryLocation {
        region: location.region,
        range: Some(SummaryMemoryRange {
            offset_lo: range.offset_lo.checked_add(delta)?,
            offset_hi: range.offset_hi.checked_add(delta)?,
            width: range.width,
        }),
    })
}

fn copy_root_if_known(
    dst: &SSAVar,
    src: &SSAVar,
    roots: &mut BTreeMap<SSAVar, SummaryMemoryRegion>,
) {
    if let Some(root) = rooted_region(src, roots) {
        roots.insert(dst.clone(), root);
    }
}

fn copy_binary_root_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    roots: &mut BTreeMap<SSAVar, SummaryMemoryRegion>,
) {
    let a_root = rooted_region(a, roots);
    let b_root = rooted_region(b, roots);
    match (a_root, b_root) {
        (Some(root), None) | (None, Some(root)) => {
            roots.insert(dst.clone(), root);
        }
        (Some(a_root), Some(b_root)) if a_root == b_root => {
            roots.insert(dst.clone(), a_root);
        }
        _ => {}
    }
}

fn copy_phi_root_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    roots: &mut BTreeMap<SSAVar, SummaryMemoryRegion>,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| rooted_region(src, roots));
    if let Some(first) = source_roots.next()
        && source_roots.all(|root| root == first)
    {
        roots.insert(dst.clone(), first);
    }
}

fn loaded_source(
    var: &SSAVar,
    load_sources: &BTreeMap<SSAVar, LoadedSource>,
) -> Option<LoadedSource> {
    if let Some(source) = load_sources.get(var).copied() {
        return Some(source);
    }
    if let Some((candidate, source)) = load_sources
        .iter()
        .filter(|(candidate, _)| same_ssa_identity(candidate, var) && candidate.size >= var.size)
        .max_by_key(|(candidate, _)| candidate.size)
    {
        return Some(loaded_source_with_value_width(
            *source,
            candidate.size.min(var.size),
        ));
    }
    let requested = x86_register_alias_spec(register_base_name(var))?;
    load_sources
        .iter()
        .filter_map(|(candidate, source)| {
            let candidate_spec = x86_register_alias_spec(register_base_name(candidate))?;
            x86_alias_covers(&candidate_spec, &requested).then_some((
                candidate.version,
                candidate_spec.width_bits,
                *source,
            ))
        })
        .max_by_key(|(version, width_bits, _)| (*version, *width_bits))
        .map(|(_, _, source)| source)
}

fn same_ssa_identity(left: &SSAVar, right: &SSAVar) -> bool {
    left.name == right.name && left.version == right.version
}

fn loaded_source_with_value_width(source: LoadedSource, size: u32) -> LoadedSource {
    LoadedSource { size, ..source }
}

fn exact_dataflow_value<T: Copy>(value: Option<&DataflowValue<T>>) -> Option<T> {
    value.and_then(DataflowValue::exact).copied()
}

fn join_dataflow_value<T: Clone + Eq>(
    left: &mut DataflowValue<T>,
    right: &DataflowValue<T>,
) -> bool {
    match (&*left, right) {
        (DataflowValue::Unknown, _) | (_, DataflowValue::Unknown) => {
            if !matches!(left, DataflowValue::Unknown) {
                *left = DataflowValue::Unknown;
                return true;
            }
            false
        }
        (DataflowValue::Exact(left_value), DataflowValue::Exact(right_value)) => {
            if left_value == right_value {
                false
            } else {
                *left = DataflowValue::Unknown;
                true
            }
        }
    }
}

fn join_dataflow_map<K: Clone + Ord, T: Clone + Eq>(
    left: &mut BTreeMap<K, DataflowValue<T>>,
    right: &BTreeMap<K, DataflowValue<T>>,
) -> bool {
    let mut changed = false;
    for (key, right_value) in right {
        if let Some(left_value) = left.get_mut(key) {
            changed |= join_dataflow_value(left_value, right_value);
        } else {
            left.insert(key.clone(), right_value.clone());
            changed = true;
        }
    }
    changed
}

fn join_worker_state(left: &mut WorkerDataflowState, right: &WorkerDataflowState) -> bool {
    let roots_changed = join_dataflow_map(&mut left.roots, &right.roots);
    let locations_changed = join_dataflow_map(&mut left.locations, &right.locations);
    let loads_changed = join_dataflow_map(&mut left.load_sources, &right.load_sources);
    let controls_changed = join_dataflow_map(&mut left.control_sources, &right.control_sources);
    let byte_predicates_changed =
        join_dataflow_map(&mut left.byte_predicates, &right.byte_predicates);
    let zero_comparisons_changed =
        join_dataflow_map(&mut left.zero_comparisons, &right.zero_comparisons);
    let stack_values_changed = join_dataflow_map(&mut left.stack_values, &right.stack_values);
    if loads_changed {
        rebuild_load_source_alias_index(left);
    }
    roots_changed
        || locations_changed
        || loads_changed
        || controls_changed
        || byte_predicates_changed
        || zero_comparisons_changed
        || stack_values_changed
}

fn insert_exact_dataflow_value<K: Clone + Ord, T: Clone + Eq>(
    map: &mut BTreeMap<K, DataflowValue<T>>,
    key: &K,
    value: T,
) {
    match map.get_mut(key) {
        Some(existing @ DataflowValue::Unknown) => {
            *existing = DataflowValue::Exact(value);
        }
        Some(existing) => {
            let _ = join_dataflow_value(existing, &DataflowValue::Exact(value));
        }
        None => {
            map.insert(key.clone(), DataflowValue::Exact(value));
        }
    }
}

fn insert_dataflow_value<K: Clone + Ord, T: Clone + Eq>(
    map: &mut BTreeMap<K, DataflowValue<T>>,
    key: &K,
    value: DataflowValue<T>,
) {
    match map.get_mut(key) {
        Some(existing) => {
            let _ = join_dataflow_value(existing, &value);
        }
        None => {
            map.insert(key.clone(), value);
        }
    }
}

fn insert_load_source_dataflow_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: DataflowValue<LoadedSource>,
) {
    match value.clone() {
        DataflowValue::Exact(source) => {
            insert_exact_dataflow_value(&mut state.load_sources, key, source);
        }
        DataflowValue::Unknown => {
            insert_dataflow_value(&mut state.load_sources, key, DataflowValue::Unknown);
        }
    }
    if let Some((family, offset_bits, width_bits, version)) = x86_alias_tuple(key) {
        let alias_key = (offset_bits, width_bits, version);
        state
            .load_source_alias_members
            .entry(family.clone())
            .or_default()
            .insert(key.clone());
        match value {
            DataflowValue::Exact(source) => insert_exact_dataflow_value(
                state.load_source_aliases.entry(family).or_default(),
                &alias_key,
                source,
            ),
            DataflowValue::Unknown => insert_dataflow_value(
                state.load_source_aliases.entry(family).or_default(),
                &alias_key,
                DataflowValue::Unknown,
            ),
        }
    }
}

fn insert_exact_load_source_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: LoadedSource,
) {
    insert_load_source_dataflow_value(state, key, DataflowValue::Exact(value));
}

fn insert_unknown_load_source_value(state: &mut WorkerDataflowState, key: &SSAVar) {
    insert_load_source_dataflow_value(state, key, DataflowValue::Unknown);
}

fn insert_exact_control_source_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: BTreeSet<usize>,
) {
    insert_exact_dataflow_value(&mut state.control_sources, key, value);
}

fn insert_unknown_control_source_value(state: &mut WorkerDataflowState, key: &SSAVar) {
    insert_dataflow_value(&mut state.control_sources, key, DataflowValue::Unknown);
}

fn insert_exact_byte_predicate_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: BytePredicateValue,
) {
    insert_exact_dataflow_value(&mut state.byte_predicates, key, value);
}

fn insert_exact_zero_comparison_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: ZeroComparisonValue,
) {
    insert_exact_dataflow_value(&mut state.zero_comparisons, key, value);
}

fn rebuild_load_source_alias_index(state: &mut WorkerDataflowState) {
    state.load_source_aliases.clear();
    state.load_source_alias_members.clear();
    for (var, source) in &state.load_sources {
        if let Some((family, offset_bits, width_bits, version)) = x86_alias_tuple(var) {
            let alias_key = (offset_bits, width_bits, version);
            state
                .load_source_alias_members
                .entry(family.clone())
                .or_default()
                .insert(var.clone());
            insert_dataflow_value(
                state.load_source_aliases.entry(family).or_default(),
                &alias_key,
                source.clone(),
            );
        }
    }
}

fn dataflow_rooted_region(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<SummaryMemoryRegion> {
    abi_input_arg_index(var)
        .map(|index| SummaryMemoryRegion::Arg { index })
        .or_else(|| ram_address(var).map(|address| SummaryMemoryRegion::Global { address }))
        .or_else(|| exact_dataflow_value(state.roots.get(var)))
}

fn dataflow_memory_location(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<SummaryMemoryLocation> {
    exact_dataflow_value(state.locations.get(var))
        .or_else(|| dataflow_rooted_region(var, state).map(pointer_location_from_region))
}

fn dataflow_stack_root(
    stack_address_roots: Option<&BTreeMap<SSAVar, StackAddressRoot>>,
    addr: &SSAVar,
) -> Option<StackAddressRoot> {
    stack_address_roots?.get(addr).copied()
}

fn dataflow_loaded_source(var: &SSAVar, state: &WorkerDataflowState) -> Option<LoadedSource> {
    if let Some(source) = exact_dataflow_value(state.load_sources.get(var)) {
        return Some(source);
    }
    if let Some((candidate, source)) = state
        .load_sources
        .iter()
        .filter(|(candidate, _)| same_ssa_identity(candidate, var) && candidate.size >= var.size)
        .filter_map(|(candidate, source)| source.exact().map(|source| (candidate, *source)))
        .max_by_key(|(candidate, _)| candidate.size)
    {
        return Some(loaded_source_with_value_width(
            source,
            candidate.size.min(var.size),
        ));
    }
    let requested = x86_register_alias_spec(register_base_name(var))?;
    state
        .load_source_aliases
        .get(&requested.family)?
        .iter()
        .filter_map(|((offset_bits, width_bits, version), source)| {
            let source = source.exact().copied()?;
            let candidate = RegisterAliasSpec {
                family: requested.family.clone(),
                offset_bits: *offset_bits,
                width_bits: *width_bits,
            };
            x86_alias_covers(&candidate, &requested).then_some((*version, *width_bits, source))
        })
        .max_by_key(|(version, width_bits, _)| (*version, *width_bits))
        .map(|(_, _, source)| source)
}

fn dataflow_byte_predicate(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BytePredicateValue> {
    state.byte_predicates.get(var)?.exact().cloned()
}

fn dataflow_zero_comparison(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<ZeroComparisonValue> {
    state.zero_comparisons.get(var)?.exact().cloned()
}

fn source_control_args(source: LoadedSource) -> Option<BTreeSet<usize>> {
    let arg = source_arg(source)?;
    Some(BTreeSet::from([arg]))
}

fn dataflow_control_args(var: &SSAVar, state: &WorkerDataflowState) -> Option<BTreeSet<usize>> {
    state.control_sources.get(var)?.exact().cloned()
}

fn dataflow_control_args_from_operand(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BTreeSet<usize>> {
    dataflow_control_args(var, state)
        .or_else(|| dataflow_loaded_source(var, state).and_then(source_control_args))
}

fn merge_control_args(
    left: Option<BTreeSet<usize>>,
    right: Option<BTreeSet<usize>>,
) -> Option<BTreeSet<usize>> {
    match (left, right) {
        (Some(mut left), Some(right)) => {
            left.extend(right);
            Some(left)
        }
        (Some(left), None) | (None, Some(left)) => Some(left),
        (None, None) => None,
    }
}

fn dataflow_kill_load_source_aliases(dst: &SSAVar, state: &mut WorkerDataflowState) {
    state.byte_predicates.remove(dst);
    state.zero_comparisons.remove(dst);
    let Some(dst_spec) = x86_register_alias_spec(register_base_name(dst)) else {
        state
            .load_sources
            .retain(|candidate, _| !same_ssa_identity(candidate, dst));
        state
            .locations
            .retain(|candidate, _| !same_ssa_identity(candidate, dst));
        insert_unknown_load_source_value(state, dst);
        insert_unknown_control_source_value(state, dst);
        return;
    };
    if let Some(members) = state.load_source_alias_members.remove(&dst_spec.family) {
        for member in members {
            state.load_sources.remove(&member);
        }
    }
    state.load_source_aliases.remove(&dst_spec.family);
    state.locations.remove(dst);
    insert_unknown_load_source_value(state, dst);
    insert_unknown_control_source_value(state, dst);
}

fn dataflow_copy_root_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    if let Some(root) = dataflow_rooted_region(src, state) {
        insert_exact_dataflow_value(&mut state.roots, dst, root);
    }
}

fn dataflow_copy_location_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    if let Some(location) = dataflow_memory_location(src, state) {
        insert_exact_dataflow_value(&mut state.locations, dst, location);
    }
}

fn dataflow_copy_load_source_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    let source = dataflow_loaded_source(src, state);
    let control_args = dataflow_control_args_from_operand(src, state);
    let byte_predicate = dataflow_byte_predicate(src, state);
    let zero_comparison = dataflow_zero_comparison(src, state);
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(source) = source {
        insert_exact_load_source_value(state, dst, source);
    }
    if let Some(control_args) = control_args {
        insert_exact_control_source_value(state, dst, control_args);
    }
    if let Some(byte_predicate) = byte_predicate {
        insert_exact_byte_predicate_value(state, dst, byte_predicate);
    }
    if let Some(zero_comparison) = zero_comparison {
        insert_exact_zero_comparison_value(state, dst, zero_comparison);
    }
}

fn dataflow_copy_binary_root_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &mut WorkerDataflowState,
) {
    let a_root = dataflow_rooted_region(a, state);
    let b_root = dataflow_rooted_region(b, state);
    match (a_root, b_root) {
        (Some(root), None) | (None, Some(root)) => {
            insert_exact_dataflow_value(&mut state.roots, dst, root);
        }
        (Some(a_root), Some(b_root)) if a_root == b_root => {
            insert_exact_dataflow_value(&mut state.roots, dst, a_root);
        }
        _ => {}
    }
}

fn dataflow_copy_phi_root_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    state: &mut WorkerDataflowState,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| dataflow_rooted_region(src, state));
    if let Some(first) = source_roots.next()
        && source_roots.all(|root| root == first)
    {
        insert_exact_dataflow_value(&mut state.roots, dst, first);
    }
}

fn dataflow_copy_phi_location_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    state: &mut WorkerDataflowState,
) {
    let mut source_locations = sources
        .into_iter()
        .filter_map(|src| dataflow_memory_location(src, state));
    if let Some(first) = source_locations.next()
        && source_locations.all(|location| location == first)
    {
        insert_exact_dataflow_value(&mut state.locations, dst, first);
    }
}

fn dataflow_copy_phi_load_source_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    state: &mut WorkerDataflowState,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| dataflow_loaded_source(src, state));
    let source = if let Some(first) = source_roots.next()
        && source_roots.all(|root| root == first)
    {
        Some(first)
    } else {
        None
    };
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(first) = source {
        insert_exact_load_source_value(state, dst, first);
    }
}

fn dataflow_insert_transformed_load_source(
    dst: &SSAVar,
    source: LoadedSource,
    delta: i64,
    state: &mut WorkerDataflowState,
) {
    let source = dataflow_transformed_load_source(source, delta, dst.size);
    dataflow_kill_load_source_aliases(dst, state);
    insert_exact_load_source_value(state, dst, source);
}

fn dataflow_transformed_load_source(
    source: LoadedSource,
    delta: i64,
    dst_size: u32,
) -> LoadedSource {
    LoadedSource {
        location: source.location,
        size: dst_size,
        block_addr: source.block_addr,
        value_delta: source.value_delta.saturating_add(delta),
    }
}

fn const_i64(var: &SSAVar) -> Option<i64> {
    const_value(var).and_then(|value| i64::try_from(value).ok())
}

fn const_signed_i64(var: &SSAVar) -> Option<i64> {
    let value = const_value(var)?;
    let bits = var.size.checked_mul(8)?;
    if bits == 0 || bits > 64 {
        return None;
    }
    if bits == 64 {
        return Some(value as i64);
    }
    let sign_bit = 1u64.checked_shl(bits - 1)?;
    if value & sign_bit == 0 {
        i64::try_from(value).ok()
    } else {
        let modulus = 1i128.checked_shl(bits)?;
        i64::try_from(i128::from(value) - modulus).ok()
    }
}

fn dataflow_copy_additive_load_source(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    subtract_rhs: bool,
    state: &mut WorkerDataflowState,
) {
    let a_source = dataflow_loaded_source(a, state);
    let b_source = dataflow_loaded_source(b, state);
    match (a_source, const_signed_i64(b), b_source, const_signed_i64(a)) {
        (Some(source), Some(delta), None, _) => {
            let delta = if subtract_rhs { -delta } else { delta };
            dataflow_insert_transformed_load_source(dst, source, delta, state);
        }
        (None, _, Some(source), Some(delta)) if !subtract_rhs => {
            dataflow_insert_transformed_load_source(dst, source, delta, state);
        }
        _ => dataflow_kill_load_source_aliases(dst, state),
    }
}

fn dataflow_copy_additive_location(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    subtract_rhs: bool,
    state: &mut WorkerDataflowState,
) {
    let a_location = dataflow_memory_location(a, state);
    let b_location = dataflow_memory_location(b, state);
    let location = match (
        a_location,
        const_signed_i64(b),
        b_location,
        const_signed_i64(a),
    ) {
        (Some(location), Some(delta), None, _) => {
            let delta = if subtract_rhs { -delta } else { delta };
            offset_location(location, delta)
        }
        (None, _, Some(location), Some(delta)) if !subtract_rhs => offset_location(location, delta),
        _ => None,
    };
    state.locations.remove(dst);
    if let Some(location) = location {
        insert_exact_dataflow_value(&mut state.locations, dst, location);
    }
}

fn dataflow_copy_binary_load_source_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &mut WorkerDataflowState,
) {
    let a_source = dataflow_loaded_source(a, state);
    let b_source = dataflow_loaded_source(b, state);
    let control_args = merge_control_args(
        dataflow_control_args_from_operand(a, state),
        dataflow_control_args_from_operand(b, state),
    );
    let source = match (a_source, b_source) {
        (Some(source), None) | (None, Some(source)) => Some(source),
        (Some(a_source), Some(b_source)) if a_source == b_source => Some(a_source),
        _ => None,
    };
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(source) = source {
        insert_exact_load_source_value(state, dst, source);
    }
    if let Some(control_args) = control_args {
        insert_exact_control_source_value(state, dst, control_args);
    }
}

fn copy_load_source_if_known(
    dst: &SSAVar,
    src: &SSAVar,
    load_sources: &mut BTreeMap<SSAVar, LoadedSource>,
) {
    if let Some(source) = loaded_source(src, load_sources) {
        load_sources.insert(dst.clone(), source);
    }
}

fn copy_binary_load_source_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    load_sources: &mut BTreeMap<SSAVar, LoadedSource>,
) {
    let a_source = loaded_source(a, load_sources);
    let b_source = loaded_source(b, load_sources);
    match (a_source, b_source) {
        (Some(source), None) | (None, Some(source)) => {
            load_sources.insert(dst.clone(), source);
        }
        (Some(a_source), Some(b_source)) if a_source.location == b_source.location => {
            load_sources.insert(dst.clone(), a_source);
        }
        _ => {}
    }
}

fn copy_phi_load_source_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    load_sources: &mut BTreeMap<SSAVar, LoadedSource>,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| loaded_source(src, load_sources));
    if let Some(first) = source_roots.next()
        && source_roots.all(|root| root.location == first.location)
    {
        load_sources.insert(dst.clone(), first);
    }
}

pub(super) fn large_cfg_memory_transfers(func: &SsaArtifact) -> BTreeSet<LargeCfgMemoryTransfer> {
    let mut roots = BTreeMap::<SSAVar, SummaryMemoryRegion>::new();
    let mut load_sources = BTreeMap::<SSAVar, LoadedSource>::new();
    let mut transfers = BTreeSet::<LargeCfgMemoryTransfer>::new();

    for block in func.function().blocks() {
        for phi in &block.phis {
            copy_phi_root_if_unambiguous(
                &phi.dst,
                phi.sources.iter().map(|(_, src)| src),
                &mut roots,
            );
            copy_phi_load_source_if_unambiguous(
                &phi.dst,
                phi.sources.iter().map(|(_, src)| src),
                &mut load_sources,
            );
        }

        for op in &block.ops {
            match op {
                SSAOp::Phi { dst, sources } => {
                    copy_phi_root_if_unambiguous(dst, sources, &mut roots);
                    copy_phi_load_source_if_unambiguous(dst, sources, &mut load_sources);
                }
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Subpiece { dst, src, .. }
                | SSAOp::Cast { dst, src }
                | SSAOp::Trunc { dst, src } => {
                    copy_root_if_known(dst, src, &mut roots);
                    copy_load_source_if_known(dst, src, &mut load_sources);
                }
                SSAOp::IntAdd { dst, a, b }
                | SSAOp::IntSub { dst, a, b }
                | SSAOp::IntAnd { dst, a, b }
                | SSAOp::IntOr { dst, a, b }
                | SSAOp::PtrAdd {
                    dst,
                    base: a,
                    index: b,
                    ..
                }
                | SSAOp::PtrSub {
                    dst,
                    base: a,
                    index: b,
                    ..
                } => {
                    copy_binary_root_if_unambiguous(dst, a, b, &mut roots);
                    if matches!(op, SSAOp::IntAnd { .. }) {
                        copy_binary_load_source_if_unambiguous(dst, a, b, &mut load_sources);
                    }
                }
                SSAOp::Load { dst, addr, .. }
                | SSAOp::LoadLinked { dst, addr, .. }
                | SSAOp::LoadGuarded { dst, addr, .. } => {
                    if let Some(region) = rooted_region(addr, &roots) {
                        load_sources.insert(
                            dst.clone(),
                            LoadedSource {
                                location: location_from_region(region, dst.size),
                                size: dst.size,
                                block_addr: block.addr,
                                value_delta: 0,
                            },
                        );
                    }
                }
                SSAOp::Store { addr, val, .. }
                | SSAOp::StoreGuarded { addr, val, .. }
                | SSAOp::StoreConditional { addr, val, .. } => {
                    if let (Some(dst_arg), Some(src_arg)) = (
                        rooted_arg_var(addr, &roots),
                        loaded_source(val, &load_sources).and_then(|source| {
                            match source.location.region {
                                SummaryMemoryRegion::Arg { index } => Some(index),
                                SummaryMemoryRegion::Global { .. }
                                | SummaryMemoryRegion::HeapReturn
                                | SummaryMemoryRegion::Unknown => None,
                            }
                        }),
                    ) && dst_arg != src_arg
                    {
                        transfers.insert(LargeCfgMemoryTransfer {
                            block_addr: block.addr,
                            dst_arg,
                            src_arg,
                            size: val.size,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    transfers
}

pub(super) fn summary_for_transfer(transfer: LargeCfgMemoryTransfer) -> NativeWorkerSummary {
    transfer_worker_summary(
        transfer.block_addr,
        SummaryTransferEffect {
            dst: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg {
                    index: transfer.dst_arg,
                },
                range: Some(SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 0,
                    width: Some(transfer.size),
                }),
            },
            src: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg {
                    index: transfer.src_arg,
                },
                range: Some(SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 0,
                    width: Some(transfer.size),
                }),
            },
            len: SummaryTransferLength::Unknown,
        },
    )
}

fn loop_exit_target(func: &SsaArtifact, header: u64) -> Option<u64> {
    func.function()
        .successors(header)
        .into_iter()
        .find(|target| *target > header)
        .or_else(|| {
            func.function()
                .successors(header)
                .into_iter()
                .find(|target| *target != header)
        })
}

fn loop_summary(
    func: &SsaArtifact,
    header: u64,
    terminator: NativeWorkerTerminator,
    fold: Option<NativeWorkerFold>,
) -> NativeWorkerLoopSummary {
    NativeWorkerLoopSummary {
        header,
        exit_target: loop_exit_target(func, header),
        iterations: None,
        length_arg: None,
        stride: Some(1),
        terminator: Some(terminator),
        fold,
        table_walk: None,
    }
}

fn loop_summary_from_island(
    island: &LoopIsland,
    terminator: NativeWorkerTerminator,
    fold: Option<NativeWorkerFold>,
    length_arg: Option<usize>,
) -> NativeWorkerLoopSummary {
    NativeWorkerLoopSummary {
        header: island.header,
        exit_target: island.exits.iter().copied().next(),
        iterations: None,
        length_arg,
        stride: Some(1),
        terminator: Some(terminator),
        fold,
        table_walk: None,
    }
}

fn collect_natural_loop_islands(func: &SsaArtifact) -> BTreeMap<u64, LoopIsland> {
    let function = func.function();
    let mut islands = BTreeMap::<u64, LoopIsland>::new();
    for &block in function.block_addrs() {
        for succ in function.successors(block) {
            if !function.dominates(succ, block) {
                continue;
            }
            let island = islands.entry(succ).or_insert_with(|| LoopIsland {
                header: succ,
                body: BTreeSet::from([succ]),
                entries: BTreeSet::new(),
                exits: BTreeSet::new(),
            });
            island.body.insert(block);
            let mut stack = vec![block];
            while let Some(current) = stack.pop() {
                for pred in function.predecessors(current) {
                    if island.body.insert(pred) && pred != succ {
                        stack.push(pred);
                    }
                }
            }
        }
    }

    for island in islands.values_mut() {
        for block in island.body.clone() {
            for pred in function.predecessors(block) {
                if !island.body.contains(&pred) {
                    island.entries.insert(block);
                }
            }
            for succ in function.successors(block) {
                if !island.body.contains(&succ) {
                    island.exits.insert(succ);
                }
            }
        }
        if island.entries.is_empty() {
            island.entries.insert(island.header);
        }
    }
    islands
}

fn loop_island_for_anchor(islands: &BTreeMap<u64, LoopIsland>, anchor: u64) -> Option<&LoopIsland> {
    islands
        .values()
        .filter(|island| island.body.contains(&anchor))
        .min_by_key(|island| (island.body.len(), island.header))
}

fn singleton_island(func: &SsaArtifact, anchor: u64) -> LoopIsland {
    let mut entries = BTreeSet::new();
    entries.insert(anchor);
    LoopIsland {
        header: anchor,
        body: BTreeSet::from([anchor]),
        entries,
        exits: func.function().successors(anchor).into_iter().collect(),
    }
}

fn native_loop_summary_from_worker(
    worker: &NativeWorkerSummary,
    island: &LoopIsland,
) -> Option<NativeLoopSummary> {
    let worker_loop = worker.loop_summary.as_ref()?;
    Some(NativeLoopSummary {
        header: worker_loop.header,
        body: island.body.clone(),
        entries: island.entries.clone(),
        exits: island.exits.clone(),
        iterations: worker_loop.iterations,
        length_arg: worker_loop.length_arg,
        stride: worker_loop.stride,
        terminator: worker_loop.terminator,
    })
}

fn location_width(location: Option<SummaryMemoryLocation>) -> Option<u32> {
    location
        .and_then(|location| location.range)
        .and_then(|range| range.width)
}

fn memory_access_kind(kind: NativeWorkerSummaryKind) -> NativeMemoryAccessKind {
    match kind {
        NativeWorkerSummaryKind::MemoryTransfer | NativeWorkerSummaryKind::FileTransfer => {
            NativeMemoryAccessKind::Transfer
        }
        NativeWorkerSummaryKind::MemoryRead
        | NativeWorkerSummaryKind::ProgramOrchestrator
        | NativeWorkerSummaryKind::StringScan
        | NativeWorkerSummaryKind::HashFold
        | NativeWorkerSummaryKind::TableWalk
        | NativeWorkerSummaryKind::PathWalk
        | NativeWorkerSummaryKind::DirectoryTraversal
        | NativeWorkerSummaryKind::RecordStream
        | NativeWorkerSummaryKind::FieldSelection
        | NativeWorkerSummaryKind::OutputStream
        | NativeWorkerSummaryKind::FormatRender
        | NativeWorkerSummaryKind::MetadataProbe
        | NativeWorkerSummaryKind::SortMerge
        | NativeWorkerSummaryKind::NumericTransform
        | NativeWorkerSummaryKind::Parser
        | NativeWorkerSummaryKind::DiagnosticWrapper
        | NativeWorkerSummaryKind::FormatArgumentFetch => NativeMemoryAccessKind::Read,
        NativeWorkerSummaryKind::MemoryWrite => NativeMemoryAccessKind::Write,
        NativeWorkerSummaryKind::MemoryEscape => NativeMemoryAccessKind::Escape,
        NativeWorkerSummaryKind::MemoryFree => NativeMemoryAccessKind::Free,
        NativeWorkerSummaryKind::Allocation => NativeMemoryAccessKind::Allocation,
        NativeWorkerSummaryKind::Lifetime => NativeMemoryAccessKind::Lifetime,
        NativeWorkerSummaryKind::Synchronization => NativeMemoryAccessKind::Synchronization,
        NativeWorkerSummaryKind::Atomic => NativeMemoryAccessKind::Atomic,
        NativeWorkerSummaryKind::Unknown => NativeMemoryAccessKind::Unknown,
    }
}

fn memory_accesses_from_worker(worker: &NativeWorkerSummary) -> Vec<NativeMemoryAccessSummary> {
    let mut accesses = Vec::new();
    let has_explicit_location =
        worker.memory.is_some() || worker.dst.is_some() || worker.src.is_some();
    let has_transfer_len =
        worker.len.is_some() && worker.kind != NativeWorkerSummaryKind::NumericTransform;
    if has_explicit_location || has_transfer_len {
        let kind = if worker.kind == NativeWorkerSummaryKind::NumericTransform
            && worker.dst.is_some()
            && worker.memory.is_none()
        {
            NativeMemoryAccessKind::Write
        } else {
            memory_access_kind(worker.kind)
        };
        accesses.push(NativeMemoryAccessSummary {
            kind,
            location: worker.memory,
            dst: worker.dst,
            src: worker.src,
            len: worker.len,
            width: location_width(worker.memory)
                .or_else(|| location_width(worker.dst))
                .or_else(|| location_width(worker.src)),
        });
    }
    if let Some(effect) = worker.allocation {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Allocation,
            location: None,
            dst: None,
            src: None,
            len: effect.size_arg.map(SummaryTransferLength::Arg),
            width: None,
        });
    }
    if let Some(effect) = worker.lifetime {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Lifetime,
            location: Some(SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: effect.arg },
                range: None,
            }),
            dst: None,
            src: None,
            len: None,
            width: None,
        });
    }
    if let Some(effect) = worker.sync {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Synchronization,
            location: Some(SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: effect.arg },
                range: None,
            }),
            dst: None,
            src: None,
            len: None,
            width: None,
        });
    }
    if let Some(effect) = worker.atomic {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Atomic,
            location: Some(effect.location),
            dst: None,
            src: None,
            len: None,
            width: location_width(Some(effect.location)),
        });
    }
    accesses.sort();
    accesses.dedup();
    accesses
}

fn reductions_from_worker(worker: &NativeWorkerSummary) -> Vec<NativeReductionSummary> {
    worker
        .loop_summary
        .as_ref()
        .and_then(|loop_summary| loop_summary.fold.as_ref())
        .map(|fold| NativeReductionSummary {
            accumulator: fold.accumulator.clone(),
            bits: fold.bits,
            operation: fold.operation,
            source: worker.memory.or(worker.src),
            init: fold.init,
            multiplier: fold.multiplier,
            byte_transform: fold.byte_transform,
        })
        .into_iter()
        .collect()
}

fn region_summary_from_worker(
    func: &SsaArtifact,
    islands: &BTreeMap<u64, LoopIsland>,
    worker: NativeWorkerSummary,
) -> NativeRegionSummary {
    let island = loop_island_for_anchor(islands, worker.anchor)
        .cloned()
        .unwrap_or_else(|| singleton_island(func, worker.anchor));
    let loop_summary = native_loop_summary_from_worker(&worker, &island);
    let blocks = loop_summary
        .as_ref()
        .map(|summary| summary.body.clone())
        .unwrap_or_else(|| island.body.clone());
    let residual_reasons = worker
        .evidence
        .budget_limited
        .then_some(ResidualReason::LargeCfg)
        .into_iter()
        .collect();
    NativeRegionSummary {
        stable_id: stable_region_summary_id(worker.anchor, worker.kind, &blocks),
        anchor: worker.anchor,
        kind: worker.kind,
        blocks,
        entries: island.entries,
        exits: island.exits,
        memory_accesses: memory_accesses_from_worker(&worker),
        loop_summary,
        reductions: reductions_from_worker(&worker),
        parser: worker.parser.clone(),
        residual_reasons,
        confidence: worker.evidence.tier,
        evidence: worker.evidence,
    }
}

pub(super) fn classify_native_region_summaries(
    func: &SsaArtifact,
    worker_summaries: &[NativeWorkerSummary],
) -> Vec<NativeRegionSummary> {
    let islands = collect_natural_loop_islands(func);
    canonical_region_summaries(
        worker_summaries
            .iter()
            .cloned()
            .map(|worker| region_summary_from_worker(func, &islands, worker))
            .collect(),
    )
}

fn source_arg(source: LoadedSource) -> Option<usize> {
    match source.location.region {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    }
}

fn fold_observation_has_accumulator_identity(fold: &FoldObservation) -> bool {
    !SSAVarNameKind::classify(&fold.accumulator).is_constant()
}

fn loaded_source_access_width(source: LoadedSource) -> u32 {
    source
        .location
        .range
        .and_then(|range| range.width)
        .unwrap_or(source.size)
}

fn fold_observation_has_hash_stream_source(fold: &FoldObservation) -> bool {
    fold_observation_has_accumulator_identity(fold) && loaded_source_access_width(fold.source) == 1
}

fn dataflow_loaded_compare<'a>(
    a: &'a SSAVar,
    b: &'a SSAVar,
    state: &WorkerDataflowState,
) -> Option<(LoadedSource, &'a SSAVar)> {
    dataflow_loaded_source(a, state)
        .map(|source| (source, b))
        .or_else(|| dataflow_loaded_source(b, state).map(|source| (source, a)))
}

fn dataflow_compare_control_args(
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BTreeSet<usize>> {
    merge_control_args(
        dataflow_control_args_from_operand(a, state),
        dataflow_control_args_from_operand(b, state),
    )
}

fn dataflow_loaded_binary_source(
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<(LoadedSource, String)> {
    dataflow_loaded_source(a, state)
        .map(|source| (source, b.display_name()))
        .or_else(|| dataflow_loaded_source(b, state).map(|source| (source, a.display_name())))
}

fn dataflow_arg_index(var: &SSAVar, state: &WorkerDataflowState) -> Option<usize> {
    abi_input_arg_index(var).or_else(|| match dataflow_rooted_region(var, state)? {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    })
}

fn dataflow_tracked_arg_index(var: &SSAVar, state: &WorkerDataflowState) -> Option<usize> {
    match exact_dataflow_value(state.roots.get(var))? {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    }
}

fn byte_eq_predicate_for_operand(
    source: LoadedSource,
    other: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<NativeWorkerPredicate> {
    if let Some(arg) = dataflow_arg_index(other, state)
        && source.value_delta == 0
    {
        return Some(NativeWorkerPredicate::ByteEqArg { arg });
    }
    let raw = const_i64(other)?;
    let value = raw.checked_sub(source.value_delta)?;
    (0..=i64::from(u8::MAX))
        .contains(&value)
        .then_some(NativeWorkerPredicate::ByteEqConst { value: value as u8 })
}

fn byte_predicate_from_loaded_compare(
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BytePredicateValue> {
    dataflow_loaded_source(a, state)
        .and_then(|source| {
            byte_eq_predicate_for_operand(source, b, state)
                .map(|predicate| BytePredicateValue { source, predicate })
        })
        .or_else(|| {
            dataflow_loaded_source(b, state).and_then(|source| {
                byte_eq_predicate_for_operand(source, a, state)
                    .map(|predicate| BytePredicateValue { source, predicate })
            })
        })
}

fn byte_predicate_from_zero_compare(
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BytePredicateValue> {
    if const_value(b) == Some(0) {
        return dataflow_byte_predicate(a, state);
    }
    if const_value(a) == Some(0) {
        return dataflow_byte_predicate(b, state);
    }
    None
}

fn zero_comparison_value(
    a: &SSAVar,
    b: &SSAVar,
    branch_when_zero: bool,
) -> Option<ZeroComparisonValue> {
    if const_value(b) == Some(0) {
        return Some(ZeroComparisonValue {
            value: a.clone(),
            branch_when_zero,
        });
    }
    if const_value(a) == Some(0) {
        return Some(ZeroComparisonValue {
            value: b.clone(),
            branch_when_zero,
        });
    }
    None
}

fn numeric_transform_binary_observation(
    anchor: u64,
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
    operation: NativeWorkerFoldOperation,
) -> Option<NumericTransformObservation> {
    if dataflow_loaded_binary_source(a, b, state).is_some() {
        return None;
    }
    let length_arg = dataflow_arg_index(a, state).or_else(|| dataflow_arg_index(b, state));
    let has_const_operand = const_value(a).is_some() || const_value(b).is_some();
    if length_arg.is_none() && !has_const_operand {
        return None;
    }
    Some(NumericTransformObservation {
        anchor,
        dst_arg: dataflow_tracked_arg_index(dst, state),
        length_arg,
        accumulator: dst.display_name(),
        bits: dst.size.saturating_mul(8),
        operation,
    })
}

fn numeric_increment_observation(
    anchor: u64,
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<NumericTransformObservation> {
    let non_const_operand = match (const_value(a).is_some(), const_value(b).is_some()) {
        (true, false) => b,
        (false, true) => a,
        _ => return None,
    };
    if dataflow_loaded_source(non_const_operand, state).is_some()
        || dataflow_tracked_arg_index(non_const_operand, state).is_some()
    {
        return None;
    }
    Some(NumericTransformObservation {
        anchor,
        dst_arg: dataflow_tracked_arg_index(dst, state),
        length_arg: None,
        accumulator: dst.display_name(),
        bits: dst.size.saturating_mul(8),
        operation: NativeWorkerFoldOperation::Add,
    })
}

fn numeric_transform_unary_observation(
    anchor: u64,
    dst: &SSAVar,
    src: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<NumericTransformObservation> {
    if dataflow_loaded_source(src, state).is_some() {
        return None;
    }
    let length_arg = dataflow_arg_index(src, state)?;
    Some(NumericTransformObservation {
        anchor,
        dst_arg: dataflow_tracked_arg_index(dst, state),
        length_arg: Some(length_arg),
        accumulator: dst.display_name(),
        bits: dst.size.saturating_mul(8),
        operation: NativeWorkerFoldOperation::Add,
    })
}

fn merge_parser_byte_value(
    observations: &mut BlockWorkerObservations,
    arg: usize,
    anchor: u64,
    value: u8,
) {
    let evidence = observations
        .parser_comparisons
        .entry(arg)
        .or_insert_with(|| ParserLoopEvidence {
            anchor,
            ..ParserLoopEvidence::default()
        });
    evidence.anchor = evidence.anchor.min(anchor);
    evidence.byte_values.insert(value);
    if matches!(value, b'+' | b'-') {
        evidence.accepts_sign = true;
    }
}

fn merge_parser_byte_range(
    observations: &mut BlockWorkerObservations,
    arg: usize,
    anchor: u64,
    range: ParserByteRange,
) {
    let evidence = observations
        .parser_comparisons
        .entry(arg)
        .or_insert_with(|| ParserLoopEvidence {
            anchor,
            ..ParserLoopEvidence::default()
        });
    evidence.anchor = evidence.anchor.min(anchor);
    evidence.byte_ranges.insert(range);
}

fn byte_range_from_upper_bound(
    source: LoadedSource,
    inclusive_upper: i64,
) -> Option<ParserByteRange> {
    if source.value_delta == -i64::from(b'0') && inclusive_upper == 9 {
        return Some(ParserByteRange { lo: b'0', hi: b'9' });
    }
    if source.value_delta == -i64::from(b'0') && (0..9).contains(&inclusive_upper) {
        return Some(ParserByteRange {
            lo: b'0',
            hi: b'0'.checked_add(u8::try_from(inclusive_upper).ok()?)?,
        });
    }
    let hi = inclusive_upper.saturating_sub(source.value_delta);
    if !(0..=255).contains(&hi) {
        return None;
    }
    Some(ParserByteRange {
        lo: 0,
        hi: hi as u8,
    })
}

fn byte_range_from_lower_bound(
    source: LoadedSource,
    inclusive_lower: i64,
) -> Option<ParserByteRange> {
    let lo = inclusive_lower.saturating_sub(source.value_delta);
    if !(0..=255).contains(&lo) {
        return None;
    }
    Some(ParserByteRange {
        lo: lo as u8,
        hi: u8::MAX,
    })
}

fn record_parser_range_compare(
    observations: &mut BlockWorkerObservations,
    block_addr: u64,
    source: LoadedSource,
    other: &SSAVar,
    source_on_left: bool,
    less_equal: bool,
) {
    let Some(arg) = source_arg(source) else {
        return;
    };
    let Some(raw_bound) = const_i64(other) else {
        return;
    };
    let range = if source_on_left {
        let upper = if less_equal {
            raw_bound
        } else {
            raw_bound.saturating_sub(1)
        };
        byte_range_from_upper_bound(source, upper)
    } else {
        let lower = if less_equal {
            raw_bound
        } else {
            raw_bound.saturating_add(1)
        };
        byte_range_from_lower_bound(source, lower)
    };
    if let Some(range) = range {
        merge_parser_byte_range(observations, arg, block_addr, range);
    }
}

fn scan_worker_kind(
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummaryKind {
    let arg_pointer_null_scan = matches!(source.location.region, SummaryMemoryRegion::Arg { .. })
        && source.size >= 4
        && matches!(
            terminator,
            NativeWorkerTerminator::ZeroByte | NativeWorkerTerminator::ByteEquals(0)
        );
    match (source.location.region, terminator) {
        (SummaryMemoryRegion::Global { .. }, _) => NativeWorkerSummaryKind::TableWalk,
        _ if arg_pointer_null_scan => NativeWorkerSummaryKind::TableWalk,
        (_, NativeWorkerTerminator::ByteEquals(b'/' | b'\\' | b':' | b'.')) => {
            NativeWorkerSummaryKind::PathWalk
        }
        (_, NativeWorkerTerminator::ZeroByte) => NativeWorkerSummaryKind::StringScan,
        _ => NativeWorkerSummaryKind::MemoryRead,
    }
}

fn scan_summary(
    func: &SsaArtifact,
    anchor: u64,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    let kind = scan_worker_kind(source, terminator);
    NativeWorkerSummary {
        anchor,
        kind,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary(func, anchor, terminator, None)),
        evidence: bounded_evidence(),
    }
}

fn scan_summary_for_island(
    island: &LoopIsland,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    let kind = scan_worker_kind(source, terminator);
    NativeWorkerSummary {
        anchor: island.header,
        kind,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary_from_island(island, terminator, None, None)),
        evidence: bounded_evidence(),
    }
}

fn table_walk_summary_for_island(island: &LoopIsland, source: LoadedSource) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor: island.header,
        kind: NativeWorkerSummaryKind::TableWalk,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary_from_island(
            island,
            NativeWorkerTerminator::Unknown,
            None,
            None,
        )),
        evidence: bounded_evidence(),
    }
}

fn parser_summary(
    func: &SsaArtifact,
    anchor: u64,
    arg: usize,
    dst_arg: Option<usize>,
    parser: NativeParserSummary,
    value_fold: Option<NativeWorkerFold>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: arg },
            range: Some(SummaryMemoryRange {
                offset_lo: 0,
                offset_hi: 0,
                width: Some(1),
            }),
        }),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(parser),
        loop_summary: Some(loop_summary(
            func,
            anchor,
            NativeWorkerTerminator::Unknown,
            value_fold,
        )),
        evidence: bounded_evidence(),
    }
}

fn parser_summary_for_island(
    island: &LoopIsland,
    arg: usize,
    dst_arg: Option<usize>,
    parser: NativeParserSummary,
    value_fold: Option<NativeWorkerFold>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor: island.header,
        kind: NativeWorkerSummaryKind::Parser,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: arg },
            range: Some(SummaryMemoryRange {
                offset_lo: 0,
                offset_hi: 0,
                width: Some(1),
            }),
        }),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(parser),
        loop_summary: Some(loop_summary_from_island(
            island,
            NativeWorkerTerminator::Unknown,
            value_fold,
            None,
        )),
        evidence: bounded_evidence(),
    }
}

fn numeric_transform_summary_for_island(
    island: &LoopIsland,
    observation: NumericTransformObservation,
) -> NativeWorkerSummary {
    let length_arg = observation.length_arg;
    let terminator = length_arg
        .map(|_| NativeWorkerTerminator::LengthBound)
        .unwrap_or(NativeWorkerTerminator::Unknown);
    numeric_transform_worker_summary_with_loop(
        island.header,
        observation.dst_arg,
        length_arg,
        observation.accumulator,
        observation.bits,
        observation.operation,
        loop_summary_from_island(island, terminator, None, length_arg),
    )
}

fn numeric_transform_summary(
    func: &SsaArtifact,
    observation: NumericTransformObservation,
) -> NativeWorkerSummary {
    let length_arg = observation.length_arg;
    let terminator = length_arg
        .map(|_| NativeWorkerTerminator::LengthBound)
        .unwrap_or(NativeWorkerTerminator::Unknown);
    let exit_target = func
        .function()
        .successors(observation.anchor)
        .into_iter()
        .next();
    numeric_transform_worker_summary_with_loop(
        observation.anchor,
        observation.dst_arg,
        observation.length_arg,
        observation.accumulator,
        observation.bits,
        observation.operation,
        NativeWorkerLoopSummary {
            header: observation.anchor,
            exit_target,
            iterations: None,
            length_arg,
            stride: None,
            terminator: Some(terminator),
            fold: None,
            table_walk: None,
        },
    )
}

fn infer_length_arg_for_memory_arg(func: &SsaArtifact, memory_arg: usize) -> Option<usize> {
    let mut candidates = BTreeSet::<usize>::new();
    for block in func.function().blocks() {
        for op in &block.ops {
            let operands = match op {
                SSAOp::IntAdd { a, b, .. }
                | SSAOp::PtrAdd {
                    base: a, index: b, ..
                }
                | SSAOp::IntSub { a, b, .. }
                | SSAOp::PtrSub {
                    base: a, index: b, ..
                } => Some((a, b)),
                _ => None,
            };
            let Some((a, b)) = operands else {
                continue;
            };
            match (abi_input_arg_index(a), abi_input_arg_index(b)) {
                (Some(left), Some(right)) if left == memory_arg && right != memory_arg => {
                    candidates.insert(right);
                }
                (Some(left), Some(right)) if right == memory_arg && left != memory_arg => {
                    candidates.insert(left);
                }
                _ => {}
            }
        }
    }
    (candidates.len() == 1).then(|| *candidates.iter().next().expect("single length arg"))
}

fn combined_worker_predicate(
    predicates: BTreeSet<NativeWorkerPredicate>,
) -> Option<NativeWorkerPredicate> {
    let mut predicates: Vec<_> = predicates.into_iter().collect();
    match predicates.len() {
        0 => None,
        1 => predicates.pop(),
        _ => Some(NativeWorkerPredicate::AnyOf(predicates)),
    }
}

fn predicated_numeric_transform_summary_for_island(
    island: &LoopIsland,
    transform: &NumericTransformObservation,
    source: LoadedSource,
    length_arg: usize,
    predicate: NativeWorkerPredicate,
) -> NativeWorkerSummary {
    let fold = NativeWorkerFold {
        accumulator: transform.accumulator.clone(),
        bits: transform.bits,
        operation: transform.operation,
        predicate: Some(predicate),
        init: None,
        multiplier: None,
        byte_transform: None,
    };
    NativeWorkerSummary {
        anchor: island.header,
        kind: NativeWorkerSummaryKind::NumericTransform,
        dst: transform.dst_arg.map(arg_location),
        src: None,
        memory: Some(source.location),
        len: Some(SummaryTransferLength::Arg(length_arg)),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary_from_island(
            island,
            NativeWorkerTerminator::LengthBound,
            Some(fold),
            Some(length_arg),
        )),
        evidence: bounded_evidence(),
    }
}

fn infer_loop_accumulator_init(
    func: &SsaArtifact,
    island: &LoopIsland,
    accumulator: &str,
) -> Option<u64> {
    for block_addr in &island.body {
        let Some(block) = func.function().get_block(*block_addr) else {
            continue;
        };
        for phi in &block.phis {
            if phi.dst.display_name() != accumulator {
                continue;
            }
            let mut constants = BTreeSet::new();
            for (pred, src) in &phi.sources {
                if !island.body.contains(pred)
                    && let Some(value) = resolved_const_value(func, src)
                {
                    constants.insert(value);
                }
            }
            if constants.len() == 1 {
                return constants.into_iter().next();
            }
        }
    }
    None
}

fn signed_resolved_const_value(func: &SsaArtifact, var: &SSAVar) -> Option<i64> {
    resolved_const_value(func, var).map(|value| value as i64)
}

fn infer_loop_multiplier(func: &SsaArtifact, island: &LoopIsland) -> Option<u64> {
    let mut constants = BTreeSet::new();
    for block_addr in &island.body {
        let Some(block) = func.function().get_block(*block_addr) else {
            continue;
        };
        for op in &block.ops {
            if let SSAOp::IntMult { a, b, .. } = op {
                if let Some(value) = resolved_const_value(func, a).filter(|value| *value > 0xff) {
                    constants.insert(value);
                }
                if let Some(value) = resolved_const_value(func, b).filter(|value| *value > 0xff) {
                    constants.insert(value);
                }
            }
        }
    }
    (constants.len() == 1).then(|| *constants.iter().next().expect("single multiplier"))
}

fn loop_has_ascii_lowercase_transform(func: &SsaArtifact, island: &LoopIsland) -> bool {
    let mut has_upper_base = false;
    let mut has_upper_bound = false;
    let mut has_lower_delta = false;
    for block_addr in &island.body {
        let Some(block) = func.function().get_block(*block_addr) else {
            continue;
        };
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { a, b, .. } => {
                    let constants = [
                        signed_resolved_const_value(func, a),
                        signed_resolved_const_value(func, b),
                    ];
                    has_upper_base |= constants.contains(&Some(-65));
                    has_lower_delta |= constants.contains(&Some(32));
                }
                SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
                    let constants = [resolved_const_value(func, a), resolved_const_value(func, b)];
                    has_upper_bound |= constants.contains(&Some(26));
                }
                _ => {}
            }
        }
    }
    has_upper_base && has_upper_bound && has_lower_delta
}

fn enrich_hash_fold_summary_for_island(
    func: &SsaArtifact,
    island: &LoopIsland,
    source: LoadedSource,
    summary: &mut NativeWorkerSummary,
) {
    let length_arg = source_arg(source).and_then(|arg| infer_length_arg_for_memory_arg(func, arg));
    if let Some(length_arg) = length_arg {
        summary.len = Some(SummaryTransferLength::Arg(length_arg));
    }
    let Some(loop_summary) = summary.loop_summary.as_mut() else {
        return;
    };
    if let Some(length_arg) = length_arg {
        loop_summary.length_arg = Some(length_arg);
        loop_summary.terminator = Some(NativeWorkerTerminator::LengthBound);
    }
    let Some(fold) = loop_summary.fold.as_mut() else {
        return;
    };
    fold.init = infer_loop_accumulator_init(func, island, &fold.accumulator);
    fold.multiplier = infer_loop_multiplier(func, island);
    if loop_has_ascii_lowercase_transform(func, island) {
        fold.byte_transform = Some(NativeWorkerByteTransform::AsciiLowercase);
    }
}

fn transfer_worker_block(
    block: &r2ssa::function::SSABlock,
    input: &WorkerDataflowState,
    mut observations: Option<&mut BlockWorkerObservations>,
    stack_address_roots: Option<&BTreeMap<SSAVar, StackAddressRoot>>,
) -> WorkerDataflowState {
    let mut state = input.clone();
    for phi in &block.phis {
        dataflow_copy_phi_root_if_unambiguous(
            &phi.dst,
            phi.sources.iter().map(|(_, src)| src),
            &mut state,
        );
        dataflow_copy_phi_load_source_if_unambiguous(
            &phi.dst,
            phi.sources.iter().map(|(_, src)| src),
            &mut state,
        );
        dataflow_copy_phi_location_if_unambiguous(
            &phi.dst,
            phi.sources.iter().map(|(_, src)| src),
            &mut state,
        );
    }

    for op in &block.ops {
        match op {
            SSAOp::Phi { dst, sources } => {
                dataflow_copy_phi_root_if_unambiguous(dst, sources, &mut state);
                dataflow_copy_phi_load_source_if_unambiguous(dst, sources, &mut state);
                dataflow_copy_phi_location_if_unambiguous(dst, sources, &mut state);
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Subpiece { dst, src, .. }
            | SSAOp::Cast { dst, src }
            | SSAOp::Trunc { dst, src } => {
                dataflow_copy_root_if_known(dst, src, &mut state);
                dataflow_copy_load_source_if_known(dst, src, &mut state);
                dataflow_copy_location_if_known(dst, src, &mut state);
            }
            SSAOp::IntAdd { dst, a, b }
            | SSAOp::PtrAdd {
                dst,
                base: a,
                index: b,
                ..
            } => {
                dataflow_copy_binary_root_if_unambiguous(dst, a, b, &mut state);
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.folds.push(FoldObservation {
                        anchor: block.addr,
                        source,
                        accumulator,
                        operation: NativeWorkerFoldOperation::Add,
                    });
                }
                if matches!(op, SSAOp::IntAdd { .. })
                    && is_return_value_var(dst)
                    && let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.returns.push(ReturnObservation {
                        anchor: block.addr,
                        field_plus_count: Some((source, accumulator)),
                        negative_count_return: false,
                    });
                }
                if matches!(op, SSAOp::IntAdd { .. })
                    && let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) =
                        numeric_increment_observation(block.addr, dst, a, b, &state)
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_copy_additive_load_source(dst, a, b, false, &mut state);
                dataflow_copy_additive_location(dst, a, b, false, &mut state);
            }
            SSAOp::IntSub { dst, a, b }
            | SSAOp::PtrSub {
                dst,
                base: a,
                index: b,
                ..
            } => {
                dataflow_copy_binary_root_if_unambiguous(dst, a, b, &mut state);
                let byte_predicate = byte_predicate_from_loaded_compare(a, b, &state);
                dataflow_copy_additive_load_source(dst, a, b, true, &mut state);
                dataflow_copy_additive_location(dst, a, b, true, &mut state);
                if let Some(byte_predicate) = byte_predicate {
                    insert_exact_byte_predicate_value(&mut state, dst, byte_predicate);
                }
            }
            SSAOp::IntMult { dst, a, b }
            | SSAOp::IntDiv { dst, a, b }
            | SSAOp::IntSDiv { dst, a, b }
            | SSAOp::IntRem { dst, a, b }
            | SSAOp::IntSRem { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) = numeric_transform_binary_observation(
                        block.addr,
                        dst,
                        a,
                        b,
                        &state,
                        NativeWorkerFoldOperation::Add,
                    )
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::IntAnd { dst, a, b } | SSAOp::IntOr { dst, a, b } => {
                dataflow_copy_binary_root_if_unambiguous(dst, a, b, &mut state);
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::IntXor { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.folds.push(FoldObservation {
                        anchor: block.addr,
                        source,
                        accumulator,
                        operation: NativeWorkerFoldOperation::Xor,
                    });
                }
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::IntLeft { dst, a, b }
            | SSAOp::IntRight { dst, a, b }
            | SSAOp::IntSRight { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.folds.push(FoldObservation {
                        anchor: block.addr,
                        source,
                        accumulator,
                        operation: NativeWorkerFoldOperation::RotateMix,
                    });
                }
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) = numeric_transform_binary_observation(
                        block.addr,
                        dst,
                        a,
                        b,
                        &state,
                        NativeWorkerFoldOperation::RotateMix,
                    )
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::PopCount { dst, src } | SSAOp::Lzcount { dst, src } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) =
                        numeric_transform_unary_observation(block.addr, dst, src, &state)
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::IntNot { dst, src } | SSAOp::IntNegate { dst, src } => {
                if is_return_value_var(dst)
                    && const_value(src).is_none()
                    && let Some(observations) = observations.as_deref_mut()
                {
                    observations.returns.push(ReturnObservation {
                        anchor: block.addr,
                        field_plus_count: None,
                        negative_count_return: true,
                    });
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::IntEqual { dst, a, b } | SSAOp::IntNotEqual { dst, a, b } => {
                let control_args = dataflow_compare_control_args(a, b, &state);
                let branch_when_zero = matches!(op, SSAOp::IntEqual { .. });
                let zero_comparison = zero_comparison_value(a, b, branch_when_zero);
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, other)) = dataflow_loaded_compare(a, b, &state)
                {
                    let terminator = const_value(other)
                        .map(|value| {
                            if value == 0 {
                                NativeWorkerTerminator::ZeroByte
                            } else {
                                NativeWorkerTerminator::ByteEquals((value & 0xff) as u8)
                            }
                        })
                        .unwrap_or(NativeWorkerTerminator::Unknown);
                    if let Some(arg) = source_arg(source)
                        && let Some(raw_value) = const_i64(other)
                        && let Some(value) = raw_value.checked_sub(source.value_delta)
                        && (0..=i64::from(u8::MAX)).contains(&value)
                    {
                        merge_parser_byte_value(observations, arg, block.addr, value as u8);
                    }
                    observations.scans.push(ScanObservation {
                        anchor: block.addr,
                        source,
                        terminator,
                    });
                }
                if let Some(observations) = observations.as_deref_mut() {
                    let byte_predicate = byte_predicate_from_zero_compare(a, b, &state)
                        .or_else(|| byte_predicate_from_loaded_compare(a, b, &state));
                    if let Some(byte_predicate) = byte_predicate {
                        observations.byte_predicates.push(BytePredicateObservation {
                            anchor: block.addr,
                            source: byte_predicate.source,
                            predicate: byte_predicate.predicate,
                        });
                    }
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
                if let Some(zero_comparison) = zero_comparison {
                    insert_exact_zero_comparison_value(&mut state, dst, zero_comparison);
                }
            }
            SSAOp::IntLess { dst, a, b } | SSAOp::IntSLess { dst, a, b } => {
                let control_args = dataflow_compare_control_args(a, b, &state);
                if let Some(observations) = observations.as_deref_mut() {
                    if let Some(source) = dataflow_loaded_source(a, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            b,
                            true,
                            false,
                        );
                    }
                    if let Some(source) = dataflow_loaded_source(b, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            a,
                            false,
                            false,
                        );
                    }
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::IntLessEqual { dst, a, b } | SSAOp::IntSLessEqual { dst, a, b } => {
                let control_args = dataflow_compare_control_args(a, b, &state);
                if let Some(observations) = observations.as_deref_mut() {
                    if let Some(source) = dataflow_loaded_source(a, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            b,
                            true,
                            true,
                        );
                    }
                    if let Some(source) = dataflow_loaded_source(b, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            a,
                            false,
                            true,
                        );
                    }
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::BoolNot { dst, src } => {
                let control_args = dataflow_control_args_from_operand(src, &state);
                let zero_comparison = dataflow_zero_comparison(src, &state).map(|mut value| {
                    value.branch_when_zero = !value.branch_when_zero;
                    value
                });
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
                if let Some(zero_comparison) = zero_comparison {
                    insert_exact_zero_comparison_value(&mut state, dst, zero_comparison);
                }
            }
            SSAOp::BoolAnd { dst, a, b }
            | SSAOp::BoolOr { dst, a, b }
            | SSAOp::BoolXor { dst, a, b } => {
                let control_args = merge_control_args(
                    dataflow_control_args_from_operand(a, &state),
                    dataflow_control_args_from_operand(b, &state),
                );
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::Load { dst, addr, .. }
            | SSAOp::LoadLinked { dst, addr, .. }
            | SSAOp::LoadGuarded { dst, addr, .. } => {
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(stack_root) = dataflow_stack_root(stack_address_roots, addr)
                    && let Some(root) = exact_dataflow_value(state.stack_values.get(&stack_root))
                {
                    insert_exact_dataflow_value(&mut state.roots, dst, root);
                }
                if let Some(location) = dataflow_memory_location(addr, &state) {
                    let location = location_with_access_width(location, dst.size);
                    let source = LoadedSource {
                        location,
                        size: dst.size,
                        block_addr: block.addr,
                        value_delta: 0,
                    };
                    if let Some(observations) = observations.as_deref_mut()
                        && matches!(location.region, SummaryMemoryRegion::Global { .. })
                    {
                        observations.global_loads.push(GlobalLoadObservation {
                            anchor: block.addr,
                            source,
                        });
                    }
                    if let Some(observations) = observations.as_deref_mut()
                        && let SummaryMemoryRegion::Arg { index } = location.region
                    {
                        observations
                            .option_string_reads
                            .push(OptionStringReadObservation {
                                anchor: block.addr,
                                arg: index,
                            });
                    }
                    insert_exact_load_source_value(&mut state, dst, source);
                }
            }
            SSAOp::Store { addr, val, .. } => {
                if let Some(stack_root) = dataflow_stack_root(stack_address_roots, addr) {
                    if let Some(root) = dataflow_rooted_region(val, &state) {
                        insert_exact_dataflow_value(&mut state.stack_values, &stack_root, root);
                    } else {
                        insert_dataflow_value(
                            &mut state.stack_values,
                            &stack_root,
                            DataflowValue::Unknown,
                        );
                    }
                }
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(location) = dataflow_memory_location(addr, &state)
                {
                    observations.memory_writes.push(MemoryWriteObservation {
                        anchor: block.addr,
                        location: location_with_access_width(location, val.size),
                        width: val.size,
                    });
                }
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(SummaryMemoryRegion::Arg { index }) =
                        dataflow_rooted_region(addr, &state)
                    && let Some(value) =
                        const_value(val).filter(|value| *value <= u64::from(u8::MAX))
                {
                    observations
                        .option_string_writes
                        .push(OptionStringWriteObservation {
                            anchor: block.addr,
                            arg: index,
                            value: value as u8,
                            control_args: BTreeSet::new(),
                        });
                }
            }
            SSAOp::StoreGuarded {
                addr, val, guard, ..
            } => {
                let control_args =
                    dataflow_control_args_from_operand(guard, &state).unwrap_or_default();
                if let Some(stack_root) = dataflow_stack_root(stack_address_roots, addr) {
                    if let Some(root) = dataflow_rooted_region(val, &state) {
                        insert_exact_dataflow_value(&mut state.stack_values, &stack_root, root);
                    } else {
                        insert_dataflow_value(
                            &mut state.stack_values,
                            &stack_root,
                            DataflowValue::Unknown,
                        );
                    }
                }
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(location) = dataflow_memory_location(addr, &state)
                {
                    observations.memory_writes.push(MemoryWriteObservation {
                        anchor: block.addr,
                        location: location_with_access_width(location, val.size),
                        width: val.size,
                    });
                }
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(SummaryMemoryRegion::Arg { index }) =
                        dataflow_rooted_region(addr, &state)
                    && let Some(value) =
                        const_value(val).filter(|value| *value <= u64::from(u8::MAX))
                {
                    observations
                        .option_string_writes
                        .push(OptionStringWriteObservation {
                            anchor: block.addr,
                            arg: index,
                            value: value as u8,
                            control_args,
                        });
                }
            }
            SSAOp::CBranch { target, cond } => {
                if let Some(control_args) = dataflow_control_args_from_operand(cond, &state)
                    && let Some(observations) = observations.as_deref_mut()
                {
                    observations
                        .option_string_branch_controls
                        .extend(control_args);
                }
                if let Some(zero_comparison) = dataflow_zero_comparison(cond, &state)
                    && let Some(observations) = observations.as_deref_mut()
                {
                    let source = dataflow_loaded_source(&zero_comparison.value, &state);
                    observations.zero_guards.push(ZeroGuardObservation {
                        anchor: block.addr,
                        target: ram_address(target),
                        value: zero_comparison.value,
                        branch_when_zero: zero_comparison.branch_when_zero,
                        source,
                    });
                }
            }
            SSAOp::CpuId { dst } => {
                if let Some(observations) = observations.as_deref_mut() {
                    observations.global_loads.push(GlobalLoadObservation {
                        anchor: block.addr,
                        source: LoadedSource {
                            location: SummaryMemoryLocation {
                                region: SummaryMemoryRegion::Unknown,
                                range: None,
                            },
                            size: dst.size,
                            block_addr: block.addr,
                            value_delta: 0,
                        },
                    });
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            _ => {
                if let Some(dst) = op.dst() {
                    dataflow_kill_load_source_aliases(dst, &mut state);
                }
            }
        }
    }
    state
}

fn compute_worker_dataflow_inputs(func: &SsaArtifact) -> BTreeMap<u64, WorkerDataflowState> {
    let function = func.function();
    let stack_address_roots = function
        .decompile_prep_facts()
        .map(|facts| &facts.stack_address_roots);
    let block_addrs = function.block_addrs();
    let mut inputs = BTreeMap::<u64, WorkerDataflowState>::new();
    let mut outputs = BTreeMap::<u64, WorkerDataflowState>::new();
    let mut changed = true;

    while changed {
        changed = false;
        for block_addr in block_addrs {
            let mut input = WorkerDataflowState::default();
            for pred in function.predecessors(*block_addr) {
                if let Some(pred_output) = outputs.get(&pred) {
                    let _ = join_worker_state(&mut input, pred_output);
                }
            }
            if inputs.get(block_addr) != Some(&input) {
                inputs.insert(*block_addr, input.clone());
                changed = true;
            }
            let Some(block) = function.get_block(*block_addr) else {
                continue;
            };
            let output = transfer_worker_block(block, &input, None, stack_address_roots);
            if outputs.get(block_addr) != Some(&output) {
                outputs.insert(*block_addr, output);
                changed = true;
            }
        }
    }

    inputs
}

fn collect_block_worker_observations(func: &SsaArtifact) -> BTreeMap<u64, BlockWorkerObservations> {
    let inputs = compute_worker_dataflow_inputs(func);
    let stack_address_roots = func
        .function()
        .decompile_prep_facts()
        .map(|facts| &facts.stack_address_roots);
    let mut observations = BTreeMap::new();
    for block in func.function().blocks() {
        let input = inputs.get(&block.addr).cloned().unwrap_or_default();
        let mut block_observations = BlockWorkerObservations::default();
        let _ = transfer_worker_block(
            block,
            &input,
            Some(&mut block_observations),
            stack_address_roots,
        );
        observations.insert(block.addr, block_observations);
    }
    observations
}

fn merge_parser_evidence(left: &mut ParserLoopEvidence, right: ParserLoopEvidence) {
    if left.anchor == 0 {
        left.anchor = right.anchor;
    } else {
        left.anchor = left.anchor.min(right.anchor);
    }
    left.byte_values.extend(right.byte_values);
    left.byte_ranges.extend(right.byte_ranges);
    left.accepts_sign |= right.accepts_sign;
}

fn loop_effect_summaries(
    func: &SsaArtifact,
    observations: BTreeMap<u64, BlockWorkerObservations>,
) -> Vec<LoopEffectSummary> {
    let islands = collect_natural_loop_islands(func);
    let mut summaries = BTreeMap::<u64, LoopEffectSummary>::new();
    for (block_addr, block_observations) in observations {
        let (island, natural_loop) = loop_island_for_anchor(&islands, block_addr)
            .cloned()
            .map(|island| (island, true))
            .unwrap_or_else(|| (singleton_island(func, block_addr), false));
        let summary = summaries
            .entry(island.header)
            .or_insert_with(|| LoopEffectSummary {
                island,
                natural_loop,
                ..LoopEffectSummary::default()
            });
        summary.scans.extend(block_observations.scans);
        summary.folds.extend(block_observations.folds);
        summary.global_loads.extend(block_observations.global_loads);
        summary
            .memory_writes
            .extend(block_observations.memory_writes);
        summary
            .numeric_transforms
            .extend(block_observations.numeric_transforms);
        summary
            .byte_predicates
            .extend(block_observations.byte_predicates);
        summary.zero_guards.extend(block_observations.zero_guards);
        for (arg, evidence) in block_observations.parser_comparisons {
            merge_parser_evidence(summary.parser_comparisons.entry(arg).or_default(), evidence);
        }
    }
    summaries.into_values().collect()
}

fn memory_write_arg(location: SummaryMemoryLocation) -> Option<usize> {
    match location.region {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    }
}

fn parser_output_args_from_effects(effects: &[LoopEffectSummary]) -> BTreeMap<usize, usize> {
    const MIN_DISTINCT_OUT_WRITES: usize = 2;

    let mut parser_args = BTreeSet::new();
    let mut writes_by_arg = BTreeMap::<usize, BTreeSet<SummaryMemoryLocation>>::new();
    for effect in effects {
        parser_args.extend(effect.parser_comparisons.keys().copied());
        for write in &effect.memory_writes {
            if let Some(arg) = memory_write_arg(write.location) {
                writes_by_arg.entry(arg).or_default().insert(write.location);
            }
        }
    }

    parser_args
        .into_iter()
        .filter_map(|parser_arg| {
            let dst_arg = writes_by_arg
                .iter()
                .filter(|(arg, writes)| {
                    **arg != parser_arg && writes.len() >= MIN_DISTINCT_OUT_WRITES
                })
                .map(|(arg, _)| *arg)
                .next()?;
            Some((parser_arg, dst_arg))
        })
        .collect()
}

fn parser_return_predicates_from_effects(
    func: &SsaArtifact,
    effects: &[LoopEffectSummary],
) -> BTreeMap<usize, NativeParserReturnPredicate> {
    let mut parser_anchors = BTreeMap::<usize, u64>::new();
    let mut zero_scan_blocks = BTreeMap::<usize, BTreeSet<u64>>::new();
    let mut guards = Vec::<ZeroGuardObservation>::new();

    for effect in effects {
        for (arg, evidence) in &effect.parser_comparisons {
            parser_anchors
                .entry(*arg)
                .and_modify(|anchor| *anchor = (*anchor).min(evidence.anchor))
                .or_insert(evidence.anchor);
        }
        for scan in &effect.scans {
            if scan.terminator == NativeWorkerTerminator::ZeroByte
                && let Some(arg) = source_arg(scan.source)
            {
                zero_scan_blocks.entry(arg).or_default().insert(scan.anchor);
            }
        }
        guards.extend(effect.zero_guards.iter().cloned());
    }

    let mut predicates = BTreeMap::new();
    for (arg, parser_anchor) in parser_anchors {
        let Some(zero_blocks) = zero_scan_blocks.get(&arg) else {
            continue;
        };
        let has_nonzero_then_zero_check = guards.iter().any(|guard| {
            if guard.anchor < parser_anchor {
                return false;
            }
            let successors = func.function().successors(guard.anchor);
            let nonzero_successors = successors.into_iter().filter(|succ| {
                if guard.branch_when_zero {
                    Some(*succ) != guard.target
                } else {
                    Some(*succ) == guard.target
                }
            });
            nonzero_successors
                .filter(|succ| *succ >= parser_anchor)
                .any(|succ| zero_blocks.contains(&succ))
        });
        if has_nonzero_then_zero_check {
            predicates.insert(
                arg,
                NativeParserReturnPredicate {
                    kind: NativeParserReturnPredicateKind::NonzeroCursorAndZeroTerminator,
                    cursor_arg: arg,
                },
            );
        }
    }
    predicates
}

fn loaded_source_offset(source: LoadedSource) -> Option<u64> {
    let range = source.location.range?;
    if range.offset_lo == range.offset_hi && range.offset_lo >= 0 {
        u64::try_from(range.offset_lo).ok()
    } else {
        None
    }
}

fn zero_guard_successors(func: &SsaArtifact, guard: &ZeroGuardObservation) -> BTreeSet<u64> {
    if guard.branch_when_zero {
        return guard.target.into_iter().collect();
    }
    func.function()
        .successors(guard.anchor)
        .into_iter()
        .filter(|successor| Some(*successor) != guard.target)
        .collect()
}

fn island_exit_reaches_block(func: &SsaArtifact, island: &LoopIsland, target: u64) -> bool {
    if island.body.contains(&target) {
        return false;
    }
    let mut visited = BTreeSet::new();
    let mut stack: Vec<_> = island.exits.iter().copied().collect();
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        if current == target {
            return true;
        }
        if island.body.contains(&current) {
            continue;
        }
        stack.extend(func.function().successors(current));
    }
    false
}

fn zero_guard_exits_island(
    func: &SsaArtifact,
    island: &LoopIsland,
    guard: &ZeroGuardObservation,
) -> bool {
    zero_guard_successors(func, guard)
        .into_iter()
        .any(|successor| {
            !island.body.contains(&successor)
                || island.exits.contains(&successor)
                || island_exit_reaches_block(func, island, successor)
        })
}

fn table_walk_return_blocks(
    func: &SsaArtifact,
    island: &LoopIsland,
    observations: &BTreeMap<u64, BlockWorkerObservations>,
) -> Vec<ReturnObservation> {
    observations
        .values()
        .flat_map(|block| block.returns.iter())
        .filter(|ret| island_exit_reaches_block(func, island, ret.anchor))
        .cloned()
        .collect()
}

fn table_walk_details_from_effects(
    func: &SsaArtifact,
    observations: &BTreeMap<u64, BlockWorkerObservations>,
    effects: &[LoopEffectSummary],
) -> BTreeMap<(usize, u64), NativeTableWalkSummary> {
    let mut details = BTreeMap::new();
    for effect in effects.iter().filter(|effect| effect.natural_loop) {
        let mut table_args = BTreeSet::<usize>::new();
        for guard in &effect.zero_guards {
            if let Some(source) = guard.source
                && let Some(arg) = source_arg(source)
            {
                table_args.insert(arg);
            }
        }
        for scan in &effect.scans {
            if let Some(arg) = source_arg(scan.source)
                && loaded_source_access_width(scan.source) >= 2
            {
                table_args.insert(arg);
            }
        }

        let return_blocks = table_walk_return_blocks(func, &effect.island, observations);
        for table_arg in table_args {
            let mut next_offset = None;
            let mut name_offset = None;
            let mut len_offset = None;

            for guard in &effect.zero_guards {
                let Some(source) = guard.source else {
                    continue;
                };
                if source_arg(source) != Some(table_arg) {
                    continue;
                }
                let Some(offset) = loaded_source_offset(source) else {
                    continue;
                };
                let width = loaded_source_access_width(source);
                if width >= 4 {
                    if zero_guard_exits_island(func, &effect.island, guard) {
                        next_offset = Some(next_offset.map_or(offset, |old: u64| old.min(offset)));
                    } else {
                        name_offset = Some(name_offset.map_or(offset, |old: u64| old.min(offset)));
                    }
                } else if width <= 4 && offset > 0 {
                    len_offset = Some(len_offset.map_or(offset, |old: u64| old.min(offset)));
                }
            }

            if len_offset.is_none() {
                len_offset = effect
                    .scans
                    .iter()
                    .filter(|scan| source_arg(scan.source) == Some(table_arg))
                    .filter(|scan| loaded_source_access_width(scan.source) <= 4)
                    .filter_map(|scan| loaded_source_offset(scan.source))
                    .filter(|offset| *offset > 0)
                    .min();
            }

            let needle_arg = effect
                .scans
                .iter()
                .filter(|scan| loaded_source_access_width(scan.source) == 1)
                .filter(|scan| loaded_source_offset(scan.source) == Some(0))
                .filter_map(|scan| source_arg(scan.source))
                .find(|arg| *arg != table_arg);

            let mut id_offset = None;
            let mut count_accumulator = None;
            let mut match_returns_field_plus_count = false;
            let mut exhausted_returns_negative_count = false;
            for ret in &return_blocks {
                if let Some((source, accumulator)) = &ret.field_plus_count
                    && source_arg(*source) == Some(table_arg)
                    && let Some(offset) = loaded_source_offset(*source)
                {
                    id_offset = Some(offset);
                    count_accumulator = Some(accumulator.clone());
                    match_returns_field_plus_count = true;
                }
                exhausted_returns_negative_count |= ret.negative_count_return;
            }

            if count_accumulator.is_none() {
                count_accumulator = effect
                    .numeric_transforms
                    .iter()
                    .find(|transform| {
                        transform.operation == NativeWorkerFoldOperation::Add
                            && transform.length_arg.is_none()
                    })
                    .map(|transform| transform.accumulator.clone());
            }

            if needle_arg.is_some()
                && id_offset.is_some()
                && len_offset.is_some()
                && name_offset.is_some()
                && next_offset.is_some()
                && match_returns_field_plus_count
                && exhausted_returns_negative_count
            {
                details.insert(
                    (table_arg, effect.island.header),
                    NativeTableWalkSummary {
                        table_arg,
                        needle_arg,
                        id_offset,
                        len_offset,
                        name_offset,
                        next_offset,
                        count_accumulator,
                        match_returns_field_plus_count,
                        exhausted_returns_negative_count,
                    },
                );
            }
        }
    }
    details
}

fn attach_table_walk_detail(
    summary: &mut NativeWorkerSummary,
    details: &BTreeMap<(usize, u64), NativeTableWalkSummary>,
) {
    if summary.kind != NativeWorkerSummaryKind::TableWalk {
        return;
    }
    let Some(loop_summary) = summary.loop_summary.as_mut() else {
        return;
    };
    let Some(memory) = summary.memory else {
        return;
    };
    let SummaryMemoryRegion::Arg { index } = memory.region else {
        return;
    };
    if let Some(detail) = details.get(&(index, loop_summary.header)).cloned() {
        loop_summary.table_walk = Some(detail);
    }
}

fn parser_summary_from_evidence(
    arg: usize,
    evidence: &ParserLoopEvidence,
    digit_fold_evidence: bool,
) -> Option<NativeParserSummary> {
    let numeric_range = parser_evidence_proves_digit_range(evidence, digit_fold_evidence);
    let digit_values = evidence
        .byte_values
        .iter()
        .filter(|value| value.is_ascii_digit())
        .count();
    let token_range = evidence.byte_ranges.iter().any(|range| {
        range.lo <= b' '
            || (range.lo <= b'A' && range.hi >= b'Z')
            || (range.lo <= b'a' && range.hi >= b'z')
    });
    let delimiter_values = evidence
        .byte_values
        .iter()
        .filter(|value| !value.is_ascii_digit())
        .count();
    let kind = if numeric_range || digit_values >= 2 {
        NativeParserKind::Numeric
    } else if token_range || delimiter_values >= 2 || evidence.byte_values.len() >= 4 {
        NativeParserKind::Token
    } else {
        return None;
    };
    Some(NativeParserSummary {
        kind,
        cursor_arg: Some(arg),
        base: matches!(kind, NativeParserKind::Numeric).then_some(10),
        digit_min: matches!(kind, NativeParserKind::Numeric).then_some(b'0'),
        digit_max: matches!(kind, NativeParserKind::Numeric).then_some(b'9'),
        accepts_sign: evidence.accepts_sign,
        return_predicate: None,
    })
}

fn parser_evidence_proves_digit_range(
    evidence: &ParserLoopEvidence,
    digit_fold_evidence: bool,
) -> bool {
    if evidence
        .byte_ranges
        .iter()
        .any(|range| range.lo <= b'0' && range.hi >= b'9')
    {
        return true;
    }

    let lower_bound = evidence
        .byte_ranges
        .iter()
        .filter(|range| range.hi == u8::MAX)
        .map(|range| range.lo)
        .max();
    let upper_bound = evidence
        .byte_ranges
        .iter()
        .filter(|range| range.lo == 0)
        .map(|range| range.hi)
        .min();
    if matches!((lower_bound, upper_bound), (Some(lo), Some(hi)) if lo <= b'0' && hi >= b'9' && lo <= hi)
    {
        return true;
    }

    if digit_fold_evidence
        && evidence
            .byte_ranges
            .iter()
            .any(|range| range.lo == b'0' && range.hi >= b'8')
        && (evidence.byte_values.contains(&b'9')
            || evidence
                .byte_ranges
                .iter()
                .any(|range| range.lo == b'0' && range.hi >= b'9'))
    {
        return true;
    }

    digit_fold_evidence
        && evidence
            .byte_ranges
            .iter()
            .any(|range| range.lo == 0 && range.hi.saturating_add(1) == b'0')
        && (evidence.byte_values.contains(&b'9')
            || evidence
                .byte_ranges
                .iter()
                .any(|range| range.lo == 0 && range.hi.saturating_add(1) == b'9'))
}

fn option_string_control_args_by_block(
    func: &SsaArtifact,
    observations: &BTreeMap<u64, BlockWorkerObservations>,
) -> BTreeMap<u64, BTreeSet<usize>> {
    let mut controls = BTreeMap::<u64, BTreeSet<usize>>::new();
    for (block_addr, assumptions) in &func.predicates().block_assumptions {
        for assumption in assumptions {
            let Some(branch_controls) = observations
                .get(&assumption.predecessor)
                .map(|block| &block.option_string_branch_controls)
                .filter(|controls| !controls.is_empty())
            else {
                continue;
            };
            controls
                .entry(*block_addr)
                .or_default()
                .extend(branch_controls.iter().copied());
        }
    }

    for (&branch_addr, block) in observations {
        if block.option_string_branch_controls.is_empty() {
            continue;
        }
        for succ in func.function().successors(branch_addr) {
            controls
                .entry(succ)
                .or_default()
                .extend(block.option_string_branch_controls.iter().copied());
        }
    }
    controls
}

fn option_string_render_summaries(
    func: &SsaArtifact,
    observations: &BTreeMap<u64, BlockWorkerObservations>,
) -> Vec<NativeWorkerSummary> {
    const MIN_INPUT_READS: usize = 4;
    const MIN_OPTION_BYTES: usize = 4;

    let mut input_reads = BTreeMap::<usize, (usize, u64)>::new();
    let mut output_bytes = BTreeMap::<(usize, usize), BTreeSet<u8>>::new();
    let mut output_zeroes = BTreeSet::<(usize, usize)>::new();
    let mut output_anchors = BTreeMap::<(usize, usize), u64>::new();
    let block_controls = option_string_control_args_by_block(func, observations);

    for (block_addr, block) in observations {
        for read in &block.option_string_reads {
            let entry = input_reads.entry(read.arg).or_insert((0, read.anchor));
            entry.0 += 1;
            entry.1 = entry.1.min(read.anchor);
        }
        for write in &block.option_string_writes {
            let mut control_args = write.control_args.clone();
            if let Some(block_control_args) = block_controls.get(block_addr) {
                control_args.extend(block_control_args.iter().copied());
            }
            for input_arg in control_args.into_iter().filter(|arg| *arg != write.arg) {
                let key = (input_arg, write.arg);
                output_anchors
                    .entry(key)
                    .and_modify(|anchor| *anchor = (*anchor).min(write.anchor))
                    .or_insert(write.anchor);
                if write.value == 0 {
                    output_zeroes.insert(key);
                } else if write.value.is_ascii_alphanumeric() {
                    output_bytes.entry(key).or_default().insert(write.value);
                }
            }
        }
    }

    output_bytes
        .into_iter()
        .filter(|(key, bytes)| output_zeroes.contains(key) && bytes.len() >= MIN_OPTION_BYTES)
        .filter_map(|((input_arg, output_arg), _)| {
            let (_, read_anchor) = input_reads
                .get(&input_arg)
                .filter(|(count, _)| *count >= MIN_INPUT_READS)?;
            let anchor = output_anchors
                .get(&(input_arg, output_arg))
                .copied()
                .unwrap_or(func.entry)
                .min(*read_anchor);
            Some(format_render_worker_summary(
                anchor,
                input_arg,
                Some(output_arg),
            ))
        })
        .collect()
}

fn summaries_from_loop_effects(func: &SsaArtifact) -> Vec<NativeWorkerSummary> {
    let observations = collect_block_worker_observations(func);
    let mut summaries = Vec::<NativeWorkerSummary>::new();
    summaries.extend(option_string_render_summaries(func, &observations));
    let effects = loop_effect_summaries(func, observations.clone());
    let parser_output_args = parser_output_args_from_effects(&effects);
    let parser_return_predicates = parser_return_predicates_from_effects(func, &effects);
    let table_walk_details = table_walk_details_from_effects(func, &observations, &effects);
    for effect in effects {
        let mut seen_scans = BTreeSet::new();
        for scan in effect.scans {
            if seen_scans.insert((scan.source.location, scan.terminator)) {
                if effect.natural_loop {
                    let mut summary =
                        scan_summary_for_island(&effect.island, scan.source, scan.terminator);
                    attach_table_walk_detail(&mut summary, &table_walk_details);
                    summaries.push(summary);
                } else {
                    summaries.push(scan_summary(
                        func,
                        scan.anchor,
                        scan.source,
                        scan.terminator,
                    ));
                }
            }
        }

        let digit_fold_args = effect
            .folds
            .iter()
            .filter(|fold| fold.source.value_delta == -i64::from(b'0'))
            .filter_map(|fold| source_arg(fold.source))
            .collect::<BTreeSet<_>>();
        let mut parser_value_folds = BTreeMap::<usize, NativeWorkerFold>::new();
        for fold in effect.folds.iter().filter(|fold| {
            fold.source.value_delta == -i64::from(b'0')
                && fold.operation == NativeWorkerFoldOperation::Add
        }) {
            let Some(arg) = source_arg(fold.source) else {
                continue;
            };
            parser_value_folds
                .entry(arg)
                .or_insert_with(|| NativeWorkerFold {
                    accumulator: fold.accumulator.clone(),
                    bits: fold.source.size.saturating_mul(8),
                    operation: fold.operation,
                    predicate: None,
                    init: Some(0),
                    multiplier: Some(10),
                    byte_transform: None,
                });
        }

        let mut seen_folds = BTreeSet::new();
        for fold in effect
            .folds
            .into_iter()
            .filter(fold_observation_has_hash_stream_source)
        {
            if seen_folds.insert((
                fold.source.location,
                fold.accumulator.clone(),
                fold.operation,
            )) {
                if effect.natural_loop {
                    let mut summary = hash_fold_summary_for_island(
                        &effect.island,
                        fold.source,
                        fold.accumulator,
                        fold.operation,
                    );
                    enrich_hash_fold_summary_for_island(
                        func,
                        &effect.island,
                        fold.source,
                        &mut summary,
                    );
                    summaries.push(summary);
                } else {
                    summaries.push(hash_fold_summary(
                        func,
                        fold.anchor,
                        fold.source,
                        fold.accumulator,
                        fold.operation,
                    ));
                }
            }
        }

        let mut seen_global_loads = BTreeSet::new();
        for load in effect.global_loads {
            if seen_global_loads.insert(load.source.location) {
                match (effect.natural_loop, load.source.location.region) {
                    (true, SummaryMemoryRegion::Global { .. }) => {
                        let mut summary =
                            table_walk_summary_for_island(&effect.island, load.source);
                        attach_table_walk_detail(&mut summary, &table_walk_details);
                        summaries.push(summary);
                    }
                    _ => {
                        summaries.push(metadata_probe_worker_summary_for_memory(
                            load.anchor,
                            Some(load.source.location),
                        ));
                    }
                }
            }
        }

        let mut seen_memory_writes = BTreeSet::new();
        for write in effect.memory_writes {
            if seen_memory_writes.insert((write.location, write.width)) {
                summaries.push(memory_worker_summary(
                    write.anchor,
                    SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Write,
                        location: write.location,
                    },
                ));
            }
        }

        let mut predicated_numeric_transform_keys = BTreeSet::new();
        if effect.natural_loop {
            let mut predicates_by_source = BTreeMap::<
                SummaryMemoryLocation,
                (LoadedSource, BTreeSet<NativeWorkerPredicate>),
            >::new();
            for observation in &effect.byte_predicates {
                let entry = predicates_by_source
                    .entry(observation.source.location)
                    .or_insert_with(|| (observation.source, BTreeSet::new()));
                entry.1.insert(observation.predicate.clone());
            }
            for (_location, (source, predicates)) in predicates_by_source {
                let Some(memory_arg) = source_arg(source) else {
                    continue;
                };
                let Some(length_arg) = infer_length_arg_for_memory_arg(func, memory_arg) else {
                    continue;
                };
                let Some(predicate) = combined_worker_predicate(predicates) else {
                    continue;
                };
                for transform in effect
                    .numeric_transforms
                    .iter()
                    .filter(|transform| transform.operation == NativeWorkerFoldOperation::Add)
                {
                    predicated_numeric_transform_keys.insert((
                        transform.dst_arg,
                        transform.accumulator.clone(),
                        transform.bits,
                        transform.operation,
                    ));
                    summaries.push(predicated_numeric_transform_summary_for_island(
                        &effect.island,
                        transform,
                        source,
                        length_arg,
                        predicate.clone(),
                    ));
                }
            }
        }

        let mut seen_numeric_transforms = BTreeSet::new();
        for transform in effect.numeric_transforms {
            if predicated_numeric_transform_keys.contains(&(
                transform.dst_arg,
                transform.accumulator.clone(),
                transform.bits,
                transform.operation,
            )) {
                continue;
            }
            if seen_numeric_transforms.insert((
                transform.dst_arg,
                transform.length_arg,
                transform.accumulator.clone(),
                transform.bits,
                transform.operation,
            )) {
                if effect.natural_loop {
                    summaries.push(numeric_transform_summary_for_island(
                        &effect.island,
                        transform,
                    ));
                } else if has_loopish_or_dispatch_control(func) {
                    summaries.push(numeric_transform_summary(func, transform));
                }
            }
        }

        if effect.natural_loop {
            for (arg, evidence) in &effect.parser_comparisons {
                if let Some(mut parser) =
                    parser_summary_from_evidence(*arg, evidence, digit_fold_args.contains(arg))
                {
                    parser.return_predicate = parser_return_predicates.get(arg).copied();
                    let value_fold = matches!(parser.kind, NativeParserKind::Numeric)
                        .then(|| parser_value_folds.get(arg).cloned())
                        .flatten();
                    summaries.push(parser_summary_for_island(
                        &effect.island,
                        *arg,
                        parser_output_args.get(arg).copied(),
                        parser,
                        value_fold,
                    ));
                }
            }
        } else if has_loopish_or_dispatch_control(func) {
            for (arg, evidence) in &effect.parser_comparisons {
                if let Some(mut parser) =
                    parser_summary_from_evidence(*arg, evidence, digit_fold_args.contains(arg))
                {
                    parser.return_predicate = parser_return_predicates.get(arg).copied();
                    let value_fold = matches!(parser.kind, NativeParserKind::Numeric)
                        .then(|| parser_value_folds.get(arg).cloned())
                        .flatten();
                    summaries.push(parser_summary(
                        func,
                        evidence.anchor,
                        *arg,
                        parser_output_args.get(arg).copied(),
                        parser,
                        value_fold,
                    ));
                }
            }
        }
    }
    summaries
}

fn has_loopish_or_dispatch_control(func: &SsaArtifact) -> bool {
    let risk = func.function().cfg_risk_summary();
    risk.loop_count > 0
        || risk.back_edge_count > 0
        || risk.switch_block_count > 0
        || risk.block_count >= 16
}

pub(super) fn classify_function_worker_summaries_unbounded(
    func: &SsaArtifact,
) -> Vec<NativeWorkerSummary> {
    summaries_from_loop_effects(func)
}

pub(super) fn classify_function_worker_enrichment_summaries_unbounded(
    _func: &SsaArtifact,
) -> Vec<NativeWorkerSummary> {
    Vec::new()
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    use super::*;
    use crate::semantics::SemanticConfidence;

    fn aarch64_test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("x1", 0x08, 8));
        arch.add_register(RegisterDef::new("x2", 0x10, 8));
        arch.add_register(RegisterDef::new("x3", 0x18, 8));
        arch
    }

    fn x86_64_alias_test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("EAX", 0x00, 4));
        arch.add_register(RegisterDef::new("AX", 0x00, 2));
        arch.add_register(RegisterDef::new("AL", 0x00, 1));
        arch.add_register(RegisterDef::new("RDI", 0x20, 8));
        arch.add_register(RegisterDef::new("RSI", 0x28, 8));
        arch.add_register(RegisterDef::new("RDX", 0x30, 8));
        arch.add_register(RegisterDef::new("EDX", 0x30, 4));
        arch.add_register(RegisterDef::new("DX", 0x30, 2));
        arch.add_register(RegisterDef::new("DL", 0x30, 1));
        arch.add_register(RegisterDef::new("RCX", 0x38, 8));
        arch.add_register(RegisterDef::new("ECX", 0x38, 4));
        arch.add_register(RegisterDef::new("CX", 0x38, 2));
        arch.add_register(RegisterDef::new("CL", 0x38, 1));
        arch.add_register(RegisterDef::new("R8", 0x40, 8));
        arch
    }

    #[test]
    fn function_semantic_summary_seed_models_known_imports_in_r2sym() {
        let malloc =
            function_semantic_summary_seed_for_name(InterprocFunctionId(1), "sym.imp.malloc")
                .expect("malloc seed");
        assert_eq!(malloc.return_relation, SummaryReturnRelation::HeapAlloc);
        assert_eq!(
            malloc.allocation_effects,
            vec![SummaryAllocationEffect {
                size_arg: Some(0),
                zeroed: false,
            }]
        );

        assert!(
            function_semantic_summary_seed_for_name(InterprocFunctionId(2), "memcpy").is_none(),
            "raw names without import/PLT evidence must not seed semantics"
        );

        let memcpy =
            function_semantic_summary_seed_for_name(InterprocFunctionId(2), "sym.imp.memcpy")
                .expect("memcpy seed");
        assert_eq!(memcpy.return_relation, SummaryReturnRelation::Arg(0));
        assert!(memcpy.arg_effects.get(&0).expect("dst").write);
        assert!(memcpy.arg_effects.get(&1).expect("src").read);
        assert_eq!(
            memcpy.transfer_effects,
            vec![SummaryTransferEffect {
                dst: arg_location(0),
                src: arg_location(1),
                len: SummaryTransferLength::Arg(2),
            }]
        );
    }

    #[test]
    fn classifier_detects_zero_terminated_string_scan() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x10, 1);
        let pred = Varnode::unique(0x11, 1);
        let mut block = R2ILBlock::new(0x4000, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred,
            a: loaded,
            b: Varnode::constant(0, 1),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("string scan SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .loop_summary
                    .as_ref()
                    .and_then(|loop_summary| loop_summary.terminator)
                    == Some(NativeWorkerTerminator::ZeroByte)
        }));
    }

    #[test]
    fn classifier_detects_byte_hash_fold() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x20, 1);
        let acc = Varnode::unique(0x21, 8);
        let mut block = R2ILBlock::new(0x4010, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: acc.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x22, 8),
            a: Varnode::register(0x08, 8),
            b: acc,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("hash fold SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let hash_fold = summaries
            .iter()
            .find(|summary| {
                matches!(summary.kind, NativeWorkerSummaryKind::HashFold)
                    && matches!(
                        summary.memory.map(|memory| memory.region),
                        Some(SummaryMemoryRegion::Arg { index: 0 })
                    )
                    && summary
                        .loop_summary
                        .as_ref()
                        .and_then(|loop_summary| loop_summary.fold.as_ref())
                        .is_some_and(|fold| {
                            fold.operation == NativeWorkerFoldOperation::Add && fold.bits == 8
                        })
            })
            .expect("evidence-first hash fold summary");
        assert_eq!(hash_fold.evidence.tier, SemanticConfidence::Likely);
        assert_eq!(
            hash_fold.evidence.coverage,
            SemanticEvidenceCoverage::Bounded
        );
        assert_eq!(
            hash_fold.evidence.provenance,
            SemanticEvidenceProvenance::Stable
        );
        assert_eq!(
            hash_fold.evidence.reasons,
            vec![SemanticEvidenceReason::SummaryBudget]
        );
    }

    #[test]
    fn classifier_keeps_byte_hash_fold_after_widened_transform() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x80, 1);
        let widened = Varnode::unique(0x81, 8);
        let transformed = Varnode::unique(0x82, 8);
        let mixed = Varnode::unique(0x83, 8);
        let mut block = R2ILBlock::new(0x4080, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: widened.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntAdd {
            dst: transformed.clone(),
            a: widened,
            b: Varnode::constant(32, 8),
        });
        block.push(R2ILOp::IntXor {
            dst: mixed,
            a: Varnode::register(0x08, 8),
            b: transformed,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("hash fold SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let hash_fold = summaries
            .iter()
            .find(|summary| {
                matches!(summary.kind, NativeWorkerSummaryKind::HashFold)
                    && matches!(
                        summary.memory.map(|memory| memory.region),
                        Some(SummaryMemoryRegion::Arg { index: 0 })
                    )
            })
            .expect("widened transformed byte still proves a hash-fold stream");
        let fold = hash_fold
            .loop_summary
            .as_ref()
            .and_then(|loop_summary| loop_summary.fold.as_ref())
            .expect("hash fold summary carries a fold proof");
        assert_eq!(fold.operation, NativeWorkerFoldOperation::Xor);
        assert_eq!(fold.bits, 8);
    }

    #[test]
    fn dataflow_load_source_tracks_size_adapted_ssa_identity() {
        let mut state = WorkerDataflowState::default();
        let wide = SSAVar::new("tmp:byte_carrier", 4, 8);
        let narrow = SSAVar::new("tmp:byte_carrier", 4, 1);
        let source = LoadedSource {
            location: arg_location(0),
            size: 8,
            block_addr: 0x4090,
            value_delta: 32,
        };
        insert_exact_load_source_value(&mut state, &wide, source);

        let resolved = dataflow_loaded_source(&narrow, &state)
            .expect("narrow same-identity view keeps load provenance");
        assert_eq!(resolved.location, source.location);
        assert_eq!(resolved.size, 1);
        assert_eq!(resolved.value_delta, 32);

        dataflow_kill_load_source_aliases(&wide, &mut state);
        assert!(
            dataflow_loaded_source(&narrow, &state).is_none(),
            "killing one size view must remove stale same-identity provenance"
        );
    }

    #[test]
    fn classifier_does_not_treat_byte_transform_constant_as_hash_fold() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x30, 1);
        let widened = Varnode::unique(0x31, 8);
        let mut block = R2ILBlock::new(0x4020, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: widened.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x32, 8),
            a: widened,
            b: Varnode::constant(0x20, 8),
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("byte transform SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(
            summaries
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::HashFold)),
            "loaded byte plus literal is a byte transform, not a hash fold: {summaries:?}"
        );
    }

    #[test]
    fn classifier_does_not_treat_pointer_width_add_as_hash_fold() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x34, 8);
        let mut block = R2ILBlock::new(0x4024, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x35, 8),
            a: Varnode::register(0x08, 8),
            b: loaded,
        });
        block.push(R2ILOp::Branch {
            target: Varnode::constant(0x4024, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("pointer add SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(
            summaries
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::HashFold)),
            "pointer-width field/list arithmetic is not byte-stream hash evidence: {summaries:?}"
        );
    }

    #[test]
    fn worker_constant_resolver_follows_single_assignment_defs() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4020, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x120, 8),
            src: Varnode::constant(0x14650fb0739d0383, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("constant copy SSA");
        let block = artifact
            .function()
            .blocks()
            .next()
            .expect("single SSA block");
        let SSAOp::Copy { dst, .. } = &block.ops[0] else {
            panic!("expected SSA copy");
        };

        assert_eq!(
            resolved_const_value(&artifact, dst),
            Some(0x14650fb0739d0383)
        );
    }

    #[test]
    fn classifier_detects_option_string_render_without_name() {
        let arch = aarch64_test_arch();
        let guard = Varnode::unique(0x2f, 1);
        let mut block = R2ILBlock::new(0x4030, 4);
        for idx in 0..4 {
            let loaded = Varnode::unique(0x30 + idx, 1);
            block.push(R2ILOp::Load {
                dst: loaded.clone(),
                space: SpaceId::Ram,
                addr: Varnode::register(0x00, 8),
            });
            if idx == 0 {
                block.push(R2ILOp::IntNotEqual {
                    dst: guard.clone(),
                    a: loaded,
                    b: Varnode::constant(0, 1),
                });
            }
        }
        for byte in [b'b', b'd', b'f', b'g', 0] {
            block.push(R2ILOp::StoreGuarded {
                space: SpaceId::Ram,
                addr: Varnode::register(0x08, 8),
                val: Varnode::constant(u64::from(byte), 1),
                guard: guard.clone(),
                ordering: r2il::MemoryOrdering::Unknown,
            });
        }
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("option render SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let render = summaries
            .iter()
            .find(|summary| {
                matches!(summary.kind, NativeWorkerSummaryKind::FormatRender)
                    && matches!(
                        summary.memory.map(|memory| memory.region),
                        Some(SummaryMemoryRegion::Arg { index: 0 })
                    )
                    && matches!(
                        summary.dst.map(|dst| dst.region),
                        Some(SummaryMemoryRegion::Arg { index: 1 })
                    )
            })
            .expect("structural option string render summary");
        assert_eq!(render.evidence.tier, SemanticConfidence::Likely);
        assert_eq!(
            render.evidence.reasons,
            vec![SemanticEvidenceReason::SummaryBudget]
        );
        assert!(
            !render
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
        );
    }

    #[test]
    fn classifier_rejects_uncorrelated_option_reads_and_writes() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4038, 4);
        for idx in 0..4 {
            let loaded = Varnode::unique(0x38 + idx, 1);
            block.push(R2ILOp::Load {
                dst: loaded,
                space: SpaceId::Ram,
                addr: Varnode::register(0x00, 8),
            });
        }
        for byte in [b'b', b'd', b'f', b'g', 0] {
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::register(0x08, 8),
                val: Varnode::constant(u64::from(byte), 1),
            });
        }
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("uncorrelated option SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(
            summaries
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::FormatRender)),
            "uncorrelated reads/writes must not produce option-string summary: {summaries:?}"
        );
    }

    #[test]
    fn key_to_opts_name_alone_does_not_create_summary() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x4030),
            Some("dbg.key_to_opts".to_string()),
        );

        assert!(!has_native_worker_summary_family("dbg.key_to_opts"));
        assert!(
            summaries_from_interproc_summary_unbounded(0x4030, &summary)
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::FormatRender))
        );
    }

    #[test]
    fn classifier_detects_numeric_parser_loop_from_digit_range() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x40, 1);
        let wide = Varnode::unique(0x41, 8);
        let digit = Varnode::unique(0x42, 8);
        let pred = Varnode::unique(0x43, 1);
        let mut block = R2ILBlock::new(0x4040, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: wide.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntSub {
            dst: digit.clone(),
            a: wide,
            b: Varnode::constant(u64::from(b'0'), 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: digit,
            b: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4040, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("numeric parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("numeric parser summary");
        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.cursor_arg, Some(0));
        assert_eq!(parser.base, Some(10));
        assert_eq!(parser.digit_min, Some(b'0'));
        assert_eq!(parser.digit_max, Some(b'9'));
    }

    #[test]
    fn classifier_detects_numeric_parser_through_x86_full_to_low_alias() {
        let arch = x86_64_alias_test_arch();
        let wide = Varnode::unique(0x50, 8);
        let digit = Varnode::unique(0x51, 8);
        let pred = Varnode::unique(0x52, 1);
        let mut block = R2ILBlock::new(0x4050, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0x20, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: wide.clone(),
            src: Varnode::register(0x00, 1),
        });
        block.push(R2ILOp::IntSub {
            dst: digit.clone(),
            a: wide,
            b: Varnode::constant(u64::from(b'0'), 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: digit,
            b: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4050, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("x86 numeric parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("numeric parser summary through EAX/AL alias");
        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.cursor_arg, Some(0));
        assert_eq!(parser.base, Some(10));
    }

    #[test]
    fn classifier_detects_numeric_parser_from_signed_add_delta() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x58, 1);
        let wide = Varnode::unique(0x59, 8);
        let digit = Varnode::unique(0x5a, 8);
        let pred = Varnode::unique(0x5b, 1);
        let mut block = R2ILBlock::new(0x4058, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntSExt {
            dst: wide.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntAdd {
            dst: digit.clone(),
            a: wide,
            b: Varnode::constant(0xffffffffffffffd0, 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: digit,
            b: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4058, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("signed-add parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("numeric parser summary from signed add");
        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.base, Some(10));
    }

    #[test]
    fn parser_digit_range_accepts_x86_split_flag_bounds_with_digit_fold() {
        let evidence = ParserLoopEvidence {
            anchor: 0x4058,
            byte_values: BTreeSet::from([b'9']),
            byte_ranges: BTreeSet::from([
                ParserByteRange { lo: 0, hi: b'/' },
                ParserByteRange {
                    lo: 0,
                    hi: b'9' - 1,
                },
            ]),
            accepts_sign: false,
        };

        let parser =
            parser_summary_from_evidence(0, &evidence, true).expect("digit parser evidence");

        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.base, Some(10));
        assert_eq!(parser.digit_min, Some(b'0'));
        assert_eq!(parser.digit_max, Some(b'9'));
    }

    #[test]
    fn parser_digit_range_accepts_normalized_less_than_nine_with_digit_fold() {
        let evidence = ParserLoopEvidence {
            anchor: 0x405a,
            byte_values: BTreeSet::from([b'9']),
            byte_ranges: BTreeSet::from([ParserByteRange { lo: b'0', hi: b'8' }]),
            accepts_sign: false,
        };

        let parser =
            parser_summary_from_evidence(0, &evidence, true).expect("split digit parser evidence");

        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.base, Some(10));
        assert_eq!(parser.digit_min, Some(b'0'));
        assert_eq!(parser.digit_max, Some(b'9'));
    }

    #[test]
    fn parser_output_arg_requires_distinct_out_writes() {
        let mut parser_comparisons = BTreeMap::new();
        parser_comparisons.insert(
            0,
            ParserLoopEvidence {
                anchor: 0x4060,
                ..ParserLoopEvidence::default()
            },
        );
        let effects = vec![LoopEffectSummary {
            parser_comparisons,
            memory_writes: vec![
                MemoryWriteObservation {
                    anchor: 0x4070,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index: 1 },
                        range: Some(SummaryMemoryRange {
                            offset_lo: 0,
                            offset_hi: 0,
                            width: Some(4),
                        }),
                    },
                    width: 4,
                },
                MemoryWriteObservation {
                    anchor: 0x4070,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index: 1 },
                        range: Some(SummaryMemoryRange {
                            offset_lo: 8,
                            offset_hi: 8,
                            width: Some(8),
                        }),
                    },
                    width: 8,
                },
            ],
            ..LoopEffectSummary::default()
        }];

        assert_eq!(parser_output_args_from_effects(&effects).get(&0), Some(&1));
    }

    #[test]
    fn parser_return_predicate_requires_nonzero_guard_to_zero_scan() {
        let arch = aarch64_test_arch();
        let mut guard_block = R2ILBlock::new(0x5000, 4);
        guard_block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x6000, 8),
            cond: Varnode::unique(0x5010, 1),
        });
        let zero_block = R2ILBlock::new(0x5004, 4);
        let exit_block = R2ILBlock::new(0x6000, 4);
        let artifact =
            SsaArtifact::for_symbolic(&[guard_block, zero_block, exit_block], Some(&arch))
                .expect("guarded return predicate CFG");

        let mut parser_comparisons = BTreeMap::new();
        parser_comparisons.insert(
            0,
            ParserLoopEvidence {
                anchor: 0x4000,
                ..ParserLoopEvidence::default()
            },
        );
        let effects = vec![
            LoopEffectSummary {
                parser_comparisons,
                ..LoopEffectSummary::default()
            },
            LoopEffectSummary {
                scans: vec![ScanObservation {
                    anchor: 0x5004,
                    source: LoadedSource {
                        location: arg_byte_location(0),
                        size: 1,
                        block_addr: 0x5004,
                        value_delta: 0,
                    },
                    terminator: NativeWorkerTerminator::ZeroByte,
                }],
                zero_guards: vec![ZeroGuardObservation {
                    anchor: 0x5000,
                    target: Some(0x6000),
                    value: SSAVar::new("cursor", 1, 8),
                    branch_when_zero: true,
                    source: None,
                }],
                ..LoopEffectSummary::default()
            },
        ];

        let predicates = parser_return_predicates_from_effects(&artifact, &effects);

        assert_eq!(
            predicates.get(&0).map(|predicate| predicate.kind),
            Some(NativeParserReturnPredicateKind::NonzeroCursorAndZeroTerminator)
        );
    }

    fn arg_source(index: usize, offset: i64, width: u32, block_addr: u64) -> LoadedSource {
        LoadedSource {
            location: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index },
                range: Some(SummaryMemoryRange {
                    offset_lo: offset,
                    offset_hi: offset,
                    width: Some(width),
                }),
            },
            size: width,
            block_addr,
            value_delta: 0,
        }
    }

    #[test]
    fn table_walk_details_require_fields_and_exit_returns() {
        let arch = aarch64_test_arch();
        let mut next_guard_block = R2ILBlock::new(0x5100, 4);
        next_guard_block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x6000, 8),
            cond: Varnode::unique(0x5100, 1),
        });
        let mut name_guard_block = R2ILBlock::new(0x5104, 4);
        name_guard_block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x5108, 8),
            cond: Varnode::unique(0x5104, 1),
        });
        let mut latch_block = R2ILBlock::new(0x5108, 4);
        latch_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x5100, 8),
        });
        let match_return_block = R2ILBlock::new(0x6000, 4);
        let exhausted_return_block = R2ILBlock::new(0x6010, 4);
        let artifact = SsaArtifact::for_symbolic(
            &[
                next_guard_block,
                name_guard_block,
                latch_block,
                match_return_block,
                exhausted_return_block,
            ],
            Some(&arch),
        )
        .expect("table walk proof CFG");
        let island = LoopIsland {
            header: 0x5100,
            body: BTreeSet::from([0x5100, 0x5104, 0x5108]),
            entries: BTreeSet::from([0x5100]),
            exits: BTreeSet::from([0x6000, 0x6010]),
        };
        let effects = vec![LoopEffectSummary {
            island,
            natural_loop: true,
            scans: vec![
                ScanObservation {
                    anchor: 0x5104,
                    source: arg_source(0, 6, 2, 0x5104),
                    terminator: NativeWorkerTerminator::ZeroByte,
                },
                ScanObservation {
                    anchor: 0x5108,
                    source: arg_source(1, 0, 1, 0x5108),
                    terminator: NativeWorkerTerminator::ZeroByte,
                },
            ],
            numeric_transforms: vec![NumericTransformObservation {
                anchor: 0x5100,
                dst_arg: None,
                length_arg: None,
                accumulator: "seen".to_string(),
                bits: 32,
                operation: NativeWorkerFoldOperation::Add,
            }],
            zero_guards: vec![
                ZeroGuardObservation {
                    anchor: 0x5100,
                    target: Some(0x6000),
                    value: SSAVar::new("next", 1, 8),
                    branch_when_zero: true,
                    source: Some(arg_source(0, 32, 8, 0x5100)),
                },
                ZeroGuardObservation {
                    anchor: 0x5104,
                    target: Some(0x5108),
                    value: SSAVar::new("name", 1, 8),
                    branch_when_zero: true,
                    source: Some(arg_source(0, 24, 8, 0x5104)),
                },
                ZeroGuardObservation {
                    anchor: 0x5104,
                    target: Some(0x5108),
                    value: SSAVar::new("len", 1, 2),
                    branch_when_zero: true,
                    source: Some(arg_source(0, 6, 2, 0x5104)),
                },
            ],
            ..LoopEffectSummary::default()
        }];
        let observations = BTreeMap::from([
            (
                0x6000,
                BlockWorkerObservations {
                    returns: vec![ReturnObservation {
                        anchor: 0x6000,
                        field_plus_count: Some((arg_source(0, 0, 4, 0x6000), "seen".to_string())),
                        negative_count_return: false,
                    }],
                    ..BlockWorkerObservations::default()
                },
            ),
            (
                0x6010,
                BlockWorkerObservations {
                    returns: vec![ReturnObservation {
                        anchor: 0x6010,
                        field_plus_count: None,
                        negative_count_return: true,
                    }],
                    ..BlockWorkerObservations::default()
                },
            ),
        ]);

        let details = table_walk_details_from_effects(&artifact, &observations, &effects);
        let detail = details.get(&(0, 0x5100)).expect("table walk detail");

        assert_eq!(detail.needle_arg, Some(1));
        assert_eq!(detail.id_offset, Some(0));
        assert_eq!(detail.len_offset, Some(6));
        assert_eq!(detail.name_offset, Some(24));
        assert_eq!(detail.next_offset, Some(32));
        assert!(detail.match_returns_field_plus_count);
        assert!(detail.exhausted_returns_negative_count);
    }

    #[test]
    fn parser_digit_range_rejects_split_flag_bounds_without_digit_fold() {
        let evidence = ParserLoopEvidence {
            anchor: 0x405c,
            byte_values: BTreeSet::from([b'9']),
            byte_ranges: BTreeSet::from([
                ParserByteRange { lo: 0, hi: b'/' },
                ParserByteRange {
                    lo: 0,
                    hi: b'9' - 1,
                },
            ]),
            accepts_sign: false,
        };

        let parser =
            parser_summary_from_evidence(0, &evidence, false).expect("token parser evidence");

        assert_eq!(parser.kind, NativeParserKind::Token);
    }

    #[test]
    fn classifier_detects_token_parser_loop_from_whitespace_range() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x60, 1);
        let pred = Varnode::unique(0x61, 1);
        let mut block = R2ILBlock::new(0x4060, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(0x20, 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4060, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("token parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("token parser summary");
        assert_eq!(parser.kind, NativeParserKind::Token);
        assert_eq!(parser.cursor_arg, Some(0));
    }

    #[test]
    fn classifier_detects_path_walk_from_path_delimiter_scan() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x70, 1);
        let pred = Varnode::unique(0x71, 1);
        let mut block = R2ILBlock::new(0x4070, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(u64::from(b'/'), 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4070, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("path scan SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::PathWalk)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
    }

    #[test]
    fn classifier_detects_table_walk_from_global_loop_load() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4080, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x80, 4),
            space: SpaceId::Ram,
            addr: Varnode::ram(0x9000, 8),
        });
        block.push(R2ILOp::Branch {
            target: Varnode::constant(0x4080, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("table walk SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Global { address: 0x9000 })
                )
                && summary.loop_summary.is_some()
        }));
    }

    #[test]
    fn classifier_detects_table_walk_from_arg_pointer_null_check() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x84, 8);
        let pred = Varnode::unique(0x85, 1);
        let mut block = R2ILBlock::new(0x4084, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4084, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("table pointer SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.terminator == Some(NativeWorkerTerminator::ZeroByte)
                })
        }));
        assert!(!summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
    }

    #[test]
    fn classifier_detects_metadata_probe_from_single_global_load() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4090, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x90, 4),
            space: SpaceId::Ram,
            addr: Varnode::ram(0xa000, 8),
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("metadata probe SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MetadataProbe)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Global { address: 0xa000 })
                )
        }));
    }

    #[test]
    fn classifier_detects_numeric_transform_loop_without_name() {
        let arch = aarch64_test_arch();
        let product = Varnode::unique(0xa0, 8);
        let pred = Varnode::unique(0xa1, 1);
        let mut block = R2ILBlock::new(0x40a0, 4);
        block.push(R2ILOp::IntMult {
            dst: product.clone(),
            a: Varnode::register(0x00, 8),
            b: Varnode::constant(3, 8),
        });
        block.push(R2ILOp::IntNotEqual {
            dst: pred.clone(),
            a: product,
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x40a0, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("numeric transform SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::NumericTransform)
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.header == 0x40a0
                        && loop_summary
                            .fold
                            .as_ref()
                            .is_some_and(|fold| fold.bits == 64)
                })
        }));
    }

    #[test]
    fn classifier_detects_predicated_byte_count_from_sub_zero_compares() {
        let arch = aarch64_test_arch();
        let end = Varnode::unique(0xb0, 8);
        let loaded = Varnode::unique(0xb1, 1);
        let diff_a = Varnode::unique(0xb2, 8);
        let diff_b = Varnode::unique(0xb3, 8);
        let pred_a = Varnode::unique(0xb4, 1);
        let pred_b = Varnode::unique(0xb5, 1);
        let count = Varnode::unique(0xb6, 8);
        let mut block = R2ILBlock::new(0x40b0, 4);
        block.push(R2ILOp::IntAdd {
            dst: end,
            a: Varnode::register(0x00, 8),
            b: Varnode::register(0x08, 8),
        });
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: diff_a.clone(),
            a: Varnode::register(0x10, 8),
            b: loaded.clone(),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred_a.clone(),
            a: diff_a,
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: diff_b.clone(),
            a: loaded,
            b: Varnode::register(0x18, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred_b,
            a: diff_b,
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: count,
            a: Varnode::unique(0xb7, 8),
            b: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x40b0, 8),
            cond: pred_a,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("byte count SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::NumericTransform)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(1)))
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.length_arg == Some(1)
                        && loop_summary.fold.as_ref().is_some_and(|fold| {
                            fold.operation == NativeWorkerFoldOperation::Add
                                && matches!(
                                    fold.predicate,
                                    Some(NativeWorkerPredicate::AnyOf(ref predicates))
                                        if predicates == &vec![
                                            NativeWorkerPredicate::ByteEqArg { arg: 2 },
                                            NativeWorkerPredicate::ByteEqArg { arg: 3 },
                                        ]
                                )
                        })
                })
        }));
    }

    #[test]
    fn classifier_detects_x86_aliased_predicated_byte_count() {
        let arch = x86_64_alias_test_arch();
        let end = Varnode::unique(0xc0, 8);
        let loaded = Varnode::unique(0xc1, 1);
        let diff = Varnode::unique(0xc2, 8);
        let arg_byte = Varnode::unique(0xc3, 1);
        let pred = Varnode::unique(0xc4, 1);
        let count = Varnode::unique(0xc5, 8);
        let mut block = R2ILBlock::new(0x40c0, 4);
        block.push(R2ILOp::IntAdd {
            dst: end,
            a: Varnode::register(0x20, 8),
            b: Varnode::register(0x28, 8),
        });
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x20, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: Varnode::register(0x00, 4),
            src: loaded,
        });
        block.push(R2ILOp::Copy {
            dst: arg_byte.clone(),
            src: Varnode::register(0x30, 1),
        });
        block.push(R2ILOp::IntSub {
            dst: diff.clone(),
            a: arg_byte,
            b: Varnode::register(0x00, 1),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred.clone(),
            a: diff,
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: count,
            a: Varnode::register(0x40, 8),
            b: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x40c0, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_decompile(&[block], Some(&arch)).expect("x86 byte count SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::NumericTransform)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(1)))
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.fold.as_ref().is_some_and(|fold| {
                        fold.operation == NativeWorkerFoldOperation::Add
                            && matches!(
                                fold.predicate,
                                Some(NativeWorkerPredicate::ByteEqArg { arg: 2 })
                            )
                    })
                })
        }));
    }

    #[test]
    fn interproc_structural_summary_uses_effects_without_name() {
        let mut summary =
            FunctionSemanticSummary::unknown(r2ssa::InterprocFunctionId(0x6110), None);
        summary.return_relation = SummaryReturnRelation::HeapAlloc;
        summary.memory_effects.push(SummaryMemoryEffect {
            kind: SummaryMemoryEffectKind::Free,
            location: arg_location(0),
        });
        summary.memory_effects.push(SummaryMemoryEffect {
            kind: SummaryMemoryEffectKind::Read,
            location: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Global { address: 0xb000 },
                range: Some(SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 3,
                    width: Some(4),
                }),
            },
        });
        summary.reads_global_memory = true;

        let summaries = summaries_from_interproc_summary_unbounded(0x6110, &summary);

        assert!(
            summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Allocation))
        );
        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Lifetime)
                && matches!(
                    summary.lifetime,
                    Some(SummaryLifetimeEffect {
                        arg: 0,
                        op: SummaryLifetimeOp::Free,
                    })
                )
        }));
        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MetadataProbe)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Global { address: 0xb000 })
                )
        }));
    }

    #[test]
    fn dataflow_alias_index_uses_family_lookup_and_kills_stale_aliases() {
        let eax_0 = SSAVar::new("EAX", 0, 4);
        let eax_1 = SSAVar::new("EAX", 1, 4);
        let al_0 = SSAVar::new("AL", 0, 1);
        let first = LoadedSource {
            location: arg_byte_location(0),
            size: 4,
            block_addr: 0x4100,
            value_delta: 0,
        };
        let second = LoadedSource {
            location: arg_byte_location(1),
            size: 4,
            block_addr: 0x4110,
            value_delta: 0,
        };
        let mut state = WorkerDataflowState::default();

        insert_exact_load_source_value(&mut state, &eax_0, first);
        assert_eq!(dataflow_loaded_source(&al_0, &state), Some(first));

        dataflow_kill_load_source_aliases(&eax_1, &mut state);
        assert_eq!(dataflow_loaded_source(&al_0, &state), None);

        insert_exact_load_source_value(&mut state, &eax_1, second);
        assert_eq!(dataflow_loaded_source(&al_0, &state), Some(second));
    }

    #[test]
    fn dataflow_alias_index_rebuilds_after_join_conflict() {
        let eax = SSAVar::new("EAX", 0, 4);
        let al = SSAVar::new("AL", 0, 1);
        let mut left = WorkerDataflowState::default();
        let mut right = WorkerDataflowState::default();

        insert_exact_load_source_value(
            &mut left,
            &eax,
            LoadedSource {
                location: arg_byte_location(0),
                size: 4,
                block_addr: 0x4120,
                value_delta: 0,
            },
        );
        insert_exact_load_source_value(
            &mut right,
            &eax,
            LoadedSource {
                location: arg_byte_location(1),
                size: 4,
                block_addr: 0x4130,
                value_delta: 0,
            },
        );

        assert!(join_worker_state(&mut left, &right));
        assert_eq!(dataflow_loaded_source(&al, &left), None);
    }

    #[test]
    fn worker_dataflow_recovers_arg_root_through_stack_spill() {
        let slot_addr = SSAVar::new("tmp:slot_addr", 1, 8);
        let saved_ptr = SSAVar::new("tmp:saved_ptr", 1, 8);
        let indexed_ptr = SSAVar::new("tmp:indexed_ptr", 1, 8);
        let loaded_byte = SSAVar::new("tmp:loaded_byte", 1, 1);
        let stack_root = StackAddressRoot {
            base: r2ssa::StackAddressBase::FramePointer,
            offset: -0x18,
        };
        let stack_roots = BTreeMap::from([(slot_addr.clone(), stack_root)]);
        let block = r2ssa::function::SSABlock {
            addr: 0x4200,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Store {
                    space: "Ram".to_string(),
                    addr: slot_addr.clone(),
                    val: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::Load {
                    dst: saved_ptr.clone(),
                    space: "Ram".to_string(),
                    addr: slot_addr,
                },
                SSAOp::IntAdd {
                    dst: indexed_ptr.clone(),
                    a: saved_ptr,
                    b: SSAVar::constant(1, 8),
                },
                SSAOp::Load {
                    dst: loaded_byte.clone(),
                    space: "Ram".to_string(),
                    addr: indexed_ptr,
                },
            ],
        };

        let state = transfer_worker_block(
            &block,
            &WorkerDataflowState::default(),
            None,
            Some(&stack_roots),
        );
        let source = dataflow_loaded_source(&loaded_byte, &state).expect("arg byte source");

        assert_eq!(
            source.location.region,
            SummaryMemoryRegion::Arg { index: 0 }
        );
    }

    #[test]
    fn worker_dataflow_records_offset_arg_memory_write() {
        let ptr = SSAVar::new("tmp:out_plus_hash", 1, 8);
        let value = SSAVar::new("tmp:hash_value", 1, 8);
        let block = r2ssa::function::SSABlock {
            addr: 0x4280,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: ptr.clone(),
                    a: SSAVar::new("RSI", 0, 8),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Store {
                    space: "Ram".to_string(),
                    addr: ptr,
                    val: value,
                },
            ],
        };
        let mut observations = BlockWorkerObservations::default();

        transfer_worker_block(
            &block,
            &WorkerDataflowState::default(),
            Some(&mut observations),
            None,
        );

        assert_eq!(
            observations.memory_writes,
            vec![MemoryWriteObservation {
                anchor: 0x4280,
                location: SummaryMemoryLocation {
                    region: SummaryMemoryRegion::Arg { index: 1 },
                    range: Some(SummaryMemoryRange {
                        offset_lo: 8,
                        offset_hi: 8,
                        width: Some(8),
                    }),
                },
                width: 8,
            }]
        );
    }

    #[test]
    fn worker_dataflow_preserves_x86_byte_source_after_same_family_widening() {
        let loaded_byte = SSAVar::new("tmp:loaded_byte", 1, 1);
        let mut input = WorkerDataflowState::default();
        insert_exact_dataflow_value(
            &mut input.roots,
            &SSAVar::new("RDI", 0, 8),
            SummaryMemoryRegion::Arg { index: 0 },
        );
        let block = r2ssa::function::SSABlock {
            addr: 0x4300,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Load {
                    dst: loaded_byte.clone(),
                    space: "Ram".to_string(),
                    addr: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntZExt {
                    dst: SSAVar::new("EAX", 1, 4),
                    src: loaded_byte,
                },
                SSAOp::IntZExt {
                    dst: SSAVar::new("RAX", 2, 8),
                    src: SSAVar::new("EAX", 1, 4),
                },
                SSAOp::IntLess {
                    dst: SSAVar::new("CF", 1, 1),
                    a: SSAVar::new("AL", 0, 1),
                    b: SSAVar::constant(u64::from(b'/'), 1),
                },
            ],
        };
        let mut observations = BlockWorkerObservations::default();

        transfer_worker_block(&block, &input, Some(&mut observations), None);

        let evidence = observations
            .parser_comparisons
            .get(&0)
            .expect("arg byte compare should survive EAX/RAX widening");
        assert!(evidence.byte_ranges.contains(&ParserByteRange {
            lo: 0,
            hi: b'/' - 1
        }));
    }

    #[test]
    fn interproc_summary_rejects_name_only_getopt_and_hash_pattern_families() {
        let md5 = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5000),
            Some("sym._md5_process_block".to_string()),
        );
        let fnmatch = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5010),
            Some("sym._internal_fnwmatch".to_string()),
        );
        let getopt = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5020),
            Some("sym._getopt_internal_r".to_string()),
        );

        let md5_summaries = summaries_from_interproc_summary_unbounded(0x5000, &md5);
        let fnmatch_summaries = summaries_from_interproc_summary_unbounded(0x5010, &fnmatch);
        let getopt_summaries = summaries_from_interproc_summary_unbounded(0x5020, &getopt);

        assert!(
            md5_summaries.is_empty(),
            "function names alone must not manufacture hash-fold semantics: {md5_summaries:?}"
        );
        assert!(
            fnmatch_summaries.is_empty(),
            "function names alone must not manufacture parser/string-scan semantics: {fnmatch_summaries:?}"
        );
        assert!(
            getopt_summaries.is_empty(),
            "function names alone must not manufacture parser/table-walk semantics: {getopt_summaries:?}"
        );
    }

    #[test]
    fn hash_context_read_name_alone_does_not_create_state_copy() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5028),
            Some("dbg.sha384_read_ctx".to_string()),
        );
        let summaries = summaries_from_interproc_summary_unbounded(0x5028, &summary);

        assert!(
            summaries.is_empty(),
            "function names alone must not manufacture digest context effects: {summaries:?}"
        );
    }

    #[test]
    fn interproc_summary_rejects_broad_coreutils_name_only_families() {
        let digest = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5030),
            Some("sym.digest_file.isra.0".to_string()),
        );
        let binop = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5040),
            Some("sym.binop".to_string()),
        );
        let quote = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5050),
            Some("sym.quotearg_n_options".to_string()),
        );
        let mbrtowc = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5060),
            Some("sym.rpl_mbrtowc".to_string()),
        );
        let write_counts = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5070),
            Some("dbg.write_counts".to_string()),
        );
        let verror = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5080),
            Some("dbg.verror_at_line".to_string()),
        );
        let argmatch = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5090),
            Some("dbg.argmatch".to_string()),
        );
        let renameatu = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50a0),
            Some("dbg.renameatu".to_string()),
        );
        let streamsavedir = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50b0),
            Some("sym.streamsavedir".to_string()),
        );
        let quote_alloc = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50c0),
            Some("sym.quotearg_alloc_mem".to_string()),
        );
        let xpalloc = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50d0),
            Some("sym.xpalloc".to_string()),
        );
        let version = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50e0),
            Some("sym.version_etc_va".to_string()),
        );

        let digest_summaries = summaries_from_interproc_summary_unbounded(0x5030, &digest);
        let binop_summaries = summaries_from_interproc_summary_unbounded(0x5040, &binop);
        let quote_summaries = summaries_from_interproc_summary_unbounded(0x5050, &quote);
        let mbrtowc_summaries = summaries_from_interproc_summary_unbounded(0x5060, &mbrtowc);
        let write_counts_summaries =
            summaries_from_interproc_summary_unbounded(0x5070, &write_counts);
        let verror_summaries = summaries_from_interproc_summary_unbounded(0x5080, &verror);
        let argmatch_summaries = summaries_from_interproc_summary_unbounded(0x5090, &argmatch);
        let renameatu_summaries = summaries_from_interproc_summary_unbounded(0x50a0, &renameatu);
        let streamsavedir_summaries =
            summaries_from_interproc_summary_unbounded(0x50b0, &streamsavedir);
        let quote_alloc_summaries =
            summaries_from_interproc_summary_unbounded(0x50c0, &quote_alloc);
        let xpalloc_summaries = summaries_from_interproc_summary_unbounded(0x50d0, &xpalloc);
        let version_summaries = summaries_from_interproc_summary_unbounded(0x50e0, &version);

        assert!(digest_summaries.is_empty());
        assert!(binop_summaries.is_empty());
        let test_or = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5041),
            Some("dbg.or".to_string()),
        );
        let test_or_summaries = summaries_from_interproc_summary_unbounded(0x5041, &test_or);
        assert!(test_or_summaries.is_empty());
        assert!(quote_summaries.is_empty());
        assert!(mbrtowc_summaries.is_empty());
        assert!(write_counts_summaries.is_empty());
        assert!(verror_summaries.is_empty());
        assert!(argmatch_summaries.is_empty());
        assert!(renameatu_summaries.is_empty());
        assert!(streamsavedir_summaries.is_empty());
        assert!(quote_alloc_summaries.is_empty());
        assert!(xpalloc_summaries.is_empty());
        assert!(version_summaries.is_empty());
    }

    #[test]
    fn interproc_summary_rejects_named_worker_families_without_evidence() {
        let diagnose = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5100),
            Some("sym.diagnose".to_string()),
        );
        let printf_fetchargs = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5200),
            Some("sym.printf_fetchargs".to_string()),
        );
        let usage = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5300),
            Some("dbg.usage".to_string()),
        );
        let keycompare = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5400),
            Some("dbg.keycompare".to_string()),
        );
        let readlinebuffer = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5500),
            Some("sym.readlinebuffer_delim".to_string()),
        );
        let quotearg = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5600),
            Some("sym.quotearg_buffer_restyled".to_string()),
        );
        let mbrtoc32 = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5700),
            Some("sym.rpl_mbrtoc32".to_string()),
        );
        let xstrtoumax = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5800),
            Some("dbg.xstrtoumax".to_string()),
        );
        let vstrtoimax = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5801),
            Some("dbg.vstrtoimax".to_string()),
        );
        let copy_file_data = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5900),
            Some("sym.copy_file_data".to_string()),
        );
        let copy_with_unblock = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5901),
            Some("dbg.copy_with_unblock".to_string()),
        );
        let iwrite = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5902),
            Some("sym.iwrite.constprop.0".to_string()),
        );
        let translate_charset = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5903),
            Some("dbg.translate_charset".to_string()),
        );
        let invalidate_cache = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5904),
            Some("dbg.invalidate_cache".to_string()),
        );
        let parse_long_options = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5905),
            Some("dbg.parse_long_options".to_string()),
        );
        let parse_gnu_options = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5906),
            Some("dbg.parse_gnu_standard_options_only".to_string()),
        );
        let human_options = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5907),
            Some("dbg.human_options".to_string()),
        );
        let parse_integer = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5908),
            Some("dbg.parse_integer".to_string()),
        );
        let synchronize_output = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5909),
            Some("dbg.synchronize_output".to_string()),
        );
        let copy_internal = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5a00),
            Some("sym.copy_internal".to_string()),
        );
        let fts_read = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5b00),
            Some("sym.rpl_fts_read".to_string()),
        );
        let fts_close = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5b01),
            Some("sym.rpl_fts_close".to_string()),
        );
        let changedir = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5c00),
            Some("sym.fts_safe_changedir".to_string()),
        );
        let cut_fields = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5d00),
            Some("dbg.cut_fields_bytesearch".to_string()),
        );
        let print_long = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5e00),
            Some("dbg.print_long_format".to_string()),
        );
        let sort_merge = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5f00),
            Some("dbg.mergefps".to_string()),
        );
        let main_summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x6000),
            Some("dbg.main".to_string()),
        );

        let diagnose_summaries = summaries_from_interproc_summary_unbounded(0x5100, &diagnose);
        let fetch_summaries = summaries_from_interproc_summary_unbounded(0x5200, &printf_fetchargs);
        let usage_summaries = summaries_from_interproc_summary_unbounded(0x5300, &usage);
        let keycompare_summaries = summaries_from_interproc_summary_unbounded(0x5400, &keycompare);
        let readlinebuffer_summaries =
            summaries_from_interproc_summary_unbounded(0x5500, &readlinebuffer);
        let quotearg_summaries = summaries_from_interproc_summary_unbounded(0x5600, &quotearg);
        let mbrtoc32_summaries = summaries_from_interproc_summary_unbounded(0x5700, &mbrtoc32);
        let xstrtoumax_summaries = summaries_from_interproc_summary_unbounded(0x5800, &xstrtoumax);
        let vstrtoimax_summaries = summaries_from_interproc_summary_unbounded(0x5801, &vstrtoimax);
        let copy_file_summaries =
            summaries_from_interproc_summary_unbounded(0x5900, &copy_file_data);
        let copy_with_unblock_summaries =
            summaries_from_interproc_summary_unbounded(0x5901, &copy_with_unblock);
        let iwrite_summaries = summaries_from_interproc_summary_unbounded(0x5902, &iwrite);
        let translate_charset_summaries =
            summaries_from_interproc_summary_unbounded(0x5903, &translate_charset);
        let invalidate_cache_summaries =
            summaries_from_interproc_summary_unbounded(0x5904, &invalidate_cache);
        let parse_long_options_summaries =
            summaries_from_interproc_summary_unbounded(0x5905, &parse_long_options);
        let parse_gnu_options_summaries =
            summaries_from_interproc_summary_unbounded(0x5906, &parse_gnu_options);
        let human_options_summaries =
            summaries_from_interproc_summary_unbounded(0x5907, &human_options);
        let parse_integer_summaries =
            summaries_from_interproc_summary_unbounded(0x5908, &parse_integer);
        let synchronize_output_summaries =
            summaries_from_interproc_summary_unbounded(0x5909, &synchronize_output);
        let copy_internal_summaries =
            summaries_from_interproc_summary_unbounded(0x5a00, &copy_internal);
        let fts_read_summaries = summaries_from_interproc_summary_unbounded(0x5b00, &fts_read);
        let fts_close_summaries = summaries_from_interproc_summary_unbounded(0x5b01, &fts_close);
        let changedir_summaries = summaries_from_interproc_summary_unbounded(0x5c00, &changedir);
        let cut_field_summaries = summaries_from_interproc_summary_unbounded(0x5d00, &cut_fields);
        let print_long_summaries = summaries_from_interproc_summary_unbounded(0x5e00, &print_long);
        let sort_merge_summaries = summaries_from_interproc_summary_unbounded(0x5f00, &sort_merge);
        let main_summaries = summaries_from_interproc_summary_unbounded(0x6000, &main_summary);

        let name_only_summaries = [
            ("sym.diagnose", &diagnose_summaries),
            ("sym.printf_fetchargs", &fetch_summaries),
            ("dbg.usage", &usage_summaries),
            ("dbg.keycompare", &keycompare_summaries),
            ("sym.readlinebuffer_delim", &readlinebuffer_summaries),
            ("sym.quotearg_buffer_restyled", &quotearg_summaries),
            ("sym.rpl_mbrtoc32", &mbrtoc32_summaries),
            ("dbg.xstrtoumax", &xstrtoumax_summaries),
            ("dbg.vstrtoimax", &vstrtoimax_summaries),
            ("sym.copy_file_data", &copy_file_summaries),
            ("dbg.copy_with_unblock", &copy_with_unblock_summaries),
            ("sym.iwrite.constprop.0", &iwrite_summaries),
            ("dbg.translate_charset", &translate_charset_summaries),
            ("dbg.invalidate_cache", &invalidate_cache_summaries),
            ("dbg.parse_long_options", &parse_long_options_summaries),
            (
                "dbg.parse_gnu_standard_options_only",
                &parse_gnu_options_summaries,
            ),
            ("dbg.human_options", &human_options_summaries),
            ("dbg.parse_integer", &parse_integer_summaries),
            ("dbg.synchronize_output", &synchronize_output_summaries),
            ("sym.copy_internal", &copy_internal_summaries),
            ("sym.rpl_fts_read", &fts_read_summaries),
            ("sym.rpl_fts_close", &fts_close_summaries),
            ("sym.fts_safe_changedir", &changedir_summaries),
            ("dbg.cut_fields_bytesearch", &cut_field_summaries),
            ("dbg.print_long_format", &print_long_summaries),
            ("dbg.mergefps", &sort_merge_summaries),
            ("dbg.main", &main_summaries),
        ];

        for (name, summaries) in name_only_summaries {
            assert!(
                summaries.is_empty(),
                "function name alone must not manufacture native-worker summaries for {name}: {summaries:?}"
            );
        }
    }

    #[test]
    fn interproc_summary_rejects_broad_hard_failure_name_only_families() {
        let cases: &[(&str, &[NativeWorkerSummaryKind])] = &[
            (
                "dbg.__xargmatch_internal",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::DiagnosticWrapper,
                ],
            ),
            (
                "dbg.cut_file",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::FieldSelection,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.memchr2",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.hash_print_statistics",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "sym.hash_insert_if_absent",
                &[NativeWorkerSummaryKind::TableWalk],
            ),
            ("dbg.hash_lookup", &[NativeWorkerSummaryKind::TableWalk]),
            (
                "dbg.hash_get_entries",
                &[NativeWorkerSummaryKind::TableWalk],
            ),
            ("entry0", &[NativeWorkerSummaryKind::ProgramOrchestrator]),
            (
                "dbg.save_token",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.filename_unescape",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "sym.compare",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.close_stream",
                &[
                    NativeWorkerSummaryKind::OutputStream,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.record_file",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.reap",
                &[
                    NativeWorkerSummaryKind::Synchronization,
                    NativeWorkerSummaryKind::NumericTransform,
                ],
            ),
            ("dbg.quotearg_free", &[NativeWorkerSummaryKind::Lifetime]),
            (
                "sym.print_filename.part.0",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.file_name_concat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.wc_lines_avx2",
                &[NativeWorkerSummaryKind::RecordStream],
            ),
            (
                "dbg.full_read",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::MemoryRead,
                ],
            ),
            (
                "dbg.full_write",
                &[
                    NativeWorkerSummaryKind::OutputStream,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.copy_with_block",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            ("dbg.isaac_refill", &[NativeWorkerSummaryKind::TableWalk]),
            (
                "dbg.sort_files",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.stream_open",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.same_nameat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "sym.mcel_scan",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.set_process_security_ctx",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.strmode",
                &[
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.do_statx",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::PathWalk,
                ],
            ),
            (
                "dbg.mfile_name_concat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.getuidbyname",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.init_node",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "sym.mcel_scant",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.filenvercmp",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "sym.print_file_name_and_frills.isra.0",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::FormatRender,
                ],
            ),
            (
                "dbg.try_tempname_len",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.write_bytes",
                &[
                    NativeWorkerSummaryKind::OutputStream,
                    NativeWorkerSummaryKind::RecordStream,
                ],
            ),
            (
                "dbg.hash_clear",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Lifetime,
                ],
            ),
            (
                "dbg.hash_free",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Lifetime,
                ],
            ),
            (
                "sym.limfield.isra.0",
                &[
                    NativeWorkerSummaryKind::FieldSelection,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.fts_sort",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            ("dbg.xnumtoumax", &[NativeWorkerSummaryKind::Parser]),
            ("dbg.parse_field_count", &[NativeWorkerSummaryKind::Parser]),
            (
                "dbg.parse_symbols",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "sym.leave_dir",
                &[
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "sym.find_entry",
                &[
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "sym.rpl_fts_children",
                &[NativeWorkerSummaryKind::DirectoryTraversal],
            ),
            (
                "dbg.decode_preserve_arg",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.areadlink_with_size",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.mbsnwidth",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.file_escape",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.zaptemp",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::Lifetime,
                ],
            ),
            (
                "dbg.sequential_sort",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.open_input_files",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.get_meminfo",
                &[
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.randread_new",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.randread",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.gregorian_to_persian",
                &[NativeWorkerSummaryKind::NumericTransform],
            ),
            (
                "dbg.next_prime",
                &[NativeWorkerSummaryKind::NumericTransform],
            ),
            (
                "dbg.num_processors",
                &[
                    NativeWorkerSummaryKind::NumericTransform,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.rpl_pipe2",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.cycle_check",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::MemoryRead,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            ("dbg.copy_bytes", &[NativeWorkerSummaryKind::MemoryTransfer]),
            (
                "sym.oprintf_.constprop.0",
                &[
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.setlocale_null_r_unlocked",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.gettext_quote",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.set_program_name",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Synchronization,
                ],
            ),
            (
                "dbg.file_prefixlen",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "sym.operand_matches",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.xstrcoll_df_version",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::StringScan,
                ],
            ),
            ("dbg.alloc_ibuf", &[NativeWorkerSummaryKind::Allocation]),
        ];

        for (idx, (name, _expected_kinds)) in cases.iter().enumerate() {
            let summary = FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(0x7000 + idx as u64),
                Some((*name).to_string()),
            );
            let summaries =
                summaries_from_interproc_summary_unbounded(0x7000 + idx as u64, &summary);
            assert!(
                summaries.is_empty(),
                "function name alone must not manufacture native-worker summaries for {name}: {summaries:?}"
            );
        }
    }

    #[test]
    fn native_worker_family_predicate_recognizes_summary_owned_names() {
        assert!(has_native_worker_summary_family("dbg.readlinebuffer_delim"));
        assert!(has_native_worker_summary_family("sym.printf_fetchargs"));
        assert!(has_native_worker_summary_family("sym.oprintf_.constprop.0"));
        assert!(has_native_worker_summary_family(
            "sym.quotearg_buffer_restyled"
        ));
        assert!(!has_native_worker_summary_family("sym._md5_process_block"));
        assert!(!has_native_worker_summary_family("dbg.sha384_read_ctx"));
        assert!(has_native_worker_summary_family("sym._internal_fnwmatch"));
        assert!(has_native_worker_summary_family("sym._getopt_internal_r"));
        assert!(has_native_worker_summary_family("sym.digest_file.isra.0"));
        assert!(has_native_worker_summary_family("sym.binop"));
        assert!(has_native_worker_summary_family("dbg.write_counts"));
        assert!(has_native_worker_summary_family("dbg.verror_at_line"));
        assert!(has_native_worker_summary_family("dbg.argmatch"));
        assert!(has_native_worker_summary_family("dbg.print_xfer_stats"));
        assert!(has_native_worker_summary_family("sym.quotearg_n_options"));
        assert!(has_native_worker_summary_family("sym.quotearg_alloc_mem"));
        assert!(has_native_worker_summary_family(
            "sym.clone_quoting_options"
        ));
        assert!(has_native_worker_summary_family("sym.version_etc_va"));
        assert!(has_native_worker_summary_family("dbg.renameatu"));
        assert!(has_native_worker_summary_family("dbg.streamsavedir"));
        assert!(has_native_worker_summary_family("sym.xpalloc"));
        assert!(has_native_worker_summary_family("sym.rpl_mbrtowc"));
        assert!(has_native_worker_summary_family("sym.rpl_fopen"));
        assert!(has_native_worker_summary_family("dbg.openat_safer"));
        assert!(has_native_worker_summary_family("dbg.rpl_nanosleep"));
        assert!(has_native_worker_summary_family("dbg.xnanosleep"));
        assert!(has_native_worker_summary_family("dbg.settimeout"));
        assert!(has_native_worker_summary_family("entry.init0"));
        assert!(has_native_worker_summary_family("entry0"));
        assert!(has_native_worker_summary_family("entry.fini0"));
        assert!(has_native_worker_summary_family("sym.register_tm_clones"));
        assert!(has_native_worker_summary_family("sym._init"));
        assert!(has_native_worker_summary_family("sym.copy_file_data"));
        assert!(has_native_worker_summary_family("dbg.copy_with_unblock"));
        assert!(has_native_worker_summary_family("dbg.copy_bytes"));
        assert!(has_native_worker_summary_family("sym.iwrite.constprop.0"));
        assert!(has_native_worker_summary_family("dbg.translate_charset"));
        assert!(has_native_worker_summary_family("dbg.invalidate_cache"));
        assert!(has_native_worker_summary_family("dbg.parse_long_options"));
        assert!(has_native_worker_summary_family(
            "dbg.parse_gnu_standard_options_only"
        ));
        assert!(has_native_worker_summary_family("dbg.human_options"));
        assert!(has_native_worker_summary_family("dbg.parse_integer"));
        assert!(has_native_worker_summary_family("dbg.parse_number"));
        assert!(has_native_worker_summary_family("dbg.traverse_raw_number"));
        assert!(has_native_worker_summary_family("dbg.synchronize_output"));
        assert!(has_native_worker_summary_family("sym.rpl_fts_read"));
        assert!(has_native_worker_summary_family("sym.rpl_fts_close"));
        assert!(has_native_worker_summary_family("sym.fts_safe_changedir"));
        assert!(has_native_worker_summary_family(
            "dbg.cut_fields_bytesearch"
        ));
        assert!(has_native_worker_summary_family("dbg.print_long_format"));
        assert!(has_native_worker_summary_family("dbg.mergefps"));
        assert!(has_native_worker_summary_family("dbg.main"));
        assert!(has_native_worker_summary_family("dbg.__xargmatch_internal"));
        assert!(has_native_worker_summary_family("dbg.cut_file"));
        assert!(has_native_worker_summary_family("dbg.cut_bytes"));
        assert!(has_native_worker_summary_family("dbg.memchr2"));
        assert!(has_native_worker_summary_family(
            "dbg.hash_print_statistics"
        ));
        assert!(has_native_worker_summary_family(
            "sym.hash_insert_if_absent"
        ));
        assert!(has_native_worker_summary_family("sym.hash_rehash"));
        assert!(has_native_worker_summary_family("dbg.excise"));
        assert!(has_native_worker_summary_family(
            "sym.print_filename.part.0"
        ));
        assert!(has_native_worker_summary_family("dbg.wc_lines_avx512"));
        assert!(has_native_worker_summary_family("dbg.sort_files"));
        assert!(has_native_worker_summary_family("dbg.stream_open"));
        assert!(has_native_worker_summary_family("dbg.same_nameat"));
        assert!(has_native_worker_summary_family("sym.mcel_scan"));
        assert!(has_native_worker_summary_family("sym.mcel_cmp"));
        assert!(has_native_worker_summary_family("sym.mcel_tocmp"));
        assert!(has_native_worker_summary_family(
            "dbg.set_process_security_ctx"
        ));
        assert!(has_native_worker_summary_family("dbg.strmode"));
        assert!(has_native_worker_summary_family("dbg.do_statx"));
        assert!(has_native_worker_summary_family("dbg.get_dir_status"));
        assert!(has_native_worker_summary_family("dbg.is_utf8_charset"));
        assert!(has_native_worker_summary_family("dbg.mfile_name_concat"));
        assert!(has_native_worker_summary_family("dbg.getuidbyname"));
        assert!(has_native_worker_summary_family("dbg.init_node"));
        assert!(has_native_worker_summary_family("dbg.mergefiles"));
        assert!(has_native_worker_summary_family("dbg.xnrealloc"));
        assert!(has_native_worker_summary_family("sym.mcel_scant"));
        assert!(has_native_worker_summary_family("dbg.filenvercmp"));
        assert!(has_native_worker_summary_family(
            "sym.print_file_name_and_frills.isra.0"
        ));
        assert!(has_native_worker_summary_family("dbg.try_tempname_len"));
        assert!(has_native_worker_summary_family("dbg.close_stdin"));
        assert!(has_native_worker_summary_family("dbg.rpl_fclose"));
        assert!(has_native_worker_summary_family("dbg.write_bytes"));
        assert!(has_native_worker_summary_family("dbg.hash_clear"));
        assert!(has_native_worker_summary_family("dbg.hash_free"));
        assert!(has_native_worker_summary_family("sym.limfield.isra.0"));
        assert!(has_native_worker_summary_family("dbg.fts_sort"));
        assert!(has_native_worker_summary_family("dbg.xnumtoumax"));
        assert!(has_native_worker_summary_family("sym.leave_dir"));
        assert!(has_native_worker_summary_family("sym.find_entry"));
        assert!(has_native_worker_summary_family("dbg.decode_preserve_arg"));
        assert!(has_native_worker_summary_family("dbg.areadlink_with_size"));
        assert!(has_native_worker_summary_family("dbg.mbsnwidth"));
        assert!(has_native_worker_summary_family(
            "sym.print_filename.part.0"
        ));
        assert!(has_native_worker_summary_family("dbg.prompt.constprop.0"));
        assert!(has_native_worker_summary_family("dbg.file_escape"));
        assert!(has_native_worker_summary_family("dbg.zaptemp"));
        assert!(has_native_worker_summary_family("dbg.sequential_sort"));
        assert!(has_native_worker_summary_family("dbg.open_input_files"));
        assert!(has_native_worker_summary_family("dbg.get_meminfo"));
        assert!(has_native_worker_summary_family("dbg.randread_new"));
        assert!(has_native_worker_summary_family("dbg.randread"));
        assert!(has_native_worker_summary_family(
            "dbg._gl_scratch_buffer_grow_preserve"
        ));
        assert!(has_native_worker_summary_family("dbg.argv_iter"));
        assert!(has_native_worker_summary_family("dbg.argv_iter_init_argv"));
        assert!(has_native_worker_summary_family(
            "dbg.argv_iter_init_stream"
        ));
        assert!(has_native_worker_summary_family("dbg.gregorian_to_persian"));
        assert!(has_native_worker_summary_family(
            "dbg.gregorian_to_ethiopian"
        ));
        assert!(has_native_worker_summary_family("dbg.next_prime"));
        assert!(has_native_worker_summary_family("dbg.num_processors"));
        assert!(has_native_worker_summary_family("sym.rpl_pipe2"));
        assert!(has_native_worker_summary_family("dbg.cycle_check_init"));
        assert!(has_native_worker_summary_family("dbg.cycle_check"));
        assert!(has_native_worker_summary_family("dbg.fdutimensat"));
        assert!(has_native_worker_summary_family(
            "dbg.setlocale_null_r_unlocked"
        ));
        assert!(has_native_worker_summary_family("dbg.gettext_quote"));
        assert!(has_native_worker_summary_family("dbg.set_program_name"));
        assert!(has_native_worker_summary_family("dbg.mcel_scanz"));
        assert!(has_native_worker_summary_family("dbg.nstrftime"));
        assert!(has_native_worker_summary_family("dbg.mktime_z"));
        assert!(has_native_worker_summary_family(
            "dbg.length_of_file_name_and_frills"
        ));
        assert!(has_native_worker_summary_family("dbg.yesno"));
        assert!(!has_native_worker_summary_family(
            "sym.sha256_process_block"
        ));
        assert!(!has_native_worker_summary_family(
            "sym.sha256_process_bytes"
        ));
        assert!(!has_native_worker_summary_family("sym.sm3_process_block"));
        assert!(has_native_worker_summary_family("dbg.save_token"));
        assert!(has_native_worker_summary_family("dbg.filename_unescape"));
        assert!(has_native_worker_summary_family("sym.compare"));
        assert!(has_native_worker_summary_family("dbg.memcoll"));
        assert!(has_native_worker_summary_family("dbg.close_stream"));
        assert!(has_native_worker_summary_family("dbg.rpl_fseeko"));
        assert!(has_native_worker_summary_family("sym.maybe_close_stdout"));
        assert!(has_native_worker_summary_family("dbg.print_stats"));
        assert!(has_native_worker_summary_family("dbg.create_hard_link"));
        assert!(has_native_worker_summary_family("dbg.fopen_safer"));
        assert!(has_native_worker_summary_family("dbg.open_safer"));
        assert!(has_native_worker_summary_family("dbg.rpl_fflush"));
        assert!(has_native_worker_summary_family("dbg.tzalloc"));
        assert!(has_native_worker_summary_family("dbg.xget_version"));
        assert!(has_native_worker_summary_family("dbg.rpl_reallocarray"));
        assert!(has_native_worker_summary_family("dbg.record_file"));
        assert!(has_native_worker_summary_family("sym.calc_req_mask"));
        assert!(has_native_worker_summary_family("dbg.reap"));
        assert!(has_native_worker_summary_family(
            "dbg.num_processors_via_affinity_mask"
        ));
        assert!(has_native_worker_summary_family("dbg.process_signals"));
        assert!(has_native_worker_summary_family("dbg.exit_cleanup"));
        assert!(has_native_worker_summary_family("dbg.clear_files"));
        assert!(has_native_worker_summary_family("dbg.cwd_advance_fd"));
        assert!(has_native_worker_summary_family("dbg.restore_initial_cwd"));
        assert!(has_native_worker_summary_family("dbg.get_root_dev_ino"));
        assert!(has_native_worker_summary_family("dbg.getuser"));
        assert!(has_native_worker_summary_family("dbg.getgroup"));
        assert!(has_native_worker_summary_family("dbg.last_component"));
        assert!(has_native_worker_summary_family("sym.flush_stdout"));
        assert!(has_native_worker_summary_family("sym.format_user_or_group"));
        assert!(has_native_worker_summary_family("sym.xstrtol_fatal"));
        assert!(has_native_worker_summary_family("sym.rpl_obstack_free"));
        assert!(has_native_worker_summary_family(
            "dbg.rpl_obstack_allocated_p"
        ));
        assert!(has_native_worker_summary_family("dbg.has_xattr"));
        assert!(has_native_worker_summary_family("dbg.check_tuning"));
        assert!(has_native_worker_summary_family("dbg.imaxtostr"));
        assert!(has_native_worker_summary_family("dbg.umaxtostr"));
        assert!(has_native_worker_summary_family("dbg.hwcap_allowed"));
        assert!(has_native_worker_summary_family("dbg.file_prefixlen"));
        assert!(has_native_worker_summary_family("dbg.getmonth"));
        assert!(has_native_worker_summary_family("sym.operand_matches"));
        assert!(has_native_worker_summary_family("dbg.xstrxfrm"));
        assert!(has_native_worker_summary_family(
            "dbg.set_file_security_ctx"
        ));
        assert!(has_native_worker_summary_family("dbg.localtime_rz"));
        assert!(has_native_worker_summary_family("dbg.locale_charset"));
        assert!(has_native_worker_summary_family("dbg.current_timespec"));
        assert!(has_native_worker_summary_family(
            "dbg.rpl_obstack_memory_used"
        ));
        assert!(has_native_worker_summary_family("dbg.alloc_ibuf"));
        assert!(has_native_worker_summary_family("dbg.alloc_obuf"));
        assert!(has_native_worker_summary_family("dbg.xstrcoll_df_version"));
        assert!(has_native_worker_summary_family("dbg.rev_strcmp_df_mtime"));
        assert!(has_native_worker_summary_family("dbg.hash_lookup"));
        assert!(has_native_worker_summary_family("dbg.hash_get_entries"));
        assert!(has_native_worker_summary_family("dbg.heap_insert"));
        assert!(!has_native_worker_summary_family("dbg.raw_hasher"));
        assert!(!has_native_worker_summary_family("sym.blake2b_compress"));
        assert!(has_native_worker_summary_family(
            "dbg.re_string_reconstruct"
        ));
        assert!(has_native_worker_summary_family("dbg.parse_datetime_body"));
        assert!(has_native_worker_summary_family("dbg.posixtime"));
        assert!(has_native_worker_summary_family("dbg.randperm_new"));
        assert!(has_native_worker_summary_family("dbg.readtoken"));
        assert!(has_native_worker_summary_family("dbg.readtokens"));
        assert!(has_native_worker_summary_family("dbg.re_search_internal"));
        assert!(has_native_worker_summary_family("dbg.re_compile_internal"));
        assert!(has_native_worker_summary_family("dbg.parse_expression"));
        assert!(has_native_worker_summary_family("dbg.build_trtable"));
        assert!(has_native_worker_summary_family(
            "dbg.update_cur_sifted_state"
        ));
        assert!(has_native_worker_summary_family("dbg.transit_state_bkref"));
        assert!(has_native_worker_summary_family("dbg.build_charclass"));
        assert!(has_native_worker_summary_family("dbg.check_arrival"));
        assert!(has_native_worker_summary_family("dbg.peek_token"));
        assert!(has_native_worker_summary_family(
            "dbg.build_wcs_upper_buffer"
        ));
        assert!(has_native_worker_summary_family("dbg.yyparse"));
        assert!(has_native_worker_summary_family("dbg.install_file_in_file"));
        assert!(has_native_worker_summary_family("dbg.chown_files"));
        assert!(has_native_worker_summary_family("dbg.read_utmp"));
        assert!(has_native_worker_summary_family("dbg.dopass"));
        assert!(has_native_worker_summary_family("sym.factor_up.part.0"));
        assert!(has_native_worker_summary_family(
            "dbg.mp_factor_using_pollard_rho"
        ));
        assert!(has_native_worker_summary_family("dbg.seq_fast"));
        assert!(has_native_worker_summary_family("dbg.tsort"));
        assert!(has_native_worker_summary_family("dbg.parse_field_count"));
        assert!(has_native_worker_summary_family("dbg.parse_symbols"));
        assert!(has_native_worker_summary_family("dbg.file_name_concat"));
        assert!(has_native_worker_summary_family("dbg.rpl_fts_children"));
        assert!(has_native_worker_summary_family("dbg.full_read"));
        assert!(has_native_worker_summary_family("dbg.full_write"));
        assert!(has_native_worker_summary_family("dbg.copy_with_block"));
        assert!(has_native_worker_summary_family("dbg.error_tail"));
        assert!(has_native_worker_summary_family("dbg.argmatch_to_argument"));
        assert!(has_native_worker_summary_family("dbg.opendirat"));
        assert!(has_native_worker_summary_family("dbg.fd_safer"));
        assert!(has_native_worker_summary_family("dbg.verror"));
        assert!(has_native_worker_summary_family("dbg.print_errno_message"));
        assert!(has_native_worker_summary_family("sym.begfield.isra.0"));
        assert!(has_native_worker_summary_family("dbg.emit_verbose"));
        assert!(has_native_worker_summary_family("dbg.create_hole"));
        assert!(has_native_worker_summary_family("dbg.posix2_version"));
        assert!(has_native_worker_summary_family("dbg.rpl_getfilecon_raw"));
        assert!(has_native_worker_summary_family("dbg.fadvise"));
        assert!(has_native_worker_summary_family("dbg.indent"));
        assert!(has_native_worker_summary_family("dbg.dired_dump_obstack"));
        assert!(has_native_worker_summary_family(
            "dbg._obstack_begin_worker"
        ));
        assert!(has_native_worker_summary_family("dbg.heap_remove_top"));
        assert!(!has_native_worker_summary_family(
            "dbg.test_symbolic_xor_guard"
        ));
    }

    #[test]
    fn named_coreutils_tail_helpers_do_not_materialize_without_evidence() {
        let cases: &[(&str, &[NativeWorkerSummaryKind])] = &[
            (
                "dbg.error_tail",
                &[NativeWorkerSummaryKind::DiagnosticWrapper],
            ),
            (
                "dbg.argmatch_to_argument",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MemoryRead,
                ],
            ),
            (
                "dbg.opendirat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            ("dbg.fd_safer", &[NativeWorkerSummaryKind::MetadataProbe]),
            (
                "dbg.print_errno_message",
                &[NativeWorkerSummaryKind::DiagnosticWrapper],
            ),
            (
                "dbg.emit_verbose",
                &[
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.posix2_version",
                &[NativeWorkerSummaryKind::MetadataProbe],
            ),
            (
                "dbg.rpl_getfilecon_raw",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.dired_dump_obstack",
                &[
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg._obstack_begin_worker",
                &[
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.heap_remove_top",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            ("dbg.indent", &[NativeWorkerSummaryKind::NumericTransform]),
            (
                "dbg.re_string_reconstruct",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::NumericTransform,
                ],
            ),
            (
                "dbg.re_search_internal",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.parse_datetime_body",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.posixtime",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.randperm_new",
                &[
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.readtoken",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.readtokens",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.re_compile_internal",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.update_cur_sifted_state",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::NumericTransform,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.check_arrival",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::NumericTransform,
                ],
            ),
            (
                "dbg.install_file_in_file",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::FileTransfer,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.chown_files",
                &[
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.read_utmp",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::RecordStream,
                ],
            ),
            (
                "dbg.dopass",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::NumericTransform,
                ],
            ),
            (
                "sym.factor_up.part.0.constprop.0",
                &[
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::NumericTransform,
                ],
            ),
            (
                "dbg.seq_fast",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
        ];

        for (idx, (name, _expected_kinds)) in cases.iter().enumerate() {
            let summary = FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(0x9100 + idx as u64),
                Some((*name).to_string()),
            );
            let summaries =
                summaries_from_interproc_summary_unbounded(0x9100 + idx as u64, &summary);
            assert!(
                summaries.is_empty(),
                "function name alone must not manufacture native-worker summaries for {name}: {summaries:?}"
            );
        }
    }

    #[test]
    fn native_worker_summary_applicability_rejects_name_hint_families() {
        let applicability =
            native_worker_summary_applicability_for_name(0x401000, "dbg.save_token");

        assert!(!applicability.is_supported());
        assert!(applicability.worker_kinds.is_empty());
        assert!(applicability.sources.is_empty());
        assert_eq!(
            applicability.evidence.reasons,
            vec![SemanticEvidenceReason::ResidualSearchRequired]
        );
    }

    #[test]
    fn native_worker_summary_applicability_marks_structural_seed_evidence() {
        let applicability =
            native_worker_summary_applicability_for_name(0x401000, "sym.imp.malloc");

        assert!(applicability.is_supported());
        assert!(!applicability.is_name_hint_only());
        assert!(applicability.has_non_name_evidence());
        assert!(
            applicability
                .worker_kinds
                .contains(&NativeWorkerSummaryKind::Allocation)
        );
        assert!(
            applicability
                .sources
                .contains(&NativeWorkerSummaryApplicabilitySource::AllocationEffect)
        );
    }

    #[test]
    fn native_worker_summary_applicability_rejects_unknown_names() {
        let applicability =
            native_worker_summary_applicability_for_name(0x401000, "dbg.not_a_known_worker");

        assert!(!applicability.is_supported());
        assert!(applicability.worker_kinds.is_empty());
    }

    #[test]
    fn semantic_route_name_normalization_owns_compiler_suffixes() {
        let cases = [
            ("sym.limfield.isra.0", Some("limfield")),
            ("dbg.factor_up.part.0.constprop.0", Some("factor_up")),
            ("fcn.00008b50", Some("00008b50")),
            ("sub.00401000", Some("00401000")),
            ("", None),
        ];

        for (name, expected) in cases {
            assert_eq!(
                normalize_native_worker_role_name(name).as_deref(),
                expected,
                "{name}",
            );
        }
    }

    #[test]
    fn semantic_route_name_classifies_anonymous_and_autogenerated_names() {
        for name in [
            "fcn.00008b50",
            "sym.fcn.00008b50",
            "sub_401000",
            "dbg.sub.401000",
        ] {
            assert!(is_anonymous_semantic_route_name(name), "{name}");
            assert!(is_autogenerated_semantic_function_name(name), "{name}");
        }

        for name in ["loc.401000", "_00401000", ""] {
            assert!(!is_anonymous_semantic_route_name(name), "{name}");
            assert!(is_autogenerated_semantic_function_name(name), "{name}");
        }

        for name in ["_", "sym.limfield.isra.0", "dbg.worker", "main"] {
            assert!(!is_anonymous_semantic_route_name(name), "{name}");
            assert!(!is_autogenerated_semantic_function_name(name), "{name}");
        }
    }

    #[test]
    fn native_worker_summary_route_policy_rejects_name_only_direct_summary_roles() {
        for name in ["sym.blake2b_compress", "dbg.sha384_read_ctx"] {
            let policy = native_worker_summary_route_policy_for_name(0x401000, name);

            assert_eq!(
                policy.kind,
                NativeWorkerSummaryRouteKind::Standard,
                "unexpected policy for {name}: {policy:?}"
            );
            assert!(!policy.should_use_direct_summary());
            assert!(policy.certificate.is_none());
            assert!(
                !policy.applicability.is_supported(),
                "hash/digest names alone must not create worker applicability for {name}: {policy:?}"
            );
        }

        for name in ["dbg.settimeout", "dbg.xnmalloc"] {
            let policy = native_worker_summary_route_policy_for_name(0x401000, name);

            assert_eq!(
                policy.kind,
                NativeWorkerSummaryRouteKind::Standard,
                "unexpected policy for {name}: {policy:?}"
            );
            assert!(!policy.should_use_direct_summary());
            assert!(policy.certificate.is_none());
            assert!(
                !policy.applicability.is_supported(),
                "function names alone must not create worker applicability for {name}: {policy:?}"
            );
            assert!(
                !policy
                    .applicability
                    .sources
                    .contains(&NativeWorkerSummaryApplicabilitySource::TrustedSymbol),
                "name-only route must not be upgraded to trusted symbol for {name}"
            );
        }
    }

    #[test]
    fn native_worker_summary_route_policy_rejects_prefer_full_without_compatible_evidence() {
        let policy = native_worker_summary_route_policy_for_name(0x401000, "dbg.diagnose");

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::Standard);
        assert!(!policy.should_prefer_full());
        assert!(!policy.should_use_direct_summary());
        assert!(policy.certificate.is_none());
        assert!(!policy.applicability.is_supported());

        let mut summary = FunctionSemanticSummary::unknown(
            InterprocFunctionId(0x401000),
            Some("dbg.diagnose".to_string()),
        );
        summary.return_relation = SummaryReturnRelation::Void;
        let policy = native_worker_summary_route_policy_for_summary(0x401000, &summary);

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::Standard);
        assert!(!policy.should_prefer_full());
        assert!(!policy.should_use_direct_summary());
        assert!(policy.applicability.has_route_evidence());
        assert!(
            policy.certificate.is_none(),
            "void return evidence alone is not compatible diagnostic route evidence"
        );
    }

    #[test]
    fn native_worker_summary_route_policy_certifies_direct_summary_only_with_evidence() {
        let mut summary = FunctionSemanticSummary::unknown(
            InterprocFunctionId(0x401000),
            Some("dbg.xnmalloc".to_string()),
        );
        summary.allocation_effects.push(SummaryAllocationEffect {
            size_arg: Some(1),
            zeroed: false,
        });
        summary.return_relation = SummaryReturnRelation::HeapAlloc;

        let policy = native_worker_summary_route_policy_for_summary(0x401000, &summary);

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::DirectSummary);
        assert!(policy.should_use_direct_summary());
        let certificate = policy.certificate.as_ref().expect("route certificate");
        assert_eq!(
            certificate.route_kind,
            SummaryRouteCertificateKind::DirectSummary
        );
        assert_eq!(certificate.normalized_name.as_deref(), Some("xnmalloc"));
        assert_ne!(certificate.source, SemanticClaimSource::NameHint);
        assert_eq!(
            certificate.route_evidence_kinds,
            BTreeSet::from([NativeWorkerSummaryKind::Allocation])
        );
    }

    #[test]
    fn summary_route_certificate_identity_includes_route_evidence_kind() {
        let applicability = |kind| NativeWorkerSummaryApplicability {
            normalized_name: Some("xnmalloc".to_string()),
            worker_kinds: BTreeSet::from([kind]),
            route_evidence_kinds: BTreeSet::from([kind]),
            sources: BTreeSet::from([NativeWorkerSummaryApplicabilitySource::AllocationEffect]),
            evidence: SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget),
        };
        let allocation = summary_route_certificate(
            0x401000,
            NativeWorkerSummaryRouteKind::DirectSummary,
            Some("xnmalloc"),
            &applicability(NativeWorkerSummaryKind::Allocation),
            "allocation route",
        );
        let transfer = summary_route_certificate(
            0x401000,
            NativeWorkerSummaryRouteKind::DirectSummary,
            Some("xnmalloc"),
            &applicability(NativeWorkerSummaryKind::MemoryTransfer),
            "allocation route",
        );

        assert_ne!(allocation.stable_id, transfer.stable_id);
        assert_ne!(
            allocation.route_evidence_kinds,
            transfer.route_evidence_kinds
        );
    }

    #[test]
    fn native_worker_summary_route_policy_rejects_stale_route_certificate_kind() {
        let mut summary = FunctionSemanticSummary::unknown(
            InterprocFunctionId(0x401000),
            Some("dbg.xnmalloc".to_string()),
        );
        summary.allocation_effects.push(SummaryAllocationEffect {
            size_arg: Some(1),
            zeroed: false,
        });
        summary.return_relation = SummaryReturnRelation::HeapAlloc;
        let mut policy = native_worker_summary_route_policy_for_summary(0x401000, &summary);
        policy
            .certificate
            .as_mut()
            .expect("route certificate")
            .route_kind = SummaryRouteCertificateKind::Standard;

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::DirectSummary);
        assert!(!policy.has_route_certificate());
        assert!(!policy.should_use_direct_summary());
    }

    #[test]
    fn native_worker_summary_route_policy_rejects_name_hint_route_certificate() {
        let mut summary = FunctionSemanticSummary::unknown(
            InterprocFunctionId(0x401000),
            Some("dbg.xnmalloc".to_string()),
        );
        summary.allocation_effects.push(SummaryAllocationEffect {
            size_arg: Some(1),
            zeroed: false,
        });
        summary.return_relation = SummaryReturnRelation::HeapAlloc;
        let mut policy = native_worker_summary_route_policy_for_summary(0x401000, &summary);
        policy
            .certificate
            .as_mut()
            .expect("route certificate")
            .source = SemanticClaimSource::NameHint;

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::DirectSummary);
        assert!(!policy.has_route_certificate());
        assert!(!policy.should_use_direct_summary());
    }

    #[test]
    fn native_worker_summary_route_policy_rejects_unrelated_structural_evidence_for_named_family() {
        let mut summary = FunctionSemanticSummary::unknown(
            InterprocFunctionId(0x401000),
            Some("dbg.error_tail".to_string()),
        );
        summary.return_relation = SummaryReturnRelation::Arg(0);

        let policy = native_worker_summary_route_policy_for_summary(0x401000, &summary);

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::Standard);
        assert!(!policy.should_use_direct_summary());
        assert!(
            policy.certificate.is_none(),
            "unrelated structural evidence must not certify the error_tail route"
        );
    }

    #[test]
    fn native_worker_summary_route_policy_keeps_unknown_names_standard() {
        let policy =
            native_worker_summary_route_policy_for_name(0x401000, "dbg.not_a_known_worker");

        assert_eq!(policy.kind, NativeWorkerSummaryRouteKind::Standard);
        assert!(!policy.should_use_direct_summary());
        assert!(!policy.should_prefer_full());
        assert!(policy.certificate.is_none());
        assert!(!policy.applicability.is_supported());
    }

    #[test]
    fn named_worker_family_summaries_have_deterministic_bounded_evidence() {
        let names = [
            "dbg.full_write",
            "sym.sha256_process_block",
            "dbg.parse_symbols",
            "dbg.file_name_concat",
            "dbg.rpl_fts_children",
            "dbg.hash_lookup",
            "dbg.full_read",
        ];
        let summaries_for_names = |names: &[&str]| {
            names
                .iter()
                .enumerate()
                .flat_map(|(idx, name)| {
                    let summary = FunctionSemanticSummary::unknown(
                        r2ssa::InterprocFunctionId(0x8000 + idx as u64),
                        Some((*name).to_string()),
                    );
                    summaries_from_interproc_summary_unbounded(0x8000 + idx as u64, &summary)
                })
                .collect::<Vec<_>>()
        };

        let first = bounded_worker_summaries(summaries_for_names(&names));
        let second = bounded_worker_summaries(summaries_for_names(&names));

        assert_eq!(first, second);
        assert!(
            first.is_empty(),
            "function names alone must not manufacture bounded worker summaries: {first:?}"
        );
        assert!(first.windows(2).all(|pair| {
            native_worker_summary_sort_key(&pair[0]) <= native_worker_summary_sort_key(&pair[1])
        }));
        for summary in first {
            assert_eq!(summary.evidence.tier, SemanticConfidence::Heuristic);
            assert_eq!(summary.evidence.coverage, SemanticEvidenceCoverage::Bounded);
            assert_eq!(
                summary.evidence.provenance,
                SemanticEvidenceProvenance::Ranked
            );
            assert_eq!(
                summary.evidence.ambiguity,
                SemanticEvidenceAmbiguity::Ranked
            );
            assert!(summary.evidence.budget_limited);
            assert_eq!(
                summary.evidence.reasons,
                vec![
                    SemanticEvidenceReason::SummaryBudget,
                    SemanticEvidenceReason::NameHint
                ]
            );
        }
    }

    #[test]
    fn named_hash_fold_family_does_not_create_summary_without_evidence() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x9000),
            Some("dbg.raw_hasher".to_string()),
        );

        let summaries = summaries_from_interproc_summary_unbounded(0x9000, &summary);
        assert!(
            summaries
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::HashFold)),
            "raw_hasher name alone must not create hash-fold semantics: {summaries:?}"
        );
    }

    #[test]
    fn scratch_buffer_growth_name_alone_does_not_create_summary() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x9100),
            Some("dbg._gl_scratch_buffer_grow_preserve".to_string()),
        );

        let summaries = summaries_from_interproc_summary_unbounded(0x9100, &summary);

        assert!(
            summaries.is_empty(),
            "function names alone must not manufacture scratch-buffer effects: {summaries:?}"
        );
    }

    #[test]
    fn argv_iterator_name_alone_does_not_create_summary() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x9200),
            Some("dbg.argv_iter".to_string()),
        );

        let summaries = summaries_from_interproc_summary_unbounded(0x9200, &summary);

        assert!(
            summaries.is_empty(),
            "function names alone must not manufacture argv-iterator semantics: {summaries:?}"
        );
    }

    #[test]
    fn region_summaries_preserve_loop_island_shape() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x30, 1);
        let pred = Varnode::unique(0x31, 1);
        let mut block = R2ILBlock::new(0x4020, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(0, 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4020, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("loop scan SSA");
        let workers =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let regions = classify_native_region_summaries(&artifact, &workers);

        assert!(regions.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.header == 0x4020 && loop_summary.body.contains(&0x4020)
                })
                && summary.arg_indices().contains(&0)
        }));
    }

    #[test]
    fn region_summaries_preserve_full_domain_beyond_worker_display_cap() {
        let arch = aarch64_test_arch();
        let block = R2ILBlock::new(0x5000, 4);
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("fixture SSA");
        let workers = (0..(NATIVE_WORKER_SUMMARY_MAX + 8))
            .map(|index| {
                memory_worker_summary(
                    0x6000 + (index as u64 * 0x10),
                    SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location: SummaryMemoryLocation {
                            region: SummaryMemoryRegion::Arg { index },
                            range: None,
                        },
                    },
                )
            })
            .collect::<Vec<_>>();

        let display_workers = bounded_worker_summaries(workers.clone());
        let regions = classify_native_region_summaries(&artifact, &workers);

        assert_eq!(display_workers.len(), NATIVE_WORKER_SUMMARY_MAX);
        assert!(
            regions.len() > display_workers.len(),
            "region summaries are canonical analysis facts and must not be capped by display workers"
        );
        assert!(regions.iter().any(|summary| {
            summary
                .arg_indices()
                .contains(&(NATIVE_WORKER_SUMMARY_MAX + 7))
        }));
    }

    #[test]
    fn bounded_worker_summaries_keep_named_families_over_generic_memory_effects() {
        let anchor = 0x6000;
        let mut workers = vec![
            record_stream_worker_summary(anchor, 0, None),
            field_selection_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ];
        workers.extend((0..(NATIVE_WORKER_SUMMARY_MAX + 8)).map(|index| {
            memory_worker_summary(
                anchor,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index },
                        range: None,
                    },
                },
            )
        }));

        let display_workers = bounded_worker_summaries(workers);

        assert_eq!(display_workers.len(), NATIVE_WORKER_SUMMARY_MAX);
        assert!(
            display_workers
                .iter()
                .any(|summary| summary.kind == NativeWorkerSummaryKind::RecordStream)
        );
        assert!(
            display_workers
                .iter()
                .any(|summary| summary.kind == NativeWorkerSummaryKind::FieldSelection)
        );
        assert!(
            display_workers
                .iter()
                .any(|summary| summary.kind == NativeWorkerSummaryKind::OutputStream)
        );
    }

    #[test]
    fn region_summaries_join_memory_access_ranges() {
        let arch = aarch64_test_arch();
        let block = R2ILBlock::new(0x7000, 4);
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("range join fixture SSA");
        let workers = (0..6)
            .map(|index| {
                memory_worker_summary(
                    0x7000,
                    SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location: SummaryMemoryLocation {
                            region: SummaryMemoryRegion::Arg { index: 0 },
                            range: Some(SummaryMemoryRange {
                                offset_lo: index * 8,
                                offset_hi: index * 8 + 7,
                                width: Some(8),
                            }),
                        },
                    },
                )
            })
            .collect::<Vec<_>>();

        let regions = classify_native_region_summaries(&artifact, &workers);

        let summary = regions
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::MemoryRead))
            .expect("read summary");
        assert_eq!(summary.memory_accesses.len(), 1);
        let range = summary.memory_accesses[0]
            .location
            .and_then(|location| location.range)
            .expect("joined range");
        assert_eq!(range.offset_lo, 0);
        assert_eq!(range.offset_hi, 47);
        assert_eq!(range.width, Some(8));
    }
}
