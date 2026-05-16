use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    SummaryAllocationEffect, SummaryAtomicEffect, SummaryLifetimeEffect, SummaryMemoryLocation,
    SummarySyncEffect, SummaryTransferLength,
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::backward::{BackwardConditionSummary, BackwardMemoryCondition};
use crate::sim::DerivedSummaryDiagnostics;

use super::artifact::{
    ResidualReason, SemanticConfidence, SemanticEvidence, SemanticEvidenceReason, SliceClass,
};
use super::facts::SymbolicReachabilityStatus;
use super::vm::{InterpreterDispatchSummary, VmStepSummary};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RefinementStage {
    Raw,
    Compiled,
    Residual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ArtifactGranularity {
    WholeFunction,
    Regioned,
    SummaryOnly,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ExecutionModel {
    Native,
    Vm,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RegionKey {
    pub anchor_block: u64,
    pub frontier: BTreeSet<u64>,
}

impl RegionKey {
    pub fn new(anchor_block: u64, frontier: BTreeSet<u64>) -> Self {
        Self {
            anchor_block,
            frontier,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Judged<T> {
    pub value: T,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl<T> Judged<T> {
    pub fn new(value: T, evidence: SemanticEvidence) -> Self {
        Self { value, evidence }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ControlFact {
    pub target: u64,
    pub status: SymbolicReachabilityStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_truth: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled: Option<BackwardConditionSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryFact {
    pub term: BackwardMemoryCondition,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticPredicate {
    pub expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled: Option<BackwardConditionSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetFact {
    pub target: u64,
    pub status: SymbolicReachabilityStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_truth: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticRegion {
    pub anchor: u64,
    pub frontier: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub control: Vec<Judged<ControlFact>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory: Vec<Judged<MemoryFact>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub pre: Vec<Judged<SemanticPredicate>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub post: Vec<Judged<SemanticPredicate>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub targets: Vec<Judged<TargetFact>>,
}

impl SemanticRegion {
    pub fn key(&self) -> RegionKey {
        RegionKey::new(self.anchor, self.frontier.clone())
    }

    fn compiled_condition_for_target(
        &self,
        target: u64,
        proof_only: bool,
    ) -> Option<&BackwardConditionSummary> {
        self.control
            .iter()
            .find(|fact| fact.value.target == target)
            .and_then(|fact| {
                let allowed = if proof_only {
                    fact.evidence.allows_hard_proof()
                } else {
                    fact.evidence.allows_narrowing()
                };
                allowed.then_some(fact.value.compiled.as_ref()).flatten()
            })
    }

    fn unique_compiled_condition(&self, proof_only: bool) -> Option<&BackwardConditionSummary> {
        let mut candidates = self.control.iter().filter_map(|fact| {
            let allowed = if proof_only {
                fact.evidence.allows_hard_proof()
            } else {
                fact.evidence.allows_narrowing()
            };
            allowed.then_some(fact.value.compiled.as_ref()).flatten()
        });
        let first = candidates.next()?;
        candidates
            .all(|candidate| candidate == first)
            .then_some(first)
    }

    fn unique_reachable_target(&self, proof_only: bool) -> Option<u64> {
        let mut candidates = self.control.iter().filter_map(|fact| {
            let allowed = if proof_only {
                fact.evidence.allows_hard_proof()
            } else {
                fact.evidence.allows_narrowing()
            };
            allowed
                .then_some(matches!(
                    fact.value.status,
                    SymbolicReachabilityStatus::Reachable
                ))
                .and_then(|reachable| reachable.then_some(fact.value.target))
        });
        let first = candidates.next()?;
        candidates
            .all(|candidate| candidate == first)
            .then_some(first)
    }

    pub fn exact_reachable_target(&self) -> Option<u64> {
        self.unique_reachable_target(true)
    }

    pub fn actionable_reachable_target(&self) -> Option<u64> {
        self.unique_reachable_target(false)
    }

    pub fn exact_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        self.unique_compiled_condition(true)
    }

    pub fn actionable_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        self.unique_compiled_condition(false)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.compiled_condition_for_target(target, true)
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.compiled_condition_for_target(target, false)
    }

    pub fn exact_memory_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.memory
            .iter()
            .filter(|term| term.evidence.allows_hard_proof())
            .map(|term| &term.value.term)
            .collect()
    }

    pub fn actionable_memory_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.memory
            .iter()
            .filter(|term| term.evidence.allows_narrowing())
            .map(|term| &term.value.term)
            .collect()
    }

    pub fn exact_memory_terms_for_target(&self, target: u64) -> Vec<&BackwardMemoryCondition> {
        self.exact_compiled_condition_for_target(target)
            .map(|compiled| {
                compiled
                    .memory_terms
                    .iter()
                    .filter(|term| term.evidence().allows_hard_proof())
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn actionable_memory_terms_for_target(&self, target: u64) -> Vec<&BackwardMemoryCondition> {
        match self.actionable_compiled_condition_for_target(target) {
            Some(compiled) if !compiled.memory_terms.is_empty() => compiled
                .memory_terms
                .iter()
                .filter(|term| term.evidence().allows_narrowing())
                .collect(),
            Some(_) => Vec::new(),
            None => {
                if self.actionable_reachable_target() == Some(target) {
                    self.actionable_memory_terms()
                } else {
                    Vec::new()
                }
            }
        }
    }

    pub fn branch_truth_for_target(&self, target: u64) -> Option<bool> {
        self.control
            .iter()
            .find(|fact| fact.value.target == target)
            .and_then(|fact| fact.value.branch_truth)
    }

    pub fn supports_guarded_structuring(&self) -> bool {
        let reachable_target = self
            .exact_reachable_target()
            .or_else(|| self.actionable_reachable_target());
        let has_condition = reachable_target
            .and_then(|target| self.actionable_compiled_condition_for_target(target))
            .is_some();
        let has_memory_facts = !self.memory.is_empty()
            || self
                .control
                .iter()
                .filter_map(|fact| fact.value.compiled.as_ref())
                .any(|compiled| !compiled.memory_terms.is_empty());
        let has_target_memory_support = reachable_target
            .map(|target| !self.actionable_memory_terms_for_target(target).is_empty())
            .unwrap_or(false);
        self.control
            .iter()
            .any(|fact| fact.evidence.allows_guarded_structuring())
            && has_condition
            && (!has_memory_facts || has_target_memory_support)
    }

    pub fn supports_query_guidance(&self) -> bool {
        self.control
            .iter()
            .any(|fact| fact.evidence.allows_narrowing() && fact.value.compiled.is_some())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeWorkerSummaryKind {
    ProgramOrchestrator,
    MemoryTransfer,
    FileTransfer,
    MemoryRead,
    MemoryWrite,
    MemoryEscape,
    MemoryFree,
    StringScan,
    HashFold,
    TableWalk,
    PathWalk,
    DirectoryTraversal,
    RecordStream,
    FieldSelection,
    OutputStream,
    FormatRender,
    MetadataProbe,
    SortMerge,
    NumericTransform,
    Parser,
    DiagnosticWrapper,
    FormatArgumentFetch,
    Allocation,
    Lifetime,
    Synchronization,
    Atomic,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeSummarySpecificity {
    ProgramOrchestrator,
    GenericMemory,
    MemoryTransfer,
    FileTransfer,
    StringScan,
    HashFold,
    TableWalk,
    PathWalk,
    DirectoryTraversal,
    RecordStream,
    FieldSelection,
    OutputStream,
    FormatRender,
    MetadataProbe,
    SortMerge,
    NumericTransform,
    Parser,
    SemanticWrapper,
    RuntimeEffect,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeWorkerRoleSource {
    Structural,
    SummarySeed,
    NameHint,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeWorkerRoleIdentity {
    pub role_name: String,
    pub source: NativeWorkerRoleSource,
    pub confidence: SemanticConfidence,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_names: Vec<String>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub summary_kinds: BTreeSet<NativeWorkerSummaryKind>,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl NativeSummarySpecificity {
    pub fn is_primary_renderable(self) -> bool {
        !matches!(self, Self::GenericMemory | Self::Unknown)
    }
}

impl NativeWorkerSummaryKind {
    pub fn canonical_role_name(self) -> &'static str {
        match self {
            Self::ProgramOrchestrator => "program_orchestrator",
            Self::MemoryTransfer => "memory_transfer",
            Self::FileTransfer => "file_transfer",
            Self::MemoryRead => "memory_read",
            Self::MemoryWrite => "memory_write",
            Self::MemoryEscape => "memory_escape",
            Self::MemoryFree => "memory_free",
            Self::StringScan => "string_scan",
            Self::HashFold => "hash_fold",
            Self::TableWalk => "table_walk",
            Self::PathWalk => "path_walk",
            Self::DirectoryTraversal => "directory_traversal",
            Self::RecordStream => "record_stream",
            Self::FieldSelection => "field_selection",
            Self::OutputStream => "output_stream",
            Self::FormatRender => "format_render",
            Self::MetadataProbe => "metadata_probe",
            Self::SortMerge => "sort_merge",
            Self::NumericTransform => "numeric_transform",
            Self::Parser => "parser",
            Self::DiagnosticWrapper => "diagnostic_wrapper",
            Self::FormatArgumentFetch => "format_argument_fetch",
            Self::Allocation => "allocation",
            Self::Lifetime => "lifetime",
            Self::Synchronization => "synchronization",
            Self::Atomic => "atomic",
            Self::Unknown => "unknown",
        }
    }

    pub fn base_specificity(self) -> NativeSummarySpecificity {
        match self {
            Self::ProgramOrchestrator => NativeSummarySpecificity::ProgramOrchestrator,
            Self::MemoryTransfer => NativeSummarySpecificity::MemoryTransfer,
            Self::FileTransfer => NativeSummarySpecificity::FileTransfer,
            Self::MemoryRead | Self::MemoryWrite => NativeSummarySpecificity::GenericMemory,
            Self::MemoryEscape
            | Self::MemoryFree
            | Self::Allocation
            | Self::Lifetime
            | Self::Synchronization
            | Self::Atomic => NativeSummarySpecificity::RuntimeEffect,
            Self::StringScan => NativeSummarySpecificity::StringScan,
            Self::HashFold => NativeSummarySpecificity::HashFold,
            Self::TableWalk => NativeSummarySpecificity::TableWalk,
            Self::PathWalk => NativeSummarySpecificity::PathWalk,
            Self::DirectoryTraversal => NativeSummarySpecificity::DirectoryTraversal,
            Self::RecordStream => NativeSummarySpecificity::RecordStream,
            Self::FieldSelection => NativeSummarySpecificity::FieldSelection,
            Self::OutputStream => NativeSummarySpecificity::OutputStream,
            Self::FormatRender => NativeSummarySpecificity::FormatRender,
            Self::MetadataProbe => NativeSummarySpecificity::MetadataProbe,
            Self::SortMerge => NativeSummarySpecificity::SortMerge,
            Self::NumericTransform => NativeSummarySpecificity::NumericTransform,
            Self::Parser => NativeSummarySpecificity::Parser,
            Self::DiagnosticWrapper | Self::FormatArgumentFetch => {
                NativeSummarySpecificity::SemanticWrapper
            }
            Self::Unknown => NativeSummarySpecificity::Unknown,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeWorkerTerminator {
    None,
    ZeroByte,
    ByteEquals(u8),
    LengthBound,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeWorkerFoldOperation {
    Add,
    Xor,
    RotateMix,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeWorkerPredicate {
    ByteEqArg { arg: usize },
    ByteEqConst { value: u8 },
    AnyOf(Vec<NativeWorkerPredicate>),
    AllOf(Vec<NativeWorkerPredicate>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeWorkerFold {
    pub accumulator: String,
    pub bits: u32,
    pub operation: NativeWorkerFoldOperation,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub predicate: Option<NativeWorkerPredicate>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeParserKind {
    Numeric,
    Token,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeParserSummary {
    pub kind: NativeParserKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cursor_arg: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digit_min: Option<u8>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digit_max: Option<u8>,
    #[serde(default)]
    pub accepts_sign: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeWorkerLoopSummary {
    pub header: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exit_target: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub iterations: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub length_arg: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stride: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub terminator: Option<NativeWorkerTerminator>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fold: Option<NativeWorkerFold>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeWorkerSummary {
    pub anchor: u64,
    pub kind: NativeWorkerSummaryKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dst: Option<SummaryMemoryLocation>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub src: Option<SummaryMemoryLocation>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub memory: Option<SummaryMemoryLocation>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub len: Option<SummaryTransferLength>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allocation: Option<SummaryAllocationEffect>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lifetime: Option<SummaryLifetimeEffect>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sync: Option<SummarySyncEffect>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub atomic: Option<SummaryAtomicEffect>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parser: Option<NativeParserSummary>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loop_summary: Option<NativeWorkerLoopSummary>,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl NativeWorkerSummary {
    pub fn specificity(&self) -> NativeSummarySpecificity {
        if self.kind == NativeWorkerSummaryKind::NumericTransform {
            return NativeSummarySpecificity::NumericTransform;
        }
        if self.parser.is_some() {
            return NativeSummarySpecificity::Parser;
        }
        if self
            .loop_summary
            .as_ref()
            .and_then(|summary| summary.fold.as_ref())
            .is_some()
        {
            return NativeSummarySpecificity::HashFold;
        }
        match self.kind.base_specificity() {
            NativeSummarySpecificity::GenericMemory
                if self.loop_summary.as_ref().is_some_and(|summary| {
                    summary.length_arg.is_some()
                        || summary.stride.is_some()
                        || summary.terminator.is_some_and(|terminator| {
                            !matches!(
                                terminator,
                                NativeWorkerTerminator::None | NativeWorkerTerminator::Unknown
                            )
                        })
                }) =>
            {
                NativeSummarySpecificity::StringScan
            }
            specificity => specificity,
        }
    }

    pub fn is_generic_memory_summary(&self) -> bool {
        self.specificity() == NativeSummarySpecificity::GenericMemory
    }

    pub fn is_primary_render_summary(&self) -> bool {
        self.specificity().is_primary_renderable()
    }

    pub fn has_name_hint_evidence(&self) -> bool {
        self.evidence
            .reasons
            .contains(&SemanticEvidenceReason::NameHint)
    }

    pub fn is_primary_non_name_summary(&self) -> bool {
        self.is_primary_render_summary() && !self.has_name_hint_evidence()
    }

    pub fn arg_indices(&self) -> BTreeSet<usize> {
        let mut indices = BTreeSet::new();
        collect_location_arg_indices(self.dst.as_ref(), &mut indices);
        collect_location_arg_indices(self.src.as_ref(), &mut indices);
        collect_location_arg_indices(self.memory.as_ref(), &mut indices);
        if let Some(SummaryTransferLength::Arg(index)) = self.len {
            indices.insert(index);
        }
        if let Some(length_arg) = self
            .loop_summary
            .as_ref()
            .and_then(|summary| summary.length_arg)
        {
            indices.insert(length_arg);
        }
        if let Some(effect) = self.allocation
            && let Some(index) = effect.size_arg
        {
            indices.insert(index);
        }
        if let Some(effect) = self.lifetime {
            indices.insert(effect.arg);
        }
        if let Some(effect) = self.sync {
            indices.insert(effect.arg);
        }
        collect_location_arg_indices(
            self.atomic.as_ref().map(|effect| &effect.location),
            &mut indices,
        );
        if let Some(parser) = self.parser.as_ref()
            && let Some(index) = parser.cursor_arg
        {
            indices.insert(index);
        }
        indices
    }

    pub fn out_param_indices(&self) -> BTreeSet<usize> {
        let mut indices = BTreeSet::new();
        match self.kind {
            NativeWorkerSummaryKind::MemoryTransfer => {
                collect_location_arg_indices(self.dst.as_ref(), &mut indices);
            }
            NativeWorkerSummaryKind::NumericTransform => {
                collect_location_arg_indices(self.dst.as_ref(), &mut indices);
            }
            NativeWorkerSummaryKind::MemoryWrite | NativeWorkerSummaryKind::Atomic => {
                collect_location_arg_indices(self.memory.as_ref(), &mut indices);
                collect_location_arg_indices(
                    self.atomic.as_ref().map(|effect| &effect.location),
                    &mut indices,
                );
            }
            _ => {}
        }
        indices
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NativeMemoryAccessKind {
    Read,
    Write,
    Transfer,
    Escape,
    Free,
    Allocation,
    Lifetime,
    Synchronization,
    Atomic,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeMemoryAccessSummary {
    pub kind: NativeMemoryAccessKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<SummaryMemoryLocation>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dst: Option<SummaryMemoryLocation>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub src: Option<SummaryMemoryLocation>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub len: Option<SummaryTransferLength>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub width: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeReductionSummary {
    pub accumulator: String,
    pub bits: u32,
    pub operation: NativeWorkerFoldOperation,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<SummaryMemoryLocation>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeLoopSummary {
    pub header: u64,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub body: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub entries: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub exits: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub iterations: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub length_arg: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stride: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub terminator: Option<NativeWorkerTerminator>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeRegionSummary {
    pub stable_id: u64,
    pub anchor: u64,
    pub kind: NativeWorkerSummaryKind,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub blocks: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub entries: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub exits: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_accesses: Vec<NativeMemoryAccessSummary>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loop_summary: Option<NativeLoopSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reductions: Vec<NativeReductionSummary>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parser: Option<NativeParserSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<ResidualReason>,
    pub confidence: SemanticConfidence,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl NativeRegionSummary {
    pub fn specificity(&self) -> NativeSummarySpecificity {
        if self.parser.is_some() {
            return NativeSummarySpecificity::Parser;
        }
        if !self.reductions.is_empty() {
            return NativeSummarySpecificity::HashFold;
        }
        match self.kind.base_specificity() {
            NativeSummarySpecificity::GenericMemory
                if self.loop_summary.as_ref().is_some_and(|summary| {
                    summary.length_arg.is_some()
                        || summary.stride.is_some()
                        || summary.terminator.is_some_and(|terminator| {
                            !matches!(
                                terminator,
                                NativeWorkerTerminator::None | NativeWorkerTerminator::Unknown
                            )
                        })
                }) =>
            {
                NativeSummarySpecificity::StringScan
            }
            specificity => specificity,
        }
    }

    pub fn is_generic_memory_summary(&self) -> bool {
        self.specificity() == NativeSummarySpecificity::GenericMemory
    }

    pub fn is_primary_render_summary(&self) -> bool {
        self.specificity().is_primary_renderable()
    }

    pub fn has_name_hint_evidence(&self) -> bool {
        self.evidence
            .reasons
            .contains(&SemanticEvidenceReason::NameHint)
    }

    pub fn is_primary_non_name_summary(&self) -> bool {
        self.is_primary_render_summary() && !self.has_name_hint_evidence()
    }

    pub fn arg_indices(&self) -> BTreeSet<usize> {
        let mut indices = BTreeSet::new();
        for access in &self.memory_accesses {
            collect_location_arg_indices(access.location.as_ref(), &mut indices);
            collect_location_arg_indices(access.dst.as_ref(), &mut indices);
            collect_location_arg_indices(access.src.as_ref(), &mut indices);
            if let Some(SummaryTransferLength::Arg(index)) = access.len {
                indices.insert(index);
            }
        }
        if let Some(length_arg) = self
            .loop_summary
            .as_ref()
            .and_then(|summary| summary.length_arg)
        {
            indices.insert(length_arg);
        }
        if let Some(parser) = self.parser.as_ref()
            && let Some(index) = parser.cursor_arg
        {
            indices.insert(index);
        }
        indices
    }

    pub fn out_param_indices(&self) -> BTreeSet<usize> {
        let mut indices = BTreeSet::new();
        for access in &self.memory_accesses {
            match access.kind {
                NativeMemoryAccessKind::Write
                | NativeMemoryAccessKind::Transfer
                | NativeMemoryAccessKind::Atomic => {
                    collect_location_arg_indices(access.location.as_ref(), &mut indices);
                    collect_location_arg_indices(access.dst.as_ref(), &mut indices);
                }
                _ => {}
            }
        }
        indices
    }
}

fn collect_location_arg_indices(
    location: Option<&SummaryMemoryLocation>,
    indices: &mut BTreeSet<usize>,
) {
    if let Some(SummaryMemoryLocation {
        region: r2ssa::SummaryMemoryRegion::Arg { index },
        ..
    }) = location
    {
        indices.insert(*index);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeFunctionSummary {
    pub slice_class: SliceClass,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role_identity: Option<Box<NativeWorkerRoleIdentity>>,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub derived_diagnostics: DerivedSummaryDiagnostics,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub region_summaries: Vec<NativeRegionSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub worker_summaries: Vec<NativeWorkerSummary>,
}

impl NativeFunctionSummary {
    pub fn primary_region_summary_count(&self) -> usize {
        self.region_summaries
            .iter()
            .filter(|summary| summary.is_primary_render_summary())
            .count()
    }

    pub fn primary_worker_summary_count(&self) -> usize {
        self.worker_summaries
            .iter()
            .filter(|summary| summary.is_primary_render_summary())
            .count()
    }

    pub fn primary_summary_count(&self) -> usize {
        if self.region_summaries.is_empty() {
            self.primary_worker_summary_count()
        } else {
            self.primary_region_summary_count()
        }
    }

    pub fn generic_memory_summary_count(&self) -> usize {
        self.region_summaries
            .iter()
            .filter(|summary| summary.is_generic_memory_summary())
            .count()
            + self
                .worker_summaries
                .iter()
                .filter(|summary| summary.is_generic_memory_summary())
                .count()
    }

    pub fn has_primary_summary(&self) -> bool {
        self.primary_summary_count() > 0
    }

    pub fn has_primary_non_name_summary(&self) -> bool {
        if self.region_summaries.is_empty() {
            self.worker_summaries
                .iter()
                .any(NativeWorkerSummary::is_primary_non_name_summary)
        } else {
            self.region_summaries
                .iter()
                .any(NativeRegionSummary::is_primary_non_name_summary)
        }
    }

    pub fn has_memory_read_write_pair(&self) -> bool {
        let mut has_read = false;
        let mut has_write = false;
        for summary in &self.region_summaries {
            has_read |= matches!(summary.kind, NativeWorkerSummaryKind::MemoryRead);
            has_write |= matches!(summary.kind, NativeWorkerSummaryKind::MemoryWrite);
        }
        for summary in &self.worker_summaries {
            has_read |= matches!(summary.kind, NativeWorkerSummaryKind::MemoryRead);
            has_write |= matches!(summary.kind, NativeWorkerSummaryKind::MemoryWrite);
        }
        has_read && has_write
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeArtifactBody {
    pub summary: NativeFunctionSummary,
    #[serde(
        default,
        skip_serializing_if = "BTreeMap::is_empty",
        serialize_with = "serialize_region_map",
        deserialize_with = "deserialize_region_map"
    )]
    pub regions: BTreeMap<RegionKey, SemanticRegion>,
}

fn serialize_region_map<S>(
    regions: &BTreeMap<RegionKey, SemanticRegion>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    regions
        .values()
        .cloned()
        .collect::<Vec<_>>()
        .serialize(serializer)
}

fn deserialize_region_map<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<RegionKey, SemanticRegion>, D::Error>
where
    D: Deserializer<'de>,
{
    let regions = Vec::<SemanticRegion>::deserialize(deserializer)?;
    Ok(regions
        .into_iter()
        .map(|region| (region.key(), region))
        .collect())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemanticTargetConditionSource<'a> {
    pub block_addr: u64,
    pub branch_truth: bool,
    pub summary: &'a BackwardConditionSummary,
    pub necessary_for_target: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SemanticTargetRegionSource<'a> {
    pub region: &'a SemanticRegion,
    pub branch_truth: Option<bool>,
    pub summary: &'a BackwardConditionSummary,
    pub necessary_for_target: bool,
}

fn summary_strength_rank(
    summary: &BackwardConditionSummary,
) -> (u8, u8, usize, usize, usize, usize) {
    let strength = summary.evidence().strength_rank();
    (
        strength.0,
        strength.1,
        summary.memory_terms.len(),
        summary.supported_paths,
        usize::MAX.saturating_sub(summary.total_paths),
        usize::MAX.saturating_sub(summary.simplified.len()),
    )
}

impl NativeArtifactBody {
    fn target_source_region(&self, target_addr: u64, proof_only: bool) -> Option<&SemanticRegion> {
        self.authoritative_target_region_source(target_addr, proof_only)
            .map(|source| source.region)
    }

    fn target_memory_region_candidates(&self, target_addr: u64) -> Vec<&SemanticRegion> {
        self.regions
            .values()
            .filter(|region| {
                !region
                    .actionable_memory_terms_for_target(target_addr)
                    .is_empty()
            })
            .collect()
    }

    fn target_memory_sources_are_equivalent(
        candidates: &[&SemanticRegion],
        target_addr: u64,
    ) -> bool {
        let Some(first) = candidates.first() else {
            return true;
        };
        let first_terms = first.actionable_memory_terms_for_target(target_addr);
        candidates.iter().all(|candidate| {
            candidate.actionable_memory_terms_for_target(target_addr) == first_terms
        })
    }

    fn authoritative_memory_region(&self, target_addr: u64) -> Option<&SemanticRegion> {
        let candidates = self.target_memory_region_candidates(target_addr);
        if candidates.is_empty() {
            return None;
        }
        if !Self::target_memory_sources_are_equivalent(&candidates, target_addr) {
            return None;
        }
        candidates.into_iter().next()
    }

    fn target_region_candidates(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Vec<SemanticTargetRegionSource<'_>> {
        self.regions
            .values()
            .filter_map(|region| {
                let necessary_for_target = if proof_only {
                    region.exact_reachable_target() == Some(target_addr)
                } else {
                    region.actionable_reachable_target() == Some(target_addr)
                };
                let summary = if proof_only {
                    region.exact_compiled_condition_for_target(target_addr)
                } else {
                    region.actionable_compiled_condition_for_target(target_addr)
                }?;
                Some(SemanticTargetRegionSource {
                    region,
                    branch_truth: region.branch_truth_for_target(target_addr),
                    summary,
                    necessary_for_target,
                })
            })
            .collect()
    }

    fn target_sources_are_equivalent(candidates: &[SemanticTargetRegionSource<'_>]) -> bool {
        let Some(first) = candidates.first() else {
            return true;
        };
        candidates.iter().all(|candidate| {
            candidate.summary == first.summary
                && !matches!(
                    (candidate.branch_truth, first.branch_truth),
                    (Some(left), Some(right)) if left != right
                )
        })
    }

    fn authoritative_target_region_source(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<SemanticTargetRegionSource<'_>> {
        let candidates = self.target_region_candidates(target_addr, proof_only);
        if candidates.is_empty() {
            return None;
        }
        if proof_only
            && candidates
                .iter()
                .any(|candidate| !candidate.necessary_for_target)
        {
            return None;
        }
        if !Self::target_sources_are_equivalent(&candidates) {
            return None;
        }
        let representative = candidates.iter().copied().max_by(|left, right| {
            (
                usize::from(left.necessary_for_target),
                summary_strength_rank(left.summary),
                usize::MAX.saturating_sub(left.region.anchor as usize),
                usize::from(left.branch_truth.unwrap_or(false)),
            )
                .cmp(&(
                    usize::from(right.necessary_for_target),
                    summary_strength_rank(right.summary),
                    usize::MAX.saturating_sub(right.region.anchor as usize),
                    usize::from(right.branch_truth.unwrap_or(false)),
                ))
        })?;
        Some(SemanticTargetRegionSource {
            necessary_for_target: candidates
                .iter()
                .all(|candidate| candidate.necessary_for_target),
            ..representative
        })
    }

    pub fn target_source_conflict(&self, target_addr: u64, proof_only: bool) -> bool {
        let candidates = self.target_region_candidates(target_addr, proof_only);
        candidates.len() > 1 && !Self::target_sources_are_equivalent(&candidates)
    }

    pub fn conflicting_targets(&self, proof_only: bool) -> BTreeSet<u64> {
        self.regions
            .values()
            .flat_map(|region| region.control.iter().map(|fact| fact.value.target))
            .filter(|target| self.target_source_conflict(*target, proof_only))
            .collect()
    }

    pub fn region_for_anchor(&self, anchor: u64) -> Option<&SemanticRegion> {
        self.regions.values().find(|region| region.anchor == anchor)
    }

    pub fn exact_control_count(&self) -> usize {
        self.regions
            .values()
            .flat_map(|region| region.control.iter())
            .filter(|fact| fact.evidence.allows_hard_proof())
            .count()
    }

    pub fn actionable_control_count(&self) -> usize {
        self.regions
            .values()
            .flat_map(|region| region.control.iter())
            .filter(|fact| fact.evidence.allows_narrowing())
            .count()
    }

    pub fn supports_guarded_structuring(&self) -> bool {
        self.regions.values().any(|region| {
            region.supports_guarded_structuring()
                && region
                    .actionable_reachable_target()
                    .is_some_and(|target| !self.target_source_conflict(target, false))
        })
    }

    pub fn has_summary_islands(&self) -> bool {
        !self.summary.region_summaries.is_empty() || !self.summary.worker_summaries.is_empty()
    }

    pub fn has_primary_summary_islands(&self) -> bool {
        self.summary.has_primary_summary()
    }

    pub fn has_primary_non_name_summary_islands(&self) -> bool {
        self.summary.has_primary_non_name_summary()
    }

    pub fn summary_island_count(&self) -> usize {
        if self.summary.region_summaries.is_empty() {
            self.summary.worker_summaries.len()
        } else {
            self.summary.region_summaries.len()
        }
    }

    pub fn primary_summary_island_count(&self) -> usize {
        self.summary.primary_summary_count()
    }

    pub fn generic_memory_summary_count(&self) -> usize {
        self.summary.generic_memory_summary_count()
    }

    pub fn has_memory_read_write_summary_pair(&self) -> bool {
        self.summary.has_memory_read_write_pair()
    }

    pub fn supports_query_guidance(&self) -> bool {
        self.regions
            .values()
            .any(SemanticRegion::supports_query_guidance)
    }

    pub fn has_target_guidance(&self, target_addr: u64, proof_only: bool) -> bool {
        self.target_source_region(target_addr, proof_only).is_some()
    }

    pub fn target_guidance_is_necessary(&self, target_addr: u64, proof_only: bool) -> bool {
        self.target_source_region(target_addr, proof_only)
            .is_some_and(|region| {
                if proof_only {
                    region.exact_reachable_target() == Some(target_addr)
                } else {
                    region.actionable_reachable_target() == Some(target_addr)
                }
            })
    }

    pub fn exact_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::exact_reachable_target)
    }

    pub fn exact_branch_truth_for_block(&self, block_addr: u64) -> Option<bool> {
        let region = self.region_for_anchor(block_addr)?;
        let target = region.exact_reachable_target()?;
        region.branch_truth_for_target(target)
    }

    pub fn actionable_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::actionable_reachable_target)
    }

    pub fn exact_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::exact_compiled_condition)
    }

    pub fn actionable_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::actionable_compiled_condition)
    }

    pub fn actionable_memory_terms_for_block(
        &self,
        block_addr: u64,
    ) -> Vec<&BackwardMemoryCondition> {
        self.region_for_anchor(block_addr)
            .map(SemanticRegion::actionable_memory_terms)
            .unwrap_or_default()
    }

    pub fn actionable_regions(&self) -> impl Iterator<Item = &SemanticRegion> {
        self.regions.values().filter(|region| {
            region.supports_guarded_structuring()
                && region
                    .actionable_reachable_target()
                    .is_some_and(|target| !self.target_source_conflict(target, false))
        })
    }

    pub fn target_condition_source(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<SemanticTargetConditionSource<'_>> {
        let representative = self.authoritative_target_region_source(target_addr, proof_only)?;
        let branch_truth = representative.branch_truth?;
        Some(SemanticTargetConditionSource {
            block_addr: representative.region.anchor,
            branch_truth,
            summary: representative.summary,
            necessary_for_target: representative.necessary_for_target,
        })
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.target_source_region(target_addr, false)?
            .actionable_compiled_condition_for_target(target_addr)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.target_source_region(target_addr, true)?
            .exact_compiled_condition_for_target(target_addr)
    }

    pub fn actionable_memory_terms_for_target(
        &self,
        target_addr: u64,
    ) -> Vec<&BackwardMemoryCondition> {
        self.authoritative_memory_region(target_addr)
            .map(|region| region.actionable_memory_terms_for_target(target_addr))
            .unwrap_or_default()
    }

    pub fn authoritative_region_for_target(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<&SemanticRegion> {
        self.target_source_region(target_addr, proof_only)
    }

    pub fn authoritative_memory_region_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&SemanticRegion> {
        self.authoritative_memory_region(target_addr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmArtifactBody {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<InterpreterDispatchSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_summary: Option<VmStepSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub transfer_summary: Option<VmStepSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticArtifactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
    pub residual_reasons: Vec<ResidualReason>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<InterpreterDispatchSummary>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ambiguous_targets: Vec<u64>,
    pub cache_hit: bool,
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use proptest::prelude::*;

    use super::{
        ControlFact, Judged, MemoryFact, NativeArtifactBody, NativeFunctionSummary,
        NativeSummarySpecificity, NativeWorkerSummary, NativeWorkerSummaryKind,
        NativeWorkerTerminator, RegionKey, SemanticRegion, TargetFact,
    };
    use crate::sim::DerivedSummaryDiagnostics;
    use crate::{
        BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
        BackwardMemoryRegion, SemanticEvidence, SliceClass, SymbolicReachabilityStatus,
    };

    fn compiled_summary(tag: u64) -> BackwardConditionSummary {
        BackwardConditionSummary {
            simplified: format!("cond_{tag}"),
            terms: vec![format!("term_{tag}")],
            memory_terms: vec![BackwardMemoryCondition {
                region: BackwardMemoryRegion::Argument { index: 0 },
                offset_lo: tag as i64,
                offset_hi: tag as i64,
                size: 8,
                exact_offset: true,
                evidence: SemanticEvidence::exact(),
                binding: Some(format!("arg0_{tag}")),
                expr: format!("*(arg0 + 0x{tag:x})"),
                value_expr: None,
                exact_value: false,
            }],
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        }
    }

    fn worker_body(regions: impl IntoIterator<Item = SemanticRegion>) -> NativeArtifactBody {
        NativeArtifactBody {
            summary: NativeFunctionSummary {
                slice_class: SliceClass::Worker,
                role_identity: None,
                closure_functions: 0,
                helper_functions: 0,
                derived_summaries: 0,
                derived_diagnostics: DerivedSummaryDiagnostics::default(),
                region_summaries: Vec::new(),
                worker_summaries: Vec::new(),
            },
            regions: regions
                .into_iter()
                .map(|region| {
                    (
                        RegionKey::new(region.anchor, region.frontier.clone()),
                        region,
                    )
                })
                .collect(),
        }
    }

    fn worker_summary(kind: NativeWorkerSummaryKind) -> NativeWorkerSummary {
        NativeWorkerSummary {
            anchor: 0x401000,
            kind,
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
            evidence: SemanticEvidence::exact(),
        }
    }

    #[test]
    fn generic_memory_worker_summary_is_not_primary_renderable() {
        let summary = worker_summary(NativeWorkerSummaryKind::MemoryRead);

        assert_eq!(
            summary.specificity(),
            NativeSummarySpecificity::GenericMemory
        );
        assert!(summary.is_generic_memory_summary());
        assert!(!summary.is_primary_render_summary());
    }

    #[test]
    fn terminated_memory_worker_summary_is_primary_renderable_scan() {
        let mut summary = worker_summary(NativeWorkerSummaryKind::MemoryRead);
        summary.loop_summary = Some(super::NativeWorkerLoopSummary {
            header: 0x401000,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::ZeroByte),
            fold: None,
        });

        assert_eq!(summary.specificity(), NativeSummarySpecificity::StringScan);
        assert!(!summary.is_generic_memory_summary());
        assert!(summary.is_primary_render_summary());
    }

    fn guided_region(anchor: u64, target: u64, branch_truth: bool) -> SemanticRegion {
        let compiled = compiled_summary(anchor ^ target);
        SemanticRegion {
            anchor,
            frontier: BTreeSet::from([target]),
            control: vec![Judged::new(
                ControlFact {
                    target,
                    status: SymbolicReachabilityStatus::Reachable,
                    branch_truth: Some(branch_truth),
                    condition: Some(compiled.simplified.clone()),
                    compiled: Some(compiled.clone()),
                },
                SemanticEvidence::exact(),
            )],
            memory: compiled
                .memory_terms
                .iter()
                .cloned()
                .map(|term| Judged::new(MemoryFact { term }, SemanticEvidence::exact()))
                .collect(),
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![Judged::new(
                TargetFact {
                    target,
                    status: SymbolicReachabilityStatus::Reachable,
                    branch_truth: Some(branch_truth),
                },
                SemanticEvidence::exact(),
            )],
        }
    }

    fn control_only_region(anchor: u64, target: u64, branch_truth: bool) -> SemanticRegion {
        let mut region = guided_region(anchor, target, branch_truth);
        region.memory.clear();
        for fact in &mut region.control {
            if let Some(compiled) = fact.value.compiled.as_mut() {
                compiled.memory_terms.clear();
            }
        }
        region
    }

    #[test]
    fn control_only_compiled_condition_supports_guarded_structuring() {
        let region = control_only_region(0x401000, 0x401040, true);
        assert!(region.supports_guarded_structuring());
        assert!(worker_body([region]).supports_guarded_structuring());
    }

    proptest! {
        #[test]
        fn conflicting_targets_are_reported_deterministically(
            targets in proptest::collection::vec(0x401000u64..0x401100, 1..6),
        ) {
            let regions = targets
                .iter()
                .enumerate()
                .flat_map(|(idx, target)| {
                    [
                        guided_region(0x5000 + (idx as u64) * 2, *target, true),
                        guided_region(0x5001 + (idx as u64) * 2, *target, false),
                    ]
                })
                .collect::<Vec<_>>();
            let reversed = regions.iter().cloned().rev().collect::<Vec<_>>();
            let expected = targets
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();

            let forward = worker_body(regions);
            let backward = worker_body(reversed);

            prop_assert_eq!(
                forward.conflicting_targets(false).into_iter().collect::<Vec<_>>(),
                expected
            );
            prop_assert_eq!(forward.conflicting_targets(false), backward.conflicting_targets(false));
        }
    }

    #[test]
    fn conflicting_target_sources_disable_guidance_and_structuring() {
        let body = worker_body([
            guided_region(0x401000, 0x401100, true),
            guided_region(0x401010, 0x401100, false),
        ]);

        assert!(body.target_source_conflict(0x401100, false));
        assert!(!body.has_target_guidance(0x401100, false));
        assert!(!body.supports_guarded_structuring());
    }
}
