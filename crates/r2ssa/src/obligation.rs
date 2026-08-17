//! Exhaustive source-side semantic obligation inventory.
//!
//! Render certificates answer whether one emitted construct is justified. This
//! module answers the complementary question: which canonical SSA instructions
//! and effects must survive every downstream transformation? The inventory is
//! built once from the prepared source artifact and uses canonical source sites,
//! never rendered names or AST positions, as persistent identities.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::CanonicalStorageId;
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::op::SSAOp;
use crate::semantic::{SourceBoundaryFacts, StructuredDataflowFacts};

pub const SEMANTIC_OBLIGATION_SCHEMA_VERSION: u32 = 6;

/// Stable location of one canonical SSA instruction.
///
/// The ordinal is the semantic order within the source block. It is independent
/// of graph allocation and traversal order. Phi and ordinary-op namespaces are
/// separate so synthesized SSA joins cannot alias lifted operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CanonicalInstructionId {
    pub block_addr: u64,
    pub site: CanonicalInstructionSite,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CanonicalInstructionSite {
    Phi(CanonicalStorageId),
    Op(u64),
    /// One exact native instruction span for which the trusted translator
    /// emitted no canonical P-code and supplied no no-effect authority.
    NativeSpan {
        instruction_addr: u64,
        size: u32,
    },
}

impl std::fmt::Display for CanonicalInstructionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.site {
            CanonicalInstructionSite::Phi(storage) => {
                write!(
                    f,
                    "0x{:x}:phi:{:?}:0x{:x}:{}",
                    self.block_addr, storage.space, storage.offset, storage.size
                )
            }
            CanonicalInstructionSite::Op(ordinal) => {
                write!(f, "0x{:x}:op:{ordinal}", self.block_addr)
            }
            CanonicalInstructionSite::NativeSpan {
                instruction_addr,
                size,
            } => write!(
                f,
                "0x{:x}:native:0x{instruction_addr:x}:{size}",
                self.block_addr
            ),
        }
    }
}

/// Why a source instruction must survive.
///
/// One instruction can own more than one obligation. For example, an atomic
/// compare-and-swap owns both memory-read and memory-write obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticObligationKind {
    ObservableMemoryRead,
    ObservableMemoryWrite,
    Call,
    CallArgument,
    CallResult,
    Return,
    ReturnValue,
    ControlPredicate,
    ControlTransfer,
    Trap,
    Atomicity,
    MemoryOrdering,
    VolatileOrUnknownEffect,
    LoopCarriedState,
    LiveStateTransition,
    LiveValueProducer,
}

impl std::fmt::Display for SemanticObligationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::ObservableMemoryRead => "memory-read",
            Self::ObservableMemoryWrite => "memory-write",
            Self::Call => "call",
            Self::CallArgument => "call-argument",
            Self::CallResult => "call-result",
            Self::Return => "return",
            Self::ReturnValue => "return-value",
            Self::ControlPredicate => "control-predicate",
            Self::ControlTransfer => "control-transfer",
            Self::Trap => "trap",
            Self::Atomicity => "atomicity",
            Self::MemoryOrdering => "memory-ordering",
            Self::VolatileOrUnknownEffect => "volatile-or-unknown",
            Self::LoopCarriedState => "loop-carried-state",
            Self::LiveStateTransition => "live-state-transition",
            Self::LiveValueProducer => "live-value-producer",
        };
        f.write_str(label)
    }
}

/// Stable identity of one source semantic obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SemanticObligationId {
    pub instruction: CanonicalInstructionId,
    pub kind: SemanticObligationKind,
    pub component: SemanticObligationComponent,
}

impl std::fmt::Display for SemanticObligationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{:?}", self.instruction, self.kind, self.component)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticObligationComponent {
    Whole,
    MemoryAccess(u32),
    PredicateOperand,
    Index(u32),
    RegisterSlot {
        index: u32,
        storage: CanonicalStorageId,
    },
    StackOffset(i64),
    LoopTransition {
        carrier: CanonicalStorageId,
        predecessor: u64,
    },
    MemoryOrdering(SemanticMemoryOrdering),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticMemoryOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
    Unknown,
}

impl From<r2il::MemoryOrdering> for SemanticMemoryOrdering {
    fn from(ordering: r2il::MemoryOrdering) -> Self {
        match ordering {
            r2il::MemoryOrdering::Relaxed => Self::Relaxed,
            r2il::MemoryOrdering::Acquire => Self::Acquire,
            r2il::MemoryOrdering::Release => Self::Release,
            r2il::MemoryOrdering::AcqRel => Self::AcqRel,
            r2il::MemoryOrdering::SeqCst => Self::SeqCst,
            r2il::MemoryOrdering::Unknown => Self::Unknown,
        }
    }
}

/// Initial source-side classification assigned exactly once per instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticInstructionState {
    LiveObligation,
    ProvenDead,
    StructuralControlOnly,
    UnsupportedUnknown,
}

/// Exact source owner for one semantic site.
///
/// Graph instructions and genuine zero-op native spans are disjoint by type;
/// callers cannot silently coerce a native span into a fabricated `InstId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticSourceSite {
    GraphInstruction(InstId),
    GenuineNativeSpan(crate::GenuineNativeInstructionSpan),
}

impl SemanticSourceSite {
    pub const fn graph_inst(self) -> Option<InstId> {
        match self {
            Self::GraphInstruction(inst) => Some(inst),
            Self::GenuineNativeSpan(_) => None,
        }
    }

    pub const fn native_span(self) -> Option<crate::GenuineNativeInstructionSpan> {
        match self {
            Self::GraphInstruction(_) => None,
            Self::GenuineNativeSpan(span) => Some(span),
        }
    }
}

impl std::fmt::Display for SemanticInstructionState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::LiveObligation => "live",
            Self::ProvenDead => "proven-dead",
            Self::StructuralControlOnly => "structural-control-only",
            Self::UnsupportedUnknown => "unsupported-unknown",
        };
        f.write_str(label)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticInstructionDisposition {
    pub id: CanonicalInstructionId,
    pub source: SemanticSourceSite,
    pub state: SemanticInstructionState,
    pub obligations: BTreeSet<SemanticObligationId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticObligation {
    pub id: SemanticObligationId,
    pub source: SemanticSourceSite,
    /// Exact canonical values needed to realize this obligation.
    pub inputs: Vec<ValueId>,
}

/// Complete source inventory for one prepared function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObligationInventoryFailureKind {
    MissingBlock,
    MissingOperationSite,
    MissingCanonicalPhiStorage,
    DuplicateCanonicalInstruction,
    DuplicateObligationSeed,
    UnstructuredControlCycle,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationInventoryFailure {
    pub inst: InstId,
    pub block_addr: Option<u64>,
    pub kind: ObligationInventoryFailureKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticObligationInventory {
    schema_version: u32,
    source_instruction_count: usize,
    instructions: BTreeMap<CanonicalInstructionId, SemanticInstructionDisposition>,
    obligations: BTreeMap<SemanticObligationId, SemanticObligation>,
    by_inst: BTreeMap<InstId, CanonicalInstructionId>,
    native_spans: BTreeMap<CanonicalInstructionId, crate::GenuineNativeInstructionSpan>,
    construction_failures: Vec<ObligationInventoryFailure>,
    unstructured_cycle_blocks: BTreeSet<u64>,
}

impl SemanticObligationInventory {
    fn empty(source_instruction_count: usize) -> Self {
        Self {
            schema_version: SEMANTIC_OBLIGATION_SCHEMA_VERSION,
            source_instruction_count,
            instructions: BTreeMap::new(),
            obligations: BTreeMap::new(),
            by_inst: BTreeMap::new(),
            native_spans: BTreeMap::new(),
            construction_failures: Vec::new(),
            unstructured_cycle_blocks: BTreeSet::new(),
        }
    }
}

/// Exact-once reconciliation result for a downstream transformation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ObligationCoverageReport {
    source_complete: bool,
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
}

impl ObligationCoverageReport {
    pub fn is_closed(&self) -> bool {
        self.source_complete
            && self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
    }

    pub const fn source_complete(&self) -> bool {
        self.source_complete
    }

    pub fn missing(&self) -> &[SemanticObligationId] {
        &self.missing
    }

    pub fn duplicate(&self) -> &[SemanticObligationId] {
        &self.duplicate
    }

    pub fn unexpected(&self) -> &[SemanticObligationId] {
        &self.unexpected
    }
}

impl SemanticObligationInventory {
    pub(crate) fn collect(
        graph: &SsaGraph,
        structured: &StructuredDataflowFacts,
        boundaries: &SourceBoundaryFacts,
    ) -> Self {
        let (canonical_ids, mut construction_failures) = collect_canonical_instruction_ids(graph);
        let mut required = BTreeMap::<
            InstId,
            BTreeSet<(SemanticObligationKind, SemanticObligationComponent)>,
        >::new();
        let mut explicit_inputs = BTreeMap::<
            (InstId, SemanticObligationKind, SemanticObligationComponent),
            Vec<ValueId>,
        >::new();
        let mut unsupported = BTreeSet::<InstId>::new();
        let mut duplicate_seeds =
            BTreeSet::<(InstId, SemanticObligationKind, SemanticObligationComponent)>::new();
        for block_addr in &structured.unstructured_cycle_blocks {
            if let Some(block) = graph
                .block_id_for_addr(*block_addr)
                .and_then(|block| graph.block(block))
            {
                for inst in &block.insts {
                    construction_failures.push(ObligationInventoryFailure {
                        inst: *inst,
                        block_addr: Some(*block_addr),
                        kind: ObligationInventoryFailureKind::UnstructuredControlCycle,
                    });
                }
            }
        }

        for inst in &graph.insts {
            match &inst.payload {
                InstPayload::Op(op) => {
                    seed_direct_obligations(
                        inst,
                        op,
                        &mut required,
                        &mut explicit_inputs,
                        &mut duplicate_seeds,
                        &mut unsupported,
                    );
                }
                InstPayload::Phi { .. } if inst.canonical_storage.is_none() => {
                    unsupported.insert(inst.id);
                    seed_instruction(
                        inst.id,
                        SemanticObligationKind::VolatileOrUnknownEffect,
                        SemanticObligationComponent::Whole,
                        &mut required,
                    );
                }
                InstPayload::Phi { .. } => {}
            }
        }

        for access in structured.memory_accesses.values() {
            let kind = if access.is_write {
                SemanticObligationKind::ObservableMemoryWrite
            } else {
                SemanticObligationKind::ObservableMemoryRead
            };
            let mut inputs = vec![access.address];
            if access.is_write
                && let Some(value) = access.value
            {
                inputs.push(value);
            }
            seed_instruction_with_inputs(
                access.id.inst,
                kind,
                SemanticObligationComponent::MemoryAccess(access.id.ordinal),
                inputs,
                &mut required,
                &mut explicit_inputs,
                &mut duplicate_seeds,
            );
            if !access.provenance_complete {
                unsupported.insert(access.id.inst);
                seed_instruction(
                    access.id.inst,
                    SemanticObligationKind::VolatileOrUnknownEffect,
                    SemanticObligationComponent::MemoryAccess(access.id.ordinal),
                    &mut required,
                );
            }
        }

        for boundary in boundaries.returns.values() {
            seed_instruction(
                boundary.at,
                SemanticObligationKind::Return,
                SemanticObligationComponent::Whole,
                &mut required,
            );
            for value in &boundary.values {
                seed_instruction_with_inputs(
                    boundary.at,
                    SemanticObligationKind::ReturnValue,
                    boundary_component(value.slot),
                    vec![value.value],
                    &mut required,
                    &mut explicit_inputs,
                    &mut duplicate_seeds,
                );
                seed_value_definition(
                    graph,
                    value.value,
                    SemanticObligationKind::LiveValueProducer,
                    &mut required,
                );
            }
            for composition in &boundary.register_compositions {
                let values = std::iter::once(composition.base.value)
                    .chain(
                        composition
                            .overlays
                            .iter()
                            .map(|overlay| overlay.definition.value),
                    )
                    .collect::<Vec<_>>();
                seed_instruction_with_inputs(
                    boundary.at,
                    SemanticObligationKind::ReturnValue,
                    boundary_component(composition.slot),
                    values.clone(),
                    &mut required,
                    &mut explicit_inputs,
                    &mut duplicate_seeds,
                );
                for value in values {
                    seed_value_definition(
                        graph,
                        value,
                        SemanticObligationKind::LiveValueProducer,
                        &mut required,
                    );
                }
            }
            if let Some(return_address) = boundary.return_address {
                seed_value_definition(
                    graph,
                    return_address.value,
                    SemanticObligationKind::LiveValueProducer,
                    &mut required,
                );
            }
            if let Some(crate::semantic::SourceReturnStackPointerFact::ReachingValue {
                value,
                ..
            }) = boundary.exit_stack_pointer
            {
                seed_value_definition(
                    graph,
                    value,
                    SemanticObligationKind::LiveValueProducer,
                    &mut required,
                );
            }
            if !boundary.complete {
                unsupported.insert(boundary.at);
                seed_instruction(
                    boundary.at,
                    SemanticObligationKind::VolatileOrUnknownEffect,
                    SemanticObligationComponent::Whole,
                    &mut required,
                );
                taint_incomplete_boundary_inputs(
                    graph,
                    boundary.at,
                    &mut required,
                    &mut unsupported,
                );
            }
        }

        for boundary in boundaries.calls.values() {
            seed_instruction(
                boundary.at,
                SemanticObligationKind::Call,
                SemanticObligationComponent::Whole,
                &mut required,
            );
            for argument in &boundary.arguments {
                let component = match argument.slot {
                    crate::semantic::CallBoundarySlot::Register { index, storage } => {
                        SemanticObligationComponent::RegisterSlot { index, storage }
                    }
                    crate::semantic::CallBoundarySlot::Stack(offset) => {
                        SemanticObligationComponent::StackOffset(offset)
                    }
                };
                // A preserved-entry argument names no value in this function,
                // so it has no producer to keep live. The argument obligation
                // still exists: the call reads that carrier either way.
                let inputs = match argument.value {
                    crate::semantic::SourceCallArgumentValue::Value(value) => vec![value],
                    crate::semantic::SourceCallArgumentValue::PreservedEntry => Vec::new(),
                };
                seed_instruction_with_inputs(
                    boundary.at,
                    SemanticObligationKind::CallArgument,
                    component,
                    inputs,
                    &mut required,
                    &mut explicit_inputs,
                    &mut duplicate_seeds,
                );
                if let crate::semantic::SourceCallArgumentValue::Value(value) = argument.value {
                    seed_value_definition(
                        graph,
                        value,
                        SemanticObligationKind::LiveValueProducer,
                        &mut required,
                    );
                }
            }
            for value in &boundary.results {
                seed_instruction_with_inputs(
                    boundary.at,
                    SemanticObligationKind::CallResult,
                    boundary_component(value.slot),
                    vec![value.value],
                    &mut required,
                    &mut explicit_inputs,
                    &mut duplicate_seeds,
                );
                seed_value_definition(
                    graph,
                    value.value,
                    SemanticObligationKind::LiveValueProducer,
                    &mut required,
                );
            }
            if !boundary.complete {
                unsupported.insert(boundary.at);
                seed_instruction(
                    boundary.at,
                    SemanticObligationKind::VolatileOrUnknownEffect,
                    SemanticObligationComponent::Whole,
                    &mut required,
                );
                taint_incomplete_boundary_inputs(
                    graph,
                    boundary.at,
                    &mut required,
                    &mut unsupported,
                );
            }
        }

        // First close dependencies from observable effects and exact ABI boundaries. A loop
        // carrier is semantically live only when that independent root closure reaches its phi;
        // recognizer-retained facts must never decide source obligation liveness.
        propagate_live_dependencies(graph, &mut required);
        let live_before_loop_annotation = required.keys().copied().collect::<BTreeSet<_>>();
        for fact in structured.loops.values() {
            for carrier in &fact.carriers {
                let carrier_inst = graph.def_inst(carrier.phi);
                if carrier_inst.is_none_or(|inst| !live_before_loop_annotation.contains(&inst)) {
                    continue;
                }
                seed_value_definition(
                    graph,
                    carrier.phi,
                    SemanticObligationKind::LoopCarriedState,
                    &mut required,
                );
                let carrier_storage = carrier_inst
                    .and_then(|inst| graph.inst(inst))
                    .and_then(|inst| inst.canonical_storage);
                for update in &carrier.updates {
                    if let (Some(carrier_inst), Some(carrier)) = (carrier_inst, carrier_storage) {
                        seed_instruction_with_inputs(
                            carrier_inst,
                            SemanticObligationKind::LiveStateTransition,
                            SemanticObligationComponent::LoopTransition {
                                carrier,
                                predecessor: update.predecessor,
                            },
                            vec![update.value],
                            &mut required,
                            &mut explicit_inputs,
                            &mut duplicate_seeds,
                        );
                    } else if let Some(carrier_inst) = carrier_inst {
                        unsupported.insert(carrier_inst);
                        seed_instruction(
                            carrier_inst,
                            SemanticObligationKind::VolatileOrUnknownEffect,
                            SemanticObligationComponent::Whole,
                            &mut required,
                        );
                    }
                }
            }
        }
        propagate_live_dependencies(graph, &mut required);
        for (inst, _, _) in duplicate_seeds {
            let block_addr = graph
                .inst(inst)
                .and_then(|inst| graph.block(inst.block))
                .map(|block| block.addr);
            construction_failures.push(ObligationInventoryFailure {
                inst,
                block_addr,
                kind: ObligationInventoryFailureKind::DuplicateObligationSeed,
            });
        }

        let mut inventory = Self::empty(graph.insts.len());
        inventory.construction_failures = construction_failures;
        inventory.unstructured_cycle_blocks = structured.unstructured_cycle_blocks.clone();
        for inst in &graph.insts {
            let Some(id) = canonical_ids.get(&inst.id).copied() else {
                continue;
            };
            let kinds = required.remove(&inst.id).unwrap_or_default();
            let state = if unsupported.contains(&inst.id) {
                SemanticInstructionState::UnsupportedUnknown
            } else if !kinds.is_empty() {
                SemanticInstructionState::LiveObligation
            } else if instruction_is_structural(&inst.payload) {
                SemanticInstructionState::StructuralControlOnly
            } else {
                SemanticInstructionState::ProvenDead
            };
            let mut obligation_ids = BTreeSet::new();
            for (kind, component) in kinds {
                let obligation_id = SemanticObligationId {
                    instruction: id,
                    kind,
                    component,
                };
                obligation_ids.insert(obligation_id);
                inventory.obligations.insert(
                    obligation_id,
                    SemanticObligation {
                        id: obligation_id,
                        source: SemanticSourceSite::GraphInstruction(inst.id),
                        inputs: explicit_inputs
                            .remove(&(inst.id, kind, component))
                            .unwrap_or_else(|| inst.inputs.clone()),
                    },
                );
            }
            inventory.by_inst.insert(inst.id, id);
            inventory.instructions.insert(
                id,
                SemanticInstructionDisposition {
                    id,
                    source: SemanticSourceSite::GraphInstruction(inst.id),
                    state,
                    obligations: obligation_ids,
                },
            );
        }
        inventory
    }

    /// Bind exact genuine native spans to this inventory. Zero-op spans are
    /// retained as explicit unsupported obligations without synthesizing an
    /// R2IL or SSA instruction. This is private to the genuine-lift boundary.
    pub(crate) fn bind_genuine_native_spans(
        &mut self,
        spans: impl IntoIterator<Item = crate::GenuineNativeInstructionSpan>,
    ) -> bool {
        for span in spans {
            let id = CanonicalInstructionId {
                block_addr: span.block_addr(),
                site: CanonicalInstructionSite::NativeSpan {
                    instruction_addr: span.instruction_addr(),
                    size: span.size(),
                },
            };
            if self.native_spans.insert(id, span).is_some() {
                return false;
            }
            if span.canonical_op_count() != 0 {
                continue;
            }
            let obligation_id = SemanticObligationId {
                instruction: id,
                kind: SemanticObligationKind::VolatileOrUnknownEffect,
                component: SemanticObligationComponent::Whole,
            };
            let mut obligations = BTreeSet::new();
            obligations.insert(obligation_id);
            if self
                .instructions
                .insert(
                    id,
                    SemanticInstructionDisposition {
                        id,
                        source: SemanticSourceSite::GenuineNativeSpan(span),
                        state: SemanticInstructionState::UnsupportedUnknown,
                        obligations,
                    },
                )
                .is_some()
                || self
                    .obligations
                    .insert(
                        obligation_id,
                        SemanticObligation {
                            id: obligation_id,
                            source: SemanticSourceSite::GenuineNativeSpan(span),
                            inputs: Vec::new(),
                        },
                    )
                    .is_some()
            {
                return false;
            }
        }
        true
    }

    pub fn instruction_for_inst(&self, inst: InstId) -> Option<&SemanticInstructionDisposition> {
        self.by_inst
            .get(&inst)
            .and_then(|id| self.instructions.get(id))
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn source_instruction_count(&self) -> usize {
        self.source_instruction_count
    }

    pub fn instructions(
        &self,
    ) -> &BTreeMap<CanonicalInstructionId, SemanticInstructionDisposition> {
        &self.instructions
    }

    /// Exact source-derived native spans bound at the genuine-lift boundary.
    pub fn native_spans(
        &self,
    ) -> &BTreeMap<CanonicalInstructionId, crate::GenuineNativeInstructionSpan> {
        &self.native_spans
    }

    pub fn obligations(&self) -> &BTreeMap<SemanticObligationId, SemanticObligation> {
        &self.obligations
    }

    pub fn construction_failures(&self) -> &[ObligationInventoryFailure] {
        &self.construction_failures
    }

    pub fn unstructured_cycle_blocks(&self) -> &BTreeSet<u64> {
        &self.unstructured_cycle_blocks
    }

    pub fn is_complete(&self) -> bool {
        let zero_op_span_count = self
            .native_spans
            .values()
            .filter(|span| span.canonical_op_count() == 0)
            .count();
        if self.schema_version != SEMANTIC_OBLIGATION_SCHEMA_VERSION
            || !self.construction_failures.is_empty()
            || !self.unstructured_cycle_blocks.is_empty()
            || self.instructions.len() != self.source_instruction_count + zero_op_span_count
            || self.by_inst.len() != self.source_instruction_count
        {
            return false;
        }
        for (id, instruction) in &self.instructions {
            if instruction.id != *id
                || match instruction.source {
                    SemanticSourceSite::GraphInstruction(inst) => {
                        self.by_inst.get(&inst) != Some(id)
                    }
                    SemanticSourceSite::GenuineNativeSpan(source_span) => {
                        self.native_spans.get(id).is_none_or(|span| {
                            span.canonical_op_count() != 0
                                || *span != source_span
                                || id.block_addr != span.block_addr()
                                || !matches!(
                                    id.site,
                                    CanonicalInstructionSite::NativeSpan {
                                        instruction_addr,
                                        size,
                                    } if instruction_addr == span.instruction_addr()
                                        && size == span.size()
                                )
                        })
                    }
                }
                || !instruction.obligations.iter().all(|obligation_id| {
                    obligation_id.instruction == *id
                        && self
                            .obligations
                            .get(obligation_id)
                            .is_some_and(|obligation| {
                                obligation.id == *obligation_id
                                    && obligation.source == instruction.source
                            })
                })
            {
                return false;
            }
            let should_have_obligations = matches!(
                instruction.state,
                SemanticInstructionState::LiveObligation
                    | SemanticInstructionState::UnsupportedUnknown
            );
            if should_have_obligations == instruction.obligations.is_empty() {
                return false;
            }
        }
        for (inst, id) in &self.by_inst {
            if self
                .instructions
                .get(id)
                .and_then(|instruction| instruction.source.graph_inst())
                != Some(*inst)
            {
                return false;
            }
        }
        for (id, obligation) in &self.obligations {
            if obligation.id != *id
                || self
                    .instructions
                    .get(&id.instruction)
                    .is_none_or(|instruction| {
                        instruction.source != obligation.source
                            || !instruction.obligations.contains(id)
                    })
            {
                return false;
            }
        }
        for (id, span) in &self.native_spans {
            if id.block_addr != span.block_addr()
                || !matches!(
                    id.site,
                    CanonicalInstructionSite::NativeSpan {
                        instruction_addr,
                        size,
                    } if instruction_addr == span.instruction_addr() && size == span.size()
                )
                || (span.canonical_op_count() == 0) != self.instructions.contains_key(id)
            {
                return false;
            }
        }
        true
    }

    pub fn obligations_for_inst(&self, inst: InstId) -> impl Iterator<Item = &SemanticObligation> {
        self.instruction_for_inst(inst)
            .into_iter()
            .flat_map(|instruction| instruction.obligations.iter())
            .filter_map(|id| self.obligations.get(id))
    }

    /// Reconcile downstream dispositions against the source inventory.
    ///
    /// Every source obligation must occur exactly once. This is independent of
    /// AST shape and catches both lost and duplicated effects before rendering is
    /// authorized.
    pub fn audit_coverage(
        &self,
        disposed: impl IntoIterator<Item = SemanticObligationId>,
    ) -> ObligationCoverageReport {
        let mut counts = BTreeMap::<SemanticObligationId, usize>::new();
        for id in disposed {
            *counts.entry(id).or_default() += 1;
        }
        let mut report = ObligationCoverageReport {
            source_complete: self.is_complete(),
            missing: Vec::new(),
            duplicate: Vec::new(),
            unexpected: Vec::new(),
        };
        for id in self.obligations.keys() {
            match counts.remove(id).unwrap_or_default() {
                0 => report.missing.push(*id),
                1 => {}
                _ => report.duplicate.push(*id),
            }
        }
        for (id, count) in counts {
            for _ in 0..count {
                report.unexpected.push(id);
            }
        }
        report
    }

    /// Deterministic, human-readable inventory for debug and fixture capture.
    pub fn debug_lines(&self) -> Vec<String> {
        self.instructions
            .values()
            .map(|instruction| {
                let obligations = instruction
                    .obligations
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{} {} [{}]", instruction.id, instruction.state, obligations)
            })
            .collect()
    }
}

fn boundary_component(slot: crate::semantic::CallBoundarySlot) -> SemanticObligationComponent {
    match slot {
        crate::semantic::CallBoundarySlot::Register { index, storage } => {
            SemanticObligationComponent::RegisterSlot { index, storage }
        }
        crate::semantic::CallBoundarySlot::Stack(offset) => {
            SemanticObligationComponent::StackOffset(offset)
        }
    }
}

fn collect_canonical_instruction_ids(
    graph: &SsaGraph,
) -> (
    BTreeMap<InstId, CanonicalInstructionId>,
    Vec<ObligationInventoryFailure>,
) {
    let mut ids = BTreeMap::new();
    let mut owners = BTreeMap::<CanonicalInstructionId, InstId>::new();
    let mut failures = Vec::new();
    for inst in &graph.insts {
        let Some(block_addr) = graph.block(inst.block).map(|block| block.addr) else {
            failures.push(ObligationInventoryFailure {
                inst: inst.id,
                block_addr: None,
                kind: ObligationInventoryFailureKind::MissingBlock,
            });
            continue;
        };
        let site = match inst.payload {
            InstPayload::Phi { .. } => {
                let Some(storage) = inst.canonical_storage else {
                    failures.push(ObligationInventoryFailure {
                        inst: inst.id,
                        block_addr: Some(block_addr),
                        kind: ObligationInventoryFailureKind::MissingCanonicalPhiStorage,
                    });
                    continue;
                };
                CanonicalInstructionSite::Phi(storage)
            }
            InstPayload::Op(_) => {
                let Some((_, op_idx)) = graph.op_site_for_inst(inst.id) else {
                    failures.push(ObligationInventoryFailure {
                        inst: inst.id,
                        block_addr: Some(block_addr),
                        kind: ObligationInventoryFailureKind::MissingOperationSite,
                    });
                    continue;
                };
                CanonicalInstructionSite::Op(op_idx as u64)
            }
        };
        let id = CanonicalInstructionId { block_addr, site };
        if owners.insert(id, inst.id).is_some() {
            failures.push(ObligationInventoryFailure {
                inst: inst.id,
                block_addr: Some(block_addr),
                kind: ObligationInventoryFailureKind::DuplicateCanonicalInstruction,
            });
            continue;
        }
        ids.insert(inst.id, id);
    }
    (ids, failures)
}

type ObligationSeeds =
    BTreeMap<InstId, BTreeSet<(SemanticObligationKind, SemanticObligationComponent)>>;

fn taint_incomplete_boundary_inputs(
    graph: &SsaGraph,
    boundary_inst: InstId,
    required: &mut ObligationSeeds,
    unsupported: &mut BTreeSet<InstId>,
) {
    let Some(boundary) = graph.inst(boundary_inst) else {
        return;
    };
    let mut predecessor_blocks = BTreeSet::new();
    let mut ready = VecDeque::from([boundary.block]);
    while let Some(block_id) = ready.pop_front() {
        if !predecessor_blocks.insert(block_id) {
            continue;
        }
        if let Some(block) = graph.block(block_id) {
            ready.extend(block.predecessors.iter().copied());
        }
    }

    let boundary_reenters = block_can_reenter(graph, boundary.block);

    // Without a complete ABI snapshot, SSA has no name-independent way to
    // identify which reaching register definitions carry implicit arguments or
    // return values. Conservatively keep every value definition that can reach
    // the boundary out of the ProvenDead state.
    for candidate in &graph.insts {
        if candidate.output.is_none()
            || candidate.id == boundary_inst
            || !predecessor_blocks.contains(&candidate.block)
            || (candidate.block == boundary.block
                && candidate.ordinal >= boundary.ordinal
                && !boundary_reenters)
        {
            continue;
        }
        unsupported.insert(candidate.id);
        seed_instruction(
            candidate.id,
            SemanticObligationKind::VolatileOrUnknownEffect,
            SemanticObligationComponent::Whole,
            required,
        );
    }
}

fn block_can_reenter(graph: &SsaGraph, start: crate::graph::BlockId) -> bool {
    let Some(block) = graph.block(start) else {
        return false;
    };
    let mut ready = VecDeque::from_iter(block.successors.iter().copied());
    let mut visited = BTreeSet::new();
    while let Some(block_id) = ready.pop_front() {
        if block_id == start {
            return true;
        }
        if !visited.insert(block_id) {
            continue;
        }
        if let Some(block) = graph.block(block_id) {
            ready.extend(block.successors.iter().copied());
        }
    }
    false
}

fn seed_direct_obligations(
    inst: &crate::graph::GraphInst,
    op: &SSAOp,
    required: &mut ObligationSeeds,
    explicit_inputs: &mut BTreeMap<
        (InstId, SemanticObligationKind, SemanticObligationComponent),
        Vec<ValueId>,
    >,
    duplicate_seeds: &mut BTreeSet<(InstId, SemanticObligationKind, SemanticObligationComponent)>,
    unsupported: &mut BTreeSet<InstId>,
) {
    use SemanticObligationComponent as Component;
    use SemanticObligationKind as Kind;

    match op {
        SSAOp::Load { .. } | SSAOp::Store { .. } => {}
        SSAOp::Fence { ordering } => seed_instruction(
            inst.id,
            Kind::MemoryOrdering,
            Component::MemoryOrdering((*ordering).into()),
            required,
        ),
        SSAOp::LoadLinked { ordering, .. } | SSAOp::LoadGuarded { ordering, .. } => {
            seed_instruction(
                inst.id,
                Kind::MemoryOrdering,
                Component::MemoryOrdering((*ordering).into()),
                required,
            );
            if matches!(op, SSAOp::LoadLinked { .. }) {
                seed_instruction(inst.id, Kind::Atomicity, Component::Whole, required);
            } else if let Some(guard) = inst.inputs.last().copied() {
                seed_instruction_with_inputs(
                    inst.id,
                    Kind::ControlPredicate,
                    Component::PredicateOperand,
                    vec![guard],
                    required,
                    explicit_inputs,
                    duplicate_seeds,
                );
            }
        }
        SSAOp::StoreConditional { ordering, .. } | SSAOp::StoreGuarded { ordering, .. } => {
            seed_instruction(
                inst.id,
                Kind::MemoryOrdering,
                Component::MemoryOrdering((*ordering).into()),
                required,
            );
            if matches!(op, SSAOp::StoreConditional { .. }) {
                seed_instruction(inst.id, Kind::Atomicity, Component::Whole, required);
            } else if let Some(guard) = inst.inputs.last().copied() {
                seed_instruction_with_inputs(
                    inst.id,
                    Kind::ControlPredicate,
                    Component::PredicateOperand,
                    vec![guard],
                    required,
                    explicit_inputs,
                    duplicate_seeds,
                );
            }
        }
        SSAOp::AtomicCAS { ordering, .. } => {
            seed_instruction(inst.id, Kind::Atomicity, Component::Whole, required);
            seed_instruction(
                inst.id,
                Kind::MemoryOrdering,
                Component::MemoryOrdering((*ordering).into()),
                required,
            );
        }
        SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
            seed_instruction(inst.id, Kind::Call, Component::Whole, required);
        }
        SSAOp::Return { .. } => seed_instruction(inst.id, Kind::Return, Component::Whole, required),
        SSAOp::CBranch { .. } => {
            let predicate = inst.inputs.last().copied().into_iter().collect();
            seed_instruction_with_inputs(
                inst.id,
                Kind::ControlPredicate,
                Component::Whole,
                predicate,
                required,
                explicit_inputs,
                duplicate_seeds,
            );
            seed_instruction(inst.id, Kind::ControlTransfer, Component::Whole, required);
        }
        SSAOp::Branch { .. } | SSAOp::BranchInd { .. } => {
            seed_instruction(inst.id, Kind::ControlTransfer, Component::Whole, required);
        }
        SSAOp::IntDiv { .. }
        | SSAOp::IntSDiv { .. }
        | SSAOp::IntRem { .. }
        | SSAOp::IntSRem { .. } => {
            seed_instruction(inst.id, Kind::Trap, Component::Whole, required)
        }
        SSAOp::Breakpoint => seed_instruction(inst.id, Kind::Trap, Component::Whole, required),
        SSAOp::CallOther { .. }
        | SSAOp::Unimplemented
        | SSAOp::CpuId { .. }
        | SSAOp::New { .. } => {
            unsupported.insert(inst.id);
            seed_instruction(
                inst.id,
                Kind::VolatileOrUnknownEffect,
                Component::Whole,
                required,
            );
        }
        SSAOp::Phi { .. }
        | SSAOp::Copy { .. }
        | SSAOp::IntAdd { .. }
        | SSAOp::IntSub { .. }
        | SSAOp::IntMult { .. }
        | SSAOp::IntNegate { .. }
        | SSAOp::IntCarry { .. }
        | SSAOp::IntSCarry { .. }
        | SSAOp::IntSBorrow { .. }
        | SSAOp::IntAnd { .. }
        | SSAOp::IntOr { .. }
        | SSAOp::IntXor { .. }
        | SSAOp::IntNot { .. }
        | SSAOp::IntLeft { .. }
        | SSAOp::IntRight { .. }
        | SSAOp::IntSRight { .. }
        | SSAOp::IntEqual { .. }
        | SSAOp::IntNotEqual { .. }
        | SSAOp::IntLess { .. }
        | SSAOp::IntSLess { .. }
        | SSAOp::IntLessEqual { .. }
        | SSAOp::IntSLessEqual { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::IntSExt { .. }
        | SSAOp::BoolNot { .. }
        | SSAOp::BoolAnd { .. }
        | SSAOp::BoolOr { .. }
        | SSAOp::BoolXor { .. }
        | SSAOp::Piece { .. }
        | SSAOp::Subpiece { .. }
        | SSAOp::PopCount { .. }
        | SSAOp::Lzcount { .. }
        | SSAOp::FloatAdd { .. }
        | SSAOp::FloatSub { .. }
        | SSAOp::FloatMult { .. }
        | SSAOp::FloatDiv { .. }
        | SSAOp::FloatNeg { .. }
        | SSAOp::FloatAbs { .. }
        | SSAOp::FloatSqrt { .. }
        | SSAOp::FloatCeil { .. }
        | SSAOp::FloatFloor { .. }
        | SSAOp::FloatRound { .. }
        | SSAOp::FloatNaN { .. }
        | SSAOp::FloatEqual { .. }
        | SSAOp::FloatNotEqual { .. }
        | SSAOp::FloatLess { .. }
        | SSAOp::FloatLessEqual { .. }
        | SSAOp::Int2Float { .. }
        | SSAOp::Float2Int { .. }
        | SSAOp::FloatFloat { .. }
        | SSAOp::Trunc { .. }
        | SSAOp::CallDefine { .. }
        | SSAOp::Nop
        | SSAOp::PtrAdd { .. }
        | SSAOp::PtrSub { .. }
        | SSAOp::SegmentOp { .. }
        | SSAOp::Cast { .. }
        | SSAOp::Extract { .. }
        | SSAOp::Insert { .. }
        | SSAOp::Select { .. } => {}
    }
    if matches!(
        op,
        SSAOp::Fence {
            ordering: r2il::MemoryOrdering::Unknown
        } | SSAOp::LoadLinked {
            ordering: r2il::MemoryOrdering::Unknown,
            ..
        } | SSAOp::StoreConditional {
            ordering: r2il::MemoryOrdering::Unknown,
            ..
        } | SSAOp::AtomicCAS {
            ordering: r2il::MemoryOrdering::Unknown,
            ..
        } | SSAOp::LoadGuarded {
            ordering: r2il::MemoryOrdering::Unknown,
            ..
        } | SSAOp::StoreGuarded {
            ordering: r2il::MemoryOrdering::Unknown,
            ..
        }
    ) {
        unsupported.insert(inst.id);
    }
}

fn seed_instruction(
    inst: InstId,
    kind: SemanticObligationKind,
    component: SemanticObligationComponent,
    required: &mut ObligationSeeds,
) {
    required.entry(inst).or_default().insert((kind, component));
}

fn seed_instruction_with_inputs(
    inst: InstId,
    kind: SemanticObligationKind,
    component: SemanticObligationComponent,
    inputs: Vec<ValueId>,
    required: &mut ObligationSeeds,
    explicit_inputs: &mut BTreeMap<
        (InstId, SemanticObligationKind, SemanticObligationComponent),
        Vec<ValueId>,
    >,
    duplicate_seeds: &mut BTreeSet<(InstId, SemanticObligationKind, SemanticObligationComponent)>,
) {
    seed_instruction(inst, kind, component, required);
    let identity = (inst, kind, component);
    if let std::collections::btree_map::Entry::Vacant(entry) = explicit_inputs.entry(identity) {
        entry.insert(inputs);
    } else {
        duplicate_seeds.insert(identity);
    }
}

fn seed_value_definition(
    graph: &SsaGraph,
    value: ValueId,
    kind: SemanticObligationKind,
    required: &mut ObligationSeeds,
) {
    if let Some(inst) = graph.def_inst(value) {
        seed_instruction(inst, kind, SemanticObligationComponent::Whole, required);
    }
}

fn propagate_live_dependencies(graph: &SsaGraph, required: &mut ObligationSeeds) {
    let mut ready = required.keys().copied().collect::<VecDeque<_>>();
    let mut visited = BTreeSet::new();
    while let Some(inst_id) = ready.pop_front() {
        if !visited.insert(inst_id) {
            continue;
        }
        let Some(inst) = graph.inst(inst_id) else {
            continue;
        };
        for input in &inst.inputs {
            let Some(definition) = graph.def_inst(*input) else {
                continue;
            };
            let was_live = required.contains_key(&definition);
            seed_instruction(
                definition,
                SemanticObligationKind::LiveValueProducer,
                SemanticObligationComponent::Whole,
                required,
            );
            if !was_live {
                ready.push_back(definition);
            }
        }
    }
}

fn instruction_is_structural(payload: &InstPayload) -> bool {
    matches!(
        payload,
        InstPayload::Op(SSAOp::Nop | SSAOp::CallDefine { .. })
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CallBoundarySlot, CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec,
        SourceCallArgumentSpec, SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface,
        SourceFunctionInterface, SourceFunctionReturn, SsaArtifact,
    };
    use proptest::prelude::*;
    use r2il::{ArchSpec, MemoryOrdering, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn obligation_fixture() -> Vec<R2ILBlock> {
        let mut entry = R2ILBlock::new(0x1000, 4);
        let addr = Varnode::register(0, 8);
        let loaded = Varnode::unique(0x10, 4);
        let dead = Varnode::unique(0x20, 4);
        entry.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: addr.clone(),
        });
        entry.push(R2ILOp::IntAdd {
            dst: dead,
            a: Varnode::constant(1, 4),
            b: Varnode::constant(2, 4),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr,
            val: loaded,
        });
        entry.push(R2ILOp::Return {
            target: Varnode::register(8, 8),
        });
        vec![entry]
    }

    fn loop_carrier_fixture() -> Vec<R2ILBlock> {
        let accumulator = Varnode::register(0, 8);
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::Copy {
            dst: accumulator.clone(),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x2010, 8),
        });

        let mut header = R2ILBlock::new(0x2010, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x2020, 8),
            cond: Varnode::constant(1, 1),
        });

        let mut exit = R2ILBlock::new(0x2014, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut latch = R2ILBlock::new(0x2020, 4);
        latch.push(R2ILOp::IntAdd {
            dst: accumulator.clone(),
            a: accumulator,
            b: Varnode::constant(1, 8),
        });
        latch.push(R2ILOp::Branch {
            target: Varnode::ram(0x2010, 8),
        });

        vec![entry, header, exit, latch]
    }

    fn irreducible_cycle_fixture() -> Vec<R2ILBlock> {
        let mut entry = R2ILBlock::new(0x8000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x8010, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut left = R2ILBlock::new(0x8004, 4);
        left.push(R2ILOp::Branch {
            target: Varnode::ram(0x8020, 8),
        });
        let mut right = R2ILBlock::new(0x8010, 4);
        right.push(R2ILOp::Branch {
            target: Varnode::ram(0x8020, 8),
        });
        let mut split = R2ILBlock::new(0x8020, 4);
        split.push(R2ILOp::CBranch {
            target: Varnode::ram(0x8010, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut back = R2ILBlock::new(0x8024, 4);
        back.push(R2ILOp::Branch {
            target: Varnode::ram(0x8004, 8),
        });
        vec![entry, left, right, split, back]
    }

    fn x86_64_call_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rsi", 16, 8));
        arch.add_register(RegisterDef::new("rip", 24, 8));
        arch.add_register(RegisterDef::new("rdx", 32, 8));
        arch.add_register(RegisterDef::new("rcx", 40, 8));
        arch.add_register(RegisterDef::new("r8", 48, 8));
        arch.add_register(RegisterDef::new("r9", 56, 8));
        arch
    }

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn direct_call_identity(
        block_addr: u64,
        op_index: usize,
        target: &Varnode,
    ) -> SourceCallSiteIdentity {
        SourceCallSiteIdentity::new(
            block_addr,
            op_index,
            CanonicalStorageId::from_varnode(target),
        )
    }

    fn call_interface(
        revision: &[u8],
        identity: SourceCallSiteIdentity,
        complete: bool,
        arguments: impl IntoIterator<Item = SourceCallArgumentSpec>,
        variadic: bool,
        noreturn: bool,
        result: SourceCallResult,
    ) -> SourceCallSiteInterface {
        SourceCallSiteInterface::new(
            revision.to_vec(),
            identity,
            complete,
            "test-call-abi",
            arguments,
            variadic,
            noreturn,
            result,
        )
        .expect("valid callsite interface")
    }

    #[test]
    fn inventory_classifies_every_canonical_instruction_once() {
        let artifact = SsaArtifact::raw(&obligation_fixture(), None).expect("SSA artifact");
        let inventory = &artifact.facts().obligations;
        assert_eq!(inventory.instructions.len(), artifact.graph().insts.len());
        assert_eq!(inventory.by_inst.len(), artifact.graph().insts.len());
        assert!(inventory.instructions.values().all(|instruction| {
            instruction.state != SemanticInstructionState::LiveObligation
                || !instruction.obligations.is_empty()
        }));
        assert!(inventory.is_complete());
    }

    #[test]
    fn obligation_ids_are_stable_across_deterministic_reconstruction() {
        let blocks = obligation_fixture();
        let first = SsaArtifact::raw(&blocks, None).expect("first artifact");
        let second = SsaArtifact::raw(&blocks, None).expect("second artifact");
        assert_eq!(
            first
                .facts()
                .obligations
                .obligations
                .keys()
                .collect::<Vec<_>>(),
            second
                .facts()
                .obligations
                .obligations
                .keys()
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn obligation_ids_do_not_depend_on_input_block_traversal_order() {
        let blocks = loop_carrier_fixture();
        let first = SsaArtifact::raw(&blocks, None).expect("ordered artifact");
        let mut reordered = blocks;
        reordered[1..].reverse();
        let second = SsaArtifact::raw(&reordered, None).expect("reordered artifact");
        assert_eq!(
            first.obligations().obligations.keys().collect::<Vec<_>>(),
            second.obligations().obligations.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn phi_obligation_ids_do_not_depend_on_register_display_names() {
        let blocks = loop_carrier_fixture();
        let mut first_arch = ArchSpec::new("test-a");
        first_arch.add_register(RegisterDef::new("counter_a", 0, 8));
        let mut second_arch = ArchSpec::new("test-b");
        second_arch.add_register(RegisterDef::new("counter_b", 0, 8));

        let first = SsaArtifact::raw(&blocks, Some(&first_arch)).expect("first artifact");
        let second = SsaArtifact::raw(&blocks, Some(&second_arch)).expect("second artifact");
        assert_eq!(
            first.obligations().obligations.keys().collect::<Vec<_>>(),
            second.obligations().obligations.keys().collect::<Vec<_>>()
        );
        assert!(first.obligations().obligations.keys().any(|id| matches!(
            id.instruction.site,
            CanonicalInstructionSite::Phi(CanonicalStorageId {
                space: crate::CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            })
        )));
    }

    #[test]
    fn implicit_call_boundary_fails_closed_without_abi_snapshot() {
        let mut block = R2ILBlock::new(0x3000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x11, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(16, 8),
            src: Varnode::constant(0x22, 8),
        });
        block.push(R2ILOp::Call {
            target: Varnode::ram(0x4000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });

        let artifact =
            SsaArtifact::raw(&[block], Some(&x86_64_call_arch())).expect("call artifact");
        let arguments = artifact
            .obligations()
            .obligations
            .values()
            .filter(|obligation| obligation.id.kind == SemanticObligationKind::CallArgument)
            .collect::<Vec<_>>();
        assert!(arguments.is_empty());
        let call = artifact
            .obligations()
            .instructions
            .get(&CanonicalInstructionId {
                block_addr: 0x3000,
                site: CanonicalInstructionSite::Op(2),
            })
            .expect("call instruction");
        assert_eq!(call.state, SemanticInstructionState::UnsupportedUnknown);
        assert!(call.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::Call
                && id.component == SemanticObligationComponent::Whole
        }));
        assert!(call.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::VolatileOrUnknownEffect
                && id.component == SemanticObligationComponent::Whole
        }));
        for ordinal in 0..2 {
            let setup = artifact
                .obligations()
                .instructions
                .get(&CanonicalInstructionId {
                    block_addr: 0x3000,
                    site: CanonicalInstructionSite::Op(ordinal),
                })
                .expect("implicit argument setup");
            assert_eq!(setup.state, SemanticInstructionState::UnsupportedUnknown);
            assert!(setup.obligations.iter().any(|id| {
                id.kind == SemanticObligationKind::VolatileOrUnknownEffect
                    && id.component == SemanticObligationComponent::Whole
            }));
        }
        assert!(artifact.obligations().is_complete());
    }

    #[test]
    fn explicit_zero_argument_void_call_is_distinct_from_missing_interface() {
        let target = Varnode::ram(0x4000, 8);
        let mut block = R2ILBlock::new(0x3040, 4);
        block.push(R2ILOp::Call {
            target: target.clone(),
        });
        let arch = x86_64_call_arch();

        let missing = SsaArtifact::raw(&[block.clone()], Some(&arch)).expect("missing interface");
        let missing_call = missing
            .facts()
            .boundaries
            .calls
            .get(&crate::semantic::CallSiteId(0))
            .expect("missing call boundary");
        assert!(!missing_call.complete);
        assert_eq!(missing_call.calling_convention, None);
        assert_eq!(missing_call.variadic, None);
        assert_eq!(missing_call.noreturn, None);
        assert_eq!(missing_call.result_kind, None);
        assert!(missing_call.arguments.is_empty());
        assert!(missing_call.results.is_empty());

        let identity = direct_call_identity(0x3040, 0, &target);
        let explicit = SsaArtifact::raw_with_interfaces(
            &[block.clone()],
            Some(&arch),
            None,
            vec![call_interface(
                b"call-revision-1",
                identity,
                true,
                [],
                true,
                true,
                SourceCallResult::Void,
            )],
        )
        .expect("explicit void interface");
        let explicit_call = explicit
            .facts()
            .boundaries
            .calls
            .get(&crate::semantic::CallSiteId(0))
            .expect("explicit call boundary");
        assert!(explicit_call.complete);
        assert_eq!(
            explicit_call.calling_convention.as_deref(),
            Some("test-call-abi")
        );
        assert_eq!(explicit_call.variadic, Some(true));
        assert_eq!(explicit_call.noreturn, Some(true));
        assert_eq!(explicit_call.result_kind, Some(SourceCallResult::Void));
        assert!(explicit_call.arguments.is_empty());
        assert!(explicit_call.results.is_empty());

        let incomplete = SsaArtifact::raw_with_interfaces(
            &[block],
            Some(&arch),
            None,
            vec![call_interface(
                b"call-revision-1",
                identity,
                false,
                [],
                false,
                false,
                SourceCallResult::Void,
            )],
        )
        .expect("explicit incomplete interface");
        let incomplete_call = incomplete
            .facts()
            .boundaries
            .calls
            .get(&crate::semantic::CallSiteId(0))
            .expect("incomplete call boundary");
        assert!(!incomplete_call.complete);
        assert_eq!(incomplete_call.result_kind, Some(SourceCallResult::Void));
        assert!(incomplete_call.arguments.is_empty());
        assert!(incomplete_call.results.is_empty());
    }

    #[test]
    fn explicit_register_argument_and_result_use_exact_declared_carriers() {
        let target = Varnode::ram(0x4100, 8);
        let argument_storage = register_storage(8, 8);
        let result_storage = register_storage(0, 8);
        let mut block = R2ILBlock::new(0x3080, 8);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x2a, 8),
        });
        block.push(R2ILOp::Call {
            target: target.clone(),
        });
        let interface = call_interface(
            b"call-revision-2",
            direct_call_identity(0x3080, 1, &target),
            true,
            [SourceCallArgumentSpec::new(0, argument_storage)],
            false,
            false,
            SourceCallResult::Register {
                storage: result_storage,
            },
        );
        let artifact = SsaArtifact::for_decompile_with_interfaces(
            &[block],
            Some(&x86_64_call_arch()),
            None,
            vec![interface],
        )
        .expect("call artifact");
        let boundary = artifact
            .facts()
            .boundaries
            .calls
            .get(&crate::semantic::CallSiteId(0))
            .expect("call boundary");

        assert!(boundary.complete);
        assert_eq!(boundary.variadic, Some(false));
        assert_eq!(boundary.noreturn, Some(false));
        assert_eq!(
            boundary.result_kind,
            Some(SourceCallResult::Register {
                storage: result_storage,
            })
        );
        assert_eq!(boundary.arguments.len(), 1);
        assert_eq!(
            boundary.arguments[0].slot,
            CallBoundarySlot::Register {
                index: 0,
                storage: argument_storage,
            }
        );
        assert_eq!(
            match boundary.arguments[0].value {
                crate::semantic::SourceCallArgumentValue::Value(value) => {
                    artifact.graph().def_inst(value)
                }
                crate::semantic::SourceCallArgumentValue::PreservedEntry => None,
            },
            artifact.graph().inst_id_for_op_site(0x3080, 0)
        );
        assert_eq!(boundary.results.len(), 1);
        assert_eq!(
            boundary.results[0].slot,
            CallBoundarySlot::Register {
                index: 0,
                storage: result_storage,
            }
        );
        assert!(matches!(
            artifact
                .graph()
                .def_inst(boundary.results[0].value)
                .and_then(|inst| artifact.graph().inst(inst))
                .map(|inst| &inst.payload),
            Some(InstPayload::Op(SSAOp::CallDefine { .. }))
        ));
    }

    #[test]
    fn duplicate_wrong_target_and_missing_carrier_interfaces_fail_closed() {
        let target = Varnode::ram(0x4200, 8);
        let mut block = R2ILBlock::new(0x30c0, 4);
        block.push(R2ILOp::Call {
            target: target.clone(),
        });
        let identity = direct_call_identity(0x30c0, 0, &target);
        let valid = call_interface(
            b"call-revision-3",
            identity,
            true,
            [],
            false,
            false,
            SourceCallResult::Void,
        );
        let duplicate = SsaArtifact::raw_with_interfaces(
            &[block.clone()],
            Some(&x86_64_call_arch()),
            None,
            vec![valid.clone(), valid],
        )
        .expect("duplicate interface artifact");
        assert!(
            !duplicate
                .machine_context()
                .call_site_interfaces_are_coherent()
        );
        assert!(
            !duplicate
                .facts()
                .boundaries
                .calls
                .get(&crate::semantic::CallSiteId(0))
                .expect("duplicate call boundary")
                .complete
        );

        let wrong_target = call_interface(
            b"call-revision-3",
            SourceCallSiteIdentity::new(
                0x30c0,
                0,
                CanonicalStorageId::from_varnode(&Varnode::ram(0x4300, 8)),
            ),
            true,
            [],
            false,
            false,
            SourceCallResult::Void,
        );
        let wrong_target_artifact = SsaArtifact::raw_with_interfaces(
            &[block.clone()],
            Some(&x86_64_call_arch()),
            None,
            vec![wrong_target],
        )
        .expect("wrong target artifact");
        assert!(
            !wrong_target_artifact
                .machine_context()
                .call_site_interfaces_are_coherent()
        );
        assert!(
            !wrong_target_artifact
                .facts()
                .boundaries
                .calls
                .get(&crate::semantic::CallSiteId(0))
                .expect("wrong-target call boundary")
                .complete
        );

        let missing_carrier = call_interface(
            b"call-revision-3",
            identity,
            true,
            [SourceCallArgumentSpec::new(0, register_storage(0x100, 8))],
            false,
            false,
            SourceCallResult::Void,
        );
        let missing_carrier_artifact = SsaArtifact::raw_with_interfaces(
            &[block],
            Some(&x86_64_call_arch()),
            None,
            vec![missing_carrier],
        )
        .expect("missing carrier artifact");
        assert!(
            !missing_carrier_artifact
                .machine_context()
                .call_site_interfaces_are_coherent()
        );
        assert!(
            !missing_carrier_artifact
                .facts()
                .boundaries
                .calls
                .get(&crate::semantic::CallSiteId(0))
                .expect("missing-carrier call boundary")
                .complete
        );
    }

    #[test]
    fn indirect_call_and_revision_mismatch_interfaces_fail_closed() {
        let target = Varnode::register(8, 8);
        let mut indirect_block = R2ILBlock::new(0x3100, 4);
        indirect_block.push(R2ILOp::CallInd {
            target: target.clone(),
        });
        let indirect_interface = call_interface(
            b"call-revision-4",
            direct_call_identity(0x3100, 0, &target),
            true,
            [],
            false,
            false,
            SourceCallResult::Void,
        );
        let indirect = SsaArtifact::raw_with_interfaces(
            &[indirect_block],
            Some(&x86_64_call_arch()),
            None,
            vec![indirect_interface],
        )
        .expect("indirect call artifact");
        let indirect_call = indirect
            .facts()
            .boundaries
            .calls
            .get(&crate::semantic::CallSiteId(0))
            .expect("indirect call boundary");
        assert!(indirect_call.call_site.eq(&crate::semantic::CallSiteId(0)));
        assert_eq!(
            indirect.facts().call_sites.by_id[&crate::semantic::CallSiteId(0)].raw_identity,
            None
        );
        assert!(!indirect_call.complete);

        let direct_target = Varnode::ram(0x4400, 8);
        let mut direct_block = R2ILBlock::new(0x3140, 4);
        direct_block.push(R2ILOp::Call {
            target: direct_target.clone(),
        });
        let function_interface = SourceFunctionInterface::new(
            b"function-revision".to_vec(),
            "test-call-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("function interface");
        let mismatched_call = call_interface(
            b"other-revision",
            direct_call_identity(0x3140, 0, &direct_target),
            true,
            [],
            false,
            false,
            SourceCallResult::Void,
        );
        let mismatched = SsaArtifact::raw_with_interfaces(
            &[direct_block],
            Some(&x86_64_call_arch()),
            Some(function_interface),
            vec![mismatched_call],
        )
        .expect("revision mismatch artifact");
        assert!(
            !mismatched
                .machine_context()
                .call_site_interfaces_are_coherent()
        );
        assert!(
            !mismatched
                .facts()
                .boundaries
                .calls
                .get(&crate::semantic::CallSiteId(0))
                .expect("revision-mismatched call boundary")
                .complete
        );
    }

    #[test]
    fn architecture_profile_without_function_interface_keeps_return_incomplete() {
        let mut block = R2ILBlock::new(0x3100, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(0x42, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });

        let artifact =
            SsaArtifact::raw(&[block], Some(&x86_64_call_arch())).expect("return artifact");
        let producer = artifact
            .obligations()
            .instructions
            .get(&CanonicalInstructionId {
                block_addr: 0x3100,
                site: CanonicalInstructionSite::Op(0),
            })
            .expect("potential return-value producer");
        assert_eq!(producer.state, SemanticInstructionState::UnsupportedUnknown);
        assert!(producer.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::VolatileOrUnknownEffect
                && id.component == SemanticObligationComponent::Whole
        }));
        let returned = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(!returned.complete);
        assert!(returned.values.is_empty());
        assert!(artifact.obligations().is_complete());
    }

    #[test]
    fn synthetic_interface_without_typed_machine_roles_is_refused() {
        let mut block = R2ILBlock::new(0x3140, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(8, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        let parameter_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let return_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let interface = SourceFunctionInterface::new(
            b"fixture-revision-1".to_vec(),
            "sysv-amd64",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            SourceFunctionReturn::Register {
                storage: return_storage,
            },
            [],
        )
        .expect("explicit interface");
        let artifact =
            SsaArtifact::raw_with_interface(&[block], Some(&x86_64_call_arch()), interface)
                .expect("return artifact");

        let returned = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(artifact.facts().boundaries.parameters.is_empty());
        assert!(!returned.complete);
        assert!(returned.values.is_empty());
        let producer = artifact
            .obligations()
            .instructions()
            .get(&CanonicalInstructionId {
                block_addr: 0x3140,
                site: CanonicalInstructionSite::Op(1),
            })
            .expect("untrusted return producer");
        assert_eq!(producer.state, SemanticInstructionState::UnsupportedUnknown);
        assert!(producer.obligations.iter().any(|obligation| {
            obligation.kind == SemanticObligationKind::VolatileOrUnknownEffect
        }));
    }

    #[test]
    fn incomplete_boundary_keeps_later_loop_definitions_unknown() {
        let mut block = R2ILBlock::new(0x3180, 4);
        block.push(R2ILOp::Call {
            target: Varnode::ram(0x4000, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x42, 8),
        });
        block.push(R2ILOp::Branch {
            target: Varnode::ram(0x3180, 8),
        });

        let artifact =
            SsaArtifact::raw(&[block], Some(&x86_64_call_arch())).expect("loop artifact");
        let next_iteration_argument = artifact
            .obligations()
            .instructions
            .get(&CanonicalInstructionId {
                block_addr: 0x3180,
                site: CanonicalInstructionSite::Op(1),
            })
            .expect("next-iteration argument producer");
        assert_eq!(
            next_iteration_argument.state,
            SemanticInstructionState::UnsupportedUnknown
        );
        assert!(next_iteration_argument.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::VolatileOrUnknownEffect
                && id.component == SemanticObligationComponent::Whole
        }));
        assert!(artifact.obligations().is_complete());
    }

    #[test]
    fn duplicate_explicit_obligation_seed_fails_inventory_construction() {
        let mut block = R2ILBlock::new(0x3200, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x11, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(16, 8),
            src: Varnode::constant(0x22, 8),
        });
        block.push(R2ILOp::Call {
            target: Varnode::ram(0x4000, 8),
        });
        let artifact =
            SsaArtifact::raw(&[block], Some(&x86_64_call_arch())).expect("call artifact");
        let graph = artifact.graph();
        let first = graph
            .inst(graph.inst_id_for_op_site(0x3200, 0).expect("first setup"))
            .and_then(|inst| inst.output)
            .expect("first argument value");
        let second = graph
            .inst(graph.inst_id_for_op_site(0x3200, 1).expect("second setup"))
            .and_then(|inst| inst.output)
            .expect("second argument value");
        let call_inst = graph
            .inst_id_for_op_site(0x3200, 2)
            .expect("call instruction");
        let call_site = crate::semantic::CallSiteId(0);
        let slot = crate::semantic::CallBoundarySlot::Register {
            index: 0,
            storage: CanonicalStorageId {
                space: crate::CanonicalStorageSpace::Register,
                offset: 8,
                size: 8,
            },
        };
        let mut boundaries = SourceBoundaryFacts::default();
        boundaries.calls.insert(
            call_site,
            crate::semantic::SourceCallBoundaryFact {
                call_site,
                at: call_inst,
                calling_convention: Some("test-abi".to_string()),
                variadic: Some(false),
                noreturn: Some(false),
                result_kind: Some(crate::SourceCallResult::Void),
                arguments: vec![
                    crate::semantic::SourceCallArgumentFact {
                        slot,
                        value: crate::semantic::SourceCallArgumentValue::Value(first),
                    },
                    crate::semantic::SourceCallArgumentFact {
                        slot,
                        value: crate::semantic::SourceCallArgumentValue::Value(second),
                    },
                ],
                results: Vec::new(),
                complete: true,
            },
        );
        let inventory =
            SemanticObligationInventory::collect(graph, artifact.structured(), &boundaries);

        assert!(!inventory.is_complete());
        assert!(inventory.construction_failures().iter().any(|failure| {
            failure.inst == call_inst
                && failure.kind == ObligationInventoryFailureKind::DuplicateObligationSeed
        }));
        let arguments = inventory
            .obligations_for_inst(call_inst)
            .filter(|obligation| obligation.id.kind == SemanticObligationKind::CallArgument)
            .collect::<Vec<_>>();
        assert_eq!(arguments.len(), 1);
        assert_eq!(arguments[0].inputs, vec![first]);
    }

    #[test]
    fn atomic_cas_has_read_write_and_ordering_obligations() {
        let mut block = R2ILBlock::new(0x5000, 4);
        block.push(R2ILOp::AtomicCAS {
            dst: Varnode::unique(0x10, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            expected: Varnode::constant(1, 8),
            replacement: Varnode::constant(2, 8),
            ordering: MemoryOrdering::SeqCst,
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(8, 8),
        });

        let artifact = SsaArtifact::raw(&[block], None).expect("atomic artifact");
        let atomic = artifact
            .obligations()
            .instructions
            .get(&CanonicalInstructionId {
                block_addr: 0x5000,
                site: CanonicalInstructionSite::Op(0),
            })
            .expect("atomic instruction");
        assert_eq!(
            atomic
                .obligations
                .iter()
                .filter(|id| id.kind == SemanticObligationKind::ObservableMemoryRead)
                .count(),
            1
        );
        assert_eq!(
            atomic
                .obligations
                .iter()
                .filter(|id| id.kind == SemanticObligationKind::ObservableMemoryWrite)
                .count(),
            1
        );
        assert!(atomic.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::ObservableMemoryRead
                && id.component == SemanticObligationComponent::MemoryAccess(0)
        }));
        assert!(atomic.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::ObservableMemoryWrite
                && id.component == SemanticObligationComponent::MemoryAccess(1)
        }));
        assert!(atomic.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::Atomicity
                && id.component == SemanticObligationComponent::Whole
        }));
        assert!(atomic.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::MemoryOrdering
                && id.component
                    == SemanticObligationComponent::MemoryOrdering(SemanticMemoryOrdering::SeqCst)
        }));
    }

    #[test]
    fn unknown_atomic_ordering_is_unsupported() {
        let mut block = R2ILBlock::new(0x6000, 4);
        block.push(R2ILOp::Fence {
            ordering: MemoryOrdering::Unknown,
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(8, 8),
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("fence artifact");
        let fence = artifact
            .obligations()
            .instructions
            .get(&CanonicalInstructionId {
                block_addr: 0x6000,
                site: CanonicalInstructionSite::Op(0),
            })
            .expect("fence instruction");
        assert_eq!(fence.state, SemanticInstructionState::UnsupportedUnknown);
        assert!(fence.obligations.iter().any(|id| {
            id.kind == SemanticObligationKind::MemoryOrdering
                && id.component
                    == SemanticObligationComponent::MemoryOrdering(SemanticMemoryOrdering::Unknown)
        }));
    }

    #[test]
    fn storage_less_phi_refuses_complete_inventory() {
        let artifact = SsaArtifact::raw(&loop_carrier_fixture(), None).expect("loop artifact");
        let mut graph = artifact.graph().clone();
        let phi = graph
            .insts
            .iter_mut()
            .find(|inst| matches!(inst.payload, InstPayload::Phi { .. }))
            .expect("loop phi");
        phi.canonical_storage = None;
        let inventory = SemanticObligationInventory::collect(
            &graph,
            artifact.structured(),
            &artifact.facts().boundaries,
        );
        assert!(!inventory.is_complete());
        assert!(inventory.construction_failures.iter().any(|failure| {
            failure.kind == ObligationInventoryFailureKind::MissingCanonicalPhiStorage
        }));
    }

    #[test]
    fn irreducible_cycle_refuses_complete_inventory() {
        let artifact =
            SsaArtifact::raw(&irreducible_cycle_fixture(), None).expect("irreducible artifact");
        assert!(!artifact.structured().unstructured_cycle_blocks.is_empty());
        assert!(!artifact.obligations().is_complete());
        assert!(
            artifact
                .obligations()
                .construction_failures
                .iter()
                .any(|failure| {
                    failure.kind == ObligationInventoryFailureKind::UnstructuredControlCycle
                })
        );
    }

    #[test]
    fn empty_irreducible_cycle_still_refuses_complete_inventory() {
        let artifact =
            SsaArtifact::raw(&irreducible_cycle_fixture(), None).expect("irreducible artifact");
        let mut graph = artifact.graph().clone();
        graph.insts.clear();
        graph.values.clear();
        graph.def_of.clear();
        graph.uses_of.clear();
        graph.op_inst_by_site.clear();
        graph.op_site_by_inst.clear();
        for block in &mut graph.blocks {
            block.insts.clear();
        }
        let inventory = SemanticObligationInventory::collect(
            &graph,
            artifact.structured(),
            &artifact.facts().boundaries,
        );
        assert_eq!(inventory.source_instruction_count(), 0);
        assert!(!inventory.unstructured_cycle_blocks().is_empty());
        assert!(!inventory.is_complete());
        let report = inventory.audit_coverage(inventory.obligations.keys().copied());
        assert!(!report.source_complete());
        assert!(!report.is_closed());
    }

    #[test]
    fn malformed_bidirectional_inventory_mapping_is_incomplete() {
        let artifact = SsaArtifact::raw(&obligation_fixture(), None).expect("SSA artifact");
        let mut inventory = artifact.obligations().clone();
        let obligation = inventory
            .obligations
            .values_mut()
            .next()
            .expect("source obligation");
        obligation.source = SemanticSourceSite::GraphInstruction(InstId(u32::MAX));
        assert!(!inventory.is_complete());
    }

    #[test]
    fn loop_transition_is_carrier_edge_owned_even_without_update_definition() {
        let artifact = SsaArtifact::raw(&loop_carrier_fixture(), None).expect("loop artifact");
        let mut structured = artifact.structured().clone();
        let undef = artifact
            .graph()
            .values
            .iter()
            .find(|value| artifact.graph().def_inst(value.id).is_none())
            .map(|value| value.id)
            .expect("undefined or constant value");
        let carrier = structured
            .loops
            .values_mut()
            .flat_map(|loop_fact| loop_fact.carriers.iter_mut())
            .next()
            .expect("loop carrier");
        carrier.updates[0].value = undef;
        let predecessor = carrier.updates[0].predecessor;
        let phi_inst = artifact
            .graph()
            .def_inst(carrier.phi)
            .expect("phi definition");
        let storage = artifact
            .graph()
            .inst(phi_inst)
            .and_then(|inst| inst.canonical_storage)
            .expect("phi storage");

        let inventory = SemanticObligationInventory::collect(
            artifact.graph(),
            &structured,
            &artifact.facts().boundaries,
        );
        let transition = inventory
            .obligations_for_inst(phi_inst)
            .find(|obligation| {
                obligation.id.kind == SemanticObligationKind::LiveStateTransition
                    && obligation.id.component
                        == SemanticObligationComponent::LoopTransition {
                            carrier: storage,
                            predecessor,
                        }
            })
            .expect("carrier-edge transition");
        assert_eq!(transition.inputs, vec![undef]);
    }

    #[test]
    fn shared_loop_update_values_keep_distinct_predecessor_obligations() {
        let artifact = SsaArtifact::raw(&loop_carrier_fixture(), None).expect("loop artifact");
        let mut structured = artifact.structured().clone();
        let carrier = structured
            .loops
            .values_mut()
            .flat_map(|loop_fact| loop_fact.carriers.iter_mut())
            .next()
            .expect("loop carrier");
        let mut second = carrier.updates[0].clone();
        second.predecessor = 0x2030;
        carrier.updates.push(second);
        let phi_inst = artifact
            .graph()
            .def_inst(carrier.phi)
            .expect("phi definition");
        let inventory = SemanticObligationInventory::collect(
            artifact.graph(),
            &structured,
            &artifact.facts().boundaries,
        );
        let transitions = inventory
            .obligations_for_inst(phi_inst)
            .filter(|obligation| obligation.id.kind == SemanticObligationKind::LiveStateTransition)
            .collect::<Vec<_>>();
        assert_eq!(transitions.len(), 2);
        assert_ne!(transitions[0].id, transitions[1].id);
        assert_eq!(transitions[0].inputs, transitions[1].inputs);
    }

    #[test]
    fn coverage_reports_lost_effect_and_duplicated_write() {
        let artifact = SsaArtifact::raw(&obligation_fixture(), None).expect("SSA artifact");
        let inventory = &artifact.facts().obligations;
        let all = inventory.obligations.keys().copied().collect::<Vec<_>>();
        assert!(inventory.audit_coverage(all.clone()).is_closed());

        let write = all
            .iter()
            .copied()
            .find(|id| id.kind == SemanticObligationKind::ObservableMemoryWrite)
            .expect("write obligation");
        let without_write = all
            .iter()
            .copied()
            .filter(|id| *id != write)
            .collect::<Vec<_>>();
        let missing = inventory.audit_coverage(without_write);
        assert_eq!(missing.missing, vec![write]);

        let mut duplicated_write = all;
        duplicated_write.push(write);
        let duplicate = inventory.audit_coverage(duplicated_write);
        assert_eq!(duplicate.duplicate, vec![write]);
    }

    #[test]
    fn coverage_reports_missing_loop_latch_state_transition() {
        let artifact = SsaArtifact::raw(&loop_carrier_fixture(), None).expect("loop SSA artifact");
        let inventory = artifact.obligations();
        let latch = inventory
            .obligations
            .keys()
            .copied()
            .find(|id| id.kind == SemanticObligationKind::LiveStateTransition)
            .expect("loop latch state-transition obligation");
        let without_latch = inventory
            .obligations
            .keys()
            .copied()
            .filter(|id| *id != latch)
            .collect::<Vec<_>>();
        let report = inventory.audit_coverage(without_latch);
        assert_eq!(report.missing, vec![latch]);
        assert!(!report.is_closed());
    }

    proptest! {
        #[test]
        fn obligation_ids_are_stable_for_all_non_entry_block_orders(
            priorities in any::<[u8; 3]>()
        ) {
            let blocks = loop_carrier_fixture();
            let first = SsaArtifact::raw(&blocks, None).expect("ordered artifact");
            let mut tail = blocks[1..].to_vec();
            tail.sort_by_key(|block| {
                let original = blocks[1..]
                    .iter()
                    .position(|candidate| candidate.addr == block.addr)
                    .expect("fixture block");
                (priorities[original], block.addr)
            });
            let mut reordered = vec![blocks[0].clone()];
            reordered.extend(tail);
            let second = SsaArtifact::raw(&reordered, None).expect("reordered artifact");
            prop_assert_eq!(
                first.obligations().obligations.keys().collect::<Vec<_>>(),
                second.obligations().obligations.keys().collect::<Vec<_>>()
            );
        }
    }
}
