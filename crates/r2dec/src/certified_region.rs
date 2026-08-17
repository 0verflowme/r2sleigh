//! Proof-bound control-region foundations.
//!
//! The first supported shape is one canonical block. Every source instruction
//! and obligation is carried by stable ID. Value expressions bind to the
//! partial semantic-C layer. Admitted expressions, plain memory, and terminal
//! controls receive exact mappings; unsupported effects and control become
//! explicit residual mappings rather than disappearing.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
    CertifiedArtifactOrigin, CertifiedCallArgumentOrigin, CertifiedConditionalControl,
    CertifiedControlTruthiness, CertifiedDirectCall, CertifiedDirectControl,
    CertifiedLedgerClosure, CertifiedMachineFunction, CertifiedMachineProjection,
    CertifiedMemoryStatement, CertifiedNormalizedStackRange, CertifiedReturnControl,
    CertifiedReturnRegisterDefinition, CertifiedSourceTopology, CertifiedSwitchControl,
    CertifiedTypedRegionKind, EffectDisposition, ObligationLedger, TypedRegionMapping,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalInstructionSite, CanonicalStorageId, SemanticInstructionState,
    SemanticObligationComponent, SemanticObligationId, SemanticObligationInventory,
    SemanticObligationKind, StructuredAccessId,
};
use serde::Serialize;

use crate::semantic_c::{
    SEMANTIC_C_SCHEMA_VERSION, SemanticCCallArgumentValue, SemanticCDirectCall, SemanticCError,
    SemanticCExprId, SemanticCExpressionLayer, SemanticCFrameMechanicsAuthority,
    SemanticCFrameMechanicsOwner, SemanticCIdentityScope, SemanticCReturn,
    SemanticCReturnMechanicsOwner, SemanticCReturnRegisterDefinition, SemanticCScope,
    semantic_call_from_control, semantic_return_from_control,
};
use crate::{CertifiedPrivateFrameConditionalJoinRewrite, CertifiedPrivateFrameJoinValueOrigin};

pub const CERTIFIED_REGION_SCHEMA_VERSION: u32 = 15;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SingleBlockAccountingScope {
    SourceAccountingWithCertifiedSemanticEntitiesAndOpenBlockExit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum RegionResidualReason {
    MemoryEffectRequiresCertifiedStatement,
    CallBoundaryRequiresCertifiedCall,
    ReturnRequiresCertifiedControl,
    ControlRequiresCertifiedRegion,
    TrapOrOrderingRequiresCertifiedEffect,
    LoopStateRequiresCertifiedStructuring,
    UnsupportedSourceSemantics,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum RegionObligationDisposition {
    AbsorbedIntoExpression { producer: CanonicalInstructionId },
    AbsorbedIntoStatement { producer: CanonicalInstructionId },
    AbsorbedIntoFrameMechanics { producer: CanonicalInstructionId },
    AbsorbedIntoCall { producer: CanonicalInstructionId },
    AbsorbedIntoControl { producer: CanonicalInstructionId },
    AbsorbedIntoReturn { producer: CanonicalInstructionId },
    Residualized { reason: RegionResidualReason },
}

/// Exact semantic output node that owns one source obligation. These handles
/// are created only while the corresponding typed node is present in the
/// artifact-local semantic layer; producer counts and AST positions are never
/// accepted as substitutes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum RegionTypedOwner {
    Expression {
        producer: CanonicalInstructionId,
        root: SemanticCExprId,
    },
    Statement {
        producer: CanonicalInstructionId,
        component: SemanticObligationComponent,
    },
    Call {
        producer: CanonicalInstructionId,
        component: SemanticObligationComponent,
    },
    Control {
        producer: CanonicalInstructionId,
        component: SemanticObligationComponent,
    },
    Return {
        producer: CanonicalInstructionId,
        component: SemanticObligationComponent,
    },
    ReturnMechanics {
        source_producer: CanonicalInstructionId,
        return_producers: Box<[CanonicalInstructionId]>,
    },
    FrameMechanics {
        source_producer: CanonicalInstructionId,
        frame_pointer_storage: CanonicalStorageId,
        saved_range: CertifiedNormalizedStackRange,
        return_producers: Box<[CanonicalInstructionId]>,
    },
    PrivateFrameConditionalJoin {
        producer: CanonicalInstructionId,
        role: PrivateFrameConditionalJoinOwnerRole,
    },
}

/// Exact composite role by which the private-frame rewrite plan owns an
/// already-ledgered source effect. These roles never replace or invent the
/// underlying ledger disposition.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum PrivateFrameConditionalJoinOwnerRole {
    AuxiliaryStoreMemory {
        access: StructuredAccessId,
    },
    AuxiliaryLoadMemory {
        access: StructuredAccessId,
    },
    AuxiliaryLoadValue {
        access: StructuredAccessId,
        root: SemanticCExprId,
    },
    JoinedTrueStoreMemory {
        access: StructuredAccessId,
    },
    JoinedFalseStoreMemory {
        access: StructuredAccessId,
    },
    JoinedLoadMemory {
        access: StructuredAccessId,
    },
    JoinedLoadValue {
        access: StructuredAccessId,
        root: SemanticCExprId,
    },
    PrivateStackMechanics,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct PrivateFrameConditionalJoinAccountingAuthority {
    header: u64,
    stack_pointer_storage: CanonicalStorageId,
    reservation_range: CertifiedNormalizedStackRange,
    roles: Box<[(SemanticObligationId, PrivateFrameConditionalJoinOwnerRole)]>,
}

fn private_role_manifest_is_canonical(
    roles: &[(SemanticObligationId, PrivateFrameConditionalJoinOwnerRole)],
) -> bool {
    roles.windows(2).all(|pair| pair[0].0 < pair[1].0)
        && roles.iter().all(|(obligation, role)| match role {
            PrivateFrameConditionalJoinOwnerRole::AuxiliaryStoreMemory { .. }
            | PrivateFrameConditionalJoinOwnerRole::JoinedTrueStoreMemory { .. }
            | PrivateFrameConditionalJoinOwnerRole::JoinedFalseStoreMemory { .. } => {
                obligation.kind == SemanticObligationKind::ObservableMemoryWrite
            }
            PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadMemory { .. }
            | PrivateFrameConditionalJoinOwnerRole::JoinedLoadMemory { .. } => {
                obligation.kind == SemanticObligationKind::ObservableMemoryRead
            }
            PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadValue { .. }
            | PrivateFrameConditionalJoinOwnerRole::JoinedLoadValue { .. }
            | PrivateFrameConditionalJoinOwnerRole::PrivateStackMechanics => {
                obligation.kind == SemanticObligationKind::LiveValueProducer
            }
        })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RegionObligationMapping {
    obligation: SemanticObligationId,
    disposition: RegionObligationDisposition,
    owner: Option<RegionTypedOwner>,
}

/// Opaque final typed-output authority owned by the semantic-C layer.
///
/// The certification token proves only ledger closure. This seal additionally
/// retains the exact artifact-local owners, including expression arena roots,
/// and cannot be constructed until every contributing accounting audits cleanly.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedTypedOutputSeal {
    schema_version: u32,
    ledger_closure: CertifiedLedgerClosure,
    mappings: Box<[RegionObligationMapping]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedOutputSealError {
    EmptyAccountingSet,
    InexactAccounting,
    ResidualMapping(SemanticObligationId),
    MissingTypedOwner(SemanticObligationId),
    IncompleteManifest,
    ArtifactOriginMismatch,
    LedgerClosureMismatch,
}

impl std::fmt::Display for TypedOutputSealError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "typed output sealing failed: {self:?}")
    }
}

impl std::error::Error for TypedOutputSealError {}

impl RegionObligationMapping {
    pub const fn obligation(&self) -> SemanticObligationId {
        self.obligation
    }

    pub const fn disposition(&self) -> &RegionObligationDisposition {
        &self.disposition
    }

    pub const fn owner(&self) -> Option<&RegionTypedOwner> {
        self.owner.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedRegionInstruction {
    source: CanonicalInstructionId,
    state: SemanticInstructionState,
    expression_producer: Option<CanonicalInstructionId>,
    statement_producer: Option<CanonicalInstructionId>,
    call_producer: Option<CanonicalInstructionId>,
    control_producer: Option<CanonicalInstructionId>,
    return_producer: Option<CanonicalInstructionId>,
}

impl CertifiedRegionInstruction {
    pub const fn source(&self) -> CanonicalInstructionId {
        self.source
    }

    pub const fn state(&self) -> SemanticInstructionState {
        self.state
    }

    pub const fn expression_producer(&self) -> Option<CanonicalInstructionId> {
        self.expression_producer
    }

    pub const fn statement_producer(&self) -> Option<CanonicalInstructionId> {
        self.statement_producer
    }

    pub const fn call_producer(&self) -> Option<CanonicalInstructionId> {
        self.call_producer
    }

    pub const fn control_producer(&self) -> Option<CanonicalInstructionId> {
        self.control_producer
    }

    pub const fn return_producer(&self) -> Option<CanonicalInstructionId> {
        self.return_producer
    }
}

/// Exact source accounting for one canonical basic block.
///
/// This envelope accounts for admitted terminal-control evidence but is not
/// itself a structured control region. Residual and absorbed mappings describe
/// local source obligations only and grant no execution or rendering
/// permission. Dispositions use stable producer IDs only; the artifact-local
/// expression root is resolved inside the owned layer and is never serialized
/// as proof evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSingleBlockAccounting {
    schema_version: u32,
    scope: SingleBlockAccountingScope,
    identity_scope: SemanticCIdentityScope,
    origin: CertifiedArtifactOrigin,
    block_addr: u64,
    source: SemanticObligationInventory,
    topology: CertifiedSourceTopology,
    ledger: ObligationLedger,
    expression_layer: SemanticCExpressionLayer,
    memory_statements: Box<[CertifiedMemoryStatement]>,
    direct_calls: Box<[CertifiedDirectCall]>,
    semantic_calls: Box<[SemanticCDirectCall]>,
    direct_controls: Box<[CertifiedDirectControl]>,
    conditional_controls: Box<[CertifiedConditionalControl]>,
    switch_controls: Box<[CertifiedSwitchControl]>,
    return_controls: Box<[CertifiedReturnControl]>,
    semantic_returns: Box<[SemanticCReturn]>,
    instructions: Box<[CertifiedRegionInstruction]>,
    mappings: Box<[RegionObligationMapping]>,
    private_frame_conditional_join: Option<PrivateFrameConditionalJoinAccountingAuthority>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionBuildError {
    SemanticC(SemanticCError),
    EmptySource,
    MultipleBlocks(BTreeSet<u64>),
    MissingBlock(u64),
    MissingSourceInstruction(CanonicalInstructionId),
    MissingExpression(CanonicalInstructionId),
    ExpressionObligationMismatch(SemanticObligationId),
    StatementObligationMismatch(SemanticObligationId),
    CallObligationMismatch(SemanticObligationId),
    ControlObligationMismatch(SemanticObligationId),
    ReturnObligationMismatch(SemanticObligationId),
    AmbiguousControl(CanonicalInstructionId),
    ArtifactOriginMismatch,
    PrivateFrameConditionalJoinMismatch,
    UnsupportedPrivateFrameConditionalJoinObligation(SemanticObligationId),
}

impl std::fmt::Display for RegionBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified region construction failed: {self:?}")
    }
}

impl std::error::Error for RegionBuildError {}

impl From<SemanticCError> for RegionBuildError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn only_source_block(topology: &CertifiedSourceTopology) -> Result<u64, RegionBuildError> {
    let [block] = topology.blocks() else {
        return if topology.blocks().is_empty() {
            Err(RegionBuildError::EmptySource)
        } else {
            Err(RegionBuildError::MultipleBlocks(
                topology.blocks().iter().map(|block| block.addr()).collect(),
            ))
        };
    };
    Ok(block.addr())
}

fn require_source_block(
    topology: &CertifiedSourceTopology,
    block_addr: u64,
) -> Result<&r2cert::CertifiedSourceBlock, RegionBuildError> {
    topology
        .block(block_addr)
        .ok_or(RegionBuildError::MissingBlock(block_addr))
}

fn block_source_instruction_order(
    source: &SemanticObligationInventory,
    block: &r2cert::CertifiedSourceBlock,
) -> Vec<CanonicalInstructionId> {
    let mut ordered = block.instructions().to_vec();
    let mut native = source
        .native_spans()
        .iter()
        .filter(|(id, span)| id.block_addr == block.addr() && span.canonical_op_count() == 0)
        .map(|(id, span)| (*id, *span))
        .collect::<Vec<_>>();
    native.sort_unstable_by_key(|(id, span)| {
        (
            span.first_canonical_op(),
            span.instruction_addr(),
            span.size(),
            *id,
        )
    });
    for (id, span) in native {
        let insertion = ordered
            .iter()
            .position(|candidate| {
                matches!(candidate.site, CanonicalInstructionSite::Op(ordinal) if ordinal >= span.first_canonical_op())
            })
            .unwrap_or(ordered.len());
        ordered.insert(insertion, id);
    }
    ordered
}

fn ledger_expression_inputs(
    ledger: &ObligationLedger,
    source: &SemanticObligationInventory,
    producer: CanonicalInstructionId,
) -> Option<BTreeSet<CanonicalInstructionId>> {
    let instruction = source.instructions().get(&producer)?;
    let live = instruction
        .obligations
        .iter()
        .copied()
        .filter(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
        .collect::<Vec<_>>();
    let [obligation] = live.as_slice() else {
        return None;
    };
    let [effect] = ledger.effects(*obligation) else {
        return None;
    };
    let expression = effect.expression_evidence()?;
    (effect.disposition() == &EffectDisposition::AbsorbedIntoExpression { producer }
        && expression.entity().producer() == producer
        && expression
            .entity()
            .source_obligations()
            .contains(obligation))
    .then(|| expression.inputs().clone())
}

fn exact_layer_expression_dependencies(
    layer: &SemanticCExpressionLayer,
    source: &SemanticObligationInventory,
    ledger: &ObligationLedger,
) -> Option<BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>> {
    let mut dependencies = BTreeMap::new();
    for entity in layer.entities() {
        let producer = entity.producer();
        let instruction = source.instructions().get(&producer)?;
        let live = instruction
            .obligations
            .iter()
            .copied()
            .filter(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
            .collect::<Vec<_>>();
        let [obligation] = live.as_slice() else {
            return None;
        };
        let [effect] = ledger.effects(*obligation) else {
            return None;
        };
        let expression = effect.expression_evidence()?;
        if instruction.state != SemanticInstructionState::LiveObligation
            || effect.disposition() != &(EffectDisposition::AbsorbedIntoExpression { producer })
            || expression.entity().producer() != producer
            || expression.entity().source_obligations() != entity.source_obligations()
            || entity.source_obligations() != &BTreeSet::from([*obligation])
            || layer.expr(entity.root()).is_none()
            || dependencies
                .insert(producer, expression.inputs().clone())
                .is_some()
        {
            return None;
        }
    }
    Some(dependencies)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactDependencyVisit {
    Active,
    Complete,
}

fn visit_exact_expression_dependency(
    producer: CanonicalInstructionId,
    boundaries: &BTreeSet<CanonicalInstructionId>,
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    states: &mut BTreeMap<CanonicalInstructionId, ExactDependencyVisit>,
    visible: &mut BTreeSet<CanonicalInstructionId>,
) -> Option<()> {
    if boundaries.contains(&producer) {
        return Some(());
    }
    match states.get(&producer) {
        Some(ExactDependencyVisit::Active) => return None,
        Some(ExactDependencyVisit::Complete) => return Some(()),
        None => {}
    }
    let inputs = dependencies.get(&producer)?;
    states.insert(producer, ExactDependencyVisit::Active);
    visible.insert(producer);
    for input in inputs {
        visit_exact_expression_dependency(*input, boundaries, dependencies, states, visible)?;
    }
    states.insert(producer, ExactDependencyVisit::Complete);
    Some(())
}

fn exact_visible_expression_closure(
    roots: impl IntoIterator<Item = CanonicalInstructionId>,
    boundaries: &BTreeSet<CanonicalInstructionId>,
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
) -> Option<BTreeSet<CanonicalInstructionId>> {
    let mut states = BTreeMap::new();
    let mut visible = BTreeSet::new();
    for producer in roots {
        visit_exact_expression_dependency(
            producer,
            boundaries,
            dependencies,
            &mut states,
            &mut visible,
        )?;
    }
    Some(visible)
}

fn return_mechanics_reaches_producer(
    source: &SemanticObligationInventory,
    ledger: &ObligationLedger,
    control: &CertifiedReturnControl,
    expected: CanonicalInstructionId,
) -> bool {
    let mut frontier = [
        control.return_address().value().producer(),
        control
            .exit_stack_pointer()
            .value()
            .and_then(|value| value.producer()),
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<_>>();
    let mut visited = BTreeSet::new();
    while let Some(producer) = frontier.pop() {
        if producer == expected {
            return true;
        }
        if !visited.insert(producer) {
            continue;
        }
        let Some(inputs) = ledger_expression_inputs(ledger, source, producer) else {
            return false;
        };
        frontier.extend(inputs);
    }
    false
}

fn mechanics_manifest_has_exact_order<'a>(
    owners: impl IntoIterator<Item = (CanonicalInstructionId, &'a [CanonicalInstructionId])>,
    source_order: &[CanonicalInstructionId],
    return_order: &[CanonicalInstructionId],
) -> bool {
    let owners = owners.into_iter().collect::<Vec<_>>();
    let producer_set = owners
        .iter()
        .map(|(producer, _)| *producer)
        .collect::<BTreeSet<_>>();
    let actual_producers = owners
        .iter()
        .map(|(producer, _)| *producer)
        .collect::<Vec<_>>();
    if owners.len() != producer_set.len()
        || actual_producers
            != source_order
                .iter()
                .copied()
                .filter(|producer| producer_set.contains(producer))
                .collect::<Vec<_>>()
    {
        return false;
    }
    owners.iter().all(|(_, return_producers)| {
        let return_set = return_producers.iter().copied().collect::<BTreeSet<_>>();
        !return_set.is_empty()
            && return_producers.len() == return_set.len()
            && *return_producers
                == return_order
                    .iter()
                    .copied()
                    .filter(|producer| return_set.contains(producer))
                    .collect::<Vec<_>>()
    })
}

fn return_mechanics_manifest_has_exact_order(
    owners: &[SemanticCReturnMechanicsOwner],
    source_order: &[CanonicalInstructionId],
    return_order: &[CanonicalInstructionId],
) -> bool {
    mechanics_manifest_has_exact_order(
        owners
            .iter()
            .map(|owner| (owner.source_producer(), owner.return_producers())),
        source_order,
        return_order,
    )
}

fn frame_mechanics_manifest_has_exact_order(
    owners: &[SemanticCFrameMechanicsOwner],
    authority: Option<&SemanticCFrameMechanicsAuthority>,
    expected_services: Option<&BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>>,
    source_order: &[CanonicalInstructionId],
    return_order: &[CanonicalInstructionId],
) -> bool {
    let (Some(authority), Some(expected_services)) = (authority, expected_services) else {
        return owners.is_empty() && authority.is_none() && expected_services.is_none();
    };
    mechanics_manifest_has_exact_order(
        owners
            .iter()
            .map(|owner| (owner.source_producer(), owner.return_producers())),
        source_order,
        return_order,
    ) && owners.iter().all(|owner| {
        owner.frame_pointer_storage() == authority.frame_pointer_storage()
            && owner.saved_range() == authority.saved_range()
            && expected_services
                .get(&owner.source_producer())
                .is_some_and(|expected| {
                    owner.return_producers()
                        == return_order
                            .iter()
                            .copied()
                            .filter(|producer| expected.contains(producer))
                            .collect::<Vec<_>>()
                })
    })
}

fn exact_frame_mechanics_services(
    authority: &SemanticCFrameMechanicsAuthority,
    source: &SemanticObligationInventory,
    ledger: &ObligationLedger,
    return_controls: &[&CertifiedReturnControl],
    return_order: &[CanonicalInstructionId],
) -> Option<BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>> {
    let mut services = replay_frame_mechanics_services(authority, source, ledger, return_order)?;
    for (producer, served) in &mut services {
        for control in return_controls {
            if return_mechanics_reaches_producer(source, ledger, control, *producer) {
                served.insert(control.producer());
            }
        }
    }
    Some(services)
}

fn replay_frame_mechanics_services(
    authority: &SemanticCFrameMechanicsAuthority,
    source: &SemanticObligationInventory,
    ledger: &ObligationLedger,
    return_order: &[CanonicalInstructionId],
) -> Option<BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>> {
    if authority.frame_pointer_storage().size == 0
        || authority.saved_range().size_bytes() == 0
        || authority.return_order() != return_order
        || authority.restore_roots().len() != return_order.len()
    {
        return None;
    }
    let mut dependencies = source
        .instructions()
        .keys()
        .filter_map(|producer| {
            ledger_expression_inputs(ledger, source, *producer).map(|inputs| (*producer, inputs))
        })
        .collect::<BTreeMap<_, _>>();
    for (producer, inputs) in authority.explicit_dependencies() {
        dependencies
            .entry(*producer)
            .or_default()
            .extend(inputs.iter().copied().filter(|input| input != producer));
    }
    let mut services = BTreeMap::<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>::new();
    for return_producer in return_order {
        let mut complete = BTreeSet::new();
        for root in authority
            .common_roots()
            .iter()
            .chain(authority.restore_roots().get(return_producer)?.iter())
        {
            let mut active = BTreeSet::new();
            let mut stack = vec![(*root, false)];
            while let Some((producer, leaving)) = stack.pop() {
                services
                    .entry(producer)
                    .or_default()
                    .insert(*return_producer);
                if leaving {
                    active.remove(&producer);
                    complete.insert(producer);
                    continue;
                }
                if active.contains(&producer) {
                    return None;
                }
                if complete.contains(&producer) {
                    continue;
                }
                active.insert(producer);
                stack.push((producer, true));
                let inputs = dependencies.get(&producer)?;
                stack.extend(inputs.iter().rev().map(|input| (*input, false)));
            }
        }
    }
    Some(services)
}

struct CertifiedBlockParts {
    expression_layer: SemanticCExpressionLayer,
    memory_statements: Vec<CertifiedMemoryStatement>,
    direct_calls: Vec<CertifiedDirectCall>,
    direct_controls: Vec<CertifiedDirectControl>,
    conditional_controls: Vec<CertifiedConditionalControl>,
    switch_controls: Vec<CertifiedSwitchControl>,
    return_controls: Vec<CertifiedReturnControl>,
}

fn projection_block_parts(
    projection: &CertifiedMachineProjection,
    block_addr: u64,
    expression_layer: SemanticCExpressionLayer,
) -> CertifiedBlockParts {
    let producers = projection
        .topology()
        .block(block_addr)
        .into_iter()
        .flat_map(|block| block.instructions())
        .copied()
        .collect::<Vec<_>>();
    CertifiedBlockParts {
        expression_layer,
        memory_statements: producers
            .iter()
            .filter_map(|producer| projection.memory_statement_for_producer(*producer).cloned())
            .collect(),
        direct_calls: producers
            .iter()
            .filter_map(|producer| projection.direct_call_for_producer(*producer).cloned())
            .collect(),
        direct_controls: producers
            .iter()
            .filter_map(|producer| projection.direct_control_for_producer(*producer).cloned())
            .collect(),
        conditional_controls: producers
            .iter()
            .filter_map(|producer| {
                projection
                    .conditional_control_for_producer(*producer)
                    .cloned()
            })
            .collect(),
        switch_controls: projection
            .switch_control_for_block(block_addr)
            .cloned()
            .into_iter()
            .collect(),
        return_controls: producers
            .iter()
            .filter_map(|producer| projection.return_control_for_producer(*producer).cloned())
            .collect(),
    }
}

fn insert_private_role(
    roles: &mut BTreeMap<SemanticObligationId, PrivateFrameConditionalJoinOwnerRole>,
    obligation: SemanticObligationId,
    role: PrivateFrameConditionalJoinOwnerRole,
) -> Result<(), RegionBuildError> {
    if roles.insert(obligation, role).is_some() {
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }
    Ok(())
}

fn insert_private_statement_role(
    roles: &mut BTreeMap<SemanticObligationId, PrivateFrameConditionalJoinOwnerRole>,
    statement: &CertifiedMemoryStatement,
    role: PrivateFrameConditionalJoinOwnerRole,
) -> Result<(), RegionBuildError> {
    if statement.access()
        != match &role {
            PrivateFrameConditionalJoinOwnerRole::AuxiliaryStoreMemory { access }
            | PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadMemory { access }
            | PrivateFrameConditionalJoinOwnerRole::JoinedTrueStoreMemory { access }
            | PrivateFrameConditionalJoinOwnerRole::JoinedFalseStoreMemory { access }
            | PrivateFrameConditionalJoinOwnerRole::JoinedLoadMemory { access }
            | PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadValue { access, .. }
            | PrivateFrameConditionalJoinOwnerRole::JoinedLoadValue { access, .. } => *access,
            PrivateFrameConditionalJoinOwnerRole::PrivateStackMechanics => {
                return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
            }
        }
        || statement.source_obligations().is_empty()
    {
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }
    for obligation in statement.source_obligations() {
        insert_private_role(roles, *obligation, role.clone())?;
    }
    Ok(())
}

fn exact_ledger_is_closed_for_private_join(
    projection: &CertifiedMachineProjection,
    rewrite: &CertifiedPrivateFrameConditionalJoinRewrite,
) -> bool {
    if rewrite.origin() != projection.origin()
        || rewrite.ledger_closure().origin() != projection.origin()
        || projection
            .source()
            .instructions()
            .values()
            .any(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return false;
    }
    let mut mappings = Vec::with_capacity(projection.source().obligations().len());
    for obligation in projection.source().obligations().keys() {
        let [effect] = projection.ledger().effects(*obligation) else {
            return false;
        };
        if matches!(
            effect.disposition(),
            EffectDisposition::Residualized { .. }
                | EffectDisposition::Refused { .. }
                | EffectDisposition::Rendered
                | EffectDisposition::Rewritten { .. }
                | EffectDisposition::Superseded { .. }
                | EffectDisposition::ProvenDead
        ) {
            return false;
        }
        mappings.push(TypedRegionMapping::new(
            *obligation,
            effect.disposition().clone(),
        ));
    }
    rewrite.ledger_closure().matches_ledger(
        projection.origin(),
        CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
        CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
        &mappings,
    )
}

fn private_join_accounting_authority(
    projection: &CertifiedMachineProjection,
    rewrite: &CertifiedPrivateFrameConditionalJoinRewrite,
) -> Result<PrivateFrameConditionalJoinAccountingAuthority, RegionBuildError> {
    let join = rewrite.machine_join();
    let stack = projection
        .stack_discipline()
        .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
    if join.origin() != projection.origin()
        || rewrite.origin() != projection.origin()
        || projection.private_frame_conditional_join(join.header()) != Some(join)
        || join.header() != projection.topology().entry_addr()
        || stack.origin() != projection.origin()
        || rewrite.expression_layer().schema_version() != SEMANTIC_C_SCHEMA_VERSION
        || !exact_ledger_is_closed_for_private_join(projection, rewrite)
        || !projection.direct_calls().is_empty()
    {
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }

    let layer = rewrite.expression_layer();
    let mut roles = BTreeMap::new();
    let auxiliary = join
        .auxiliary_direct_flows()
        .iter()
        .map(|(access, flow)| (*access, flow))
        .collect::<BTreeMap<_, _>>();
    if auxiliary.len() != rewrite.direct_substitutions().len() {
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }
    let mut rewritten_load_producers = BTreeSet::new();
    for substitution in rewrite.direct_substitutions() {
        let access = substitution.load_access();
        let flow = auxiliary
            .get(&access)
            .copied()
            .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
        let mut stores = flow
            .definitions()
            .iter()
            .filter_map(|definition| definition.store());
        let store = stores
            .next()
            .filter(|_| stores.next().is_none())
            .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
        insert_private_statement_role(
            &mut roles,
            store.statement(),
            PrivateFrameConditionalJoinOwnerRole::AuxiliaryStoreMemory {
                access: store.statement().access(),
            },
        )?;
        let load = flow.load().statement();
        if load.access() != access || substitution.load_result().producer() != Some(load.producer())
        {
            return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
        }
        insert_private_statement_role(
            &mut roles,
            load,
            PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadMemory { access },
        )?;
        let entity = layer
            .entity_for_producer(load.producer())
            .filter(|entity| entity.root() == substitution.load_root())
            .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
        for obligation in entity.source_obligations() {
            insert_private_role(
                &mut roles,
                *obligation,
                PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadValue {
                    access,
                    root: entity.root(),
                },
            )?;
        }
        rewritten_load_producers.insert(load.producer());
    }

    let joined = rewrite.joined_select();
    let joined_load = join.joined_flow().load().statement();
    if joined.load_access() != joined_load.access()
        || joined.load_result().producer() != Some(joined_load.producer())
    {
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }
    for (statement, role) in [
        (
            join.true_arm().store().statement(),
            PrivateFrameConditionalJoinOwnerRole::JoinedTrueStoreMemory {
                access: join.true_arm().store().statement().access(),
            },
        ),
        (
            join.false_arm().store().statement(),
            PrivateFrameConditionalJoinOwnerRole::JoinedFalseStoreMemory {
                access: join.false_arm().store().statement().access(),
            },
        ),
        (
            joined_load,
            PrivateFrameConditionalJoinOwnerRole::JoinedLoadMemory {
                access: joined_load.access(),
            },
        ),
    ] {
        insert_private_statement_role(&mut roles, statement, role)?;
    }
    let joined_entity = layer
        .entity_for_producer(joined_load.producer())
        .filter(|entity| entity.root() == joined.load_root())
        .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
    for obligation in joined_entity.source_obligations() {
        insert_private_role(
            &mut roles,
            *obligation,
            PrivateFrameConditionalJoinOwnerRole::JoinedLoadValue {
                access: joined_load.access(),
                root: joined_entity.root(),
            },
        )?;
    }
    rewritten_load_producers.insert(joined_load.producer());

    let mut visible_roots = vec![joined.condition_root(), joined.return_root()];
    for value in rewrite
        .direct_substitutions()
        .iter()
        .map(|substitution| substitution.replacement())
        .chain([joined.true_value(), joined.false_value()])
    {
        if let CertifiedPrivateFrameJoinValueOrigin::Produced { root, .. } = value.origin() {
            visible_roots.push(*root);
        }
    }
    let mut stack_roots = stack
        .assignments()
        .iter()
        .map(|assignment| assignment.producer())
        .collect::<BTreeSet<_>>();
    stack_roots.insert(stack.reservation().producer());
    for region in stack.private_regions() {
        for access in region.accesses() {
            if let Some(producer) = access.statement().address().producer() {
                stack_roots.insert(producer);
            }
        }
    }
    for release in stack.releases() {
        stack_roots.insert(release.restoration().producer());
        if let Some(assignment) = release.post_restoration() {
            stack_roots.insert(assignment.producer());
        }
        if let Some(statement) = release.return_address_read()
            && let Some(producer) = statement.address().producer()
        {
            stack_roots.insert(producer);
        }
    }
    let mut stack_producers = BTreeSet::new();
    let mut frontier = stack_roots.into_iter().collect::<Vec<_>>();
    while let Some(producer) = frontier.pop() {
        if !stack_producers.insert(producer) {
            continue;
        }
        if let Some(inputs) =
            ledger_expression_inputs(projection.ledger(), projection.source(), producer)
        {
            frontier.extend(inputs);
        }
    }
    let return_mechanics = layer
        .return_mechanics()
        .owners()
        .iter()
        .map(|owner| owner.source_producer())
        .chain(
            layer
                .frame_mechanics()
                .owners()
                .iter()
                .map(|owner| owner.source_producer()),
        )
        .collect::<BTreeSet<_>>();
    let dependency_map =
        exact_layer_expression_dependencies(layer, projection.source(), projection.ledger())
            .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
    let visible_seeds = visible_roots
        .into_iter()
        .map(|root| {
            layer
                .expr(root)
                .map(|expression| expression.source_instructions())
                .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    let visible_producers =
        exact_visible_expression_closure(visible_seeds, &rewritten_load_producers, &dependency_map)
            .ok_or(RegionBuildError::PrivateFrameConditionalJoinMismatch)?;
    for entity in layer.entities() {
        if rewritten_load_producers.contains(&entity.producer()) {
            continue;
        }
        if visible_producers.contains(&entity.producer()) {
            continue;
        }
        if return_mechanics.contains(&entity.producer()) {
            continue;
        }
        if stack_producers.contains(&entity.producer()) {
            for obligation in entity.source_obligations() {
                insert_private_role(
                    &mut roles,
                    *obligation,
                    PrivateFrameConditionalJoinOwnerRole::PrivateStackMechanics,
                )?;
            }
            continue;
        }
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }

    let authority = PrivateFrameConditionalJoinAccountingAuthority {
        header: join.header(),
        stack_pointer_storage: stack.stack_pointer_storage(),
        reservation_range: stack.reservation_range(),
        roles: roles.into_iter().collect::<Vec<_>>().into_boxed_slice(),
    };
    if !private_role_manifest_is_canonical(&authority.roles) {
        return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
    }
    Ok(authority)
}

fn semantic_return_definition_matches(
    semantic: &SemanticCReturnRegisterDefinition,
    certified: &CertifiedReturnRegisterDefinition,
    layer: &SemanticCExpressionLayer,
) -> bool {
    certified.value().producer() == Some(certified.producer())
        && semantic.storage() == certified.storage()
        && semantic.binding() == certified.value().binding()
        && semantic.producer() == certified.producer()
        && layer
            .entity_for_producer(certified.producer())
            .is_some_and(|entity| {
                entity.output() == semantic.binding()
                    && entity.root() == semantic.expression()
                    && layer.expr_type(entity.root()).ok() == Some(certified.value().ty())
            })
        && certified.storage().size.checked_mul(8) == Some(certified.value().binding().width_bits())
}

fn semantic_return_matches_control(
    returned: &SemanticCReturn,
    control: &CertifiedReturnControl,
    layer: &SemanticCExpressionLayer,
) -> bool {
    returned.control_target() == control.control_target().binding()
        && returned.source_obligations() == &control.source_obligations()
        && returned.values().len() == control.values().len()
        && returned
            .values()
            .iter()
            .zip(control.values())
            .all(|(semantic, certified)| {
                let Some(producer) = certified.value().producer() else {
                    return false;
                };
                semantic.slot() == certified.slot()
                    && semantic.binding() == certified.value().binding()
                    && semantic.producer() == producer
                    && layer.entity_for_producer(producer).is_some_and(|entity| {
                        entity.root() == semantic.expression()
                            && entity.output() == semantic.binding()
                            && layer.expr_type(entity.root()).ok() == Some(certified.value().ty())
                    })
            })
        && returned.register_compositions().len() == control.register_compositions().len()
        && returned
            .register_compositions()
            .iter()
            .zip(control.register_compositions())
            .all(|(semantic, certified)| {
                semantic.slot() == certified.slot()
                    && semantic_return_definition_matches(semantic.base(), certified.base(), layer)
                    && semantic.overlays().len() == certified.overlays().len()
                    && semantic.overlays().iter().zip(certified.overlays()).all(
                        |(semantic_overlay, certified_overlay)| {
                            semantic_overlay.offset_bytes() == certified_overlay.offset_bytes()
                                && semantic_return_definition_matches(
                                    semantic_overlay.definition(),
                                    certified_overlay.definition(),
                                    layer,
                                )
                        },
                    )
            })
}

impl CertifiedSingleBlockAccounting {
    pub fn from_certified(certified: &CertifiedMachineFunction) -> Result<Self, RegionBuildError> {
        let block_addr = only_source_block(certified.topology())?;
        let expression_layer = SemanticCExpressionLayer::from_certified(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, RegionBuildError> {
        let block_addr = only_source_block(certified.topology())?;
        let expression_layer = SemanticCExpressionLayer::from_projection(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    /// Account one selected block in a multi-block certified artifact.
    ///
    /// The expected instruction and obligation subset is always derived from
    /// the retained full-function topology and inventory.
    pub fn from_certified_block(
        certified: &CertifiedMachineFunction,
        block_addr: u64,
    ) -> Result<Self, RegionBuildError> {
        require_source_block(certified.topology(), block_addr)?;
        let expression_layer = SemanticCExpressionLayer::from_certified(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    pub fn from_projection_block(
        certified: &CertifiedMachineProjection,
        block_addr: u64,
    ) -> Result<Self, RegionBuildError> {
        require_source_block(certified.topology(), block_addr)?;
        let expression_layer = SemanticCExpressionLayer::from_projection(certified)?;
        Self::from_projection_block_with_layer(certified, block_addr, expression_layer)
    }

    /// Build block-local accounting whose value layer may reference two-way
    /// merges the owning region has certified.
    ///
    /// Reserved for a region holding `CertifiedTwoWayJoinPhi` witnesses: the
    /// merges become variables that the region itself assigns on each incoming
    /// edge, so a caller without witnesses must keep using
    /// `from_projection_block`, where a merge stays a hard error.
    pub(crate) fn from_projection_block_with_join_phis(
        certified: &CertifiedMachineProjection,
        block_addr: u64,
        join_phis: &BTreeMap<CanonicalInstructionId, r2cert::CertifiedTwoWayJoinPhi>,
    ) -> Result<Self, RegionBuildError> {
        require_source_block(certified.topology(), block_addr)?;
        let expression_layer =
            SemanticCExpressionLayer::from_projection_with_join_phis(certified, join_phis)?;
        Self::from_projection_block_with_layer(certified, block_addr, expression_layer)
    }

    fn from_projection_block_with_layer(
        certified: &CertifiedMachineProjection,
        block_addr: u64,
        expression_layer: SemanticCExpressionLayer,
    ) -> Result<Self, RegionBuildError> {
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    /// Build block-local typed-output accounting for one exact sealed
    /// private-frame conditional-join rewrite plan.
    pub(crate) fn from_private_frame_conditional_join_rewrite_block(
        projection: &CertifiedMachineProjection,
        rewrite: &CertifiedPrivateFrameConditionalJoinRewrite,
        block_addr: u64,
    ) -> Result<Self, RegionBuildError> {
        require_source_block(projection.topology(), block_addr)?;
        let authority = private_join_accounting_authority(projection, rewrite)?;
        if projection.source().obligations().keys().any(|obligation| {
            matches!(
                obligation.kind,
                SemanticObligationKind::Call
                    | SemanticObligationKind::CallArgument
                    | SemanticObligationKind::CallResult
                    | SemanticObligationKind::Trap
                    | SemanticObligationKind::Atomicity
                    | SemanticObligationKind::MemoryOrdering
                    | SemanticObligationKind::VolatileOrUnknownEffect
                    | SemanticObligationKind::LoopCarriedState
                    | SemanticObligationKind::LiveStateTransition
            )
        }) {
            return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
        }
        let roles = authority.roles.iter().cloned().collect::<BTreeMap<_, _>>();
        let parts =
            projection_block_parts(projection, block_addr, rewrite.expression_layer().clone());
        let mut accounting = Self::from_parts_with_private_join(
            projection.origin(),
            projection.source(),
            projection.topology(),
            projection.ledger(),
            block_addr,
            parts,
            None,
        )?;
        for mapping in &mut accounting.mappings {
            if let Some(role) = roles.get(&mapping.obligation) {
                let [effect] = projection.ledger().effects(mapping.obligation) else {
                    return Err(
                        RegionBuildError::UnsupportedPrivateFrameConditionalJoinObligation(
                            mapping.obligation,
                        ),
                    );
                };
                let exact_disposition = match effect.disposition() {
                    EffectDisposition::AbsorbedIntoExpression { producer } => {
                        RegionObligationDisposition::AbsorbedIntoExpression {
                            producer: *producer,
                        }
                    }
                    EffectDisposition::AbsorbedIntoStatement { producer } => {
                        RegionObligationDisposition::AbsorbedIntoStatement {
                            producer: *producer,
                        }
                    }
                    _ => {
                        return Err(
                            RegionBuildError::UnsupportedPrivateFrameConditionalJoinObligation(
                                mapping.obligation,
                            ),
                        );
                    }
                };
                if mapping.disposition != exact_disposition {
                    return Err(
                        RegionBuildError::UnsupportedPrivateFrameConditionalJoinObligation(
                            mapping.obligation,
                        ),
                    );
                }
                mapping.owner = Some(RegionTypedOwner::PrivateFrameConditionalJoin {
                    producer: mapping.obligation.instruction,
                    role: role.clone(),
                });
            } else if matches!(
                mapping.disposition,
                RegionObligationDisposition::Residualized { .. }
            ) || matches!(mapping.owner, Some(RegionTypedOwner::Call { .. }))
            {
                return Err(
                    RegionBuildError::UnsupportedPrivateFrameConditionalJoinObligation(
                        mapping.obligation,
                    ),
                );
            }
        }
        accounting.private_frame_conditional_join = Some(authority);
        if !accounting.audit().has_exact_source_accounting() {
            return Err(RegionBuildError::PrivateFrameConditionalJoinMismatch);
        }
        Ok(accounting)
    }

    fn from_parts(
        origin: &CertifiedArtifactOrigin,
        source: &SemanticObligationInventory,
        topology: &CertifiedSourceTopology,
        ledger: &ObligationLedger,
        block_addr: u64,
        parts: CertifiedBlockParts,
    ) -> Result<Self, RegionBuildError> {
        Self::from_parts_with_private_join(
            origin, source, topology, ledger, block_addr, parts, None,
        )
    }

    fn from_parts_with_private_join(
        origin: &CertifiedArtifactOrigin,
        source: &SemanticObligationInventory,
        topology: &CertifiedSourceTopology,
        ledger: &ObligationLedger,
        block_addr: u64,
        parts: CertifiedBlockParts,
        private_frame_conditional_join: Option<PrivateFrameConditionalJoinAccountingAuthority>,
    ) -> Result<Self, RegionBuildError> {
        if !ledger.matches_origin(origin) {
            return Err(RegionBuildError::ArtifactOriginMismatch);
        }
        let CertifiedBlockParts {
            expression_layer,
            mut memory_statements,
            direct_calls,
            direct_controls,
            conditional_controls,
            switch_controls,
            return_controls,
        } = parts;
        let source_block = require_source_block(topology, block_addr)?;
        let return_mechanics = expression_layer
            .return_mechanics()
            .owners()
            .iter()
            .map(|owner| (owner.source_producer(), owner))
            .collect::<BTreeMap<_, _>>();
        let frame_mechanics = expression_layer
            .frame_mechanics()
            .owners()
            .iter()
            .map(|owner| (owner.source_producer(), owner))
            .collect::<BTreeMap<_, _>>();
        if return_mechanics
            .keys()
            .any(|producer| frame_mechanics.contains_key(producer))
        {
            return Err(RegionBuildError::AmbiguousControl(
                *return_mechanics
                    .keys()
                    .find(|producer| frame_mechanics.contains_key(producer))
                    .expect("overlap checked"),
            ));
        }
        memory_statements.retain(|statement| {
            !return_mechanics.contains_key(&statement.producer())
                && !frame_mechanics.contains_key(&statement.producer())
        });
        let semantic_returns = return_controls
            .iter()
            .map(|control| semantic_return_from_control(control, &expression_layer))
            .collect::<Result<Vec<_>, _>>()?;
        let semantic_calls = direct_calls
            .iter()
            .map(|call| semantic_call_from_control(call, &expression_layer))
            .collect::<Result<Vec<_>, _>>()?;
        let expression_entities = expression_layer
            .entities()
            .iter()
            .map(|entity| (entity.producer(), entity))
            .collect::<BTreeMap<_, _>>();
        let statement_entities = memory_statements
            .iter()
            .map(|statement| (statement.producer(), statement))
            .collect::<BTreeMap<_, _>>();
        let direct_call_entities = direct_calls
            .iter()
            .map(|call| (call.producer(), call))
            .collect::<BTreeMap<_, _>>();
        let direct_control_entities = direct_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let conditional_control_entities = conditional_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let switch_control_entities = switch_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let return_control_entities = return_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        if let Some(producer) = direct_control_entities
            .keys()
            .find(|producer| {
                conditional_control_entities.contains_key(producer)
                    || switch_control_entities.contains_key(producer)
            })
            .or_else(|| {
                conditional_control_entities
                    .keys()
                    .find(|producer| switch_control_entities.contains_key(producer))
            })
        {
            return Err(RegionBuildError::AmbiguousControl(*producer));
        }
        let mut instructions = Vec::with_capacity(source.instructions().len());
        let mut mappings = Vec::with_capacity(source.obligations().len());

        for id in block_source_instruction_order(source, source_block) {
            let disposition = source
                .instructions()
                .get(&id)
                .ok_or(RegionBuildError::MissingSourceInstruction(id))?;
            let expression_producer = expression_entities.get(&id).map(|entity| entity.producer());
            let statement_producer = statement_entities
                .get(&id)
                .map(|statement| statement.producer());
            let call_producer = direct_call_entities.get(&id).map(|call| call.producer());
            let control_producer = direct_control_entities
                .get(&id)
                .map(|control| control.producer())
                .or_else(|| {
                    conditional_control_entities
                        .get(&id)
                        .map(|control| control.producer())
                })
                .or_else(|| {
                    switch_control_entities
                        .get(&id)
                        .map(|control| control.producer())
                });
            let return_producer = return_control_entities
                .get(&id)
                .map(|control| control.producer());
            instructions.push(CertifiedRegionInstruction {
                source: id,
                state: disposition.state,
                expression_producer,
                statement_producer,
                call_producer,
                control_producer,
                return_producer,
            });
            for obligation in &disposition.obligations {
                let mapping = if let Some(mechanics_owner) = frame_mechanics.get(&id) {
                    if !mechanics_owner.source_obligations().contains(obligation) {
                        return Err(RegionBuildError::ExpressionObligationMismatch(*obligation));
                    }
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::ExpressionObligationMismatch(*obligation));
                    };
                    let exact_ledger_owner = match obligation.kind {
                        SemanticObligationKind::LiveValueProducer => {
                            effect.disposition()
                                == &(EffectDisposition::AbsorbedIntoExpression { producer: id })
                                && effect.expression_evidence().is_some_and(|expression| {
                                    expression.entity().producer() == id
                                        && expression
                                            .entity()
                                            .source_obligations()
                                            .contains(obligation)
                                })
                        }
                        SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite => {
                            effect.disposition()
                                == &(EffectDisposition::AbsorbedIntoStatement { producer: id })
                                && effect.statement_evidence().is_some_and(|statement| {
                                    statement.producer() == id
                                        && statement.source_obligations().contains(obligation)
                                })
                        }
                        _ => false,
                    };
                    if !exact_ledger_owner {
                        return Err(RegionBuildError::ExpressionObligationMismatch(*obligation));
                    }
                    (
                        RegionObligationDisposition::AbsorbedIntoFrameMechanics { producer: id },
                        Some(RegionTypedOwner::FrameMechanics {
                            source_producer: id,
                            frame_pointer_storage: mechanics_owner.frame_pointer_storage(),
                            saved_range: mechanics_owner.saved_range(),
                            return_producers: mechanics_owner
                                .return_producers()
                                .to_vec()
                                .into_boxed_slice(),
                        }),
                    )
                } else if let Some(mechanics_owner) = return_mechanics.get(&id) {
                    if !mechanics_owner.source_obligations().contains(obligation) {
                        return Err(RegionBuildError::ExpressionObligationMismatch(*obligation));
                    }
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::ExpressionObligationMismatch(*obligation));
                    };
                    let exact_source_owner = match obligation.kind {
                        SemanticObligationKind::LiveValueProducer => {
                            effect.disposition()
                                == &(EffectDisposition::AbsorbedIntoExpression { producer: id })
                                && effect.expression_evidence().is_some_and(|expression| {
                                    expression.entity().producer() == id
                                        && expression
                                            .entity()
                                            .source_obligations()
                                            .contains(obligation)
                                })
                        }
                        SemanticObligationKind::ObservableMemoryRead => {
                            effect.disposition()
                                == &(EffectDisposition::AbsorbedIntoStatement { producer: id })
                                && effect.statement_evidence().is_some_and(|statement| {
                                    statement.producer() == id
                                        && statement.source_obligations().contains(obligation)
                                })
                        }
                        _ => false,
                    };
                    if !exact_source_owner {
                        return Err(RegionBuildError::ExpressionObligationMismatch(*obligation));
                    }
                    (
                        RegionObligationDisposition::AbsorbedIntoReturn { producer: id },
                        Some(RegionTypedOwner::ReturnMechanics {
                            source_producer: id,
                            return_producers: mechanics_owner
                                .return_producers()
                                .to_vec()
                                .into_boxed_slice(),
                        }),
                    )
                } else if obligation.kind == SemanticObligationKind::LiveValueProducer {
                    if let Some(entity) = expression_entities.get(&id) {
                        if !entity.source_obligations().contains(obligation) {
                            return Err(RegionBuildError::ExpressionObligationMismatch(
                                *obligation,
                            ));
                        }
                        (
                            RegionObligationDisposition::AbsorbedIntoExpression { producer: id },
                            Some(RegionTypedOwner::Expression {
                                producer: id,
                                root: entity.root(),
                            }),
                        )
                    } else if expression_layer.open_obligations().contains(obligation) {
                        (
                            RegionObligationDisposition::Residualized {
                                reason: residual_reason(obligation.kind),
                            },
                            None,
                        )
                    } else {
                        return Err(RegionBuildError::MissingExpression(id));
                    }
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite
                ) && statement_entities
                    .get(&id)
                    .is_some_and(|statement| statement.source_obligations().contains(obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::StatementObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoStatement { producer: id })
                    {
                        return Err(RegionBuildError::StatementObligationMismatch(*obligation));
                    }
                    (
                        RegionObligationDisposition::AbsorbedIntoStatement { producer: id },
                        Some(RegionTypedOwner::Statement {
                            producer: id,
                            component: obligation.component,
                        }),
                    )
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::Call | SemanticObligationKind::CallArgument
                ) && direct_call_entities
                    .get(&id)
                    .is_some_and(|call| call.source_obligations().contains(obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::CallObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoCall { producer: id })
                        || effect.direct_call_evidence() != direct_call_entities.get(&id).copied()
                    {
                        return Err(RegionBuildError::CallObligationMismatch(*obligation));
                    }
                    (
                        RegionObligationDisposition::AbsorbedIntoCall { producer: id },
                        Some(RegionTypedOwner::Call {
                            producer: id,
                            component: obligation.component,
                        }),
                    )
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::ControlPredicate
                        | SemanticObligationKind::ControlTransfer
                ) && (direct_control_entities
                    .get(&id)
                    .is_some_and(|control| control.source_obligation() == *obligation)
                    || conditional_control_entities
                        .get(&id)
                        .is_some_and(|control| control.source_obligations().contains(obligation))
                    || switch_control_entities
                        .get(&id)
                        .is_some_and(|control| control.source_obligation() == *obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::ControlObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoControl { producer: id })
                        || switch_control_entities.contains_key(&id)
                            && effect.switch_control_evidence()
                                != switch_control_entities.get(&id).copied()
                    {
                        return Err(RegionBuildError::ControlObligationMismatch(*obligation));
                    }
                    (
                        RegionObligationDisposition::AbsorbedIntoControl { producer: id },
                        Some(RegionTypedOwner::Control {
                            producer: id,
                            component: obligation.component,
                        }),
                    )
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
                ) && return_control_entities
                    .get(&id)
                    .is_some_and(|control| control.source_obligations().contains(obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::ReturnObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoReturn { producer: id })
                    {
                        return Err(RegionBuildError::ReturnObligationMismatch(*obligation));
                    }
                    (
                        RegionObligationDisposition::AbsorbedIntoReturn { producer: id },
                        Some(RegionTypedOwner::Return {
                            producer: id,
                            component: obligation.component,
                        }),
                    )
                } else {
                    (
                        RegionObligationDisposition::Residualized {
                            reason: residual_reason(obligation.kind),
                        },
                        None,
                    )
                };
                let (mapping, owner) = mapping;
                mappings.push(RegionObligationMapping {
                    obligation: *obligation,
                    disposition: mapping,
                    owner,
                });
            }
        }

        Ok(Self {
			schema_version: CERTIFIED_REGION_SCHEMA_VERSION,
			scope: SingleBlockAccountingScope::SourceAccountingWithCertifiedSemanticEntitiesAndOpenBlockExit,
			identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
			origin: origin.clone(),
            block_addr,
            source: source.clone(),
            topology: topology.clone(),
            ledger: ledger.clone(),
            expression_layer,
            memory_statements: memory_statements.into_boxed_slice(),
            direct_calls: direct_calls.into_boxed_slice(),
            semantic_calls: semantic_calls.into_boxed_slice(),
            direct_controls: direct_controls.into_boxed_slice(),
            conditional_controls: conditional_controls.into_boxed_slice(),
            switch_controls: switch_controls.into_boxed_slice(),
            return_controls: return_controls.into_boxed_slice(),
            semantic_returns: semantic_returns.into_boxed_slice(),
            instructions: instructions.into_boxed_slice(),
            mappings: mappings.into_boxed_slice(),
            private_frame_conditional_join,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SingleBlockAccountingScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn block_addr(&self) -> u64 {
        self.block_addr
    }

    pub const fn topology(&self) -> &CertifiedSourceTopology {
        &self.topology
    }

    pub const fn ledger(&self) -> &ObligationLedger {
        &self.ledger
    }

    pub const fn expression_layer(&self) -> &SemanticCExpressionLayer {
        &self.expression_layer
    }

    pub const fn memory_statements(&self) -> &[CertifiedMemoryStatement] {
        &self.memory_statements
    }

    pub fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement> {
        self.memory_statements
            .iter()
            .find(|statement| statement.producer() == producer)
    }

    pub const fn direct_calls(&self) -> &[CertifiedDirectCall] {
        &self.direct_calls
    }

    pub const fn semantic_calls(&self) -> &[SemanticCDirectCall] {
        &self.semantic_calls
    }

    pub fn direct_call_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectCall> {
        self.direct_calls
            .iter()
            .find(|call| call.producer() == producer)
    }

    pub const fn direct_controls(&self) -> &[CertifiedDirectControl] {
        &self.direct_controls
    }

    pub fn direct_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectControl> {
        self.direct_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub const fn conditional_controls(&self) -> &[CertifiedConditionalControl] {
        &self.conditional_controls
    }

    pub fn conditional_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedConditionalControl> {
        self.conditional_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub const fn switch_controls(&self) -> &[CertifiedSwitchControl] {
        &self.switch_controls
    }

    pub fn switch_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedSwitchControl> {
        self.switch_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub const fn return_controls(&self) -> &[CertifiedReturnControl] {
        &self.return_controls
    }

    pub const fn semantic_returns(&self) -> &[SemanticCReturn] {
        &self.semantic_returns
    }

    pub fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl> {
        self.return_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub fn source_block(&self) -> Option<&r2cert::CertifiedSourceBlock> {
        self.topology.block(self.block_addr)
    }

    pub const fn instructions(&self) -> &[CertifiedRegionInstruction] {
        &self.instructions
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub fn audit(&self) -> RegionAuditReport {
        let source_block = self.topology.block(self.block_addr);
        let expected_instructions = source_block
            .into_iter()
            .flat_map(|block| block_source_instruction_order(&self.source, block))
            .collect::<BTreeSet<_>>();
        let expected_obligations = expected_instructions
            .iter()
            .filter_map(|id| self.source.instructions().get(id))
            .flat_map(|instruction| instruction.obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let instruction_counts = counts(
            self.instructions
                .iter()
                .map(|instruction| instruction.source),
        );
        let obligation_counts = counts(self.mappings.iter().map(|mapping| mapping.obligation));
        let (missing_instructions, duplicate_instructions, unexpected_instructions) =
            reconcile(expected_instructions.iter().copied(), &instruction_counts);
        let (missing_obligations, duplicate_obligations, unexpected_obligations) =
            reconcile(expected_obligations.iter().copied(), &obligation_counts);
        let mut invalid = Vec::new();
        let expression_entities = self
            .expression_layer
            .entities()
            .iter()
            .map(|entity| (entity.producer(), entity))
            .collect::<BTreeMap<_, _>>();
        let mechanics_owners = self.expression_layer.return_mechanics().owners();
        let mechanics_entities = mechanics_owners
            .iter()
            .map(|owner| (owner.source_producer(), owner))
            .collect::<BTreeMap<_, _>>();
        let frame_owners = self.expression_layer.frame_mechanics().owners();
        let frame_entities = frame_owners
            .iter()
            .map(|owner| (owner.source_producer(), owner))
            .collect::<BTreeMap<_, _>>();
        let mechanics_producers = mechanics_entities
            .keys()
            .chain(frame_entities.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let return_mechanics_obligations = mechanics_owners
            .iter()
            .flat_map(|owner| owner.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let frame_mechanics_obligations = frame_owners
            .iter()
            .flat_map(|owner| owner.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let mechanics_obligations = return_mechanics_obligations
            .union(&frame_mechanics_obligations)
            .copied()
            .collect::<BTreeSet<_>>();
        let expected_expression_producers = self
            .source
            .instructions()
            .iter()
            .filter_map(|(id, instruction)| {
                instruction
                    .obligations
                    .iter()
                    .any(|obligation| {
                        obligation.kind == SemanticObligationKind::LiveValueProducer
                            && !self
                                .expression_layer
                                .open_obligations()
                                .contains(obligation)
                    })
                    .then_some(*id)
            })
            .filter(|producer| !mechanics_producers.contains(producer))
            .collect::<BTreeSet<_>>();
        let actual_expression_producers =
            expression_entities.keys().copied().collect::<BTreeSet<_>>();
        let expected_expression_obligations = self
            .source
            .obligations()
            .keys()
            .copied()
            .filter(|id| {
                id.kind == SemanticObligationKind::LiveValueProducer
                    && !self.expression_layer.open_obligations().contains(id)
                    && !mechanics_obligations.contains(id)
            })
            .collect::<BTreeSet<_>>();
        let expected_block_expression_obligations = expected_obligations
            .iter()
            .copied()
            .filter(|id| {
                id.kind == SemanticObligationKind::LiveValueProducer
                    && !self.expression_layer.open_obligations().contains(id)
                    && !mechanics_obligations.contains(id)
            })
            .collect::<BTreeSet<_>>();
        let entity_expression_obligations = self
            .expression_layer
            .entities()
            .iter()
            .flat_map(|entity| entity.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let mapped_expression_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                (matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoExpression { .. }
                ) && !matches!(mapping.owner, Some(RegionTypedOwner::FrameMechanics { .. })))
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let statement_entities = self
            .memory_statements
            .iter()
            .map(|statement| (statement.producer(), statement))
            .collect::<BTreeMap<_, _>>();
        let statement_obligations = self
            .memory_statements
            .iter()
            .flat_map(|statement| statement.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let mapped_statement_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                (matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoStatement { .. }
                ) && !matches!(mapping.owner, Some(RegionTypedOwner::FrameMechanics { .. })))
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let direct_call_entities = self
            .direct_calls
            .iter()
            .map(|call| (call.producer(), call))
            .collect::<BTreeMap<_, _>>();
        let semantic_call_entities = self
            .semantic_calls
            .iter()
            .map(|call| (call.producer(), call))
            .collect::<BTreeMap<_, _>>();
        let call_obligations = self
            .direct_calls
            .iter()
            .flat_map(CertifiedDirectCall::source_obligations)
            .collect::<BTreeSet<_>>();
        let mapped_call_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoCall { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let direct_control_entities = self
            .direct_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let conditional_control_entities = self
            .conditional_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let switch_control_entities = self
            .switch_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let return_control_entities = self
            .return_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let semantic_return_entities = self
            .semantic_returns
            .iter()
            .map(|returned| (returned.producer(), returned))
            .collect::<BTreeMap<_, _>>();
        let direct_control_obligations = self
            .direct_controls
            .iter()
            .map(CertifiedDirectControl::source_obligation)
            .collect::<BTreeSet<_>>();
        let conditional_control_obligations = self
            .conditional_controls
            .iter()
            .flat_map(CertifiedConditionalControl::source_obligations)
            .collect::<BTreeSet<_>>();
        let switch_control_obligations = self
            .switch_controls
            .iter()
            .map(CertifiedSwitchControl::source_obligation)
            .collect::<BTreeSet<_>>();
        let control_obligations = direct_control_obligations
            .union(&conditional_control_obligations)
            .copied()
            .chain(switch_control_obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let mapped_control_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let return_obligations = self
            .return_controls
            .iter()
            .flat_map(CertifiedReturnControl::source_obligations)
            .collect::<BTreeSet<_>>();
        let mapped_return_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(&mapping.owner, Some(RegionTypedOwner::Return { .. }))
                    .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let mapped_mechanics_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    &mapping.owner,
                    Some(RegionTypedOwner::ReturnMechanics { .. })
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let mapped_frame_mechanics_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    &mapping.owner,
                    Some(RegionTypedOwner::FrameMechanics { .. })
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let private_roles = self
            .private_frame_conditional_join
            .as_ref()
            .map(|authority| authority.roles.iter().cloned().collect::<BTreeMap<_, _>>())
            .unwrap_or_default();

        for mapping in &self.mappings {
            let owner_matches = match (&mapping.disposition, &mapping.owner) {
                (
                    RegionObligationDisposition::AbsorbedIntoExpression { producer },
                    Some(RegionTypedOwner::Expression {
                        producer: owner,
                        root,
                    }),
                ) => expression_entities.get(producer).is_some_and(|entity| {
                    producer == owner
                        && entity.root() == *root
                        && entity.source_obligations().contains(&mapping.obligation)
                }),
                (
                    RegionObligationDisposition::AbsorbedIntoStatement { producer },
                    Some(RegionTypedOwner::Statement {
                        producer: owner,
                        component,
                    }),
                ) => {
                    producer == owner
                        && *component == mapping.obligation.component
                        && statement_entities.get(producer).is_some_and(|statement| {
                            statement.source_obligations().contains(&mapping.obligation)
                        })
                }
                (
                    RegionObligationDisposition::AbsorbedIntoCall { producer },
                    Some(RegionTypedOwner::Call {
                        producer: owner,
                        component,
                    }),
                ) => {
                    producer == owner
                        && *component == mapping.obligation.component
                        && direct_call_entities.get(producer).is_some_and(|call| {
                            call.source_obligations().contains(&mapping.obligation)
                        })
                        && semantic_call_entities.contains_key(producer)
                }
                (
                    RegionObligationDisposition::AbsorbedIntoControl { producer },
                    Some(RegionTypedOwner::Control {
                        producer: owner,
                        component,
                    }),
                ) => {
                    producer == owner
                        && *component == mapping.obligation.component
                        && (direct_control_entities
                            .get(producer)
                            .is_some_and(|control| {
                                control.source_obligation() == mapping.obligation
                            })
                            || conditional_control_entities
                                .get(producer)
                                .is_some_and(|control| {
                                    control.source_obligations().contains(&mapping.obligation)
                                })
                            || switch_control_entities
                                .get(producer)
                                .is_some_and(|control| {
                                    control.source_obligation() == mapping.obligation
                                }))
                }
                (
                    RegionObligationDisposition::AbsorbedIntoReturn { producer },
                    Some(RegionTypedOwner::Return {
                        producer: owner,
                        component,
                    }),
                ) => {
                    producer == owner
                        && *component == mapping.obligation.component
                        && return_control_entities
                            .get(producer)
                            .is_some_and(|control| {
                                control.source_obligations().contains(&mapping.obligation)
                            })
                        && semantic_return_entities.contains_key(producer)
                }
                (
                    RegionObligationDisposition::AbsorbedIntoReturn { producer },
                    Some(RegionTypedOwner::ReturnMechanics {
                        source_producer,
                        return_producers,
                    }),
                ) => mechanics_entities.get(producer).is_some_and(|owner| {
                    producer == source_producer
                        && return_producers.as_ref() == owner.return_producers()
                        && owner.source_obligations().contains(&mapping.obligation)
                        && !return_producers.is_empty()
                }),
                (
                    RegionObligationDisposition::AbsorbedIntoFrameMechanics { producer },
                    Some(RegionTypedOwner::FrameMechanics {
                        source_producer,
                        frame_pointer_storage,
                        saved_range,
                        return_producers,
                    }),
                ) => frame_entities.get(producer).is_some_and(|owner| {
                    producer == source_producer
                        && *frame_pointer_storage == owner.frame_pointer_storage()
                        && *saved_range == owner.saved_range()
                        && return_producers.as_ref() == owner.return_producers()
                        && owner.source_obligations().contains(&mapping.obligation)
                        && !return_producers.is_empty()
                }),
                (
                    RegionObligationDisposition::AbsorbedIntoExpression { producer },
                    Some(RegionTypedOwner::PrivateFrameConditionalJoin {
                        producer: owner,
                        role,
                    }),
                ) => {
                    producer == owner
                        && private_roles.get(&mapping.obligation) == Some(role)
                        && matches!(
                            self.ledger.effects(mapping.obligation),
                            [effect]
                                if effect.disposition()
                                    == &EffectDisposition::AbsorbedIntoExpression {
                                        producer: *producer,
                                    }
                                    && effect.expression_evidence().is_some_and(|evidence| {
                                        evidence.entity().producer() == *producer
                                            && evidence
                                                .entity()
                                                .source_obligations()
                                                .contains(&mapping.obligation)
                                    })
                        )
                        && expression_entities.get(producer).is_some_and(|entity| {
                            entity.source_obligations().contains(&mapping.obligation)
                                && match role {
                                    PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadValue {
                                        root,
                                        ..
                                    }
                                    | PrivateFrameConditionalJoinOwnerRole::JoinedLoadValue {
                                        root,
                                        ..
                                    } => entity.root() == *root,
                                    PrivateFrameConditionalJoinOwnerRole::PrivateStackMechanics => {
                                        true
                                    }
                                    _ => false,
                                }
                        })
                }
                (
                    RegionObligationDisposition::AbsorbedIntoStatement { producer },
                    Some(RegionTypedOwner::PrivateFrameConditionalJoin {
                        producer: owner,
                        role,
                    }),
                ) => {
                    let role_access = match role {
                        PrivateFrameConditionalJoinOwnerRole::AuxiliaryStoreMemory { access }
                        | PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadMemory { access }
                        | PrivateFrameConditionalJoinOwnerRole::JoinedTrueStoreMemory { access }
                        | PrivateFrameConditionalJoinOwnerRole::JoinedFalseStoreMemory { access }
                        | PrivateFrameConditionalJoinOwnerRole::JoinedLoadMemory { access } => {
                            Some(*access)
                        }
                        _ => None,
                    };
                    producer == owner
                        && private_roles.get(&mapping.obligation) == Some(role)
                        && matches!(
                            self.ledger.effects(mapping.obligation),
                            [effect]
                                if effect.disposition()
                                    == &EffectDisposition::AbsorbedIntoStatement {
                                        producer: *producer,
                                    }
                                    && effect.statement_evidence()
                                        == statement_entities.get(producer).copied()
                        )
                        && statement_entities.get(producer).is_some_and(|statement| {
                            role_access == Some(statement.access())
                                && statement.source_obligations().contains(&mapping.obligation)
                        })
                }
                (RegionObligationDisposition::Residualized { .. }, None) => true,
                _ => false,
            };
            if !owner_matches {
                invalid.push(format!(
                    "typed output owner does not match obligation {}",
                    mapping.obligation
                ));
            }
        }

        if self.schema_version != CERTIFIED_REGION_SCHEMA_VERSION {
            invalid.push("region schema version mismatch".to_string());
        }
        let mapped_private_roles = self
            .mappings
            .iter()
            .filter_map(|mapping| match &mapping.owner {
                Some(RegionTypedOwner::PrivateFrameConditionalJoin { role, .. }) => {
                    Some((mapping.obligation, role.clone()))
                }
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let expected_private_roles = private_roles
            .iter()
            .filter(|(obligation, _)| expected_obligations.contains(obligation))
            .map(|(obligation, role)| (*obligation, role.clone()))
            .collect::<BTreeMap<_, _>>();
        if mapped_private_roles != expected_private_roles
            || self
                .private_frame_conditional_join
                .as_ref()
                .is_some_and(|authority| {
                    authority.header != self.topology.entry_addr()
                        || authority.stack_pointer_storage.size == 0
                        || authority.reservation_range.size_bytes() == 0
                        || authority.roles.len() != private_roles.len()
                        || !private_role_manifest_is_canonical(&authority.roles)
                })
        {
            invalid
                .push("private-frame conditional-join ownership manifest is not exact".to_string());
        }
        if !self.source.is_complete() {
            invalid.push("retained source obligation inventory is incomplete".to_string());
        }
        if self.scope
			!= SingleBlockAccountingScope::SourceAccountingWithCertifiedSemanticEntitiesAndOpenBlockExit
		{
			invalid.push("single-block accounting scope mismatch".to_string());
		}
        if self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles {
            invalid.push("region identity scope mismatch".to_string());
        }
        if !self
            .origin
            .matches_retained_source(&self.source, &self.topology)
        {
            invalid.push("region artifact origin does not match retained source".to_string());
        }
        if !self.ledger.matches_origin(&self.origin) {
            invalid.push("region obligation ledger does not match artifact origin".to_string());
        }
        let source_instruction_order = self
            .topology
            .blocks()
            .iter()
            .flat_map(|block| block_source_instruction_order(&self.source, block))
            .collect::<Vec<_>>();
        let certified_return_controls = self
            .topology
            .blocks()
            .iter()
            .filter(|block| {
                matches!(
                    block.terminator(),
                    r2cert::CertifiedSourceTerminator::Return
                )
            })
            .filter_map(|block| {
                let producer = block.instructions().last().copied()?;
                let obligation = SemanticObligationId {
                    instruction: producer,
                    kind: SemanticObligationKind::Return,
                    component: SemanticObligationComponent::Whole,
                };
                match self.ledger.effects(obligation) {
                    [effect]
                        if effect.disposition()
                            == &EffectDisposition::AbsorbedIntoReturn { producer }
                            && effect.return_control_evidence().is_some_and(|control| {
                                control.producer() == producer
                                    && control.return_obligation() == obligation
                            }) =>
                    {
                        effect.return_control_evidence()
                    }
                    _ => None,
                }
            })
            .collect::<Vec<_>>();
        let certified_return_order = certified_return_controls
            .iter()
            .map(|control| control.producer())
            .collect::<Vec<_>>();
        let expected_block_mechanics_obligations = mechanics_owners
            .iter()
            .filter(|owner| expected_instructions.contains(&owner.source_producer()))
            .flat_map(|owner| owner.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        if mechanics_entities.len() != mechanics_owners.len()
            || !return_mechanics_manifest_has_exact_order(
                mechanics_owners,
                &source_instruction_order,
                &certified_return_order,
            )
            || mapped_mechanics_obligations != expected_block_mechanics_obligations
            || return_mechanics_obligations.len()
                != mechanics_owners
                    .iter()
                    .map(|owner| owner.source_obligations().len())
                    .sum::<usize>()
        {
            invalid.push("return-mechanics ownership manifest is not exact".to_string());
        }
        for owner in mechanics_owners {
            let source_obligations = self
                .source
                .instructions()
                .get(&owner.source_producer())
                .map(|instruction| instruction.obligations.iter().copied().collect::<Vec<_>>());
            let return_set = owner
                .return_producers()
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            let expected_returns = certified_return_order
                .iter()
                .copied()
                .filter(|producer| return_set.contains(producer))
                .collect::<Vec<_>>();
            let returns_are_grounded = !owner.return_producers().is_empty()
                && owner.return_producers().len() == return_set.len()
                && owner.return_producers() == expected_returns
                && owner.return_producers().iter().all(|return_producer| {
                    let obligation = SemanticObligationId {
                        instruction: *return_producer,
                        kind: SemanticObligationKind::Return,
                        component: SemanticObligationComponent::Whole,
                    };
                    matches!(
                        self.ledger.effects(obligation),
                        [effect]
                            if effect.return_control_evidence().is_some_and(|control| {
                                return_mechanics_reaches_producer(
                                    &self.source,
                                    &self.ledger,
                                    control,
                                    owner.source_producer(),
                                )
                            })
                    )
                });
            let obligations_are_grounded = owner.source_obligations().iter().all(|obligation| {
                let [effect] = self.ledger.effects(*obligation) else {
                    return false;
                };
                match obligation.kind {
                    SemanticObligationKind::LiveValueProducer => {
                        effect.disposition()
                            == &EffectDisposition::AbsorbedIntoExpression {
                                producer: owner.source_producer(),
                            }
                            && effect.expression_evidence().is_some_and(|expression| {
                                expression.entity().producer() == owner.source_producer()
                                    && expression
                                        .entity()
                                        .source_obligations()
                                        .contains(obligation)
                            })
                    }
                    SemanticObligationKind::ObservableMemoryRead => {
                        effect.disposition()
                            == &EffectDisposition::AbsorbedIntoStatement {
                                producer: owner.source_producer(),
                            }
                            && effect.statement_evidence().is_some_and(|statement| {
                                statement.producer() == owner.source_producer()
                                    && statement.source_obligations().contains(obligation)
                            })
                    }
                    _ => false,
                }
            });
            if source_obligations.as_deref() != Some(owner.source_obligations())
                || !returns_are_grounded
                || !obligations_are_grounded
                || expression_entities.contains_key(&owner.source_producer())
                || statement_entities.contains_key(&owner.source_producer())
            {
                invalid.push(format!(
                    "invalid return-mechanics owner for {}",
                    owner.source_producer()
                ));
            }
        }
        let expected_block_frame_obligations = frame_owners
            .iter()
            .filter(|owner| expected_instructions.contains(&owner.source_producer()))
            .flat_map(|owner| owner.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let frame_descriptor = frame_owners
            .first()
            .map(|owner| (owner.frame_pointer_storage(), owner.saved_range()));
        let frame_authority = self.expression_layer.frame_mechanics().authority();
        let exact_frame_services = frame_authority.and_then(|authority| {
            exact_frame_mechanics_services(
                authority,
                &self.source,
                &self.ledger,
                &certified_return_controls,
                &certified_return_order,
            )
        });
        let retained_semantic_frame_producers = self
            .expression_layer
            .entities()
            .iter()
            .map(|entity| entity.producer())
            .chain(statement_entities.keys().copied())
            .collect::<BTreeSet<_>>();
        let frame_candidate_coverage_is_exact =
            exact_frame_services.as_ref().is_some_and(|services| {
                services
                    .keys()
                    .filter(|producer| expected_instructions.contains(producer))
                    .all(|producer| {
                        frame_entities.contains_key(producer)
                            || retained_semantic_frame_producers.contains(producer)
                    })
            }) || (frame_authority.is_none() && frame_owners.is_empty());
        if frame_entities.len() != frame_owners.len()
            || mechanics_entities
                .keys()
                .any(|producer| frame_entities.contains_key(producer))
            || !frame_mechanics_manifest_has_exact_order(
                frame_owners,
                frame_authority,
                exact_frame_services.as_ref(),
                &source_instruction_order,
                &certified_return_order,
            )
            || !frame_candidate_coverage_is_exact
            || mapped_frame_mechanics_obligations != expected_block_frame_obligations
            || frame_mechanics_obligations.len()
                != frame_owners
                    .iter()
                    .map(|owner| owner.source_obligations().len())
                    .sum::<usize>()
            || frame_owners.iter().any(|owner| {
                Some((owner.frame_pointer_storage(), owner.saved_range())) != frame_descriptor
            })
        {
            invalid.push("frame-mechanics ownership manifest is not exact".to_string());
        }
        for owner in frame_owners {
            let source_obligations = self
                .source
                .instructions()
                .get(&owner.source_producer())
                .map(|instruction| instruction.obligations.iter().copied().collect::<Vec<_>>());
            let obligations_are_grounded = owner.source_obligations().iter().all(|obligation| {
                let [effect] = self.ledger.effects(*obligation) else {
                    return false;
                };
                match obligation.kind {
                    SemanticObligationKind::LiveValueProducer => {
                        effect.disposition()
                            == &EffectDisposition::AbsorbedIntoExpression {
                                producer: owner.source_producer(),
                            }
                            && effect.expression_evidence().is_some_and(|expression| {
                                expression.entity().producer() == owner.source_producer()
                                    && expression
                                        .entity()
                                        .source_obligations()
                                        .contains(obligation)
                            })
                    }
                    SemanticObligationKind::ObservableMemoryRead
                    | SemanticObligationKind::ObservableMemoryWrite => {
                        effect.disposition()
                            == &EffectDisposition::AbsorbedIntoStatement {
                                producer: owner.source_producer(),
                            }
                            && effect.statement_evidence().is_some_and(|statement| {
                                statement.producer() == owner.source_producer()
                                    && statement.source_obligations().contains(obligation)
                            })
                    }
                    _ => false,
                }
            });
            if source_obligations.as_deref() != Some(owner.source_obligations())
                || !obligations_are_grounded
                || expression_entities.contains_key(&owner.source_producer())
                || statement_entities.contains_key(&owner.source_producer())
            {
                invalid.push(format!(
                    "invalid frame-mechanics owner for {}",
                    owner.source_producer()
                ));
            }
        }
        if self.topology.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || source_block.is_none_or(|block| {
                block_source_instruction_order(&self.source, block)
                    != self
                        .instructions
                        .iter()
                        .map(|instruction| instruction.source)
                        .collect::<Vec<_>>()
            })
        {
            invalid.push("region instructions do not match retained source topology".to_string());
        }
        if self.expression_layer.entities().len() != expression_entities.len()
            || actual_expression_producers != expected_expression_producers
        {
            invalid.push(
                "semantic expression producer set does not match retained source".to_string(),
            );
        }
        if entity_expression_obligations != expected_expression_obligations
            || mapped_expression_obligations != expected_block_expression_obligations
        {
            invalid.push(
                "semantic expression obligations do not exactly match retained source".to_string(),
            );
        }
        if statement_entities.len() != self.memory_statements.len()
            || statement_obligations != mapped_statement_obligations
            || !statement_obligations.is_subset(&expected_obligations)
        {
            invalid.push(
                "certified memory statements do not exactly match selected mappings".to_string(),
            );
        }
        if direct_call_entities.len() != self.direct_calls.len()
            || semantic_call_entities.len() != self.semantic_calls.len()
            || direct_call_entities
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != semantic_call_entities
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
            || call_obligations != mapped_call_obligations
            || !call_obligations.is_subset(&expected_obligations)
        {
            invalid
                .push("certified direct calls do not exactly match selected mappings".to_string());
        }
        for (producer, call) in &direct_call_entities {
            let source_interface = self
                .origin
                .machine_context()
                .source()
                .call_site_interface(call.call_site());
            let semantic_matches = semantic_call_entities
                .get(producer)
                .is_some_and(|semantic| {
                    semantic.call_site() == call.call_site()
                        && semantic.raw_identity() == call.raw_identity()
                        && semantic.interface_revision() == call.interface_revision()
                        && semantic.target_binding() == call.target_value().binding()
                        && semantic.target() == call.target()
                        && semantic.fallthrough() == call.fallthrough()
                        && semantic.calling_convention() == call.calling_convention()
                        && semantic.source_obligations() == &call.source_obligations()
                        && semantic.arguments().len() == call.arguments().len()
                        && semantic.arguments().iter().zip(call.arguments()).all(
                            |(semantic_argument, certified_argument)| {
                                semantic_argument.slot() == certified_argument.slot()
                                    // A preserved-entry argument names no
                                    // value, so this region cannot match one
                                    // against a semantic argument yet.
                                    && certified_argument.value().is_some_and(|certified_value| {
                                        semantic_argument.binding() == certified_value.binding()
                                            && semantic_argument.ty() == certified_value.ty()
                                    })
                                    && match (
                                        semantic_argument.value(),
                                        certified_argument.origin(),
                                    ) {
                                        (
                                            SemanticCCallArgumentValue::Expression(expression),
                                            CertifiedCallArgumentOrigin::Produced {
                                                producer: argument_producer,
                                            },
                                        ) => expression_entities
                                            .get(argument_producer)
                                            .is_some_and(|entity| {
                                                entity.root() == *expression
                                                    && entity.output()
                                                        == semantic_argument.binding()
                                            }),
                                        (
                                            SemanticCCallArgumentValue::Constant(actual),
                                            CertifiedCallArgumentOrigin::Constant { value },
                                        ) => actual == value,
                                        (
                                            SemanticCCallArgumentValue::AbiParameter {
                                                index: actual,
                                                input,
                                            },
                                            CertifiedCallArgumentOrigin::AbiParameter {
                                                index: expected,
                                            },
                                        ) => {
                                            actual == expected
                                                && self
                                                    .expression_layer
                                                    .function_interface()
                                                    .is_some_and(|interface| {
                                                        interface
                                                            .parameters()
                                                            .get(*actual as usize)
                                                            .is_some_and(|parameter| {
                                                                parameter.index() == *actual
                                                                    && parameter.value()
                                                                        == Some(*input)
                                                            })
                                                    })
                                        }
                                        _ => false,
                                    }
                            },
                        )
                });
            let source_interface_matches = source_interface.is_some_and(|interface| {
                interface.identity() == call.raw_identity()
                    && interface.revision_identity() == call.interface_revision()
                    && interface.calling_convention() == call.calling_convention()
                    && interface.arguments().len() == call.arguments().len()
                    && interface.arguments().iter().zip(call.arguments()).all(
                        |(expected, argument)| {
                            argument.slot()
                                == (r2ssa::CallBoundarySlot::Register {
                                    index: expected.index(),
                                    storage: expected.storage(),
                                })
                        },
                    )
                    && matches!(interface.result(), r2ssa::SourceCallResult::Void)
                    && interface.is_complete()
                    && !interface.is_variadic()
                    && !interface.is_noreturn()
            });
            if !semantic_matches || !source_interface_matches {
                invalid.push(format!(
                    "semantic direct call does not match certified call for {producer}"
                ));
            }
        }
        if direct_control_entities.len() != self.direct_controls.len()
            || conditional_control_entities.len() != self.conditional_controls.len()
            || switch_control_entities.len() != self.switch_controls.len()
            || direct_control_entities.keys().any(|producer| {
                conditional_control_entities.contains_key(producer)
                    || switch_control_entities.contains_key(producer)
            })
            || conditional_control_entities
                .keys()
                .any(|producer| switch_control_entities.contains_key(producer))
            || control_obligations.len()
                != self
                    .direct_controls
                    .len()
                    .saturating_add(self.conditional_controls.len().saturating_mul(2))
                    .saturating_add(self.switch_controls.len())
            || control_obligations != mapped_control_obligations
            || !control_obligations.is_subset(&expected_obligations)
        {
            invalid.push(
                "certified terminal controls do not exactly match selected mappings".to_string(),
            );
        }
        for control in &self.switch_controls {
            let effects = self.ledger.effects(control.source_obligation());
            if !matches!(
                effects,
                [effect]
                    if effect.disposition()
                        == &(EffectDisposition::AbsorbedIntoControl {
                            producer: control.producer(),
                        })
                        && effect.switch_control_evidence() == Some(control)
            ) {
                invalid.push(format!(
                    "switch control does not match certified ledger evidence for {}",
                    control.producer()
                ));
            }
        }
        if return_control_entities.len() != self.return_controls.len()
            || return_obligations != mapped_return_obligations
            || !return_obligations.is_subset(&expected_obligations)
            || semantic_return_entities.len() != self.semantic_returns.len()
            || semantic_return_entities
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != return_control_entities
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
        {
            invalid.push("certified returns do not exactly match selected mappings".to_string());
        }
        for (producer, control) in &return_control_entities {
            let semantic_matches = semantic_return_entities
                .get(producer)
                .is_some_and(|returned| {
                    semantic_return_matches_control(returned, control, &self.expression_layer)
                });
            if !semantic_matches {
                invalid.push(format!(
                    "semantic return does not match certified return for {producer}"
                ));
            }
        }
        if self.expression_layer.schema_version() != SEMANTIC_C_SCHEMA_VERSION
            || self.expression_layer.scope() != SemanticCScope::LiveValueExpressionsOnly
            || self.expression_layer.identity_scope() != self.identity_scope
        {
            invalid.push("nested semantic expression layer contract mismatch".to_string());
        }
        for entity in self.expression_layer.entities() {
            let expected = self
                .source
                .instructions()
                .get(&entity.producer())
                .map(|instruction| {
                    instruction
                        .obligations
                        .iter()
                        .copied()
                        .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                        .collect::<BTreeSet<_>>()
                });
            if expected.as_ref() != Some(entity.source_obligations())
                || entity
                    .source_obligations()
                    .iter()
                    .any(|id| id.instruction != entity.producer())
            {
                invalid.push(format!(
                    "semantic expression obligations are misbound for {}",
                    entity.producer()
                ));
            }
        }
        if self
            .instructions
            .iter()
            .map(|instruction| &instruction.source)
            .any(|id| id.block_addr != self.block_addr)
        {
            invalid.push("region block address does not match its source instructions".to_string());
        }
        for instruction in &self.instructions {
            if self
                .source
                .instructions()
                .get(&instruction.source)
                .map(|expected| expected.state)
                != Some(instruction.state)
            {
                invalid.push(format!(
                    "source instruction state mismatch for {}",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.expression_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoExpression {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "expression producer for {} has no live-value mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.statement_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoStatement {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "statement producer for {} has no memory mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.call_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoCall {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "call producer for {} has no call-boundary mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.control_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoControl {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "control producer for {} has no transfer mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.return_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoReturn {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "return producer for {} has no return mapping",
                    instruction.source
                ));
            }
            match (
                instruction.expression_producer,
                expression_entities.get(&instruction.source),
            ) {
                (Some(producer), Some(entity)) if entity.producer() == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "expression producer for {} is not bound to its semantic entity",
                    instruction.source
                )),
            }
            match (
                instruction.statement_producer,
                statement_entities.get(&instruction.source),
            ) {
                (Some(producer), Some(statement)) if statement.producer() == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "statement producer for {} is not bound to its certified memory statement",
                    instruction.source
                )),
            }
            match (
                instruction.call_producer,
                direct_call_entities
                    .get(&instruction.source)
                    .map(|call| call.producer()),
            ) {
                (Some(producer), Some(entity_producer)) if entity_producer == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "call producer for {} is not bound to its certified direct call",
                    instruction.source
                )),
            }
            match (
                instruction.control_producer,
                direct_control_entities
                    .get(&instruction.source)
                    .map(|control| control.producer())
                    .or_else(|| {
                        conditional_control_entities
                            .get(&instruction.source)
                            .map(|control| control.producer())
                    })
                    .or_else(|| {
                        switch_control_entities
                            .get(&instruction.source)
                            .map(|control| control.producer())
                    }),
            ) {
                (Some(producer), Some(entity_producer)) if entity_producer == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "control producer for {} is not bound to its certified terminal transfer",
                    instruction.source
                )),
            }
            match (
                instruction.return_producer,
                return_control_entities
                    .get(&instruction.source)
                    .map(|control| control.producer()),
            ) {
                (Some(producer), Some(entity_producer)) if entity_producer == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "return producer for {} is not bound to its certified return",
                    instruction.source
                )),
            }
        }
        for mapping in &self.mappings {
            match mapping.disposition {
                RegionObligationDisposition::AbsorbedIntoExpression { producer } => {
                    let entity_matches = expression_entities.get(&producer).is_some_and(|entity| {
                        entity.source_obligations().contains(&mapping.obligation)
                    });
                    if mapping.obligation.kind != SemanticObligationKind::LiveValueProducer
                        || producer != mapping.obligation.instruction
                        || !entity_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.expression_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid expression mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoStatement { producer } => {
                    let statement_matches =
                        statement_entities.get(&producer).is_some_and(|statement| {
                            statement.source_obligations().contains(&mapping.obligation)
                        });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoStatement { producer }
                                && effect.statement_evidence() == statement_entities
                                    .get(&producer)
                                    .copied()
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::ObservableMemoryRead
                            | SemanticObligationKind::ObservableMemoryWrite
                    ) || producer != mapping.obligation.instruction
                        || !statement_matches
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.statement_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid memory-statement mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoFrameMechanics { producer } => {
                    let owner_matches = matches!(
                        &mapping.owner,
                        Some(RegionTypedOwner::FrameMechanics {
                            source_producer,
                            frame_pointer_storage,
                            saved_range,
                            return_producers,
                        }) if producer == *source_producer
                            && frame_entities.get(&producer).is_some_and(|owner| {
                                owner.frame_pointer_storage() == *frame_pointer_storage
                                    && owner.saved_range() == *saved_range
                                    && owner.return_producers() == return_producers.as_ref()
                                    && owner.source_obligations().contains(&mapping.obligation)
                            })
                    );
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if match mapping.obligation.kind {
                                SemanticObligationKind::LiveValueProducer => {
                                    effect.disposition()
                                        == &EffectDisposition::AbsorbedIntoExpression { producer }
                                        && effect.expression_evidence().is_some_and(|expression| {
                                            expression.entity().producer() == producer
                                                && expression
                                                    .entity()
                                                    .source_obligations()
                                                    .contains(&mapping.obligation)
                                        })
                                }
                                SemanticObligationKind::ObservableMemoryRead
                                | SemanticObligationKind::ObservableMemoryWrite => {
                                    effect.disposition()
                                        == &EffectDisposition::AbsorbedIntoStatement { producer }
                                        && effect.statement_evidence().is_some_and(|statement| {
                                            statement.producer() == producer
                                                && statement
                                                    .source_obligations()
                                                    .contains(&mapping.obligation)
                                        })
                                }
                                _ => false,
                            }
                    );
                    if producer != mapping.obligation.instruction
                        || !owner_matches
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.expression_producer.is_none()
                                && instruction.statement_producer.is_none()
                        })
                    {
                        invalid.push(format!(
                            "invalid frame-mechanics mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoCall { producer } => {
                    let call_matches = direct_call_entities.get(&producer).is_some_and(|call| {
                        call.source_obligations().contains(&mapping.obligation)
                            && self.source_block().is_some_and(|block| {
                                matches!(
                                    block.terminator(),
                                    r2cert::CertifiedSourceTerminator::Call {
                                        target,
                                        fallthrough: Some(fallthrough),
                                    } if *target == call.target()
                                        && *fallthrough == call.fallthrough()
                                ) && block.successors() == [call.fallthrough()]
                                    && self.topology.block(call.fallthrough()).is_some()
                                    && block.addr() != call.fallthrough()
                                    && block.instructions().last() == Some(&producer)
                            })
                    });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoCall { producer }
                                && effect.direct_call_evidence()
                                    == direct_call_entities.get(&producer).copied()
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::Call | SemanticObligationKind::CallArgument
                    ) || producer != mapping.obligation.instruction
                        || !call_matches
                        || !ledger_matches
                        || !semantic_call_entities.contains_key(&producer)
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.call_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid direct-call mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoControl { producer } => {
                    let direct_matches =
                        direct_control_entities
                            .get(&producer)
                            .is_some_and(|control| {
                                control.source_obligation() == mapping.obligation
                                    && self.source_block().is_some_and(|block| {
                                        matches!(
                                                block.terminator(),
                                                r2cert::CertifiedSourceTerminator::Branch { target }
                                                    if *target == control.target()
                                        ) && block.successors() == [control.target()]
                                            && self.topology.block(control.target()).is_some()
                                            && block.addr() != control.target()
                                            && block.instructions().last() == Some(&producer)
                                    })
                            });
                    let conditional_matches = conditional_control_entities
                        .get(&producer)
                        .is_some_and(|control| {
                            let successors = self.source_block().map(|block| {
                                block.successors().iter().copied().collect::<BTreeSet<_>>()
                            });
                            let expected_successors =
                                BTreeSet::from([control.true_target(), control.false_target()]);
                            let values_are_grounded = [control.target_value(), control.condition()]
                                .into_iter()
                                .all(|value| {
                                    value.producer().is_none_or(|value_producer| {
                                        expression_entities.get(&value_producer).is_some_and(
                                            |entity| entity.output() == value.binding(),
                                        )
                                    })
                                });
                            let source_obligations_match = self
                                .source
                                .obligations()
                                .get(&control.predicate_obligation())
                                .is_some_and(|obligation| {
                                    obligation.inputs == [control.condition().binding().value()]
                                })
                                && self
                                    .source
                                    .obligations()
                                    .get(&control.transfer_obligation())
                                    .is_some_and(|obligation| {
                                        obligation.inputs
                                            == [
                                                control.target_value().binding().value(),
                                                control.condition().binding().value(),
                                            ]
                                    });
                            control.source_obligations().contains(&mapping.obligation)
                                && control.source_obligations().len() == 2
                                && control.condition().binding().width_bits() == 8
                                && control.truthiness() == CertifiedControlTruthiness::NonZeroIsTrue
                                && values_are_grounded
                                && source_obligations_match
                                && control.true_target() != control.false_target()
                                && self.source_block().is_some_and(|block| {
                                    matches!(
                                        block.terminator(),
                                        r2cert::CertifiedSourceTerminator::ConditionalBranch {
                                            true_target,
                                            false_target,
                                        } if *true_target == control.true_target()
                                            && *false_target == control.false_target()
                                    ) && successors.as_ref() == Some(&expected_successors)
                                        && block.successors().len() == 2
                                        && block.addr() != control.true_target()
                                        && block.addr() != control.false_target()
                                        && self.topology.block(control.true_target()).is_some()
                                        && self.topology.block(control.false_target()).is_some()
                                        && block.instructions().last() == Some(&producer)
                                })
                        });
                    let switch_matches =
                        switch_control_entities
                            .get(&producer)
                            .is_some_and(|control| {
                                let topology = control.topology();
                                control.source_obligation() == mapping.obligation
                                    && control.origin() == &self.origin
                                    && self.source_block().is_some_and(|block| {
                                        matches!(
                                            block.terminator(),
                                            r2cert::CertifiedSourceTerminator::Switch {
                                                switch_addr,
                                                terminal_instruction_addr,
                                                min_value,
                                                max_value,
                                                cases,
                                                default,
                                            } if *switch_addr == topology.switch_addr()
                                                && switch_addr == terminal_instruction_addr
                                                && *min_value == topology.min_value()
                                                && *max_value == topology.max_value()
                                                && cases.as_ref() == topology.cases()
                                                && *default == Some(topology.default_target())
                                        ) && block.instructions().last() == Some(&producer)
                                    })
                            });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoControl { producer }
                                && ((direct_matches
                                    && effect.direct_control_evidence()
                                        == direct_control_entities.get(&producer).copied())
                                    || (conditional_matches
                                        && effect.conditional_control_evidence()
                                            == conditional_control_entities
                                                .get(&producer)
                                                .copied())
                                    || (switch_matches
                                        && effect.switch_control_evidence()
                                            == switch_control_entities.get(&producer).copied()))
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::ControlPredicate
                            | SemanticObligationKind::ControlTransfer
                    ) || producer != mapping.obligation.instruction
                        || usize::from(direct_matches)
                            + usize::from(conditional_matches)
                            + usize::from(switch_matches)
                            != 1
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.control_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid terminal-control mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoReturn { producer } => {
                    if let Some(RegionTypedOwner::ReturnMechanics {
                        source_producer,
                        return_producers,
                    }) = &mapping.owner
                    {
                        let mechanics_matches = producer == *source_producer
                            && mechanics_entities.get(&producer).is_some_and(|owner| {
                                owner.return_producers() == return_producers.as_ref()
                                    && owner.source_obligations().contains(&mapping.obligation)
                            });
                        let ledger_matches = matches!(
                            self.ledger.effects(mapping.obligation),
                            [effect]
                                if match mapping.obligation.kind {
                                    SemanticObligationKind::LiveValueProducer => {
                                        effect.disposition()
                                            == &EffectDisposition::AbsorbedIntoExpression {
                                                producer,
                                            }
                                            && effect.expression_evidence().is_some_and(|expression| {
                                                expression.entity().producer() == producer
                                                    && expression
                                                        .entity()
                                                        .source_obligations()
                                                        .contains(&mapping.obligation)
                                            })
                                    }
                                    SemanticObligationKind::ObservableMemoryRead => {
                                        effect.disposition()
                                            == &EffectDisposition::AbsorbedIntoStatement {
                                                producer,
                                            }
                                            && effect.statement_evidence().is_some_and(|statement| {
                                                statement.producer() == producer
                                                    && statement
                                                        .source_obligations()
                                                        .contains(&mapping.obligation)
                                            })
                                    }
                                    _ => false,
                                }
                        );
                        if !mechanics_matches
                            || !ledger_matches
                            || !self.instructions.iter().any(|instruction| {
                                instruction.source == producer
                                    && instruction.expression_producer.is_none()
                                    && instruction.statement_producer.is_none()
                            })
                        {
                            invalid.push(format!(
                                "invalid return-mechanics mapping for {}",
                                mapping.obligation
                            ));
                        }
                        continue;
                    }
                    let return_matches =
                        return_control_entities
                            .get(&producer)
                            .is_some_and(|control| {
                                let values_are_grounded = control.values().iter().all(|returned| {
                                    returned.value().producer().is_some_and(|value_producer| {
                                        expression_entities.get(&value_producer).is_some_and(
                                            |entity| entity.output() == returned.value().binding(),
                                        )
                                    })
                                });
                                let compositions_are_grounded =
                                    control.register_compositions().iter().all(|composition| {
                                        std::iter::once(composition.base())
                                            .chain(
                                                composition
                                                    .overlays()
                                                    .iter()
                                                    .map(|overlay| overlay.definition()),
                                            )
                                            .all(|definition| {
                                                definition.value().producer()
                                                    == Some(definition.producer())
                                                    && expression_entities
                                                        .get(&definition.producer())
                                                        .is_some_and(|entity| {
                                                            entity.output()
                                                                == definition.value().binding()
                                                        })
                                            })
                                    });
                                control.source_obligations().contains(&mapping.obligation)
                                    && values_are_grounded
                                    && compositions_are_grounded
                                    && self.source_block().is_some_and(|block| {
                                        matches!(
                                            block.terminator(),
                                            r2cert::CertifiedSourceTerminator::Return
                                        ) && block.successors().is_empty()
                                            && block.instructions().last() == Some(&producer)
                                    })
                            });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoReturn { producer }
                                && effect.return_control_evidence()
                                    == return_control_entities.get(&producer).copied()
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
                    ) || producer != mapping.obligation.instruction
                        || !return_matches
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.return_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid terminal-return mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::Residualized { reason } => {
                    if reason != residual_reason(mapping.obligation.kind) {
                        invalid.push(format!("wrong residual reason for {}", mapping.obligation));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoStatement { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "statement-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoCall { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "call-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoControl { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "control-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoReturn { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "return-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                }
            }
        }
        let residual_set = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::Residualized { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let closed_set = mapped_expression_obligations
            .union(&mapped_statement_obligations)
            .copied()
            .chain(mapped_call_obligations.iter().copied())
            .chain(mapped_control_obligations.iter().copied())
            .chain(mapped_return_obligations.iter().copied())
            .chain(mapped_mechanics_obligations.iter().copied())
            .chain(mapped_frame_mechanics_obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let expected_residual_set = expected_obligations
            .difference(&closed_set)
            .copied()
            .collect::<BTreeSet<_>>();
        if residual_set != expected_residual_set {
            invalid.push(
                "region residual mappings do not equal the unowned selected obligations"
                    .to_string(),
            );
        }

        RegionAuditReport {
            missing_instructions,
            duplicate_instructions,
            unexpected_instructions,
            missing_obligations,
            duplicate_obligations,
            unexpected_obligations,
            invalid,
            residualized_obligations: residual_set.into_iter().collect(),
        }
    }
}

fn ledger_mapping_for_typed_owner(
    ledger: &ObligationLedger,
    mapping: &RegionObligationMapping,
) -> Option<TypedRegionMapping> {
    if matches!(
        &mapping.owner,
        Some(
            RegionTypedOwner::ReturnMechanics { .. }
                | RegionTypedOwner::FrameMechanics { .. }
                | RegionTypedOwner::PrivateFrameConditionalJoin { .. }
        )
    ) {
        let [effect] = ledger.effects(mapping.obligation) else {
            return None;
        };
        return Some(TypedRegionMapping::new(
            mapping.obligation,
            effect.disposition().clone(),
        ));
    }
    let disposition = match mapping.disposition {
        RegionObligationDisposition::AbsorbedIntoExpression { producer } => {
            EffectDisposition::AbsorbedIntoExpression { producer }
        }
        RegionObligationDisposition::AbsorbedIntoStatement { producer } => {
            EffectDisposition::AbsorbedIntoStatement { producer }
        }
        RegionObligationDisposition::AbsorbedIntoFrameMechanics { .. } => return None,
        RegionObligationDisposition::AbsorbedIntoCall { producer } => {
            EffectDisposition::AbsorbedIntoCall { producer }
        }
        RegionObligationDisposition::AbsorbedIntoControl { producer } => {
            EffectDisposition::AbsorbedIntoControl { producer }
        }
        RegionObligationDisposition::AbsorbedIntoReturn { producer } => {
            EffectDisposition::AbsorbedIntoReturn { producer }
        }
        RegionObligationDisposition::Residualized { .. } => return None,
    };
    Some(TypedRegionMapping::new(mapping.obligation, disposition))
}

fn exact_typed_output_manifest<'a>(
    origin: &CertifiedArtifactOrigin,
    accountings: impl IntoIterator<Item = &'a CertifiedSingleBlockAccounting>,
) -> Result<(Vec<RegionObligationMapping>, Vec<TypedRegionMapping>), TypedOutputSealError> {
    let accountings = accountings.into_iter().collect::<Vec<_>>();
    if accountings.is_empty() {
        return Err(TypedOutputSealError::EmptyAccountingSet);
    }
    let mut mappings = Vec::new();
    let mut ledger_mappings = Vec::new();
    for accounting in accountings {
        if accounting.origin() != origin || !accounting.ledger().matches_origin(origin) {
            return Err(TypedOutputSealError::ArtifactOriginMismatch);
        }
        let report = accounting.audit();
        if !report.has_exact_source_accounting() {
            return Err(TypedOutputSealError::InexactAccounting);
        }
        for mapping in accounting.mappings() {
            if matches!(
                mapping.disposition(),
                RegionObligationDisposition::Residualized { .. }
            ) {
                return Err(TypedOutputSealError::ResidualMapping(mapping.obligation()));
            }
            if mapping.owner().is_none() {
                return Err(TypedOutputSealError::MissingTypedOwner(
                    mapping.obligation(),
                ));
            }
            let ledger_mapping = ledger_mapping_for_typed_owner(accounting.ledger(), mapping)
                .ok_or(TypedOutputSealError::ResidualMapping(mapping.obligation()))?;
            mappings.push(mapping.clone());
            ledger_mappings.push(ledger_mapping);
        }
    }

    let expected = origin
        .source()
        .obligations()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let counts = counts(mappings.iter().map(RegionObligationMapping::obligation));
    let actual = counts.keys().copied().collect::<BTreeSet<_>>();
    if actual != expected
        || mappings.len() != expected.len()
        || counts.values().any(|count| *count != 1)
    {
        return Err(TypedOutputSealError::IncompleteManifest);
    }
    Ok((mappings, ledger_mappings))
}

impl CertifiedTypedOutputSeal {
    pub(crate) fn new<'a>(
        ledger_closure: CertifiedLedgerClosure,
        region_kind: CertifiedTypedRegionKind,
        region_schema_version: u32,
        accountings: impl IntoIterator<Item = &'a CertifiedSingleBlockAccounting>,
    ) -> Result<Self, TypedOutputSealError> {
        let accountings = accountings.into_iter().collect::<Vec<_>>();
        let (mappings, ledger_mappings) =
            exact_typed_output_manifest(ledger_closure.origin(), accountings.iter().copied())?;
        if !ledger_closure.matches_ledger(
            ledger_closure.origin(),
            region_kind,
            region_schema_version,
            &ledger_mappings,
        ) {
            return Err(TypedOutputSealError::LedgerClosureMismatch);
        }
        Ok(Self {
            schema_version: CERTIFIED_REGION_SCHEMA_VERSION,
            ledger_closure,
            mappings: mappings.into_boxed_slice(),
        })
    }

    pub(crate) const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub(crate) fn matches_region<'a>(
        &self,
        origin: &CertifiedArtifactOrigin,
        region_kind: CertifiedTypedRegionKind,
        region_schema_version: u32,
        accountings: impl IntoIterator<Item = &'a CertifiedSingleBlockAccounting>,
    ) -> bool {
        let accountings = accountings.into_iter().collect::<Vec<_>>();
        let Ok((mappings, ledger_mappings)) =
            exact_typed_output_manifest(origin, accountings.iter().copied())
        else {
            return false;
        };
        self.schema_version == CERTIFIED_REGION_SCHEMA_VERSION
            && self.mappings.as_ref() == mappings.as_slice()
            && self.ledger_closure.matches_ledger(
                origin,
                region_kind,
                region_schema_version,
                &ledger_mappings,
            )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RegionAuditReport {
    missing_instructions: Vec<CanonicalInstructionId>,
    duplicate_instructions: Vec<CanonicalInstructionId>,
    unexpected_instructions: Vec<CanonicalInstructionId>,
    missing_obligations: Vec<SemanticObligationId>,
    duplicate_obligations: Vec<SemanticObligationId>,
    unexpected_obligations: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    residualized_obligations: Vec<SemanticObligationId>,
}

impl RegionAuditReport {
    pub fn has_exact_source_accounting(&self) -> bool {
        self.missing_instructions.is_empty()
            && self.duplicate_instructions.is_empty()
            && self.unexpected_instructions.is_empty()
            && self.missing_obligations.is_empty()
            && self.duplicate_obligations.is_empty()
            && self.unexpected_obligations.is_empty()
            && self.invalid.is_empty()
    }

    pub fn missing_obligations(&self) -> &[SemanticObligationId] {
        &self.missing_obligations
    }

    pub fn missing_instructions(&self) -> &[CanonicalInstructionId] {
        &self.missing_instructions
    }

    pub fn duplicate_instructions(&self) -> &[CanonicalInstructionId] {
        &self.duplicate_instructions
    }

    pub fn unexpected_instructions(&self) -> &[CanonicalInstructionId] {
        &self.unexpected_instructions
    }

    pub fn duplicate_obligations(&self) -> &[SemanticObligationId] {
        &self.duplicate_obligations
    }

    pub fn unexpected_obligations(&self) -> &[SemanticObligationId] {
        &self.unexpected_obligations
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn residualized_obligations(&self) -> &[SemanticObligationId] {
        &self.residualized_obligations
    }

    /// Whether selected source obligations remain residual. This does not
    /// describe block-exit or successor-port openness.
    pub fn has_residuals(&self) -> bool {
        !self.residualized_obligations.is_empty()
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

fn reconcile<T: Copy + Ord>(
    expected: impl IntoIterator<Item = T>,
    actual: &BTreeMap<T, usize>,
) -> (Vec<T>, Vec<T>, Vec<T>) {
    let expected = expected.into_iter().collect::<BTreeSet<_>>();
    let missing = expected
        .iter()
        .copied()
        .filter(|value| !actual.contains_key(value))
        .collect();
    let duplicate = actual
        .iter()
        .filter_map(|(value, count)| (*count > 1).then_some(*value))
        .collect();
    let unexpected = actual
        .keys()
        .copied()
        .filter(|value| !expected.contains(value))
        .collect();
    (missing, duplicate, unexpected)
}

fn residual_reason(kind: SemanticObligationKind) -> RegionResidualReason {
    match kind {
        SemanticObligationKind::ObservableMemoryRead
        | SemanticObligationKind::ObservableMemoryWrite => {
            RegionResidualReason::MemoryEffectRequiresCertifiedStatement
        }
        SemanticObligationKind::Call
        | SemanticObligationKind::CallArgument
        | SemanticObligationKind::CallResult => {
            RegionResidualReason::CallBoundaryRequiresCertifiedCall
        }
        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
            RegionResidualReason::ReturnRequiresCertifiedControl
        }
        SemanticObligationKind::ControlPredicate | SemanticObligationKind::ControlTransfer => {
            RegionResidualReason::ControlRequiresCertifiedRegion
        }
        SemanticObligationKind::Trap
        | SemanticObligationKind::Atomicity
        | SemanticObligationKind::MemoryOrdering => {
            RegionResidualReason::TrapOrOrderingRequiresCertifiedEffect
        }
        SemanticObligationKind::VolatileOrUnknownEffect => {
            RegionResidualReason::UnsupportedSourceSemantics
        }
        SemanticObligationKind::LoopCarriedState | SemanticObligationKind::LiveStateTransition => {
            RegionResidualReason::LoopStateRequiresCertifiedStructuring
        }
        SemanticObligationKind::LiveValueProducer => {
            RegionResidualReason::UnsupportedSourceSemantics
        }
    }
}

#[cfg(test)]
mod return_mechanics_manifest_tests {
    use super::*;
    use r2ssa::{CanonicalInstructionSite, InstId};

    fn id(ordinal: u64) -> CanonicalInstructionId {
        CanonicalInstructionId {
            block_addr: 0x2000,
            site: CanonicalInstructionSite::Op(ordinal),
        }
    }

    fn block_id(block_addr: u64, ordinal: u64) -> CanonicalInstructionId {
        CanonicalInstructionId {
            block_addr,
            site: CanonicalInstructionSite::Op(ordinal),
        }
    }

    fn owner(
        source_producer: CanonicalInstructionId,
        return_producers: impl IntoIterator<Item = CanonicalInstructionId>,
    ) -> SemanticCReturnMechanicsOwner {
        SemanticCReturnMechanicsOwner {
            source_producer,
            return_producers: return_producers
                .into_iter()
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            source_obligations: Vec::new().into_boxed_slice(),
        }
    }

    fn obligation(
        producer: CanonicalInstructionId,
        kind: SemanticObligationKind,
    ) -> SemanticObligationId {
        SemanticObligationId {
            instruction: producer,
            kind,
            component: SemanticObligationComponent::Whole,
        }
    }

    #[test]
    fn private_join_role_manifest_refuses_reorder_duplicate_and_wrong_effect_class() {
        let store = obligation(id(0), SemanticObligationKind::ObservableMemoryWrite);
        let load = obligation(id(1), SemanticObligationKind::ObservableMemoryRead);
        let mechanics = obligation(id(2), SemanticObligationKind::LiveValueProducer);
        let store_role = PrivateFrameConditionalJoinOwnerRole::AuxiliaryStoreMemory {
            access: StructuredAccessId {
                inst: InstId(4),
                ordinal: 0,
            },
        };
        let load_role = PrivateFrameConditionalJoinOwnerRole::AuxiliaryLoadMemory {
            access: StructuredAccessId {
                inst: InstId(7),
                ordinal: 0,
            },
        };
        let canonical = [
            (store, store_role.clone()),
            (load, load_role.clone()),
            (
                mechanics,
                PrivateFrameConditionalJoinOwnerRole::PrivateStackMechanics,
            ),
        ];
        assert!(private_role_manifest_is_canonical(&canonical));
        assert!(!private_role_manifest_is_canonical(&[
            (load, load_role.clone()),
            (store, store_role.clone()),
        ]));
        assert!(!private_role_manifest_is_canonical(&[
            (store, store_role.clone()),
            (store, store_role),
        ]));
        assert!(!private_role_manifest_is_canonical(&[(
            store,
            PrivateFrameConditionalJoinOwnerRole::PrivateStackMechanics,
        )]));
    }

    #[test]
    fn visible_expression_closure_is_transitive_and_stops_at_composite_boundaries() {
        let root = id(10);
        let middle = id(11);
        let leaf = id(12);
        let dependencies = BTreeMap::from([
            (root, BTreeSet::from([middle])),
            (middle, BTreeSet::from([leaf])),
            (leaf, BTreeSet::new()),
        ]);
        assert_eq!(
            exact_visible_expression_closure([root], &BTreeSet::new(), &dependencies),
            Some(BTreeSet::from([root, middle, leaf]))
        );

        let rewritten_load = id(20);
        let private_address = id(21);
        let bounded = BTreeMap::from([
            (root, BTreeSet::from([rewritten_load])),
            (rewritten_load, BTreeSet::from([private_address])),
        ]);
        assert_eq!(
            exact_visible_expression_closure([root], &BTreeSet::from([rewritten_load]), &bounded,),
            Some(BTreeSet::from([root]))
        );
        assert_eq!(
            exact_visible_expression_closure(
                [rewritten_load],
                &BTreeSet::from([rewritten_load]),
                &BTreeMap::new(),
            ),
            Some(BTreeSet::new())
        );
    }

    #[test]
    fn visible_expression_closure_keeps_shared_mechanics_dependencies_visible() {
        let root = id(25);
        let shared_mechanics = id(26);
        let rewritten_load = id(27);
        let private_address = id(28);
        let dependencies = BTreeMap::from([
            (root, BTreeSet::from([shared_mechanics, rewritten_load])),
            (shared_mechanics, BTreeSet::new()),
            (rewritten_load, BTreeSet::from([private_address])),
        ]);
        assert_eq!(
            exact_visible_expression_closure(
                [root],
                &BTreeSet::from([rewritten_load]),
                &dependencies,
            ),
            Some(BTreeSet::from([root, shared_mechanics]))
        );
    }

    #[test]
    fn visible_expression_closure_refuses_missing_and_cyclic_dependencies() {
        let root = id(30);
        let missing = id(31);
        assert_eq!(
            exact_visible_expression_closure(
                [root],
                &BTreeSet::new(),
                &BTreeMap::from([(root, BTreeSet::from([missing]))]),
            ),
            None
        );
        assert_eq!(
            exact_visible_expression_closure(
                [root],
                &BTreeSet::new(),
                &BTreeMap::from([
                    (root, BTreeSet::from([missing])),
                    (missing, BTreeSet::from([root])),
                ]),
            ),
            None
        );
        assert_eq!(
            exact_visible_expression_closure([root], &BTreeSet::new(), &BTreeMap::new()),
            None
        );
    }

    #[test]
    fn return_mechanics_manifest_refuses_duplicate_reorder_and_owner_mutation() {
        let first = id(0);
        let second = id(1);
        let first_return = id(2);
        let second_return = id(3);
        let source_order = [first, second, first_return, second_return];
        let return_order = [first_return, second_return];
        let canonical = [
            owner(first, [first_return, second_return]),
            owner(second, [second_return]),
        ];
        assert!(return_mechanics_manifest_has_exact_order(
            &canonical,
            &source_order,
            &return_order,
        ));
        assert!(!return_mechanics_manifest_has_exact_order(
            &[
                owner(second, [second_return]),
                owner(first, [first_return, second_return]),
            ],
            &source_order,
            &return_order,
        ));
        assert!(!return_mechanics_manifest_has_exact_order(
            &[
                owner(first, [first_return, second_return]),
                owner(first, [first_return, second_return]),
                owner(second, [second_return]),
            ],
            &source_order,
            &return_order,
        ));
        assert!(!return_mechanics_manifest_has_exact_order(
            &[
                owner(first, [second_return, first_return]),
                owner(second, [second_return]),
            ],
            &source_order,
            &return_order,
        ));
        assert!(!return_mechanics_manifest_has_exact_order(
            &[
                owner(first, [first_return, id(99)]),
                owner(second, [second_return]),
            ],
            &source_order,
            &return_order,
        ));
    }

    #[test]
    fn frame_manifest_uses_global_block_order_and_precise_served_returns() {
        let entry_save = block_id(0x1000, 0);
        let shared_restore_input = block_id(0x2000, 0);
        let first_restore = block_id(0x2000, 1);
        let first_return = block_id(0x2000, 2);
        let second_restore = block_id(0x3000, 0);
        let second_return = block_id(0x3000, 1);
        let source_order = [
            entry_save,
            shared_restore_input,
            first_restore,
            first_return,
            second_restore,
            second_return,
        ];
        let return_order = [first_return, second_return];
        let canonical = [
            (entry_save, vec![first_return, second_return]),
            (shared_restore_input, vec![first_return, second_return]),
            (first_restore, vec![first_return]),
            (second_restore, vec![second_return]),
        ];
        assert!(mechanics_manifest_has_exact_order(
            canonical
                .iter()
                .map(|(producer, returns)| (*producer, returns.as_slice())),
            &source_order,
            &return_order,
        ));

        let mut unrelated_return = canonical.clone();
        unrelated_return[2].1 = vec![second_return, first_return];
        assert!(!mechanics_manifest_has_exact_order(
            unrelated_return
                .iter()
                .map(|(producer, returns)| (*producer, returns.as_slice())),
            &source_order,
            &return_order,
        ));
        let mut reordered = canonical.clone();
        reordered.swap(1, 2);
        assert!(!mechanics_manifest_has_exact_order(
            reordered
                .iter()
                .map(|(producer, returns)| (*producer, returns.as_slice())),
            &source_order,
            &return_order,
        ));
    }
}
