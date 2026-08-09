use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CallBoundarySlot, CanonicalInstructionId, CanonicalStorageId, ConditionalReturnCandidateFact,
    ConditionalReturnCarrierFact, InstId, InstPayload, MachineBuildError, MachineValueUse,
    ObjectId, PredicateId, SSAOp, SemanticInstructionState, SemanticObligationComponent,
    SemanticObligationId, SemanticObligationInventory, SemanticObligationKind,
    SourceFunctionReturn, SsaArtifact, StackAddressRoot, StructuredAccessId,
};
use serde::Serialize;

use crate::{
    CERTIFICATION_SCHEMA_VERSION, CertificationError, CertifiedArtifactOrigin,
    CertifiedConditionalControl, CertifiedDirectControl, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedRenderPermit, CertifiedReturnControl,
    CertifiedSourceTerminator, CertifiedSourceTopology, CertifiedStackSlot,
    CertifiedTypedRegionKind, EffectDisposition, ObligationLedger, RenderAuthorizationError,
    TypedRegionMapping,
};

pub const CERTIFIED_CONDITIONAL_RETURN_FUNNEL_CONTRACT_VERSION: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalReturnCandidate {
    truth: bool,
    edge_target: u64,
    forwarder: Option<u64>,
    producer_block: u64,
    producer: CanonicalInstructionId,
    value: MachineValueUse,
    forwarder_transfer: Option<CertifiedDirectControl>,
    join_transfer: CertifiedDirectControl,
}

impl CertifiedConditionalReturnCandidate {
    pub const fn truth(&self) -> bool {
        self.truth
    }

    pub const fn edge_target(&self) -> u64 {
        self.edge_target
    }

    pub const fn forwarder(&self) -> Option<u64> {
        self.forwarder
    }

    pub const fn producer_block(&self) -> u64 {
        self.producer_block
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }

    pub const fn forwarder_transfer(&self) -> Option<&CertifiedDirectControl> {
        self.forwarder_transfer.as_ref()
    }

    pub const fn join_transfer(&self) -> &CertifiedDirectControl {
        &self.join_transfer
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalReturnPhiInput {
    predecessor: u64,
    value: MachineValueUse,
}

impl CertifiedConditionalReturnPhiInput {
    pub const fn predecessor(&self) -> u64 {
        self.predecessor
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalReturnRegisterPhi {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    producer: CanonicalInstructionId,
    storage: CanonicalStorageId,
    phi: MachineValueUse,
    inputs: Box<[CertifiedConditionalReturnPhiInput]>,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl CertifiedConditionalReturnRegisterPhi {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn phi(&self) -> &MachineValueUse {
        &self.phi
    }

    pub const fn inputs(&self) -> &[CertifiedConditionalReturnPhiInput] {
        &self.inputs
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        super::validate_schema(self.schema_version)?;
        let [left, right] = self.inputs.as_ref() else {
            return Err(unmapped(self.producer));
        };
        let obligation = SemanticObligationId {
            instruction: self.producer,
            kind: SemanticObligationKind::LiveValueProducer,
            component: SemanticObligationComponent::Whole,
        };
        if self.origin.source() != source
            || self.phi.producer() != Some(self.producer)
            || self.storage.size.checked_mul(8) != Some(self.phi.binding().width_bits())
            || left.predecessor == right.predecessor
            || left.value.binding().width_bits() != self.phi.binding().width_bits()
            || right.value.binding().width_bits() != self.phi.binding().width_bits()
            || self.source_obligations != BTreeSet::from([obligation])
            || source
                .instructions()
                .get(&self.producer)
                .is_none_or(|instruction| {
                    instruction.state != SemanticInstructionState::LiveObligation
                        || instruction.obligations != self.source_obligations
                })
            || source.obligations().get(&obligation).is_none_or(|source| {
                source.inputs.len() != 2
                    || source.inputs.iter().copied().collect::<BTreeSet<_>>()
                        != BTreeSet::from([
                            left.value.binding().value(),
                            right.value.binding().value(),
                        ])
            })
        {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedMemoryVersion {
    object: ObjectId,
    version: u32,
}

impl CertifiedMemoryVersion {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn version(&self) -> u32 {
        self.version
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateStackScalar {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    slot: CertifiedStackSlot,
    object: ObjectId,
    width_bytes: u32,
    accesses: Box<[StructuredAccessId]>,
    true_store: CertifiedMemoryStatement,
    false_store: CertifiedMemoryStatement,
    load: CertifiedMemoryStatement,
    merged_version: CertifiedMemoryVersion,
    reaching_definitions: Box<[(u64, CertifiedMemoryVersion)]>,
    loaded_value: MachineValueUse,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl CertifiedPrivateStackScalar {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn slot(&self) -> &CertifiedStackSlot {
        &self.slot
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn width_bytes(&self) -> u32 {
        self.width_bytes
    }

    pub const fn accesses(&self) -> &[StructuredAccessId] {
        &self.accesses
    }

    pub const fn true_store(&self) -> &CertifiedMemoryStatement {
        &self.true_store
    }

    pub const fn false_store(&self) -> &CertifiedMemoryStatement {
        &self.false_store
    }

    pub const fn load(&self) -> &CertifiedMemoryStatement {
        &self.load
    }

    pub const fn merged_version(&self) -> &CertifiedMemoryVersion {
        &self.merged_version
    }

    pub const fn reaching_definitions(&self) -> &[(u64, CertifiedMemoryVersion)] {
        &self.reaching_definitions
    }

    pub const fn loaded_value(&self) -> &MachineValueUse {
        &self.loaded_value
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.load.producer()
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        super::validate_schema(self.schema_version)?;
        self.true_store.validate(source)?;
        self.false_store.validate(source)?;
        self.load.validate(source)?;
        let [left, right] = self.reaching_definitions.as_ref() else {
            return Err(unmapped(self.producer()));
        };
        let exact_accesses = BTreeSet::from([
            self.true_store.access(),
            self.false_store.access(),
            self.load.access(),
        ]);
        let load_live = SemanticObligationId {
            instruction: self.load.producer(),
            kind: SemanticObligationKind::LiveValueProducer,
            component: SemanticObligationComponent::Whole,
        };
        let mut expected = self.true_store.source_obligations().clone();
        expected.extend(self.false_store.source_obligations());
        expected.extend(self.load.source_obligations());
        expected.insert(load_live);
        let stores_are_exact = [self.true_store(), self.false_store()].iter().all(|store| {
            store.object() == self.object
                && store.width_bits() == self.width_bytes.saturating_mul(8)
                && matches!(store.kind(), CertifiedMemoryStatementKind::Write { value }
                    if value.binding().width_bits() == store.width_bits())
                && source
                    .instructions()
                    .get(&store.producer())
                    .is_some_and(|instruction| {
                        instruction.obligations == *store.source_obligations()
                    })
        });
        let load_is_exact = self.load.object() == self.object
            && self.load.width_bits() == self.width_bytes.saturating_mul(8)
            && matches!(self.load.kind(), CertifiedMemoryStatementKind::Read { result }
                if result == &self.loaded_value)
            && source
                .instructions()
                .get(&self.load.producer())
                .is_some_and(|instruction| {
                    instruction.obligations == {
                        let mut obligations = self.load.source_obligations().clone();
                        obligations.insert(load_live);
                        obligations
                    }
                });
        if self.origin.source() != source
            || self.width_bytes == 0
            || self.slot.object() != Some(self.object)
            || self.slot.size_bytes() != self.width_bytes
            || self.accesses.len() != 3
            || self.accesses.iter().copied().collect::<BTreeSet<_>>() != exact_accesses
            || !stores_are_exact
            || !load_is_exact
            || self.true_store.producer() == self.false_store.producer()
            || self.merged_version.object != self.object
            || left.0 == right.0
            || left.1.object != self.object
            || right.1.object != self.object
            || self.source_obligations != expected
        {
            return Err(CertificationError::ObligationNotMapped(load_live));
        }
        Ok(())
    }

    #[cfg(test)]
    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let machine = crate::CertifiedMachineFunction::from_artifact(artifact)?;
        let expected = machine
            .conditional_return_funnels()
            .values()
            .find_map(|control| match control.carrier() {
                CertifiedConditionalReturnCarrier::PrivateStackScalar(scalar)
                    if scalar.producer() == self.producer() =>
                {
                    Some(scalar.as_ref())
                }
                _ => None,
            })
            .ok_or(MachineBuildError::ObligationMismatch(
                self.load.access().inst,
            ))?;
        if self == expected {
            Ok(())
        } else {
            Err(MachineBuildError::ObligationMismatch(
                self.load.access().inst,
            ))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedConditionalReturnCarrier {
    RegisterPhi(Box<CertifiedConditionalReturnRegisterPhi>),
    PrivateStackScalar(Box<CertifiedPrivateStackScalar>),
}

impl CertifiedConditionalReturnCarrier {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        match self {
            Self::RegisterPhi(state) => state.origin(),
            Self::PrivateStackScalar(state) => state.origin(),
        }
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        match self {
            Self::RegisterPhi(state) => state.producer(),
            Self::PrivateStackScalar(state) => state.producer(),
        }
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        match self {
            Self::RegisterPhi(state) => state.source_obligations(),
            Self::PrivateStackScalar(state) => state.source_obligations(),
        }
    }

    pub(crate) fn validate(
        &self,
        source: &SemanticObligationInventory,
    ) -> Result<(), CertificationError> {
        match self {
            Self::RegisterPhi(state) => state.validate(source),
            Self::PrivateStackScalar(state) => state.validate(source),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalReturnFunnelControl {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    predicate: PredicateId,
    branch_control: CertifiedConditionalControl,
    true_candidate: CertifiedConditionalReturnCandidate,
    false_candidate: CertifiedConditionalReturnCandidate,
    join_block: u64,
    return_control: CertifiedReturnControl,
    return_storage: CanonicalStorageId,
    return_value: MachineValueUse,
    return_value_chain: Box<[MachineValueUse]>,
    carrier: CertifiedConditionalReturnCarrier,
}

impl CertifiedConditionalReturnFunnelControl {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn predicate(&self) -> PredicateId {
        self.predicate
    }

    pub const fn branch_control(&self) -> &CertifiedConditionalControl {
        &self.branch_control
    }

    pub const fn true_candidate(&self) -> &CertifiedConditionalReturnCandidate {
        &self.true_candidate
    }

    pub const fn false_candidate(&self) -> &CertifiedConditionalReturnCandidate {
        &self.false_candidate
    }

    pub const fn join_block(&self) -> u64 {
        self.join_block
    }

    pub const fn return_control(&self) -> &CertifiedReturnControl {
        &self.return_control
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn return_value(&self) -> &MachineValueUse {
        &self.return_value
    }

    pub const fn return_value_chain(&self) -> &[MachineValueUse] {
        &self.return_value_chain
    }

    pub const fn carrier(&self) -> &CertifiedConditionalReturnCarrier {
        &self.carrier
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        super::validate_schema(self.schema_version)?;
        self.branch_control.validate(source)?;
        self.return_control.validate(source)?;
        self.carrier.validate(source)?;
        if self.origin.source() != source
            || self.carrier.origin() != &self.origin
            || !self.true_candidate.truth
            || self.false_candidate.truth
            || self.branch_control.true_target() != self.true_candidate.edge_target
            || self.branch_control.false_target() != self.false_candidate.edge_target
            || self.true_candidate.producer_block == self.false_candidate.producer_block
            || self.true_candidate.join_transfer.target() != self.join_block
            || self.false_candidate.join_transfer.target() != self.join_block
            || self.return_control.producer().block_addr != self.join_block
            || !matches!(
                self.return_control.values(),
                [returned]
                    if returned.slot()
                        == (CallBoundarySlot::Register {
                            index: 0,
                            storage: self.return_storage,
                        })
                        && returned.value() == &self.return_value
            )
            || !candidate_routing_is_exact(&self.origin, &self.true_candidate, self.join_block)
            || !candidate_routing_is_exact(&self.origin, &self.false_candidate, self.join_block)
            || !funnel_topology_is_exact(self)
            || !carrier_candidates_are_exact(self)
            || !return_chain_is_exact(source, self)
        {
            return Err(unmapped(self.carrier.producer()));
        }
        Ok(())
    }

    #[cfg(test)]
    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let machine = crate::CertifiedMachineFunction::from_artifact(artifact)?;
        let expected = machine
            .conditional_return_funnel(self.predicate)
            .ok_or(MachineBuildError::TopologyMismatch)?;
        if self == expected {
            Ok(())
        } else {
            Err(MachineBuildError::TopologyMismatch)
        }
    }
}

fn candidate_routing_is_exact(
    origin: &CertifiedArtifactOrigin,
    candidate: &CertifiedConditionalReturnCandidate,
    join: u64,
) -> bool {
    let Some(producer) = origin.topology().block(candidate.producer_block) else {
        return false;
    };
    if producer.instructions().last() != Some(&candidate.join_transfer.producer())
        || candidate.join_transfer.target() != join
        || !producer.instructions().contains(&candidate.producer)
        || producer.successors() != [join]
    {
        return false;
    }
    match (candidate.forwarder, &candidate.forwarder_transfer) {
        (None, None) => {
            candidate.edge_target == candidate.producer_block
                && producer.predecessors() == [origin.topology().entry_addr()]
        }
        (Some(forwarder), Some(transfer)) => {
            candidate.edge_target == forwarder
                && transfer.target() == candidate.producer_block
                && origin.topology().block(forwarder).is_some_and(|block| {
                    block.predecessors() == [origin.topology().entry_addr()]
                        && block.successors() == [candidate.producer_block]
                        && block.instructions() == [transfer.producer()]
                })
                && producer.predecessors() == [forwarder]
        }
        _ => false,
    }
}

fn funnel_topology_is_exact(control: &CertifiedConditionalReturnFunnelControl) -> bool {
    let topology = control.origin.topology();
    let branch = control.branch_control.producer().block_addr;
    let expected_blocks = [
        Some(branch),
        Some(control.true_candidate.producer_block),
        control.true_candidate.forwarder,
        Some(control.false_candidate.producer_block),
        control.false_candidate.forwarder,
        Some(control.join_block),
    ]
    .into_iter()
    .flatten()
    .collect::<BTreeSet<_>>();
    let actual_blocks = topology
        .blocks()
        .iter()
        .map(|block| block.addr())
        .collect::<BTreeSet<_>>();
    topology.entry_addr() == branch
        && expected_blocks == actual_blocks
        && topology.block(branch).is_some_and(|block| {
            block.predecessors().is_empty()
                && block.instructions().last() == Some(&control.branch_control.producer())
                && block.successors().len() == 2
                && block.successors().iter().copied().collect::<BTreeSet<_>>()
                    == BTreeSet::from([
                        control.true_candidate.edge_target,
                        control.false_candidate.edge_target,
                    ])
                && matches!(
                    block.terminator(),
                    CertifiedSourceTerminator::ConditionalBranch {
                        true_target,
                        false_target,
                    } if *true_target == control.true_candidate.edge_target
                        && *false_target == control.false_candidate.edge_target
                )
        })
        && topology.block(control.join_block).is_some_and(|block| {
            block
                .predecessors()
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                == BTreeSet::from([
                    control.true_candidate.producer_block,
                    control.false_candidate.producer_block,
                ])
                && block.successors().is_empty()
                && block.instructions().last() == Some(&control.return_control.producer())
                && matches!(block.terminator(), CertifiedSourceTerminator::Return)
        })
}

fn carrier_candidates_are_exact(control: &CertifiedConditionalReturnFunnelControl) -> bool {
    match &control.carrier {
        CertifiedConditionalReturnCarrier::RegisterPhi(state) => {
            state.inputs.len() == 2
                && state.inputs.iter().any(|input| {
                    input.predecessor == control.true_candidate.producer_block
                        && input.value == control.true_candidate.value
                })
                && state.inputs.iter().any(|input| {
                    input.predecessor == control.false_candidate.producer_block
                        && input.value == control.false_candidate.value
                })
                && control.true_candidate.value.producer() == Some(control.true_candidate.producer)
                && control.false_candidate.value.producer()
                    == Some(control.false_candidate.producer)
        }
        CertifiedConditionalReturnCarrier::PrivateStackScalar(state) => {
            state.reaching_definitions.len() == 2
                && state
                    .reaching_definitions
                    .iter()
                    .any(|(predecessor, _)| *predecessor == control.true_candidate.producer_block)
                && state
                    .reaching_definitions
                    .iter()
                    .any(|(predecessor, _)| *predecessor == control.false_candidate.producer_block)
                && state.true_store.producer() == control.true_candidate.producer
                && state.false_store.producer() == control.false_candidate.producer
                && matches!(state.true_store.kind(), CertifiedMemoryStatementKind::Write { value }
                    if value == &control.true_candidate.value)
                && matches!(state.false_store.kind(), CertifiedMemoryStatementKind::Write { value }
                    if value == &control.false_candidate.value)
        }
    }
}

fn return_chain_is_exact(
    source: &SemanticObligationInventory,
    control: &CertifiedConditionalReturnFunnelControl,
) -> bool {
    let mut previous = match &control.carrier {
        CertifiedConditionalReturnCarrier::RegisterPhi(state) => state.phi.binding().value(),
        CertifiedConditionalReturnCarrier::PrivateStackScalar(state) => {
            state.loaded_value.binding().value()
        }
    };
    for value in &control.return_value_chain {
        let Some(producer) = value.producer() else {
            return false;
        };
        let Some(expected_inst) = source_instruction_inst(source, producer) else {
            return false;
        };
        let obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::LiveValueProducer,
            component: SemanticObligationComponent::Whole,
        };
        if producer.block_addr != control.join_block
            || source
                .obligations()
                .get(&obligation)
                .is_none_or(|obligation| {
                    obligation.inputs != [previous] || obligation.source_inst != expected_inst
                })
        {
            return false;
        }
        previous = value.binding().value();
    }
    previous == control.return_value.binding().value()
}

fn source_instruction_inst(
    source: &SemanticObligationInventory,
    producer: CanonicalInstructionId,
) -> Option<InstId> {
    source
        .instructions()
        .get(&producer)
        .map(|instruction| instruction.inst)
}

fn unmapped(producer: CanonicalInstructionId) -> CertificationError {
    CertificationError::ObligationNotMapped(SemanticObligationId {
        instruction: producer,
        kind: SemanticObligationKind::LiveValueProducer,
        component: SemanticObligationComponent::Whole,
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn certified_conditional_return_funnels(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    stack_slots: &BTreeMap<StackAddressRoot, CertifiedStackSlot>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
) -> Result<BTreeMap<PredicateId, CertifiedConditionalReturnFunnelControl>, MachineBuildError> {
    let mut controls = BTreeMap::new();
    let Some(interface) = artifact.machine_context().function_interface() else {
        return Ok(controls);
    };
    let SourceFunctionReturn::Register {
        storage: interface_return,
    } = interface.return_kind()
    else {
        return Ok(controls);
    };
    for (predicate, fact) in &artifact.structured().conditional_return_funnels {
        if *predicate != fact.predicate || interface_return != fact.return_storage {
            continue;
        }
        let Some(branch_producer) = topology
            .block(fact.branch_block)
            .and_then(|block| block.instructions().last())
        else {
            continue;
        };
        let Some(branch_control) = conditional_controls.get(branch_producer) else {
            continue;
        };
        let Some(return_producer) = canonical(artifact, fact.return_inst) else {
            continue;
        };
        let Some(return_control) = return_controls.get(&return_producer) else {
            continue;
        };
        let Some(true_candidate) = build_candidate(
            artifact,
            topology,
            direct_controls,
            fact.join_block,
            &fact.true_candidate,
        )?
        else {
            continue;
        };
        let Some(false_candidate) = build_candidate(
            artifact,
            topology,
            direct_controls,
            fact.join_block,
            &fact.false_candidate,
        )?
        else {
            continue;
        };
        let carrier = match &fact.carrier {
            ConditionalReturnCarrierFact::RegisterPhi(state) => {
                let Some(producer) = canonical(artifact, state.phi_inst) else {
                    continue;
                };
                let inputs = state
                    .inputs
                    .iter()
                    .map(|input| {
                        Ok(CertifiedConditionalReturnPhiInput {
                            predecessor: input.predecessor,
                            value: MachineValueUse::from_artifact(artifact, input.value)?,
                        })
                    })
                    .collect::<Result<Vec<_>, MachineBuildError>>()?;
                let register = CertifiedConditionalReturnRegisterPhi {
                    schema_version: CERTIFICATION_SCHEMA_VERSION,
                    origin: origin.clone(),
                    producer,
                    storage: state.storage,
                    phi: MachineValueUse::from_artifact(artifact, state.phi)?,
                    inputs: inputs.into_boxed_slice(),
                    source_obligations: artifact
                        .obligations()
                        .instructions()
                        .get(&producer)
                        .map(|instruction| instruction.obligations.clone())
                        .unwrap_or_default(),
                };
                if register.validate(artifact.obligations()).is_err() {
                    continue;
                }
                CertifiedConditionalReturnCarrier::RegisterPhi(Box::new(register))
            }
            ConditionalReturnCarrierFact::PrivateStackSlot(state) => {
                let root = StackAddressRoot {
                    base: state.base,
                    offset: state.offset,
                };
                let Some(slot) = stack_slots.get(&root).filter(|slot| {
                    slot.object() == Some(state.object) && slot.size_bytes() == state.width
                }) else {
                    continue;
                };
                let Some(true_store) =
                    statement_for_access(artifact, memory_statements, state.true_store)
                else {
                    continue;
                };
                let Some(false_store) =
                    statement_for_access(artifact, memory_statements, state.false_store)
                else {
                    continue;
                };
                let Some(load) = statement_for_access(artifact, memory_statements, state.load)
                else {
                    continue;
                };
                let load_live = SemanticObligationId {
                    instruction: load.producer(),
                    kind: SemanticObligationKind::LiveValueProducer,
                    component: SemanticObligationComponent::Whole,
                };
                let mut source_obligations = true_store.source_obligations().clone();
                source_obligations.extend(false_store.source_obligations());
                source_obligations.extend(load.source_obligations());
                source_obligations.insert(load_live);
                let scalar = CertifiedPrivateStackScalar {
                    schema_version: CERTIFICATION_SCHEMA_VERSION,
                    origin: origin.clone(),
                    slot: slot.clone(),
                    object: state.object,
                    width_bytes: state.width,
                    accesses: state.accesses.clone().into_boxed_slice(),
                    true_store: true_store.clone(),
                    false_store: false_store.clone(),
                    load: load.clone(),
                    merged_version: CertifiedMemoryVersion {
                        object: state.merged_version.object,
                        version: state.merged_version.version,
                    },
                    reaching_definitions: state
                        .reaching_definitions
                        .iter()
                        .map(|(predecessor, version)| {
                            (
                                *predecessor,
                                CertifiedMemoryVersion {
                                    object: version.object,
                                    version: version.version,
                                },
                            )
                        })
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    loaded_value: MachineValueUse::from_artifact(artifact, state.loaded_value)?,
                    source_obligations,
                };
                if scalar.validate(artifact.obligations()).is_err() {
                    continue;
                }
                CertifiedConditionalReturnCarrier::PrivateStackScalar(Box::new(scalar))
            }
        };
        if !obligation_surface_is_exact(artifact.obligations(), &carrier) {
            continue;
        }
        if fact.return_value_chain.iter().any(|inst_id| {
            artifact.graph().inst(*inst_id).is_none_or(|inst| {
                artifact
                    .graph()
                    .block(inst.block)
                    .is_none_or(|block| block.addr != fact.join_block)
                    || inst.inputs.len() != 1
                    || inst.output.is_none()
                    || !matches!(
                        inst.payload,
                        InstPayload::Op(
                            SSAOp::Copy { .. }
                                | SSAOp::IntZExt { .. }
                                | SSAOp::IntSExt { .. }
                                | SSAOp::Trunc { .. }
                                | SSAOp::Cast { .. }
                                | SSAOp::Subpiece { .. }
                        )
                    )
            })
        }) {
            continue;
        }
        let return_value_chain = fact
            .return_value_chain
            .iter()
            .map(|inst| {
                artifact
                    .graph()
                    .inst(*inst)
                    .and_then(|inst| inst.output)
                    .ok_or(MachineBuildError::MissingInstruction(*inst))
                    .and_then(|output| MachineValueUse::from_artifact(artifact, output))
            })
            .collect::<Result<Vec<_>, MachineBuildError>>()?;
        let control = CertifiedConditionalReturnFunnelControl {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            origin: origin.clone(),
            predicate: *predicate,
            branch_control: branch_control.clone(),
            true_candidate,
            false_candidate,
            join_block: fact.join_block,
            return_control: return_control.clone(),
            return_storage: fact.return_storage,
            return_value: MachineValueUse::from_artifact(artifact, fact.return_value)?,
            return_value_chain: return_value_chain.into_boxed_slice(),
            carrier,
        };
        if control.validate(artifact.obligations()).is_err() {
            continue;
        }
        if controls.insert(*predicate, control).is_some() {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    Ok(controls)
}

fn build_candidate(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    join: u64,
    fact: &ConditionalReturnCandidateFact,
) -> Result<Option<CertifiedConditionalReturnCandidate>, MachineBuildError> {
    let Some(producer) = canonical(artifact, fact.producer_inst) else {
        return Ok(None);
    };
    let Some(join_transfer) = topology
        .block(fact.producer_block)
        .and_then(|block| block.instructions().last())
        .and_then(|producer| direct_controls.get(producer))
        .filter(|control| control.target() == join)
    else {
        return Ok(None);
    };
    let forwarder_transfer = match fact.forwarder {
        Some(forwarder) => {
            let Some(control) = topology
                .block(forwarder)
                .and_then(|block| block.instructions().last())
                .and_then(|producer| direct_controls.get(producer))
                .filter(|control| control.target() == fact.producer_block)
            else {
                return Ok(None);
            };
            Some(control.clone())
        }
        None => None,
    };
    Ok(Some(CertifiedConditionalReturnCandidate {
        truth: fact.truth,
        edge_target: fact.edge_target,
        forwarder: fact.forwarder,
        producer_block: fact.producer_block,
        producer,
        value: MachineValueUse::from_artifact(artifact, fact.value)?,
        forwarder_transfer,
        join_transfer: join_transfer.clone(),
    }))
}

fn statement_for_access<'a>(
    artifact: &SsaArtifact,
    statements: &'a BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    access: StructuredAccessId,
) -> Option<&'a CertifiedMemoryStatement> {
    canonical(artifact, access.inst)
        .and_then(|producer| statements.get(&producer))
        .filter(|statement| statement.access() == access)
}

fn canonical(artifact: &SsaArtifact, inst: InstId) -> Option<CanonicalInstructionId> {
    artifact
        .obligations()
        .instruction_for_inst(inst)
        .map(|instruction| instruction.id)
}

fn obligation_surface_is_exact(
    source: &SemanticObligationInventory,
    carrier: &CertifiedConditionalReturnCarrier,
) -> bool {
    if source
        .instructions()
        .values()
        .any(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return false;
    }
    let memory_owned = carrier.source_obligations();
    source
        .obligations()
        .values()
        .all(|obligation| match obligation.id.kind {
            SemanticObligationKind::ObservableMemoryRead
            | SemanticObligationKind::ObservableMemoryWrite => {
                memory_owned.contains(&obligation.id)
            }
            SemanticObligationKind::LiveValueProducer
            | SemanticObligationKind::ControlPredicate
            | SemanticObligationKind::ControlTransfer
            | SemanticObligationKind::Return
            | SemanticObligationKind::ReturnValue => true,
            SemanticObligationKind::Call
            | SemanticObligationKind::CallArgument
            | SemanticObligationKind::CallResult
            | SemanticObligationKind::Trap
            | SemanticObligationKind::Atomicity
            | SemanticObligationKind::MemoryOrdering
            | SemanticObligationKind::VolatileOrUnknownEffect
            | SemanticObligationKind::LoopCarriedState
            | SemanticObligationKind::LiveStateTransition => false,
        })
}

/// Authorize the exact whole-function conditional return funnel sealed by
/// [`CertifiedConditionalReturnFunnelControl`]. The witness, ledger, and
/// manifest are revalidated together; none can mint authority independently.
pub fn certify_conditional_return_funnel_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    control: &CertifiedConditionalReturnFunnelControl,
) -> Result<CertifiedRenderPermit, RenderAuthorizationError> {
    if origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || !origin.matches_retained_source(origin.source(), origin.topology())
        || control.origin() != origin
    {
        return Err(RenderAuthorizationError::InvalidOrigin);
    }
    if control.schema_version() != CERTIFICATION_SCHEMA_VERSION {
        return Err(RenderAuthorizationError::InvalidRegionSchema);
    }
    let source = origin.source();
    let carrier = control.carrier();
    if carrier.validate(source).is_err() {
        return Err(RenderAuthorizationError::InvalidRegionDisposition(
            carrier_obligation(carrier),
        ));
    }
    let Some(interface) = origin.machine_context().source().function_interface() else {
        return Err(RenderAuthorizationError::InvalidOrigin);
    };
    if !matches!(
        interface.return_kind(),
        SourceFunctionReturn::Register { storage } if storage == control.return_storage()
    ) || matches!(carrier, CertifiedConditionalReturnCarrier::PrivateStackScalar(state)
        if interface.stack_slots().iter().filter(|slot| {
            slot.base() == state.slot().base()
                && slot.offset() == state.slot().offset()
                && slot.size_bytes() == state.width_bytes()
        }).count() != 1)
    {
        return Err(RenderAuthorizationError::InvalidOrigin);
    }
    if !funnel_topology_is_exact(control)
        || !candidate_routing_is_exact(origin, control.true_candidate(), control.join_block())
        || !candidate_routing_is_exact(origin, control.false_candidate(), control.join_block())
        || !carrier_candidates_are_exact(control)
        || !return_chain_is_exact(source, control)
        || !obligation_surface_is_exact(source, carrier)
    {
        return Err(RenderAuthorizationError::InvalidRegionTopology);
    }
    if control.validate(source).is_err() {
        return Err(RenderAuthorizationError::InvalidRegionDisposition(
            carrier_obligation(carrier),
        ));
    }
    if let Some(instruction) = source
        .instructions()
        .values()
        .find(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return Err(RenderAuthorizationError::UnsupportedSourceSemantics(
            instruction.id,
        ));
    }

    let report = ledger.audit(source);
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(RenderAuthorizationError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(RenderAuthorizationError::ResidualOrRefusedObligation(
            *obligation,
        ));
    }
    for obligation in source.obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(RenderAuthorizationError::IncompleteLedger);
        };
        if !funnel_effect_is_exact(control, obligation.id, effect) {
            return Err(RenderAuthorizationError::InvalidRegionDisposition(
                obligation.id,
            ));
        }
    }

    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !source.obligations().contains_key(&mapping.obligation()) {
            return Err(RenderAuthorizationError::UnexpectedMapping(
                mapping.obligation(),
            ));
        }
        if by_obligation
            .insert(mapping.obligation(), mapping)
            .is_some()
        {
            return Err(RenderAuthorizationError::DuplicateMapping(
                mapping.obligation(),
            ));
        }
    }
    for obligation in source.obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(RenderAuthorizationError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(RenderAuthorizationError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(RenderAuthorizationError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedRenderPermit {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::ConditionalReturnFunnelFunction,
        region_schema_version: CERTIFIED_CONDITIONAL_RETURN_FUNNEL_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

fn carrier_obligation(carrier: &CertifiedConditionalReturnCarrier) -> SemanticObligationId {
    carrier
        .source_obligations()
        .iter()
        .copied()
        .next()
        .unwrap_or(SemanticObligationId {
            instruction: carrier.producer(),
            kind: SemanticObligationKind::LiveValueProducer,
            component: SemanticObligationComponent::Whole,
        })
}

fn funnel_effect_is_exact(
    control: &CertifiedConditionalReturnFunnelControl,
    obligation: SemanticObligationId,
    effect: &crate::CertifiedEffect,
) -> bool {
    let carrier = control.carrier();
    if carrier.source_obligations().contains(&obligation) {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoConditionalReturnState {
                producer: carrier.producer(),
            })
            && effect.conditional_return_state_evidence() == Some(carrier);
    }
    match obligation.kind {
        SemanticObligationKind::LiveValueProducer => {
            effect.disposition()
                == &(EffectDisposition::AbsorbedIntoExpression {
                    producer: obligation.instruction,
                })
                && effect.expression_evidence().is_some_and(|expression| {
                    expression.entity().producer() == obligation.instruction
                        && expression
                            .entity()
                            .source_obligations()
                            .contains(&obligation)
                })
        }
        SemanticObligationKind::ControlPredicate => {
            obligation.instruction == control.branch_control().producer()
                && effect.disposition()
                    == &(EffectDisposition::AbsorbedIntoControl {
                        producer: obligation.instruction,
                    })
                && effect.conditional_control_evidence() == Some(control.branch_control())
        }
        SemanticObligationKind::ControlTransfer => {
            if obligation.instruction == control.branch_control().producer() {
                return effect.disposition()
                    == &(EffectDisposition::AbsorbedIntoControl {
                        producer: obligation.instruction,
                    })
                    && effect.conditional_control_evidence() == Some(control.branch_control());
            }
            funnel_direct_controls(control).into_iter().any(|direct| {
                direct.producer() == obligation.instruction
                    && effect.disposition()
                        == &(EffectDisposition::AbsorbedIntoControl {
                            producer: obligation.instruction,
                        })
                    && effect.direct_control_evidence() == Some(direct)
            })
        }
        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
            obligation.instruction == control.return_control().producer()
                && effect.disposition()
                    == &(EffectDisposition::AbsorbedIntoReturn {
                        producer: obligation.instruction,
                    })
                && effect.return_control_evidence() == Some(control.return_control())
        }
        SemanticObligationKind::ObservableMemoryRead
        | SemanticObligationKind::ObservableMemoryWrite
        | SemanticObligationKind::Call
        | SemanticObligationKind::CallArgument
        | SemanticObligationKind::CallResult
        | SemanticObligationKind::Trap
        | SemanticObligationKind::Atomicity
        | SemanticObligationKind::MemoryOrdering
        | SemanticObligationKind::VolatileOrUnknownEffect
        | SemanticObligationKind::LoopCarriedState
        | SemanticObligationKind::LiveStateTransition => false,
    }
}

fn funnel_direct_controls(
    control: &CertifiedConditionalReturnFunnelControl,
) -> Vec<&CertifiedDirectControl> {
    let candidates = [control.true_candidate(), control.false_candidate()];
    candidates
        .into_iter()
        .flat_map(|candidate| {
            candidate
                .forwarder_transfer()
                .into_iter()
                .chain(std::iter::once(candidate.join_transfer()))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceStackSlotSpec, StackAddressBase,
    };

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("conditional-return-cert-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("x0", 8, 8));
        arch.add_register(RegisterDef::new("arg0", 16, 8));
        arch.add_register(RegisterDef::new("pc", 24, 8));
        arch.add_register(RegisterDef::new("other", 32, 8));
        arch
    }

    fn interface(
        revision: &[u8],
        slot_offset: Option<i64>,
        slot_width: u32,
        slot_base_storage: CanonicalStorageId,
        extra_slot: bool,
    ) -> SourceFunctionInterface {
        let slots = slot_offset
            .map(|offset| {
                let mut slots = vec![SourceStackSlotSpec::new(
                    StackAddressBase::StackPointer,
                    slot_base_storage,
                    offset,
                    slot_width,
                )];
                if extra_slot {
                    slots.push(SourceStackSlotSpec::new(
                        StackAddressBase::StackPointer,
                        slot_base_storage,
                        -8,
                        4,
                    ));
                }
                slots
            })
            .unwrap_or_default();
        SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, storage(16, 8))],
            SourceFunctionReturn::Register {
                storage: storage(8, 8),
            },
            slots,
        )
        .expect("conditional return interface")
    }

    fn branch_entry() -> R2ILBlock {
        let mut block = R2ILBlock::new(0x7000, 4);
        let condition = Varnode::unique(0x10, 1);
        block.push(R2ILOp::IntEqual {
            dst: condition.clone(),
            a: Varnode::register(16, 8),
            b: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7020, 8),
            cond: condition,
        });
        block
    }

    fn register_blocks() -> Vec<R2ILBlock> {
        let mut false_arm = R2ILBlock::new(0x7004, 4);
        false_arm.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0, 8),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7030, 8),
        });
        let mut true_arm = R2ILBlock::new(0x7020, 4);
        true_arm.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(1, 8),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7030, 8),
        });
        let mut join = R2ILBlock::new(0x7030, 4);
        join.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        vec![branch_entry(), false_arm, true_arm, join]
    }

    fn stack_address(unique: u64, offset: i64) -> (R2ILOp, Varnode) {
        let address = Varnode::unique(unique, 8);
        (
            R2ILOp::IntAdd {
                dst: address.clone(),
                a: Varnode::register(0, 8),
                b: Varnode::constant(offset as u64, 8),
            },
            address,
        )
    }

    fn store_arm(addr: u64, value: u64, unique: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        let (address_op, address) = stack_address(unique, -4);
        block.push(address_op);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: Varnode::constant(value, 4),
        });
        block.push(R2ILOp::Branch {
            target: Varnode::ram(0x7030, 8),
        });
        block
    }

    fn stack_blocks() -> Vec<R2ILBlock> {
        let mut forwarder = R2ILBlock::new(0x7004, 4);
        forwarder.push(R2ILOp::Branch {
            target: Varnode::ram(0x7008, 8),
        });
        let mut join = R2ILBlock::new(0x7030, 4);
        let (address_op, address) = stack_address(0x50, -4);
        let loaded = Varnode::unique(0x60, 4);
        join.push(address_op);
        join.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: address,
        });
        join.push(R2ILOp::IntZExt {
            dst: Varnode::register(8, 8),
            src: loaded,
        });
        join.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        vec![
            branch_entry(),
            forwarder,
            store_arm(0x7008, 0, 0x30),
            store_arm(0x7020, 1, 0x40),
            join,
        ]
    }

    fn register_artifact(revision: &[u8]) -> SsaArtifact {
        SsaArtifact::raw_with_interface(
            &register_blocks(),
            Some(&arch()),
            interface(revision, None, 0, storage(0, 8), false),
        )
        .expect("register funnel artifact")
    }

    fn stack_artifact(revision: &[u8]) -> SsaArtifact {
        SsaArtifact::for_decompile_with_interface(
            &stack_blocks(),
            Some(&arch()),
            interface(revision, Some(-4), 4, storage(0, 8), false),
        )
        .expect("stack funnel artifact")
    }

    fn one_control(
        certified: &crate::CertifiedMachineFunction,
    ) -> &CertifiedConditionalReturnFunnelControl {
        let controls = certified
            .conditional_return_funnels()
            .values()
            .collect::<Vec<_>>();
        let [control] = controls.as_slice() else {
            panic!("one certified conditional return funnel: {controls:#?}");
        };
        control
    }

    #[test]
    fn seals_register_phi_funnel_and_owns_phi_once() {
        let artifact = register_artifact(b"conditional-return-cert-revision-1");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("certified register funnel");
        let control = one_control(&certified);
        assert!(control.true_candidate().truth());
        assert!(!control.false_candidate().truth());
        let CertifiedConditionalReturnCarrier::RegisterPhi(state) = control.carrier() else {
            panic!("register phi carrier");
        };
        assert_eq!(state.inputs().len(), 2);
        assert_eq!(state.storage(), storage(8, 8));
        for obligation in state.source_obligations() {
            assert!(matches!(
                certified.ledger().effects(*obligation),
                [effect]
                    if effect.disposition()
                        == &crate::EffectDisposition::AbsorbedIntoConditionalReturnState {
                            producer: state.producer(),
                        }
                        && effect.conditional_return_state_evidence() == Some(control.carrier())
            ));
        }
        assert!(certified.finish().has_exactly_one_disposition_per_source());
    }

    #[test]
    fn seals_private_stack_scalar_and_owns_exact_union_once() {
        let artifact = stack_artifact(b"conditional-return-cert-revision-1");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("certified stack funnel");
        let control = one_control(&certified);
        assert_eq!(control.false_candidate().forwarder(), Some(0x7004));
        assert_eq!(control.return_value_chain().len(), 1);
        let CertifiedConditionalReturnCarrier::PrivateStackScalar(state) = control.carrier() else {
            panic!("private stack carrier");
        };
        assert_eq!(state.slot().base(), StackAddressBase::StackPointer);
        assert_eq!(state.slot().offset(), -4);
        assert_eq!(state.width_bytes(), 4);
        assert_eq!(state.accesses().len(), 3);
        assert_eq!(state.reaching_definitions().len(), 2);
        assert_eq!(state.source_obligations().len(), 4);
        for obligation in state.source_obligations() {
            assert!(matches!(
                certified.ledger().effects(*obligation),
                [effect]
                    if effect.disposition()
                        == &crate::EffectDisposition::AbsorbedIntoConditionalReturnState {
                            producer: state.producer(),
                        }
                        && effect.conditional_return_state_evidence() == Some(control.carrier())
            ));
        }
        assert!(certified.finish().has_exactly_one_disposition_per_source());
    }

    #[test]
    fn mutated_store_load_labels_slot_storage_and_revision_fail_revalidation() {
        let stack = stack_artifact(b"conditional-return-cert-revision-1");
        let certified =
            crate::CertifiedMachineFunction::from_artifact(&stack).expect("certified stack funnel");
        let control = one_control(&certified);
        let CertifiedConditionalReturnCarrier::PrivateStackScalar(state) = control.carrier() else {
            panic!("private stack carrier");
        };

        let mut dropped_access = state.clone();
        dropped_access.accesses = dropped_access.accesses[..2].to_vec().into_boxed_slice();
        assert!(dropped_access.validate_against_artifact(&stack).is_err());

        let mut duplicated_access = state.clone();
        duplicated_access.accesses = vec![state.accesses[0]; 3].into_boxed_slice();
        assert!(duplicated_access.validate_against_artifact(&stack).is_err());

        let mut dropped_store = state.clone();
        dropped_store.true_store = dropped_store.false_store.clone();
        assert!(dropped_store.validate_against_artifact(&stack).is_err());

        let mut dropped_load = state.clone();
        dropped_load.load = dropped_load.true_store.clone();
        assert!(dropped_load.validate_against_artifact(&stack).is_err());

        let mut wrong_slot = state.clone();
        wrong_slot.slot.offset -= 4;
        assert!(wrong_slot.validate_against_artifact(&stack).is_err());

        let mut wrong_width = state.clone();
        wrong_width.width_bytes = 8;
        assert!(wrong_width.validate_against_artifact(&stack).is_err());

        let register = register_artifact(b"conditional-return-cert-revision-1");
        let register_machine = crate::CertifiedMachineFunction::from_artifact(&register)
            .expect("certified register funnel");
        let register_control = one_control(&register_machine);
        let CertifiedConditionalReturnCarrier::RegisterPhi(register_state) =
            register_control.carrier()
        else {
            panic!("register phi carrier");
        };
        let mut swapped = register_control.clone();
        let CertifiedConditionalReturnCarrier::RegisterPhi(swapped_state) = &mut swapped.carrier
        else {
            unreachable!();
        };
        let left = swapped_state.inputs[0].value.clone();
        swapped_state.inputs[0].value = swapped_state.inputs[1].value.clone();
        swapped_state.inputs[1].value = left;
        assert!(swapped.validate_against_artifact(&register).is_err());

        let mut wrong_storage = register_control.clone();
        let CertifiedConditionalReturnCarrier::RegisterPhi(wrong_state) =
            &mut wrong_storage.carrier
        else {
            unreachable!();
        };
        wrong_state.storage = storage(32, 8);
        assert!(wrong_storage.validate_against_artifact(&register).is_err());
        assert_eq!(register_state.storage(), storage(8, 8));

        let other_revision = register_artifact(b"conditional-return-cert-revision-2");
        let other_machine = crate::CertifiedMachineFunction::from_artifact(&other_revision)
            .expect("other revision machine");
        let mut wrong_revision = register_control.clone();
        wrong_revision.origin = other_machine.origin().clone();
        assert!(wrong_revision.validate_against_artifact(&register).is_err());
    }

    #[test]
    fn source_mutations_and_extra_observable_access_do_not_seal_a_funnel() {
        let mut dropped_store = stack_blocks();
        dropped_store[2].ops.remove(1);
        let artifact = SsaArtifact::for_decompile_with_interface(
            &dropped_store,
            Some(&arch()),
            interface(b"dropped-store", Some(-4), 4, storage(0, 8), false),
        )
        .expect("dropped store artifact");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("dropped store machine");
        assert!(certified.conditional_return_funnels().is_empty());

        let mut duplicated_store = stack_blocks();
        let (address_op, address) = stack_address(0x70, -4);
        duplicated_store[2].ops.insert(1, address_op);
        duplicated_store[2].ops.insert(
            2,
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: address,
                val: Varnode::constant(9, 4),
            },
        );
        let artifact = SsaArtifact::for_decompile_with_interface(
            &duplicated_store,
            Some(&arch()),
            interface(b"duplicated-store", Some(-4), 4, storage(0, 8), false),
        )
        .expect("duplicated store artifact");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("duplicated store machine");
        assert!(certified.conditional_return_funnels().is_empty());

        let mut dropped_load = stack_blocks();
        dropped_load[4].ops.remove(1);
        let artifact = SsaArtifact::for_decompile_with_interface(
            &dropped_load,
            Some(&arch()),
            interface(b"dropped-load", Some(-4), 4, storage(0, 8), false),
        )
        .expect("dropped load artifact");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("dropped load machine");
        assert!(certified.conditional_return_funnels().is_empty());

        let mut duplicated_load = stack_blocks();
        let address = match &duplicated_load[4].ops[0] {
            R2ILOp::IntAdd { dst, .. } => dst.clone(),
            _ => panic!("stack address calculation"),
        };
        duplicated_load[4].ops.insert(
            2,
            R2ILOp::Load {
                dst: Varnode::unique(0x90, 4),
                space: SpaceId::Ram,
                addr: address,
            },
        );
        let artifact = SsaArtifact::for_decompile_with_interface(
            &duplicated_load,
            Some(&arch()),
            interface(b"duplicated-load", Some(-4), 4, storage(0, 8), false),
        )
        .expect("duplicated load artifact");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("duplicated load machine");
        assert!(certified.conditional_return_funnels().is_empty());

        let mut extra_access = stack_blocks();
        let (address_op, address) = stack_address(0x80, -8);
        extra_access[3].ops.insert(1, address_op);
        extra_access[3].ops.insert(
            2,
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: address,
                val: Varnode::constant(3, 4),
            },
        );
        let artifact = SsaArtifact::for_decompile_with_interface(
            &extra_access,
            Some(&arch()),
            interface(b"extra-access", Some(-4), 4, storage(0, 8), true),
        )
        .expect("extra access artifact");
        assert_eq!(artifact.structured().conditional_return_funnels.len(), 1);
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("extra access machine");
        assert!(certified.conditional_return_funnels().is_empty());
    }

    fn mapping_manifest(certified: &crate::CertifiedMachineFunction) -> Vec<TypedRegionMapping> {
        certified
            .source()
            .obligations()
            .keys()
            .map(|obligation| {
                let [effect] = certified.ledger().effects(*obligation) else {
                    panic!("one exact disposition for {obligation}");
                };
                TypedRegionMapping::new(*obligation, effect.disposition().clone())
            })
            .collect()
    }

    fn rebind_control_origin(
        control: &mut CertifiedConditionalReturnFunnelControl,
        origin: &CertifiedArtifactOrigin,
    ) {
        control.origin = origin.clone();
        match &mut control.carrier {
            CertifiedConditionalReturnCarrier::RegisterPhi(state) => {
                state.origin = origin.clone();
            }
            CertifiedConditionalReturnCarrier::PrivateStackScalar(state) => {
                state.origin = origin.clone();
            }
        }
    }

    #[test]
    fn register_and_stack_funnels_mint_distinct_v1_render_permits() {
        for artifact in [
            register_artifact(b"conditional-return-permit-register-v1"),
            stack_artifact(b"conditional-return-permit-stack-v1"),
        ] {
            let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
                .expect("certified funnel machine");
            let control = one_control(&certified);
            let mappings = mapping_manifest(&certified);
            let permit = certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                mappings.clone(),
                control,
            )
            .expect("conditional return funnel permit");
            assert!(permit.authorizes_certified_c());
            assert!(permit.matches_region(
                certified.origin(),
                crate::CertifiedTypedRegionKind::ConditionalReturnFunnelFunction,
                CERTIFIED_CONDITIONAL_RETURN_FUNNEL_CONTRACT_VERSION,
                &mappings,
            ));

            let mut wrong_contract = permit;
            wrong_contract.region_schema_version =
                CERTIFIED_CONDITIONAL_RETURN_FUNNEL_CONTRACT_VERSION + 1;
            assert!(!wrong_contract.authorizes_certified_c());
        }
    }

    #[test]
    fn funnel_permit_rejects_origin_control_manifest_schema_and_topology_mutations() {
        let register = register_artifact(b"conditional-return-permit-register-v1");
        let certified = crate::CertifiedMachineFunction::from_artifact(&register)
            .expect("certified register funnel");
        let control = one_control(&certified);
        let mappings = mapping_manifest(&certified);

        let stack = stack_artifact(b"conditional-return-permit-stack-v1");
        let stack_certified =
            crate::CertifiedMachineFunction::from_artifact(&stack).expect("certified stack funnel");
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                mappings.clone(),
                one_control(&stack_certified),
            ),
            Err(RenderAuthorizationError::InvalidOrigin)
        ));
        assert!(matches!(
            certify_conditional_return_funnel_region(
                stack_certified.origin(),
                certified.ledger(),
                mappings.clone(),
                control,
            ),
            Err(RenderAuthorizationError::InvalidOrigin)
        ));

        let mut missing = mappings.clone();
        missing.pop();
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                missing,
                control,
            ),
            Err(RenderAuthorizationError::MissingMapping(_))
        ));

        let mut duplicate = mappings.clone();
        duplicate.push(mappings[0].clone());
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                duplicate,
                control,
            ),
            Err(RenderAuthorizationError::DuplicateMapping(_))
        ));

        let mut swapped = mappings.clone();
        let distinct = swapped
            .iter()
            .enumerate()
            .find_map(|(left, mapping)| {
                swapped
                    .iter()
                    .enumerate()
                    .find(|(_, other)| other.source_disposition != mapping.source_disposition)
                    .map(|(right, _)| (left, right))
            })
            .expect("distinct funnel dispositions");
        let left = swapped[distinct.0].source_disposition.clone();
        swapped[distinct.0].source_disposition = swapped[distinct.1].source_disposition.clone();
        swapped[distinct.1].source_disposition = left;
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                swapped,
                control,
            ),
            Err(RenderAuthorizationError::DispositionMismatch(_))
        ));

        let mut wrong_disposition = mappings.clone();
        wrong_disposition[0].source_disposition = EffectDisposition::ProvenDead;
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                wrong_disposition,
                control,
            ),
            Err(RenderAuthorizationError::DispositionMismatch(_))
        ));

        let mut wrong_schema = control.clone();
        wrong_schema.schema_version += 1;
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                certified.ledger(),
                mappings.clone(),
                &wrong_schema,
            ),
            Err(RenderAuthorizationError::InvalidRegionSchema)
        ));

        let mut wrong_origin = certified.origin().clone();
        let branch = wrong_origin
            .topology
            .blocks
            .iter_mut()
            .find(|block| block.addr == control.branch_control().producer().block_addr)
            .expect("branch block");
        branch.successors = vec![control.join_block()].into_boxed_slice();
        let mut wrong_topology = control.clone();
        rebind_control_origin(&mut wrong_topology, &wrong_origin);
        assert!(matches!(
            certify_conditional_return_funnel_region(
                &wrong_origin,
                certified.ledger(),
                mappings,
                &wrong_topology,
            ),
            Err(RenderAuthorizationError::InvalidRegionTopology)
        ));
    }

    #[test]
    fn funnel_permit_rejects_wrong_state_evidence_and_residual_ledger() {
        let artifact = register_artifact(b"conditional-return-permit-state-v1");
        let certified = crate::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("certified register funnel");
        let control = one_control(&certified);
        let mappings = mapping_manifest(&certified);
        let obligation = carrier_obligation(control.carrier());

        let mut wrong_state_ledger = certified.ledger().clone();
        let [effect] = wrong_state_ledger
            .effects
            .get_mut(&obligation)
            .expect("state effect")
            .as_mut_slice()
        else {
            panic!("one state effect");
        };
        let mut wrong_carrier = control.carrier().clone();
        let CertifiedConditionalReturnCarrier::RegisterPhi(state) = &mut wrong_carrier else {
            panic!("register carrier");
        };
        state.storage = storage(32, 8);
        effect.evidence =
            crate::DispositionEvidence::ConditionalReturnState(Box::new(wrong_carrier));
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                &wrong_state_ledger,
                mappings.clone(),
                control,
            ),
            Err(RenderAuthorizationError::IncompleteLedger)
                | Err(RenderAuthorizationError::InvalidRegionDisposition(_))
        ));

        let mut residual_ledger = certified.ledger().clone();
        let [effect] = residual_ledger
            .effects
            .get_mut(&obligation)
            .expect("state effect")
            .as_mut_slice()
        else {
            panic!("one state effect");
        };
        effect.disposition = EffectDisposition::Residualized {
            reason: "test residual".to_string(),
        };
        effect.evidence = crate::DispositionEvidence::Diagnostic;
        assert!(matches!(
            certify_conditional_return_funnel_region(
                certified.origin(),
                &residual_ledger,
                mappings,
                control,
            ),
            Err(RenderAuthorizationError::ResidualOrRefusedObligation(id)) if id == obligation
        ));
    }
}
