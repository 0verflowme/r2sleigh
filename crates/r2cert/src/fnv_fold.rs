//! Sealed certification for the canonical AArch64 O2 FNV byte fold.
//!
//! The source fact is deliberately narrow. This module binds every retained
//! identity to one artifact origin, exposes an exact block/producer manifest,
//! and assigns only the three loop carriers to dedicated state ownership.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CANONICAL_FNV_FOLD_LOOP_FACT_SCHEMA_VERSION, CallBoundarySlot, CanonicalFnvFoldCarrierFact,
    CanonicalFnvFoldLoopFact, CanonicalFnvFoldUnsignedLessWitness, CanonicalInstructionId,
    CanonicalStorageId, CanonicalStorageSpace, InstId, InstPayload, LoopId, MachineAddressSpace,
    MachineBuildError, MachineMemoryEndianness, MachineProjection, MachineValueUse, ObjectId,
    PredicateId, SSAOp, SemanticInstructionState, SemanticObligationComponent,
    SemanticObligationId, SemanticObligationInventory, SemanticObligationKind, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceTypeKind, SsaArtifact,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertificationError, CertifiedAbiParameter,
    CertifiedArtifactOrigin, CertifiedConditionalControl, CertifiedControlTruthiness,
    CertifiedExpr, CertifiedMemoryStatement, CertifiedMemoryStatementKind, CertifiedRenderPermit,
    CertifiedReturnControl, CertifiedSourceTerminator, CertifiedSourceTopology,
    CertifiedTypedRegionKind, EffectDisposition, ObligationLedger, RenderAuthorizationError,
    TypedRegionMapping,
};

pub const CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION: u32 = 1;
pub const CERTIFIED_FNV_OFFSET_BASIS: u64 = 0x1465_0fb0_739d_0383;
pub const CERTIFIED_FNV_PRIME: u64 = 0x100_0000_01b3;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedFnvFoldPhase {
    Entry,
    Setup,
    HeaderLatch,
    Exit,
}

/// Exact source order for one FNV fold phase.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldPhaseOrder {
    phase: CertifiedFnvFoldPhase,
    block: u64,
    producers: Box<[CanonicalInstructionId]>,
}

impl CertifiedFnvFoldPhaseOrder {
    pub const fn phase(&self) -> CertifiedFnvFoldPhase {
        self.phase
    }

    pub const fn block(&self) -> u64 {
        self.block
    }

    pub const fn producers(&self) -> &[CanonicalInstructionId] {
        &self.producers
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldCarrier {
    storage: CanonicalStorageId,
    width_bits: u32,
    phi: MachineValueUse,
    entry: MachineValueUse,
    update: MachineValueUse,
    update_producer: CanonicalInstructionId,
    update_support_producers: Box<[CanonicalInstructionId]>,
}

impl CertifiedFnvFoldCarrier {
    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn width_bits(&self) -> u32 {
        self.width_bits
    }

    pub const fn phi(&self) -> &MachineValueUse {
        &self.phi
    }

    pub const fn entry(&self) -> &MachineValueUse {
        &self.entry
    }

    pub const fn update(&self) -> &MachineValueUse {
        &self.update
    }

    pub const fn update_producer(&self) -> CanonicalInstructionId {
        self.update_producer
    }

    pub const fn update_support_producers(&self) -> &[CanonicalInstructionId] {
        &self.update_support_producers
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldMemoryVersion {
    object: ObjectId,
    version: u32,
}

impl CertifiedFnvFoldMemoryVersion {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn version(&self) -> u32 {
        self.version
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedFnvFoldUnsignedLess {
    Direct {
        compare: CanonicalInstructionId,
        condition_copies: Box<[CanonicalInstructionId]>,
    },
    NegatedReverseLessEqual {
        compare: CanonicalInstructionId,
        comparison_copies: Box<[CanonicalInstructionId]>,
        bool_not: CanonicalInstructionId,
        condition_copies: Box<[CanonicalInstructionId]>,
    },
}

/// Exact terminal self-loop branch used by the canonical FNV latch.
///
/// Generic conditional-control evidence intentionally excludes self targets;
/// this witness admits only the fact-bound FNV true-to-self/false-to-exit edge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldLatchControl {
    schema_version: u32,
    producer: CanonicalInstructionId,
    source_inst: InstId,
    true_target: u64,
    false_target: u64,
    target_value: MachineValueUse,
    condition: MachineValueUse,
    truthiness: CertifiedControlTruthiness,
    predicate_obligation: SemanticObligationId,
    transfer_obligation: SemanticObligationId,
}

impl CertifiedFnvFoldLatchControl {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub(crate) const fn source_inst(&self) -> InstId {
        self.source_inst
    }

    pub const fn true_target(&self) -> u64 {
        self.true_target
    }

    pub const fn false_target(&self) -> u64 {
        self.false_target
    }

    pub const fn target_value(&self) -> &MachineValueUse {
        &self.target_value
    }

    pub const fn condition(&self) -> &MachineValueUse {
        &self.condition
    }

    pub const fn truthiness(&self) -> CertifiedControlTruthiness {
        self.truthiness
    }

    pub const fn predicate_obligation(&self) -> SemanticObligationId {
        self.predicate_obligation
    }

    pub const fn transfer_obligation(&self) -> SemanticObligationId {
        self.transfer_obligation
    }

    pub fn source_obligations(&self) -> BTreeSet<SemanticObligationId> {
        BTreeSet::from([self.predicate_obligation, self.transfer_obligation])
    }

    pub(crate) fn validate(
        &self,
        source: &SemanticObligationInventory,
    ) -> Result<(), CertificationError> {
        super::validate_schema(self.schema_version)?;
        if self.true_target != self.producer.block_addr
            || self.false_target == self.true_target
            || self.truthiness != CertifiedControlTruthiness::NonZeroIsTrue
            || self.condition.binding().width_bits() != 8
            || self.predicate_obligation.instruction != self.producer
            || self.predicate_obligation.kind != SemanticObligationKind::ControlPredicate
            || self.predicate_obligation.component != SemanticObligationComponent::Whole
            || self.transfer_obligation.instruction != self.producer
            || self.transfer_obligation.kind != SemanticObligationKind::ControlTransfer
            || self.transfer_obligation.component != SemanticObligationComponent::Whole
        {
            return Err(CertificationError::ObligationNotMapped(
                self.transfer_obligation,
            ));
        }
        let predicate = source.obligations().get(&self.predicate_obligation).ok_or(
            CertificationError::UnknownObligation(self.predicate_obligation),
        )?;
        let transfer = source.obligations().get(&self.transfer_obligation).ok_or(
            CertificationError::UnknownObligation(self.transfer_obligation),
        )?;
        if source
            .instructions()
            .get(&self.producer)
            .is_none_or(|instruction| {
                instruction.inst != self.source_inst
                    || instruction.obligations != self.source_obligations()
            })
            || predicate.source_inst != self.source_inst
            || predicate.inputs != [self.condition.binding().value()]
            || transfer.source_inst != self.source_inst
            || transfer.inputs
                != [
                    self.target_value.binding().value(),
                    self.condition.binding().value(),
                ]
        {
            return Err(CertificationError::ObligationNotMapped(
                self.transfer_obligation,
            ));
        }
        Ok(())
    }
}

/// Sealed whole-function witness for the canonical FNV fold loop.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldLoop {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    revision_identity: Box<[u8]>,
    loop_id: LoopId,
    entry: u64,
    setup: u64,
    header_latch: u64,
    exit: u64,
    pointer_parameter: CertifiedAbiParameter,
    remaining_parameter: CertifiedAbiParameter,
    return_storage: CanonicalStorageId,
    pointer_logical: SourceLogicalValue,
    remaining_logical: SourceLogicalValue,
    return_logical: SourceLogicalValue,
    pointer: CertifiedFnvFoldCarrier,
    remaining: CertifiedFnvFoldCarrier,
    hash: CertifiedFnvFoldCarrier,
    pointer_entry_copy: CanonicalInstructionId,
    load_address: MachineValueUse,
    load_address_copy: CanonicalInstructionId,
    offset_basis: u64,
    initializer_producer: CanonicalInstructionId,
    initializer_witness: Box<[CanonicalInstructionId]>,
    exit_phi: MachineValueUse,
    exit_phi_producer: CanonicalInstructionId,
    byte_load: CertifiedMemoryStatement,
    memory_version: CertifiedFnvFoldMemoryVersion,
    raw_byte: MachineValueUse,
    byte64: MachineValueUse,
    byte64_zext: CanonicalInstructionId,
    byte32_for_range: MachineValueUse,
    byte32_for_lower: MachineValueUse,
    byte32_original: MachineValueUse,
    range: MachineValueUse,
    range_producer: CanonicalInstructionId,
    lowercase: MachineValueUse,
    lowercase_producer: CanonicalInstructionId,
    uppercase: MachineValueUse,
    ascii_predicate: CertifiedFnvFoldUnsignedLess,
    selected: MachineValueUse,
    select_producer: CanonicalInstructionId,
    true_identity_producers: Box<[CanonicalInstructionId]>,
    false_identity_producers: Box<[CanonicalInstructionId]>,
    lowercase_on_true: bool,
    selected64: MachineValueUse,
    selected64_zext: CanonicalInstructionId,
    xor: MachineValueUse,
    xor_producer: CanonicalInstructionId,
    prime: MachineValueUse,
    prime_value: u64,
    prime_producer: CanonicalInstructionId,
    prime_witness: Box<[CanonicalInstructionId]>,
    product: MachineValueUse,
    multiply_producer: CanonicalInstructionId,
    zero_predicate: PredicateId,
    zero_condition: MachineValueUse,
    zero_condition_producer: CanonicalInstructionId,
    zero_control: CertifiedConditionalControl,
    latch_predicate: PredicateId,
    latch_condition: MachineValueUse,
    latch_condition_producer: CanonicalInstructionId,
    latch_control: CertifiedFnvFoldLatchControl,
    returned: MachineValueUse,
    return_control: CertifiedReturnControl,
    phase_order: Box<[CertifiedFnvFoldPhaseOrder]>,
    visible_expressions: BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    state_producers: BTreeSet<CanonicalInstructionId>,
    state_obligations: BTreeSet<SemanticObligationId>,
}

impl CertifiedFnvFoldLoop {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn contract_version(&self) -> u32 {
        self.contract_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn loop_id(&self) -> LoopId {
        self.loop_id
    }

    pub const fn entry(&self) -> u64 {
        self.entry
    }

    pub const fn setup(&self) -> u64 {
        self.setup
    }

    pub const fn header_latch(&self) -> u64 {
        self.header_latch
    }

    pub const fn exit(&self) -> u64 {
        self.exit
    }

    pub const fn pointer_parameter(&self) -> &CertifiedAbiParameter {
        &self.pointer_parameter
    }

    pub const fn remaining_parameter(&self) -> &CertifiedAbiParameter {
        &self.remaining_parameter
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn pointer_logical(&self) -> SourceLogicalValue {
        self.pointer_logical
    }

    pub const fn remaining_logical(&self) -> SourceLogicalValue {
        self.remaining_logical
    }

    pub const fn return_logical(&self) -> SourceLogicalValue {
        self.return_logical
    }

    pub const fn pointer(&self) -> &CertifiedFnvFoldCarrier {
        &self.pointer
    }

    pub const fn remaining(&self) -> &CertifiedFnvFoldCarrier {
        &self.remaining
    }

    pub const fn hash(&self) -> &CertifiedFnvFoldCarrier {
        &self.hash
    }

    pub const fn load_address(&self) -> &MachineValueUse {
        &self.load_address
    }

    pub const fn pointer_entry_copy(&self) -> CanonicalInstructionId {
        self.pointer_entry_copy
    }

    pub const fn load_address_copy(&self) -> CanonicalInstructionId {
        self.load_address_copy
    }

    pub const fn offset_basis(&self) -> u64 {
        self.offset_basis
    }

    pub const fn initializer_producer(&self) -> CanonicalInstructionId {
        self.initializer_producer
    }

    pub const fn initializer_witness(&self) -> &[CanonicalInstructionId] {
        &self.initializer_witness
    }

    pub const fn exit_phi(&self) -> &MachineValueUse {
        &self.exit_phi
    }

    pub const fn exit_phi_producer(&self) -> CanonicalInstructionId {
        self.exit_phi_producer
    }

    pub const fn byte_load(&self) -> &CertifiedMemoryStatement {
        &self.byte_load
    }

    pub const fn memory_version(&self) -> CertifiedFnvFoldMemoryVersion {
        self.memory_version
    }

    pub const fn raw_byte(&self) -> &MachineValueUse {
        &self.raw_byte
    }

    pub const fn byte64(&self) -> &MachineValueUse {
        &self.byte64
    }

    pub const fn byte64_zext(&self) -> CanonicalInstructionId {
        self.byte64_zext
    }

    pub const fn byte32_for_range(&self) -> &MachineValueUse {
        &self.byte32_for_range
    }

    pub const fn byte32_for_lower(&self) -> &MachineValueUse {
        &self.byte32_for_lower
    }

    pub const fn byte32_original(&self) -> &MachineValueUse {
        &self.byte32_original
    }

    pub const fn range(&self) -> &MachineValueUse {
        &self.range
    }

    pub const fn range_producer(&self) -> CanonicalInstructionId {
        self.range_producer
    }

    pub const fn lowercase(&self) -> &MachineValueUse {
        &self.lowercase
    }

    pub const fn lowercase_producer(&self) -> CanonicalInstructionId {
        self.lowercase_producer
    }

    pub const fn uppercase(&self) -> &MachineValueUse {
        &self.uppercase
    }

    pub const fn ascii_predicate(&self) -> &CertifiedFnvFoldUnsignedLess {
        &self.ascii_predicate
    }

    pub const fn lowercase_on_true(&self) -> bool {
        self.lowercase_on_true
    }

    pub const fn selected(&self) -> &MachineValueUse {
        &self.selected
    }

    pub const fn select_producer(&self) -> CanonicalInstructionId {
        self.select_producer
    }

    pub const fn true_identity_producers(&self) -> &[CanonicalInstructionId] {
        &self.true_identity_producers
    }

    pub const fn false_identity_producers(&self) -> &[CanonicalInstructionId] {
        &self.false_identity_producers
    }

    pub const fn selected64(&self) -> &MachineValueUse {
        &self.selected64
    }

    pub const fn selected64_zext(&self) -> CanonicalInstructionId {
        self.selected64_zext
    }

    pub const fn xor(&self) -> &MachineValueUse {
        &self.xor
    }

    pub const fn xor_producer(&self) -> CanonicalInstructionId {
        self.xor_producer
    }

    pub const fn prime(&self) -> &MachineValueUse {
        &self.prime
    }

    pub const fn prime_value(&self) -> u64 {
        self.prime_value
    }

    pub const fn prime_producer(&self) -> CanonicalInstructionId {
        self.prime_producer
    }

    pub const fn prime_witness(&self) -> &[CanonicalInstructionId] {
        &self.prime_witness
    }

    pub const fn product(&self) -> &MachineValueUse {
        &self.product
    }

    pub const fn multiply_producer(&self) -> CanonicalInstructionId {
        self.multiply_producer
    }

    pub const fn zero_predicate(&self) -> PredicateId {
        self.zero_predicate
    }

    pub const fn zero_condition(&self) -> &MachineValueUse {
        &self.zero_condition
    }

    pub const fn zero_condition_producer(&self) -> CanonicalInstructionId {
        self.zero_condition_producer
    }

    pub const fn zero_control(&self) -> &CertifiedConditionalControl {
        &self.zero_control
    }

    pub const fn latch_control(&self) -> &CertifiedFnvFoldLatchControl {
        &self.latch_control
    }

    pub const fn latch_predicate(&self) -> PredicateId {
        self.latch_predicate
    }

    pub const fn latch_condition(&self) -> &MachineValueUse {
        &self.latch_condition
    }

    pub const fn latch_condition_producer(&self) -> CanonicalInstructionId {
        self.latch_condition_producer
    }

    pub const fn return_control(&self) -> &CertifiedReturnControl {
        &self.return_control
    }

    pub const fn returned(&self) -> &MachineValueUse {
        &self.returned
    }

    pub const fn phase_order(&self) -> &[CertifiedFnvFoldPhaseOrder] {
        &self.phase_order
    }

    pub fn expression_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedExpr> {
        self.visible_expressions.get(&producer)
    }

    pub fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.state_obligations
    }

    pub(crate) fn owns_obligation(
        &self,
        source: &SemanticObligationInventory,
        obligation: SemanticObligationId,
        producer: CanonicalInstructionId,
    ) -> bool {
        self.validate(source).is_ok()
            && obligation.instruction == producer
            && self.state_producers.contains(&producer)
            && self.state_obligations.contains(&obligation)
    }

    pub(crate) fn validate(
        &self,
        source: &SemanticObligationInventory,
    ) -> Result<(), CertificationError> {
        super::validate_schema(self.schema_version)?;
        if self.contract_version != CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION
            || self.origin.source() != source
            || !self
                .origin
                .matches_retained_source(source, self.origin.topology())
            || !self.abi_is_exact()
            || !self.topology_is_exact()
            || !self.phase_order_is_exact(source)
            || !self.carriers_are_exact(source)
            || !self.values_are_exact()
            || !self.byte_read_is_exact(source)
            || !self.obligation_surface_is_exact(source)
        {
            return Err(unmapped(self.zero_control.producer()));
        }
        for expression in self.visible_expressions.values() {
            expression.validate(source)?;
        }
        self.byte_load.validate(source)?;
        self.zero_control.validate(source)?;
        self.latch_control.validate(source)?;
        self.return_control.validate(source)?;
        Ok(())
    }

    fn abi_is_exact(&self) -> bool {
        let Some(interface) = self.origin.machine_context().source().function_interface() else {
            return false;
        };
        let Some(graph) = interface.type_graph() else {
            return false;
        };
        let [byte_type, pointer_type, integer_type] = graph.types() else {
            return false;
        };
        let full64 = |logical: SourceLogicalValue| {
            logical.carrier().kind() == SourceCarrierKind::Full
                && logical.carrier().offset_bits() == 0
                && logical.carrier().size_bits() == 64
        };
        interface.revision_identity() == self.revision_identity.as_ref()
            && interface
                .calling_convention()
                .eq_ignore_ascii_case("aapcs64")
            && interface.stack_slots().is_empty()
            && interface.stack_slot_roles_complete()
            && graph.aggregates().is_empty()
            && matches!(
                pointer_type.kind(),
                SourceTypeKind::Pointer { target_type_id: 0 }
            )
            && pointer_type.size_bits() == 64
            && pointer_type.align_bits() == 64
            && byte_type.kind() == SourceTypeKind::UnsignedInteger
            && byte_type.size_bits() == 8
            && byte_type.align_bits() == 8
            && integer_type.kind() == SourceTypeKind::UnsignedInteger
            && integer_type.size_bits() == 64
            && integer_type.align_bits() == 64
            && interface.parameter_logical_values()
                == [self.pointer_logical, self.remaining_logical]
            && interface.return_logical_value() == Some(self.return_logical)
            && self.pointer_logical.type_id() == 1
            && self.remaining_logical.type_id() == 2
            && self.return_logical.type_id() == 2
            && full64(self.pointer_logical)
            && full64(self.remaining_logical)
            && full64(self.return_logical)
            && matches!(interface.parameters(), [pointer, remaining]
                if pointer.index() == 0
                    && remaining.index() == 1
                    && pointer.storage() == self.pointer_parameter.storage()
                    && remaining.storage() == self.remaining_parameter.storage())
            && self.pointer_parameter.index() == 0
            && self.remaining_parameter.index() == 1
            && self.pointer_parameter.storage().size == 8
            && self.remaining_parameter.storage().size == 8
            && self.pointer_parameter.value().is_some_and(|value| {
                value.producer().is_none() && value.binding().width_bits() == 64
            })
            && self.remaining_parameter.value().is_some_and(|value| {
                value.producer().is_none()
                    && value.binding().width_bits() == 64
                    && value.binding().value() == self.remaining.entry.binding().value()
            })
            && matches!(interface.return_kind(), SourceFunctionReturn::Register { storage }
                if storage == self.return_storage && storage.size == 8)
            && self.hash.storage == self.return_storage
    }

    fn topology_is_exact(&self) -> bool {
        let topology = self.origin.topology();
        let (Some(entry), Some(setup), Some(header), Some(exit)) = (
            topology.block(self.entry),
            topology.block(self.setup),
            topology.block(self.header_latch),
            topology.block(self.exit),
        ) else {
            return false;
        };
        topology.entry_addr() == self.entry
            && topology.blocks().len() == 4
            && BTreeSet::from([self.entry, self.setup, self.header_latch, self.exit]).len() == 4
            && entry.predecessors().is_empty()
            && entry.successors().iter().copied().collect::<BTreeSet<_>>()
                == BTreeSet::from([self.setup, self.exit])
            && matches!(entry.terminator(), CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } if *true_target == self.exit && *false_target == self.setup)
            && setup.predecessors() == [self.entry]
            && setup.successors() == [self.header_latch]
            && matches!(setup.terminator(), CertifiedSourceTerminator::Fallthrough { next }
                if *next == self.header_latch)
            && header
                .predecessors()
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                == BTreeSet::from([self.setup, self.header_latch])
            && header.successors().iter().copied().collect::<BTreeSet<_>>()
                == BTreeSet::from([self.header_latch, self.exit])
            && matches!(header.terminator(), CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } if *true_target == self.header_latch && *false_target == self.exit)
            && exit.predecessors().iter().copied().collect::<BTreeSet<_>>()
                == BTreeSet::from([self.entry, self.header_latch])
            && exit.successors().is_empty()
            && matches!(exit.terminator(), CertifiedSourceTerminator::Return)
            && self.zero_control.true_target() == self.exit
            && self.zero_control.false_target() == self.setup
            && self.latch_control.true_target() == self.header_latch
            && self.latch_control.false_target() == self.exit
    }

    fn phase_order_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let expected = [
            (CertifiedFnvFoldPhase::Entry, self.entry),
            (CertifiedFnvFoldPhase::Setup, self.setup),
            (CertifiedFnvFoldPhase::HeaderLatch, self.header_latch),
            (CertifiedFnvFoldPhase::Exit, self.exit),
        ];
        let manifest_producers = self
            .phase_order
            .iter()
            .flat_map(|phase| phase.producers.iter().copied())
            .collect::<Vec<_>>();
        self.phase_order.len() == expected.len()
            && self
                .phase_order
                .iter()
                .zip(expected)
                .all(|(phase, (expected_phase, block))| {
                    phase.phase == expected_phase
                        && phase.block == block
                        && self
                            .origin
                            .topology()
                            .block(block)
                            .is_some_and(|source_block| {
                                source_block.instructions() == phase.producers.as_ref()
                            })
                })
            && manifest_producers
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .len()
                == manifest_producers.len()
            && manifest_producers.iter().copied().collect::<BTreeSet<_>>()
                == source
                    .instructions()
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
    }

    fn carriers_are_exact(&self, source: &SemanticObligationInventory) -> bool {
        let carriers = [&self.pointer, &self.remaining, &self.hash];
        carriers.iter().all(|carrier| {
            carrier.width_bits == 64
                && carrier.storage.size == 8
                && carrier.storage.space == CanonicalStorageSpace::Register
                && carrier.phi.binding().width_bits() == 64
                && carrier.entry.binding().width_bits() == 64
                && carrier.update.binding().width_bits() == 64
                && carrier.phi.producer().is_some()
                && carrier.update.producer().is_some()
                && self.carrier_state_is_exact(source, carrier)
        }) && BTreeSet::from([
            self.pointer.storage,
            self.remaining.storage,
            self.hash.storage,
        ])
        .len()
            == 3
            && self.pointer_parameter.storage() == self.hash.storage
            && self.remaining_parameter.storage() == self.remaining.storage
            && self.pointer.storage != self.pointer_parameter.storage()
            && self.hash.entry.binding().value() != self.hash.phi.binding().value()
            && self.hash.update.binding().value() == self.product.binding().value()
            && self.exit_phi.binding().value() == self.returned.binding().value()
    }

    fn carrier_state_is_exact(
        &self,
        source: &SemanticObligationInventory,
        carrier: &CertifiedFnvFoldCarrier,
    ) -> bool {
        let Some(producer) = carrier.phi.producer() else {
            return false;
        };
        let expected = BTreeSet::from([
            SemanticObligationId {
                instruction: producer,
                kind: SemanticObligationKind::LiveValueProducer,
                component: SemanticObligationComponent::Whole,
            },
            SemanticObligationId {
                instruction: producer,
                kind: SemanticObligationKind::LoopCarriedState,
                component: SemanticObligationComponent::Whole,
            },
            SemanticObligationId {
                instruction: producer,
                kind: SemanticObligationKind::LiveStateTransition,
                component: SemanticObligationComponent::LoopTransition {
                    carrier: carrier.storage,
                    predecessor: self.header_latch,
                },
            },
        ]);
        source
            .instructions()
            .get(&producer)
            .is_some_and(|instruction| instruction.obligations == expected)
            && expected.iter().all(|obligation| {
                source
                    .obligations()
                    .get(obligation)
                    .is_some_and(|fact| match obligation.kind {
                        SemanticObligationKind::LiveValueProducer
                        | SemanticObligationKind::LoopCarriedState => {
                            fact.inputs.len() == 2
                                && fact.inputs.iter().copied().collect::<BTreeSet<_>>()
                                    == BTreeSet::from([
                                        carrier.entry.binding().value(),
                                        carrier.update.binding().value(),
                                    ])
                        }
                        SemanticObligationKind::LiveStateTransition => {
                            fact.inputs == [carrier.update.binding().value()]
                        }
                        _ => false,
                    })
            })
    }

    fn values_are_exact(&self) -> bool {
        let produced_by = |value: &MachineValueUse, producer| value.producer() == Some(producer);
        produced_by(&self.range, self.range_producer)
            && produced_by(&self.lowercase, self.lowercase_producer)
            && produced_by(&self.selected, self.select_producer)
            && produced_by(&self.selected64, self.selected64_zext)
            && produced_by(&self.xor, self.xor_producer)
            && produced_by(&self.prime, self.prime_producer)
            && produced_by(&self.product, self.multiply_producer)
            && produced_by(&self.zero_condition, self.zero_condition_producer)
            && produced_by(&self.latch_condition, self.latch_condition_producer)
            && produced_by(&self.exit_phi, self.exit_phi_producer)
            && self.zero_control.condition() == &self.zero_condition
            && self.latch_control.condition() == &self.latch_condition
            && self.returned == self.exit_phi
            && matches!(self.return_control.values(), [returned]
                if returned.slot() == (CallBoundarySlot::Register {
                    index: 0,
                    storage: self.return_storage,
                }) && returned.value() == &self.returned)
            && self.offset_basis == CERTIFIED_FNV_OFFSET_BASIS
            && self.prime_value == CERTIFIED_FNV_PRIME
            && self.lowercase_on_true
            && self.raw_byte.binding().width_bits() == 8
            && self.byte64.binding().width_bits() == 64
            && self.byte32_for_range.binding().width_bits() == 32
            && self.byte32_for_lower.binding().width_bits() == 32
            && self.byte32_original.binding().width_bits() == 32
            && self.range.binding().width_bits() == 32
            && self.lowercase.binding().width_bits() == 32
            && self.uppercase.binding().width_bits() == 8
            && self.selected.binding().width_bits() == 32
            && self.selected64.binding().width_bits() == 64
            && self.xor.binding().width_bits() == 64
            && self.prime.binding().width_bits() == 64
            && self.product.binding().width_bits() == 64
            && self.zero_condition.binding().width_bits() == 8
            && self.latch_condition.binding().width_bits() == 8
            && self.returned.binding().width_bits() == 64
            && self.zero_predicate != self.latch_predicate
            && self.structural_producers_are_manifest_bound()
            && self.predicate_producers_are_manifest_bound()
    }

    fn structural_producers_are_manifest_bound(&self) -> bool {
        let manifest = self
            .phase_order
            .iter()
            .flat_map(|phase| phase.producers.iter().copied())
            .collect::<BTreeSet<_>>();
        let required = [
            self.pointer_entry_copy,
            self.load_address_copy,
            self.initializer_producer,
            self.exit_phi_producer,
            self.byte64_zext,
            self.range_producer,
            self.lowercase_producer,
            self.select_producer,
            self.selected64_zext,
            self.xor_producer,
            self.prime_producer,
            self.multiply_producer,
            self.zero_condition_producer,
            self.zero_control.producer(),
            self.latch_condition_producer,
            self.latch_control.producer(),
            self.return_control.producer(),
            self.pointer.update_producer,
            self.remaining.update_producer,
            self.hash.update_producer,
        ];
        let identity = self
            .pointer
            .update_support_producers
            .iter()
            .chain(&self.remaining.update_support_producers)
            .chain(&self.hash.update_support_producers)
            .chain(self.initializer_witness.iter())
            .chain(self.true_identity_producers.iter())
            .chain(self.false_identity_producers.iter())
            .chain(self.prime_witness.iter());
        required.iter().all(|producer| manifest.contains(producer))
            && identity
                .into_iter()
                .all(|producer| manifest.contains(producer))
            && self.pointer.entry.producer() == Some(self.pointer_entry_copy)
            && self.load_address.producer() == Some(self.load_address_copy)
            && self.hash.entry.producer() == Some(self.initializer_producer)
            && self.byte64.producer() == Some(self.byte64_zext)
    }

    fn predicate_producers_are_manifest_bound(&self) -> bool {
        let manifest = self
            .phase_order
            .iter()
            .flat_map(|phase| phase.producers.iter().copied())
            .collect::<BTreeSet<_>>();
        let all_present = |producers: &[CanonicalInstructionId]| {
            producers.iter().all(|producer| manifest.contains(producer))
        };
        match &self.ascii_predicate {
            CertifiedFnvFoldUnsignedLess::Direct {
                compare,
                condition_copies,
            } => manifest.contains(compare) && all_present(condition_copies),
            CertifiedFnvFoldUnsignedLess::NegatedReverseLessEqual {
                compare,
                comparison_copies,
                bool_not,
                condition_copies,
            } => {
                manifest.contains(compare)
                    && all_present(comparison_copies)
                    && manifest.contains(bool_not)
                    && all_present(condition_copies)
            }
        }
    }

    fn byte_read_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let result = match self.byte_load.kind() {
            CertifiedMemoryStatementKind::Read { result } => result,
            CertifiedMemoryStatementKind::Write { .. } => return false,
        };
        let spaces = self
            .origin
            .machine_context()
            .memory_model()
            .spaces()
            .iter()
            .filter(|space| MachineAddressSpace::from(space.space()) == self.byte_load.space())
            .collect::<Vec<_>>();
        let [space] = spaces.as_slice() else {
            return false;
        };
        self.byte_load.access().ordinal == 0
            && self.byte_load.object() == self.memory_version.object
            && self.memory_version.version == 0
            && self.byte_load.address() == &self.load_address
            && result == &self.raw_byte
            && self.byte_load.width_bits() == 8
            && self.byte_load.word_size_bytes() == 1
            && space.address_bits() == 64
            && space.word_size_bytes() == self.byte_load.word_size_bytes()
            && space.endianness() == self.byte_load.endianness()
            && matches!(
                self.byte_load.endianness(),
                MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
            )
            && self.byte_load.producer().block_addr == self.header_latch
            && self.byte_load.source_obligations().len() == 1
            && self
                .byte_load
                .source_obligations()
                .iter()
                .all(|obligation| {
                    obligation.kind == SemanticObligationKind::ObservableMemoryRead
                        && source.obligations().contains_key(obligation)
                })
    }

    fn obligation_surface_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let expected_state = self
            .state_producers
            .iter()
            .filter_map(|producer| source.instructions().get(producer))
            .flat_map(|instruction| instruction.obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let expression_obligations = self
            .visible_expressions
            .iter()
            .flat_map(|(producer, expression)| {
                (*producer == expression.entity().producer())
                    .then_some(expression.entity().source_obligations().iter().copied())
                    .into_iter()
                    .flatten()
            })
            .collect::<BTreeSet<_>>();
        let mut visible = expression_obligations.clone();
        visible.extend(self.byte_load.source_obligations());
        visible.extend(self.zero_control.source_obligations());
        visible.extend(self.latch_control.source_obligations());
        visible.extend(self.return_control.source_obligations());
        let all = source
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let expected_visible_live = all
            .iter()
            .copied()
            .filter(|obligation| {
                obligation.kind == SemanticObligationKind::LiveValueProducer
                    && !self.state_obligations.contains(obligation)
            })
            .collect::<BTreeSet<_>>();
        expected_state == self.state_obligations
            && self.state_producers
                == BTreeSet::from([
                    self.pointer
                        .phi
                        .producer()
                        .unwrap_or(self.zero_control.producer()),
                    self.remaining
                        .phi
                        .producer()
                        .unwrap_or(self.zero_control.producer()),
                    self.hash
                        .phi
                        .producer()
                        .unwrap_or(self.zero_control.producer()),
                ])
            && self.state_obligations.is_disjoint(&visible)
            && expression_obligations == expected_visible_live
            && self
                .state_obligations
                .union(&visible)
                .copied()
                .collect::<BTreeSet<_>>()
                == all
            && source.instructions().values().all(|instruction| {
                instruction.state != SemanticInstructionState::UnsupportedUnknown
            })
            && all.iter().all(|obligation| {
                matches!(
                    obligation.kind,
                    SemanticObligationKind::LiveValueProducer
                        | SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::LoopCarriedState
                        | SemanticObligationKind::LiveStateTransition
                        | SemanticObligationKind::ControlPredicate
                        | SemanticObligationKind::ControlTransfer
                        | SemanticObligationKind::Return
                        | SemanticObligationKind::ReturnValue
                )
            })
    }

    #[cfg(test)]
    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let projection = MachineProjection::from_artifact(artifact)?;
        if !projection.failures().is_empty() {
            return Err(projection.failures()[0].error().clone());
        }
        let machine_context = super::CertifiedMachineContext::from_artifact(artifact)?;
        let topology = super::certified_source_topology(artifact)?;
        let origin = super::certified_artifact_origin(artifact, &machine_context, &topology)?;
        let parameters = super::certified_abi_parameters(artifact)?;
        let statements = super::certified_memory_statements(artifact)?;
        let controls = super::certified_conditional_controls(artifact, &topology)?;
        let returns = super::certified_return_controls(artifact, &topology)?;
        let expressions = certified_expressions(artifact, &projection)?;
        let expected = certified_fnv_fold_loop(
            artifact,
            &origin,
            &topology,
            &projection,
            &parameters,
            &statements,
            &controls,
            &returns,
            &expressions,
        )?
        .ok_or(MachineBuildError::TopologyMismatch)?;
        if expected == *self {
            Ok(())
        } else {
            Err(MachineBuildError::TopologyMismatch)
        }
    }
}

fn unmapped(producer: CanonicalInstructionId) -> CertificationError {
    CertificationError::ObligationNotMapped(SemanticObligationId {
        instruction: producer,
        kind: SemanticObligationKind::LiveValueProducer,
        component: SemanticObligationComponent::Whole,
    })
}

fn canonical(artifact: &SsaArtifact, inst: InstId) -> Option<CanonicalInstructionId> {
    artifact
        .obligations()
        .instruction_for_inst(inst)
        .map(|instruction| instruction.id)
}

fn canonical_insts(
    artifact: &SsaArtifact,
    insts: &[InstId],
) -> Result<Box<[CanonicalInstructionId]>, MachineBuildError> {
    insts
        .iter()
        .map(|inst| {
            canonical(artifact, *inst)
                .ok_or(MachineBuildError::MissingInstructionDisposition(*inst))
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Vec::into_boxed_slice)
}

fn carrier(
    artifact: &SsaArtifact,
    fact: &CanonicalFnvFoldCarrierFact,
) -> Result<CertifiedFnvFoldCarrier, MachineBuildError> {
    let phi = MachineValueUse::from_artifact(artifact, fact.phi)?;
    let entry = MachineValueUse::from_artifact(artifact, fact.entry)?;
    let update = MachineValueUse::from_artifact(artifact, fact.update)?;
    let phi_producer = canonical(artifact, fact.phi_inst).ok_or(
        MachineBuildError::MissingInstructionDisposition(fact.phi_inst),
    )?;
    let update_producer = canonical(artifact, fact.update_inst).ok_or(
        MachineBuildError::MissingInstructionDisposition(fact.update_inst),
    )?;
    if phi.producer() != Some(phi_producer) || fact.width.checked_mul(8) != Some(64) {
        return Err(MachineBuildError::EntityMismatch(fact.phi_inst));
    }
    Ok(CertifiedFnvFoldCarrier {
        storage: fact.storage,
        width_bits: 64,
        phi,
        entry,
        update,
        update_producer,
        update_support_producers: canonical_insts(artifact, &fact.update_support_insts)?,
    })
}

fn latch_control(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    fact: &CanonicalFnvFoldLoopFact,
) -> Result<CertifiedFnvFoldLatchControl, MachineBuildError> {
    let source_inst = fact.latch.branch_inst;
    let producer = canonical(artifact, source_inst).ok_or(
        MachineBuildError::MissingInstructionDisposition(source_inst),
    )?;
    topology
        .block(fact.topology.header_latch)
        .filter(|block| {
            block.instructions().last() == Some(&producer)
                && block.successors().iter().copied().collect::<BTreeSet<_>>()
                    == BTreeSet::from([fact.topology.header_latch, fact.topology.exit])
                && matches!(block.terminator(), CertifiedSourceTerminator::ConditionalBranch {
                    true_target,
                    false_target,
                } if *true_target == fact.topology.header_latch
                    && *false_target == fact.topology.exit)
        })
        .ok_or(MachineBuildError::TopologyMismatch)?;
    let instruction = artifact
        .obligations()
        .instructions()
        .get(&producer)
        .filter(|instruction| {
            instruction.inst == source_inst
                && instruction.state == SemanticInstructionState::LiveObligation
        })
        .ok_or(MachineBuildError::ObligationMismatch(source_inst))?;
    let predicate_obligation = SemanticObligationId {
        instruction: producer,
        kind: SemanticObligationKind::ControlPredicate,
        component: SemanticObligationComponent::Whole,
    };
    let transfer_obligation = SemanticObligationId {
        instruction: producer,
        kind: SemanticObligationKind::ControlTransfer,
        component: SemanticObligationComponent::Whole,
    };
    if instruction.obligations != BTreeSet::from([predicate_obligation, transfer_obligation]) {
        return Err(MachineBuildError::ObligationMismatch(source_inst));
    }
    let inst = artifact
        .graph()
        .inst(source_inst)
        .filter(|inst| {
            inst.output.is_none()
                && matches!(inst.payload, InstPayload::Op(SSAOp::CBranch { .. }))
                && inst.inputs.len() == 2
                && inst.inputs[1] == fact.latch.condition
        })
        .ok_or(MachineBuildError::EntityMismatch(source_inst))?;
    let (block_addr, op_index) = artifact
        .graph()
        .op_site_for_inst(source_inst)
        .ok_or(MachineBuildError::TopologyMismatch)?;
    let source_block = artifact
        .function()
        .get_block(fact.topology.header_latch)
        .ok_or(MachineBuildError::TopologyMismatch)?;
    if block_addr != fact.topology.header_latch
        || op_index + 1 != source_block.ops.len()
        || fact
            .topology
            .header_latch
            .checked_add(u64::from(source_block.size))
            != Some(fact.topology.exit)
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let target_value = MachineValueUse::from_artifact(artifact, inst.inputs[0])?;
    let condition = MachineValueUse::from_artifact(artifact, inst.inputs[1])?;
    if condition.binding().value() != fact.latch.condition
        || target_value.binding().width_bits() != 64
        || target_value.constant().is_some_and(|target| {
            target.width_bits() != 64 || target.bits() != fact.topology.header_latch
        })
    {
        return Err(MachineBuildError::EntityMismatch(source_inst));
    }
    let control = CertifiedFnvFoldLatchControl {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        producer,
        source_inst,
        true_target: fact.topology.header_latch,
        false_target: fact.topology.exit,
        target_value,
        condition,
        truthiness: CertifiedControlTruthiness::NonZeroIsTrue,
        predicate_obligation,
        transfer_obligation,
    };
    control
        .validate(artifact.obligations())
        .map_err(|_| MachineBuildError::ObligationMismatch(source_inst))?;
    Ok(control)
}

fn single_fact(
    facts: &BTreeMap<u64, CanonicalFnvFoldLoopFact>,
) -> Result<Option<&CanonicalFnvFoldLoopFact>, MachineBuildError> {
    let mut facts = facts.values();
    let Some(fact) = facts.next() else {
        return Ok(None);
    };
    if facts.next().is_some() {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(Some(fact))
}

fn exact_fact(
    artifact: &SsaArtifact,
) -> Result<Option<&CanonicalFnvFoldLoopFact>, MachineBuildError> {
    let facts = &artifact.structured().canonical_fnv_fold_loops;
    let Some(fact) = single_fact(facts)? else {
        return Ok(None);
    };
    if facts.get(&fact.topology.header_latch) != Some(fact)
        || fact.schema_version != CANONICAL_FNV_FOLD_LOOP_FACT_SCHEMA_VERSION
        || !fact.validate_against(artifact)
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(Some(fact))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn certified_fnv_fold_loop(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    projection: &MachineProjection,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
) -> Result<Option<CertifiedFnvFoldLoop>, MachineBuildError> {
    let Some(fact) = exact_fact(artifact)? else {
        return Ok(None);
    };
    if !projection.failures().is_empty()
        || origin.source() != artifact.obligations()
        || origin.topology() != topology
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    build_fnv_fold(
        artifact,
        origin,
        topology,
        abi_parameters,
        memory_statements,
        conditional_controls,
        return_controls,
        expressions,
        fact,
    )
    .map(Some)
}

#[allow(clippy::too_many_arguments)]
fn build_fnv_fold(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    fact: &CanonicalFnvFoldLoopFact,
) -> Result<CertifiedFnvFoldLoop, MachineBuildError> {
    let mismatch = || MachineBuildError::TopologyMismatch;
    let pointer_parameter = abi_parameters
        .get(&fact.abi.pointer_parameter.index)
        .filter(|parameter| {
            parameter.storage() == fact.abi.pointer_parameter.storage
                && parameter.value().is_some_and(|value| {
                    value.binding().value() == fact.abi.pointer_parameter.value
                })
        })
        .ok_or_else(mismatch)?;
    let remaining_parameter = abi_parameters
        .get(&fact.abi.remaining_parameter.index)
        .filter(|parameter| {
            parameter.storage() == fact.abi.remaining_parameter.storage
                && parameter.value().is_some_and(|value| {
                    value.binding().value() == fact.abi.remaining_parameter.value
                })
        })
        .ok_or_else(mismatch)?;
    let pointer = carrier(artifact, &fact.pointer.carrier)?;
    let remaining = carrier(artifact, &fact.remaining)?;
    let hash = carrier(artifact, &fact.hash.carrier)?;
    let load_producer = canonical(artifact, fact.byte_load.load_inst).ok_or(
        MachineBuildError::MissingInstructionDisposition(fact.byte_load.load_inst),
    )?;
    let byte_load = memory_statements
        .get(&load_producer)
        .filter(|statement| {
            statement.access() == fact.byte_load.access
                && statement.object() == fact.byte_load.memory_object
                && statement.space() == MachineAddressSpace::from(fact.byte_load.memory_space)
                && statement.width_bits() == 8
                && matches!(statement.kind(), CertifiedMemoryStatementKind::Read { result }
                    if result.binding().value() == fact.byte_load.raw_byte)
        })
        .ok_or_else(mismatch)?;
    let zero_control_producer = canonical(artifact, fact.zero_guard.branch_inst).ok_or(
        MachineBuildError::MissingInstructionDisposition(fact.zero_guard.branch_inst),
    )?;
    let zero_control = conditional_controls
        .get(&zero_control_producer)
        .filter(|control| {
            control.condition().binding().value() == fact.zero_guard.condition
                && control.true_target() == fact.topology.exit
                && control.false_target() == fact.topology.setup
        })
        .ok_or_else(mismatch)?;
    let latch_control = latch_control(artifact, topology, fact)?;
    let return_producer = canonical(artifact, fact.returned.return_inst).ok_or(
        MachineBuildError::MissingInstructionDisposition(fact.returned.return_inst),
    )?;
    let return_control = return_controls
        .get(&return_producer)
        .filter(|control| {
            matches!(control.values(), [returned]
                if returned.slot() == (CallBoundarySlot::Register {
                    index: 0,
                    storage: fact.abi.return_storage,
                }) && returned.value().binding().value() == fact.returned.value)
        })
        .ok_or_else(mismatch)?;

    let state_producers = BTreeSet::from([
        pointer.phi.producer().ok_or_else(mismatch)?,
        remaining.phi.producer().ok_or_else(mismatch)?,
        hash.phi.producer().ok_or_else(mismatch)?,
    ]);
    if state_producers.len() != 3 {
        return Err(mismatch());
    }
    let state_obligations = state_producers
        .iter()
        .filter_map(|producer| artifact.obligations().instructions().get(producer))
        .flat_map(|instruction| instruction.obligations.iter().copied())
        .collect::<BTreeSet<_>>();
    let visible_expressions = expressions
        .iter()
        .filter(|(producer, _)| !state_producers.contains(producer))
        .map(|(producer, expression)| (*producer, expression.clone()))
        .collect::<BTreeMap<_, _>>();
    let phase_order = [
        (CertifiedFnvFoldPhase::Entry, fact.topology.entry),
        (CertifiedFnvFoldPhase::Setup, fact.topology.setup),
        (
            CertifiedFnvFoldPhase::HeaderLatch,
            fact.topology.header_latch,
        ),
        (CertifiedFnvFoldPhase::Exit, fact.topology.exit),
    ]
    .into_iter()
    .map(|(phase, block)| {
        topology
            .block(block)
            .map(|source| CertifiedFnvFoldPhaseOrder {
                phase,
                block,
                producers: source.instructions().to_vec().into_boxed_slice(),
            })
            .ok_or_else(mismatch)
    })
    .collect::<Result<Vec<_>, _>>()?;
    let predicate_witness = match &fact.ascii.predicate_witness {
        CanonicalFnvFoldUnsignedLessWitness::Direct {
            compare_inst,
            condition_copies,
        } => CertifiedFnvFoldUnsignedLess::Direct {
            compare: canonical(artifact, *compare_inst).ok_or(
                MachineBuildError::MissingInstructionDisposition(*compare_inst),
            )?,
            condition_copies: canonical_insts(artifact, condition_copies)?,
        },
        CanonicalFnvFoldUnsignedLessWitness::NegatedReverseLessEqual {
            compare_inst,
            comparison_copies,
            not_inst,
            condition_copies,
        } => CertifiedFnvFoldUnsignedLess::NegatedReverseLessEqual {
            compare: canonical(artifact, *compare_inst).ok_or(
                MachineBuildError::MissingInstructionDisposition(*compare_inst),
            )?,
            comparison_copies: canonical_insts(artifact, comparison_copies)?,
            bool_not: canonical(artifact, *not_inst)
                .ok_or(MachineBuildError::MissingInstructionDisposition(*not_inst))?,
            condition_copies: canonical_insts(artifact, condition_copies)?,
        },
    };
    let load_address = MachineValueUse::memory_address_for_access(artifact, fact.byte_load.access)?;
    if load_address.binding().value() != fact.pointer.load_address {
        return Err(mismatch());
    }
    let witness = CertifiedFnvFoldLoop {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION,
        origin: origin.clone(),
        revision_identity: fact.abi.revision_identity.clone(),
        loop_id: fact.loop_id,
        entry: fact.topology.entry,
        setup: fact.topology.setup,
        header_latch: fact.topology.header_latch,
        exit: fact.topology.exit,
        pointer_parameter: pointer_parameter.clone(),
        remaining_parameter: remaining_parameter.clone(),
        return_storage: fact.abi.return_storage,
        pointer_logical: fact.abi.pointer_logical,
        remaining_logical: fact.abi.remaining_logical,
        return_logical: fact.abi.return_logical,
        pointer,
        remaining,
        hash,
        pointer_entry_copy: canonical(artifact, fact.pointer.entry_copy_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.pointer.entry_copy_inst),
        )?,
        load_address,
        load_address_copy: canonical(artifact, fact.pointer.load_address_copy_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.pointer.load_address_copy_inst),
        )?,
        offset_basis: fact.hash.offset_basis,
        initializer_producer: canonical(artifact, fact.hash.initializer_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.hash.initializer_inst),
        )?,
        initializer_witness: canonical_insts(artifact, &fact.hash.initializer_witness_insts)?,
        exit_phi: MachineValueUse::from_artifact(artifact, fact.hash.exit_phi)?,
        exit_phi_producer: canonical(artifact, fact.hash.exit_phi_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.hash.exit_phi_inst),
        )?,
        byte_load: byte_load.clone(),
        memory_version: CertifiedFnvFoldMemoryVersion {
            object: fact.byte_load.memory_version.object,
            version: fact.byte_load.memory_version.version,
        },
        raw_byte: MachineValueUse::from_artifact(artifact, fact.byte_load.raw_byte)?,
        byte64: MachineValueUse::from_artifact(artifact, fact.byte_load.byte64)?,
        byte64_zext: canonical(artifact, fact.byte_load.byte64_zext_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.byte_load.byte64_zext_inst),
        )?,
        byte32_for_range: MachineValueUse::from_artifact(
            artifact,
            fact.byte_load.byte32_for_range,
        )?,
        byte32_for_lower: MachineValueUse::from_artifact(
            artifact,
            fact.byte_load.byte32_for_lower,
        )?,
        byte32_original: MachineValueUse::from_artifact(artifact, fact.byte_load.byte32_original)?,
        range: MachineValueUse::from_artifact(artifact, fact.ascii.range)?,
        range_producer: canonical(artifact, fact.ascii.range_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.ascii.range_inst),
        )?,
        lowercase: MachineValueUse::from_artifact(artifact, fact.ascii.lowercase)?,
        lowercase_producer: canonical(artifact, fact.ascii.lowercase_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.ascii.lowercase_inst),
        )?,
        uppercase: MachineValueUse::from_artifact(artifact, fact.ascii.uppercase)?,
        ascii_predicate: predicate_witness,
        selected: MachineValueUse::from_artifact(artifact, fact.ascii.selected)?,
        select_producer: canonical(artifact, fact.ascii.select_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.ascii.select_inst),
        )?,
        true_identity_producers: canonical_insts(artifact, &fact.ascii.true_identity_insts)?,
        false_identity_producers: canonical_insts(artifact, &fact.ascii.false_identity_insts)?,
        lowercase_on_true: fact.ascii.lowercase_on_true,
        selected64: MachineValueUse::from_artifact(artifact, fact.recurrence.selected64)?,
        selected64_zext: canonical(artifact, fact.recurrence.selected64_zext_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.recurrence.selected64_zext_inst),
        )?,
        xor: MachineValueUse::from_artifact(artifact, fact.recurrence.xor)?,
        xor_producer: canonical(artifact, fact.recurrence.xor_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.recurrence.xor_inst),
        )?,
        prime: MachineValueUse::from_artifact(artifact, fact.recurrence.prime)?,
        prime_value: CERTIFIED_FNV_PRIME,
        prime_producer: canonical(artifact, fact.recurrence.prime_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.recurrence.prime_inst),
        )?,
        prime_witness: canonical_insts(artifact, &fact.recurrence.prime_witness_insts)?,
        product: MachineValueUse::from_artifact(artifact, fact.recurrence.product)?,
        multiply_producer: canonical(artifact, fact.recurrence.multiply_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.recurrence.multiply_inst),
        )?,
        zero_predicate: fact.zero_guard.predicate,
        zero_condition: MachineValueUse::from_artifact(artifact, fact.zero_guard.condition)?,
        zero_condition_producer: canonical(artifact, fact.zero_guard.condition_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.zero_guard.condition_inst),
        )?,
        zero_control: zero_control.clone(),
        latch_predicate: fact.latch.predicate,
        latch_condition: MachineValueUse::from_artifact(artifact, fact.latch.condition)?,
        latch_condition_producer: canonical(artifact, fact.latch.condition_inst).ok_or(
            MachineBuildError::MissingInstructionDisposition(fact.latch.condition_inst),
        )?,
        latch_control: latch_control.clone(),
        returned: MachineValueUse::from_artifact(artifact, fact.returned.value)?,
        return_control: return_control.clone(),
        phase_order: phase_order.into_boxed_slice(),
        visible_expressions,
        state_producers,
        state_obligations,
    };
    witness
        .validate(artifact.obligations())
        .map_err(|_| mismatch())?;
    Ok(witness)
}

#[cfg(test)]
fn certified_expressions(
    artifact: &SsaArtifact,
    machine: &MachineProjection,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedExpr>, MachineBuildError> {
    let mut expressions = BTreeMap::new();
    for entity in machine.entities() {
        let obligations = entity
            .source_obligations()
            .iter()
            .copied()
            .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
            .collect::<BTreeSet<_>>();
        if obligations.is_empty() {
            continue;
        }
        let expression =
            super::certified_expr_from_machine(artifact, machine, entity, obligations)?;
        if expressions.insert(entity.producer(), expression).is_some() {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    Ok(expressions)
}

fn fnv_fold_effect_is_exact(
    witness: &CertifiedFnvFoldLoop,
    obligation: SemanticObligationId,
    effect: &crate::CertifiedEffect,
) -> bool {
    if witness.source_obligations().contains(&obligation) {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoFnvFoldState {
                producer: obligation.instruction,
            })
            && effect.fnv_fold_state_evidence() == Some(witness);
    }
    if witness
        .byte_load()
        .source_obligations()
        .contains(&obligation)
    {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoStatement {
                producer: obligation.instruction,
            })
            && effect.statement_evidence() == Some(witness.byte_load());
    }
    if witness
        .zero_control()
        .source_obligations()
        .contains(&obligation)
    {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoControl {
                producer: obligation.instruction,
            })
            && effect.conditional_control_evidence() == Some(witness.zero_control());
    }
    if witness
        .latch_control()
        .source_obligations()
        .contains(&obligation)
    {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoControl {
                producer: obligation.instruction,
            })
            && effect.fnv_fold_latch_control_evidence() == Some(witness.latch_control());
    }
    if witness
        .return_control()
        .source_obligations()
        .contains(&obligation)
    {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoReturn {
                producer: obligation.instruction,
            })
            && effect.return_control_evidence() == Some(witness.return_control());
    }
    obligation.kind == SemanticObligationKind::LiveValueProducer
        && effect.disposition()
            == &(EffectDisposition::AbsorbedIntoExpression {
                producer: obligation.instruction,
            })
        && witness
            .expression_for_producer(obligation.instruction)
            .is_some_and(|expression| effect.expression_evidence() == Some(expression))
}

/// Authorize the exact whole-function typed FNV loop only after source-ledger closure.
pub fn certify_fnv_fold_loop_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    witness: &CertifiedFnvFoldLoop,
) -> Result<CertifiedRenderPermit, RenderAuthorizationError> {
    if origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || !origin.matches_retained_source(origin.source(), origin.topology())
        || witness.origin() != origin
    {
        return Err(RenderAuthorizationError::InvalidOrigin);
    }
    if witness.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || witness.contract_version() != CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION
    {
        return Err(RenderAuthorizationError::InvalidRegionSchema);
    }
    let source = origin.source();
    if witness.validate(source).is_err() {
        return Err(RenderAuthorizationError::InvalidRegionTopology);
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
    for obligation in source.obligations().keys() {
        let [effect] = ledger.effects(*obligation) else {
            return Err(RenderAuthorizationError::IncompleteLedger);
        };
        if !fnv_fold_effect_is_exact(witness, *obligation, effect) {
            return Err(RenderAuthorizationError::InvalidRegionDisposition(
                *obligation,
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
        if effect.disposition() != mapping.source_disposition() {
            return Err(RenderAuthorizationError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedRenderPermit {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::FnvFoldLoopFunction,
        region_schema_version: CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, SpaceId};
    use r2sleigh_lift::{Disassembler, build_arch_spec};
    use r2ssa::{
        SourceAbiParameterSpec, SourceCarrierProjection, SourceFunctionInterface, SourceType,
        SourceTypeGraph,
    };
    use sha2::{Digest, Sha256};

    const REVISION: &[u8] = b"real-arm64-fnv-fold-o2-v1";
    const REAL_FNV_SOURCE_SHA256: &str =
        "6524278ba4cd32a72dcf9cbcc385275999a50c3449d0e97035736891bcddff09";
    const REAL_FNV_O2_FUNCTION_SHA256: &str =
        "127862f7bb0f1efcdd2830dd5bec8eadd8ac9812a847f477909b95fec671b6ac";
    const REAL_FNV_O2_BINARY_SHA256: &str =
        "e15adf9d8916bdbc1a45a07741734279cc815b87a5b2762cfb24cd78d33503c1";
    const REAL_FNV_O2_BINARY_PATH: &str = "tests/r2r/bins/r2sleigh_manual_limits_O2";
    const REAL_FNV_O2_COMPILER_COMMAND: &str =
        "cc -O2 -g -o tests/r2r/bins/r2sleigh_manual_limits_O2 tests/gold/manual_limits.c";
    const REAL_FNV_O2_BASE: u64 = 0x1_0000_0594;
    const REAL_FNV_O2_SETUP: u64 = 0x1_0000_05ac;
    const REAL_FNV_O2_LOOP: u64 = 0x1_0000_05b4;
    const REAL_FNV_O2_EXIT: u64 = 0x1_0000_05d8;
    const REAL_FNV_O2_BLOCKS: &[&str] = &[
        "e80300aa607080d2a073aef200f6c1f2a08ce2f2810100b4",
        "693680d20920c0f2",
        "0a1540384b0501514c011b327f6900718a318a1a0a000aca407d099b210400f101ffff54",
        "c0035fd6",
    ];

    fn decode_hex(encoded: &str) -> Vec<u8> {
        encoded
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| {
                let high = (pair[0] as char).to_digit(16).expect("hex digit") as u8;
                let low = (pair[1] as char).to_digit(16).expect("hex digit") as u8;
                (high << 4) | low
            })
            .collect()
    }

    fn sha256_hex(bytes: &[u8]) -> String {
        format!("{:x}", Sha256::digest(bytes))
    }

    fn real_storage(arch: &ArchSpec, register: &str) -> CanonicalStorageId {
        let register = arch
            .get_register(register)
            .expect("pinned AARCH64 register");
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: register.offset,
            size: register.size,
        }
    }

    fn mutated_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn real_interface(arch: &ArchSpec) -> SourceFunctionInterface {
        let types = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
            ],
            [],
        )
        .expect("real FNV type graph");
        let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
        SourceFunctionInterface::new_exact_with_logical_types(
            REVISION.to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, real_storage(arch, "x0")),
                SourceAbiParameterSpec::new(1, real_storage(arch, "x1")),
            ],
            SourceFunctionReturn::Register {
                storage: real_storage(arch, "x0"),
            },
            [],
            [
                SourceLogicalValue::new(1, full64),
                SourceLogicalValue::new(2, full64),
            ],
            Some(SourceLogicalValue::new(2, full64)),
            Some(types),
        )
        .and_then(|interface| interface.with_return_address_storage(real_storage(arch, "x30")))
        .expect("real FNV interface")
    }

    fn real_fixture() -> (ArchSpec, Vec<R2ILBlock>) {
        let provenance = format!(
            "binary={REAL_FNV_O2_BINARY_PATH} binary_sha256={REAL_FNV_O2_BINARY_SHA256} command={REAL_FNV_O2_COMPILER_COMMAND}"
        );
        assert_eq!(
            sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
            REAL_FNV_SOURCE_SHA256,
            "source provenance changed: {provenance}"
        );
        assert_eq!(
            sha256_hex(include_bytes!(
                "../../../tests/r2r/bins/r2sleigh_manual_limits_O2"
            )),
            REAL_FNV_O2_BINARY_SHA256,
            "full-binary provenance changed: {provenance}"
        );
        let function_bytes = REAL_FNV_O2_BLOCKS
            .iter()
            .flat_map(|encoded| decode_hex(encoded))
            .collect::<Vec<_>>();
        assert_eq!(function_bytes.len(), 72, "{provenance}");
        assert_eq!(
            sha256_hex(&function_bytes),
            REAL_FNV_O2_FUNCTION_SHA256,
            "function-byte provenance changed: {provenance}"
        );

        let arch = build_arch_spec(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AARCH64 architecture");
        let disassembler = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AARCH64 disassembler");
        let mut address = REAL_FNV_O2_BASE;
        let blocks = REAL_FNV_O2_BLOCKS
            .iter()
            .map(|encoded| {
                let bytes = decode_hex(encoded);
                let block = disassembler
                    .lift_block(&bytes, address, bytes.len())
                    .expect("pinned real ARM64 O2 FNV block");
                assert_eq!(
                    block.size as usize,
                    bytes.len(),
                    "real block must be fully consumed"
                );
                address += bytes.len() as u64;
                block
            })
            .collect::<Vec<_>>();
        assert_eq!(blocks.len(), 4, "{provenance}");
        let memory_spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            !memory_spaces.is_empty(),
            "real FNV lift must access memory"
        );
        assert!(
            memory_spaces.iter().all(|space| *space == SpaceId::Ram),
            "real ARM64 FNV accesses must use Ram: {memory_spaces:?}"
        );
        (arch, blocks)
    }

    fn real_artifact() -> SsaArtifact {
        let (arch, blocks) = real_fixture();
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), real_interface(&arch))
            .expect("prepared real ARM64 O2 FNV artifact")
    }

    fn certified() -> (SsaArtifact, super::super::CertifiedMachineFunction) {
        let artifact = real_artifact();
        let certified = super::super::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("real ARM64 O2 FNV certification");
        (artifact, certified)
    }

    fn manifest(certified: &super::super::CertifiedMachineFunction) -> Vec<TypedRegionMapping> {
        certified
            .source()
            .obligations()
            .keys()
            .map(|obligation| {
                let [effect] = certified.ledger().effects(*obligation) else {
                    panic!("one exact disposition")
                };
                TypedRegionMapping::new(*obligation, effect.disposition().clone())
            })
            .collect()
    }

    fn assert_corrupt(artifact: &SsaArtifact, witness: CertifiedFnvFoldLoop) {
        assert!(witness.validate(artifact.obligations()).is_err());
        assert!(witness.validate_against_artifact(artifact).is_err());
    }

    #[test]
    fn real_arm64_o2_seals_exact_visible_evidence_and_grants_permit() {
        let (artifact, certified) = certified();
        let witness = certified.fnv_fold_loop().expect("real FNV witness");
        witness
            .validate_against_artifact(&artifact)
            .expect("artifact revalidation");
        assert_eq!(witness.contract_version(), 1);
        assert_eq!(witness.revision_identity(), REVISION);
        assert_eq!(witness.phase_order().len(), 4);
        assert_eq!(witness.entry(), REAL_FNV_O2_BASE);
        assert_eq!(witness.setup(), REAL_FNV_O2_SETUP);
        assert_eq!(witness.header_latch(), REAL_FNV_O2_LOOP);
        assert_eq!(witness.exit(), REAL_FNV_O2_EXIT);
        assert_eq!(witness.offset_basis(), CERTIFIED_FNV_OFFSET_BASIS);
        assert_eq!(witness.prime_value(), CERTIFIED_FNV_PRIME);
        assert_eq!(witness.byte_load().space(), MachineAddressSpace::Ram);
        assert_eq!(witness.byte_load().width_bits(), 8);
        assert_eq!(witness.byte_load().word_size_bytes(), 1);
        assert!(matches!(
            witness.ascii_predicate(),
            CertifiedFnvFoldUnsignedLess::Direct { .. }
                | CertifiedFnvFoldUnsignedLess::NegatedReverseLessEqual { .. }
        ));

        for obligation in witness.source_obligations() {
            let [effect] = certified.ledger().effects(*obligation) else {
                panic!("one FNV state effect")
            };
            assert_eq!(
                effect.disposition(),
                &EffectDisposition::AbsorbedIntoFnvFoldState {
                    producer: obligation.instruction,
                }
            );
            assert_eq!(effect.fnv_fold_state_evidence(), Some(witness));
        }
        assert_eq!(witness.byte_load().source_obligations().len(), 1);
        let read = *witness
            .byte_load()
            .source_obligations()
            .iter()
            .next()
            .expect("one byte-read obligation");
        let [effect] = certified.ledger().effects(read) else {
            panic!("one byte-read effect")
        };
        assert_eq!(effect.statement_evidence(), Some(witness.byte_load()));
        for obligation in witness.latch_control().source_obligations() {
            let [effect] = certified.ledger().effects(obligation) else {
                panic!("one latch-control effect")
            };
            assert_eq!(
                effect.fnv_fold_latch_control_evidence(),
                Some(witness.latch_control())
            );
            assert!(effect.conditional_control_evidence().is_none());
        }

        let mappings = manifest(&certified);
        let permit = certify_fnv_fold_loop_region(
            certified.origin(),
            certified.ledger(),
            mappings.clone(),
            witness,
        )
        .expect("real FNV permit");
        assert!(permit.authorizes_certified_c());
        assert!(permit.matches_region(
            certified.origin(),
            CertifiedTypedRegionKind::FnvFoldLoopFunction,
            CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION,
            &mappings,
        ));
    }

    #[test]
    fn rejects_phase_topology_revision_and_obligation_mutations() {
        let (artifact, certified) = certified();
        let witness = certified.fnv_fold_loop().expect("real FNV witness");

        let mut corrupt = witness.clone();
        corrupt.phase_order = corrupt.phase_order[..3].into();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.phase_order[2].producers.swap(0, 1);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.phase_order[0].producers[0] = corrupt.phase_order[0].producers[1];
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.entry = REAL_FNV_O2_SETUP;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.revision_identity = b"stale-fnv-revision".to_vec().into_boxed_slice();
        assert_corrupt(&artifact, corrupt);

        let obligation = *witness
            .source_obligations()
            .iter()
            .next()
            .expect("FNV state obligation");
        let mut corrupt = witness.clone();
        corrupt.state_obligations.remove(&obligation);
        assert_corrupt(&artifact, corrupt);

        let facts = artifact.structured().canonical_fnv_fold_loops.clone();
        assert!(
            single_fact(&BTreeMap::new())
                .expect("empty fact set")
                .is_none()
        );
        let fact = facts.values().next().expect("one real FNV fact").clone();
        let mut duplicate = facts;
        duplicate.insert(REAL_FNV_O2_LOOP + 1, fact);
        assert_eq!(
            single_fact(&duplicate),
            Err(MachineBuildError::TopologyMismatch)
        );
    }

    #[test]
    fn real_lift_certifies_exact_materialized_constant_witnesses() {
        let (artifact, certified) = certified();
        let witness = certified.fnv_fold_loop().expect("real FNV witness");
        witness
            .validate_against_artifact(&artifact)
            .expect("real materialized constant revalidation");
        assert_eq!(witness.offset_basis(), CERTIFIED_FNV_OFFSET_BASIS);
        assert_eq!(witness.prime_value(), CERTIFIED_FNV_PRIME);
        assert_eq!(witness.initializer_witness().len(), 7);
        assert_eq!(witness.prime_witness().len(), 3);
    }

    #[test]
    fn rejects_carrier_value_storage_memory_constant_and_polarity_mutations() {
        let (artifact, certified) = certified();
        let witness = certified.fnv_fold_loop().expect("real FNV witness");

        let mut corrupt = witness.clone();
        corrupt.pointer.phi = corrupt.remaining.phi.clone();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.pointer.storage = mutated_storage(32);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.return_storage = mutated_storage(8);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.raw_byte = corrupt.byte64.clone();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.returned = corrupt.hash.phi.clone();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.memory_version.version += 1;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.byte_load.space = MachineAddressSpace::Custom(7);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.byte_load.endianness = MachineMemoryEndianness::Big;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.byte_load.word_size_bytes = 2;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.byte_load.access.ordinal = 1;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.byte_load.object = ObjectId(corrupt.byte_load.object().0 + 1);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.offset_basis ^= 1;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.prime_value ^= 1;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.lowercase_on_true = false;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.latch_control.true_target = corrupt.exit;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.latch_control.false_target = corrupt.setup;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.latch_control.condition = corrupt.zero_condition.clone();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.latch_control.predicate_obligation = corrupt.zero_control.predicate_obligation();
        assert_corrupt(&artifact, corrupt);
    }

    #[test]
    fn rejects_ledger_and_forged_permit_mappings() {
        let (_artifact, certified) = certified();
        let witness = certified.fnv_fold_loop().expect("real FNV witness");
        let obligation = *witness
            .source_obligations()
            .iter()
            .next()
            .expect("FNV state obligation");
        let mappings = manifest(&certified);

        let mut missing_ledger = certified.ledger().clone();
        missing_ledger.effects.remove(&obligation);
        assert_eq!(
            certify_fnv_fold_loop_region(
                certified.origin(),
                &missing_ledger,
                mappings.clone(),
                witness,
            ),
            Err(RenderAuthorizationError::IncompleteLedger)
        );

        let mut duplicate_ledger = certified.ledger().clone();
        let effect = duplicate_ledger.effects(obligation)[0].clone();
        duplicate_ledger.record(effect);
        assert_eq!(
            certify_fnv_fold_loop_region(
                certified.origin(),
                &duplicate_ledger,
                mappings.clone(),
                witness,
            ),
            Err(RenderAuthorizationError::IncompleteLedger)
        );

        let mut missing = mappings.clone();
        missing.remove(0);
        assert!(matches!(
            certify_fnv_fold_loop_region(certified.origin(), certified.ledger(), missing, witness,),
            Err(RenderAuthorizationError::MissingMapping(_))
        ));

        let mut duplicate = mappings.clone();
        duplicate.push(mappings[0].clone());
        assert!(matches!(
            certify_fnv_fold_loop_region(
                certified.origin(),
                certified.ledger(),
                duplicate,
                witness,
            ),
            Err(RenderAuthorizationError::DuplicateMapping(_))
        ));

        let mut forged = mappings;
        forged[0].source_disposition = EffectDisposition::ProvenDead;
        assert!(matches!(
            certify_fnv_fold_loop_region(certified.origin(), certified.ledger(), forged, witness,),
            Err(RenderAuthorizationError::DispositionMismatch(_))
        ));
    }
}
