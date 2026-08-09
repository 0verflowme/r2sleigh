//! Sealed certification for one exact x86-64 O0 private-frame conditional return.
//!
//! The witness absorbs the mechanically private stack-frame state while retaining
//! the visible predicate, control transfers, and ABI return as their existing
//! proof-bearing certificates. It is whole-function authority only when joined
//! with the exact ledger and typed-region manifest.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CallBoundarySlot, CanonicalInstructionId, CanonicalInstructionSite, CanonicalStorageId,
    CanonicalStorageSpace, InstId, InstPayload, MachineBuildError, MachineProjection,
    MachineValueUse, MemoryDefFact, MemoryUseFact, ObjectId, PRIVATE_FRAME_FACT_SCHEMA_VERSION,
    PredicateId, PrivateFrameFact, RelativeMemoryAddress, SSAOp, SemanticInstructionState,
    SemanticObligationComponent, SemanticObligationId, SemanticObligationInventory,
    SemanticObligationKind, SourceCarrierKind, SourceFunctionReturn, SourceStackSlotRole,
    SourceTypeKind, SsaArtifact, StackAddressBase, StackAddressRoot, StructuredAccessId, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertificationError, CertifiedAbiParameter,
    CertifiedArtifactOrigin, CertifiedConditionalControl, CertifiedDirectControl, CertifiedExpr,
    CertifiedMemoryStatement, CertifiedMemoryStatementKind, CertifiedRenderPermit,
    CertifiedReturnControl, CertifiedSourceTerminator, CertifiedSourceTopology, CertifiedStackSlot,
    CertifiedTypedRegionKind, EffectDisposition, ObligationLedger, RenderAuthorizationError,
    TypedRegionMapping,
};

pub const CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION: u32 = 1;

/// Exact private result carrier for the sealed O0 frame region. A source local
/// declaration is retained when present; otherwise `source_declared` is false
/// and the carrier is authorized only by the function-specific object,
/// MemorySSA, nonescape, topology, and return checks in this certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameLocal {
    schema_version: u32,
    base: StackAddressBase,
    offset: i64,
    size_bytes: u32,
    object: Option<ObjectId>,
    source_declared: bool,
}

impl CertifiedPrivateFrameLocal {
    pub const fn base(&self) -> StackAddressBase {
        self.base
    }

    pub const fn offset(&self) -> i64 {
        self.offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub const fn object(&self) -> Option<ObjectId> {
        self.object
    }

    pub const fn source_declared(&self) -> bool {
        self.source_declared
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CertifiedPrivateFrameMemoryVersion {
    object: ObjectId,
    version: u32,
}

impl CertifiedPrivateFrameMemoryVersion {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn version(&self) -> u32 {
        self.version
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameMemoryLocation {
    object: ObjectId,
    offset: i64,
    size_bytes: u32,
}

impl CertifiedPrivateFrameMemoryLocation {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn offset(&self) -> i64 {
        self.offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameMemoryUse {
    location: CertifiedPrivateFrameMemoryLocation,
    version: CertifiedPrivateFrameMemoryVersion,
}

impl CertifiedPrivateFrameMemoryUse {
    pub const fn location(&self) -> CertifiedPrivateFrameMemoryLocation {
        self.location
    }

    pub const fn version(&self) -> CertifiedPrivateFrameMemoryVersion {
        self.version
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameMemoryDef {
    location: CertifiedPrivateFrameMemoryLocation,
    previous_version: CertifiedPrivateFrameMemoryVersion,
    next_version: CertifiedPrivateFrameMemoryVersion,
}

impl CertifiedPrivateFrameMemoryDef {
    pub const fn location(&self) -> CertifiedPrivateFrameMemoryLocation {
        self.location
    }

    pub const fn previous_version(&self) -> CertifiedPrivateFrameMemoryVersion {
        self.previous_version
    }

    pub const fn next_version(&self) -> CertifiedPrivateFrameMemoryVersion {
        self.next_version
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameAccessMemory {
    access: StructuredAccessId,
    definitions: Box<[CertifiedPrivateFrameMemoryDef]>,
    uses: Box<[CertifiedPrivateFrameMemoryUse]>,
}

impl CertifiedPrivateFrameAccessMemory {
    pub const fn access(&self) -> StructuredAccessId {
        self.access
    }

    pub const fn definitions(&self) -> &[CertifiedPrivateFrameMemoryDef] {
        &self.definitions
    }

    pub const fn uses(&self) -> &[CertifiedPrivateFrameMemoryUse] {
        &self.uses
    }
}

/// Exact provenance-incomplete envelope load admitted only as private-frame state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedPrivateFrameEnvelopePolicy {
    AbsorbedByTypedPrivateFrameRegion,
}

/// Exact provenance-incomplete envelope load admitted only as private-frame state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameRawLoad {
    source_inst: InstId,
    producer: CanonicalInstructionId,
    access: StructuredAccessId,
    object: ObjectId,
    address: MachineValueUse,
    result: MachineValueUse,
    space: r2ssa::MachineAddressSpace,
    endianness: r2ssa::MachineMemoryEndianness,
    word_size_bytes: u32,
    width_bits: u32,
    policy: CertifiedPrivateFrameEnvelopePolicy,
    memory: CertifiedPrivateFrameAccessMemory,
}

impl CertifiedPrivateFrameRawLoad {
    pub const fn source_inst(&self) -> InstId {
        self.source_inst
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn access(&self) -> StructuredAccessId {
        self.access
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn address(&self) -> &MachineValueUse {
        &self.address
    }

    pub const fn result(&self) -> &MachineValueUse {
        &self.result
    }

    pub const fn space(&self) -> r2ssa::MachineAddressSpace {
        self.space
    }

    pub const fn endianness(&self) -> r2ssa::MachineMemoryEndianness {
        self.endianness
    }

    pub const fn word_size_bytes(&self) -> u32 {
        self.word_size_bytes
    }

    pub const fn width_bits(&self) -> u32 {
        self.width_bits
    }

    pub const fn policy(&self) -> CertifiedPrivateFrameEnvelopePolicy {
        self.policy
    }

    pub const fn memory(&self) -> &CertifiedPrivateFrameAccessMemory {
        &self.memory
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameStackUpdate {
    source_inst: InstId,
    input: MachineValueUse,
    output: MachineValueUse,
    delta: i64,
}

impl CertifiedPrivateFrameStackUpdate {
    pub const fn source_inst(&self) -> InstId {
        self.source_inst
    }

    pub const fn input(&self) -> &MachineValueUse {
        &self.input
    }

    pub const fn output(&self) -> &MachineValueUse {
        &self.output
    }

    pub const fn delta(&self) -> i64 {
        self.delta
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameRegisterCopy {
    source_inst: InstId,
    input: MachineValueUse,
    output: MachineValueUse,
}

impl CertifiedPrivateFrameRegisterCopy {
    pub const fn source_inst(&self) -> InstId {
        self.source_inst
    }

    pub const fn input(&self) -> &MachineValueUse {
        &self.input
    }

    pub const fn output(&self) -> &MachineValueUse {
        &self.output
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFramePhysicalRange {
    start_from_entry_sp: i64,
    end_from_entry_sp: i64,
}

impl CertifiedPrivateFramePhysicalRange {
    pub const fn start_from_entry_sp(&self) -> i64 {
        self.start_from_entry_sp
    }

    pub const fn end_from_entry_sp(&self) -> i64 {
        self.end_from_entry_sp
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameHomeReload {
    statement: CertifiedMemoryStatement,
    value: MachineValueUse,
    memory_version: CertifiedPrivateFrameMemoryVersion,
    memory_uses: Box<[CertifiedPrivateFrameMemoryUse]>,
}

impl CertifiedPrivateFrameHomeReload {
    pub const fn statement(&self) -> &CertifiedMemoryStatement {
        &self.statement
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }

    pub const fn memory_version(&self) -> CertifiedPrivateFrameMemoryVersion {
        self.memory_version
    }

    pub const fn memory_uses(&self) -> &[CertifiedPrivateFrameMemoryUse] {
        &self.memory_uses
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameHome {
    slot: CertifiedStackSlot,
    parameter: CertifiedAbiParameter,
    parameter_value: MachineValueUse,
    init_store: CertifiedMemoryStatement,
    init_memory_version: CertifiedPrivateFrameMemoryVersion,
    init_memory_defs: Box<[CertifiedPrivateFrameMemoryDef]>,
    reloads: Box<[CertifiedPrivateFrameHomeReload]>,
}

impl CertifiedPrivateFrameHome {
    pub const fn slot(&self) -> &CertifiedStackSlot {
        &self.slot
    }

    pub const fn parameter(&self) -> &CertifiedAbiParameter {
        &self.parameter
    }

    pub const fn parameter_value(&self) -> &MachineValueUse {
        &self.parameter_value
    }

    pub const fn init_store(&self) -> &CertifiedMemoryStatement {
        &self.init_store
    }

    pub const fn init_memory_version(&self) -> CertifiedPrivateFrameMemoryVersion {
        self.init_memory_version
    }

    pub const fn init_memory_defs(&self) -> &[CertifiedPrivateFrameMemoryDef] {
        &self.init_memory_defs
    }

    pub const fn reloads(&self) -> &[CertifiedPrivateFrameHomeReload] {
        &self.reloads
    }
}

/// Sealed whole-function witness for the exact private-frame diamond.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameConditionalReturn {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    revision_identity: Box<[u8]>,
    entry_block: u64,
    exit_block: u64,
    pointer_width_bytes: u32,
    entry_sp_storage: CanonicalStorageId,
    entry_fp_storage: CanonicalStorageId,
    entry_pc_storage: CanonicalStorageId,
    entry_sp: MachineValueUse,
    entry_fp: MachineValueUse,
    push: CertifiedPrivateFrameStackUpdate,
    frame_pointer_set: CertifiedPrivateFrameRegisterCopy,
    saved_frame_pointer_capture: CertifiedPrivateFrameRegisterCopy,
    saved_frame_pointer_restore: CertifiedPrivateFrameRegisterCopy,
    saved_frame_pointer_store: CertifiedMemoryStatement,
    saved_frame_pointer_load: CertifiedPrivateFrameRawLoad,
    saved_frame_pointer_store_memory: CertifiedPrivateFrameAccessMemory,
    pop: CertifiedPrivateFrameStackUpdate,
    return_address_load: CertifiedPrivateFrameRawLoad,
    return_advance: CertifiedPrivateFrameStackUpdate,
    home: CertifiedPrivateFrameHome,
    local_slot: CertifiedPrivateFrameLocal,
    local_accesses: Box<[StructuredAccessId]>,
    local_access_memory: Box<[CertifiedPrivateFrameAccessMemory]>,
    predicate: PredicateId,
    predicate_value: MachineValueUse,
    predicate_expression: CertifiedExpr,
    branch_control: CertifiedConditionalControl,
    true_store: CertifiedMemoryStatement,
    true_control: CertifiedDirectControl,
    false_store: CertifiedMemoryStatement,
    false_control: CertifiedDirectControl,
    join_block: u64,
    join_load: CertifiedMemoryStatement,
    return_storage: CanonicalStorageId,
    return_value: MachineValueUse,
    return_relays: Box<[CanonicalInstructionId]>,
    return_transforms: Box<[CertifiedExpr]>,
    return_control: CertifiedReturnControl,
    saved_frame_pointer_range: CertifiedPrivateFramePhysicalRange,
    home_range: CertifiedPrivateFramePhysicalRange,
    local_range: CertifiedPrivateFramePhysicalRange,
    return_address_range: CertifiedPrivateFramePhysicalRange,
    prologue_order: Box<[CanonicalInstructionId]>,
    true_arm_order: Box<[CanonicalInstructionId]>,
    false_arm_order: Box<[CanonicalInstructionId]>,
    epilogue_order: Box<[CanonicalInstructionId]>,
    state_producers: BTreeSet<CanonicalInstructionId>,
    state_obligations: BTreeSet<SemanticObligationId>,
}

impl CertifiedPrivateFrameConditionalReturn {
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

    pub const fn entry_block(&self) -> u64 {
        self.entry_block
    }

    pub const fn exit_block(&self) -> u64 {
        self.exit_block
    }

    pub const fn pointer_width_bytes(&self) -> u32 {
        self.pointer_width_bytes
    }

    pub const fn entry_sp_storage(&self) -> CanonicalStorageId {
        self.entry_sp_storage
    }

    pub const fn entry_fp_storage(&self) -> CanonicalStorageId {
        self.entry_fp_storage
    }

    pub const fn entry_pc_storage(&self) -> CanonicalStorageId {
        self.entry_pc_storage
    }

    pub const fn entry_sp(&self) -> &MachineValueUse {
        &self.entry_sp
    }

    pub const fn entry_fp(&self) -> &MachineValueUse {
        &self.entry_fp
    }

    pub const fn push(&self) -> &CertifiedPrivateFrameStackUpdate {
        &self.push
    }

    pub const fn frame_pointer_set(&self) -> &CertifiedPrivateFrameRegisterCopy {
        &self.frame_pointer_set
    }

    pub const fn saved_frame_pointer_capture(&self) -> &CertifiedPrivateFrameRegisterCopy {
        &self.saved_frame_pointer_capture
    }

    pub const fn saved_frame_pointer_restore(&self) -> &CertifiedPrivateFrameRegisterCopy {
        &self.saved_frame_pointer_restore
    }

    pub const fn saved_frame_pointer_store(&self) -> &CertifiedMemoryStatement {
        &self.saved_frame_pointer_store
    }

    pub const fn saved_frame_pointer_load(&self) -> &CertifiedPrivateFrameRawLoad {
        &self.saved_frame_pointer_load
    }

    pub const fn saved_frame_pointer_store_memory(&self) -> &CertifiedPrivateFrameAccessMemory {
        &self.saved_frame_pointer_store_memory
    }

    pub const fn pop(&self) -> &CertifiedPrivateFrameStackUpdate {
        &self.pop
    }

    pub const fn return_address_load(&self) -> &CertifiedPrivateFrameRawLoad {
        &self.return_address_load
    }

    pub const fn return_advance(&self) -> &CertifiedPrivateFrameStackUpdate {
        &self.return_advance
    }

    pub const fn home(&self) -> &CertifiedPrivateFrameHome {
        &self.home
    }

    pub const fn local_slot(&self) -> &CertifiedPrivateFrameLocal {
        &self.local_slot
    }

    pub const fn local_accesses(&self) -> &[StructuredAccessId] {
        &self.local_accesses
    }

    pub const fn local_access_memory(&self) -> &[CertifiedPrivateFrameAccessMemory] {
        &self.local_access_memory
    }

    pub const fn predicate(&self) -> PredicateId {
        self.predicate
    }

    pub const fn predicate_value(&self) -> &MachineValueUse {
        &self.predicate_value
    }

    pub const fn predicate_expression(&self) -> &CertifiedExpr {
        &self.predicate_expression
    }

    pub const fn branch_control(&self) -> &CertifiedConditionalControl {
        &self.branch_control
    }

    pub const fn true_store(&self) -> &CertifiedMemoryStatement {
        &self.true_store
    }

    pub const fn true_control(&self) -> &CertifiedDirectControl {
        &self.true_control
    }

    pub const fn false_store(&self) -> &CertifiedMemoryStatement {
        &self.false_store
    }

    pub const fn false_control(&self) -> &CertifiedDirectControl {
        &self.false_control
    }

    pub const fn join_block(&self) -> u64 {
        self.join_block
    }

    pub const fn join_load(&self) -> &CertifiedMemoryStatement {
        &self.join_load
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn return_value(&self) -> &MachineValueUse {
        &self.return_value
    }

    pub const fn return_relays(&self) -> &[CanonicalInstructionId] {
        &self.return_relays
    }

    pub const fn return_transforms(&self) -> &[CertifiedExpr] {
        &self.return_transforms
    }

    pub const fn return_control(&self) -> &CertifiedReturnControl {
        &self.return_control
    }

    pub const fn saved_frame_pointer_range(&self) -> CertifiedPrivateFramePhysicalRange {
        self.saved_frame_pointer_range
    }

    pub const fn home_range(&self) -> CertifiedPrivateFramePhysicalRange {
        self.home_range
    }

    pub const fn local_range(&self) -> CertifiedPrivateFramePhysicalRange {
        self.local_range
    }

    pub const fn return_address_range(&self) -> CertifiedPrivateFramePhysicalRange {
        self.return_address_range
    }

    pub fn state_producers(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.state_producers
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
        if self.contract_version != CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION
            || self.origin.source() != source
            || !self
                .origin
                .matches_retained_source(source, self.origin.topology())
        {
            return Err(unmapped(self.branch_control.producer()));
        }
        let Some(interface) = self.origin.machine_context().source().function_interface() else {
            return Err(unmapped(self.branch_control.producer()));
        };
        if interface.revision_identity() != self.revision_identity.as_ref()
            || self.pointer_width_bytes != 8
            || self.entry_sp_storage.size != self.pointer_width_bytes
            || self.entry_fp_storage.size != self.pointer_width_bytes
            || self.entry_pc_storage.size != self.pointer_width_bytes
            || self.entry_sp_storage.space != CanonicalStorageSpace::Register
            || self.entry_fp_storage.space != CanonicalStorageSpace::Register
            || self.entry_pc_storage.space != CanonicalStorageSpace::Register
            || self.entry_sp_storage == self.entry_fp_storage
            || self.entry_sp_storage == self.entry_pc_storage
            || self.entry_fp_storage == self.entry_pc_storage
            || !matches!(
                interface.return_kind(),
                SourceFunctionReturn::Register { storage } if storage == self.return_storage
            )
            || !self.declared_slots_are_exact(interface)
            || !self.parameter_home_is_exact(interface)
        {
            return Err(unmapped(self.return_control.producer()));
        }
        self.predicate_expression.validate(source)?;
        for transform in &self.return_transforms {
            transform.validate(source)?;
        }
        self.branch_control.validate(source)?;
        self.true_control.validate(source)?;
        self.false_control.validate(source)?;
        self.return_control.validate(source)?;
        for statement in self.memory_statements() {
            statement.validate(source)?;
        }
        if !self.topology_is_exact()
            || !self.envelope_is_exact()
            || !self.return_transform_chain_is_exact(source)
            || !self.state_values_are_origin_bound(source)
            || !self.raw_load_is_exact(source, &self.saved_frame_pointer_load, false)
            || !self.raw_load_is_exact(source, &self.return_address_load, true)
            || !self.physical_ranges_are_exact_and_disjoint()
            || !self.access_and_version_evidence_is_exact()
            || !self.order_is_exact(source)
            || !self.obligation_surface_is_exact(source)
        {
            return Err(unmapped(self.branch_control.producer()));
        }
        Ok(())
    }

    fn return_transform_chain_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let loaded = match self.join_load.kind() {
            CertifiedMemoryStatementKind::Read { result } => result,
            CertifiedMemoryStatementKind::Write { .. } => return false,
        };
        if self.return_transforms.is_empty() {
            return self.return_relays.is_empty()
                && self.return_value.binding().value() == loaded.binding().value();
        }
        if self.return_transforms.len() > 2
            || self.return_value.producer()
                != self
                    .return_transforms
                    .last()
                    .map(|transform| transform.entity().producer())
        {
            return false;
        }
        if self.return_relays.len() > 1
            || self.return_relays.iter().any(|producer| {
                source
                    .instructions()
                    .get(producer)
                    .is_none_or(|instruction| {
                        instruction.state != SemanticInstructionState::ProvenDead
                            || !instruction.obligations.is_empty()
                    })
            })
        {
            return false;
        }
        let mut expected_input = loaded.producer();
        for transform in &self.return_transforms {
            let producer = transform.entity().producer();
            let obligation = SemanticObligationId {
                instruction: producer,
                kind: SemanticObligationKind::LiveValueProducer,
                component: SemanticObligationComponent::Whole,
            };
            if expected_input.is_none_or(|input| transform.inputs() != &BTreeSet::from([input]))
                || transform.entity().source_obligations() != &BTreeSet::from([obligation])
                || source
                    .instructions()
                    .get(&producer)
                    .is_none_or(|instruction| {
                        instruction.obligations != BTreeSet::from([obligation])
                    })
            {
                return false;
            }
            expected_input = Some(producer);
        }
        true
    }

    fn state_values_are_origin_bound(&self, source: &SemanticObligationInventory) -> bool {
        let produced_at = |value: &MachineValueUse, inst: InstId| {
            value.producer().is_some_and(|producer| {
                source
                    .instructions()
                    .get(&producer)
                    .is_some_and(|instruction| instruction.inst == inst)
            })
        };
        self.predicate == PredicateId(0)
            && self.entry_sp.producer().is_none()
            && self.entry_fp.producer().is_none()
            && produced_at(&self.push.output, self.push.source_inst)
            && produced_at(
                &self.frame_pointer_set.output,
                self.frame_pointer_set.source_inst,
            )
            && produced_at(
                &self.saved_frame_pointer_capture.output,
                self.saved_frame_pointer_capture.source_inst,
            )
            && produced_at(
                &self.saved_frame_pointer_restore.output,
                self.saved_frame_pointer_restore.source_inst,
            )
            && produced_at(&self.pop.output, self.pop.source_inst)
            && produced_at(&self.return_advance.output, self.return_advance.source_inst)
            && self.predicate_value.producer()
                == Some(self.predicate_expression.entity().producer())
            && self.predicate_value.binding() == self.branch_control.condition().binding()
    }

    fn raw_load_is_exact(
        &self,
        source: &SemanticObligationInventory,
        load: &CertifiedPrivateFrameRawLoad,
        requires_live_value: bool,
    ) -> bool {
        let mut expected = BTreeSet::from([
            SemanticObligationId {
                instruction: load.producer,
                kind: SemanticObligationKind::ObservableMemoryRead,
                component: SemanticObligationComponent::MemoryAccess(load.access.ordinal),
            },
            SemanticObligationId {
                instruction: load.producer,
                kind: SemanticObligationKind::VolatileOrUnknownEffect,
                component: SemanticObligationComponent::MemoryAccess(load.access.ordinal),
            },
        ]);
        let live = SemanticObligationId {
            instruction: load.producer,
            kind: SemanticObligationKind::LiveValueProducer,
            component: SemanticObligationComponent::Whole,
        };
        if requires_live_value {
            expected.insert(live);
        }
        let versions = load
            .memory
            .uses
            .iter()
            .map(|use_fact| use_fact.version)
            .collect::<BTreeSet<_>>();
        let alias_objects = load
            .memory
            .uses
            .iter()
            .map(|use_fact| use_fact.version.object)
            .collect::<BTreeSet<_>>();
        let Some(home_object) = self.home.slot.object() else {
            return false;
        };
        let Some(local_object) = self.local_slot.object() else {
            return false;
        };
        let Some(local_join_version) = self
            .local_access_memory
            .iter()
            .find(|memory| memory.access == self.join_load.access())
            .and_then(|memory| match memory.uses.as_ref() {
                [use_fact] => Some(use_fact.version),
                _ => None,
            })
        else {
            return false;
        };
        let [home_alias, local_alias] = load.memory.uses.as_ref() else {
            return false;
        };
        load.access.inst == load.source_inst
            && load.memory.access == load.access
            && load.result.producer() == Some(load.producer)
            && load.result.binding().width_bits() == load.width_bits
            && load.address.binding().width_bits() == self.pointer_width_bytes.saturating_mul(8)
            && load.width_bits == self.pointer_width_bytes.saturating_mul(8)
            && load.word_size_bytes > 0
            && load.endianness != r2ssa::MachineMemoryEndianness::Unknown
            && matches!(
                load.space,
                r2ssa::MachineAddressSpace::Ram | r2ssa::MachineAddressSpace::Custom(_)
            )
            && load.policy == CertifiedPrivateFrameEnvelopePolicy::AbsorbedByTypedPrivateFrameRegion
            && load.memory.definitions.is_empty()
            && load.memory.uses.len() == 2
            && versions.len() == 2
            && alias_objects == BTreeSet::from([home_object, local_object])
            && !alias_objects.contains(&load.object)
            && home_alias.version.object == home_object
            && home_alias.version == self.home.init_memory_version
            && local_alias.version.object == local_object
            && local_alias.version == local_join_version
            && load.memory.uses.iter().all(|use_fact| {
                use_fact.location.object == load.object
                    && use_fact.location.offset == 0
                    && use_fact.location.size_bytes == self.pointer_width_bytes
                    && use_fact.version.version > 0
            })
            && source
                .instructions()
                .get(&load.producer)
                .is_some_and(|instruction| {
                    instruction.inst == load.source_inst && instruction.obligations == expected
                })
            && source
                .obligations()
                .get(&SemanticObligationId {
                    instruction: load.producer,
                    kind: SemanticObligationKind::ObservableMemoryRead,
                    component: SemanticObligationComponent::MemoryAccess(load.access.ordinal),
                })
                .is_some_and(|obligation| {
                    obligation.source_inst == load.source_inst
                        && obligation.inputs == [load.address.binding().value()]
                })
    }

    fn declared_slots_are_exact(&self, interface: &r2ssa::SourceFunctionInterface) -> bool {
        let slots = interface.stack_slots();
        if slots.len()
            != if self.local_slot.source_declared() {
                2
            } else {
                1
            }
            || slots.iter().any(|slot| {
                slot.base() != StackAddressBase::FramePointer
                    || slot.base_storage() != self.entry_fp_storage
            })
        {
            return false;
        }
        let home_matches = slots.iter().filter(|slot| {
            slot.base() == self.home.slot.base()
                && slot.offset() == self.home.slot.offset()
                && slot.size_bytes() == self.home.slot.size_bytes()
                && matches!(
                    slot.role(),
                    SourceStackSlotRole::ParameterHome {
                        parameter_index,
                        home_storage,
                    } if parameter_index == self.home.parameter.index()
                        && home_storage == self.home.parameter.storage()
                )
        });
        if home_matches.count() != 1 {
            return false;
        }
        let local_matches = slots.iter().filter(|slot| {
            slot.base() == self.local_slot.base()
                && slot.offset() == self.local_slot.offset()
                && slot.size_bytes() == self.local_slot.size_bytes()
                && slot.role() == SourceStackSlotRole::Local
        });
        local_matches.count() == usize::from(self.local_slot.source_declared())
            && self.local_slot.schema_version == CERTIFICATION_SCHEMA_VERSION
            && self.local_slot.object.is_some()
    }

    fn parameter_home_is_exact(&self, interface: &r2ssa::SourceFunctionInterface) -> bool {
        let width_bits = self.home.slot.size_bytes().saturating_mul(8);
        if self.home.parameter_value.producer().is_some()
            || self.home.parameter_value.constant().is_some()
            || self.home.parameter_value.binding().width_bits() != width_bits
        {
            return false;
        }
        if let Some(value) = self.home.parameter.value() {
            return value.binding().value() == self.home.parameter_value.binding().value()
                && self.home.parameter.storage().size == self.home.slot.size_bytes();
        }
        let Some(logical) = interface
            .parameter_logical_values()
            .get(usize::try_from(self.home.parameter.index()).unwrap_or(usize::MAX))
        else {
            return false;
        };
        let Some(source_type) = interface
            .type_graph()
            .and_then(|graph| graph.types().get(usize::try_from(logical.type_id()).ok()?))
        else {
            return false;
        };
        self.home.parameter.storage().size > self.home.slot.size_bytes()
            && logical.carrier().kind() == SourceCarrierKind::LowBits
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == u64::from(width_bits)
            && source_type.kind() == SourceTypeKind::SignedInteger
            && source_type.size_bits() == u64::from(width_bits)
            && source_type.align_bits() == u64::from(width_bits)
    }

    fn envelope_is_exact(&self) -> bool {
        let pointer_bits = self.pointer_width_bytes.saturating_mul(8);
        let saved_store_value = match self.saved_frame_pointer_store.kind() {
            CertifiedMemoryStatementKind::Write { value } => value,
            CertifiedMemoryStatementKind::Read { .. } => return false,
        };
        let saved_load_result = self.saved_frame_pointer_load.result();
        let return_target = self.return_address_load.result();
        let true_value = match self.true_store.kind() {
            CertifiedMemoryStatementKind::Write { value } => value,
            CertifiedMemoryStatementKind::Read { .. } => return false,
        };
        let false_value = match self.false_store.kind() {
            CertifiedMemoryStatementKind::Write { value } => value,
            CertifiedMemoryStatementKind::Read { .. } => return false,
        };
        self.entry_sp.binding().value() == self.push.input.binding().value()
            && self.entry_fp.binding().value()
                == self.saved_frame_pointer_capture.input.binding().value()
            && self.saved_frame_pointer_capture.output.binding().value()
                == saved_store_value.binding().value()
            && self.push.output.binding().value()
                == self.saved_frame_pointer_store.address().binding().value()
            && self.push.output.binding().value()
                == self.saved_frame_pointer_load.address().binding().value()
            && self.push.output.binding().value() == self.frame_pointer_set.input.binding().value()
            && self.push.output.binding().value() == self.pop.input.binding().value()
            && saved_load_result.binding().value()
                == self.saved_frame_pointer_restore.input.binding().value()
            && self.pop.output.binding().value()
                == self.return_address_load.address().binding().value()
            && self.pop.output.binding().value() == self.return_advance.input.binding().value()
            && return_target.binding().value()
                == self.return_control.control_target().binding().value()
            && self.push.delta == -i64::from(self.pointer_width_bytes)
            && self.pop.delta == i64::from(self.pointer_width_bytes)
            && self.return_advance.delta == i64::from(self.pointer_width_bytes)
            && [
                &self.entry_sp,
                &self.entry_fp,
                &self.push.input,
                &self.push.output,
                &self.frame_pointer_set.input,
                &self.frame_pointer_set.output,
                &self.saved_frame_pointer_capture.input,
                &self.saved_frame_pointer_capture.output,
                &self.saved_frame_pointer_restore.input,
                &self.saved_frame_pointer_restore.output,
                &self.pop.input,
                &self.pop.output,
                &self.return_advance.input,
                &self.return_advance.output,
                return_target,
            ]
            .iter()
            .all(|value| value.binding().width_bits() == pointer_bits)
            && self.return_control.control_target().binding().width_bits() == pointer_bits
            && true_value.constant().is_some_and(|value| value.bits() == 1)
            && false_value
                .constant()
                .is_some_and(|value| value.bits() == 0)
    }

    #[cfg(test)]
    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let machine_context = super::CertifiedMachineContext::from_artifact(artifact)?;
        let topology = super::certified_source_topology(artifact)?;
        let origin = super::certified_artifact_origin(artifact, &machine_context, &topology)?;
        let abi_parameters = super::certified_abi_parameters(artifact)?;
        let stack_slots = super::certified_stack_slots(artifact)?;
        let memory_statements = super::certified_memory_statements(artifact)?;
        let direct_controls = super::certified_direct_controls(artifact, &topology)?;
        let conditional_controls = super::certified_conditional_controls(artifact, &topology)?;
        let return_controls = super::certified_return_controls(artifact, &topology)?;
        let projection = MachineProjection::from_artifact(artifact)?;
        let expressions = certified_expressions(artifact, &projection)?;
        let expected = certified_private_frame_conditional_return(
            artifact,
            &origin,
            &topology,
            &abi_parameters,
            &stack_slots,
            &memory_statements,
            &direct_controls,
            &conditional_controls,
            &return_controls,
            &expressions,
        )?
        .ok_or(MachineBuildError::TopologyMismatch)?;
        validate_private_frame_projection(artifact, &projection, Some(&expected))?;
        if expected == *self {
            Ok(())
        } else {
            Err(MachineBuildError::TopologyMismatch)
        }
    }

    fn memory_statements(&self) -> Vec<&CertifiedMemoryStatement> {
        std::iter::once(&self.saved_frame_pointer_store)
            .chain(std::iter::once(self.home.init_store()))
            .chain(self.home.reloads().iter().map(|reload| reload.statement()))
            .chain(std::iter::once(&self.true_store))
            .chain(std::iter::once(&self.false_store))
            .chain(std::iter::once(&self.join_load))
            .collect()
    }

    fn topology_is_exact(&self) -> bool {
        let topology = self.origin.topology();
        let [entry, false_arm, true_arm, join] = topology.blocks() else {
            return false;
        };
        topology.entry_addr() == self.entry_block
            && entry.addr() == self.entry_block
            && entry.predecessors().is_empty()
            && entry.successors()
                == [
                    self.branch_control.true_target(),
                    self.branch_control.false_target(),
                ]
            && matches!(
                entry.terminator(),
                CertifiedSourceTerminator::ConditionalBranch {
                    true_target,
                    false_target
                } if *true_target == self.branch_control.true_target()
                    && *false_target == self.branch_control.false_target()
            )
            && false_arm.addr() == self.branch_control.false_target()
            && true_arm.addr() == self.branch_control.true_target()
            && false_arm.successors() == [self.join_block]
            && true_arm.successors() == [self.join_block]
            && matches!(false_arm.terminator(), CertifiedSourceTerminator::Branch { target }
                if *target == self.join_block)
            && matches!(true_arm.terminator(), CertifiedSourceTerminator::Branch { target }
                if *target == self.join_block)
            && join.addr() == self.join_block
            && join.addr() == self.exit_block
            && join.predecessors()
                == [
                    self.branch_control.false_target(),
                    self.branch_control.true_target(),
                ]
            && join.successors().is_empty()
            && matches!(join.terminator(), CertifiedSourceTerminator::Return)
            && self.true_control.target() == self.join_block
            && self.false_control.target() == self.join_block
    }

    fn physical_ranges_are_exact_and_disjoint(&self) -> bool {
        let ranges = [
            self.saved_frame_pointer_range,
            self.home_range,
            self.local_range,
            self.return_address_range,
        ];
        let home_start = self
            .home
            .slot
            .offset()
            .checked_sub(i64::from(self.pointer_width_bytes));
        let local_start = self
            .local_slot
            .offset()
            .checked_sub(i64::from(self.pointer_width_bytes));
        self.saved_frame_pointer_range
            == (CertifiedPrivateFramePhysicalRange {
                start_from_entry_sp: -8,
                end_from_entry_sp: 0,
            })
            && self.return_address_range
                == (CertifiedPrivateFramePhysicalRange {
                    start_from_entry_sp: 0,
                    end_from_entry_sp: 8,
                })
            && home_start.is_some_and(|start| {
                self.home_range.start_from_entry_sp == start
                    && start.checked_add(i64::from(self.home.slot.size_bytes()))
                        == Some(self.home_range.end_from_entry_sp)
            })
            && local_start.is_some_and(|start| {
                self.local_range.start_from_entry_sp == start
                    && start.checked_add(i64::from(self.local_slot.size_bytes()))
                        == Some(self.local_range.end_from_entry_sp)
            })
            && ranges.iter().all(|range| {
                range.start_from_entry_sp < range.end_from_entry_sp
                    && range.end_from_entry_sp - range.start_from_entry_sp
                        <= i64::from(self.pointer_width_bytes)
            })
            && ranges.iter().enumerate().all(|(index, range)| {
                ranges[index + 1..].iter().all(|other| {
                    range.end_from_entry_sp <= other.start_from_entry_sp
                        || other.end_from_entry_sp <= range.start_from_entry_sp
                })
            })
    }

    fn access_and_version_evidence_is_exact(&self) -> bool {
        let [home_reload] = self.home.reloads() else {
            return false;
        };
        let Some(true_memory) = self
            .local_access_memory
            .iter()
            .find(|memory| memory.access == self.true_store.access())
        else {
            return false;
        };
        let Some(false_memory) = self
            .local_access_memory
            .iter()
            .find(|memory| memory.access == self.false_store.access())
        else {
            return false;
        };
        let Some(join_memory) = self
            .local_access_memory
            .iter()
            .find(|memory| memory.access == self.join_load.access())
        else {
            return false;
        };
        let ([true_definition], [false_definition], [join_use]) = (
            true_memory.definitions.as_ref(),
            false_memory.definitions.as_ref(),
            join_memory.uses.as_ref(),
        ) else {
            return false;
        };
        let accesses = self.memory_statements();
        let access_ids = accesses
            .iter()
            .map(|statement| statement.access())
            .collect::<BTreeSet<_>>();
        let retained_ids = std::iter::once(self.saved_frame_pointer_store_memory.access())
            .chain(std::iter::once(self.saved_frame_pointer_load.access()))
            .chain(std::iter::once(self.return_address_load.access()))
            .chain(std::iter::once(self.home.init_store().access()))
            .chain(std::iter::once(home_reload.statement().access()))
            .chain(
                self.local_access_memory
                    .iter()
                    .map(|access| access.access()),
            )
            .collect::<BTreeSet<_>>();
        let local_accesses = self.local_accesses.iter().copied().collect::<BTreeSet<_>>();
        let local_memory = self
            .local_access_memory
            .iter()
            .map(|access| access.access())
            .collect::<BTreeSet<_>>();
        let raw_ids = BTreeSet::from([
            self.saved_frame_pointer_load.access(),
            self.return_address_load.access(),
        ]);
        access_ids.len() == accesses.len()
            && access_ids.is_disjoint(&raw_ids)
            && access_ids.union(&raw_ids).copied().collect::<BTreeSet<_>>() == retained_ids
            && self.local_accesses.len() == 3
            && self.local_access_memory.len() == 3
            && self
                .local_access_memory
                .iter()
                .map(|access| access.access())
                .eq(self.local_accesses.iter().copied())
            && local_accesses == local_memory
            && local_accesses
                == BTreeSet::from([
                    self.true_store.access(),
                    self.false_store.access(),
                    self.join_load.access(),
                ])
            && self.home.init_memory_version == home_reload.memory_version
            && self.home.init_memory_defs.len() == 1
            && self.home.init_memory_defs.iter().all(|definition| {
                definition.location.object == self.home.slot.object().unwrap_or(ObjectId(u32::MAX))
                    && definition.location.offset == 0
                    && definition.location.size_bytes == self.home.slot.size_bytes()
                    && definition.next_version == self.home.init_memory_version
            })
            && home_reload.memory_uses.len() == 1
            && home_reload.memory_uses[0].version == self.home.init_memory_version
            && home_reload.memory_uses[0].location.object
                == self.home.slot.object().unwrap_or(ObjectId(u32::MAX))
            && self.saved_frame_pointer_store_memory.access
                == self.saved_frame_pointer_store.access()
            && self.saved_frame_pointer_store_memory.definitions.len() == 1
            && self.saved_frame_pointer_store_memory.uses.is_empty()
            && self.saved_frame_pointer_store_memory.definitions[0]
                .location
                .object
                == self.saved_frame_pointer_store.object()
            && self.saved_frame_pointer_store_memory.definitions[0]
                .location
                .size_bytes
                == self.pointer_width_bytes
            && true_memory.uses.is_empty()
            && false_memory.uses.is_empty()
            && join_memory.definitions.is_empty()
            && [true_definition, false_definition]
                .iter()
                .all(|definition| {
                    definition.location.object
                        == self.local_slot.object().unwrap_or(ObjectId(u32::MAX))
                        && definition.location.offset == 0
                        && definition.location.size_bytes == self.local_slot.size_bytes()
                })
            && true_definition.next_version != false_definition.next_version
            && join_use.location.object == self.local_slot.object().unwrap_or(ObjectId(u32::MAX))
            && join_use.location.offset == 0
            && join_use.location.size_bytes == self.local_slot.size_bytes()
            && join_use.version.version
                > true_definition
                    .next_version
                    .version
                    .max(false_definition.next_version.version)
            && self.all_access_memory().all(|access| {
                access.definitions.iter().all(valid_memory_def)
                    && access.uses.iter().all(valid_memory_use)
            })
    }

    fn all_access_memory(&self) -> impl Iterator<Item = &CertifiedPrivateFrameAccessMemory> {
        std::iter::once(&self.saved_frame_pointer_store_memory)
            .chain(self.local_access_memory.iter())
    }

    fn order_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let Some(entry) = self.origin.topology().block(self.entry_block) else {
            return false;
        };
        let Some(exit) = self.origin.topology().block(self.exit_block) else {
            return false;
        };
        let Some(capture) = self.saved_frame_pointer_capture.output.producer() else {
            return false;
        };
        let Some(push) = self.push.output.producer() else {
            return false;
        };
        let Some(frame_set) = self.frame_pointer_set.output.producer() else {
            return false;
        };
        let Some(pop) = self.pop.output.producer() else {
            return false;
        };
        let Some(restore) = self.saved_frame_pointer_restore.output.producer() else {
            return false;
        };
        let Some(advance) = self.return_advance.output.producer() else {
            return false;
        };
        let Some(home_address) = self.home.init_store.address().producer() else {
            return false;
        };
        let Some(true_address) = self.true_store.address().producer() else {
            return false;
        };
        let Some(false_address) = self.false_store.address().producer() else {
            return false;
        };
        let Some(local_address) = self.join_load.address().producer() else {
            return false;
        };
        let [home_reload] = self.home.reloads() else {
            return false;
        };
        let expected_prologue = [
            capture,
            push,
            self.saved_frame_pointer_store.producer(),
            frame_set,
            home_address,
            self.home.init_store.producer(),
            home_reload.statement.producer(),
            self.predicate_expression.entity().producer(),
            self.branch_control.producer(),
        ];
        let expected_true_arm = [
            true_address,
            self.true_store.producer(),
            self.true_control.producer(),
        ];
        let expected_false_arm = [
            false_address,
            self.false_store.producer(),
            self.false_control.producer(),
        ];
        let mut expected_epilogue_operations = vec![local_address, self.join_load.producer()];
        expected_epilogue_operations.extend(self.return_relays.iter().copied());
        expected_epilogue_operations.extend(
            self.return_transforms
                .iter()
                .map(|transform| transform.entity().producer()),
        );
        expected_epilogue_operations.extend([
            self.saved_frame_pointer_load.producer(),
            pop,
            restore,
            self.return_address_load.producer(),
            advance,
            self.return_control.producer(),
        ]);
        let Some(true_block) = self
            .origin
            .topology()
            .block(self.branch_control.true_target())
        else {
            return false;
        };
        let Some(false_block) = self
            .origin
            .topology()
            .block(self.branch_control.false_target())
        else {
            return false;
        };
        let phi_prefix_is_exact = self.epilogue_order.len()
            == 10usize
                .saturating_add(self.return_relays.len())
                .saturating_add(self.return_transforms.len())
            && self.epilogue_order[..2].iter().all(|producer| {
                matches!(producer.site, CanonicalInstructionSite::Phi(_))
                    && source
                        .instructions()
                        .get(producer)
                        .is_some_and(|instruction| {
                            instruction.obligations.is_empty()
                                && matches!(
                                    instruction.state,
                                    SemanticInstructionState::ProvenDead
                                        | SemanticInstructionState::StructuralControlOnly
                                )
                        })
            });
        self.prologue_order.as_ref() == expected_prologue
            && self.true_arm_order.as_ref() == expected_true_arm
            && self.false_arm_order.as_ref() == expected_false_arm
            && phi_prefix_is_exact
            && self.epilogue_order[2..] == expected_epilogue_operations
            && entry.instructions() == expected_prologue
            && true_block.instructions() == expected_true_arm
            && false_block.instructions() == expected_false_arm
            && exit.instructions() == self.epilogue_order.as_ref()
            && self.prologue_order.iter().all(|producer| {
                source
                    .instructions()
                    .get(producer)
                    .is_some_and(|instruction| instruction.inst != self.return_control.source_inst)
            })
            && self.epilogue_order.last() == Some(&self.return_control.producer())
    }

    fn obligation_surface_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let expected_state = self
            .state_producers
            .iter()
            .filter_map(|producer| source.instructions().get(producer))
            .flat_map(|instruction| instruction.obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut visible = self
            .predicate_expression
            .entity()
            .source_obligations()
            .clone();
        for transform in &self.return_transforms {
            visible.extend(transform.entity().source_obligations());
        }
        visible.extend(self.branch_control.source_obligations());
        visible.insert(self.true_control.source_obligation());
        visible.insert(self.false_control.source_obligation());
        visible.extend(self.return_control.source_obligations());
        let all = source
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        expected_state == self.state_obligations
            && self.state_obligations.is_disjoint(&visible)
            && self.state_obligations.iter().all(|obligation| {
                matches!(
                    obligation.kind,
                    SemanticObligationKind::LiveValueProducer
                        | SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite
                        | SemanticObligationKind::VolatileOrUnknownEffect
                )
            })
            && self
                .state_obligations
                .union(&visible)
                .copied()
                .collect::<BTreeSet<_>>()
                == all
            && source.instructions().values().all(|instruction| {
                instruction.state != SemanticInstructionState::UnsupportedUnknown
                    || instruction.id == self.saved_frame_pointer_load.producer
                    || instruction.id == self.return_address_load.producer
            })
    }
}

fn valid_memory_def(definition: &CertifiedPrivateFrameMemoryDef) -> bool {
    definition.location.size_bytes > 0
        && definition.previous_version.object == definition.location.object
        && definition.next_version.object == definition.location.object
        && definition.next_version.version > definition.previous_version.version
}

fn valid_memory_use(use_fact: &CertifiedPrivateFrameMemoryUse) -> bool {
    use_fact.location.size_bytes > 0
        && use_fact.version.object == use_fact.location.object
        && use_fact.version.version > 0
}

fn unmapped(producer: CanonicalInstructionId) -> CertificationError {
    CertificationError::ObligationNotMapped(SemanticObligationId {
        instruction: producer,
        kind: SemanticObligationKind::LiveValueProducer,
        component: SemanticObligationComponent::Whole,
    })
}

fn version(object: ObjectId, version: u32) -> CertifiedPrivateFrameMemoryVersion {
    CertifiedPrivateFrameMemoryVersion { object, version }
}

fn location(
    object: ObjectId,
    address: &RelativeMemoryAddress,
    size_bytes: u32,
) -> Option<CertifiedPrivateFrameMemoryLocation> {
    Some(CertifiedPrivateFrameMemoryLocation {
        object,
        offset: address.exact_offset()?,
        size_bytes,
    })
}

fn memory_use(use_fact: &MemoryUseFact) -> Option<CertifiedPrivateFrameMemoryUse> {
    Some(CertifiedPrivateFrameMemoryUse {
        location: location(
            use_fact.location.object,
            &use_fact.location.address,
            use_fact.location.size,
        )?,
        version: version(use_fact.version.object, use_fact.version.version),
    })
}

fn memory_def(definition: &MemoryDefFact) -> Option<CertifiedPrivateFrameMemoryDef> {
    Some(CertifiedPrivateFrameMemoryDef {
        location: location(
            definition.location.object,
            &definition.location.address,
            definition.location.size,
        )?,
        previous_version: version(
            definition.previous_version.object,
            definition.previous_version.version,
        ),
        next_version: version(
            definition.next_version.object,
            definition.next_version.version,
        ),
    })
}

fn access_memory(
    access: StructuredAccessId,
    definitions: &[MemoryDefFact],
    uses: &[MemoryUseFact],
) -> Option<CertifiedPrivateFrameAccessMemory> {
    Some(CertifiedPrivateFrameAccessMemory {
        access,
        definitions: definitions
            .iter()
            .map(memory_def)
            .collect::<Option<Vec<_>>>()?
            .into_boxed_slice(),
        uses: uses
            .iter()
            .map(memory_use)
            .collect::<Option<Vec<_>>>()?
            .into_boxed_slice(),
    })
}

fn stack_update(
    artifact: &SsaArtifact,
    fact: r2ssa::PrivateFrameStackUpdateFact,
) -> Result<CertifiedPrivateFrameStackUpdate, MachineBuildError> {
    Ok(CertifiedPrivateFrameStackUpdate {
        source_inst: fact.inst,
        input: MachineValueUse::from_artifact(artifact, fact.input)?,
        output: MachineValueUse::from_artifact(artifact, fact.output)?,
        delta: fact.delta,
    })
}

fn register_copy(
    artifact: &SsaArtifact,
    fact: r2ssa::PrivateFrameRegisterCopyFact,
) -> Result<CertifiedPrivateFrameRegisterCopy, MachineBuildError> {
    Ok(CertifiedPrivateFrameRegisterCopy {
        source_inst: fact.inst,
        input: MachineValueUse::from_artifact(artifact, fact.input)?,
        output: MachineValueUse::from_artifact(artifact, fact.output)?,
    })
}

fn raw_load(
    artifact: &SsaArtifact,
    access: StructuredAccessId,
    object: ObjectId,
    address: ValueId,
    result: ValueId,
    uses: &[MemoryUseFact],
) -> Result<CertifiedPrivateFrameRawLoad, MachineBuildError> {
    let fact = artifact
        .facts()
        .structured
        .memory_accesses
        .get(&access)
        .filter(|fact| {
            fact.id == access
                && fact.object == object
                && fact.address == address
                && fact.value == Some(result)
                && !fact.is_write
                && !fact.provenance_complete
                && fact.width > 0
        })
        .ok_or(MachineBuildError::EntityMismatch(access.inst))?;
    let inst = artifact
        .graph()
        .inst(access.inst)
        .filter(|inst| {
            inst.output == Some(result)
                && inst.inputs.as_slice() == [address]
                && matches!(inst.payload, InstPayload::Op(SSAOp::Load { .. }))
        })
        .ok_or(MachineBuildError::EntityMismatch(access.inst))?;
    let producer = canonical(artifact, inst.id)
        .ok_or(MachineBuildError::MissingInstructionDisposition(inst.id))?;
    let source_space = artifact
        .machine_context()
        .memory_space_at(fact.block_addr, fact.op_index)
        .ok_or(MachineBuildError::MachineContextMismatch)?;
    let model = artifact.machine_context().memory_model();
    let space_model = model
        .space(source_space)
        .filter(|space| {
            model.is_available()
                && model.is_coherent()
                && space.address_bits() > 0
                && space.word_size_bytes() > 0
                && space.endianness() != r2ssa::MachineMemoryEndianness::Unknown
        })
        .ok_or(MachineBuildError::MachineContextMismatch)?;
    let width_bits = fact
        .width
        .checked_mul(8)
        .filter(|width| *width > 0)
        .ok_or(MachineBuildError::EntityMismatch(inst.id))?;
    let memory =
        access_memory(access, &[], uses).ok_or(MachineBuildError::EntityMismatch(access.inst))?;
    Ok(CertifiedPrivateFrameRawLoad {
        source_inst: inst.id,
        producer,
        access,
        object,
        address: MachineValueUse::from_artifact(artifact, address)?,
        result: MachineValueUse::from_artifact(artifact, result)?,
        space: r2ssa::MachineAddressSpace::from(source_space),
        endianness: space_model.endianness(),
        word_size_bytes: space_model.word_size_bytes(),
        width_bits,
        policy: CertifiedPrivateFrameEnvelopePolicy::AbsorbedByTypedPrivateFrameRegion,
        memory,
    })
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

fn add_state_inst(
    artifact: &SsaArtifact,
    producers: &mut BTreeSet<CanonicalInstructionId>,
    inst: InstId,
) -> Option<CanonicalInstructionId> {
    let producer = canonical(artifact, inst)?;
    producers.insert(producer);
    Some(producer)
}

fn add_statement_state(
    producers: &mut BTreeSet<CanonicalInstructionId>,
    statement: &CertifiedMemoryStatement,
) {
    producers.insert(statement.producer());
    if let Some(producer) = statement.address().producer() {
        producers.insert(producer);
    }
}

fn exact_statement_value(
    statement: &CertifiedMemoryStatement,
    value: ValueId,
    write: bool,
) -> bool {
    match statement.kind() {
        CertifiedMemoryStatementKind::Read { result } => {
            !write && result.binding().value() == value
        }
        CertifiedMemoryStatementKind::Write { value: written } => {
            write && written.binding().value() == value
        }
    }
}

pub(crate) fn validate_private_frame_projection(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    witness: Option<&CertifiedPrivateFrameConditionalReturn>,
) -> Result<(), MachineBuildError> {
    let Some(witness) = witness else {
        return projection
            .failures()
            .first()
            .map(|failure| Err(failure.error().clone()))
            .unwrap_or(Ok(()));
    };
    let raw_loads = [
        &witness.saved_frame_pointer_load,
        &witness.return_address_load,
    ];
    if projection.failures().len() != raw_loads.len() {
        return Err(MachineBuildError::EntityMismatch(r2ssa::InstId(u32::MAX)));
    }
    for load in raw_loads {
        let failure = projection
            .failures()
            .iter()
            .find(|failure| {
                failure.output() == load.result.binding().value()
                    && failure.producer() == load.producer
            })
            .ok_or(MachineBuildError::EntityMismatch(load.source_inst))?;
        if !matches!(failure.error(), MachineBuildError::UnsupportedOperation { inst, op }
            if *inst == load.source_inst && matches!(op.as_ref(), SSAOp::Load { .. }))
            || projection.entity_for_output(failure.output()).is_some()
        {
            return Err(MachineBuildError::EntityMismatch(load.source_inst));
        }
    }

    let graph = artifact.graph();
    let mut seen = BTreeSet::new();
    let mut worklist = raw_loads
        .iter()
        .map(|load| load.result.binding().value())
        .collect::<Vec<_>>();
    while let Some(value) = worklist.pop() {
        if !seen.insert(value) {
            continue;
        }
        for use_site in graph.use_sites(value) {
            let instruction = graph
                .inst(use_site.inst)
                .ok_or(MachineBuildError::MissingInstruction(use_site.inst))?;
            if let Some(output) = instruction.output {
                let producer = canonical(artifact, instruction.id).ok_or(
                    MachineBuildError::MissingInstructionDisposition(instruction.id),
                )?;
                if !witness.state_producers.contains(&producer) {
                    return Err(MachineBuildError::ObligationMismatch(instruction.id));
                }
                worklist.push(output);
            } else if instruction.id != witness.return_control.source_inst {
                return Err(MachineBuildError::ObligationMismatch(instruction.id));
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn certified_private_frame_conditional_return(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
    stack_slots: &BTreeMap<StackAddressRoot, CertifiedStackSlot>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
) -> Result<Option<CertifiedPrivateFrameConditionalReturn>, MachineBuildError> {
    let Some(fact) = artifact.private_frame() else {
        return Ok(None);
    };
    if fact.schema_version != PRIVATE_FRAME_FACT_SCHEMA_VERSION
        || origin.source() != artifact.obligations()
        || origin.topology() != topology
        // This contract intentionally excludes the alternative generic funnel
        // carrier so ledger ownership cannot overlap nondeterministically.
        || fact.local.conditional_funnel.is_some()
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    build_private_frame(
        artifact,
        origin,
        topology,
        abi_parameters,
        stack_slots,
        memory_statements,
        direct_controls,
        conditional_controls,
        return_controls,
        expressions,
        fact,
    )
    .map(Some)
}

fn private_frame_parameter_is_exact(
    artifact: &SsaArtifact,
    parameter: &CertifiedAbiParameter,
    fact: &PrivateFrameFact,
) -> bool {
    if let Some(value) = parameter.value() {
        return value.binding().value() == fact.home.abi_parameter_value;
    }
    if fact.home.abi_parameter_value != fact.home.parameter_value
        || fact.home.width >= parameter.storage().size
    {
        return false;
    }
    let Some(interface) = artifact.machine_context().function_interface() else {
        return false;
    };
    let Some(logical) = interface
        .parameter_logical_values()
        .get(usize::try_from(parameter.index()).unwrap_or(usize::MAX))
    else {
        return false;
    };
    let Some(source_type) = interface
        .type_graph()
        .and_then(|graph| graph.types().get(usize::try_from(logical.type_id()).ok()?))
    else {
        return false;
    };
    let Some(value) = artifact.graph().value(fact.home.parameter_value) else {
        return false;
    };
    let low_storage = CanonicalStorageId {
        space: parameter.storage().space,
        offset: parameter.storage().offset,
        size: fact.home.width,
    };
    let width_bits = u64::from(fact.home.width).saturating_mul(8);
    artifact
        .graph()
        .def_inst(fact.home.parameter_value)
        .is_none()
        && value.var.version == 0
        && value.var.size == fact.home.width
        && value.canonical_storage == Some(low_storage)
        && logical.carrier().kind() == SourceCarrierKind::LowBits
        && logical.carrier().offset_bits() == 0
        && logical.carrier().size_bits() == width_bits
        && source_type.kind() == SourceTypeKind::SignedInteger
        && source_type.size_bits() == width_bits
        && source_type.align_bits() == width_bits
}

#[allow(clippy::too_many_arguments)]
fn build_private_frame(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
    stack_slots: &BTreeMap<StackAddressRoot, CertifiedStackSlot>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    fact: &PrivateFrameFact,
) -> Result<CertifiedPrivateFrameConditionalReturn, MachineBuildError> {
    let mismatch = || MachineBuildError::ObligationMismatch(fact.local.return_inst);
    let home_slot = stack_slots
        .get(&StackAddressRoot {
            base: fact.home.base,
            offset: fact.home.offset,
        })
        .filter(|slot| {
            slot.size_bytes() == fact.home.width && slot.object() == Some(fact.home.object)
        })
        .ok_or_else(mismatch)?;
    let declared_local_slot = stack_slots
        .get(&StackAddressRoot {
            base: fact.local.base,
            offset: fact.local.offset,
        })
        .filter(|slot| {
            slot.size_bytes() == fact.local.width && slot.object() == Some(fact.local.object)
        });
    let local_slot = CertifiedPrivateFrameLocal {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        base: fact.local.base,
        offset: fact.local.offset,
        size_bytes: fact.local.width,
        object: Some(fact.local.object),
        source_declared: declared_local_slot.is_some(),
    };
    let parameter = abi_parameters
        .get(&fact.home.parameter_index)
        .filter(|parameter| {
            parameter.storage() == fact.home.parameter_storage
                && private_frame_parameter_is_exact(artifact, parameter, fact)
        })
        .ok_or_else(mismatch)?;
    let saved_store =
        statement_for_access(artifact, memory_statements, fact.saved_frame_pointer.store)
            .ok_or_else(mismatch)?;
    let saved_load = raw_load(
        artifact,
        fact.saved_frame_pointer.load,
        fact.saved_frame_pointer.load_object,
        fact.push.output,
        fact.saved_frame_pointer.loaded_value,
        &fact.saved_frame_pointer.load_memory_uses,
    )?;
    let return_address_load = raw_load(
        artifact,
        fact.return_address.load,
        fact.return_address.object,
        fact.return_address.stack_value,
        fact.return_address.target,
        &fact.return_address.memory_uses,
    )?;
    let home_init = statement_for_access(artifact, memory_statements, fact.home.init_store)
        .ok_or_else(mismatch)?;
    let [home_reload_fact] = fact.home.reloads.as_slice() else {
        return Err(mismatch());
    };
    let home_reload = statement_for_access(artifact, memory_statements, home_reload_fact.access)
        .ok_or_else(mismatch)?;
    let true_store = statement_for_access(artifact, memory_statements, fact.local.true_store)
        .ok_or_else(mismatch)?;
    let false_store = statement_for_access(artifact, memory_statements, fact.local.false_store)
        .ok_or_else(mismatch)?;
    let join_load = statement_for_access(artifact, memory_statements, fact.local.join_load)
        .ok_or_else(mismatch)?;
    if saved_store.object() != fact.saved_frame_pointer.store_object
        || saved_load.object() != fact.saved_frame_pointer.load_object
        || return_address_load.object() != fact.return_address.object
        || home_init.object() != fact.home.object
        || home_reload.object() != fact.home.object
        || true_store.object() != fact.local.object
        || false_store.object() != fact.local.object
        || join_load.object() != fact.local.object
        || !exact_statement_value(saved_store, fact.saved_frame_pointer.stored_value, true)
        || saved_load.result().binding().value() != fact.saved_frame_pointer.loaded_value
        || return_address_load.result().binding().value() != fact.return_address.target
        || !exact_statement_value(home_init, fact.home.parameter_value, true)
        || !exact_statement_value(home_reload, home_reload_fact.value, false)
        || !exact_statement_value(true_store, fact.local.true_value, true)
        || !exact_statement_value(false_store, fact.local.false_value, true)
        || !exact_statement_value(join_load, fact.local.loaded_value, false)
    {
        return Err(mismatch());
    }
    let predicate_fact = artifact
        .facts()
        .predicates
        .predicates
        .get(&fact.local.predicate)
        .filter(|predicate| {
            predicate.block_addr == fact.local.branch_block
                && predicate.true_target == fact.local.true_target
                && predicate.false_target == fact.local.false_target
        })
        .ok_or_else(mismatch)?;
    let predicate_producer = artifact
        .graph()
        .def_inst(predicate_fact.condition)
        .and_then(|inst| canonical(artifact, inst))
        .ok_or_else(mismatch)?;
    let predicate_expression = expressions
        .get(&predicate_producer)
        .filter(|expression| {
            expression.entity().producer() == predicate_producer
                && expression
                    .entity()
                    .source_obligations()
                    .contains(&SemanticObligationId {
                        instruction: predicate_producer,
                        kind: SemanticObligationKind::LiveValueProducer,
                        component: SemanticObligationComponent::Whole,
                    })
        })
        .ok_or_else(mismatch)?;
    let branch_producer = topology
        .block(fact.local.branch_block)
        .and_then(|block| block.instructions().last())
        .copied()
        .ok_or_else(mismatch)?;
    let branch_control = conditional_controls
        .get(&branch_producer)
        .filter(|control| {
            control.condition().binding().value() == predicate_fact.condition
                && control.true_target() == fact.local.true_target
                && control.false_target() == fact.local.false_target
        })
        .ok_or_else(mismatch)?;
    let arm_control = |block_addr| {
        topology
            .block(block_addr)
            .and_then(|block| block.instructions().last())
            .and_then(|producer| direct_controls.get(producer))
            .filter(|control| control.target() == fact.local.join_block)
    };
    let true_control = arm_control(fact.local.true_target).ok_or_else(mismatch)?;
    let false_control = arm_control(fact.local.false_target).ok_or_else(mismatch)?;
    let return_producer = canonical(artifact, fact.local.return_inst).ok_or_else(mismatch)?;
    let return_control = return_controls
        .get(&return_producer)
        .filter(|control| {
            control.control_target().binding().value() == fact.return_address.target
                && matches!(control.values(), [returned]
                    if returned.slot() == (CallBoundarySlot::Register {
                        index: 0,
                        storage: fact.local.return_storage,
                    }) && returned.value().binding().value() == fact.local.return_value)
        })
        .ok_or_else(mismatch)?;
    let return_relays = fact
        .local
        .return_relay_insts
        .iter()
        .map(|inst| {
            let producer = canonical(artifact, *inst)?;
            artifact
                .obligations()
                .instructions()
                .get(&producer)
                .filter(|instruction| {
                    instruction.state == SemanticInstructionState::ProvenDead
                        && instruction.obligations.is_empty()
                })?;
            Some(producer)
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(mismatch)?;
    let return_transforms = fact
        .local
        .return_transform_insts
        .iter()
        .map(|inst| {
            let producer = canonical(artifact, *inst)?;
            let obligation = SemanticObligationId {
                instruction: producer,
                kind: SemanticObligationKind::LiveValueProducer,
                component: SemanticObligationComponent::Whole,
            };
            expressions
                .get(&producer)
                .filter(|expression| {
                    expression.entity().producer() == producer
                        && expression.entity().source_obligations() == &BTreeSet::from([obligation])
                })
                .cloned()
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(mismatch)?;

    let mut state_producers = BTreeSet::new();
    let capture_producer = add_state_inst(
        artifact,
        &mut state_producers,
        fact.saved_frame_pointer.capture.inst,
    )
    .ok_or_else(mismatch)?;
    let push_producer =
        add_state_inst(artifact, &mut state_producers, fact.push.inst).ok_or_else(mismatch)?;
    let frame_set_producer =
        add_state_inst(artifact, &mut state_producers, fact.frame_pointer_set.inst)
            .ok_or_else(mismatch)?;
    let pop_producer =
        add_state_inst(artifact, &mut state_producers, fact.pop.inst).ok_or_else(mismatch)?;
    let restore_producer = add_state_inst(
        artifact,
        &mut state_producers,
        fact.saved_frame_pointer.restore.inst,
    )
    .ok_or_else(mismatch)?;
    let advance_producer = add_state_inst(artifact, &mut state_producers, fact.return_advance.inst)
        .ok_or_else(mismatch)?;
    for statement in [
        saved_store,
        home_init,
        home_reload,
        true_store,
        false_store,
        join_load,
    ] {
        add_statement_state(&mut state_producers, statement);
    }
    for load in [&saved_load, &return_address_load] {
        state_producers.insert(load.producer());
        if let Some(producer) = load.address().producer() {
            state_producers.insert(producer);
        }
    }
    let state_obligations = state_producers
        .iter()
        .filter_map(|producer| artifact.obligations().instructions().get(producer))
        .flat_map(|instruction| instruction.obligations.iter().copied())
        .collect::<BTreeSet<_>>();
    let prologue_order = [
        capture_producer,
        push_producer,
        saved_store.producer(),
        frame_set_producer,
        home_init.address().producer().ok_or_else(mismatch)?,
        home_init.producer(),
        home_reload.producer(),
        predicate_producer,
        branch_producer,
    ];
    let true_arm_order = [
        true_store.address().producer().ok_or_else(mismatch)?,
        true_store.producer(),
        true_control.producer(),
    ];
    let false_arm_order = [
        false_store.address().producer().ok_or_else(mismatch)?,
        false_store.producer(),
        false_control.producer(),
    ];
    let mut epilogue_operations = vec![
        join_load.address().producer().ok_or_else(mismatch)?,
        join_load.producer(),
    ];
    epilogue_operations.extend(return_relays.iter().copied());
    epilogue_operations.extend(
        return_transforms
            .iter()
            .map(|transform| transform.entity().producer()),
    );
    epilogue_operations.extend([
        saved_load.producer(),
        pop_producer,
        restore_producer,
        return_address_load.producer(),
        advance_producer,
        return_producer,
    ]);
    let epilogue_order = topology
        .block(fact.exit_block)
        .map(|block| block.instructions().to_vec())
        .filter(|instructions| {
            instructions.len()
                == 10usize
                    .saturating_add(return_relays.len())
                    .saturating_add(return_transforms.len())
                && instructions[2..] == epilogue_operations
                && instructions[..2].iter().all(|producer| {
                    let Some(source) = artifact.obligations().instructions().get(producer) else {
                        return false;
                    };
                    let Some(inst) = artifact.graph().inst(source.inst) else {
                        return false;
                    };
                    matches!(inst.payload, InstPayload::Phi { .. })
                        && inst
                            .output
                            .is_some_and(|output| artifact.graph().use_sites(output).is_empty())
                })
        })
        .ok_or_else(mismatch)?;
    let local_access_memory = fact
        .local
        .access_memory
        .iter()
        .map(|access| access_memory(access.access, &access.memory_defs, &access.memory_uses))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(mismatch)?;
    let witness = CertifiedPrivateFrameConditionalReturn {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION,
        origin: origin.clone(),
        revision_identity: fact.revision_identity.clone(),
        entry_block: fact.entry_block,
        exit_block: fact.exit_block,
        pointer_width_bytes: fact.pointer_width_bytes,
        entry_sp_storage: fact.entry_sp_storage,
        entry_fp_storage: fact.entry_fp_storage,
        entry_pc_storage: fact.entry_pc_storage,
        entry_sp: MachineValueUse::from_artifact(artifact, fact.entry_sp)?,
        entry_fp: MachineValueUse::from_artifact(artifact, fact.entry_fp)?,
        push: stack_update(artifact, fact.push)?,
        frame_pointer_set: register_copy(artifact, fact.frame_pointer_set)?,
        saved_frame_pointer_capture: register_copy(artifact, fact.saved_frame_pointer.capture)?,
        saved_frame_pointer_restore: register_copy(artifact, fact.saved_frame_pointer.restore)?,
        saved_frame_pointer_store: saved_store.clone(),
        saved_frame_pointer_load: saved_load,
        saved_frame_pointer_store_memory: access_memory(
            fact.saved_frame_pointer.store,
            &fact.saved_frame_pointer.store_memory_defs,
            &[],
        )
        .ok_or_else(mismatch)?,
        pop: stack_update(artifact, fact.pop)?,
        return_address_load,
        return_advance: stack_update(artifact, fact.return_advance)?,
        home: CertifiedPrivateFrameHome {
            slot: home_slot.clone(),
            parameter: parameter.clone(),
            parameter_value: MachineValueUse::from_artifact(artifact, fact.home.parameter_value)?,
            init_store: home_init.clone(),
            init_memory_version: version(
                fact.home.init_memory_version.object,
                fact.home.init_memory_version.version,
            ),
            init_memory_defs: fact
                .home
                .init_memory_defs
                .iter()
                .map(memory_def)
                .collect::<Option<Vec<_>>>()
                .ok_or_else(mismatch)?
                .into_boxed_slice(),
            reloads: vec![CertifiedPrivateFrameHomeReload {
                statement: home_reload.clone(),
                value: MachineValueUse::from_artifact(artifact, home_reload_fact.value)?,
                memory_version: version(
                    home_reload_fact.memory_version.object,
                    home_reload_fact.memory_version.version,
                ),
                memory_uses: home_reload_fact
                    .memory_uses
                    .iter()
                    .map(memory_use)
                    .collect::<Option<Vec<_>>>()
                    .ok_or_else(mismatch)?
                    .into_boxed_slice(),
            }]
            .into_boxed_slice(),
        },
        local_slot,
        local_accesses: fact.local.accesses.clone().into_boxed_slice(),
        local_access_memory: local_access_memory.into_boxed_slice(),
        predicate: fact.local.predicate,
        predicate_value: MachineValueUse::from_artifact(artifact, predicate_fact.condition)?,
        predicate_expression: predicate_expression.clone(),
        branch_control: branch_control.clone(),
        true_store: true_store.clone(),
        true_control: true_control.clone(),
        false_store: false_store.clone(),
        false_control: false_control.clone(),
        join_block: fact.local.join_block,
        join_load: join_load.clone(),
        return_storage: fact.local.return_storage,
        return_value: MachineValueUse::from_artifact(artifact, fact.local.return_value)?,
        return_relays: return_relays.into_boxed_slice(),
        return_transforms: return_transforms.into_boxed_slice(),
        return_control: return_control.clone(),
        saved_frame_pointer_range: CertifiedPrivateFramePhysicalRange {
            start_from_entry_sp: fact.saved_frame_pointer_range.start_from_entry_sp,
            end_from_entry_sp: fact.saved_frame_pointer_range.end_from_entry_sp,
        },
        home_range: CertifiedPrivateFramePhysicalRange {
            start_from_entry_sp: fact.home_range.start_from_entry_sp,
            end_from_entry_sp: fact.home_range.end_from_entry_sp,
        },
        local_range: CertifiedPrivateFramePhysicalRange {
            start_from_entry_sp: fact.local_range.start_from_entry_sp,
            end_from_entry_sp: fact.local_range.end_from_entry_sp,
        },
        return_address_range: CertifiedPrivateFramePhysicalRange {
            start_from_entry_sp: fact.return_address_range.start_from_entry_sp,
            end_from_entry_sp: fact.return_address_range.end_from_entry_sp,
        },
        prologue_order: prologue_order.into(),
        true_arm_order: true_arm_order.into(),
        false_arm_order: false_arm_order.into(),
        epilogue_order: epilogue_order.into_boxed_slice(),
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

/// Authorize the exact whole-function private-frame conditional return.
pub fn certify_private_frame_conditional_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    witness: &CertifiedPrivateFrameConditionalReturn,
) -> Result<CertifiedRenderPermit, RenderAuthorizationError> {
    if origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || !origin.matches_retained_source(origin.source(), origin.topology())
        || witness.origin() != origin
    {
        return Err(RenderAuthorizationError::InvalidOrigin);
    }
    if witness.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || witness.contract_version() != CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION
    {
        return Err(RenderAuthorizationError::InvalidRegionSchema);
    }
    let source = origin.source();
    if witness.validate(source).is_err() {
        return Err(RenderAuthorizationError::InvalidRegionTopology);
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
    if let Some(instruction) = source.instructions().values().find(|instruction| {
        instruction.state == SemanticInstructionState::UnsupportedUnknown
            && instruction.id != witness.saved_frame_pointer_load.producer
            && instruction.id != witness.return_address_load.producer
    }) {
        return Err(RenderAuthorizationError::UnsupportedSourceSemantics(
            instruction.id,
        ));
    }
    for obligation in source.obligations().keys() {
        let [effect] = ledger.effects(*obligation) else {
            return Err(RenderAuthorizationError::IncompleteLedger);
        };
        if !private_frame_effect_is_exact(witness, *obligation, effect) {
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
        region_kind: CertifiedTypedRegionKind::PrivateFrameConditionalReturnFunction,
        region_schema_version: CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

fn private_frame_effect_is_exact(
    witness: &CertifiedPrivateFrameConditionalReturn,
    obligation: SemanticObligationId,
    effect: &super::CertifiedEffect,
) -> bool {
    if witness.source_obligations().contains(&obligation) {
        return effect.disposition()
            == &(EffectDisposition::AbsorbedIntoPrivateFrameState {
                producer: obligation.instruction,
            })
            && effect.private_frame_state_evidence() == Some(witness);
    }
    match obligation.kind {
        SemanticObligationKind::LiveValueProducer => {
            let expression = std::iter::once(witness.predicate_expression())
                .chain(witness.return_transforms())
                .find(|expression| expression.entity().producer() == obligation.instruction);
            effect.disposition()
                == &(EffectDisposition::AbsorbedIntoExpression {
                    producer: obligation.instruction,
                })
                && effect.expression_evidence() == expression
        }
        SemanticObligationKind::ControlPredicate | SemanticObligationKind::ControlTransfer => {
            let conditional =
                effect.conditional_control_evidence() == Some(witness.branch_control());
            let direct = effect.direct_control_evidence() == Some(witness.true_control())
                || effect.direct_control_evidence() == Some(witness.false_control());
            effect.disposition()
                == &(EffectDisposition::AbsorbedIntoControl {
                    producer: obligation.instruction,
                })
                && (conditional || direct)
        }
        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
            effect.disposition()
                == &(EffectDisposition::AbsorbedIntoReturn {
                    producer: obligation.instruction,
                })
                && effect.return_control_evidence() == Some(witness.return_control())
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

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SourceStackSlotSpec, StackAddressBase,
    };

    const REVISION: &[u8] = b"check-secret-private-frame-v1";

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-private-frame-cert-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("eax", 0, 4));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("edi", 8, 4));
        arch.add_register(RegisterDef::new("rsp", 16, 8));
        arch.add_register(RegisterDef::new("rbp", 24, 8));
        arch.add_register(RegisterDef::new("rip", 32, 8));
        arch
    }

    fn interface() -> SourceFunctionInterface {
        interface_with_local(true)
    }

    fn interface_with_local(declare_local: bool) -> SourceFunctionInterface {
        let mut slots = vec![SourceStackSlotSpec::new_parameter_home(
            StackAddressBase::FramePointer,
            storage(24, 8),
            -8,
            4,
            0,
            storage(8, 4),
        )];
        if declare_local {
            slots.push(SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(24, 8),
                -4,
                4,
            ));
        }
        SourceFunctionInterface::new_exact(
            REVISION.to_vec(),
            "sysv",
            [SourceAbiParameterSpec::new(0, storage(8, 4))],
            SourceFunctionReturn::Register {
                storage: storage(0, 4),
            },
            slots,
        )
        .expect("exact private-frame interface")
    }

    fn frame_address(unique: u64, offset: i64) -> (R2ILOp, Varnode) {
        let address = Varnode::unique(unique, 8);
        (
            R2ILOp::IntAdd {
                dst: address.clone(),
                a: Varnode::register(24, 8),
                b: Varnode::constant(offset as u64, 8),
            },
            address,
        )
    }

    fn artifact() -> SsaArtifact {
        artifact_with_interface(interface())
    }

    fn artifact_with_interface(interface: SourceFunctionInterface) -> SsaArtifact {
        let mut entry = R2ILBlock::new(0x1000, 0x10);
        let saved_fp = Varnode::unique(0x10, 8);
        entry.push(R2ILOp::Copy {
            dst: saved_fp.clone(),
            src: Varnode::register(24, 8),
        });
        entry.push(R2ILOp::IntSub {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
            val: saved_fp,
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: Varnode::register(16, 8),
        });
        let (home_address_op, home_address) = frame_address(0x20, -8);
        entry.push(home_address_op);
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: home_address.clone(),
            val: Varnode::register(8, 4),
        });
        let home_value = Varnode::unique(0x28, 4);
        entry.push(R2ILOp::Load {
            dst: home_value.clone(),
            space: SpaceId::Ram,
            addr: home_address,
        });
        let condition = Varnode::unique(0x30, 1);
        entry.push(R2ILOp::IntEqual {
            dst: condition.clone(),
            a: home_value,
            b: Varnode::constant(0x5ec2e7, 4),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x1020, 8),
            cond: condition,
        });

        let mut false_arm = R2ILBlock::new(0x1010, 0x10);
        let (false_address_op, false_address) = frame_address(0x40, -4);
        false_arm.push(false_address_op);
        false_arm.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: false_address,
            val: Varnode::constant(0, 4),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });

        let mut true_arm = R2ILBlock::new(0x1020, 0x10);
        let (true_address_op, true_address) = frame_address(0x50, -4);
        true_arm.push(true_address_op);
        true_arm.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: true_address,
            val: Varnode::constant(1, 4),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });

        let mut join = R2ILBlock::new(0x1030, 0x10);
        let (local_address_op, local_address) = frame_address(0x60, -4);
        join.push(local_address_op);
        join.push(R2ILOp::Load {
            dst: Varnode::register(0, 4),
            space: SpaceId::Ram,
            addr: local_address,
        });
        let restored_fp = Varnode::unique(0x70, 8);
        join.push(R2ILOp::Load {
            dst: restored_fp.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        join.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: restored_fp,
        });
        join.push(R2ILOp::Load {
            dst: Varnode::register(32, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        join.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });

        SsaArtifact::for_decompile_with_interface(
            &[entry, false_arm, true_arm, join],
            Some(&arch()),
            interface,
        )
        .expect("private-frame artifact")
    }

    fn certified() -> (SsaArtifact, super::super::CertifiedMachineFunction) {
        let artifact = artifact();
        let certified = super::super::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("private-frame certification");
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

    #[test]
    fn seals_private_frame_state_and_keeps_visible_evidence_joined() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");
        witness
            .validate_against_artifact(&artifact)
            .expect("artifact revalidation");
        assert_eq!(witness.contract_version(), 1);
        assert_eq!(witness.revision_identity(), REVISION);
        assert_eq!(witness.local_accesses().len(), 3);
        assert_eq!(witness.local_access_memory().len(), 3);
        assert!(witness.source_obligations().iter().all(|obligation| {
            let [effect] = certified.ledger().effects(*obligation) else {
                return false;
            };
            effect.disposition()
                == &(EffectDisposition::AbsorbedIntoPrivateFrameState {
                    producer: obligation.instruction,
                })
                && effect.private_frame_state_evidence() == Some(witness)
                && effect.expression_evidence().is_none()
                && effect.statement_evidence().is_none()
        }));

        for obligation in witness.branch_control().source_obligations() {
            let [effect] = certified.ledger().effects(obligation) else {
                panic!("one branch disposition")
            };
            assert_eq!(
                effect.disposition(),
                &EffectDisposition::AbsorbedIntoControl {
                    producer: witness.branch_control().producer(),
                }
            );
            assert_eq!(
                effect.conditional_control_evidence(),
                Some(witness.branch_control())
            );
        }
        for obligation in witness.return_control().source_obligations() {
            let [effect] = certified.ledger().effects(obligation) else {
                panic!("one return disposition")
            };
            assert_eq!(
                effect.return_control_evidence(),
                Some(witness.return_control())
            );
        }

        let mappings = manifest(&certified);
        let permit = certify_private_frame_conditional_return_region(
            certified.origin(),
            certified.ledger(),
            mappings.clone(),
            witness,
        )
        .expect("private-frame permit");
        assert!(permit.authorizes_certified_c());
        assert!(permit.matches_region(
            certified.origin(),
            CertifiedTypedRegionKind::PrivateFrameConditionalReturnFunction,
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION,
            &mappings,
        ));
    }

    #[test]
    fn seals_structurally_private_result_when_source_declares_only_the_home() {
        let artifact = artifact_with_interface(interface_with_local(false));
        let certified = super::super::CertifiedMachineFunction::from_artifact(&artifact)
            .expect("private-frame certification with hidden result");
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness with hidden result");
        assert!(!witness.local_slot().source_declared());
        assert_eq!(witness.local_slot().offset(), -4);
        assert_eq!(witness.local_slot().size_bytes(), 4);
        witness
            .validate_against_artifact(&artifact)
            .expect("hidden-result artifact revalidation");
    }

    fn assert_corrupt(artifact: &SsaArtifact, witness: CertifiedPrivateFrameConditionalReturn) {
        assert!(witness.validate(artifact.obligations()).is_err());
        assert!(witness.validate_against_artifact(artifact).is_err());
    }

    #[test]
    fn rejects_revision_storage_order_range_access_and_version_corruption() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");

        let mut corrupt = witness.clone();
        corrupt.revision_identity = b"stale-private-frame".to_vec().into_boxed_slice();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.origin.schema_version += 1;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.return_storage = storage(8, 4);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.prologue_order.swap(0, 1);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.local_range = corrupt.home_range;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.local_accesses[0] = StructuredAccessId {
            inst: corrupt.local_accesses[0].inst,
            ordinal: 99,
        };
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.local_access_memory[0].definitions[0]
            .next_version
            .version += 1;
        assert_corrupt(&artifact, corrupt);
    }

    #[test]
    fn rejects_missing_duplicate_and_reordered_retained_accesses() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");

        let mut corrupt = witness.clone();
        corrupt.local_accesses = corrupt.local_accesses[1..].into();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        let duplicate = [
            corrupt.local_accesses[0],
            corrupt.local_accesses[0],
            corrupt.local_accesses[2],
        ];
        corrupt.local_accesses = duplicate.into();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.local_access_memory.swap(0, 1);
        assert_corrupt(&artifact, corrupt);
    }

    #[test]
    fn rejects_raw_projection_and_transitive_state_corruption() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");
        let projection = MachineProjection::from_artifact(&artifact)
            .expect("private-frame projection retains exact failures");

        validate_private_frame_projection(&artifact, &projection, Some(witness))
            .expect("exact raw-load projection admission");

        let mut corrupt = witness.clone();
        corrupt.saved_frame_pointer_load.result = corrupt.return_address_load.result.clone();
        assert!(validate_private_frame_projection(&artifact, &projection, Some(&corrupt)).is_err());
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.saved_frame_pointer_load.producer = corrupt.return_address_load.producer;
        assert!(validate_private_frame_projection(&artifact, &projection, Some(&corrupt)).is_err());
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        let restore = corrupt
            .saved_frame_pointer_restore
            .output
            .producer()
            .expect("restore producer");
        assert!(corrupt.state_producers.remove(&restore));
        assert!(validate_private_frame_projection(&artifact, &projection, Some(&corrupt)).is_err());
        assert!(corrupt.validate_against_artifact(&artifact).is_err());
    }

    #[test]
    fn rejects_raw_alias_role_and_access_cardinality_corruption() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");

        let mut corrupt = witness.clone();
        corrupt.saved_frame_pointer_load.memory.uses.swap(0, 1);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.saved_frame_pointer_store_memory.definitions = Box::new([]);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.saved_frame_pointer_load.memory.uses[0]
            .version
            .version += 1;
        assert_corrupt(&artifact, corrupt);
    }

    #[test]
    fn rejects_origin_binding_control_and_fixed_order_corruption() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");

        let mut corrupt = witness.clone();
        corrupt.push.source_inst = corrupt.saved_frame_pointer_capture.source_inst;
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.entry_sp_storage = storage(0, 8);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.predicate = PredicateId(1);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.predicate_value = corrupt.return_value.clone();
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.true_arm_order.swap(0, 1);
        assert_corrupt(&artifact, corrupt);

        let mut corrupt = witness.clone();
        corrupt.epilogue_order = corrupt.epilogue_order[..9].into();
        assert_corrupt(&artifact, corrupt);
    }

    #[test]
    fn rejects_state_obligation_ledger_and_manifest_mutations() {
        let (artifact, certified) = certified();
        let witness = certified
            .private_frame_conditional_return()
            .expect("private-frame witness");
        let state_obligation = *witness
            .source_obligations()
            .iter()
            .next()
            .expect("state obligation");

        let mut corrupt_witness = witness.clone();
        corrupt_witness.state_obligations.remove(&state_obligation);
        assert_corrupt(&artifact, corrupt_witness);

        let mappings = manifest(&certified);
        let mut missing_ledger = certified.ledger().clone();
        missing_ledger.effects.remove(&state_obligation);
        assert_eq!(
            certify_private_frame_conditional_return_region(
                certified.origin(),
                &missing_ledger,
                mappings.clone(),
                witness,
            ),
            Err(RenderAuthorizationError::IncompleteLedger)
        );

        let mut duplicate_ledger = certified.ledger().clone();
        let effect = duplicate_ledger.effects(state_obligation)[0].clone();
        duplicate_ledger.record(effect);
        assert_eq!(
            certify_private_frame_conditional_return_region(
                certified.origin(),
                &duplicate_ledger,
                mappings.clone(),
                witness,
            ),
            Err(RenderAuthorizationError::IncompleteLedger)
        );

        let mut missing_manifest = mappings.clone();
        missing_manifest.remove(0);
        assert!(matches!(
            certify_private_frame_conditional_return_region(
                certified.origin(),
                certified.ledger(),
                missing_manifest,
                witness,
            ),
            Err(RenderAuthorizationError::MissingMapping(_))
        ));

        let mut duplicate_manifest = mappings.clone();
        duplicate_manifest.push(mappings[0].clone());
        assert!(matches!(
            certify_private_frame_conditional_return_region(
                certified.origin(),
                certified.ledger(),
                duplicate_manifest,
                witness,
            ),
            Err(RenderAuthorizationError::DuplicateMapping(_))
        ));

        let mut wrong_manifest = mappings;
        wrong_manifest[0].source_disposition = EffectDisposition::ProvenDead;
        assert!(matches!(
            certify_private_frame_conditional_return_region(
                certified.origin(),
                certified.ledger(),
                wrong_manifest,
                witness,
            ),
            Err(RenderAuthorizationError::DispositionMismatch(_))
        ));
    }
}
