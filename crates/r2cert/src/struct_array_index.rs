//! Closed certification for the exact x86-64 `DemoStruct` array update.
//!
//! The certificate retains only typed source identities and canonical
//! instruction/obligation handles. It grants no rendering authority.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CallBoundarySlot, CallBoundaryValueFact, CanonicalInstructionId, CanonicalInstructionSite,
    CanonicalStorageId, CanonicalStorageSpace, InstId, InstPayload, MachineAddressSpace,
    MachineBuildError, MachineMemoryEndianness, SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION,
    SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SSAOp, STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION,
    SemanticInstructionState, SemanticObligationComponent, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind, SourceCarrierKind, SourceFunctionReturn,
    SourceLogicalValue, SourceStackSlotRole, SourceTypeKind, SsaArtifact,
    StructArrayIndexAccessFact, StructArrayIndexAccessKind, StructArrayIndexFact,
    StructArrayIndexFlagPacketFact, StructArrayIndexHomeFact, StructArrayIndexLowering,
    StructArrayIndexScaleFact, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedMachineContext,
    certified_artifact_origin, certified_source_topology,
};

pub const CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION: u32 = 1;

const MEMBER_COUNT: usize = 14;
const MEMBER_SIZE_BYTES: u32 = 4;
const STRIDE_BYTES: u64 = 56;
const ALIGN_BYTES: u64 = 4;
const STORED_MEMBER: u32 = 2;
const LOADED_MEMBER: u32 = 13;
const RAX_OFFSET: u64 = 0;
const RDX_OFFSET: u64 = 16;
const RSI_OFFSET: u64 = 48;
const RDI_OFFSET: u64 = 56;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedStructArrayIndexLowering {
    O2Register,
    O0ParameterHomes,
}

impl From<StructArrayIndexLowering> for CertifiedStructArrayIndexLowering {
    fn from(lowering: StructArrayIndexLowering) -> Self {
        match lowering {
            StructArrayIndexLowering::O2Register => Self::O2Register,
            StructArrayIndexLowering::O0ParameterHomes => Self::O0ParameterHomes,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexLayout {
    signed_integer_type_id: u32,
    aggregate_type_id: u32,
    pointer_type_id: u32,
    aggregate_id: u32,
    stride_bytes: u64,
    align_bytes: u64,
    member_offsets_bytes: Box<[u64]>,
}

impl CertifiedStructArrayIndexLayout {
    pub const fn signed_integer_type_id(&self) -> u32 {
        self.signed_integer_type_id
    }

    pub const fn aggregate_type_id(&self) -> u32 {
        self.aggregate_type_id
    }

    pub const fn pointer_type_id(&self) -> u32 {
        self.pointer_type_id
    }

    pub const fn aggregate_id(&self) -> u32 {
        self.aggregate_id
    }

    pub const fn stride_bytes(&self) -> u64 {
        self.stride_bytes
    }

    pub const fn align_bytes(&self) -> u64 {
        self.align_bytes
    }

    pub const fn member_offsets_bytes(&self) -> &[u64] {
        &self.member_offsets_bytes
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexParameter {
    index: u32,
    abi_storage: CanonicalStorageId,
    graph_storage: CanonicalStorageId,
    graph_value: ValueId,
    logical_value: SourceLogicalValue,
}

impl CertifiedStructArrayIndexParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn abi_storage(&self) -> CanonicalStorageId {
        self.abi_storage
    }

    pub const fn graph_storage(&self) -> CanonicalStorageId {
        self.graph_storage
    }

    pub const fn graph_value(&self) -> ValueId {
        self.graph_value
    }

    pub const fn logical_value(&self) -> SourceLogicalValue {
        self.logical_value
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexHomeReload {
    address_add: CanonicalInstructionId,
    load: CanonicalInstructionId,
    value: ValueId,
}

impl CertifiedStructArrayIndexHomeReload {
    pub const fn address_add(&self) -> CanonicalInstructionId {
        self.address_add
    }

    pub const fn load(&self) -> CanonicalInstructionId {
        self.load
    }

    pub const fn value(&self) -> ValueId {
        self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexHome {
    parameter_index: u32,
    frame_pointer_offset: i64,
    entry_stack_offset: i64,
    size_bytes: u32,
    initializer_address_add: CanonicalInstructionId,
    initializer_copy: CanonicalInstructionId,
    initializer_store: CanonicalInstructionId,
    stored_value: ValueId,
    reloads: Box<[CertifiedStructArrayIndexHomeReload]>,
}

impl CertifiedStructArrayIndexHome {
    pub const fn parameter_index(&self) -> u32 {
        self.parameter_index
    }

    pub const fn frame_pointer_offset(&self) -> i64 {
        self.frame_pointer_offset
    }

    pub const fn entry_stack_offset(&self) -> i64 {
        self.entry_stack_offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub const fn initializer_address_add(&self) -> CanonicalInstructionId {
        self.initializer_address_add
    }

    pub const fn initializer_copy(&self) -> CanonicalInstructionId {
        self.initializer_copy
    }

    pub const fn initializer_store(&self) -> CanonicalInstructionId {
        self.initializer_store
    }

    pub const fn stored_value(&self) -> ValueId {
        self.stored_value
    }

    pub const fn reloads(&self) -> &[CertifiedStructArrayIndexHomeReload] {
        &self.reloads
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexScale {
    signed_index: ValueId,
    sign_extend: CanonicalInstructionId,
    extended_index: ValueId,
    wide_left_extend: CanonicalInstructionId,
    wide_constant_extend: CanonicalInstructionId,
    wide_multiply: CanonicalInstructionId,
    scaled_multiply: CanonicalInstructionId,
    scaled_index: ValueId,
    discarded_high_subpiece: CanonicalInstructionId,
    product_sign_extend: CanonicalInstructionId,
    overflow_compare: CanonicalInstructionId,
    overflow_flag_copy: CanonicalInstructionId,
    stride_bytes: u64,
}

impl CertifiedStructArrayIndexScale {
    pub const fn signed_index(&self) -> ValueId {
        self.signed_index
    }

    pub const fn scaled_index(&self) -> ValueId {
        self.scaled_index
    }

    pub const fn scaled_multiply(&self) -> CanonicalInstructionId {
        self.scaled_multiply
    }

    pub const fn stride_bytes(&self) -> u64 {
        self.stride_bytes
    }

    pub fn instructions(&self) -> [CanonicalInstructionId; 9] {
        [
            self.sign_extend,
            self.wide_left_extend,
            self.wide_constant_extend,
            self.wide_multiply,
            self.scaled_multiply,
            self.discarded_high_subpiece,
            self.product_sign_extend,
            self.overflow_compare,
            self.overflow_flag_copy,
        ]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedStructArrayIndexAccessKind {
    Write,
    Read,
}

impl From<StructArrayIndexAccessKind> for CertifiedStructArrayIndexAccessKind {
    fn from(kind: StructArrayIndexAccessKind) -> Self {
        match kind {
            StructArrayIndexAccessKind::Write => Self::Write,
            StructArrayIndexAccessKind::Read => Self::Read,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexAccess {
    index: u32,
    kind: CertifiedStructArrayIndexAccessKind,
    member_id: u32,
    member_offset_bytes: u64,
    size_bytes: u32,
    memory_space: MachineAddressSpace,
    base_add: CanonicalInstructionId,
    unit_scale: CanonicalInstructionId,
    address_add: CanonicalInstructionId,
    address: ValueId,
    memory_instruction: CanonicalInstructionId,
    value: ValueId,
    memory_obligation: SemanticObligationId,
}

impl CertifiedStructArrayIndexAccess {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn kind(&self) -> CertifiedStructArrayIndexAccessKind {
        self.kind
    }

    pub const fn member_id(&self) -> u32 {
        self.member_id
    }

    pub const fn member_offset_bytes(&self) -> u64 {
        self.member_offset_bytes
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }

    pub const fn base_add(&self) -> CanonicalInstructionId {
        self.base_add
    }

    pub const fn unit_scale(&self) -> CanonicalInstructionId {
        self.unit_scale
    }

    pub const fn address_add(&self) -> CanonicalInstructionId {
        self.address_add
    }

    pub const fn address(&self) -> ValueId {
        self.address
    }

    pub const fn memory_instruction(&self) -> CanonicalInstructionId {
        self.memory_instruction
    }

    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn memory_obligation(&self) -> SemanticObligationId {
        self.memory_obligation
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexFlagPacket {
    value: ValueId,
    instructions: Box<[CanonicalInstructionId]>,
}

impl CertifiedStructArrayIndexFlagPacket {
    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn instructions(&self) -> &[CanonicalInstructionId] {
        &self.instructions
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexReturn {
    slot: CallBoundarySlot,
    returned_value: ValueId,
    add: CanonicalInstructionId,
    zero_extend: CanonicalInstructionId,
    full_value: ValueId,
    return_target: ValueId,
    return_instruction: CanonicalInstructionId,
    return_storage: CanonicalStorageId,
    logical_value: SourceLogicalValue,
    wraps_at_bits: u32,
}

impl CertifiedStructArrayIndexReturn {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn returned_value(&self) -> ValueId {
        self.returned_value
    }

    pub const fn add(&self) -> CanonicalInstructionId {
        self.add
    }

    pub const fn zero_extend(&self) -> CanonicalInstructionId {
        self.zero_extend
    }

    pub const fn full_value(&self) -> ValueId {
        self.full_value
    }

    pub const fn return_target(&self) -> ValueId {
        self.return_target
    }

    pub const fn return_instruction(&self) -> CanonicalInstructionId {
        self.return_instruction
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn logical_value(&self) -> SourceLogicalValue {
        self.logical_value
    }

    pub const fn wraps_at_bits(&self) -> u32 {
        self.wraps_at_bits
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedStructArrayIndexDispositionClass {
    FrameEnvelope,
    ImmutableParameterHome,
    IndexScale,
    ValuePreparation,
    AddressComputation,
    SemanticRelay,
    ProvenDeadArithmetic,
    ProvenDeadFlagPacket,
    ExternalAccess {
        index: u32,
        kind: CertifiedStructArrayIndexAccessKind,
    },
    Wrap32Add,
    ReturnComposition,
}

/// Opaque whole-source proof with an exact-closure obligation ledger.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexFunction {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    entry: u64,
    lowering: CertifiedStructArrayIndexLowering,
    layout: CertifiedStructArrayIndexLayout,
    revision_identity: Box<[u8]>,
    parameters: Box<[CertifiedStructArrayIndexParameter]>,
    homes: Box<[CertifiedStructArrayIndexHome]>,
    scales: Box<[CertifiedStructArrayIndexScale]>,
    value_preparation_instructions: Box<[CanonicalInstructionId]>,
    accesses: Box<[CertifiedStructArrayIndexAccess]>,
    address_flag_packets: Box<[CertifiedStructArrayIndexFlagPacket]>,
    add_flags: CertifiedStructArrayIndexFlagPacket,
    returned: CertifiedStructArrayIndexReturn,
    instruction_inventory: Box<[CanonicalInstructionId]>,
    frame_instructions: BTreeSet<CanonicalInstructionId>,
    semantic_instructions: BTreeSet<CanonicalInstructionId>,
    instruction_dispositions: Box<
        [(
            CanonicalInstructionId,
            CertifiedStructArrayIndexDispositionClass,
        )],
    >,
    obligation_dispositions: Box<
        [(
            SemanticObligationId,
            CertifiedStructArrayIndexDispositionClass,
        )],
    >,
}

impl CertifiedStructArrayIndexFunction {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn contract_version(&self) -> u32 {
        self.contract_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn entry(&self) -> u64 {
        self.entry
    }

    pub const fn lowering(&self) -> CertifiedStructArrayIndexLowering {
        self.lowering
    }

    pub const fn layout(&self) -> &CertifiedStructArrayIndexLayout {
        &self.layout
    }

    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameters(&self) -> &[CertifiedStructArrayIndexParameter] {
        &self.parameters
    }

    pub const fn homes(&self) -> &[CertifiedStructArrayIndexHome] {
        &self.homes
    }

    pub const fn scales(&self) -> &[CertifiedStructArrayIndexScale] {
        &self.scales
    }

    pub const fn value_preparation_instructions(&self) -> &[CanonicalInstructionId] {
        &self.value_preparation_instructions
    }

    pub const fn accesses(&self) -> &[CertifiedStructArrayIndexAccess] {
        &self.accesses
    }

    pub const fn address_flag_packets(&self) -> &[CertifiedStructArrayIndexFlagPacket] {
        &self.address_flag_packets
    }

    pub const fn add_flags(&self) -> &CertifiedStructArrayIndexFlagPacket {
        &self.add_flags
    }

    pub const fn returned(&self) -> &CertifiedStructArrayIndexReturn {
        &self.returned
    }

    pub const fn instruction_inventory(&self) -> &[CanonicalInstructionId] {
        &self.instruction_inventory
    }

    pub const fn frame_instructions(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.frame_instructions
    }

    pub const fn semantic_instructions(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.semantic_instructions
    }

    pub const fn instruction_dispositions(
        &self,
    ) -> &[(
        CanonicalInstructionId,
        CertifiedStructArrayIndexDispositionClass,
    )] {
        &self.instruction_dispositions
    }

    pub const fn obligation_dispositions(
        &self,
    ) -> &[(
        SemanticObligationId,
        CertifiedStructArrayIndexDispositionClass,
    )] {
        &self.obligation_dispositions
    }

    /// Recheck every private field and exact-once ledger entry against the
    /// immutable source inventory retained by the artifact origin.
    pub fn validate(&self, source: &SemanticObligationInventory) -> bool {
        self.validate_contract(source).is_ok()
    }

    fn validate_contract(&self, source: &SemanticObligationInventory) -> Result<(), ()> {
        if self.schema_version != CERTIFICATION_SCHEMA_VERSION
            || self.contract_version != CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION
            || self.origin.source() != source
            || !source.is_complete()
            || !self
                .origin
                .matches_retained_source(source, self.origin.topology())
            || self.origin.topology().entry_addr() != self.entry
            || self.origin.topology().blocks().len() != 1
            || self.revision_identity.is_empty()
        {
            return Err(());
        }
        validate_layout_and_abi(self)?;
        validate_lowering_shape(self)?;
        validate_access_contract(self, source)?;
        validate_instruction_closure(self, source)?;
        validate_typed_bindings(self, source)?;
        validate_obligation_closure(self, source)
    }
}

/// Construct the certificate only from a complete retained SSA artifact.
pub fn certify_struct_array_index_function(
    artifact: &SsaArtifact,
) -> Result<Option<CertifiedStructArrayIndexFunction>, MachineBuildError> {
    let facts = &artifact.structured().struct_array_indexes;
    if facts.is_empty() {
        return Ok(None);
    }
    if facts.len() != 1 {
        return Err(MachineBuildError::TopologyMismatch);
    }
    certify_one(artifact, facts.values().next().expect("one fact")).map(Some)
}

fn certify_one(
    artifact: &SsaArtifact,
    fact: &StructArrayIndexFact,
) -> Result<CertifiedStructArrayIndexFunction, MachineBuildError> {
    if fact.schema_version != STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION
        || !fact.validate_against(artifact)
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    validate_source_fact(fact, artifact)?;
    let machine_context = CertifiedMachineContext::from_artifact(artifact)?;
    let topology = certified_source_topology(artifact)?;
    let origin = certified_artifact_origin(artifact, &machine_context, &topology)?;
    let instruction_inventory = canonical_instructions(artifact, &fact.instruction_inventory)?;
    let parameters = fact
        .abi
        .parameters
        .iter()
        .zip(&fact.abi.parameter_logical_values)
        .map(
            |(parameter, logical_value)| CertifiedStructArrayIndexParameter {
                index: parameter.index,
                abi_storage: parameter.abi_storage,
                graph_storage: parameter.graph_storage,
                graph_value: parameter.graph_value,
                logical_value: *logical_value,
            },
        )
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let homes = fact
        .homes
        .iter()
        .map(|home| certified_home(artifact, home))
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let scales = fact
        .scales
        .iter()
        .map(|scale| certified_scale(artifact, scale))
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let accesses = fact
        .accesses
        .iter()
        .enumerate()
        .map(|(index, access)| certified_access(artifact, index, access))
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let address_flag_packets = fact
        .address_flag_packets
        .iter()
        .map(|packet| certified_flag_packet(artifact, packet))
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let add_flags = certified_flag_packet(artifact, &fact.add_flags)?;
    let returned = certified_return(artifact, fact)?;
    let value_preparation_instructions =
        canonical_instructions(artifact, &fact.value_preparation_instructions)?.into_boxed_slice();

    let mut certificate = CertifiedStructArrayIndexFunction {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION,
        origin,
        entry: fact.entry,
        lowering: fact.lowering.into(),
        layout: CertifiedStructArrayIndexLayout {
            signed_integer_type_id: fact.types.signed_integer_type_id,
            aggregate_type_id: fact.types.aggregate_type_id,
            pointer_type_id: fact.types.pointer_type_id,
            aggregate_id: fact.types.aggregate_id,
            stride_bytes: fact.types.stride_bytes,
            align_bytes: fact.types.align_bytes,
            member_offsets_bytes: fact.types.member_offsets_bytes.clone(),
        },
        revision_identity: fact.abi.revision_identity.clone(),
        parameters,
        homes,
        scales,
        value_preparation_instructions,
        accesses,
        address_flag_packets,
        add_flags,
        returned,
        instruction_inventory: instruction_inventory.into_boxed_slice(),
        frame_instructions: canonical_instructions(artifact, &fact.frame_instructions)?
            .into_iter()
            .collect(),
        semantic_instructions: canonical_instructions(artifact, &fact.semantic_instructions)?
            .into_iter()
            .collect(),
        instruction_dispositions: Box::new([]),
        obligation_dispositions: Box::new([]),
    };
    certificate.instruction_dispositions =
        instruction_dispositions(artifact, fact, &certificate)?.into_boxed_slice();
    certificate.obligation_dispositions =
        obligation_dispositions(artifact.obligations(), &certificate)?.into_boxed_slice();
    if !certificate.validate(artifact.obligations()) {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(certificate)
}

fn validate_source_fact(
    fact: &StructArrayIndexFact,
    artifact: &SsaArtifact,
) -> Result<(), MachineBuildError> {
    let interface = artifact
        .machine_context()
        .function_interface()
        .ok_or(MachineBuildError::MachineContextMismatch)?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.calling_convention() != "sysv_amd64"
        || interface.revision_identity() != &*fact.abi.revision_identity
        || interface.parameters().len() != 3
        || interface.parameter_logical_values() != &*fact.abi.parameter_logical_values
        || interface.return_logical_value() != Some(fact.abi.return_logical_value)
        || interface.return_kind()
            != (SourceFunctionReturn::Register {
                storage: fact.abi.return_storage,
            })
        || interface
            .type_graph()
            .is_none_or(|graph| graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION)
        || artifact
            .obligations()
            .instructions()
            .values()
            .any(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return Err(MachineBuildError::MachineContextMismatch);
    }
    validate_direct_return(fact, artifact)
}

fn validate_direct_return(
    fact: &StructArrayIndexFact,
    artifact: &SsaArtifact,
) -> Result<(), MachineBuildError> {
    let slot = CallBoundarySlot::Register {
        index: 0,
        storage: fact.abi.return_storage,
    };
    let boundary = artifact
        .facts()
        .boundaries
        .returns
        .get(&fact.returned.return_inst)
        .ok_or(MachineBuildError::TopologyMismatch)?;
    let zero_extend = artifact.graph().inst(fact.returned.zero_extend).ok_or(
        MachineBuildError::MissingInstruction(fact.returned.zero_extend),
    )?;
    let returned = artifact.graph().inst(fact.returned.return_inst).ok_or(
        MachineBuildError::MissingInstruction(fact.returned.return_inst),
    )?;
    if fact.returned.composition.is_some()
        || fact.returned.definition.storage != fact.abi.return_storage
        || fact.returned.definition.producer != fact.returned.zero_extend
        || fact.returned.definition.value != fact.returned.physical_full_register
        || !boundary.complete
        || boundary.values.as_slice()
            != [CallBoundaryValueFact {
                slot,
                value: fact.returned.physical_full_register,
            }]
        || !boundary.register_compositions.is_empty()
        || zero_extend.output != Some(fact.returned.physical_full_register)
        || zero_extend.inputs.as_slice() != [fact.returned.returned_value]
        || !matches!(zero_extend.payload, InstPayload::Op(SSAOp::IntZExt { .. }))
        || returned.inputs.as_slice() != [fact.returned.return_target]
        || !matches!(returned.payload, InstPayload::Op(SSAOp::Return { .. }))
        || fact.returned.wraps_at_bits != 32
        || !register_storage(fact.abi.return_storage, RAX_OFFSET, 8)
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(())
}

fn certified_home(
    artifact: &SsaArtifact,
    home: &StructArrayIndexHomeFact,
) -> Result<CertifiedStructArrayIndexHome, MachineBuildError> {
    Ok(CertifiedStructArrayIndexHome {
        parameter_index: home.parameter_index,
        frame_pointer_offset: home.frame_pointer_offset,
        entry_stack_offset: home.entry_stack_offset,
        size_bytes: home.size_bytes,
        initializer_address_add: canonical_instruction(artifact, home.initializer_address_add)?,
        initializer_copy: canonical_instruction(artifact, home.initializer_copy)?,
        initializer_store: canonical_instruction(artifact, home.initializer_store)?,
        stored_value: home.stored_value,
        reloads: home
            .reloads
            .iter()
            .map(|reload| {
                Ok(CertifiedStructArrayIndexHomeReload {
                    address_add: canonical_instruction(artifact, reload.address_add)?,
                    load: canonical_instruction(artifact, reload.load)?,
                    value: reload.value,
                })
            })
            .collect::<Result<Vec<_>, MachineBuildError>>()?
            .into_boxed_slice(),
    })
}

fn certified_scale(
    artifact: &SsaArtifact,
    scale: &StructArrayIndexScaleFact,
) -> Result<CertifiedStructArrayIndexScale, MachineBuildError> {
    Ok(CertifiedStructArrayIndexScale {
        signed_index: scale.signed_index,
        sign_extend: canonical_instruction(artifact, scale.sign_extend)?,
        extended_index: scale.extended_index,
        wide_left_extend: canonical_instruction(artifact, scale.wide_left_extend)?,
        wide_constant_extend: canonical_instruction(artifact, scale.wide_constant_extend)?,
        wide_multiply: canonical_instruction(artifact, scale.wide_multiply)?,
        scaled_multiply: canonical_instruction(artifact, scale.scaled_multiply)?,
        scaled_index: scale.scaled_index,
        discarded_high_subpiece: canonical_instruction(artifact, scale.discarded_high_subpiece)?,
        product_sign_extend: canonical_instruction(artifact, scale.product_sign_extend)?,
        overflow_compare: canonical_instruction(artifact, scale.overflow_compare)?,
        overflow_flag_copy: canonical_instruction(artifact, scale.overflow_flag_copy)?,
        stride_bytes: scale.stride_bytes,
    })
}

fn certified_access(
    artifact: &SsaArtifact,
    index: usize,
    access: &StructArrayIndexAccessFact,
) -> Result<CertifiedStructArrayIndexAccess, MachineBuildError> {
    let index = u32::try_from(index).map_err(|_| MachineBuildError::TopologyMismatch)?;
    let memory_instruction = canonical_instruction(artifact, access.memory_inst)?;
    let expected_kind = match access.kind {
        StructArrayIndexAccessKind::Write => SemanticObligationKind::ObservableMemoryWrite,
        StructArrayIndexAccessKind::Read => SemanticObligationKind::ObservableMemoryRead,
    };
    let matching = artifact
        .obligations()
        .obligations()
        .keys()
        .copied()
        .filter(|obligation| {
            obligation.instruction == memory_instruction
                && obligation.kind == expected_kind
                && matches!(
                    obligation.component,
                    SemanticObligationComponent::MemoryAccess(_)
                )
        })
        .collect::<Vec<_>>();
    let [memory_obligation] = matching.as_slice() else {
        return Err(MachineBuildError::ObligationMismatch(access.memory_inst));
    };
    Ok(CertifiedStructArrayIndexAccess {
        index,
        kind: access.kind.into(),
        member_id: access.member_id,
        member_offset_bytes: access.member_offset_bytes,
        size_bytes: access.size_bytes,
        memory_space: access.memory_space.into(),
        base_add: canonical_instruction(artifact, access.base_add)?,
        unit_scale: canonical_instruction(artifact, access.unit_scale)?,
        address_add: canonical_instruction(artifact, access.address_add)?,
        address: access.address,
        memory_instruction,
        value: access.value,
        memory_obligation: *memory_obligation,
    })
}

fn certified_flag_packet(
    artifact: &SsaArtifact,
    packet: &StructArrayIndexFlagPacketFact,
) -> Result<CertifiedStructArrayIndexFlagPacket, MachineBuildError> {
    Ok(CertifiedStructArrayIndexFlagPacket {
        value: packet.value,
        instructions: canonical_instructions(
            artifact,
            &[
                packet.sign,
                packet.zero_equal,
                packet.low_byte_mask,
                packet.population_count,
                packet.parity_mask,
                packet.parity_equal,
            ],
        )?
        .into_boxed_slice(),
    })
}

fn certified_return(
    artifact: &SsaArtifact,
    fact: &StructArrayIndexFact,
) -> Result<CertifiedStructArrayIndexReturn, MachineBuildError> {
    Ok(CertifiedStructArrayIndexReturn {
        slot: CallBoundarySlot::Register {
            index: 0,
            storage: fact.abi.return_storage,
        },
        returned_value: fact.returned.returned_value,
        add: canonical_instruction(artifact, fact.returned.add)?,
        zero_extend: canonical_instruction(artifact, fact.returned.zero_extend)?,
        full_value: fact.returned.physical_full_register,
        return_target: fact.returned.return_target,
        return_instruction: canonical_instruction(artifact, fact.returned.return_inst)?,
        return_storage: fact.abi.return_storage,
        logical_value: fact.abi.return_logical_value,
        wraps_at_bits: fact.returned.wraps_at_bits,
    })
}

fn validate_layout_and_abi(certificate: &CertifiedStructArrayIndexFunction) -> Result<(), ()> {
    let layout = &certificate.layout;
    if layout.stride_bytes != STRIDE_BYTES
        || layout.align_bytes != ALIGN_BYTES
        || layout.member_offsets_bytes.len() != MEMBER_COUNT
        || layout
            .member_offsets_bytes
            .iter()
            .enumerate()
            .any(|(index, offset)| *offset != index as u64 * u64::from(MEMBER_SIZE_BYTES))
        || certificate.parameters.len() != 3
        || certificate
            .parameters
            .iter()
            .enumerate()
            .any(|(index, parameter)| {
                parameter.index != index as u32
                    || parameter.logical_value.type_id()
                        != if index == 0 {
                            layout.pointer_type_id
                        } else {
                            layout.signed_integer_type_id
                        }
                    || parameter.logical_value.carrier().offset_bits() != 0
                    || parameter.logical_value.carrier().kind()
                        != if index == 0 {
                            SourceCarrierKind::Full
                        } else {
                            SourceCarrierKind::LowBits
                        }
                    || parameter.logical_value.carrier().size_bits()
                        != if index == 0 { 64 } else { 32 }
            })
        || !register_storage(certificate.parameters[0].abi_storage, RDI_OFFSET, 8)
        || certificate.parameters[0].graph_storage != certificate.parameters[0].abi_storage
        || !register_storage(certificate.parameters[1].abi_storage, RSI_OFFSET, 8)
        || !register_storage(certificate.parameters[1].graph_storage, RSI_OFFSET, 4)
        || !register_storage(certificate.parameters[2].abi_storage, RDX_OFFSET, 8)
        || !register_storage(certificate.parameters[2].graph_storage, RDX_OFFSET, 4)
        || certificate.returned.logical_value.type_id() != layout.signed_integer_type_id
        || certificate.returned.logical_value.carrier().kind() != SourceCarrierKind::LowBits
        || certificate.returned.logical_value.carrier().offset_bits() != 0
        || certificate.returned.logical_value.carrier().size_bits() != 32
        || !register_storage(certificate.returned.return_storage, RAX_OFFSET, 8)
        || certificate.returned.slot
            != (CallBoundarySlot::Register {
                index: 0,
                storage: certificate.returned.return_storage,
            })
        || certificate.returned.wraps_at_bits != 32
        || certificate
            .origin
            .machine_context()
            .source()
            .function_interface()
            .is_none_or(|interface| {
                interface.calling_convention() != "sysv_amd64"
                    || interface.revision_identity() != &*certificate.revision_identity
                    || interface.parameters().len() != certificate.parameters.len()
                    || interface
                        .parameters()
                        .iter()
                        .zip(&certificate.parameters)
                        .any(|(source, certified)| {
                            source.index() != certified.index
                                || source.storage() != certified.abi_storage
                        })
                    || interface.parameter_logical_values()
                        != certificate
                            .parameters
                            .iter()
                            .map(|parameter| parameter.logical_value)
                            .collect::<Vec<_>>()
                    || interface.return_logical_value() != Some(certificate.returned.logical_value)
                    || interface.return_kind()
                        != (SourceFunctionReturn::Register {
                            storage: certificate.returned.return_storage,
                        })
            })
    {
        return Err(());
    }
    let graph = certificate
        .origin
        .machine_context()
        .source()
        .function_interface()
        .and_then(|interface| interface.type_graph())
        .ok_or(())?;
    let signed = graph
        .types()
        .get(layout.signed_integer_type_id as usize)
        .ok_or(())?;
    let aggregate_type = graph
        .types()
        .get(layout.aggregate_type_id as usize)
        .ok_or(())?;
    let pointer = graph
        .types()
        .get(layout.pointer_type_id as usize)
        .ok_or(())?;
    let aggregate = graph
        .aggregates()
        .get(layout.aggregate_id as usize)
        .ok_or(())?;
    if signed.kind() != SourceTypeKind::SignedInteger
        || signed.size_bits() != 32
        || signed.align_bits() != 32
        || aggregate_type.kind()
            != (SourceTypeKind::Struct {
                aggregate_id: layout.aggregate_id,
            })
        || aggregate_type.size_bits() != STRIDE_BYTES * 8
        || aggregate_type.align_bits() != ALIGN_BYTES * 8
        || pointer.kind()
            != (SourceTypeKind::Pointer {
                target_type_id: layout.aggregate_type_id,
            })
        || aggregate.type_id() != layout.aggregate_type_id
        || aggregate.size_bits() != STRIDE_BYTES * 8
        || aggregate.align_bits() != ALIGN_BYTES * 8
        || aggregate.members().len() != MEMBER_COUNT
        || aggregate
            .members()
            .iter()
            .enumerate()
            .any(|(index, member)| {
                member.member_id() != index as u32
                    || member.type_id() != layout.signed_integer_type_id
                    || member.offset_bits() != layout.member_offsets_bytes[index] * 8
                    || member.size_bits() != u64::from(MEMBER_SIZE_BYTES) * 8
            })
    {
        return Err(());
    }
    Ok(())
}

fn validate_lowering_shape(certificate: &CertifiedStructArrayIndexFunction) -> Result<(), ()> {
    let (inventory, semantics, homes, scales, preparation, accesses, address_packets) =
        match certificate.lowering {
            CertifiedStructArrayIndexLowering::O2Register => (43, 32, 0, 1, 2, 4, 0),
            CertifiedStructArrayIndexLowering::O0ParameterHomes => (114, 103, 3, 3, 5, 5, 3),
        };
    if certificate.instruction_inventory.len() != inventory
        || certificate.homes.len() != homes
        || certificate.scales.len() != scales
        || certificate.value_preparation_instructions.len() != preparation
        || certificate.accesses.len() != accesses
        || certificate.address_flag_packets.len() != address_packets
        || certificate.frame_instructions.len() != 11
        || certificate.semantic_instructions.len() != semantics
        || certificate
            .instruction_dispositions
            .iter()
            .filter(|(_, class)| {
                !matches!(
                    class,
                    CertifiedStructArrayIndexDispositionClass::FrameEnvelope
                )
            })
            .count()
            != semantics + 1
        || certificate.scales.iter().any(|scale| {
            scale.stride_bytes != certificate.layout.stride_bytes
                || scale
                    .instructions()
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    .len()
                    != 9
        })
        || certificate.add_flags.instructions.len() != 6
        || certificate
            .address_flag_packets
            .iter()
            .any(|packet| packet.instructions.len() != 6)
    {
        return Err(());
    }
    match certificate.lowering {
        CertifiedStructArrayIndexLowering::O2Register => {
            if !certificate
                .origin
                .machine_context()
                .source()
                .function_interface()
                .is_some_and(|interface| interface.stack_slots().is_empty())
            {
                return Err(());
            }
        }
        CertifiedStructArrayIndexLowering::O0ParameterHomes => {
            let expected = [(0, -8, -16, 8, 3), (1, -12, -20, 4, 3), (2, -16, -24, 4, 1)];
            if certificate.homes.iter().zip(expected).any(
                |(home, (parameter, frame, stack, size, reloads))| {
                    home.parameter_index != parameter
                        || home.frame_pointer_offset != frame
                        || home.entry_stack_offset != stack
                        || home.size_bytes != size
                        || home.reloads.len() != reloads
                },
            ) || !certificate
                .origin
                .machine_context()
                .source()
                .function_interface()
                .is_some_and(|interface| {
                    interface.stack_slots().len() == 3
                        && interface.stack_slots().iter().all(|slot| {
                            matches!(slot.role(), SourceStackSlotRole::ParameterHome { .. })
                        })
                })
            {
                return Err(());
            }
        }
    }
    Ok(())
}

fn validate_access_contract(
    certificate: &CertifiedStructArrayIndexFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let expected = match certificate.lowering {
        CertifiedStructArrayIndexLowering::O2Register => vec![
            (CertifiedStructArrayIndexAccessKind::Write, STORED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, LOADED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, LOADED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, LOADED_MEMBER),
        ],
        CertifiedStructArrayIndexLowering::O0ParameterHomes => vec![
            (CertifiedStructArrayIndexAccessKind::Write, STORED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, STORED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, LOADED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, LOADED_MEMBER),
            (CertifiedStructArrayIndexAccessKind::Read, LOADED_MEMBER),
        ],
    };
    if certificate.accesses.iter().zip(expected).enumerate().any(
        |(index, (access, (kind, member)))| {
            access.index != index as u32
                || access.kind != kind
                || access.member_id != member
                || access.member_offset_bytes
                    != certificate.layout.member_offsets_bytes[member as usize]
                || access.size_bytes != MEMBER_SIZE_BYTES
                || access.memory_obligation.instruction != access.memory_instruction
                || access.memory_obligation.kind
                    != match kind {
                        CertifiedStructArrayIndexAccessKind::Write => {
                            SemanticObligationKind::ObservableMemoryWrite
                        }
                        CertifiedStructArrayIndexAccessKind::Read => {
                            SemanticObligationKind::ObservableMemoryRead
                        }
                    }
                || !matches!(
                    access.memory_obligation.component,
                    SemanticObligationComponent::MemoryAccess(_)
                )
                || source
                    .obligations()
                    .get(&access.memory_obligation)
                    .is_none_or(|obligation| !match kind {
                        CertifiedStructArrayIndexAccessKind::Write => {
                            obligation.inputs.as_slice() == [access.address, access.value]
                        }
                        CertifiedStructArrayIndexAccessKind::Read => {
                            obligation.inputs.as_slice() == [access.address]
                        }
                    })
                || memory_space_for_instruction(certificate, access.memory_instruction)
                    != Some(access.memory_space)
        },
    ) || !certificate
        .accesses
        .windows(2)
        .all(|pair| pair[0].memory_instruction < pair[1].memory_instruction)
        || certificate
            .accesses
            .iter()
            .map(|access| access.memory_instruction)
            .collect::<BTreeSet<_>>()
            .len()
            != certificate.accesses.len()
        || certificate
            .accesses
            .iter()
            .filter(|access| access.member_id == LOADED_MEMBER)
            .map(|access| access.value)
            .collect::<BTreeSet<_>>()
            .len()
            != 3
    {
        return Err(());
    }
    let external_space = certificate.accesses[0].memory_space;
    if certificate
        .accesses
        .iter()
        .any(|access| access.memory_space != external_space)
    {
        return Err(());
    }
    let memory = certificate.origin.machine_context().source().memory_model();
    let source_space = match certificate.accesses[0].memory_instruction.site {
        CanonicalInstructionSite::Op(ordinal) => {
            usize::try_from(ordinal).ok().and_then(|ordinal| {
                certificate
                    .origin
                    .machine_context()
                    .source()
                    .memory_space_at(certificate.entry, ordinal)
            })
        }
        CanonicalInstructionSite::Phi(_) => None,
    }
    .ok_or(())?;
    if memory.space(source_space).is_none_or(|space| {
        space.address_bits() != 64
            || space.word_size_bytes() != 1
            || space.endianness() != MachineMemoryEndianness::Little
    }) {
        return Err(());
    }
    match certificate.lowering {
        CertifiedStructArrayIndexLowering::O2Register => {
            if certificate.accesses[1..].iter().any(|access| {
                access.base_add != certificate.accesses[1].base_add
                    || access.unit_scale != certificate.accesses[1].unit_scale
                    || access.address_add != certificate.accesses[1].address_add
                    || access.address != certificate.accesses[1].address
            }) {
                return Err(());
            }
        }
        CertifiedStructArrayIndexLowering::O0ParameterHomes => {
            if certificate.accesses[2..].iter().any(|access| {
                access.base_add != certificate.accesses[2].base_add
                    || access.unit_scale != certificate.accesses[2].unit_scale
                    || access.address_add != certificate.accesses[2].address_add
                    || access.address != certificate.accesses[2].address
            }) || certificate
                .accesses
                .iter()
                .enumerate()
                .any(|(index, access)| {
                    access.unit_scale != certificate.scales[index.min(2)].scaled_multiply
                })
            {
                return Err(());
            }
        }
    }
    Ok(())
}

fn validate_instruction_closure(
    certificate: &CertifiedStructArrayIndexFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let inventory = certificate
        .instruction_inventory
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let dispositions = certificate
        .instruction_dispositions
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    if inventory.len() != certificate.instruction_inventory.len()
        || inventory != source.instructions().keys().copied().collect()
        || dispositions.len() != certificate.instruction_dispositions.len()
        || dispositions.keys().copied().collect::<BTreeSet<_>>() != inventory
        || certificate
            .frame_instructions
            .intersection(&certificate.semantic_instructions)
            .next()
            .is_some()
        || certificate
            .frame_instructions
            .union(&certificate.semantic_instructions)
            .copied()
            .collect::<BTreeSet<_>>()
            != inventory
        || certificate
            .instruction_inventory
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(());
    }
    for (instruction, class) in &certificate.instruction_dispositions {
        let source_instruction = source.instructions().get(instruction).ok_or(())?;
        if source_instruction.state == SemanticInstructionState::UnsupportedUnknown
            || certificate.frame_instructions.contains(instruction)
                && *instruction != certificate.returned.return_instruction
                && *class != CertifiedStructArrayIndexDispositionClass::FrameEnvelope
            || certificate.semantic_instructions.contains(instruction)
                && *class == CertifiedStructArrayIndexDispositionClass::FrameEnvelope
            || matches!(
                class,
                CertifiedStructArrayIndexDispositionClass::ProvenDeadArithmetic
                    | CertifiedStructArrayIndexDispositionClass::ProvenDeadFlagPacket
            ) && source_instruction.state != SemanticInstructionState::ProvenDead
            || *class == CertifiedStructArrayIndexDispositionClass::SemanticRelay
                && source_instruction.state != SemanticInstructionState::LiveObligation
        {
            return Err(());
        }
    }
    Ok(())
}

fn validate_typed_bindings(
    certificate: &CertifiedStructArrayIndexFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let dispositions = certificate
        .instruction_dispositions
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    let has_class = |instruction, class| dispositions.get(&instruction) == Some(&class);
    for home in &certificate.homes {
        if [
            home.initializer_address_add,
            home.initializer_copy,
            home.initializer_store,
        ]
        .into_iter()
        .chain(
            home.reloads
                .iter()
                .flat_map(|reload| [reload.address_add, reload.load]),
        )
        .any(|instruction| {
            !has_class(
                instruction,
                CertifiedStructArrayIndexDispositionClass::ImmutableParameterHome,
            )
        }) {
            return Err(());
        }
    }
    for scale in &certificate.scales {
        if scale.instructions().into_iter().any(|instruction| {
            !has_class(
                instruction,
                CertifiedStructArrayIndexDispositionClass::IndexScale,
            )
        }) {
            return Err(());
        }
    }
    if certificate
        .value_preparation_instructions
        .iter()
        .copied()
        .any(|instruction| {
            !has_class(
                instruction,
                CertifiedStructArrayIndexDispositionClass::ValuePreparation,
            )
        })
        || certificate
            .address_flag_packets
            .iter()
            .chain(std::iter::once(&certificate.add_flags))
            .flat_map(|packet| packet.instructions.iter().copied())
            .any(|instruction| {
                !has_class(
                    instruction,
                    CertifiedStructArrayIndexDispositionClass::ProvenDeadFlagPacket,
                )
            })
    {
        return Err(());
    }
    for access in &certificate.accesses {
        if !matches!(
            dispositions.get(&access.base_add),
            Some(
                CertifiedStructArrayIndexDispositionClass::AddressComputation
                    | CertifiedStructArrayIndexDispositionClass::IndexScale
            )
        ) || !matches!(
            dispositions.get(&access.unit_scale),
            Some(
                CertifiedStructArrayIndexDispositionClass::AddressComputation
                    | CertifiedStructArrayIndexDispositionClass::IndexScale
            )
        ) || !matches!(
            dispositions.get(&access.address_add),
            Some(
                CertifiedStructArrayIndexDispositionClass::AddressComputation
                    | CertifiedStructArrayIndexDispositionClass::IndexScale
            )
        ) || !has_class(
            access.memory_instruction,
            CertifiedStructArrayIndexDispositionClass::ExternalAccess {
                index: access.index,
                kind: access.kind,
            },
        ) {
            return Err(());
        }
    }
    if !has_class(
        certificate.returned.add,
        CertifiedStructArrayIndexDispositionClass::Wrap32Add,
    ) || !has_class(
        certificate.returned.zero_extend,
        CertifiedStructArrayIndexDispositionClass::ReturnComposition,
    ) || !has_class(
        certificate.returned.return_instruction,
        CertifiedStructArrayIndexDispositionClass::ReturnComposition,
    ) {
        return Err(());
    }
    let return_value = source
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == certificate.returned.return_instruction
                && obligation.id.kind == SemanticObligationKind::ReturnValue
                && obligation.id.component
                    == (SemanticObligationComponent::RegisterSlot {
                        index: 0,
                        storage: certificate.returned.return_storage,
                    })
        })
        .collect::<Vec<_>>();
    if !matches!(return_value.as_slice(), [obligation]
        if obligation.inputs.as_slice() == [certificate.returned.full_value])
    {
        return Err(());
    }
    let direct_definition = source
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == certificate.returned.zero_extend
                && obligation.id.kind == SemanticObligationKind::LiveValueProducer
                && obligation.id.component == SemanticObligationComponent::Whole
        })
        .collect::<Vec<_>>();
    if !matches!(direct_definition.as_slice(), [obligation]
        if obligation.inputs.as_slice() == [certificate.returned.returned_value])
    {
        return Err(());
    }
    Ok(())
}

fn memory_space_for_instruction(
    certificate: &CertifiedStructArrayIndexFunction,
    instruction: CanonicalInstructionId,
) -> Option<MachineAddressSpace> {
    let CanonicalInstructionSite::Op(ordinal) = instruction.site else {
        return None;
    };
    let ordinal = usize::try_from(ordinal).ok()?;
    certificate
        .origin
        .machine_context()
        .source()
        .memory_space_at(instruction.block_addr, ordinal)
        .map(Into::into)
}

fn validate_obligation_closure(
    certificate: &CertifiedStructArrayIndexFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let instructions = certificate
        .instruction_dispositions
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    let obligations = certificate
        .obligation_dispositions
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    if obligations.len() != certificate.obligation_dispositions.len()
        || obligations.len() != source.obligations().len()
        || obligations.keys().copied().collect::<BTreeSet<_>>()
            != source.obligations().keys().copied().collect()
    {
        return Err(());
    }
    for (obligation, class) in &certificate.obligation_dispositions {
        if instructions.get(&obligation.instruction) != Some(class)
            || !obligation_allowed(*obligation, *class)
        {
            return Err(());
        }
    }
    for access in &certificate.accesses {
        if obligations.get(&access.memory_obligation)
            != Some(&CertifiedStructArrayIndexDispositionClass::ExternalAccess {
                index: access.index,
                kind: access.kind,
            })
        {
            return Err(());
        }
    }
    Ok(())
}

fn obligation_allowed(
    obligation: SemanticObligationId,
    class: CertifiedStructArrayIndexDispositionClass,
) -> bool {
    match class {
        CertifiedStructArrayIndexDispositionClass::FrameEnvelope => matches!(
            obligation.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::ObservableMemoryRead
                | SemanticObligationKind::ObservableMemoryWrite
                | SemanticObligationKind::ControlTransfer
                | SemanticObligationKind::Return
                | SemanticObligationKind::ReturnValue
                | SemanticObligationKind::Trap
                | SemanticObligationKind::VolatileOrUnknownEffect
        ),
        CertifiedStructArrayIndexDispositionClass::ImmutableParameterHome => matches!(
            obligation.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::ObservableMemoryRead
                | SemanticObligationKind::ObservableMemoryWrite
                | SemanticObligationKind::Trap
                | SemanticObligationKind::VolatileOrUnknownEffect
        ),
        CertifiedStructArrayIndexDispositionClass::ExternalAccess { kind, .. } => {
            matches!(obligation.kind, SemanticObligationKind::LiveValueProducer)
                || obligation.kind
                    == match kind {
                        CertifiedStructArrayIndexAccessKind::Write => {
                            SemanticObligationKind::ObservableMemoryWrite
                        }
                        CertifiedStructArrayIndexAccessKind::Read => {
                            SemanticObligationKind::ObservableMemoryRead
                        }
                    }
        }
        CertifiedStructArrayIndexDispositionClass::ReturnComposition => matches!(
            obligation.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::Return
                | SemanticObligationKind::ReturnValue
                | SemanticObligationKind::ControlTransfer
        ),
        CertifiedStructArrayIndexDispositionClass::IndexScale
        | CertifiedStructArrayIndexDispositionClass::ValuePreparation
        | CertifiedStructArrayIndexDispositionClass::AddressComputation
        | CertifiedStructArrayIndexDispositionClass::SemanticRelay
        | CertifiedStructArrayIndexDispositionClass::Wrap32Add => matches!(
            obligation.kind,
            SemanticObligationKind::LiveValueProducer | SemanticObligationKind::Trap
        ),
        CertifiedStructArrayIndexDispositionClass::ProvenDeadArithmetic
        | CertifiedStructArrayIndexDispositionClass::ProvenDeadFlagPacket => false,
    }
}

fn instruction_dispositions(
    artifact: &SsaArtifact,
    fact: &StructArrayIndexFact,
    certificate: &CertifiedStructArrayIndexFunction,
) -> Result<
    Vec<(
        CanonicalInstructionId,
        CertifiedStructArrayIndexDispositionClass,
    )>,
    MachineBuildError,
> {
    let source = artifact.obligations();
    let mut classes = BTreeMap::new();
    assign_many(
        &mut classes,
        canonical_instructions(artifact, &fact.frame_instructions)?,
        CertifiedStructArrayIndexDispositionClass::FrameEnvelope,
    )?;
    for home in &certificate.homes {
        let instructions = [
            home.initializer_address_add,
            home.initializer_copy,
            home.initializer_store,
        ]
        .into_iter()
        .chain(
            home.reloads
                .iter()
                .flat_map(|reload| [reload.address_add, reload.load]),
        );
        assign_many(
            &mut classes,
            instructions,
            CertifiedStructArrayIndexDispositionClass::ImmutableParameterHome,
        )?;
    }
    for scale in &certificate.scales {
        assign_many(
            &mut classes,
            scale.instructions(),
            CertifiedStructArrayIndexDispositionClass::IndexScale,
        )?;
    }
    assign_many(
        &mut classes,
        certificate.value_preparation_instructions.iter().copied(),
        CertifiedStructArrayIndexDispositionClass::ValuePreparation,
    )?;
    for packet in certificate
        .address_flag_packets
        .iter()
        .chain(std::iter::once(&certificate.add_flags))
    {
        assign_many(
            &mut classes,
            packet.instructions.iter().copied(),
            CertifiedStructArrayIndexDispositionClass::ProvenDeadFlagPacket,
        )?;
    }
    for access in &certificate.accesses {
        for instruction in [access.base_add, access.unit_scale, access.address_add] {
            if classes
                .get(&instruction)
                .is_none_or(|class| *class != CertifiedStructArrayIndexDispositionClass::IndexScale)
            {
                assign(
                    &mut classes,
                    instruction,
                    CertifiedStructArrayIndexDispositionClass::AddressComputation,
                )?;
            }
        }
        assign(
            &mut classes,
            access.memory_instruction,
            CertifiedStructArrayIndexDispositionClass::ExternalAccess {
                index: access.index,
                kind: access.kind,
            },
        )?;
    }
    assign(
        &mut classes,
        certificate.returned.add,
        CertifiedStructArrayIndexDispositionClass::Wrap32Add,
    )?;
    assign(
        &mut classes,
        certificate.returned.zero_extend,
        CertifiedStructArrayIndexDispositionClass::ReturnComposition,
    )?;
    classes.insert(
        certificate.returned.return_instruction,
        CertifiedStructArrayIndexDispositionClass::ReturnComposition,
    );

    let semantic = canonical_instructions(artifact, &fact.semantic_instructions)?
        .into_iter()
        .collect::<BTreeSet<_>>();
    let residue = semantic
        .iter()
        .copied()
        .filter(|instruction| !classes.contains_key(instruction))
        .collect::<Vec<_>>();
    let (expected_live, expected_dead) = match fact.lowering {
        StructArrayIndexLowering::O2Register => (1, 2),
        StructArrayIndexLowering::O0ParameterHomes => (3, 8),
    };
    let live = residue
        .iter()
        .filter(|instruction| {
            source
                .instructions()
                .get(instruction)
                .is_some_and(|source| source.state == SemanticInstructionState::LiveObligation)
        })
        .count();
    let dead = residue
        .iter()
        .filter(|instruction| {
            source
                .instructions()
                .get(instruction)
                .is_some_and(|source| source.state == SemanticInstructionState::ProvenDead)
        })
        .count();
    if residue.len() != expected_live + expected_dead
        || live != expected_live
        || dead != expected_dead
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    for instruction in residue {
        let class = match source
            .instructions()
            .get(&instruction)
            .map(|source| source.state)
        {
            Some(SemanticInstructionState::LiveObligation) => {
                CertifiedStructArrayIndexDispositionClass::SemanticRelay
            }
            Some(SemanticInstructionState::ProvenDead) => {
                CertifiedStructArrayIndexDispositionClass::ProvenDeadArithmetic
            }
            _ => return Err(MachineBuildError::TopologyMismatch),
        };
        assign(&mut classes, instruction, class)?;
    }
    Ok(classes.into_iter().collect())
}

fn obligation_dispositions(
    source: &SemanticObligationInventory,
    certificate: &CertifiedStructArrayIndexFunction,
) -> Result<
    Vec<(
        SemanticObligationId,
        CertifiedStructArrayIndexDispositionClass,
    )>,
    MachineBuildError,
> {
    let instructions = certificate
        .instruction_dispositions
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    source
        .obligations()
        .keys()
        .copied()
        .map(|obligation| {
            let class = instructions
                .get(&obligation.instruction)
                .copied()
                .filter(|class| obligation_allowed(obligation, *class))
                .ok_or_else(|| obligation_error(source, obligation))?;
            Ok((obligation, class))
        })
        .collect()
}

fn assign_many(
    classes: &mut BTreeMap<CanonicalInstructionId, CertifiedStructArrayIndexDispositionClass>,
    instructions: impl IntoIterator<Item = CanonicalInstructionId>,
    class: CertifiedStructArrayIndexDispositionClass,
) -> Result<(), MachineBuildError> {
    for instruction in instructions {
        assign(classes, instruction, class)?;
    }
    Ok(())
}

fn assign(
    classes: &mut BTreeMap<CanonicalInstructionId, CertifiedStructArrayIndexDispositionClass>,
    instruction: CanonicalInstructionId,
    class: CertifiedStructArrayIndexDispositionClass,
) -> Result<(), MachineBuildError> {
    match classes.insert(instruction, class) {
        None => Ok(()),
        Some(previous) if previous == class => Ok(()),
        Some(_) => Err(MachineBuildError::TopologyMismatch),
    }
}

fn canonical_instructions(
    artifact: &SsaArtifact,
    instructions: &[InstId],
) -> Result<Vec<CanonicalInstructionId>, MachineBuildError> {
    instructions
        .iter()
        .map(|instruction| canonical_instruction(artifact, *instruction))
        .collect()
}

fn canonical_instruction(
    artifact: &SsaArtifact,
    instruction: InstId,
) -> Result<CanonicalInstructionId, MachineBuildError> {
    artifact
        .obligations()
        .instruction_for_inst(instruction)
        .map(|source| source.id)
        .ok_or(MachineBuildError::ObligationMismatch(instruction))
}

fn obligation_error(
    source: &SemanticObligationInventory,
    obligation: SemanticObligationId,
) -> MachineBuildError {
    MachineBuildError::ObligationMismatch(
        source
            .obligations()
            .get(&obligation)
            .map(|source| source.source_inst)
            .unwrap_or(InstId(u32::MAX)),
    )
}

fn register_storage(storage: CanonicalStorageId, offset: u64, size: u32) -> bool {
    storage.space == CanonicalStorageSpace::Register
        && storage.offset == offset
        && storage.size == size
}

#[cfg(test)]
mod tests {
    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };
    use r2ssa::{
        SourceAbiParameterSpec, SourceAggregateLayout, SourceAggregateMember,
        SourceCarrierProjection, SourceFunctionInterface, SourceStackSlotSpec, SourceType,
        SourceTypeGraph, StackAddressBase,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(7);
    const ENTRY: u64 = 0x1000_00ab0;
    const RCX_OFFSET: u64 = 8;
    const CF_OFFSET: u64 = 512;
    const PF_OFFSET: u64 = 514;
    const ZF_OFFSET: u64 = 518;
    const SF_OFFSET: u64 = 519;
    const OF_OFFSET: u64 = 523;

    fn register(offset: u64, size: u32) -> Varnode {
        Varnode::register(offset, size)
    }

    fn constant(value: u64, size: u32) -> Varnode {
        Varnode::constant(value, size)
    }

    fn unique(next: &mut u64, size: u32) -> Varnode {
        let value = Varnode::unique(*next, size);
        *next += 0x80;
        value
    }

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-struct-array-cert-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("EAX", RAX_OFFSET, 4),
            ("RAX", RAX_OFFSET, 8),
            ("ECX", RCX_OFFSET, 4),
            ("RCX", RCX_OFFSET, 8),
            ("EDX", RDX_OFFSET, 4),
            ("RDX", RDX_OFFSET, 8),
            ("RSP", 32, 8),
            ("RBP", 40, 8),
            ("ESI", RSI_OFFSET, 4),
            ("RSI", RSI_OFFSET, 8),
            ("RDI", RDI_OFFSET, 8),
            ("CF", CF_OFFSET, 1),
            ("PF", PF_OFFSET, 1),
            ("ZF", ZF_OFFSET, 1),
            ("SF", SF_OFFSET, 1),
            ("OF", OF_OFFSET, 1),
            ("RIP", 648, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn type_graph(name_seed: &str) -> SourceTypeGraph {
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Struct { aggregate_id: 0 }, 448, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 1 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                1,
                448,
                32,
                format!("{name_seed}_aggregate"),
                (0..MEMBER_COUNT).map(|index| {
                    SourceAggregateMember::new(
                        index as u32,
                        0,
                        index as u64 * 32,
                        32,
                        format!("{name_seed}_member_{index}"),
                    )
                }),
            )],
        )
        .expect("natural struct-array graph")
    }

    fn interface(name_seed: &str, with_homes: bool) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let homes = with_homes
            .then(|| {
                [
                    SourceStackSlotSpec::new_parameter_home(
                        StackAddressBase::FramePointer,
                        storage(40),
                        -8,
                        8,
                        0,
                        storage(RDI_OFFSET),
                    ),
                    SourceStackSlotSpec::new_parameter_home(
                        StackAddressBase::FramePointer,
                        storage(40),
                        -12,
                        4,
                        1,
                        storage(RSI_OFFSET),
                    ),
                    SourceStackSlotSpec::new_parameter_home(
                        StackAddressBase::FramePointer,
                        storage(40),
                        -16,
                        4,
                        2,
                        storage(RDX_OFFSET),
                    ),
                ]
            })
            .map_or_else(Vec::new, |homes| homes.to_vec());
        SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-cert-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
                SourceAbiParameterSpec::new(2, storage(RDX_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX_OFFSET),
            },
            homes,
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(type_graph(name_seed)),
        )
        .expect("exact struct-array interface")
    }

    fn push_frame_prefix(block: &mut R2ILBlock, next: &mut u64) {
        let saved = unique(next, 8);
        block.push(R2ILOp::Copy {
            dst: saved.clone(),
            src: register(40, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: register(32, 8),
            a: register(32, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: register(32, 8),
            val: saved,
        });
        block.push(R2ILOp::Copy {
            dst: register(40, 8),
            src: register(32, 8),
        });
    }

    fn push_frame_suffix(block: &mut R2ILBlock, next: &mut u64) {
        let restored = unique(next, 8);
        block.push(R2ILOp::Copy {
            dst: restored.clone(),
            src: constant(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: restored.clone(),
            space: DATA,
            addr: register(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: register(32, 8),
            a: register(32, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Copy {
            dst: register(40, 8),
            src: restored,
        });
        block.push(R2ILOp::Load {
            dst: register(648, 8),
            space: DATA,
            addr: register(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: register(32, 8),
            a: register(32, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Return {
            target: register(648, 8),
        });
    }

    fn push_flag_packet_sized(block: &mut R2ILBlock, next: &mut u64, input: Varnode, size: u32) {
        block.push(R2ILOp::IntSLess {
            dst: register(SF_OFFSET, 1),
            a: input.clone(),
            b: constant(0, size),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(ZF_OFFSET, 1),
            a: input.clone(),
            b: constant(0, size),
        });
        let low = unique(next, size);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: input,
            b: constant(0xff, size),
        });
        let population = unique(next, 1);
        block.push(R2ILOp::PopCount {
            dst: population.clone(),
            src: low,
        });
        let parity = unique(next, 1);
        block.push(R2ILOp::IntAnd {
            dst: parity.clone(),
            a: population,
            b: constant(1, 1),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(PF_OFFSET, 1),
            a: parity,
            b: constant(0, 1),
        });
    }

    fn push_home(block: &mut R2ILBlock, next: &mut u64, offset: i64, source: Varnode) {
        let address = unique(next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(40, 8),
            b: constant(offset as u64, 8),
        });
        let copied = unique(next, source.size);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: source,
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: address,
            val: copied,
        });
    }

    fn reload_home(block: &mut R2ILBlock, next: &mut u64, offset: i64, size: u32) -> Varnode {
        let address = unique(next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(40, 8),
            b: constant(offset as u64, 8),
        });
        let loaded = unique(next, size);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: DATA,
            addr: address,
        });
        loaded
    }

    fn push_scale_packet(block: &mut R2ILBlock, next: &mut u64, input: Varnode, carrier: u64) {
        block.push(R2ILOp::IntSExt {
            dst: register(carrier, 8),
            src: input,
        });
        let wide_index = unique(next, 16);
        block.push(R2ILOp::IntSExt {
            dst: wide_index.clone(),
            src: register(carrier, 8),
        });
        let wide_stride = unique(next, 16);
        block.push(R2ILOp::IntSExt {
            dst: wide_stride.clone(),
            src: constant(STRIDE_BYTES, 8),
        });
        let wide_product = unique(next, 16);
        block.push(R2ILOp::IntMult {
            dst: wide_product.clone(),
            a: wide_index,
            b: wide_stride,
        });
        block.push(R2ILOp::IntMult {
            dst: register(carrier, 8),
            a: register(carrier, 8),
            b: constant(STRIDE_BYTES, 8),
        });
        block.push(R2ILOp::Subpiece {
            dst: unique(next, 8),
            src: wide_product.clone(),
            offset: 8,
        });
        let extended = unique(next, 16);
        block.push(R2ILOp::IntSExt {
            dst: extended.clone(),
            src: register(carrier, 8),
        });
        block.push(R2ILOp::IntNotEqual {
            dst: register(CF_OFFSET, 1),
            a: extended,
            b: wide_product,
        });
        block.push(R2ILOp::Copy {
            dst: register(OF_OFFSET, 1),
            src: register(CF_OFFSET, 1),
        });
    }

    fn push_address_sum(
        block: &mut R2ILBlock,
        next: &mut u64,
        base: Varnode,
        scaled: u64,
        destination: u64,
    ) {
        block.push(R2ILOp::IntCarry {
            dst: register(CF_OFFSET, 1),
            a: base.clone(),
            b: register(scaled, 8),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF_OFFSET, 1),
            a: base.clone(),
            b: register(scaled, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: register(destination, 8),
            a: base,
            b: register(scaled, 8),
        });
        push_flag_packet_sized(block, next, register(destination, 8), 8);
    }

    fn o2_block(entry: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 23);
        let mut next = 0x10000;
        push_frame_prefix(&mut block, &mut next);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 4),
            src: register(RDX_OFFSET, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: register(RDX_OFFSET, 4),
        });
        push_scale_packet(&mut block, &mut next, register(RSI_OFFSET, 4), RCX_OFFSET);
        let member_two_base = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_two_base.clone(),
            a: constant(8, 8),
            b: register(RDI_OFFSET, 8),
        });
        let member_two_scale = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: member_two_scale.clone(),
            a: register(RCX_OFFSET, 8),
            b: constant(1, 8),
        });
        let member_two_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_two_address.clone(),
            a: member_two_base,
            b: member_two_scale,
        });
        let stored = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: stored.clone(),
            src: register(RDX_OFFSET, 4),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: member_two_address,
            val: stored,
        });
        let member_thirteen_base = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_thirteen_base.clone(),
            a: constant(52, 8),
            b: register(RDI_OFFSET, 8),
        });
        let member_thirteen_scale = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: member_thirteen_scale.clone(),
            a: register(RCX_OFFSET, 8),
            b: constant(1, 8),
        });
        let member_thirteen_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_thirteen_address.clone(),
            a: member_thirteen_base,
            b: member_thirteen_scale,
        });
        let one = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: one.clone(),
            space: DATA,
            addr: member_thirteen_address.clone(),
        });
        block.push(R2ILOp::IntCarry {
            dst: register(CF_OFFSET, 1),
            a: register(RDX_OFFSET, 4),
            b: one,
        });
        let two = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: two.clone(),
            space: DATA,
            addr: member_thirteen_address.clone(),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF_OFFSET, 1),
            a: register(RDX_OFFSET, 4),
            b: two,
        });
        let three = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: three.clone(),
            space: DATA,
            addr: member_thirteen_address,
        });
        block.push(R2ILOp::IntAdd {
            dst: register(RAX_OFFSET, 4),
            a: register(RDX_OFFSET, 4),
            b: three,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: register(RAX_OFFSET, 4),
        });
        push_flag_packet_sized(&mut block, &mut next, register(RAX_OFFSET, 4), 4);
        push_frame_suffix(&mut block, &mut next);
        assert_eq!(block.ops.len(), 43);
        block
    }

    fn o0_block(entry: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 73);
        let mut next = 0x40000;
        push_frame_prefix(&mut block, &mut next);
        push_home(&mut block, &mut next, -8, register(RDI_OFFSET, 8));
        push_home(&mut block, &mut next, -12, register(RSI_OFFSET, 4));
        push_home(&mut block, &mut next, -16, register(RDX_OFFSET, 4));

        let value = reload_home(&mut block, &mut next, -16, 4);
        block.push(R2ILOp::Copy {
            dst: register(RCX_OFFSET, 4),
            src: value.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RCX_OFFSET, 8),
            src: value.clone(),
        });
        let arr = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 8),
            src: arr,
        });
        let index = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, index, RDX_OFFSET);
        push_address_sum(
            &mut block,
            &mut next,
            register(RAX_OFFSET, 8),
            RDX_OFFSET,
            RAX_OFFSET,
        );
        let address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(RAX_OFFSET, 8),
            b: constant(8, 8),
        });
        let stored = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: stored.clone(),
            src: value,
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: address,
            val: stored,
        });

        let arr = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 8),
            src: arr,
        });
        let index = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, index, RCX_OFFSET);
        push_address_sum(
            &mut block,
            &mut next,
            register(RAX_OFFSET, 8),
            RCX_OFFSET,
            RAX_OFFSET,
        );
        let address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(RAX_OFFSET, 8),
            b: constant(8, 8),
        });
        let member_two = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: member_two.clone(),
            space: DATA,
            addr: address,
        });
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 4),
            src: member_two.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: member_two.clone(),
        });

        let arr = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RCX_OFFSET, 8),
            src: arr,
        });
        let index = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, index, RDX_OFFSET);
        push_address_sum(
            &mut block,
            &mut next,
            register(RCX_OFFSET, 8),
            RDX_OFFSET,
            RCX_OFFSET,
        );
        let address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(RCX_OFFSET, 8),
            b: constant(52, 8),
        });
        let one = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: one.clone(),
            space: DATA,
            addr: address.clone(),
        });
        block.push(R2ILOp::IntCarry {
            dst: register(CF_OFFSET, 1),
            a: member_two.clone(),
            b: one,
        });
        let two = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: two.clone(),
            space: DATA,
            addr: address.clone(),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF_OFFSET, 1),
            a: member_two.clone(),
            b: two,
        });
        let three = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: three.clone(),
            space: DATA,
            addr: address,
        });
        block.push(R2ILOp::IntAdd {
            dst: register(RAX_OFFSET, 4),
            a: member_two,
            b: three,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: register(RAX_OFFSET, 4),
        });
        push_flag_packet_sized(&mut block, &mut next, register(RAX_OFFSET, 4), 4);
        push_frame_suffix(&mut block, &mut next);
        assert_eq!(block.ops.len(), 114);
        block
    }

    fn artifact(entry: u64, o0: bool, name_seed: &str) -> SsaArtifact {
        let block = if o0 { o0_block(entry) } else { o2_block(entry) };
        SsaArtifact::raw_with_interface(&[block], Some(&arch()), interface(name_seed, o0))
            .expect("struct-array artifact")
    }

    fn certificate(artifact: &SsaArtifact) -> CertifiedStructArrayIndexFunction {
        certify_struct_array_index_function(artifact)
            .expect("certification construction")
            .expect("exact struct-array certificate")
    }

    #[test]
    fn exact_o2_and_o0_certificates_close_the_whole_source() {
        for o0 in [false, true] {
            let artifact = artifact(ENTRY, o0, if o0 { "o0" } else { "o2" });
            let certificate = certificate(&artifact);
            assert!(certificate.validate(artifact.obligations()));
            assert_eq!(certificate.accesses().len(), if o0 { 5 } else { 4 });
            assert_eq!(certificate.homes().len(), if o0 { 3 } else { 0 });
            assert_eq!(certificate.scales().len(), if o0 { 3 } else { 1 });
            assert_eq!(
                certificate.obligation_dispositions().len(),
                artifact.obligations().obligations().len()
            );
        }
    }

    #[test]
    fn access_disposition_mutations_fail_closed() {
        let artifact = artifact(ENTRY, false, "access-mutations");
        let certificate = certificate(&artifact);
        let access_obligation = certificate.accesses[1].memory_obligation;
        let position = certificate
            .obligation_dispositions
            .iter()
            .position(|(obligation, _)| *obligation == access_obligation)
            .expect("access disposition");

        let mut missing = certificate.clone();
        let mut dispositions = missing.obligation_dispositions.to_vec();
        dispositions.remove(position);
        missing.obligation_dispositions = dispositions.into_boxed_slice();
        assert!(!missing.validate(artifact.obligations()));

        let mut duplicate = certificate.clone();
        let mut dispositions = duplicate.obligation_dispositions.to_vec();
        dispositions[position + 1] = dispositions[position];
        duplicate.obligation_dispositions = dispositions.into_boxed_slice();
        assert!(!duplicate.validate(artifact.obligations()));

        let mut reordered = certificate.clone();
        let mut accesses = reordered.accesses.to_vec();
        accesses.swap(1, 2);
        reordered.accesses = accesses.into_boxed_slice();
        assert!(!reordered.validate(artifact.obligations()));
    }

    #[test]
    fn layout_member_stride_and_foreign_origin_mutations_fail_closed() {
        let source = artifact(ENTRY, false, "layout-mutations");
        let valid = certificate(&source);

        let mut wrong_member = valid.clone();
        wrong_member.accesses[0].member_id = 3;
        assert!(!wrong_member.validate(source.obligations()));

        let mut wrong_layout = valid.clone();
        wrong_layout.layout.member_offsets_bytes[13] = 48;
        assert!(!wrong_layout.validate(source.obligations()));

        let mut wrong_stride = valid.clone();
        wrong_stride.layout.stride_bytes = 48;
        assert!(!wrong_stride.validate(source.obligations()));

        let relocated = artifact(ENTRY + 0x5000, false, "relocated");
        let mut foreign_origin = valid.clone();
        foreign_origin.origin = certificate(&relocated).origin;
        assert!(!foreign_origin.validate(source.obligations()));
    }

    #[test]
    fn dropped_home_scale_return_and_inventory_mutations_fail_closed() {
        let artifact = artifact(ENTRY, true, "private-mutations");
        let certificate = certificate(&artifact);

        let mut dropped_home = certificate.clone();
        dropped_home.homes = dropped_home.homes[1..].to_vec().into_boxed_slice();
        assert!(!dropped_home.validate(artifact.obligations()));

        let mut dropped_scale = certificate.clone();
        dropped_scale.scales = dropped_scale.scales[1..].to_vec().into_boxed_slice();
        assert!(!dropped_scale.validate(artifact.obligations()));

        let mut wrong_return = certificate.clone();
        wrong_return.returned.wraps_at_bits = 64;
        assert!(!wrong_return.validate(artifact.obligations()));

        let mut wrong_direct_value = certificate.clone();
        wrong_direct_value.returned.full_value = wrong_direct_value.returned.returned_value;
        assert!(!wrong_direct_value.validate(artifact.obligations()));

        let mut dropped_inventory = certificate.clone();
        dropped_inventory.instruction_inventory = dropped_inventory.instruction_inventory[1..]
            .to_vec()
            .into_boxed_slice();
        assert!(!dropped_inventory.validate(artifact.obligations()));
    }
}
