//! Closed certification for the exact x86-64 `sum_array` lowerings.
//!
//! O0 and O2 retain distinct typed bindings.  Both certificates close the
//! complete canonical instruction and semantic-obligation inventories and are
//! meaningful only with the immutable artifact origin that issued them.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CanonicalInstructionId, CanonicalInstructionSite, CanonicalStorageId, CanonicalStorageSpace,
    InstId, MachineAddressSpace, MachineBuildError, SEMANTIC_OBLIGATION_SCHEMA_VERSION,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION,
    SUM_ARRAY_FACT_SCHEMA_VERSION, SemanticInstructionState, SemanticObligationComponent,
    SemanticObligationId, SemanticObligationInventory, SemanticObligationKind, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceStackSlotRole, SourceTypeKind, SsaArtifact,
    SumArrayFact, SumArrayHomeRole, SumArrayInstructionClass, SumArrayLowering, SumArrayO2Fact,
    SumArrayO2ReturnPath, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedMachineContext,
    certified_artifact_origin, certified_source_topology,
};

pub const CERTIFIED_SUM_ARRAY_CONTRACT_VERSION: u32 = 1;

const RAX_OFFSET: u64 = 0;
const RBP_OFFSET: u64 = 40;
const RSI_OFFSET: u64 = 48;
const RDI_OFFSET: u64 = 56;
const O0_INSTRUCTION_COUNT: usize = 111;
const O2_INSTRUCTION_COUNT: usize = 672;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedSumArrayLowering {
    O0ScalarHomes,
    O2Vectorized,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedSumArrayDispositionClass {
    Semantic,
    Frame,
    Structural,
    ProvenDead,
}

impl From<SumArrayInstructionClass> for CertifiedSumArrayDispositionClass {
    fn from(class: SumArrayInstructionClass) -> Self {
        match class {
            SumArrayInstructionClass::Semantic => Self::Semantic,
            SumArrayInstructionClass::Frame => Self::Frame,
            SumArrayInstructionClass::Structural => Self::Structural,
            SumArrayInstructionClass::ProvenDead => Self::ProvenDead,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayType {
    signed_integer_type_id: u32,
    pointer_type_id: u32,
    element_size_bytes: u32,
}

impl CertifiedSumArrayType {
    pub const fn signed_integer_type_id(&self) -> u32 {
        self.signed_integer_type_id
    }

    pub const fn pointer_type_id(&self) -> u32 {
        self.pointer_type_id
    }

    pub const fn element_size_bytes(&self) -> u32 {
        self.element_size_bytes
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayParameter {
    index: u32,
    abi_storage: CanonicalStorageId,
    graph_storage: CanonicalStorageId,
    graph_value: ValueId,
    logical_value: SourceLogicalValue,
}

impl CertifiedSumArrayParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn graph_value(&self) -> ValueId {
        self.graph_value
    }

    pub const fn abi_storage(&self) -> CanonicalStorageId {
        self.abi_storage
    }

    pub const fn graph_storage(&self) -> CanonicalStorageId {
        self.graph_storage
    }

    pub const fn logical_value(&self) -> SourceLogicalValue {
        self.logical_value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayAbi {
    revision_identity: Box<[u8]>,
    parameters: Box<[CertifiedSumArrayParameter]>,
    return_logical_value: SourceLogicalValue,
    return_storage: CanonicalStorageId,
}

impl CertifiedSumArrayAbi {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameters(&self) -> &[CertifiedSumArrayParameter] {
        &self.parameters
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayFrame {
    memory_space: MachineAddressSpace,
    stack_storage: Option<CanonicalStorageId>,
    frame_pointer_storage: Option<CanonicalStorageId>,
    instruction_pointer_storage: Option<CanonicalStorageId>,
    entry_stack: ValueId,
    allocated_stack: ValueId,
    saved_frame_pointer: ValueId,
    restored_frame_pointer: Option<ValueId>,
    return_target: Option<ValueId>,
    prologue: Box<[CanonicalInstructionId]>,
    main_epilogue: Box<[CanonicalInstructionId]>,
    alternate_epilogue: Box<[CanonicalInstructionId]>,
}

impl CertifiedSumArrayFrame {
    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }

    pub const fn entry_stack(&self) -> ValueId {
        self.entry_stack
    }

    pub const fn allocated_stack(&self) -> ValueId {
        self.allocated_stack
    }

    pub const fn saved_frame_pointer(&self) -> ValueId {
        self.saved_frame_pointer
    }

    pub const fn stack_storage(&self) -> Option<CanonicalStorageId> {
        self.stack_storage
    }

    pub const fn frame_pointer_storage(&self) -> Option<CanonicalStorageId> {
        self.frame_pointer_storage
    }

    pub const fn instruction_pointer_storage(&self) -> Option<CanonicalStorageId> {
        self.instruction_pointer_storage
    }

    pub const fn restored_frame_pointer(&self) -> Option<ValueId> {
        self.restored_frame_pointer
    }

    pub const fn return_target(&self) -> Option<ValueId> {
        self.return_target
    }

    pub const fn prologue(&self) -> &[CanonicalInstructionId] {
        &self.prologue
    }

    pub const fn main_epilogue(&self) -> &[CanonicalInstructionId] {
        &self.main_epilogue
    }

    pub const fn alternate_epilogue(&self) -> &[CanonicalInstructionId] {
        &self.alternate_epilogue
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedSumArrayHomeRole {
    ArrayParameter,
    LengthParameter,
    SumLocal,
    IndexLocal,
}

impl From<SumArrayHomeRole> for CertifiedSumArrayHomeRole {
    fn from(role: SumArrayHomeRole) -> Self {
        match role {
            SumArrayHomeRole::ArrayParameter => Self::ArrayParameter,
            SumArrayHomeRole::LengthParameter => Self::LengthParameter,
            SumArrayHomeRole::SumLocal => Self::SumLocal,
            SumArrayHomeRole::IndexLocal => Self::IndexLocal,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayReload {
    address_add: CanonicalInstructionId,
    load: CanonicalInstructionId,
    value: ValueId,
}

impl CertifiedSumArrayReload {
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
pub struct CertifiedSumArrayHome {
    role: CertifiedSumArrayHomeRole,
    frame_pointer_offset: i64,
    entry_stack_offset: i64,
    size_bytes: u32,
    initializer_address_add: CanonicalInstructionId,
    initializer_copy: CanonicalInstructionId,
    initializer_store: CanonicalInstructionId,
    initial_value: ValueId,
    reloads: Box<[CertifiedSumArrayReload]>,
}

impl CertifiedSumArrayHome {
    pub const fn role(&self) -> CertifiedSumArrayHomeRole {
        self.role
    }

    pub const fn reloads(&self) -> &[CertifiedSumArrayReload] {
        &self.reloads
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

    pub const fn initial_value(&self) -> ValueId {
        self.initial_value
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayRead {
    order: u32,
    memory_space: MachineAddressSpace,
    address: ValueId,
    load: CanonicalInstructionId,
    value: ValueId,
    size_bytes: u32,
}

impl CertifiedSumArrayRead {
    pub const fn order(&self) -> u32 {
        self.order
    }

    pub const fn load(&self) -> CanonicalInstructionId {
        self.load
    }

    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }

    pub const fn address(&self) -> ValueId {
        self.address
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayReturn {
    path: Option<CertifiedSumArrayO2ReturnPath>,
    block: u64,
    returned_low32: ValueId,
    sum_load: Option<CanonicalInstructionId>,
    zero_extend: Option<CanonicalInstructionId>,
    physical_full_register: ValueId,
    definition: CanonicalInstructionId,
    return_target: ValueId,
    return_instruction: CanonicalInstructionId,
    return_storage: CanonicalStorageId,
}

impl CertifiedSumArrayReturn {
    pub const fn returned_low32(&self) -> ValueId {
        self.returned_low32
    }

    pub const fn physical_full_register(&self) -> ValueId {
        self.physical_full_register
    }

    pub const fn return_instruction(&self) -> CanonicalInstructionId {
        self.return_instruction
    }

    pub const fn path(&self) -> Option<CertifiedSumArrayO2ReturnPath> {
        self.path
    }

    pub const fn block(&self) -> u64 {
        self.block
    }

    pub const fn sum_load(&self) -> Option<CanonicalInstructionId> {
        self.sum_load
    }

    pub const fn zero_extend(&self) -> Option<CanonicalInstructionId> {
        self.zero_extend
    }

    pub const fn definition(&self) -> CanonicalInstructionId {
        self.definition
    }

    pub const fn return_target(&self) -> ValueId {
        self.return_target
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedSumArrayO2ReturnPath {
    VectorOrScalar,
    NonPositiveLength,
}

impl From<SumArrayO2ReturnPath> for CertifiedSumArrayO2ReturnPath {
    fn from(path: SumArrayO2ReturnPath) -> Self {
        match path {
            SumArrayO2ReturnPath::VectorOrScalar => Self::VectorOrScalar,
            SumArrayO2ReturnPath::NonPositiveLength => Self::NonPositiveLength,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO0Predicate {
    blocks: [u64; 3],
    index: ValueId,
    length: ValueId,
    subtract: CanonicalInstructionId,
    signed_overflow: CanonicalInstructionId,
    sign: CanonicalInstructionId,
    greater_or_equal: ValueId,
    branch: CanonicalInstructionId,
    signed_width_bits: u32,
}

impl CertifiedSumArrayO0Predicate {
    pub const fn blocks(&self) -> [u64; 3] {
        self.blocks
    }

    pub const fn index(&self) -> ValueId {
        self.index
    }

    pub const fn length(&self) -> ValueId {
        self.length
    }

    pub const fn subtract(&self) -> CanonicalInstructionId {
        self.subtract
    }

    pub const fn signed_overflow(&self) -> CanonicalInstructionId {
        self.signed_overflow
    }

    pub const fn sign(&self) -> CanonicalInstructionId {
        self.sign
    }

    pub const fn greater_or_equal(&self) -> ValueId {
        self.greater_or_equal
    }

    pub const fn branch(&self) -> CanonicalInstructionId {
        self.branch
    }

    pub const fn signed_width_bits(&self) -> u32 {
        self.signed_width_bits
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO0Loop {
    array_base: ValueId,
    index: ValueId,
    sign_extend_index: CanonicalInstructionId,
    extended_index: ValueId,
    scale: CanonicalInstructionId,
    scaled_index: ValueId,
    address_add: CanonicalInstructionId,
    element_address: ValueId,
    reads: Box<[CertifiedSumArrayRead]>,
    prior_sum_reads: Box<[CertifiedSumArrayRead]>,
    add: CanonicalInstructionId,
    next_sum: ValueId,
    sum_store: CanonicalInstructionId,
    increment: CanonicalInstructionId,
    next_index: ValueId,
    index_store: CanonicalInstructionId,
    back_edge: CanonicalInstructionId,
    wraps_at_bits: u32,
}

impl CertifiedSumArrayO0Loop {
    pub const fn reads(&self) -> &[CertifiedSumArrayRead] {
        &self.reads
    }

    pub const fn prior_sum_reads(&self) -> &[CertifiedSumArrayRead] {
        &self.prior_sum_reads
    }

    pub const fn array_base(&self) -> ValueId {
        self.array_base
    }

    pub const fn index(&self) -> ValueId {
        self.index
    }

    pub const fn sign_extend_index(&self) -> CanonicalInstructionId {
        self.sign_extend_index
    }

    pub const fn extended_index(&self) -> ValueId {
        self.extended_index
    }

    pub const fn scale(&self) -> CanonicalInstructionId {
        self.scale
    }

    pub const fn scaled_index(&self) -> ValueId {
        self.scaled_index
    }

    pub const fn address_add(&self) -> CanonicalInstructionId {
        self.address_add
    }

    pub const fn element_address(&self) -> ValueId {
        self.element_address
    }

    pub const fn add(&self) -> CanonicalInstructionId {
        self.add
    }

    pub const fn next_sum(&self) -> ValueId {
        self.next_sum
    }

    pub const fn sum_store(&self) -> CanonicalInstructionId {
        self.sum_store
    }

    pub const fn increment(&self) -> CanonicalInstructionId {
        self.increment
    }

    pub const fn next_index(&self) -> ValueId {
        self.next_index
    }

    pub const fn index_store(&self) -> CanonicalInstructionId {
        self.index_store
    }

    pub const fn back_edge(&self) -> CanonicalInstructionId {
        self.back_edge
    }

    pub const fn wraps_at_bits(&self) -> u32 {
        self.wraps_at_bits
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO0Binding {
    frame: CertifiedSumArrayFrame,
    homes: Box<[CertifiedSumArrayHome]>,
    predicate: CertifiedSumArrayO0Predicate,
    scalar_loop: CertifiedSumArrayO0Loop,
    returned: CertifiedSumArrayReturn,
}

impl CertifiedSumArrayO0Binding {
    pub const fn frame(&self) -> &CertifiedSumArrayFrame {
        &self.frame
    }

    pub const fn homes(&self) -> &[CertifiedSumArrayHome] {
        &self.homes
    }

    pub const fn scalar_loop(&self) -> &CertifiedSumArrayO0Loop {
        &self.scalar_loop
    }

    pub const fn predicate(&self) -> &CertifiedSumArrayO0Predicate {
        &self.predicate
    }

    pub const fn returned(&self) -> &CertifiedSumArrayReturn {
        &self.returned
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2Guard {
    block: u64,
    input: ValueId,
    condition: ValueId,
    branch: CanonicalInstructionId,
    signed_width_bits: u32,
}

impl CertifiedSumArrayO2Guard {
    pub const fn block(&self) -> u64 {
        self.block
    }

    pub const fn input(&self) -> ValueId {
        self.input
    }

    pub const fn condition(&self) -> ValueId {
        self.condition
    }

    pub const fn branch(&self) -> CanonicalInstructionId {
        self.branch
    }

    pub const fn signed_width_bits(&self) -> u32 {
        self.signed_width_bits
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2VectorRead {
    order: u32,
    memory_space: MachineAddressSpace,
    address: ValueId,
    load: CanonicalInstructionId,
    value: ValueId,
    size_bytes: u32,
    lane_projections: Box<[CanonicalInstructionId]>,
    lane_values: Box<[ValueId]>,
}

impl CertifiedSumArrayO2VectorRead {
    pub const fn order(&self) -> u32 {
        self.order
    }

    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }

    pub const fn address(&self) -> ValueId {
        self.address
    }

    pub const fn load(&self) -> CanonicalInstructionId {
        self.load
    }

    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub const fn lane_projections(&self) -> &[CanonicalInstructionId] {
        &self.lane_projections
    }

    pub const fn lane_values(&self) -> &[ValueId] {
        &self.lane_values
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2Lane {
    lane: u32,
    accumulator_storage: CanonicalStorageId,
    initial_projection: CanonicalInstructionId,
    initial_value: ValueId,
    phi: CanonicalInstructionId,
    phi_value: ValueId,
    load_projection: CanonicalInstructionId,
    loaded_value: ValueId,
    add: CanonicalInstructionId,
    next_value: ValueId,
    wraps_at_bits: u32,
}

impl CertifiedSumArrayO2Lane {
    pub const fn lane(&self) -> u32 {
        self.lane
    }

    pub const fn phi(&self) -> CanonicalInstructionId {
        self.phi
    }

    pub const fn next_value(&self) -> ValueId {
        self.next_value
    }

    pub const fn accumulator_storage(&self) -> CanonicalStorageId {
        self.accumulator_storage
    }

    pub const fn initial_projection(&self) -> CanonicalInstructionId {
        self.initial_projection
    }

    pub const fn initial_value(&self) -> ValueId {
        self.initial_value
    }

    pub const fn phi_value(&self) -> ValueId {
        self.phi_value
    }

    pub const fn load_projection(&self) -> CanonicalInstructionId {
        self.load_projection
    }

    pub const fn loaded_value(&self) -> ValueId {
        self.loaded_value
    }

    pub const fn add(&self) -> CanonicalInstructionId {
        self.add
    }

    pub const fn wraps_at_bits(&self) -> u32 {
        self.wraps_at_bits
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2VectorLoop {
    blocks: [u64; 2],
    byte_offset_phi: CanonicalInstructionId,
    byte_offset: ValueId,
    bound: ValueId,
    reads: Box<[CertifiedSumArrayO2VectorRead]>,
    lanes: Box<[CertifiedSumArrayO2Lane]>,
    induction_add: CanonicalInstructionId,
    next_byte_offset: ValueId,
    step_bytes: u32,
    back_edge: CanonicalInstructionId,
}

impl CertifiedSumArrayO2VectorLoop {
    pub const fn blocks(&self) -> [u64; 2] {
        self.blocks
    }

    pub const fn byte_offset_phi(&self) -> CanonicalInstructionId {
        self.byte_offset_phi
    }

    pub const fn byte_offset(&self) -> ValueId {
        self.byte_offset
    }

    pub const fn bound(&self) -> ValueId {
        self.bound
    }

    pub const fn reads(&self) -> &[CertifiedSumArrayO2VectorRead] {
        &self.reads
    }

    pub const fn lanes(&self) -> &[CertifiedSumArrayO2Lane] {
        &self.lanes
    }

    pub const fn induction_add(&self) -> CanonicalInstructionId {
        self.induction_add
    }

    pub const fn next_byte_offset(&self) -> ValueId {
        self.next_byte_offset
    }

    pub const fn step_bytes(&self) -> u32 {
        self.step_bytes
    }

    pub const fn back_edge(&self) -> CanonicalInstructionId {
        self.back_edge
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2Reduction {
    block: u64,
    input_lanes: Box<[ValueId]>,
    pairwise_adds: Box<[CanonicalInstructionId]>,
    pairwise_values: Box<[ValueId]>,
    selector_packets: Box<[Box<[CanonicalInstructionId]>]>,
    final_add: CanonicalInstructionId,
    returned_low32: ValueId,
    zero_extend: CanonicalInstructionId,
    physical_full_register: ValueId,
    wraps_at_bits: u32,
}

impl CertifiedSumArrayO2Reduction {
    pub const fn block(&self) -> u64 {
        self.block
    }

    pub const fn input_lanes(&self) -> &[ValueId] {
        &self.input_lanes
    }

    pub const fn selector_packets(&self) -> &[Box<[CanonicalInstructionId]>] {
        &self.selector_packets
    }

    pub const fn pairwise_adds(&self) -> &[CanonicalInstructionId] {
        &self.pairwise_adds
    }

    pub const fn pairwise_values(&self) -> &[ValueId] {
        &self.pairwise_values
    }

    pub const fn final_add(&self) -> CanonicalInstructionId {
        self.final_add
    }

    pub const fn returned_low32(&self) -> ValueId {
        self.returned_low32
    }

    pub const fn zero_extend(&self) -> CanonicalInstructionId {
        self.zero_extend
    }

    pub const fn physical_full_register(&self) -> ValueId {
        self.physical_full_register
    }

    pub const fn wraps_at_bits(&self) -> u32 {
        self.wraps_at_bits
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2ScalarTail {
    header_block: u64,
    accumulator_phi: CanonicalInstructionId,
    accumulator: ValueId,
    index_phi: CanonicalInstructionId,
    index: ValueId,
    length_phi: CanonicalInstructionId,
    length: ValueId,
    scale: CanonicalInstructionId,
    element_address: ValueId,
    reads: Box<[CertifiedSumArrayRead]>,
    add: CanonicalInstructionId,
    next_accumulator: ValueId,
    increment: CanonicalInstructionId,
    next_index: ValueId,
    back_edge: CanonicalInstructionId,
    wraps_at_bits: u32,
}

impl CertifiedSumArrayO2ScalarTail {
    pub const fn header_block(&self) -> u64 {
        self.header_block
    }

    pub const fn accumulator_phi(&self) -> CanonicalInstructionId {
        self.accumulator_phi
    }

    pub const fn accumulator(&self) -> ValueId {
        self.accumulator
    }

    pub const fn index_phi(&self) -> CanonicalInstructionId {
        self.index_phi
    }

    pub const fn index(&self) -> ValueId {
        self.index
    }

    pub const fn length_phi(&self) -> CanonicalInstructionId {
        self.length_phi
    }

    pub const fn length(&self) -> ValueId {
        self.length
    }

    pub const fn scale(&self) -> CanonicalInstructionId {
        self.scale
    }

    pub const fn element_address(&self) -> ValueId {
        self.element_address
    }

    pub const fn reads(&self) -> &[CertifiedSumArrayRead] {
        &self.reads
    }

    pub const fn add(&self) -> CanonicalInstructionId {
        self.add
    }

    pub const fn next_accumulator(&self) -> ValueId {
        self.next_accumulator
    }

    pub const fn increment(&self) -> CanonicalInstructionId {
        self.increment
    }

    pub const fn next_index(&self) -> ValueId {
        self.next_index
    }

    pub const fn back_edge(&self) -> CanonicalInstructionId {
        self.back_edge
    }

    pub const fn wraps_at_bits(&self) -> u32 {
        self.wraps_at_bits
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2Topology {
    blocks: Box<[u64]>,
    block_sizes: Box<[u32]>,
    operation_counts: Box<[u32]>,
    phi_counts: Box<[u32]>,
}

impl CertifiedSumArrayO2Topology {
    pub const fn blocks(&self) -> &[u64] {
        &self.blocks
    }

    pub const fn block_sizes(&self) -> &[u32] {
        &self.block_sizes
    }

    pub const fn operation_counts(&self) -> &[u32] {
        &self.operation_counts
    }

    pub const fn phi_counts(&self) -> &[u32] {
        &self.phi_counts
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayO2Binding {
    topology: CertifiedSumArrayO2Topology,
    frame: CertifiedSumArrayFrame,
    guards: Box<[CertifiedSumArrayO2Guard]>,
    vector_loop: CertifiedSumArrayO2VectorLoop,
    reduction: CertifiedSumArrayO2Reduction,
    scalar_tail: CertifiedSumArrayO2ScalarTail,
    returns: Box<[CertifiedSumArrayReturn]>,
}

impl CertifiedSumArrayO2Binding {
    pub const fn topology(&self) -> &CertifiedSumArrayO2Topology {
        &self.topology
    }

    pub const fn frame(&self) -> &CertifiedSumArrayFrame {
        &self.frame
    }

    pub const fn guards(&self) -> &[CertifiedSumArrayO2Guard] {
        &self.guards
    }

    pub const fn vector_loop(&self) -> &CertifiedSumArrayO2VectorLoop {
        &self.vector_loop
    }

    pub const fn reduction(&self) -> &CertifiedSumArrayO2Reduction {
        &self.reduction
    }

    pub const fn scalar_tail(&self) -> &CertifiedSumArrayO2ScalarTail {
        &self.scalar_tail
    }

    pub const fn returns(&self) -> &[CertifiedSumArrayReturn] {
        &self.returns
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedSumArrayBinding {
    O0(CertifiedSumArrayO0Binding),
    O2(CertifiedSumArrayO2Binding),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayInstructionDisposition {
    instruction: CanonicalInstructionId,
    block_index: u32,
    ordinal: u32,
    class: CertifiedSumArrayDispositionClass,
}

impl CertifiedSumArrayInstructionDisposition {
    pub const fn instruction(&self) -> CanonicalInstructionId {
        self.instruction
    }

    pub const fn block_index(&self) -> u32 {
        self.block_index
    }

    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }

    pub const fn class(&self) -> CertifiedSumArrayDispositionClass {
        self.class
    }
}

/// Opaque whole-source certificate with exact instruction and obligation
/// closure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArrayFunction {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    entry: u64,
    lowering: CertifiedSumArrayLowering,
    types: CertifiedSumArrayType,
    abi: CertifiedSumArrayAbi,
    binding: CertifiedSumArrayBinding,
    instruction_inventory: Box<[CertifiedSumArrayInstructionDisposition]>,
    obligation_dispositions: Box<[(SemanticObligationId, CertifiedSumArrayDispositionClass)]>,
    #[serde(skip)]
    contract_snapshot: Box<[u8]>,
}

impl CertifiedSumArrayFunction {
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

    pub const fn lowering(&self) -> CertifiedSumArrayLowering {
        self.lowering
    }

    pub const fn types(&self) -> CertifiedSumArrayType {
        self.types
    }

    pub const fn abi(&self) -> &CertifiedSumArrayAbi {
        &self.abi
    }

    pub const fn binding(&self) -> &CertifiedSumArrayBinding {
        &self.binding
    }

    pub const fn instruction_inventory(&self) -> &[CertifiedSumArrayInstructionDisposition] {
        &self.instruction_inventory
    }

    pub const fn obligation_dispositions(
        &self,
    ) -> &[(SemanticObligationId, CertifiedSumArrayDispositionClass)] {
        &self.obligation_dispositions
    }

    pub fn instruction_disposition(
        &self,
        instruction: CanonicalInstructionId,
    ) -> Option<&CertifiedSumArrayInstructionDisposition> {
        self.instruction_inventory
            .iter()
            .find(|item| item.instruction == instruction)
    }

    pub fn obligation_disposition(
        &self,
        obligation: SemanticObligationId,
    ) -> Option<CertifiedSumArrayDispositionClass> {
        self.obligation_dispositions
            .binary_search_by_key(&obligation, |(id, _)| *id)
            .ok()
            .map(|index| self.obligation_dispositions[index].1)
    }

    pub fn validate(&self, source: &SemanticObligationInventory) -> bool {
        self.validate_contract(source).is_ok()
    }

    fn validate_contract(&self, source: &SemanticObligationInventory) -> Result<(), ()> {
        if self.schema_version != CERTIFICATION_SCHEMA_VERSION
            || self.contract_version != CERTIFIED_SUM_ARRAY_CONTRACT_VERSION
            || source.schema_version() != SEMANTIC_OBLIGATION_SCHEMA_VERSION
            || !source.is_complete()
            || self.origin.source() != source
            || !self
                .origin
                .matches_retained_source(source, self.origin.topology())
            || self.origin.topology().entry_addr() != self.entry
            || self.abi.revision_identity.is_empty()
            || self.contract_snapshot.is_empty()
            || !sum_array_contract_snapshot(self)
                .is_ok_and(|snapshot| snapshot.as_slice() == &*self.contract_snapshot)
        {
            return Err(());
        }
        validate_common(self)?;
        validate_binding(self, source)?;
        validate_instruction_closure(self, source)?;
        validate_obligation_closure(self, source)
    }
}

/// Construct a closed certificate only when the artifact retains exactly one
/// admitted O0 or O2 `sum_array` fact.  Refusal facts never become
/// certificates.
pub fn certify_sum_array_function(
    artifact: &SsaArtifact,
) -> Result<Option<CertifiedSumArrayFunction>, MachineBuildError> {
    let o0 = &artifact.structured().sum_arrays;
    let o2 = &artifact.structured().sum_array_o2;
    if o0.is_empty() && o2.is_empty() {
        return Ok(None);
    }
    if o0.len() + o2.len() != 1 {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let certificate = if let Some(fact) = o0.values().next() {
        certify_o0(artifact, fact)?
    } else {
        certify_o2(
            artifact,
            o2.values()
                .next()
                .ok_or(MachineBuildError::TopologyMismatch)?,
        )?
    };
    Ok(Some(certificate))
}

fn certify_o0(
    artifact: &SsaArtifact,
    fact: &SumArrayFact,
) -> Result<CertifiedSumArrayFunction, MachineBuildError> {
    if fact.schema_version != SUM_ARRAY_FACT_SCHEMA_VERSION
        || fact.lowering != SumArrayLowering::O0ScalarHomes
        || !fact.validate_against(artifact)
        || fact.instruction_inventory.len() != O0_INSTRUCTION_COUNT
        || fact.returned.composition.is_some()
        || fact.returned.definition.storage != fact.abi.return_storage
        || fact.returned.definition.value != fact.returned.physical_full_register
        || fact.returned.definition.producer != fact.returned.zero_extend
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    validate_source_common(artifact, &fact.abi)?;
    if fact.frame.instructions.len() != 11 {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let (origin, types, abi, instruction_inventory) = certified_common(
        artifact,
        &fact.types,
        &fact.abi,
        &fact.instruction_inventory,
    )?;
    let frame = CertifiedSumArrayFrame {
        memory_space: fact.frame.memory_space.into(),
        stack_storage: Some(fact.frame.stack_storage),
        frame_pointer_storage: Some(fact.frame.frame_pointer_storage),
        instruction_pointer_storage: Some(fact.frame.instruction_pointer_storage),
        entry_stack: fact.frame.entry_stack,
        allocated_stack: fact.frame.allocated_stack,
        saved_frame_pointer: fact.frame.saved_frame_pointer,
        restored_frame_pointer: Some(fact.frame.restored_frame_pointer),
        return_target: Some(fact.frame.return_target),
        prologue: canonical_instructions(artifact, &fact.frame.instructions[..4])?
            .into_boxed_slice(),
        main_epilogue: canonical_instructions(artifact, &fact.frame.instructions[4..])?
            .into_boxed_slice(),
        alternate_epilogue: Box::new([]),
    };
    let homes = fact
        .homes
        .iter()
        .map(|home| {
            Ok(CertifiedSumArrayHome {
                role: home.role.into(),
                frame_pointer_offset: home.frame_pointer_offset,
                entry_stack_offset: home.entry_stack_offset,
                size_bytes: home.size_bytes,
                initializer_address_add: canonical_instruction(
                    artifact,
                    home.initializer_address_add,
                )?,
                initializer_copy: canonical_instruction(artifact, home.initializer_copy)?,
                initializer_store: canonical_instruction(artifact, home.initializer_store)?,
                initial_value: home.initial_value,
                reloads: home
                    .reloads
                    .iter()
                    .map(|reload| {
                        Ok(CertifiedSumArrayReload {
                            address_add: canonical_instruction(artifact, reload.address_add)?,
                            load: canonical_instruction(artifact, reload.load)?,
                            value: reload.value,
                        })
                    })
                    .collect::<Result<Vec<_>, MachineBuildError>>()?
                    .into_boxed_slice(),
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    let predicate = CertifiedSumArrayO0Predicate {
        blocks: [
            fact.predicate.header_block,
            fact.predicate.body_block,
            fact.predicate.exit_block,
        ],
        index: fact.predicate.index,
        length: fact.predicate.length,
        subtract: canonical_instruction(artifact, fact.predicate.subtract)?,
        signed_overflow: canonical_instruction(artifact, fact.predicate.signed_overflow)?,
        sign: canonical_instruction(artifact, fact.predicate.sign)?,
        greater_or_equal: fact.predicate.greater_or_equal,
        branch: canonical_instruction(artifact, fact.predicate.branch)?,
        signed_width_bits: fact.predicate.signed_width_bits,
    };
    let scalar_loop = CertifiedSumArrayO0Loop {
        array_base: fact.scalar_loop.array_base,
        index: fact.scalar_loop.index,
        sign_extend_index: canonical_instruction(artifact, fact.scalar_loop.sign_extend_index)?,
        extended_index: fact.scalar_loop.extended_index,
        scale: canonical_instruction(artifact, fact.scalar_loop.scale)?,
        scaled_index: fact.scalar_loop.scaled_index,
        address_add: canonical_instruction(artifact, fact.scalar_loop.address_add)?,
        element_address: fact.scalar_loop.element_address,
        reads: certified_reads(artifact, &fact.scalar_loop.reads)?.into_boxed_slice(),
        prior_sum_reads: certified_reads(artifact, &fact.scalar_loop.prior_sum_reads)?
            .into_boxed_slice(),
        add: canonical_instruction(artifact, fact.scalar_loop.add)?,
        next_sum: fact.scalar_loop.next_sum,
        sum_store: canonical_instruction(artifact, fact.scalar_loop.sum_store)?,
        increment: canonical_instruction(artifact, fact.scalar_loop.increment)?,
        next_index: fact.scalar_loop.next_index,
        index_store: canonical_instruction(artifact, fact.scalar_loop.index_store)?,
        back_edge: canonical_instruction(artifact, fact.scalar_loop.back_edge)?,
        wraps_at_bits: fact.scalar_loop.wraps_at_bits,
    };
    let returned = CertifiedSumArrayReturn {
        path: None,
        block: fact.predicate.exit_block,
        returned_low32: fact.returned.returned_low32,
        sum_load: Some(canonical_instruction(artifact, fact.returned.sum_load)?),
        zero_extend: Some(canonical_instruction(artifact, fact.returned.zero_extend)?),
        physical_full_register: fact.returned.physical_full_register,
        definition: canonical_instruction(artifact, fact.returned.definition.producer)?,
        return_target: fact.returned.return_target,
        return_instruction: canonical_instruction(artifact, fact.returned.return_inst)?,
        return_storage: fact.abi.return_storage,
    };
    finish_certificate(
        artifact,
        CertifiedSumArrayFunction {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            contract_version: CERTIFIED_SUM_ARRAY_CONTRACT_VERSION,
            origin,
            entry: fact.entry,
            lowering: CertifiedSumArrayLowering::O0ScalarHomes,
            types,
            abi,
            binding: CertifiedSumArrayBinding::O0(CertifiedSumArrayO0Binding {
                frame,
                homes,
                predicate,
                scalar_loop,
                returned,
            }),
            instruction_inventory,
            obligation_dispositions: Box::new([]),
            contract_snapshot: Box::new([]),
        },
    )
}

fn certify_o2(
    artifact: &SsaArtifact,
    fact: &SumArrayO2Fact,
) -> Result<CertifiedSumArrayFunction, MachineBuildError> {
    if fact.schema_version != SUM_ARRAY_FACT_SCHEMA_VERSION
        || fact.lowering != SumArrayLowering::O2Vectorized
        || !fact.validate_against(artifact)
        || fact.instruction_inventory.len() != O2_INSTRUCTION_COUNT
        || fact.returns.iter().any(|returned| {
            returned.composition.is_some()
                || returned.definition.storage != fact.abi.return_storage
                || returned.definition.value != returned.physical_full_register
        })
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    validate_source_common(artifact, &fact.abi)?;
    let (origin, types, abi, instruction_inventory) = certified_common(
        artifact,
        &fact.types,
        &fact.abi,
        &fact.instruction_inventory,
    )?;
    let frame = CertifiedSumArrayFrame {
        memory_space: fact.frame.memory_space.into(),
        stack_storage: None,
        frame_pointer_storage: None,
        instruction_pointer_storage: None,
        entry_stack: fact.frame.entry_stack,
        allocated_stack: fact.frame.allocated_stack,
        saved_frame_pointer: fact.frame.saved_frame_pointer,
        restored_frame_pointer: None,
        return_target: None,
        prologue: canonical_instructions(artifact, &fact.frame.prologue)?.into_boxed_slice(),
        main_epilogue: canonical_instructions(artifact, &fact.frame.main_epilogue)?
            .into_boxed_slice(),
        alternate_epilogue: canonical_instructions(artifact, &fact.frame.zero_epilogue)?
            .into_boxed_slice(),
    };
    let guards = fact
        .guards
        .iter()
        .map(|guard| {
            Ok(CertifiedSumArrayO2Guard {
                block: guard.block,
                input: guard.input,
                condition: guard.condition,
                branch: canonical_instruction(artifact, guard.branch)?,
                signed_width_bits: guard.signed_width_bits,
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    let reads = fact
        .vector_loop
        .reads
        .iter()
        .map(|read| {
            Ok(CertifiedSumArrayO2VectorRead {
                order: read.order,
                memory_space: read.memory_space.into(),
                address: read.address,
                load: canonical_instruction(artifact, read.load)?,
                value: read.value,
                size_bytes: read.size_bytes,
                lane_projections: canonical_instructions(artifact, &read.lane_projections)?
                    .into_boxed_slice(),
                lane_values: read.lane_values.clone(),
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    let lanes = fact
        .vector_loop
        .lanes
        .iter()
        .map(|lane| {
            Ok(CertifiedSumArrayO2Lane {
                lane: lane.lane,
                accumulator_storage: lane.accumulator_storage,
                initial_projection: canonical_instruction(artifact, lane.initial_projection)?,
                initial_value: lane.initial_value,
                phi: canonical_instruction(artifact, lane.phi)?,
                phi_value: lane.phi_value,
                load_projection: canonical_instruction(artifact, lane.load_projection)?,
                loaded_value: lane.loaded_value,
                add: canonical_instruction(artifact, lane.add)?,
                next_value: lane.next_value,
                wraps_at_bits: lane.wraps_at_bits,
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    let vector_loop = CertifiedSumArrayO2VectorLoop {
        blocks: [
            fact.vector_loop.preheader_block,
            fact.vector_loop.header_block,
        ],
        byte_offset_phi: canonical_instruction(artifact, fact.vector_loop.byte_offset_phi)?,
        byte_offset: fact.vector_loop.byte_offset,
        bound: fact.vector_loop.bound,
        reads,
        lanes,
        induction_add: canonical_instruction(artifact, fact.vector_loop.induction_add)?,
        next_byte_offset: fact.vector_loop.next_byte_offset,
        step_bytes: fact.vector_loop.step_bytes,
        back_edge: canonical_instruction(artifact, fact.vector_loop.back_edge)?,
    };
    let reduction = CertifiedSumArrayO2Reduction {
        block: fact.reduction.block,
        input_lanes: fact.reduction.input_lanes.clone(),
        pairwise_adds: canonical_instructions(artifact, &fact.reduction.pairwise_adds)?
            .into_boxed_slice(),
        pairwise_values: fact.reduction.pairwise_values.clone(),
        selector_packets: fact
            .reduction
            .selector_packets
            .iter()
            .map(|packet| canonical_instructions(artifact, packet).map(Vec::into_boxed_slice))
            .collect::<Result<Vec<_>, MachineBuildError>>()?
            .into_boxed_slice(),
        final_add: canonical_instruction(artifact, fact.reduction.final_add)?,
        returned_low32: fact.reduction.returned_low32,
        zero_extend: canonical_instruction(artifact, fact.reduction.zero_extend)?,
        physical_full_register: fact.reduction.physical_full_register,
        wraps_at_bits: fact.reduction.wraps_at_bits,
    };
    let scalar_tail = CertifiedSumArrayO2ScalarTail {
        header_block: fact.scalar_tail.header_block,
        accumulator_phi: canonical_instruction(artifact, fact.scalar_tail.accumulator_phi)?,
        accumulator: fact.scalar_tail.accumulator,
        index_phi: canonical_instruction(artifact, fact.scalar_tail.index_phi)?,
        index: fact.scalar_tail.index,
        length_phi: canonical_instruction(artifact, fact.scalar_tail.length_phi)?,
        length: fact.scalar_tail.length,
        scale: canonical_instruction(artifact, fact.scalar_tail.scale)?,
        element_address: fact.scalar_tail.element_address,
        reads: certified_reads(artifact, &fact.scalar_tail.reads)?.into_boxed_slice(),
        add: canonical_instruction(artifact, fact.scalar_tail.add)?,
        next_accumulator: fact.scalar_tail.next_accumulator,
        increment: canonical_instruction(artifact, fact.scalar_tail.increment)?,
        next_index: fact.scalar_tail.next_index,
        back_edge: canonical_instruction(artifact, fact.scalar_tail.back_edge)?,
        wraps_at_bits: fact.scalar_tail.wraps_at_bits,
    };
    let returns = fact
        .returns
        .iter()
        .map(|returned| {
            Ok(CertifiedSumArrayReturn {
                path: Some(returned.path.into()),
                block: returned.block,
                returned_low32: returned.returned_low32,
                sum_load: None,
                zero_extend: None,
                physical_full_register: returned.physical_full_register,
                definition: canonical_instruction(artifact, returned.definition.producer)?,
                return_target: returned.return_target,
                return_instruction: canonical_instruction(artifact, returned.return_inst)?,
                return_storage: fact.abi.return_storage,
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    finish_certificate(
        artifact,
        CertifiedSumArrayFunction {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            contract_version: CERTIFIED_SUM_ARRAY_CONTRACT_VERSION,
            origin,
            entry: fact.entry,
            lowering: CertifiedSumArrayLowering::O2Vectorized,
            types,
            abi,
            binding: CertifiedSumArrayBinding::O2(CertifiedSumArrayO2Binding {
                topology: CertifiedSumArrayO2Topology {
                    blocks: fact.topology.blocks.clone(),
                    block_sizes: fact.topology.block_sizes.clone(),
                    operation_counts: fact.topology.operation_counts.clone(),
                    phi_counts: fact.topology.phi_counts.clone(),
                },
                frame,
                guards,
                vector_loop,
                reduction,
                scalar_tail,
                returns,
            }),
            instruction_inventory,
            obligation_dispositions: Box::new([]),
            contract_snapshot: Box::new([]),
        },
    )
}

fn certified_common(
    artifact: &SsaArtifact,
    types: &r2ssa::SumArrayTypeFact,
    abi: &r2ssa::SumArrayAbiFact,
    inventory: &[r2ssa::SumArrayInstructionDispositionFact],
) -> Result<
    (
        CertifiedArtifactOrigin,
        CertifiedSumArrayType,
        CertifiedSumArrayAbi,
        Box<[CertifiedSumArrayInstructionDisposition]>,
    ),
    MachineBuildError,
> {
    let machine_context = CertifiedMachineContext::from_artifact(artifact)?;
    let topology = certified_source_topology(artifact)?;
    let origin = certified_artifact_origin(artifact, &machine_context, &topology)?;
    let parameters = abi
        .parameters
        .iter()
        .zip(&abi.parameter_logical_values)
        .map(|(parameter, logical_value)| CertifiedSumArrayParameter {
            index: parameter.index,
            abi_storage: parameter.abi_storage,
            graph_storage: parameter.graph_storage,
            graph_value: parameter.graph_value,
            logical_value: *logical_value,
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let instruction_inventory = inventory
        .iter()
        .map(|item| {
            Ok(CertifiedSumArrayInstructionDisposition {
                instruction: canonical_instruction(artifact, item.instruction)?,
                block_index: item.block_index,
                ordinal: item.ordinal,
                class: item.class.into(),
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    Ok((
        origin,
        CertifiedSumArrayType {
            signed_integer_type_id: types.signed_integer_type_id,
            pointer_type_id: types.pointer_type_id,
            element_size_bytes: types.element_size_bytes,
        },
        CertifiedSumArrayAbi {
            revision_identity: abi.revision_identity.clone(),
            parameters,
            return_logical_value: abi.return_logical_value,
            return_storage: abi.return_storage,
        },
        instruction_inventory,
    ))
}

fn finish_certificate(
    artifact: &SsaArtifact,
    mut certificate: CertifiedSumArrayFunction,
) -> Result<CertifiedSumArrayFunction, MachineBuildError> {
    let classes = certificate
        .instruction_inventory
        .iter()
        .map(|item| (item.instruction, item.class))
        .collect::<BTreeMap<_, _>>();
    certificate.obligation_dispositions = artifact
        .obligations()
        .obligations()
        .keys()
        .copied()
        .map(|obligation| {
            classes
                .get(&obligation.instruction)
                .copied()
                .map(|class| (obligation, class))
                .ok_or_else(|| obligation_error(artifact.obligations(), obligation))
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    certificate.contract_snapshot = sum_array_contract_snapshot(&certificate)
        .map_err(|_| MachineBuildError::TopologyMismatch)?
        .into_boxed_slice();
    if !certificate.validate(artifact.obligations()) {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(certificate)
}

fn certified_reads(
    artifact: &SsaArtifact,
    reads: &[r2ssa::SumArrayReadFact],
) -> Result<Vec<CertifiedSumArrayRead>, MachineBuildError> {
    reads
        .iter()
        .map(|read| {
            Ok(CertifiedSumArrayRead {
                order: read.order,
                memory_space: read.memory_space.into(),
                address: read.address,
                load: canonical_instruction(artifact, read.load)?,
                value: read.value,
                size_bytes: read.size_bytes,
            })
        })
        .collect()
}

fn validate_source_common(
    artifact: &SsaArtifact,
    abi: &r2ssa::SumArrayAbiFact,
) -> Result<(), MachineBuildError> {
    let interface = artifact
        .machine_context()
        .function_interface()
        .ok_or(MachineBuildError::MachineContextMismatch)?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.calling_convention() != "sysv_amd64"
        || interface.revision_identity() != &*abi.revision_identity
        || interface.parameters().len() != 2
        || interface.parameter_logical_values() != &*abi.parameter_logical_values
        || interface.return_logical_value() != Some(abi.return_logical_value)
        || interface.return_kind()
            != (SourceFunctionReturn::Register {
                storage: abi.return_storage,
            })
        || interface
            .type_graph()
            .is_none_or(|graph| graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION)
        || !artifact.obligations().is_complete()
    {
        return Err(MachineBuildError::MachineContextMismatch);
    }
    Ok(())
}

fn sum_array_contract_snapshot(
    certificate: &CertifiedSumArrayFunction,
) -> Result<Vec<u8>, serde_json::Error> {
    serde_json::to_vec(&(
        certificate.schema_version,
        certificate.contract_version,
        certificate.entry,
        certificate.lowering,
        certificate.types,
        &certificate.abi,
        &certificate.binding,
        &certificate.instruction_inventory,
        &certificate.obligation_dispositions,
    ))
}

fn validate_common(certificate: &CertifiedSumArrayFunction) -> Result<(), ()> {
    let types = certificate.types;
    let abi = &certificate.abi;
    if types.element_size_bytes != 4
        || abi.parameters.len() != 2
        || abi.parameters.iter().enumerate().any(|(index, parameter)| {
            parameter.index != index as u32
                || parameter.logical_value.type_id()
                    != if index == 0 {
                        types.pointer_type_id
                    } else {
                        types.signed_integer_type_id
                    }
                || parameter.logical_value.carrier().offset_bits() != 0
                || parameter.logical_value.carrier().kind()
                    != if index == 0 {
                        SourceCarrierKind::Full
                    } else {
                        SourceCarrierKind::LowBits
                    }
                || parameter.logical_value.carrier().size_bits() != if index == 0 { 64 } else { 32 }
        })
        || !register_storage(abi.parameters[0].abi_storage, RDI_OFFSET, 8)
        || abi.parameters[0].graph_storage != abi.parameters[0].abi_storage
        || !register_storage(abi.parameters[1].abi_storage, RSI_OFFSET, 8)
        || !register_storage(abi.parameters[1].graph_storage, RSI_OFFSET, 4)
        || abi.return_logical_value.type_id() != types.signed_integer_type_id
        || abi.return_logical_value.carrier().kind() != SourceCarrierKind::LowBits
        || abi.return_logical_value.carrier().offset_bits() != 0
        || abi.return_logical_value.carrier().size_bits() != 32
        || !register_storage(abi.return_storage, RAX_OFFSET, 8)
    {
        return Err(());
    }
    let interface = certificate
        .origin
        .machine_context()
        .source()
        .function_interface()
        .ok_or(())?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.calling_convention() != "sysv_amd64"
        || interface.revision_identity() != &*abi.revision_identity
        || interface.parameters().len() != abi.parameters.len()
        || interface
            .parameters()
            .iter()
            .zip(&abi.parameters)
            .any(|(source, certified)| {
                source.index() != certified.index || source.storage() != certified.abi_storage
            })
        || interface.parameter_logical_values()
            != abi
                .parameters
                .iter()
                .map(|parameter| parameter.logical_value)
                .collect::<Vec<_>>()
        || interface.return_logical_value() != Some(abi.return_logical_value)
        || interface.return_kind()
            != (SourceFunctionReturn::Register {
                storage: abi.return_storage,
            })
    {
        return Err(());
    }
    let graph = interface.type_graph().ok_or(())?;
    let signed = graph
        .types()
        .get(types.signed_integer_type_id as usize)
        .ok_or(())?;
    let pointer = graph
        .types()
        .get(types.pointer_type_id as usize)
        .ok_or(())?;
    if graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || graph.types().len() != 2
        || !graph.aggregates().is_empty()
        || signed.kind() != SourceTypeKind::SignedInteger
        || signed.size_bits() != 32
        || signed.align_bits() != 32
        || pointer.kind()
            != (SourceTypeKind::Pointer {
                target_type_id: types.signed_integer_type_id,
            })
        || pointer.size_bits() != 64
        || pointer.align_bits() != 64
    {
        return Err(());
    }
    Ok(())
}

fn validate_binding(
    certificate: &CertifiedSumArrayFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    match (&certificate.lowering, &certificate.binding) {
        (CertifiedSumArrayLowering::O0ScalarHomes, CertifiedSumArrayBinding::O0(binding)) => {
            validate_o0(certificate, binding, source)
        }
        (CertifiedSumArrayLowering::O2Vectorized, CertifiedSumArrayBinding::O2(binding)) => {
            validate_o2(certificate, binding, source)
        }
        _ => Err(()),
    }
}

fn validate_o0(
    certificate: &CertifiedSumArrayFunction,
    binding: &CertifiedSumArrayO0Binding,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let blocks = certificate.origin.topology().blocks();
    let frame = &binding.frame;
    if blocks.len() != 4
        || certificate.instruction_inventory.len() != O0_INSTRUCTION_COUNT
        || blocks
            .iter()
            .map(|block| block.instructions().len())
            .collect::<Vec<_>>()
            != [16, 38, 46, 11]
        || frame.prologue.len() != 4
        || frame.main_epilogue.len() != 7
        || !frame.alternate_epilogue.is_empty()
        || !register_storage(frame.stack_storage.ok_or(())?, 32, 8)
        || !register_storage(frame.frame_pointer_storage.ok_or(())?, RBP_OFFSET, 8)
        || !register_storage(frame.instruction_pointer_storage.ok_or(())?, 648, 8)
        || frame.restored_frame_pointer.is_none()
        || frame.return_target.is_none()
        || binding.homes.len() != 4
        || binding.predicate.blocks != [blocks[1].addr(), blocks[2].addr(), blocks[3].addr()]
        || binding.predicate.signed_width_bits != 32
        || binding.scalar_loop.wraps_at_bits != 32
        || binding.scalar_loop.reads.len() != 1
        || binding.scalar_loop.prior_sum_reads.len() != 3
        || binding.returned.path.is_some()
        || binding.returned.block != blocks[3].addr()
        || binding.returned.sum_load.is_none()
        || binding.returned.zero_extend.is_none()
        || binding.returned.definition != binding.returned.zero_extend.ok_or(())?
        || binding.returned.return_storage != certificate.abi.return_storage
        || binding.returned.return_target != frame.return_target.ok_or(())?
        || binding.returned.returned_low32 == binding.returned.physical_full_register
    {
        return Err(());
    }
    let expected_homes = [
        (CertifiedSumArrayHomeRole::ArrayParameter, -8, -16, 8, 1),
        (CertifiedSumArrayHomeRole::LengthParameter, -12, -20, 4, 1),
        (CertifiedSumArrayHomeRole::SumLocal, -16, -24, 4, 4),
        (CertifiedSumArrayHomeRole::IndexLocal, -20, -28, 4, 3),
    ];
    if binding.homes.iter().zip(expected_homes).any(
        |(home, (role, frame_offset, stack_offset, size, reloads))| {
            home.role != role
                || home.frame_pointer_offset != frame_offset
                || home.entry_stack_offset != stack_offset
                || home.size_bytes != size
                || home.reloads.len() != reloads
        },
    ) || binding.predicate.index != binding.homes[3].reloads[0].value
        || binding.predicate.length != binding.homes[1].reloads[0].value
        || binding.scalar_loop.index != binding.homes[3].reloads[1].value
        || binding.scalar_loop.element_address != binding.scalar_loop.reads[0].address
        || binding
            .scalar_loop
            .prior_sum_reads
            .iter()
            .zip(&binding.homes[2].reloads[..3])
            .zip([12, 14, 16])
            .any(|((read, reload), order)| {
                read.order != order || read.load != reload.load || read.value != reload.value
            })
        || binding.returned.returned_low32 != binding.homes[2].reloads[3].value
        || binding.returned.sum_load != Some(binding.homes[2].reloads[3].load)
        || binding.scalar_loop.reads[0].order != 0
        || binding.scalar_loop.reads[0].size_bytes != 4
        || binding
            .scalar_loop
            .prior_sum_reads
            .iter()
            .any(|read| read.size_bytes != 4)
    {
        return Err(());
    }
    if certificate
        .origin
        .machine_context()
        .source()
        .function_interface()
        .is_none_or(|interface| {
            let expected = [
                (-20, 4, SourceStackSlotRole::Local),
                (-16, 4, SourceStackSlotRole::Local),
                (
                    -12,
                    4,
                    SourceStackSlotRole::ParameterHome {
                        parameter_index: 1,
                        home_storage: certificate.abi.parameters[1].abi_storage,
                    },
                ),
                (
                    -8,
                    8,
                    SourceStackSlotRole::ParameterHome {
                        parameter_index: 0,
                        home_storage: certificate.abi.parameters[0].abi_storage,
                    },
                ),
            ];
            interface.stack_slots().len() != expected.len()
                || expected.iter().any(|(offset, size, role)| {
                    !interface.stack_slots().iter().any(|slot| {
                        slot.base_storage() == frame.frame_pointer_storage.unwrap()
                            && slot.offset() == *offset
                            && slot.size_bytes() == *size
                            && slot.role() == *role
                    })
                })
        })
    {
        return Err(());
    }
    validate_frame_classes(certificate, frame)?;
    let classes = instruction_classes(certificate)?;
    for home in &binding.homes {
        for instruction in [
            home.initializer_address_add,
            home.initializer_copy,
            home.initializer_store,
        ]
        .into_iter()
        .chain(
            home.reloads
                .iter()
                .flat_map(|reload| [reload.address_add, reload.load]),
        ) {
            if !matches!(
                classes.get(&instruction),
                Some(
                    CertifiedSumArrayDispositionClass::Semantic
                        | CertifiedSumArrayDispositionClass::Structural
                )
            ) {
                return Err(());
            }
        }
    }
    for instruction in [
        binding.predicate.subtract,
        binding.predicate.signed_overflow,
        binding.predicate.sign,
        binding.predicate.branch,
        binding.scalar_loop.back_edge,
    ] {
        require_class(
            &classes,
            instruction,
            CertifiedSumArrayDispositionClass::Structural,
        )?;
    }
    for instruction in [
        binding.scalar_loop.sign_extend_index,
        binding.scalar_loop.scale,
        binding.scalar_loop.address_add,
        binding.scalar_loop.add,
        binding.scalar_loop.sum_store,
        binding.scalar_loop.increment,
        binding.scalar_loop.index_store,
        binding.returned.sum_load.ok_or(())?,
        binding.returned.zero_extend.ok_or(())?,
    ]
    .into_iter()
    {
        require_class(
            &classes,
            instruction,
            CertifiedSumArrayDispositionClass::Semantic,
        )?;
    }
    for read in binding
        .scalar_loop
        .reads
        .iter()
        .chain(&*binding.scalar_loop.prior_sum_reads)
    {
        if !matches!(
            classes.get(&read.load),
            Some(
                CertifiedSumArrayDispositionClass::Semantic
                    | CertifiedSumArrayDispositionClass::Structural
            )
        ) {
            return Err(());
        }
    }
    require_class(
        &classes,
        binding.returned.return_instruction,
        CertifiedSumArrayDispositionClass::Frame,
    )?;
    validate_reads(
        certificate,
        source,
        binding
            .scalar_loop
            .reads
            .iter()
            .chain(&*binding.scalar_loop.prior_sum_reads),
    )?;
    validate_return(source, &binding.returned)?;
    validate_direct_definition(
        source,
        binding.returned.zero_extend.ok_or(())?,
        binding.returned.returned_low32,
    )
}

fn validate_o2(
    certificate: &CertifiedSumArrayFunction,
    binding: &CertifiedSumArrayO2Binding,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    const SIZES: [u32; 10] = [8, 7, 6, 39, 28, 30, 6, 11, 2, 4];
    const OPS: [u32; 10] = [16, 14, 21, 119, 46, 154, 3, 42, 7, 17];
    const PHIS: [u32; 10] = [0, 0, 0, 0, 27, 0, 0, 103, 103, 0];
    const OFFSETS: [u64; 10] = [0, 8, 15, 25, 64, 92, 122, 128, 139, 21];
    let topology = &binding.topology;
    let blocks = certificate.origin.topology().blocks();
    let frame = &binding.frame;
    if certificate.instruction_inventory.len() != O2_INSTRUCTION_COUNT
        || topology.blocks.len() != 10
        || topology.block_sizes.as_ref() != SIZES
        || topology.operation_counts.as_ref() != OPS
        || topology.phi_counts.as_ref() != PHIS
        || blocks.len() != 10
        || blocks
            .iter()
            .map(|block| block.addr())
            .ne(topology.blocks.iter().copied())
        || topology
            .blocks
            .iter()
            .zip(OFFSETS)
            .any(|(block, offset)| block.checked_sub(certificate.entry) != Some(offset))
        || blocks
            .iter()
            .zip(OPS.into_iter().zip(PHIS))
            .any(|(block, (ops, phis))| block.instructions().len() != (ops + phis) as usize)
        || frame.stack_storage.is_some()
        || frame.frame_pointer_storage.is_some()
        || frame.instruction_pointer_storage.is_some()
        || frame.restored_frame_pointer.is_some()
        || frame.return_target.is_some()
        || frame.prologue.len() != 4
        || frame.main_epilogue.len() != 7
        || frame.alternate_epilogue.len() != 7
        || binding.guards.len() != 3
        || binding.vector_loop.blocks != [topology.blocks[3], topology.blocks[4]]
        || binding.vector_loop.reads.len() != 2
        || binding.vector_loop.lanes.len() != 8
        || binding.vector_loop.step_bytes != 32
        || binding.reduction.block != topology.blocks[5]
        || binding.reduction.input_lanes.len() != 8
        || binding.reduction.pairwise_adds.len() != 4
        || binding.reduction.pairwise_values.len() != 4
        || binding.reduction.selector_packets.len() != 8
        || binding
            .reduction
            .selector_packets
            .iter()
            .any(|packet| packet.len() != 15)
        || binding.reduction.wraps_at_bits != 32
        || binding.scalar_tail.header_block != topology.blocks[7]
        || binding.scalar_tail.reads.len() != 3
        || binding.scalar_tail.wraps_at_bits != 32
        || binding.returns.len() != 2
        || !certificate
            .origin
            .machine_context()
            .source()
            .function_interface()
            .is_some_and(|interface| interface.stack_slots().is_empty())
    {
        return Err(());
    }
    if binding
        .guards
        .iter()
        .zip([0usize, 1, 5])
        .any(|(guard, block)| {
            guard.block != topology.blocks[block] || guard.signed_width_bits != 32
        })
        || binding.guards[0].input != certificate.abi.parameters[1].graph_value
        || binding.guards[1].input != certificate.abi.parameters[1].graph_value
        || binding
            .vector_loop
            .reads
            .iter()
            .enumerate()
            .any(|(order, read)| {
                read.order != order as u32
                    || read.size_bytes != 16
                    || read.lane_projections.len() != 4
                    || read.lane_values.len() != 4
                    || read.memory_space != frame.memory_space
            })
        || binding
            .vector_loop
            .lanes
            .iter()
            .enumerate()
            .any(|(index, lane)| {
                let read = &binding.vector_loop.reads[index / 4];
                let lane_index = index % 4;
                lane.lane != index as u32
                    || lane.wraps_at_bits != 32
                    || lane.load_projection != read.lane_projections[lane_index]
                    || lane.loaded_value != read.lane_values[lane_index]
                    || lane.next_value != binding.reduction.input_lanes[index]
            })
        || binding.reduction.returned_low32 == binding.reduction.physical_full_register
        || binding
            .scalar_tail
            .reads
            .iter()
            .enumerate()
            .any(|(order, read)| {
                read.order != order as u32
                    || read.size_bytes != 4
                    || read.address != binding.scalar_tail.element_address
                    || read.memory_space != frame.memory_space
            })
        || binding
            .returns
            .iter()
            .zip([
                (CertifiedSumArrayO2ReturnPath::VectorOrScalar, 8usize),
                (CertifiedSumArrayO2ReturnPath::NonPositiveLength, 9usize),
            ])
            .any(|(returned, (path, block))| {
                returned.path != Some(path)
                    || returned.block != topology.blocks[block]
                    || returned.sum_load.is_some()
                    || returned.zero_extend.is_some()
                    || returned.return_storage != certificate.abi.return_storage
                    || returned.returned_low32 == returned.physical_full_register
            })
    {
        return Err(());
    }
    validate_frame_classes(certificate, frame)?;
    let classes = instruction_classes(certificate)?;
    for guard in &binding.guards {
        require_class(
            &classes,
            guard.branch,
            CertifiedSumArrayDispositionClass::Semantic,
        )?;
    }
    for instruction in
        [
            binding.vector_loop.byte_offset_phi,
            binding.vector_loop.induction_add,
            binding.vector_loop.back_edge,
            binding.reduction.final_add,
            binding.reduction.zero_extend,
            binding.scalar_tail.accumulator_phi,
            binding.scalar_tail.index_phi,
            binding.scalar_tail.length_phi,
            binding.scalar_tail.scale,
            binding.scalar_tail.add,
            binding.scalar_tail.increment,
            binding.scalar_tail.back_edge,
        ]
        .into_iter()
        .chain(binding.vector_loop.reads.iter().flat_map(|read| {
            std::iter::once(read.load).chain(read.lane_projections.iter().copied())
        }))
        .chain(binding.vector_loop.lanes.iter().flat_map(|lane| {
            [
                lane.initial_projection,
                lane.phi,
                lane.load_projection,
                lane.add,
            ]
        }))
        .chain(binding.reduction.pairwise_adds.iter().copied())
        .chain(
            binding
                .reduction
                .selector_packets
                .iter()
                .flat_map(|packet| packet.iter().copied()),
        )
        .chain(binding.scalar_tail.reads.iter().map(|read| read.load))
    {
        require_class(
            &classes,
            instruction,
            CertifiedSumArrayDispositionClass::Semantic,
        )?;
    }
    require_class(
        &classes,
        binding.returns[0].definition,
        CertifiedSumArrayDispositionClass::Semantic,
    )?;
    require_class(
        &classes,
        binding.returns[1].definition,
        CertifiedSumArrayDispositionClass::Semantic,
    )?;
    for returned in &binding.returns {
        require_class(
            &classes,
            returned.return_instruction,
            CertifiedSumArrayDispositionClass::Frame,
        )?;
        validate_return(source, returned)?;
    }
    validate_vector_reads(certificate, source, &binding.vector_loop.reads)?;
    validate_reads(certificate, source, binding.scalar_tail.reads.iter())?;
    validate_direct_definition(
        source,
        binding.reduction.zero_extend,
        binding.reduction.returned_low32,
    )
}

fn validate_instruction_closure(
    certificate: &CertifiedSumArrayFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let inventory = certificate
        .instruction_inventory
        .iter()
        .map(|item| item.instruction)
        .collect::<BTreeSet<_>>();
    let topology = certificate.origin.topology();
    let expected = topology
        .blocks()
        .iter()
        .flat_map(|block| block.instructions().iter().copied())
        .collect::<Vec<_>>();
    if inventory.len() != certificate.instruction_inventory.len()
        || inventory != source.instructions().keys().copied().collect()
        || expected
            != certificate
                .instruction_inventory
                .iter()
                .map(|item| item.instruction)
                .collect::<Vec<_>>()
    {
        return Err(());
    }
    let mut cursor = 0usize;
    for (block_index, block) in topology.blocks().iter().enumerate() {
        for (ordinal, instruction) in block.instructions().iter().copied().enumerate() {
            let item = certificate.instruction_inventory.get(cursor).ok_or(())?;
            let source_instruction = source.instructions().get(&instruction).ok_or(())?;
            if item.instruction != instruction
                || item.block_index != block_index as u32
                || item.ordinal != ordinal as u32
                || expected_instruction_class(certificate.lowering, block_index, ordinal)
                    != Some(item.class)
                || (source_instruction.state == SemanticInstructionState::UnsupportedUnknown
                    && item.class != CertifiedSumArrayDispositionClass::Frame)
                || (item.class == CertifiedSumArrayDispositionClass::ProvenDead
                    && (source_instruction.state != SemanticInstructionState::ProvenDead
                        || !source_instruction.obligations.is_empty()))
            {
                return Err(());
            }
            cursor += 1;
        }
    }
    if cursor != certificate.instruction_inventory.len() {
        return Err(());
    }
    Ok(())
}

fn expected_instruction_class(
    lowering: CertifiedSumArrayLowering,
    block: usize,
    ordinal: usize,
) -> Option<CertifiedSumArrayDispositionClass> {
    match lowering {
        CertifiedSumArrayLowering::O0ScalarHomes => Some(match block {
            0 if ordinal < 4 => CertifiedSumArrayDispositionClass::Frame,
            0 => CertifiedSumArrayDispositionClass::Semantic,
            1 if ordinal < 20 => CertifiedSumArrayDispositionClass::ProvenDead,
            1 if ordinal - 20 <= 6 => CertifiedSumArrayDispositionClass::Semantic,
            1 => CertifiedSumArrayDispositionClass::Structural,
            2 if matches!(ordinal, 0..=12 | 17..=18 | 25..=31 | 34..=35 | 42..=44) => {
                CertifiedSumArrayDispositionClass::Semantic
            }
            2 => CertifiedSumArrayDispositionClass::Structural,
            3 if ordinal <= 3 => CertifiedSumArrayDispositionClass::Semantic,
            3 => CertifiedSumArrayDispositionClass::Frame,
            _ => return None,
        }),
        CertifiedSumArrayLowering::O2Vectorized => {
            let phi_count = *[0usize, 0, 0, 0, 27, 0, 0, 103, 103, 0].get(block)?;
            if ordinal < phi_count {
                return Some(if matches!(block, 4 | 7 | 8) {
                    CertifiedSumArrayDispositionClass::Semantic
                } else {
                    CertifiedSumArrayDispositionClass::Structural
                });
            }
            let operation = ordinal.checked_sub(phi_count)?;
            Some(
                if block == 0 && operation < 4 || block == 8 || block == 9 && operation >= 10 {
                    CertifiedSumArrayDispositionClass::Frame
                } else if matches!(block, 0..=7 | 9) {
                    CertifiedSumArrayDispositionClass::Semantic
                } else {
                    CertifiedSumArrayDispositionClass::Structural
                },
            )
        }
    }
}

fn validate_obligation_closure(
    certificate: &CertifiedSumArrayFunction,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let instructions = instruction_classes(certificate)?;
    let obligations = certificate
        .obligation_dispositions
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    if obligations.len() != certificate.obligation_dispositions.len()
        || obligations.len() != source.obligations().len()
        || obligations.keys().copied().collect::<BTreeSet<_>>()
            != source.obligations().keys().copied().collect()
        || certificate
            .obligation_dispositions
            .iter()
            .any(|(obligation, class)| {
                instructions.get(&obligation.instruction) != Some(class)
                    || *class == CertifiedSumArrayDispositionClass::ProvenDead
            })
    {
        return Err(());
    }
    Ok(())
}

fn validate_frame_classes(
    certificate: &CertifiedSumArrayFunction,
    frame: &CertifiedSumArrayFrame,
) -> Result<(), ()> {
    let classes = instruction_classes(certificate)?;
    for instruction in frame
        .prologue
        .iter()
        .chain(&*frame.main_epilogue)
        .chain(&*frame.alternate_epilogue)
    {
        require_class(
            &classes,
            *instruction,
            CertifiedSumArrayDispositionClass::Frame,
        )?;
    }
    Ok(())
}

fn instruction_classes(
    certificate: &CertifiedSumArrayFunction,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedSumArrayDispositionClass>, ()> {
    let classes = certificate
        .instruction_inventory
        .iter()
        .map(|item| (item.instruction, item.class))
        .collect::<BTreeMap<_, _>>();
    if classes.len() != certificate.instruction_inventory.len() {
        return Err(());
    }
    Ok(classes)
}

fn require_class(
    classes: &BTreeMap<CanonicalInstructionId, CertifiedSumArrayDispositionClass>,
    instruction: CanonicalInstructionId,
    class: CertifiedSumArrayDispositionClass,
) -> Result<(), ()> {
    if classes.get(&instruction) == Some(&class) {
        Ok(())
    } else {
        Err(())
    }
}

fn validate_vector_reads(
    certificate: &CertifiedSumArrayFunction,
    source: &SemanticObligationInventory,
    reads: &[CertifiedSumArrayO2VectorRead],
) -> Result<(), ()> {
    for read in reads {
        validate_read(
            certificate,
            source,
            read.memory_space,
            read.address,
            read.load,
        )?;
    }
    Ok(())
}

fn validate_reads<'a>(
    certificate: &CertifiedSumArrayFunction,
    source: &SemanticObligationInventory,
    reads: impl IntoIterator<Item = &'a CertifiedSumArrayRead>,
) -> Result<(), ()> {
    for read in reads {
        validate_read(
            certificate,
            source,
            read.memory_space,
            read.address,
            read.load,
        )?;
    }
    Ok(())
}

fn validate_read(
    certificate: &CertifiedSumArrayFunction,
    source: &SemanticObligationInventory,
    memory_space: MachineAddressSpace,
    address: ValueId,
    load: CanonicalInstructionId,
) -> Result<(), ()> {
    let matches = source
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == load
                && obligation.id.kind == SemanticObligationKind::ObservableMemoryRead
                && matches!(
                    obligation.id.component,
                    SemanticObligationComponent::MemoryAccess(_)
                )
        })
        .collect::<Vec<_>>();
    if !matches!(matches.as_slice(), [obligation] if obligation.inputs.as_slice() == [address])
        || memory_space_for_instruction(certificate, load) != Some(memory_space)
    {
        return Err(());
    }
    Ok(())
}

fn validate_return(
    source: &SemanticObligationInventory,
    returned: &CertifiedSumArrayReturn,
) -> Result<(), ()> {
    let slot = SemanticObligationComponent::RegisterSlot {
        index: 0,
        storage: returned.return_storage,
    };
    let values = source
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == returned.return_instruction
                && obligation.id.kind == SemanticObligationKind::ReturnValue
                && obligation.id.component == slot
        })
        .collect::<Vec<_>>();
    let returns = source
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == returned.return_instruction
                && obligation.id.kind == SemanticObligationKind::Return
                && obligation.id.component == SemanticObligationComponent::Whole
        })
        .count();
    if !matches!(values.as_slice(), [obligation]
        if obligation.inputs.as_slice() == [returned.physical_full_register])
        || returns != 1
    {
        return Err(());
    }
    Ok(())
}

fn validate_direct_definition(
    source: &SemanticObligationInventory,
    definition: CanonicalInstructionId,
    input: ValueId,
) -> Result<(), ()> {
    let definitions = source
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == definition
                && obligation.id.kind == SemanticObligationKind::LiveValueProducer
                && obligation.id.component == SemanticObligationComponent::Whole
        })
        .collect::<Vec<_>>();
    if !matches!(definitions.as_slice(), [obligation] if obligation.inputs.as_slice() == [input]) {
        return Err(());
    }
    Ok(())
}

fn memory_space_for_instruction(
    certificate: &CertifiedSumArrayFunction,
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
    use r2il::{AddressSpace, R2ILBlock, R2ILOp, Varnode};
    use r2sleigh_lift::{Disassembler, build_arch_spec};
    use r2ssa::{
        SourceAbiParameterSpec, SourceCarrierProjection, SourceFunctionInterface,
        SourceStackSlotSpec, SourceType, SourceTypeGraph, StackAddressBase,
    };

    use super::*;

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

    fn x86() -> (r2il::ArchSpec, Disassembler) {
        let arch = build_arch_spec(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("x86-64 architecture");
        let disassembler = Disassembler::from_sla(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("x86-64 disassembler");
        (arch, disassembler)
    }

    fn full_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn types() -> SourceTypeGraph {
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            [],
        )
        .expect("sum-array types")
    }

    fn interface(revision: &[u8], homes: bool) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let stack_slots = homes.then(|| {
            vec![
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -20,
                    4,
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -16,
                    4,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -12,
                    4,
                    1,
                    full_storage(RSI_OFFSET),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -8,
                    8,
                    0,
                    full_storage(RDI_OFFSET),
                ),
            ]
        });
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, full_storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, full_storage(RSI_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: full_storage(RAX_OFFSET),
            },
            stack_slots.unwrap_or_default(),
            [
                SourceLogicalValue::new(
                    1,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(types()),
        )
        .expect("exact sum-array interface")
    }

    fn lift_blocks(base: u64, encoded: &[&str]) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
        let (mut arch, disassembler) = x86();
        let mut address = base;
        let blocks = encoded
            .iter()
            .map(|encoded| {
                let bytes = decode_hex(encoded);
                let block = disassembler
                    .lift_block(&bytes, address, bytes.len())
                    .expect("pinned x86 block");
                address += bytes.len() as u64;
                block
            })
            .collect::<Vec<_>>();
        let lifted_spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        for space in lifted_spaces {
            if !arch.spaces.iter().any(|candidate| candidate.id == space) {
                arch.add_space(AddressSpace::new(space, "sleigh-data", 8));
            }
        }
        (arch, blocks)
    }

    fn o0_blocks(base: u64) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
        lift_blocks(
            base,
            &[
                "554889e548897df88975f4c745f000000000c745ec00000000",
                "8b45ec3b45f47d1c",
                "488b45f848634dec8b04880345f08945f08b45ec83c0018945ecebdc",
                "8b45f05dc3",
            ],
        )
    }

    fn o2_blocks(base: u64) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
        lift_blocks(
            base,
            &[
                "554889e585f67e0d",
                "89f183fe08730a",
                "31d231c0eb6b",
                "31c05dc3",
                "89ca81e2f8ffff7f89c8c1e80325ffffff0f48c1e005660fefc031f6660fefc90f1f8000000000",
                "f30f6f1437660ffec2f30f6f543710660ffeca4883c6204839f075e4",
                "660ffec8660f70c1ee660ffec1660f70c855660ffec8660f7ec839ca7411",
                "660f1f440000",
                "03049748ffc24839d175f5",
                "5dc3",
            ],
        )
    }

    fn o0_artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let (arch, blocks) = o0_blocks(base);
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface(revision, true))
            .expect("prepared O0 sum-array artifact")
    }

    fn o2_artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let (arch, blocks) = o2_blocks(base);
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface(revision, false))
            .expect("prepared O2 sum-array artifact")
    }

    #[test]
    fn sum_array_exact_o0_certificate_closes_source() {
        let artifact = o0_artifact(0x1000_0610, b"r2cert-sum-o0");
        let certificate = certify_sum_array_function(&artifact)
            .expect("certification result")
            .expect("exact O0 certificate");
        assert_eq!(
            certificate.lowering,
            CertifiedSumArrayLowering::O0ScalarHomes
        );
        assert_eq!(
            certificate.instruction_inventory.len(),
            O0_INSTRUCTION_COUNT
        );
        assert_eq!(
            certificate.obligation_dispositions.len(),
            artifact.obligations().obligations().len()
        );
        let CertifiedSumArrayBinding::O0(binding) = &certificate.binding else {
            panic!("O0 binding");
        };
        assert_eq!(binding.homes.len(), 4);
        assert_eq!(binding.scalar_loop.reads.len(), 1);
        assert_eq!(binding.scalar_loop.prior_sum_reads.len(), 3);
        assert!(certificate.validate(artifact.obligations()));
    }

    #[test]
    fn sum_array_real_o2_certificate_closes_all_lanes_and_returns() {
        let artifact = o2_artifact(0x1000_0620, b"r2cert-sum-o2");
        let certificate = certify_sum_array_function(&artifact)
            .expect("certification result")
            .expect("exact O2 certificate");
        assert_eq!(
            certificate.lowering,
            CertifiedSumArrayLowering::O2Vectorized
        );
        assert_eq!(
            certificate.instruction_inventory.len(),
            O2_INSTRUCTION_COUNT
        );
        assert_eq!(
            certificate.obligation_dispositions.len(),
            artifact.obligations().obligations().len()
        );
        let CertifiedSumArrayBinding::O2(binding) = &certificate.binding else {
            panic!("O2 binding");
        };
        assert_eq!(binding.vector_loop.reads.len(), 2);
        assert_eq!(binding.vector_loop.lanes.len(), 8);
        assert_eq!(binding.reduction.input_lanes.len(), 8);
        assert_eq!(binding.scalar_tail.reads.len(), 3);
        assert_eq!(binding.returns.len(), 2);
        assert!(certificate.validate(artifact.obligations()));
    }

    #[test]
    fn sum_array_certificate_mutations_fail_closed() {
        let o0 = o0_artifact(0x1000_0610, b"r2cert-sum-o0-mutation");
        let certificate = certify_sum_array_function(&o0)
            .expect("certification result")
            .expect("O0 certificate");

        let mut semantic = certificate.clone();
        let CertifiedSumArrayBinding::O0(binding) = &mut semantic.binding else {
            panic!("O0 binding");
        };
        binding.scalar_loop.next_sum = binding.scalar_loop.next_index;
        assert!(!semantic.validate(o0.obligations()));

        let mut inventory = certificate.clone();
        inventory.instruction_inventory[0].class = CertifiedSumArrayDispositionClass::Semantic;
        assert!(!inventory.validate(o0.obligations()));

        let mut obligations = certificate;
        obligations.obligation_dispositions = obligations.obligation_dispositions[1..].into();
        assert!(!obligations.validate(o0.obligations()));

        let o2 = o2_artifact(0x1000_0620, b"r2cert-sum-o2-mutation");
        let mut vector = certify_sum_array_function(&o2)
            .expect("certification result")
            .expect("O2 certificate");
        let CertifiedSumArrayBinding::O2(binding) = &mut vector.binding else {
            panic!("O2 binding");
        };
        binding.vector_loop.lanes[0].next_value = binding.vector_loop.lanes[1].next_value;
        assert!(!vector.validate(o2.obligations()));
    }

    #[test]
    fn sum_array_foreign_origin_and_relocation_are_separate() {
        let first = o2_artifact(0x1000_0620, b"r2cert-sum-origin-a");
        let second = o2_artifact(0x2000_0620, b"r2cert-sum-origin-b");
        let first_certificate = certify_sum_array_function(&first)
            .expect("first result")
            .expect("first certificate");
        let second_certificate = certify_sum_array_function(&second)
            .expect("second result")
            .expect("relocated certificate");
        assert!(first_certificate.validate(first.obligations()));
        assert!(second_certificate.validate(second.obligations()));
        assert!(!first_certificate.validate(second.obligations()));
        assert!(!second_certificate.validate(first.obligations()));
    }

    #[test]
    fn sum_array_refusal_or_absence_never_certifies() {
        let (arch, mut blocks) = o2_blocks(0x1000_0620);
        let address = blocks[5]
            .ops
            .iter_mut()
            .find_map(|op| match op {
                R2ILOp::Load { addr, .. } if addr.size == 8 => Some(addr),
                _ => None,
            })
            .expect("first vector address");
        *address = Varnode::unique(0xbeef_0000, 8);
        let refused = SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(b"r2cert-refused-o2", false),
        )
        .expect("mutated O2 artifact remains analyzable");
        assert!(refused.structured().sum_arrays.is_empty());
        assert!(refused.structured().sum_array_o2.is_empty());
        assert!(
            certify_sum_array_function(&refused)
                .expect("refusal is not an error")
                .is_none()
        );
    }
}
