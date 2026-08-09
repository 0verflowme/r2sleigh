//! Closed certification for the exact six-block x86-64 O0 nested wrap32 guard.
//!
//! The certificate is issued only from the exact source-side recognizer fact.
//! It retains the immutable artifact origin, every canonical instruction and
//! source state, every semantic obligation disposition, and the complete
//! frame, memory-SSA, arithmetic, flag, control, phi, and return witness.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    AffineAddressTerm, CallSiteId, CanonicalInstructionId, CanonicalStorageId, CompareKind, InstId,
    InstPayload, MachineAddressSpace, MachineBuildError, MemoryDefFact, MemoryLocation,
    MemoryUseFact, MemoryVersion, NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION,
    NestedWrap32GuardO0AccessFact, NestedWrap32GuardO0ArithmeticFact,
    NestedWrap32GuardO0ComparisonFact, NestedWrap32GuardO0Fact, NestedWrap32GuardO0FlagPacketFact,
    NestedWrap32GuardO0FrameFact, NestedWrap32GuardO0InstructionClass,
    NestedWrap32GuardO0PhiLayerFact, NestedWrap32GuardO0PhysicalRange,
    NestedWrap32GuardO0ReturnFact, NestedWrap32GuardO0SlotFact, NestedWrap32GuardO0TopologyFact,
    ObjectId, ObjectKind, PredicateId, RelativeMemoryAddress, SEMANTIC_OBLIGATION_SCHEMA_VERSION,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION,
    SemanticInstructionState, SemanticObligationId, SemanticObligationInventory, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceTypeKind, SsaArtifact, StackAddressBase,
    StructuredAccessId, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedMachineContext,
    certified_artifact_origin, certified_source_topology,
};

pub const CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION: u32 = 1;

const INSTRUCTION_COUNT: usize = 126;
const MEMORY_ACCESS_COUNT: usize = 20;
const FAILURE_PHI_COUNT: usize = 13;
const EXIT_PHI_COUNT: usize = 14;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedNestedWrap32GuardO0DispositionClass {
    FrameEnvelope,
    ParameterHomeState,
    Wrap32Arithmetic,
    LocalSpillState,
    ComparisonPacket,
    NestedControl,
    PrivateResultCarrier,
    ReturnComposition,
    MachineRelayPhi,
}

impl From<NestedWrap32GuardO0InstructionClass> for CertifiedNestedWrap32GuardO0DispositionClass {
    fn from(class: NestedWrap32GuardO0InstructionClass) -> Self {
        match class {
            NestedWrap32GuardO0InstructionClass::FrameEnvelope => Self::FrameEnvelope,
            NestedWrap32GuardO0InstructionClass::ParameterHomeState => Self::ParameterHomeState,
            NestedWrap32GuardO0InstructionClass::Wrap32Arithmetic => Self::Wrap32Arithmetic,
            NestedWrap32GuardO0InstructionClass::LocalSpillState => Self::LocalSpillState,
            NestedWrap32GuardO0InstructionClass::ComparisonPacket => Self::ComparisonPacket,
            NestedWrap32GuardO0InstructionClass::NestedControl => Self::NestedControl,
            NestedWrap32GuardO0InstructionClass::PrivateResultCarrier => Self::PrivateResultCarrier,
            NestedWrap32GuardO0InstructionClass::ReturnComposition => Self::ReturnComposition,
            NestedWrap32GuardO0InstructionClass::MachineRelayPhi => Self::MachineRelayPhi,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0InstructionDisposition {
    instruction: CanonicalInstructionId,
    source_state: SemanticInstructionState,
    class: CertifiedNestedWrap32GuardO0DispositionClass,
}

impl CertifiedNestedWrap32GuardO0InstructionDisposition {
    pub const fn instruction(&self) -> CanonicalInstructionId {
        self.instruction
    }

    pub const fn source_state(&self) -> SemanticInstructionState {
        self.source_state
    }

    pub const fn class(&self) -> CertifiedNestedWrap32GuardO0DispositionClass {
        self.class
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CertifiedNestedWrap32GuardO0AccessId {
    instruction: CanonicalInstructionId,
    ordinal: u32,
}

impl CertifiedNestedWrap32GuardO0AccessId {
    pub const fn instruction(&self) -> CanonicalInstructionId {
        self.instruction
    }

    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0PhysicalRange {
    offset_from_entry_stack: i64,
    size_bytes: u32,
}

impl From<NestedWrap32GuardO0PhysicalRange> for CertifiedNestedWrap32GuardO0PhysicalRange {
    fn from(range: NestedWrap32GuardO0PhysicalRange) -> Self {
        Self {
            offset_from_entry_stack: range.offset_from_entry_stack,
            size_bytes: range.size_bytes,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Topology {
    header: u64,
    second: u64,
    success: u64,
    forwarder: u64,
    failure: u64,
    exit: u64,
}

impl CertifiedNestedWrap32GuardO0Topology {
    pub const fn header(&self) -> u64 {
        self.header
    }

    pub const fn ordered(&self) -> [u64; 6] {
        [
            self.header,
            self.second,
            self.success,
            self.forwarder,
            self.failure,
            self.exit,
        ]
    }
}

impl From<NestedWrap32GuardO0TopologyFact> for CertifiedNestedWrap32GuardO0Topology {
    fn from(topology: NestedWrap32GuardO0TopologyFact) -> Self {
        Self {
            header: topology.header,
            second: topology.second,
            success: topology.success,
            forwarder: topology.forwarder,
            failure: topology.failure,
            exit: topology.exit,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Parameter {
    index: u32,
    abi_storage: CanonicalStorageId,
    low32_storage: CanonicalStorageId,
    low32_value: ValueId,
    logical_value: SourceLogicalValue,
}

impl CertifiedNestedWrap32GuardO0Parameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn low32_value(&self) -> ValueId {
        self.low32_value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Abi {
    revision_identity: Box<[u8]>,
    parameters: Box<[CertifiedNestedWrap32GuardO0Parameter]>,
    return_logical_value: SourceLogicalValue,
    return_storage: CanonicalStorageId,
}

impl CertifiedNestedWrap32GuardO0Abi {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameters(&self) -> &[CertifiedNestedWrap32GuardO0Parameter] {
        &self.parameters
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Frame {
    memory_space: MachineAddressSpace,
    entry_stack: ValueId,
    allocated_stack: ValueId,
    saved_frame_pointer: ValueId,
    established_frame_pointer: ValueId,
    restored_frame_pointer: ValueId,
    restored_stack: ValueId,
    return_target: ValueId,
    final_stack: ValueId,
    return_instruction: CanonicalInstructionId,
    saved_frame_pointer_range: CertifiedNestedWrap32GuardO0PhysicalRange,
    return_address_range: CertifiedNestedWrap32GuardO0PhysicalRange,
    instructions: Box<[CanonicalInstructionId]>,
}

impl CertifiedNestedWrap32GuardO0Frame {
    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }

    pub const fn instructions(&self) -> &[CanonicalInstructionId] {
        &self.instructions
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedNestedWrap32GuardO0ObjectKind {
    StackSlot { base: StackAddressBase, offset: i64 },
    FrameObject { base: StackAddressBase, offset: i64 },
    Parameter { index: usize },
    Global { space: String, address: u64 },
    HeapAlloc { call_site: CallSiteId },
    EscapedUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Object {
    object: ObjectId,
    kind: CertifiedNestedWrap32GuardO0ObjectKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CertifiedNestedWrap32GuardO0MemoryVersion {
    object: ObjectId,
    version: u32,
}

impl From<MemoryVersion> for CertifiedNestedWrap32GuardO0MemoryVersion {
    fn from(version: MemoryVersion) -> Self {
        Self {
            object: version.object,
            version: version.version,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedNestedWrap32GuardO0RelativeAddress {
    Exact(i64),
    Affine {
        terms: Box<[AffineAddressTerm]>,
        offset: i64,
    },
    Unknown,
}

impl From<&RelativeMemoryAddress> for CertifiedNestedWrap32GuardO0RelativeAddress {
    fn from(address: &RelativeMemoryAddress) -> Self {
        match address {
            RelativeMemoryAddress::Exact(offset) => Self::Exact(*offset),
            RelativeMemoryAddress::Affine { terms, offset } => Self::Affine {
                terms: terms.clone().into_boxed_slice(),
                offset: *offset,
            },
            RelativeMemoryAddress::Unknown => Self::Unknown,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0MemoryLocation {
    object: ObjectId,
    address: CertifiedNestedWrap32GuardO0RelativeAddress,
    size_bytes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0MemoryUse {
    location: CertifiedNestedWrap32GuardO0MemoryLocation,
    version: CertifiedNestedWrap32GuardO0MemoryVersion,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0MemoryDef {
    location: CertifiedNestedWrap32GuardO0MemoryLocation,
    previous_version: CertifiedNestedWrap32GuardO0MemoryVersion,
    next_version: CertifiedNestedWrap32GuardO0MemoryVersion,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0MemoryPhi {
    block: u64,
    object: ObjectId,
    location: CertifiedNestedWrap32GuardO0MemoryLocation,
    output_version: CertifiedNestedWrap32GuardO0MemoryVersion,
    inputs: Box<[(u64, CertifiedNestedWrap32GuardO0MemoryVersion)]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0MemoryAccess {
    id: CertifiedNestedWrap32GuardO0AccessId,
    block: u64,
    operation_index: usize,
    object: ObjectId,
    address: ValueId,
    value: Option<ValueId>,
    is_write: bool,
    width_bytes: u32,
    provenance_complete: bool,
    uses: Box<[CertifiedNestedWrap32GuardO0MemoryUse]>,
    definitions: Box<[CertifiedNestedWrap32GuardO0MemoryDef]>,
}

impl CertifiedNestedWrap32GuardO0MemoryAccess {
    pub const fn id(&self) -> CertifiedNestedWrap32GuardO0AccessId {
        self.id
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0SlotAccess {
    access: CertifiedNestedWrap32GuardO0AccessId,
    object: ObjectId,
    value: Option<ValueId>,
    memory_uses: usize,
    memory_definitions: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Slot {
    base: StackAddressBase,
    frame_pointer_offset: i64,
    entry_stack_offset: i64,
    size_bytes: u32,
    object: ObjectId,
    accesses: Box<[CertifiedNestedWrap32GuardO0SlotAccess]>,
}

impl CertifiedNestedWrap32GuardO0Slot {
    pub const fn frame_pointer_offset(&self) -> i64 {
        self.frame_pointer_offset
    }

    pub const fn accesses(&self) -> &[CertifiedNestedWrap32GuardO0SlotAccess] {
        &self.accesses
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Slots {
    parameter_homes: Box<[CertifiedNestedWrap32GuardO0Slot]>,
    sum: CertifiedNestedWrap32GuardO0Slot,
    difference: CertifiedNestedWrap32GuardO0Slot,
    result: CertifiedNestedWrap32GuardO0Slot,
}

impl CertifiedNestedWrap32GuardO0Slots {
    pub const fn parameter_homes(&self) -> &[CertifiedNestedWrap32GuardO0Slot] {
        &self.parameter_homes
    }

    pub const fn result(&self) -> &CertifiedNestedWrap32GuardO0Slot {
        &self.result
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0FlagPacket {
    value: ValueId,
    sign: ValueId,
    zero: ValueId,
    low_byte: ValueId,
    population: ValueId,
    parity_bit: ValueId,
    parity: ValueId,
    instructions: Box<[CanonicalInstructionId]>,
}

impl CertifiedNestedWrap32GuardO0FlagPacket {
    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn instructions(&self) -> &[CanonicalInstructionId] {
        &self.instructions
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Arithmetic {
    left: ValueId,
    right: ValueId,
    result: ValueId,
    carry_or_borrow: ValueId,
    signed_overflow: ValueId,
    flag_packet: CertifiedNestedWrap32GuardO0FlagPacket,
    wraps_at_bits: u32,
}

impl CertifiedNestedWrap32GuardO0Arithmetic {
    pub const fn result(&self) -> ValueId {
        self.result
    }

    pub const fn wraps_at_bits(&self) -> u32 {
        self.wraps_at_bits
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedNestedWrap32GuardO0CompareKind {
    Equal,
    NotEqual,
    Less,
    SignedLess,
    LessEqual,
    SignedLessEqual,
}

impl From<CompareKind> for CertifiedNestedWrap32GuardO0CompareKind {
    fn from(kind: CompareKind) -> Self {
        match kind {
            CompareKind::Equal => Self::Equal,
            CompareKind::NotEqual => Self::NotEqual,
            CompareKind::Less => Self::Less,
            CompareKind::SignedLess => Self::SignedLess,
            CompareKind::LessEqual => Self::LessEqual,
            CompareKind::SignedLessEqual => Self::SignedLessEqual,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0CompareProvenance {
    kind: CertifiedNestedWrap32GuardO0CompareKind,
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Predicate {
    id: PredicateId,
    block: u64,
    condition: ValueId,
    comparison: Option<CertifiedNestedWrap32GuardO0CompareProvenance>,
    evaluated_comparison: Option<CertifiedNestedWrap32GuardO0CompareProvenance>,
    true_target: u64,
    false_target: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0BlockAssumption {
    block: u64,
    predecessor: u64,
    predicate: PredicateId,
    truth: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Comparison {
    block: u64,
    address: ValueId,
    loaded: ValueId,
    copied_operand: ValueId,
    expected: u32,
    carry_or_borrow: ValueId,
    signed_overflow: ValueId,
    difference: ValueId,
    flag_packet: CertifiedNestedWrap32GuardO0FlagPacket,
    inverted_zero: ValueId,
    branch: CanonicalInstructionId,
    true_target: u64,
    false_target: u64,
}

impl CertifiedNestedWrap32GuardO0Comparison {
    pub const fn expected(&self) -> u32 {
        self.expected
    }

    pub const fn branch(&self) -> CanonicalInstructionId {
        self.branch
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Phi {
    instruction: CanonicalInstructionId,
    output: ValueId,
    inputs: Box<[(u64, ValueId)]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0PhiLayer {
    block: u64,
    predecessors: [u64; 2],
    phis: Box<[CertifiedNestedWrap32GuardO0Phi]>,
}

impl CertifiedNestedWrap32GuardO0PhiLayer {
    pub const fn phis(&self) -> &[CertifiedNestedWrap32GuardO0Phi] {
        &self.phis
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Control {
    success_transfer: CanonicalInstructionId,
    forwarder_transfer: CanonicalInstructionId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0ResultCarrier {
    success_address: ValueId,
    success_value: ValueId,
    success_store: CertifiedNestedWrap32GuardO0AccessId,
    failure_address: ValueId,
    failure_value: ValueId,
    failure_store: CertifiedNestedWrap32GuardO0AccessId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Return {
    result_load: CertifiedNestedWrap32GuardO0AccessId,
    loaded_result: ValueId,
    low32_copy: CanonicalInstructionId,
    zero_extend: CanonicalInstructionId,
    returned_value: ValueId,
    return_instruction: CanonicalInstructionId,
    return_target: ValueId,
}

impl CertifiedNestedWrap32GuardO0Return {
    pub const fn returned_value(&self) -> ValueId {
        self.returned_value
    }

    pub const fn return_instruction(&self) -> CanonicalInstructionId {
        self.return_instruction
    }
}

/// Opaque, whole-function certificate for the exact O0 nested wrap32 guard.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0Function {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    revision_identity: Box<[u8]>,
    topology: CertifiedNestedWrap32GuardO0Topology,
    abi: CertifiedNestedWrap32GuardO0Abi,
    frame: CertifiedNestedWrap32GuardO0Frame,
    objects: Box<[CertifiedNestedWrap32GuardO0Object]>,
    memory_accesses: Box<[CertifiedNestedWrap32GuardO0MemoryAccess]>,
    memory_phis: Box<[CertifiedNestedWrap32GuardO0MemoryPhi]>,
    slots: CertifiedNestedWrap32GuardO0Slots,
    sum: CertifiedNestedWrap32GuardO0Arithmetic,
    difference: CertifiedNestedWrap32GuardO0Arithmetic,
    sum_comparison: CertifiedNestedWrap32GuardO0Comparison,
    difference_comparison: CertifiedNestedWrap32GuardO0Comparison,
    predicates: Box<[CertifiedNestedWrap32GuardO0Predicate]>,
    block_assumptions: Box<[CertifiedNestedWrap32GuardO0BlockAssumption]>,
    control: CertifiedNestedWrap32GuardO0Control,
    failure_phis: CertifiedNestedWrap32GuardO0PhiLayer,
    exit_phis: CertifiedNestedWrap32GuardO0PhiLayer,
    result: CertifiedNestedWrap32GuardO0ResultCarrier,
    returned: CertifiedNestedWrap32GuardO0Return,
    instruction_dispositions: Box<[CertifiedNestedWrap32GuardO0InstructionDisposition]>,
    obligation_dispositions: Box<
        [(
            SemanticObligationId,
            CertifiedNestedWrap32GuardO0DispositionClass,
        )],
    >,
    #[serde(skip)]
    contract_snapshot: Box<[u8]>,
}

impl CertifiedNestedWrap32GuardO0Function {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn topology(&self) -> CertifiedNestedWrap32GuardO0Topology {
        self.topology
    }

    pub const fn abi(&self) -> &CertifiedNestedWrap32GuardO0Abi {
        &self.abi
    }

    pub const fn frame(&self) -> &CertifiedNestedWrap32GuardO0Frame {
        &self.frame
    }

    pub const fn slots(&self) -> &CertifiedNestedWrap32GuardO0Slots {
        &self.slots
    }

    pub const fn memory_accesses(&self) -> &[CertifiedNestedWrap32GuardO0MemoryAccess] {
        &self.memory_accesses
    }

    pub const fn memory_phis(&self) -> &[CertifiedNestedWrap32GuardO0MemoryPhi] {
        &self.memory_phis
    }

    pub const fn sum(&self) -> &CertifiedNestedWrap32GuardO0Arithmetic {
        &self.sum
    }

    pub const fn difference(&self) -> &CertifiedNestedWrap32GuardO0Arithmetic {
        &self.difference
    }

    pub const fn sum_comparison(&self) -> &CertifiedNestedWrap32GuardO0Comparison {
        &self.sum_comparison
    }

    pub const fn difference_comparison(&self) -> &CertifiedNestedWrap32GuardO0Comparison {
        &self.difference_comparison
    }

    pub const fn failure_phis(&self) -> &CertifiedNestedWrap32GuardO0PhiLayer {
        &self.failure_phis
    }

    pub const fn exit_phis(&self) -> &CertifiedNestedWrap32GuardO0PhiLayer {
        &self.exit_phis
    }

    pub const fn returned(&self) -> &CertifiedNestedWrap32GuardO0Return {
        &self.returned
    }

    pub const fn instruction_dispositions(
        &self,
    ) -> &[CertifiedNestedWrap32GuardO0InstructionDisposition] {
        &self.instruction_dispositions
    }

    pub const fn obligation_dispositions(
        &self,
    ) -> &[(
        SemanticObligationId,
        CertifiedNestedWrap32GuardO0DispositionClass,
    )] {
        &self.obligation_dispositions
    }

    pub fn validate(&self, source: &SemanticObligationInventory) -> bool {
        validate_contract(self, source).is_ok()
    }

    /// Recollect the exact source fact and immutable origin before accepting a
    /// certificate for an artifact. This refuses graph-identical-looking facts
    /// issued by a foreign source revision or machine context.
    pub fn validate_against_artifact(&self, artifact: &SsaArtifact) -> bool {
        self.validate(artifact.obligations())
            && certify_nested_wrap32_guard_o0_function(artifact)
                .is_ok_and(|recollected| recollected.as_ref() == Some(self))
    }
}

/// Issue a certificate only when the artifact retains exactly one exact O0
/// nested-wrap32-guard fact. Refusal facts and ambiguous matches remain
/// uncertified.
pub fn certify_nested_wrap32_guard_o0_function(
    artifact: &SsaArtifact,
) -> Result<Option<CertifiedNestedWrap32GuardO0Function>, MachineBuildError> {
    let facts = &artifact.structured().nested_wrap32_guard_o0;
    if facts.is_empty() {
        return Ok(None);
    }
    if facts.len() != 1 {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let Some((entry, fact)) = facts.iter().next() else {
        return Err(MachineBuildError::TopologyMismatch);
    };
    if *entry != fact.topology.header
        || fact.schema_version != NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION
        || fact.instruction_inventory.len() != INSTRUCTION_COUNT
        || fact.dispositions.len() != INSTRUCTION_COUNT
        || !fact.validate_against_parts(
            artifact.function(),
            artifact.graph(),
            artifact.objects(),
            artifact.memory(),
            artifact.predicates(),
            &artifact.facts().boundaries,
            &artifact.structured().memory_accesses,
            artifact.machine_context(),
        )
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    certify_exact_fact(artifact, fact).map(Some)
}

fn certify_exact_fact(
    artifact: &SsaArtifact,
    fact: &NestedWrap32GuardO0Fact,
) -> Result<CertifiedNestedWrap32GuardO0Function, MachineBuildError> {
    validate_source(artifact, fact)?;
    let machine_context = CertifiedMachineContext::from_artifact(artifact)?;
    let source_topology = certified_source_topology(artifact)?;
    let origin = certified_artifact_origin(artifact, &machine_context, &source_topology)?;
    let parameters = fact
        .abi
        .parameters
        .iter()
        .zip(&fact.abi.parameter_logical_values)
        .map(
            |(parameter, logical_value)| CertifiedNestedWrap32GuardO0Parameter {
                index: parameter.index,
                abi_storage: parameter.abi_storage,
                low32_storage: parameter.low32_storage,
                low32_value: parameter.low32_value,
                logical_value: *logical_value,
            },
        )
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let abi = CertifiedNestedWrap32GuardO0Abi {
        revision_identity: fact.abi.revision_identity.clone(),
        parameters,
        return_logical_value: fact.abi.return_logical_value,
        return_storage: fact.abi.return_storage,
    };
    let frame = certified_frame(artifact, fact.frame)?;
    let objects = certified_objects(artifact)?;
    let memory_accesses = certified_memory_accesses(artifact)?;
    let memory_phis = certified_memory_phis(artifact);
    let slots = CertifiedNestedWrap32GuardO0Slots {
        parameter_homes: fact
            .slots
            .parameter_homes
            .iter()
            .map(|slot| certified_slot(artifact, slot))
            .collect::<Result<Vec<_>, MachineBuildError>>()?
            .into_boxed_slice(),
        sum: certified_slot(artifact, &fact.slots.sum)?,
        difference: certified_slot(artifact, &fact.slots.difference)?,
        result: certified_slot(artifact, &fact.slots.result)?,
    };
    let sum = certified_arithmetic(artifact, fact.sum)?;
    let difference = certified_arithmetic(artifact, fact.difference)?;
    let sum_comparison = certified_comparison(artifact, fact.sum_comparison)?;
    let difference_comparison = certified_comparison(artifact, fact.difference_comparison)?;
    let predicates = artifact
        .predicates()
        .predicates
        .values()
        .map(|predicate| CertifiedNestedWrap32GuardO0Predicate {
            id: predicate.id,
            block: predicate.block_addr,
            condition: predicate.condition,
            comparison: predicate.comparison.as_ref().map(|comparison| {
                CertifiedNestedWrap32GuardO0CompareProvenance {
                    kind: comparison.kind.into(),
                    lhs: comparison.lhs,
                    rhs: comparison.rhs,
                }
            }),
            evaluated_comparison: predicate.evaluated_comparison.as_ref().map(|comparison| {
                CertifiedNestedWrap32GuardO0CompareProvenance {
                    kind: comparison.kind.into(),
                    lhs: comparison.lhs,
                    rhs: comparison.rhs,
                }
            }),
            true_target: predicate.true_target,
            false_target: predicate.false_target,
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let block_assumptions = artifact
        .predicates()
        .block_assumptions
        .iter()
        .flat_map(|(block, assumptions)| {
            assumptions
                .iter()
                .map(|assumption| CertifiedNestedWrap32GuardO0BlockAssumption {
                    block: *block,
                    predecessor: assumption.predecessor,
                    predicate: assumption.predicate,
                    truth: assumption.truth,
                })
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let graph = artifact.graph();
    let control = CertifiedNestedWrap32GuardO0Control {
        success_transfer: canonical_instruction(
            artifact,
            graph
                .inst_id_for_op_site(fact.topology.success, 3)
                .ok_or(MachineBuildError::TopologyMismatch)?,
        )?,
        forwarder_transfer: canonical_instruction(
            artifact,
            graph
                .inst_id_for_op_site(fact.topology.forwarder, 0)
                .ok_or(MachineBuildError::TopologyMismatch)?,
        )?,
    };
    let failure_phis = certified_phi_layer(artifact, &fact.failure_phis)?;
    let exit_phis = certified_phi_layer(artifact, &fact.exit_phis)?;
    let success_store = certified_access_id(
        artifact,
        StructuredAccessId {
            inst: graph
                .inst_id_for_op_site(fact.topology.success, 2)
                .ok_or(MachineBuildError::TopologyMismatch)?,
            ordinal: 0,
        },
    )?;
    let failure_store = certified_access_id(
        artifact,
        StructuredAccessId {
            inst: graph
                .inst_id_for_op_site(fact.topology.failure, 2)
                .ok_or(MachineBuildError::TopologyMismatch)?,
            ordinal: 0,
        },
    )?;
    let result = CertifiedNestedWrap32GuardO0ResultCarrier {
        success_address: fact.success_address,
        success_value: fact.success_value,
        success_store,
        failure_address: fact.failure_address,
        failure_value: fact.failure_value,
        failure_store,
    };
    let returned = certified_return(artifact, fact.returned)?;
    let instruction_dispositions = certified_instruction_dispositions(artifact, fact)?;
    let classes = instruction_dispositions
        .iter()
        .map(|disposition| (disposition.instruction, disposition.class))
        .collect::<BTreeMap<_, _>>();
    let obligation_dispositions = artifact
        .obligations()
        .obligations()
        .keys()
        .copied()
        .map(|obligation| {
            classes
                .get(&obligation.instruction)
                .copied()
                .map(|class| (obligation, class))
                .ok_or_else(|| obligation_error(artifact, obligation))
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    let mut certificate = CertifiedNestedWrap32GuardO0Function {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION,
        origin,
        revision_identity: fact.abi.revision_identity.clone(),
        topology: fact.topology.into(),
        abi,
        frame,
        objects,
        memory_accesses,
        memory_phis,
        slots,
        sum,
        difference,
        sum_comparison,
        difference_comparison,
        predicates,
        block_assumptions,
        control,
        failure_phis,
        exit_phis,
        result,
        returned,
        instruction_dispositions,
        obligation_dispositions,
        contract_snapshot: Box::new([]),
    };
    certificate.contract_snapshot = contract_snapshot(&certificate)
        .map_err(|_| MachineBuildError::TopologyMismatch)?
        .into_boxed_slice();
    if !certificate.validate(artifact.obligations()) {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(certificate)
}

fn validate_source(
    artifact: &SsaArtifact,
    fact: &NestedWrap32GuardO0Fact,
) -> Result<(), MachineBuildError> {
    let interface = artifact
        .machine_context()
        .function_interface()
        .ok_or(MachineBuildError::MachineContextMismatch)?;
    let types = interface
        .type_graph()
        .ok_or(MachineBuildError::MachineContextMismatch)?;
    let [integer] = types.types() else {
        return Err(MachineBuildError::MachineContextMismatch);
    };
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity() != &*fact.abi.revision_identity
        || interface.calling_convention() != "sysv_amd64"
        || interface.parameters().len() != 2
        || interface.parameter_logical_values() != &*fact.abi.parameter_logical_values
        || interface.return_logical_value() != Some(fact.abi.return_logical_value)
        || interface.return_kind()
            != (SourceFunctionReturn::Register {
                storage: fact.abi.return_storage,
            })
        || types.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || !types.aggregates().is_empty()
        || integer.kind() != SourceTypeKind::SignedInteger
        || integer.size_bits() != 32
        || integer.align_bits() != 32
        || artifact.graph().insts.len() != INSTRUCTION_COUNT
        || artifact.obligations().schema_version() != SEMANTIC_OBLIGATION_SCHEMA_VERSION
        || artifact.obligations().source_instruction_count() != INSTRUCTION_COUNT
        || !artifact.obligations().is_complete()
    {
        return Err(MachineBuildError::MachineContextMismatch);
    }
    Ok(())
}

fn certified_frame(
    artifact: &SsaArtifact,
    frame: NestedWrap32GuardO0FrameFact,
) -> Result<CertifiedNestedWrap32GuardO0Frame, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0Frame {
        memory_space: frame.memory_space.into(),
        entry_stack: frame.entry_stack,
        allocated_stack: frame.allocated_stack,
        saved_frame_pointer: frame.saved_frame_pointer,
        established_frame_pointer: frame.established_frame_pointer,
        restored_frame_pointer: frame.restored_frame_pointer,
        restored_stack: frame.restored_stack,
        return_target: frame.return_target,
        final_stack: frame.final_stack,
        return_instruction: canonical_instruction(artifact, frame.return_inst)?,
        saved_frame_pointer_range: frame.saved_frame_pointer_range.into(),
        return_address_range: frame.return_address_range.into(),
        instructions: canonical_instructions(artifact, &frame.instructions)?.into_boxed_slice(),
    })
}

fn certified_objects(
    artifact: &SsaArtifact,
) -> Result<Box<[CertifiedNestedWrap32GuardO0Object]>, MachineBuildError> {
    artifact
        .objects()
        .objects
        .values()
        .map(|object| {
            let kind = match &object.kind {
                ObjectKind::StackSlot { base, offset } => {
                    CertifiedNestedWrap32GuardO0ObjectKind::StackSlot {
                        base: *base,
                        offset: *offset,
                    }
                }
                ObjectKind::FrameObject { base, offset } => {
                    CertifiedNestedWrap32GuardO0ObjectKind::FrameObject {
                        base: *base,
                        offset: *offset,
                    }
                }
                ObjectKind::Parameter { index } => {
                    CertifiedNestedWrap32GuardO0ObjectKind::Parameter { index: *index }
                }
                ObjectKind::Global { space, address } => {
                    CertifiedNestedWrap32GuardO0ObjectKind::Global {
                        space: space.clone(),
                        address: *address,
                    }
                }
                ObjectKind::HeapAlloc { call_site } => {
                    CertifiedNestedWrap32GuardO0ObjectKind::HeapAlloc {
                        call_site: *call_site,
                    }
                }
                ObjectKind::EscapedUnknown => {
                    CertifiedNestedWrap32GuardO0ObjectKind::EscapedUnknown
                }
            };
            Ok(CertifiedNestedWrap32GuardO0Object {
                object: object.id,
                kind,
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()
        .map(Vec::into_boxed_slice)
}

fn certified_memory_accesses(
    artifact: &SsaArtifact,
) -> Result<Box<[CertifiedNestedWrap32GuardO0MemoryAccess]>, MachineBuildError> {
    let mut accesses = artifact
        .structured()
        .memory_accesses
        .values()
        .map(|access| {
            Ok(CertifiedNestedWrap32GuardO0MemoryAccess {
                id: certified_access_id(artifact, access.id)?,
                block: access.block_addr,
                operation_index: access.op_index,
                object: access.object,
                address: access.address,
                value: access.value,
                is_write: access.is_write,
                width_bytes: access.width,
                provenance_complete: access.provenance_complete,
                uses: artifact
                    .memory()
                    .uses_by_inst
                    .get(&access.id.inst)
                    .into_iter()
                    .flatten()
                    .map(certified_memory_use)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
                definitions: artifact
                    .memory()
                    .defs_by_inst
                    .get(&access.id.inst)
                    .into_iter()
                    .flatten()
                    .map(certified_memory_def)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?;
    accesses.sort_by_key(|access| access.id);
    Ok(accesses.into_boxed_slice())
}

fn certified_memory_phis(artifact: &SsaArtifact) -> Box<[CertifiedNestedWrap32GuardO0MemoryPhi]> {
    let mut phis = artifact
        .memory()
        .phis_by_block
        .iter()
        .flat_map(|(block, phis)| {
            phis.iter()
                .map(|phi| CertifiedNestedWrap32GuardO0MemoryPhi {
                    block: *block,
                    object: phi.object,
                    location: certified_memory_location(&phi.location),
                    output_version: phi.output_version.into(),
                    inputs: phi
                        .inputs
                        .iter()
                        .map(|(predecessor, version)| (*predecessor, (*version).into()))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                })
        })
        .collect::<Vec<_>>();
    phis.sort_by_key(|phi| (phi.block, phi.object, phi.output_version));
    phis.into_boxed_slice()
}

fn certified_memory_use(fact: &MemoryUseFact) -> CertifiedNestedWrap32GuardO0MemoryUse {
    CertifiedNestedWrap32GuardO0MemoryUse {
        location: certified_memory_location(&fact.location),
        version: fact.version.into(),
    }
}

fn certified_memory_def(fact: &MemoryDefFact) -> CertifiedNestedWrap32GuardO0MemoryDef {
    CertifiedNestedWrap32GuardO0MemoryDef {
        location: certified_memory_location(&fact.location),
        previous_version: fact.previous_version.into(),
        next_version: fact.next_version.into(),
    }
}

fn certified_memory_location(
    location: &MemoryLocation,
) -> CertifiedNestedWrap32GuardO0MemoryLocation {
    CertifiedNestedWrap32GuardO0MemoryLocation {
        object: location.object,
        address: (&location.address).into(),
        size_bytes: location.size,
    }
}

fn certified_slot(
    artifact: &SsaArtifact,
    slot: &NestedWrap32GuardO0SlotFact,
) -> Result<CertifiedNestedWrap32GuardO0Slot, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0Slot {
        base: slot.base,
        frame_pointer_offset: slot.frame_pointer_offset,
        entry_stack_offset: slot.entry_stack_offset,
        size_bytes: slot.size_bytes,
        object: slot.object,
        accesses: slot
            .accesses
            .iter()
            .map(|access| certified_slot_access(artifact, *access))
            .collect::<Result<Vec<_>, MachineBuildError>>()?
            .into_boxed_slice(),
    })
}

fn certified_slot_access(
    artifact: &SsaArtifact,
    access: NestedWrap32GuardO0AccessFact,
) -> Result<CertifiedNestedWrap32GuardO0SlotAccess, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0SlotAccess {
        access: certified_access_id(artifact, access.access)?,
        object: access.object,
        value: access.value,
        memory_uses: access.memory_uses,
        memory_definitions: access.memory_defs,
    })
}

fn certified_arithmetic(
    artifact: &SsaArtifact,
    arithmetic: NestedWrap32GuardO0ArithmeticFact,
) -> Result<CertifiedNestedWrap32GuardO0Arithmetic, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0Arithmetic {
        left: arithmetic.left,
        right: arithmetic.right,
        result: arithmetic.result,
        carry_or_borrow: arithmetic.carry_or_borrow,
        signed_overflow: arithmetic.signed_overflow,
        flag_packet: certified_flag_packet(artifact, arithmetic.flag_packet)?,
        wraps_at_bits: arithmetic.wraps_at_bits,
    })
}

fn certified_flag_packet(
    artifact: &SsaArtifact,
    packet: NestedWrap32GuardO0FlagPacketFact,
) -> Result<CertifiedNestedWrap32GuardO0FlagPacket, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0FlagPacket {
        value: packet.value,
        sign: packet.sign,
        zero: packet.zero,
        low_byte: packet.low_byte,
        population: packet.population,
        parity_bit: packet.parity_bit,
        parity: packet.parity,
        instructions: canonical_instructions(artifact, &packet.instructions)?.into_boxed_slice(),
    })
}

fn certified_comparison(
    artifact: &SsaArtifact,
    comparison: NestedWrap32GuardO0ComparisonFact,
) -> Result<CertifiedNestedWrap32GuardO0Comparison, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0Comparison {
        block: comparison.block,
        address: comparison.address,
        loaded: comparison.loaded,
        copied_operand: comparison.copied_operand,
        expected: comparison.expected,
        carry_or_borrow: comparison.carry_or_borrow,
        signed_overflow: comparison.signed_overflow,
        difference: comparison.difference,
        flag_packet: certified_flag_packet(artifact, comparison.flag_packet)?,
        inverted_zero: comparison.inverted_zero,
        branch: canonical_instruction(artifact, comparison.branch_inst)?,
        true_target: comparison.true_target,
        false_target: comparison.false_target,
    })
}

fn certified_phi_layer(
    artifact: &SsaArtifact,
    layer: &NestedWrap32GuardO0PhiLayerFact,
) -> Result<CertifiedNestedWrap32GuardO0PhiLayer, MachineBuildError> {
    if layer.phis.len() != layer.outputs.len() {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let graph = artifact.graph();
    let phis = layer
        .phis
        .iter()
        .copied()
        .zip(layer.outputs.iter().copied())
        .map(|(instruction, output)| {
            let graph_instruction = graph
                .inst(instruction)
                .ok_or(MachineBuildError::MissingInstruction(instruction))?;
            let InstPayload::Phi { predecessors } = &graph_instruction.payload else {
                return Err(MachineBuildError::TopologyMismatch);
            };
            if graph_instruction.output != Some(output)
                || predecessors.len() != graph_instruction.inputs.len()
            {
                return Err(MachineBuildError::TopologyMismatch);
            }
            let inputs = predecessors
                .iter()
                .zip(&graph_instruction.inputs)
                .map(|(predecessor, input)| {
                    graph
                        .block(*predecessor)
                        .map(|block| (block.addr, *input))
                        .ok_or(MachineBuildError::TopologyMismatch)
                })
                .collect::<Result<Vec<_>, MachineBuildError>>()?
                .into_boxed_slice();
            Ok(CertifiedNestedWrap32GuardO0Phi {
                instruction: canonical_instruction(artifact, instruction)?,
                output,
                inputs,
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    Ok(CertifiedNestedWrap32GuardO0PhiLayer {
        block: layer.block,
        predecessors: layer.predecessors,
        phis,
    })
}

fn certified_return(
    artifact: &SsaArtifact,
    returned: NestedWrap32GuardO0ReturnFact,
) -> Result<CertifiedNestedWrap32GuardO0Return, MachineBuildError> {
    Ok(CertifiedNestedWrap32GuardO0Return {
        result_load: certified_access_id(artifact, returned.result_load)?,
        loaded_result: returned.loaded_result,
        low32_copy: canonical_instruction(artifact, returned.low32_copy)?,
        zero_extend: canonical_instruction(artifact, returned.zero_extend)?,
        returned_value: returned.returned_value,
        return_instruction: canonical_instruction(artifact, returned.return_inst)?,
        return_target: returned.return_target,
    })
}

fn certified_instruction_dispositions(
    artifact: &SsaArtifact,
    fact: &NestedWrap32GuardO0Fact,
) -> Result<Box<[CertifiedNestedWrap32GuardO0InstructionDisposition]>, MachineBuildError> {
    if fact.instruction_inventory.len() != fact.dispositions.len()
        || fact
            .instruction_inventory
            .iter()
            .zip(&fact.dispositions)
            .any(|(instruction, disposition)| *instruction != disposition.inst)
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    fact.instruction_inventory
        .iter()
        .copied()
        .zip(&fact.dispositions)
        .map(|(instruction, disposition)| {
            let source = artifact
                .obligations()
                .instruction_for_inst(instruction)
                .ok_or(MachineBuildError::ObligationMismatch(instruction))?;
            Ok(CertifiedNestedWrap32GuardO0InstructionDisposition {
                instruction: source.id,
                source_state: source.state,
                class: disposition.class.into(),
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()
        .map(Vec::into_boxed_slice)
}

fn certified_access_id(
    artifact: &SsaArtifact,
    access: StructuredAccessId,
) -> Result<CertifiedNestedWrap32GuardO0AccessId, MachineBuildError> {
    if !artifact.structured().memory_accesses.contains_key(&access) {
        return Err(MachineBuildError::ObligationMismatch(access.inst));
    }
    Ok(CertifiedNestedWrap32GuardO0AccessId {
        instruction: canonical_instruction(artifact, access.inst)?,
        ordinal: access.ordinal,
    })
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

fn obligation_error(artifact: &SsaArtifact, obligation: SemanticObligationId) -> MachineBuildError {
    MachineBuildError::ObligationMismatch(
        artifact
            .obligations()
            .obligations()
            .get(&obligation)
            .map(|source| source.source_inst)
            .unwrap_or(InstId(u32::MAX)),
    )
}

fn validate_contract(
    certificate: &CertifiedNestedWrap32GuardO0Function,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    if certificate.schema_version != CERTIFICATION_SCHEMA_VERSION
        || certificate.contract_version != CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION
        || source.schema_version() != SEMANTIC_OBLIGATION_SCHEMA_VERSION
        || !source.is_complete()
        || source.source_instruction_count() != INSTRUCTION_COUNT
        || certificate.origin.source() != source
        || !certificate
            .origin
            .matches_retained_source(source, certificate.origin.topology())
        || certificate.origin.topology().entry_addr() != certificate.topology.header
        || certificate.revision_identity.is_empty()
        || certificate.abi.revision_identity != certificate.revision_identity
        || certificate.contract_snapshot.is_empty()
        || !contract_snapshot(certificate)
            .is_ok_and(|snapshot| snapshot.as_slice() == &*certificate.contract_snapshot)
    {
        return Err(());
    }
    validate_abi(certificate)?;
    validate_shape(certificate)?;
    validate_memory(certificate)?;
    validate_instruction_closure(certificate, source)?;
    validate_obligation_closure(certificate, source)
}

fn validate_abi(certificate: &CertifiedNestedWrap32GuardO0Function) -> Result<(), ()> {
    let machine = certificate.origin.machine_context().source();
    let interface = machine.function_interface().ok_or(())?;
    let types = interface.type_graph().ok_or(())?;
    let [integer] = types.types() else {
        return Err(());
    };
    let abi = &certificate.abi;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity() != certificate.revision_identity.as_ref()
        || interface.calling_convention() != "sysv_amd64"
        || interface.parameters().len() != 2
        || interface.parameter_logical_values().len() != 2
        || interface.return_logical_value() != Some(abi.return_logical_value)
        || interface.return_kind()
            != (SourceFunctionReturn::Register {
                storage: abi.return_storage,
            })
        || types.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || !types.aggregates().is_empty()
        || integer.kind() != SourceTypeKind::SignedInteger
        || integer.size_bits() != 32
        || integer.align_bits() != 32
        || abi.parameters.len() != 2
        || abi
            .parameters
            .iter()
            .zip(interface.parameters())
            .zip(interface.parameter_logical_values())
            .enumerate()
            .any(|(index, ((parameter, source), logical))| {
                parameter.index != index as u32
                    || parameter.index != source.index()
                    || parameter.abi_storage != source.storage()
                    || parameter.logical_value != *logical
                    || logical.type_id() != 0
                    || logical.carrier().kind() != SourceCarrierKind::LowBits
                    || logical.carrier().offset_bits() != 0
                    || logical.carrier().size_bits() != 32
            })
        || abi.return_logical_value.type_id() != 0
        || abi.return_logical_value.carrier().kind() != SourceCarrierKind::LowBits
        || abi.return_logical_value.carrier().offset_bits() != 0
        || abi.return_logical_value.carrier().size_bits() != 32
        || !machine.abi_model().is_available()
        || !machine.abi_model().is_coherent()
        || machine.abi_model().argument_registers().len() != 2
        || machine.abi_model().return_registers().len() != 1
    {
        return Err(());
    }
    Ok(())
}

fn validate_shape(certificate: &CertifiedNestedWrap32GuardO0Function) -> Result<(), ()> {
    let topology = certificate.topology;
    let blocks = certificate.origin.topology().blocks();
    let expected_blocks = topology.ordered();
    let expected_instruction_counts = [66usize, 14, 4, 1, 16, 25];
    let saved = certificate.frame.saved_frame_pointer_range;
    let returned = certificate.frame.return_address_range;
    if expected_blocks.into_iter().collect::<BTreeSet<_>>().len() != 6
        || blocks.len() != 6
        || blocks.iter().map(|block| block.addr()).ne(expected_blocks)
        || blocks
            .iter()
            .zip(expected_instruction_counts)
            .any(|(block, count)| block.instructions().len() != count)
        || certificate.frame.instructions.len() != 11
        || saved.offset_from_entry_stack != -8
        || saved.size_bytes != 8
        || returned.offset_from_entry_stack != 0
        || returned.size_bytes != 8
        || certificate.sum.wraps_at_bits != 32
        || certificate.difference.wraps_at_bits != 32
        || certificate.sum.flag_packet.instructions.len() != 6
        || certificate.difference.flag_packet.instructions.len() != 6
        || certificate.sum_comparison.expected != 0x64
        || certificate.difference_comparison.expected != 0x14
        || certificate.sum_comparison.flag_packet.instructions.len() != 6
        || certificate
            .difference_comparison
            .flag_packet
            .instructions
            .len()
            != 6
        || certificate.sum_comparison.block != topology.header
        || certificate.difference_comparison.block != topology.second
        || certificate.sum_comparison.true_target != topology.failure
        || certificate.sum_comparison.false_target != topology.second
        || certificate.difference_comparison.true_target != topology.forwarder
        || certificate.difference_comparison.false_target != topology.success
        || certificate.failure_phis.block != topology.failure
        || certificate.failure_phis.predecessors != [topology.header, topology.forwarder]
        || certificate.failure_phis.phis.len() != FAILURE_PHI_COUNT
        || certificate.exit_phis.block != topology.exit
        || certificate.exit_phis.predecessors != [topology.success, topology.failure]
        || certificate.exit_phis.phis.len() != EXIT_PHI_COUNT
        || certificate.predicates.len() != 2
        || certificate.block_assumptions.len() != 4
        || certificate.returned.return_instruction != certificate.frame.return_instruction
        || certificate.returned.return_target != certificate.frame.return_target
    {
        return Err(());
    }
    for layer in [&certificate.failure_phis, &certificate.exit_phis] {
        if layer.phis.iter().any(|phi| {
            phi.instruction.block_addr != layer.block
                || phi.inputs.len() != 2
                || phi
                    .inputs
                    .iter()
                    .map(|(block, _)| *block)
                    .ne(layer.predecessors)
        }) {
            return Err(());
        }
    }
    let classes = instruction_classes(certificate)?;
    for phi in certificate
        .failure_phis
        .phis
        .iter()
        .chain(&*certificate.exit_phis.phis)
    {
        require_class(
            &classes,
            phi.instruction,
            CertifiedNestedWrap32GuardO0DispositionClass::MachineRelayPhi,
        )?;
    }
    for control in [
        certificate.sum_comparison.branch,
        certificate.difference_comparison.branch,
        certificate.control.success_transfer,
        certificate.control.forwarder_transfer,
    ] {
        require_class(
            &classes,
            control,
            CertifiedNestedWrap32GuardO0DispositionClass::NestedControl,
        )?;
    }
    for instruction in [
        certificate.returned.low32_copy,
        certificate.returned.zero_extend,
        certificate.returned.return_instruction,
    ] {
        require_class(
            &classes,
            instruction,
            CertifiedNestedWrap32GuardO0DispositionClass::ReturnComposition,
        )?;
    }
    Ok(())
}

fn validate_memory(certificate: &CertifiedNestedWrap32GuardO0Function) -> Result<(), ()> {
    let objects = certificate
        .objects
        .iter()
        .map(|object| object.object)
        .collect::<BTreeSet<_>>();
    let accesses = certificate
        .memory_accesses
        .iter()
        .map(|access| (access.id, access))
        .collect::<BTreeMap<_, _>>();
    if objects.len() != certificate.objects.len()
        || accesses.len() != MEMORY_ACCESS_COUNT
        || accesses.len() != certificate.memory_accesses.len()
        || certificate
            .memory_accesses
            .windows(2)
            .any(|window| window[0].id >= window[1].id)
        || certificate.memory_accesses.iter().any(|access| {
            !objects.contains(&access.object)
                || access
                    .uses
                    .iter()
                    .any(|memory| memory.location.object != access.object)
                || access
                    .definitions
                    .iter()
                    .any(|memory| memory.location.object != access.object)
        })
        || certificate.memory_phis.iter().any(|phi| {
            !objects.contains(&phi.object)
                || phi.location.object != phi.object
                || phi.output_version.object != phi.object
                || phi
                    .inputs
                    .iter()
                    .any(|(_, version)| version.object != phi.object)
        })
    {
        return Err(());
    }
    let slots = &certificate.slots;
    if slots.parameter_homes.len() != 2
        || !slot_shape(&slots.parameter_homes[0], -8, -16, 3)
        || !slot_shape(&slots.parameter_homes[1], -12, -20, 7)
        || !slot_shape(&slots.sum, -16, -24, 2)
        || !slot_shape(&slots.difference, -20, -28, 2)
        || !slot_shape(&slots.result, -4, -12, 3)
    {
        return Err(());
    }
    let slot_objects = slots
        .parameter_homes
        .iter()
        .chain([&slots.sum, &slots.difference, &slots.result])
        .map(|slot| slot.object)
        .collect::<BTreeSet<_>>();
    if slot_objects.len() != 5 || !slot_objects.iter().all(|object| objects.contains(object)) {
        return Err(());
    }
    let slot_accesses = slots
        .parameter_homes
        .iter()
        .chain([&slots.sum, &slots.difference, &slots.result])
        .flat_map(|slot| slot.accesses.iter())
        .collect::<Vec<_>>();
    if slot_accesses.len() != 17
        || slot_accesses.iter().any(|slot_access| {
            accesses.get(&slot_access.access).is_none_or(|access| {
                !access.provenance_complete
                    || access.object != slot_access.object
                    || access.value != slot_access.value
                    || access.uses.len() != slot_access.memory_uses
                    || access.definitions.len() != slot_access.memory_definitions
                    || access.width_bytes != 4
            })
        })
        || accesses
            .get(&certificate.result.success_store)
            .is_none_or(|access| {
                !access.is_write
                    || access.block != certificate.topology.success
                    || access.address != certificate.result.success_address
                    || access.value != Some(certificate.result.success_value)
            })
        || accesses
            .get(&certificate.result.failure_store)
            .is_none_or(|access| {
                !access.is_write
                    || access.block != certificate.topology.failure
                    || access.address != certificate.result.failure_address
                    || access.value != Some(certificate.result.failure_value)
            })
        || accesses
            .get(&certificate.returned.result_load)
            .is_none_or(|access| {
                access.is_write
                    || access.block != certificate.topology.exit
                    || access.value != Some(certificate.returned.loaded_result)
            })
    {
        return Err(());
    }
    Ok(())
}

fn slot_shape(
    slot: &CertifiedNestedWrap32GuardO0Slot,
    frame_pointer_offset: i64,
    entry_stack_offset: i64,
    access_count: usize,
) -> bool {
    slot.base == StackAddressBase::FramePointer
        && slot.frame_pointer_offset == frame_pointer_offset
        && slot.entry_stack_offset == entry_stack_offset
        && slot.size_bytes == 4
        && slot.accesses.len() == access_count
}

fn validate_instruction_closure(
    certificate: &CertifiedNestedWrap32GuardO0Function,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let certified = certificate
        .instruction_dispositions
        .iter()
        .map(|disposition| disposition.instruction)
        .collect::<BTreeSet<_>>();
    let source_instructions = source
        .instructions()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let topology_instructions = certificate
        .origin
        .topology()
        .blocks()
        .iter()
        .flat_map(|block| block.instructions().iter().copied())
        .collect::<BTreeSet<_>>();
    if certificate.instruction_dispositions.len() != INSTRUCTION_COUNT
        || certified.len() != INSTRUCTION_COUNT
        || certified != source_instructions
        || certified != topology_instructions
        || certificate
            .instruction_dispositions
            .iter()
            .any(|disposition| {
                source
                    .instructions()
                    .get(&disposition.instruction)
                    .is_none_or(|source| {
                        source.state != disposition.source_state
                            || (source.state == SemanticInstructionState::ProvenDead
                                && !source.obligations.is_empty())
                    })
            })
    {
        return Err(());
    }
    Ok(())
}

fn validate_obligation_closure(
    certificate: &CertifiedNestedWrap32GuardO0Function,
    source: &SemanticObligationInventory,
) -> Result<(), ()> {
    let classes = instruction_classes(certificate)?;
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
            .windows(2)
            .any(|window| window[0].0 >= window[1].0)
        || certificate
            .obligation_dispositions
            .iter()
            .any(|(obligation, class)| {
                classes.get(&obligation.instruction) != Some(class)
                    || source
                        .obligations()
                        .get(obligation)
                        .is_none_or(|source_obligation| {
                            source
                                .instructions()
                                .get(&obligation.instruction)
                                .is_none_or(|instruction| {
                                    instruction.inst != source_obligation.source_inst
                                        || !instruction.obligations.contains(obligation)
                                })
                        })
            })
    {
        return Err(());
    }
    Ok(())
}

fn instruction_classes(
    certificate: &CertifiedNestedWrap32GuardO0Function,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedNestedWrap32GuardO0DispositionClass>, ()> {
    let classes = certificate
        .instruction_dispositions
        .iter()
        .map(|disposition| (disposition.instruction, disposition.class))
        .collect::<BTreeMap<_, _>>();
    (classes.len() == certificate.instruction_dispositions.len())
        .then_some(classes)
        .ok_or(())
}

fn require_class(
    classes: &BTreeMap<CanonicalInstructionId, CertifiedNestedWrap32GuardO0DispositionClass>,
    instruction: CanonicalInstructionId,
    expected: CertifiedNestedWrap32GuardO0DispositionClass,
) -> Result<(), ()> {
    (classes.get(&instruction) == Some(&expected))
        .then_some(())
        .ok_or(())
}

fn contract_snapshot(
    certificate: &CertifiedNestedWrap32GuardO0Function,
) -> Result<Vec<u8>, postcard::Error> {
    #[derive(Serialize)]
    struct Snapshot<'a> {
        schema_version: u32,
        contract_version: u32,
        origin: &'a CertifiedArtifactOrigin,
        revision_identity: &'a [u8],
        topology: CertifiedNestedWrap32GuardO0Topology,
        abi: &'a CertifiedNestedWrap32GuardO0Abi,
        frame: &'a CertifiedNestedWrap32GuardO0Frame,
        objects: &'a [CertifiedNestedWrap32GuardO0Object],
        memory_accesses: &'a [CertifiedNestedWrap32GuardO0MemoryAccess],
        memory_phis: &'a [CertifiedNestedWrap32GuardO0MemoryPhi],
        slots: &'a CertifiedNestedWrap32GuardO0Slots,
        sum: &'a CertifiedNestedWrap32GuardO0Arithmetic,
        difference: &'a CertifiedNestedWrap32GuardO0Arithmetic,
        sum_comparison: &'a CertifiedNestedWrap32GuardO0Comparison,
        difference_comparison: &'a CertifiedNestedWrap32GuardO0Comparison,
        predicates: &'a [CertifiedNestedWrap32GuardO0Predicate],
        block_assumptions: &'a [CertifiedNestedWrap32GuardO0BlockAssumption],
        control: CertifiedNestedWrap32GuardO0Control,
        failure_phis: &'a CertifiedNestedWrap32GuardO0PhiLayer,
        exit_phis: &'a CertifiedNestedWrap32GuardO0PhiLayer,
        result: &'a CertifiedNestedWrap32GuardO0ResultCarrier,
        returned: &'a CertifiedNestedWrap32GuardO0Return,
        instruction_dispositions: &'a [CertifiedNestedWrap32GuardO0InstructionDisposition],
        obligation_dispositions: &'a [(
            SemanticObligationId,
            CertifiedNestedWrap32GuardO0DispositionClass,
        )],
    }
    postcard::to_stdvec(&Snapshot {
        schema_version: certificate.schema_version,
        contract_version: certificate.contract_version,
        origin: &certificate.origin,
        revision_identity: &certificate.revision_identity,
        topology: certificate.topology,
        abi: &certificate.abi,
        frame: &certificate.frame,
        objects: &certificate.objects,
        memory_accesses: &certificate.memory_accesses,
        memory_phis: &certificate.memory_phis,
        slots: &certificate.slots,
        sum: &certificate.sum,
        difference: &certificate.difference,
        sum_comparison: &certificate.sum_comparison,
        difference_comparison: &certificate.difference_comparison,
        predicates: &certificate.predicates,
        block_assumptions: &certificate.block_assumptions,
        control: certificate.control,
        failure_phis: &certificate.failure_phis,
        exit_phis: &certificate.exit_phis,
        result: &certificate.result,
        returned: &certificate.returned,
        instruction_dispositions: &certificate.instruction_dispositions,
        obligation_dispositions: &certificate.obligation_dispositions,
    })
}
