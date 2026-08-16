//! Bounded differential falsification for the admitted semantic-C block body.
//!
//! This checker constructs certification and semantic-C layers internally from
//! one prepared artifact, then evaluates one open-exit block independently
//! from canonical SSA and the typed semantic-C AST. Closed conditional-return
//! checks also interpret the strict rendered-C control shape. A successful
//! finite run means only that no mismatch was observed for the supplied state
//! and bounds. It is not a proof, a typed-output seal, or execution authority
//! for an open control-flow port.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedControlTruthiness,
    CertifiedFramePreservation, CertifiedFrameRestore, CertifiedMachineProjection,
    CertifiedMemoryExecutionPolicy, CertifiedMemoryStatement, CertifiedMemoryStatementKind,
    CertifiedPrivateFrameConditionalArm, CertifiedPrivateFrameConditionalJoin,
    CertifiedPrivateFrameVersionDefinition,
};
use r2ssa::{
    BlockTerminator, CallBoundarySlot, CallSiteId, CanonicalInstructionId,
    CanonicalInstructionSite, CanonicalStorageSpace, InstPayload, MachineAddressProvenance,
    MachineAddressSpace, MachineArithmeticFlagOp, MachineArithmeticMode, MachineArithmeticOp,
    MachineBitwiseOp, MachineBooleanOp, MachineCastKind, MachineComparisonOp, MachineExprId,
    MachineExprKind, MachineMemoryEndianness, MachineOvershiftBehavior, MachineShiftKind,
    MachineSignedness, MachineStackBase, MachineType, MachineValueBinding, MachineValueUse,
    ObjectId, SSAOp, SemanticInstructionState, SourceCallResult, SourceCallSiteIdentity,
    SourceCarrierKind, SourceFunctionReturn, SourceTypeKind, SsaArtifact, StructuredAccessId,
    TrustedSsaArtifact, ValueId,
};
use serde::ser::{SerializeSeq, SerializeStruct};
use serde::{Serialize, Serializer};

use crate::certified_call::CertifiedDirectCallBlockRegion;
use crate::certified_if_return::{
    CertifiedConditionalReturnArm, CertifiedConditionalReturnFunction,
};
use crate::certified_private_frame_join::{
    CertifiedPrivateFrameConditionalJoinFunction, CertifiedPrivateFrameJoinValue,
    CertifiedPrivateFrameJoinValueOrigin,
};
use crate::certified_region::{CertifiedSingleBlockAccounting, RegionObligationDisposition};
use crate::certified_return::CertifiedTerminalReturnBlockRegion;
use crate::semantic_c::{
    SemanticCCallArgumentValue, SemanticCDirectCall, SemanticCExprId, SemanticCExprKind,
    SemanticCExpressionLayer, SemanticCReturn,
};
use crate::semantic_function::CertifiedSemanticCFunction;
use crate::semantic_memory_function::CertifiedMemorySemanticCFunction;
use crate::semantic_stmt::SemanticCBlockStepLayer;

pub const SEMANTIC_DIFFERENTIAL_SCHEMA_VERSION: u32 = 8;
pub const SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION: u32 = 8;

fn hex_bytes(bytes: &[u8]) -> String {
    use std::fmt::Write as _;

    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}

fn serialize_u64_hex<S: Serializer>(value: &u64, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&format!("0x{value:016x}"))
}

fn serialize_canonical_instruction_id<S: Serializer>(
    value: &CanonicalInstructionId,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    CanonicalInstructionIdWire::from(*value).serialize(serializer)
}

fn serialize_canonical_instruction_ids<S: Serializer>(
    values: &[CanonicalInstructionId],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut sequence = serializer.serialize_seq(Some(values.len()))?;
    for value in values {
        sequence.serialize_element(&CanonicalInstructionIdWire::from(*value))?;
    }
    sequence.end()
}

#[derive(Serialize)]
struct CanonicalInstructionIdWire {
    block_addr_hex: String,
    site: CanonicalInstructionSiteWire,
}

impl From<CanonicalInstructionId> for CanonicalInstructionIdWire {
    fn from(value: CanonicalInstructionId) -> Self {
        let site = match value.site {
            CanonicalInstructionSite::Op(ordinal) => CanonicalInstructionSiteWire::Op {
                ordinal_hex: format!("0x{ordinal:016x}"),
            },
            CanonicalInstructionSite::Phi(storage) => CanonicalInstructionSiteWire::Phi {
                space: canonical_storage_space_name(storage.space),
                offset_hex: format!("0x{:016x}", storage.offset),
                size_bytes: storage.size,
            },
            CanonicalInstructionSite::NativeSpan {
                instruction_addr,
                size,
            } => CanonicalInstructionSiteWire::NativeSpan {
                instruction_addr_hex: format!("0x{instruction_addr:016x}"),
                size_bytes: size,
            },
        };
        Self {
            block_addr_hex: format!("0x{:016x}", value.block_addr),
            site,
        }
    }
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum CanonicalInstructionSiteWire {
    Op {
        ordinal_hex: String,
    },
    Phi {
        space: String,
        offset_hex: String,
        size_bytes: u32,
    },
    NativeSpan {
        instruction_addr_hex: String,
        size_bytes: u32,
    },
}

fn canonical_storage_space_name(space: CanonicalStorageSpace) -> String {
    match space {
        CanonicalStorageSpace::Ram => "ram".to_string(),
        CanonicalStorageSpace::Register => "register".to_string(),
        CanonicalStorageSpace::Unique => "unique".to_string(),
        CanonicalStorageSpace::Constant => "constant".to_string(),
        CanonicalStorageSpace::Custom(id) => format!("custom:{id}"),
        CanonicalStorageSpace::Unknown => "unknown".to_string(),
    }
}

fn machine_address_space_name(space: MachineAddressSpace) -> String {
    match space {
        MachineAddressSpace::Ram => "ram".to_string(),
        MachineAddressSpace::Register => "register".to_string(),
        MachineAddressSpace::Unique => "unique".to_string(),
        MachineAddressSpace::Constant => "constant".to_string(),
        MachineAddressSpace::Custom(id) => format!("custom:{id}"),
    }
}

fn serialize_machine_address_space<S: Serializer>(
    value: &MachineAddressSpace,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&machine_address_space_name(*value))
}

fn serialize_machine_type<S: Serializer>(
    value: &MachineType,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    #[derive(Serialize)]
    #[serde(tag = "kind", rename_all = "snake_case")]
    enum MachineTypeWire {
        Bool {
            storage_bits: u32,
        },
        Integer {
            width_bits: u32,
            signedness: &'static str,
        },
        Address {
            width_bits: u32,
            space: String,
            provenance: MachineAddressProvenanceWire,
        },
    }
    #[derive(Serialize)]
    #[serde(tag = "kind", rename_all = "snake_case")]
    enum MachineAddressProvenanceWire {
        Unknown,
        Parameter { index: u32 },
        Stack { base: &'static str, offset: String },
        Global { address_hex: String },
        Derived { value: ValueId, width_bits: u32 },
    }
    let provenance = |value| match value {
        MachineAddressProvenance::Unknown => MachineAddressProvenanceWire::Unknown,
        MachineAddressProvenance::Parameter { index } => {
            MachineAddressProvenanceWire::Parameter { index }
        }
        MachineAddressProvenance::Stack { base, offset } => MachineAddressProvenanceWire::Stack {
            base: match base {
                MachineStackBase::FramePointer => "frame_pointer",
                MachineStackBase::StackPointer => "stack_pointer",
            },
            offset: offset.to_string(),
        },
        MachineAddressProvenance::Global { address } => MachineAddressProvenanceWire::Global {
            address_hex: format!("0x{address:016x}"),
        },
        MachineAddressProvenance::Derived { base } => MachineAddressProvenanceWire::Derived {
            value: base.value(),
            width_bits: base.width_bits(),
        },
    };
    let wire = match value {
        MachineType::Bool { storage_bits } => MachineTypeWire::Bool {
            storage_bits: *storage_bits,
        },
        MachineType::Integer {
            width_bits,
            signedness,
        } => MachineTypeWire::Integer {
            width_bits: *width_bits,
            signedness: match signedness {
                MachineSignedness::Unsigned => "unsigned",
                MachineSignedness::Signed => "signed",
            },
        },
        MachineType::Address {
            width_bits,
            space,
            provenance: address_provenance,
        } => MachineTypeWire::Address {
            width_bits: *width_bits,
            space: machine_address_space_name(*space),
            provenance: provenance(*address_provenance),
        },
    };
    wire.serialize(serializer)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DifferentialBitVector {
    width_bits: u32,
    bits: u64,
}

impl DifferentialBitVector {
    pub fn new(width_bits: u32, bits: u64) -> Option<Self> {
        supported_width(width_bits).then(|| Self {
            width_bits,
            bits: bits & width_mask(width_bits),
        })
    }

    pub const fn width_bits(self) -> u32 {
        self.width_bits
    }

    pub const fn bits(self) -> u64 {
        self.bits
    }
}

impl Serialize for DifferentialBitVector {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("DifferentialBitVector", 2)?;
        state.serialize_field("width_bits", &self.width_bits)?;
        state.serialize_field("bits_hex", &format!("0x{:016x}", self.bits))?;
        state.end()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DifferentialMemoryLocation {
    pub space: MachineAddressSpace,
    pub byte_address: u64,
}

impl Serialize for DifferentialMemoryLocation {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("DifferentialMemoryLocation", 2)?;
        state.serialize_field("space", &machine_address_space_name(self.space))?;
        state.serialize_field("byte_address_hex", &format!("0x{:016x}", self.byte_address))?;
        state.end()
    }
}

/// Exact, non-hashed serialization of the certified artifact origin.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialArtifactIdentity {
    certification_schema_version: u32,
    exact_origin_postcard_hex: String,
}

/// Exact semantic-C candidate and evaluator contract used for one run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DifferentialCandidateKind {
    BlockStepLayer,
    TerminalReturnRegion,
    MemoryTerminalReturnFunction,
    DirectCallRegion,
    ConditionalReturnFunction,
    PrivateFrameConditionalJoinFunction,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialCandidateIdentity {
    evaluator_contract_version: u32,
    candidate_kind: DifferentialCandidateKind,
    exact_candidate_postcard_hex: String,
}

impl DifferentialCandidateIdentity {
    fn from_layer(layer: &SemanticCBlockStepLayer) -> Result<Self, String> {
        let candidate_kind = DifferentialCandidateKind::BlockStepLayer;
        let encoded = postcard::to_stdvec(&(candidate_kind, layer))
            .map_err(|error| format!("semantic layer encoding failed: {error}"))?;
        Ok(Self {
            evaluator_contract_version: SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION,
            candidate_kind,
            exact_candidate_postcard_hex: hex_bytes(&encoded),
        })
    }

    fn from_terminal_region(region: &CertifiedTerminalReturnBlockRegion) -> Result<Self, String> {
        let candidate_kind = DifferentialCandidateKind::TerminalReturnRegion;
        let encoded = postcard::to_stdvec(&(candidate_kind, region))
            .map_err(|error| format!("terminal semantic region encoding failed: {error}"))?;
        Ok(Self {
            evaluator_contract_version: SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION,
            candidate_kind,
            exact_candidate_postcard_hex: hex_bytes(&encoded),
        })
    }

    fn from_memory_terminal_return_function(
        function: &CertifiedMemorySemanticCFunction,
    ) -> Result<Self, String> {
        let candidate_kind = DifferentialCandidateKind::MemoryTerminalReturnFunction;
        let encoded = postcard::to_stdvec(&(candidate_kind, function))
            .map_err(|error| format!("memory terminal-return function encoding failed: {error}"))?;
        Ok(Self {
            evaluator_contract_version: SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION,
            candidate_kind,
            exact_candidate_postcard_hex: hex_bytes(&encoded),
        })
    }

    fn from_direct_call_region(region: &CertifiedDirectCallBlockRegion) -> Result<Self, String> {
        let candidate_kind = DifferentialCandidateKind::DirectCallRegion;
        let encoded = postcard::to_stdvec(&(candidate_kind, region))
            .map_err(|error| format!("direct-call semantic region encoding failed: {error}"))?;
        Ok(Self {
            evaluator_contract_version: SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION,
            candidate_kind,
            exact_candidate_postcard_hex: hex_bytes(&encoded),
        })
    }

    fn from_conditional_return_function(
        function: &CertifiedConditionalReturnFunction,
    ) -> Result<Self, String> {
        let candidate_kind = DifferentialCandidateKind::ConditionalReturnFunction;
        let encoded = postcard::to_stdvec(&(candidate_kind, function))
            .map_err(|error| format!("conditional-return function encoding failed: {error}"))?;
        Ok(Self {
            evaluator_contract_version: SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION,
            candidate_kind,
            exact_candidate_postcard_hex: hex_bytes(&encoded),
        })
    }

    fn from_private_frame_conditional_join_function(
        function: &CertifiedPrivateFrameConditionalJoinFunction,
    ) -> Result<Self, String> {
        let candidate_kind = DifferentialCandidateKind::PrivateFrameConditionalJoinFunction;
        let encoded = postcard::to_stdvec(&(candidate_kind, function)).map_err(|error| {
            format!("private-frame conditional-join function encoding failed: {error}")
        })?;
        Ok(Self {
            evaluator_contract_version: SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION,
            candidate_kind,
            exact_candidate_postcard_hex: hex_bytes(&encoded),
        })
    }

    pub const fn evaluator_contract_version(&self) -> u32 {
        self.evaluator_contract_version
    }

    pub const fn candidate_kind(&self) -> DifferentialCandidateKind {
        self.candidate_kind
    }

    pub fn exact_candidate_postcard_hex(&self) -> &str {
        &self.exact_candidate_postcard_hex
    }
}

impl DifferentialArtifactIdentity {
    fn from_origin(origin: &CertifiedArtifactOrigin) -> Result<Self, String> {
        let encoded = postcard::to_stdvec(origin)
            .map_err(|error| format!("artifact origin encoding failed: {error}"))?;
        Ok(Self {
            certification_schema_version: CERTIFICATION_SCHEMA_VERSION,
            exact_origin_postcard_hex: hex_bytes(&encoded),
        })
    }

    pub const fn certification_schema_version(&self) -> u32 {
        self.certification_schema_version
    }

    pub fn exact_origin_postcard_hex(&self) -> &str {
        &self.exact_origin_postcard_hex
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DifferentialState {
    origin: CertifiedArtifactOrigin,
    artifact_identity: DifferentialArtifactIdentity,
    /// Exact artifact-local values available at the selected block boundary.
    values: BTreeMap<ValueId, DifferentialBitVector>,
    /// Readable and writable byte domain. Access outside this map is incomplete,
    /// never an implicit zero byte or an invented machine trap.
    memory: BTreeMap<DifferentialMemoryLocation, u8>,
}

impl DifferentialState {
    pub fn for_artifact(trusted: &TrustedSsaArtifact) -> Result<Self, String> {
        let certified = CertifiedMachineProjection::from_artifact(trusted)
            .map_err(|error| format!("artifact certification failed: {error}"))?;
        let origin = certified.origin().clone();
        let artifact_identity = DifferentialArtifactIdentity::from_origin(&origin)?;
        Ok(Self {
            origin,
            artifact_identity,
            values: BTreeMap::new(),
            memory: BTreeMap::new(),
        })
    }

    pub const fn artifact_identity(&self) -> &DifferentialArtifactIdentity {
        &self.artifact_identity
    }

    pub const fn values(&self) -> &BTreeMap<ValueId, DifferentialBitVector> {
        &self.values
    }

    pub const fn memory(&self) -> &BTreeMap<DifferentialMemoryLocation, u8> {
        &self.memory
    }

    pub fn set_value(
        &mut self,
        value: ValueId,
        bitvector: DifferentialBitVector,
    ) -> Option<DifferentialBitVector> {
        self.values.insert(value, bitvector)
    }

    pub fn set_memory_byte(
        &mut self,
        location: DifferentialMemoryLocation,
        value: u8,
    ) -> Option<u8> {
        self.memory.insert(location, value)
    }
}

impl Serialize for DifferentialState {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        #[derive(Serialize)]
        struct ValueRecord {
            value: ValueId,
            bitvector: DifferentialBitVector,
        }
        #[derive(Serialize)]
        struct ByteRecord {
            location: DifferentialMemoryLocation,
            value: u8,
        }
        let values = self
            .values
            .iter()
            .map(|(value, bitvector)| ValueRecord {
                value: *value,
                bitvector: *bitvector,
            })
            .collect::<Vec<_>>();
        let memory = self
            .memory
            .iter()
            .map(|(location, value)| ByteRecord {
                location: *location,
                value: *value,
            })
            .collect::<Vec<_>>();
        let mut state = serializer.serialize_struct("DifferentialState", 3)?;
        state.serialize_field("artifact_identity", &self.artifact_identity)?;
        state.serialize_field("values", &values)?;
        state.serialize_field("memory", &memory)?;
        state.end()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct DifferentialLimits {
    pub max_source_steps: u32,
    pub max_expression_nodes: u32,
    pub max_memory_bytes: u32,
}

impl Default for DifferentialLimits {
    fn default() -> Self {
        Self {
            max_source_steps: 32,
            max_expression_nodes: 128,
            max_memory_bytes: 64,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DifferentialSide {
    SourceSsa,
    SemanticC,
    Both,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DifferentialConclusion {
    NoMismatchObserved,
    MismatchObserved,
    Incomplete,
    InvalidInput,
    InvalidArtifact,
    HarnessFailure,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DifferentialCandidateAdmission {
    NotEvaluated,
    Admitted,
    Residual,
    Refused,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DifferentialMismatchKind {
    BoundaryOutcome,
    OutputSequence,
    MemoryEventSequence,
    FinalMemory,
    ExecutionOutcome,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialMismatch {
    pub kind: DifferentialMismatchKind,
    pub index: Option<u32>,
    pub source: String,
    pub semantic_c: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DifferentialCaseDisposition {
    Matched,
    SemanticMismatch {
        mismatch: DifferentialMismatch,
    },
    CandidateNotAdmitted {
        admission: DifferentialCandidateAdmission,
        reason: String,
    },
    InterpreterUnsupported {
        side: DifferentialSide,
        reason: String,
    },
    MemoryOutOfDomain {
        side: DifferentialSide,
        location: DifferentialMemoryLocation,
    },
    MissingBoundaryInput {
        side: DifferentialSide,
        value: ValueId,
    },
    BudgetExceeded {
        side: DifferentialSide,
    },
    InconclusiveExecutionPair {
        source: String,
        semantic_c: String,
    },
    InvalidInput {
        reason: String,
    },
    InvalidArtifact {
        reason: String,
    },
    HarnessFailure {
        reason: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DifferentialMemoryEventKind {
    Read,
    Write,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialMemoryEvent {
    #[serde(serialize_with = "serialize_canonical_instruction_id")]
    pub producer: CanonicalInstructionId,
    pub access: StructuredAccessId,
    pub object: ObjectId,
    pub kind: DifferentialMemoryEventKind,
    #[serde(serialize_with = "serialize_machine_address_space")]
    pub space: MachineAddressSpace,
    #[serde(serialize_with = "serialize_u64_hex")]
    pub byte_address: u64,
    pub width_bits: u32,
    pub endianness: MachineMemoryEndianness,
    pub value: DifferentialBitVector,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialCallArgument {
    pub slot: CallBoundarySlot,
    pub value: DifferentialBitVector,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DifferentialBoundaryOutcome {
    /// The block body completed, but its exit remains owned by a future control
    /// region and is not interpreted as a return or function termination.
    OpenBlockExit {
        #[serde(serialize_with = "serialize_u64_hex")]
        block_addr: u64,
    },
    Returned {
        values: Box<[DifferentialBitVector]>,
    },
    /// Evaluation stops at the exact call boundary. The callee and all
    /// post-call register or memory state remain outside this contract.
    OpenDirectCall {
        #[serde(serialize_with = "serialize_canonical_instruction_id")]
        producer: CanonicalInstructionId,
        call_site: CallSiteId,
        raw_identity: SourceCallSiteIdentity,
        interface_revision: Box<[u8]>,
        #[serde(serialize_with = "serialize_u64_hex")]
        target: u64,
        #[serde(serialize_with = "serialize_u64_hex")]
        fallthrough: u64,
        calling_convention: String,
        arguments: Box<[DifferentialCallArgument]>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialObservedValue {
    pub binding: MachineValueBinding,
    #[serde(serialize_with = "serialize_canonical_instruction_id")]
    pub producer: CanonicalInstructionId,
    #[serde(serialize_with = "serialize_machine_type")]
    pub ty: MachineType,
    #[serde(serialize_with = "serialize_canonical_instruction_ids")]
    pub source_instructions: Box<[CanonicalInstructionId]>,
    pub bitvector: DifferentialBitVector,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialObservedByte {
    pub location: DifferentialMemoryLocation,
    pub value: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialObservedRun {
    pub outcome: DifferentialBoundaryOutcome,
    pub outputs: Box<[DifferentialObservedValue]>,
    pub memory_events: Box<[DifferentialMemoryEvent]>,
    pub final_memory: Box<[DifferentialObservedByte]>,
}

/// Observable prefix retained when an interpreter stops before block exit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialObservedTrace {
    pub memory_events: Box<[DifferentialMemoryEvent]>,
    pub final_memory: Box<[DifferentialObservedByte]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DifferentialReport {
    schema_version: u32,
    /// Exact identity of the requested artifact. Certification failures leave
    /// this absent instead of incorrectly substituting the initial-state
    /// artifact identity.
    artifact_identity: Option<DifferentialArtifactIdentity>,
    candidate_identity: Option<DifferentialCandidateIdentity>,
    initial_state: DifferentialState,
    limits: DifferentialLimits,
    admission: DifferentialCandidateAdmission,
    #[serde(serialize_with = "serialize_u64_hex")]
    block_addr: u64,
    conclusion: DifferentialConclusion,
    disposition: DifferentialCaseDisposition,
    source: Option<DifferentialObservedRun>,
    semantic_c: Option<DifferentialObservedRun>,
    source_prefix: Option<DifferentialObservedTrace>,
    semantic_c_prefix: Option<DifferentialObservedTrace>,
}

impl DifferentialReport {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn block_addr(&self) -> u64 {
        self.block_addr
    }

    pub const fn artifact_identity(&self) -> Option<&DifferentialArtifactIdentity> {
        self.artifact_identity.as_ref()
    }

    pub const fn initial_state(&self) -> &DifferentialState {
        &self.initial_state
    }

    pub const fn candidate_identity(&self) -> Option<&DifferentialCandidateIdentity> {
        self.candidate_identity.as_ref()
    }

    pub const fn limits(&self) -> DifferentialLimits {
        self.limits
    }

    pub const fn admission(&self) -> DifferentialCandidateAdmission {
        self.admission
    }

    pub const fn conclusion(&self) -> DifferentialConclusion {
        self.conclusion
    }

    pub const fn disposition(&self) -> &DifferentialCaseDisposition {
        &self.disposition
    }

    pub const fn source(&self) -> Option<&DifferentialObservedRun> {
        self.source.as_ref()
    }

    pub const fn semantic_c(&self) -> Option<&DifferentialObservedRun> {
        self.semantic_c.as_ref()
    }

    pub const fn source_prefix(&self) -> Option<&DifferentialObservedTrace> {
        self.source_prefix.as_ref()
    }

    pub const fn semantic_c_prefix(&self) -> Option<&DifferentialObservedTrace> {
        self.semantic_c_prefix.as_ref()
    }
}

/// Execute one admitted open-exit block from a common initial state.
///
/// Certification, accounting, and the typed AST are constructed internally so
/// artifact-local handles cannot be paired with a foreign source graph.
pub fn check_block_differential(
    trusted: &TrustedSsaArtifact,
    block_addr: u64,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> DifferentialReport {
    let artifact = trusted.artifact();
    let certified = match CertifiedMachineProjection::from_artifact(trusted) {
        Ok(certified) => certified,
        Err(error) => {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("artifact certification failed: {error}"),
                },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let requested_artifact_identity =
        match DifferentialArtifactIdentity::from_origin(certified.origin()) {
            Ok(identity) => identity,
            Err(reason) => {
                let mut report = issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
                report.artifact_identity = None;
                return report;
            }
        };
    let invalid_input = |reason| {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::InvalidInput,
            DifferentialCaseDisposition::InvalidInput { reason },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity.clone());
        report
    };
    if limits.max_source_steps == 0
        || limits.max_expression_nodes == 0
        || limits.max_memory_bytes == 0
    {
        return invalid_input("differential limits must all be nonzero".to_string());
    }
    if initial.origin != *certified.origin() {
        return invalid_input(
            "differential state belongs to a different certified artifact origin".to_string(),
        );
    }
    if let Err(reason) = validate_initial_state(artifact, block_addr, initial) {
        return invalid_input(reason);
    }
    if initial.memory.len() > limits.max_memory_bytes as usize {
        return issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
    }
    let accounting =
        match CertifiedSingleBlockAccounting::from_projection_block(&certified, block_addr) {
            Ok(accounting) => accounting,
            Err(error) => {
                return issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::Refused,
                    DifferentialConclusion::InvalidArtifact,
                    DifferentialCaseDisposition::InvalidArtifact {
                        reason: format!("block accounting failed: {error}"),
                    },
                    None,
                    None,
                );
            }
        };
    let audit = accounting.audit();
    if !audit.has_exact_source_accounting() {
        return issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Refused,
            DifferentialConclusion::InvalidArtifact,
            DifferentialCaseDisposition::InvalidArtifact {
                reason: format!("block accounting audit failed: {:?}", audit.invalid()),
            },
            None,
            None,
        );
    }
    if audit.has_residuals()
        || accounting.mappings().iter().any(|mapping| {
            matches!(
                mapping.disposition(),
                RegionObligationDisposition::Residualized { .. }
            )
        })
    {
        return candidate_not_admitted(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Residual,
            "selected block contains residual semantic obligations".to_string(),
        );
    }
    if !accounting.direct_controls().is_empty() || !accounting.conditional_controls().is_empty() {
        return candidate_not_admitted(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Residual,
            "typed block-step AST has no executable control node".to_string(),
        );
    }
    if !accounting.return_controls().is_empty() {
        return candidate_not_admitted(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Residual,
            "open-exit differential contract has no terminal return node".to_string(),
        );
    }
    if !accounting.direct_calls().is_empty() {
        return candidate_not_admitted(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Residual,
            "open-exit differential contract has no direct-call boundary node".to_string(),
        );
    }
    let layer = match SemanticCBlockStepLayer::from_accounting(accounting) {
        Ok(layer) => layer,
        Err(error) => {
            return issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure {
                    reason: format!("semantic block layer failed: {error}"),
                },
                None,
                None,
            );
        }
    };
    let candidate_identity = match DifferentialCandidateIdentity::from_layer(&layer) {
        Ok(identity) => identity,
        Err(reason) => {
            return issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure { reason },
                None,
                None,
            );
        }
    };
    if !layer.audit().has_exact_source_order() {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: "semantic block source-order audit failed".to_string(),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if let Err(reason) = audit_semantic_translation(&certified, &layer) {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure { reason },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if layer.steps().len() > limits.max_source_steps as usize {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let mut memory_execution_bytes = 0_u32;
    for step in layer.steps() {
        let Some(reference) = step.memory() else {
            continue;
        };
        let Some(statement) = layer.resolve_memory_statement(reference) else {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure {
                    reason: "memory step became unresolved after source-order audit".to_string(),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        };
        let Some(bytes) = statement.width_bits().checked_add(7).map(|width| width / 8) else {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: "memory execution width overflow".to_string(),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        };
        let Some(total) = memory_execution_bytes.checked_add(bytes) else {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: "memory execution byte budget overflow".to_string(),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        };
        memory_execution_bytes = total;
    }
    if memory_execution_bytes > limits.max_memory_bytes {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if layer
        .steps()
        .iter()
        .any(|step| matches!(step.state(), SemanticInstructionState::UnsupportedUnknown))
    {
        let mut report = candidate_not_admitted(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Residual,
            "selected block contains unsupported source semantics".to_string(),
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }

    let source = execute_source(artifact, &layer, initial, limits);
    let semantic_c = execute_semantic(artifact, &layer, initial, limits);
    finish_report(
        initial,
        Some(candidate_identity),
        block_addr,
        limits,
        source,
        semantic_c,
    )
}

/// Execute one exact direct-void-call prefix through independent source-SSA and
/// semantic-C interpreters. Both sides stop at the call boundary; neither the
/// callee nor post-call state is modeled or claimed.
pub fn check_direct_call_differential(
    trusted: &TrustedSsaArtifact,
    block_addr: u64,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> DifferentialReport {
    let artifact = trusted.artifact();
    let certified = match CertifiedMachineProjection::from_artifact(trusted) {
        Ok(certified) => certified,
        Err(error) => {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("artifact certification failed: {error}"),
                },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let requested_artifact_identity =
        match DifferentialArtifactIdentity::from_origin(certified.origin()) {
            Ok(identity) => identity,
            Err(reason) => {
                let mut report = issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
                report.artifact_identity = None;
                return report;
            }
        };
    let invalid_input = |reason| {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::InvalidInput,
            DifferentialCaseDisposition::InvalidInput { reason },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity.clone());
        report
    };
    if limits.max_source_steps == 0
        || limits.max_expression_nodes == 0
        || limits.max_memory_bytes == 0
    {
        return invalid_input("differential limits must all be nonzero".to_string());
    }
    if initial.origin != *certified.origin() {
        return invalid_input(
            "differential state belongs to a different certified artifact origin".to_string(),
        );
    }
    if let Err(reason) = validate_initial_state(artifact, block_addr, initial) {
        return invalid_input(reason);
    }
    if initial.memory.len() > limits.max_memory_bytes as usize {
        return issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
    }
    let accounting =
        match CertifiedSingleBlockAccounting::from_projection_block(&certified, block_addr) {
            Ok(accounting) => accounting,
            Err(error) => {
                return issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::Refused,
                    DifferentialConclusion::InvalidArtifact,
                    DifferentialCaseDisposition::InvalidArtifact {
                        reason: format!("direct-call accounting failed: {error}"),
                    },
                    None,
                    None,
                );
            }
        };
    let accounting_audit = accounting.audit();
    if !accounting_audit.has_exact_source_accounting() {
        return issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Refused,
            DifferentialConclusion::InvalidArtifact,
            DifferentialCaseDisposition::InvalidArtifact {
                reason: format!(
                    "direct-call accounting audit failed: {:?}",
                    accounting_audit.invalid()
                ),
            },
            None,
            None,
        );
    }
    let region = match CertifiedDirectCallBlockRegion::from_accounting(accounting) {
        Ok(region) => region,
        Err(error) => {
            return candidate_not_admitted(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Residual,
                format!("direct-call region was not admitted: {error}"),
            );
        }
    };
    let candidate_identity = match DifferentialCandidateIdentity::from_direct_call_region(&region) {
        Ok(identity) => identity,
        Err(reason) => {
            return issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure { reason },
                None,
                None,
            );
        }
    };
    let body = region.body();
    if !body.audit().has_exact_source_order() {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: "direct-call source-order audit failed".to_string(),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if let Err(reason) = audit_semantic_translation(&certified, body) {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure { reason },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if body.steps().len() > limits.max_source_steps as usize {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if body
        .steps()
        .iter()
        .any(|step| matches!(step.state(), SemanticInstructionState::UnsupportedUnknown))
    {
        let mut report = candidate_not_admitted(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Residual,
            "direct-call prefix contains unsupported source semantics".to_string(),
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let source = direct_callize_source_run(
        execute_source(artifact, body, initial, limits),
        artifact,
        block_addr,
        initial,
    );
    let semantic_c = direct_callize_semantic_run(
        execute_semantic(artifact, body, initial, limits),
        region.call(),
        initial,
    );
    finish_report(
        initial,
        Some(candidate_identity),
        block_addr,
        limits,
        source,
        semantic_c,
    )
}

/// Execute one fully certified terminal-return function through independent
/// source-SSA and semantic-C interpreters from the same initial state.
pub fn check_terminal_return_differential(
    trusted: &TrustedSsaArtifact,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> DifferentialReport {
    let artifact = trusted.artifact();
    let certified = match CertifiedMachineProjection::from_artifact(trusted) {
        Ok(certified) => certified,
        Err(error) => {
            let mut report = issued_report(
                initial,
                artifact.function().entry,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("artifact certification failed: {error}"),
                },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let requested_artifact_identity =
        match DifferentialArtifactIdentity::from_origin(certified.origin()) {
            Ok(identity) => identity,
            Err(reason) => {
                let mut report = issued_report(
                    initial,
                    artifact.function().entry,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
                report.artifact_identity = None;
                return report;
            }
        };
    let invalid_input = |block_addr, reason| {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::InvalidInput,
            DifferentialCaseDisposition::InvalidInput { reason },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity.clone());
        report
    };
    let [source_block] = certified.topology().blocks() else {
        let mut report = issued_report(
            initial,
            artifact.function().entry,
            limits,
            DifferentialCandidateAdmission::Refused,
            DifferentialConclusion::InvalidArtifact,
            DifferentialCaseDisposition::InvalidArtifact {
                reason: "terminal return differential requires exactly one source block"
                    .to_string(),
            },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity.clone());
        return report;
    };
    let block_addr = source_block.addr();
    if limits.max_source_steps == 0
        || limits.max_expression_nodes == 0
        || limits.max_memory_bytes == 0
    {
        return invalid_input(
            block_addr,
            "differential limits must all be nonzero".to_string(),
        );
    }
    if initial.origin != *certified.origin() {
        return invalid_input(
            block_addr,
            "differential state belongs to a different certified artifact origin".to_string(),
        );
    }
    if let Err(reason) = validate_initial_state(artifact, block_addr, initial) {
        return invalid_input(block_addr, reason);
    }
    if initial.memory.len() > limits.max_memory_bytes as usize {
        return issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
    }
    let accounting = match CertifiedSingleBlockAccounting::from_projection(&certified) {
        Ok(accounting) => accounting,
        Err(error) => {
            return issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("terminal accounting failed: {error}"),
                },
                None,
                None,
            );
        }
    };
    let region = match CertifiedTerminalReturnBlockRegion::from_accounting(
        accounting,
        certified.frame_preservation(),
    ) {
        Ok(region) => region,
        Err(error) => {
            return candidate_not_admitted(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Residual,
                format!("terminal return region was not admitted: {error}"),
            );
        }
    };
    let candidate_identity = match DifferentialCandidateIdentity::from_terminal_region(&region) {
        Ok(identity) => identity,
        Err(reason) => {
            return issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure { reason },
                None,
                None,
            );
        }
    };
    let semantic_function = match CertifiedSemanticCFunction::from_terminal_region(region.clone()) {
        Ok(function) => function,
        Err(error) => {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure {
                    reason: format!("certified semantic function failed: {error}"),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        }
    };
    if let Err(error) = semantic_function.render_certified_c() {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: format!("certified semantic C rendering failed: {error}"),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let layer = region.layer();
    if layer.steps().len() > limits.max_source_steps as usize {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if let Err(reason) = audit_semantic_translation(&certified, layer) {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure { reason },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let Some(returned) = region.returned() else {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: "audited terminal region lost its semantic return".to_string(),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    };
    let source = source_terminalize_run(
        artifact,
        block_addr,
        execute_source(artifact, layer, initial, limits),
    );
    let semantic_c = terminalize_run(execute_semantic(artifact, layer, initial, limits), returned);
    finish_report(
        initial,
        Some(candidate_identity),
        block_addr,
        limits,
        source,
        semantic_c,
    )
}

/// Execute the exact closed plain-RAM-memory-plus-return function through
/// independent source-SSA and typed semantic-C interpreters over identical
/// finite byte memory. `NoMismatchObserved` remains bounded falsification
/// evidence and never grants certification or helper-ABI authority.
pub fn check_memory_terminal_return_differential(
    trusted: &TrustedSsaArtifact,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> DifferentialReport {
    let artifact = trusted.artifact();
    let certified = match CertifiedMachineProjection::from_artifact(trusted) {
        Ok(certified) => certified,
        Err(error) => {
            let mut report = issued_report(
                initial,
                artifact.function().entry,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("artifact certification failed: {error}"),
                },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let requested_artifact_identity =
        match DifferentialArtifactIdentity::from_origin(certified.origin()) {
            Ok(identity) => identity,
            Err(reason) => {
                let mut report = issued_report(
                    initial,
                    artifact.function().entry,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
                report.artifact_identity = None;
                return report;
            }
        };
    let block_addr = certified.topology().blocks().first().map_or(
        artifact.function().entry,
        r2cert::CertifiedSourceBlock::addr,
    );
    let invalid_input = |reason| {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::InvalidInput,
            DifferentialCaseDisposition::InvalidInput { reason },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity.clone());
        report
    };
    if limits.max_source_steps == 0
        || limits.max_expression_nodes == 0
        || limits.max_memory_bytes == 0
    {
        return invalid_input("differential limits must all be nonzero".to_string());
    }
    if initial.origin != *certified.origin() {
        return invalid_input(
            "differential state belongs to a different certified artifact origin".to_string(),
        );
    }
    if let Err(reason) = validate_initial_state(artifact, block_addr, initial) {
        return invalid_input(reason);
    }
    if initial.memory.len() > limits.max_memory_bytes as usize {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity);
        return report;
    }
    let function = match CertifiedMemorySemanticCFunction::from_artifact(trusted) {
        Ok(function) => function,
        Err(error) => {
            let mut report = candidate_not_admitted(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Residual,
                format!("memory terminal-return function was not admitted: {error}"),
            );
            report.artifact_identity = Some(requested_artifact_identity);
            return report;
        }
    };
    let candidate_identity =
        match DifferentialCandidateIdentity::from_memory_terminal_return_function(&function) {
            Ok(identity) => identity,
            Err(reason) => {
                return issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
            }
        };
    if !function.audit().has_exact_closed_memory_return() {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: "memory terminal-return audit failed".to_string(),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if let Err(error) = function.render_certified_c() {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: format!("certified memory semantic C rendering failed: {error}"),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let layer = function.layer();
    if layer.steps().len() > limits.max_source_steps as usize {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let mut memory_execution_bytes = 0_u32;
    for step in layer.steps() {
        let Some(reference) = step.memory() else {
            continue;
        };
        let Some(statement) = layer.resolve_memory_statement(reference) else {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure {
                    reason: "memory step became unresolved after source-order audit".to_string(),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        };
        let Some(bytes) = statement.width_bits().checked_add(7).map(|width| width / 8) else {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: "memory execution width overflow".to_string(),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        };
        let Some(total) = memory_execution_bytes.checked_add(bytes) else {
            let mut report = issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: "memory execution byte budget overflow".to_string(),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        };
        memory_execution_bytes = total;
    }
    if memory_execution_bytes > limits.max_memory_bytes {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if let Err(reason) = audit_semantic_translation(&certified, layer) {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure { reason },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let Some(returned) = function.returned() else {
        let mut report = issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure {
                reason: "audited memory function lost its exact return".to_string(),
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    };
    let source = source_terminalize_run(
        artifact,
        block_addr,
        execute_source(artifact, layer, initial, limits),
    );
    let semantic_c = terminalize_run(execute_semantic(artifact, layer, initial, limits), returned);
    finish_report(
        initial,
        Some(candidate_identity),
        block_addr,
        limits,
        source,
        semantic_c,
    )
}

/// Execute one exact closed conditional-return function through independent
/// source-SSA, semantic-C, and strict rendered-control paths. The source path
/// obtains edge polarity and return values directly from canonical CFG/SSA
/// boundary facts; a finite match remains falsification evidence, not proof.
pub fn check_conditional_return_differential(
    trusted: &TrustedSsaArtifact,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> DifferentialReport {
    let artifact = trusted.artifact();
    let entry = artifact.function().entry;
    let certified = match CertifiedMachineProjection::from_artifact(trusted) {
        Ok(certified) => certified,
        Err(error) => {
            let mut report = issued_report(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("artifact certification failed: {error}"),
                },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let requested_artifact_identity =
        match DifferentialArtifactIdentity::from_origin(certified.origin()) {
            Ok(identity) => identity,
            Err(reason) => {
                let mut report = issued_report(
                    initial,
                    entry,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
                report.artifact_identity = None;
                return report;
            }
        };
    let invalid_input = |reason| {
        let mut report = issued_report(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::InvalidInput,
            DifferentialCaseDisposition::InvalidInput { reason },
            None,
            None,
        );
        report.artifact_identity = Some(requested_artifact_identity.clone());
        report
    };
    if limits.max_source_steps == 0
        || limits.max_expression_nodes == 0
        || limits.max_memory_bytes == 0
    {
        return invalid_input("differential limits must all be nonzero".to_string());
    }
    if initial.origin != *certified.origin() {
        return invalid_input(
            "differential state belongs to a different certified artifact origin".to_string(),
        );
    }
    if let Err(reason) = validate_initial_state(artifact, entry, initial) {
        return invalid_input(reason);
    }
    if initial.memory.len() > limits.max_memory_bytes as usize {
        return issued_report(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
    }
    let function = match CertifiedConditionalReturnFunction::from_projection(&certified) {
        Ok(function) => function,
        Err(error) => {
            return candidate_not_admitted(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::Residual,
                format!("conditional-return function was not admitted: {error}"),
            );
        }
    };
    let candidate_identity =
        match DifferentialCandidateIdentity::from_conditional_return_function(&function) {
            Ok(identity) => identity,
            Err(reason) => {
                return issued_report(
                    initial,
                    entry,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
            }
        };
    let rendered_c = match function.render_certified_c() {
        Ok(rendered_c) => rendered_c,
        Err(error) => {
            let mut report = issued_report(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure {
                    reason: format!("certified conditional C rendering failed: {error}"),
                },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        }
    };
    for layer in [
        function.header().body(),
        function.true_arm().layer(),
        function.false_arm().layer(),
    ] {
        if let Err(reason) = audit_semantic_translation(&certified, layer) {
            let mut report = issued_report(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure { reason },
                None,
                None,
            );
            report.candidate_identity = Some(candidate_identity);
            return report;
        }
    }
    let maximum_steps = function.header().body().steps().len().saturating_add(
        function
            .true_arm()
            .layer()
            .steps()
            .len()
            .max(function.false_arm().layer().steps().len()),
    );
    if maximum_steps > limits.max_source_steps as usize {
        let mut report = issued_report(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let source = execute_conditional_source(artifact, initial, limits);
    let (semantic_c, rendered_c) =
        execute_conditional_semantic(artifact, &function, &rendered_c, initial, limits);
    finish_conditional_report(
        initial,
        Some(candidate_identity),
        entry,
        limits,
        source,
        semantic_c,
        rendered_c,
    )
}

/// Execute one audited private-frame conditional-join function through
/// independent canonical-SSA and sealed typed-rewrite evaluators. This is one
/// caller-supplied bounded test case, not a proof or a rendered-C oracle.
pub fn check_private_frame_conditional_join_differential(
    trusted: &TrustedSsaArtifact,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> DifferentialReport {
    let artifact = trusted.artifact();
    let entry = artifact.function().entry;
    let certified = match CertifiedMachineProjection::from_artifact(trusted) {
        Ok(certified) => certified,
        Err(error) => {
            let mut report = issued_report(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::Refused,
                DifferentialConclusion::InvalidArtifact,
                DifferentialCaseDisposition::InvalidArtifact {
                    reason: format!("artifact certification failed: {error}"),
                },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let requested_identity = match DifferentialArtifactIdentity::from_origin(certified.origin()) {
        Ok(identity) => identity,
        Err(reason) => {
            let mut report = issued_report(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::NotEvaluated,
                DifferentialConclusion::HarnessFailure,
                DifferentialCaseDisposition::HarnessFailure { reason },
                None,
                None,
            );
            report.artifact_identity = None;
            return report;
        }
    };
    let invalid_input = |reason| {
        let mut report = issued_report(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::InvalidInput,
            DifferentialCaseDisposition::InvalidInput { reason },
            None,
            None,
        );
        report.artifact_identity = Some(requested_identity.clone());
        report
    };
    if limits.max_source_steps == 0
        || limits.max_expression_nodes == 0
        || limits.max_memory_bytes == 0
    {
        return invalid_input("differential limits must all be nonzero".to_string());
    }
    if initial.origin != *certified.origin() {
        return invalid_input(
            "differential state belongs to a different certified artifact origin".to_string(),
        );
    }
    if let Err(reason) = validate_initial_state(artifact, entry, initial) {
        return invalid_input(reason);
    }
    if let Err(reason) = validate_private_join_initial_state(artifact, initial) {
        return invalid_input(reason);
    }
    if initial.memory.len() > limits.max_memory_bytes as usize {
        let mut report = issued_report(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::Both,
            },
            None,
            None,
        );
        report.artifact_identity = Some(requested_identity);
        return report;
    }
    let function = match CertifiedPrivateFrameConditionalJoinFunction::from_artifact(trusted) {
        Ok(function) => function,
        Err(error) => {
            return candidate_not_admitted(
                initial,
                entry,
                limits,
                DifferentialCandidateAdmission::Residual,
                format!("private-frame conditional join was not admitted: {error}"),
            );
        }
    };
    if function.origin() != certified.origin()
        || !function.audit().has_exact_private_frame_conditional_join()
    {
        return candidate_not_admitted(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::Refused,
            "private-frame conditional join failed exact audit".to_string(),
        );
    }
    let candidate_identity =
        match DifferentialCandidateIdentity::from_private_frame_conditional_join_function(&function)
        {
            Ok(identity) => identity,
            Err(reason) => {
                let mut report = issued_report(
                    initial,
                    entry,
                    limits,
                    DifferentialCandidateAdmission::NotEvaluated,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure { reason },
                    None,
                    None,
                );
                report.artifact_identity = Some(requested_identity);
                return report;
            }
        };
    if let Err(reason) =
        audit_semantic_expression_layer(&certified, function.rewrite().expression_layer())
    {
        let mut report = issued_report(
            initial,
            entry,
            limits,
            DifferentialCandidateAdmission::NotEvaluated,
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure { reason },
            None,
            None,
        );
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    if let Err(failure) = validate_private_join_memory_domain(
        artifact,
        &certified,
        function.rewrite().machine_join(),
        initial,
    ) {
        let mut report = report_failure(initial, entry, limits, DifferentialSide::Both, failure);
        report.candidate_identity = Some(candidate_identity);
        return report;
    }
    let (source, selected_true) =
        execute_private_frame_join_source(artifact, &certified, &function, initial, limits);
    let source = match (source, selected_true) {
        (Ok(run), Some(selected_true)) => {
            let trace = DifferentialObservedTrace {
                memory_events: run.memory_events.clone(),
                final_memory: run.final_memory.clone(),
            };
            normalize_private_join_run(artifact, &certified, &function, initial, selected_true, run)
                .map_err(|failure| FailedRun { failure, trace })
        }
        (result, _) => result,
    };
    let semantic_c = execute_private_frame_join_semantic(artifact, &function, initial, limits)
        .and_then(|run| {
            project_private_join_semantic_memory(&certified, &function, initial, run).map_err(
                |failure| FailedRun {
                    failure,
                    trace: DifferentialObservedTrace {
                        memory_events: Box::new([]),
                        final_memory: Box::new([]),
                    },
                },
            )
        });
    finish_report(
        initial,
        Some(candidate_identity),
        entry,
        limits,
        source,
        semantic_c,
    )
}

fn validate_initial_state(
    artifact: &SsaArtifact,
    block_addr: u64,
    initial: &DifferentialState,
) -> Result<(), String> {
    let selected = artifact
        .graph()
        .block_id_for_addr(block_addr)
        .ok_or_else(|| format!("unknown block 0x{block_addr:x}"))?;
    for (id, value) in &initial.values {
        let graph_value = artifact
            .graph()
            .value(*id)
            .ok_or_else(|| format!("initial state names unknown value {id:?}"))?;
        let width = value_width(graph_value.var.size)?;
        if value.width_bits != width {
            return Err(format!(
                "initial width mismatch for {id:?}: {} != {width}",
                value.width_bits
            ));
        }
        if graph_value.var.constant_bits().is_some() {
            return Err(format!("initial state attempts to replace constant {id:?}"));
        }
        if artifact
            .graph()
            .def_inst(*id)
            .and_then(|inst| artifact.graph().inst(inst))
            .is_some_and(|inst| inst.block == selected)
        {
            return Err(format!(
                "initial state attempts to replace local producer for {id:?}"
            ));
        }
    }
    let model = artifact.machine_context().memory_model();
    for location in initial.memory.keys() {
        let source_space = match location.space {
            MachineAddressSpace::Ram => r2il::SpaceId::Ram,
            MachineAddressSpace::Custom(id) => r2il::SpaceId::Custom(id),
            _ => {
                return Err(format!(
                    "memory seed uses non-memory address space {:?}",
                    location.space
                ));
            }
        };
        let space = model
            .space(source_space)
            .filter(|_| model.is_available() && model.is_coherent())
            .ok_or_else(|| format!("memory seed uses unavailable space {source_space:?}"))?;
        if space.address_bits() == 0
            || space.address_bits() > 64
            || (space.address_bits() < 64
                && location.byte_address >= (1_u64 << space.address_bits()))
        {
            return Err(format!(
                "memory seed address 0x{:x} exceeds {}-bit space",
                location.byte_address,
                space.address_bits()
            ));
        }
    }
    Ok(())
}

fn validate_private_join_initial_state(
    artifact: &SsaArtifact,
    initial: &DifferentialState,
) -> Result<(), String> {
    for value in initial.values.keys() {
        if artifact.graph().def_inst(*value).is_some() {
            return Err(format!(
                "private-join initial state attempts to replace function-local producer {value:?}"
            ));
        }
    }
    Ok(())
}

fn audit_semantic_translation(
    certified: &CertifiedMachineProjection,
    layer: &SemanticCBlockStepLayer,
) -> Result<(), String> {
    let machine = certified.projection();
    let semantic = layer.accounting().expression_layer();
    let mut seen = BTreeSet::new();
    for step in layer.steps() {
        let Some(reference) = step.value() else {
            continue;
        };
        let entity = layer
            .resolve_value(reference)
            .ok_or_else(|| "semantic value reference is unresolved".to_string())?;
        let machine_entity = machine
            .entity_for_producer(entity.producer())
            .ok_or_else(|| "semantic entity lacks a machine counterpart".to_string())?;
        let certified_expr = certified
            .expression_for_producer(entity.producer())
            .ok_or_else(|| "semantic entity lacks certified expression evidence".to_string())?;
        if certified_expr.root() != machine_entity.root()
            || certified_expr.entity().producer() != entity.producer()
        {
            return Err(
                "certified expression root or producer differs from machine evidence".into(),
            );
        }
        if entity.output() != machine_entity.output() {
            return Err("semantic entity output differs from machine evidence".to_string());
        }
        if entity.source_obligations() != certified_expr.entity().source_obligations() {
            return Err(
                "semantic entity obligations differ from certified expression evidence".to_string(),
            );
        }
        let semantic_root = semantic
            .expr(entity.root())
            .ok_or_else(|| "semantic entity root is missing".to_string())?;
        let mut expected_sources = certified_expr.inputs().clone();
        expected_sources.insert(entity.producer());
        if semantic_root.source_instructions() != &expected_sources {
            return Err("semantic root provenance differs from certified inputs".to_string());
        }
        audit_semantic_expr_pair(
            machine,
            semantic,
            machine_entity.root(),
            entity.root(),
            &mut seen,
        )?;
    }
    Ok(())
}

fn audit_semantic_expression_layer(
    certified: &CertifiedMachineProjection,
    semantic: &SemanticCExpressionLayer,
) -> Result<(), String> {
    let machine = certified.projection();
    let mut seen = BTreeSet::new();
    let mut outputs = BTreeSet::new();
    for entity in semantic.entities() {
        if !outputs.insert(entity.output()) {
            return Err("semantic expression layer has an ambiguous output binding".to_string());
        }
        let machine_entity = machine
            .entity_for_producer(entity.producer())
            .ok_or_else(|| "semantic entity lacks a machine counterpart".to_string())?;
        let certified_expr = certified
            .expression_for_producer(entity.producer())
            .ok_or_else(|| "semantic entity lacks certified expression evidence".to_string())?;
        if certified_expr.root() != machine_entity.root()
            || certified_expr.entity().producer() != entity.producer()
            || entity.output() != machine_entity.output()
            || entity.source_obligations() != certified_expr.entity().source_obligations()
        {
            return Err("semantic entity differs from certified machine evidence".to_string());
        }
        let root = semantic
            .expr(entity.root())
            .ok_or_else(|| "semantic entity root is missing".to_string())?;
        let mut expected_sources = certified_expr.inputs().clone();
        expected_sources.insert(entity.producer());
        if root.source_instructions() != &expected_sources {
            return Err("semantic root provenance differs from certified inputs".to_string());
        }
        audit_semantic_expr_pair(
            machine,
            semantic,
            machine_entity.root(),
            entity.root(),
            &mut seen,
        )?;
    }
    Ok(())
}

fn audit_semantic_expr_pair(
    machine: &r2ssa::MachineProjection,
    semantic: &SemanticCExpressionLayer,
    machine_id: MachineExprId,
    semantic_id: SemanticCExprId,
    seen: &mut BTreeSet<(MachineExprId, SemanticCExprId)>,
) -> Result<(), String> {
    if !seen.insert((machine_id, semantic_id)) {
        return Ok(());
    }
    let machine_expr = machine
        .expr(machine_id)
        .ok_or_else(|| "machine expression is missing".to_string())?;
    let semantic_expr = semantic
        .expr(semantic_id)
        .ok_or_else(|| "semantic expression is missing".to_string())?;
    if machine_expr.ty() != semantic_expr.ty() {
        return Err("semantic expression type differs from machine evidence".to_string());
    }
    let child = |machine_child, semantic_child, seen: &mut BTreeSet<_>| {
        audit_semantic_expr_pair(machine, semantic, machine_child, semantic_child, seen)
    };
    match (machine_expr.kind(), semantic_expr.kind()) {
        (
            MachineExprKind::Source {
                binding: machine_binding,
                ..
            },
            SemanticCExprKind::Input {
                binding: semantic_binding,
            },
        ) if machine_binding == semantic_binding => {
            let source_is_produced = machine.entity_for_output(machine_binding.value()).is_some();
            let semantic_input_type = semantic.inputs().get(semantic_binding);
            if (source_is_produced && semantic_input_type.is_some())
                || (!source_is_produced && semantic_input_type.map(|(ty, _)| ty) != Some(machine_expr.ty()))
            {
                return Err("semantic input classification differs from machine evidence".into());
            }
            Ok(())
        }
        (
            MachineExprKind::Constant {
                binding: machine_binding,
                value: machine_value,
            },
            SemanticCExprKind::Constant {
                binding: semantic_binding,
                value: semantic_value,
            },
        ) if machine_binding == semantic_binding && machine_value == semantic_value => Ok(()),
        (
            MachineExprKind::MemoryRead {
                access: machine_access,
                object: machine_object,
                space: machine_space,
                endianness: machine_endianness,
                word_size_bytes: machine_word_size,
                address: machine_address,
                width_bits: machine_width,
            },
            SemanticCExprKind::MemoryRead {
                access: semantic_access,
                object: semantic_object,
                space: semantic_space,
                endianness: semantic_endianness,
                word_size_bytes: semantic_word_size,
                address: semantic_address,
                width_bits: semantic_width,
            },
        ) if machine_access == semantic_access
            && machine_object == semantic_object
            && machine_space == semantic_space
            && machine_endianness == semantic_endianness
            && machine_word_size == semantic_word_size
            && machine_width == semantic_width =>
        {
            child(*machine_address, *semantic_address, seen)
        }
        (
            MachineExprKind::Copy {
                input: machine_input,
            },
            SemanticCExprKind::Copy {
                input: semantic_input,
            },
        ) => child(*machine_input, *semantic_input, seen),
        (
            MachineExprKind::Arithmetic {
                op: machine_op,
                mode: machine_mode,
                left: machine_left,
                right: machine_right,
            },
            SemanticCExprKind::Arithmetic {
                op: semantic_op,
                mode: semantic_mode,
                left: semantic_left,
                right: semantic_right,
            },
        ) if machine_op == semantic_op && machine_mode == semantic_mode => {
            child(*machine_left, *semantic_left, seen)?;
            child(*machine_right, *semantic_right, seen)
        }
        (
            MachineExprKind::ArithmeticFlag {
                op: machine_op,
                left: machine_left,
                right: machine_right,
            },
            SemanticCExprKind::ArithmeticFlag {
                op: semantic_op,
                left: semantic_left,
                right: semantic_right,
            },
        ) if machine_op == semantic_op => {
            child(*machine_left, *semantic_left, seen)?;
            child(*machine_right, *semantic_right, seen)
        }
        (
            MachineExprKind::Bitwise {
                op: machine_op,
                left: machine_left,
                right: machine_right,
            },
            SemanticCExprKind::Bitwise {
                op: semantic_op,
                left: semantic_left,
                right: semantic_right,
            },
        ) if machine_op == semantic_op => {
            child(*machine_left, *semantic_left, seen)?;
            child(*machine_right, *semantic_right, seen)
        }
        (
            MachineExprKind::BitwiseNot {
                input: machine_input,
            },
            SemanticCExprKind::BitwiseNot {
                input: semantic_input,
            },
        ) => child(*machine_input, *semantic_input, seen),
        (
            MachineExprKind::BooleanNot {
                input: machine_input,
            },
            SemanticCExprKind::BooleanNot {
                input: semantic_input,
            },
        ) => child(*machine_input, *semantic_input, seen),
        (
            MachineExprKind::Boolean {
                op: machine_op,
                left: machine_left,
                right: machine_right,
            },
            SemanticCExprKind::Boolean {
                op: semantic_op,
                left: semantic_left,
                right: semantic_right,
            },
        ) if machine_op == semantic_op => {
            child(*machine_left, *semantic_left, seen)?;
            child(*machine_right, *semantic_right, seen)
        }
        (
            MachineExprKind::Shift {
                kind: machine_kind,
                overshift: machine_overshift,
                value: machine_value,
                count: machine_count,
            },
            SemanticCExprKind::Shift {
                kind: semantic_kind,
                overshift: semantic_overshift,
                value: semantic_value,
                count: semantic_count,
            },
        ) if machine_kind == semantic_kind && machine_overshift == semantic_overshift => {
            child(*machine_value, *semantic_value, seen)?;
            child(*machine_count, *semantic_count, seen)
        }
        (
            MachineExprKind::Compare {
                op: machine_op,
                interpretation: machine_interpretation,
                left: machine_left,
                right: machine_right,
            },
            SemanticCExprKind::Compare {
                op: semantic_op,
                interpretation: semantic_interpretation,
                left: semantic_left,
                right: semantic_right,
            },
        ) if machine_op == semantic_op && machine_interpretation == semantic_interpretation => {
            child(*machine_left, *semantic_left, seen)?;
            child(*machine_right, *semantic_right, seen)
        }
        (
            MachineExprKind::Cast {
                kind: machine_kind,
                input: machine_input,
            },
            SemanticCExprKind::Cast {
                kind: semantic_kind,
                input: semantic_input,
            },
        ) if machine_kind == semantic_kind => child(*machine_input, *semantic_input, seen),
        (
            MachineExprKind::Extract {
                input: machine_input,
                lsb_bits: machine_lsb,
            },
            SemanticCExprKind::Extract {
                input: semantic_input,
                lsb_bits: semantic_lsb,
            },
        ) if machine_lsb == semantic_lsb => child(*machine_input, *semantic_input, seen),
        (
            MachineExprKind::Select {
                condition: machine_condition,
                if_true: machine_if_true,
                if_false: machine_if_false,
            },
            SemanticCExprKind::Select {
                condition: semantic_condition,
                if_true: semantic_if_true,
                if_false: semantic_if_false,
            },
        ) => {
            child(*machine_condition, *semantic_condition, seen)?;
            child(*machine_if_true, *semantic_if_true, seen)?;
            child(*machine_if_false, *semantic_if_false, seen)
        }
        (MachineExprKind::Phi { .. }, _) => {
            Err("phi expression entered the semantic differential subset".to_string())
        }
        _ => Err("semantic expression kind differs from machine evidence".to_string()),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RunFailure {
    Unsupported(String),
    Invalid(String),
    MissingBoundaryInput(ValueId),
    MemoryOutOfDomain(DifferentialMemoryLocation),
    BudgetExceeded,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FailedRun {
    failure: RunFailure,
    trace: DifferentialObservedTrace,
}

type InterpreterResult = Result<DifferentialObservedRun, FailedRun>;

#[derive(Clone)]
struct ExecutionState {
    values: BTreeMap<ValueId, DifferentialBitVector>,
    memory: BTreeMap<DifferentialMemoryLocation, u8>,
    events: Vec<DifferentialMemoryEvent>,
}

impl From<&DifferentialState> for ExecutionState {
    fn from(initial: &DifferentialState) -> Self {
        Self {
            values: initial.values.clone(),
            memory: initial.memory.clone(),
            events: Vec::new(),
        }
    }
}

fn execute_source(
    artifact: &SsaArtifact,
    layer: &SemanticCBlockStepLayer,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> InterpreterResult {
    let mut state = ExecutionState::from(initial);
    execute_source_inner(
        artifact,
        layer.accounting().block_addr(),
        &mut state,
        limits,
    )
    .map_err(|failure| FailedRun {
        failure,
        trace: observed_trace(&state),
    })
}

fn conditional_arm(
    function: &CertifiedConditionalReturnFunction,
    condition: DifferentialBitVector,
) -> &CertifiedConditionalReturnArm {
    if condition.bits() != 0 {
        function.true_arm()
    } else {
        function.false_arm()
    }
}

fn source_conditional_target(
    artifact: &SsaArtifact,
    block_addr: u64,
    state: &ExecutionState,
) -> Result<u64, RunFailure> {
    let source_block = artifact
        .function()
        .cfg()
        .get_block(block_addr)
        .ok_or_else(|| RunFailure::Invalid("conditional source block is missing".to_string()))?;
    let BlockTerminator::ConditionalBranch {
        true_target,
        false_target,
    } = &source_block.terminator
    else {
        return Err(RunFailure::Invalid(
            "source terminator is not a conditional branch".to_string(),
        ));
    };
    let true_target = *true_target;
    let false_target = *false_target;
    if source_block.successors() != [true_target, false_target] {
        return Err(RunFailure::Invalid(
            "conditional source CFG lost true/false successor order".to_string(),
        ));
    }
    let graph = artifact.graph();
    let graph_block = graph
        .block_id_for_addr(block_addr)
        .and_then(|id| graph.block(id))
        .ok_or_else(|| RunFailure::Invalid("conditional graph block is missing".to_string()))?;
    let terminator = graph_block
        .insts
        .last()
        .and_then(|id| graph.inst(*id))
        .ok_or_else(|| RunFailure::Invalid("conditional source block is empty".to_string()))?;
    let InstPayload::Op(SSAOp::CBranch { target, cond }) = &terminator.payload else {
        return Err(RunFailure::Invalid(
            "conditional graph terminator is not a source branch".to_string(),
        ));
    };
    let target_id = graph
        .value_id_for_var(target)
        .ok_or_else(|| RunFailure::Invalid("conditional target value is missing".to_string()))?;
    let condition_id = graph
        .value_id_for_var(cond)
        .ok_or_else(|| RunFailure::Invalid("conditional predicate value is missing".to_string()))?;
    if terminator.inputs.as_slice() != [target_id, condition_id] {
        return Err(RunFailure::Invalid(
            "conditional graph operands differ from source SSA".to_string(),
        ));
    }
    let condition = source_value(artifact, state, condition_id)?;
    if condition.width_bits() != 8 {
        return Err(RunFailure::Invalid(
            "conditional source predicate is not eight bits".to_string(),
        ));
    }
    Ok(if condition.bits() != 0 {
        true_target
    } else {
        false_target
    })
}

fn execute_conditional_source(
    artifact: &SsaArtifact,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> InterpreterResult {
    let mut state = ExecutionState::from(initial);
    let result = (|| {
        let header_addr = artifact.function().entry;
        execute_source_inner(artifact, header_addr, &mut state, limits)?;
        let target = source_conditional_target(artifact, header_addr, &state)?;
        let run = execute_source_inner(artifact, target, &mut state, limits)?;
        Ok((run, target))
    })();
    match result {
        Ok((run, target)) => source_terminalize_run(artifact, target, Ok(run)),
        Err(failure) => Err(FailedRun {
            failure,
            trace: observed_trace(&state),
        }),
    }
}

fn execute_private_join_block(
    artifact: &SsaArtifact,
    block_addr: u64,
    state: &mut ExecutionState,
    remaining_steps: &mut u32,
    inert_phis: &BTreeMap<CanonicalInstructionId, (ValueId, Box<[u64]>)>,
) -> Result<(), RunFailure> {
    let graph = artifact.graph();
    let block = graph
        .block_id_for_addr(block_addr)
        .and_then(|id| graph.block(id))
        .ok_or_else(|| RunFailure::Invalid("private-join route block is missing".to_string()))?;
    let mut consumed = BTreeSet::new();
    for inst_id in &block.insts {
        if *remaining_steps == 0 {
            return Err(RunFailure::BudgetExceeded);
        }
        *remaining_steps -= 1;
        let inst = graph.inst(*inst_id).ok_or_else(|| {
            RunFailure::Invalid("private-join instruction is missing".to_string())
        })?;
        if let InstPayload::Phi { predecessors } = &inst.payload {
            let producer = artifact
                .obligations()
                .instruction_for_inst(*inst_id)
                .map(|instruction| instruction.id)
                .ok_or_else(|| {
                    RunFailure::Invalid("inert phi lacks source identity".to_string())
                })?;
            let (output, expected_predecessors) = inert_phis.get(&producer).ok_or_else(|| {
                RunFailure::Unsupported("uncertified phi on private-join route".to_string())
            })?;
            let actual_predecessors = predecessors
                .iter()
                .map(|predecessor| graph.block(*predecessor).map(|block| block.addr))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| {
                    RunFailure::Invalid("inert phi predecessor is missing".to_string())
                })?;
            if inst.output != Some(*output)
                || actual_predecessors.as_slice() != expected_predecessors.as_ref()
                || !consumed.insert(producer)
            {
                return Err(RunFailure::Invalid(
                    "inert phi differs from its exact certificate".to_string(),
                ));
            }
            continue;
        }
        execute_source_inst(artifact, state, *inst_id)?;
    }
    if consumed.len() != inert_phis.len() {
        return Err(RunFailure::Invalid(
            "certified inert phi was not consumed exactly once".to_string(),
        ));
    }
    Ok(())
}

fn private_join_route(
    join: &CertifiedPrivateFrameConditionalJoin,
    target: u64,
) -> Result<(&CertifiedPrivateFrameConditionalArm, bool), RunFailure> {
    if target == join.condition().true_target()
        && target == join.true_arm().entry_target()
        && target != join.false_arm().entry_target()
    {
        Ok((join.true_arm(), true))
    } else if target == join.condition().false_target()
        && target == join.false_arm().entry_target()
        && target != join.true_arm().entry_target()
    {
        Ok((join.false_arm(), false))
    } else {
        Err(RunFailure::Invalid(
            "source branch target differs from sealed arm polarity".to_string(),
        ))
    }
}

fn exact_source_direct_target(artifact: &SsaArtifact, block_addr: u64) -> Result<u64, RunFailure> {
    let block = artifact
        .function()
        .cfg()
        .get_block(block_addr)
        .ok_or_else(|| RunFailure::Invalid("direct-control source block is missing".to_string()))?;
    let target = match block.terminator {
        BlockTerminator::Branch { target } | BlockTerminator::Fallthrough { next: target } => {
            target
        }
        _ => {
            return Err(RunFailure::Invalid(
                "certified arm control is not a direct source transfer".to_string(),
            ));
        }
    };
    if block.successors() != [target] {
        return Err(RunFailure::Invalid(
            "direct source successor differs from its terminator".to_string(),
        ));
    }
    Ok(target)
}

fn modular_stack_offset(value: DifferentialBitVector, offset: i64) -> u64 {
    value.bits().wrapping_add_signed(offset) & width_mask(value.width_bits())
}

fn exact_exit_stack_pointer(
    entry: DifferentialBitVector,
    actual: DifferentialBitVector,
    stack_pointer_delta_bytes: Option<u32>,
) -> bool {
    if entry.width_bits() != actual.width_bits() {
        return false;
    }
    let delta = stack_pointer_delta_bytes.map(i64::from).unwrap_or(0);
    actual.bits() == modular_stack_offset(entry, delta)
}

fn exact_return_address_event(
    event: &DifferentialMemoryEvent,
    statement: &CertifiedMemoryStatement,
    entry: DifferentialBitVector,
    stack_offset: i64,
    slot_size_bytes: u32,
) -> bool {
    private_event_matches_statement(event, statement)
        && event.byte_address == modular_stack_offset(entry, stack_offset)
        && event.width_bits / 8 == slot_size_bytes
        && statement.width_bits() / 8 == slot_size_bytes
}

fn validate_private_join_frame_authority(
    projection: &CertifiedMachineProjection,
    join: &CertifiedPrivateFrameConditionalJoin,
) -> Result<(), RunFailure> {
    if projection.frame_preservation() != join.frame_preservation() {
        return Err(RunFailure::Invalid(
            "private join frame preservation differs from the machine projection".to_string(),
        ));
    }
    Ok(())
}

fn exact_private_join_frame_restore<'a>(
    frame: &'a CertifiedFramePreservation,
    join: &CertifiedPrivateFrameConditionalJoin,
) -> Result<&'a CertifiedFrameRestore, RunFailure> {
    let matching = frame
        .restores()
        .iter()
        .filter(|restore| restore.return_control() == join.return_control())
        .collect::<Vec<_>>();
    let [restore] = matching.as_slice() else {
        return Err(RunFailure::Invalid(
            "private join lacks one exact frame restore".to_string(),
        ));
    };
    Ok(*restore)
}

fn private_frame_entry_value(
    artifact: &SsaArtifact,
    projection: &CertifiedMachineProjection,
    frame: &CertifiedFramePreservation,
    initial: &DifferentialState,
) -> Result<DifferentialBitVector, RunFailure> {
    let CertifiedMemoryStatementKind::Write { value } = frame.entry_save().kind() else {
        return Err(RunFailure::Invalid(
            "frame entry save is not an exact write".to_string(),
        ));
    };
    let boundary = if let Some(first) = frame.entry_save_copies().first() {
        let expression = projection
            .projection()
            .expr(first.root())
            .ok_or_else(|| RunFailure::Invalid("frame entry copy root is missing".to_string()))?;
        let MachineExprKind::Copy { input } = expression.kind() else {
            return Err(RunFailure::Invalid(
                "frame entry copy is not bit-preserving".to_string(),
            ));
        };
        let source = projection
            .projection()
            .expr(*input)
            .ok_or_else(|| RunFailure::Invalid("frame entry copy input is missing".to_string()))?;
        let MachineExprKind::Source { binding, .. } = source.kind() else {
            return Err(RunFailure::Invalid(
                "frame entry copy does not begin at a source boundary".to_string(),
            ));
        };
        let last = frame
            .entry_save_copies()
            .last()
            .expect("checked nonempty frame entry copies");
        let output = projection
            .projection()
            .entity_for_producer(last.entity().producer())
            .map(|entity| entity.output())
            .ok_or_else(|| RunFailure::Invalid("frame entry copy output is missing".to_string()))?;
        if output != value.binding() {
            return Err(RunFailure::Invalid(
                "frame entry copy chain does not reach the saved value".to_string(),
            ));
        }
        *binding
    } else {
        value.binding()
    };
    if artifact.graph().def_inst(boundary.value()).is_some()
        || boundary.width_bits() != frame.entry_save().width_bits()
    {
        return Err(RunFailure::Invalid(
            "frame entry save does not originate at an exact boundary value".to_string(),
        ));
    }
    let entry = initial
        .values
        .get(&boundary.value())
        .copied()
        .ok_or(RunFailure::MissingBoundaryInput(boundary.value()))?;
    require_width(entry, boundary.width_bits())?;
    Ok(entry)
}

fn validate_private_frame_restored_value(
    entry: DifferentialBitVector,
    restored: DifferentialBitVector,
    width_bits: u32,
) -> Result<(), RunFailure> {
    require_width(entry, width_bits)?;
    require_width(restored, width_bits)?;
    if restored != entry {
        return Err(RunFailure::Invalid(
            "private frame did not restore the entry frame pointer".to_string(),
        ));
    }
    Ok(())
}

fn execute_private_frame_join_source(
    artifact: &SsaArtifact,
    projection: &CertifiedMachineProjection,
    function: &CertifiedPrivateFrameConditionalJoinFunction,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> (InterpreterResult, Option<bool>) {
    let join = function.rewrite().machine_join();
    let mut state = ExecutionState::from(initial);
    let mut remaining_steps = limits.max_source_steps;
    let mut visited = BTreeSet::new();
    let result = (|| {
        validate_private_join_frame_authority(projection, join)?;
        let frame_restore = join
            .frame_preservation()
            .map(|frame| {
                Ok((
                    exact_private_join_frame_restore(frame, join)?,
                    private_frame_entry_value(artifact, projection, frame, initial)?,
                ))
            })
            .transpose()?;
        if !visited.insert(join.header()) {
            return Err(RunFailure::Invalid(
                "private-join route contains a cycle".to_string(),
            ));
        }
        execute_private_join_block(
            artifact,
            join.header(),
            &mut state,
            &mut remaining_steps,
            &BTreeMap::new(),
        )?;
        let target = source_conditional_target(artifact, join.header(), &state)?;
        let (arm, selected_true) = private_join_route(join, target)?;
        let mut next = arm.entry_target();
        for transparent in arm.transparent() {
            if transparent.block_addr() != next {
                return Err(RunFailure::Invalid(
                    "transparent arm chain is not source ordered".to_string(),
                ));
            }
            if !visited.insert(next) {
                return Err(RunFailure::Invalid(
                    "private-join route contains a cycle".to_string(),
                ));
            }
            execute_private_join_block(
                artifact,
                next,
                &mut state,
                &mut remaining_steps,
                &BTreeMap::new(),
            )?;
            let source_target = exact_source_direct_target(artifact, next)?;
            if source_target != transparent.control().target() {
                return Err(RunFailure::Invalid(
                    "transparent control target differs from source".to_string(),
                ));
            }
            next = source_target;
        }
        if next != arm.store_block() || arm.join_transfer().target() != join.join_block() {
            return Err(RunFailure::Invalid(
                "sealed arm does not terminate at the shared join".to_string(),
            ));
        }
        if !visited.insert(arm.store_block()) {
            return Err(RunFailure::Invalid(
                "private-join route contains a cycle".to_string(),
            ));
        }
        execute_private_join_block(
            artifact,
            arm.store_block(),
            &mut state,
            &mut remaining_steps,
            &BTreeMap::new(),
        )?;
        if exact_source_direct_target(artifact, arm.store_block())? != arm.join_transfer().target()
        {
            return Err(RunFailure::Invalid(
                "arm store transfer target differs from source".to_string(),
            ));
        }
        let inert = join
            .inert_join_phis()
            .iter()
            .map(|phi| {
                (
                    phi.producer(),
                    (phi.output(), phi.predecessors().to_vec().into_boxed_slice()),
                )
            })
            .collect::<BTreeMap<_, _>>();
        if inert.len() != join.inert_join_phis().len() {
            return Err(RunFailure::Invalid(
                "duplicate certified inert phi identity".to_string(),
            ));
        }
        if !visited.insert(join.join_block()) {
            return Err(RunFailure::Invalid(
                "private-join route contains a cycle".to_string(),
            ));
        }
        execute_private_join_block(
            artifact,
            join.join_block(),
            &mut state,
            &mut remaining_steps,
            &inert,
        )?;
        if let Some((restore, entry_frame_pointer)) = frame_restore {
            let restored = state
                .values
                .get(&restore.restore_assignment().output().value())
                .copied()
                .ok_or_else(|| {
                    RunFailure::Invalid("restored frame pointer is missing".to_string())
                })?;
            validate_private_frame_restored_value(
                entry_frame_pointer,
                restored,
                restore.restore_assignment().output().width_bits(),
            )?;
        }
        let stack = projection.stack_discipline().ok_or_else(|| {
            RunFailure::Invalid("private join lost its stack discipline".to_string())
        })?;
        let entry_sp = semantic_value_use(
            artifact,
            join.header(),
            &ExecutionState::from(initial),
            stack.entry_stack_pointer(),
            None,
        )?;
        let restored = state
            .values
            .get(&join.release().restoration().output().value())
            .copied()
            .ok_or_else(|| RunFailure::Invalid("restored stack pointer is missing".to_string()))?;
        if restored != entry_sp {
            return Err(RunFailure::Invalid(
                "private frame did not restore the entry stack pointer".to_string(),
            ));
        }
        let mechanism = artifact
            .machine_context()
            .function_interface()
            .and_then(|interface| interface.return_mechanism());
        let exit_value = if let Some(exit) = join.release().exit_stack_pointer().value() {
            let value = state
                .values
                .get(&exit.binding().value())
                .copied()
                .ok_or_else(|| {
                    RunFailure::Invalid("certified exit stack pointer is missing".to_string())
                })?;
            require_width(value, exit.binding().width_bits())?;
            if let Some(post) = join.release().post_restoration()
                && post.output() != exit.binding()
            {
                return Err(RunFailure::Invalid(
                    "post-restoration assignment differs from exit stack pointer".to_string(),
                ));
            }
            value
        } else {
            restored
        };
        if !exact_exit_stack_pointer(
            entry_sp,
            exit_value,
            mechanism.map(|mechanism| mechanism.stack_pointer_delta_bytes()),
        ) {
            return Err(RunFailure::Invalid(
                "dynamic exit stack pointer differs from the exact source return mechanism"
                    .to_string(),
            ));
        }
        let block = artifact
            .graph()
            .block_id_for_addr(join.join_block())
            .and_then(|id| artifact.graph().block(id))
            .ok_or_else(|| RunFailure::Invalid("shared join block is missing".to_string()))?;
        let run = observed_source_run(artifact, block, state.clone())?;
        Ok((run, selected_true))
    })();
    match result {
        Ok((run, selected_true)) => (
            source_terminalize_run(artifact, join.join_block(), Ok(run)),
            Some(selected_true),
        ),
        Err(failure) => (
            Err(FailedRun {
                failure,
                trace: observed_trace(&state),
            }),
            None,
        ),
    }
}

fn execute_source_inner(
    artifact: &SsaArtifact,
    block_addr: u64,
    state: &mut ExecutionState,
    limits: DifferentialLimits,
) -> Result<DifferentialObservedRun, RunFailure> {
    let graph = artifact.graph();
    let block = graph
        .block_id_for_addr(block_addr)
        .and_then(|id| graph.block(id))
        .ok_or_else(|| RunFailure::Invalid("selected graph block is missing".to_string()))?;
    if block.insts.len() > limits.max_source_steps as usize {
        return Err(RunFailure::BudgetExceeded);
    }
    for inst_id in &block.insts {
        execute_source_inst(artifact, state, *inst_id)?;
    }
    observed_source_run(artifact, block, state.clone())
}

fn execute_source_inst(
    artifact: &SsaArtifact,
    state: &mut ExecutionState,
    inst_id: r2ssa::InstId,
) -> Result<(), RunFailure> {
    let inst = artifact
        .graph()
        .inst(inst_id)
        .ok_or_else(|| RunFailure::Invalid(format!("missing instruction {inst_id:?}")))?;
    let producer = artifact
        .obligations()
        .instruction_for_inst(inst_id)
        .map(|instruction| instruction.id)
        .ok_or_else(|| RunFailure::Invalid(format!("missing source ID for {inst_id:?}")))?;
    let InstPayload::Op(op) = &inst.payload else {
        return Err(RunFailure::Unsupported(
            "phi execution requires a certified incoming edge".to_string(),
        ));
    };
    match op {
        SSAOp::Nop
        | SSAOp::Branch { .. }
        | SSAOp::Return { .. }
        | SSAOp::Call { .. }
        | SSAOp::CBranch { .. } => {}
        SSAOp::Load { .. } => {
            let access = source_memory_access(artifact, inst_id, false)?;
            if inst.inputs.as_slice() != [access.address] || inst.output != access.value {
                return Err(RunFailure::Invalid(
                    "load operands differ from structured memory fact".to_string(),
                ));
            }
            let output = inst
                .output
                .ok_or_else(|| RunFailure::Invalid("load has no output".to_string()))?;
            let address = source_value(artifact, state, access.address)?;
            let memory = source_memory_model(artifact, access.source_space)?;
            source_validate_memory_shape(
                access.width_bits,
                memory.word_size_bytes,
                memory.endianness,
            )?;
            let value = source_read_memory(
                &state.memory,
                memory.space,
                address.bits,
                memory.address_bits,
                access.width_bits,
                memory.endianness,
            )?;
            state.events.push(DifferentialMemoryEvent {
                producer,
                access: access.id,
                object: access.object,
                kind: DifferentialMemoryEventKind::Read,
                space: memory.space,
                byte_address: address.bits,
                width_bits: access.width_bits,
                endianness: memory.endianness,
                value,
            });
            bind_source_output(artifact, state, output, value)?;
        }
        SSAOp::Store { .. } => {
            let access = source_memory_access(artifact, inst_id, true)?;
            let [address_id, value_id] = inst.inputs.as_slice() else {
                return Err(RunFailure::Invalid(
                    "store does not have exactly two inputs".to_string(),
                ));
            };
            if *address_id != access.address || access.value != Some(*value_id) {
                return Err(RunFailure::Invalid(
                    "store operands differ from structured memory fact".to_string(),
                ));
            }
            let address = source_value(artifact, state, *address_id)?;
            let value = source_value(artifact, state, *value_id)?;
            let memory = source_memory_model(artifact, access.source_space)?;
            source_validate_memory_shape(
                access.width_bits,
                memory.word_size_bytes,
                memory.endianness,
            )?;
            if value.width_bits != access.width_bits {
                return Err(RunFailure::Invalid(
                    "store value width differs from access width".to_string(),
                ));
            }
            source_write_memory(
                &mut state.memory,
                memory.space,
                address.bits,
                memory.address_bits,
                value,
                memory.endianness,
            )?;
            state.events.push(DifferentialMemoryEvent {
                producer,
                access: access.id,
                object: access.object,
                kind: DifferentialMemoryEventKind::Write,
                space: memory.space,
                byte_address: address.bits,
                width_bits: access.width_bits,
                endianness: memory.endianness,
                value,
            });
        }
        _ => execute_source_value_op(artifact, state, inst, op)?,
    }
    Ok(())
}

struct SourceMemoryModel {
    space: MachineAddressSpace,
    address_bits: u32,
    endianness: MachineMemoryEndianness,
    word_size_bytes: u32,
}

struct SourceMemoryAccess {
    id: StructuredAccessId,
    object: ObjectId,
    address: ValueId,
    value: Option<ValueId>,
    width_bits: u32,
    source_space: r2il::SpaceId,
}

fn memory_space_authorities_match(
    graph_space: r2il::SpaceId,
    prepared_space: r2il::SpaceId,
    context_space: r2il::SpaceId,
    fact_space: r2il::SpaceId,
    object_space: r2il::SpaceId,
) -> bool {
    graph_space == prepared_space
        && graph_space == context_space
        && graph_space == fact_space
        && graph_space == object_space
}

fn source_memory_access(
    artifact: &SsaArtifact,
    inst: r2ssa::InstId,
    is_write: bool,
) -> Result<SourceMemoryAccess, RunFailure> {
    let graph_inst = artifact
        .graph()
        .inst(inst)
        .ok_or_else(|| RunFailure::Invalid("memory graph instruction is missing".to_string()))?;
    let (block_addr, op_index) = artifact
        .graph()
        .op_site_for_inst(inst)
        .ok_or_else(|| RunFailure::Invalid("memory operation site is missing".to_string()))?;
    let prepared_op = artifact
        .function()
        .get_block(block_addr)
        .and_then(|block| block.ops.get(op_index))
        .ok_or_else(|| RunFailure::Invalid("prepared memory operation is missing".to_string()))?;
    let source_space = artifact
        .machine_context()
        .memory_space_at(block_addr, op_index)
        .ok_or_else(|| RunFailure::Invalid("prepared memory space is missing".to_string()))?;
    let (address, value, width_bits, graph_space, prepared_space) =
        match (&graph_inst.payload, prepared_op) {
            (
                InstPayload::Op(SSAOp::Load {
                    dst,
                    space: graph_space,
                    addr,
                }),
                SSAOp::Load {
                    dst: prepared_dst,
                    space: prepared_space,
                    addr: prepared_addr,
                },
            ) if !is_write
                && dst == prepared_dst
                && addr == prepared_addr
                && graph_space == prepared_space
                && *graph_space == source_space =>
            {
                (
                    artifact.graph().value_id_for_var(addr).ok_or_else(|| {
                        RunFailure::Invalid("SSA load address is missing".to_string())
                    })?,
                    artifact.graph().value_id_for_var(dst),
                    dst.size
                        .checked_mul(8)
                        .ok_or_else(|| RunFailure::Invalid("load width overflow".to_string()))?,
                    *graph_space,
                    *prepared_space,
                )
            }
            (
                InstPayload::Op(SSAOp::Store {
                    space: graph_space,
                    addr,
                    val,
                }),
                SSAOp::Store {
                    space: prepared_space,
                    addr: prepared_addr,
                    val: prepared_value,
                },
            ) if is_write
                && addr == prepared_addr
                && val == prepared_value
                && graph_space == prepared_space
                && *graph_space == source_space =>
            {
                (
                    artifact.graph().value_id_for_var(addr).ok_or_else(|| {
                        RunFailure::Invalid("SSA store address is missing".to_string())
                    })?,
                    Some(artifact.graph().value_id_for_var(val).ok_or_else(|| {
                        RunFailure::Invalid("SSA store value is missing".to_string())
                    })?),
                    val.size
                        .checked_mul(8)
                        .ok_or_else(|| RunFailure::Invalid("store width overflow".to_string()))?,
                    *graph_space,
                    *prepared_space,
                )
            }
            _ => {
                return Err(RunFailure::Invalid(
                    "graph memory operation differs from prepared SSA".to_string(),
                ));
            }
        };
    let id = StructuredAccessId { inst, ordinal: 0 };
    let object = artifact
        .objects()
        .object_for_value(address, source_space)
        .ok_or_else(|| RunFailure::Unsupported("memory object is unresolved".to_string()))?;
    let object_space = artifact
        .objects()
        .object(object)
        .map(|object| object.kind.space())
        .ok_or_else(|| RunFailure::Unsupported("memory object fact is missing".to_string()))?;
    let facts = artifact
        .facts()
        .structured
        .memory_accesses
        .values()
        .filter(|fact| fact.id.inst == inst)
        .collect::<Vec<_>>();
    let [fact] = facts.as_slice() else {
        return Err(RunFailure::Unsupported(
            "memory instruction lacks one exact structured access".to_string(),
        ));
    };
    if !fact.provenance_complete
        || fact.id != id
        || fact.is_write != is_write
        || fact.object != object
        || !memory_space_authorities_match(
            graph_space,
            prepared_space,
            source_space,
            fact.space,
            object_space,
        )
        || fact.address != address
        || fact.value != value
        || fact.width.checked_mul(8) != Some(width_bits)
        || fact.block_addr != block_addr
        || fact.op_index != op_index
        || artifact
            .machine_context()
            .memory_space_at(block_addr, op_index)
            != Some(source_space)
    {
        return Err(RunFailure::Unsupported(
            "memory access provenance is incomplete".to_string(),
        ));
    }
    Ok(SourceMemoryAccess {
        id,
        object,
        address,
        value,
        width_bits,
        source_space,
    })
}

fn source_memory_model(
    artifact: &SsaArtifact,
    source_space: r2il::SpaceId,
) -> Result<SourceMemoryModel, RunFailure> {
    let model = artifact.machine_context().memory_model();
    let space = model
        .space(source_space)
        .filter(|_| model.is_available() && model.is_coherent())
        .ok_or_else(|| {
            RunFailure::Unsupported("machine memory model is unavailable".to_string())
        })?;
    Ok(SourceMemoryModel {
        space: MachineAddressSpace::from(source_space),
        address_bits: space.address_bits(),
        endianness: space.endianness(),
        word_size_bytes: space.word_size_bytes(),
    })
}

fn execute_source_value_op(
    artifact: &SsaArtifact,
    state: &mut ExecutionState,
    inst: &r2ssa::GraphInst,
    op: &SSAOp,
) -> Result<(), RunFailure> {
    let output = inst.output.ok_or_else(|| {
        RunFailure::Unsupported(format!("operation without admitted output: {op:?}"))
    })?;
    let output_width = graph_value_width(artifact, output)?;
    let input = |index: usize| {
        inst.inputs
            .get(index)
            .copied()
            .ok_or_else(|| RunFailure::Invalid(format!("missing operand {index}")))
            .and_then(|value| source_value(artifact, state, value))
    };
    let result = match op {
        SSAOp::Copy { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            require_width(value, output_width)?;
            value
        }
        SSAOp::IntAdd { .. } | SSAOp::IntSub { .. } | SSAOp::IntMult { .. } => {
            require_operand_count(inst, 2)?;
            let left = input(0)?;
            let right = input(1)?;
            require_binary_widths(left, right, output_width)?;
            let bits = match op {
                SSAOp::IntAdd { .. } => left.bits.wrapping_add(right.bits),
                SSAOp::IntSub { .. } => left.bits.wrapping_sub(right.bits),
                SSAOp::IntMult { .. } => left.bits.wrapping_mul(right.bits),
                _ => unreachable!(),
            };
            source_bitvector(output_width, bits)?
        }
        SSAOp::IntAnd { .. } | SSAOp::IntOr { .. } | SSAOp::IntXor { .. } => {
            require_operand_count(inst, 2)?;
            let left = input(0)?;
            let right = input(1)?;
            require_binary_widths(left, right, output_width)?;
            let bits = match op {
                SSAOp::IntAnd { .. } => left.bits & right.bits,
                SSAOp::IntOr { .. } => left.bits | right.bits,
                SSAOp::IntXor { .. } => left.bits ^ right.bits,
                _ => unreachable!(),
            };
            source_bitvector(output_width, bits)?
        }
        SSAOp::IntNot { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            require_width(value, output_width)?;
            source_bitvector(output_width, !value.bits)?
        }
        SSAOp::PopCount { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            source_bitvector(output_width, u64::from(value.bits.count_ones()))?
        }
        SSAOp::IntCarry { .. } | SSAOp::IntSCarry { .. } | SSAOp::IntSBorrow { .. } => {
            require_operand_count(inst, 2)?;
            let left = input(0)?;
            let right = input(1)?;
            if left.width_bits != right.width_bits {
                return Err(RunFailure::Invalid(
                    "flag operand widths differ".to_string(),
                ));
            }
            let mask = u128::from(source_width_mask(left.width_bits));
            let sign = 1u64 << (left.width_bits - 1);
            let flag = match op {
                SSAOp::IntCarry { .. } => u128::from(left.bits) + u128::from(right.bits) > mask,
                SSAOp::IntSCarry { .. } => {
                    let result = left.bits.wrapping_add(right.bits) & mask as u64;
                    ((left.bits ^ result) & (right.bits ^ result) & sign) != 0
                }
                SSAOp::IntSBorrow { .. } => {
                    let result = left.bits.wrapping_sub(right.bits) & mask as u64;
                    ((left.bits ^ right.bits) & (left.bits ^ result) & sign) != 0
                }
                _ => unreachable!(),
            };
            source_bitvector(output_width, u64::from(flag))?
        }
        SSAOp::BoolNot { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            require_width(value, output_width)?;
            if value.bits > 1 {
                return Err(RunFailure::Invalid(
                    "boolean negation operand is not canonical".to_string(),
                ));
            }
            source_bitvector(output_width, u64::from(value.bits == 0))?
        }
        SSAOp::BoolAnd { .. } | SSAOp::BoolOr { .. } | SSAOp::BoolXor { .. } => {
            require_operand_count(inst, 2)?;
            let left = input(0)?;
            let right = input(1)?;
            require_binary_widths(left, right, output_width)?;
            if left.bits > 1 || right.bits > 1 {
                return Err(RunFailure::Invalid(
                    "boolean binary operand is not canonical".to_string(),
                ));
            }
            let bits = match op {
                SSAOp::BoolAnd { .. } => left.bits & right.bits,
                SSAOp::BoolOr { .. } => left.bits | right.bits,
                SSAOp::BoolXor { .. } => left.bits ^ right.bits,
                _ => unreachable!(),
            };
            source_bitvector(output_width, bits)?
        }
        SSAOp::IntLeft { .. } | SSAOp::IntRight { .. } | SSAOp::IntSRight { .. } => {
            require_operand_count(inst, 2)?;
            let value = input(0)?;
            let count = input(1)?;
            require_width(value, output_width)?;
            let kind = match op {
                SSAOp::IntLeft { .. } => MachineShiftKind::Left,
                SSAOp::IntRight { .. } => MachineShiftKind::LogicalRight,
                SSAOp::IntSRight { .. } => MachineShiftKind::ArithmeticRight,
                _ => unreachable!(),
            };
            source_shift_value(kind, value, count.bits)?
        }
        SSAOp::IntEqual { .. }
        | SSAOp::IntNotEqual { .. }
        | SSAOp::IntLess { .. }
        | SSAOp::IntSLess { .. }
        | SSAOp::IntLessEqual { .. }
        | SSAOp::IntSLessEqual { .. } => {
            require_operand_count(inst, 2)?;
            let left = input(0)?;
            let right = input(1)?;
            if left.width_bits != right.width_bits {
                return Err(RunFailure::Invalid(
                    "comparison operand widths differ".to_string(),
                ));
            }
            let condition = match op {
                SSAOp::IntEqual { .. } => left.bits == right.bits,
                SSAOp::IntNotEqual { .. } => left.bits != right.bits,
                SSAOp::IntLess { .. } => left.bits < right.bits,
                SSAOp::IntLessEqual { .. } => left.bits <= right.bits,
                SSAOp::IntSLess { .. } => source_signed_key(left) < source_signed_key(right),
                SSAOp::IntSLessEqual { .. } => source_signed_key(left) <= source_signed_key(right),
                _ => unreachable!(),
            };
            source_bitvector(output_width, u64::from(condition))?
        }
        SSAOp::IntZExt { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            if output_width <= value.width_bits {
                return Err(RunFailure::Invalid("invalid zero extension".to_string()));
            }
            source_bitvector(output_width, value.bits)?
        }
        SSAOp::IntSExt { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            if output_width <= value.width_bits {
                return Err(RunFailure::Invalid("invalid sign extension".to_string()));
            }
            source_sign_extend(value, output_width)?
        }
        SSAOp::Trunc { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            if output_width >= value.width_bits {
                return Err(RunFailure::Invalid("invalid truncation".to_string()));
            }
            source_bitvector(output_width, value.bits)?
        }
        SSAOp::Cast { .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            require_width(value, output_width)?;
            value
        }
        SSAOp::Subpiece { offset, .. } => {
            require_operand_count(inst, 1)?;
            let value = input(0)?;
            let lsb_bits = offset
                .checked_mul(8)
                .ok_or_else(|| RunFailure::Invalid("subpiece offset overflow".to_string()))?;
            if lsb_bits
                .checked_add(output_width)
                .is_none_or(|end| end > value.width_bits)
            {
                return Err(RunFailure::Invalid("invalid subpiece range".to_string()));
            }
            source_bitvector(output_width, value.bits >> lsb_bits)?
        }
        SSAOp::Select { .. } => {
            require_operand_count(inst, 3)?;
            let condition = input(0)?;
            let selected = if condition.bits != 0 {
                input(1)?
            } else {
                input(2)?
            };
            require_width(selected, output_width)?;
            selected
        }
        _ => {
            return Err(RunFailure::Unsupported(format!(
                "source operation is outside the differential subset: {op:?}"
            )));
        }
    };
    bind_source_output(artifact, state, output, result)
}

fn source_value(
    artifact: &SsaArtifact,
    state: &ExecutionState,
    id: ValueId,
) -> Result<DifferentialBitVector, RunFailure> {
    let graph_value = artifact
        .graph()
        .value(id)
        .ok_or_else(|| RunFailure::Invalid(format!("unknown source value {id:?}")))?;
    let width = value_width(graph_value.var.size).map_err(RunFailure::Invalid)?;
    if let Some(bits) = graph_value.var.constant_bits() {
        if width < 64 && bits > source_width_mask(width) {
            return Err(RunFailure::Invalid(format!(
                "constant {id:?} exceeds its declared width"
            )));
        }
        return source_bitvector(width, bits);
    }
    let value = state
        .values
        .get(&id)
        .copied()
        .ok_or(RunFailure::MissingBoundaryInput(id))?;
    require_width(value, width)?;
    Ok(value)
}

fn bind_source_output(
    artifact: &SsaArtifact,
    state: &mut ExecutionState,
    output: ValueId,
    value: DifferentialBitVector,
) -> Result<(), RunFailure> {
    let width = graph_value_width(artifact, output)?;
    require_width(value, width)?;
    if state.values.insert(output, value).is_some() {
        return Err(RunFailure::Invalid(format!(
            "source value {output:?} was assigned twice"
        )));
    }
    Ok(())
}

fn execute_semantic(
    artifact: &SsaArtifact,
    layer: &SemanticCBlockStepLayer,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> InterpreterResult {
    let mut state = ExecutionState::from(initial);
    let mut remaining_expression_nodes = limits.max_expression_nodes;
    execute_semantic_inner(artifact, layer, &mut state, &mut remaining_expression_nodes).map_err(
        |failure| FailedRun {
            failure,
            trace: observed_trace(&state),
        },
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RenderedConditionalReturn {
    Void,
    Value(ValueId),
}

fn execute_conditional_semantic(
    artifact: &SsaArtifact,
    function: &CertifiedConditionalReturnFunction,
    rendered_c: &str,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> (InterpreterResult, InterpreterResult) {
    let mut header_state = ExecutionState::from(initial);
    let mut remaining_expression_nodes = limits.max_expression_nodes;
    if let Err(failure) = execute_semantic_inner(
        artifact,
        function.header().body(),
        &mut header_state,
        &mut remaining_expression_nodes,
    ) {
        let failed = FailedRun {
            failure,
            trace: observed_trace(&header_state),
        };
        return (Err(failed.clone()), Err(failed));
    }

    let mut semantic_state = header_state.clone();
    let mut semantic_nodes = remaining_expression_nodes;
    let semantic_result = (|| {
        let condition = source_value(
            artifact,
            &semantic_state,
            function.header().transfer().condition().binding().value(),
        )?;
        if condition.width_bits() != 8 {
            return Err(RunFailure::Invalid(
                "conditional semantic predicate is not eight bits".to_string(),
            ));
        }
        let arm = conditional_arm(function, condition);
        let run = execute_semantic_inner(
            artifact,
            arm.layer(),
            &mut semantic_state,
            &mut semantic_nodes,
        )?;
        Ok((run, arm))
    })();
    let semantic = match semantic_result {
        Ok((run, arm)) => terminalize_run(
            Ok(run),
            arm.returned().expect("audited conditional return arm"),
        ),
        Err(failure) => Err(FailedRun {
            failure,
            trace: observed_trace(&semantic_state),
        }),
    };

    let mut rendered_state = header_state;
    let mut rendered_nodes = remaining_expression_nodes;
    let rendered_result = (|| {
        let (selected_true_arm, returned) =
            parse_rendered_conditional_return(rendered_c, &rendered_state)?;
        let layer = rendered_return_layer(function, selected_true_arm, returned)?;
        let run =
            execute_semantic_inner(artifact, layer, &mut rendered_state, &mut rendered_nodes)?;
        Ok((run, returned))
    })();
    let rendered = match rendered_result {
        Ok((run, returned)) => terminalize_rendered_run(Ok(run), returned),
        Err(failure) => Err(FailedRun {
            failure,
            trace: observed_trace(&rendered_state),
        }),
    };
    (semantic, rendered)
}

fn parse_rendered_conditional_return(
    rendered_c: &str,
    state: &ExecutionState,
) -> Result<(bool, RenderedConditionalReturn), RunFailure> {
    const PREFIX: &str = "\n\tif ((uint8_t)(";
    if rendered_c.match_indices(PREFIX).count() != 1 {
        return Err(RunFailure::Invalid(
            "rendered conditional has no unique strict if statement".to_string(),
        ));
    }
    let (_, conditional) = rendered_c.split_once(PREFIX).ok_or_else(|| {
        RunFailure::Invalid("rendered conditional if statement is missing".to_string())
    })?;
    let (condition_line, arms) = conditional.split_once('\n').ok_or_else(|| {
        RunFailure::Invalid("rendered conditional if line is unterminated".to_string())
    })?;
    let (condition_expression, nonzero_is_true) =
        if let Some(expression) = condition_line.strip_suffix(") != UINT8_C(0)) {") {
            (expression, true)
        } else if let Some(expression) = condition_line.strip_suffix(") == UINT8_C(0)) {") {
            (expression, false)
        } else {
            return Err(RunFailure::Invalid(
                "rendered conditional predicate is outside the strict C grammar".to_string(),
            ));
        };
    let condition = parse_rendered_condition_value(condition_expression, state)?;
    let selected_true_arm = (condition.bits() != 0) == nonzero_is_true;
    let (true_arm, false_arm) = arms.split_once("\t} else {\n").ok_or_else(|| {
        RunFailure::Invalid("rendered conditional else arm is missing".to_string())
    })?;
    let false_arm = false_arm.strip_suffix("\t}\n}\n").ok_or_else(|| {
        RunFailure::Invalid("rendered conditional function tail is malformed".to_string())
    })?;
    let selected = if selected_true_arm {
        true_arm
    } else {
        false_arm
    };
    Ok((selected_true_arm, parse_rendered_return(selected)?))
}

fn parse_rendered_condition_value(
    expression: &str,
    state: &ExecutionState,
) -> Result<DifferentialBitVector, RunFailure> {
    let value = if let Some(value) = expression.strip_prefix("v_") {
        let id = value.parse::<u32>().map(ValueId).map_err(|_| {
            RunFailure::Invalid("rendered predicate value name is malformed".to_string())
        })?;
        state.values.get(&id).copied().ok_or_else(|| {
            RunFailure::Invalid("rendered predicate value is unavailable".to_string())
        })?
    } else if let Some(value) = expression
        .strip_prefix("((uint8_t)UINT64_C(0x")
        .and_then(|value| value.strip_suffix("))"))
    {
        let bits = u64::from_str_radix(value, 16).map_err(|_| {
            RunFailure::Invalid("rendered constant predicate is malformed".to_string())
        })?;
        semantic_bitvector(8, bits)?
    } else {
        return Err(RunFailure::Invalid(
            "rendered predicate expression is outside the strict C grammar".to_string(),
        ));
    };
    if value.width_bits() != 8 {
        return Err(RunFailure::Invalid(
            "rendered conditional predicate is not eight bits".to_string(),
        ));
    }
    Ok(value)
}

fn parse_rendered_return(body: &str) -> Result<RenderedConditionalReturn, RunFailure> {
    let mut returns = body
        .lines()
        .filter(|line| line.trim_start().starts_with("return"));
    let returned = returns
        .next()
        .ok_or_else(|| RunFailure::Invalid("rendered conditional arm has no return".to_string()))?;
    if returns.next().is_some()
        || body.lines().last() != Some(returned)
        || !returned.starts_with("\t\treturn")
    {
        return Err(RunFailure::Invalid(
            "rendered conditional arm does not end in one strict return".to_string(),
        ));
    }
    if returned == "\t\treturn;" {
        return Ok(RenderedConditionalReturn::Void);
    }
    let value = returned
        .strip_prefix("\t\treturn v_")
        .and_then(|value| value.strip_suffix(';'))
        .ok_or_else(|| {
            RunFailure::Invalid("rendered return value is outside the strict C grammar".to_string())
        })?
        .parse::<u32>()
        .map(ValueId)
        .map_err(|_| RunFailure::Invalid("rendered return value is malformed".to_string()))?;
    Ok(RenderedConditionalReturn::Value(value))
}

fn rendered_return_layer(
    function: &CertifiedConditionalReturnFunction,
    selected_true_arm: bool,
    returned: RenderedConditionalReturn,
) -> Result<&SemanticCBlockStepLayer, RunFailure> {
    if returned == RenderedConditionalReturn::Void {
        return Ok(if selected_true_arm {
            function.true_arm().layer()
        } else {
            function.false_arm().layer()
        });
    }
    let RenderedConditionalReturn::Value(value) = returned else {
        unreachable!();
    };
    let mut matching = [function.true_arm().layer(), function.false_arm().layer()]
        .into_iter()
        .filter(|layer| {
            layer.steps().iter().any(|step| {
                step.value().is_some_and(|reference| {
                    layer
                        .resolve_value(reference)
                        .is_some_and(|entity| entity.output().value() == value)
                })
            })
        });
    let layer = matching.next().ok_or_else(|| {
        RunFailure::Invalid("rendered return has no semantic value producer".to_string())
    })?;
    if matching.next().is_some() {
        return Err(RunFailure::Invalid(
            "rendered return has multiple semantic value producers".to_string(),
        ));
    }
    Ok(layer)
}

fn execute_semantic_inner(
    artifact: &SsaArtifact,
    layer: &SemanticCBlockStepLayer,
    state: &mut ExecutionState,
    remaining_expression_nodes: &mut u32,
) -> Result<DifferentialObservedRun, RunFailure> {
    let mut executed = BTreeSet::new();
    let mut executed_accesses = BTreeSet::new();
    let mut reads = BTreeMap::new();
    for step in layer.steps() {
        if !executed.insert(step.source()) {
            return Err(RunFailure::Invalid(
                "semantic source step executed twice".to_string(),
            ));
        }
        if let Some(reference) = step.memory() {
            let statement = layer.resolve_memory_statement(reference).ok_or_else(|| {
                RunFailure::Invalid("memory reference does not resolve".to_string())
            })?;
            execute_semantic_memory(
                artifact,
                layer,
                state,
                &mut reads,
                &mut executed_accesses,
                statement,
            )?;
        }
        if let Some(reference) = step.value() {
            let entity = layer.resolve_value(reference).ok_or_else(|| {
                RunFailure::Invalid("value reference does not resolve".to_string())
            })?;
            let mut evaluator = SemanticEvaluator {
                artifact,
                block_addr: layer.accounting().block_addr(),
                expressions: layer.accounting().expression_layer(),
                state,
                reads: &reads,
                output_roots: None,
                rewritten_reads: None,
                consumed_rewrites: None,
                memo: BTreeMap::new(),
                visiting: BTreeSet::new(),
                remaining_nodes: remaining_expression_nodes,
            };
            let value = evaluator.eval(entity.root())?;
            let binding = entity.output();
            require_width(value, binding.width_bits())?;
            if state.values.insert(binding.value(), value).is_some() {
                return Err(RunFailure::Invalid(format!(
                    "semantic value {:?} was assigned twice",
                    binding.value()
                )));
            }
        }
    }
    observed_semantic_run(layer, state.clone())
}

#[derive(Debug, Clone)]
struct CachedMemoryRead {
    producer: CanonicalInstructionId,
    object: ObjectId,
    space: MachineAddressSpace,
    endianness: MachineMemoryEndianness,
    word_size_bytes: u32,
    byte_address: u64,
    width_bits: u32,
    value: DifferentialBitVector,
}

fn execute_semantic_memory(
    artifact: &SsaArtifact,
    layer: &SemanticCBlockStepLayer,
    state: &mut ExecutionState,
    reads: &mut BTreeMap<StructuredAccessId, CachedMemoryRead>,
    executed_accesses: &mut BTreeSet<StructuredAccessId>,
    statement: &r2cert::CertifiedMemoryStatement,
) -> Result<(), RunFailure> {
    if statement.execution() != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder {
        return Err(RunFailure::Invalid(
            "memory execution policy is not exactly-once".to_string(),
        ));
    }
    if !executed_accesses.insert(statement.access()) {
        return Err(RunFailure::Invalid(
            "memory access executed twice".to_string(),
        ));
    }
    semantic_validate_memory_shape(
        statement.width_bits(),
        statement.word_size_bytes(),
        statement.endianness(),
    )?;
    let address_bits = match statement.address().ty() {
        MachineType::Address {
            width_bits, space, ..
        } if *space == statement.space() => *width_bits,
        _ => {
            return Err(RunFailure::Invalid(
                "memory statement address lacks its exact address type".to_string(),
            ));
        }
    };
    let address = semantic_value_use(
        artifact,
        layer.accounting().block_addr(),
        state,
        statement.address(),
        Some(statement.access()),
    )?;
    match statement.kind() {
        CertifiedMemoryStatementKind::Read { result } => {
            if result.binding().width_bits() != statement.width_bits()
                || result.producer() != Some(statement.producer())
                || result.memory_access().is_some()
            {
                return Err(RunFailure::Invalid(
                    "certified read result does not match its access".to_string(),
                ));
            }
            let value = semantic_read_memory(
                &state.memory,
                statement.space(),
                address.bits,
                address_bits,
                statement.width_bits(),
                statement.endianness(),
            )?;
            let cached = CachedMemoryRead {
                producer: statement.producer(),
                object: statement.object(),
                space: statement.space(),
                endianness: statement.endianness(),
                word_size_bytes: statement.word_size_bytes(),
                byte_address: address.bits,
                width_bits: statement.width_bits(),
                value,
            };
            if reads.insert(statement.access(), cached).is_some() {
                return Err(RunFailure::Invalid(
                    "memory read access executed twice".to_string(),
                ));
            }
            state.events.push(DifferentialMemoryEvent {
                producer: statement.producer(),
                access: statement.access(),
                object: statement.object(),
                kind: DifferentialMemoryEventKind::Read,
                space: statement.space(),
                byte_address: address.bits,
                width_bits: statement.width_bits(),
                endianness: statement.endianness(),
                value,
            });
        }
        CertifiedMemoryStatementKind::Write { value } => {
            let value = semantic_value_use(
                artifact,
                layer.accounting().block_addr(),
                state,
                value,
                None,
            )?;
            require_width(value, statement.width_bits())?;
            semantic_write_memory(
                &mut state.memory,
                statement.space(),
                address.bits,
                address_bits,
                value,
                statement.endianness(),
            )?;
            state.events.push(DifferentialMemoryEvent {
                producer: statement.producer(),
                access: statement.access(),
                object: statement.object(),
                kind: DifferentialMemoryEventKind::Write,
                space: statement.space(),
                byte_address: address.bits,
                width_bits: statement.width_bits(),
                endianness: statement.endianness(),
                value,
            });
        }
    }
    Ok(())
}

fn semantic_value_use(
    artifact: &SsaArtifact,
    block_addr: u64,
    state: &ExecutionState,
    value: &MachineValueUse,
    expected_access: Option<StructuredAccessId>,
) -> Result<DifferentialBitVector, RunFailure> {
    let binding = value.binding();
    if binding.width_bits() != value.ty().width_bits() || value.memory_access() != expected_access {
        return Err(RunFailure::Invalid(
            "machine value use type or access mismatch".to_string(),
        ));
    }
    if value.producer() != canonical_producer_for_value(artifact, binding.value())? {
        return Err(RunFailure::Invalid(
            "machine value use producer differs from the source graph".to_string(),
        ));
    }
    if let Some(constant) = value.constant() {
        if constant.width_bits() != binding.width_bits() {
            return Err(RunFailure::Invalid(
                "machine constant width mismatch".to_string(),
            ));
        }
        let source_constant = artifact
            .graph()
            .value(binding.value())
            .and_then(|value| value.var.constant_bits())
            .ok_or_else(|| {
                RunFailure::Invalid("machine constant lacks a source constant".to_string())
            })?;
        if source_constant != constant.bits() {
            return Err(RunFailure::Invalid(
                "machine constant differs from the source bitvector".to_string(),
            ));
        }
        return semantic_bitvector(constant.width_bits(), constant.bits());
    }
    if artifact
        .graph()
        .value(binding.value())
        .is_some_and(|value| value.var.constant_bits().is_some())
    {
        return Err(RunFailure::Invalid(
            "source constant was downgraded to a runtime value".to_string(),
        ));
    }
    let locally_produced = artifact
        .graph()
        .def_inst(binding.value())
        .and_then(|inst| artifact.graph().inst(inst))
        .and_then(|inst| artifact.graph().block(inst.block))
        .is_some_and(|block| block.addr == block_addr);
    let resolved = state.values.get(&binding.value()).copied().ok_or_else(|| {
        if locally_produced {
            RunFailure::Invalid(format!(
                "local producer has not executed for {:?}",
                binding.value()
            ))
        } else {
            RunFailure::MissingBoundaryInput(binding.value())
        }
    })?;
    require_width(resolved, binding.width_bits())?;
    Ok(resolved)
}

fn semantic_binding_value(
    artifact: &SsaArtifact,
    block_addr: u64,
    state: &ExecutionState,
    binding: MachineValueBinding,
) -> Result<DifferentialBitVector, RunFailure> {
    let graph_value = artifact
        .graph()
        .value(binding.value())
        .ok_or_else(|| RunFailure::Invalid("semantic input binding is unknown".to_string()))?;
    let width = value_width(graph_value.var.size).map_err(RunFailure::Invalid)?;
    if binding.width_bits() != width || graph_value.var.constant_bits().is_some() {
        return Err(RunFailure::Invalid(
            "semantic input does not match a nonconstant source binding".to_string(),
        ));
    }
    let locally_produced = artifact
        .graph()
        .def_inst(binding.value())
        .and_then(|inst| artifact.graph().inst(inst))
        .and_then(|inst| artifact.graph().block(inst.block))
        .is_some_and(|block| block.addr == block_addr);
    let value = state.values.get(&binding.value()).copied().ok_or_else(|| {
        if locally_produced {
            RunFailure::Invalid(
                "semantic dependency was evaluated before its local producer".to_string(),
            )
        } else {
            RunFailure::MissingBoundaryInput(binding.value())
        }
    })?;
    require_width(value, binding.width_bits())?;
    Ok(value)
}

fn canonical_producer_for_value(
    artifact: &SsaArtifact,
    value: ValueId,
) -> Result<Option<CanonicalInstructionId>, RunFailure> {
    artifact
        .graph()
        .def_inst(value)
        .map(|inst| {
            artifact
                .obligations()
                .instruction_for_inst(inst)
                .map(|instruction| instruction.id)
                .ok_or_else(|| {
                    RunFailure::Invalid("value producer lacks a canonical source ID".to_string())
                })
        })
        .transpose()
}

struct SemanticEvaluator<'a> {
    artifact: &'a SsaArtifact,
    block_addr: u64,
    expressions: &'a SemanticCExpressionLayer,
    state: &'a ExecutionState,
    reads: &'a BTreeMap<StructuredAccessId, CachedMemoryRead>,
    output_roots: Option<&'a BTreeMap<MachineValueBinding, SemanticCExprId>>,
    rewritten_reads: Option<&'a BTreeMap<StructuredAccessId, DifferentialBitVector>>,
    consumed_rewrites: Option<&'a mut BTreeSet<StructuredAccessId>>,
    memo: BTreeMap<SemanticCExprId, DifferentialBitVector>,
    visiting: BTreeSet<SemanticCExprId>,
    remaining_nodes: &'a mut u32,
}

impl SemanticEvaluator<'_> {
    fn eval(&mut self, id: SemanticCExprId) -> Result<DifferentialBitVector, RunFailure> {
        if let Some(value) = self.memo.get(&id).copied() {
            return Ok(value);
        }
        if !self.visiting.insert(id) {
            return Err(RunFailure::Invalid(
                "semantic expression cycle detected".to_string(),
            ));
        }
        if *self.remaining_nodes == 0 {
            return Err(RunFailure::BudgetExceeded);
        }
        *self.remaining_nodes -= 1;
        let expression = self
            .expressions
            .expr(id)
            .ok_or_else(|| RunFailure::Invalid(format!("semantic expression {id:?} is missing")))?;
        let width = expression.ty().width_bits();
        if !supported_width(width) {
            return Err(RunFailure::Unsupported(format!(
                "semantic width {width} is outside the differential subset"
            )));
        }
        let result = match expression.kind() {
            SemanticCExprKind::Input { binding } => {
                if binding.width_bits() != width {
                    return Err(RunFailure::Invalid(
                        "semantic input width mismatch".to_string(),
                    ));
                }
                if let Some(root) = self
                    .output_roots
                    .and_then(|outputs| outputs.get(binding))
                    .copied()
                {
                    self.eval(root)?
                } else {
                    semantic_binding_value(self.artifact, self.block_addr, self.state, *binding)?
                }
            }
            SemanticCExprKind::Constant { binding, value } => {
                if binding.width_bits() != width || value.width_bits() != width {
                    return Err(RunFailure::Invalid(
                        "semantic constant width mismatch".to_string(),
                    ));
                }
                semantic_bitvector(width, value.bits())?
            }
            SemanticCExprKind::MemoryRead {
                access,
                object,
                space,
                endianness,
                word_size_bytes,
                address,
                width_bits,
            } => {
                if let Some(value) = self
                    .rewritten_reads
                    .and_then(|rewrites| rewrites.get(access))
                    .copied()
                {
                    if *width_bits != width || value.width_bits() != width {
                        return Err(RunFailure::Invalid(
                            "private memory rewrite width mismatch".to_string(),
                        ));
                    }
                    let consumed = self.consumed_rewrites.as_deref_mut().ok_or_else(|| {
                        RunFailure::Invalid(
                            "private memory rewrite lacks consumption accounting".to_string(),
                        )
                    })?;
                    if !consumed.insert(*access) {
                        return Err(RunFailure::Invalid(
                            "private memory rewrite was consumed more than once".to_string(),
                        ));
                    }
                    value
                } else {
                    let address = self.eval(*address)?;
                    let cached = self.reads.get(access).ok_or_else(|| {
                        RunFailure::Invalid(
                            "memory-read expression has no exactly-once statement event"
                                .to_string(),
                        )
                    })?;
                    if cached.producer.block_addr != self.block_addr
                        || cached.object != *object
                        || cached.space != *space
                        || cached.endianness != *endianness
                        || cached.word_size_bytes != *word_size_bytes
                        || cached.byte_address != address.bits
                        || cached.width_bits != *width_bits
                        || *width_bits != width
                    {
                        return Err(RunFailure::Invalid(
                            "memory-read expression differs from statement event".to_string(),
                        ));
                    }
                    cached.value
                }
            }
            SemanticCExprKind::Copy { input } => {
                let value = self.eval(*input)?;
                require_width(value, width)?;
                value
            }
            SemanticCExprKind::Arithmetic {
                op,
                mode,
                left,
                right,
            } => {
                if *mode != MachineArithmeticMode::Wrapping {
                    return Err(RunFailure::Unsupported(
                        "checked arithmetic has no admitted helper contract".to_string(),
                    ));
                }
                let left = self.eval(*left)?;
                let right = self.eval(*right)?;
                require_binary_widths(left, right, width)?;
                let bits = match op {
                    MachineArithmeticOp::Add => left.bits.wrapping_add(right.bits),
                    MachineArithmeticOp::Subtract => left.bits.wrapping_sub(right.bits),
                    MachineArithmeticOp::Multiply => left.bits.wrapping_mul(right.bits),
                };
                semantic_bitvector(width, bits)?
            }
            SemanticCExprKind::ArithmeticFlag { op, left, right } => {
                if !matches!(expression.ty(), MachineType::Bool { .. }) {
                    return Err(RunFailure::Invalid(
                        "arithmetic flag result is not a typed bool".to_string(),
                    ));
                }
                let left = self.eval(*left)?;
                let right = self.eval(*right)?;
                if left.width_bits == 0 || left.width_bits != right.width_bits {
                    return Err(RunFailure::Invalid(
                        "arithmetic flag input widths differ".to_string(),
                    ));
                }
                let mask = width_mask(left.width_bits);
                let left_bits = left.bits & mask;
                let right_bits = right.bits & mask;
                let sign = 1u64 << (left.width_bits - 1);
                let condition = match op {
                    MachineArithmeticFlagOp::UnsignedCarry => {
                        u128::from(left_bits) + u128::from(right_bits) > u128::from(mask)
                    }
                    MachineArithmeticFlagOp::SignedCarry => {
                        let result = left_bits.wrapping_add(right_bits) & mask;
                        (!(left_bits ^ right_bits) & (left_bits ^ result) & sign) != 0
                    }
                    MachineArithmeticFlagOp::SignedBorrow => {
                        let result = left_bits.wrapping_sub(right_bits) & mask;
                        ((left_bits ^ right_bits) & (left_bits ^ result) & sign) != 0
                    }
                };
                semantic_bitvector(width, u64::from(condition))?
            }
            SemanticCExprKind::Bitwise { op, left, right } => {
                let left = self.eval(*left)?;
                let right = self.eval(*right)?;
                require_binary_widths(left, right, width)?;
                let bits = match op {
                    MachineBitwiseOp::And => left.bits & right.bits,
                    MachineBitwiseOp::Or => left.bits | right.bits,
                    MachineBitwiseOp::Xor => left.bits ^ right.bits,
                };
                semantic_bitvector(width, bits)?
            }
            SemanticCExprKind::BitwiseNot { input } => {
                let value = self.eval(*input)?;
                require_width(value, width)?;
                semantic_bitvector(width, !value.bits)?
            }
            SemanticCExprKind::BooleanNot { input } => {
                let input_type = self
                    .expressions
                    .expr(*input)
                    .map(|input| input.ty())
                    .ok_or_else(|| {
                        RunFailure::Invalid("boolean-not input is missing".to_string())
                    })?;
                if !matches!(expression.ty(), MachineType::Bool { .. })
                    || input_type != expression.ty()
                {
                    return Err(RunFailure::Invalid(
                        "boolean-not input is not the exact sealed bool type".to_string(),
                    ));
                }
                let value = self.eval(*input)?;
                require_width(value, width)?;
                semantic_bitvector(width, u64::from(value.bits == 0))?
            }
            SemanticCExprKind::Boolean { op, left, right } => {
                let left_type = self
                    .expressions
                    .expr(*left)
                    .map(|input| input.ty())
                    .ok_or_else(|| RunFailure::Invalid("boolean left input is missing".into()))?;
                let right_type = self
                    .expressions
                    .expr(*right)
                    .map(|input| input.ty())
                    .ok_or_else(|| RunFailure::Invalid("boolean right input is missing".into()))?;
                if !matches!(expression.ty(), MachineType::Bool { .. })
                    || left_type != expression.ty()
                    || right_type != expression.ty()
                {
                    return Err(RunFailure::Invalid(
                        "boolean operands do not have the exact sealed bool type".into(),
                    ));
                }
                let left = self.eval(*left)?;
                let right = self.eval(*right)?;
                require_binary_widths(left, right, width)?;
                if left.bits > 1 || right.bits > 1 {
                    return Err(RunFailure::Invalid(
                        "boolean operand is not canonical zero-or-one".into(),
                    ));
                }
                let condition = match op {
                    MachineBooleanOp::And => left.bits != 0 && right.bits != 0,
                    MachineBooleanOp::Or => left.bits != 0 || right.bits != 0,
                    MachineBooleanOp::Xor => (left.bits != 0) != (right.bits != 0),
                };
                semantic_bitvector(width, u64::from(condition))?
            }
            SemanticCExprKind::Shift {
                kind,
                overshift,
                value,
                count,
            } => {
                let value = self.eval(*value)?;
                let count = self.eval(*count)?;
                require_width(value, width)?;
                let supported_policy = matches!(
                    (kind, overshift),
                    (MachineShiftKind::Left, MachineOvershiftBehavior::Zero)
                        | (
                            MachineShiftKind::LogicalRight,
                            MachineOvershiftBehavior::Zero
                        )
                        | (
                            MachineShiftKind::ArithmeticRight,
                            MachineOvershiftBehavior::SignFill
                        )
                );
                if !supported_policy {
                    return Err(RunFailure::Unsupported(
                        "shift policy is outside the differential subset".to_string(),
                    ));
                }
                semantic_shift_value(*kind, value, count.bits)?
            }
            SemanticCExprKind::Compare {
                op,
                interpretation,
                left,
                right,
            } => {
                if !matches!(expression.ty(), MachineType::Bool { .. }) {
                    return Err(RunFailure::Invalid(
                        "comparison result is not a typed bool".to_string(),
                    ));
                }
                let left = self.eval(*left)?;
                let right = self.eval(*right)?;
                if left.width_bits != right.width_bits {
                    return Err(RunFailure::Invalid(
                        "semantic comparison widths differ".to_string(),
                    ));
                }
                let condition = match interpretation {
                    MachineSignedness::Unsigned => match op {
                        MachineComparisonOp::Equal => left.bits == right.bits,
                        MachineComparisonOp::NotEqual => left.bits != right.bits,
                        MachineComparisonOp::LessThan => left.bits < right.bits,
                        MachineComparisonOp::LessThanOrEqual => left.bits <= right.bits,
                    },
                    MachineSignedness::Signed => {
                        let left = semantic_signed_value(left);
                        let right = semantic_signed_value(right);
                        match op {
                            MachineComparisonOp::Equal => left == right,
                            MachineComparisonOp::NotEqual => left != right,
                            MachineComparisonOp::LessThan => left < right,
                            MachineComparisonOp::LessThanOrEqual => left <= right,
                        }
                    }
                };
                semantic_bitvector(width, u64::from(condition))?
            }
            SemanticCExprKind::Cast { kind, input } => {
                let value = self.eval(*input)?;
                let input_type = self
                    .expressions
                    .expr(*input)
                    .map(|expression| expression.ty())
                    .ok_or_else(|| RunFailure::Invalid("cast input is missing".to_string()))?;
                match kind {
                    MachineCastKind::ZeroExtend if width > value.width_bits => {
                        semantic_bitvector(width, value.bits)?
                    }
                    MachineCastKind::SignExtend if width > value.width_bits => {
                        semantic_sign_extend(value, width)?
                    }
                    MachineCastKind::Truncate if width < value.width_bits => {
                        semantic_bitvector(width, value.bits)?
                    }
                    MachineCastKind::BitReinterpret if width == value.width_bits => value,
                    MachineCastKind::IntegerToAddress
                        if width == value.width_bits
                            && matches!(input_type, MachineType::Integer { .. })
                            && matches!(expression.ty(), MachineType::Address { .. }) =>
                    {
                        value
                    }
                    MachineCastKind::AddressToInteger
                        if width == value.width_bits
                            && matches!(input_type, MachineType::Address { .. })
                            && matches!(expression.ty(), MachineType::Integer { .. }) =>
                    {
                        value
                    }
                    _ => {
                        return Err(RunFailure::Invalid(
                            "invalid semantic cast relation".to_string(),
                        ));
                    }
                }
            }
            SemanticCExprKind::Extract { input, lsb_bits } => {
                let value = self.eval(*input)?;
                if lsb_bits
                    .checked_add(width)
                    .is_none_or(|end| end > value.width_bits)
                {
                    return Err(RunFailure::Invalid(
                        "invalid semantic extract range".to_string(),
                    ));
                }
                semantic_bitvector(width, value.bits >> lsb_bits)?
            }
            SemanticCExprKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                let condition_type = self
                    .expressions
                    .expr(*condition)
                    .map(|condition| condition.ty())
                    .ok_or_else(|| {
                        RunFailure::Invalid("select condition is missing".to_string())
                    })?;
                let if_true_type = self
                    .expressions
                    .expr(*if_true)
                    .map(|arm| arm.ty())
                    .ok_or_else(|| RunFailure::Invalid("select true arm is missing".to_string()))?;
                let if_false_type = self
                    .expressions
                    .expr(*if_false)
                    .map(|arm| arm.ty())
                    .ok_or_else(|| {
                        RunFailure::Invalid("select false arm is missing".to_string())
                    })?;
                if !matches!(condition_type, MachineType::Bool { .. })
                    || if_true_type != expression.ty()
                    || if_false_type != expression.ty()
                {
                    return Err(RunFailure::Invalid(
                        "select condition or arm type is not sealed".to_string(),
                    ));
                }
                let condition = self.eval(*condition)?;
                let selected = if condition.bits != 0 {
                    self.eval(*if_true)?
                } else {
                    self.eval(*if_false)?
                };
                require_width(selected, width)?;
                selected
            }
        };
        require_width(result, width)?;
        self.visiting.remove(&id);
        self.memo.insert(id, result);
        Ok(result)
    }
}

fn private_join_output_index(
    layer: &SemanticCExpressionLayer,
) -> Result<BTreeMap<MachineValueBinding, SemanticCExprId>, RunFailure> {
    let mut outputs = BTreeMap::new();
    for entity in layer.entities() {
        if outputs.insert(entity.output(), entity.root()).is_some() {
            return Err(RunFailure::Invalid(
                "private-join expression output is ambiguous".to_string(),
            ));
        }
    }
    Ok(outputs)
}

fn evaluate_private_join_value(
    artifact: &SsaArtifact,
    layer: &SemanticCExpressionLayer,
    outputs: &BTreeMap<MachineValueBinding, SemanticCExprId>,
    state: &ExecutionState,
    value: &CertifiedPrivateFrameJoinValue,
    remaining_nodes: &mut u32,
) -> Result<DifferentialBitVector, RunFailure> {
    let binding = value.value().binding();
    let result = match value.origin() {
        CertifiedPrivateFrameJoinValueOrigin::Produced { producer, root } => {
            let entity = layer.entity_for_producer(*producer).ok_or_else(|| {
                RunFailure::Invalid("produced rewrite value has no semantic entity".to_string())
            })?;
            if entity.output() != binding || entity.root() != *root {
                return Err(RunFailure::Invalid(
                    "produced rewrite value differs from its sealed entity".to_string(),
                ));
            }
            let empty_reads = BTreeMap::new();
            let mut evaluator = SemanticEvaluator {
                artifact,
                block_addr: producer.block_addr,
                expressions: layer,
                state,
                reads: &empty_reads,
                output_roots: Some(outputs),
                rewritten_reads: None,
                consumed_rewrites: None,
                memo: BTreeMap::new(),
                visiting: BTreeSet::new(),
                remaining_nodes,
            };
            evaluator.eval(*root)?
        }
        CertifiedPrivateFrameJoinValueOrigin::Constant(constant) => {
            if value.value().constant() != Some(*constant) {
                return Err(RunFailure::Invalid(
                    "constant rewrite value differs from its machine use".to_string(),
                ));
            }
            semantic_bitvector(constant.width_bits(), constant.bits())?
        }
        CertifiedPrivateFrameJoinValueOrigin::AbiParameter { index, storage } => {
            if !layer.is_exact_abi_parameter(binding, value.value().ty(), *index, *storage) {
                return Err(RunFailure::Invalid(
                    "ABI rewrite value differs from its sealed input origin".to_string(),
                ));
            }
            semantic_binding_value(artifact, artifact.function().entry, state, binding)?
        }
    };
    require_width(result, binding.width_bits())?;
    Ok(result)
}

fn eval_private_join_root(
    artifact: &SsaArtifact,
    layer: &SemanticCExpressionLayer,
    outputs: &BTreeMap<MachineValueBinding, SemanticCExprId>,
    state: &ExecutionState,
    root: SemanticCExprId,
    rewrites: &BTreeMap<StructuredAccessId, DifferentialBitVector>,
    remaining_nodes: &mut u32,
) -> Result<(DifferentialBitVector, BTreeSet<StructuredAccessId>), RunFailure> {
    let empty_reads = BTreeMap::new();
    let mut consumed = BTreeSet::new();
    let value = {
        let mut evaluator = SemanticEvaluator {
            artifact,
            block_addr: artifact.function().entry,
            expressions: layer,
            state,
            reads: &empty_reads,
            output_roots: Some(outputs),
            rewritten_reads: Some(rewrites),
            consumed_rewrites: Some(&mut consumed),
            memo: BTreeMap::new(),
            visiting: BTreeSet::new(),
            remaining_nodes,
        };
        evaluator.eval(root)?
    };
    Ok((value, consumed))
}

fn runtime_rewrite_consumption_is_valid(
    consumed: &BTreeSet<StructuredAccessId>,
    sealed: &BTreeMap<StructuredAccessId, DifferentialBitVector>,
) -> bool {
    consumed.iter().all(|access| sealed.contains_key(access))
}

fn exact_semantic_scalar_carrier_relation(
    kind: SourceCarrierKind,
    offset_bits: u64,
    size_bits: u64,
    physical_width: u32,
    logical_width: u32,
) -> bool {
    offset_bits == 0
        && size_bits == u64::from(logical_width)
        && match kind {
            SourceCarrierKind::Full => logical_width == physical_width,
            SourceCarrierKind::LowBits => logical_width < physical_width,
        }
}

fn project_semantic_logical_return(
    layer: &SemanticCExpressionLayer,
    physical: DifferentialBitVector,
) -> Result<DifferentialBitVector, RunFailure> {
    let projection = layer
        .function_interface()
        .and_then(|interface| interface.return_projection())
        .ok_or_else(|| {
            RunFailure::Invalid("private join lacks a logical return projection".to_string())
        })?;
    if !matches!(projection.physical_ty(), MachineType::Integer { .. })
        || !matches!(projection.logical_ty(), MachineType::Integer { .. })
        || projection.physical_ty().width_bits() != physical.width_bits()
        || !exact_semantic_scalar_carrier_relation(
            projection.carrier().kind(),
            projection.carrier().offset_bits(),
            projection.carrier().size_bits(),
            projection.physical_ty().width_bits(),
            projection.logical_ty().width_bits(),
        )
    {
        return Err(RunFailure::Invalid(
            "private join logical return projection is incoherent".to_string(),
        ));
    }
    semantic_bitvector(projection.logical_ty().width_bits(), physical.bits())
}

fn project_source_logical_return(
    artifact: &SsaArtifact,
    physical: DifferentialBitVector,
) -> Result<DifferentialBitVector, RunFailure> {
    let interface = artifact
        .machine_context()
        .function_interface()
        .ok_or_else(|| RunFailure::Invalid("source function interface is missing".to_string()))?;
    let SourceFunctionReturn::Register { storage } = interface.return_kind() else {
        return Err(RunFailure::Invalid(
            "source private join is not a scalar register return".to_string(),
        ));
    };
    let physical_width = storage
        .size
        .checked_mul(8)
        .ok_or_else(|| RunFailure::Invalid("source return width overflow".to_string()))?;
    let logical = interface
        .return_logical_value()
        .ok_or_else(|| RunFailure::Invalid("source logical return value is missing".to_string()))?;
    let source_type = interface
        .type_graph()
        .and_then(|graph| {
            usize::try_from(logical.type_id())
                .ok()
                .and_then(|id| graph.types().get(id))
        })
        .ok_or_else(|| RunFailure::Invalid("source logical return type is missing".to_string()))?;
    if source_type.id() != logical.type_id() {
        return Err(RunFailure::Invalid(
            "source logical return type identity is incoherent".to_string(),
        ));
    }
    let logical_width = u32::try_from(source_type.size_bits())
        .ok()
        .filter(|width| matches!(width, 8 | 16 | 32 | 64))
        .ok_or_else(|| RunFailure::Invalid("source logical return width is invalid".to_string()))?;
    let carrier = logical.carrier();
    let exact_carrier = carrier.offset_bits() == 0
        && carrier.size_bits() == u64::from(logical_width)
        && matches!(
            source_type.kind(),
            SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger
        )
        && match carrier.kind() {
            SourceCarrierKind::Full => logical_width == physical_width,
            SourceCarrierKind::LowBits => logical_width < physical_width,
        };
    if physical.width_bits() != physical_width || !exact_carrier {
        return Err(RunFailure::Invalid(
            "source logical return carrier is incoherent".to_string(),
        ));
    }
    semantic_bitvector(logical_width, physical.bits())
}

fn execute_private_frame_join_semantic(
    artifact: &SsaArtifact,
    function: &CertifiedPrivateFrameConditionalJoinFunction,
    initial: &DifferentialState,
    limits: DifferentialLimits,
) -> InterpreterResult {
    let rewrite = function.rewrite();
    let layer = rewrite.expression_layer();
    let state = ExecutionState::from(initial);
    let result = (|| {
        if rewrite.joined_select().truthiness() != CertifiedControlTruthiness::NonZeroIsTrue
            || rewrite.joined_select().condition().binding().width_bits() != 8
        {
            return Err(RunFailure::Invalid(
                "private join condition policy is not exact nonzero truthiness".to_string(),
            ));
        }
        let outputs = private_join_output_index(layer)?;
        let mut remaining_nodes = limits.max_expression_nodes;
        let mut direct = BTreeMap::new();
        for substitution in rewrite.direct_substitutions() {
            let replacement = evaluate_private_join_value(
                artifact,
                layer,
                &outputs,
                &state,
                substitution.replacement(),
                &mut remaining_nodes,
            )?;
            if direct
                .insert(substitution.load_access(), replacement)
                .is_some()
            {
                return Err(RunFailure::Invalid(
                    "duplicate direct private-memory rewrite".to_string(),
                ));
            }
        }
        let (condition, consumed_direct) = eval_private_join_root(
            artifact,
            layer,
            &outputs,
            &state,
            rewrite.joined_select().condition_root(),
            &direct,
            &mut remaining_nodes,
        )?;
        if !runtime_rewrite_consumption_is_valid(&consumed_direct, &direct)
            || condition.width_bits() != 8
        {
            return Err(RunFailure::Invalid(
                "condition DAG consumed an unsealed direct rewrite".to_string(),
            ));
        }
        let selected = if condition.bits() != 0 {
            rewrite.joined_select().true_value()
        } else {
            rewrite.joined_select().false_value()
        };
        let selected = evaluate_private_join_value(
            artifact,
            layer,
            &outputs,
            &state,
            selected,
            &mut remaining_nodes,
        )?;
        let joined = BTreeMap::from([(rewrite.joined_select().load_access(), selected)]);
        let (physical, consumed_joined) = eval_private_join_root(
            artifact,
            layer,
            &outputs,
            &state,
            rewrite.joined_select().return_root(),
            &joined,
            &mut remaining_nodes,
        )?;
        if !runtime_rewrite_consumption_is_valid(&consumed_joined, &joined) {
            return Err(RunFailure::Invalid(
                "return DAG consumed an unsealed joined rewrite".to_string(),
            ));
        }
        let logical = project_semantic_logical_return(layer, physical)?;
        Ok(DifferentialObservedRun {
            outcome: DifferentialBoundaryOutcome::Returned {
                values: vec![logical].into_boxed_slice(),
            },
            outputs: Box::new([]),
            memory_events: Box::new([]),
            final_memory: state
                .memory
                .iter()
                .map(|(location, value)| DifferentialObservedByte {
                    location: *location,
                    value: *value,
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        })
    })();
    result.map_err(|failure| FailedRun {
        failure,
        trace: observed_trace(&state),
    })
}

fn private_event_matches_statement(
    event: &DifferentialMemoryEvent,
    statement: &CertifiedMemoryStatement,
) -> bool {
    event.producer == statement.producer()
        && event.access == statement.access()
        && event.object == statement.object()
        && event.space == statement.space()
        && event.width_bits == statement.width_bits()
        && event.endianness == statement.endianness()
        && matches!(
            (event.kind, statement.kind()),
            (
                DifferentialMemoryEventKind::Read,
                CertifiedMemoryStatementKind::Read { .. }
            ) | (
                DifferentialMemoryEventKind::Write,
                CertifiedMemoryStatementKind::Write { .. }
            )
        )
}

fn validate_private_frame_events(
    events: &[DifferentialMemoryEvent],
    frame: &CertifiedFramePreservation,
    restore: &CertifiedFrameRestore,
) -> Result<(), RunFailure> {
    let saves = events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.access == frame.entry_save().access())
        .collect::<Vec<_>>();
    let restores = events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.access == restore.restore_read().access())
        .collect::<Vec<_>>();
    let ([(save_index, save)], [(restore_index, restored)]) =
        (saves.as_slice(), restores.as_slice())
    else {
        return Err(RunFailure::Invalid(
            "source did not execute each exact frame access once".to_string(),
        ));
    };
    if !private_event_matches_statement(save, frame.entry_save())
        || !private_event_matches_statement(restored, restore.restore_read())
    {
        return Err(RunFailure::Invalid(
            "source frame event differs from exact frame evidence".to_string(),
        ));
    }
    require_width(save.value, frame.entry_save().width_bits())?;
    require_width(restored.value, restore.restore_read().width_bits())?;
    if save_index >= restore_index {
        return Err(RunFailure::Invalid(
            "source frame restore did not follow its entry save".to_string(),
        ));
    }
    if save.value != restored.value {
        return Err(RunFailure::Invalid(
            "source frame restore value differs from its entry save".to_string(),
        ));
    }
    Ok(())
}

fn add_expected_private_flow(
    expected: &mut BTreeMap<
        StructuredAccessId,
        (
            CertifiedMemoryStatement,
            Option<r2cert::CertifiedNormalizedStackRange>,
        ),
    >,
    flow: &r2cert::CertifiedPrivateFrameValueFlow,
    include_stores: impl Fn(&CertifiedMemoryStatement) -> bool,
) -> Result<(), RunFailure> {
    for access in flow.region().accesses() {
        let statement = access.statement();
        let include = matches!(statement.kind(), CertifiedMemoryStatementKind::Read { .. })
            || include_stores(statement);
        if include
            && expected
                .insert(
                    statement.access(),
                    (statement.clone(), Some(access.range())),
                )
                .is_some()
        {
            return Err(RunFailure::Invalid(
                "private memory access has duplicate dynamic ownership".to_string(),
            ));
        }
    }
    Ok(())
}

fn private_stack_intervals(
    projection: &CertifiedMachineProjection,
    join: &CertifiedPrivateFrameConditionalJoin,
    initial: &DifferentialState,
) -> Result<Vec<(u64, u64)>, RunFailure> {
    validate_private_join_frame_authority(projection, join)?;
    let stack = projection
        .stack_discipline()
        .ok_or_else(|| RunFailure::Invalid("private join lacks stack discipline".to_string()))?;
    let entry = initial
        .values
        .get(&stack.entry_stack_pointer().binding().value())
        .copied()
        .ok_or(RunFailure::MissingBoundaryInput(
            stack.entry_stack_pointer().binding().value(),
        ))?;
    require_width(entry, stack.entry_stack_pointer().binding().width_bits())?;
    let ranges = join
        .auxiliary_direct_flows()
        .iter()
        .map(|(_, flow)| flow.range())
        .chain([join.joined_flow().range()])
        .chain(join.frame_preservation().map(|frame| frame.saved_range()));
    let mut intervals = BTreeSet::new();
    for range in ranges {
        let start = modular_stack_offset(entry, range.offset());
        let end = start
            .checked_add(u64::from(range.size_bytes()))
            .ok_or_else(|| RunFailure::Invalid("private stack range end overflow".to_string()))?;
        intervals.insert((start, end));
    }
    Ok(intervals.into_iter().collect())
}

fn validate_private_join_memory_domain(
    artifact: &SsaArtifact,
    projection: &CertifiedMachineProjection,
    join: &CertifiedPrivateFrameConditionalJoin,
    initial: &DifferentialState,
) -> Result<(), RunFailure> {
    let mut intervals = private_stack_intervals(projection, join, initial)?;
    if let Some(read) = join.release().return_address_read() {
        let stack = projection.stack_discipline().ok_or_else(|| {
            RunFailure::Invalid("private join lacks stack discipline".to_string())
        })?;
        let entry = initial
            .values
            .get(&stack.entry_stack_pointer().binding().value())
            .copied()
            .ok_or(RunFailure::MissingBoundaryInput(
                stack.entry_stack_pointer().binding().value(),
            ))?;
        let mechanism = artifact
            .machine_context()
            .function_interface()
            .and_then(|interface| interface.return_mechanism())
            .ok_or_else(|| {
                RunFailure::Invalid(
                    "stacked return-address read lacks exact source mechanism".to_string(),
                )
            })?;
        if read.width_bits() / 8 != mechanism.slot_size_bytes() {
            return Err(RunFailure::Invalid(
                "return-address read size differs from source mechanism".to_string(),
            ));
        }
        let start = modular_stack_offset(entry, mechanism.stack_offset());
        let end = start
            .checked_add(u64::from(mechanism.slot_size_bytes()))
            .ok_or_else(|| RunFailure::Invalid("return-address range overflow".to_string()))?;
        intervals.push((start, end));
    } else if artifact
        .machine_context()
        .function_interface()
        .and_then(|interface| interface.return_mechanism())
        .is_some()
    {
        return Err(RunFailure::Invalid(
            "stacked source mechanism lacks certified return-address read".to_string(),
        ));
    }
    for (start, end) in intervals {
        for byte_address in start..end {
            let location = DifferentialMemoryLocation {
                space: MachineAddressSpace::Ram,
                byte_address,
            };
            if !initial.memory.contains_key(&location) {
                return Err(RunFailure::MemoryOutOfDomain(location));
            }
        }
    }
    Ok(())
}

fn normalize_private_join_run(
    artifact: &SsaArtifact,
    projection: &CertifiedMachineProjection,
    function: &CertifiedPrivateFrameConditionalJoinFunction,
    initial: &DifferentialState,
    selected_true: bool,
    mut run: DifferentialObservedRun,
) -> Result<DifferentialObservedRun, RunFailure> {
    let join = function.rewrite().machine_join();
    let selected_store = if selected_true {
        join.true_arm().store().statement()
    } else {
        join.false_arm().store().statement()
    };
    let mut expected = BTreeMap::new();
    for (_, flow) in join.auxiliary_direct_flows() {
        add_expected_private_flow(&mut expected, flow, |_| true)?;
        if flow.definitions().iter().any(|definition| {
            !matches!(definition, CertifiedPrivateFrameVersionDefinition::Store(_))
        }) {
            return Err(RunFailure::Invalid(
                "auxiliary private flow is not direct".to_string(),
            ));
        }
    }
    add_expected_private_flow(&mut expected, join.joined_flow(), |statement| {
        statement.access() == selected_store.access()
    })?;
    if !expected.contains_key(&selected_store.access()) {
        return Err(RunFailure::Invalid(
            "selected arm store lacks exact joined-flow ownership".to_string(),
        ));
    }
    let frame_restore = if let Some(frame) = join.frame_preservation() {
        let restore = exact_private_join_frame_restore(frame, join)?;
        for statement in [frame.entry_save(), restore.restore_read()] {
            if expected
                .insert(
                    statement.access(),
                    (statement.clone(), Some(frame.saved_range())),
                )
                .is_some()
            {
                return Err(RunFailure::Invalid(
                    "frame memory access collides with private ownership".to_string(),
                ));
            }
        }
        Some((frame, restore))
    } else {
        None
    };
    if let Some(read) = join.release().return_address_read()
        && expected
            .insert(read.access(), (read.clone(), None))
            .is_some()
    {
        return Err(RunFailure::Invalid(
            "return-address read collides with a private access".to_string(),
        ));
    }
    let intervals = private_stack_intervals(projection, join, initial)?;
    let stack = projection
        .stack_discipline()
        .ok_or_else(|| RunFailure::Invalid("private join lacks stack discipline".to_string()))?;
    let entry_sp = initial
        .values
        .get(&stack.entry_stack_pointer().binding().value())
        .copied()
        .ok_or(RunFailure::MissingBoundaryInput(
            stack.entry_stack_pointer().binding().value(),
        ))?;
    let mut consumed = BTreeSet::new();
    for event in &run.memory_events {
        let (statement, range) = expected.get(&event.access).ok_or_else(|| {
            RunFailure::Invalid(
                "source emitted a memory event outside private, frame, and return evidence"
                    .to_string(),
            )
        })?;
        if !private_event_matches_statement(event, statement) || !consumed.insert(event.access) {
            return Err(RunFailure::Invalid(
                "source memory event differs from exact audited ownership".to_string(),
            ));
        }
        if let Some(range) = range {
            let expected_address = modular_stack_offset(entry_sp, range.offset());
            if event.byte_address != expected_address || event.width_bits / 8 != range.size_bytes()
            {
                return Err(RunFailure::Invalid(
                    "private access differs from its exact audited range".to_string(),
                ));
            }
        } else {
            let mechanism = artifact
                .machine_context()
                .function_interface()
                .and_then(|interface| interface.return_mechanism())
                .ok_or_else(|| {
                    RunFailure::Invalid(
                        "return-address event lacks exact source mechanism".to_string(),
                    )
                })?;
            if !exact_return_address_event(
                event,
                statement,
                entry_sp,
                mechanism.stack_offset(),
                mechanism.slot_size_bytes(),
            ) {
                return Err(RunFailure::Invalid(
                    "return-address event differs from exact source mechanism".to_string(),
                ));
            }
        }
    }
    if consumed != expected.keys().copied().collect() {
        return Err(RunFailure::Invalid(
            "source did not consume every expected private, frame, or return-address access"
                .to_string(),
        ));
    }
    if let Some((frame, restore)) = frame_restore {
        validate_private_frame_events(&run.memory_events, frame, restore)?;
    }
    let physical = match &run.outcome {
        DifferentialBoundaryOutcome::Returned { values } if values.len() == 1 => values[0],
        _ => {
            return Err(RunFailure::Invalid(
                "private join did not produce one scalar return".to_string(),
            ));
        }
    };
    let logical = project_source_logical_return(artifact, physical)?;
    run.outcome = DifferentialBoundaryOutcome::Returned {
        values: vec![logical].into_boxed_slice(),
    };
    run.outputs = Box::new([]);
    run.memory_events = Box::new([]);
    run.final_memory = run
        .final_memory
        .into_vec()
        .into_iter()
        .filter(|byte| {
            byte.location.space != MachineAddressSpace::Ram
                || intervals.iter().all(|(start, end)| {
                    byte.location.byte_address < *start || byte.location.byte_address >= *end
                })
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    Ok(run)
}

fn project_private_join_semantic_memory(
    projection: &CertifiedMachineProjection,
    function: &CertifiedPrivateFrameConditionalJoinFunction,
    initial: &DifferentialState,
    mut run: DifferentialObservedRun,
) -> Result<DifferentialObservedRun, RunFailure> {
    let intervals =
        private_stack_intervals(projection, function.rewrite().machine_join(), initial)?;
    run.final_memory = run
        .final_memory
        .into_vec()
        .into_iter()
        .filter(|byte| {
            byte.location.space != MachineAddressSpace::Ram
                || intervals.iter().all(|(start, end)| {
                    byte.location.byte_address < *start || byte.location.byte_address >= *end
                })
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    Ok(run)
}

fn observed_source_run(
    artifact: &SsaArtifact,
    block: &r2ssa::GraphBlock,
    state: ExecutionState,
) -> Result<DifferentialObservedRun, RunFailure> {
    let mut outputs = Vec::new();
    for inst_id in &block.insts {
        let inst = artifact.graph().inst(*inst_id).ok_or_else(|| {
            RunFailure::Invalid("observed source instruction is missing".to_string())
        })?;
        let producer = artifact
            .obligations()
            .instruction_for_inst(*inst_id)
            .map(|instruction| instruction.id)
            .ok_or_else(|| RunFailure::Invalid("observed source ID is missing".to_string()))?;
        let has_live_output = artifact
            .obligations()
            .instructions()
            .get(&producer)
            .is_some_and(|instruction| {
                instruction.obligations.iter().any(|obligation| {
                    obligation.kind == r2ssa::SemanticObligationKind::LiveValueProducer
                })
            });
        if !has_live_output {
            continue;
        }
        let output = inst.output.ok_or_else(|| {
            RunFailure::Invalid("live source output has no graph value".to_string())
        })?;
        let bitvector = state.values.get(&output).copied().ok_or_else(|| {
            RunFailure::Invalid(format!("observed source output {output:?} is missing"))
        })?;
        let binding = MachineValueUse::from_artifact(artifact, output)
            .map_err(|error| RunFailure::Invalid(format!("source binding failed: {error}")))?
            .binding();
        let ty = source_output_type(inst, binding.width_bits())?;
        let mut sources = BTreeSet::from([producer]);
        for input in &inst.inputs {
            if let Some(input_producer) = canonical_producer_for_value(artifact, *input)? {
                sources.insert(input_producer);
            }
        }
        outputs.push(DifferentialObservedValue {
            binding,
            producer,
            ty,
            source_instructions: sources.into_iter().collect(),
            bitvector,
        });
    }
    finish_observed_run(block.addr, outputs, state)
}

fn observed_semantic_run(
    layer: &SemanticCBlockStepLayer,
    state: ExecutionState,
) -> Result<DifferentialObservedRun, RunFailure> {
    let mut outputs = Vec::new();
    for step in layer.steps() {
        let Some(reference) = step.value() else {
            continue;
        };
        let entity = layer
            .resolve_value(reference)
            .ok_or_else(|| RunFailure::Invalid("output entity is missing".to_string()))?;
        let value = state
            .values
            .get(&entity.output().value())
            .copied()
            .ok_or_else(|| {
                RunFailure::Invalid(format!(
                    "observed output {:?} is missing",
                    entity.output().value()
                ))
            })?;
        let expression = layer
            .accounting()
            .expression_layer()
            .expr(entity.root())
            .ok_or_else(|| RunFailure::Invalid("observed semantic root is missing".to_string()))?;
        outputs.push(DifferentialObservedValue {
            binding: entity.output(),
            producer: entity.producer(),
            ty: expression.ty().clone(),
            source_instructions: expression.source_instructions().iter().copied().collect(),
            bitvector: value,
        });
    }
    finish_observed_run(layer.accounting().block_addr(), outputs, state)
}

fn finish_observed_run(
    block_addr: u64,
    outputs: Vec<DifferentialObservedValue>,
    state: ExecutionState,
) -> Result<DifferentialObservedRun, RunFailure> {
    let final_memory = state
        .memory
        .into_iter()
        .map(|(location, value)| DifferentialObservedByte { location, value })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    Ok(DifferentialObservedRun {
        outcome: DifferentialBoundaryOutcome::OpenBlockExit { block_addr },
        outputs: outputs.into_boxed_slice(),
        memory_events: state.events.into_boxed_slice(),
        final_memory,
    })
}

fn source_terminalize_run(
    artifact: &SsaArtifact,
    block_addr: u64,
    result: InterpreterResult,
) -> InterpreterResult {
    result.and_then(
        |mut run| match source_return_values(artifact, block_addr, &run) {
            Ok(values) => {
                run.outcome = DifferentialBoundaryOutcome::Returned {
                    values: values.into_boxed_slice(),
                };
                Ok(run)
            }
            Err(failure) => Err(FailedRun {
                failure,
                trace: DifferentialObservedTrace {
                    memory_events: run.memory_events,
                    final_memory: run.final_memory,
                },
            }),
        },
    )
}

fn source_return_values(
    artifact: &SsaArtifact,
    block_addr: u64,
    run: &DifferentialObservedRun,
) -> Result<Vec<DifferentialBitVector>, RunFailure> {
    source_return_values_with(artifact, block_addr, |value| {
        run.outputs
            .iter()
            .find(|output| output.binding.value() == value)
            .map(|output| output.bitvector)
            .ok_or_else(|| {
                RunFailure::Invalid(
                    "source returned value is absent from observed outputs".to_string(),
                )
            })
    })
}

fn source_return_values_with(
    artifact: &SsaArtifact,
    block_addr: u64,
    mut value: impl FnMut(ValueId) -> Result<DifferentialBitVector, RunFailure>,
) -> Result<Vec<DifferentialBitVector>, RunFailure> {
    let source_block = artifact
        .function()
        .cfg()
        .get_block(block_addr)
        .filter(|block| matches!(block.terminator, BlockTerminator::Return))
        .ok_or_else(|| RunFailure::Invalid("source arm is not a return block".to_string()))?;
    if !source_block.successors().is_empty() {
        return Err(RunFailure::Invalid(
            "source return block has a successor".to_string(),
        ));
    }
    let graph = artifact.graph();
    let graph_block = graph
        .block_id_for_addr(block_addr)
        .and_then(|id| graph.block(id))
        .ok_or_else(|| RunFailure::Invalid("source return graph block is missing".to_string()))?;
    let return_inst = graph_block
        .insts
        .last()
        .copied()
        .ok_or_else(|| RunFailure::Invalid("source return block is empty".to_string()))?;
    if graph
        .inst(return_inst)
        .is_none_or(|inst| !matches!(inst.payload, InstPayload::Op(SSAOp::Return { .. })))
    {
        return Err(RunFailure::Invalid(
            "source graph terminator is not a return".to_string(),
        ));
    }
    let boundary = artifact
        .facts()
        .boundaries
        .returns
        .get(&return_inst)
        .filter(|boundary| boundary.at == return_inst && boundary.complete)
        .ok_or_else(|| RunFailure::Invalid("source return boundary is incomplete".to_string()))?;
    let interface = artifact
        .machine_context()
        .function_interface()
        .ok_or_else(|| RunFailure::Invalid("source return interface is missing".to_string()))?;
    match (
        interface.return_kind(),
        boundary.values.as_slice(),
        boundary.register_compositions.as_slice(),
    ) {
        (SourceFunctionReturn::Void, [], []) => Ok(Vec::new()),
        (SourceFunctionReturn::Register { storage }, [returned], [])
            if returned.slot == (CallBoundarySlot::Register { index: 0, storage }) =>
        {
            value(returned.value).map(|returned| vec![returned])
        }
        (SourceFunctionReturn::Register { storage }, [], [composition])
            if composition.slot == (CallBoundarySlot::Register { index: 0, storage })
                && composition.validate(
                    artifact.function(),
                    artifact.graph(),
                    artifact.machine_context(),
                    return_inst,
                ) =>
        {
            let width_bits = storage
                .size
                .checked_mul(8)
                .ok_or_else(|| RunFailure::Invalid("return width overflow".to_string()))?;
            let base = value(composition.base.value)?;
            require_width(base, width_bits)?;
            let mut bits = base.bits;
            for overlay in &composition.overlays {
                let overlay_value = value(overlay.definition.value)?;
                let overlay_width = overlay
                    .definition
                    .storage
                    .size
                    .checked_mul(8)
                    .ok_or_else(|| RunFailure::Invalid("overlay width overflow".to_string()))?;
                require_width(overlay_value, overlay_width)?;
                let lsb_bits = overlay
                    .offset_bytes
                    .checked_mul(8)
                    .ok_or_else(|| RunFailure::Invalid("overlay offset overflow".to_string()))?;
                if lsb_bits
                    .checked_add(overlay_width)
                    .is_none_or(|end| end > width_bits)
                {
                    return Err(RunFailure::Invalid(
                        "return overlay lies outside its register".to_string(),
                    ));
                }
                let overlay_mask = source_width_mask(overlay_width) << lsb_bits;
                bits = (bits & !overlay_mask) | ((overlay_value.bits << lsb_bits) & overlay_mask);
            }
            Ok(vec![source_bitvector(width_bits, bits)?])
        }
        _ => Err(RunFailure::Invalid(
            "source return boundary differs from the function interface".to_string(),
        )),
    }
}

fn terminalize_rendered_run(
    result: InterpreterResult,
    returned: RenderedConditionalReturn,
) -> InterpreterResult {
    result.and_then(|mut run| {
        let values = match returned {
            RenderedConditionalReturn::Void => Ok(Vec::new()),
            RenderedConditionalReturn::Value(value) => run
                .outputs
                .iter()
                .find(|output| output.binding.value() == value)
                .map(|output| vec![output.bitvector])
                .ok_or_else(|| {
                    RunFailure::Invalid(
                        "rendered returned value is absent from observed outputs".to_string(),
                    )
                }),
        };
        match values {
            Ok(values) => {
                run.outcome = DifferentialBoundaryOutcome::Returned {
                    values: values.into_boxed_slice(),
                };
                Ok(run)
            }
            Err(failure) => Err(FailedRun {
                failure,
                trace: DifferentialObservedTrace {
                    memory_events: run.memory_events,
                    final_memory: run.final_memory,
                },
            }),
        }
    })
}

fn terminalize_run(result: InterpreterResult, returned: &SemanticCReturn) -> InterpreterResult {
    result.and_then(|mut run| {
        let values = returned
            .values()
            .iter()
            .map(|returned_value| {
                run.outputs
                    .iter()
                    .find(|output| output.binding == returned_value.binding())
                    .map(|output| output.bitvector)
                    .ok_or_else(|| {
                        RunFailure::Invalid(format!(
                            "returned binding {:?} is absent from observed outputs",
                            returned_value.binding().value()
                        ))
                    })
            })
            .collect::<Result<Vec<_>, _>>();
        match values {
            Ok(values) => {
                run.outcome = DifferentialBoundaryOutcome::Returned {
                    values: values.into_boxed_slice(),
                };
                Ok(run)
            }
            Err(failure) => Err(FailedRun {
                failure,
                trace: DifferentialObservedTrace {
                    memory_events: run.memory_events,
                    final_memory: run.final_memory,
                },
            }),
        }
    })
}

fn source_direct_call_outcome(
    artifact: &SsaArtifact,
    block_addr: u64,
    initial: &DifferentialState,
    run: &DifferentialObservedRun,
) -> Result<DifferentialBoundaryOutcome, RunFailure> {
    let graph = artifact.graph();
    let block = graph
        .block_id_for_addr(block_addr)
        .and_then(|id| graph.block(id))
        .ok_or_else(|| RunFailure::Invalid("direct-call source block is missing".to_string()))?;
    let inst_id = block
        .insts
        .last()
        .copied()
        .ok_or_else(|| RunFailure::Invalid("direct-call source block is empty".to_string()))?;
    let inst = graph
        .inst(inst_id)
        .filter(|inst| matches!(inst.payload, InstPayload::Op(SSAOp::Call { .. })))
        .ok_or_else(|| RunFailure::Invalid("source terminator is not a direct call".to_string()))?;
    let producer = artifact
        .obligations()
        .instruction_for_inst(inst_id)
        .map(|instruction| instruction.id)
        .ok_or_else(|| {
            RunFailure::Invalid("direct call lacks a canonical source ID".to_string())
        })?;
    let call_site = artifact
        .call_sites()
        .by_inst
        .get(&inst_id)
        .copied()
        .ok_or_else(|| RunFailure::Invalid("direct call lacks a callsite ID".to_string()))?;
    let fact = artifact
        .call_sites()
        .by_id
        .get(&call_site)
        .filter(|fact| fact.at == inst.id && fact.id == call_site)
        .ok_or_else(|| RunFailure::Invalid("direct callsite fact is inconsistent".to_string()))?;
    let raw_identity = fact
        .raw_identity
        .ok_or_else(|| RunFailure::Invalid("direct call lacks a raw identity".to_string()))?;
    let target = fact
        .direct_target
        .ok_or_else(|| RunFailure::Invalid("direct call lacks a static target".to_string()))?;
    let fallthrough = fact
        .fallthrough
        .ok_or_else(|| RunFailure::Invalid("direct call lacks a fallthrough".to_string()))?;
    let interface = artifact
        .machine_context()
        .call_site_interface(call_site)
        .filter(|interface| {
            interface.identity() == raw_identity
                && interface.is_complete()
                && !interface.is_variadic()
                && !interface.is_noreturn()
                && matches!(interface.result(), SourceCallResult::Void)
        })
        .ok_or_else(|| {
            RunFailure::Invalid("direct call interface is not exact void ABI data".to_string())
        })?;
    let boundary = artifact
        .facts()
        .boundaries
        .calls
        .get(&call_site)
        .filter(|boundary| {
            boundary.call_site == call_site
                && boundary.at == inst_id
                && boundary.complete
                && boundary.calling_convention.as_deref() == Some(interface.calling_convention())
                && boundary.variadic == Some(false)
                && boundary.noreturn == Some(false)
                && boundary.result_kind == Some(SourceCallResult::Void)
                && boundary.results.is_empty()
                && boundary.arguments.len() == interface.arguments().len()
        })
        .ok_or_else(|| {
            RunFailure::Invalid("direct call boundary facts are inconsistent".to_string())
        })?;
    let arguments = boundary
        .arguments
        .iter()
        .zip(interface.arguments())
        .map(|(value, expected)| {
            if value.slot
                != (CallBoundarySlot::Register {
                    index: expected.index(),
                    storage: expected.storage(),
                })
            {
                return Err(RunFailure::Invalid(
                    "direct call argument order or storage differs from source interface"
                        .to_string(),
                ));
            }
            Ok(DifferentialCallArgument {
                slot: value.slot,
                value: observed_call_value(artifact, initial, run, value.value)?,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DifferentialBoundaryOutcome::OpenDirectCall {
        producer,
        call_site,
        raw_identity,
        interface_revision: interface.revision_identity().to_vec().into_boxed_slice(),
        target,
        fallthrough,
        calling_convention: interface.calling_convention().to_string(),
        arguments: arguments.into_boxed_slice(),
    })
}

fn semantic_direct_call_outcome(
    call: &SemanticCDirectCall,
    initial: &DifferentialState,
    run: &DifferentialObservedRun,
) -> Result<DifferentialBoundaryOutcome, RunFailure> {
    let arguments = call
        .arguments()
        .iter()
        .map(|argument| {
            let value = match argument.value() {
                SemanticCCallArgumentValue::Expression(_) => run
                    .outputs
                    .iter()
                    .find(|output| output.binding == argument.binding())
                    .map(|output| output.bitvector)
                    .ok_or_else(|| {
                        RunFailure::Invalid(
                            "semantic call expression output is missing".to_string(),
                        )
                    })?,
                SemanticCCallArgumentValue::Constant(value) => DifferentialBitVector::new(
                    value.width_bits(),
                    value.bits(),
                )
                .ok_or_else(|| {
                    RunFailure::Invalid("semantic call constant width is invalid".to_string())
                })?,
                SemanticCCallArgumentValue::AbiParameter { input, .. } => initial
                    .values
                    .get(&input.value())
                    .copied()
                    .ok_or(RunFailure::MissingBoundaryInput(input.value()))?,
            };
            if value.width_bits() != argument.binding().width_bits() {
                return Err(RunFailure::Invalid(
                    "semantic call argument width differs from its binding".to_string(),
                ));
            }
            Ok(DifferentialCallArgument {
                slot: argument.slot(),
                value,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DifferentialBoundaryOutcome::OpenDirectCall {
        producer: call.producer(),
        call_site: call.call_site(),
        raw_identity: call.raw_identity(),
        interface_revision: call.interface_revision().to_vec().into_boxed_slice(),
        target: call.target(),
        fallthrough: call.fallthrough(),
        calling_convention: call.calling_convention().to_string(),
        arguments: arguments.into_boxed_slice(),
    })
}

fn observed_call_value(
    artifact: &SsaArtifact,
    initial: &DifferentialState,
    run: &DifferentialObservedRun,
    value: ValueId,
) -> Result<DifferentialBitVector, RunFailure> {
    let graph_value = artifact
        .graph()
        .value(value)
        .ok_or_else(|| RunFailure::Invalid("call argument value is missing".to_string()))?;
    if let Some(bits) = graph_value.var.constant_bits() {
        let width = value_width(graph_value.var.size).map_err(RunFailure::Invalid)?;
        return DifferentialBitVector::new(width, bits)
            .ok_or_else(|| RunFailure::Invalid("call constant width is invalid".to_string()));
    }
    if let Some(output) = run
        .outputs
        .iter()
        .find(|output| output.binding.value() == value)
    {
        return Ok(output.bitvector);
    }
    initial
        .values
        .get(&value)
        .copied()
        .ok_or(RunFailure::MissingBoundaryInput(value))
}

fn direct_callize_source_run(
    result: InterpreterResult,
    artifact: &SsaArtifact,
    block_addr: u64,
    initial: &DifferentialState,
) -> InterpreterResult {
    result.and_then(|mut run| {
        match source_direct_call_outcome(artifact, block_addr, initial, &run) {
            Ok(outcome) => {
                run.outcome = outcome;
                Ok(run)
            }
            Err(failure) => Err(FailedRun {
                failure,
                trace: DifferentialObservedTrace {
                    memory_events: run.memory_events,
                    final_memory: run.final_memory,
                },
            }),
        }
    })
}

fn direct_callize_semantic_run(
    result: InterpreterResult,
    call: &SemanticCDirectCall,
    initial: &DifferentialState,
) -> InterpreterResult {
    result.and_then(
        |mut run| match semantic_direct_call_outcome(call, initial, &run) {
            Ok(outcome) => {
                run.outcome = outcome;
                Ok(run)
            }
            Err(failure) => Err(FailedRun {
                failure,
                trace: DifferentialObservedTrace {
                    memory_events: run.memory_events,
                    final_memory: run.final_memory,
                },
            }),
        },
    )
}

fn observed_trace(state: &ExecutionState) -> DifferentialObservedTrace {
    DifferentialObservedTrace {
        memory_events: state.events.clone().into_boxed_slice(),
        final_memory: state
            .memory
            .iter()
            .map(|(location, value)| DifferentialObservedByte {
                location: *location,
                value: *value,
            })
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    }
}

fn finish_conditional_report(
    initial: &DifferentialState,
    candidate_identity: Option<DifferentialCandidateIdentity>,
    block_addr: u64,
    limits: DifferentialLimits,
    source: InterpreterResult,
    semantic_c: InterpreterResult,
    rendered_c: InterpreterResult,
) -> DifferentialReport {
    let typed_candidate_matches = matches!(
        (&source, &semantic_c),
        (Ok(source), Ok(semantic_c)) if first_difference(source, semantic_c).is_none()
    );
    if typed_candidate_matches {
        finish_report(
            initial,
            candidate_identity,
            block_addr,
            limits,
            source,
            rendered_c,
        )
    } else {
        finish_report(
            initial,
            candidate_identity,
            block_addr,
            limits,
            source,
            semantic_c,
        )
    }
}

fn finish_report(
    initial: &DifferentialState,
    candidate_identity: Option<DifferentialCandidateIdentity>,
    block_addr: u64,
    limits: DifferentialLimits,
    source: InterpreterResult,
    semantic_c: InterpreterResult,
) -> DifferentialReport {
    let mut report = match (source, semantic_c) {
        (Ok(source), Ok(semantic_c)) => {
            let mismatch = first_difference(&source, &semantic_c);
            let (conclusion, disposition) = if let Some(mismatch) = mismatch {
                (
                    DifferentialConclusion::MismatchObserved,
                    DifferentialCaseDisposition::SemanticMismatch { mismatch },
                )
            } else {
                (
                    DifferentialConclusion::NoMismatchObserved,
                    DifferentialCaseDisposition::Matched,
                )
            };
            issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Admitted,
                conclusion,
                disposition,
                Some(source),
                Some(semantic_c),
            )
        }
        (Err(source), Err(semantic_c)) => {
            finish_failed_pair(initial, block_addr, limits, source, semantic_c)
        }
        (Err(error), Ok(semantic_c)) => asymmetric_failure(
            initial,
            block_addr,
            limits,
            DifferentialSide::SourceSsa,
            error,
            None,
            Some(semantic_c),
        ),
        (Ok(source), Err(error)) => asymmetric_failure(
            initial,
            block_addr,
            limits,
            DifferentialSide::SemanticC,
            error,
            Some(source),
            None,
        ),
    };
    report.candidate_identity = candidate_identity;
    report
}

fn report_failure(
    initial: &DifferentialState,
    block_addr: u64,
    limits: DifferentialLimits,
    side: DifferentialSide,
    failure: RunFailure,
) -> DifferentialReport {
    let (conclusion, disposition) = match failure {
        RunFailure::Unsupported(reason) => (
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::InterpreterUnsupported { side, reason },
        ),
        RunFailure::MemoryOutOfDomain(location) => (
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::MemoryOutOfDomain { side, location },
        ),
        RunFailure::MissingBoundaryInput(value) => (
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::MissingBoundaryInput { side, value },
        ),
        RunFailure::BudgetExceeded => (
            DifferentialConclusion::Incomplete,
            DifferentialCaseDisposition::BudgetExceeded { side },
        ),
        RunFailure::Invalid(reason) => (
            DifferentialConclusion::HarnessFailure,
            DifferentialCaseDisposition::HarnessFailure { reason },
        ),
    };
    issued_report(
        initial,
        block_addr,
        limits,
        DifferentialCandidateAdmission::Admitted,
        conclusion,
        disposition,
        None,
        None,
    )
}

fn finish_failed_pair(
    initial: &DifferentialState,
    block_addr: u64,
    limits: DifferentialLimits,
    source: FailedRun,
    semantic_c: FailedRun,
) -> DifferentialReport {
    let mut report =
        if let Some(mismatch) = first_trace_difference(&source.trace, &semantic_c.trace) {
            issued_report(
                initial,
                block_addr,
                limits,
                DifferentialCandidateAdmission::Admitted,
                DifferentialConclusion::MismatchObserved,
                DifferentialCaseDisposition::SemanticMismatch { mismatch },
                None,
                None,
            )
        } else {
            match (&source.failure, &semantic_c.failure) {
                (RunFailure::Invalid(source), RunFailure::Invalid(semantic_c)) => issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::Admitted,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure {
                        reason: format!("source: {source}; semantic-C: {semantic_c}"),
                    },
                    None,
                    None,
                ),
                (RunFailure::Invalid(reason), semantic_c) => issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::Admitted,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure {
                        reason: format!(
                            "source harness failure: {reason}; semantic-C stopped: {}",
                            failure_description(semantic_c)
                        ),
                    },
                    None,
                    None,
                ),
                (source, RunFailure::Invalid(reason)) => issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::Admitted,
                    DifferentialConclusion::HarnessFailure,
                    DifferentialCaseDisposition::HarnessFailure {
                        reason: format!(
                            "source stopped: {}; semantic-C harness failure: {reason}",
                            failure_description(source)
                        ),
                    },
                    None,
                    None,
                ),
                (RunFailure::Unsupported(source), RunFailure::Unsupported(semantic_c)) => {
                    let reason = if source == semantic_c {
                        source.clone()
                    } else {
                        format!("source: {source}; semantic-C: {semantic_c}")
                    };
                    report_failure(
                        initial,
                        block_addr,
                        limits,
                        DifferentialSide::Both,
                        RunFailure::Unsupported(reason),
                    )
                }
                _ if source.failure == semantic_c.failure => report_failure(
                    initial,
                    block_addr,
                    limits,
                    DifferentialSide::Both,
                    source.failure.clone(),
                ),
                _ => issued_report(
                    initial,
                    block_addr,
                    limits,
                    DifferentialCandidateAdmission::Admitted,
                    DifferentialConclusion::Incomplete,
                    DifferentialCaseDisposition::InconclusiveExecutionPair {
                        source: failure_description(&source.failure),
                        semantic_c: failure_description(&semantic_c.failure),
                    },
                    None,
                    None,
                ),
            }
        };
    report.source_prefix = Some(source.trace);
    report.semantic_c_prefix = Some(semantic_c.trace);
    report
}

fn failure_description(failure: &RunFailure) -> String {
    match failure {
        RunFailure::Unsupported(reason) => format!("unsupported: {reason}"),
        RunFailure::Invalid(reason) => format!("invalid: {reason}"),
        RunFailure::MissingBoundaryInput(value) => {
            format!("missing boundary input: {value:?}")
        }
        RunFailure::MemoryOutOfDomain(location) => {
            format!("memory out of domain: {location:?}")
        }
        RunFailure::BudgetExceeded => "budget exceeded".to_string(),
    }
}

fn asymmetric_failure(
    initial: &DifferentialState,
    block_addr: u64,
    limits: DifferentialLimits,
    side: DifferentialSide,
    failed: FailedRun,
    source: Option<DifferentialObservedRun>,
    semantic_c: Option<DifferentialObservedRun>,
) -> DifferentialReport {
    let failure = failed.failure;
    let mut report = match failure {
        RunFailure::MemoryOutOfDomain(location) => issued_report(
            initial,
            block_addr,
            limits,
            DifferentialCandidateAdmission::Admitted,
            DifferentialConclusion::MismatchObserved,
            DifferentialCaseDisposition::SemanticMismatch {
                mismatch: DifferentialMismatch {
                    kind: DifferentialMismatchKind::ExecutionOutcome,
                    index: None,
                    source: if side == DifferentialSide::SourceSsa {
                        format!("memory out of domain at {location:?}")
                    } else {
                        "completed".to_string()
                    },
                    semantic_c: if side == DifferentialSide::SemanticC {
                        format!("memory out of domain at {location:?}")
                    } else {
                        "completed".to_string()
                    },
                },
            },
            source,
            semantic_c,
        ),
        failure => {
            let mut report = report_failure(initial, block_addr, limits, side, failure);
            report.source = source;
            report.semantic_c = semantic_c;
            report
        }
    };
    if side == DifferentialSide::SourceSsa {
        report.source_prefix = Some(failed.trace);
    } else {
        report.semantic_c_prefix = Some(failed.trace);
    }
    report
}

fn candidate_not_admitted(
    initial: &DifferentialState,
    block_addr: u64,
    limits: DifferentialLimits,
    admission: DifferentialCandidateAdmission,
    reason: String,
) -> DifferentialReport {
    issued_report(
        initial,
        block_addr,
        limits,
        admission,
        DifferentialConclusion::Incomplete,
        DifferentialCaseDisposition::CandidateNotAdmitted { admission, reason },
        None,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn issued_report(
    initial: &DifferentialState,
    block_addr: u64,
    limits: DifferentialLimits,
    admission: DifferentialCandidateAdmission,
    conclusion: DifferentialConclusion,
    disposition: DifferentialCaseDisposition,
    source: Option<DifferentialObservedRun>,
    semantic_c: Option<DifferentialObservedRun>,
) -> DifferentialReport {
    DifferentialReport {
        schema_version: SEMANTIC_DIFFERENTIAL_SCHEMA_VERSION,
        artifact_identity: Some(initial.artifact_identity.clone()),
        candidate_identity: None,
        initial_state: initial.clone(),
        limits,
        admission,
        block_addr,
        conclusion,
        disposition,
        source,
        semantic_c,
        source_prefix: None,
        semantic_c_prefix: None,
    }
}

fn first_difference(
    source: &DifferentialObservedRun,
    semantic_c: &DifferentialObservedRun,
) -> Option<DifferentialMismatch> {
    if source.outcome != semantic_c.outcome {
        return Some(DifferentialMismatch {
            kind: DifferentialMismatchKind::BoundaryOutcome,
            index: None,
            source: format!("{:?}", source.outcome),
            semantic_c: format!("{:?}", semantic_c.outcome),
        });
    }
    if source.outputs != semantic_c.outputs {
        let index = source
            .outputs
            .iter()
            .zip(semantic_c.outputs.iter())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| source.outputs.len().min(semantic_c.outputs.len()));
        return Some(DifferentialMismatch {
            kind: DifferentialMismatchKind::OutputSequence,
            index: Some(index as u32),
            source: source
                .outputs
                .get(index)
                .map_or_else(|| "missing".to_string(), |value| format!("{value:?}")),
            semantic_c: semantic_c
                .outputs
                .get(index)
                .map_or_else(|| "missing".to_string(), |value| format!("{value:?}")),
        });
    }
    if source.memory_events != semantic_c.memory_events {
        let index = source
            .memory_events
            .iter()
            .zip(semantic_c.memory_events.iter())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| {
                source
                    .memory_events
                    .len()
                    .min(semantic_c.memory_events.len())
            });
        return Some(DifferentialMismatch {
            kind: DifferentialMismatchKind::MemoryEventSequence,
            index: Some(index as u32),
            source: source
                .memory_events
                .get(index)
                .map_or_else(|| "missing".to_string(), |event| format!("{event:?}")),
            semantic_c: semantic_c
                .memory_events
                .get(index)
                .map_or_else(|| "missing".to_string(), |event| format!("{event:?}")),
        });
    }
    if source.final_memory != semantic_c.final_memory {
        let index = source
            .final_memory
            .iter()
            .zip(semantic_c.final_memory.iter())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| source.final_memory.len().min(semantic_c.final_memory.len()));
        return Some(DifferentialMismatch {
            kind: DifferentialMismatchKind::FinalMemory,
            index: Some(index as u32),
            source: source
                .final_memory
                .get(index)
                .map_or_else(|| "missing".to_string(), |byte| format!("{byte:?}")),
            semantic_c: semantic_c
                .final_memory
                .get(index)
                .map_or_else(|| "missing".to_string(), |byte| format!("{byte:?}")),
        });
    }
    None
}

fn first_trace_difference(
    source: &DifferentialObservedTrace,
    semantic_c: &DifferentialObservedTrace,
) -> Option<DifferentialMismatch> {
    if source.memory_events != semantic_c.memory_events {
        let index = source
            .memory_events
            .iter()
            .zip(semantic_c.memory_events.iter())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| {
                source
                    .memory_events
                    .len()
                    .min(semantic_c.memory_events.len())
            });
        return Some(DifferentialMismatch {
            kind: DifferentialMismatchKind::MemoryEventSequence,
            index: Some(index as u32),
            source: source
                .memory_events
                .get(index)
                .map_or_else(|| "missing".to_string(), |event| format!("{event:?}")),
            semantic_c: semantic_c
                .memory_events
                .get(index)
                .map_or_else(|| "missing".to_string(), |event| format!("{event:?}")),
        });
    }
    if source.final_memory != semantic_c.final_memory {
        let index = source
            .final_memory
            .iter()
            .zip(semantic_c.final_memory.iter())
            .position(|(left, right)| left != right)
            .unwrap_or_else(|| source.final_memory.len().min(semantic_c.final_memory.len()));
        return Some(DifferentialMismatch {
            kind: DifferentialMismatchKind::FinalMemory,
            index: Some(index as u32),
            source: source
                .final_memory
                .get(index)
                .map_or_else(|| "missing".to_string(), |byte| format!("{byte:?}")),
            semantic_c: semantic_c
                .final_memory
                .get(index)
                .map_or_else(|| "missing".to_string(), |byte| format!("{byte:?}")),
        });
    }
    None
}

fn graph_value_width(artifact: &SsaArtifact, value: ValueId) -> Result<u32, RunFailure> {
    artifact
        .graph()
        .value(value)
        .ok_or_else(|| RunFailure::Invalid(format!("unknown graph value {value:?}")))
        .and_then(|value| value_width(value.var.size).map_err(RunFailure::Invalid))
}

fn source_output_type(inst: &r2ssa::GraphInst, width_bits: u32) -> Result<MachineType, RunFailure> {
    let InstPayload::Op(op) = &inst.payload else {
        return Err(RunFailure::Unsupported(
            "phi output type requires an incoming-edge proof".to_string(),
        ));
    };
    let ty = match op {
        SSAOp::IntEqual { .. }
        | SSAOp::IntNotEqual { .. }
        | SSAOp::IntLess { .. }
        | SSAOp::IntSLess { .. }
        | SSAOp::IntLessEqual { .. }
        | SSAOp::IntSLessEqual { .. }
        | SSAOp::BoolNot { .. }
        | SSAOp::BoolAnd { .. }
        | SSAOp::BoolOr { .. }
        | SSAOp::BoolXor { .. } => MachineType::Bool {
            storage_bits: width_bits,
        },
        SSAOp::IntSRight { .. } | SSAOp::IntSExt { .. } => MachineType::Integer {
            width_bits,
            signedness: MachineSignedness::Signed,
        },
        SSAOp::Load { .. }
        | SSAOp::Copy { .. }
        | SSAOp::IntAdd { .. }
        | SSAOp::IntSub { .. }
        | SSAOp::IntMult { .. }
        | SSAOp::IntAnd { .. }
        | SSAOp::IntOr { .. }
        | SSAOp::IntXor { .. }
        | SSAOp::IntNot { .. }
        | SSAOp::IntLeft { .. }
        | SSAOp::IntRight { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::Trunc { .. }
        | SSAOp::Cast { .. }
        | SSAOp::Subpiece { .. }
        | SSAOp::Select { .. } => MachineType::Integer {
            width_bits,
            signedness: MachineSignedness::Unsigned,
        },
        _ => {
            return Err(RunFailure::Unsupported(format!(
                "source output type is outside the differential subset: {op:?}"
            )));
        }
    };
    Ok(ty)
}

fn value_width(size_bytes: u32) -> Result<u32, String> {
    let width = size_bytes
        .checked_mul(8)
        .ok_or_else(|| "value width overflow".to_string())?;
    if supported_width(width) {
        Ok(width)
    } else {
        Err(format!("unsupported value width {width}"))
    }
}

fn supported_width(width_bits: u32) -> bool {
    matches!(width_bits, 8 | 16 | 32 | 64)
}

fn width_mask(width_bits: u32) -> u64 {
    if width_bits == 64 {
        u64::MAX
    } else {
        (1_u64 << width_bits) - 1
    }
}

fn require_width(value: DifferentialBitVector, width_bits: u32) -> Result<(), RunFailure> {
    if value.width_bits == width_bits {
        Ok(())
    } else {
        Err(RunFailure::Invalid(format!(
            "bitvector width {} differs from expected {width_bits}",
            value.width_bits
        )))
    }
}

fn require_binary_widths(
    left: DifferentialBitVector,
    right: DifferentialBitVector,
    width_bits: u32,
) -> Result<(), RunFailure> {
    require_width(left, width_bits)?;
    require_width(right, width_bits)
}

fn require_operand_count(inst: &r2ssa::GraphInst, count: usize) -> Result<(), RunFailure> {
    if inst.inputs.len() == count {
        Ok(())
    } else {
        Err(RunFailure::Invalid(format!(
            "instruction {:?} has {} operands, expected {count}",
            inst.id,
            inst.inputs.len()
        )))
    }
}

fn source_width_mask(width_bits: u32) -> u64 {
    match width_bits {
        8 => 0xff,
        16 => 0xffff,
        32 => 0xffff_ffff,
        64 => u64::MAX,
        _ => 0,
    }
}

fn source_bitvector(width_bits: u32, bits: u64) -> Result<DifferentialBitVector, RunFailure> {
    if !supported_width(width_bits) {
        return Err(RunFailure::Unsupported(format!(
            "unsupported source bitvector width {width_bits}"
        )));
    }
    Ok(DifferentialBitVector {
        width_bits,
        bits: bits & source_width_mask(width_bits),
    })
}

fn source_signed_key(value: DifferentialBitVector) -> u64 {
    value.bits ^ (1_u64 << (value.width_bits - 1))
}

fn source_sign_extend(
    value: DifferentialBitVector,
    output_width: u32,
) -> Result<DifferentialBitVector, RunFailure> {
    let sign = 1_u64 << (value.width_bits - 1);
    let bits = if value.bits & sign == 0 {
        value.bits
    } else {
        value.bits | (source_width_mask(output_width) & !source_width_mask(value.width_bits))
    };
    source_bitvector(output_width, bits)
}

fn source_shift_value(
    kind: MachineShiftKind,
    value: DifferentialBitVector,
    count: u64,
) -> Result<DifferentialBitVector, RunFailure> {
    let width = value.width_bits;
    let bits = if count >= u64::from(width) {
        match kind {
            MachineShiftKind::Left | MachineShiftKind::LogicalRight => 0,
            MachineShiftKind::ArithmeticRight => {
                if value.bits & (1_u64 << (width - 1)) == 0 {
                    0
                } else {
                    source_width_mask(width)
                }
            }
        }
    } else {
        let count = count as u32;
        match kind {
            MachineShiftKind::Left => value.bits << count,
            MachineShiftKind::LogicalRight => value.bits >> count,
            MachineShiftKind::ArithmeticRight if count == 0 => value.bits,
            MachineShiftKind::ArithmeticRight => {
                let shifted = value.bits >> count;
                if value.bits & (1_u64 << (width - 1)) == 0 {
                    shifted
                } else {
                    shifted | (source_width_mask(width) << (width - count))
                }
            }
        }
    };
    source_bitvector(width, bits)
}

fn source_validate_memory_shape(
    width_bits: u32,
    word_size_bytes: u32,
    endianness: MachineMemoryEndianness,
) -> Result<(), RunFailure> {
    if !supported_width(width_bits) || !width_bits.is_multiple_of(8) {
        return Err(RunFailure::Unsupported(format!(
            "memory width {width_bits} is outside the byte-memory subset"
        )));
    }
    if word_size_bytes != 1 {
        return Err(RunFailure::Unsupported(
            "word-addressed memory has no differential execution contract".to_string(),
        ));
    }
    if !matches!(
        endianness,
        MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
    ) {
        return Err(RunFailure::Unsupported(
            "memory endianness is not executable".to_string(),
        ));
    }
    Ok(())
}

fn source_read_memory(
    memory: &BTreeMap<DifferentialMemoryLocation, u8>,
    space: MachineAddressSpace,
    byte_address: u64,
    address_bits: u32,
    width_bits: u32,
    endianness: MachineMemoryEndianness,
) -> Result<DifferentialBitVector, RunFailure> {
    let byte_count = width_bits / 8;
    if address_bits == 0 || address_bits > 64 {
        return Err(RunFailure::Unsupported(format!(
            "source address width {address_bits} is not executable"
        )));
    }
    let maximum = if address_bits == 64 {
        u64::MAX
    } else {
        (1_u64 << address_bits) - 1
    };
    let final_offset = u64::from(byte_count - 1);
    let end = byte_address.checked_add(final_offset).ok_or({
        RunFailure::MemoryOutOfDomain(DifferentialMemoryLocation {
            space,
            byte_address: u64::MAX,
        })
    })?;
    if byte_address > maximum || end > maximum {
        return Err(RunFailure::MemoryOutOfDomain(DifferentialMemoryLocation {
            space,
            byte_address: if byte_address > maximum {
                byte_address
            } else {
                maximum + 1
            },
        }));
    }
    let mut bits = 0_u64;
    for offset in 0..u64::from(byte_count) {
        let address = byte_address + offset;
        let location = DifferentialMemoryLocation {
            space,
            byte_address: address,
        };
        let byte = memory
            .get(&location)
            .copied()
            .ok_or(RunFailure::MemoryOutOfDomain(location))?;
        let shift = match endianness {
            MachineMemoryEndianness::Little => offset * 8,
            MachineMemoryEndianness::Big => u64::from(byte_count - 1) * 8 - offset * 8,
            _ => {
                return Err(RunFailure::Unsupported(
                    "source memory endianness is not executable".to_string(),
                ));
            }
        };
        bits |= u64::from(byte) << shift;
    }
    source_bitvector(width_bits, bits)
}

fn source_write_memory(
    memory: &mut BTreeMap<DifferentialMemoryLocation, u8>,
    space: MachineAddressSpace,
    byte_address: u64,
    address_bits: u32,
    value: DifferentialBitVector,
    endianness: MachineMemoryEndianness,
) -> Result<(), RunFailure> {
    let byte_count = value.width_bits / 8;
    if address_bits == 0 || address_bits > 64 {
        return Err(RunFailure::Unsupported(format!(
            "source address width {address_bits} is not executable"
        )));
    }
    let maximum = if address_bits == 64 {
        u64::MAX
    } else {
        (1_u64 << address_bits) - 1
    };
    let final_offset = u64::from(byte_count - 1);
    let end = byte_address.checked_add(final_offset).ok_or({
        RunFailure::MemoryOutOfDomain(DifferentialMemoryLocation {
            space,
            byte_address: u64::MAX,
        })
    })?;
    if byte_address > maximum || end > maximum {
        return Err(RunFailure::MemoryOutOfDomain(DifferentialMemoryLocation {
            space,
            byte_address: if byte_address > maximum {
                byte_address
            } else {
                maximum + 1
            },
        }));
    }
    let mut locations = Vec::with_capacity(byte_count as usize);
    for offset in 0..u64::from(byte_count) {
        let location = DifferentialMemoryLocation {
            space,
            byte_address: byte_address + offset,
        };
        if !memory.contains_key(&location) {
            return Err(RunFailure::MemoryOutOfDomain(location));
        }
        locations.push(location);
    }
    for (index, location) in locations.into_iter().enumerate() {
        let shift = match endianness {
            MachineMemoryEndianness::Little => index * 8,
            MachineMemoryEndianness::Big => (byte_count as usize - 1 - index) * 8,
            _ => {
                return Err(RunFailure::Unsupported(
                    "memory endianness is not executable".to_string(),
                ));
            }
        };
        memory.insert(location, ((value.bits >> shift) & 0xff) as u8);
    }
    Ok(())
}

fn semantic_bitvector(width_bits: u32, bits: u64) -> Result<DifferentialBitVector, RunFailure> {
    let bits = match width_bits {
        8 | 16 | 32 => bits % (1_u64 << width_bits),
        64 => bits,
        _ => {
            return Err(RunFailure::Unsupported(format!(
                "unsupported semantic bitvector width {width_bits}"
            )));
        }
    };
    Ok(DifferentialBitVector { width_bits, bits })
}

fn semantic_signed_value(value: DifferentialBitVector) -> i128 {
    let sign_threshold = 1_i128 << (value.width_bits - 1);
    let unsigned = i128::from(value.bits);
    if unsigned >= sign_threshold {
        unsigned - (1_i128 << value.width_bits)
    } else {
        unsigned
    }
}

fn semantic_sign_extend(
    value: DifferentialBitVector,
    output_width: u32,
) -> Result<DifferentialBitVector, RunFailure> {
    let shift = 64 - value.width_bits;
    let extended = ((value.bits << shift) as i64 >> shift) as u64;
    semantic_bitvector(output_width, extended)
}

fn semantic_shift_value(
    kind: MachineShiftKind,
    value: DifferentialBitVector,
    count: u64,
) -> Result<DifferentialBitVector, RunFailure> {
    let bits = if count >= u64::from(value.width_bits) {
        match kind {
            MachineShiftKind::Left | MachineShiftKind::LogicalRight => 0,
            MachineShiftKind::ArithmeticRight if semantic_signed_value(value) < 0 => u64::MAX,
            MachineShiftKind::ArithmeticRight => 0,
        }
    } else {
        let count = count as u32;
        match kind {
            MachineShiftKind::Left => value.bits.checked_shl(count).unwrap_or(0),
            MachineShiftKind::LogicalRight => value.bits.checked_shr(count).unwrap_or(0),
            MachineShiftKind::ArithmeticRight => (semantic_signed_value(value) >> count) as u64,
        }
    };
    semantic_bitvector(value.width_bits, bits)
}

fn semantic_validate_memory_shape(
    width_bits: u32,
    word_size_bytes: u32,
    endianness: MachineMemoryEndianness,
) -> Result<(), RunFailure> {
    match width_bits {
        8 | 16 | 32 | 64 => {}
        _ => {
            return Err(RunFailure::Unsupported(format!(
                "semantic memory width {width_bits} is outside the byte-memory subset"
            )));
        }
    }
    if word_size_bytes != 1 {
        return Err(RunFailure::Unsupported(
            "semantic word-addressed memory is not executable".to_string(),
        ));
    }
    match endianness {
        MachineMemoryEndianness::Little | MachineMemoryEndianness::Big => Ok(()),
        _ => Err(RunFailure::Unsupported(
            "semantic memory endianness is not executable".to_string(),
        )),
    }
}

fn semantic_read_memory(
    memory: &BTreeMap<DifferentialMemoryLocation, u8>,
    space: MachineAddressSpace,
    byte_address: u64,
    address_bits: u32,
    width_bits: u32,
    endianness: MachineMemoryEndianness,
) -> Result<DifferentialBitVector, RunFailure> {
    if !(1..=64).contains(&address_bits) {
        return Err(RunFailure::Unsupported(format!(
            "semantic address width {address_bits} is not executable"
        )));
    }
    let byte_count = (width_bits / 8) as usize;
    let outside_start = address_bits < 64 && byte_address >> address_bits != 0;
    let end = byte_address.checked_add((byte_count - 1) as u64);
    let outside_end = end.is_none_or(|end| address_bits < 64 && end >> address_bits != 0);
    if outside_start || outside_end {
        let location = if outside_start {
            byte_address
        } else if address_bits < 64 {
            1_u64 << address_bits
        } else {
            u64::MAX
        };
        return Err(RunFailure::MemoryOutOfDomain(DifferentialMemoryLocation {
            space,
            byte_address: location,
        }));
    }
    let mut bytes = [0_u8; 8];
    for (index, byte) in bytes.iter_mut().take(byte_count).enumerate() {
        let location = DifferentialMemoryLocation {
            space,
            byte_address: byte_address + index as u64,
        };
        *byte = memory
            .get(&location)
            .copied()
            .ok_or(RunFailure::MemoryOutOfDomain(location))?;
    }
    let bits = match endianness {
        MachineMemoryEndianness::Little => u64::from_le_bytes(bytes),
        MachineMemoryEndianness::Big => {
            bytes.copy_within(0..byte_count, 8 - byte_count);
            bytes[..8 - byte_count].fill(0);
            u64::from_be_bytes(bytes)
        }
        _ => {
            return Err(RunFailure::Unsupported(
                "semantic memory endianness is not executable".to_string(),
            ));
        }
    };
    semantic_bitvector(width_bits, bits)
}

fn semantic_write_memory(
    memory: &mut BTreeMap<DifferentialMemoryLocation, u8>,
    space: MachineAddressSpace,
    byte_address: u64,
    address_bits: u32,
    value: DifferentialBitVector,
    endianness: MachineMemoryEndianness,
) -> Result<(), RunFailure> {
    if !(1..=64).contains(&address_bits) {
        return Err(RunFailure::Unsupported(format!(
            "semantic address width {address_bits} is not executable"
        )));
    }
    let byte_count = (value.width_bits / 8) as usize;
    let outside_start = address_bits < 64 && byte_address >> address_bits != 0;
    let end = byte_address.checked_add((byte_count - 1) as u64);
    let outside_end = end.is_none_or(|end| address_bits < 64 && end >> address_bits != 0);
    if outside_start || outside_end {
        let location = if outside_start {
            byte_address
        } else if address_bits < 64 {
            1_u64 << address_bits
        } else {
            u64::MAX
        };
        return Err(RunFailure::MemoryOutOfDomain(DifferentialMemoryLocation {
            space,
            byte_address: location,
        }));
    }
    let bytes = match endianness {
        MachineMemoryEndianness::Little => value.bits.to_le_bytes(),
        MachineMemoryEndianness::Big => value.bits.to_be_bytes(),
        _ => {
            return Err(RunFailure::Unsupported(
                "semantic memory endianness is not executable".to_string(),
            ));
        }
    };
    for index in 0..byte_count {
        let location = DifferentialMemoryLocation {
            space,
            byte_address: byte_address + index as u64,
        };
        if !memory.contains_key(&location) {
            return Err(RunFailure::MemoryOutOfDomain(location));
        }
    }
    for index in 0..byte_count {
        let source_index = match endianness {
            MachineMemoryEndianness::Little => index,
            MachineMemoryEndianness::Big => 8 - byte_count + index,
            _ => unreachable!(),
        };
        memory.insert(
            DifferentialMemoryLocation {
                space,
                byte_address: byte_address + index as u64,
            },
            bytes[source_index],
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2ssa::{StackAddressBase, StackAddressRoot};
    use std::ffi::c_void;
    use std::mem::size_of;

    use crate::certified_private_frame_join::{
        canonical_private_frame_accesses_for_test,
        certified_private_frame_join_rewrite_from_parts_for_test,
        private_frame_condition_accesses_for_test,
    };
    use crate::semantic_c::{
        SemanticCError, SemanticCExprKind, SemanticCInputOrigin,
        certified_private_entry_stack_pointer_input, value_name,
    };
    use crate::{
        CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_FUNCTION_SCHEMA_VERSION,
        CERTIFIED_PRIVATE_FRAME_JOIN_REWRITE_SCHEMA_VERSION,
        CertifiedPrivateFrameConditionalJoinFunction,
        CertifiedPrivateFrameConditionalJoinFunctionScope,
        CertifiedPrivateFrameConditionalJoinRewrite,
        CertifiedPrivateFrameConditionalJoinRewriteScope, CertifiedPrivateFrameJoinValueOrigin,
        PrivateFrameConditionalJoinRewriteError,
    };

    use r2cert::{
        CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION, CertifiedMachineFunction,
        CertifiedMemoryStatementKind, CertifiedPrivateFrameJoinTransfer, CertifiedTypedRegionKind,
        LedgerClosureError, TypedRegionMapping, certify_private_frame_conditional_join_region,
    };

    use r2source::{
        RADARE_ABI_VERSION, RADARE_CAP_EXACT_FRAME_POINTER_STORAGE,
        RADARE_CAP_EXACT_FUNCTION_INTERFACE, RADARE_CAP_EXACT_FUNCTION_TYPES,
        RADARE_CAP_EXACT_RETURN_MECHANISM, RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
        RADARE_CAP_EXACT_STACK_SLOT_ROLES, RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE,
        RADARE_CAP_RETURN_ADDRESS_STORAGE, RADARE_CAP_REVISION, RADARE_CAP_STACK_POINTER_STORAGE,
        RADARE_CAP_STACK_SLOTS, RADARE_CAP_TYPES, RADARE_ENDIAN_LITTLE,
        RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION, RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION,
        RadareAbi138Accessors, RadareAbi138AggregateMemberView, RadareAbi138AggregateView,
        RadareAbi138BlockView, RadareAbi138CarrierProjection, RadareAbi138FunctionInterfaceView,
        RadareAbi138ParameterView, RadareAbi138RegisterStorageView,
        RadareAbi138ReturnMechanismView, RadareAbi138SnapshotInput, RadareAbi138SnapshotView,
        RadareAbi138StackAllocationContractView, RadareAbi138StackSlotView,
        RadareAbi138SuccessorView, RadareAbi138TypeGraphView, RadareAbi138TypeView,
    };

    #[test]
    fn runtime_rewrite_consumption_accepts_one_short_circuit_select_arm() {
        let left = StructuredAccessId {
            inst: r2ssa::InstId(10),
            ordinal: 0,
        };
        let right = StructuredAccessId {
            inst: r2ssa::InstId(11),
            ordinal: 0,
        };
        let foreign = StructuredAccessId {
            inst: r2ssa::InstId(12),
            ordinal: 0,
        };
        let sealed = BTreeMap::from([
            (left, DifferentialBitVector::new(8, 1).unwrap()),
            (right, DifferentialBitVector::new(8, 0).unwrap()),
        ]);
        assert!(runtime_rewrite_consumption_is_valid(
            &BTreeSet::from([left]),
            &sealed,
        ));
        assert!(runtime_rewrite_consumption_is_valid(
            &BTreeSet::from([right]),
            &sealed,
        ));
        assert!(!runtime_rewrite_consumption_is_valid(
            &BTreeSet::from([foreign]),
            &sealed,
        ));
    }

    #[test]
    fn source_memory_space_authority_rejects_each_mismatch() {
        let exact = [r2il::SpaceId::Ram; 5];
        assert!(memory_space_authorities_match(
            exact[0], exact[1], exact[2], exact[3], exact[4]
        ));

        for mismatched_authority in 0..exact.len() {
            let mut spaces = exact;
            spaces[mismatched_authority] = r2il::SpaceId::Custom(7);
            assert!(
                !memory_space_authorities_match(
                    spaces[0], spaces[1], spaces[2], spaces[3], spaces[4]
                ),
                "authority {mismatched_authority} must bind the exact memory space"
            );
        }
    }

    #[derive(Debug, Clone)]
    struct NativeSpanSuccessorFixture {
        kind: i32,
        target: u64,
        external: bool,
    }

    #[derive(Debug, Clone)]
    struct NativeSpanBlockFixture {
        addr: u64,
        bytes: Vec<u8>,
        successors: Vec<NativeSpanSuccessorFixture>,
    }

    struct NativeSpanStackSlotFixture {
        view: RadareAbi138StackSlotView,
        strings: [String; 5],
    }

    struct NativeSpanSnapshotFixture {
        addr: u64,
        blocks: Vec<NativeSpanBlockFixture>,
        arch_id: String,
        cpu_id: String,
        calling_convention: String,
        return_address: RadareAbi138RegisterStorageView,
        stack_pointer: RadareAbi138RegisterStorageView,
        frame_pointer: Option<RadareAbi138RegisterStorageView>,
        scalar_return: Option<RadareAbi138RegisterStorageView>,
        return_address_name: String,
        stack_pointer_name: String,
        frame_pointer_name: Option<String>,
        scalar_return_name: Option<String>,
        parameter: Option<RadareAbi138ParameterView>,
        parameter_name: Option<String>,
        stack_slots: Vec<NativeSpanStackSlotFixture>,
        exact_private_stack: bool,
        implicit_active_sp_bytes: u32,
        stacked_return: bool,
        types: Vec<(i32, u64)>,
        return_type_id: u32,
        return_carrier: RadareAbi138CarrierProjection,
    }

    impl NativeSpanSnapshotFixture {
        fn top(&self) -> RadareAbi138SnapshotView {
            RadareAbi138SnapshotView {
                schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
                struct_size: u32::try_from(size_of::<RadareAbi138SnapshotView>())
                    .expect("snapshot view size fits u32"),
                capabilities: RADARE_CAP_REVISION
                    | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE
                    | RADARE_CAP_EXACT_FUNCTION_INTERFACE
                    | RADARE_CAP_STACK_SLOTS
                    | RADARE_CAP_EXACT_STACK_SLOT_ROLES
                    | RADARE_CAP_RETURN_ADDRESS_STORAGE
                    | RADARE_CAP_STACK_POINTER_STORAGE
                    | if self.frame_pointer.is_some() {
                        RADARE_CAP_EXACT_FRAME_POINTER_STORAGE
                    } else {
                        0
                    }
                    | if self.parameter.is_some() {
                        RADARE_CAP_EXACT_FUNCTION_TYPES | RADARE_CAP_TYPES
                    } else {
                        0
                    }
                    | if self.exact_private_stack {
                        RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT
                    } else {
                        0
                    }
                    | if self.stacked_return {
                        RADARE_CAP_EXACT_RETURN_MECHANISM
                    } else {
                        0
                    },
                function_addr: self.addr,
                function_size: self.end().checked_sub(self.addr).expect("fixture size"),
                bits: 64,
                endian: RADARE_ENDIAN_LITTLE,
                arch_id_length: self.arch_id.len(),
                cpu_id_length: self.cpu_id.len(),
                function_name_length: 19,
                revision_identity: self.addr,
                num_blocks: self.blocks.len(),
                num_external_exits: self.external_exits().len(),
                total_source_bytes: self.blocks.iter().map(|block| block.bytes.len()).sum(),
                num_types: self.types.len(),
                num_stack_slots: self.stack_slots.len(),
                ..Default::default()
            }
        }

        fn end(&self) -> u64 {
            self.blocks
                .last()
                .and_then(|block| {
                    block.addr.checked_add(
                        u64::try_from(block.bytes.len()).expect("fixture size fits u64"),
                    )
                })
                .expect("fixture range")
        }

        fn external_exits(&self) -> Vec<u64> {
            self.blocks
                .iter()
                .flat_map(|block| &block.successors)
                .filter(|successor| successor.external)
                .map(|successor| successor.target)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
    }

    unsafe fn fixture<'a>(snapshot: *const c_void) -> &'a NativeSpanSnapshotFixture {
        // SAFETY: every callback is invoked synchronously with the live fixture
        // pointer supplied to `capture_radare_abi138` below.
        unsafe { &*snapshot.cast::<NativeSpanSnapshotFixture>() }
    }

    unsafe fn copy_fixture_string(value: &[u8], out: *mut u8, capacity: usize) -> u8 {
        if capacity != value.len().saturating_add(1) {
            return 0;
        }
        // SAFETY: the audited capture boundary supplies exactly `capacity`
        // writable bytes and this helper checks the required length first.
        unsafe {
            std::ptr::copy_nonoverlapping(value.as_ptr(), out, value.len());
            out.add(value.len()).write(0);
        }
        1
    }

    unsafe extern "C" fn snapshot_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138SnapshotView,
    ) -> u8 {
        // SAFETY: callback arguments are the live fixture and capture-owned output.
        unsafe { out.write(fixture(snapshot).top()) };
        1
    }

    unsafe extern "C" fn arch_id(snapshot: *const c_void, out: *mut u8, capacity: usize) -> u8 {
        // SAFETY: forwarded capture-owned output buffer.
        unsafe { copy_fixture_string(fixture(snapshot).arch_id.as_bytes(), out, capacity) }
    }

    unsafe extern "C" fn cpu_id(snapshot: *const c_void, out: *mut u8, capacity: usize) -> u8 {
        // SAFETY: forwarded capture-owned output buffer.
        unsafe { copy_fixture_string(fixture(snapshot).cpu_id.as_bytes(), out, capacity) }
    }

    unsafe extern "C" fn function_name(
        _snapshot: *const c_void,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        // SAFETY: forwarded capture-owned output buffer.
        unsafe { copy_fixture_string(b"native_span_fixture", out, capacity) }
    }

    unsafe extern "C" fn interface_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138FunctionInterfaceView,
    ) -> u8 {
        // SAFETY: the callback receives the live fixture pointer.
        let fixture = unsafe { fixture(snapshot) };
        // SAFETY: the capture owns one initialized output slot.
        unsafe {
            out.write(RadareAbi138FunctionInterfaceView {
                calling_convention_length: fixture.calling_convention.len(),
                num_parameters: usize::from(fixture.parameter.is_some()),
                return_kind: if fixture.parameter.is_some() { 2 } else { 1 },
                return_storage: fixture.scalar_return.unwrap_or_default(),
                return_address_storage: fixture.return_address,
                stack_pointer_storage: fixture.stack_pointer,
                stack_resources_complete: 1,
                stack_slot_roles_complete: 1,
                complete: 1,
                return_type_id: fixture.return_type_id,
                return_carrier: fixture.return_carrier,
                logical_types_complete: u8::from(fixture.parameter.is_some()),
                ..Default::default()
            })
        };
        1
    }

    unsafe extern "C" fn interface_calling_convention(
        snapshot: *const c_void,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        // SAFETY: forwarded capture-owned output buffer.
        unsafe {
            copy_fixture_string(
                fixture(snapshot).calling_convention.as_bytes(),
                out,
                capacity,
            )
        }
    }

    unsafe extern "C" fn interface_storage_name(
        snapshot: *const c_void,
        kind: i32,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        // SAFETY: the callback receives the live fixture pointer.
        let fixture = unsafe { fixture(snapshot) };
        let name = match kind {
            0 => fixture
                .scalar_return_name
                .as_ref()
                .map(String::as_bytes)
                .unwrap_or_default(),
            1 => fixture.return_address_name.as_bytes(),
            2 => fixture.stack_pointer_name.as_bytes(),
            3 => fixture
                .frame_pointer_name
                .as_ref()
                .map(String::as_bytes)
                .unwrap_or_default(),
            _ => return 0,
        };
        // SAFETY: forwarded capture-owned output buffer.
        unsafe { copy_fixture_string(name, out, capacity) }
    }

    unsafe extern "C" fn parameter_view(
        snapshot: *const c_void,
        index: usize,
        out: *mut RadareAbi138ParameterView,
    ) -> u8 {
        let fixture = unsafe { fixture(snapshot) };
        let Some(parameter) = fixture.parameter.filter(|_| index == 0) else {
            return 0;
        };
        unsafe { out.write(parameter) };
        1
    }

    unsafe extern "C" fn parameter_name(
        snapshot: *const c_void,
        index: usize,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        let fixture = unsafe { fixture(snapshot) };
        let Some(name) = fixture.parameter_name.as_ref().filter(|_| index == 0) else {
            return 0;
        };
        unsafe { copy_fixture_string(name.as_bytes(), out, capacity) }
    }

    unsafe extern "C" fn stack_slot_view(
        snapshot: *const c_void,
        index: usize,
        out: *mut RadareAbi138StackSlotView,
    ) -> u8 {
        let fixture = unsafe { fixture(snapshot) };
        let Some(slot) = fixture.stack_slots.get(index) else {
            return 0;
        };
        unsafe { out.write(slot.view) };
        1
    }

    unsafe extern "C" fn stack_slot_string(
        snapshot: *const c_void,
        index: usize,
        kind: i32,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        let fixture = unsafe { fixture(snapshot) };
        let Some(value) = fixture.stack_slots.get(index).and_then(|slot| {
            usize::try_from(kind)
                .ok()
                .and_then(|kind| slot.strings.get(kind))
        }) else {
            return 0;
        };
        unsafe { copy_fixture_string(value.as_bytes(), out, capacity) }
    }

    unsafe extern "C" fn type_graph_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138TypeGraphView,
    ) -> u8 {
        let fixture = unsafe { fixture(snapshot) };
        if fixture.parameter.is_none() {
            return 0;
        }
        unsafe {
            out.write(RadareAbi138TypeGraphView {
                num_types: fixture.types.len(),
                num_aggregates: 0,
                complete: 1,
            })
        };
        1
    }

    unsafe extern "C" fn type_view(
        snapshot: *const c_void,
        index: usize,
        out: *mut RadareAbi138TypeView,
    ) -> u8 {
        let fixture = unsafe { fixture(snapshot) };
        let Some((kind, size_bits)) = fixture.types.get(index).copied() else {
            return 0;
        };
        unsafe {
            out.write(RadareAbi138TypeView {
                id: u32::try_from(index).expect("type index fits u32"),
                kind,
                size_bits,
                align_bits: size_bits,
                target_type_id: u32::MAX,
                aggregate_id: u32::MAX,
            })
        };
        1
    }

    unsafe extern "C" fn unused_aggregate_view(
        _snapshot: *const c_void,
        _index: usize,
        _out: *mut RadareAbi138AggregateView,
    ) -> u8 {
        0
    }

    unsafe extern "C" fn unused_aggregate_member_view(
        _snapshot: *const c_void,
        _aggregate: usize,
        _member: usize,
        _out: *mut RadareAbi138AggregateMemberView,
    ) -> u8 {
        0
    }

    unsafe extern "C" fn unused_aggregate_member_name(
        _snapshot: *const c_void,
        _aggregate: usize,
        _member: usize,
        _out: *mut u8,
        _capacity: usize,
    ) -> u8 {
        0
    }

    unsafe extern "C" fn block_view(
        snapshot: *const c_void,
        index: usize,
        out: *mut RadareAbi138BlockView,
    ) -> u8 {
        // SAFETY: the callback receives the live fixture pointer.
        let fixture = unsafe { fixture(snapshot) };
        let Some(block) = fixture.blocks.get(index) else {
            return 0;
        };
        // SAFETY: the capture owns one initialized output slot.
        unsafe {
            out.write(RadareAbi138BlockView {
                addr: block.addr,
                size: u64::try_from(block.bytes.len()).expect("fixture size fits u64"),
                num_successors: block.successors.len(),
                switch_addr: u64::MAX,
            })
        };
        1
    }

    unsafe extern "C" fn block_bytes(
        snapshot: *const c_void,
        block_index: usize,
        offset: usize,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        // SAFETY: the callback receives the live fixture pointer.
        let fixture = unsafe { fixture(snapshot) };
        let Some(block) = fixture.blocks.get(block_index) else {
            return 0;
        };
        if offset != 0 || capacity != block.bytes.len() {
            return 0;
        }
        // SAFETY: the capture-owned output has exactly the advertised capacity.
        unsafe {
            std::ptr::copy_nonoverlapping(block.bytes.as_ptr(), out, capacity);
        }
        1
    }

    unsafe extern "C" fn successor_view(
        snapshot: *const c_void,
        block_index: usize,
        successor_index: usize,
        out: *mut RadareAbi138SuccessorView,
    ) -> u8 {
        // SAFETY: the callback receives the live fixture pointer.
        let fixture = unsafe { fixture(snapshot) };
        let Some(successor) = fixture
            .blocks
            .get(block_index)
            .and_then(|block| block.successors.get(successor_index))
        else {
            return 0;
        };
        // SAFETY: the capture owns one initialized output slot.
        unsafe {
            out.write(RadareAbi138SuccessorView {
                kind: successor.kind,
                target_addr: successor.target,
                external: u8::from(successor.external),
                ..Default::default()
            })
        };
        1
    }

    unsafe extern "C" fn external_exit(snapshot: *const c_void, index: usize, out: *mut u64) -> u8 {
        // SAFETY: callback arguments are the live fixture and capture-owned output.
        let fixture = unsafe { fixture(snapshot) };
        let external_exits = fixture.external_exits();
        let Some(exit) = external_exits.get(index) else {
            return 0;
        };
        unsafe { out.write(*exit) };
        1
    }

    unsafe extern "C" fn return_mechanism_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138ReturnMechanismView,
    ) -> u8 {
        // SAFETY: callback arguments are the live fixture and capture-owned output.
        let fixture = unsafe { fixture(snapshot) };
        if !fixture.stacked_return {
            return 0;
        }
        unsafe {
            out.write(RadareAbi138ReturnMechanismView {
                kind: 1,
                stack_offset: 0,
                slot_size_bytes: 8,
                stack_pointer_delta_bytes: 8,
            })
        };
        1
    }

    unsafe extern "C" fn frame_pointer_storage_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138RegisterStorageView,
    ) -> u8 {
        // SAFETY: callback arguments are the live fixture and capture-owned output.
        let fixture = unsafe { fixture(snapshot) };
        let Some(frame_pointer) = fixture.frame_pointer else {
            return 0;
        };
        unsafe { out.write(frame_pointer) };
        1
    }

    unsafe extern "C" fn stack_allocation_contract_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138StackAllocationContractView,
    ) -> u8 {
        // SAFETY: callback arguments are the live fixture and capture-owned output.
        let fixture = unsafe { fixture(snapshot) };
        if !fixture.exact_private_stack {
            return 0;
        }
        unsafe {
            out.write(RadareAbi138StackAllocationContractView {
                growth: 1,
                implicit_active_sp_bytes: fixture.implicit_active_sp_bytes,
            })
        };
        1
    }

    type LiftedBlockSpans = Vec<(u64, u32, u64, u64)>;

    struct X86InterfaceFixture<'a> {
        exact_private_stack: bool,
        implicit_active_sp_bytes: u32,
        stacked_return: bool,
        frame_pointer_register: Option<&'a str>,
        parameter_register: Option<&'a str>,
        parameter_logical_type_id: u32,
        parameter_carrier: RadareAbi138CarrierProjection,
        scalar_return_register: Option<&'a str>,
        types: Vec<(i32, u64)>,
        return_type_id: u32,
        return_carrier: RadareAbi138CarrierProjection,
    }

    fn trusted_x86_blocks_fixture(
        blocks: Vec<NativeSpanBlockFixture>,
        addr: u64,
        exact_private_stack: bool,
        parameter_register: Option<&str>,
    ) -> (
        TrustedSsaArtifact,
        Vec<r2il::R2ILBlock>,
        Vec<LiftedBlockSpans>,
    ) {
        trusted_x86_blocks_fixture_with_interface(
            blocks,
            addr,
            X86InterfaceFixture {
                exact_private_stack,
                implicit_active_sp_bytes: 0,
                stacked_return: exact_private_stack,
                frame_pointer_register: None,
                parameter_register,
                parameter_logical_type_id: 0,
                parameter_carrier: RadareAbi138CarrierProjection {
                    kind: 1,
                    offset_bits: 0,
                    size_bits: 64,
                },
                scalar_return_register: parameter_register.map(|_| "RAX"),
                types: parameter_register
                    .map(|_| vec![(2, 64), (2, 32)])
                    .unwrap_or_default(),
                return_type_id: if parameter_register.is_some() {
                    1
                } else {
                    u32::MAX
                },
                return_carrier: if parameter_register.is_some() {
                    RadareAbi138CarrierProjection {
                        kind: 2,
                        offset_bits: 0,
                        size_bits: 32,
                    }
                } else {
                    RadareAbi138CarrierProjection::default()
                },
            },
        )
    }

    fn trusted_x86_blocks_fixture_with_interface(
        blocks: Vec<NativeSpanBlockFixture>,
        addr: u64,
        interface: X86InterfaceFixture<'_>,
    ) -> (
        TrustedSsaArtifact,
        Vec<r2il::R2ILBlock>,
        Vec<LiftedBlockSpans>,
    ) {
        let trusted_disassembler = r2sleigh_lift::Disassembler::from_trusted_profile(
            r2sleigh_lift::TrustedSleighProfile::X86_64,
        )
        .expect("embedded x86-64 profile");
        let return_address = trusted_disassembler
            .register("RIP")
            .expect("trusted RIP register");
        let stack_pointer = trusted_disassembler
            .register("RSP")
            .expect("trusted RSP register");
        let frame_pointer = interface.frame_pointer_register.map(|name| {
            let register = trusted_disassembler
                .register(name)
                .expect("trusted frame-pointer register");
            RadareAbi138RegisterStorageView {
                name_length: name.len(),
                offset: register.address.offset,
                size: u32::try_from(register.size).expect("frame-pointer size fits u32"),
            }
        });
        let parameter = interface.parameter_register.map(|name| {
            let register = trusted_disassembler
                .register(name)
                .expect("trusted parameter register");
            RadareAbi138ParameterView {
                index: 0,
                name_length: name.len(),
                storage: RadareAbi138RegisterStorageView {
                    name_length: name.len(),
                    offset: register.address.offset,
                    size: u32::try_from(register.size).expect("parameter size fits u32"),
                },
                logical_type_id: interface.parameter_logical_type_id,
                carrier: interface.parameter_carrier,
            }
        });
        let scalar_return = interface.scalar_return_register.map(|name| {
            let register = trusted_disassembler
                .register(name)
                .expect("trusted scalar-return register");
            RadareAbi138RegisterStorageView {
                name_length: name.len(),
                offset: register.address.offset,
                size: u32::try_from(register.size).expect("scalar-return size fits u32"),
            }
        });
        let stack_slots = match (
            frame_pointer,
            parameter,
            interface.frame_pointer_register,
            interface.parameter_register,
        ) {
            (Some(frame_pointer), Some(parameter), Some(frame_name), Some(parameter_name)) => vec![
                NativeSpanStackSlotFixture {
                    view: RadareAbi138StackSlotView {
                        base: 0,
                        base_name_length: frame_name.len(),
                        base_offset: frame_pointer.offset,
                        base_size: frame_pointer.size,
                        offset: -8,
                        size: 4,
                        offset_valid: 1,
                        role: 2,
                        arg_index: 0,
                        home_reg_length: parameter_name.len(),
                        home_reg_offset: parameter.storage.offset,
                        home_reg_size: parameter.storage.size,
                        ..Default::default()
                    },
                    strings: [
                        String::new(),
                        String::new(),
                        frame_name.to_string(),
                        String::new(),
                        parameter_name.to_string(),
                    ],
                },
                NativeSpanStackSlotFixture {
                    view: RadareAbi138StackSlotView {
                        base: 0,
                        base_name_length: frame_name.len(),
                        base_offset: frame_pointer.offset,
                        base_size: frame_pointer.size,
                        offset: -4,
                        size: 4,
                        offset_valid: 1,
                        role: 0,
                        arg_index: -1,
                        ..Default::default()
                    },
                    strings: [
                        String::new(),
                        String::new(),
                        frame_name.to_string(),
                        String::new(),
                        String::new(),
                    ],
                },
            ],
            _ => Vec::new(),
        };
        let fixture = NativeSpanSnapshotFixture {
            addr,
            blocks,
            arch_id: "x86".into(),
            cpu_id: "x86".into(),
            calling_convention: "sysv".into(),
            return_address: RadareAbi138RegisterStorageView {
                name_length: 3,
                offset: return_address.address.offset,
                size: u32::try_from(return_address.size).expect("RIP size fits u32"),
            },
            stack_pointer: RadareAbi138RegisterStorageView {
                name_length: 3,
                offset: stack_pointer.address.offset,
                size: u32::try_from(stack_pointer.size).expect("RSP size fits u32"),
            },
            frame_pointer,
            scalar_return,
            return_address_name: "RIP".to_string(),
            stack_pointer_name: "RSP".to_string(),
            frame_pointer_name: interface.frame_pointer_register.map(str::to_string),
            scalar_return_name: interface.scalar_return_register.map(str::to_string),
            parameter,
            parameter_name: interface.parameter_register.map(str::to_string),
            stack_slots,
            exact_private_stack: interface.exact_private_stack,
            implicit_active_sp_bytes: interface.implicit_active_sp_bytes,
            stacked_return: interface.stacked_return,
            types: interface.types,
            return_type_id: interface.return_type_id,
            return_carrier: interface.return_carrier,
        };
        let accessors = RadareAbi138Accessors {
            struct_size: u32::try_from(size_of::<RadareAbi138Accessors>())
                .expect("accessor size fits u32"),
            abi_version: RADARE_ABI_VERSION,
            snapshot_schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            accessor_schema_version: RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION,
            snapshot_view: Some(snapshot_view),
            arch_id: Some(arch_id),
            cpu_id: Some(cpu_id),
            function_name: Some(function_name),
            interface_view: Some(interface_view),
            interface_calling_convention: Some(interface_calling_convention),
            interface_storage_name: Some(interface_storage_name),
            parameter_view: Some(parameter_view),
            parameter_name: Some(parameter_name),
            parameter_storage_name: Some(parameter_name),
            stack_slot_view: Some(stack_slot_view),
            stack_slot_string: Some(stack_slot_string),
            type_graph_view: Some(type_graph_view),
            type_view: Some(type_view),
            aggregate_view: Some(unused_aggregate_view),
            aggregate_name: Some(parameter_name),
            aggregate_member_view: Some(unused_aggregate_member_view),
            aggregate_member_name: Some(unused_aggregate_member_name),
            block_view: Some(block_view),
            block_bytes: Some(block_bytes),
            successor_view: Some(successor_view),
            external_exit: Some(external_exit),
            return_mechanism_view: Some(return_mechanism_view),
            frame_pointer_storage_view: Some(frame_pointer_storage_view),
            stack_allocation_contract_view: Some(stack_allocation_contract_view),
            ..Default::default()
        };
        let input = RadareAbi138SnapshotInput {
            struct_size: u32::try_from(size_of::<RadareAbi138SnapshotInput>())
                .expect("input size fits u32"),
            abi_version: RADARE_ABI_VERSION,
            snapshot_schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            accessor_schema_version: RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION,
            snapshot: (&fixture as *const NativeSpanSnapshotFixture).cast(),
            accessors: &accessors,
        };
        // SAFETY: the fixture and immutable callback table remain live for the
        // full synchronous capture and every callback obeys the exact ABI.
        let source =
            unsafe { r2source::capture_radare_abi138(&input) }.expect("owned source capture");
        let lifted = r2sleigh_lift::Disassembler::lift_owned_function(source)
            .expect("trusted production lift");
        let blocks = lifted
            .lifted()
            .blocks()
            .iter()
            .map(|block| block.block().clone())
            .collect();
        let spans = lifted
            .lifted()
            .blocks()
            .iter()
            .map(|block| {
                block
                    .instruction_spans()
                    .iter()
                    .map(|span| {
                        (
                            span.addr(),
                            span.size(),
                            span.first_canonical_op(),
                            span.canonical_op_count(),
                        )
                    })
                    .collect()
            })
            .collect();
        (
            TrustedSsaArtifact::prepare(lifted).expect("trusted production SSA"),
            blocks,
            spans,
        )
    }

    fn trusted_x86_fixture(
        bytes: &[u8],
        addr: u64,
        terminal_return: bool,
        exact_private_stack: bool,
    ) -> (TrustedSsaArtifact, r2il::R2ILBlock, LiftedBlockSpans) {
        let end = addr
            .checked_add(u64::try_from(bytes.len()).expect("fixture size fits u64"))
            .expect("fixture range");
        let successors = (!terminal_return)
            .then_some(NativeSpanSuccessorFixture {
                kind: 1,
                target: end,
                external: true,
            })
            .into_iter()
            .collect();
        let (trusted, blocks, spans) = trusted_x86_blocks_fixture(
            vec![NativeSpanBlockFixture {
                addr,
                bytes: bytes.to_vec(),
                successors,
            }],
            addr,
            exact_private_stack,
            None,
        );
        let [block] = blocks.try_into().expect("one lifted block");
        let [spans] = spans.try_into().expect("one lifted block span set");
        (trusted, block, spans)
    }

    fn try_trusted_aarch64_blocks_fixture(
        blocks: Vec<NativeSpanBlockFixture>,
    ) -> Result<
        (
            TrustedSsaArtifact,
            Vec<r2il::R2ILBlock>,
            Vec<LiftedBlockSpans>,
        ),
        String,
    > {
        let addr = blocks
            .first()
            .map(|block| block.addr)
            .ok_or_else(|| "AArch64 fixture has no blocks".to_string())?;
        let trusted_disassembler = r2sleigh_lift::Disassembler::from_trusted_profile(
            r2sleigh_lift::TrustedSleighProfile::Aarch64Le,
        )
        .map_err(|error| format!("embedded AArch64 profile: {error}"))?;
        let register = |name: &str| {
            trusted_disassembler
                .register(name)
                .map_err(|error| format!("trusted AArch64 {name} register: {error}"))
        };
        let x0 = register("x0")?;
        let w0 = register("w0")?;
        let stack_pointer = register("sp")?;
        let return_address = register("x30")?;
        if x0.address.offset != w0.address.offset || x0.size != 8 || w0.size != 4 {
            return Err("trusted AArch64 x0/w0 storage alias is not exact".to_string());
        }
        let fixture = NativeSpanSnapshotFixture {
            addr,
            blocks,
            arch_id: "arm".into(),
            cpu_id: "arm".into(),
            calling_convention: "aapcs".into(),
            return_address: RadareAbi138RegisterStorageView {
                name_length: 3,
                offset: return_address.address.offset,
                size: u32::try_from(return_address.size).expect("x30 size fits u32"),
            },
            stack_pointer: RadareAbi138RegisterStorageView {
                name_length: 2,
                offset: stack_pointer.address.offset,
                size: u32::try_from(stack_pointer.size).expect("sp size fits u32"),
            },
            frame_pointer: None,
            scalar_return: Some(RadareAbi138RegisterStorageView {
                name_length: 2,
                offset: x0.address.offset,
                size: u32::try_from(x0.size).expect("x0 size fits u32"),
            }),
            return_address_name: "x30".into(),
            stack_pointer_name: "sp".into(),
            frame_pointer_name: None,
            scalar_return_name: Some("x0".into()),
            parameter: Some(RadareAbi138ParameterView {
                index: 0,
                name_length: 2,
                storage: RadareAbi138RegisterStorageView {
                    name_length: 2,
                    offset: x0.address.offset,
                    size: u32::try_from(x0.size).expect("x0 size fits u32"),
                },
                logical_type_id: 0,
                carrier: RadareAbi138CarrierProjection {
                    kind: 2,
                    offset_bits: 0,
                    size_bits: 32,
                },
            }),
            parameter_name: Some("x0".into()),
            stack_slots: Vec::new(),
            exact_private_stack: true,
            implicit_active_sp_bytes: 0,
            stacked_return: false,
            types: vec![(1, 32)],
            return_type_id: 0,
            return_carrier: RadareAbi138CarrierProjection {
                kind: 2,
                offset_bits: 0,
                size_bits: 32,
            },
        };
        let accessors = RadareAbi138Accessors {
            struct_size: u32::try_from(size_of::<RadareAbi138Accessors>())
                .expect("accessor size fits u32"),
            abi_version: RADARE_ABI_VERSION,
            snapshot_schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            accessor_schema_version: RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION,
            snapshot_view: Some(snapshot_view),
            arch_id: Some(arch_id),
            cpu_id: Some(cpu_id),
            function_name: Some(function_name),
            interface_view: Some(interface_view),
            interface_calling_convention: Some(interface_calling_convention),
            interface_storage_name: Some(interface_storage_name),
            parameter_view: Some(parameter_view),
            parameter_name: Some(parameter_name),
            parameter_storage_name: Some(parameter_name),
            stack_slot_view: Some(stack_slot_view),
            stack_slot_string: Some(stack_slot_string),
            type_graph_view: Some(type_graph_view),
            type_view: Some(type_view),
            aggregate_view: Some(unused_aggregate_view),
            aggregate_name: Some(parameter_name),
            aggregate_member_view: Some(unused_aggregate_member_view),
            aggregate_member_name: Some(unused_aggregate_member_name),
            block_view: Some(block_view),
            block_bytes: Some(block_bytes),
            successor_view: Some(successor_view),
            external_exit: Some(external_exit),
            return_mechanism_view: Some(return_mechanism_view),
            frame_pointer_storage_view: Some(frame_pointer_storage_view),
            stack_allocation_contract_view: Some(stack_allocation_contract_view),
            ..Default::default()
        };
        let input = RadareAbi138SnapshotInput {
            struct_size: u32::try_from(size_of::<RadareAbi138SnapshotInput>())
                .expect("input size fits u32"),
            abi_version: RADARE_ABI_VERSION,
            snapshot_schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            accessor_schema_version: RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION,
            snapshot: (&fixture as *const NativeSpanSnapshotFixture).cast(),
            accessors: &accessors,
        };
        // SAFETY: the fixture and immutable callback table remain live for the
        // full synchronous capture and every callback obeys the exact ABI.
        let source = unsafe { r2source::capture_radare_abi138(&input) }
            .map_err(|error| format!("AArch64 source capture: {error}"))?;
        let lifted = r2sleigh_lift::Disassembler::lift_owned_function(source)
            .map_err(|error| format!("AArch64 trusted lift: {error}"))?;
        let blocks = lifted
            .lifted()
            .blocks()
            .iter()
            .map(|block| block.block().clone())
            .collect();
        let spans = lifted
            .lifted()
            .blocks()
            .iter()
            .map(|block| {
                block
                    .instruction_spans()
                    .iter()
                    .map(|span| {
                        (
                            span.addr(),
                            span.size(),
                            span.first_canonical_op(),
                            span.canonical_op_count(),
                        )
                    })
                    .collect()
            })
            .collect();
        let trusted = TrustedSsaArtifact::prepare(lifted)
            .map_err(|error| format!("AArch64 trusted SSA: {error}"))?;
        Ok((trusted, blocks, spans))
    }

    fn aarch64_private_join_blocks() -> Vec<NativeSpanBlockFixture> {
        const BASE: u64 = 0x1_0000_0000;
        const HEADER: u64 = BASE + 0x598;
        const FORWARDER: u64 = BASE + 0x5b0;
        const STORE_ONE: u64 = BASE + 0x5b4;
        const STORE_ZERO: u64 = BASE + 0x5c0;
        const JOIN: u64 = BASE + 0x5c8;
        vec![
            NativeSpanBlockFixture {
                addr: HEADER,
                bytes: vec![
                    0xff, 0x43, 0x00, 0xd1, 0xe0, 0x0b, 0x00, 0xb9, 0xe8, 0x0b, 0x40, 0xb9, 0xa9,
                    0xd5, 0x9b, 0x52, 0x08, 0x01, 0x09, 0x6b, 0xa1, 0x00, 0x00, 0x54,
                ],
                successors: vec![
                    NativeSpanSuccessorFixture {
                        kind: 0,
                        target: STORE_ZERO,
                        external: false,
                    },
                    NativeSpanSuccessorFixture {
                        kind: 1,
                        target: FORWARDER,
                        external: false,
                    },
                ],
            },
            NativeSpanBlockFixture {
                addr: FORWARDER,
                bytes: vec![0x01, 0x00, 0x00, 0x14],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: STORE_ONE,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: STORE_ONE,
                bytes: vec![
                    0x28, 0x00, 0x80, 0x52, 0xe8, 0x0f, 0x00, 0xb9, 0x03, 0x00, 0x00, 0x14,
                ],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: JOIN,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: STORE_ZERO,
                bytes: vec![0xff, 0x0f, 0x00, 0xb9, 0x01, 0x00, 0x00, 0x14],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: JOIN,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: JOIN,
                bytes: vec![
                    0xe0, 0x0f, 0x40, 0xb9, 0xff, 0x43, 0x00, 0x91, 0xc0, 0x03, 0x5f, 0xd6,
                ],
                successors: Vec::new(),
            },
        ]
    }

    fn trusted_native_span_fixture(
        bytes: &[u8],
        addr: u64,
    ) -> (TrustedSsaArtifact, r2il::R2ILBlock, LiftedBlockSpans) {
        trusted_x86_fixture(bytes, addr, false, false)
    }

    fn x86_o0_framed_private_join_blocks() -> Vec<NativeSpanBlockFixture> {
        const HEADER: u64 = 0x650;
        const STORE_ONE: u64 = 0x660;
        const STORE_ZERO: u64 = 0x669;
        const JOIN: u64 = 0x670;

        vec![
            NativeSpanBlockFixture {
                addr: HEADER,
                bytes: vec![
                    0x55, // push rbp
                    0x48, 0x89, 0xe5, // mov rbp, rsp
                    0x89, 0x7d, 0xf8, // mov dword [rbp-8], edi
                    0x81, 0x7d, 0xf8, 0xad, 0xde, 0x00, 0x00, // cmp dword [rbp-8], 0xdead
                    0x75, 0x09, // jne store-zero
                ],
                successors: vec![
                    NativeSpanSuccessorFixture {
                        kind: 0,
                        target: STORE_ZERO,
                        external: false,
                    },
                    NativeSpanSuccessorFixture {
                        kind: 1,
                        target: STORE_ONE,
                        external: false,
                    },
                ],
            },
            NativeSpanBlockFixture {
                addr: STORE_ONE,
                bytes: vec![
                    0xc7, 0x45, 0xfc, 0x01, 0x00, 0x00, 0x00, // mov dword [rbp-4], 1
                    0xeb, 0x07, // jmp join
                ],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: JOIN,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: STORE_ZERO,
                bytes: vec![
                    0xc7, 0x45, 0xfc, 0x00, 0x00, 0x00, 0x00, // mov dword [rbp-4], 0
                ],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 1,
                    target: JOIN,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: JOIN,
                bytes: vec![
                    0x8b, 0x45, 0xfc, // mov eax, dword [rbp-4]
                    0x5d, // pop rbp
                    0xc3, // ret
                ],
                successors: Vec::new(),
            },
        ]
    }

    fn conditional_private_join_blocks(
        addr: u64,
        zero_op_forwarder: bool,
    ) -> Vec<NativeSpanBlockFixture> {
        let header_addr = addr;
        let false_addr = header_addr + 17;
        let false_size = 10_u64;
        let forwarder_addr = false_addr + false_size;
        let forwarder_size = if zero_op_forwarder { 3_u64 } else { 2_u64 };
        let true_addr = forwarder_addr + forwarder_size;
        let true_size = 10_u64;
        let join_addr = true_addr + true_size;
        let rel8 = |instruction_end: u64, target: u64| {
            i8::try_from(
                i64::try_from(target).expect("target fits i64")
                    - i64::try_from(instruction_end).expect("instruction end fits i64"),
            )
            .expect("fixture branch fits rel8") as u8
        };

        let mut forwarder = Vec::with_capacity(usize::try_from(forwarder_size).unwrap());
        if zero_op_forwarder {
            forwarder.push(0x90);
        }
        forwarder.extend_from_slice(&[0xeb, rel8(true_addr, true_addr)]);

        vec![
            NativeSpanBlockFixture {
                addr: header_addr,
                bytes: vec![
                    0x48,
                    0x8d,
                    0x64,
                    0x24,
                    0xe0, // lea rsp, [rsp-32]
                    0x48,
                    0x89,
                    0x4c,
                    0x24,
                    0x08, // mov qword [rsp+8], rcx
                    0x48,
                    0x8b,
                    0x4c,
                    0x24,
                    0x08, // mov rcx, qword [rsp+8]
                    0xe3,
                    rel8(false_addr, forwarder_addr), // jrcxz forwarder
                ],
                successors: vec![
                    NativeSpanSuccessorFixture {
                        kind: 0,
                        target: forwarder_addr,
                        external: false,
                    },
                    NativeSpanSuccessorFixture {
                        kind: 1,
                        target: false_addr,
                        external: false,
                    },
                ],
            },
            NativeSpanBlockFixture {
                addr: false_addr,
                bytes: vec![
                    0xc7,
                    0x44,
                    0x24,
                    0x18,
                    0x00,
                    0x00,
                    0x00,
                    0x00, // mov dword [rsp+24], 0
                    0xeb,
                    rel8(forwarder_addr, join_addr), // jmp join
                ],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: join_addr,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: forwarder_addr,
                bytes: forwarder,
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: true_addr,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: true_addr,
                bytes: vec![
                    0xc7,
                    0x44,
                    0x24,
                    0x18,
                    0x01,
                    0x00,
                    0x00,
                    0x00, // mov dword [rsp+24], 1
                    0xeb,
                    rel8(join_addr, join_addr), // jmp join
                ],
                successors: vec![NativeSpanSuccessorFixture {
                    kind: 0,
                    target: join_addr,
                    external: false,
                }],
            },
            NativeSpanBlockFixture {
                addr: join_addr,
                bytes: vec![
                    0x8b, 0x44, 0x24, 0x18, // mov eax, dword [rsp+24]
                    0x48, 0x8d, 0x64, 0x24, 0x20, // lea rsp, [rsp+32]
                    0xc3, // ret
                ],
                successors: Vec::new(),
            },
        ]
    }

    fn assert_zero_op_native_spans_are_exactly_residual(
        trusted: &TrustedSsaArtifact,
        canonical: &r2il::R2ILBlock,
        expected_zero_span_count: usize,
    ) -> Vec<CanonicalInstructionId> {
        let source = &trusted.source_blocks()[0];
        assert_eq!(source.addr, canonical.addr);
        assert_eq!(source.size, canonical.size);
        assert_eq!(source.ops, canonical.ops);
        assert_eq!(source.op_metadata, canonical.op_metadata);

        let inventory = trusted.artifact().obligations();
        assert!(inventory.is_complete());
        let zero_spans = inventory
            .native_spans()
            .iter()
            .filter(|(_, span)| span.canonical_op_count() == 0)
            .collect::<Vec<_>>();
        assert_eq!(zero_spans.len(), expected_zero_span_count);

        let mut zero_ids = Vec::with_capacity(zero_spans.len());
        let mut zero_obligations = Vec::with_capacity(zero_spans.len());
        for (id, span) in zero_spans {
            assert_eq!(id.block_addr, source.addr);
            assert!(matches!(
                id.site,
                CanonicalInstructionSite::NativeSpan {
                    instruction_addr,
                    size,
                } if instruction_addr == span.instruction_addr() && size == span.size()
            ));
            let disposition = inventory
                .instructions()
                .get(id)
                .expect("zero-op span disposition");
            assert_eq!(
                disposition.state,
                SemanticInstructionState::UnsupportedUnknown
            );
            assert_eq!(disposition.source.native_span(), Some(*span));
            assert_eq!(disposition.source.graph_inst(), None);
            let obligation_id = r2ssa::SemanticObligationId {
                instruction: *id,
                kind: r2ssa::SemanticObligationKind::VolatileOrUnknownEffect,
                component: r2ssa::SemanticObligationComponent::Whole,
            };
            assert_eq!(
                disposition.obligations,
                BTreeSet::from([obligation_id]),
                "one exact Whole unknown obligation per zero-op span"
            );
            let obligation = inventory
                .obligations()
                .get(&obligation_id)
                .expect("zero-op span obligation");
            assert_eq!(obligation.source, disposition.source);
            assert!(obligation.inputs.is_empty());
            zero_ids.push(*id);
            zero_obligations.push(obligation_id);
        }

        let certified = CertifiedMachineProjection::from_artifact(trusted)
            .expect("fail-closed machine projection");
        for (id, obligation) in zero_ids.iter().zip(&zero_obligations) {
            assert!(certified.residual_producers().contains(id));
            assert_eq!(certified.ledger().effects(*obligation).len(), 1);
            assert!(matches!(
                certified.ledger().effects(*obligation)[0].disposition(),
                r2cert::EffectDisposition::Residualized { .. }
            ));
        }
        zero_ids
    }

    #[test]
    fn genuine_mixed_zero_op_spans_use_production_trusted_ssa_wiring() {
        const ADDR: u64 = 0x401000;
        let (trusted, canonical, spans) =
            trusted_native_span_fixture(&[0x90, 0x31, 0xc0, 0x90], ADDR);

        let canonical_op_count =
            u64::try_from(canonical.ops.len()).expect("canonical op count fits u64");
        assert!(!canonical.ops.is_empty());
        assert_eq!(
            spans,
            vec![
                (ADDR, 1, 0, 0),
                (ADDR + 1, 2, 0, canonical_op_count),
                (ADDR + 3, 1, canonical_op_count, 0),
            ]
        );
        assert_zero_op_native_spans_are_exactly_residual(&trusted, &canonical, 2);
    }

    #[test]
    fn genuine_trusted_ssa_shares_exact_artifact_ownership() {
        const ADDR: u64 = 0x401100;
        let (trusted, _, _) = trusted_native_span_fixture(&[0x31, 0xc0], ADDR);

        let shared = trusted.shared_artifact();
        let same_artifact = trusted.shared_artifact();
        assert!(trusted.shares_artifact(&shared));
        assert!(std::ptr::eq(trusted.artifact(), shared.as_ref()));
        assert!(std::sync::Arc::ptr_eq(&shared, &same_artifact));

        let weak = std::sync::Arc::downgrade(&shared);
        drop(same_artifact);
        drop(trusted);
        assert!(std::sync::Weak::upgrade(&weak).is_some());
        drop(shared);
        assert!(std::sync::Weak::upgrade(&weak).is_none());
    }

    #[test]
    fn genuine_all_zero_op_spans_residualize_and_refuse_differential_admission() {
        const ADDR: u64 = 0x402000;
        let (trusted, canonical, spans) = trusted_native_span_fixture(&[0x90, 0x90, 0x90], ADDR);

        assert!(canonical.ops.is_empty());
        assert!(canonical.op_metadata.is_empty());
        assert_eq!(
            spans,
            vec![(ADDR, 1, 0, 0), (ADDR + 1, 1, 0, 0), (ADDR + 2, 1, 0, 0)]
        );
        let zero_ids = assert_zero_op_native_spans_are_exactly_residual(&trusted, &canonical, 3);
        assert_eq!(zero_ids.len(), 3);

        let initial = DifferentialState::for_artifact(&trusted).expect("differential state");
        let report =
            check_block_differential(&trusted, ADDR, &initial, DifferentialLimits::default());
        assert_eq!(report.admission(), DifferentialCandidateAdmission::Residual);
        assert_eq!(report.conclusion(), DifferentialConclusion::Incomplete);
        assert!(matches!(
            report.disposition(),
            DifferentialCaseDisposition::CandidateNotAdmitted {
                admission: DifferentialCandidateAdmission::Residual,
                ..
            }
        ));
    }

    #[test]
    fn genuine_private_frame_flow_is_wired_through_both_public_certificates() {
        const ADDR: u64 = 0x403000;
        const VALID: &[u8] = &[
            0x48, 0x8d, 0x64, 0x24, 0xf0, // lea rsp, [rsp-16]
            0xc7, 0x44, 0x24, 0x08, 0x01, 0x00, 0x00, 0x00, // mov dword [rsp+8], 1
            0x8b, 0x44, 0x24, 0x08, // mov eax, dword [rsp+8]
            0x48, 0x8d, 0x64, 0x24, 0x10, // lea rsp, [rsp+16]
            0xc3, // ret
        ];
        const UNINITIALIZED_LOAD: &[u8] = &[
            0x48, 0x8d, 0x64, 0x24, 0xf0, // lea rsp, [rsp-16]
            0x8b, 0x44, 0x24, 0x08, // mov eax, dword [rsp+8]
            0xc7, 0x44, 0x24, 0x08, 0x01, 0x00, 0x00, 0x00, // mov dword [rsp+8], 1
            0x48, 0x8d, 0x64, 0x24, 0x10, // lea rsp, [rsp+16]
            0xc3, // ret
        ];

        let (trusted, _, _) = trusted_x86_fixture(VALID, ADDR, true, true);
        let full = CertifiedMachineFunction::from_artifact(&trusted)
            .expect("full genuine private-frame certificate");
        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("projected genuine private-frame certificate");
        assert!(full.stack_discipline().is_some());
        assert!(projection.stack_discipline().is_some());
        assert_eq!(full.private_frame_value_flows().len(), 1);
        assert_eq!(
            full.private_frame_value_flows(),
            projection.private_frame_value_flows()
        );
        assert_eq!(
            CertifiedPrivateFrameConditionalJoinRewrite::from_artifact(&trusted),
            Err(PrivateFrameConditionalJoinRewriteError::MissingExactJoin)
        );

        let (trusted, _, _) = trusted_x86_fixture(UNINITIALIZED_LOAD, ADDR + 0x100, true, true);
        let full = CertifiedMachineFunction::from_artifact(&trusted)
            .expect("full genuine uninitialized-load certificate");
        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("projected genuine uninitialized-load certificate");
        assert!(full.stack_discipline().is_some());
        assert!(projection.stack_discipline().is_some());
        assert!(full.private_frame_value_flows().is_empty());
        assert!(projection.private_frame_value_flows().is_empty());
    }

    #[test]
    fn genuine_x86_generic_renderer_uses_logical_parameter_and_graph_binding() {
        const ADDR: u64 = 0x403800;
        let (trusted, lifted, spans) = trusted_x86_blocks_fixture(
            vec![NativeSpanBlockFixture {
                addr: ADDR,
                bytes: vec![
                    0x48, 0x89, 0xc8, // mov rax, rcx
                    0xc3, // ret
                ],
                successors: Vec::new(),
            }],
            ADDR,
            true,
            Some("RCX"),
        );
        assert_eq!(lifted.len(), 1);
        assert_eq!(spans.len(), 1);

        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("genuine generic x86 projection");
        assert!(projection.private_frame_conditional_joins().is_empty());
        let function = CertifiedSemanticCFunction::from_artifact(&trusted)
            .expect("genuine generic x86 semantic-C function");
        let interface = function
            .region()
            .layer()
            .accounting()
            .expression_layer()
            .function_interface()
            .expect("genuine generic x86 function interface");
        let [parameter] = interface.parameters() else {
            panic!("one exact generic x86 parameter")
        };
        let binding = parameter
            .value()
            .expect("one exact generic x86 graph parameter binding");
        assert_eq!(parameter.storage().size.checked_mul(8), Some(64));
        assert_eq!(parameter.ty().width_bits(), 64);
        assert_eq!(
            parameter.projection().logical_ty(),
            Some(&MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            })
        );

        let rendered = function
            .render_certified_c()
            .expect("genuine generic x86 strict C rendering");
        assert!(rendered.contains("uint32_t certified_sub_403800(uint64_t arg_0)"));
        assert!(rendered.contains(&format!(
            "uint64_t {} = (uint64_t)(arg_0);",
            value_name(binding)
        )));
    }

    #[test]
    fn genuine_x86_o0_rbp_red_zone_join_closes_and_matches_machine_semantics() {
        const HEADER: u64 = 0x650;
        const STORE_ONE: u64 = 0x660;
        const STORE_ZERO: u64 = 0x669;
        const JOIN: u64 = 0x670;

        let (trusted, lifted, spans) = trusted_x86_blocks_fixture_with_interface(
            x86_o0_framed_private_join_blocks(),
            HEADER,
            X86InterfaceFixture {
                exact_private_stack: true,
                implicit_active_sp_bytes: 128,
                stacked_return: true,
                frame_pointer_register: Some("RBP"),
                parameter_register: Some("RDI"),
                parameter_logical_type_id: 0,
                parameter_carrier: RadareAbi138CarrierProjection {
                    kind: 2,
                    offset_bits: 0,
                    size_bits: 32,
                },
                scalar_return_register: Some("RAX"),
                types: vec![(1, 32)],
                return_type_id: 0,
                return_carrier: RadareAbi138CarrierProjection {
                    kind: 2,
                    offset_bits: 0,
                    size_bits: 32,
                },
            },
        );
        assert_eq!(lifted.len(), 4);
        assert_eq!(spans.len(), 4);
        assert!(spans.iter().flatten().all(|span| span.3 != 0));

        let source_interface = trusted
            .artifact()
            .machine_context()
            .function_interface()
            .expect("exact captured x86 function interface");
        let [source_parameter] = source_interface.parameters() else {
            panic!("one exact x86 parameter")
        };
        assert_eq!(source_parameter.storage().offset, 0x38);
        assert_eq!(source_parameter.storage().size, 8);
        let [logical_parameter] = source_interface.parameter_logical_values() else {
            panic!("one exact logical x86 parameter")
        };
        assert_eq!(logical_parameter.type_id(), 0);
        assert_eq!(
            logical_parameter.carrier().kind(),
            SourceCarrierKind::LowBits
        );
        assert_eq!(logical_parameter.carrier().offset_bits(), 0);
        assert_eq!(logical_parameter.carrier().size_bits(), 32);
        let type_graph = source_interface
            .type_graph()
            .expect("exact signed-i32 type graph");
        let [source_type] = type_graph.types() else {
            panic!("one exact source type")
        };
        assert_eq!(source_type.kind(), SourceTypeKind::SignedInteger);
        assert_eq!(source_type.size_bits(), 32);
        let SourceFunctionReturn::Register {
            storage: return_storage,
        } = source_interface.return_kind()
        else {
            panic!("exact RAX scalar return")
        };
        assert_eq!(return_storage.offset, 0);
        assert_eq!(return_storage.size, 8);
        let return_logical = source_interface
            .return_logical_value()
            .expect("exact signed-i32 return projection");
        assert_eq!(return_logical.type_id(), 0);
        assert_eq!(return_logical.carrier().kind(), SourceCarrierKind::LowBits);
        assert_eq!(return_logical.carrier().offset_bits(), 0);
        assert_eq!(return_logical.carrier().size_bits(), 32);
        let stack_pointer_storage = source_interface
            .stack_pointer_storage()
            .expect("exact RSP storage");
        assert_eq!(stack_pointer_storage.offset, 0x20);
        assert_eq!(stack_pointer_storage.size, 8);
        let frame_pointer_storage = source_interface
            .exact_frame_pointer_storage()
            .expect("exact RBP storage");
        assert_eq!(frame_pointer_storage.offset, 0x28);
        assert_eq!(frame_pointer_storage.size, 8);
        let return_address_storage = source_interface
            .return_address_storage()
            .expect("exact RIP storage");
        assert_eq!(return_address_storage.offset, 0x288);
        assert_eq!(return_address_storage.size, 8);
        let source_stack_contract = source_interface
            .stack_allocation_contract()
            .expect("exact lower-growing red-zone contract");
        assert_eq!(source_stack_contract.implicit_active_sp_bytes(), 128);
        assert!(source_interface.return_mechanism().is_some());
        let [parameter_home, result_local] = source_interface.stack_slots() else {
            panic!("exact parameter-home and result-local stack slots")
        };
        assert_eq!(parameter_home.base(), StackAddressBase::FramePointer);
        assert_eq!(parameter_home.base_storage(), frame_pointer_storage);
        assert_eq!(parameter_home.offset(), -8);
        assert_eq!(parameter_home.size_bytes(), 4);
        assert_eq!(
            parameter_home.role(),
            r2source::SourceStackSlotRole::ParameterHome {
                parameter_index: 0,
                home_storage: source_parameter.storage(),
            }
        );
        assert_eq!(result_local.base(), StackAddressBase::FramePointer);
        assert_eq!(result_local.base_storage(), frame_pointer_storage);
        assert_eq!(result_local.offset(), -4);
        assert_eq!(result_local.size_bytes(), 4);
        assert_eq!(result_local.role(), r2source::SourceStackSlotRole::Local);

        let prep = trusted
            .artifact()
            .function()
            .decompile_prep_facts()
            .expect("exact decompiler preparation facts");
        let source_roots = prep
            .stack_address_roots
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        let entry_roots = prep
            .entry_stack_address_roots
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        for offset in [-8, -4] {
            assert!(source_roots.contains(&StackAddressRoot {
                base: StackAddressBase::FramePointer,
                offset,
            }));
        }
        for offset in [-16, -12] {
            assert!(entry_roots.contains(&StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset,
            }));
        }

        let full = CertifiedMachineFunction::from_artifact(&trusted)
            .expect("full genuine framed x86 certificate");
        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("projected genuine framed x86 certificate");
        let frame = full
            .frame_preservation()
            .expect("exact x86 frame-pointer preservation");
        let certified_prep = full
            .origin()
            .decompile_preparation()
            .expect("certified preparation snapshot");
        assert!(!certified_prep.entry_stack_address_roots().is_empty());
        assert_eq!(frame.frame_pointer_storage(), frame_pointer_storage);
        assert_eq!(frame.saved_range().offset(), -8);
        assert_eq!(frame.saved_range().size_bytes(), 8);
        assert_eq!(frame.entry_save().producer().block_addr, HEADER);
        let [frame_restore] = frame.restores() else {
            panic!("one exact RBP restore")
        };
        assert_eq!(frame_restore.restore_read().producer().block_addr, JOIN);

        let stack = full
            .stack_discipline()
            .expect("exact x86 implicit private-stack discipline");
        assert_eq!(stack.reservation_range().offset(), -8);
        assert_eq!(stack.reservation_range().size_bytes(), 8);
        assert_eq!(stack.private_ownership_range().offset(), -136);
        assert_eq!(stack.private_ownership_range().size_bytes(), 136);
        assert_eq!(stack.implicit_active_sp_bytes(), 128);
        let [release] = stack.releases() else {
            panic!("one exact x86 stack release")
        };
        assert!(release.return_address_read().is_some());
        let mut private_ranges = stack
            .private_regions()
            .iter()
            .map(|region| region.accessed_range())
            .collect::<Vec<_>>();
        private_ranges.sort();
        assert_eq!(
            private_ranges
                .iter()
                .map(|range| (range.offset(), range.size_bytes()))
                .collect::<Vec<_>>(),
            [(-16, 4), (-12, 4)]
        );

        let mut flows = full
            .private_frame_value_flows()
            .values()
            .collect::<Vec<_>>();
        flows.sort_by_key(|flow| flow.range());
        let [parameter_flow, result_flow] = flows.as_slice() else {
            panic!("two exact x86 private-frame value flows")
        };
        assert_eq!(parameter_flow.range().offset(), -16);
        assert_eq!(parameter_flow.range().size_bytes(), 4);
        assert_eq!(parameter_flow.definitions().len(), 1);
        assert!(
            parameter_flow
                .definition(parameter_flow.root_version())
                .is_some_and(|definition| definition.store().is_some())
        );
        assert_eq!(result_flow.range().offset(), -12);
        assert_eq!(result_flow.range().size_bytes(), 4);
        assert_eq!(result_flow.definitions().len(), 3);
        assert!(
            result_flow
                .definition(result_flow.root_version())
                .is_some_and(|definition| {
                    definition
                        .phi()
                        .is_some_and(|phi| phi.block_addr() == JOIN && phi.inputs().len() == 2)
                })
        );
        assert_eq!(
            full.private_frame_value_flows(),
            projection.private_frame_value_flows()
        );

        assert_eq!(full.private_frame_conditional_joins().len(), 1);
        let certificate = full
            .private_frame_conditional_join(HEADER)
            .expect("header-keyed framed x86 conditional join");
        assert_eq!(certificate.header(), HEADER);
        assert_eq!(certificate.join_block(), JOIN);
        assert_eq!(certificate.condition().true_target(), STORE_ZERO);
        assert_eq!(certificate.condition().false_target(), STORE_ONE);
        assert_eq!(certificate.joined_flow().range().offset(), -12);
        assert_eq!(certificate.frame_preservation(), Some(frame));
        assert!(matches!(
            certificate.true_arm().join_transfer(),
            CertifiedPrivateFrameJoinTransfer::Fallthrough { block_addr, target }
                if *block_addr == STORE_ZERO && *target == JOIN
        ));
        assert!(matches!(
            certificate.false_arm().join_transfer(),
            CertifiedPrivateFrameJoinTransfer::Direct(control)
                if control.producer().block_addr == STORE_ONE && control.target() == JOIN
        ));
        assert_eq!(
            full.private_frame_conditional_joins(),
            projection.private_frame_conditional_joins()
        );

        let rewrite = CertifiedPrivateFrameConditionalJoinRewrite::from_artifact(&trusted)
            .expect("genuine framed x86 private-join rewrite");
        assert_eq!(rewrite.machine_join(), certificate);
        let function = CertifiedPrivateFrameConditionalJoinFunction::from_artifact(&trusted)
            .expect("closed genuine framed x86 semantic-C function");
        assert_eq!(function.rewrite(), &rewrite);
        assert!(function.audit().has_exact_private_frame_conditional_join());
        let rendered = function
            .render_certified_c()
            .expect("strict genuine framed x86 C");
        assert!(rendered.starts_with("#include <stdint.h>\n"));
        assert!(rendered.contains("int32_t certified_sub_650(int32_t arg_0)"));
        assert!(rendered.contains("UINT64_C(0xdead)"));
        assert!(rendered.contains("UINT64_C(0x1)"));
        assert!(rendered.contains("UINT64_C(0x0)"));
        assert!(!rendered.contains("memory"));
        assert!(!rendered.contains("stack"));
        assert!(!rendered.contains("local"));
        assert!(!rendered.contains('*'));

        let entry_sp = stack.entry_stack_pointer().binding();
        let entry_frame_pointer = match frame
            .entry_save_copies()
            .first()
            .and_then(|copy| full.projection().expr(copy.root()))
            .map(|expression| expression.kind())
        {
            Some(MachineExprKind::Copy { input }) => {
                match full
                    .projection()
                    .expr(*input)
                    .map(|expression| expression.kind())
                {
                    Some(MachineExprKind::Source { binding, .. }) => *binding,
                    _ => panic!("certified RBP save-copy input must be the entry source"),
                }
            }
            _ => panic!("certified RBP save must retain its entry copy"),
        };
        let parameter = full
            .abi_parameters()
            .get(&0)
            .and_then(|parameter| parameter.value())
            .expect("exact producerless RDI parameter");
        let seeded_byte = |byte_address: u64| ((byte_address as u8) ^ 0x5a).wrapping_add(1);
        let seeded_state = |input: u64| {
            let mut state = DifferentialState::for_artifact(&trusted).expect("genuine x86 state");
            for (binding, bits) in [
                (entry_sp, 0x8000),
                (entry_frame_pointer, 0x1234_5678_9abc_def0),
                (parameter.binding(), input),
            ] {
                assert!(
                    state
                        .set_value(
                            binding.value(),
                            DifferentialBitVector::new(binding.width_bits(), bits)
                                .expect("exact x86 boundary value"),
                        )
                        .is_none()
                );
            }
            for byte_address in 0x7ff0..0x8008 {
                assert!(
                    state
                        .set_memory_byte(
                            DifferentialMemoryLocation {
                                space: MachineAddressSpace::Ram,
                                byte_address,
                            },
                            seeded_byte(byte_address),
                        )
                        .is_none()
                );
            }
            state
        };
        let route_steps = |arm: &CertifiedPrivateFrameConditionalArm| {
            std::iter::once(certificate.header())
                .chain(arm.transparent().iter().map(|branch| branch.block_addr()))
                .chain([arm.store_block(), certificate.join_block()])
                .map(|addr| {
                    trusted
                        .artifact()
                        .graph()
                        .block_id_for_addr(addr)
                        .and_then(|id| trusted.artifact().graph().block(id))
                        .map(|block| block.insts.len())
                        .expect("sealed framed x86 route block")
                })
                .sum::<usize>()
        };
        let limits = DifferentialLimits {
            max_source_steps: u32::try_from(
                route_steps(certificate.true_arm()).max(route_steps(certificate.false_arm())),
            )
            .expect("framed x86 route steps fit u32"),
            max_expression_nodes: 256,
            max_memory_bytes: 64,
        };
        let mutation_state = seeded_state(0xdead);
        let (raw_source, selected_true) = execute_private_frame_join_source(
            trusted.artifact(),
            &projection,
            &function,
            &mutation_state,
            limits,
        );
        let raw_source = raw_source.expect("exact framed source run before normalization");
        let selected_true = selected_true.expect("exact framed source route");
        normalize_private_join_run(
            trusted.artifact(),
            &projection,
            &function,
            &mutation_state,
            selected_true,
            raw_source.clone(),
        )
        .expect("exact frame events normalize");
        let save_position = raw_source
            .memory_events
            .iter()
            .position(|event| event.access == frame.entry_save().access())
            .expect("exact frame save event");
        let restore_position = raw_source
            .memory_events
            .iter()
            .position(|event| event.access == frame_restore.restore_read().access())
            .expect("exact frame restore event");
        let normalization_refuses = |run| {
            matches!(
                normalize_private_join_run(
                    trusted.artifact(),
                    &projection,
                    &function,
                    &mutation_state,
                    selected_true,
                    run,
                ),
                Err(RunFailure::Invalid(_))
            )
        };

        let mut reversed = raw_source.clone();
        reversed.memory_events.swap(save_position, restore_position);
        assert!(normalization_refuses(reversed));

        let mut wrong_value = raw_source.clone();
        let restore_width = wrong_value.memory_events[restore_position]
            .value
            .width_bits();
        let restore_bits = wrong_value.memory_events[restore_position].value.bits() ^ 1;
        wrong_value.memory_events[restore_position].value =
            DifferentialBitVector::new(restore_width, restore_bits).expect("changed frame value");
        assert!(normalization_refuses(wrong_value));

        let mut missing = raw_source.clone();
        let mut events = missing.memory_events.into_vec();
        events.remove(restore_position);
        missing.memory_events = events.into_boxed_slice();
        assert!(normalization_refuses(missing));

        let mut duplicate = raw_source.clone();
        let mut events = duplicate.memory_events.into_vec();
        events.push(events[restore_position].clone());
        duplicate.memory_events = events.into_boxed_slice();
        assert!(normalization_refuses(duplicate));

        let entry_frame_value =
            private_frame_entry_value(trusted.artifact(), &projection, frame, &mutation_state)
                .expect("exact entry frame boundary value");
        let wrong_restored = DifferentialBitVector::new(
            entry_frame_value.width_bits(),
            entry_frame_value.bits() ^ 1,
        )
        .expect("changed restored frame value");
        assert!(
            validate_private_frame_restored_value(
                entry_frame_value,
                wrong_restored,
                frame_restore.restore_assignment().output().width_bits(),
            )
            .is_err()
        );

        for (input, expected) in [
            (0xdead, 1),
            (0, 0),
            (u64::MAX, 0),
            (0xaaaa_bbbb_0000_dead, 1),
        ] {
            let report = check_private_frame_conditional_join_differential(
                &trusted,
                &seeded_state(input),
                limits,
            );
            assert_eq!(
                report.conclusion(),
                DifferentialConclusion::NoMismatchObserved,
                "input={input:#x}: {:?}",
                report.disposition()
            );
            let DifferentialBoundaryOutcome::Returned { values } = &report
                .source()
                .expect("genuine framed x86 source run")
                .outcome
            else {
                panic!("genuine framed x86 join must return")
            };
            assert_eq!(
                values.as_ref(),
                [DifferentialBitVector::new(32, expected).unwrap()]
            );
            let expected_public_memory = (0x8000..0x8008)
                .map(|byte_address| DifferentialObservedByte {
                    location: DifferentialMemoryLocation {
                        space: MachineAddressSpace::Ram,
                        byte_address,
                    },
                    value: seeded_byte(byte_address),
                })
                .collect::<Vec<_>>();
            for run in [
                report.source().expect("genuine framed x86 source run"),
                report
                    .semantic_c()
                    .expect("genuine framed x86 semantic-C run"),
            ] {
                assert!(run.memory_events.is_empty());
                assert_eq!(run.final_memory.as_ref(), expected_public_memory.as_slice());
                assert!(
                    run.final_memory
                        .iter()
                        .all(|byte| { !(0x7ff0..0x8000).contains(&byte.location.byte_address) })
                );
            }
        }
    }

    #[test]
    fn genuine_aarch64_private_frame_join_matches_machine_polarity() {
        const BASE: u64 = 0x1_0000_0000;
        const HEADER: u64 = BASE + 0x598;
        const FORWARDER: u64 = BASE + 0x5b0;
        const STORE_ONE: u64 = BASE + 0x5b4;
        const STORE_ZERO: u64 = BASE + 0x5c0;
        const JOIN: u64 = BASE + 0x5c8;

        let source_blocks = aarch64_private_join_blocks();
        let (trusted, lifted, spans) = try_trusted_aarch64_blocks_fixture(source_blocks.clone())
            .unwrap_or_else(|error| {
                panic!("genuine AArch64 fixture failed: {error}; blocks={source_blocks:#x?}")
            });
        assert_eq!(lifted.len(), 5);
        assert_eq!(spans.len(), 5);
        assert!(spans.iter().flatten().all(|span| span.3 != 0));

        let full = CertifiedMachineFunction::from_artifact(&trusted)
            .expect("full genuine AArch64 private-frame certificate");
        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("projected genuine AArch64 private-frame certificate");
        let stack = projection
            .stack_discipline()
            .expect("AArch64 lower private stack discipline");
        assert_eq!(stack.reservation_range().offset(), -16);
        assert_eq!(stack.reservation_range().size_bytes(), 16);
        assert_eq!(stack.releases().len(), 1);
        let restoration = stack.releases()[0].restoration();
        assert_eq!(
            restoration.normalized_affine_relation().base_storage(),
            stack.stack_pointer_storage()
        );
        assert_eq!(restoration.normalized_affine_relation().offset_bytes(), 0);
        assert_eq!(
            restoration.normalized_affine_relation().width_bits(),
            stack.entry_stack_pointer().binding().width_bits()
        );
        assert!(stack.releases()[0].post_restoration().is_none());
        assert!(stack.releases()[0].return_address_read().is_none());
        let mut private_ranges = stack
            .private_regions()
            .iter()
            .map(|region| {
                (
                    region.accessed_range().offset(),
                    region.accessed_range().size_bytes(),
                )
            })
            .collect::<Vec<_>>();
        private_ranges.sort_unstable();
        assert_eq!(stack.private_regions().len(), 2);
        assert_eq!(private_ranges, vec![(-8, 4), (-4, 4)]);

        assert_eq!(full.private_frame_value_flows().len(), 2);
        assert_eq!(
            full.private_frame_value_flows(),
            projection.private_frame_value_flows()
        );
        let certificate = full
            .private_frame_conditional_join(HEADER)
            .expect("AArch64 header-keyed private-frame join");
        assert_eq!(full.private_frame_conditional_joins().len(), 1);
        assert_eq!(
            full.private_frame_conditional_joins(),
            projection.private_frame_conditional_joins()
        );
        assert_eq!(certificate.join_block(), JOIN);
        assert_eq!(certificate.condition().true_target(), STORE_ZERO);
        assert_eq!(certificate.condition().false_target(), FORWARDER);
        assert_eq!(certificate.true_arm().entry_target(), STORE_ZERO);
        assert!(certificate.true_arm().transparent().is_empty());
        assert_eq!(certificate.true_arm().store_block(), STORE_ZERO);
        assert_eq!(certificate.false_arm().entry_target(), FORWARDER);
        let [false_forwarder] = certificate.false_arm().transparent() else {
            panic!("one exact false-arm transparent branch")
        };
        assert_eq!(false_forwarder.block_addr(), FORWARDER);
        assert_eq!(certificate.false_arm().store_block(), STORE_ONE);
        assert_eq!(certificate.auxiliary_direct_flows().len(), 1);
        assert!(certificate.release().return_address_read().is_none());

        let rewrite = CertifiedPrivateFrameConditionalJoinRewrite::from_artifact(&trusted)
            .expect("genuine AArch64 private-frame rewrite plan");
        assert_eq!(rewrite.machine_join(), certificate);
        assert_eq!(rewrite.direct_substitutions().len(), 1);
        assert_eq!(rewrite.origin(), projection.origin());
        let function = CertifiedPrivateFrameConditionalJoinFunction::from_artifact(&trusted)
            .expect("genuine AArch64 typed private-frame function");
        assert_eq!(function.rewrite(), &rewrite);
        assert_eq!(function.accountings().len(), 5);
        let audit = function.audit();
        assert!(
            audit.has_exact_private_frame_conditional_join(),
            "{:?}",
            audit.invalid()
        );

        let semantic_parameter = rewrite
            .expression_layer()
            .function_interface()
            .and_then(|interface| interface.parameters().first())
            .expect("exact AArch64 x0 parameter");
        let parameter = semantic_parameter
            .value()
            .expect("exact AArch64 w0 parameter binding");
        let source_interface = trusted
            .artifact()
            .machine_context()
            .function_interface()
            .expect("exact AArch64 source interface");
        let source_parameter = source_interface
            .parameters()
            .first()
            .expect("exact AArch64 source x0 parameter");
        let source_logical = source_interface
            .parameter_logical_values()
            .first()
            .expect("exact AArch64 source logical parameter");
        let certified_parameter = projection
            .abi_parameters()
            .get(&0)
            .expect("exact certified AArch64 ABI parameter");
        assert_eq!(source_parameter.index(), 0);
        assert_eq!(source_parameter.storage(), semantic_parameter.storage());
        assert_eq!(certified_parameter.storage(), semantic_parameter.storage());
        assert_eq!(semantic_parameter.storage().size.checked_mul(8), Some(64));
        assert_eq!(
            certified_parameter.graph_storage().size.checked_mul(8),
            Some(32)
        );
        assert_eq!(
            certified_parameter.value().map(|value| value.binding()),
            Some(parameter)
        );
        assert_eq!(parameter.width_bits(), 32);
        assert_eq!(
            semantic_parameter.ty(),
            &MachineType::Integer {
                width_bits: 32,
                signedness: MachineSignedness::Unsigned,
            }
        );
        let logical_parameter_ty = semantic_parameter
            .projection()
            .logical_ty()
            .expect("signed scalar AArch64 logical parameter");
        assert_eq!(
            semantic_parameter.projection().source_type_id(),
            source_logical.type_id()
        );
        assert_eq!(logical_parameter_ty.width_bits(), 32);
        assert_eq!(
            logical_parameter_ty.signedness(),
            Some(MachineSignedness::Signed)
        );
        assert_eq!(
            semantic_parameter.projection().carrier().kind(),
            SourceCarrierKind::LowBits
        );
        assert_eq!(semantic_parameter.projection().carrier().offset_bits(), 0);
        assert_eq!(semantic_parameter.projection().carrier().size_bits(), 32);
        let [direct] = rewrite.direct_substitutions() else {
            panic!("one exact AArch64 auxiliary substitution")
        };
        assert_eq!(direct.replacement().value().binding(), parameter);
        assert!(matches!(
            direct.replacement().origin(),
            CertifiedPrivateFrameJoinValueOrigin::AbiParameter { index: 0, storage }
                if *storage == semantic_parameter.storage()
        ));
        let rendered = function
            .render_certified_c()
            .expect("genuine AArch64 strict C rendering");
        assert!(rendered.contains("int32_t certified_sub_100000598(int32_t arg_0)"));
        assert!(rendered.contains(&format!(
            "uint32_t {} = (uint32_t)(arg_0);",
            value_name(parameter)
        )));
        let entry_sp = stack.entry_stack_pointer().binding();
        assert_eq!(entry_sp.width_bits(), 64);
        let return_target = certificate.return_control().control_target().binding();
        let return_carrier = trusted
            .artifact()
            .graph()
            .def_inst(return_target.value())
            .and_then(|producer| trusted.artifact().graph().inst(producer))
            .and_then(|transport| match transport.inputs.as_slice() {
                [carrier] => Some(*carrier),
                _ => None,
            })
            .expect("one-hop exact x30 return carrier transport");
        let x30_storage = source_interface
            .return_address_storage()
            .expect("exact source x30 return-address storage");
        assert_eq!(x30_storage.size.checked_mul(8), Some(64));
        assert_eq!(
            trusted
                .artifact()
                .graph()
                .value(return_carrier)
                .and_then(|value| value.canonical_storage),
            Some(x30_storage)
        );
        let route_steps = |arm: &CertifiedPrivateFrameConditionalArm| {
            std::iter::once(certificate.header())
                .chain(arm.transparent().iter().map(|branch| branch.block_addr()))
                .chain([arm.store_block(), certificate.join_block()])
                .map(|addr| {
                    trusted
                        .artifact()
                        .graph()
                        .block_id_for_addr(addr)
                        .and_then(|id| trusted.artifact().graph().block(id))
                        .map(|block| block.insts.len())
                        .expect("sealed AArch64 route graph block")
                })
                .sum::<usize>()
        };
        let limits = DifferentialLimits {
            max_source_steps: u32::try_from(
                route_steps(certificate.true_arm()).max(route_steps(certificate.false_arm())),
            )
            .expect("AArch64 route steps fit u32"),
            max_expression_nodes: 256,
            max_memory_bytes: 32,
        };
        let seeded_state = |input: u64| {
            let mut state = DifferentialState::for_artifact(&trusted).expect("AArch64 state");
            assert!(
                state
                    .set_value(
                        entry_sp.value(),
                        DifferentialBitVector::new(entry_sp.width_bits(), 0x9000)
                            .expect("entry sp"),
                    )
                    .is_none()
            );
            assert!(
                state
                    .set_value(
                        parameter.value(),
                        DifferentialBitVector::new(parameter.width_bits(), input)
                            .expect("x0 input"),
                    )
                    .is_none()
            );
            assert!(
                state
                    .set_value(
                        return_carrier,
                        DifferentialBitVector::new(64, 0x1234_5678_9abc_def0)
                            .expect("x30 return carrier"),
                    )
                    .is_none()
            );
            for byte_address in 0x8ff8..0x9000 {
                assert!(
                    state
                        .set_memory_byte(
                            DifferentialMemoryLocation {
                                space: MachineAddressSpace::Ram,
                                byte_address,
                            },
                            0xa5,
                        )
                        .is_none()
                );
            }
            state
        };
        for (input, expected) in [(0xdead, 1), (0, 0), (0xdeac, 0), (0xffff_ffff, 0)] {
            let report = check_private_frame_conditional_join_differential(
                &trusted,
                &seeded_state(input),
                limits,
            );
            assert_eq!(
                report.conclusion(),
                DifferentialConclusion::NoMismatchObserved,
                "input={input:#x}: {:?}",
                report.disposition()
            );
            let DifferentialBoundaryOutcome::Returned { values } =
                &report.source().expect("AArch64 source run").outcome
            else {
                panic!("AArch64 private join must return")
            };
            assert_eq!(
                values.as_ref(),
                [DifferentialBitVector::new(32, expected).unwrap()]
            );
            assert!(report.source().unwrap().memory_events.is_empty());
            assert!(report.source().unwrap().final_memory.is_empty());
        }

        let mut wrong_successor_kind = aarch64_private_join_blocks();
        assert_eq!(wrong_successor_kind[2].addr, STORE_ONE);
        assert_eq!(wrong_successor_kind[2].successors[0].target, JOIN);
        wrong_successor_kind[2].successors[0].kind = 1;
        assert!(
            try_trusted_aarch64_blocks_fixture(wrong_successor_kind).is_err(),
            "a fallthrough advisory must not certify an encoded direct branch"
        );
    }

    #[test]
    fn genuine_private_frame_conditional_join_is_wired_through_public_certificates() {
        const ADDR: u64 = 0x404000;
        let source_blocks = conditional_private_join_blocks(ADDR, false);
        let header = source_blocks[0].addr;
        let join_addr = source_blocks[4].addr;
        let (trusted, lifted, spans) =
            trusted_x86_blocks_fixture(source_blocks, ADDR, true, Some("RCX"));
        assert_eq!(lifted.len(), 5);
        assert_eq!(spans.len(), 5);
        assert!(spans.iter().flatten().all(|span| span.3 != 0));

        let full = CertifiedMachineFunction::from_artifact(&trusted)
            .expect("full genuine conditional private-frame certificate");
        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("projected genuine conditional private-frame certificate");
        assert!(full.stack_discipline().is_some());
        assert!(projection.stack_discipline().is_some());
        assert_eq!(full.private_frame_value_flows().len(), 2);
        assert_eq!(
            full.private_frame_value_flows(),
            projection.private_frame_value_flows()
        );
        assert_eq!(full.private_frame_conditional_joins().len(), 1);
        assert_eq!(
            full.private_frame_conditional_joins(),
            projection.private_frame_conditional_joins()
        );
        let certificate = full
            .private_frame_conditional_join(header)
            .expect("header-keyed conditional join");
        assert_eq!(certificate.join_block(), join_addr);
        assert_eq!(certificate.true_arm().transparent().len(), 1);
        assert!(certificate.false_arm().transparent().is_empty());
        assert_eq!(certificate.auxiliary_direct_flows().len(), 1);
        assert!(certificate.release().return_address_read().is_some());
        let rewrite = CertifiedPrivateFrameConditionalJoinRewrite::from_artifact(&trusted)
            .expect("genuine private-frame conditional-join rewrite plan");
        assert_eq!(
            rewrite.schema_version(),
            CERTIFIED_PRIVATE_FRAME_JOIN_REWRITE_SCHEMA_VERSION
        );
        assert_eq!(
            rewrite.scope(),
            CertifiedPrivateFrameConditionalJoinRewriteScope::ProofBoundRewritePlanOnly
        );
        assert_eq!(rewrite.origin(), projection.origin());
        assert_eq!(rewrite.machine_join(), certificate);
        let [direct] = rewrite.direct_substitutions() else {
            panic!("one exact auxiliary direct substitution")
        };
        let [(auxiliary_access, auxiliary_flow)] = certificate.auxiliary_direct_flows() else {
            panic!("one exact auxiliary direct flow")
        };
        assert_eq!(direct.load_access(), *auxiliary_access);
        let auxiliary_load = match auxiliary_flow.load().statement().kind() {
            CertifiedMemoryStatementKind::Read { result } => result,
            CertifiedMemoryStatementKind::Write { .. } => panic!("auxiliary direct load"),
        };
        assert_eq!(direct.load_result(), auxiliary_load);
        assert!(matches!(
            rewrite.expression_layer().expr(direct.load_root()).map(|expression| expression.kind()),
            Some(SemanticCExprKind::MemoryRead { access, .. }) if *access == direct.load_access()
        ));
        let auxiliary_store = auxiliary_flow
            .definition(auxiliary_flow.root_version())
            .and_then(|definition| definition.store())
            .expect("auxiliary direct root store");
        let auxiliary_store_value = match auxiliary_store.statement().kind() {
            CertifiedMemoryStatementKind::Write { value } => value,
            CertifiedMemoryStatementKind::Read { .. } => panic!("auxiliary direct store"),
        };
        assert_eq!(direct.replacement().value(), auxiliary_store_value);
        assert!(matches!(
            direct.replacement().origin(),
            CertifiedPrivateFrameJoinValueOrigin::Produced { producer, root }
                if Some(*producer) == direct.replacement().value().producer()
                    && rewrite.expression_layer().expr(*root).is_some()
        ));
        let condition_accesses = private_frame_condition_accesses_for_test(&rewrite)
            .expect("exact expanded condition accesses");
        assert_eq!(condition_accesses, vec![direct.load_access()]);
        assert_ne!(direct.load_access(), rewrite.joined_select().load_access());
        assert!(!condition_accesses.contains(&rewrite.joined_select().load_access()));
        let reversed = [rewrite.joined_select().load_access(), direct.load_access()];
        let canonical = canonical_private_frame_accesses_for_test(reversed)
            .expect("canonical exact access order");
        let mut expected = reversed;
        expected.sort();
        assert_eq!(canonical, expected);
        assert!(canonical.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(
            canonical_private_frame_accesses_for_test(
                [direct.load_access(), direct.load_access(),]
            )
            .is_err()
        );
        assert!(!rewrite.open_obligations().is_empty());
        assert_eq!(
            rewrite.joined_select().load_access(),
            certificate.joined_flow().load().statement().access()
        );
        assert_eq!(
            rewrite.joined_select().truthiness(),
            certificate.condition().truthiness()
        );
        assert!(matches!(
            rewrite.joined_select().true_value().origin(),
            CertifiedPrivateFrameJoinValueOrigin::Produced { producer, .. }
                if Some(*producer) == rewrite.joined_select().true_value().value().producer()
        ));
        assert!(matches!(
            rewrite.joined_select().false_value().origin(),
            CertifiedPrivateFrameJoinValueOrigin::Produced { producer, .. }
                if Some(*producer) == rewrite.joined_select().false_value().value().producer()
        ));
        let true_store_value = match certificate.true_arm().store().statement().kind() {
            CertifiedMemoryStatementKind::Write { value } => value,
            CertifiedMemoryStatementKind::Read { .. } => panic!("conditional arm store"),
        };
        let false_store_value = match certificate.false_arm().store().statement().kind() {
            CertifiedMemoryStatementKind::Write { value } => value,
            CertifiedMemoryStatementKind::Read { .. } => panic!("conditional arm store"),
        };
        assert_eq!(
            rewrite.joined_select().true_value().value(),
            true_store_value
        );
        assert_eq!(
            rewrite.joined_select().false_value().value(),
            false_store_value
        );
        assert_eq!(
            rewrite.joined_select().true_value().value().ty(),
            rewrite.joined_select().load_result().ty()
        );
        assert_eq!(
            rewrite.joined_select().false_value().value().ty(),
            rewrite.joined_select().load_result().ty()
        );
        let interface = rewrite
            .expression_layer()
            .function_interface()
            .expect("exact scalar fixture interface");
        let return_projection = interface
            .return_projection()
            .expect("exact low-bits return projection");
        assert_eq!(return_projection.physical_ty().width_bits(), 64);
        assert_eq!(return_projection.logical_ty().width_bits(), 32);
        assert_eq!(
            rewrite
                .expression_layer()
                .expr(rewrite.joined_select().return_root())
                .expect("exact return DAG root")
                .ty()
                .width_bits(),
            64
        );
        assert_eq!(rewrite.joined_select().load_result().ty().width_bits(), 32);
        assert_eq!(
            rewrite.ledger_closure().region_kind(),
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction
        );
        assert_eq!(
            rewrite.ledger_closure().region_schema_version(),
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION
        );
        assert_eq!(rewrite.ledger_closure().origin(), rewrite.origin());

        let projected_join = projection
            .private_frame_conditional_join(header)
            .expect("projected header-keyed conditional join");
        let stack = projection
            .stack_discipline()
            .expect("projected private stack discipline");
        let private_stack_input = certified_private_entry_stack_pointer_input(
            &projection,
            Some(projected_join),
            Some(stack),
        )
        .expect("exact certified private entry stack pointer");
        assert_eq!(
            private_stack_input.classify(
                stack.entry_stack_pointer().binding(),
                stack.entry_stack_pointer().ty(),
            ),
            SemanticCInputOrigin::CertifiedPrivateEntryStackPointer {
                storage: stack.stack_pointer_storage(),
                header,
            }
        );
        assert_eq!(
            private_stack_input.classify(
                projected_join.condition().condition().binding(),
                stack.entry_stack_pointer().ty(),
            ),
            SemanticCInputOrigin::UnclassifiedSource
        );
        assert_eq!(
            certified_private_entry_stack_pointer_input(&projection, None, Some(stack),),
            Err(SemanticCError::InvalidCertifiedPrivateFrameInput)
        );
        assert_eq!(
            certified_private_entry_stack_pointer_input(&projection, Some(projected_join), None,),
            Err(SemanticCError::InvalidCertifiedPrivateFrameInput)
        );
        let projected_layer = SemanticCExpressionLayer::from_projection(&projection)
            .expect("exact stack discipline classifies the private entry stack pointer");
        assert_eq!(
            projected_layer
                .input_origins()
                .get(&stack.entry_stack_pointer().binding()),
            Some(&SemanticCInputOrigin::CertifiedPrivateEntryStackPointer {
                storage: stack.stack_pointer_storage(),
                header,
            })
        );
        match SemanticCExpressionLayer::from_private_frame_conditional_join(
            &projection,
            projected_join,
            stack,
        ) {
            Ok(_) => {}
            Err(SemanticCError::UnclassifiedSourceInput(value)) => {
                assert_ne!(value, stack.entry_stack_pointer().binding().value());
            }
            Err(error) => panic!("private entry-SP seam failed unexpectedly: {error}"),
        }

        let mappings = full
            .source()
            .obligations()
            .keys()
            .map(|obligation| {
                let [effect] = full.ledger().effects(*obligation) else {
                    panic!("one exact genuine ledger effect")
                };
                TypedRegionMapping::new(*obligation, effect.disposition().clone())
            })
            .collect::<Vec<_>>();
        let closure = certify_private_frame_conditional_join_region(
            trusted.artifact(),
            full.origin(),
            full.ledger(),
            mappings.clone(),
            certificate,
        )
        .expect("genuine private-frame conditional join ledger closure");
        assert_eq!(
            closure.region_kind(),
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction
        );
        assert_eq!(
            closure.region_schema_version(),
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION
        );
        assert!(closure.matches_ledger(
            full.origin(),
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
            &mappings,
        ));
        assert_eq!(rewrite.ledger_closure(), &closure);

        let function = CertifiedPrivateFrameConditionalJoinFunction::from_artifact(&trusted)
            .expect("genuine typed-output private-frame function");
        assert_eq!(
            function.schema_version(),
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_FUNCTION_SCHEMA_VERSION
        );
        assert_eq!(
            function.scope(),
            CertifiedPrivateFrameConditionalJoinFunctionScope::ClosedSourceAccountedPrivateFrameConditionalJoin
        );
        assert_eq!(function.origin(), projection.origin());
        assert_eq!(function.rewrite(), &rewrite);
        assert_eq!(function.accountings().len(), 5);
        assert!(
            function
                .accountings()
                .iter()
                .all(|accounting| accounting.audit().has_exact_source_accounting())
        );
        let function_audit = function.audit();
        assert!(
            function_audit.has_exact_private_frame_conditional_join(),
            "{:?}",
            function_audit.invalid()
        );
        assert_eq!(function.mappings().len(), full.source().obligations().len());
        assert!(
            function
                .mappings()
                .iter()
                .all(|mapping| mapping.owner().is_some())
        );
        let rendered = function
            .render_certified_c()
            .expect("strict typed private-frame conditional return C");
        assert!(rendered.starts_with("#include <stdint.h>\n"));
        assert!(rendered.contains("uint32_t certified_sub_404000(uint64_t"));
        assert!(rendered.contains(" != UINT64_C(0)) ?"));
        assert!(rendered.contains("UINT64_C(0x1)"));
        assert!(rendered.contains("UINT64_C(0x0)"));
        assert!(rendered.contains("return (uint32_t)("));
        assert!(!rendered.contains("*"));
        assert!(!rendered.contains("memory"));
        assert!(!rendered.contains("stack"));
        assert!(!rendered.contains("local"));
        assert_eq!(rendered.matches("return ").count(), 1);

        let entry_sp = stack.entry_stack_pointer().binding();
        let parameter = rewrite
            .expression_layer()
            .function_interface()
            .and_then(|interface| interface.parameters().first())
            .and_then(|parameter| parameter.value())
            .expect("exact RCX boundary binding");
        let seeded_state = |condition: u64, include_parameter: bool, include_memory: bool| {
            let mut state = DifferentialState::for_artifact(&trusted).expect("genuine state");
            assert!(
                state
                    .set_value(
                        entry_sp.value(),
                        DifferentialBitVector::new(entry_sp.width_bits(), 0x8000)
                            .expect("entry rsp"),
                    )
                    .is_none()
            );
            if include_parameter {
                assert!(
                    state
                        .set_value(
                            parameter.value(),
                            DifferentialBitVector::new(parameter.width_bits(), condition)
                                .expect("RCX condition"),
                        )
                        .is_none()
                );
            }
            if include_memory {
                for byte_address in 0x7fe0..0x8008 {
                    assert!(
                        state
                            .set_memory_byte(
                                DifferentialMemoryLocation {
                                    space: MachineAddressSpace::Ram,
                                    byte_address,
                                },
                                0,
                            )
                            .is_none()
                    );
                }
            }
            state
        };
        let route_steps = |arm: &CertifiedPrivateFrameConditionalArm| {
            std::iter::once(certificate.header())
                .chain(arm.transparent().iter().map(|branch| branch.block_addr()))
                .chain([arm.store_block(), certificate.join_block()])
                .map(|addr| {
                    trusted
                        .artifact()
                        .graph()
                        .block_id_for_addr(addr)
                        .and_then(|id| trusted.artifact().graph().block(id))
                        .map(|block| block.insts.len())
                        .expect("sealed route graph block")
                })
                .sum::<usize>()
        };
        let maximum_steps =
            route_steps(certificate.true_arm()).max(route_steps(certificate.false_arm()));
        let limits = DifferentialLimits {
            max_source_steps: u32::try_from(maximum_steps).expect("route steps fit u32"),
            max_expression_nodes: 256,
            max_memory_bytes: 64,
        };
        let mechanism = trusted
            .artifact()
            .machine_context()
            .function_interface()
            .and_then(|interface| interface.return_mechanism())
            .expect("exact stacked return mechanism");
        let entry_bits = DifferentialBitVector::new(64, 0x8000).unwrap();
        let physical_return = DifferentialBitVector::new(64, 0xffff_ffff_0000_0001).unwrap();
        assert_eq!(
            project_source_logical_return(trusted.artifact(), physical_return),
            Ok(DifferentialBitVector::new(32, 1).unwrap())
        );
        assert_eq!(
            project_semantic_logical_return(rewrite.expression_layer(), physical_return),
            Ok(DifferentialBitVector::new(32, 1).unwrap())
        );
        assert!(
            project_source_logical_return(
                trusted.artifact(),
                DifferentialBitVector::new(32, 1).unwrap(),
            )
            .is_err()
        );
        assert!(!exact_semantic_scalar_carrier_relation(
            SourceCarrierKind::Full,
            0,
            32,
            64,
            32,
        ));
        assert!(!exact_semantic_scalar_carrier_relation(
            SourceCarrierKind::LowBits,
            0,
            64,
            64,
            64,
        ));
        assert!(exact_semantic_scalar_carrier_relation(
            SourceCarrierKind::LowBits,
            0,
            32,
            64,
            32,
        ));
        assert!(exact_exit_stack_pointer(
            entry_bits,
            DifferentialBitVector::new(64, 0x8008).unwrap(),
            Some(mechanism.stack_pointer_delta_bytes()),
        ));
        assert!(!exact_exit_stack_pointer(
            entry_bits,
            DifferentialBitVector::new(64, 0x8000).unwrap(),
            Some(mechanism.stack_pointer_delta_bytes()),
        ));
        assert!(exact_exit_stack_pointer(entry_bits, entry_bits, None));
        let return_address_read = certificate
            .release()
            .return_address_read()
            .expect("stacked return-address read");
        let mut return_address_event = DifferentialMemoryEvent {
            producer: return_address_read.producer(),
            access: return_address_read.access(),
            object: return_address_read.object(),
            kind: DifferentialMemoryEventKind::Read,
            space: return_address_read.space(),
            byte_address: 0x8000,
            width_bits: return_address_read.width_bits(),
            endianness: return_address_read.endianness(),
            value: DifferentialBitVector::new(return_address_read.width_bits(), 0).unwrap(),
        };
        assert!(exact_return_address_event(
            &return_address_event,
            return_address_read,
            entry_bits,
            mechanism.stack_offset(),
            mechanism.slot_size_bytes(),
        ));
        return_address_event.byte_address = return_address_event.byte_address.wrapping_add(1);
        assert!(!exact_return_address_event(
            &return_address_event,
            return_address_read,
            entry_bits,
            mechanism.stack_offset(),
            mechanism.slot_size_bytes(),
        ));
        assert_eq!(
            modular_stack_offset(DifferentialBitVector::new(64, 4).unwrap(), -8),
            u64::MAX - 3,
        );

        let mut foreign_local_seed = seeded_state(0, true, true);
        assert!(
            trusted
                .artifact()
                .graph()
                .def_inst(false_store_value.binding().value())
                .is_some()
        );
        assert!(
            foreign_local_seed
                .set_value(
                    false_store_value.binding().value(),
                    DifferentialBitVector::new(false_store_value.binding().width_bits(), 0)
                        .expect("unselected arm value"),
                )
                .is_none()
        );
        let foreign_local = check_private_frame_conditional_join_differential(
            &trusted,
            &foreign_local_seed,
            limits,
        );
        assert_eq!(
            foreign_local.conclusion(),
            DifferentialConclusion::InvalidInput
        );
        assert!(matches!(
            foreign_local.disposition(),
            DifferentialCaseDisposition::InvalidInput { reason }
                if reason.contains("function-local producer")
        ));
        for (condition, expected) in [(0, 1), (1, 0), (u64::MAX, 0)] {
            let report = check_private_frame_conditional_join_differential(
                &trusted,
                &seeded_state(condition, true, true),
                limits,
            );
            assert_eq!(
                report.conclusion(),
                DifferentialConclusion::NoMismatchObserved
            );
            assert_eq!(report.disposition(), &DifferentialCaseDisposition::Matched);
            assert_eq!(
                report
                    .candidate_identity()
                    .expect("private join candidate identity")
                    .candidate_kind(),
                DifferentialCandidateKind::PrivateFrameConditionalJoinFunction
            );
            let DifferentialBoundaryOutcome::Returned { values } =
                &report.source().expect("source run").outcome
            else {
                panic!("source private join must return")
            };
            assert_eq!(
                values.as_ref(),
                [DifferentialBitVector::new(32, expected).unwrap()]
            );
            assert!(report.source().unwrap().memory_events.is_empty());
            assert_eq!(report.source().unwrap().final_memory.len(), 28);
        }

        let missing_input = check_private_frame_conditional_join_differential(
            &trusted,
            &seeded_state(0, false, true),
            limits,
        );
        assert_eq!(
            missing_input.conclusion(),
            DifferentialConclusion::Incomplete
        );
        assert!(matches!(
            missing_input.disposition(),
            DifferentialCaseDisposition::MissingBoundaryInput { value, .. }
                if *value == parameter.value()
        ));
        let missing_memory = check_private_frame_conditional_join_differential(
            &trusted,
            &seeded_state(0, true, false),
            limits,
        );
        assert_eq!(
            missing_memory.conclusion(),
            DifferentialConclusion::Incomplete
        );
        assert!(matches!(
            missing_memory.disposition(),
            DifferentialCaseDisposition::MemoryOutOfDomain { .. }
        ));
        let budget_boundary = check_private_frame_conditional_join_differential(
            &trusted,
            &seeded_state(0, true, true),
            DifferentialLimits {
                max_source_steps: u32::try_from(route_steps(certificate.true_arm()))
                    .expect("route steps fit u32"),
                ..limits
            },
        );
        assert_eq!(
            budget_boundary.conclusion(),
            DifferentialConclusion::NoMismatchObserved
        );
        let budget_short = check_private_frame_conditional_join_differential(
            &trusted,
            &seeded_state(0, true, true),
            DifferentialLimits {
                max_source_steps: u32::try_from(route_steps(certificate.true_arm()) - 1)
                    .expect("route steps fit u32"),
                ..limits
            },
        );
        assert_eq!(
            budget_short.conclusion(),
            DifferentialConclusion::Incomplete
        );
        assert!(matches!(
            budget_short.disposition(),
            DifferentialCaseDisposition::BudgetExceeded {
                side: DifferentialSide::SourceSsa
            }
        ));

        let foreign_blocks = conditional_private_join_blocks(ADDR + 0x200, false);
        let foreign_header = foreign_blocks[0].addr;
        let (foreign_trusted, _, _) =
            trusted_x86_blocks_fixture(foreign_blocks, ADDR + 0x200, true, Some("RCX"));
        let foreign_full = CertifiedMachineFunction::from_artifact(&foreign_trusted)
            .expect("foreign genuine conditional private-frame certificate");
        let foreign_projection = CertifiedMachineProjection::from_artifact(&foreign_trusted)
            .expect("foreign genuine conditional private-frame projection");
        let foreign_join = foreign_full
            .private_frame_conditional_join(foreign_header)
            .expect("foreign sealed conditional join");
        let foreign_stack = foreign_projection
            .stack_discipline()
            .expect("foreign private stack discipline");
        assert_eq!(
            certified_private_entry_stack_pointer_input(
                &projection,
                Some(foreign_join),
                Some(stack),
            ),
            Err(SemanticCError::InvalidCertifiedPrivateFrameInput)
        );
        assert_eq!(
            certified_private_entry_stack_pointer_input(
                &projection,
                Some(projected_join),
                Some(foreign_stack),
            ),
            Err(SemanticCError::InvalidCertifiedPrivateFrameInput)
        );
        assert!(
            SemanticCExpressionLayer::from_private_frame_conditional_join(
                &projection,
                foreign_join,
                stack,
            )
            .is_err()
        );
        assert!(
            certified_private_frame_join_rewrite_from_parts_for_test(
                &trusted,
                &projection,
                foreign_join,
                stack,
            )
            .is_err()
        );
        assert!(
            certified_private_frame_join_rewrite_from_parts_for_test(
                &trusted,
                &projection,
                projected_join,
                foreign_stack,
            )
            .is_err()
        );
        assert_eq!(
            certify_private_frame_conditional_join_region(
                foreign_trusted.artifact(),
                full.origin(),
                full.ledger(),
                mappings.clone(),
                certificate,
            ),
            Err(LedgerClosureError::InvalidOrigin)
        );
        assert_eq!(
            certify_private_frame_conditional_join_region(
                trusted.artifact(),
                full.origin(),
                full.ledger(),
                mappings,
                foreign_join,
            ),
            Err(LedgerClosureError::InvalidRegionTopology)
        );

        let source_blocks = conditional_private_join_blocks(ADDR + 0x100, true);
        let (trusted, lifted, spans) =
            trusted_x86_blocks_fixture(source_blocks, ADDR + 0x100, true, Some("RCX"));
        assert_eq!(lifted.len(), 5);
        let zero_spans = spans
            .iter()
            .flatten()
            .filter(|span| span.3 == 0)
            .collect::<Vec<_>>();
        assert_eq!(zero_spans.len(), 1);
        let unsupported = trusted
            .artifact()
            .obligations()
            .instructions()
            .values()
            .filter(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
            .map(|instruction| instruction.id)
            .collect::<Vec<_>>();
        assert_eq!(unsupported.len(), 1);

        let full = CertifiedMachineFunction::from_artifact(&trusted)
            .expect("full genuine zero-op-span certificate");
        let projection = CertifiedMachineProjection::from_artifact(&trusted)
            .expect("projected genuine zero-op-span certificate");
        assert_eq!(full.topology(), projection.topology());
        assert_eq!(full.topology().blocks().len(), 5);
        assert!(full.stack_discipline().is_none());
        assert!(projection.stack_discipline().is_none());
        assert!(full.private_frame_conditional_joins().is_empty());
        assert!(projection.private_frame_conditional_joins().is_empty());
        assert!(projection.residual_producers().contains(&unsupported[0]));
        assert!(matches!(
            CertifiedPrivateFrameConditionalJoinRewrite::from_artifact(&trusted),
            Err(PrivateFrameConditionalJoinRewriteError::MissingExactJoin)
                | Err(PrivateFrameConditionalJoinRewriteError::MissingStackDiscipline)
        ));
        assert!(CertifiedPrivateFrameConditionalJoinFunction::from_artifact(&trusted).is_err());
        let refused_state = DifferentialState::for_artifact(&trusted).expect("zero-span state");
        let refused = check_private_frame_conditional_join_differential(
            &trusted,
            &refused_state,
            DifferentialLimits::default(),
        );
        assert_eq!(
            refused.admission(),
            DifferentialCandidateAdmission::Residual
        );
    }

    #[test]
    fn rendered_conditional_oracle_observes_polarity_and_arm_order() {
        let state = ExecutionState {
            values: BTreeMap::from([
                (
                    ValueId(0),
                    DifferentialBitVector::new(8, 1).expect("predicate"),
                ),
                (
                    ValueId(1),
                    DifferentialBitVector::new(64, 0x11).expect("true value"),
                ),
                (
                    ValueId(2),
                    DifferentialBitVector::new(64, 0x22).expect("false value"),
                ),
            ]),
            memory: BTreeMap::new(),
            events: Vec::new(),
        };
        let ordinary = concat!(
            "strict(void) {\n",
            "\tif ((uint8_t)(v_0) != UINT8_C(0)) {\n",
            "\t\treturn v_1;\n",
            "\t} else {\n",
            "\t\treturn v_2;\n",
            "\t}\n",
            "}\n",
        );
        assert_eq!(
            parse_rendered_conditional_return(ordinary, &state).expect("ordinary"),
            (true, RenderedConditionalReturn::Value(ValueId(1)))
        );

        let reversed = ordinary.replace(" != UINT8_C(0)", " == UINT8_C(0)");
        assert_eq!(
            parse_rendered_conditional_return(&reversed, &state).expect("reversed"),
            (false, RenderedConditionalReturn::Value(ValueId(2)))
        );

        let swapped = ordinary
            .replace("return v_1", "return v_swap")
            .replace("return v_2", "return v_1")
            .replace("return v_swap", "return v_2");
        assert_eq!(
            parse_rendered_conditional_return(&swapped, &state).expect("swapped"),
            (true, RenderedConditionalReturn::Value(ValueId(2)))
        );
    }

    #[test]
    fn independent_kernels_have_absolute_known_answers() {
        let negative = DifferentialBitVector {
            width_bits: 8,
            bits: 0x80,
        };
        assert_eq!(
            source_bitvector(8, 0x1ff).expect("source mask").bits(),
            0xff
        );
        assert_eq!(
            semantic_bitvector(8, 0x1ff).expect("semantic mask").bits(),
            0xff
        );
        assert_eq!(
            source_sign_extend(negative, 16)
                .expect("source sign extension")
                .bits(),
            0xff80
        );
        assert_eq!(
            semantic_sign_extend(negative, 16)
                .expect("semantic sign extension")
                .bits(),
            0xff80
        );
        for shift in [1, 8, u64::MAX] {
            let expected = if shift == 1 { 0xc0 } else { 0xff };
            assert_eq!(
                source_shift_value(MachineShiftKind::ArithmeticRight, negative, shift)
                    .expect("source arithmetic shift")
                    .bits(),
                expected
            );
            assert_eq!(
                semantic_shift_value(MachineShiftKind::ArithmeticRight, negative, shift)
                    .expect("semantic arithmetic shift")
                    .bits(),
                expected
            );
        }

        let mut memory = BTreeMap::new();
        for (offset, byte) in [0x11, 0x22, 0x33, 0x44].into_iter().enumerate() {
            memory.insert(
                DifferentialMemoryLocation {
                    space: MachineAddressSpace::Ram,
                    byte_address: 0x20 + offset as u64,
                },
                byte,
            );
        }
        for (endianness, expected) in [
            (MachineMemoryEndianness::Little, 0x4433_2211),
            (MachineMemoryEndianness::Big, 0x1122_3344),
        ] {
            assert_eq!(
                source_read_memory(&memory, MachineAddressSpace::Ram, 0x20, 64, 32, endianness,)
                    .expect("source read")
                    .bits(),
                expected
            );
            assert_eq!(
                semantic_read_memory(&memory, MachineAddressSpace::Ram, 0x20, 64, 32, endianness,)
                    .expect("semantic read")
                    .bits(),
                expected
            );
        }
    }

    #[test]
    fn ordered_event_and_final_memory_mutations_are_detected() {
        let location = DifferentialMemoryLocation {
            space: MachineAddressSpace::Ram,
            byte_address: 0x40,
        };
        let event = DifferentialMemoryEvent {
            producer: CanonicalInstructionId {
                block_addr: 0x7300,
                site: r2ssa::CanonicalInstructionSite::Op(0),
            },
            access: StructuredAccessId {
                inst: r2ssa::InstId(0),
                ordinal: 0,
            },
            object: ObjectId(0),
            kind: DifferentialMemoryEventKind::Read,
            space: MachineAddressSpace::Ram,
            byte_address: 0x40,
            width_bits: 8,
            endianness: MachineMemoryEndianness::Little,
            value: DifferentialBitVector::new(8, 1).expect("byte"),
        };
        let mut write = event.clone();
        write.kind = DifferentialMemoryEventKind::Write;
        write.byte_address = 0x41;
        let run = DifferentialObservedRun {
            outcome: DifferentialBoundaryOutcome::OpenBlockExit { block_addr: 0x7300 },
            outputs: Box::new([]),
            memory_events: vec![event.clone(), write].into_boxed_slice(),
            final_memory: vec![DifferentialObservedByte { location, value: 1 }].into_boxed_slice(),
        };
        let mut reordered = run.clone();
        reordered.memory_events.swap(0, 1);
        assert_eq!(
            first_difference(&run, &reordered).map(|difference| difference.kind),
            Some(DifferentialMismatchKind::MemoryEventSequence)
        );
        let mut deleted = run.clone();
        deleted.memory_events = vec![event.clone()].into_boxed_slice();
        assert_eq!(
            first_difference(&run, &deleted).map(|difference| difference.kind),
            Some(DifferentialMismatchKind::MemoryEventSequence)
        );
        let mut duplicated = run.clone();
        duplicated.memory_events =
            vec![event.clone(), event, duplicated.memory_events[1].clone()].into_boxed_slice();
        assert_eq!(
            first_difference(&run, &duplicated).map(|difference| difference.kind),
            Some(DifferentialMismatchKind::MemoryEventSequence)
        );
        let mut memory = run.clone();
        memory.final_memory[0].value = 2;
        assert_eq!(
            first_difference(&run, &memory).map(|difference| difference.kind),
            Some(DifferentialMismatchKind::FinalMemory)
        );
    }

    #[test]
    fn high_bit_wire_values_never_use_json_numbers() {
        #[derive(Serialize)]
        struct InstructionRecord {
            #[serde(serialize_with = "serialize_canonical_instruction_id")]
            instruction: CanonicalInstructionId,
        }
        #[derive(Serialize)]
        struct TypeRecord {
            #[serde(serialize_with = "serialize_machine_type")]
            ty: MachineType,
        }
        let bitvector = serde_json::to_value(
            DifferentialBitVector::new(8, u64::MAX).expect("masked bitvector"),
        )
        .expect("bitvector JSON");
        assert_eq!(bitvector["bits_hex"], "0x00000000000000ff");
        let location = serde_json::to_value(DifferentialMemoryLocation {
            space: MachineAddressSpace::Ram,
            byte_address: u64::MAX,
        })
        .expect("location JSON");
        assert_eq!(location["byte_address_hex"], "0xffffffffffffffff");
        let instruction = serde_json::to_value(InstructionRecord {
            instruction: CanonicalInstructionId {
                block_addr: u64::MAX,
                site: CanonicalInstructionSite::Phi(r2ssa::CanonicalStorageId {
                    space: CanonicalStorageSpace::Custom(7),
                    offset: u64::MAX,
                    size: 8,
                }),
            },
        })
        .expect("instruction JSON");
        assert_eq!(
            instruction["instruction"]["block_addr_hex"],
            "0xffffffffffffffff"
        );
        assert_eq!(
            instruction["instruction"]["site"]["offset_hex"],
            "0xffffffffffffffff"
        );

        let global = serde_json::to_value(TypeRecord {
            ty: MachineType::Address {
                width_bits: 64,
                space: MachineAddressSpace::Ram,
                provenance: MachineAddressProvenance::Global { address: u64::MAX },
            },
        })
        .expect("global type JSON");
        assert_eq!(
            global["ty"]["provenance"]["address_hex"],
            "0xffffffffffffffff"
        );
        let stack = serde_json::to_value(TypeRecord {
            ty: MachineType::Address {
                width_bits: 64,
                space: MachineAddressSpace::Ram,
                provenance: MachineAddressProvenance::Stack {
                    base: MachineStackBase::StackPointer,
                    offset: i64::MIN,
                },
            },
        })
        .expect("stack type JSON");
        assert_eq!(stack["ty"]["provenance"]["offset"], i64::MIN.to_string());
    }

    #[test]
    fn native_span_instruction_identity_has_exact_json_coordinates() {
        #[derive(Serialize)]
        struct InstructionRecord {
            #[serde(serialize_with = "serialize_canonical_instruction_id")]
            instruction: CanonicalInstructionId,
        }

        let encoded = serde_json::to_value(InstructionRecord {
            instruction: CanonicalInstructionId {
                block_addr: 0x401000,
                site: CanonicalInstructionSite::NativeSpan {
                    instruction_addr: 0x401003,
                    size: 2,
                },
            },
        })
        .expect("native span JSON");

        assert_eq!(
            encoded,
            serde_json::json!({
                "instruction": {
                    "block_addr_hex": "0x0000000000401000",
                    "site": {
                        "kind": "native_span",
                        "instruction_addr_hex": "0x0000000000401003",
                        "size_bytes": 2,
                    },
                },
            })
        );
        assert_eq!(SEMANTIC_DIFFERENTIAL_SCHEMA_VERSION, 8);
        assert_eq!(SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION, 8);
    }
}
