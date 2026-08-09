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
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedMachineProjection,
    CertifiedMemoryExecutionPolicy, CertifiedMemoryStatementKind,
};
use r2ssa::{
    BlockTerminator, CallBoundarySlot, CallSiteId, CanonicalInstructionId,
    CanonicalInstructionSite, CanonicalStorageSpace, InstPayload, MachineAddressProvenance,
    MachineAddressSpace, MachineArithmeticFlagOp, MachineArithmeticMode, MachineArithmeticOp,
    MachineBitwiseOp, MachineBooleanOp, MachineCastKind, MachineComparisonOp, MachineExprId,
    MachineExprKind, MachineMemoryEndianness, MachineOvershiftBehavior, MachineShiftKind,
    MachineSignedness, MachineStackBase, MachineType, MachineValueBinding, MachineValueUse,
    ObjectId, SSAOp, SemanticInstructionState, SourceCallResult, SourceCallSiteIdentity,
    SourceFunctionReturn, SsaArtifact, StructuredAccessId, TrustedSsaArtifact, ValueId,
};
use serde::ser::{SerializeSeq, SerializeStruct};
use serde::{Serialize, Serializer};

use crate::certified_call::CertifiedDirectCallBlockRegion;
use crate::certified_if_return::{
    CertifiedConditionalReturnArm, CertifiedConditionalReturnFunction,
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

pub const SEMANTIC_DIFFERENTIAL_SCHEMA_VERSION: u32 = 6;
pub const SEMANTIC_DIFFERENTIAL_EVALUATOR_CONTRACT_VERSION: u32 = 6;

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
    let region = match CertifiedTerminalReturnBlockRegion::from_accounting(accounting) {
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
            },
            SemanticCExprKind::Input {
                binding: semantic_binding,
            },
        ) if machine_binding == semantic_binding => {
            let source_is_produced = machine.entity_for_output(machine_binding.value()).is_some();
            let semantic_input_type = semantic.inputs().get(semantic_binding);
            if (source_is_produced && semantic_input_type.is_some())
                || (!source_is_produced && semantic_input_type != Some(machine_expr.ty()))
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
    let (address, value, width_bits, source_space) =
        match (&graph_inst.payload, prepared_op) {
            (
                InstPayload::Op(SSAOp::Load { dst, addr, .. }),
                SSAOp::Load {
                    dst: prepared_dst,
                    addr: prepared_addr,
                    ..
                },
            ) if !is_write && dst == prepared_dst && addr == prepared_addr => (
                artifact.graph().value_id_for_var(addr).ok_or_else(|| {
                    RunFailure::Invalid("SSA load address is missing".to_string())
                })?,
                artifact.graph().value_id_for_var(dst),
                dst.size
                    .checked_mul(8)
                    .ok_or_else(|| RunFailure::Invalid("load width overflow".to_string()))?,
                source_space,
            ),
            (
                InstPayload::Op(SSAOp::Store { addr, val, .. }),
                SSAOp::Store {
                    addr: prepared_addr,
                    val: prepared_value,
                    ..
                },
            ) if is_write && addr == prepared_addr && val == prepared_value => (
                artifact.graph().value_id_for_var(addr).ok_or_else(|| {
                    RunFailure::Invalid("SSA store address is missing".to_string())
                })?,
                Some(artifact.graph().value_id_for_var(val).ok_or_else(|| {
                    RunFailure::Invalid("SSA store value is missing".to_string())
                })?),
                val.size
                    .checked_mul(8)
                    .ok_or_else(|| RunFailure::Invalid("store width overflow".to_string()))?,
                source_space,
            ),
            _ => {
                return Err(RunFailure::Invalid(
                    "graph memory operation differs from prepared SSA".to_string(),
                ));
            }
        };
    let id = StructuredAccessId { inst, ordinal: 0 };
    let object = artifact
        .objects()
        .object_for_value(address)
        .ok_or_else(|| RunFailure::Unsupported("memory object is unresolved".to_string()))?;
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
    if statement.execution() != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrderViaHelper {
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
                semantic_binding_value(self.artifact, self.block_addr, self.state, *binding)?
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
                let address = self.eval(*address)?;
                let cached = self.reads.get(access).ok_or_else(|| {
                    RunFailure::Invalid(
                        "memory-read expression has no exactly-once statement event".to_string(),
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
}
