//! Proof-preserving strict-C rendering for the sealed x86-64 `DemoStruct`
//! array update.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedStructArrayIndexAccessKind, CertifiedStructArrayIndexDispositionClass,
    CertifiedStructArrayIndexFunction, CertifiedStructArrayIndexLowering,
    CertifiedStructArrayIndexParameter, certify_struct_array_index_function,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace, InstPayload,
    MachineBuildError, SSAOp, SemanticObligationId, SsaArtifact, ValueId,
};
use serde::Serialize;

pub const CERTIFIED_STRUCT_ARRAY_INDEX_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION;

const MEMBER_COUNT: usize = 14;
const STORED_MEMBER: u32 = 2;
const LOADED_MEMBER: u32 = 13;
const STRIDE_BYTES: u64 = 56;
const MEMBER_BYTES: u32 = 4;
const MAX_DIFFERENTIAL_CASES: usize = 512;
const MAX_ABS_INDEX: i32 = 32;
const ARRAY_BASE: u64 = 0x40_0000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum StructArrayIndexSemanticCFunctionScope {
    ClosedOneBlockX86_64StructArrayIndex,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexAbiManifest {
    revision_identity: Box<[u8]>,
    parameters: Box<[CertifiedStructArrayIndexParameter]>,
    return_storage: CanonicalStorageId,
}

impl StructArrayIndexAbiManifest {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameters(&self) -> &[CertifiedStructArrayIndexParameter] {
        &self.parameters
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum StructArrayIndexRenderPhaseKind {
    StoreMember2,
    ReadMember2AfterStore,
    ReadMember13ForCarry,
    ReadMember13ForOverflow,
    ReadMember13ForAdd,
    Wrap32Add,
}

/// One source-ordered renderer phase. `access_index == None` is admitted only
/// for the O2 forwarded read of the just-written member; it is not invented as
/// a machine memory event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexRenderPhase {
    kind: StructArrayIndexRenderPhaseKind,
    producer: CanonicalInstructionId,
    value: ValueId,
    access_index: Option<u32>,
}

impl StructArrayIndexRenderPhase {
    pub const fn kind(&self) -> StructArrayIndexRenderPhaseKind {
        self.kind
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn access_index(&self) -> Option<u32> {
        self.access_index
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexRenderProgram {
    lowering: CertifiedStructArrayIndexLowering,
    stride_bytes: u64,
    member_offsets_bytes: Box<[u64]>,
    phases: Box<[StructArrayIndexRenderPhase]>,
}

impl StructArrayIndexRenderProgram {
    pub const fn lowering(&self) -> CertifiedStructArrayIndexLowering {
        self.lowering
    }

    pub const fn stride_bytes(&self) -> u64 {
        self.stride_bytes
    }

    pub const fn member_offsets_bytes(&self) -> &[u64] {
        &self.member_offsets_bytes
    }

    pub const fn phases(&self) -> &[StructArrayIndexRenderPhase] {
        &self.phases
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexRenderNames {
    function: String,
    aggregate: String,
    array: String,
    index: String,
    value: String,
}

impl StructArrayIndexRenderNames {
    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn aggregate(&self) -> &str {
        &self.aggregate
    }

    pub fn array(&self) -> &str {
        &self.array
    }

    pub fn index(&self) -> &str {
        &self.index
    }

    pub fn value(&self) -> &str {
        &self.value
    }
}

/// Private final-render authority. The exact source origin, opaque
/// certificate, full instruction inventory, and both closure ledgers must all
/// remain byte-for-byte equal to the freshly certified composition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct StructArrayIndexRenderPermit {
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedStructArrayIndexFunction,
    instruction_inventory: Box<[CanonicalInstructionId]>,
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

impl StructArrayIndexRenderPermit {
    fn new(certificate: &CertifiedStructArrayIndexFunction) -> Self {
        Self {
            contract_version: CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION,
            origin: certificate.origin().clone(),
            certificate: certificate.clone(),
            instruction_inventory: certificate
                .instruction_inventory()
                .to_vec()
                .into_boxed_slice(),
            instruction_dispositions: certificate
                .instruction_dispositions()
                .to_vec()
                .into_boxed_slice(),
            obligation_dispositions: certificate
                .obligation_dispositions()
                .to_vec()
                .into_boxed_slice(),
        }
    }

    fn matches(&self, certificate: &CertifiedStructArrayIndexFunction) -> bool {
        self.contract_version == CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION
            && self.origin == *certificate.origin()
            && self.certificate == *certificate
            && self.instruction_inventory.as_ref() == certificate.instruction_inventory()
            && self.instruction_dispositions.as_ref() == certificate.instruction_dispositions()
            && self.obligation_dispositions.as_ref() == certificate.obligation_dispositions()
            && certificate.validate(self.origin.source())
            && self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStructArrayIndexSemanticCFunction {
    schema_version: u32,
    scope: StructArrayIndexSemanticCFunctionScope,
    names: StructArrayIndexRenderNames,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedStructArrayIndexFunction,
    abi: StructArrayIndexAbiManifest,
    sealed_program: StructArrayIndexRenderProgram,
    program: StructArrayIndexRenderProgram,
    render_permit: StructArrayIndexRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StructArrayIndexSemanticCFunctionError {
    Machine(MachineBuildError),
    MissingStructArrayIndexCertificate,
    InvalidInterface,
    EmptyDifferential,
    TooManyDifferentialCases(usize),
    IndexOutsideModeledDomain(i32),
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for StructArrayIndexSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "struct-array semantic C function failed: {self:?}")
    }
}

impl std::error::Error for StructArrayIndexSemanticCFunctionError {}

impl From<MachineBuildError> for StructArrayIndexSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl CertifiedStructArrayIndexSemanticCFunction {
    /// The only construction path reruns the exact artifact-local certificate.
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, StructArrayIndexSemanticCFunctionError> {
        let certificate = certify_struct_array_index_function(artifact)?
            .ok_or(StructArrayIndexSemanticCFunctionError::MissingStructArrayIndexCertificate)?;
        let abi = expected_abi(&certificate)?;
        let program = expected_program(&certificate)?;
        let function = Self {
            schema_version: CERTIFIED_STRUCT_ARRAY_INDEX_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: StructArrayIndexSemanticCFunctionScope::ClosedOneBlockX86_64StructArrayIndex,
            names: StructArrayIndexRenderNames {
                function: "certified_struct_array_index".to_string(),
                aggregate: "DemoStruct".to_string(),
                array: "array".to_string(),
                index: "index".to_string(),
                value: "value".to_string(),
            },
            origin: certificate.origin().clone(),
            render_permit: StructArrayIndexRenderPermit::new(&certificate),
            certificate,
            abi,
            sealed_program: program.clone(),
            program,
        };
        let audit = function.audit();
        if !audit.has_exact_struct_array_index_function() {
            return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
                audit.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> StructArrayIndexSemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &StructArrayIndexRenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn certificate(&self) -> &CertifiedStructArrayIndexFunction {
        &self.certificate
    }

    pub const fn abi(&self) -> &StructArrayIndexAbiManifest {
        &self.abi
    }

    pub const fn program(&self) -> &StructArrayIndexRenderProgram {
        &self.program
    }

    pub fn with_cosmetic_names(
        mut self,
        function: impl Into<String>,
        aggregate: impl Into<String>,
        array: impl Into<String>,
        index: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        self.names = StructArrayIndexRenderNames {
            function: function.into(),
            aggregate: aggregate.into(),
            array: array.into(),
            index: index.into(),
            value: value.into(),
        };
        self
    }

    pub fn audit(&self) -> StructArrayIndexSemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_STRUCT_ARRAY_INDEX_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("struct-array renderer schema mismatch".to_string());
        }
        if self.scope
            != StructArrayIndexSemanticCFunctionScope::ClosedOneBlockX86_64StructArrayIndex
        {
            invalid.push("struct-array renderer scope mismatch".to_string());
        }
        if self.certificate.origin() != &self.origin
            || self.certificate.contract_version() != CERTIFIED_STRUCT_ARRAY_INDEX_CONTRACT_VERSION
            || !self.certificate.validate(self.origin.source())
            || !self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
        {
            invalid.push("struct-array certificate or origin mismatch".to_string());
        }
        match expected_abi(&self.certificate) {
            Ok(expected) if expected == self.abi => {}
            _ => invalid.push("struct-array ABI manifest mismatch".to_string()),
        }
        match expected_program(&self.certificate) {
            Ok(expected) if self.program == expected && self.sealed_program == expected => {}
            _ => invalid.push("struct-array source-ordered render program mismatch".to_string()),
        }
        if !self.render_permit.matches(&self.certificate) {
            invalid.push("struct-array render permit mismatch".to_string());
        }
        StructArrayIndexSemanticCFunctionAuditReport { invalid }
    }

    pub fn render_certified_c(&self) -> Result<String, StructArrayIndexSemanticCFunctionError> {
        let audit = self.audit();
        if !audit.has_exact_struct_array_index_function() {
            return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
                audit.invalid,
            ));
        }
        let function = c_identifier("r2s_fn", &self.names.function);
        let aggregate = c_identifier("r2s_type", &self.names.aggregate);
        let array = c_identifier("r2s_arg0", &self.names.array);
        let index = c_identifier("r2s_arg1", &self.names.index);
        let value = c_identifier("r2s_arg2", &self.names.value);
        let mut output = String::new();
        output.push_str("#include <stddef.h>\n#include <stdint.h>\n\n");
        writeln!(&mut output, "typedef struct {aggregate} {{").expect("String writes cannot fail");
        for member in 0..MEMBER_COUNT {
            writeln!(&mut output, "\tint32_t member{member};").expect("String writes cannot fail");
        }
        writeln!(&mut output, "}} {aggregate};\n").expect("String writes cannot fail");
        writeln!(
            &mut output,
            "_Static_assert(sizeof({aggregate}) == 56, \"certified struct size\");"
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "_Static_assert(_Alignof({aggregate}) == 4, \"certified struct alignment\");"
        )
        .expect("String writes cannot fail");
        for member in 0..MEMBER_COUNT {
            writeln!(
                &mut output,
                "_Static_assert(offsetof({aggregate}, member{member}) == {}, \"certified member{member} offset\");",
                member * 4
            )
            .expect("String writes cannot fail");
        }
        writeln!(
            &mut output,
            "\nint32_t {function}({aggregate} *{array}, int32_t {index}, int32_t {value}) {{"
        )
        .expect("String writes cannot fail");
        writeln!(&mut output, "\t{array}[{index}].member2 = {value};")
            .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tint32_t post_write_member2 = {array}[{index}].member2;"
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tint32_t member13_for_carry = {array}[{index}].member13;"
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tint32_t member13_for_overflow = {array}[{index}].member13;"
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tint32_t member13_for_add = {array}[{index}].member13;"
        )
        .expect("String writes cannot fail");
        output
            .push_str("\t/* The first two reads retain distinct certified source identities. */\n");
        output.push_str("\t(void)member13_for_carry;\n\t(void)member13_for_overflow;\n");
        output.push_str("\tuint32_t result_bits = (uint32_t)post_write_member2 +\n");
        output.push_str("\t\t(uint32_t)member13_for_add;\n");
        output.push_str("\tif (result_bits <= (uint32_t)INT32_MAX) {\n");
        output.push_str("\t\treturn (int32_t)result_bits;\n\t}\n");
        output.push_str("\tuint32_t negative_magnitude = UINT32_MAX - result_bits;\n");
        output.push_str("\treturn -INT32_C(1) - (int32_t)negative_magnitude;\n}\n");
        Ok(output)
    }
}

fn expected_abi(
    certificate: &CertifiedStructArrayIndexFunction,
) -> Result<StructArrayIndexAbiManifest, StructArrayIndexSemanticCFunctionError> {
    let parameters = certificate.parameters();
    let returned = certificate.returned();
    if certificate.revision_identity().is_empty()
        || parameters.len() != 3
        || parameters.iter().enumerate().any(|(index, parameter)| {
            parameter.index() != index as u32
                || parameter.abi_storage().space != CanonicalStorageSpace::Register
                || parameter.abi_storage().size != 8
                || parameter.graph_storage().space != CanonicalStorageSpace::Register
                || parameter.graph_storage().size != if index == 0 { 8 } else { 4 }
        })
        || returned.return_storage().space != CanonicalStorageSpace::Register
        || returned.return_storage().size != 8
        || returned.wraps_at_bits() != 32
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidInterface);
    }
    Ok(StructArrayIndexAbiManifest {
        revision_identity: certificate.revision_identity().to_vec().into_boxed_slice(),
        parameters: parameters.to_vec().into_boxed_slice(),
        return_storage: returned.return_storage(),
    })
}

fn expected_program(
    certificate: &CertifiedStructArrayIndexFunction,
) -> Result<StructArrayIndexRenderProgram, StructArrayIndexSemanticCFunctionError> {
    let accesses = certificate.accesses();
    let (post_write_access, member13_start) = match certificate.lowering() {
        CertifiedStructArrayIndexLowering::O2Register if accesses.len() == 4 => (None, 1),
        CertifiedStructArrayIndexLowering::O0ParameterHomes if accesses.len() == 5 => (Some(1), 2),
        _ => return Err(StructArrayIndexSemanticCFunctionError::InvalidInterface),
    };
    if certificate.layout().stride_bytes() != STRIDE_BYTES
        || certificate.layout().align_bytes() != 4
        || certificate.layout().member_offsets_bytes()
            != &(0..MEMBER_COUNT)
                .map(|member| member as u64 * 4)
                .collect::<Vec<_>>()
        || accesses[0].kind() != CertifiedStructArrayIndexAccessKind::Write
        || accesses[0].member_id() != STORED_MEMBER
        || accesses[member13_start..].iter().any(|access| {
            access.kind() != CertifiedStructArrayIndexAccessKind::Read
                || access.member_id() != LOADED_MEMBER
        })
        || accesses[member13_start..].len() != 3
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidInterface);
    }
    if let Some(index) = post_write_access
        && (accesses[index].kind() != CertifiedStructArrayIndexAccessKind::Read
            || accesses[index].member_id() != STORED_MEMBER)
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidInterface);
    }
    let post_write_producer = post_write_access.map_or_else(
        || accesses[0].memory_instruction(),
        |index| accesses[index].memory_instruction(),
    );
    let phases = [
        StructArrayIndexRenderPhase {
            kind: StructArrayIndexRenderPhaseKind::StoreMember2,
            producer: accesses[0].memory_instruction(),
            value: accesses[0].value(),
            access_index: Some(0),
        },
        StructArrayIndexRenderPhase {
            kind: StructArrayIndexRenderPhaseKind::ReadMember2AfterStore,
            producer: post_write_producer,
            value: post_write_access.map_or(accesses[0].value(), |index| accesses[index].value()),
            access_index: post_write_access.map(|index| index as u32),
        },
        StructArrayIndexRenderPhase {
            kind: StructArrayIndexRenderPhaseKind::ReadMember13ForCarry,
            producer: accesses[member13_start].memory_instruction(),
            value: accesses[member13_start].value(),
            access_index: Some(member13_start as u32),
        },
        StructArrayIndexRenderPhase {
            kind: StructArrayIndexRenderPhaseKind::ReadMember13ForOverflow,
            producer: accesses[member13_start + 1].memory_instruction(),
            value: accesses[member13_start + 1].value(),
            access_index: Some((member13_start + 1) as u32),
        },
        StructArrayIndexRenderPhase {
            kind: StructArrayIndexRenderPhaseKind::ReadMember13ForAdd,
            producer: accesses[member13_start + 2].memory_instruction(),
            value: accesses[member13_start + 2].value(),
            access_index: Some((member13_start + 2) as u32),
        },
        StructArrayIndexRenderPhase {
            kind: StructArrayIndexRenderPhaseKind::Wrap32Add,
            producer: certificate.returned().add(),
            value: certificate.returned().returned_value(),
            access_index: None,
        },
    ];
    Ok(StructArrayIndexRenderProgram {
        lowering: certificate.lowering(),
        stride_bytes: certificate.layout().stride_bytes(),
        member_offsets_bytes: certificate
            .layout()
            .member_offsets_bytes()
            .to_vec()
            .into_boxed_slice(),
        phases: Box::new(phases),
    })
}

fn c_identifier(prefix: &str, requested: &str) -> String {
    let mut identifier = String::from(prefix);
    identifier.push('_');
    for byte in requested.bytes() {
        if byte.is_ascii_alphanumeric() || byte == b'_' {
            identifier.push(char::from(byte));
        } else {
            identifier.push('_');
        }
    }
    identifier
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexSemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl StructArrayIndexSemanticCFunctionAuditReport {
    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn has_exact_struct_array_index_function(&self) -> bool {
        self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexDifferentialInput {
    pub index: i32,
    pub value: i32,
    pub initial_member2: i32,
    pub member13: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexObservedEvent {
    producer: CanonicalInstructionId,
    kind: CertifiedStructArrayIndexAccessKind,
    member_id: u32,
    byte_address: u64,
    value: i32,
}

impl StructArrayIndexObservedEvent {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn kind(&self) -> CertifiedStructArrayIndexAccessKind {
        self.kind
    }

    pub const fn member_id(&self) -> u32 {
        self.member_id
    }

    pub const fn byte_address(&self) -> u64 {
        self.byte_address
    }

    pub const fn value(&self) -> i32 {
        self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexDifferentialCase {
    input: StructArrayIndexDifferentialInput,
    source_result: i32,
    candidate_result: i32,
    source_events: Box<[StructArrayIndexObservedEvent]>,
    candidate_events: Box<[StructArrayIndexObservedEvent]>,
    source_member2: i32,
    candidate_member2: i32,
}

impl StructArrayIndexDifferentialCase {
    pub const fn input(&self) -> StructArrayIndexDifferentialInput {
        self.input
    }

    pub const fn source_result(&self) -> i32 {
        self.source_result
    }

    pub const fn candidate_result(&self) -> i32 {
        self.candidate_result
    }

    pub const fn source_events(&self) -> &[StructArrayIndexObservedEvent] {
        &self.source_events
    }

    pub const fn candidate_events(&self) -> &[StructArrayIndexObservedEvent] {
        &self.candidate_events
    }

    pub const fn source_member2(&self) -> i32 {
        self.source_member2
    }

    pub const fn candidate_member2(&self) -> i32 {
        self.candidate_member2
    }

    pub fn matches(&self) -> bool {
        self.source_result == self.candidate_result
            && self.source_events == self.candidate_events
            && self.source_member2 == self.candidate_member2
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StructArrayIndexDifferentialReport {
    cases: Box<[StructArrayIndexDifferentialCase]>,
}

impl StructArrayIndexDifferentialReport {
    pub const fn cases(&self) -> &[StructArrayIndexDifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty()
            && self
                .cases
                .iter()
                .all(StructArrayIndexDifferentialCase::matches)
    }
}

pub fn check_struct_array_index_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedStructArrayIndexSemanticCFunction,
    inputs: impl IntoIterator<Item = StructArrayIndexDifferentialInput>,
) -> Result<StructArrayIndexDifferentialReport, StructArrayIndexSemanticCFunctionError> {
    let audit = candidate.audit();
    if !audit.has_exact_struct_array_index_function() {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            audit.invalid,
        ));
    }
    let source = certify_struct_array_index_function(artifact)?
        .ok_or(StructArrayIndexSemanticCFunctionError::MissingStructArrayIndexCertificate)?;
    if source.origin() != candidate.origin() || source != *candidate.certificate() {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["differential source and candidate certificates differ".to_string()],
        ));
    }
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.is_empty() {
        return Err(StructArrayIndexSemanticCFunctionError::EmptyDifferential);
    }
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(StructArrayIndexSemanticCFunctionError::TooManyDifferentialCases(inputs.len()));
    }
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        if input.index < -MAX_ABS_INDEX || input.index > MAX_ABS_INDEX {
            return Err(
                StructArrayIndexSemanticCFunctionError::IndexOutsideModeledDomain(input.index),
            );
        }
        let (source_result, source_events, source_member2) =
            execute_source_case(artifact, &source, input)?;
        let (candidate_result, candidate_events, candidate_member2) =
            execute_candidate_case(candidate, input)?;
        cases.push(StructArrayIndexDifferentialCase {
            input,
            source_result,
            candidate_result,
            source_events,
            candidate_events,
            source_member2,
            candidate_member2,
        });
    }
    Ok(StructArrayIndexDifferentialReport {
        cases: cases.into_boxed_slice(),
    })
}

fn execute_source_case(
    artifact: &SsaArtifact,
    certificate: &CertifiedStructArrayIndexFunction,
    input: StructArrayIndexDifferentialInput,
) -> Result<(i32, Box<[StructArrayIndexObservedEvent]>, i32), StructArrayIndexSemanticCFunctionError>
{
    let member2_address = member_address(input.index, STORED_MEMBER)?;
    let member13_address = member_address(input.index, LOADED_MEMBER)?;
    let parameters = certificate.parameters();
    let overrides = BTreeMap::from([
        (
            parameters[0].graph_value(),
            ExactStructBits::new(64, u128::from(ARRAY_BASE))?,
        ),
        (
            parameters[1].graph_value(),
            ExactStructBits::new(32, u128::from(input.index as u32))?,
        ),
        (
            parameters[2].graph_value(),
            ExactStructBits::new(32, u128::from(input.value as u32))?,
        ),
    ]);
    let mut memory = BTreeMap::new();
    for address in 0x10_0000 - 64..0x10_0000 + 8 {
        memory.insert(address, 0);
    }
    memory.extend(i32_bytes(member2_address, input.initial_member2));
    memory.extend(i32_bytes(member13_address, input.member13));
    let run = execute_retained_struct_array_ssa(artifact, certificate, overrides, memory)?;
    let events = run.events;
    if events.len() != certificate.accesses().len()
        || events
            .iter()
            .zip(certificate.accesses())
            .any(|(event, access)| {
                event.producer != access.memory_instruction()
                    || event.kind != access.kind()
                    || event.member_id != access.member_id()
                    || event.byte_address
                        != if access.member_id() == STORED_MEMBER {
                            member2_address
                        } else {
                            member13_address
                        }
            })
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["prepared struct-array event sequence differs from certificate".to_string()],
        ));
    }
    let source_member2 = read_exact_i32(&run.memory, member2_address)?;
    Ok((run.returned.bits as u32 as i32, events, source_member2))
}

fn execute_candidate_case(
    candidate: &CertifiedStructArrayIndexSemanticCFunction,
    input: StructArrayIndexDifferentialInput,
) -> Result<(i32, Box<[StructArrayIndexObservedEvent]>, i32), StructArrayIndexSemanticCFunctionError>
{
    let member2_address = member_address(input.index, STORED_MEMBER)?;
    let member13_address = member_address(input.index, LOADED_MEMBER)?;
    let accesses = candidate.certificate.accesses();
    let mut member2 = input.initial_member2;
    let member13 = input.member13;
    let mut post_write_member2 = None;
    let mut member13_for_add = None;
    let mut events = Vec::new();
    let mut result = None;
    for phase in candidate.program.phases() {
        let (kind, member_id, address, value) = match phase.kind {
            StructArrayIndexRenderPhaseKind::StoreMember2 => {
                member2 = input.value;
                (
                    Some(CertifiedStructArrayIndexAccessKind::Write),
                    STORED_MEMBER,
                    member2_address,
                    member2,
                )
            }
            StructArrayIndexRenderPhaseKind::ReadMember2AfterStore => {
                post_write_member2 = Some(member2);
                (
                    phase
                        .access_index
                        .map(|_| CertifiedStructArrayIndexAccessKind::Read),
                    STORED_MEMBER,
                    member2_address,
                    member2,
                )
            }
            StructArrayIndexRenderPhaseKind::ReadMember13ForCarry
            | StructArrayIndexRenderPhaseKind::ReadMember13ForOverflow => (
                Some(CertifiedStructArrayIndexAccessKind::Read),
                LOADED_MEMBER,
                member13_address,
                member13,
            ),
            StructArrayIndexRenderPhaseKind::ReadMember13ForAdd => {
                member13_for_add = Some(member13);
                (
                    Some(CertifiedStructArrayIndexAccessKind::Read),
                    LOADED_MEMBER,
                    member13_address,
                    member13,
                )
            }
            StructArrayIndexRenderPhaseKind::Wrap32Add => {
                let left = post_write_member2.ok_or_else(|| {
                    StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                        "candidate add precedes post-write member2 read".to_string(),
                    ])
                })?;
                let right = member13_for_add.ok_or_else(|| {
                    StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                        "candidate add precedes member13 add read".to_string(),
                    ])
                })?;
                result = Some((left as u32).wrapping_add(right as u32) as i32);
                continue;
            }
        };
        if let (Some(kind), Some(access_index)) = (kind, phase.access_index) {
            let access = accesses.get(access_index as usize).ok_or_else(|| {
                StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                    "candidate phase refers to an absent access".to_string(),
                ])
            })?;
            events.push(StructArrayIndexObservedEvent {
                producer: phase.producer,
                kind,
                member_id,
                byte_address: address,
                value,
            });
            if access.memory_instruction() != phase.producer
                || access.kind() != kind
                || access.member_id() != member_id
            {
                return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
                    vec!["candidate phase differs from certified access".to_string()],
                ));
            }
        }
    }
    let result = result.ok_or_else(|| {
        StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
            "candidate has no wrap32 return phase".to_string(),
        ])
    })?;
    Ok((result, events.into_boxed_slice(), member2))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExactStructBits {
    width: u32,
    bits: u128,
}

impl ExactStructBits {
    fn new(width: u32, bits: u128) -> Result<Self, StructArrayIndexSemanticCFunctionError> {
        let mask = exact_mask(width).ok_or_else(|| {
            StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![format!(
                "prepared struct-array source has unsupported width {width}"
            )])
        })?;
        Ok(Self {
            width,
            bits: bits & mask,
        })
    }

    fn signed(self) -> i128 {
        let sign = 1_u128 << (self.width - 1);
        if self.bits & sign == 0 {
            self.bits as i128
        } else if self.width == 128 {
            self.bits as i128
        } else {
            (self.bits | !exact_mask(self.width).expect("validated exact width")) as i128
        }
    }
}

struct ExactStructRun {
    returned: ExactStructBits,
    events: Box<[StructArrayIndexObservedEvent]>,
    memory: BTreeMap<u64, u8>,
}

/// Function-private interpreter for the exact 8/32/64/128-bit O0/O2 source
/// shapes. The 128-bit lane exists solely to execute the retained signed-scale
/// overflow packet; no formula is reconstructed from the certificate.
fn execute_retained_struct_array_ssa(
    artifact: &SsaArtifact,
    certificate: &CertifiedStructArrayIndexFunction,
    overrides: BTreeMap<ValueId, ExactStructBits>,
    mut memory: BTreeMap<u64, u8>,
) -> Result<ExactStructRun, StructArrayIndexSemanticCFunctionError> {
    const STACK_POINTER_OFFSET: u64 = 32;
    const FRAME_POINTER_OFFSET: u64 = 40;
    const STACK_BASE: u128 = 0x10_0000;
    const FRAME_BASE: u128 = 0x20_0000;

    if !certificate.validate(artifact.obligations())
        || certificate.origin().source() != artifact.obligations()
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["exact source runner received a foreign certificate".to_string()],
        ));
    }
    let function = artifact.function();
    let [block_addr] = function.block_addrs() else {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["prepared struct-array source is not one block".to_string()],
        ));
    };
    let block = function.get_block(*block_addr).ok_or_else(|| {
        StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
            "prepared struct-array source block is missing".to_string(),
        ])
    })?;
    if function.entry != *block_addr
        || *block_addr != certificate.entry()
        || !block.phis.is_empty()
        || !function.predecessors(*block_addr).is_empty()
        || !function.successors(*block_addr).is_empty()
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["prepared struct-array source is not closed and phi-free".to_string()],
        ));
    }
    let graph = artifact.graph();
    let graph_block = graph
        .block_id_for_addr(*block_addr)
        .and_then(|id| graph.block(id))
        .ok_or_else(|| {
            StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                "prepared struct-array graph block is missing".to_string(),
            ])
        })?;
    if graph_block.insts.len() != certificate.instruction_inventory().len()
        || graph_block.insts.len() > 128
    {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["prepared struct-array exact runner budget mismatch".to_string()],
        ));
    }

    let mut values = BTreeMap::new();
    for graph_value in &graph.values {
        if graph.def_inst(graph_value.id).is_some() || graph_value.var.constant_bits().is_some() {
            continue;
        }
        let width = graph_value.var.size.checked_mul(8).ok_or_else(|| {
            StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                "prepared struct-array input width overflow".to_string(),
            ])
        })?;
        let bits = match graph_value.canonical_storage {
            Some(storage)
                if storage.space == CanonicalStorageSpace::Register
                    && storage.offset == STACK_POINTER_OFFSET
                    && storage.size == 8 =>
            {
                STACK_BASE
            }
            Some(storage)
                if storage.space == CanonicalStorageSpace::Register
                    && storage.offset == FRAME_POINTER_OFFSET
                    && storage.size == 8 =>
            {
                FRAME_BASE
            }
            _ => 0,
        };
        values.insert(graph_value.id, ExactStructBits::new(width, bits)?);
    }
    for (value, bits) in overrides {
        let graph_value = graph.value(value).ok_or_else(|| {
            StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                "prepared struct-array override is foreign".to_string(),
            ])
        })?;
        if graph.def_inst(value).is_some()
            || graph_value.var.size.checked_mul(8) != Some(bits.width)
        {
            return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
                vec!["prepared struct-array override width mismatch".to_string()],
            ));
        }
        values.insert(value, bits);
    }

    let access_by_producer = certificate
        .accesses()
        .iter()
        .map(|access| (access.memory_instruction(), access))
        .collect::<BTreeMap<_, _>>();
    let mut events = Vec::new();
    for inst_id in &graph_block.insts {
        let inst = graph.inst(*inst_id).ok_or_else(|| {
            StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                "prepared struct-array instruction is missing".to_string(),
            ])
        })?;
        let producer = artifact
            .obligations()
            .instruction_for_inst(*inst_id)
            .map(|instruction| instruction.id)
            .ok_or_else(|| {
                StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                    "prepared struct-array instruction has no canonical identity".to_string(),
                ])
            })?;
        let InstPayload::Op(op) = &inst.payload else {
            return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
                vec!["prepared struct-array source unexpectedly contains a phi".to_string()],
            ));
        };
        if matches!(op, SSAOp::Nop | SSAOp::Return { .. }) {
            continue;
        }
        if matches!(op, SSAOp::Load { .. }) {
            let [address] = inst.inputs.as_slice() else {
                return Err(invalid_exact_op("load arity"));
            };
            let output = inst.output.ok_or_else(|| invalid_exact_op("load output"))?;
            let width = exact_graph_width(artifact, output)?;
            let address = exact_value(artifact, &values, *address)?;
            if address.width != 64 || width % 8 != 0 {
                return Err(invalid_exact_op("load shape"));
            }
            let value = exact_read_memory(&memory, address.bits as u64, width)?;
            values.insert(output, value);
            if let Some(access) = access_by_producer.get(&producer) {
                events.push(StructArrayIndexObservedEvent {
                    producer,
                    kind: CertifiedStructArrayIndexAccessKind::Read,
                    member_id: access.member_id(),
                    byte_address: address.bits as u64,
                    value: value.bits as u32 as i32,
                });
            }
            continue;
        }
        if matches!(op, SSAOp::Store { .. }) {
            let [address, stored] = inst.inputs.as_slice() else {
                return Err(invalid_exact_op("store arity"));
            };
            let address = exact_value(artifact, &values, *address)?;
            let stored = exact_value(artifact, &values, *stored)?;
            if address.width != 64 || stored.width % 8 != 0 {
                return Err(invalid_exact_op("store shape"));
            }
            exact_write_memory(&mut memory, address.bits as u64, stored)?;
            if let Some(access) = access_by_producer.get(&producer) {
                events.push(StructArrayIndexObservedEvent {
                    producer,
                    kind: CertifiedStructArrayIndexAccessKind::Write,
                    member_id: access.member_id(),
                    byte_address: address.bits as u64,
                    value: stored.bits as u32 as i32,
                });
            }
            continue;
        }
        let output = inst
            .output
            .ok_or_else(|| invalid_exact_op("value output"))?;
        let width = exact_graph_width(artifact, output)?;
        let input = |index: usize| {
            inst.inputs
                .get(index)
                .copied()
                .ok_or_else(|| invalid_exact_op("value input"))
                .and_then(|value| exact_value(artifact, &values, value))
        };
        let result = match op {
            SSAOp::Copy { .. } => exact_same_width(input(0)?, width)?,
            SSAOp::IntAdd { .. } => exact_binary(input(0)?, input(1)?, width, u128::wrapping_add)?,
            SSAOp::IntSub { .. } => exact_binary(input(0)?, input(1)?, width, u128::wrapping_sub)?,
            SSAOp::IntMult { .. } => exact_binary(input(0)?, input(1)?, width, u128::wrapping_mul)?,
            SSAOp::IntAnd { .. } => exact_binary(input(0)?, input(1)?, width, |a, b| a & b)?,
            SSAOp::IntOr { .. } => exact_binary(input(0)?, input(1)?, width, |a, b| a | b)?,
            SSAOp::IntXor { .. } => exact_binary(input(0)?, input(1)?, width, |a, b| a ^ b)?,
            SSAOp::IntZExt { .. } => {
                let value = input(0)?;
                if value.width >= width {
                    return Err(invalid_exact_op("zero extension width"));
                }
                ExactStructBits::new(width, value.bits)?
            }
            SSAOp::IntSExt { .. } => {
                let value = input(0)?;
                if value.width >= width {
                    return Err(invalid_exact_op("sign extension width"));
                }
                ExactStructBits::new(width, value.signed() as u128)?
            }
            SSAOp::Subpiece { offset, .. } => {
                let value = input(0)?;
                let shift = offset
                    .checked_mul(8)
                    .ok_or_else(|| invalid_exact_op("subpiece"))?;
                if shift.checked_add(width).is_none_or(|end| end > value.width) {
                    return Err(invalid_exact_op("subpiece width"));
                }
                ExactStructBits::new(width, value.bits >> shift)?
            }
            SSAOp::Piece { .. } => {
                let high = input(0)?;
                let low = input(1)?;
                if high.width.checked_add(low.width) != Some(width) || low.width == 128 {
                    return Err(invalid_exact_op("piece width"));
                }
                ExactStructBits::new(width, (high.bits << low.width) | low.bits)?
            }
            SSAOp::IntEqual { .. } => exact_bool(width, input(0)?.bits == input(1)?.bits)?,
            SSAOp::IntNotEqual { .. } => exact_bool(width, input(0)?.bits != input(1)?.bits)?,
            SSAOp::IntSLess { .. } => exact_bool(width, input(0)?.signed() < input(1)?.signed())?,
            SSAOp::IntCarry { .. } => {
                let left = input(0)?;
                let right = input(1)?;
                exact_require_binary(left, right, left.width)?;
                let overflow = left.width == 128 && left.bits.checked_add(right.bits).is_none()
                    || left.width < 128
                        && left.bits + right.bits
                            > exact_mask(left.width).expect("validated exact width");
                exact_bool(width, overflow)?
            }
            SSAOp::IntSCarry { .. } => {
                let left = input(0)?;
                let right = input(1)?;
                exact_require_binary(left, right, left.width)?;
                let result = ExactStructBits::new(left.width, left.bits.wrapping_add(right.bits))?;
                let sign = 1_u128 << (left.width - 1);
                exact_bool(
                    width,
                    (left.bits ^ right.bits) & sign == 0 && (left.bits ^ result.bits) & sign != 0,
                )?
            }
            SSAOp::IntSBorrow { .. } => {
                let left = input(0)?;
                let right = input(1)?;
                exact_require_binary(left, right, left.width)?;
                let result = ExactStructBits::new(left.width, left.bits.wrapping_sub(right.bits))?;
                let sign = 1_u128 << (left.width - 1);
                exact_bool(
                    width,
                    (left.bits ^ right.bits) & sign != 0 && (left.bits ^ result.bits) & sign != 0,
                )?
            }
            SSAOp::PopCount { .. } => {
                let value = input(0)?;
                ExactStructBits::new(width, u128::from(value.bits.count_ones()))?
            }
            _ => {
                return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
                    vec![format!(
                        "prepared struct-array exact runner does not admit {op:?}"
                    )],
                ));
            }
        };
        values.insert(output, result);
    }
    let returned = exact_value(artifact, &values, certificate.returned().full_value())?;
    if returned.width != 64 || events.len() != certificate.accesses().len() {
        return Err(StructArrayIndexSemanticCFunctionError::InvalidComposition(
            vec!["prepared struct-array return or event closure mismatch".to_string()],
        ));
    }
    Ok(ExactStructRun {
        returned,
        events: events.into_boxed_slice(),
        memory,
    })
}

fn invalid_exact_op(reason: &str) -> StructArrayIndexSemanticCFunctionError {
    StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![format!(
        "prepared struct-array exact runner rejected {reason}"
    )])
}

fn exact_mask(width: u32) -> Option<u128> {
    match width {
        8 | 16 | 32 | 64 => Some((1_u128 << width) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

fn exact_graph_width(
    artifact: &SsaArtifact,
    value: ValueId,
) -> Result<u32, StructArrayIndexSemanticCFunctionError> {
    artifact
        .graph()
        .value(value)
        .and_then(|value| value.var.size.checked_mul(8))
        .filter(|width| exact_mask(*width).is_some())
        .ok_or_else(|| invalid_exact_op("graph value width"))
}

fn exact_value(
    artifact: &SsaArtifact,
    values: &BTreeMap<ValueId, ExactStructBits>,
    value: ValueId,
) -> Result<ExactStructBits, StructArrayIndexSemanticCFunctionError> {
    if let Some(value) = values.get(&value).copied() {
        return Ok(value);
    }
    let graph_value = artifact
        .graph()
        .value(value)
        .ok_or_else(|| invalid_exact_op("foreign value"))?;
    let bits = graph_value
        .var
        .constant_bits()
        .ok_or_else(|| invalid_exact_op("unbound value"))?;
    ExactStructBits::new(exact_graph_width(artifact, value)?, u128::from(bits))
}

fn exact_same_width(
    value: ExactStructBits,
    width: u32,
) -> Result<ExactStructBits, StructArrayIndexSemanticCFunctionError> {
    if value.width != width {
        return Err(invalid_exact_op("copy width"));
    }
    Ok(value)
}

fn exact_require_binary(
    left: ExactStructBits,
    right: ExactStructBits,
    width: u32,
) -> Result<(), StructArrayIndexSemanticCFunctionError> {
    if left.width != width || right.width != width {
        return Err(invalid_exact_op("binary width"));
    }
    Ok(())
}

fn exact_binary(
    left: ExactStructBits,
    right: ExactStructBits,
    width: u32,
    operation: impl FnOnce(u128, u128) -> u128,
) -> Result<ExactStructBits, StructArrayIndexSemanticCFunctionError> {
    exact_require_binary(left, right, width)?;
    ExactStructBits::new(width, operation(left.bits, right.bits))
}

fn exact_bool(
    width: u32,
    value: bool,
) -> Result<ExactStructBits, StructArrayIndexSemanticCFunctionError> {
    ExactStructBits::new(width, u128::from(value))
}

fn exact_read_memory(
    memory: &BTreeMap<u64, u8>,
    address: u64,
    width: u32,
) -> Result<ExactStructBits, StructArrayIndexSemanticCFunctionError> {
    let mut bits = 0_u128;
    for index in 0..width / 8 {
        let byte = memory
            .get(
                &address
                    .checked_add(u64::from(index))
                    .ok_or_else(|| invalid_exact_op("memory read address overflow"))?,
            )
            .copied()
            .ok_or_else(|| invalid_exact_op("memory read outside modeled domain"))?;
        bits |= u128::from(byte) << (index * 8);
    }
    ExactStructBits::new(width, bits)
}

fn exact_write_memory(
    memory: &mut BTreeMap<u64, u8>,
    address: u64,
    value: ExactStructBits,
) -> Result<(), StructArrayIndexSemanticCFunctionError> {
    for index in 0..value.width / 8 {
        let location = address
            .checked_add(u64::from(index))
            .ok_or_else(|| invalid_exact_op("memory write address overflow"))?;
        if !memory.contains_key(&location) {
            return Err(invalid_exact_op("memory write outside modeled domain"));
        }
        memory.insert(location, (value.bits >> (index * 8)) as u8);
    }
    Ok(())
}

fn member_address(index: i32, member: u32) -> Result<u64, StructArrayIndexSemanticCFunctionError> {
    let address = i128::from(ARRAY_BASE)
        + i128::from(index) * i128::from(STRIDE_BYTES)
        + i128::from(member) * i128::from(MEMBER_BYTES);
    u64::try_from(address)
        .map_err(|_| StructArrayIndexSemanticCFunctionError::IndexOutsideModeledDomain(index))
}

fn i32_bytes(address: u64, value: i32) -> [(u64, u8); 4] {
    let bytes = value.to_le_bytes();
    std::array::from_fn(|index| (address + index as u64, bytes[index]))
}

fn read_exact_i32(
    memory: &BTreeMap<u64, u8>,
    address: u64,
) -> Result<i32, StructArrayIndexSemanticCFunctionError> {
    let mut bytes = [0; 4];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = memory
            .get(&(address + index as u64))
            .copied()
            .ok_or_else(|| {
                StructArrayIndexSemanticCFunctionError::InvalidComposition(vec![
                    "prepared source omitted final member2 memory".to_string(),
                ])
            })?;
    }
    Ok(i32::from_le_bytes(bytes))
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceAggregateLayout,
        SourceAggregateMember, SourceCarrierKind, SourceCarrierProjection, SourceFunctionInterface,
        SourceFunctionReturn, SourceLogicalValue, SourceStackSlotSpec, SourceType, SourceTypeGraph,
        SourceTypeKind, StackAddressBase,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(7);
    const ENTRY: u64 = 0x1000_00ab0;
    const RAX: u64 = 0;
    const RCX: u64 = 8;
    const RDX: u64 = 16;
    const RSI: u64 = 48;
    const RDI: u64 = 56;
    const CF: u64 = 512;
    const PF: u64 = 514;
    const ZF: u64 = 518;
    const SF: u64 = 519;
    const OF: u64 = 523;

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
        let mut arch = ArchSpec::new("x86-64-struct-array-render-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("EAX", RAX, 4),
            ("RAX", RAX, 8),
            ("ECX", RCX, 4),
            ("RCX", RCX, 8),
            ("EDX", RDX, 4),
            ("RDX", RDX, 8),
            ("RSP", 32, 8),
            ("RBP", 40, 8),
            ("ESI", RSI, 4),
            ("RSI", RSI, 8),
            ("RDI", RDI, 8),
            ("CF", CF, 1),
            ("PF", PF, 1),
            ("ZF", ZF, 1),
            ("SF", SF, 1),
            ("OF", OF, 1),
            ("RIP", 648, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn type_graph(name_seed: &str) -> SourceTypeGraph {
        let members = (0..MEMBER_COUNT).map(|index| {
            SourceAggregateMember::new(
                index as u32,
                0,
                index as u64 * 32,
                32,
                format!("{name_seed}_member_{index}"),
            )
        });
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
                members,
            )],
        )
        .expect("natural struct-array graph")
    }

    fn interface(name_seed: &str, homes: bool) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let stack_slots = homes.then(|| {
            vec![
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(40),
                    -8,
                    8,
                    0,
                    storage(RDI),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(40),
                    -12,
                    4,
                    1,
                    storage(RSI),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(40),
                    -16,
                    4,
                    2,
                    storage(RDX),
                ),
            ]
        });
        SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI)),
                SourceAbiParameterSpec::new(1, storage(RSI)),
                SourceAbiParameterSpec::new(2, storage(RDX)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX),
            },
            stack_slots.unwrap_or_default(),
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

    fn push_flag_packet_sized(
        block: &mut R2ILBlock,
        next: &mut u64,
        input: Varnode,
        input_size: u32,
    ) {
        block.push(R2ILOp::IntSLess {
            dst: register(SF, 1),
            a: input.clone(),
            b: constant(0, input_size),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(ZF, 1),
            a: input.clone(),
            b: constant(0, input_size),
        });
        let low = unique(next, input_size);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: input,
            b: constant(0xff, input_size),
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
            dst: register(PF, 1),
            a: parity,
            b: constant(0, 1),
        });
    }

    fn push_flag_packet(block: &mut R2ILBlock, next: &mut u64, input: Varnode) {
        push_flag_packet_sized(block, next, input, 4);
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
            src: constant(56, 8),
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
            b: constant(56, 8),
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
            dst: register(CF, 1),
            a: extended,
            b: wide_product,
        });
        block.push(R2ILOp::Copy {
            dst: register(OF, 1),
            src: register(CF, 1),
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
            dst: register(CF, 1),
            a: base.clone(),
            b: register(scaled, 8),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF, 1),
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

    fn o2_block(entry: u64, unique_seed: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 23);
        let mut next = unique_seed;
        push_frame_prefix(&mut block, &mut next);
        block.push(R2ILOp::Copy {
            dst: register(RAX, 4),
            src: register(RDX, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX, 8),
            src: register(RDX, 4),
        });
        push_scale_packet(&mut block, &mut next, register(RSI, 4), RCX);
        let member2_base = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member2_base.clone(),
            a: constant(8, 8),
            b: register(RDI, 8),
        });
        let member2_scale = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: member2_scale.clone(),
            a: register(RCX, 8),
            b: constant(1, 8),
        });
        let member2_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member2_address.clone(),
            a: member2_base,
            b: member2_scale,
        });
        let stored = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: stored.clone(),
            src: register(RDX, 4),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: member2_address,
            val: stored,
        });
        let member13_base = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member13_base.clone(),
            a: constant(52, 8),
            b: register(RDI, 8),
        });
        let member13_scale = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: member13_scale.clone(),
            a: register(RCX, 8),
            b: constant(1, 8),
        });
        let member13_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member13_address.clone(),
            a: member13_base,
            b: member13_scale,
        });
        let read1 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read1.clone(),
            space: DATA,
            addr: member13_address.clone(),
        });
        block.push(R2ILOp::IntCarry {
            dst: register(CF, 1),
            a: register(RDX, 4),
            b: read1,
        });
        let read2 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read2.clone(),
            space: DATA,
            addr: member13_address.clone(),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF, 1),
            a: register(RDX, 4),
            b: read2,
        });
        let read3 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read3.clone(),
            space: DATA,
            addr: member13_address,
        });
        block.push(R2ILOp::IntAdd {
            dst: register(RAX, 4),
            a: register(RDX, 4),
            b: read3,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX, 8),
            src: register(RAX, 4),
        });
        push_flag_packet(&mut block, &mut next, register(RAX, 4));
        push_frame_suffix(&mut block, &mut next);
        assert_eq!(block.ops.len(), 43);
        block
    }

    fn o0_block(entry: u64, unique_seed: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 73);
        let mut next = unique_seed;
        push_frame_prefix(&mut block, &mut next);
        push_home(&mut block, &mut next, -8, register(RDI, 8));
        push_home(&mut block, &mut next, -12, register(RSI, 4));
        push_home(&mut block, &mut next, -16, register(RDX, 4));
        let value = reload_home(&mut block, &mut next, -16, 4);
        block.push(R2ILOp::Copy {
            dst: register(RCX, 4),
            src: value.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RCX, 8),
            src: value.clone(),
        });
        let array1 = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RAX, 8),
            src: array1,
        });
        let index1 = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, index1, RDX);
        push_address_sum(&mut block, &mut next, register(RAX, 8), RDX, RAX);
        let member2_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member2_address.clone(),
            a: register(RAX, 8),
            b: constant(8, 8),
        });
        let stored = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: stored.clone(),
            src: value,
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: member2_address,
            val: stored,
        });
        let array2 = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RAX, 8),
            src: array2,
        });
        let index2 = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, index2, RCX);
        push_address_sum(&mut block, &mut next, register(RAX, 8), RCX, RAX);
        let member2_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member2_address.clone(),
            a: register(RAX, 8),
            b: constant(8, 8),
        });
        let member2 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: member2.clone(),
            space: DATA,
            addr: member2_address,
        });
        block.push(R2ILOp::Copy {
            dst: register(RAX, 4),
            src: member2.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX, 8),
            src: member2.clone(),
        });
        let array3 = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RCX, 8),
            src: array3,
        });
        let index3 = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, index3, RDX);
        push_address_sum(&mut block, &mut next, register(RCX, 8), RDX, RCX);
        let member13_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member13_address.clone(),
            a: register(RCX, 8),
            b: constant(52, 8),
        });
        let read1 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read1.clone(),
            space: DATA,
            addr: member13_address.clone(),
        });
        block.push(R2ILOp::IntCarry {
            dst: register(CF, 1),
            a: member2.clone(),
            b: read1,
        });
        let read2 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read2.clone(),
            space: DATA,
            addr: member13_address.clone(),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF, 1),
            a: member2.clone(),
            b: read2,
        });
        let read3 = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read3.clone(),
            space: DATA,
            addr: member13_address,
        });
        block.push(R2ILOp::IntAdd {
            dst: register(RAX, 4),
            a: member2,
            b: read3,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX, 8),
            src: register(RAX, 4),
        });
        push_flag_packet(&mut block, &mut next, register(RAX, 4));
        push_frame_suffix(&mut block, &mut next);
        assert_eq!(block.ops.len(), 114);
        block
    }

    fn artifact(block: R2ILBlock, homes: bool, name_seed: &str) -> SsaArtifact {
        SsaArtifact::raw_with_interface(&[block], Some(&arch()), interface(name_seed, homes))
            .expect("struct-array artifact")
    }

    fn o2_artifact() -> SsaArtifact {
        artifact(o2_block(ENTRY, 0x10000), false, "demo")
    }

    fn o0_artifact() -> SsaArtifact {
        artifact(o0_block(ENTRY, 0x40000), true, "demo")
    }

    fn probes() -> Vec<StructArrayIndexDifferentialInput> {
        let mut probes = vec![
            StructArrayIndexDifferentialInput {
                index: -32,
                value: i32::MIN,
                initial_member2: i32::MAX,
                member13: -1,
            },
            StructArrayIndexDifferentialInput {
                index: -1,
                value: -1,
                initial_member2: 0x1234,
                member13: 1,
            },
            StructArrayIndexDifferentialInput {
                index: 0,
                value: i32::MAX,
                initial_member2: i32::MIN,
                member13: 1,
            },
            StructArrayIndexDifferentialInput {
                index: 1,
                value: 1,
                initial_member2: -1,
                member13: i32::MAX,
            },
            StructArrayIndexDifferentialInput {
                index: 32,
                value: i32::MIN,
                initial_member2: 7,
                member13: i32::MIN,
            },
        ];
        let mut state = 0x243f_6a88_85a3_08d3_u64;
        for ordinal in 0..64 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let value = (state >> 32) as u32 as i32;
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            probes.push(StructArrayIndexDifferentialInput {
                index: (ordinal % 17) - 8,
                value,
                initial_member2: !value,
                member13: (state >> 32) as u32 as i32,
            });
        }
        probes
    }

    fn assert_refused(function: &CertifiedStructArrayIndexSemanticCFunction) {
        assert!(!function.audit().has_exact_struct_array_index_function());
        assert!(function.render_certified_c().is_err());
    }

    #[test]
    fn exact_o0_and_o2_emit_natural_layout_and_ordered_typed_c11() {
        for artifact in [o0_artifact(), o2_artifact()] {
            let function = CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact)
                .expect("struct-array semantic C");
            let c = function.render_certified_c().expect("strict C");
            assert!(c.contains("_Static_assert(sizeof(r2s_type_DemoStruct) == 56"));
            assert!(c.contains("_Alignof(r2s_type_DemoStruct) == 4"));
            assert!(c.contains("int32_t member13;"));
            assert!(c.contains("r2s_arg0_array[r2s_arg1_index].member2 = r2s_arg2_value;"));
            let post = c.find("post_write_member2").expect("member2 read");
            let carry = c.find("member13_for_carry").expect("first member13 read");
            let overflow = c
                .find("member13_for_overflow")
                .expect("second member13 read");
            let add = c.find("member13_for_add").expect("third member13 read");
            assert!(post < carry && carry < overflow && overflow < add);
            assert!(c.contains("uint32_t result_bits"));
            assert!(!c.contains("return (int32_t)result_bits;\n}"));
            assert!(!c.contains("frame"));
            assert!(!c.contains("stack"));
            assert!(!c.contains("home"));
        }
    }

    #[test]
    fn prepared_ssa_and_independent_typed_program_match_o0_and_o2_events() {
        for (artifact, expected_events) in [(o0_artifact(), 5), (o2_artifact(), 4)] {
            let function = CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact)
                .expect("struct-array semantic C");
            let report = check_struct_array_index_differential(&artifact, &function, probes())
                .expect("bounded differential");
            assert!(report.has_equivalence());
            assert!(report.cases().iter().all(|case| {
                case.source_events().len() == expected_events
                    && case.source_events()[0].kind() == CertifiedStructArrayIndexAccessKind::Write
                    && case.source_events()[0].member_id() == STORED_MEMBER
                    && case.source_member2() == case.input().value
            }));
        }
    }

    #[test]
    fn phase_permit_origin_certificate_and_cosmetic_mutations_are_audited() {
        let source_artifact = o0_artifact();
        let function = CertifiedStructArrayIndexSemanticCFunction::from_artifact(&source_artifact)
            .expect("struct-array semantic C");

        let mut dropped = function.clone();
        dropped.program.phases = dropped.program.phases[1..].to_vec().into_boxed_slice();
        assert_refused(&dropped);

        let mut duplicated = function.clone();
        let mut phases = duplicated.program.phases.to_vec();
        phases.insert(2, phases[2]);
        duplicated.program.phases = phases.into_boxed_slice();
        assert_refused(&duplicated);

        let mut reordered = function.clone();
        reordered.program.phases.swap(2, 3);
        assert_refused(&reordered);

        let mut wrong_member = function.clone();
        wrong_member.program.member_offsets_bytes[13] = 48;
        assert_refused(&wrong_member);

        let mut wrong_stride = function.clone();
        wrong_stride.program.stride_bytes = 52;
        assert_refused(&wrong_stride);

        let mut wrong_wrap = function.clone();
        wrong_wrap.program.phases[5].kind = StructArrayIndexRenderPhaseKind::ReadMember13ForAdd;
        assert_refused(&wrong_wrap);

        let mut permit = function.clone();
        permit.render_permit.contract_version ^= 1;
        assert_refused(&permit);

        let mut missing_inventory = function.clone();
        missing_inventory.render_permit.instruction_inventory =
            missing_inventory.render_permit.instruction_inventory[1..]
                .to_vec()
                .into_boxed_slice();
        assert_refused(&missing_inventory);

        let mut missing_obligation = function.clone();
        missing_obligation.render_permit.obligation_dispositions =
            missing_obligation.render_permit.obligation_dispositions[1..]
                .to_vec()
                .into_boxed_slice();
        assert_refused(&missing_obligation);

        let foreign_artifact = artifact(o0_block(ENTRY + 0x100, 0x90000), true, "foreign");
        let foreign = CertifiedStructArrayIndexSemanticCFunction::from_artifact(&foreign_artifact)
            .expect("foreign struct-array semantic C");
        let mut swapped_origin = function.clone();
        swapped_origin.origin = foreign.origin.clone();
        assert_refused(&swapped_origin);
        let mut swapped_certificate = function.clone();
        swapped_certificate.certificate = foreign.certificate.clone();
        assert_refused(&swapped_certificate);
        assert!(
            check_struct_array_index_differential(&foreign_artifact, &function, probes()).is_err()
        );

        let renamed = function.with_cosmetic_names("!", "same", "same", "same", "same");
        assert!(renamed.audit().has_exact_struct_array_index_function());
        assert!(
            renamed
                .render_certified_c()
                .expect("renamed C")
                .contains("r2s_fn__")
        );
    }

    #[test]
    fn source_type_layout_effect_and_extra_mutations_fail_closed() {
        let mut dropped = o2_block(ENTRY, 0x10000);
        dropped.ops.remove(23);
        assert!(matches!(
            CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact(
                dropped, false, "demo"
            )),
            Err(StructArrayIndexSemanticCFunctionError::MissingStructArrayIndexCertificate)
        ));

        let mut reordered = o2_block(ENTRY, 0x10000);
        reordered.ops.swap(23, 25);
        assert!(matches!(
            CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact(
                reordered, false, "demo"
            )),
            Err(StructArrayIndexSemanticCFunctionError::MissingStructArrayIndexCertificate)
        ));

        let mut extra = o2_block(ENTRY, 0x10000);
        extra.ops.insert(
            30,
            R2ILOp::IntAdd {
                dst: Varnode::unique(0xf0000, 4),
                a: constant(1, 4),
                b: constant(2, 4),
            },
        );
        assert!(matches!(
            CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact(
                extra, false, "demo"
            )),
            Err(StructArrayIndexSemanticCFunctionError::MissingStructArrayIndexCertificate)
        ));

        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let unsigned_graph = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Struct { aggregate_id: 0 }, 448, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 1 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                1,
                448,
                32,
                "wrong_signedness",
                (0..MEMBER_COUNT).map(|index| {
                    SourceAggregateMember::new(index as u32, 0, index as u64 * 32, 32, "member")
                }),
            )],
        )
        .expect("unsigned graph");
        let unsigned_interface = SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI)),
                SourceAbiParameterSpec::new(1, storage(RSI)),
                SourceAbiParameterSpec::new(2, storage(RDX)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(unsigned_graph),
        )
        .expect("unsigned interface");
        let unsigned = SsaArtifact::raw_with_interface(
            &[o2_block(ENTRY, 0x10000)],
            Some(&arch()),
            unsigned_interface,
        )
        .expect("unsigned artifact");
        assert!(matches!(
            CertifiedStructArrayIndexSemanticCFunction::from_artifact(&unsigned),
            Err(StructArrayIndexSemanticCFunctionError::MissingStructArrayIndexCertificate)
        ));
    }

    #[test]
    fn address_temp_and_type_names_are_not_authority_and_c_compiles() {
        for artifact in [
            artifact(o2_block(ENTRY, 0x10000), false, "one"),
            artifact(o2_block(ENTRY + 0x400, 0x80000), false, "two"),
            artifact(o0_block(ENTRY, 0x40000), true, "three"),
        ] {
            let function = CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact)
                .expect("address/name/temp-independent function");
            let source = function.render_certified_c().expect("strict C");
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock")
                .as_nanos();
            let directory = std::env::temp_dir()
                .join(format!("r2dec-struct-array-{}-{nonce}", std::process::id()));
            fs::create_dir(&directory).expect("temporary directory");
            let source_path = directory.join("probe.c");
            let object_path = directory.join("probe.o");
            fs::write(&source_path, source).expect("C source");
            let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
            let status = Command::new(compiler)
                .args([
                    "-std=c11",
                    "-Wall",
                    "-Wextra",
                    "-Wpedantic",
                    "-Werror",
                    "-c",
                ])
                .arg(&source_path)
                .arg("-o")
                .arg(&object_path)
                .status()
                .expect("C compiler");
            assert!(status.success());
            let _ = fs::remove_file(&source_path);
            let _ = fs::remove_file(&object_path);
            let _ = fs::remove_dir(&directory);
        }
    }

    #[test]
    fn differential_bounds_fail_closed() {
        let artifact = o2_artifact();
        let function = CertifiedStructArrayIndexSemanticCFunction::from_artifact(&artifact)
            .expect("struct-array semantic C");
        assert!(matches!(
            check_struct_array_index_differential(&artifact, &function, []),
            Err(StructArrayIndexSemanticCFunctionError::EmptyDifferential)
        ));
        assert!(matches!(
            check_struct_array_index_differential(
                &artifact,
                &function,
                (0..=MAX_DIFFERENTIAL_CASES).map(|_| StructArrayIndexDifferentialInput {
                    index: 0,
                    value: 0,
                    initial_member2: 0,
                    member13: 0,
                })
            ),
            Err(StructArrayIndexSemanticCFunctionError::TooManyDifferentialCases(_))
        ));
        assert!(matches!(
            check_struct_array_index_differential(
                &artifact,
                &function,
                [StructArrayIndexDifferentialInput {
                    index: MAX_ABS_INDEX + 1,
                    value: 0,
                    initial_member2: 0,
                    member13: 0,
                }]
            ),
            Err(StructArrayIndexSemanticCFunctionError::IndexOutsideModeledDomain(_))
        ));
    }
}
