//! Proof-preserving strict-C rendering for the two sealed x86-64 `sum_array`
//! lowerings.
//!
//! The O0 scalar-home graph and the O2 vectorized graph deliberately share
//! one render program only after their complete certificates close.  The
//! emitted loop is a semantic program, not a transcription of either machine
//! schedule: ordinary non-volatile reads may be coalesced, while every source
//! instruction and obligation remains sealed in the private render permit.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_SUM_ARRAY_CONTRACT_VERSION, CertifiedArtifactOrigin, CertifiedSumArrayBinding,
    CertifiedSumArrayDispositionClass, CertifiedSumArrayFunction,
    CertifiedSumArrayInstructionDisposition, CertifiedSumArrayLowering, CertifiedSumArrayParameter,
    certify_sum_array_function,
};
use r2ssa::{
    BlockTerminator, CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace,
    InstPayload, MachineBuildError, SSAOp, SemanticObligationId, SsaArtifact, ValueId,
};
use serde::Serialize;

pub const CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_SUM_ARRAY_CONTRACT_VERSION;

const ELEMENT_SIZE_BYTES: u32 = 4;
const ACCUMULATOR_WIDTH_BITS: u32 = 32;
const MAX_DIFFERENTIAL_CASES: usize = 512;
const MAX_DIFFERENTIAL_ELEMENTS: usize = 128;
const MAX_BLOCK_STEPS: usize = 1024;
const MAX_INSTRUCTION_STEPS: usize = 65_536;
const ARRAY_BASE: u64 = 0x40_0000;
const ENTRY_STACK: u64 = 0x10_0000;
const ENTRY_FRAME: u64 = 0x20_0000;
const RETURN_TARGET: u64 = 0x80_0000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SumArraySemanticCFunctionScope {
    ClosedExactX86_64SumArray,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SumArrayAbiManifest {
    revision_identity: Box<[u8]>,
    parameters: Box<[CertifiedSumArrayParameter]>,
    return_storage: CanonicalStorageId,
}

impl SumArrayAbiManifest {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SumArrayRenderPhaseKind {
    RejectNonPositiveLength,
    InitializeWrap32Accumulator,
    ReadSignedElement,
    Wrap32Accumulate,
    ReturnSignedBits,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SumArrayRenderProgram {
    lowering: CertifiedSumArrayLowering,
    element_size_bytes: u32,
    accumulator_width_bits: u32,
    phases: Box<[SumArrayRenderPhaseKind]>,
    guard_producers: Box<[CanonicalInstructionId]>,
    read_producers: Box<[CanonicalInstructionId]>,
    add_producers: Box<[CanonicalInstructionId]>,
    return_producers: Box<[CanonicalInstructionId]>,
}

impl SumArrayRenderProgram {
    pub const fn lowering(&self) -> CertifiedSumArrayLowering {
        self.lowering
    }

    pub const fn element_size_bytes(&self) -> u32 {
        self.element_size_bytes
    }

    pub const fn accumulator_width_bits(&self) -> u32 {
        self.accumulator_width_bits
    }

    pub const fn phases(&self) -> &[SumArrayRenderPhaseKind] {
        &self.phases
    }

    pub const fn guard_producers(&self) -> &[CanonicalInstructionId] {
        &self.guard_producers
    }

    pub const fn read_producers(&self) -> &[CanonicalInstructionId] {
        &self.read_producers
    }

    pub const fn add_producers(&self) -> &[CanonicalInstructionId] {
        &self.add_producers
    }

    pub const fn return_producers(&self) -> &[CanonicalInstructionId] {
        &self.return_producers
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SumArrayRenderNames {
    function: String,
    array: String,
    length: String,
    index: String,
    accumulator: String,
}

impl SumArrayRenderNames {
    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn array(&self) -> &str {
        &self.array
    }

    pub fn length(&self) -> &str {
        &self.length
    }

    pub fn index(&self) -> &str {
        &self.index
    }

    pub fn accumulator(&self) -> &str {
        &self.accumulator
    }
}

/// Private final-render authority.  The complete certificate and both exact
/// closure ledgers are copied rather than summarized.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct SumArrayRenderPermit {
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedSumArrayFunction,
    instruction_dispositions: Box<[CertifiedSumArrayInstructionDisposition]>,
    obligation_dispositions: Box<[(SemanticObligationId, CertifiedSumArrayDispositionClass)]>,
}

impl SumArrayRenderPermit {
    fn new(certificate: &CertifiedSumArrayFunction) -> Self {
        Self {
            contract_version: CERTIFIED_SUM_ARRAY_CONTRACT_VERSION,
            origin: certificate.origin().clone(),
            certificate: certificate.clone(),
            instruction_dispositions: certificate
                .instruction_inventory()
                .to_vec()
                .into_boxed_slice(),
            obligation_dispositions: certificate
                .obligation_dispositions()
                .to_vec()
                .into_boxed_slice(),
        }
    }

    fn matches(&self, certificate: &CertifiedSumArrayFunction) -> bool {
        self.contract_version == CERTIFIED_SUM_ARRAY_CONTRACT_VERSION
            && self.origin == *certificate.origin()
            && self.certificate == *certificate
            && self.instruction_dispositions.as_ref() == certificate.instruction_inventory()
            && self.obligation_dispositions.as_ref() == certificate.obligation_dispositions()
            && certificate.validate(self.origin.source())
            && self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSumArraySemanticCFunction {
    schema_version: u32,
    scope: SumArraySemanticCFunctionScope,
    names: SumArrayRenderNames,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedSumArrayFunction,
    abi: SumArrayAbiManifest,
    sealed_program: SumArrayRenderProgram,
    program: SumArrayRenderProgram,
    render_permit: SumArrayRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SumArraySemanticCFunctionError {
    Machine(MachineBuildError),
    MissingSumArrayCertificate,
    InvalidInterface,
    EmptyDifferential,
    TooManyDifferentialCases(usize),
    DifferentialElementBudget(usize),
    InvalidArrayModel,
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for SumArraySemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "sum-array semantic C function failed: {self:?}")
    }
}

impl std::error::Error for SumArraySemanticCFunctionError {}

impl From<MachineBuildError> for SumArraySemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl CertifiedSumArraySemanticCFunction {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, SumArraySemanticCFunctionError> {
        let certificate = certify_sum_array_function(artifact)?
            .ok_or(SumArraySemanticCFunctionError::MissingSumArrayCertificate)?;
        let abi = expected_abi(&certificate)?;
        let program = expected_program(&certificate)?;
        let function = Self {
            schema_version: CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: SumArraySemanticCFunctionScope::ClosedExactX86_64SumArray,
            names: SumArrayRenderNames {
                function: "certified_sum_array".to_string(),
                array: "array".to_string(),
                length: "length".to_string(),
                index: "index".to_string(),
                accumulator: "sum_bits".to_string(),
            },
            origin: certificate.origin().clone(),
            render_permit: SumArrayRenderPermit::new(&certificate),
            certificate,
            abi,
            sealed_program: program.clone(),
            program,
        };
        let audit = function.audit();
        if !audit.has_exact_sum_array_function() {
            return Err(SumArraySemanticCFunctionError::InvalidComposition(
                audit.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SumArraySemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &SumArrayRenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn certificate(&self) -> &CertifiedSumArrayFunction {
        &self.certificate
    }

    pub const fn abi(&self) -> &SumArrayAbiManifest {
        &self.abi
    }

    pub const fn program(&self) -> &SumArrayRenderProgram {
        &self.program
    }

    pub fn with_cosmetic_names(
        mut self,
        function: impl Into<String>,
        array: impl Into<String>,
        length: impl Into<String>,
        index: impl Into<String>,
        accumulator: impl Into<String>,
    ) -> Self {
        self.names = SumArrayRenderNames {
            function: function.into(),
            array: array.into(),
            length: length.into(),
            index: index.into(),
            accumulator: accumulator.into(),
        };
        self
    }

    pub fn audit(&self) -> SumArraySemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("sum-array renderer schema mismatch".to_string());
        }
        if self.scope != SumArraySemanticCFunctionScope::ClosedExactX86_64SumArray {
            invalid.push("sum-array renderer scope mismatch".to_string());
        }
        if self.certificate.origin() != &self.origin
            || self.certificate.contract_version() != CERTIFIED_SUM_ARRAY_CONTRACT_VERSION
            || !self.certificate.validate(self.origin.source())
            || !self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
        {
            invalid.push("sum-array certificate or origin mismatch".to_string());
        }
        match expected_abi(&self.certificate) {
            Ok(expected) if expected == self.abi => {}
            _ => invalid.push("sum-array ABI manifest mismatch".to_string()),
        }
        match expected_program(&self.certificate) {
            Ok(expected) if expected == self.program && expected == self.sealed_program => {}
            _ => invalid.push("sum-array semantic render program mismatch".to_string()),
        }
        if !self.render_permit.matches(&self.certificate) {
            invalid.push("sum-array render permit mismatch".to_string());
        }
        SumArraySemanticCFunctionAuditReport { invalid }
    }

    pub fn render_certified_c(&self) -> Result<String, SumArraySemanticCFunctionError> {
        let audit = self.audit();
        if !audit.has_exact_sum_array_function() {
            return Err(SumArraySemanticCFunctionError::InvalidComposition(
                audit.invalid,
            ));
        }
        let function = c_identifier("r2s_fn", &self.names.function);
        let array = c_identifier("r2s_arg0", &self.names.array);
        let length = c_identifier("r2s_arg1", &self.names.length);
        let index = c_identifier("r2s_index", &self.names.index);
        let accumulator = c_identifier("r2s_sum", &self.names.accumulator);
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str("static int32_t r2s_i32_from_bits(uint32_t bits) {\n");
        output.push_str("\tif (bits <= (uint32_t)INT32_MAX) {\n");
        output.push_str("\t\treturn (int32_t)bits;\n\t}\n");
        output.push_str("\tuint32_t magnitude_minus_one = UINT32_MAX - bits;\n");
        output.push_str("\treturn -INT32_C(1) - (int32_t)magnitude_minus_one;\n}\n\n");
        writeln!(
            &mut output,
            "int32_t {function}(const int32_t *{array}, int32_t {length}) {{"
        )
        .expect("String writes cannot fail");
        writeln!(&mut output, "\tif ({length} <= 0) {{").expect("String writes cannot fail");
        output.push_str("\t\treturn INT32_C(0);\n\t}\n");
        writeln!(&mut output, "\tuint32_t {accumulator} = UINT32_C(0);")
            .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tfor (int32_t {index} = 0; {index} < {length}; ++{index}) {{"
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\t{accumulator} += (uint32_t){array}[{index}];"
        )
        .expect("String writes cannot fail");
        output.push_str("\t}\n");
        writeln!(&mut output, "\treturn r2s_i32_from_bits({accumulator});")
            .expect("String writes cannot fail");
        output.push_str("}\n");
        Ok(output)
    }
}

fn expected_abi(
    certificate: &CertifiedSumArrayFunction,
) -> Result<SumArrayAbiManifest, SumArraySemanticCFunctionError> {
    let abi = certificate.abi();
    let parameters = abi.parameters();
    if abi.revision_identity().is_empty()
        || parameters.len() != 2
        || parameters.iter().enumerate().any(|(index, parameter)| {
            parameter.index() != index as u32
                || parameter.abi_storage().space != CanonicalStorageSpace::Register
                || parameter.abi_storage().size != 8
                || parameter.graph_storage().space != CanonicalStorageSpace::Register
                || parameter.graph_storage().size != if index == 0 { 8 } else { 4 }
        })
        || abi.return_storage().space != CanonicalStorageSpace::Register
        || abi.return_storage().size != 8
    {
        return Err(SumArraySemanticCFunctionError::InvalidInterface);
    }
    Ok(SumArrayAbiManifest {
        revision_identity: abi.revision_identity().to_vec().into_boxed_slice(),
        parameters: parameters.to_vec().into_boxed_slice(),
        return_storage: abi.return_storage(),
    })
}

fn expected_program(
    certificate: &CertifiedSumArrayFunction,
) -> Result<SumArrayRenderProgram, SumArraySemanticCFunctionError> {
    let phases = Box::new([
        SumArrayRenderPhaseKind::RejectNonPositiveLength,
        SumArrayRenderPhaseKind::InitializeWrap32Accumulator,
        SumArrayRenderPhaseKind::ReadSignedElement,
        SumArrayRenderPhaseKind::Wrap32Accumulate,
        SumArrayRenderPhaseKind::ReturnSignedBits,
    ]);
    let (guard_producers, read_producers, add_producers, return_producers) =
        match certificate.binding() {
            CertifiedSumArrayBinding::O0(binding) => (
                vec![binding.predicate().branch()],
                binding
                    .scalar_loop()
                    .reads()
                    .iter()
                    .map(|read| read.load())
                    .collect::<Vec<_>>(),
                vec![binding.scalar_loop().add()],
                vec![binding.returned().return_instruction()],
            ),
            CertifiedSumArrayBinding::O2(binding) => (
                binding
                    .guards()
                    .iter()
                    .map(|guard| guard.branch())
                    .collect(),
                binding
                    .vector_loop()
                    .reads()
                    .iter()
                    .map(|read| read.load())
                    .chain(binding.scalar_tail().reads().iter().map(|read| read.load()))
                    .collect(),
                binding
                    .vector_loop()
                    .lanes()
                    .iter()
                    .map(|lane| lane.add())
                    .chain(std::iter::once(binding.scalar_tail().add()))
                    .chain(binding.reduction().pairwise_adds().iter().copied())
                    .chain(std::iter::once(binding.reduction().final_add()))
                    .collect(),
                binding
                    .returns()
                    .iter()
                    .map(|returned| returned.return_instruction())
                    .collect(),
            ),
        };
    if certificate.types().element_size_bytes() != ELEMENT_SIZE_BYTES
        || guard_producers.is_empty()
        || read_producers.is_empty()
        || add_producers.is_empty()
        || return_producers.is_empty()
    {
        return Err(SumArraySemanticCFunctionError::InvalidInterface);
    }
    for producer in guard_producers
        .iter()
        .chain(&read_producers)
        .chain(&add_producers)
        .chain(&return_producers)
    {
        if certificate.instruction_disposition(*producer).is_none() {
            return Err(SumArraySemanticCFunctionError::InvalidInterface);
        }
    }
    Ok(SumArrayRenderProgram {
        lowering: certificate.lowering(),
        element_size_bytes: ELEMENT_SIZE_BYTES,
        accumulator_width_bits: ACCUMULATOR_WIDTH_BITS,
        phases,
        guard_producers: guard_producers.into_boxed_slice(),
        read_producers: read_producers.into_boxed_slice(),
        add_producers: add_producers.into_boxed_slice(),
        return_producers: return_producers.into_boxed_slice(),
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
pub struct SumArraySemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl SumArraySemanticCFunctionAuditReport {
    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn has_exact_sum_array_function(&self) -> bool {
        self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SumArrayDifferentialInput {
    length: i32,
    elements: Box<[i32]>,
}

impl SumArrayDifferentialInput {
    pub fn new(length: i32, elements: impl Into<Vec<i32>>) -> Self {
        Self {
            length,
            elements: elements.into().into_boxed_slice(),
        }
    }

    pub const fn length(&self) -> i32 {
        self.length
    }

    pub const fn elements(&self) -> &[i32] {
        &self.elements
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SumArrayObservedRead {
    element_index: u32,
    byte_address: u64,
    value: i32,
}

impl SumArrayObservedRead {
    pub const fn element_index(&self) -> u32 {
        self.element_index
    }

    pub const fn byte_address(&self) -> u64 {
        self.byte_address
    }

    pub const fn value(&self) -> i32 {
        self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SumArrayDifferentialCase {
    input: SumArrayDifferentialInput,
    source_result: i32,
    candidate_result: i32,
    source_reads: Box<[SumArrayObservedRead]>,
    candidate_reads: Box<[SumArrayObservedRead]>,
}

impl SumArrayDifferentialCase {
    pub const fn input(&self) -> &SumArrayDifferentialInput {
        &self.input
    }

    pub const fn source_result(&self) -> i32 {
        self.source_result
    }

    pub const fn candidate_result(&self) -> i32 {
        self.candidate_result
    }

    pub const fn source_reads(&self) -> &[SumArrayObservedRead] {
        &self.source_reads
    }

    pub const fn candidate_reads(&self) -> &[SumArrayObservedRead] {
        &self.candidate_reads
    }

    pub fn matches(&self) -> bool {
        self.source_result == self.candidate_result && self.source_reads == self.candidate_reads
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SumArrayDifferentialReport {
    cases: Box<[SumArrayDifferentialCase]>,
}

impl SumArrayDifferentialReport {
    pub const fn cases(&self) -> &[SumArrayDifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty() && self.cases.iter().all(SumArrayDifferentialCase::matches)
    }
}

pub fn check_sum_array_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedSumArraySemanticCFunction,
    inputs: impl IntoIterator<Item = SumArrayDifferentialInput>,
) -> Result<SumArrayDifferentialReport, SumArraySemanticCFunctionError> {
    let audit = candidate.audit();
    if !audit.has_exact_sum_array_function() {
        return Err(SumArraySemanticCFunctionError::InvalidComposition(
            audit.invalid,
        ));
    }
    let source = certify_sum_array_function(artifact)?
        .ok_or(SumArraySemanticCFunctionError::MissingSumArrayCertificate)?;
    if source.origin() != candidate.origin() || source != *candidate.certificate() {
        return Err(SumArraySemanticCFunctionError::InvalidComposition(vec![
            "differential source and candidate certificates differ".to_string(),
        ]));
    }
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.is_empty() {
        return Err(SumArraySemanticCFunctionError::EmptyDifferential);
    }
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(SumArraySemanticCFunctionError::TooManyDifferentialCases(
            inputs.len(),
        ));
    }
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        validate_differential_input(&input)?;
        let (source_result, source_reads) =
            execute_sum_array_prepared_ssa(artifact, &source, &input)?;
        let (candidate_result, candidate_reads) = execute_sum_array_candidate(candidate, &input)?;
        cases.push(SumArrayDifferentialCase {
            input,
            source_result,
            candidate_result,
            source_reads,
            candidate_reads,
        });
    }
    Ok(SumArrayDifferentialReport {
        cases: cases.into_boxed_slice(),
    })
}

fn validate_differential_input(
    input: &SumArrayDifferentialInput,
) -> Result<(), SumArraySemanticCFunctionError> {
    if input.elements.len() > MAX_DIFFERENTIAL_ELEMENTS {
        return Err(SumArraySemanticCFunctionError::DifferentialElementBudget(
            input.elements.len(),
        ));
    }
    if input.length > 0
        && usize::try_from(input.length)
            .ok()
            .is_none_or(|length| length > input.elements.len())
    {
        return Err(SumArraySemanticCFunctionError::InvalidArrayModel);
    }
    Ok(())
}

fn execute_sum_array_candidate(
    candidate: &CertifiedSumArraySemanticCFunction,
    input: &SumArrayDifferentialInput,
) -> Result<(i32, Box<[SumArrayObservedRead]>), SumArraySemanticCFunctionError> {
    if !candidate.audit().has_exact_sum_array_function()
        || candidate.program.element_size_bytes != ELEMENT_SIZE_BYTES
        || candidate.program.accumulator_width_bits != ACCUMULATOR_WIDTH_BITS
        || candidate.program.phases.as_ref()
            != [
                SumArrayRenderPhaseKind::RejectNonPositiveLength,
                SumArrayRenderPhaseKind::InitializeWrap32Accumulator,
                SumArrayRenderPhaseKind::ReadSignedElement,
                SumArrayRenderPhaseKind::Wrap32Accumulate,
                SumArrayRenderPhaseKind::ReturnSignedBits,
            ]
    {
        return Err(SumArraySemanticCFunctionError::InvalidComposition(vec![
            "typed candidate program is not the sealed sum-array loop".to_string(),
        ]));
    }
    if input.length <= 0 {
        return Ok((0, Box::new([])));
    }
    let length = usize::try_from(input.length)
        .map_err(|_| SumArraySemanticCFunctionError::InvalidArrayModel)?;
    let mut accumulator = 0u32;
    let mut reads = Vec::with_capacity(length);
    for (index, value) in input.elements[..length].iter().copied().enumerate() {
        let index =
            u32::try_from(index).map_err(|_| SumArraySemanticCFunctionError::InvalidArrayModel)?;
        accumulator = accumulator.wrapping_add(value as u32);
        reads.push(SumArrayObservedRead {
            element_index: index,
            byte_address: element_address(index)?,
            value,
        });
    }
    Ok((i32_from_bits(accumulator), reads.into_boxed_slice()))
}

fn i32_from_bits(bits: u32) -> i32 {
    if bits <= i32::MAX as u32 {
        bits as i32
    } else {
        -1 - (u32::MAX - bits) as i32
    }
}

fn element_address(index: u32) -> Result<u64, SumArraySemanticCFunctionError> {
    ARRAY_BASE
        .checked_add(u64::from(index) * u64::from(ELEMENT_SIZE_BYTES))
        .ok_or(SumArraySemanticCFunctionError::InvalidArrayModel)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExactBits {
    width: u32,
    bits: u128,
}

impl ExactBits {
    fn new(width: u32, bits: u128) -> Result<Self, SumArraySemanticCFunctionError> {
        let mask = exact_mask(width).ok_or_else(|| invalid_exact("unsupported value width"))?;
        Ok(Self {
            width,
            bits: bits & mask,
        })
    }

    fn signed(self) -> i128 {
        if self.width == 128 {
            self.bits as i128
        } else {
            let shift = 128 - self.width;
            ((self.bits << shift) as i128) >> shift
        }
    }
}

struct SourceReadEvidence {
    vector: BTreeMap<CanonicalInstructionId, u32>,
    scalar: BTreeSet<CanonicalInstructionId>,
}

impl SourceReadEvidence {
    fn from_certificate(
        certificate: &CertifiedSumArrayFunction,
    ) -> Result<Self, SumArraySemanticCFunctionError> {
        match certificate.binding() {
            CertifiedSumArrayBinding::O0(binding) => {
                let [read] = binding.scalar_loop().reads() else {
                    return Err(invalid_exact("O0 external read inventory"));
                };
                Ok(Self {
                    vector: BTreeMap::new(),
                    scalar: BTreeSet::from([read.load()]),
                })
            }
            CertifiedSumArrayBinding::O2(binding) => {
                let vector = binding
                    .vector_loop()
                    .reads()
                    .iter()
                    .map(|read| (read.load(), read.size_bytes()))
                    .collect::<BTreeMap<_, _>>();
                let [_, _, semantic_read] = binding.scalar_tail().reads() else {
                    return Err(invalid_exact("O2 scalar read inventory"));
                };
                if vector.len() != 2 || vector.values().any(|size| *size != 16) {
                    return Err(invalid_exact("O2 vector read inventory"));
                }
                Ok(Self {
                    vector,
                    scalar: BTreeSet::from([semantic_read.load()]),
                })
            }
        }
    }
}

fn execute_sum_array_prepared_ssa(
    artifact: &SsaArtifact,
    certificate: &CertifiedSumArrayFunction,
    input: &SumArrayDifferentialInput,
) -> Result<(i32, Box<[SumArrayObservedRead]>), SumArraySemanticCFunctionError> {
    if certificate.origin().source() != artifact.obligations()
        || !certificate.validate(artifact.obligations())
        || !certificate
            .origin()
            .matches_retained_source(artifact.obligations(), certificate.origin().topology())
    {
        return Err(invalid_exact("foreign source certificate"));
    }
    let graph = artifact.graph();
    let function = artifact.function();
    let parameters = certificate.abi().parameters();
    if parameters.len() != 2 {
        return Err(invalid_exact("ABI parameter inventory"));
    }
    let mut values = BTreeMap::new();
    for value in &graph.values {
        if graph.def_inst(value.id).is_some() || value.var.constant_bits().is_some() {
            continue;
        }
        let width = value
            .var
            .size
            .checked_mul(8)
            .ok_or_else(|| invalid_exact("input width overflow"))?;
        let bits = match value.canonical_storage {
            Some(storage)
                if storage.space == CanonicalStorageSpace::Register
                    && storage.offset == 32
                    && storage.size == 8 =>
            {
                ENTRY_STACK
            }
            Some(storage)
                if storage.space == CanonicalStorageSpace::Register
                    && storage.offset == 40
                    && storage.size == 8 =>
            {
                ENTRY_FRAME
            }
            _ => 0,
        };
        values.insert(value.id, ExactBits::new(width, u128::from(bits))?);
    }
    values.insert(
        parameters[0].graph_value(),
        ExactBits::new(64, u128::from(ARRAY_BASE))?,
    );
    values.insert(
        parameters[1].graph_value(),
        ExactBits::new(32, u128::from(input.length as u32))?,
    );

    let mut memory = BTreeMap::new();
    exact_write_memory(
        &mut memory,
        ENTRY_STACK,
        ExactBits::new(64, u128::from(RETURN_TARGET))?,
    )?;
    for (index, value) in input.elements.iter().copied().enumerate() {
        let index =
            u32::try_from(index).map_err(|_| SumArraySemanticCFunctionError::InvalidArrayModel)?;
        exact_write_memory(
            &mut memory,
            element_address(index)?,
            ExactBits::new(32, u128::from(value as u32))?,
        )?;
    }

    let read_evidence = SourceReadEvidence::from_certificate(certificate)?;
    let mut reads = Vec::new();
    let mut current = function.entry;
    let mut predecessor = None;
    let mut instruction_steps = 0usize;
    for _ in 0..MAX_BLOCK_STEPS {
        let block_id = graph
            .block_id_for_addr(current)
            .ok_or_else(|| invalid_exact("source block identity"))?;
        let block = graph
            .block(block_id)
            .ok_or_else(|| invalid_exact("source graph block"))?;

        let mut phi_values = Vec::new();
        for inst_id in &block.insts {
            let instruction = graph
                .inst(*inst_id)
                .ok_or_else(|| invalid_exact("phi instruction"))?;
            let InstPayload::Phi { predecessors } = &instruction.payload else {
                continue;
            };
            let previous = predecessor.ok_or_else(|| invalid_exact("entry phi predecessor"))?;
            let index = predecessors
                .iter()
                .position(|candidate| *candidate == previous)
                .ok_or_else(|| invalid_exact("phi predecessor"))?;
            let source = *instruction
                .inputs
                .get(index)
                .ok_or_else(|| invalid_exact("phi input"))?;
            let output = instruction
                .output
                .ok_or_else(|| invalid_exact("phi output"))?;
            phi_values.push((output, exact_value(artifact, &values, source)?));
        }
        for (output, value) in phi_values {
            values.insert(output, value);
        }

        let mut branch_condition = None;
        for inst_id in &block.insts {
            instruction_steps = instruction_steps.saturating_add(1);
            if instruction_steps > MAX_INSTRUCTION_STEPS {
                return Err(invalid_exact("instruction budget exhausted"));
            }
            let instruction = graph
                .inst(*inst_id)
                .ok_or_else(|| invalid_exact("source instruction"))?;
            if matches!(instruction.payload, InstPayload::Phi { .. }) {
                continue;
            }
            let producer = artifact
                .obligations()
                .instruction_for_inst(*inst_id)
                .map(|source| source.id)
                .ok_or_else(|| invalid_exact("canonical instruction identity"))?;
            let InstPayload::Op(op) = &instruction.payload else {
                unreachable!();
            };
            let input_value = |index: usize| {
                instruction
                    .inputs
                    .get(index)
                    .copied()
                    .ok_or_else(|| invalid_exact("operation input"))
                    .and_then(|value| exact_value(artifact, &values, value))
            };
            match op {
                SSAOp::Nop | SSAOp::Branch { .. } => continue,
                SSAOp::CBranch { .. } => {
                    let condition = instruction
                        .inputs
                        .last()
                        .copied()
                        .ok_or_else(|| invalid_exact("branch condition"))?;
                    branch_condition = Some(exact_value(artifact, &values, condition)?.bits != 0);
                    continue;
                }
                SSAOp::Return { .. } => {
                    let returned = certified_return_value(certificate, producer)
                        .ok_or_else(|| invalid_exact("certified return path"))?;
                    let returned = exact_value(artifact, &values, returned)?;
                    if returned.width != 64 {
                        return Err(invalid_exact("physical return width"));
                    }
                    validate_normalized_reads(input, &reads)?;
                    return Ok((
                        i32_from_bits(returned.bits as u32),
                        reads.into_boxed_slice(),
                    ));
                }
                SSAOp::Store { .. } => {
                    let address = input_value(0)?;
                    let stored = input_value(1)?;
                    if address.width != 64 || stored.width % 8 != 0 {
                        return Err(invalid_exact("store shape"));
                    }
                    exact_write_memory(&mut memory, address.bits as u64, stored)?;
                    continue;
                }
                _ => {}
            }
            let output = instruction
                .output
                .ok_or_else(|| invalid_exact("value output"))?;
            let width = exact_graph_width(artifact, output)?;
            let result = match op {
                SSAOp::Load { .. } => {
                    let address = input_value(0)?;
                    if address.width != 64 || width % 8 != 0 {
                        return Err(invalid_exact("load shape"));
                    }
                    let loaded = exact_read_memory(&memory, address.bits as u64, width)?;
                    record_source_read(
                        &read_evidence,
                        producer,
                        address.bits as u64,
                        loaded,
                        &mut reads,
                    )?;
                    loaded
                }
                SSAOp::Copy { .. } => exact_same_width(input_value(0)?, width)?,
                SSAOp::IntAdd { .. } => exact_binary(
                    "integer add",
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    u128::wrapping_add,
                )?,
                SSAOp::IntSub { .. } => exact_binary(
                    "integer subtract",
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    u128::wrapping_sub,
                )?,
                SSAOp::IntMult { .. } => exact_binary(
                    "integer multiply",
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    u128::wrapping_mul,
                )?,
                SSAOp::IntAnd { .. } => exact_bitwise(
                    "integer and",
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    |a, b| a & b,
                )?,
                SSAOp::IntOr { .. } => exact_bitwise(
                    "integer or",
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    |a, b| a | b,
                )?,
                SSAOp::IntXor { .. } => exact_bitwise(
                    "integer xor",
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    |a, b| a ^ b,
                )?,
                SSAOp::IntLeft { .. } => {
                    exact_shift(input_value(0)?, input_value(1)?, width, true)?
                }
                SSAOp::IntRight { .. } => {
                    exact_shift(input_value(0)?, input_value(1)?, width, false)?
                }
                SSAOp::IntZExt { .. } => {
                    let value = input_value(0)?;
                    if value.width >= width {
                        return Err(invalid_exact("zero extension width"));
                    }
                    ExactBits::new(width, value.bits)?
                }
                SSAOp::IntSExt { .. } => {
                    let value = input_value(0)?;
                    if value.width >= width {
                        return Err(invalid_exact("sign extension width"));
                    }
                    ExactBits::new(width, value.signed() as u128)?
                }
                SSAOp::Subpiece { offset, .. } => {
                    let value = input_value(0)?;
                    let shift = offset
                        .checked_mul(8)
                        .ok_or_else(|| invalid_exact("subpiece offset"))?;
                    if shift.checked_add(width).is_none_or(|end| end > value.width) {
                        return Err(invalid_exact("subpiece width"));
                    }
                    ExactBits::new(width, value.bits >> shift)?
                }
                SSAOp::Piece { .. } => {
                    let high = input_value(0)?;
                    let low = input_value(1)?;
                    if high.width.checked_add(low.width) != Some(width) || low.width == 128 {
                        return Err(invalid_exact("piece width"));
                    }
                    ExactBits::new(width, (high.bits << low.width) | low.bits)?
                }
                SSAOp::IntEqual { .. } => {
                    exact_bool(width, input_value(0)?.bits == input_value(1)?.bits)?
                }
                SSAOp::IntNotEqual { .. } => {
                    exact_bool(width, input_value(0)?.bits != input_value(1)?.bits)?
                }
                SSAOp::IntLess { .. } => {
                    exact_bool(width, input_value(0)?.bits < input_value(1)?.bits)?
                }
                SSAOp::IntSLess { .. } => {
                    exact_bool(width, input_value(0)?.signed() < input_value(1)?.signed())?
                }
                SSAOp::BoolNot { .. } => exact_bool(width, input_value(0)?.bits == 0)?,
                SSAOp::BoolAnd { .. } => exact_bool(
                    width,
                    input_value(0)?.bits != 0 && input_value(1)?.bits != 0,
                )?,
                SSAOp::BoolOr { .. } => exact_bool(
                    width,
                    input_value(0)?.bits != 0 || input_value(1)?.bits != 0,
                )?,
                SSAOp::BoolXor { .. } => exact_bool(
                    width,
                    (input_value(0)?.bits != 0) ^ (input_value(1)?.bits != 0),
                )?,
                SSAOp::IntCarry { .. } => exact_carry(width, input_value(0)?, input_value(1)?)?,
                SSAOp::IntSCarry { .. } => {
                    exact_signed_carry(width, input_value(0)?, input_value(1)?)?
                }
                SSAOp::IntSBorrow { .. } => {
                    exact_signed_borrow(width, input_value(0)?, input_value(1)?)?
                }
                SSAOp::PopCount { .. } => {
                    ExactBits::new(width, u128::from(input_value(0)?.bits.count_ones()))?
                }
                _ => {
                    return Err(SumArraySemanticCFunctionError::InvalidComposition(vec![
                        format!("prepared sum-array runner does not admit {op:?}"),
                    ]));
                }
            };
            values.insert(output, result);
        }

        let source_block = function
            .cfg()
            .get_block(current)
            .ok_or_else(|| invalid_exact("source CFG block"))?;
        let next = match &source_block.terminator {
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                if branch_condition.ok_or_else(|| invalid_exact("branch condition absence"))? {
                    *true_target
                } else {
                    *false_target
                }
            }
            BlockTerminator::Branch { target } => *target,
            BlockTerminator::Fallthrough { next } => *next,
            BlockTerminator::Return => return Err(invalid_exact("return instruction absence")),
            BlockTerminator::IndirectBranch
            | BlockTerminator::Switch { .. }
            | BlockTerminator::Call { .. }
            | BlockTerminator::IndirectCall { .. }
            | BlockTerminator::None => return Err(invalid_exact("unsupported control shape")),
        };
        predecessor = Some(block_id);
        current = next;
    }
    Err(invalid_exact("block budget exhausted"))
}

fn certified_return_value(
    certificate: &CertifiedSumArrayFunction,
    return_instruction: CanonicalInstructionId,
) -> Option<ValueId> {
    match certificate.binding() {
        CertifiedSumArrayBinding::O0(binding) => (binding.returned().return_instruction()
            == return_instruction)
            .then_some(binding.returned().physical_full_register()),
        CertifiedSumArrayBinding::O2(binding) => binding
            .returns()
            .iter()
            .find(|returned| returned.return_instruction() == return_instruction)
            .map(|returned| returned.physical_full_register()),
    }
}

fn record_source_read(
    evidence: &SourceReadEvidence,
    producer: CanonicalInstructionId,
    address: u64,
    loaded: ExactBits,
    reads: &mut Vec<SumArrayObservedRead>,
) -> Result<(), SumArraySemanticCFunctionError> {
    if let Some(size_bytes) = evidence.vector.get(&producer).copied() {
        if loaded.width != size_bytes * 8 || size_bytes % ELEMENT_SIZE_BYTES != 0 {
            return Err(invalid_exact("vector read width"));
        }
        for lane in 0..size_bytes / ELEMENT_SIZE_BYTES {
            let lane_address = address
                .checked_add(u64::from(lane) * u64::from(ELEMENT_SIZE_BYTES))
                .ok_or_else(|| invalid_exact("vector lane address"))?;
            let element_index = source_element_index(lane_address)?;
            reads.push(SumArrayObservedRead {
                element_index,
                byte_address: lane_address,
                value: (loaded.bits >> (lane * ACCUMULATOR_WIDTH_BITS)) as u32 as i32,
            });
        }
    } else if evidence.scalar.contains(&producer) {
        if loaded.width != ACCUMULATOR_WIDTH_BITS {
            return Err(invalid_exact("scalar read width"));
        }
        reads.push(SumArrayObservedRead {
            element_index: source_element_index(address)?,
            byte_address: address,
            value: loaded.bits as u32 as i32,
        });
    }
    Ok(())
}

fn source_element_index(address: u64) -> Result<u32, SumArraySemanticCFunctionError> {
    let offset = address
        .checked_sub(ARRAY_BASE)
        .ok_or_else(|| invalid_exact("external read precedes array base"))?;
    if offset % u64::from(ELEMENT_SIZE_BYTES) != 0 {
        return Err(invalid_exact("unaligned external read"));
    }
    u32::try_from(offset / u64::from(ELEMENT_SIZE_BYTES))
        .map_err(|_| invalid_exact("external read index overflow"))
}

fn validate_normalized_reads(
    input: &SumArrayDifferentialInput,
    reads: &[SumArrayObservedRead],
) -> Result<(), SumArraySemanticCFunctionError> {
    let expected = usize::try_from(input.length.max(0))
        .map_err(|_| SumArraySemanticCFunctionError::InvalidArrayModel)?;
    if reads.len() != expected
        || reads.iter().enumerate().any(|(index, read)| {
            read.element_index != index as u32
                || element_address(index as u32) != Ok(read.byte_address)
                || input.elements.get(index).copied() != Some(read.value)
        })
    {
        return Err(invalid_exact("normalized external read sequence"));
    }
    Ok(())
}

fn invalid_exact(reason: &str) -> SumArraySemanticCFunctionError {
    SumArraySemanticCFunctionError::InvalidComposition(vec![format!(
        "prepared sum-array exact runner rejected {reason}"
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
) -> Result<u32, SumArraySemanticCFunctionError> {
    artifact
        .graph()
        .value(value)
        .and_then(|value| value.var.size.checked_mul(8))
        .filter(|width| exact_mask(*width).is_some())
        .ok_or_else(|| invalid_exact("graph value width"))
}

fn exact_value(
    artifact: &SsaArtifact,
    values: &BTreeMap<ValueId, ExactBits>,
    value: ValueId,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    if let Some(value) = values.get(&value).copied() {
        return Ok(value);
    }
    let graph_value = artifact
        .graph()
        .value(value)
        .ok_or_else(|| invalid_exact("foreign value"))?;
    let bits = graph_value
        .var
        .constant_bits()
        .ok_or_else(|| invalid_exact("unbound value"))?;
    ExactBits::new(exact_graph_width(artifact, value)?, u128::from(bits))
}

fn exact_same_width(
    value: ExactBits,
    width: u32,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    if value.width != width {
        return Err(invalid_exact("copy width"));
    }
    Ok(value)
}

fn exact_require_binary(
    left: ExactBits,
    right: ExactBits,
    width: u32,
) -> Result<(), SumArraySemanticCFunctionError> {
    if left.width != width || right.width != width {
        return Err(invalid_exact(&format!(
            "binary width (left {}, right {}, result {})",
            left.width, right.width, width
        )));
    }
    Ok(())
}

fn exact_binary(
    operation_name: &str,
    left: ExactBits,
    right: ExactBits,
    width: u32,
    operation: impl FnOnce(u128, u128) -> u128,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    if let Err(_) = exact_require_binary(left, right, width) {
        return Err(invalid_exact(&format!(
            "{operation_name} width (left {}, right {}, result {})",
            left.width, right.width, width
        )));
    }
    ExactBits::new(width, operation(left.bits, right.bits))
}

fn exact_bitwise(
    operation_name: &str,
    left: ExactBits,
    right: ExactBits,
    width: u32,
    operation: impl FnOnce(u128, u128) -> u128,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    // The retained x86 p-code uses a wider unique temporary for a few masks.
    // Bitwise inputs are unsigned bitvectors, so this is exact zero-extension,
    // not an inferred arithmetic cast.
    if left.width != right.width || left.width > width {
        return Err(invalid_exact(&format!(
            "{operation_name} width (left {}, right {}, result {})",
            left.width, right.width, width
        )));
    }
    ExactBits::new(width, operation(left.bits, right.bits))
}

fn exact_shift(
    value: ExactBits,
    amount: ExactBits,
    width: u32,
    left: bool,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    if value.width != width {
        return Err(invalid_exact("shift width"));
    }
    let amount = u32::try_from(amount.bits).unwrap_or(u32::MAX);
    let bits = if amount >= width {
        0
    } else if left {
        value.bits << amount
    } else {
        value.bits >> amount
    };
    ExactBits::new(width, bits)
}

fn exact_bool(width: u32, value: bool) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    ExactBits::new(width, u128::from(value))
}

fn exact_carry(
    width: u32,
    left: ExactBits,
    right: ExactBits,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    exact_require_binary(left, right, left.width)?;
    let carry = if left.width == 128 {
        left.bits.checked_add(right.bits).is_none()
    } else {
        left.bits + right.bits > exact_mask(left.width).expect("validated exact width")
    };
    exact_bool(width, carry)
}

fn exact_signed_carry(
    width: u32,
    left: ExactBits,
    right: ExactBits,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    exact_require_binary(left, right, left.width)?;
    let result = ExactBits::new(left.width, left.bits.wrapping_add(right.bits))?;
    let sign = 1_u128 << (left.width - 1);
    exact_bool(
        width,
        (left.bits ^ right.bits) & sign == 0 && (left.bits ^ result.bits) & sign != 0,
    )
}

fn exact_signed_borrow(
    width: u32,
    left: ExactBits,
    right: ExactBits,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    exact_require_binary(left, right, left.width)?;
    let result = ExactBits::new(left.width, left.bits.wrapping_sub(right.bits))?;
    let sign = 1_u128 << (left.width - 1);
    exact_bool(
        width,
        (left.bits ^ right.bits) & sign != 0 && (left.bits ^ result.bits) & sign != 0,
    )
}

fn exact_read_memory(
    memory: &BTreeMap<u64, u8>,
    address: u64,
    width: u32,
) -> Result<ExactBits, SumArraySemanticCFunctionError> {
    let mut bits = 0_u128;
    for index in 0..width / 8 {
        let location = address
            .checked_add(u64::from(index))
            .ok_or_else(|| invalid_exact("memory read address overflow"))?;
        let byte = memory
            .get(&location)
            .copied()
            .ok_or_else(|| invalid_exact("memory read outside modeled domain"))?;
        bits |= u128::from(byte) << (index * 8);
    }
    ExactBits::new(width, bits)
}

fn exact_write_memory(
    memory: &mut BTreeMap<u64, u8>,
    address: u64,
    value: ExactBits,
) -> Result<(), SumArraySemanticCFunctionError> {
    for index in 0..value.width / 8 {
        let location = address
            .checked_add(u64::from(index))
            .ok_or_else(|| invalid_exact("memory write address overflow"))?;
        memory.insert(location, (value.bits >> (index * 8)) as u8);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    use r2il::{AddressSpace, R2ILBlock, R2ILOp};
    use r2sleigh_lift::{Disassembler, build_arch_spec};
    use r2ssa::{
        SourceAbiParameterSpec, SourceCarrierKind, SourceCarrierProjection,
        SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue, SourceStackSlotSpec,
        SourceType, SourceTypeGraph, SourceTypeKind, StackAddressBase,
    };

    use super::*;

    const RAX: u64 = 0;
    const RBP: u64 = 40;
    const RSI: u64 = 48;
    const RDI: u64 = 56;

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

    fn storage(offset: u64) -> CanonicalStorageId {
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
                    storage(RBP),
                    -20,
                    4,
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    storage(RBP),
                    -16,
                    4,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(RBP),
                    -12,
                    4,
                    1,
                    storage(RSI),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(RBP),
                    -8,
                    8,
                    0,
                    storage(RDI),
                ),
            ]
        });
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI)),
                SourceAbiParameterSpec::new(1, storage(RSI)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX),
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

    fn o0_artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let (arch, blocks) = lift_blocks(
            base,
            &[
                "554889e548897df88975f4c745f000000000c745ec00000000",
                "8b45ec3b45f47d1c",
                "488b45f848634dec8b04880345f08945f08b45ec83c0018945ecebdc",
                "8b45f05dc3",
            ],
        );
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface(revision, true))
            .expect("prepared O0 sum-array artifact")
    }

    fn o2_artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let (arch, blocks) = lift_blocks(
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
        );
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface(revision, false))
            .expect("prepared O2 sum-array artifact")
    }

    fn probes() -> Vec<SumArrayDifferentialInput> {
        let mut probes = vec![
            SumArrayDifferentialInput::new(-11, []),
            SumArrayDifferentialInput::new(0, []),
            SumArrayDifferentialInput::new(1, [0]),
            SumArrayDifferentialInput::new(1, [i32::MIN]),
            SumArrayDifferentialInput::new(2, [i32::MAX, 1]),
            SumArrayDifferentialInput::new(3, [i32::MIN, -1, i32::MAX]),
            SumArrayDifferentialInput::new(7, [1, -2, 3, -4, 5, -6, 7]),
            SumArrayDifferentialInput::new(
                8,
                [i32::MAX, i32::MAX, 2, 0, -1, 1, i32::MIN, i32::MIN],
            ),
            SumArrayDifferentialInput::new(9, [i32::MAX, 1, 1, 1, 1, 1, 1, 1, i32::MIN]),
            // A longer backing model proves the candidate and source read only
            // the signed-length prefix; repeated values are alias-safe normal
            // memory, not distinct symbolic objects.
            SumArrayDifferentialInput::new(3, [17, 17, 17, 99, 99, 99]),
        ];
        let mut state = 0x6a09_e667_f3bc_c909u64;
        for case in 0..24usize {
            let length = 1 + case % 32;
            let mut elements = Vec::with_capacity(length);
            for _ in 0..length {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                elements.push((state >> 32) as u32 as i32);
            }
            probes.push(SumArrayDifferentialInput::new(length as i32, elements));
        }
        probes
    }

    #[test]
    fn exact_o0_and_real_o2_render_one_strict_semantic_loop() {
        for artifact in [
            o0_artifact(0x1000_0610, b"sum-array-render-o0"),
            o2_artifact(0x1000_0620, b"sum-array-render-o2"),
        ] {
            let function = CertifiedSumArraySemanticCFunction::from_artifact(&artifact)
                .expect("certified semantic function");
            assert!(function.audit().has_exact_sum_array_function());
            let rendered = function.render_certified_c().expect("strict C");
            assert!(rendered.contains("const int32_t *"));
            assert!(rendered.contains("int32_t r2s_arg1_length"));
            assert!(rendered.contains("if (r2s_arg1_length <= 0)"));
            assert!(rendered.contains("uint32_t r2s_sum_sum_bits"));
            assert!(rendered.contains("(uint32_t)r2s_arg0_array[r2s_index_index]"));
            assert!(!rendered.contains("__int128"));
            assert!(!rendered.contains("goto"));
        }
    }

    #[test]
    fn prepared_ssa_and_typed_candidate_match_o0_and_o2() {
        for artifact in [
            o0_artifact(0x1000_0610, b"sum-array-diff-o0"),
            o2_artifact(0x1000_0620, b"sum-array-diff-o2"),
        ] {
            let function = CertifiedSumArraySemanticCFunction::from_artifact(&artifact)
                .expect("certified semantic function");
            let report = check_sum_array_differential(&artifact, &function, probes())
                .expect("bounded prepared-SSA differential");
            assert!(report.has_equivalence());
            assert!(report.cases().iter().any(|case| case.input().length() < 0));
            assert!(report.cases().iter().any(|case| case.input().length() == 0));
            assert!(report.cases().iter().any(|case| case.input().length() == 1));
            assert!(report.cases().iter().any(|case| case.input().length() >= 9));
            assert!(report.cases().iter().all(|case| {
                case.source_reads().len() == case.input().length().max(0) as usize
            }));
        }
    }

    #[test]
    fn program_permit_foreign_origin_and_bounds_fail_closed() {
        let artifact = o2_artifact(0x1000_0620, b"sum-array-seal-a");
        let function = CertifiedSumArraySemanticCFunction::from_artifact(&artifact)
            .expect("certified semantic function");

        let mut mutated = function.clone();
        mutated.program.accumulator_width_bits = 64;
        assert!(!mutated.audit().has_exact_sum_array_function());
        assert!(mutated.render_certified_c().is_err());

        let foreign = o2_artifact(0x2000_0620, b"sum-array-seal-b");
        assert!(check_sum_array_differential(&foreign, &function, probes()).is_err());
        assert!(matches!(
            check_sum_array_differential(&artifact, &function, []),
            Err(SumArraySemanticCFunctionError::EmptyDifferential)
        ));
        assert!(matches!(
            check_sum_array_differential(
                &artifact,
                &function,
                [SumArrayDifferentialInput::new(2, [1])],
            ),
            Err(SumArraySemanticCFunctionError::InvalidArrayModel)
        ));
    }

    #[test]
    fn rendered_semantic_c_compiles_as_strict_c11() {
        let artifact = o2_artifact(0x1000_0620, b"sum-array-compile");
        let rendered = CertifiedSumArraySemanticCFunction::from_artifact(&artifact)
            .expect("certified semantic function")
            .render_certified_c()
            .expect("strict C");
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let directory = std::env::temp_dir().join(format!("r2dec-sum-array-{nonce}"));
        fs::create_dir(&directory).expect("temporary directory");
        let source = directory.join("sum_array.c");
        let object = directory.join("sum_array.o");
        fs::write(&source, rendered).expect("write strict C");
        let status = Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .status()
            .expect("invoke C compiler");
        assert!(status.success());
        fs::remove_dir_all(directory).expect("remove temporary directory");
    }
}
