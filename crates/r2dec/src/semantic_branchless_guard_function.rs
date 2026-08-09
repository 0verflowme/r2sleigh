//! Proof-preserving strict-C rendering for sealed x86-64 branchless guards.

use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedBranchlessGuardDispositionClass, CertifiedBranchlessGuardFunction,
    CertifiedBranchlessGuardKind, CertifiedBranchlessGuardParameter,
    certify_branchless_guard_function,
};
use r2ssa::{
    CallBoundarySlot, CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace,
    MachineBuildError, SemanticObligationId, SourceCarrierKind, SourceFunctionReturn,
    SourceTypeKind, SsaArtifact,
};
use serde::Serialize;

use crate::semantic_differential::{DifferentialBitVector, execute_prepared_single_block_return};

pub const CERTIFIED_BRANCHLESS_GUARD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION;

const MAX_DIFFERENTIAL_CASES: usize = 512;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum BranchlessGuardSemanticCFunctionScope {
    ClosedOneBlockX86_64BranchlessGuard,
}

/// Exact logical ABI consumed by the renderer. Physical 64-bit carriers remain
/// part of the manifest even though the visible C values are signed 32-bit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BranchlessGuardAbiManifest {
    revision_identity: Box<[u8]>,
    parameters: Box<[CertifiedBranchlessGuardParameter]>,
    return_storage: CanonicalStorageId,
}

impl BranchlessGuardAbiManifest {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameters(&self) -> &[CertifiedBranchlessGuardParameter] {
        &self.parameters
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
}

/// Renderer-level program duplicated from the opaque certificate so mutations
/// cannot silently change the emitted predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum BranchlessGuardRenderProgram {
    SimpleSubtractEqual {
        expected: u32,
    },
    DualWrap32XorOrEqual {
        sum_expected: u32,
        difference_expected: u32,
    },
}

impl From<CertifiedBranchlessGuardKind> for BranchlessGuardRenderProgram {
    fn from(kind: CertifiedBranchlessGuardKind) -> Self {
        match kind {
            CertifiedBranchlessGuardKind::SimpleSubtractEqual { expected } => {
                Self::SimpleSubtractEqual { expected }
            }
            CertifiedBranchlessGuardKind::DualWrap32XorOrEqual {
                sum_expected,
                difference_expected,
            } => Self::DualWrap32XorOrEqual {
                sum_expected,
                difference_expected,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BranchlessGuardRenderNames {
    function: String,
    first: String,
    second: String,
}

impl BranchlessGuardRenderNames {
    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn first(&self) -> &str {
        &self.first
    }

    pub fn second(&self) -> &str {
        &self.second
    }
}

/// Private final-render authority, sealed to the exact certificate, origin,
/// contract, instruction inventory, and source-obligation dispositions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct BranchlessGuardRenderPermit {
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedBranchlessGuardFunction,
    instruction_inventory: Box<[CanonicalInstructionId]>,
    obligation_dispositions: Box<
        [(
            SemanticObligationId,
            CertifiedBranchlessGuardDispositionClass,
        )],
    >,
}

impl BranchlessGuardRenderPermit {
    fn new(certificate: &CertifiedBranchlessGuardFunction) -> Self {
        Self {
            contract_version: CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION,
            origin: certificate.origin().clone(),
            certificate: certificate.clone(),
            instruction_inventory: certificate
                .instruction_inventory()
                .to_vec()
                .into_boxed_slice(),
            obligation_dispositions: certificate
                .obligation_dispositions()
                .to_vec()
                .into_boxed_slice(),
        }
    }

    fn matches(&self, certificate: &CertifiedBranchlessGuardFunction) -> bool {
        self.contract_version == CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION
            && self.origin == *certificate.origin()
            && self.certificate == *certificate
            && self.instruction_inventory.as_ref() == certificate.instruction_inventory()
            && self.obligation_dispositions.as_ref() == certificate.obligation_dispositions()
            && certificate.validate(self.origin.source())
            && self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
    }
}

/// A complete C11 function admitted only by an exact branchless-guard proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedBranchlessGuardSemanticCFunction {
    schema_version: u32,
    scope: BranchlessGuardSemanticCFunctionScope,
    names: BranchlessGuardRenderNames,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedBranchlessGuardFunction,
    abi: BranchlessGuardAbiManifest,
    sealed_program: BranchlessGuardRenderProgram,
    program: BranchlessGuardRenderProgram,
    render_permit: BranchlessGuardRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BranchlessGuardSemanticCFunctionError {
    Machine(MachineBuildError),
    MissingBranchlessGuardCertificate,
    InvalidInterface,
    EmptyDifferential,
    TooManyDifferentialCases(usize),
    WrongDifferentialInputKind,
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for BranchlessGuardSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "branchless-guard semantic C function failed: {self:?}")
    }
}

impl std::error::Error for BranchlessGuardSemanticCFunctionError {}

impl From<MachineBuildError> for BranchlessGuardSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl CertifiedBranchlessGuardSemanticCFunction {
    /// The only construction path reruns the artifact-local exact certificate.
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, BranchlessGuardSemanticCFunctionError> {
        let certificate = certify_branchless_guard_function(artifact)?
            .ok_or(BranchlessGuardSemanticCFunctionError::MissingBranchlessGuardCertificate)?;
        let abi = expected_abi(&certificate)?;
        let program = BranchlessGuardRenderProgram::from(certificate.kind());
        let render_permit = BranchlessGuardRenderPermit::new(&certificate);
        let function = Self {
            schema_version: CERTIFIED_BRANCHLESS_GUARD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: BranchlessGuardSemanticCFunctionScope::ClosedOneBlockX86_64BranchlessGuard,
            names: BranchlessGuardRenderNames {
                function: "certified_branchless_guard".to_string(),
                first: "first".to_string(),
                second: "second".to_string(),
            },
            origin: certificate.origin().clone(),
            certificate,
            abi,
            sealed_program: program,
            program,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_branchless_guard_function() {
            return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> BranchlessGuardSemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &BranchlessGuardRenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn certificate(&self) -> &CertifiedBranchlessGuardFunction {
        &self.certificate
    }

    pub const fn abi(&self) -> &BranchlessGuardAbiManifest {
        &self.abi
    }

    pub const fn program(&self) -> BranchlessGuardRenderProgram {
        self.program
    }

    /// Replace presentation-only labels. Prefixed identifier resolution keeps
    /// equal, empty, digit-leading, and punctuation-only inputs collision-free.
    pub fn with_cosmetic_names(
        mut self,
        function: impl Into<String>,
        first: impl Into<String>,
        second: impl Into<String>,
    ) -> Self {
        self.names = BranchlessGuardRenderNames {
            function: function.into(),
            first: first.into(),
            second: second.into(),
        };
        self
    }

    pub fn audit(&self) -> BranchlessGuardSemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_BRANCHLESS_GUARD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("branchless-guard renderer schema mismatch".to_string());
        }
        if self.scope != BranchlessGuardSemanticCFunctionScope::ClosedOneBlockX86_64BranchlessGuard
        {
            invalid.push("branchless-guard renderer scope mismatch".to_string());
        }
        if self.certificate.origin() != &self.origin
            || self.certificate.contract_version() != CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION
            || !self.certificate.validate(self.origin.source())
            || !self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
        {
            invalid.push("branchless-guard certificate or origin mismatch".to_string());
        }
        match expected_abi(&self.certificate) {
            Ok(expected) if expected == self.abi => {}
            _ => invalid.push("branchless-guard signed-32 ABI manifest mismatch".to_string()),
        }
        let expected_program = BranchlessGuardRenderProgram::from(self.certificate.kind());
        if self.program != expected_program || self.sealed_program != expected_program {
            invalid.push("branchless-guard predicate program mismatch".to_string());
        }
        if !self.render_permit.matches(&self.certificate) {
            invalid.push("branchless-guard render permit mismatch".to_string());
        }
        BranchlessGuardSemanticCFunctionAuditReport { invalid }
    }

    pub fn render_certified_c(&self) -> Result<String, BranchlessGuardSemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_branchless_guard_function() {
            return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let function = c_identifier("r2s_fn", &self.names.function);
        let first = c_identifier("r2s_arg0", &self.names.first);
        let second = c_identifier("r2s_arg1", &self.names.second);
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        match self.program {
            BranchlessGuardRenderProgram::SimpleSubtractEqual { expected } => {
                writeln!(&mut output, "int32_t {function}(int32_t {first}) {{")
                    .expect("String writes cannot fail");
                writeln!(
                    &mut output,
                    "\treturn (int32_t)((uint32_t){first} == UINT32_C(0x{expected:x}));"
                )
                .expect("String writes cannot fail");
            }
            BranchlessGuardRenderProgram::DualWrap32XorOrEqual {
                sum_expected,
                difference_expected,
            } => {
                writeln!(
                    &mut output,
                    "int32_t {function}(int32_t {first}, int32_t {second}) {{"
                )
                .expect("String writes cannot fail");
                output.push_str("\t/* Arithmetic is deliberately modulo 2^32. */\n");
                writeln!(&mut output, "\tuint32_t first_bits = (uint32_t){first};")
                    .expect("String writes cannot fail");
                writeln!(&mut output, "\tuint32_t second_bits = (uint32_t){second};")
                    .expect("String writes cannot fail");
                output.push_str("\tuint32_t sum_bits = (uint32_t)(first_bits + second_bits);\n");
                output.push_str(
                    "\tuint32_t difference_bits = (uint32_t)(first_bits - second_bits);\n",
                );
                writeln!(
                    &mut output,
                    "\treturn (int32_t)((sum_bits == UINT32_C(0x{sum_expected:x})) &&\n\t\t(difference_bits == UINT32_C(0x{difference_expected:x})));"
                )
                .expect("String writes cannot fail");
            }
        }
        output.push_str("}\n");
        Ok(output)
    }
}

fn expected_abi(
    certificate: &CertifiedBranchlessGuardFunction,
) -> Result<BranchlessGuardAbiManifest, BranchlessGuardSemanticCFunctionError> {
    let interface = certificate
        .origin()
        .machine_context()
        .source()
        .function_interface()
        .ok_or(BranchlessGuardSemanticCFunctionError::InvalidInterface)?;
    let types = interface
        .type_graph()
        .ok_or(BranchlessGuardSemanticCFunctionError::InvalidInterface)?;
    let expected_parameter_count = match certificate.kind() {
        CertifiedBranchlessGuardKind::SimpleSubtractEqual { .. } => 1,
        CertifiedBranchlessGuardKind::DualWrap32XorOrEqual { .. } => 2,
    };
    let logical_is_signed32 = |logical: &r2ssa::SourceLogicalValue| {
        logical.type_id() == 0
            && logical.carrier().kind() == SourceCarrierKind::LowBits
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == 32
    };
    let parameters_are_exact = certificate.parameters().len() == expected_parameter_count
        && interface.parameters().len() == expected_parameter_count
        && interface.parameter_logical_values().len() == expected_parameter_count
        && certificate
            .parameters()
            .iter()
            .zip(interface.parameters())
            .enumerate()
            .all(|(index, (certified, source))| {
                certified.index() == index as u32
                    && source.index() == index as u32
                    && certified.abi_storage() == source.storage()
                    && certified.abi_storage().space == CanonicalStorageSpace::Register
                    && certified.abi_storage().size == 8
                    && certified.low32_storage().space == CanonicalStorageSpace::Register
                    && certified.low32_storage().offset == certified.abi_storage().offset
                    && certified.low32_storage().size == 4
            });
    let return_is_exact = matches!(
        interface.return_kind(),
        SourceFunctionReturn::Register { storage } if storage == certificate.return_storage()
    ) && certificate.return_storage().space
        == CanonicalStorageSpace::Register
        && certificate.return_storage().size == 8
        && certificate.returned().slot()
            == (CallBoundarySlot::Register {
                index: 0,
                storage: certificate.return_storage(),
            });
    if interface.revision_identity().is_empty()
        || interface.calling_convention() != "sysv_amd64"
        || !interface.stack_slots().is_empty()
        || types.types().len() != 1
        || !types.aggregates().is_empty()
        || types.types()[0].kind() != SourceTypeKind::SignedInteger
        || types.types()[0].size_bits() != 32
        || types.types()[0].align_bits() != 32
        || !parameters_are_exact
        || !interface
            .parameter_logical_values()
            .iter()
            .all(logical_is_signed32)
        || interface
            .return_logical_value()
            .is_none_or(|logical| !logical_is_signed32(&logical))
        || !return_is_exact
    {
        return Err(BranchlessGuardSemanticCFunctionError::InvalidInterface);
    }
    Ok(BranchlessGuardAbiManifest {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        parameters: certificate.parameters().to_vec().into_boxed_slice(),
        return_storage: certificate.return_storage(),
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
pub struct BranchlessGuardSemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl BranchlessGuardSemanticCFunctionAuditReport {
    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn has_exact_branchless_guard_function(&self) -> bool {
        self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum BranchlessGuardDifferentialInput {
    Simple { value: i32 },
    Dual { first: i32, second: i32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct BranchlessGuardDifferentialCase {
    input: BranchlessGuardDifferentialInput,
    source_result: i32,
    candidate_result: i32,
}

impl BranchlessGuardDifferentialCase {
    pub const fn input(&self) -> BranchlessGuardDifferentialInput {
        self.input
    }

    pub const fn source_result(&self) -> i32 {
        self.source_result
    }

    pub const fn candidate_result(&self) -> i32 {
        self.candidate_result
    }

    pub const fn matches(&self) -> bool {
        self.source_result == self.candidate_result
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BranchlessGuardDifferentialReport {
    cases: Box<[BranchlessGuardDifferentialCase]>,
}

impl BranchlessGuardDifferentialReport {
    pub const fn cases(&self) -> &[BranchlessGuardDifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty()
            && self
                .cases
                .iter()
                .all(BranchlessGuardDifferentialCase::matches)
    }
}

/// Compare a freshly certified source evaluator with the independently stored
/// strict-C candidate evaluator over a caller-bounded input sequence.
pub fn check_branchless_guard_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedBranchlessGuardSemanticCFunction,
    inputs: impl IntoIterator<Item = BranchlessGuardDifferentialInput>,
) -> Result<BranchlessGuardDifferentialReport, BranchlessGuardSemanticCFunctionError> {
    let audit = candidate.audit();
    if !audit.has_exact_branchless_guard_function() {
        return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
            audit.invalid,
        ));
    }
    let source = certify_branchless_guard_function(artifact)?
        .ok_or(BranchlessGuardSemanticCFunctionError::MissingBranchlessGuardCertificate)?;
    if source.origin() != candidate.origin() || source != *candidate.certificate() {
        return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
            vec!["differential source and candidate certificates differ".to_string()],
        ));
    }
    expected_abi(&source)?;
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.is_empty() {
        return Err(BranchlessGuardSemanticCFunctionError::EmptyDifferential);
    }
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(BranchlessGuardSemanticCFunctionError::TooManyDifferentialCases(inputs.len()));
    }
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        let source_result = evaluate_source(artifact, &source, input)?;
        let candidate_result = evaluate_candidate(candidate.program, input)?;
        cases.push(BranchlessGuardDifferentialCase {
            input,
            source_result,
            candidate_result,
        });
    }
    let report = BranchlessGuardDifferentialReport {
        cases: cases.into_boxed_slice(),
    };
    if !report.has_equivalence() {
        let mismatch = report
            .cases()
            .iter()
            .find(|case| !case.matches())
            .expect("non-equivalent report has a mismatch");
        return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
            vec![format!(
                "source and strict-C branchless-guard evaluators disagree for {:?}: source {}, candidate {}",
                mismatch.input(),
                mismatch.source_result(),
                mismatch.candidate_result()
            )],
        ));
    }
    Ok(report)
}

fn evaluate_source(
    artifact: &SsaArtifact,
    certificate: &CertifiedBranchlessGuardFunction,
    input: BranchlessGuardDifferentialInput,
) -> Result<i32, BranchlessGuardSemanticCFunctionError> {
    let input_bits = match (certificate.kind(), input) {
        (
            CertifiedBranchlessGuardKind::SimpleSubtractEqual { .. },
            BranchlessGuardDifferentialInput::Simple { value },
        ) => vec![value as u32],
        (
            CertifiedBranchlessGuardKind::DualWrap32XorOrEqual { .. },
            BranchlessGuardDifferentialInput::Dual { first, second },
        ) => vec![first as u32, second as u32],
        _ => return Err(BranchlessGuardSemanticCFunctionError::WrongDifferentialInputKind),
    };
    let overrides = certificate
        .parameters()
        .iter()
        .zip(input_bits)
        .map(|(parameter, bits)| {
            (
                parameter.low32_value(),
                DifferentialBitVector::new(32, u64::from(bits)).expect("32-bit differential input"),
            )
        });
    let returned =
        execute_prepared_single_block_return(artifact, overrides, 128).map_err(|reason| {
            BranchlessGuardSemanticCFunctionError::InvalidComposition(vec![reason])
        })?;
    let [returned] = returned.as_ref() else {
        return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
            vec!["prepared branchless source did not return exactly one value".to_string()],
        ));
    };
    if returned.bits() > 1 {
        return Err(BranchlessGuardSemanticCFunctionError::InvalidComposition(
            vec!["prepared branchless source returned a non-boolean value".to_string()],
        ));
    }
    Ok(returned.bits() as i32)
}

fn evaluate_candidate(
    program: BranchlessGuardRenderProgram,
    input: BranchlessGuardDifferentialInput,
) -> Result<i32, BranchlessGuardSemanticCFunctionError> {
    match (program, input) {
        (
            BranchlessGuardRenderProgram::SimpleSubtractEqual { expected },
            BranchlessGuardDifferentialInput::Simple { value },
        ) => Ok(i32::from((value as u32) == expected)),
        (
            BranchlessGuardRenderProgram::DualWrap32XorOrEqual {
                sum_expected,
                difference_expected,
            },
            BranchlessGuardDifferentialInput::Dual { first, second },
        ) => {
            let first = first as u32;
            let second = second as u32;
            Ok(i32::from(
                first.wrapping_add(second) == sum_expected
                    && first.wrapping_sub(second) == difference_expected,
            ))
        }
        _ => Err(BranchlessGuardSemanticCFunctionError::WrongDifferentialInputKind),
    }
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
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierProjection,
        SourceFunctionInterface, SourceLogicalValue, SourceType, SourceTypeGraph,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(7);
    const ENTRY: u64 = 0x1000;

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

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-branchless-guard-render-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("AL", 0, 1),
            ("EAX", 0, 4),
            ("RAX", 0, 8),
            ("ECX", 8, 4),
            ("RCX", 8, 8),
            ("RSP", 32, 8),
            ("RBP", 40, 8),
            ("ESI", 48, 4),
            ("RSI", 48, 8),
            ("EDI", 56, 4),
            ("RDI", 56, 8),
            ("CF", 512, 1),
            ("PF", 514, 1),
            ("ZF", 518, 1),
            ("SF", 519, 1),
            ("OF", 523, 1),
            ("RIP", 648, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn interface(parameter_count: usize, revision: &[u8]) -> SourceFunctionInterface {
        let types = SourceTypeGraph::new(
            [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
            [],
        )
        .expect("signed int type graph");
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "sysv_amd64",
            [storage(56), storage(48)]
                .into_iter()
                .take(parameter_count)
                .enumerate()
                .map(|(index, storage)| SourceAbiParameterSpec::new(index as u32, storage)),
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            (0..parameter_count).map(|_| SourceLogicalValue::new(0, low32)),
            Some(SourceLogicalValue::new(0, low32)),
            Some(types),
        )
        .expect("exact branchless interface")
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

    fn push_flag_packet(block: &mut R2ILBlock, next: &mut u64, value: Varnode) {
        block.push(R2ILOp::IntSLess {
            dst: register(519, 1),
            a: value.clone(),
            b: constant(0, 4),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(518, 1),
            a: value.clone(),
            b: constant(0, 4),
        });
        let low = unique(next, 4);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: value,
            b: constant(0xff, 4),
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
            dst: register(514, 1),
            a: parity,
            b: constant(0, 1),
        });
    }

    fn push_zero_flags(block: &mut R2ILBlock) {
        block.push(R2ILOp::Copy {
            dst: register(512, 1),
            src: constant(0, 1),
        });
        block.push(R2ILOp::Copy {
            dst: register(523, 1),
            src: constant(0, 1),
        });
    }

    fn push_frame_suffix(block: &mut R2ILBlock, next: &mut u64) {
        let restored = unique(next, 8);
        block.push(R2ILOp::Copy {
            dst: restored.clone(),
            src: constant(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: restored,
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
            src: Varnode::unique(next.saturating_sub(0x80), 8),
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

    fn simple_block(entry: u64, expected: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 17);
        let mut next = 0x10000;
        push_frame_prefix(&mut block, &mut next);
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(0, 4),
            a: register(0, 4),
            b: register(0, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(0, 8),
            src: register(0, 4),
        });
        push_flag_packet(&mut block, &mut next, register(0, 4));
        let copied = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: register(56, 4),
        });
        block.push(R2ILOp::IntLess {
            dst: register(512, 1),
            a: copied.clone(),
            b: constant(expected, 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: register(523, 1),
            a: copied.clone(),
            b: constant(expected, 4),
        });
        let difference = unique(&mut next, 4);
        block.push(R2ILOp::IntSub {
            dst: difference.clone(),
            a: copied,
            b: constant(expected, 4),
        });
        push_flag_packet(&mut block, &mut next, difference);
        block.push(R2ILOp::Copy {
            dst: register(0, 1),
            src: register(518, 1),
        });
        push_frame_suffix(&mut block, &mut next);
        block
    }

    fn dual_block(entry: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 24);
        let mut next = 0x20000;
        push_frame_prefix(&mut block, &mut next);
        let scaled = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: scaled.clone(),
            a: register(56, 8),
            b: constant(1, 8),
        });
        let sum64 = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: sum64.clone(),
            a: register(48, 8),
            b: scaled,
        });
        block.push(R2ILOp::Subpiece {
            dst: register(8, 4),
            src: sum64,
            offset: 0,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(8, 8),
            src: register(8, 4),
        });
        block.push(R2ILOp::IntLess {
            dst: register(512, 1),
            a: register(56, 4),
            b: register(48, 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: register(523, 1),
            a: register(56, 4),
            b: register(48, 4),
        });
        block.push(R2ILOp::IntSub {
            dst: register(56, 4),
            a: register(56, 4),
            b: register(48, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(56, 8),
            src: register(56, 4),
        });
        push_flag_packet(&mut block, &mut next, register(56, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(8, 4),
            a: register(8, 4),
            b: constant(100, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(8, 8),
            src: register(8, 4),
        });
        push_flag_packet(&mut block, &mut next, register(8, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(56, 4),
            a: register(56, 4),
            b: constant(20, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(56, 8),
            src: register(56, 4),
        });
        push_flag_packet(&mut block, &mut next, register(56, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(0, 4),
            a: register(0, 4),
            b: register(0, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(0, 8),
            src: register(0, 4),
        });
        push_flag_packet(&mut block, &mut next, register(0, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntOr {
            dst: register(56, 4),
            a: register(56, 4),
            b: register(8, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(56, 8),
            src: register(56, 4),
        });
        push_flag_packet(&mut block, &mut next, register(56, 4));
        block.push(R2ILOp::Copy {
            dst: register(0, 1),
            src: register(518, 1),
        });
        push_frame_suffix(&mut block, &mut next);
        block
    }

    fn artifact(block: R2ILBlock, parameter_count: usize, revision: &[u8]) -> SsaArtifact {
        SsaArtifact::raw_with_interface(
            &[block],
            Some(&arch()),
            interface(parameter_count, revision),
        )
        .expect("branchless guard artifact")
    }

    fn simple_artifact(expected: u64) -> SsaArtifact {
        artifact(
            simple_block(ENTRY, expected),
            1,
            b"branchless-render-revision-1",
        )
    }

    fn dual_artifact() -> SsaArtifact {
        artifact(dual_block(ENTRY), 2, b"branchless-render-revision-1")
    }

    fn simple_probes() -> Vec<BranchlessGuardDifferentialInput> {
        let mut probes = [i32::MIN, i32::MAX, -1, 0, 1, 0xdead]
            .into_iter()
            .map(|value| BranchlessGuardDifferentialInput::Simple { value })
            .collect::<Vec<_>>();
        let mut state = 0x243f_6a88_85a3_08d3_u64;
        for _ in 0..96 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            probes.push(BranchlessGuardDifferentialInput::Simple {
                value: (state >> 32) as u32 as i32,
            });
        }
        probes
    }

    fn dual_probes() -> Vec<BranchlessGuardDifferentialInput> {
        let mut probes = [
            (i32::MIN, i32::MIN),
            (i32::MIN, i32::MAX),
            (i32::MAX, i32::MIN),
            (i32::MAX, i32::MAX),
            (-1, 0),
            (0, -1),
            (0, 0),
            (1, 1),
            (60, 40),
            (0x8000_003c_u32 as i32, 0x8000_0028_u32 as i32),
        ]
        .into_iter()
        .map(|(first, second)| BranchlessGuardDifferentialInput::Dual { first, second })
        .collect::<Vec<_>>();
        let mut state = 0x1319_8a2e_0370_7344_u64;
        for _ in 0..128 {
            state = state
                .wrapping_mul(2862933555777941757)
                .wrapping_add(3037000493);
            let first = (state >> 32) as u32 as i32;
            state = state
                .wrapping_mul(2862933555777941757)
                .wrapping_add(3037000493);
            let second = (state >> 32) as u32 as i32;
            probes.push(BranchlessGuardDifferentialInput::Dual { first, second });
        }
        probes
    }

    fn c_i32(value: i32) -> String {
        if value == i32::MIN {
            "INT32_MIN".to_string()
        } else {
            format!("INT32_C({value})")
        }
    }

    fn compiled_results(
        function: &CertifiedBranchlessGuardSemanticCFunction,
        probes: &[BranchlessGuardDifferentialInput],
    ) -> Vec<i32> {
        let function = function
            .clone()
            .with_cosmetic_names("probe", "input", "input");
        let mut source = function.render_certified_c().expect("strict guard C");
        source.push_str("\n#include <inttypes.h>\n#include <stdio.h>\n\nint main(void) {\n");
        for probe in probes {
            match probe {
                BranchlessGuardDifferentialInput::Simple { value } => {
                    writeln!(
                        &mut source,
                        "\tprintf(\"%\" PRId32 \"\\n\", r2s_fn_probe({}));",
                        c_i32(*value)
                    )
                    .expect("String writes cannot fail");
                }
                BranchlessGuardDifferentialInput::Dual { first, second } => {
                    writeln!(
                        &mut source,
                        "\tprintf(\"%\" PRId32 \"\\n\", r2s_fn_probe({}, {}));",
                        c_i32(*first),
                        c_i32(*second)
                    )
                    .expect("String writes cannot fail");
                }
            }
        }
        source.push_str("\treturn 0;\n}\n");

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "r2dec-branchless-guard-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&directory).expect("temporary directory");
        let source_path = directory.join("probe.c");
        let executable = directory.join("probe");
        fs::write(&source_path, source).expect("C source");
        let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
        let status = Command::new(compiler)
            .args(["-std=c11", "-Wall", "-Wextra", "-Wpedantic", "-Werror"])
            .arg(&source_path)
            .arg("-o")
            .arg(&executable)
            .status()
            .expect("C compiler");
        assert!(status.success());
        let output = Command::new(&executable)
            .output()
            .expect("compiled C probe");
        assert!(output.status.success());
        let results = String::from_utf8(output.stdout)
            .expect("UTF-8 output")
            .lines()
            .map(|line| line.parse::<i32>().expect("integer output"))
            .collect();
        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_file(&executable);
        let _ = fs::remove_dir(&directory);
        results
    }

    fn assert_refused(function: &CertifiedBranchlessGuardSemanticCFunction) {
        assert!(!function.audit().has_exact_branchless_guard_function());
        assert!(function.render_certified_c().is_err());
    }

    #[test]
    fn exact_simple_and_dual_certificates_emit_signed_32_c11() {
        let simple =
            CertifiedBranchlessGuardSemanticCFunction::from_artifact(&simple_artifact(0xdead))
                .expect("simple semantic C");
        assert!(simple.audit().has_exact_branchless_guard_function());
        let simple_c = simple.render_certified_c().expect("simple C");
        assert!(
            simple_c.contains("int32_t r2s_fn_certified_branchless_guard(int32_t r2s_arg0_first)")
        );
        assert!(simple_c.contains("(uint32_t)r2s_arg0_first == UINT32_C(0xdead)"));

        let dual = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&dual_artifact())
            .expect("dual semantic C");
        assert!(dual.audit().has_exact_branchless_guard_function());
        let dual_c = dual.render_certified_c().expect("dual C");
        assert!(dual_c.contains("int32_t r2s_fn_certified_branchless_guard(int32_t r2s_arg0_first, int32_t r2s_arg1_second)"));
        assert!(dual_c.contains("uint32_t sum_bits"));
        assert!(dual_c.contains("uint32_t difference_bits"));
        assert!(dual_c.contains("UINT32_C(0x64)"));
        assert!(dual_c.contains("UINT32_C(0x14)"));
        assert!(!dual_c.contains("(int32_t)sum_bits"));
        assert!(!dual_c.contains("(int32_t)difference_bits"));
    }

    #[test]
    fn independent_evaluators_cover_boundaries_solutions_and_seeded_random() {
        let simple_artifact = simple_artifact(0xdead);
        let simple = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&simple_artifact)
            .expect("simple semantic C");
        let simple_report =
            check_branchless_guard_differential(&simple_artifact, &simple, simple_probes())
                .expect("simple differential");
        assert!(simple_report.has_equivalence());
        assert_eq!(
            simple_report
                .cases()
                .iter()
                .filter(|case| case.source_result() == 1)
                .count(),
            1
        );

        let dual_artifact = dual_artifact();
        let dual = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&dual_artifact)
            .expect("dual semantic C");
        let dual_report = check_branchless_guard_differential(&dual_artifact, &dual, dual_probes())
            .expect("dual differential");
        assert!(dual_report.has_equivalence());
        assert!(
            dual_report
                .cases()
                .iter()
                .any(|case| case.source_result() == 1)
        );
    }

    #[test]
    fn emitted_c_compiles_and_matches_boundary_and_seeded_random_probes() {
        for (artifact, probes) in [
            (simple_artifact(0xdead), simple_probes()),
            (dual_artifact(), dual_probes()),
        ] {
            let function = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&artifact)
                .expect("semantic C");
            let expected =
                check_branchless_guard_differential(&artifact, &function, probes.clone())
                    .expect("differential")
                    .cases()
                    .iter()
                    .map(BranchlessGuardDifferentialCase::source_result)
                    .collect::<Vec<_>>();
            assert_eq!(compiled_results(&function, &probes), expected);
        }
    }

    #[test]
    fn program_permit_certificate_and_foreign_source_mutations_fail_closed() {
        let source_artifact = simple_artifact(0xdead);
        let function = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&source_artifact)
            .expect("simple semantic C");

        let mut program = function.clone();
        program.program = BranchlessGuardRenderProgram::SimpleSubtractEqual { expected: 0xdeac };
        assert_refused(&program);

        let mut permit = function.clone();
        permit.render_permit.contract_version ^= 1;
        assert_refused(&permit);

        let foreign_artifact = simple_artifact(0xbeef);
        let foreign = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&foreign_artifact)
            .expect("foreign semantic C");
        let mut swapped = function.clone();
        swapped.certificate = foreign.certificate;
        assert_refused(&swapped);
        assert!(
            check_branchless_guard_differential(&foreign_artifact, &function, simple_probes())
                .is_err()
        );

        let mut unsupported = simple_block(ENTRY, 0xdead);
        unsupported.ops.insert(
            24,
            R2ILOp::IntAdd {
                dst: Varnode::unique(0xfeed, 4),
                a: constant(1, 4),
                b: constant(2, 4),
            },
        );
        let unsupported = artifact(unsupported, 1, b"branchless-render-revision-1");
        assert!(matches!(
            CertifiedBranchlessGuardSemanticCFunction::from_artifact(&unsupported),
            Err(BranchlessGuardSemanticCFunctionError::MissingBranchlessGuardCertificate)
        ));
    }

    #[test]
    fn differential_bounds_arity_and_cosmetic_names_are_non_authoritative() {
        let artifact = simple_artifact(0xdead);
        let function = CertifiedBranchlessGuardSemanticCFunction::from_artifact(&artifact)
            .expect("simple semantic C")
            .with_cosmetic_names("!", "same", "same");
        assert!(function.audit().has_exact_branchless_guard_function());
        assert!(
            function
                .render_certified_c()
                .expect("renamed C")
                .contains("r2s_fn__")
        );
        assert!(matches!(
            check_branchless_guard_differential(&artifact, &function, []),
            Err(BranchlessGuardSemanticCFunctionError::EmptyDifferential)
        ));
        assert!(matches!(
            check_branchless_guard_differential(
                &artifact,
                &function,
                (0..=MAX_DIFFERENTIAL_CASES)
                    .map(|_| BranchlessGuardDifferentialInput::Simple { value: 0 }),
            ),
            Err(BranchlessGuardSemanticCFunctionError::TooManyDifferentialCases(_))
        ));
        assert!(matches!(
            check_branchless_guard_differential(
                &artifact,
                &function,
                [BranchlessGuardDifferentialInput::Dual {
                    first: 0,
                    second: 0,
                }],
            ),
            Err(BranchlessGuardSemanticCFunctionError::WrongDifferentialInputKind)
        ));
    }
}
