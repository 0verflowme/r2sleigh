//! Strict typed-semantic-C rendering for the sealed x86-64 O0 nested wrap32 guard.
//!
//! Admission depends only on the opaque r2cert certificate and its immutable
//! origin. Presentation names are cosmetic. The differential harness executes
//! the retained prepared SSA directly and compares it with an independent
//! interpreter for the typed render AST under explicit step and case bounds.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedNestedWrap32GuardO0DispositionClass, CertifiedNestedWrap32GuardO0Function,
    CertifiedNestedWrap32GuardO0InstructionDisposition, certify_nested_wrap32_guard_o0_function,
};
use r2ssa::{
    BlockTerminator, CanonicalStorageSpace, MachineBuildError, MachineMemoryEndianness, SSAOp,
    SSAVar, SemanticObligationId, SourceCarrierKind, SourceFunctionReturn, SourceTypeKind,
    SsaArtifact, StackAddressBase, ValueId,
};
use serde::Serialize;

use crate::semantic_differential::DifferentialBitVector;

pub const CERTIFIED_NESTED_WRAP32_GUARD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION;

const MAX_DIFFERENTIAL_CASES: usize = 512;
const MAX_SOURCE_BLOCK_STEPS: u32 = 8;
const MAX_SOURCE_INSTRUCTION_STEPS: u32 = 256;
const MAX_TYPED_STATEMENT_STEPS: u32 = 16;
const STACK_POINTER_OFFSET: u64 = 32;
const FRAME_POINTER_OFFSET: u64 = 40;
const STACK_BASE: u64 = 0x10_0000;
const FRAME_BASE: u64 = 0x20_0000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum NestedWrap32GuardO0SemanticCFunctionScope {
    ClosedSixBlockX86_64O0NestedWrap32Guard,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NestedWrap32GuardO0AbiManifest {
    revision_identity: Box<[u8]>,
    parameter_values: [ValueId; 2],
    return_storage: r2ssa::CanonicalStorageId,
}

impl NestedWrap32GuardO0AbiManifest {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameter_values(&self) -> [ValueId; 2] {
        self.parameter_values
    }

    pub const fn return_storage(&self) -> r2ssa::CanonicalStorageId {
        self.return_storage
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NestedWrap32GuardO0RenderNames {
    function: String,
    first: String,
    second: String,
}

impl NestedWrap32GuardO0RenderNames {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NestedWrap32GuardO0TypedScalar {
    SignedI32,
    UnsignedI32,
    Boolean,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NestedWrap32GuardO0TypedBinding {
    FirstBits,
    SecondBits,
    SumBits,
    DifferenceBits,
}

impl NestedWrap32GuardO0TypedBinding {
    const fn ty(self) -> NestedWrap32GuardO0TypedScalar {
        NestedWrap32GuardO0TypedScalar::UnsignedI32
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum NestedWrap32GuardO0TypedExpr {
    ParameterBits {
        index: u32,
    },
    Binding {
        binding: NestedWrap32GuardO0TypedBinding,
    },
    WrapAdd {
        left: NestedWrap32GuardO0TypedBinding,
        right: NestedWrap32GuardO0TypedBinding,
    },
    WrapSubtract {
        left: NestedWrap32GuardO0TypedBinding,
        right: NestedWrap32GuardO0TypedBinding,
    },
    NotEqualU32 {
        value: NestedWrap32GuardO0TypedBinding,
        expected: u32,
    },
    SignedI32Constant {
        value: i32,
    },
}

impl NestedWrap32GuardO0TypedExpr {
    pub const fn ty(&self) -> NestedWrap32GuardO0TypedScalar {
        match self {
            Self::ParameterBits { .. }
            | Self::Binding { .. }
            | Self::WrapAdd { .. }
            | Self::WrapSubtract { .. } => NestedWrap32GuardO0TypedScalar::UnsignedI32,
            Self::NotEqualU32 { .. } => NestedWrap32GuardO0TypedScalar::Boolean,
            Self::SignedI32Constant { .. } => NestedWrap32GuardO0TypedScalar::SignedI32,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum NestedWrap32GuardO0TypedStatement {
    Let {
        binding: NestedWrap32GuardO0TypedBinding,
        value: NestedWrap32GuardO0TypedExpr,
    },
    If {
        condition: NestedWrap32GuardO0TypedExpr,
        then_body: Box<[NestedWrap32GuardO0TypedStatement]>,
        else_body: Box<[NestedWrap32GuardO0TypedStatement]>,
    },
    Return {
        value: NestedWrap32GuardO0TypedExpr,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NestedWrap32GuardO0TypedProgram {
    parameter_types: [NestedWrap32GuardO0TypedScalar; 2],
    return_type: NestedWrap32GuardO0TypedScalar,
    body: Box<[NestedWrap32GuardO0TypedStatement]>,
}

impl NestedWrap32GuardO0TypedProgram {
    pub const fn parameter_types(&self) -> [NestedWrap32GuardO0TypedScalar; 2] {
        self.parameter_types
    }

    pub const fn return_type(&self) -> NestedWrap32GuardO0TypedScalar {
        self.return_type
    }

    pub const fn body(&self) -> &[NestedWrap32GuardO0TypedStatement] {
        &self.body
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct NestedWrap32GuardO0RenderPermit {
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedNestedWrap32GuardO0Function,
    instructions: Box<[CertifiedNestedWrap32GuardO0InstructionDisposition]>,
    obligations: Box<
        [(
            SemanticObligationId,
            CertifiedNestedWrap32GuardO0DispositionClass,
        )],
    >,
}

impl NestedWrap32GuardO0RenderPermit {
    fn new(certificate: &CertifiedNestedWrap32GuardO0Function) -> Self {
        Self {
            contract_version: CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION,
            origin: certificate.origin().clone(),
            certificate: certificate.clone(),
            instructions: certificate
                .instruction_dispositions()
                .to_vec()
                .into_boxed_slice(),
            obligations: certificate
                .obligation_dispositions()
                .to_vec()
                .into_boxed_slice(),
        }
    }

    fn matches(&self, certificate: &CertifiedNestedWrap32GuardO0Function) -> bool {
        self.contract_version == CERTIFIED_NESTED_WRAP32_GUARD_O0_CONTRACT_VERSION
            && self.origin == *certificate.origin()
            && self.certificate == *certificate
            && self.instructions.as_ref() == certificate.instruction_dispositions()
            && self.obligations.as_ref() == certificate.obligation_dispositions()
            && certificate.validate(self.origin.source())
            && self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNestedWrap32GuardO0SemanticCFunction {
    schema_version: u32,
    scope: NestedWrap32GuardO0SemanticCFunctionScope,
    names: NestedWrap32GuardO0RenderNames,
    origin: CertifiedArtifactOrigin,
    certificate: CertifiedNestedWrap32GuardO0Function,
    abi: NestedWrap32GuardO0AbiManifest,
    sealed_program: NestedWrap32GuardO0TypedProgram,
    program: NestedWrap32GuardO0TypedProgram,
    render_permit: NestedWrap32GuardO0RenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum NestedWrap32GuardO0SemanticCFunctionError {
    Machine(MachineBuildError),
    MissingCertificate,
    InvalidInterface,
    EmptyDifferential,
    TooManyDifferentialCases(usize),
    DifferentialBudgetExceeded,
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for NestedWrap32GuardO0SemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "nested wrap32 O0 semantic C function failed: {self:?}")
    }
}

impl std::error::Error for NestedWrap32GuardO0SemanticCFunctionError {}

impl From<MachineBuildError> for NestedWrap32GuardO0SemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl CertifiedNestedWrap32GuardO0SemanticCFunction {
    /// The only admission path recollects the exact artifact-bound certificate.
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, NestedWrap32GuardO0SemanticCFunctionError> {
        let certificate = certify_nested_wrap32_guard_o0_function(artifact)?
            .ok_or(NestedWrap32GuardO0SemanticCFunctionError::MissingCertificate)?;
        if !certificate.validate_against_artifact(artifact) {
            return Err(
                NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                    "nested wrap32 certificate recollection failed".to_string(),
                ]),
            );
        }
        let abi = expected_abi(&certificate)?;
        let program = expected_program(&certificate)?;
        let render_permit = NestedWrap32GuardO0RenderPermit::new(&certificate);
        let function = Self {
            schema_version: CERTIFIED_NESTED_WRAP32_GUARD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope:
                NestedWrap32GuardO0SemanticCFunctionScope::ClosedSixBlockX86_64O0NestedWrap32Guard,
            names: NestedWrap32GuardO0RenderNames {
                function: "certified_nested_wrap32_guard_o0".to_string(),
                first: "first".to_string(),
                second: "second".to_string(),
            },
            origin: certificate.origin().clone(),
            certificate,
            abi,
            sealed_program: program.clone(),
            program,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_nested_wrap32_guard_o0_function() {
            return Err(
                NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(report.invalid),
            );
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> NestedWrap32GuardO0SemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &NestedWrap32GuardO0RenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn certificate(&self) -> &CertifiedNestedWrap32GuardO0Function {
        &self.certificate
    }

    pub const fn abi(&self) -> &NestedWrap32GuardO0AbiManifest {
        &self.abi
    }

    pub const fn typed_program(&self) -> &NestedWrap32GuardO0TypedProgram {
        &self.program
    }

    pub fn with_cosmetic_names(
        mut self,
        function: impl Into<String>,
        first: impl Into<String>,
        second: impl Into<String>,
    ) -> Self {
        self.names = NestedWrap32GuardO0RenderNames {
            function: function.into(),
            first: first.into(),
            second: second.into(),
        };
        self
    }

    pub fn audit(&self) -> NestedWrap32GuardO0SemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version
            != CERTIFIED_NESTED_WRAP32_GUARD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION
        {
            invalid.push("nested wrap32 renderer schema mismatch".to_string());
        }
        if self.scope
            != NestedWrap32GuardO0SemanticCFunctionScope::ClosedSixBlockX86_64O0NestedWrap32Guard
        {
            invalid.push("nested wrap32 renderer scope mismatch".to_string());
        }
        if self.certificate.origin() != &self.origin
            || !self.certificate.validate(self.origin.source())
            || !self
                .origin
                .matches_retained_source(self.origin.source(), self.origin.topology())
        {
            invalid.push("nested wrap32 certificate or origin mismatch".to_string());
        }
        match expected_abi(&self.certificate) {
            Ok(expected) if expected == self.abi => {}
            _ => invalid.push("nested wrap32 signed-i32 ABI manifest mismatch".to_string()),
        }
        match expected_program(&self.certificate) {
            Ok(expected) if expected == self.program && expected == self.sealed_program => {}
            _ => invalid.push("nested wrap32 typed render program mismatch".to_string()),
        }
        if !typed_program_is_well_formed(&self.program) {
            invalid.push("nested wrap32 typed render program is ill-typed".to_string());
        }
        if !self.render_permit.matches(&self.certificate) {
            invalid.push("nested wrap32 render permit mismatch".to_string());
        }
        NestedWrap32GuardO0SemanticCFunctionAuditReport { invalid }
    }

    pub fn render_certified_c(&self) -> Result<String, NestedWrap32GuardO0SemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_nested_wrap32_guard_o0_function() {
            return Err(
                NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(report.invalid),
            );
        }
        let function = c_identifier("r2s_fn", &self.names.function);
        let parameters = [
            c_identifier("r2s_arg0", &self.names.first),
            c_identifier("r2s_arg1", &self.names.second),
        ];
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        writeln!(
            &mut output,
            "int32_t {function}(int32_t {}, int32_t {}) {{",
            parameters[0], parameters[1]
        )
        .expect("String writes cannot fail");
        render_statements(&mut output, self.program.body(), &parameters, 1)?;
        output.push_str("}\n");
        Ok(output)
    }
}

fn expected_abi(
    certificate: &CertifiedNestedWrap32GuardO0Function,
) -> Result<NestedWrap32GuardO0AbiManifest, NestedWrap32GuardO0SemanticCFunctionError> {
    let interface = certificate
        .origin()
        .machine_context()
        .source()
        .function_interface()
        .ok_or(NestedWrap32GuardO0SemanticCFunctionError::InvalidInterface)?;
    let types = interface
        .type_graph()
        .ok_or(NestedWrap32GuardO0SemanticCFunctionError::InvalidInterface)?;
    let [integer] = types.types() else {
        return Err(NestedWrap32GuardO0SemanticCFunctionError::InvalidInterface);
    };
    let parameters = certificate.abi().parameters();
    let logical_is_signed32 = |logical: &r2ssa::SourceLogicalValue| {
        logical.type_id() == 0
            && logical.carrier().kind() == SourceCarrierKind::LowBits
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == 32
    };
    if interface.revision_identity() != certificate.abi().revision_identity()
        || interface.calling_convention() != "sysv_amd64"
        || interface.parameters().len() != 2
        || interface.parameter_logical_values().len() != 2
        || parameters.len() != 2
        || parameters
            .iter()
            .enumerate()
            .any(|(index, parameter)| parameter.index() != index as u32)
        || !interface
            .parameter_logical_values()
            .iter()
            .all(logical_is_signed32)
        || interface
            .return_logical_value()
            .is_none_or(|logical| !logical_is_signed32(&logical))
        || interface.return_kind()
            != (SourceFunctionReturn::Register {
                storage: certificate.abi().return_storage(),
            })
        || types.types().len() != 1
        || !types.aggregates().is_empty()
        || integer.kind() != SourceTypeKind::SignedInteger
        || integer.size_bits() != 32
        || integer.align_bits() != 32
        || !interface.stack_slot_roles_complete()
        || interface.stack_slots().len() != 4
        || interface
            .stack_slots()
            .iter()
            .any(|slot| slot.base() != StackAddressBase::FramePointer || slot.size_bytes() != 4)
        || certificate
            .origin()
            .machine_context()
            .memory_model()
            .default_endianness()
            != MachineMemoryEndianness::Little
    {
        return Err(NestedWrap32GuardO0SemanticCFunctionError::InvalidInterface);
    }
    Ok(NestedWrap32GuardO0AbiManifest {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        parameter_values: [parameters[0].low32_value(), parameters[1].low32_value()],
        return_storage: certificate.abi().return_storage(),
    })
}

fn expected_program(
    certificate: &CertifiedNestedWrap32GuardO0Function,
) -> Result<NestedWrap32GuardO0TypedProgram, NestedWrap32GuardO0SemanticCFunctionError> {
    if certificate.sum().wraps_at_bits() != 32
        || certificate.difference().wraps_at_bits() != 32
        || certificate.failure_phis().phis().len() != 13
        || certificate.exit_phis().phis().len() != 14
    {
        return Err(
            NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                "nested wrap32 arithmetic or phi contract mismatch".to_string(),
            ]),
        );
    }
    let failure = || NestedWrap32GuardO0TypedStatement::Return {
        value: NestedWrap32GuardO0TypedExpr::SignedI32Constant { value: 0 },
    };
    let success = NestedWrap32GuardO0TypedStatement::Return {
        value: NestedWrap32GuardO0TypedExpr::SignedI32Constant { value: 1 },
    };
    let second_guard = NestedWrap32GuardO0TypedStatement::If {
        condition: NestedWrap32GuardO0TypedExpr::NotEqualU32 {
            value: NestedWrap32GuardO0TypedBinding::DifferenceBits,
            expected: certificate.difference_comparison().expected(),
        },
        then_body: vec![failure()].into_boxed_slice(),
        else_body: vec![success].into_boxed_slice(),
    };
    let first_guard = NestedWrap32GuardO0TypedStatement::If {
        condition: NestedWrap32GuardO0TypedExpr::NotEqualU32 {
            value: NestedWrap32GuardO0TypedBinding::SumBits,
            expected: certificate.sum_comparison().expected(),
        },
        then_body: vec![failure()].into_boxed_slice(),
        else_body: vec![
            NestedWrap32GuardO0TypedStatement::Let {
                binding: NestedWrap32GuardO0TypedBinding::DifferenceBits,
                value: NestedWrap32GuardO0TypedExpr::WrapSubtract {
                    left: NestedWrap32GuardO0TypedBinding::FirstBits,
                    right: NestedWrap32GuardO0TypedBinding::SecondBits,
                },
            },
            second_guard,
        ]
        .into_boxed_slice(),
    };
    Ok(NestedWrap32GuardO0TypedProgram {
        parameter_types: [
            NestedWrap32GuardO0TypedScalar::SignedI32,
            NestedWrap32GuardO0TypedScalar::SignedI32,
        ],
        return_type: NestedWrap32GuardO0TypedScalar::SignedI32,
        body: vec![
            NestedWrap32GuardO0TypedStatement::Let {
                binding: NestedWrap32GuardO0TypedBinding::FirstBits,
                value: NestedWrap32GuardO0TypedExpr::ParameterBits { index: 0 },
            },
            NestedWrap32GuardO0TypedStatement::Let {
                binding: NestedWrap32GuardO0TypedBinding::SecondBits,
                value: NestedWrap32GuardO0TypedExpr::ParameterBits { index: 1 },
            },
            NestedWrap32GuardO0TypedStatement::Let {
                binding: NestedWrap32GuardO0TypedBinding::SumBits,
                value: NestedWrap32GuardO0TypedExpr::WrapAdd {
                    left: NestedWrap32GuardO0TypedBinding::FirstBits,
                    right: NestedWrap32GuardO0TypedBinding::SecondBits,
                },
            },
            first_guard,
        ]
        .into_boxed_slice(),
    })
}

fn typed_program_is_well_formed(program: &NestedWrap32GuardO0TypedProgram) -> bool {
    if program.parameter_types
        != [
            NestedWrap32GuardO0TypedScalar::SignedI32,
            NestedWrap32GuardO0TypedScalar::SignedI32,
        ]
        || program.return_type != NestedWrap32GuardO0TypedScalar::SignedI32
    {
        return false;
    }
    fn statements_are_typed(statements: &[NestedWrap32GuardO0TypedStatement]) -> bool {
        statements.iter().all(|statement| match statement {
            NestedWrap32GuardO0TypedStatement::Let { binding, value } => binding.ty() == value.ty(),
            NestedWrap32GuardO0TypedStatement::If {
                condition,
                then_body,
                else_body,
            } => {
                condition.ty() == NestedWrap32GuardO0TypedScalar::Boolean
                    && !then_body.is_empty()
                    && !else_body.is_empty()
                    && statements_are_typed(then_body)
                    && statements_are_typed(else_body)
            }
            NestedWrap32GuardO0TypedStatement::Return { value } => {
                value.ty() == NestedWrap32GuardO0TypedScalar::SignedI32
            }
        })
    }
    statements_are_typed(&program.body)
}

fn render_statements(
    output: &mut String,
    statements: &[NestedWrap32GuardO0TypedStatement],
    parameters: &[String; 2],
    indent: usize,
) -> Result<(), NestedWrap32GuardO0SemanticCFunctionError> {
    for statement in statements {
        let padding = "\t".repeat(indent);
        match statement {
            NestedWrap32GuardO0TypedStatement::Let { binding, value } => {
                if binding.ty() != value.ty()
                    || binding.ty() != NestedWrap32GuardO0TypedScalar::UnsignedI32
                {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "ill-typed nested wrap32 local binding".to_string(),
                        ]),
                    );
                }
                writeln!(
                    output,
                    "{padding}uint32_t {} = {};",
                    binding_name(*binding),
                    render_expr(value, parameters)?
                )
                .expect("String writes cannot fail");
            }
            NestedWrap32GuardO0TypedStatement::If {
                condition,
                then_body,
                else_body,
            } => {
                if condition.ty() != NestedWrap32GuardO0TypedScalar::Boolean {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "ill-typed nested wrap32 branch".to_string(),
                        ]),
                    );
                }
                writeln!(
                    output,
                    "{padding}if ({}) {{",
                    render_expr(condition, parameters)?
                )
                .expect("String writes cannot fail");
                render_statements(output, then_body, parameters, indent + 1)?;
                writeln!(output, "{padding}}} else {{").expect("String writes cannot fail");
                render_statements(output, else_body, parameters, indent + 1)?;
                writeln!(output, "{padding}}}").expect("String writes cannot fail");
            }
            NestedWrap32GuardO0TypedStatement::Return { value } => {
                if value.ty() != NestedWrap32GuardO0TypedScalar::SignedI32 {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "ill-typed nested wrap32 return".to_string(),
                        ]),
                    );
                }
                writeln!(
                    output,
                    "{padding}return {};",
                    render_expr(value, parameters)?
                )
                .expect("String writes cannot fail");
            }
        }
    }
    Ok(())
}

fn render_expr(
    expression: &NestedWrap32GuardO0TypedExpr,
    parameters: &[String; 2],
) -> Result<String, NestedWrap32GuardO0SemanticCFunctionError> {
    Ok(match expression {
        NestedWrap32GuardO0TypedExpr::ParameterBits { index } => {
            let parameter = parameters.get(*index as usize).ok_or_else(|| {
                NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                    "foreign nested wrap32 parameter index".to_string(),
                ])
            })?;
            format!("(uint32_t){parameter}")
        }
        NestedWrap32GuardO0TypedExpr::Binding { binding } => binding_name(*binding).to_string(),
        NestedWrap32GuardO0TypedExpr::WrapAdd { left, right } => format!(
            "(uint32_t)({} + {})",
            binding_name(*left),
            binding_name(*right)
        ),
        NestedWrap32GuardO0TypedExpr::WrapSubtract { left, right } => format!(
            "(uint32_t)({} - {})",
            binding_name(*left),
            binding_name(*right)
        ),
        NestedWrap32GuardO0TypedExpr::NotEqualU32 { value, expected } => {
            format!("{} != UINT32_C(0x{expected:x})", binding_name(*value))
        }
        NestedWrap32GuardO0TypedExpr::SignedI32Constant { value } => {
            if *value < 0 {
                format!("(-INT32_C({}))", value.unsigned_abs())
            } else {
                format!("INT32_C({value})")
            }
        }
    })
}

const fn binding_name(binding: NestedWrap32GuardO0TypedBinding) -> &'static str {
    match binding {
        NestedWrap32GuardO0TypedBinding::FirstBits => "r2s_first_bits",
        NestedWrap32GuardO0TypedBinding::SecondBits => "r2s_second_bits",
        NestedWrap32GuardO0TypedBinding::SumBits => "r2s_sum_bits",
        NestedWrap32GuardO0TypedBinding::DifferenceBits => "r2s_difference_bits",
    }
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
pub struct NestedWrap32GuardO0SemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl NestedWrap32GuardO0SemanticCFunctionAuditReport {
    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn has_exact_nested_wrap32_guard_o0_function(&self) -> bool {
        self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct NestedWrap32GuardO0DifferentialInput {
    first: i32,
    second: i32,
}

impl NestedWrap32GuardO0DifferentialInput {
    pub const fn new(first: i32, second: i32) -> Self {
        Self { first, second }
    }

    pub const fn first(self) -> i32 {
        self.first
    }

    pub const fn second(self) -> i32 {
        self.second
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct NestedWrap32GuardO0DifferentialCase {
    input: NestedWrap32GuardO0DifferentialInput,
    source_result: i32,
    candidate_result: i32,
}

impl NestedWrap32GuardO0DifferentialCase {
    pub const fn input(&self) -> NestedWrap32GuardO0DifferentialInput {
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
pub struct NestedWrap32GuardO0DifferentialReport {
    cases: Box<[NestedWrap32GuardO0DifferentialCase]>,
}

impl NestedWrap32GuardO0DifferentialReport {
    pub const fn cases(&self) -> &[NestedWrap32GuardO0DifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty()
            && self
                .cases
                .iter()
                .all(NestedWrap32GuardO0DifferentialCase::matches)
    }
}

/// Boundary probes plus a deterministic xorshift64 sequence. The two exact
/// success solutions and adjacent failures are always present.
pub fn nested_wrap32_guard_o0_boundary_and_random_cases(
    seed: u64,
    random_cases: usize,
) -> Result<Box<[NestedWrap32GuardO0DifferentialInput]>, NestedWrap32GuardO0SemanticCFunctionError>
{
    let mut cases = vec![
        NestedWrap32GuardO0DifferentialInput::new(60, 40),
        NestedWrap32GuardO0DifferentialInput::new(0x8000_003c_u32 as i32, 0x8000_0028_u32 as i32),
        NestedWrap32GuardO0DifferentialInput::new(59, 40),
        NestedWrap32GuardO0DifferentialInput::new(60, 39),
        NestedWrap32GuardO0DifferentialInput::new(60, 41),
        NestedWrap32GuardO0DifferentialInput::new(61, 40),
        NestedWrap32GuardO0DifferentialInput::new(0, 0),
        NestedWrap32GuardO0DifferentialInput::new(1, -1),
        NestedWrap32GuardO0DifferentialInput::new(-1, 1),
        NestedWrap32GuardO0DifferentialInput::new(i32::MIN, i32::MIN),
        NestedWrap32GuardO0DifferentialInput::new(i32::MIN, i32::MAX),
        NestedWrap32GuardO0DifferentialInput::new(i32::MAX, i32::MIN),
        NestedWrap32GuardO0DifferentialInput::new(i32::MAX, i32::MAX),
    ];
    let total = cases
        .len()
        .checked_add(random_cases)
        .ok_or(NestedWrap32GuardO0SemanticCFunctionError::TooManyDifferentialCases(usize::MAX))?;
    if total > MAX_DIFFERENTIAL_CASES {
        return Err(NestedWrap32GuardO0SemanticCFunctionError::TooManyDifferentialCases(total));
    }
    let mut state = if seed == 0 {
        0x9e37_79b9_7f4a_7c15
    } else {
        seed
    };
    for _ in 0..random_cases {
        let first = next_xorshift64(&mut state) as u32 as i32;
        let second = next_xorshift64(&mut state) as u32 as i32;
        cases.push(NestedWrap32GuardO0DifferentialInput::new(first, second));
    }
    Ok(cases.into_boxed_slice())
}

fn next_xorshift64(state: &mut u64) -> u64 {
    let mut value = *state;
    value ^= value << 13;
    value ^= value >> 7;
    value ^= value << 17;
    *state = value;
    value
}

pub fn check_nested_wrap32_guard_o0_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedNestedWrap32GuardO0SemanticCFunction,
    inputs: impl IntoIterator<Item = NestedWrap32GuardO0DifferentialInput>,
) -> Result<NestedWrap32GuardO0DifferentialReport, NestedWrap32GuardO0SemanticCFunctionError> {
    let audit = candidate.audit();
    if !audit.has_exact_nested_wrap32_guard_o0_function() {
        return Err(NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(audit.invalid));
    }
    let source = certify_nested_wrap32_guard_o0_function(artifact)?
        .ok_or(NestedWrap32GuardO0SemanticCFunctionError::MissingCertificate)?;
    if !source.validate_against_artifact(artifact)
        || source.origin() != candidate.origin()
        || source != *candidate.certificate()
    {
        return Err(
            NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                "differential source and nested wrap32 candidate origins differ".to_string(),
            ]),
        );
    }
    expected_abi(&source)?;
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.is_empty() {
        return Err(NestedWrap32GuardO0SemanticCFunctionError::EmptyDifferential);
    }
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(
            NestedWrap32GuardO0SemanticCFunctionError::TooManyDifferentialCases(inputs.len()),
        );
    }
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        let source_result = execute_prepared_nested_wrap32_guard_o0(artifact, &source, input)
            .map_err(|reason| {
                NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![reason])
            })?;
        let candidate_result = evaluate_typed_program(&candidate.program, input)?;
        cases.push(NestedWrap32GuardO0DifferentialCase {
            input,
            source_result,
            candidate_result,
        });
    }
    let report = NestedWrap32GuardO0DifferentialReport {
        cases: cases.into_boxed_slice(),
    };
    if !report.has_equivalence() {
        let mismatch = report
            .cases
            .iter()
            .find(|case| !case.matches())
            .expect("non-equivalent differential has a mismatch");
        return Err(
            NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![format!(
                "prepared SSA and typed nested wrap32 AST disagree for ({}, {}): source {}, candidate {}",
                mismatch.input.first,
                mismatch.input.second,
                mismatch.source_result,
                mismatch.candidate_result
            )]),
        );
    }
    Ok(report)
}

pub fn check_nested_wrap32_guard_o0_boundary_and_random_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedNestedWrap32GuardO0SemanticCFunction,
    seed: u64,
    random_cases: usize,
) -> Result<NestedWrap32GuardO0DifferentialReport, NestedWrap32GuardO0SemanticCFunctionError> {
    let cases = nested_wrap32_guard_o0_boundary_and_random_cases(seed, random_cases)?;
    check_nested_wrap32_guard_o0_differential(artifact, candidate, cases.iter().copied())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypedRuntimeValue {
    SignedI32(i32),
    UnsignedI32(u32),
    Boolean(bool),
}

fn evaluate_typed_program(
    program: &NestedWrap32GuardO0TypedProgram,
    input: NestedWrap32GuardO0DifferentialInput,
) -> Result<i32, NestedWrap32GuardO0SemanticCFunctionError> {
    if !typed_program_is_well_formed(program) {
        return Err(
            NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                "differential candidate AST is ill-typed".to_string(),
            ]),
        );
    }
    let mut bindings = BTreeMap::new();
    let mut steps = 0u32;
    let returned = evaluate_typed_statements(&program.body, input, &mut bindings, &mut steps)?;
    returned.ok_or_else(|| {
        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
            "typed nested wrap32 program did not return".to_string(),
        ])
    })
}

fn evaluate_typed_statements(
    statements: &[NestedWrap32GuardO0TypedStatement],
    input: NestedWrap32GuardO0DifferentialInput,
    bindings: &mut BTreeMap<NestedWrap32GuardO0TypedBinding, u32>,
    steps: &mut u32,
) -> Result<Option<i32>, NestedWrap32GuardO0SemanticCFunctionError> {
    for statement in statements {
        *steps = steps
            .checked_add(1)
            .ok_or(NestedWrap32GuardO0SemanticCFunctionError::DifferentialBudgetExceeded)?;
        if *steps > MAX_TYPED_STATEMENT_STEPS {
            return Err(NestedWrap32GuardO0SemanticCFunctionError::DifferentialBudgetExceeded);
        }
        match statement {
            NestedWrap32GuardO0TypedStatement::Let { binding, value } => {
                let TypedRuntimeValue::UnsignedI32(value) =
                    evaluate_typed_expr(value, input, bindings)?
                else {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "typed nested wrap32 local did not evaluate to uint32".to_string(),
                        ]),
                    );
                };
                if bindings.insert(*binding, value).is_some() {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "typed nested wrap32 local was assigned twice".to_string(),
                        ]),
                    );
                }
            }
            NestedWrap32GuardO0TypedStatement::If {
                condition,
                then_body,
                else_body,
            } => {
                let TypedRuntimeValue::Boolean(condition) =
                    evaluate_typed_expr(condition, input, bindings)?
                else {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "typed nested wrap32 condition was not boolean".to_string(),
                        ]),
                    );
                };
                let selected = if condition { then_body } else { else_body };
                if let Some(returned) = evaluate_typed_statements(selected, input, bindings, steps)?
                {
                    return Ok(Some(returned));
                }
            }
            NestedWrap32GuardO0TypedStatement::Return { value } => {
                let TypedRuntimeValue::SignedI32(value) =
                    evaluate_typed_expr(value, input, bindings)?
                else {
                    return Err(
                        NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                            "typed nested wrap32 return was not int32".to_string(),
                        ]),
                    );
                };
                return Ok(Some(value));
            }
        }
    }
    Ok(None)
}

fn evaluate_typed_expr(
    expression: &NestedWrap32GuardO0TypedExpr,
    input: NestedWrap32GuardO0DifferentialInput,
    bindings: &BTreeMap<NestedWrap32GuardO0TypedBinding, u32>,
) -> Result<TypedRuntimeValue, NestedWrap32GuardO0SemanticCFunctionError> {
    let binding = |binding| {
        bindings.get(&binding).copied().ok_or_else(|| {
            NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![format!(
                "typed nested wrap32 binding {binding:?} was read before definition"
            )])
        })
    };
    Ok(match expression {
        NestedWrap32GuardO0TypedExpr::ParameterBits { index: 0 } => {
            TypedRuntimeValue::UnsignedI32(input.first as u32)
        }
        NestedWrap32GuardO0TypedExpr::ParameterBits { index: 1 } => {
            TypedRuntimeValue::UnsignedI32(input.second as u32)
        }
        NestedWrap32GuardO0TypedExpr::ParameterBits { .. } => {
            return Err(
                NestedWrap32GuardO0SemanticCFunctionError::InvalidComposition(vec![
                    "typed nested wrap32 parameter index is foreign".to_string(),
                ]),
            );
        }
        NestedWrap32GuardO0TypedExpr::Binding { binding: value } => {
            TypedRuntimeValue::UnsignedI32(binding(*value)?)
        }
        NestedWrap32GuardO0TypedExpr::WrapAdd { left, right } => {
            TypedRuntimeValue::UnsignedI32(binding(*left)?.wrapping_add(binding(*right)?))
        }
        NestedWrap32GuardO0TypedExpr::WrapSubtract { left, right } => {
            TypedRuntimeValue::UnsignedI32(binding(*left)?.wrapping_sub(binding(*right)?))
        }
        NestedWrap32GuardO0TypedExpr::NotEqualU32 { value, expected } => {
            TypedRuntimeValue::Boolean(binding(*value)? != *expected)
        }
        NestedWrap32GuardO0TypedExpr::SignedI32Constant { value } => {
            TypedRuntimeValue::SignedI32(*value)
        }
    })
}

fn execute_prepared_nested_wrap32_guard_o0(
    artifact: &SsaArtifact,
    certificate: &CertifiedNestedWrap32GuardO0Function,
    input: NestedWrap32GuardO0DifferentialInput,
) -> Result<i32, String> {
    let graph = artifact.graph();
    let mut values = BTreeMap::<SSAVar, DifferentialBitVector>::new();
    for graph_value in &graph.values {
        if graph.def_inst(graph_value.id).is_some() || graph_value.var.constant_bits().is_some() {
            continue;
        }
        let width = graph_value
            .var
            .size
            .checked_mul(8)
            .ok_or_else(|| "prepared nested wrap32 input width overflow".to_string())?;
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
        values.insert(
            graph_value.var.clone(),
            DifferentialBitVector::new(width, bits)
                .ok_or_else(|| format!("unsupported prepared nested wrap32 width {width}"))?,
        );
    }
    for (parameter, bits) in certificate
        .abi()
        .parameters()
        .iter()
        .zip([input.first as u32, input.second as u32])
    {
        let graph_value = graph
            .value(parameter.low32_value())
            .ok_or_else(|| "certified nested wrap32 parameter is foreign".to_string())?;
        if graph.def_inst(graph_value.id).is_some() || graph_value.var.size != 4 {
            return Err("certified nested wrap32 parameter is not a 32-bit input".to_string());
        }
        values.insert(
            graph_value.var.clone(),
            DifferentialBitVector::new(32, u64::from(bits))
                .expect("32-bit differential input is supported"),
        );
    }

    let mut memory = BTreeMap::<(String, u64), u8>::new();
    let mut predecessor = None;
    let mut block = artifact.function().entry;
    let mut block_steps = 0u32;
    let mut instruction_steps = 0u32;
    loop {
        block_steps = block_steps
            .checked_add(1)
            .ok_or_else(|| "prepared nested wrap32 block budget overflow".to_string())?;
        if block_steps > MAX_SOURCE_BLOCK_STEPS {
            return Err("prepared nested wrap32 block budget exceeded".to_string());
        }
        let source_block = artifact
            .function()
            .get_block(block)
            .ok_or_else(|| format!("prepared nested wrap32 block 0x{block:x} is missing"))?;
        if source_block.phis.is_empty() {
            if block != artifact.function().entry && predecessor.is_none() {
                return Err("prepared nested wrap32 predecessor is missing".to_string());
            }
        } else {
            let predecessor = predecessor
                .ok_or_else(|| "prepared nested wrap32 phi block has no predecessor".to_string())?;
            let assignments = source_block
                .phis
                .iter()
                .map(|phi| {
                    let source = phi
                        .sources
                        .iter()
                        .find(|(candidate, _)| *candidate == predecessor)
                        .map(|(_, source)| source)
                        .ok_or_else(|| {
                            "prepared nested wrap32 phi predecessor is absent".to_string()
                        })?;
                    Ok((phi.dst.clone(), source_operand(&values, source)?))
                })
                .collect::<Result<Vec<_>, String>>()?;
            for (destination, value) in assignments {
                write_source_value(&mut values, &destination, value.bits())?;
            }
        }
        for operation in &source_block.ops {
            instruction_steps = instruction_steps
                .checked_add(1)
                .ok_or_else(|| "prepared nested wrap32 instruction budget overflow".to_string())?;
            if instruction_steps > MAX_SOURCE_INSTRUCTION_STEPS {
                return Err("prepared nested wrap32 instruction budget exceeded".to_string());
            }
            execute_source_operation(operation, &mut values, &mut memory)?;
        }
        let next = match &artifact
            .function()
            .cfg()
            .get_block(block)
            .ok_or_else(|| "prepared nested wrap32 CFG block is missing".to_string())?
            .terminator
        {
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                let Some(SSAOp::CBranch { cond, .. }) = source_block.ops.last() else {
                    return Err(
                        "prepared nested wrap32 conditional lacks its predicate".to_string()
                    );
                };
                if source_operand(&values, cond)?.bits() != 0 {
                    *true_target
                } else {
                    *false_target
                }
            }
            BlockTerminator::Branch { target } => *target,
            BlockTerminator::Fallthrough { next } => *next,
            BlockTerminator::Return => {
                let returned = graph
                    .value(certificate.returned().returned_value())
                    .ok_or_else(|| "certified nested wrap32 return is foreign".to_string())?;
                let result = source_operand(&values, &returned.var)?;
                if result.width_bits() != 64 || result.bits() > u64::from(u32::MAX) {
                    return Err(
                        "prepared nested wrap32 return carrier is not zero-extended".to_string()
                    );
                }
                return Ok(result.bits() as u32 as i32);
            }
            _ => return Err("prepared nested wrap32 has an unsupported terminator".to_string()),
        };
        predecessor = Some(block);
        block = next;
    }
}

fn execute_source_operation(
    operation: &SSAOp,
    values: &mut BTreeMap<SSAVar, DifferentialBitVector>,
    memory: &mut BTreeMap<(String, u64), u8>,
) -> Result<(), String> {
    let binary = |left: &SSAVar,
                  right: &SSAVar,
                  values: &BTreeMap<SSAVar, DifferentialBitVector>|
     -> Result<(DifferentialBitVector, DifferentialBitVector), String> {
        Ok((
            source_operand(values, left)?,
            source_operand(values, right)?,
        ))
    };
    match operation {
        SSAOp::Copy { dst, src } | SSAOp::IntZExt { dst, src } => {
            let source = source_operand(values, src)?;
            write_source_value(values, dst, source.bits())?;
        }
        SSAOp::IntAdd { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            write_source_value(values, dst, left.bits().wrapping_add(right.bits()))?;
        }
        SSAOp::IntSub { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            write_source_value(values, dst, left.bits().wrapping_sub(right.bits()))?;
        }
        SSAOp::IntCarry { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            let carry = u128::from(left.bits()) + u128::from(right.bits())
                > u128::from(source_width_mask(left.width_bits()));
            write_source_value(values, dst, u64::from(carry))?;
        }
        SSAOp::IntSCarry { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            let width = left.width_bits();
            let result = source_signed(left) + source_signed(right);
            let (minimum, maximum) = source_signed_bounds(width)?;
            write_source_value(values, dst, u64::from(result < minimum || result > maximum))?;
        }
        SSAOp::IntSBorrow { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            let width = left.width_bits();
            let result = source_signed(left) - source_signed(right);
            let (minimum, maximum) = source_signed_bounds(width)?;
            write_source_value(values, dst, u64::from(result < minimum || result > maximum))?;
        }
        SSAOp::IntLess { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            write_source_value(values, dst, u64::from(left.bits() < right.bits()))?;
        }
        SSAOp::IntSLess { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            write_source_value(
                values,
                dst,
                u64::from(source_signed(left) < source_signed(right)),
            )?;
        }
        SSAOp::IntEqual { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            write_source_value(values, dst, u64::from(left.bits() == right.bits()))?;
        }
        SSAOp::IntNotEqual { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            require_equal_width(left, right)?;
            write_source_value(values, dst, u64::from(left.bits() != right.bits()))?;
        }
        SSAOp::IntAnd { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            write_source_value(values, dst, left.bits() & right.bits())?;
        }
        SSAOp::IntOr { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            write_source_value(values, dst, left.bits() | right.bits())?;
        }
        SSAOp::IntXor { dst, a, b } => {
            let (left, right) = binary(a, b, values)?;
            write_source_value(values, dst, left.bits() ^ right.bits())?;
        }
        SSAOp::PopCount { dst, src } => {
            let source = source_operand(values, src)?;
            write_source_value(values, dst, u64::from(source.bits().count_ones()))?;
        }
        SSAOp::BoolNot { dst, src } => {
            let source = source_operand(values, src)?;
            write_source_value(values, dst, u64::from(source.bits() == 0))?;
        }
        SSAOp::Load { dst, space, addr } => {
            let address = source_operand(values, addr)?.bits();
            let mut bits = 0u64;
            for index in 0..dst.size {
                let byte_address = address
                    .checked_add(u64::from(index))
                    .ok_or_else(|| "prepared nested wrap32 load address overflow".to_string())?;
                let byte = memory
                    .get(&(space.clone(), byte_address))
                    .copied()
                    .unwrap_or(0);
                bits |= u64::from(byte) << (index * 8);
            }
            write_source_value(values, dst, bits)?;
        }
        SSAOp::Store { space, addr, val } => {
            let address = source_operand(values, addr)?.bits();
            let stored = source_operand(values, val)?;
            for index in 0..val.size {
                let byte_address = address
                    .checked_add(u64::from(index))
                    .ok_or_else(|| "prepared nested wrap32 store address overflow".to_string())?;
                memory.insert(
                    (space.clone(), byte_address),
                    ((stored.bits() >> (index * 8)) & 0xff) as u8,
                );
            }
        }
        SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. } => {}
        _ => {
            return Err(format!(
                "prepared nested wrap32 contains unsupported operation {operation:?}"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use r2il::{AddressSpace, R2ILBlock, R2ILOp};
    use r2sleigh_lift::{Disassembler, build_arch_spec};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierProjection,
        SourceFunctionInterface, SourceLogicalValue, SourceStackSlotSpec, SourceType,
        SourceTypeGraph,
    };

    use super::*;

    const RAX_OFFSET: u64 = 0;
    const RBP_OFFSET: u64 = 40;
    const RSI_OFFSET: u64 = 48;
    const RDI_OFFSET: u64 = 56;

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

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn interface(revision: &[u8]) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX_OFFSET),
            },
            [
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(RBP_OFFSET),
                    -8,
                    4,
                    0,
                    storage(RDI_OFFSET),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(RBP_OFFSET),
                    -12,
                    4,
                    1,
                    storage(RSI_OFFSET),
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    storage(RBP_OFFSET),
                    -16,
                    4,
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    storage(RBP_OFFSET),
                    -20,
                    4,
                ),
            ],
            [
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(
                SourceTypeGraph::new(
                    [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
                    [],
                )
                .expect("signed i32 graph"),
            ),
        )
        .expect("exact nested wrap32 interface")
    }

    fn artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let mut arch = build_arch_spec(
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
        let mut address = base;
        let blocks = [
            "554889e5897df88975f48b45f80345f48945f08b45f82b45f48945ec837df0647511",
            "837dec147509",
            "c745fc01000000eb09",
            "eb00",
            "c745fc00000000",
            "8b45fc5dc3",
        ]
        .into_iter()
        .map(|encoded| {
            let bytes = decode_hex(encoded);
            let block = disassembler
                .lift_block(&bytes, address, bytes.len())
                .expect("pinned complex_check block");
            address += bytes.len() as u64;
            block
        })
        .collect::<Vec<R2ILBlock>>();
        let spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        for space in spaces {
            if !arch.spaces.iter().any(|candidate| candidate.id == space) {
                arch.add_space(AddressSpace::new(space, "sleigh-data", 8));
            }
        }
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface(revision))
            .expect("prepared complex_check O0 artifact")
    }

    #[test]
    fn real_o0_lift_renders_and_matches_actual_prepared_ssa() {
        let artifact = artifact(0x1000_0880, b"nested-render-real-o0");
        let function = CertifiedNestedWrap32GuardO0SemanticCFunction::from_artifact(&artifact)
            .expect("certified nested wrap32 renderer");
        assert!(function.audit().has_exact_nested_wrap32_guard_o0_function());
        assert_eq!(function.certificate().instruction_dispositions().len(), 126);
        let report = check_nested_wrap32_guard_o0_boundary_and_random_differential(
            &artifact,
            &function,
            0x5eed_cafe_f00d_beef,
            128,
        )
        .expect("actual prepared-SSA differential");
        assert!(report.has_equivalence());
        assert_eq!(report.cases().len(), 141);

        let source = function
            .clone()
            .with_cosmetic_names("complex.check", "left value", "right value")
            .render_certified_c()
            .expect("strict C");
        assert!(source.contains("int32_t r2s_fn_complex_check(int32_t"));
        assert!(source.contains("uint32_t"));
        assert!(source.contains("UINT32_C(0x64)"));
        assert!(source.contains("UINT32_C(0x14)"));

        let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
        let mut child = Command::new(compiler)
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                "-x",
                "c",
                "-",
                "-fsyntax-only",
            ])
            .stdin(Stdio::piped())
            .spawn()
            .expect("C compiler");
        child
            .stdin
            .as_mut()
            .expect("compiler stdin")
            .write_all(source.as_bytes())
            .expect("write strict C");
        assert!(child.wait().expect("C compiler status").success());
    }

    #[test]
    fn renderer_and_differential_reject_foreign_or_mutated_composition() {
        let first = artifact(0x1000_0880, b"nested-render-origin-a");
        let second = artifact(0x2000_0880, b"nested-render-origin-b");
        let function = CertifiedNestedWrap32GuardO0SemanticCFunction::from_artifact(&first)
            .expect("first renderer");
        assert!(
            check_nested_wrap32_guard_o0_differential(
                &second,
                &function,
                [NestedWrap32GuardO0DifferentialInput::new(60, 40)],
            )
            .is_err()
        );

        let mut mutated = function;
        mutated.program.body = mutated.program.body[1..].to_vec().into_boxed_slice();
        assert!(!mutated.audit().has_exact_nested_wrap32_guard_o0_function());
        assert!(mutated.render_certified_c().is_err());
    }
}

fn source_operand(
    values: &BTreeMap<SSAVar, DifferentialBitVector>,
    variable: &SSAVar,
) -> Result<DifferentialBitVector, String> {
    let width = variable
        .size
        .checked_mul(8)
        .ok_or_else(|| "prepared nested wrap32 operand width overflow".to_string())?;
    if let Some(bits) = variable.constant_bits() {
        return DifferentialBitVector::new(width, bits)
            .ok_or_else(|| format!("unsupported prepared nested wrap32 constant width {width}"));
    }
    values.get(variable).copied().ok_or_else(|| {
        format!(
            "prepared nested wrap32 value version is undefined: {:?} v{}",
            variable.name_kind(),
            variable.version
        )
    })
}

fn write_source_value(
    values: &mut BTreeMap<SSAVar, DifferentialBitVector>,
    destination: &SSAVar,
    bits: u64,
) -> Result<(), String> {
    let width = destination
        .size
        .checked_mul(8)
        .ok_or_else(|| "prepared nested wrap32 destination width overflow".to_string())?;
    let value = DifferentialBitVector::new(width, bits)
        .ok_or_else(|| format!("unsupported prepared nested wrap32 destination width {width}"))?;
    if values.insert(destination.clone(), value).is_some() {
        return Err("prepared nested wrap32 SSA destination was defined twice".to_string());
    }
    Ok(())
}

fn require_equal_width(
    left: DifferentialBitVector,
    right: DifferentialBitVector,
) -> Result<(), String> {
    if left.width_bits() == right.width_bits() {
        Ok(())
    } else {
        Err("prepared nested wrap32 operand widths differ".to_string())
    }
}

fn source_width_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn source_signed(value: DifferentialBitVector) -> i128 {
    let width = value.width_bits();
    let sign = 1u64 << (width - 1);
    if value.bits() & sign == 0 {
        i128::from(value.bits())
    } else {
        i128::from(value.bits()) - (1i128 << width)
    }
}

fn source_signed_bounds(width: u32) -> Result<(i128, i128), String> {
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Err(format!(
            "unsupported prepared nested wrap32 signed width {width}"
        ));
    }
    let magnitude = 1i128 << (width - 1);
    Ok((-magnitude, magnitude - 1))
}
