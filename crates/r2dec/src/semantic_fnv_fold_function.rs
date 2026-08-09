//! Proof-preserving strict-C rendering for the sealed canonical FNV fold.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION, CERTIFIED_FNV_OFFSET_BASIS, CERTIFIED_FNV_PRIME,
    CertifiedArtifactOrigin, CertifiedFnvFoldLoop, CertifiedMachineFunction, CertifiedRenderPermit,
    CertifiedTypedRegionKind, EffectDisposition, RenderAuthorizationError, TypedRegionMapping,
    certify_fnv_fold_loop_region,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace, MachineAddressSpace,
    MachineBuildError, MachineSignedness, MachineType, MachineValueBinding, SemanticObligationId,
    SourceCarrierKind, SourceFunctionReturn, SourceTypeKind, SsaArtifact,
};
use serde::Serialize;

use crate::semantic_differential::{
    DifferentialBitVector, DifferentialMemoryEventKind, DifferentialMemoryLocation,
    PreparedFunctionLimits, execute_prepared_function_return,
};

pub const CERTIFIED_FNV_FOLD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION;

const MAX_DIFFERENTIAL_CASES: usize = 256;
const MAX_DIFFERENTIAL_INPUT_BYTES: usize = 4096;
const DIFFERENTIAL_INPUT_BASE: u64 = 0x40_0000;
const ASCII_UPPER_BASE: u32 = 0x41;
const ASCII_UPPER_SPAN: u32 = 0x1a;
const ASCII_LOWERCASE_MASK: u32 = 0x20;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FnvFoldSemanticCFunctionScope {
    ClosedCanonicalAarch64O2ByteFold,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum FnvFoldPhaseKind {
    PointerInitialization,
    HashInitialization,
    ZeroGuard,
    ByteRead,
    AsciiNormalization,
    HashTransition,
    PointerTransition,
    RemainingTransition,
    Latch,
    Return,
}

/// One renderer-level semantic phase and its exact certified producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct FnvFoldPhase {
    kind: FnvFoldPhaseKind,
    producer: CanonicalInstructionId,
}

impl FnvFoldPhase {
    pub const fn kind(&self) -> FnvFoldPhaseKind {
        self.kind
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }
}

/// Exact ABI facts consumed by the strict-C signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldAbiManifest {
    revision_identity: Box<[u8]>,
    pointer_index: u32,
    pointer_storage: CanonicalStorageId,
    pointer: MachineValueBinding,
    remaining_index: u32,
    remaining_storage: CanonicalStorageId,
    remaining: MachineValueBinding,
    return_storage: CanonicalStorageId,
    returned: MachineValueBinding,
}

impl FnvFoldAbiManifest {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn pointer_index(&self) -> u32 {
        self.pointer_index
    }

    pub const fn pointer_storage(&self) -> CanonicalStorageId {
        self.pointer_storage
    }

    pub const fn pointer(&self) -> MachineValueBinding {
        self.pointer
    }

    pub const fn remaining_index(&self) -> u32 {
        self.remaining_index
    }

    pub const fn remaining_storage(&self) -> CanonicalStorageId {
        self.remaining_storage
    }

    pub const fn remaining(&self) -> MachineValueBinding {
        self.remaining
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn returned(&self) -> MachineValueBinding {
        self.returned
    }
}

/// Structural semantics duplicated at the render boundary for mutation audits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct FnvFoldRenderProgram {
    offset_basis: u64,
    prime: u64,
    ascii_upper_base: u32,
    ascii_upper_span: u32,
    ascii_lowercase_mask: u32,
    lowercase_on_true: bool,
    zero_guard_returns_when_empty: bool,
    pointer_step: u64,
    remaining_step: u64,
    latch_continues_when_nonzero: bool,
    load_width_bytes: u32,
}

impl FnvFoldRenderProgram {
    pub const fn offset_basis(&self) -> u64 {
        self.offset_basis
    }

    pub const fn prime(&self) -> u64 {
        self.prime
    }

    pub const fn ascii_upper_base(&self) -> u32 {
        self.ascii_upper_base
    }

    pub const fn ascii_upper_span(&self) -> u32 {
        self.ascii_upper_span
    }

    pub const fn ascii_lowercase_mask(&self) -> u32 {
        self.ascii_lowercase_mask
    }

    pub const fn lowercase_on_true(&self) -> bool {
        self.lowercase_on_true
    }

    pub const fn zero_guard_returns_when_empty(&self) -> bool {
        self.zero_guard_returns_when_empty
    }

    pub const fn pointer_step(&self) -> u64 {
        self.pointer_step
    }

    pub const fn remaining_step(&self) -> u64 {
        self.remaining_step
    }

    pub const fn latch_continues_when_nonzero(&self) -> bool {
        self.latch_continues_when_nonzero
    }

    pub const fn load_width_bytes(&self) -> u32 {
        self.load_width_bytes
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldRenderNames {
    function: String,
    bytes: String,
    length: String,
    pointer: String,
    remaining: String,
    hash: String,
    byte: String,
    original: String,
    range: String,
    lowercase: String,
    folded: String,
}

impl FnvFoldRenderNames {
    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn bytes(&self) -> &str {
        &self.bytes
    }

    pub fn length(&self) -> &str {
        &self.length
    }
}

/// A complete strict-C function admitted only by the sealed FNV permit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldSemanticCFunction {
    schema_version: u32,
    scope: FnvFoldSemanticCFunctionScope,
    names: FnvFoldRenderNames,
    origin: CertifiedArtifactOrigin,
    witness: CertifiedFnvFoldLoop,
    abi: FnvFoldAbiManifest,
    sealed_program: FnvFoldRenderProgram,
    program: FnvFoldRenderProgram,
    phases: Box<[FnvFoldPhase]>,
    mappings: Box<[TypedRegionMapping]>,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FnvFoldSemanticCFunctionError {
    Machine(MachineBuildError),
    Authorization(RenderAuthorizationError),
    MissingFnvFoldWitness,
    InvalidProjectionFailure,
    InvalidInterface,
    InvalidInputLength { requested: u64, available: usize },
    DifferentialInputTooLarge(usize),
    TooManyDifferentialCases(usize),
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for FnvFoldSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FNV-fold semantic C function failed: {self:?}")
    }
}

impl std::error::Error for FnvFoldSemanticCFunctionError {}

impl From<MachineBuildError> for FnvFoldSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RenderAuthorizationError> for FnvFoldSemanticCFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl CertifiedFnvFoldSemanticCFunction {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, FnvFoldSemanticCFunctionError> {
        let certified = CertifiedMachineFunction::from_artifact(artifact)?;
        Self::from_certified(&certified)
    }

    /// Construct only from the exact whole-machine certificate and permit.
    pub fn from_certified(
        certified: &CertifiedMachineFunction,
    ) -> Result<Self, FnvFoldSemanticCFunctionError> {
        if !certified.projection().failures().is_empty() {
            return Err(FnvFoldSemanticCFunctionError::InvalidProjectionFailure);
        }
        let witness = certified
            .fnv_fold_loop()
            .ok_or(FnvFoldSemanticCFunctionError::MissingFnvFoldWitness)?
            .clone();
        let abi = expected_abi(&witness)?;
        let program = expected_program(&witness)?;
        let phases = expected_phases(&witness).into_boxed_slice();
        let mappings = exact_mappings(certified)?.into_boxed_slice();
        let render_permit = certify_fnv_fold_loop_region(
            certified.origin(),
            certified.ledger(),
            mappings.iter().cloned(),
            &witness,
        )?;
        let function = Self {
            schema_version: CERTIFIED_FNV_FOLD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: FnvFoldSemanticCFunctionScope::ClosedCanonicalAarch64O2ByteFold,
            names: default_names(),
            origin: certified.origin().clone(),
            witness,
            abi,
            sealed_program: program,
            program,
            phases,
            mappings,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_fnv_fold_function() {
            return Err(FnvFoldSemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> FnvFoldSemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &FnvFoldRenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn witness(&self) -> &CertifiedFnvFoldLoop {
        &self.witness
    }

    pub const fn abi(&self) -> &FnvFoldAbiManifest {
        &self.abi
    }

    pub const fn program(&self) -> FnvFoldRenderProgram {
        self.program
    }

    pub const fn phases(&self) -> &[FnvFoldPhase] {
        &self.phases
    }

    pub const fn mappings(&self) -> &[TypedRegionMapping] {
        &self.mappings
    }

    pub const fn render_permit(&self) -> &CertifiedRenderPermit {
        &self.render_permit
    }

    pub fn with_cosmetic_names(
        mut self,
        function: impl Into<String>,
        bytes: impl Into<String>,
        length: impl Into<String>,
    ) -> Self {
        self.names.function = function.into();
        self.names.bytes = bytes.into();
        self.names.length = length.into();
        self
    }

    pub fn audit(&self) -> FnvFoldSemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_FNV_FOLD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("FNV-fold schema mismatch".to_string());
        }
        if self.scope != FnvFoldSemanticCFunctionScope::ClosedCanonicalAarch64O2ByteFold {
            invalid.push("FNV-fold scope mismatch".to_string());
        }
        if self.witness.origin() != &self.origin
            || self.witness.contract_version() != CERTIFIED_FNV_FOLD_LOOP_CONTRACT_VERSION
        {
            invalid.push("FNV-fold witness does not match the artifact origin".to_string());
        }
        match expected_abi(&self.witness) {
            Ok(expected) if expected == self.abi => {}
            _ => invalid.push("FNV-fold ABI or logical type manifest mismatch".to_string()),
        }
        match expected_program(&self.witness) {
            Ok(expected) if expected == self.program && expected == self.sealed_program => {}
            _ => invalid
                .push("FNV-fold constants, polarity, memory, or recurrence mismatch".to_string()),
        }
        if self.phases.as_ref() != expected_phases(&self.witness).as_slice() {
            invalid.push("FNV-fold phases are incomplete or out of order".to_string());
        }
        let phase_counts = counts(self.phases.iter().map(FnvFoldPhase::kind));
        if ALL_PHASES
            .iter()
            .any(|phase| phase_counts.get(phase) != Some(&1))
            || phase_counts.len() != ALL_PHASES.len()
        {
            invalid.push("FNV-fold phases are missing or duplicated".to_string());
        }

        let source_obligations = self
            .origin
            .source()
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let mapping_counts = counts(self.mappings.iter().map(TypedRegionMapping::obligation));
        let actual_obligations = mapping_counts.keys().copied().collect::<BTreeSet<_>>();
        let missing = source_obligations
            .difference(&actual_obligations)
            .copied()
            .collect();
        let unexpected = actual_obligations
            .difference(&source_obligations)
            .copied()
            .collect();
        let duplicate = mapping_counts
            .iter()
            .filter_map(|(obligation, count)| (*count > 1).then_some(*obligation))
            .collect();
        if self.mappings.len() != source_obligations.len()
            || self.mappings.iter().any(|mapping| {
                matches!(
                    mapping.source_disposition(),
                    EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
                )
            })
        {
            invalid.push("FNV-fold source mapping is not exact and closed".to_string());
        }
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::FnvFoldLoopFunction,
            CERTIFIED_FNV_FOLD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            &self.mappings,
        ) {
            invalid.push("FNV-fold render permit does not match the mapping".to_string());
        }
        FnvFoldSemanticCFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    /// Emit one canonical strict unsigned-C spelling of the sealed fold.
    pub fn render_certified_c(&self) -> Result<String, FnvFoldSemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_fnv_fold_function() || !self.render_permit.authorizes_certified_c() {
            return Err(FnvFoldSemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let names = ResolvedNames::new(&self.names);
        let program = self.program;
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        writeln!(
            &mut output,
            "uint64_t {}(const uint8_t *{}, uint64_t {}) {{",
            names.function, names.bytes, names.length
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tconst uint8_t *{} = {};",
            names.pointer, names.bytes
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tuint64_t {} = UINT64_C(0x{:x});",
            names.hash, program.offset_basis
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tuint64_t {} = {};",
            names.remaining, names.length
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\twhile ({} != UINT64_C(0x0)) {{",
            names.remaining
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\tuint8_t {} = *{};",
            names.byte, names.pointer
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\tuint32_t {} = (uint32_t){};",
            names.original, names.byte
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\tuint32_t {} = (uint32_t)({} - UINT32_C(0x{:x}));",
            names.range, names.original, program.ascii_upper_base
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\tuint32_t {} = (uint32_t)({} | UINT32_C(0x{:x}));",
            names.lowercase, names.original, program.ascii_lowercase_mask
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\tuint32_t {} = ({} < UINT32_C(0x{:x})) ? {} : {};",
            names.folded, names.range, program.ascii_upper_span, names.lowercase, names.original
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\t{} = (uint64_t)(({} ^ (uint64_t){}) * UINT64_C(0x{:x}));",
            names.hash, names.hash, names.folded, program.prime
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\t{} = {} + UINT64_C(0x{:x});",
            names.pointer, names.pointer, program.pointer_step
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\t{} = (uint64_t)({} - UINT64_C(0x{:x}));",
            names.remaining, names.remaining, program.remaining_step
        )
        .expect("String writes cannot fail");
        output.push_str("\t}\n");
        writeln!(&mut output, "\treturn {};", names.hash).expect("String writes cannot fail");
        output.push_str("}\n");
        Ok(output)
    }
}

const ALL_PHASES: [FnvFoldPhaseKind; 10] = [
    FnvFoldPhaseKind::PointerInitialization,
    FnvFoldPhaseKind::HashInitialization,
    FnvFoldPhaseKind::ZeroGuard,
    FnvFoldPhaseKind::ByteRead,
    FnvFoldPhaseKind::AsciiNormalization,
    FnvFoldPhaseKind::HashTransition,
    FnvFoldPhaseKind::PointerTransition,
    FnvFoldPhaseKind::RemainingTransition,
    FnvFoldPhaseKind::Latch,
    FnvFoldPhaseKind::Return,
];

fn default_names() -> FnvFoldRenderNames {
    FnvFoldRenderNames {
        function: "certified_fnv_fold".to_string(),
        bytes: "bytes".to_string(),
        length: "length".to_string(),
        pointer: "pointer".to_string(),
        remaining: "remaining".to_string(),
        hash: "hash".to_string(),
        byte: "byte".to_string(),
        original: "original".to_string(),
        range: "range".to_string(),
        lowercase: "lowercase".to_string(),
        folded: "folded".to_string(),
    }
}

struct ResolvedNames {
    function: String,
    bytes: String,
    length: String,
    pointer: String,
    remaining: String,
    hash: String,
    byte: String,
    original: String,
    range: String,
    lowercase: String,
    folded: String,
}

impl ResolvedNames {
    fn new(names: &FnvFoldRenderNames) -> Self {
        Self {
            function: c_identifier("r2s_fn", &names.function),
            bytes: c_identifier("r2s_arg", &names.bytes),
            length: c_identifier("r2s_arg", &names.length),
            pointer: c_identifier("r2s_local", &names.pointer),
            remaining: c_identifier("r2s_local", &names.remaining),
            hash: c_identifier("r2s_local", &names.hash),
            byte: c_identifier("r2s_local", &names.byte),
            original: c_identifier("r2s_local", &names.original),
            range: c_identifier("r2s_local", &names.range),
            lowercase: c_identifier("r2s_local", &names.lowercase),
            folded: c_identifier("r2s_local", &names.folded),
        }
    }
}

fn expected_abi(
    witness: &CertifiedFnvFoldLoop,
) -> Result<FnvFoldAbiManifest, FnvFoldSemanticCFunctionError> {
    let interface = witness
        .origin()
        .machine_context()
        .source()
        .function_interface()
        .ok_or(FnvFoldSemanticCFunctionError::InvalidInterface)?;
    let [pointer_type, remaining_type] = interface.parameter_logical_values() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    };
    let Some(return_type) = interface.return_logical_value() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    };
    let Some(graph) = interface.type_graph() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    };
    let [byte, pointer, integer] = graph.types() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    };
    let pointer_parameter = witness.pointer_parameter();
    let remaining_parameter = witness.remaining_parameter();
    let Some(pointer_value) = pointer_parameter.value() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    };
    let Some(remaining_value) = remaining_parameter.value() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    };
    let full64 = |logical: r2ssa::SourceLogicalValue| {
        logical.carrier().kind() == SourceCarrierKind::Full
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == 64
    };
    let interface_is_exact = interface.revision_identity() == witness.revision_identity()
        && interface
            .calling_convention()
            .eq_ignore_ascii_case("aapcs64")
        && interface.stack_slots().is_empty()
        && interface.stack_slot_roles_complete()
        && graph.aggregates().is_empty()
        && byte.kind() == SourceTypeKind::UnsignedInteger
        && byte.size_bits() == 8
        && byte.align_bits() == 8
        && matches!(
            pointer.kind(),
            SourceTypeKind::Pointer { target_type_id: 0 }
        )
        && pointer.size_bits() == 64
        && pointer.align_bits() == 64
        && integer.kind() == SourceTypeKind::UnsignedInteger
        && integer.size_bits() == 64
        && integer.align_bits() == 64
        && *pointer_type == witness.pointer_logical()
        && *remaining_type == witness.remaining_logical()
        && return_type == witness.return_logical()
        && pointer_type.type_id() == 1
        && remaining_type.type_id() == 2
        && return_type.type_id() == 2
        && full64(*pointer_type)
        && full64(*remaining_type)
        && full64(return_type)
        && pointer_parameter.index() == 0
        && remaining_parameter.index() == 1
        && pointer_parameter.storage().space == CanonicalStorageSpace::Register
        && remaining_parameter.storage().space == CanonicalStorageSpace::Register
        && pointer_parameter.storage().size == 8
        && remaining_parameter.storage().size == 8
        && pointer_value.producer().is_none()
        && remaining_value.producer().is_none()
        && pointer_value.ty()
            == &MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            }
        && remaining_value.ty()
            == &MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            }
        && matches!(
            witness.load_address().ty(),
            MachineType::Address {
                width_bits: 64,
                space: MachineAddressSpace::Ram,
                ..
            }
        )
        && matches!(interface.return_kind(), SourceFunctionReturn::Register { storage }
            if storage == witness.return_storage() && storage.size == 8)
        && witness.returned().binding().width_bits() == 64;
    if !interface_is_exact {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    }
    Ok(FnvFoldAbiManifest {
        revision_identity: witness.revision_identity().to_vec().into_boxed_slice(),
        pointer_index: pointer_parameter.index(),
        pointer_storage: pointer_parameter.storage(),
        pointer: pointer_value.binding(),
        remaining_index: remaining_parameter.index(),
        remaining_storage: remaining_parameter.storage(),
        remaining: remaining_value.binding(),
        return_storage: witness.return_storage(),
        returned: witness.returned().binding(),
    })
}

fn expected_program(
    witness: &CertifiedFnvFoldLoop,
) -> Result<FnvFoldRenderProgram, FnvFoldSemanticCFunctionError> {
    if witness.offset_basis() != CERTIFIED_FNV_OFFSET_BASIS
        || witness.prime_value() != CERTIFIED_FNV_PRIME
        || !witness.lowercase_on_true()
        || witness.byte_load().space() != MachineAddressSpace::Ram
        || witness.byte_load().width_bits() != 8
        || witness.byte_load().word_size_bytes() != 1
        || witness.hash().update_producer() != witness.multiply_producer()
        || witness.pointer().update().binding().width_bits() != 64
        || witness.remaining().update().binding().width_bits() != 64
        || witness.latch_control().true_target() != witness.header_latch()
        || witness.latch_control().false_target() != witness.exit()
    {
        return Err(FnvFoldSemanticCFunctionError::InvalidInterface);
    }
    Ok(FnvFoldRenderProgram {
        offset_basis: CERTIFIED_FNV_OFFSET_BASIS,
        prime: CERTIFIED_FNV_PRIME,
        ascii_upper_base: ASCII_UPPER_BASE,
        ascii_upper_span: ASCII_UPPER_SPAN,
        ascii_lowercase_mask: ASCII_LOWERCASE_MASK,
        lowercase_on_true: true,
        zero_guard_returns_when_empty: true,
        pointer_step: 1,
        remaining_step: 1,
        latch_continues_when_nonzero: true,
        load_width_bytes: 1,
    })
}

fn expected_phases(witness: &CertifiedFnvFoldLoop) -> Vec<FnvFoldPhase> {
    vec![
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::PointerInitialization,
            producer: witness.pointer_entry_copy(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::HashInitialization,
            producer: witness.initializer_producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::ZeroGuard,
            producer: witness.zero_control().producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::ByteRead,
            producer: witness.byte_load().producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::AsciiNormalization,
            producer: witness.select_producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::HashTransition,
            producer: witness.hash().update_producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::PointerTransition,
            producer: witness.pointer().update_producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::RemainingTransition,
            producer: witness.remaining().update_producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::Latch,
            producer: witness.latch_control().producer(),
        },
        FnvFoldPhase {
            kind: FnvFoldPhaseKind::Return,
            producer: witness.return_control().producer(),
        },
    ]
}

fn exact_mappings(
    certified: &CertifiedMachineFunction,
) -> Result<Vec<TypedRegionMapping>, RenderAuthorizationError> {
    certified
        .source()
        .obligations()
        .keys()
        .map(|obligation| {
            let [effect] = certified.ledger().effects(*obligation) else {
                return Err(RenderAuthorizationError::IncompleteLedger);
            };
            Ok(TypedRegionMapping::new(
                *obligation,
                effect.disposition().clone(),
            ))
        })
        .collect()
}

fn c_identifier(prefix: &str, cosmetic: &str) -> String {
    let mut result = String::with_capacity(prefix.len() + cosmetic.len() + 1);
    result.push_str(prefix);
    result.push('_');
    for ch in cosmetic.chars() {
        result.push(if ch.is_ascii_alphanumeric() || ch == '_' {
            ch
        } else {
            '_'
        });
    }
    result
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut counts = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldSemanticCFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl FnvFoldSemanticCFunctionAuditReport {
    pub fn missing(&self) -> &[SemanticObligationId] {
        &self.missing
    }

    pub fn duplicate(&self) -> &[SemanticObligationId] {
        &self.duplicate
    }

    pub fn unexpected(&self) -> &[SemanticObligationId] {
        &self.unexpected
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn has_exact_fnv_fold_function(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldDifferentialInput {
    bytes: Box<[u8]>,
    length: u64,
}

impl FnvFoldDifferentialInput {
    pub fn new(bytes: impl Into<Vec<u8>>, length: u64) -> Self {
        Self {
            bytes: bytes.into().into_boxed_slice(),
            length,
        }
    }

    pub fn full(bytes: impl Into<Vec<u8>>) -> Self {
        let bytes = bytes.into();
        Self {
            length: bytes.len() as u64,
            bytes: bytes.into_boxed_slice(),
        }
    }

    pub const fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub const fn length(&self) -> u64 {
        self.length
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldDifferentialCase {
    input: FnvFoldDifferentialInput,
    source_result: u64,
    candidate_result: u64,
}

impl FnvFoldDifferentialCase {
    pub const fn input(&self) -> &FnvFoldDifferentialInput {
        &self.input
    }

    pub const fn source_result(&self) -> u64 {
        self.source_result
    }

    pub const fn candidate_result(&self) -> u64 {
        self.candidate_result
    }

    pub const fn matches(&self) -> bool {
        self.source_result == self.candidate_result
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldDifferentialReport {
    cases: Box<[FnvFoldDifferentialCase]>,
}

impl FnvFoldDifferentialReport {
    pub const fn cases(&self) -> &[FnvFoldDifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty() && self.cases.iter().all(FnvFoldDifferentialCase::matches)
    }
}

/// Independently compare the fresh source witness with the stored render program.
pub fn check_fnv_fold_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedFnvFoldSemanticCFunction,
    inputs: impl IntoIterator<Item = FnvFoldDifferentialInput>,
) -> Result<FnvFoldDifferentialReport, FnvFoldSemanticCFunctionError> {
    let audit = candidate.audit();
    if !audit.has_exact_fnv_fold_function() {
        return Err(FnvFoldSemanticCFunctionError::InvalidComposition(
            audit.invalid,
        ));
    }
    let source = CertifiedMachineFunction::from_artifact(artifact)?;
    let source_witness = source
        .fnv_fold_loop()
        .ok_or(FnvFoldSemanticCFunctionError::MissingFnvFoldWitness)?;
    if source.origin() != candidate.origin() || source_witness != candidate.witness() {
        return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
            "differential source and candidate origins differ".to_string(),
        ]));
    }
    expected_abi(source_witness)?;
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(FnvFoldSemanticCFunctionError::TooManyDifferentialCases(
            inputs.len(),
        ));
    }
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        validate_input(&input)?;
        let source_result = evaluate_prepared_source(artifact, candidate, &input, None)?;
        let candidate_result = evaluate_candidate(candidate.program(), &input)?;
        cases.push(FnvFoldDifferentialCase {
            input,
            source_result,
            candidate_result,
        });
    }
    let report = FnvFoldDifferentialReport {
        cases: cases.into_boxed_slice(),
    };
    if !report.has_equivalence() {
        return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
            "source and strict-C FNV evaluators disagree".to_string(),
        ]));
    }
    Ok(report)
}

fn validate_input(
    input: &FnvFoldDifferentialInput,
) -> Result<usize, FnvFoldSemanticCFunctionError> {
    let requested = usize::try_from(input.length).map_err(|_| {
        FnvFoldSemanticCFunctionError::InvalidInputLength {
            requested: input.length,
            available: input.bytes.len(),
        }
    })?;
    if requested > input.bytes.len() {
        return Err(FnvFoldSemanticCFunctionError::InvalidInputLength {
            requested: input.length,
            available: input.bytes.len(),
        });
    }
    if requested > MAX_DIFFERENTIAL_INPUT_BYTES {
        return Err(FnvFoldSemanticCFunctionError::DifferentialInputTooLarge(
            requested,
        ));
    }
    Ok(requested)
}

fn evaluate_prepared_source(
    artifact: &SsaArtifact,
    candidate: &CertifiedFnvFoldSemanticCFunction,
    input: &FnvFoldDifferentialInput,
    limits: Option<PreparedFunctionLimits>,
) -> Result<u64, FnvFoldSemanticCFunctionError> {
    let length = validate_input(input)?;
    let dynamic_blocks = length
        .checked_mul(4)
        .and_then(|steps| steps.checked_add(16))
        .ok_or_else(|| {
            FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "prepared FNV block budget overflow".to_string(),
            ])
        })?;
    let graph_instructions = artifact.graph().insts.len().max(1);
    let dynamic_instructions = dynamic_blocks
        .checked_mul(graph_instructions)
        .ok_or_else(|| {
            FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "prepared FNV instruction budget overflow".to_string(),
            ])
        })?;
    let limits = limits.unwrap_or(PreparedFunctionLimits {
        max_block_steps: u32::try_from(dynamic_blocks).map_err(|_| {
            FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "prepared FNV block budget is unsupported".to_string(),
            ])
        })?,
        max_instruction_steps: u32::try_from(dynamic_instructions).map_err(|_| {
            FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "prepared FNV instruction budget is unsupported".to_string(),
            ])
        })?,
        max_memory_bytes: u32::try_from(length.max(1)).map_err(|_| {
            FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "prepared FNV memory budget is unsupported".to_string(),
            ])
        })?,
    });
    let memory_space = candidate.witness().byte_load().space();
    let initial_memory = input.bytes[..length]
        .iter()
        .enumerate()
        .map(|(index, byte)| {
            Ok((
                DifferentialMemoryLocation {
                    space: memory_space,
                    byte_address: DIFFERENTIAL_INPUT_BASE
                        .checked_add(index as u64)
                        .ok_or_else(|| {
                            FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                                "prepared FNV input address overflow".to_string(),
                            ])
                        })?,
                },
                *byte,
            ))
        })
        .collect::<Result<Vec<_>, FnvFoldSemanticCFunctionError>>()?;
    let execution = execute_prepared_function_return(
        artifact,
        [
            (
                candidate.abi().pointer().value(),
                DifferentialBitVector::new(
                    candidate.abi().pointer().width_bits(),
                    DIFFERENTIAL_INPUT_BASE,
                )
                .ok_or_else(|| {
                    FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                        "prepared FNV pointer width is unsupported".to_string(),
                    ])
                })?,
            ),
            (
                candidate.abi().remaining().value(),
                DifferentialBitVector::new(candidate.abi().remaining().width_bits(), input.length)
                    .ok_or_else(|| {
                        FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                            "prepared FNV length width is unsupported".to_string(),
                        ])
                    })?,
            ),
        ],
        initial_memory,
        limits,
    )
    .map_err(|error| {
        FnvFoldSemanticCFunctionError::InvalidComposition(vec![format!(
            "prepared FNV SSA/CFG execution failed: {error}"
        )])
    })?;
    let [returned] = execution.returned.as_ref() else {
        return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
            "prepared FNV SSA/CFG did not return one value".to_string(),
        ]));
    };
    if returned.width_bits() != 64 {
        return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
            "prepared FNV SSA/CFG return is not 64 bits".to_string(),
        ]));
    }
    let expected_access = candidate.witness().byte_load().access();
    let expected_producer = candidate.witness().byte_load().producer();
    let reads = execution
        .memory_events
        .iter()
        .filter(|event| event.kind == DifferentialMemoryEventKind::Read)
        .collect::<Vec<_>>();
    if execution.memory_events.len() != length || reads.len() != length {
        return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
            "prepared FNV SSA/CFG observed an unexpected memory event count".to_string(),
        ]));
    }
    for (ordinal, (event, byte)) in reads.iter().zip(&input.bytes[..length]).enumerate() {
        let expected_address = DIFFERENTIAL_INPUT_BASE
            .checked_add(ordinal as u64)
            .ok_or_else(|| {
                FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                    "prepared FNV observed address overflow".to_string(),
                ])
            })?;
        if event.producer != expected_producer
            || event.access != expected_access
            || event.space != memory_space
            || event.byte_address != expected_address
            || event.width_bits != 8
            || event.value.width_bits() != 8
            || event.value.bits() != u64::from(*byte)
        {
            return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "prepared FNV SSA/CFG byte-read trace differs from its certificate".to_string(),
            ]));
        }
    }
    Ok(returned.bits())
}

fn evaluate_candidate(
    program: FnvFoldRenderProgram,
    input: &FnvFoldDifferentialInput,
) -> Result<u64, FnvFoldSemanticCFunctionError> {
    let length = validate_input(input)?;
    let mut hash = program.offset_basis;
    let mut pointer = 0_u64;
    let mut remaining = input.length;
    let mut iterations = 0_usize;
    let mut continue_loop = if program.zero_guard_returns_when_empty {
        remaining != 0
    } else {
        remaining == 0
    };
    while continue_loop {
        let index = usize::try_from(pointer).map_err(|_| {
            FnvFoldSemanticCFunctionError::InvalidInputLength {
                requested: input.length,
                available: input.bytes.len(),
            }
        })?;
        let byte =
            *input
                .bytes
                .get(index)
                .ok_or(FnvFoldSemanticCFunctionError::InvalidInputLength {
                    requested: input.length,
                    available: input.bytes.len(),
                })?;
        let original = u32::from(byte);
        let range = original.wrapping_sub(program.ascii_upper_base);
        let lowercase = original | program.ascii_lowercase_mask;
        let predicate = range < program.ascii_upper_span;
        let folded = if predicate == program.lowercase_on_true {
            lowercase
        } else {
            original
        };
        hash = (hash ^ u64::from(folded)).wrapping_mul(program.prime);
        pointer = pointer.wrapping_add(program.pointer_step);
        remaining = remaining.wrapping_sub(program.remaining_step);
        iterations += 1;
        continue_loop = (remaining != 0) == program.latch_continues_when_nonzero;
        if iterations > length {
            return Err(FnvFoldSemanticCFunctionError::InvalidComposition(vec![
                "candidate FNV latch exceeded its exact input bound".to_string(),
            ]));
        }
    }
    Ok(hash)
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;
    use std::fs;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    use r2il::{ArchSpec, R2ILOp, SpaceId};
    use r2sleigh_lift::{Disassembler, build_arch_spec};
    use r2ssa::{
        CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierProjection,
        SourceFunctionInterface, SourceLogicalValue, SourceType, SourceTypeGraph,
    };
    use sha2::{Digest, Sha256};

    use super::*;

    const REAL_FNV_SOURCE_SHA256: &str =
        "6524278ba4cd32a72dcf9cbcc385275999a50c3449d0e97035736891bcddff09";
    const REAL_FNV_O2_FUNCTION_SHA256: &str =
        "127862f7bb0f1efcdd2830dd5bec8eadd8ac9812a847f477909b95fec671b6ac";
    const REAL_FNV_O2_BINARY_SHA256: &str =
        "e15adf9d8916bdbc1a45a07741734279cc815b87a5b2762cfb24cd78d33503c1";
    const REAL_FNV_O2_BINARY_PATH: &str = "tests/r2r/bins/r2sleigh_manual_limits_O2";
    const REAL_FNV_O2_COMPILER_COMMAND: &str =
        "cc -O2 -g -o tests/r2r/bins/r2sleigh_manual_limits_O2 tests/gold/manual_limits.c";
    const REAL_FNV_O2_BASE: u64 = 0x1_0000_0594;
    const REAL_FNV_O2_BLOCKS: &[&str] = &[
        "e80300aa607080d2a073aef200f6c1f2a08ce2f2810100b4",
        "693680d20920c0f2",
        "0a1540384b0501514c011b327f6900718a318a1a0a000aca407d099b210400f101ffff54",
        "c0035fd6",
    ];

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

    fn sha256_hex(bytes: &[u8]) -> String {
        format!("{:x}", Sha256::digest(bytes))
    }

    fn real_storage(arch: &ArchSpec, register: &str) -> CanonicalStorageId {
        let register = arch
            .get_register(register)
            .expect("pinned AARCH64 register");
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: register.offset,
            size: register.size,
        }
    }

    fn real_interface(arch: &ArchSpec, revision: &[u8]) -> SourceFunctionInterface {
        let types = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
            ],
            [],
        )
        .expect("real FNV type graph");
        let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, real_storage(arch, "x0")),
                SourceAbiParameterSpec::new(1, real_storage(arch, "x1")),
            ],
            SourceFunctionReturn::Register {
                storage: real_storage(arch, "x0"),
            },
            [],
            [
                SourceLogicalValue::new(1, full64),
                SourceLogicalValue::new(2, full64),
            ],
            Some(SourceLogicalValue::new(2, full64)),
            Some(types),
        )
        .expect("real FNV interface")
    }

    fn real_o2_artifact_with_revision(revision: &[u8]) -> SsaArtifact {
        let provenance = format!(
            "binary={REAL_FNV_O2_BINARY_PATH} binary_sha256={REAL_FNV_O2_BINARY_SHA256} command={REAL_FNV_O2_COMPILER_COMMAND}"
        );
        assert_eq!(
            sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
            REAL_FNV_SOURCE_SHA256,
            "source provenance changed: {provenance}"
        );
        assert_eq!(
            sha256_hex(include_bytes!(
                "../../../tests/r2r/bins/r2sleigh_manual_limits_O2"
            )),
            REAL_FNV_O2_BINARY_SHA256,
            "binary provenance changed: {provenance}"
        );
        let function_bytes = REAL_FNV_O2_BLOCKS
            .iter()
            .flat_map(|encoded| decode_hex(encoded))
            .collect::<Vec<_>>();
        assert_eq!(function_bytes.len(), 72, "{provenance}");
        assert_eq!(
            sha256_hex(&function_bytes),
            REAL_FNV_O2_FUNCTION_SHA256,
            "function-byte provenance changed: {provenance}"
        );

        let arch = build_arch_spec(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AARCH64 architecture");
        let disassembler = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AARCH64 disassembler");
        let mut address = REAL_FNV_O2_BASE;
        let blocks = REAL_FNV_O2_BLOCKS
            .iter()
            .map(|encoded| {
                let bytes = decode_hex(encoded);
                let block = disassembler
                    .lift_block(&bytes, address, bytes.len())
                    .expect("pinned real ARM64 O2 FNV block");
                assert_eq!(
                    block.size as usize,
                    bytes.len(),
                    "real block must be fully consumed"
                );
                address += bytes.len() as u64;
                block
            })
            .collect::<Vec<_>>();
        let spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(!spaces.is_empty(), "real FNV lift must access memory");
        assert!(
            spaces.iter().all(|space| *space == SpaceId::Ram),
            "real ARM64 FNV accesses must use Ram: {spaces:?}"
        );
        let interface = real_interface(&arch, revision);
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .expect("prepared real ARM64 O2 FNV artifact")
    }

    fn real_o2_artifact() -> SsaArtifact {
        real_o2_artifact_with_revision(b"real-arm64-fnv-fold-o2-v1")
    }

    fn real_function_with_revision(
        revision: &[u8],
    ) -> (SsaArtifact, CertifiedFnvFoldSemanticCFunction) {
        let artifact = real_o2_artifact_with_revision(revision);
        let function = CertifiedFnvFoldSemanticCFunction::from_artifact(&artifact)
            .expect("real ARM64 O2 FNV semantic C");
        (artifact, function)
    }

    fn real_function() -> (SsaArtifact, CertifiedFnvFoldSemanticCFunction) {
        let artifact = real_o2_artifact();
        let function = CertifiedFnvFoldSemanticCFunction::from_artifact(&artifact)
            .expect("real ARM64 O2 FNV semantic C");
        (artifact, function)
    }

    fn assert_refused(function: &CertifiedFnvFoldSemanticCFunction) {
        assert!(!function.audit().has_exact_fnv_fold_function());
        assert!(function.render_certified_c().is_err());
    }

    fn probes() -> Vec<FnvFoldDifferentialInput> {
        let mut probes = vec![
            FnvFoldDifferentialInput::new(Vec::new(), 0),
            FnvFoldDifferentialInput::full(b"A".to_vec()),
            FnvFoldDifferentialInput::full(b"a".to_vec()),
            FnvFoldDifferentialInput::full(b"Z".to_vec()),
            FnvFoldDifferentialInput::full(b"z".to_vec()),
            FnvFoldDifferentialInput::full(b"AbC".to_vec()),
            FnvFoldDifferentialInput::full(b"abc".to_vec()),
        ];
        let mut state = 0x4d59_5df4_d0f3_3173_u64;
        for length in 1..=32_usize {
            let mut bytes = Vec::with_capacity(length);
            for _ in 0..length {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                bytes.push((state >> 56) as u8);
            }
            probes.push(FnvFoldDifferentialInput::full(bytes));
        }
        probes
    }

    fn compiled_results(
        function: &CertifiedFnvFoldSemanticCFunction,
        probes: &[FnvFoldDifferentialInput],
    ) -> Vec<u64> {
        let function = function
            .clone()
            .with_cosmetic_names("probe", "input", "length");
        let mut source = function.render_certified_c().expect("strict FNV C");
        source.push_str("\n#include <inttypes.h>\n#include <stdio.h>\n\nint main(void) {\n");
        for (index, probe) in probes.iter().enumerate() {
            write!(&mut source, "\tstatic const uint8_t case_{index}[] = {{")
                .expect("String writes cannot fail");
            if probe.bytes().is_empty() {
                source.push_str("UINT8_C(0x0)");
            } else {
                for (byte_index, byte) in probe.bytes().iter().enumerate() {
                    if byte_index != 0 {
                        source.push_str(", ");
                    }
                    write!(&mut source, "UINT8_C(0x{byte:02x})")
                        .expect("String writes cannot fail");
                }
            }
            source.push_str("};\n");
            writeln!(
                &mut source,
                "\tprintf(\"%\" PRIu64 \"\\n\", r2s_fn_probe(case_{index}, UINT64_C(0x{:x})));",
                probe.length()
            )
            .expect("String writes cannot fail");
        }
        source.push_str("\treturn 0;\n}\n");

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("r2dec-fnv-fold-{}-{nonce}", std::process::id()));
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
            .map(|line| line.parse::<u64>().expect("integer output"))
            .collect();
        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_file(&executable);
        let _ = fs::remove_dir(&directory);
        results
    }

    #[test]
    fn real_arm64_o2_lift_certifies_and_matches_actual_prepared_ssa() {
        let provenance = format!(
            "binary={REAL_FNV_O2_BINARY_PATH} binary_sha256={REAL_FNV_O2_BINARY_SHA256} command={REAL_FNV_O2_COMPILER_COMMAND}"
        );
        assert_eq!(
            sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
            REAL_FNV_SOURCE_SHA256,
            "source provenance changed: {provenance}"
        );
        let function_bytes = REAL_FNV_O2_BLOCKS
            .iter()
            .flat_map(|encoded| decode_hex(encoded))
            .collect::<Vec<_>>();
        assert_eq!(function_bytes.len(), 72, "{provenance}");
        assert_eq!(
            sha256_hex(&function_bytes),
            REAL_FNV_O2_FUNCTION_SHA256,
            "function-byte provenance changed: {provenance}"
        );

        let artifact = real_o2_artifact();
        let function = CertifiedFnvFoldSemanticCFunction::from_artifact(&artifact)
            .expect("real ARM64 O2 FNV must certify");
        assert!(function.audit().has_exact_fnv_fold_function());
        assert!(function.render_permit().authorizes_certified_c());
        assert_eq!(
            function
                .phases()
                .iter()
                .map(FnvFoldPhase::kind)
                .collect::<Vec<_>>(),
            ALL_PHASES
        );
        let c = function.render_certified_c().expect("strict real FNV C");
        assert!(c.contains("uint64_t r2s_fn_certified_fnv_fold(const uint8_t *r2s_arg_bytes, uint64_t r2s_arg_length)"));
        assert_eq!(c.matches("while (").count(), 1);
        assert_eq!(c.matches("= *r2s_local_pointer;").count(), 1);
        assert!(c.contains("UINT64_C(0x14650fb0739d0383)"));
        assert!(c.contains("UINT64_C(0x100000001b3)"));
        assert!(c.contains("UINT32_C(0x41)"));
        assert!(c.contains("UINT32_C(0x1a)"));
        assert!(c.contains("UINT32_C(0x20)"));
        for forbidden in [
            "char *",
            "r2s_read",
            "memcpy",
            "goto",
            "break;",
            "while (UINT8_C(0x1)",
        ] {
            assert!(!c.contains(forbidden), "forbidden C spelling: {forbidden}");
        }

        let probes = probes();
        let report = check_fnv_fold_differential(&artifact, &function, probes.clone())
            .expect("real ARM64 O2 FNV actual prepared-SSA differential");
        assert!(report.has_equivalence());
        assert_eq!(report.cases().len(), probes.len());
        assert_eq!(
            report.cases()[0].source_result(),
            CERTIFIED_FNV_OFFSET_BASIS
        );
        assert_eq!(report.cases()[0].source_result(), 0x1465_0fb0_739d_0383);
        assert_eq!(report.cases()[1].source_result(), 0x44bd_8ad4_73cd_9906);
        assert_eq!(report.cases()[3].source_result(), 0x44bd_a1d4_73cd_c01b);
        assert_eq!(report.cases()[5].source_result(), 0xe168_0151_0db8_9efd);
        assert_eq!(report.cases()[6].source_result(), 0xe168_0151_0db8_9efd);
        assert_eq!(
            report.cases()[1].source_result(),
            report.cases()[2].source_result()
        );
        assert_eq!(
            report.cases()[3].source_result(),
            report.cases()[4].source_result()
        );
        assert_eq!(
            report.cases()[5].source_result(),
            report.cases()[6].source_result()
        );
        assert!(matches!(
            check_fnv_fold_differential(
                &artifact,
                &function,
                (0..=MAX_DIFFERENTIAL_CASES).map(|_| FnvFoldDifferentialInput::new(Vec::new(), 0)),
            ),
            Err(FnvFoldSemanticCFunctionError::TooManyDifferentialCases(_))
        ));
        assert!(matches!(
            check_fnv_fold_differential(
                &artifact,
                &function,
                [FnvFoldDifferentialInput::new(vec![b'A'], 2)],
            ),
            Err(FnvFoldSemanticCFunctionError::InvalidInputLength { .. })
        ));
        let expected = report
            .cases()
            .iter()
            .map(FnvFoldDifferentialCase::source_result)
            .collect::<Vec<_>>();
        assert_eq!(compiled_results(&function, &probes), expected);
    }

    #[test]
    fn dropped_duplicated_or_reordered_phases_fail_before_rendering() {
        let (_, function) = real_function();
        for dropped in 0..function.phases.len() {
            let mut corrupt = function.clone();
            let mut phases = corrupt.phases.to_vec();
            phases.remove(dropped);
            corrupt.phases = phases.into_boxed_slice();
            assert_refused(&corrupt);
        }
        let mut duplicate = function.clone();
        let mut phases = duplicate.phases.to_vec();
        phases.insert(5, phases[5]);
        duplicate.phases = phases.into_boxed_slice();
        assert_refused(&duplicate);

        let mut reordered = function;
        let mut phases = reordered.phases.to_vec();
        phases.swap(5, 6);
        reordered.phases = phases.into_boxed_slice();
        assert_refused(&reordered);
    }

    #[test]
    fn polarity_constants_pointer_and_remaining_latch_mutations_are_refused() {
        let (_, function) = real_function();
        let mutate = |change: fn(&mut FnvFoldRenderProgram)| {
            let mut corrupt = function.clone();
            change(&mut corrupt.program);
            assert_refused(&corrupt);
        };
        mutate(|program| program.lowercase_on_true = false);
        mutate(|program| program.zero_guard_returns_when_empty = false);
        mutate(|program| program.offset_basis ^= 1);
        mutate(|program| program.prime ^= 1);
        mutate(|program| program.ascii_upper_base += 1);
        mutate(|program| program.ascii_upper_span -= 1);
        mutate(|program| program.ascii_lowercase_mask ^= 1);
        mutate(|program| program.pointer_step = 2);
        mutate(|program| program.remaining_step = 2);
        mutate(|program| program.latch_continues_when_nonzero = false);
        mutate(|program| program.load_width_bytes = 2);
    }

    #[test]
    fn stale_mapping_permit_abi_and_witness_are_refused() {
        let (_, candidate) = real_function();

        let mut stale_abi = candidate.clone();
        stale_abi.abi.return_storage = stale_abi.abi.remaining_storage;
        assert_refused(&stale_abi);

        let mut dropped_mapping = candidate.clone();
        dropped_mapping.mappings = dropped_mapping.mappings[..dropped_mapping.mappings.len() - 1]
            .to_vec()
            .into_boxed_slice();
        assert_refused(&dropped_mapping);

        let mut duplicate_mapping = candidate.clone();
        let mut mappings = duplicate_mapping.mappings.to_vec();
        mappings.push(mappings[0].clone());
        duplicate_mapping.mappings = mappings.into_boxed_slice();
        assert_refused(&duplicate_mapping);

        let (_, other) = real_function_with_revision(b"real-arm64-fnv-fold-o2-v2");
        assert_ne!(candidate.witness(), other.witness());
        let mut stale_witness = candidate.clone();
        stale_witness.witness = other.witness.clone();
        assert_refused(&stale_witness);

        let mut stale_permit = candidate;
        stale_permit.render_permit = other.render_permit.clone();
        assert_refused(&stale_permit);
    }
}
