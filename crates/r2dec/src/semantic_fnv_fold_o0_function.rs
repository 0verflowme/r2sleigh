//! Proof-preserving strict-C rendering for the sealed ARM64 O0 FNV fold.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_FNV_FOLD_O0_CONTRACT_VERSION, CERTIFIED_FNV_FOLD_O0_OFFSET_BASIS,
    CERTIFIED_FNV_FOLD_O0_PRIME, CertifiedArtifactOrigin, CertifiedFnvFoldO0AccessId,
    CertifiedFnvFoldO0DispositionClass, CertifiedFnvFoldO0Function, CertifiedFnvFoldO0MemoryUse,
    CertifiedFnvFoldO0Phase, CertifiedMachineFunction, CertifiedRenderPermit,
    CertifiedTypedRegionKind, EffectDisposition, RenderAuthorizationError, TypedRegionMapping,
    certify_fnv_fold_o0_region,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace, MachineAddressSpace,
    MachineBuildError, MachineMemoryEndianness, MachineSignedness, MachineType,
    MachineValueBinding, ObjectId, SemanticObligationId, SourceCarrierKind, SourceFunctionReturn,
    SourceTypeKind, SsaArtifact,
};
use serde::Serialize;

use crate::semantic_differential::{
    DifferentialBitVector, DifferentialMemoryEventKind, DifferentialMemoryLocation,
    PreparedFunctionLimits, execute_prepared_function_return,
};

pub const CERTIFIED_FNV_FOLD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_FNV_FOLD_O0_CONTRACT_VERSION;

const MAX_DIFFERENTIAL_CASES: usize = 256;
const MAX_DIFFERENTIAL_INPUT_BYTES: usize = 4096;
const DIFFERENTIAL_INPUT_BASE: u64 = 0x40_0000;
const ASCII_UPPER_BASE: u32 = 0x41;
const ASCII_UPPER_SPAN: u32 = 0x1a;
const ASCII_LOWERCASE_MASK: u32 = 0x20;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FnvFoldO0SemanticCFunctionScope {
    ClosedCanonicalAarch64O0ByteFold,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum FnvFoldO0RenderPhaseKind {
    InitialState,
    ZeroGuard,
    ByteRead,
    AsciiNormalization,
    HashTransition,
    CursorTransition,
    Latch,
    Return,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0RenderPhase {
    kind: FnvFoldO0RenderPhaseKind,
    anchor: CanonicalInstructionId,
}

impl FnvFoldO0RenderPhase {
    pub const fn kind(&self) -> FnvFoldO0RenderPhaseKind {
        self.kind
    }

    pub const fn anchor(&self) -> CanonicalInstructionId {
        self.anchor
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FnvFoldO0ProducerTarget {
    Rendered(FnvFoldO0RenderPhaseKind),
    Absorbed(CertifiedFnvFoldO0DispositionClass),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0ProducerDisposition {
    producer: CanonicalInstructionId,
    certificate_class: CertifiedFnvFoldO0DispositionClass,
    target: FnvFoldO0ProducerTarget,
}

impl FnvFoldO0ProducerDisposition {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn certificate_class(&self) -> CertifiedFnvFoldO0DispositionClass {
        self.certificate_class
    }

    pub const fn target(&self) -> FnvFoldO0ProducerTarget {
        self.target
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0AliasSeal {
    external_read: CertifiedFnvFoldO0AccessId,
    external_object: ObjectId,
    classified_frame_objects: Box<[ObjectId]>,
    external_memory_use: CertifiedFnvFoldO0MemoryUse,
}

impl FnvFoldO0AliasSeal {
    pub const fn external_read(&self) -> CertifiedFnvFoldO0AccessId {
        self.external_read
    }

    pub const fn external_object(&self) -> ObjectId {
        self.external_object
    }

    pub const fn classified_frame_objects(&self) -> &[ObjectId] {
        &self.classified_frame_objects
    }

    pub const fn external_memory_use(&self) -> &CertifiedFnvFoldO0MemoryUse {
        &self.external_memory_use
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0AbiManifest {
    revision_identity: Box<[u8]>,
    pointer_index: u32,
    pointer_storage: CanonicalStorageId,
    pointer: MachineValueBinding,
    length_index: u32,
    length_storage: CanonicalStorageId,
    length: MachineValueBinding,
    return_storage: CanonicalStorageId,
}

impl FnvFoldO0AbiManifest {
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

    pub const fn length_index(&self) -> u32 {
        self.length_index
    }

    pub const fn length_storage(&self) -> CanonicalStorageId {
        self.length_storage
    }

    pub const fn length(&self) -> MachineValueBinding {
        self.length
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0RenderProgram {
    offset_basis: u64,
    prime: u64,
    ascii_upper_base: u32,
    ascii_upper_span: u32,
    ascii_lowercase_mask: u32,
    pointer_step: u64,
    remaining_step: u64,
    load_width_bytes: u32,
    continue_when_remaining_nonzero: bool,
}

impl FnvFoldO0RenderProgram {
    pub const fn offset_basis(&self) -> u64 {
        self.offset_basis
    }

    pub const fn prime(&self) -> u64 {
        self.prime
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0RenderNames {
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

impl FnvFoldO0RenderNames {
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0SemanticCFunction {
    schema_version: u32,
    scope: FnvFoldO0SemanticCFunctionScope,
    names: FnvFoldO0RenderNames,
    origin: CertifiedArtifactOrigin,
    witness: CertifiedFnvFoldO0Function,
    abi: FnvFoldO0AbiManifest,
    sealed_program: FnvFoldO0RenderProgram,
    program: FnvFoldO0RenderProgram,
    source_phases: Box<[CertifiedFnvFoldO0Phase]>,
    render_phases: Box<[FnvFoldO0RenderPhase]>,
    producer_dispositions: Box<[FnvFoldO0ProducerDisposition]>,
    dead_structural_producers: Box<[CanonicalInstructionId]>,
    alias_seal: Option<FnvFoldO0AliasSeal>,
    mappings: Box<[TypedRegionMapping]>,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FnvFoldO0SemanticCFunctionError {
    Machine(MachineBuildError),
    Authorization(RenderAuthorizationError),
    MissingFnvFoldO0Witness,
    InvalidMemorySeal,
    InvalidInterface,
    InvalidInputLength { requested: u64, available: usize },
    TooManyDifferentialCases(usize),
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for FnvFoldO0SemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "O0 FNV-fold semantic C function failed: {self:?}")
    }
}

impl std::error::Error for FnvFoldO0SemanticCFunctionError {}

impl From<MachineBuildError> for FnvFoldO0SemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RenderAuthorizationError> for FnvFoldO0SemanticCFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl CertifiedFnvFoldO0SemanticCFunction {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, FnvFoldO0SemanticCFunctionError> {
        let certified = CertifiedMachineFunction::from_artifact(artifact)?;
        Self::from_certified(&certified)
    }

    pub fn from_certified(
        certified: &CertifiedMachineFunction,
    ) -> Result<Self, FnvFoldO0SemanticCFunctionError> {
        let witness = certified
            .fnv_fold_o0()
            .ok_or(FnvFoldO0SemanticCFunctionError::MissingFnvFoldO0Witness)?
            .clone();
        if !certified.projection().failures().is_empty() {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidMemorySeal);
        }
        let abi = expected_abi(&witness)?;
        let program = expected_program(&witness)?;
        let source_phases = witness.phases().to_vec().into_boxed_slice();
        let render_phases = expected_render_phases(&witness)?.into_boxed_slice();
        let producer_dispositions = expected_producer_dispositions(&witness)?.into_boxed_slice();
        let dead_structural_producers =
            expected_dead_structural_producers(&witness).into_boxed_slice();
        let alias_seal = Some(expected_alias_seal(&witness)?);
        let mappings = exact_mappings(certified)?.into_boxed_slice();
        if mappings.as_ref() != expected_mappings(&witness)?.as_slice() {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "O0 FNV ledger differs from the sealed disposition inventory".to_string(),
            ]));
        }
        let render_permit = certify_fnv_fold_o0_region(
            certified.origin(),
            certified.ledger(),
            mappings.iter().cloned(),
            &witness,
        )?;
        let function = Self {
            schema_version: CERTIFIED_FNV_FOLD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: FnvFoldO0SemanticCFunctionScope::ClosedCanonicalAarch64O0ByteFold,
            names: default_names(),
            origin: certified.origin().clone(),
            witness,
            abi,
            sealed_program: program,
            program,
            source_phases,
            render_phases,
            producer_dispositions,
            dead_structural_producers,
            alias_seal,
            mappings,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_fnv_fold_o0_function() {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> FnvFoldO0SemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &FnvFoldO0RenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn witness(&self) -> &CertifiedFnvFoldO0Function {
        &self.witness
    }

    pub const fn abi(&self) -> &FnvFoldO0AbiManifest {
        &self.abi
    }

    pub const fn program(&self) -> FnvFoldO0RenderProgram {
        self.program
    }

    pub const fn source_phases(&self) -> &[CertifiedFnvFoldO0Phase] {
        &self.source_phases
    }

    pub const fn render_phases(&self) -> &[FnvFoldO0RenderPhase] {
        &self.render_phases
    }

    pub const fn producer_dispositions(&self) -> &[FnvFoldO0ProducerDisposition] {
        &self.producer_dispositions
    }

    /// Exact sealed producer-only structural-phi subset absorbed before rendering.
    pub const fn dead_structural_producers(&self) -> &[CanonicalInstructionId] {
        &self.dead_structural_producers
    }

    pub const fn alias_seal(&self) -> Option<&FnvFoldO0AliasSeal> {
        self.alias_seal.as_ref()
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

    pub fn audit(&self) -> FnvFoldO0SemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_FNV_FOLD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION
            || self.scope != FnvFoldO0SemanticCFunctionScope::ClosedCanonicalAarch64O0ByteFold
        {
            invalid.push("O0 FNV renderer schema or scope mismatch".to_string());
        }
        if self.witness.origin() != &self.origin
            || self.witness.contract_version() != CERTIFIED_FNV_FOLD_O0_CONTRACT_VERSION
        {
            invalid.push("O0 FNV witness origin mismatch".to_string());
        }
        match expected_abi(&self.witness) {
            Ok(expected) if expected == self.abi => {}
            _ => invalid.push("O0 FNV ABI mismatch".to_string()),
        }
        match expected_program(&self.witness) {
            Ok(expected) if expected == self.program && expected == self.sealed_program => {}
            _ => invalid.push("O0 FNV strict-C program mismatch".to_string()),
        }
        if self.source_phases.as_ref() != self.witness.phases() {
            invalid.push("O0 FNV source phase loss or reorder".to_string());
        }
        match expected_render_phases(&self.witness) {
            Ok(expected) if expected.as_slice() == self.render_phases.as_ref() => {}
            _ => invalid.push("O0 FNV render phase loss, duplication, or reorder".to_string()),
        }
        match expected_producer_dispositions(&self.witness) {
            Ok(expected) if expected.as_slice() == self.producer_dispositions.as_ref() => {}
            _ => invalid.push("O0 FNV producer accounting mismatch".to_string()),
        }
        let expected_dead = expected_dead_structural_producers(&self.witness);
        if self.dead_structural_producers.as_ref() != expected_dead.as_slice() {
            invalid.push("O0 FNV dead structural-phi subset mismatch".to_string());
        }
        let obligation_producers = self
            .witness
            .obligation_dispositions()
            .iter()
            .map(|(obligation, _)| obligation.instruction)
            .collect::<BTreeSet<_>>();
        let rendered_producers = self
            .producer_dispositions
            .iter()
            .filter_map(|entry| {
                matches!(entry.target(), FnvFoldO0ProducerTarget::Rendered(_))
                    .then_some(entry.producer())
            })
            .collect::<BTreeSet<_>>();
        let absorbed_dead = self
            .producer_dispositions
            .iter()
            .filter_map(|entry| {
                (entry.certificate_class() == CertifiedFnvFoldO0DispositionClass::ProvenDead
                    && entry.target()
                        == FnvFoldO0ProducerTarget::Absorbed(
                            CertifiedFnvFoldO0DispositionClass::ProvenDead,
                        ))
                .then_some(entry.producer())
            })
            .collect::<BTreeSet<_>>();
        let expected_dead_set = expected_dead.iter().copied().collect::<BTreeSet<_>>();
        if expected_dead.is_empty()
            || absorbed_dead != expected_dead_set
            || !expected_dead_set.is_disjoint(&obligation_producers)
            || !expected_dead_set.is_disjoint(&rendered_producers)
            || self
                .render_phases
                .iter()
                .any(|phase| expected_dead_set.contains(&phase.anchor()))
        {
            invalid.push(
                "O0 FNV dead structural producers leaked into obligations or emitted semantics"
                    .to_string(),
            );
        }
        match expected_alias_seal(&self.witness) {
            Ok(expected) if self.alias_seal.as_ref() == Some(&expected) => {}
            _ => invalid.push("O0 FNV external alias/projection seal mismatch".to_string()),
        }
        let instruction_counts = counts(
            self.producer_dispositions
                .iter()
                .map(FnvFoldO0ProducerDisposition::producer),
        );
        let source_instructions = self
            .origin
            .source()
            .instructions()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        if instruction_counts.keys().copied().collect::<BTreeSet<_>>() != source_instructions
            || instruction_counts.values().any(|count| *count != 1)
        {
            invalid.push("O0 FNV instruction inventory is not mapped exactly once".to_string());
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
        match expected_mappings(&self.witness) {
            Ok(expected) if self.mappings.as_ref() == expected.as_slice() => {}
            _ => invalid.push("O0 FNV obligation disposition inventory mismatch".to_string()),
        }
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::FnvFoldO0Function,
            CERTIFIED_FNV_FOLD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            &self.mappings,
        ) {
            invalid.push("O0 FNV render permit mismatch".to_string());
        }
        FnvFoldO0SemanticCFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, FnvFoldO0SemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_fnv_fold_o0_function() || !self.render_permit.authorizes_certified_c()
        {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(
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

fn default_names() -> FnvFoldO0RenderNames {
    FnvFoldO0RenderNames {
        function: "certified_fnv_fold_o0".to_string(),
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
    fn new(names: &FnvFoldO0RenderNames) -> Self {
        let mut used = BTreeSet::new();
        Self {
            function: unique_render_identifier(&mut used, "r2s_fn", &names.function),
            bytes: unique_render_identifier(&mut used, "r2s_arg", &names.bytes),
            length: unique_render_identifier(&mut used, "r2s_arg", &names.length),
            pointer: unique_render_identifier(&mut used, "r2s_local", &names.pointer),
            remaining: unique_render_identifier(&mut used, "r2s_local", &names.remaining),
            hash: unique_render_identifier(&mut used, "r2s_local", &names.hash),
            byte: unique_render_identifier(&mut used, "r2s_local", &names.byte),
            original: unique_render_identifier(&mut used, "r2s_local", &names.original),
            range: unique_render_identifier(&mut used, "r2s_local", &names.range),
            lowercase: unique_render_identifier(&mut used, "r2s_local", &names.lowercase),
            folded: unique_render_identifier(&mut used, "r2s_local", &names.folded),
        }
    }
}

fn unique_render_identifier(used: &mut BTreeSet<String>, prefix: &str, requested: &str) -> String {
    let base = c_identifier(prefix, requested);
    if used.insert(base.clone()) {
        return base;
    }
    for suffix in 2_u32.. {
        let candidate = format!("{base}_{suffix}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("the finite rendered-name set cannot exhaust u32 suffixes")
}

fn expected_abi(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<FnvFoldO0AbiManifest, FnvFoldO0SemanticCFunctionError> {
    let interface = witness
        .origin()
        .machine_context()
        .source()
        .function_interface()
        .ok_or(FnvFoldO0SemanticCFunctionError::InvalidInterface)?;
    let [pointer_logical, length_logical] = interface.parameter_logical_values() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    let Some(return_logical) = interface.return_logical_value() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    let Some(graph) = interface.type_graph() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    let [byte, pointer, integer] = graph.types() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    let pointer_parameter = witness.pointer_parameter();
    let length_parameter = witness.length_parameter();
    let Some(pointer_value) = pointer_parameter.value() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    let Some(length_value) = length_parameter.value() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    let full64 = |logical: r2ssa::SourceLogicalValue| {
        logical.carrier().kind() == SourceCarrierKind::Full
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == 64
    };
    let exact = interface.revision_identity() == witness.revision_identity()
        && interface.stack_slots().len() == 5
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
        && *pointer_logical == witness.pointer_logical()
        && *length_logical == witness.length_logical()
        && return_logical == witness.return_logical()
        && pointer_logical.type_id() == 1
        && length_logical.type_id() == 2
        && return_logical.type_id() == 2
        && full64(*pointer_logical)
        && full64(*length_logical)
        && full64(return_logical)
        && pointer_parameter.index() == 0
        && length_parameter.index() == 1
        && pointer_parameter.storage().space == CanonicalStorageSpace::Register
        && length_parameter.storage().space == CanonicalStorageSpace::Register
        && pointer_parameter.storage().size == 8
        && length_parameter.storage().size == 8
        && pointer_value.producer().is_none()
        && length_value.producer().is_none()
        && pointer_value.ty()
            == &MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            }
        && length_value.ty()
            == &MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            }
        && witness.memory_address_bits() == 64
        && witness.memory_word_size_bytes() == 1
        && witness.memory_endianness() == MachineMemoryEndianness::Little
        && witness.memory_space() == MachineAddressSpace::Ram
        && matches!(interface.return_kind(), SourceFunctionReturn::Register { storage }
			if storage == witness.return_storage() && storage.size == 8);
    if !exact {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    }
    Ok(FnvFoldO0AbiManifest {
        revision_identity: witness.revision_identity().to_vec().into_boxed_slice(),
        pointer_index: pointer_parameter.index(),
        pointer_storage: pointer_parameter.storage(),
        pointer: pointer_value.binding(),
        length_index: length_parameter.index(),
        length_storage: length_parameter.storage(),
        length: length_value.binding(),
        return_storage: witness.return_storage(),
    })
}

fn expected_program(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<FnvFoldO0RenderProgram, FnvFoldO0SemanticCFunctionError> {
    let alias = witness.external_alias_policy();
    if witness.hash().offset_basis() != CERTIFIED_FNV_FOLD_O0_OFFSET_BASIS
        || witness.hash().prime_value() != CERTIFIED_FNV_FOLD_O0_PRIME
        || !alias.complete_frame_separation()
        || !alias.frame_address_escape_free()
        || !alias.source_external_byte_pointer()
        || witness.index().buffer_access() != alias.external_read()
        || witness.index().buffer_object() != alias.external_object()
        || !witness.conservative_alias_only_header_phis().is_empty()
    {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidMemorySeal);
    }
    Ok(FnvFoldO0RenderProgram {
        offset_basis: CERTIFIED_FNV_FOLD_O0_OFFSET_BASIS,
        prime: CERTIFIED_FNV_FOLD_O0_PRIME,
        ascii_upper_base: ASCII_UPPER_BASE,
        ascii_upper_span: ASCII_UPPER_SPAN,
        ascii_lowercase_mask: ASCII_LOWERCASE_MASK,
        pointer_step: 1,
        remaining_step: 1,
        load_width_bytes: 1,
        continue_when_remaining_nonzero: true,
    })
}

fn expected_render_phases(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<Vec<FnvFoldO0RenderPhase>, FnvFoldO0SemanticCFunctionError> {
    let latch = source_phase(witness, witness.topology().latch())?;
    let Some(latch_anchor) = latch.producers().last().copied() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
    };
    Ok(vec![
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::InitialState,
            anchor: witness.hash().initializer_store().producer(),
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::ZeroGuard,
            anchor: witness.loop_guard().branch(),
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::ByteRead,
            anchor: witness.external_alias_policy().external_read().producer(),
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::AsciiNormalization,
            anchor: witness.ascii().lowercase_instruction(),
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::HashTransition,
            anchor: witness.hash().multiply_instruction(),
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::CursorTransition,
            anchor: witness.index().update_instruction(),
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::Latch,
            anchor: latch_anchor,
        },
        FnvFoldO0RenderPhase {
            kind: FnvFoldO0RenderPhaseKind::Return,
            anchor: witness.return_instruction(),
        },
    ])
}

fn source_phase(
    witness: &CertifiedFnvFoldO0Function,
    block: u64,
) -> Result<&CertifiedFnvFoldO0Phase, FnvFoldO0SemanticCFunctionError> {
    witness
        .phases()
        .iter()
        .find(|phase| phase.block() == block)
        .ok_or(FnvFoldO0SemanticCFunctionError::InvalidInterface)
}

fn expected_producer_dispositions(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<Vec<FnvFoldO0ProducerDisposition>, FnvFoldO0SemanticCFunctionError> {
    let topology = witness.topology();
    let mut blocks = BTreeMap::new();
    for phase in witness.phases() {
        for producer in phase.producers() {
            if blocks.insert(*producer, phase.block()).is_some() {
                return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
            }
        }
    }
    let mut result = Vec::with_capacity(witness.instruction_dispositions().len());
    for (producer, class) in witness.instruction_dispositions() {
        let Some(block) = blocks.get(producer).copied() else {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
        };
        let target = match class {
            CertifiedFnvFoldO0DispositionClass::ProvenDead => {
                FnvFoldO0ProducerTarget::Absorbed(*class)
            }
            CertifiedFnvFoldO0DispositionClass::FrameState
            | CertifiedFnvFoldO0DispositionClass::InvariantHomeRelay
            | CertifiedFnvFoldO0DispositionClass::ForwarderControl => {
                FnvFoldO0ProducerTarget::Absorbed(*class)
            }
            CertifiedFnvFoldO0DispositionClass::ExternalAliasSealing => {
                FnvFoldO0ProducerTarget::Rendered(FnvFoldO0RenderPhaseKind::ByteRead)
            }
            CertifiedFnvFoldO0DispositionClass::Return => {
                FnvFoldO0ProducerTarget::Rendered(FnvFoldO0RenderPhaseKind::Return)
            }
            CertifiedFnvFoldO0DispositionClass::LoopControl => {
                if block == topology.header() {
                    FnvFoldO0ProducerTarget::Rendered(FnvFoldO0RenderPhaseKind::ZeroGuard)
                } else if block == topology.first_predicate_block()
                    || block == topology.second_predicate_block()
                {
                    FnvFoldO0ProducerTarget::Rendered(FnvFoldO0RenderPhaseKind::AsciiNormalization)
                } else if block == topology.latch() {
                    FnvFoldO0ProducerTarget::Rendered(FnvFoldO0RenderPhaseKind::Latch)
                } else {
                    FnvFoldO0ProducerTarget::Absorbed(*class)
                }
            }
            CertifiedFnvFoldO0DispositionClass::Semantics => {
                let kind = if block == topology.entry() {
                    FnvFoldO0RenderPhaseKind::InitialState
                } else if block == topology.header() {
                    FnvFoldO0RenderPhaseKind::ZeroGuard
                } else if block == topology.first_predicate_block()
                    && (*producer == witness.external_alias_policy().address_instruction()
                        || witness
                            .external_alias_policy()
                            .address_support_instructions()
                            .contains(producer)
                        || *producer == witness.external_alias_policy().external_read().producer())
                {
                    FnvFoldO0RenderPhaseKind::ByteRead
                } else if block == topology.first_predicate_block()
                    || block == topology.second_predicate_block()
                    || block == topology.lowercase_block()
                {
                    FnvFoldO0RenderPhaseKind::AsciiNormalization
                } else if block == topology.hash_block() {
                    FnvFoldO0RenderPhaseKind::HashTransition
                } else if block == topology.latch() {
                    FnvFoldO0RenderPhaseKind::CursorTransition
                } else if block == topology.exit() {
                    FnvFoldO0RenderPhaseKind::Return
                } else {
                    return Err(FnvFoldO0SemanticCFunctionError::InvalidInterface);
                };
                FnvFoldO0ProducerTarget::Rendered(kind)
            }
        };
        result.push(FnvFoldO0ProducerDisposition {
            producer: *producer,
            certificate_class: *class,
            target,
        });
    }
    Ok(result)
}

fn expected_alias_seal(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<FnvFoldO0AliasSeal, FnvFoldO0SemanticCFunctionError> {
    let alias = witness.external_alias_policy();
    if !alias.complete_frame_separation()
        || !alias.frame_address_escape_free()
        || !alias.source_external_byte_pointer()
        || !witness.conservative_alias_only_header_phis().is_empty()
    {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidMemorySeal);
    }
    Ok(FnvFoldO0AliasSeal {
        external_read: alias.external_read(),
        external_object: alias.external_object(),
        classified_frame_objects: alias.classified_frame_objects().to_vec().into_boxed_slice(),
        external_memory_use: alias.external_memory_use().clone(),
    })
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

fn expected_dead_structural_producers(
    witness: &CertifiedFnvFoldO0Function,
) -> Vec<CanonicalInstructionId> {
    witness
        .instruction_dispositions()
        .iter()
        .filter_map(|(producer, class)| {
            (*class == CertifiedFnvFoldO0DispositionClass::ProvenDead).then_some(*producer)
        })
        .collect()
}

fn expected_mappings(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<Vec<TypedRegionMapping>, FnvFoldO0SemanticCFunctionError> {
    witness
        .obligation_dispositions()
        .iter()
        .map(|(obligation, class)| {
            let Some(disposition) = expected_disposition(obligation.instruction, *class) else {
                return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                    "dead structural producer illegally owns an obligation".to_string(),
                ]));
            };
            Ok(TypedRegionMapping::new(*obligation, disposition))
        })
        .collect()
}

fn expected_disposition(
    producer: CanonicalInstructionId,
    class: CertifiedFnvFoldO0DispositionClass,
) -> Option<EffectDisposition> {
    match class {
        CertifiedFnvFoldO0DispositionClass::ProvenDead => None,
        CertifiedFnvFoldO0DispositionClass::FrameState => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0FrameState { producer })
        }
        CertifiedFnvFoldO0DispositionClass::InvariantHomeRelay => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0InvariantHomeRelay { producer })
        }
        CertifiedFnvFoldO0DispositionClass::ExternalAliasSealing => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0ExternalAlias { producer })
        }
        CertifiedFnvFoldO0DispositionClass::ForwarderControl => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0Forwarder { producer })
        }
        CertifiedFnvFoldO0DispositionClass::LoopControl => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0LoopControl { producer })
        }
        CertifiedFnvFoldO0DispositionClass::Semantics => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0Semantics { producer })
        }
        CertifiedFnvFoldO0DispositionClass::Return => {
            Some(EffectDisposition::AbsorbedIntoFnvFoldO0Return { producer })
        }
    }
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
pub struct FnvFoldO0SemanticCFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl FnvFoldO0SemanticCFunctionAuditReport {
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

    pub fn has_exact_fnv_fold_o0_function(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0DifferentialInput {
    bytes: Box<[u8]>,
    length: u64,
}

impl FnvFoldO0DifferentialInput {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0ObservedRead {
    ordinal: u64,
    index: u64,
    byte: u8,
    access: CertifiedFnvFoldO0AccessId,
}

impl FnvFoldO0ObservedRead {
    pub const fn ordinal(&self) -> u64 {
        self.ordinal
    }

    pub const fn index(&self) -> u64 {
        self.index
    }

    pub const fn byte(&self) -> u8 {
        self.byte
    }

    pub const fn access(&self) -> CertifiedFnvFoldO0AccessId {
        self.access
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0DifferentialCase {
    input: FnvFoldO0DifferentialInput,
    source_result: u64,
    candidate_result: u64,
    source_reads: Box<[FnvFoldO0ObservedRead]>,
    candidate_reads: Box<[FnvFoldO0ObservedRead]>,
}

impl FnvFoldO0DifferentialCase {
    pub const fn input(&self) -> &FnvFoldO0DifferentialInput {
        &self.input
    }

    pub const fn source_result(&self) -> u64 {
        self.source_result
    }

    pub const fn candidate_result(&self) -> u64 {
        self.candidate_result
    }

    pub const fn source_reads(&self) -> &[FnvFoldO0ObservedRead] {
        &self.source_reads
    }

    pub const fn candidate_reads(&self) -> &[FnvFoldO0ObservedRead] {
        &self.candidate_reads
    }

    pub fn matches(&self) -> bool {
        self.source_result == self.candidate_result && self.source_reads == self.candidate_reads
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnvFoldO0DifferentialReport {
    cases: Box<[FnvFoldO0DifferentialCase]>,
}

impl FnvFoldO0DifferentialReport {
    pub const fn cases(&self) -> &[FnvFoldO0DifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty() && self.cases.iter().all(FnvFoldO0DifferentialCase::matches)
    }
}

pub fn check_fnv_fold_o0_differential(
    artifact: &SsaArtifact,
    candidate: &CertifiedFnvFoldO0SemanticCFunction,
    inputs: impl IntoIterator<Item = FnvFoldO0DifferentialInput>,
) -> Result<FnvFoldO0DifferentialReport, FnvFoldO0SemanticCFunctionError> {
    let audit = candidate.audit();
    if !audit.has_exact_fnv_fold_o0_function() {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(
            audit.invalid,
        ));
    }
    let source = CertifiedMachineFunction::from_artifact(artifact)?;
    let source_witness = source
        .fnv_fold_o0()
        .ok_or(FnvFoldO0SemanticCFunctionError::MissingFnvFoldO0Witness)?;
    if source.origin() != candidate.origin() || source_witness != candidate.witness() {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "O0 FNV differential source and candidate origins differ".to_string(),
        ]));
    }
    validate_source_machine_witness(source_witness)?;
    let source_abi = expected_abi(source_witness)?;
    let external_read = source_witness.external_alias_policy().external_read();
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(FnvFoldO0SemanticCFunctionError::TooManyDifferentialCases(
            inputs.len(),
        ));
    }
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        validate_input(&input)?;
        let (source_result, source_reads) =
            evaluate_prepared_o0_source(artifact, source_witness, &source_abi, &input, None)?;
        let (candidate_result, candidate_reads) =
            evaluate_o0_candidate(candidate.program, external_read, &input)?;
        cases.push(FnvFoldO0DifferentialCase {
            input,
            source_result,
            candidate_result,
            source_reads: source_reads.into_boxed_slice(),
            candidate_reads: candidate_reads.into_boxed_slice(),
        });
    }
    let report = FnvFoldO0DifferentialReport {
        cases: cases.into_boxed_slice(),
    };
    if !report.has_equivalence() {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "O0 source-machine and strict-C candidate observables disagree".to_string(),
        ]));
    }
    Ok(report)
}

fn validate_source_machine_witness(
    witness: &CertifiedFnvFoldO0Function,
) -> Result<(), FnvFoldO0SemanticCFunctionError> {
    let index = witness.index();
    let ascii = witness.ascii();
    let hash = witness.hash();
    let pointer = witness.external_alias_policy().pointer_home();
    let length = witness.length_home();
    let relays_are_exact = pointer.phi().object() == pointer.initializer_version().object()
        && length.phi().object() == length.initializer_version().object()
        && index.phi().object() == index.object()
        && ascii.merge_phi().object() == ascii.object()
        && hash.phi().object() == hash.object()
        && index.initializer_version().object() == index.update_version().object()
        && hash.initializer_version().object() == hash.xor_version().object()
        && hash.xor_version().object() == hash.product_version().object()
        && ascii.initial_version().object() == ascii.lowercase_version().object()
        && witness.returned_hash_access() == hash.exit_load()
        && witness.returned_hash_version().object() == hash.object()
        && witness.return_instruction() == witness.frame().return_instruction()
        && witness.return_target() == witness.frame().return_target();
    if !relays_are_exact {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "O0 FNV frame relay or MemorySSA chain mismatch".to_string(),
        ]));
    }
    Ok(())
}

fn validate_input(
    input: &FnvFoldO0DifferentialInput,
) -> Result<usize, FnvFoldO0SemanticCFunctionError> {
    let requested = usize::try_from(input.length).map_err(|_| {
        FnvFoldO0SemanticCFunctionError::InvalidInputLength {
            requested: input.length,
            available: input.bytes.len(),
        }
    })?;
    if requested > input.bytes.len() {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInputLength {
            requested: input.length,
            available: input.bytes.len(),
        });
    }
    if requested > MAX_DIFFERENTIAL_INPUT_BYTES {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidInputLength {
            requested: input.length,
            available: MAX_DIFFERENTIAL_INPUT_BYTES,
        });
    }
    Ok(requested)
}

fn evaluate_prepared_o0_source(
    artifact: &SsaArtifact,
    witness: &CertifiedFnvFoldO0Function,
    abi: &FnvFoldO0AbiManifest,
    input: &FnvFoldO0DifferentialInput,
    limits: Option<PreparedFunctionLimits>,
) -> Result<(u64, Vec<FnvFoldO0ObservedRead>), FnvFoldO0SemanticCFunctionError> {
    let length = validate_input(input)?;
    let dynamic_blocks = length
        .checked_mul(10)
        .and_then(|steps| steps.checked_add(16))
        .ok_or_else(|| {
            FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV block budget overflow".to_string(),
            ])
        })?;
    let graph_instructions = artifact.graph().insts.len().max(1);
    let dynamic_instructions = dynamic_blocks
        .checked_mul(graph_instructions)
        .ok_or_else(|| {
            FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV instruction budget overflow".to_string(),
            ])
        })?;
    let frame_slots = witness
        .frame()
        .homes()
        .iter()
        .chain(witness.frame().locals())
        .collect::<Vec<_>>();
    let frame_bytes = frame_slots.iter().try_fold(0_usize, |total, slot| {
        usize::try_from(slot.width())
            .ok()
            .and_then(|width| total.checked_add(width))
    });
    let Some(memory_bytes) = frame_bytes.and_then(|bytes| bytes.checked_add(length.max(1))) else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "prepared O0 FNV memory budget overflow".to_string(),
        ]));
    };
    let limits = limits.unwrap_or(PreparedFunctionLimits {
        max_block_steps: u32::try_from(dynamic_blocks).map_err(|_| {
            FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV block budget is unsupported".to_string(),
            ])
        })?,
        max_instruction_steps: u32::try_from(dynamic_instructions).map_err(|_| {
            FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV instruction budget is unsupported".to_string(),
            ])
        })?,
        max_memory_bytes: u32::try_from(memory_bytes).map_err(|_| {
            FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV memory budget is unsupported".to_string(),
            ])
        })?,
    });
    let memory_space = witness.memory_space();
    let mut initial_memory = input.bytes[..length]
        .iter()
        .enumerate()
        .map(|(index, byte)| {
            Ok((
                DifferentialMemoryLocation {
                    space: memory_space,
                    byte_address: DIFFERENTIAL_INPUT_BASE
                        .checked_add(index as u64)
                        .ok_or_else(|| {
                            FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                                "prepared O0 FNV input address overflow".to_string(),
                            ])
                        })?,
                },
                *byte,
            ))
        })
        .collect::<Result<Vec<_>, FnvFoldO0SemanticCFunctionError>>()?;
    for slot in &frame_slots {
        let base = slot.offset_from_entry_sp() as u64;
        for offset in 0..u64::from(slot.width()) {
            initial_memory.push((
                DifferentialMemoryLocation {
                    space: memory_space,
                    byte_address: base.checked_add(offset).ok_or_else(|| {
                        FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                            "prepared O0 FNV frame address overflow".to_string(),
                        ])
                    })?,
                },
                0,
            ));
        }
    }
    let execution = execute_prepared_function_return(
        artifact,
        [
            (
                abi.pointer().value(),
                DifferentialBitVector::new(abi.pointer().width_bits(), DIFFERENTIAL_INPUT_BASE)
                    .ok_or_else(|| {
                        FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                            "prepared O0 FNV pointer width is unsupported".to_string(),
                        ])
                    })?,
            ),
            (
                abi.length().value(),
                DifferentialBitVector::new(abi.length().width_bits(), input.length).ok_or_else(
                    || {
                        FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                            "prepared O0 FNV length width is unsupported".to_string(),
                        ])
                    },
                )?,
            ),
        ],
        initial_memory,
        limits,
    )
    .map_err(|error| {
        FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![format!(
            "prepared O0 FNV SSA/CFG execution failed: {error}"
        )])
    })?;
    let [returned] = execution.returned.as_ref() else {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "prepared O0 FNV SSA/CFG did not return one value".to_string(),
        ]));
    };
    if returned.width_bits() != 64 {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "prepared O0 FNV SSA/CFG return is not 64 bits".to_string(),
        ]));
    }

    let alias = witness.external_alias_policy();
    let external_read = alias.external_read();
    let mut reads = Vec::with_capacity(length);
    for event in &execution.memory_events {
        if event.object == alias.external_object() {
            let ordinal = reads.len();
            let expected_address = DIFFERENTIAL_INPUT_BASE
                .checked_add(ordinal as u64)
                .ok_or_else(|| {
                    FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                        "prepared O0 FNV observed address overflow".to_string(),
                    ])
                })?;
            let Some(byte) = input.bytes.get(ordinal).copied() else {
                return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                    "prepared O0 FNV observed too many external reads".to_string(),
                ]));
            };
            if event.kind != DifferentialMemoryEventKind::Read
                || event.producer != external_read.producer()
                || event.access.ordinal != external_read.ordinal()
                || event.space != memory_space
                || event.byte_address != expected_address
                || event.width_bits != 8
                || event.endianness != witness.memory_endianness()
                || event.value.width_bits() != 8
                || event.value.bits() != u64::from(byte)
            {
                return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                    "prepared O0 FNV external byte-read trace differs from its certificate"
                        .to_string(),
                ]));
            }
            reads.push(FnvFoldO0ObservedRead {
                ordinal: ordinal as u64,
                index: ordinal as u64,
                byte,
                access: external_read,
            });
            continue;
        }

        let Some(slot) = frame_slots
            .iter()
            .find(|slot| slot.object() == event.object)
        else {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV observed an unclassified memory object".to_string(),
            ]));
        };
        let certified_access = slot.accesses().iter().any(|access| {
            access.producer() == event.producer && access.ordinal() == event.access.ordinal
        });
        let expected_address = slot.offset_from_entry_sp() as u64;
        if !alias.classified_frame_objects().contains(&event.object)
            || !certified_access
            || event.space != memory_space
            || event.byte_address != expected_address
            || event.width_bits != slot.width().checked_mul(8).unwrap_or(0)
            || event.endianness != witness.memory_endianness()
            || event.value.width_bits() != event.width_bits
        {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "prepared O0 FNV private-frame trace differs from its certificate".to_string(),
            ]));
        }
    }
    if reads.len() != length {
        return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
            "prepared O0 FNV observed an unexpected external read count".to_string(),
        ]));
    }
    Ok((returned.bits(), reads))
}

fn evaluate_o0_candidate(
    program: FnvFoldO0RenderProgram,
    external_read: CertifiedFnvFoldO0AccessId,
    input: &FnvFoldO0DifferentialInput,
) -> Result<(u64, Vec<FnvFoldO0ObservedRead>), FnvFoldO0SemanticCFunctionError> {
    let length = validate_input(input)?;
    let mut pointer = 0_u64;
    let mut remaining = input.length;
    let mut hash = program.offset_basis;
    let mut reads = Vec::with_capacity(length);
    let mut iterations = 0_usize;
    while (remaining != 0) == program.continue_when_remaining_nonzero {
        let index = usize::try_from(pointer).map_err(|_| {
            FnvFoldO0SemanticCFunctionError::InvalidInputLength {
                requested: input.length,
                available: input.bytes.len(),
            }
        })?;
        let byte =
            *input
                .bytes
                .get(index)
                .ok_or(FnvFoldO0SemanticCFunctionError::InvalidInputLength {
                    requested: input.length,
                    available: input.bytes.len(),
                })?;
        reads.push(FnvFoldO0ObservedRead {
            ordinal: reads.len() as u64,
            index: pointer,
            byte,
            access: external_read,
        });
        let original = u32::from(byte);
        let range = original.wrapping_sub(program.ascii_upper_base);
        let lowercase = original | program.ascii_lowercase_mask;
        let folded = if range < program.ascii_upper_span {
            lowercase
        } else {
            original
        };
        hash = (hash ^ u64::from(folded)).wrapping_mul(program.prime);
        pointer = pointer.wrapping_add(program.pointer_step);
        remaining = remaining.wrapping_sub(program.remaining_step);
        iterations += 1;
        if iterations > length {
            return Err(FnvFoldO0SemanticCFunctionError::InvalidComposition(vec![
                "O0 FNV candidate exceeded the certified input bound".to_string(),
            ]));
        }
    }
    Ok((hash, reads))
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
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind,
        SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
        SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeKind, StackAddressBase,
    };
    use sha2::{Digest, Sha256};

    use super::*;

    const REAL_FNV_SOURCE_SHA256: &str =
        "6524278ba4cd32a72dcf9cbcc385275999a50c3449d0e97035736891bcddff09";
    const REAL_FNV_O0_FUNCTION_SHA256: &str =
        "36af3c68ac0783e3d38125798a0644860fde98454361b46ebc72bd166b96f697";
    const REAL_FNV_O0_BINARY_SHA256: &str =
        "295868f8dab7d5d3e3304b17bce6a19f8948cca620068492f081c658146fe3bb";
    const REAL_FNV_O0_BINARY_PATH: &str = "tests/r2r/bins/r2sleigh_manual_limits_O0";
    const REAL_FNV_O0_COMPILER_COMMAND: &str = "gcc -O0 -g -fno-inline -fno-omit-frame-pointer -fno-stack-protector -no-pie -o tests/r2r/bins/r2sleigh_manual_limits_O0 tests/gold/manual_limits.c";
    const REAL_FNV_O0_BASE: u64 = 0x1_0000_075c;
    const REAL_FNV_O0_BLOCKS: &[&str] = &[
        "ffc300d1e01700f9e11300f9687080d2a873aef208f6c1f2a88ce2f2e80f00f9ff0b00f901000014",
        "e80b40f9e91340f9080109eb42040054",
        "01000014",
        "e81740f9e90b40f90801098b08014039e83f0039e83f4039080501714b010054",
        "01000014",
        "e83f403908690171cc000054",
        "01000014",
        "e83f403908810011e83f003901000014",
        "e83f4039e90308aae80f40f9080109cae80f00f9e80f40f9693680d20920c0f2087d099be80f00f901000014",
        "e80b40f908050091e80b00f9dcffff17",
        "e00f40f9ffc30091c0035fd6",
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

    fn real_interface(arch: &ArchSpec) -> SourceFunctionInterface {
        let sp = real_storage(arch, "sp");
        let slots = vec![
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 15, 1),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 16, 8),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 24, 8),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::StackPointer,
                sp,
                32,
                8,
                1,
                real_storage(arch, "x1"),
            ),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::StackPointer,
                sp,
                40,
                8,
                0,
                real_storage(arch, "x0"),
            ),
        ];
        let types = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
            ],
            [],
        )
        .expect("real O0 FNV type graph");
        let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
        SourceFunctionInterface::new_exact_with_logical_types(
            b"real-arm64-fnv-fold-o0-v1".to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, real_storage(arch, "x0")),
                SourceAbiParameterSpec::new(1, real_storage(arch, "x1")),
            ],
            SourceFunctionReturn::Register {
                storage: real_storage(arch, "x0"),
            },
            slots,
            [
                SourceLogicalValue::new(1, full64),
                SourceLogicalValue::new(2, full64),
            ],
            Some(SourceLogicalValue::new(2, full64)),
            Some(types),
        )
        .and_then(|interface| interface.with_return_address_storage(real_storage(arch, "x30")))
        .expect("real O0 FNV interface")
    }

    fn real_o0_artifact() -> SsaArtifact {
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
        let mut address = REAL_FNV_O0_BASE;
        let blocks = REAL_FNV_O0_BLOCKS
            .iter()
            .map(|encoded| {
                let bytes = decode_hex(encoded);
                let block = disassembler
                    .lift_block(&bytes, address, bytes.len())
                    .expect("pinned real ARM64 O0 FNV block");
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
            "real ARM64 FNV accesses must use the architectural Ram space: {spaces:?}"
        );
        let interface = real_interface(&arch);
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .expect("prepared real ARM64 O0 FNV artifact")
    }

    fn real_function() -> (SsaArtifact, CertifiedFnvFoldO0SemanticCFunction) {
        let artifact = real_o0_artifact();
        let function = CertifiedFnvFoldO0SemanticCFunction::from_artifact(&artifact)
            .expect("certified real ARM64 O0 FNV strict C");
        (artifact, function)
    }

    fn probes() -> Vec<FnvFoldO0DifferentialInput> {
        let mut probes = vec![
            FnvFoldO0DifferentialInput::new(Vec::new(), 0),
            FnvFoldO0DifferentialInput::full(b"A".to_vec()),
            FnvFoldO0DifferentialInput::full(b"Z".to_vec()),
            FnvFoldO0DifferentialInput::full(b"AbC".to_vec()),
            FnvFoldO0DifferentialInput::full(b"abc".to_vec()),
        ];
        for bytes in [
            vec![0x00],
            vec![0x40, 0x41, 0x5a, 0x5b],
            vec![0x7f, 0x80, 0xff],
            (0_u8..=u8::MAX).collect(),
        ] {
            probes.push(FnvFoldO0DifferentialInput::full(bytes));
        }
        let mut state = 0x4d59_5df4_d0f3_3173_u64;
        for length in 1..=32_usize {
            let mut bytes = Vec::with_capacity(length);
            for _ in 0..length {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                bytes.push((state >> 56) as u8);
            }
            probes.push(FnvFoldO0DifferentialInput::full(bytes));
        }
        probes
    }

    fn assert_refused(function: &CertifiedFnvFoldO0SemanticCFunction) {
        assert!(!function.audit().has_exact_fnv_fold_o0_function());
        assert!(function.render_certified_c().is_err());
    }

    fn compiled_results(
        function: &CertifiedFnvFoldO0SemanticCFunction,
        probes: &[FnvFoldO0DifferentialInput],
    ) -> Vec<u64> {
        let function = function
            .clone()
            .with_cosmetic_names("probe", "input", "length");
        let mut source = function.render_certified_c().expect("strict O0 FNV C");
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
            std::env::temp_dir().join(format!("r2dec-fnv-fold-o0-{}-{nonce}", std::process::id()));
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
    fn real_arm64_o0_lift_certifies_and_matches_actual_prepared_ssa() {
        let provenance = format!(
            "binary={REAL_FNV_O0_BINARY_PATH} binary_sha256={REAL_FNV_O0_BINARY_SHA256} command={REAL_FNV_O0_COMPILER_COMMAND}"
        );
        assert_eq!(
            sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
            REAL_FNV_SOURCE_SHA256,
            "source provenance changed: {provenance}"
        );
        let function_bytes = REAL_FNV_O0_BLOCKS
            .iter()
            .flat_map(|encoded| decode_hex(encoded))
            .collect::<Vec<_>>();
        assert_eq!(function_bytes.len(), 200, "{provenance}");
        assert_eq!(
            sha256_hex(&function_bytes),
            REAL_FNV_O0_FUNCTION_SHA256,
            "function-byte provenance changed: {provenance}"
        );

        let artifact = real_o0_artifact();
        let function = CertifiedFnvFoldO0SemanticCFunction::from_artifact(&artifact)
            .expect("real ARM64 O0 FNV must certify");
        assert!(function.audit().has_exact_fnv_fold_o0_function());
        assert!(function.render_permit().authorizes_certified_c());
        assert_eq!(function.source_phases().len(), 11);
        assert_eq!(function.render_phases().len(), 8);
        let alias_seal = function.alias_seal().expect("alias seal");
        assert_eq!(
            alias_seal.external_memory_use().version().object(),
            alias_seal.external_object()
        );
        assert_eq!(alias_seal.external_memory_use().version().version(), 0);
        assert_eq!(
            function.producer_dispositions().len(),
            function.origin().source().instructions().len()
        );
        let dead = function
            .dead_structural_producers()
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        assert!(!dead.is_empty());
        assert!(
            function
                .witness()
                .obligation_dispositions()
                .iter()
                .all(|(obligation, class)| {
                    *class != CertifiedFnvFoldO0DispositionClass::ProvenDead
                        && !dead.contains(&obligation.instruction)
                })
        );
        assert!(function.producer_dispositions().iter().all(|entry| {
            if dead.contains(&entry.producer()) {
                entry.certificate_class() == CertifiedFnvFoldO0DispositionClass::ProvenDead
                    && entry.target()
                        == FnvFoldO0ProducerTarget::Absorbed(
                            CertifiedFnvFoldO0DispositionClass::ProvenDead,
                        )
            } else {
                entry.certificate_class() != CertifiedFnvFoldO0DispositionClass::ProvenDead
            }
        }));
        let c = function.render_certified_c().expect("strict real O0 FNV C");
        assert!(c.contains("while (r2s_local_remaining != UINT64_C(0x0))"));
        assert_eq!(c.matches("= *r2s_local_pointer;").count(), 1);
        assert_eq!(c.matches("while (").count(), 1);
        assert!(c.contains("UINT64_C(0x14650fb0739d0383)"));
        assert!(c.contains("UINT64_C(0x100000001b3)"));
        for forbidden in [
            "goto", "break;", "memcpy", "r2s_read", "frame", "phi", "char *",
        ] {
            assert!(!c.contains(forbidden), "forbidden spelling: {forbidden}");
        }
        assert!(
            !c.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
                .any(|token| token == "int64_t")
        );

        let probes = probes();
        let report = check_fnv_fold_o0_differential(&artifact, &function, probes.clone())
            .expect("real ARM64 O0 FNV actual prepared-SSA differential");
        assert!(report.has_equivalence());
        assert_eq!(report.cases()[0].source_result(), 0x1465_0fb0_739d_0383);
        assert_eq!(report.cases()[1].source_result(), 0x44bd_8ad4_73cd_9906);
        assert_eq!(report.cases()[2].source_result(), 0x44bd_a1d4_73cd_c01b);
        assert_eq!(report.cases()[3].source_result(), 0xe168_0151_0db8_9efd);
        assert_eq!(report.cases()[4].source_result(), 0xe168_0151_0db8_9efd);
        for case in report.cases() {
            assert_eq!(case.source_reads().len(), case.input().length() as usize);
            assert_eq!(case.source_reads(), case.candidate_reads());
            for (index, read) in case.source_reads().iter().enumerate() {
                assert_eq!(read.ordinal(), index as u64);
                assert_eq!(read.index(), index as u64);
            }
        }
        let renamed = function
            .clone()
            .with_cosmetic_names("names do not prove", "same", "same");
        let renamed_report = check_fnv_fold_o0_differential(&artifact, &renamed, probes.clone())
            .expect("name-independent differential");
        assert_eq!(report.cases(), renamed_report.cases());
        let expected = report
            .cases()
            .iter()
            .map(FnvFoldO0DifferentialCase::source_result)
            .collect::<Vec<_>>();
        assert_eq!(compiled_results(&function, &probes), expected);
        assert_eq!(compiled_results(&renamed, &probes), expected);
    }

    #[test]
    fn loss_duplicate_reorder_alias_projection_phase_and_program_mutations_refuse() {
        let (_, function) = real_function();

        let mut loss = function.clone();
        loss.producer_dispositions = loss.producer_dispositions[1..].into();
        assert_refused(&loss);

        let mut duplicate = function.clone();
        let mut dispositions = duplicate.producer_dispositions.to_vec();
        dispositions.push(dispositions[0]);
        duplicate.producer_dispositions = dispositions.into_boxed_slice();
        assert_refused(&duplicate);

        let mut reorder = function.clone();
        reorder.producer_dispositions.swap(0, 1);
        assert_refused(&reorder);

        let mut phase_loss = function.clone();
        phase_loss.render_phases = phase_loss.render_phases[1..].into();
        assert_refused(&phase_loss);

        let mut phase_duplicate = function.clone();
        let mut phases = phase_duplicate.render_phases.to_vec();
        phases.insert(3, phases[3]);
        phase_duplicate.render_phases = phases.into_boxed_slice();
        assert_refused(&phase_duplicate);

        let mut phase_reorder = function.clone();
        phase_reorder.render_phases.swap(3, 4);
        assert_refused(&phase_reorder);

        let mut source_phase_reorder = function.clone();
        source_phase_reorder.source_phases.swap(1, 2);
        assert_refused(&source_phase_reorder);

        let mut dead_loss = function.clone();
        dead_loss.dead_structural_producers = dead_loss.dead_structural_producers[1..].into();
        assert_refused(&dead_loss);

        let mut dead_duplicate = function.clone();
        let mut dead_producers = dead_duplicate.dead_structural_producers.to_vec();
        dead_producers.push(dead_producers[0]);
        dead_duplicate.dead_structural_producers = dead_producers.into_boxed_slice();
        assert_refused(&dead_duplicate);

        let dead_producer = function.dead_structural_producers[0];
        let mut dead_rendered = function.clone();
        dead_rendered
            .producer_dispositions
            .iter_mut()
            .find(|entry| entry.producer == dead_producer)
            .expect("dead producer disposition")
            .target = FnvFoldO0ProducerTarget::Rendered(FnvFoldO0RenderPhaseKind::InitialState);
        assert_refused(&dead_rendered);

        let mut alias = function.clone();
        alias.alias_seal.as_mut().expect("seal").external_object = alias.witness.index().object();
        assert_refused(&alias);

        let mut projection = function.clone();
        projection.alias_seal = None;
        assert_refused(&projection);

        let mut mapping_loss = function.clone();
        mapping_loss.mappings = mapping_loss.mappings[1..].into();
        assert_refused(&mapping_loss);

        let mutate = |change: fn(&mut FnvFoldO0RenderProgram)| {
            let mut corrupt = function.clone();
            change(&mut corrupt.program);
            assert_refused(&corrupt);
        };
        mutate(|program| program.offset_basis ^= 1);
        mutate(|program| program.prime ^= 1);
        mutate(|program| program.ascii_upper_base += 1);
        mutate(|program| program.ascii_upper_span -= 1);
        mutate(|program| program.ascii_lowercase_mask ^= 1);
        mutate(|program| program.pointer_step = 2);
        mutate(|program| program.remaining_step = 2);
        mutate(|program| program.load_width_bytes = 2);
        mutate(|program| program.continue_when_remaining_nonzero = false);
    }

    #[test]
    fn invalid_lengths_and_case_limits_refuse() {
        let (artifact, function) = real_function();
        assert!(matches!(
            check_fnv_fold_o0_differential(
                &artifact,
                &function,
                [FnvFoldO0DifferentialInput::new(vec![b'A'], 2)],
            ),
            Err(FnvFoldO0SemanticCFunctionError::InvalidInputLength { .. })
        ));
        assert!(matches!(
            check_fnv_fold_o0_differential(
                &artifact,
                &function,
                (0..=MAX_DIFFERENTIAL_CASES)
                    .map(|_| FnvFoldO0DifferentialInput::new(Vec::new(), 0)),
            ),
            Err(FnvFoldO0SemanticCFunctionError::TooManyDifferentialCases(_))
        ));
    }
}
