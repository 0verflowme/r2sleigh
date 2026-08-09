//! Proof-preserving strict-C rendering for the sealed private-frame function.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedMachineFunction, CertifiedMemoryStatementKind, CertifiedPrivateFrameConditionalReturn,
    CertifiedRenderPermit, CertifiedTypedRegionKind, EffectDisposition, RenderAuthorizationError,
    TypedRegionMapping, certify_private_frame_conditional_return_region,
};
use r2ssa::{
    BlockTerminator, CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace,
    InstPayload, MachineBitVector, MachineBuildError, MachineCastKind, MachineComparisonOp,
    MachineExpr, MachineExprKind, MachineSignedness, MachineType, MachineValueBinding, SSAOp,
    SemanticObligationId, SourceCarrierKind, SourceFunctionReturn, SourceTypeKind, SsaArtifact,
    StackAddressRoot, ValueId,
};
use serde::Serialize;

pub const CERTIFIED_PRIVATE_FRAME_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION;

const MAX_DIFFERENTIAL_CASES: usize = 256;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum PrivateFrameSemanticCFunctionScope {
    ClosedPrivateFrameConditionalReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum PrivateFramePhaseKind {
    ParameterHomeSubstitution,
    Predicate,
    TrueAssignment,
    FalseAssignment,
    Merge,
    Return,
}

/// One proof-critical phase in the only accepted structured-C order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct PrivateFramePhase {
    kind: PrivateFramePhaseKind,
    producer: CanonicalInstructionId,
    input: MachineValueBinding,
    output: MachineValueBinding,
}

impl PrivateFramePhase {
    pub const fn kind(&self) -> PrivateFramePhaseKind {
        self.kind
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn input(&self) -> MachineValueBinding {
        self.input
    }

    pub const fn output(&self) -> MachineValueBinding {
        self.output
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum PrivateFramePredicateOperand {
    HomeReload {
        binding: MachineValueBinding,
        ty: MachineType,
        producer: CanonicalInstructionId,
    },
    Constant {
        binding: MachineValueBinding,
        ty: MachineType,
        value: MachineBitVector,
    },
}

impl PrivateFramePredicateOperand {
    pub const fn binding(&self) -> MachineValueBinding {
        match self {
            Self::HomeReload { binding, .. } | Self::Constant { binding, .. } => *binding,
        }
    }

    pub const fn ty(&self) -> &MachineType {
        match self {
            Self::HomeReload { ty, .. } | Self::Constant { ty, .. } => ty,
        }
    }
}

/// A typed semantic predicate, never pre-rendered source text.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PrivateFramePredicate {
    producer: CanonicalInstructionId,
    output: MachineValueBinding,
    storage_bits: u32,
    op: MachineComparisonOp,
    interpretation: MachineSignedness,
    left: PrivateFramePredicateOperand,
    right: PrivateFramePredicateOperand,
}

impl PrivateFramePredicate {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn output(&self) -> MachineValueBinding {
        self.output
    }

    pub const fn storage_bits(&self) -> u32 {
        self.storage_bits
    }

    pub const fn op(&self) -> MachineComparisonOp {
        self.op
    }

    pub const fn interpretation(&self) -> MachineSignedness {
        self.interpretation
    }

    pub const fn left(&self) -> &PrivateFramePredicateOperand {
        &self.left
    }

    pub const fn right(&self) -> &PrivateFramePredicateOperand {
        &self.right
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PrivateFrameAbiManifest {
    revision_identity: Box<[u8]>,
    parameter_index: u32,
    parameter_storage: CanonicalStorageId,
    parameter: MachineValueBinding,
    home_reload: MachineValueBinding,
    local_object: r2ssa::ObjectId,
    local_width_bits: u32,
    logical_signed: bool,
    return_storage: CanonicalStorageId,
    returned: MachineValueBinding,
}

impl PrivateFrameAbiManifest {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn parameter_index(&self) -> u32 {
        self.parameter_index
    }

    pub const fn parameter_storage(&self) -> CanonicalStorageId {
        self.parameter_storage
    }

    pub const fn parameter(&self) -> MachineValueBinding {
        self.parameter
    }

    pub const fn home_reload(&self) -> MachineValueBinding {
        self.home_reload
    }

    pub const fn local_object(&self) -> r2ssa::ObjectId {
        self.local_object
    }

    pub const fn local_width_bits(&self) -> u32 {
        self.local_width_bits
    }

    pub const fn logical_signed(&self) -> bool {
        self.logical_signed
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn returned(&self) -> MachineValueBinding {
        self.returned
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PrivateFrameRenderNames {
    function: String,
    parameter: String,
    local: String,
}

impl PrivateFrameRenderNames {
    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn parameter(&self) -> &str {
        &self.parameter
    }

    pub fn local(&self) -> &str {
        &self.local
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameSemanticCFunction {
    schema_version: u32,
    scope: PrivateFrameSemanticCFunctionScope,
    names: PrivateFrameRenderNames,
    origin: CertifiedArtifactOrigin,
    witness: CertifiedPrivateFrameConditionalReturn,
    abi: PrivateFrameAbiManifest,
    /// Immutable construction-time copy used to audit the render-facing AST.
    sealed_predicate: PrivateFramePredicate,
    predicate: PrivateFramePredicate,
    true_value: MachineBitVector,
    false_value: MachineBitVector,
    phases: Box<[PrivateFramePhase]>,
    mappings: Box<[TypedRegionMapping]>,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PrivateFrameSemanticCFunctionError {
    Machine(MachineBuildError),
    Authorization(RenderAuthorizationError),
    MissingPrivateFrameWitness,
    InvalidProjectionFailure,
    InvalidPredicate,
    InvalidInterface,
    InvalidWidth(u32),
    TooManyDifferentialCases(usize),
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for PrivateFrameSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private-frame semantic C function failed: {self:?}")
    }
}

impl std::error::Error for PrivateFrameSemanticCFunctionError {}

impl From<MachineBuildError> for PrivateFrameSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RenderAuthorizationError> for PrivateFrameSemanticCFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl CertifiedPrivateFrameSemanticCFunction {
    /// Certify the prepared artifact before entering the whole-function renderer.
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, PrivateFrameSemanticCFunctionError> {
        let certified = CertifiedMachineFunction::from_artifact(artifact)?;
        Self::from_certified(&certified)
    }

    /// Construct only from the sealed whole-machine certificate.
    pub fn from_certified(
        certified: &CertifiedMachineFunction,
    ) -> Result<Self, PrivateFrameSemanticCFunctionError> {
        let witness = certified
            .private_frame_conditional_return()
            .ok_or(PrivateFrameSemanticCFunctionError::MissingPrivateFrameWitness)?
            .clone();
        validate_certified_interface(certified, &witness)?;
        validate_projection_failures(certified, &witness)?;
        let abi = expected_abi(&witness)?;
        validate_return_transforms(certified, &witness, &abi)?;
        let predicate = predicate_from_certified(certified, &witness, &abi)?;
        let (true_value, false_value) = assignment_values(&witness)?;
        let phases = expected_phases(&witness)?.into_boxed_slice();
        let mappings = exact_mappings(certified)?.into_boxed_slice();
        let render_permit = certify_private_frame_conditional_return_region(
            certified.origin(),
            certified.ledger(),
            mappings.iter().cloned(),
            &witness,
        )?;
        let function = Self {
            schema_version: CERTIFIED_PRIVATE_FRAME_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: PrivateFrameSemanticCFunctionScope::ClosedPrivateFrameConditionalReturn,
            names: PrivateFrameRenderNames {
                function: "certified_private_frame".to_string(),
                parameter: "argument".to_string(),
                local: "result".to_string(),
            },
            origin: certified.origin().clone(),
            witness,
            abi,
            sealed_predicate: predicate.clone(),
            predicate,
            true_value,
            false_value,
            phases,
            mappings,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_private_frame_function() {
            return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> PrivateFrameSemanticCFunctionScope {
        self.scope
    }

    pub const fn names(&self) -> &PrivateFrameRenderNames {
        &self.names
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn witness(&self) -> &CertifiedPrivateFrameConditionalReturn {
        &self.witness
    }

    pub const fn abi(&self) -> &PrivateFrameAbiManifest {
        &self.abi
    }

    pub const fn predicate(&self) -> &PrivateFramePredicate {
        &self.predicate
    }

    pub const fn phases(&self) -> &[PrivateFramePhase] {
        &self.phases
    }

    pub const fn mappings(&self) -> &[TypedRegionMapping] {
        &self.mappings
    }

    pub const fn render_permit(&self) -> &CertifiedRenderPermit {
        &self.render_permit
    }

    /// Replace presentation names without changing proof identity or semantics.
    pub fn with_cosmetic_names(
        mut self,
        function: impl Into<String>,
        parameter: impl Into<String>,
        local: impl Into<String>,
    ) -> Self {
        self.names = PrivateFrameRenderNames {
            function: function.into(),
            parameter: parameter.into(),
            local: local.into(),
        };
        self
    }

    pub fn audit(&self) -> PrivateFrameSemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_PRIVATE_FRAME_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("private-frame schema mismatch".to_string());
        }
        if self.scope != PrivateFrameSemanticCFunctionScope::ClosedPrivateFrameConditionalReturn {
            invalid.push("private-frame scope mismatch".to_string());
        }
        if self.witness.origin() != &self.origin
            || self.witness.contract_version()
                != CERTIFIED_PRIVATE_FRAME_CONDITIONAL_RETURN_CONTRACT_VERSION
        {
            invalid.push("private-frame witness is not exact for the artifact origin".to_string());
        }
        match expected_abi(&self.witness) {
            Ok(expected) if expected == self.abi => {}
            _ => {
                invalid.push("revision, ABI, storage, type, or local manifest mismatch".to_string())
            }
        }
        if self.predicate != self.sealed_predicate
            || !predicate_is_exact(&self.predicate, &self.witness, &self.abi)
        {
            invalid.push("typed private-frame predicate or Home substitution mismatch".to_string());
        }
        match assignment_values(&self.witness) {
            Ok((true_value, false_value))
                if true_value == self.true_value && false_value == self.false_value => {}
            _ => invalid.push("true/false assignment polarity is not exact 1/0".to_string()),
        }
        match expected_phases(&self.witness) {
            Ok(expected) if expected.as_slice() == self.phases.as_ref() => {}
            _ => invalid.push("private-frame phases are incomplete or out of order".to_string()),
        }
        let phase_counts = counts(self.phases.iter().map(PrivateFramePhase::kind));
        if ALL_PHASES
            .iter()
            .any(|kind| phase_counts.get(kind) != Some(&1))
            || phase_counts.len() != ALL_PHASES.len()
        {
            invalid.push("private-frame phases are missing or duplicated".to_string());
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
            invalid.push("private-frame source mapping is not exact and closed".to_string());
        }
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::PrivateFrameConditionalReturnFunction,
            CERTIFIED_PRIVATE_FRAME_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            &self.mappings,
        ) {
            invalid.push("private-frame render permit does not match the mapping".to_string());
        }
        PrivateFrameSemanticCFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, PrivateFrameSemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_private_frame_function()
            || !self.render_permit.authorizes_certified_c()
        {
            return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let ty = semantic_integer_type(self.abi.local_width_bits, self.abi.logical_signed)?;
        let function = c_identifier("r2s_fn", &self.names.function);
        let parameter = c_identifier("r2s_arg", &self.names.parameter);
        let local = c_identifier("r2s_local", &self.names.local);
        let (predicate, substitutions) = render_predicate(&self.predicate, &parameter)?;
        if substitutions != 1 {
            return Err(PrivateFrameSemanticCFunctionError::InvalidPredicate);
        }
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        writeln!(&mut output, "{ty} {function}({ty} {parameter}) {{")
            .expect("String writes cannot fail");
        writeln!(&mut output, "\t{ty} {local};").expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tif ((uint8_t)({predicate}) != UINT8_C(0)) {{"
        )
        .expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\t\t{local} = ({ty})UINT64_C(0x{:x});",
            self.true_value.bits()
        )
        .expect("String writes cannot fail");
        output.push_str("\t} else {\n");
        writeln!(
            &mut output,
            "\t\t{local} = ({ty})UINT64_C(0x{:x});",
            self.false_value.bits()
        )
        .expect("String writes cannot fail");
        output.push_str("\t}\n");
        writeln!(&mut output, "\treturn {local};").expect("String writes cannot fail");
        output.push_str("}\n");
        Ok(output)
    }
}

const ALL_PHASES: [PrivateFramePhaseKind; 6] = [
    PrivateFramePhaseKind::ParameterHomeSubstitution,
    PrivateFramePhaseKind::Predicate,
    PrivateFramePhaseKind::TrueAssignment,
    PrivateFramePhaseKind::FalseAssignment,
    PrivateFramePhaseKind::Merge,
    PrivateFramePhaseKind::Return,
];

fn expected_abi(
    witness: &CertifiedPrivateFrameConditionalReturn,
) -> Result<PrivateFrameAbiManifest, PrivateFrameSemanticCFunctionError> {
    let interface = witness
        .origin()
        .machine_context()
        .source()
        .function_interface()
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
    let [source_parameter] = interface.parameters() else {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    };
    let parameter = witness.home().parameter();
    let [home_reload] = witness.home().reloads() else {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    };
    let local_object = witness
        .local_slot()
        .object()
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
    let width_bits = witness
        .home()
        .slot()
        .size_bytes()
        .checked_mul(8)
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidWidth(0))?;
    uint_type(width_bits)?;
    let unsigned = MachineType::Integer {
        width_bits,
        signedness: MachineSignedness::Unsigned,
    };
    let join_result = match witness.join_load().kind() {
        CertifiedMemoryStatementKind::Read { result } => result,
        CertifiedMemoryStatementKind::Write { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    let logical_signed = private_frame_logical_signed(interface, width_bits)?;
    let abi_width_bits = parameter.storage().size.checked_mul(8).unwrap_or(0);
    let return_width_bits = witness.return_storage().size.checked_mul(8).unwrap_or(0);
    let parameter_boundary_is_exact = match parameter.value() {
        Some(parameter_value) => {
            parameter_value.binding() == witness.home().parameter_value().binding()
                && parameter_value.binding().width_bits() == abi_width_bits
                && abi_width_bits == width_bits
                && parameter_value.producer().is_none()
                && parameter_value.constant().is_none()
        }
        None => {
            logical_signed
                && abi_width_bits > width_bits
                && witness.home().parameter_value().binding().width_bits() == width_bits
                && witness.home().parameter_value().producer().is_none()
                && witness.home().parameter_value().constant().is_none()
        }
    };
    let return_composition_is_exact = match witness.return_transforms() {
        [] => {
            witness.return_value().binding() == join_result.binding()
                && return_width_bits == width_bits
        }
        [_] => {
            witness.return_value().binding() != join_result.binding()
                && (return_width_bits == width_bits
                    || (logical_signed && return_width_bits > width_bits))
        }
        [_, _] => {
            logical_signed
                && return_width_bits > width_bits
                && witness.return_value().binding() != join_result.binding()
        }
        [_, _, ..] => false,
    };
    let interface_is_exact = source_parameter.index() == parameter.index()
        && source_parameter.storage() == parameter.storage()
        && parameter.storage().space == CanonicalStorageSpace::Register
        && parameter_boundary_is_exact
        && (abi_width_bits == width_bits || (logical_signed && abi_width_bits > width_bits))
        && witness.home().parameter_value().ty() == &unsigned
        && home_reload.value().ty() == &unsigned
        && witness.home().slot().size_bytes().checked_mul(8) == Some(width_bits)
        && witness.local_slot().size_bytes().checked_mul(8) == Some(width_bits)
        && witness.return_storage().space == CanonicalStorageSpace::Register
        && (return_width_bits == width_bits || (logical_signed && return_width_bits > width_bits))
        && witness.return_value().binding().width_bits() == return_width_bits
        && join_result.ty() == &unsigned
        && return_composition_is_exact
        && interface.revision_identity() == witness.revision_identity()
        && matches!(interface.return_kind(), SourceFunctionReturn::Register { storage }
			if storage == witness.return_storage());
    if !interface_is_exact {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    }
    Ok(PrivateFrameAbiManifest {
        revision_identity: witness.revision_identity().to_vec().into_boxed_slice(),
        parameter_index: parameter.index(),
        parameter_storage: parameter.storage(),
        parameter: witness.home().parameter_value().binding(),
        home_reload: home_reload.value().binding(),
        local_object,
        local_width_bits: width_bits,
        logical_signed,
        return_storage: witness.return_storage(),
        returned: witness.return_value().binding(),
    })
}

fn validate_return_transforms(
    certified: &CertifiedMachineFunction,
    witness: &CertifiedPrivateFrameConditionalReturn,
    abi: &PrivateFrameAbiManifest,
) -> Result<(), PrivateFrameSemanticCFunctionError> {
    let joined = match witness.join_load().kind() {
        CertifiedMemoryStatementKind::Read { result } => result,
        CertifiedMemoryStatementKind::Write { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    let mut previous_root = certified
        .projection()
        .entity_for_output(joined.binding().value())
        .map(|entity| entity.root())
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
    let mut previous_binding = joined.binding();
    let source_input_is_exact = |input, binding, expected_type: &MachineType| {
        certified
            .projection()
            .expr(input)
            .is_some_and(|expression| {
                expression.origin().is_none()
                    && expression.ty() == expected_type
                    && matches!(expression.kind(), MachineExprKind::Source { binding: actual }
                    if *actual == binding)
            })
    };
    for relay in witness.return_relays() {
        let entity = certified
            .projection()
            .entity_for_producer(*relay)
            .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
        let expression = certified
            .projection()
            .expr(entity.root())
            .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
        let MachineExprKind::Copy { input } = expression.kind() else {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        };
        if !source_input_is_exact(*input, previous_binding, expression.ty())
            || expression.origin() != Some(*relay)
            || entity.output().width_bits() != previous_binding.width_bits()
        {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    }
    for (index, transform) in witness.return_transforms().iter().enumerate() {
        let entity = certified
            .projection()
            .entity_for_producer(transform.entity().producer())
            .filter(|entity| entity.root() == transform.root())
            .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
        let expression = certified
            .projection()
            .expr(transform.root())
            .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
        let exact_kind = match expression.kind() {
            MachineExprKind::Copy { input } => {
                source_input_is_exact(*input, previous_binding, expression.ty())
                    && entity.output().width_bits() == previous_binding.width_bits()
            }
            MachineExprKind::Cast {
                kind: MachineCastKind::ZeroExtend,
                input,
            } => certified
                .projection()
                .expr(*input)
                .is_some_and(|input_expression| {
                    source_input_is_exact(*input, previous_binding, input_expression.ty())
                        && input_expression.ty().width_bits() < expression.ty().width_bits()
                        && entity.output().width_bits() == expression.ty().width_bits()
                }),
            _ => false,
        };
        if !exact_kind
            || expression.origin() != Some(transform.entity().producer())
            || (witness.return_transforms().len() == 2
                && ((index == 0 && !matches!(expression.kind(), MachineExprKind::Copy { .. }))
                    || (index == 1
                        && !matches!(
                            expression.kind(),
                            MachineExprKind::Cast {
                                kind: MachineCastKind::ZeroExtend,
                                ..
                            }
                        ))))
        {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
        previous_root = transform.root();
        previous_binding = entity.output();
    }
    let returned_root = certified
        .projection()
        .entity_for_output(witness.return_value().binding().value())
        .map(|entity| entity.root());
    if witness.return_transforms().is_empty() {
        if witness.return_value().binding() != joined.binding() {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    } else if returned_root != Some(previous_root)
        || previous_binding != witness.return_value().binding()
        || certified
            .projection()
            .expr(previous_root)
            .is_none_or(|expression| expression.ty().width_bits() != abi.return_storage.size * 8)
    {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    }
    Ok(())
}

fn private_frame_logical_signed(
    interface: &r2ssa::SourceFunctionInterface,
    width_bits: u32,
) -> Result<bool, PrivateFrameSemanticCFunctionError> {
    match (
        interface.type_graph(),
        interface.parameter_logical_values(),
        interface.return_logical_value(),
    ) {
        (None, [], None) => Ok(false),
        (Some(graph), [parameter], Some(returned)) => {
            let type_id = usize::try_from(parameter.type_id())
                .map_err(|_| PrivateFrameSemanticCFunctionError::InvalidInterface)?;
            let source_type = graph
                .types()
                .get(type_id)
                .ok_or(PrivateFrameSemanticCFunctionError::InvalidInterface)?;
            let carrier_is_low = |logical: r2ssa::SourceLogicalValue| {
                logical.type_id() == parameter.type_id()
                    && logical.carrier().kind() == SourceCarrierKind::LowBits
                    && logical.carrier().offset_bits() == 0
                    && logical.carrier().size_bits() == u64::from(width_bits)
            };
            if graph.types().len() != 1
                || !graph.aggregates().is_empty()
                || source_type.kind() != SourceTypeKind::SignedInteger
                || source_type.size_bits() != u64::from(width_bits)
                || source_type.align_bits() != u64::from(width_bits)
                || !carrier_is_low(*parameter)
                || !carrier_is_low(returned)
            {
                return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
            }
            Ok(true)
        }
        _ => Err(PrivateFrameSemanticCFunctionError::InvalidInterface),
    }
}

fn predicate_from_certified(
    certified: &CertifiedMachineFunction,
    witness: &CertifiedPrivateFrameConditionalReturn,
    abi: &PrivateFrameAbiManifest,
) -> Result<PrivateFramePredicate, PrivateFrameSemanticCFunctionError> {
    if certified.origin() != witness.origin() {
        return Err(PrivateFrameSemanticCFunctionError::InvalidPredicate);
    }
    let root = certified
        .projection()
        .expr(witness.predicate_expression().root())
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidPredicate)?;
    let MachineType::Bool { storage_bits } = root.ty() else {
        return Err(PrivateFrameSemanticCFunctionError::InvalidPredicate);
    };
    let MachineExprKind::Compare {
        op,
        interpretation,
        left,
        right,
    } = root.kind()
    else {
        return Err(PrivateFrameSemanticCFunctionError::InvalidPredicate);
    };
    let left = predicate_operand(
        certified.projection().expr(*left),
        abi,
        witness.home().reloads()[0].statement().producer(),
    )?;
    let right = predicate_operand(
        certified.projection().expr(*right),
        abi,
        witness.home().reloads()[0].statement().producer(),
    )?;
    let predicate = PrivateFramePredicate {
        producer: witness.predicate_expression().entity().producer(),
        output: witness.predicate_value().binding(),
        storage_bits: *storage_bits,
        op: *op,
        interpretation: *interpretation,
        left,
        right,
    };
    if root.origin() != Some(predicate.producer)
        || witness.predicate_expression().inputs()
            != &BTreeSet::from([witness.home().reloads()[0].statement().producer()])
        || !predicate_is_exact(&predicate, witness, abi)
    {
        return Err(PrivateFrameSemanticCFunctionError::InvalidPredicate);
    }
    Ok(predicate)
}

fn predicate_operand(
    expression: Option<&MachineExpr>,
    abi: &PrivateFrameAbiManifest,
    home_producer: CanonicalInstructionId,
) -> Result<PrivateFramePredicateOperand, PrivateFrameSemanticCFunctionError> {
    let expression = expression.ok_or(PrivateFrameSemanticCFunctionError::InvalidPredicate)?;
    match expression.kind() {
        MachineExprKind::Source { binding }
            if *binding == abi.home_reload && expression.origin().is_none() =>
        {
            Ok(PrivateFramePredicateOperand::HomeReload {
                binding: *binding,
                ty: expression.ty().clone(),
                producer: home_producer,
            })
        }
        MachineExprKind::Constant { binding, value } if expression.origin().is_none() => {
            Ok(PrivateFramePredicateOperand::Constant {
                binding: *binding,
                ty: expression.ty().clone(),
                value: *value,
            })
        }
        _ => Err(PrivateFrameSemanticCFunctionError::InvalidPredicate),
    }
}

fn predicate_is_exact(
    predicate: &PrivateFramePredicate,
    witness: &CertifiedPrivateFrameConditionalReturn,
    abi: &PrivateFrameAbiManifest,
) -> bool {
    let [home_reload] = witness.home().reloads() else {
        return false;
    };
    let unsigned = MachineType::Integer {
        width_bits: abi.local_width_bits,
        signedness: MachineSignedness::Unsigned,
    };
    let operands = [&predicate.left, &predicate.right];
    let mut home_count = 0;
    let mut constant_count = 0;
    for operand in operands {
        match operand {
            PrivateFramePredicateOperand::HomeReload {
                binding,
                ty,
                producer,
            } if *binding == abi.home_reload
                && *ty == unsigned
                && *producer == home_reload.statement().producer() =>
            {
                home_count += 1;
            }
            PrivateFramePredicateOperand::Constant { binding, ty, value }
                if binding.width_bits() == abi.local_width_bits
                    && *ty == unsigned
                    && value.width_bits() == abi.local_width_bits =>
            {
                constant_count += 1;
            }
            PrivateFramePredicateOperand::HomeReload { .. }
            | PrivateFramePredicateOperand::Constant { .. } => {}
        }
    }
    predicate.producer == witness.predicate_expression().entity().producer()
        && predicate.output == witness.predicate_value().binding()
        && predicate.output == witness.branch_control().condition().binding()
        && predicate.storage_bits == predicate.output.width_bits()
        && home_count == 1
        && constant_count == 1
}

fn assignment_values(
    witness: &CertifiedPrivateFrameConditionalReturn,
) -> Result<(MachineBitVector, MachineBitVector), PrivateFrameSemanticCFunctionError> {
    let true_value = match witness.true_store().kind() {
        CertifiedMemoryStatementKind::Write { value } => value,
        CertifiedMemoryStatementKind::Read { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    let false_value = match witness.false_store().kind() {
        CertifiedMemoryStatementKind::Write { value } => value,
        CertifiedMemoryStatementKind::Read { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    let (Some(true_constant), Some(false_constant)) =
        (true_value.constant(), false_value.constant())
    else {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    };
    let width_bits = witness
        .local_slot()
        .size_bytes()
        .checked_mul(8)
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidWidth(0))?;
    let unsigned = MachineType::Integer {
        width_bits,
        signedness: MachineSignedness::Unsigned,
    };
    if true_constant.bits() != 1
        || false_constant.bits() != 0
        || true_constant.width_bits() != width_bits
        || false_constant.width_bits() != width_bits
        || true_value.ty() != &unsigned
        || false_value.ty() != &unsigned
        || witness.true_store().width_bits() != width_bits
        || witness.false_store().width_bits() != width_bits
    {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    }
    Ok((true_constant, false_constant))
}

fn expected_phases(
    witness: &CertifiedPrivateFrameConditionalReturn,
) -> Result<Vec<PrivateFramePhase>, PrivateFrameSemanticCFunctionError> {
    let [home_reload] = witness.home().reloads() else {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    };
    let true_value = match witness.true_store().kind() {
        CertifiedMemoryStatementKind::Write { value } => value,
        CertifiedMemoryStatementKind::Read { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    let false_value = match witness.false_store().kind() {
        CertifiedMemoryStatementKind::Write { value } => value,
        CertifiedMemoryStatementKind::Read { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    let merged = match witness.join_load().kind() {
        CertifiedMemoryStatementKind::Read { result } => result,
        CertifiedMemoryStatementKind::Write { .. } => {
            return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
        }
    };
    Ok(vec![
        PrivateFramePhase {
            kind: PrivateFramePhaseKind::ParameterHomeSubstitution,
            producer: home_reload.statement().producer(),
            input: witness.home().parameter_value().binding(),
            output: home_reload.value().binding(),
        },
        PrivateFramePhase {
            kind: PrivateFramePhaseKind::Predicate,
            producer: witness.predicate_expression().entity().producer(),
            input: home_reload.value().binding(),
            output: witness.predicate_value().binding(),
        },
        PrivateFramePhase {
            kind: PrivateFramePhaseKind::TrueAssignment,
            producer: witness.true_store().producer(),
            input: true_value.binding(),
            output: merged.binding(),
        },
        PrivateFramePhase {
            kind: PrivateFramePhaseKind::FalseAssignment,
            producer: witness.false_store().producer(),
            input: false_value.binding(),
            output: merged.binding(),
        },
        PrivateFramePhase {
            kind: PrivateFramePhaseKind::Merge,
            producer: witness.join_load().producer(),
            input: merged.binding(),
            output: witness.return_value().binding(),
        },
        PrivateFramePhase {
            kind: PrivateFramePhaseKind::Return,
            producer: witness.return_control().producer(),
            input: witness.return_value().binding(),
            output: witness.return_value().binding(),
        },
    ])
}

fn validate_projection_failures(
    certified: &CertifiedMachineFunction,
    witness: &CertifiedPrivateFrameConditionalReturn,
) -> Result<(), PrivateFrameSemanticCFunctionError> {
    let expected = [
        witness.saved_frame_pointer_load(),
        witness.return_address_load(),
    ];
    if certified.projection().failures().len() != expected.len() {
        return Err(PrivateFrameSemanticCFunctionError::InvalidProjectionFailure);
    }
    for load in expected {
        let Some(failure) = certified.projection().failures().iter().find(|failure| {
            failure.output() == load.result().binding().value()
                && failure.producer() == load.producer()
        }) else {
            return Err(PrivateFrameSemanticCFunctionError::InvalidProjectionFailure);
        };
        if !matches!(failure.error(), MachineBuildError::UnsupportedOperation { inst, op }
			if *inst == load.source_inst() && matches!(op.as_ref(), SSAOp::Load { .. }))
            || certified
                .projection()
                .entity_for_output(failure.output())
                .is_some()
        {
            return Err(PrivateFrameSemanticCFunctionError::InvalidProjectionFailure);
        }
    }
    Ok(())
}

fn validate_certified_interface(
    certified: &CertifiedMachineFunction,
    witness: &CertifiedPrivateFrameConditionalReturn,
) -> Result<(), PrivateFrameSemanticCFunctionError> {
    let parameter = witness.home().parameter();
    let home_root = StackAddressRoot {
        base: witness.home().slot().base(),
        offset: witness.home().slot().offset(),
    };
    let local_root = StackAddressRoot {
        base: witness.local_slot().base(),
        offset: witness.local_slot().offset(),
    };
    let local_source_slot_matches = if witness.local_slot().source_declared() {
        certified
            .stack_slots()
            .get(&local_root)
            .is_some_and(|slot| {
                slot.base() == witness.local_slot().base()
                    && slot.offset() == witness.local_slot().offset()
                    && slot.size_bytes() == witness.local_slot().size_bytes()
                    && slot.object() == witness.local_slot().object()
            })
    } else {
        !certified.stack_slots().contains_key(&local_root)
    };
    if certified.origin() != witness.origin()
        || certified.abi_parameters().len() != 1
        || certified.abi_parameters().get(&parameter.index()) != Some(parameter)
        || certified.stack_slots().len()
            != if witness.local_slot().source_declared() {
                2
            } else {
                1
            }
        || certified.stack_slots().get(&home_root) != Some(witness.home().slot())
        || !local_source_slot_matches
        || certified.machine_context() != witness.origin().machine_context()
    {
        return Err(PrivateFrameSemanticCFunctionError::InvalidInterface);
    }
    Ok(())
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

fn render_predicate(
    predicate: &PrivateFramePredicate,
    parameter: &str,
) -> Result<(String, usize), PrivateFrameSemanticCFunctionError> {
    let (left, left_substitutions) = render_operand(&predicate.left, parameter)?;
    let (right, right_substitutions) = render_operand(&predicate.right, parameter)?;
    let substitutions = left_substitutions.saturating_add(right_substitutions);
    let width = predicate.left.ty().width_bits();
    if predicate.right.ty().width_bits() != width {
        return Err(PrivateFrameSemanticCFunctionError::InvalidPredicate);
    }
    let signed_order = predicate.interpretation == MachineSignedness::Signed
        && matches!(
            predicate.op,
            MachineComparisonOp::LessThan | MachineComparisonOp::LessThanOrEqual
        );
    let (left, right) = if signed_order {
        let ty = uint_type(width)?;
        let sign_shift = width
            .checked_sub(1)
            .ok_or(PrivateFrameSemanticCFunctionError::InvalidWidth(width))?;
        let sign_bit = 1_u64
            .checked_shl(sign_shift)
            .ok_or(PrivateFrameSemanticCFunctionError::InvalidWidth(width))?;
        (
            format!("((({ty})({left})) ^ (({ty})UINT64_C(0x{sign_bit:x})))"),
            format!("((({ty})({right})) ^ (({ty})UINT64_C(0x{sign_bit:x})))"),
        )
    } else {
        (left, right)
    };
    let op = match predicate.op {
        MachineComparisonOp::Equal => "==",
        MachineComparisonOp::NotEqual => "!=",
        MachineComparisonOp::LessThan => "<",
        MachineComparisonOp::LessThanOrEqual => "<=",
    };
    Ok((format!("({left} {op} {right})"), substitutions))
}

fn render_operand(
    operand: &PrivateFramePredicateOperand,
    parameter: &str,
) -> Result<(String, usize), PrivateFrameSemanticCFunctionError> {
    match operand {
        PrivateFramePredicateOperand::HomeReload { ty, .. } => {
            uint_type(ty.width_bits())?;
            Ok((parameter.to_string(), 1))
        }
        PrivateFramePredicateOperand::Constant { ty, value, .. } => {
            let ty = uint_type(ty.width_bits())?;
            Ok((format!("(({ty})UINT64_C(0x{:x}))", value.bits()), 0))
        }
    }
}

fn uint_type(width_bits: u32) -> Result<&'static str, PrivateFrameSemanticCFunctionError> {
    match width_bits {
        8 => Ok("uint8_t"),
        16 => Ok("uint16_t"),
        32 => Ok("uint32_t"),
        64 => Ok("uint64_t"),
        _ => Err(PrivateFrameSemanticCFunctionError::InvalidWidth(width_bits)),
    }
}

fn semantic_integer_type(
    width_bits: u32,
    signed: bool,
) -> Result<&'static str, PrivateFrameSemanticCFunctionError> {
    if !signed {
        return uint_type(width_bits);
    }
    match width_bits {
        8 => Ok("int8_t"),
        16 => Ok("int16_t"),
        32 => Ok("int32_t"),
        64 => Ok("int64_t"),
        _ => Err(PrivateFrameSemanticCFunctionError::InvalidWidth(width_bits)),
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
pub struct PrivateFrameSemanticCFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl PrivateFrameSemanticCFunctionAuditReport {
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

    pub fn has_exact_private_frame_function(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct PrivateFrameDifferentialCase {
    input: u64,
    source_result: u64,
    candidate_result: u64,
}

impl PrivateFrameDifferentialCase {
    pub const fn input(&self) -> u64 {
        self.input
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
pub struct PrivateFrameDifferentialReport {
    cases: Box<[PrivateFrameDifferentialCase]>,
}

impl PrivateFrameDifferentialReport {
    pub const fn cases(&self) -> &[PrivateFrameDifferentialCase] {
        &self.cases
    }

    pub fn has_equivalence(&self) -> bool {
        !self.cases.is_empty() && self.cases.iter().all(PrivateFrameDifferentialCase::matches)
    }
}

/// Execute the retained prepared SSA and the stored render AST independently.
pub fn check_private_frame_differential(
    artifact: &SsaArtifact,
    certified: &CertifiedMachineFunction,
    candidate: &CertifiedPrivateFrameSemanticCFunction,
    inputs: impl IntoIterator<Item = u64>,
) -> Result<PrivateFrameDifferentialReport, PrivateFrameSemanticCFunctionError> {
    let report = candidate.audit();
    let fresh = CertifiedMachineFunction::from_artifact(artifact)?;
    if fresh != *certified
        || !report.has_exact_private_frame_function()
        || certified.origin() != candidate.origin()
        || certified.private_frame_conditional_return() != Some(candidate.witness())
    {
        return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
            report.invalid,
        ));
    }
    validate_certified_interface(certified, candidate.witness())?;
    validate_projection_failures(certified, candidate.witness())?;
    let source_abi = expected_abi(candidate.witness())?;
    predicate_from_certified(certified, candidate.witness(), &source_abi)?;
    let inputs = inputs.into_iter().collect::<Vec<_>>();
    if inputs.len() > MAX_DIFFERENTIAL_CASES {
        return Err(PrivateFrameSemanticCFunctionError::TooManyDifferentialCases(inputs.len()));
    }
    let mask = width_mask(candidate.abi.local_width_bits);
    let mut cases = Vec::with_capacity(inputs.len());
    for input in inputs {
        let input = input & mask;
        cases.push(PrivateFrameDifferentialCase {
            input,
            source_result: execute_private_frame_prepared_ssa(
                artifact,
                candidate.witness(),
                input,
            )?,
            candidate_result: evaluate_function(
                &candidate.predicate,
                candidate.true_value.bits(),
                candidate.false_value.bits(),
                input,
            ),
        });
    }
    Ok(PrivateFrameDifferentialReport {
        cases: cases.into_boxed_slice(),
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PrivateFrameExactBits {
    width: u32,
    bits: u64,
}

impl PrivateFrameExactBits {
    fn new(width: u32, bits: u64) -> Result<Self, PrivateFrameSemanticCFunctionError> {
        if !matches!(width, 8 | 16 | 32 | 64) {
            return Err(PrivateFrameSemanticCFunctionError::InvalidWidth(width));
        }
        Ok(Self {
            width,
            bits: bits & width_mask(width),
        })
    }

    fn signed(self) -> i64 {
        signed_value(self.bits, self.width)
    }
}

fn execute_private_frame_prepared_ssa(
    artifact: &SsaArtifact,
    witness: &CertifiedPrivateFrameConditionalReturn,
    input: u64,
) -> Result<u64, PrivateFrameSemanticCFunctionError> {
    const ENTRY_STACK: u64 = 0x10_0000;
    const ENTRY_FRAME: u64 = 0x20_0000;
    const RETURN_TARGET: u64 = 0x40_0000;
    const MAX_BLOCK_STEPS: usize = 8;
    const MAX_INSTRUCTION_STEPS: usize = 96;

    if witness.origin().source() != artifact.obligations()
        || !witness
            .origin()
            .matches_retained_source(artifact.obligations(), witness.origin().topology())
    {
        return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
            vec!["prepared private-frame runner received a foreign witness".to_string()],
        ));
    }
    let graph = artifact.graph();
    let function = artifact.function();
    let mut values = BTreeMap::new();
    for value in &graph.values {
        if graph.def_inst(value.id).is_some() {
            continue;
        }
        let width = value.var.size.checked_mul(8).ok_or(
            PrivateFrameSemanticCFunctionError::InvalidWidth(value.var.size),
        )?;
        let bits = if value.id == witness.entry_sp().binding().value() {
            ENTRY_STACK
        } else if value.id == witness.entry_fp().binding().value() {
            ENTRY_FRAME
        } else if value.id == witness.home().parameter_value().binding().value() {
            input
        } else {
            value.var.constant_bits().unwrap_or(0)
        };
        values.insert(value.id, PrivateFrameExactBits::new(width, bits)?);
    }
    let mut memory = BTreeMap::new();
    private_frame_write_memory(
        &mut memory,
        ENTRY_STACK,
        PrivateFrameExactBits::new(64, RETURN_TARGET)?,
    );
    let mut current = function.entry;
    let mut predecessor = None;
    let mut instruction_steps = 0usize;
    for _ in 0..MAX_BLOCK_STEPS {
        let block_id = graph.block_id_for_addr(current).ok_or_else(|| {
            PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                "prepared private-frame block is missing".to_string(),
            ])
        })?;
        let block = graph.block(block_id).ok_or_else(|| {
            PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                "prepared private-frame graph block is missing".to_string(),
            ])
        })?;
        let mut branch_condition = None;
        for inst_id in &block.insts {
            instruction_steps = instruction_steps.saturating_add(1);
            if instruction_steps > MAX_INSTRUCTION_STEPS {
                return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                    vec!["prepared private-frame instruction budget exhausted".to_string()],
                ));
            }
            let instruction = graph.inst(*inst_id).ok_or_else(|| {
                PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                    "prepared private-frame instruction is missing".to_string(),
                ])
            })?;
            if let InstPayload::Phi { predecessors } = &instruction.payload {
                let previous = predecessor.ok_or_else(|| {
                    PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                        "entry private-frame block unexpectedly contains a phi".to_string(),
                    ])
                })?;
                let index = predecessors
                    .iter()
                    .position(|candidate| *candidate == previous)
                    .ok_or_else(|| {
                        PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                            "private-frame phi predecessor is absent".to_string(),
                        ])
                    })?;
                let source = *instruction.inputs.get(index).ok_or_else(|| {
                    PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                        "private-frame phi input is absent".to_string(),
                    ])
                })?;
                if let Some(output) = instruction.output {
                    let value = private_frame_value(artifact, &values, source)?;
                    values.insert(output, value);
                }
                continue;
            }
            let InstPayload::Op(op) = &instruction.payload else {
                unreachable!();
            };
            let input_value = |index: usize| {
                instruction
                    .inputs
                    .get(index)
                    .copied()
                    .ok_or_else(|| {
                        PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                            "prepared private-frame operation input is absent".to_string(),
                        ])
                    })
                    .and_then(|value| private_frame_value(artifact, &values, value))
            };
            if matches!(op, SSAOp::Nop | SSAOp::Branch { .. } | SSAOp::Return { .. }) {
                continue;
            }
            if matches!(op, SSAOp::CBranch { .. }) {
                branch_condition = Some(input_value(1)?.bits != 0);
                continue;
            }
            if matches!(op, SSAOp::Store { .. }) {
                let address = input_value(0)?;
                let stored = input_value(1)?;
                if address.width != 64 || stored.width % 8 != 0 {
                    return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                        vec!["prepared private-frame store shape mismatch".to_string()],
                    ));
                }
                private_frame_write_memory(&mut memory, address.bits, stored);
                continue;
            }
            let output = instruction.output.ok_or_else(|| {
                PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                    "prepared private-frame value output is absent".to_string(),
                ])
            })?;
            let width = graph
                .value(output)
                .and_then(|value| value.var.size.checked_mul(8))
                .ok_or(PrivateFrameSemanticCFunctionError::InvalidWidth(0))?;
            let exact = match op {
                SSAOp::Load { .. } => {
                    let address = input_value(0)?;
                    if address.width != 64 || width % 8 != 0 {
                        return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                            vec!["prepared private-frame load shape mismatch".to_string()],
                        ));
                    }
                    private_frame_read_memory(&memory, address.bits, width)?
                }
                SSAOp::Copy { .. } => private_frame_same_width(input_value(0)?, width)?,
                SSAOp::IntAdd { .. } => private_frame_binary(
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    u64::wrapping_add,
                )?,
                SSAOp::IntSub { .. } => private_frame_binary(
                    input_value(0)?,
                    input_value(1)?,
                    width,
                    u64::wrapping_sub,
                )?,
                SSAOp::IntEqual { .. } => PrivateFrameExactBits::new(
                    width,
                    u64::from(input_value(0)?.bits == input_value(1)?.bits),
                )?,
                SSAOp::IntSLess { .. } => PrivateFrameExactBits::new(
                    width,
                    u64::from(input_value(0)?.signed() < input_value(1)?.signed()),
                )?,
                SSAOp::IntZExt { .. } => {
                    let source = input_value(0)?;
                    if source.width >= width {
                        return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                            vec![
                                "prepared private-frame zero-extension width mismatch".to_string(),
                            ],
                        ));
                    }
                    PrivateFrameExactBits::new(width, source.bits)?
                }
                _ => {
                    return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                        vec![format!(
                            "prepared private-frame runner does not admit {op:?}"
                        )],
                    ));
                }
            };
            values.insert(output, exact);
        }
        let source_block = function.cfg().get_block(current).ok_or_else(|| {
            PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                "prepared private-frame source block is missing".to_string(),
            ])
        })?;
        let next = match &source_block.terminator {
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                if branch_condition.ok_or_else(|| {
                    PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                        "prepared private-frame branch condition is absent".to_string(),
                    ])
                })? {
                    *true_target
                } else {
                    *false_target
                }
            }
            BlockTerminator::Branch { target } => *target,
            BlockTerminator::Fallthrough { next } => *next,
            BlockTerminator::Return => {
                return private_frame_value(
                    artifact,
                    &values,
                    witness.return_value().binding().value(),
                )
                .map(|value| value.bits);
            }
            BlockTerminator::IndirectBranch
            | BlockTerminator::Switch { .. }
            | BlockTerminator::Call { .. }
            | BlockTerminator::IndirectCall { .. }
            | BlockTerminator::None => {
                return Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
                    vec!["prepared private-frame control shape is unsupported".to_string()],
                ));
            }
        };
        predecessor = Some(block_id);
        current = next;
    }
    Err(PrivateFrameSemanticCFunctionError::InvalidComposition(
        vec!["prepared private-frame block budget exhausted".to_string()],
    ))
}

fn private_frame_value(
    artifact: &SsaArtifact,
    values: &BTreeMap<ValueId, PrivateFrameExactBits>,
    value: ValueId,
) -> Result<PrivateFrameExactBits, PrivateFrameSemanticCFunctionError> {
    if let Some(value) = values.get(&value) {
        return Ok(*value);
    }
    let graph_value = artifact.graph().value(value).ok_or_else(|| {
        PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
            "prepared private-frame value is foreign".to_string(),
        ])
    })?;
    let width = graph_value
        .var
        .size
        .checked_mul(8)
        .ok_or(PrivateFrameSemanticCFunctionError::InvalidWidth(0))?;
    let bits = graph_value.var.constant_bits().ok_or_else(|| {
        PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
            "prepared private-frame value is unavailable".to_string(),
        ])
    })?;
    PrivateFrameExactBits::new(width, bits)
}

fn private_frame_same_width(
    value: PrivateFrameExactBits,
    width: u32,
) -> Result<PrivateFrameExactBits, PrivateFrameSemanticCFunctionError> {
    if value.width != width {
        return Err(PrivateFrameSemanticCFunctionError::InvalidWidth(width));
    }
    PrivateFrameExactBits::new(width, value.bits)
}

fn private_frame_binary(
    left: PrivateFrameExactBits,
    right: PrivateFrameExactBits,
    width: u32,
    op: fn(u64, u64) -> u64,
) -> Result<PrivateFrameExactBits, PrivateFrameSemanticCFunctionError> {
    if left.width != width || right.width != width {
        return Err(PrivateFrameSemanticCFunctionError::InvalidWidth(width));
    }
    PrivateFrameExactBits::new(width, op(left.bits, right.bits))
}

fn private_frame_write_memory(
    memory: &mut BTreeMap<u64, u8>,
    address: u64,
    value: PrivateFrameExactBits,
) {
    for index in 0..value.width / 8 {
        memory.insert(
            address + u64::from(index),
            (value.bits >> (index * 8)) as u8,
        );
    }
}

fn private_frame_read_memory(
    memory: &BTreeMap<u64, u8>,
    address: u64,
    width: u32,
) -> Result<PrivateFrameExactBits, PrivateFrameSemanticCFunctionError> {
    let mut bits = 0u64;
    for index in 0..width / 8 {
        let byte = memory
            .get(&(address + u64::from(index)))
            .copied()
            .ok_or_else(|| {
                PrivateFrameSemanticCFunctionError::InvalidComposition(vec![
                    "prepared private-frame load reads uninitialized memory".to_string(),
                ])
            })?;
        bits |= u64::from(byte) << (index * 8);
    }
    PrivateFrameExactBits::new(width, bits)
}

fn evaluate_function(
    predicate: &PrivateFramePredicate,
    true_value: u64,
    false_value: u64,
    input: u64,
) -> u64 {
    if evaluate_predicate(predicate, input) {
        true_value
    } else {
        false_value
    }
}

fn evaluate_predicate(predicate: &PrivateFramePredicate, input: u64) -> bool {
    let value = |operand: &PrivateFramePredicateOperand| match operand {
        PrivateFramePredicateOperand::HomeReload { .. } => input,
        PrivateFramePredicateOperand::Constant { value, .. } => value.bits(),
    };
    let width = predicate.left.ty().width_bits();
    let left = value(&predicate.left) & width_mask(width);
    let right = value(&predicate.right) & width_mask(width);
    match (predicate.op, predicate.interpretation) {
        (MachineComparisonOp::Equal, _) => left == right,
        (MachineComparisonOp::NotEqual, _) => left != right,
        (MachineComparisonOp::LessThan, MachineSignedness::Unsigned) => left < right,
        (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Unsigned) => left <= right,
        (MachineComparisonOp::LessThan, MachineSignedness::Signed) => {
            signed_value(left, width) < signed_value(right, width)
        }
        (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Signed) => {
            signed_value(left, width) <= signed_value(right, width)
        }
    }
}

fn width_mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        1_u64.checked_shl(width).unwrap_or(0).wrapping_sub(1)
    }
}

fn signed_value(value: u64, width: u32) -> i64 {
    if width == 64 {
        value as i64
    } else {
        let shift = 64_u32.saturating_sub(width);
        ((value << shift) as i64) >> shift
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierProjection,
        SourceFunctionInterface, SourceLogicalValue, SourceStackSlotSpec, SourceType,
        SourceTypeGraph, SsaArtifact, StackAddressBase,
    };

    use super::*;

    const REVISION: &[u8] = b"private-frame-r2dec-v1";
    const MAGIC: u64 = 0x5ec2e7;

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-private-frame-r2dec-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("eax", 0, 4));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("edi", 8, 4));
        arch.add_register(RegisterDef::new("rsp", 16, 8));
        arch.add_register(RegisterDef::new("rbp", 24, 8));
        arch.add_register(RegisterDef::new("rip", 32, 8));
        arch
    }

    fn interface_with_carrier(
        revision: &[u8],
        declare_local: bool,
        full_carrier: bool,
    ) -> SourceFunctionInterface {
        let parameter_storage = storage(8, if full_carrier { 8 } else { 4 });
        let return_storage = storage(0, if full_carrier { 8 } else { 4 });
        let mut slots = vec![SourceStackSlotSpec::new_parameter_home(
            StackAddressBase::FramePointer,
            storage(24, 8),
            -8,
            4,
            0,
            parameter_storage,
        )];
        if declare_local {
            slots.push(SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(24, 8),
                -4,
                4,
            ));
        }
        if full_carrier {
            let types = SourceTypeGraph::new(
                [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
                [],
            )
            .expect("signed int type graph");
            let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
            SourceFunctionInterface::new_exact_with_logical_types(
                revision.to_vec(),
                "sysv_amd64",
                [SourceAbiParameterSpec::new(0, parameter_storage)],
                SourceFunctionReturn::Register {
                    storage: return_storage,
                },
                slots,
                [SourceLogicalValue::new(0, low32)],
                Some(SourceLogicalValue::new(0, low32)),
                Some(types),
            )
            .expect("exact full-carrier private-frame interface")
        } else {
            SourceFunctionInterface::new_exact(
                revision.to_vec(),
                "sysv",
                [SourceAbiParameterSpec::new(0, parameter_storage)],
                SourceFunctionReturn::Register {
                    storage: return_storage,
                },
                slots,
            )
            .expect("exact private-frame interface")
        }
    }

    fn frame_address(unique: u64, offset: i64) -> (R2ILOp, Varnode) {
        let address = Varnode::unique(unique, 8);
        (
            R2ILOp::IntAdd {
                dst: address.clone(),
                a: Varnode::register(24, 8),
                b: Varnode::constant(offset as u64, 8),
            },
            address,
        )
    }

    fn artifact_with_predicate_and_local(
        magic: u64,
        revision: &[u8],
        signed_less: bool,
        declare_local: bool,
    ) -> SsaArtifact {
        artifact_with_carrier(magic, revision, signed_less, declare_local, false)
    }

    fn artifact_with_carrier(
        magic: u64,
        revision: &[u8],
        signed_less: bool,
        declare_local: bool,
        full_carrier: bool,
    ) -> SsaArtifact {
        let mut entry = R2ILBlock::new(0x1000, 0x10);
        let saved_fp = Varnode::unique(0x10, 8);
        entry.push(R2ILOp::Copy {
            dst: saved_fp.clone(),
            src: Varnode::register(24, 8),
        });
        entry.push(R2ILOp::IntSub {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
            val: saved_fp,
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: Varnode::register(16, 8),
        });
        let (home_address_op, home_address) = frame_address(0x20, -8);
        entry.push(home_address_op);
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: home_address.clone(),
            val: Varnode::register(8, 4),
        });
        let home_value = Varnode::unique(0x28, 4);
        entry.push(R2ILOp::Load {
            dst: home_value.clone(),
            space: SpaceId::Ram,
            addr: home_address,
        });
        let condition = Varnode::unique(0x30, 1);
        entry.push(if signed_less {
            R2ILOp::IntSLess {
                dst: condition.clone(),
                a: home_value,
                b: Varnode::constant(magic, 4),
            }
        } else {
            R2ILOp::IntEqual {
                dst: condition.clone(),
                a: home_value,
                b: Varnode::constant(magic, 4),
            }
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x1020, 8),
            cond: condition,
        });

        let mut false_arm = R2ILBlock::new(0x1010, 0x10);
        let (false_address_op, false_address) = frame_address(0x40, -4);
        false_arm.push(false_address_op);
        false_arm.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: false_address,
            val: Varnode::constant(0, 4),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });

        let mut true_arm = R2ILBlock::new(0x1020, 0x10);
        let (true_address_op, true_address) = frame_address(0x50, -4);
        true_arm.push(true_address_op);
        true_arm.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: true_address,
            val: Varnode::constant(1, 4),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });

        let mut join = R2ILBlock::new(0x1030, 0x10);
        let (local_address_op, local_address) = frame_address(0x60, -4);
        join.push(local_address_op);
        let loaded_result = if full_carrier {
            Varnode::unique(0x68, 4)
        } else {
            Varnode::register(0, 4)
        };
        join.push(R2ILOp::Load {
            dst: loaded_result.clone(),
            space: SpaceId::Ram,
            addr: local_address,
        });
        if full_carrier {
            join.push(R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: loaded_result,
            });
            join.push(R2ILOp::IntZExt {
                dst: Varnode::register(0, 8),
                src: Varnode::register(0, 4),
            });
        }
        let restored_fp = Varnode::unique(0x70, 8);
        join.push(R2ILOp::Load {
            dst: restored_fp.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        join.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: restored_fp,
        });
        join.push(R2ILOp::Load {
            dst: Varnode::register(32, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        join.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });

        SsaArtifact::for_decompile_with_interface(
            &[entry, false_arm, true_arm, join],
            Some(&arch()),
            interface_with_carrier(revision, declare_local, full_carrier),
        )
        .expect("private-frame artifact")
    }

    fn artifact_with_predicate(magic: u64, revision: &[u8], signed_less: bool) -> SsaArtifact {
        artifact_with_predicate_and_local(magic, revision, signed_less, true)
    }

    fn artifact(magic: u64, revision: &[u8]) -> SsaArtifact {
        artifact_with_predicate(magic, revision, false)
    }

    fn certified(magic: u64, revision: &[u8]) -> CertifiedMachineFunction {
        CertifiedMachineFunction::from_artifact(&artifact(magic, revision))
            .expect("private-frame certification")
    }

    fn signed_certified() -> CertifiedMachineFunction {
        CertifiedMachineFunction::from_artifact(&artifact_with_predicate(0, REVISION, true))
            .expect("signed private-frame certification")
    }

    fn function() -> (
        CertifiedMachineFunction,
        CertifiedPrivateFrameSemanticCFunction,
    ) {
        let certified = certified(MAGIC, REVISION);
        let function = CertifiedPrivateFrameSemanticCFunction::from_certified(&certified)
            .expect("private-frame semantic C");
        (certified, function)
    }

    fn assert_refused(function: &CertifiedPrivateFrameSemanticCFunction) {
        assert!(!function.audit().has_exact_private_frame_function());
        assert!(function.render_certified_c().is_err());
    }

    fn compiled_results(
        function: &CertifiedPrivateFrameSemanticCFunction,
        inputs: &[u64],
    ) -> Vec<u64> {
        let function = function.clone().with_cosmetic_names("probe", "x", "value");
        let mut source = function.render_certified_c().expect("strict C");
        source.push_str(
			"\n#include <stdio.h>\n#include <stdlib.h>\n\nint main(int argc, char **argv) {\n\tif (argc != 2) { return 2; }\n\tuint32_t x = (uint32_t)strtoull(argv[1], NULL, 0);\n\tprintf(\"%u\\n\", (unsigned)r2s_fn_probe(x));\n\treturn 0;\n}\n",
		);
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "r2dec-private-frame-{}-{nonce}",
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
        let results = inputs
            .iter()
            .map(|input| {
                let output = Command::new(&executable)
                    .arg(input.to_string())
                    .output()
                    .expect("compiled C probe");
                assert!(output.status.success());
                String::from_utf8(output.stdout)
                    .expect("UTF-8 output")
                    .trim()
                    .parse::<u64>()
                    .expect("integer output")
            })
            .collect();
        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_file(&executable);
        let _ = fs::remove_dir(&directory);
        results
    }

    #[test]
    fn renders_only_the_visible_parameter_predicate_and_local() {
        let (_, function) = function();
        assert!(function.audit().has_exact_private_frame_function());
        assert_eq!(
            function
                .phases()
                .iter()
                .map(PrivateFramePhase::kind)
                .collect::<Vec<_>>(),
            ALL_PHASES
        );
        let c = function.render_certified_c().expect("strict C");
        assert!(c.contains("uint32_t r2s_fn_certified_private_frame(uint32_t r2s_arg_argument)"));
        assert!(c.contains("r2s_arg_argument == ((uint32_t)UINT64_C(0x5ec2e7))"));
        assert!(c.contains("r2s_local_result = (uint32_t)UINT64_C(0x1)"));
        assert!(c.contains("return r2s_local_result;"));
        for forbidden in [
            "rsp",
            "rbp",
            "rip",
            "saved_fp",
            "return_address",
            "load(",
            "store(",
            "r2s_read",
            "r2s_write",
            "frame_address",
            "home_reload",
        ] {
            assert!(
                !c.contains(forbidden),
                "leaked forbidden helper/state: {forbidden}"
            );
        }
    }

    #[test]
    fn renders_structurally_private_result_without_a_source_local_declaration() {
        let artifact = artifact_with_predicate_and_local(MAGIC, REVISION, false, false);
        let certified = CertifiedMachineFunction::from_artifact(&artifact)
            .expect("hidden-result private-frame certification");
        let witness = certified
            .private_frame_conditional_return()
            .expect("hidden-result private-frame witness");
        assert!(!witness.local_slot().source_declared());
        let function = CertifiedPrivateFrameSemanticCFunction::from_certified(&certified)
            .expect("hidden-result private-frame semantic C");
        assert!(function.audit().has_exact_private_frame_function());
        let c = function
            .render_certified_c()
            .expect("hidden-result strict C");
        assert!(c.contains("r2s_local_result"));
        assert!(c.contains("return r2s_local_result;"));
    }

    #[test]
    fn renders_signed_low32_logic_from_full_sysv_carriers_and_hidden_result() {
        let artifact = artifact_with_carrier(MAGIC, REVISION, false, false, true);
        let certified = CertifiedMachineFunction::from_artifact(&artifact)
            .expect("full-carrier hidden-result certification");
        let witness = certified
            .private_frame_conditional_return()
            .expect("full-carrier private-frame witness");
        assert!(!witness.local_slot().source_declared());
        assert_eq!(witness.home().parameter().storage().size, 8);
        assert_eq!(witness.return_storage().size, 8);
        assert_eq!(witness.return_relays().len(), 1);
        assert_eq!(witness.return_transforms().len(), 1);
        let exact_abi = expected_abi(witness).expect("full-carrier ABI manifest");
        validate_return_transforms(&certified, witness, &exact_abi)
            .expect("full-carrier return transforms");
        let function = CertifiedPrivateFrameSemanticCFunction::from_certified(&certified)
            .expect("full-carrier private-frame semantic C");
        assert!(function.abi().logical_signed());
        assert_eq!(function.abi().local_width_bits(), 32);
        let c = function.render_certified_c().expect("signed strict C");
        assert!(c.contains("int32_t r2s_fn_certified_private_frame(int32_t r2s_arg_argument)"));
        let report = check_private_frame_differential(
            &artifact,
            &certified,
            &function,
            [0, MAGIC - 1, MAGIC, MAGIC + 1, u32::MAX as u64],
        )
        .expect("full-carrier prepared-SSA differential");
        assert!(report.has_equivalence());
    }

    #[test]
    fn bounded_source_and_candidate_differential_covers_boundaries_and_random() {
        let (certified, function) = function();
        let source = artifact(MAGIC, REVISION);
        let mut inputs = vec![0, 1, MAGIC - 1, MAGIC, MAGIC + 1, u32::MAX as u64];
        let mut state = 0xd1ff_3a71_cafe_babe_u64;
        for _ in 0..64 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            inputs.push(state & u32::MAX as u64);
        }
        let report = check_private_frame_differential(&source, &certified, &function, inputs)
            .expect("bounded differential");
        assert!(report.has_equivalence());
        assert!(report.cases().iter().any(|case| {
            case.input() == MAGIC && case.source_result() == 1 && case.candidate_result() == 1
        }));
        assert!(report.cases().iter().any(|case| {
            case.input() == MAGIC + 1 && case.source_result() == 0 && case.candidate_result() == 0
        }));
        assert!(matches!(
            check_private_frame_differential(
                &source,
                &certified,
                &function,
                0..=(MAX_DIFFERENTIAL_CASES as u64)
            ),
            Err(PrivateFrameSemanticCFunctionError::TooManyDifferentialCases(_))
        ));
    }

    #[test]
    fn names_are_cosmetic_and_do_not_change_differential_results() {
        let (certified, function) = function();
        let source = artifact(MAGIC, REVISION);
        let renamed =
            function
                .clone()
                .with_cosmetic_names("renamed-function", "input value", "answer value");
        assert_eq!(function.origin(), renamed.origin());
        assert_eq!(function.predicate(), renamed.predicate());
        assert_eq!(function.phases(), renamed.phases());
        assert_ne!(
            function.render_certified_c().expect("original C"),
            renamed.render_certified_c().expect("renamed C")
        );
        assert!(
            check_private_frame_differential(
                &source,
                &certified,
                &renamed,
                [0, MAGIC, u32::MAX as u64],
            )
            .expect("renamed differential")
            .has_equivalence()
        );
    }

    #[test]
    fn rejects_dropped_duplicated_and_reordered_phases() {
        let (_, function) = function();
        for index in [2, 3, 4, 5] {
            let mut dropped = function.clone();
            let mut phases = dropped.phases.to_vec();
            phases.remove(index);
            dropped.phases = phases.into_boxed_slice();
            assert_refused(&dropped);
        }
        let mut duplicated = function.clone();
        let mut phases = duplicated.phases.to_vec();
        phases.insert(3, phases[2]);
        duplicated.phases = phases.into_boxed_slice();
        assert_refused(&duplicated);
        for (left, right) in [(2, 3), (3, 4), (4, 5)] {
            let mut reordered = function.clone();
            let mut phases = reordered.phases.to_vec();
            phases.swap(left, right);
            reordered.phases = phases.into_boxed_slice();
            assert_refused(&reordered);
        }
    }

    #[test]
    fn rejects_polarity_opcode_constant_signedness_and_substitution_mutations() {
        let (_, function) = function();
        let mut swapped = function.clone();
        std::mem::swap(&mut swapped.true_value, &mut swapped.false_value);
        assert_refused(&swapped);

        let mut opcode = function.clone();
        opcode.predicate.op = MachineComparisonOp::NotEqual;
        assert_refused(&opcode);

        let other =
            CertifiedPrivateFrameSemanticCFunction::from_certified(&certified(MAGIC + 7, REVISION))
                .expect("other constant");
        let mut constant = function.clone();
        constant.predicate.right = other.predicate.right.clone();
        assert_refused(&constant);

        let mut signedness = function.clone();
        signedness.predicate.interpretation = MachineSignedness::Signed;
        assert_refused(&signedness);

        let mut duplicated_home = function.clone();
        duplicated_home.predicate.right = duplicated_home.predicate.left.clone();
        assert_refused(&duplicated_home);
    }

    #[test]
    fn rejects_stale_bindings_types_storage_revision_permit_and_mapping() {
        let (_, function) = function();
        let other = CertifiedPrivateFrameSemanticCFunction::from_certified(&certified(
            MAGIC + 7,
            b"private-frame-r2dec-other-revision",
        ))
        .expect("other private frame");

        let mut stale_schema = function.clone();
        stale_schema.schema_version = stale_schema.schema_version.saturating_add(1);
        assert_refused(&stale_schema);

        let mut stale_binding = function.clone();
        if let PrivateFramePredicateOperand::HomeReload { binding, .. } =
            &mut stale_binding.predicate.left
        {
            *binding = stale_binding.abi.parameter;
        } else {
            panic!("fixture Home operand")
        }
        assert_refused(&stale_binding);

        let mut stale_type = function.clone();
        if let PrivateFramePredicateOperand::HomeReload { ty, .. } = &mut stale_type.predicate.left
        {
            *ty = MachineType::Integer {
                width_bits: 32,
                signedness: MachineSignedness::Signed,
            };
        } else {
            panic!("fixture Home operand")
        }
        assert_refused(&stale_type);

        let mut stale_storage = function.clone();
        stale_storage.abi.return_storage = storage(8, 4);
        assert_refused(&stale_storage);

        let mut stale_width = function.clone();
        stale_width.abi.local_width_bits = 64;
        assert_refused(&stale_width);

        let mut stale_revision = function.clone();
        stale_revision.witness = other.witness.clone();
        assert_refused(&stale_revision);

        let mut forged_permit = function.clone();
        forged_permit.render_permit = other.render_permit.clone();
        assert_refused(&forged_permit);

        let mut dropped_mapping = function.clone();
        dropped_mapping.mappings = dropped_mapping.mappings[..dropped_mapping.mappings.len() - 1]
            .to_vec()
            .into_boxed_slice();
        assert_refused(&dropped_mapping);

        let mut duplicated_mapping = function;
        let mut mappings = duplicated_mapping.mappings.to_vec();
        mappings.push(mappings[0].clone());
        duplicated_mapping.mappings = mappings.into_boxed_slice();
        assert_refused(&duplicated_mapping);
    }

    #[test]
    fn emitted_c_compiles_and_matches_false_true_boundary_and_random_probes() {
        let (_, function) = function();
        let mut inputs = vec![0, MAGIC - 1, MAGIC, MAGIC + 1, u32::MAX as u64];
        let mut state = 0xa11c_e55e_9912_3344_u64;
        for _ in 0..24 {
            state = state.wrapping_mul(1664525).wrapping_add(1013904223);
            inputs.push(state & u32::MAX as u64);
        }
        for (input, actual) in inputs.iter().zip(compiled_results(&function, &inputs)) {
            assert_eq!(actual, u64::from(*input == MAGIC), "input {input:#x}");
        }
    }

    #[test]
    fn signed_min_max_differential_and_compiled_c_use_portable_sign_keys() {
        let certified = signed_certified();
        let function = CertifiedPrivateFrameSemanticCFunction::from_certified(&certified)
            .expect("signed private-frame semantic C");
        assert_eq!(function.predicate().op(), MachineComparisonOp::LessThan);
        assert_eq!(
            function.predicate().interpretation(),
            MachineSignedness::Signed
        );
        let inputs = [0x8000_0000, 0xffff_ffff, 0, 1, 0x7fff_ffff];
        let source = artifact_with_predicate(0, REVISION, true);
        let differential = check_private_frame_differential(&source, &certified, &function, inputs)
            .expect("signed differential");
        assert!(differential.has_equivalence());
        assert_eq!(compiled_results(&function, &inputs), [1, 1, 0, 0, 0]);
        let c = function.render_certified_c().expect("signed strict C");
        assert!(c.contains("^ ((uint32_t)UINT64_C(0x80000000))"));
        assert!(!c.contains("(int32_t)"));
    }
}
