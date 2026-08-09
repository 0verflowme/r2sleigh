//! Exact whole-function rendering for one sealed conditional return funnel.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_CONDITIONAL_RETURN_FUNNEL_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedConditionalReturnCarrier, CertifiedConditionalReturnFunnelControl,
    CertifiedMachineFunction, CertifiedRenderPermit, CertifiedTypedRegionKind, EffectDisposition,
    RenderAuthorizationError, TypedRegionMapping, certify_conditional_return_funnel_region,
};
use r2ssa::{
    CanonicalInstructionId, MachineBuildError, MachineValueBinding, MachineValueUse,
    SemanticObligationId, SsaArtifact,
};
use serde::Serialize;

use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCExpressionLayer, SemanticCFunctionInterface,
    SemanticCFunctionReturn, SemanticCInputOrigin, storage_type, value_name,
};

pub const CERTIFIED_CONDITIONAL_FUNNEL_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_CONDITIONAL_RETURN_FUNNEL_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ConditionalFunnelReturnFunctionScope {
    ClosedConditionalFunnelWithOneSharedTerminalReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum ConditionalFunnelCarrierKind {
    RegisterPhi,
    PrivateStackScalar,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ConditionalFunnelCarrierManifest {
    kind: ConditionalFunnelCarrierKind,
    producer: CanonicalInstructionId,
    binding: MachineValueBinding,
    width_bits: u32,
}

impl ConditionalFunnelCarrierManifest {
    pub const fn kind(&self) -> ConditionalFunnelCarrierKind {
        self.kind
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn width_bits(&self) -> u32 {
        self.width_bits
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum ConditionalFunnelPhaseKind {
    Predicate,
    TrueCandidateAssignment,
    FalseCandidateAssignment,
    CarrierMerge,
    ReturnTransform,
    SharedReturn,
}

/// One render-critical phase in strict structured-C order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ConditionalFunnelPhase {
    kind: ConditionalFunnelPhaseKind,
    producer: CanonicalInstructionId,
    value: MachineValueBinding,
}

impl ConditionalFunnelPhase {
    pub const fn kind(&self) -> ConditionalFunnelPhaseKind {
        self.kind
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn value(&self) -> MachineValueBinding {
        self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalFunnelReturnFunction {
    schema_version: u32,
    scope: ConditionalFunnelReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    control: CertifiedConditionalReturnFunnelControl,
    carrier: ConditionalFunnelCarrierManifest,
    phases: Box<[ConditionalFunnelPhase]>,
    mappings: Box<[TypedRegionMapping]>,
    expressions: SemanticCExpressionLayer,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConditionalFunnelReturnFunctionError {
    Machine(MachineBuildError),
    Authorization(RenderAuthorizationError),
    SemanticC(SemanticCError),
    MissingUniqueFunnel(usize),
    MissingFunctionInterface,
    MissingExpression(CanonicalInstructionId),
    InvalidWidth(u32),
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for ConditionalFunnelReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "conditional funnel return function failed: {self:?}")
    }
}

impl std::error::Error for ConditionalFunnelReturnFunctionError {}

impl From<MachineBuildError> for ConditionalFunnelReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RenderAuthorizationError> for ConditionalFunnelReturnFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl From<SemanticCError> for ConditionalFunnelReturnFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

impl CertifiedConditionalFunnelReturnFunction {
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, ConditionalFunnelReturnFunctionError> {
        let certified = CertifiedMachineFunction::from_artifact(artifact)?;
        Self::from_certified(&certified)
    }

    pub fn from_certified(
        certified: &CertifiedMachineFunction,
    ) -> Result<Self, ConditionalFunnelReturnFunctionError> {
        let controls = certified
            .conditional_return_funnels()
            .values()
            .collect::<Vec<_>>();
        let [control] = controls.as_slice() else {
            return Err(ConditionalFunnelReturnFunctionError::MissingUniqueFunnel(
                controls.len(),
            ));
        };
        let control = (*control).clone();
        let carrier = expected_carrier(&control);
        supported_width(carrier.width_bits)?;
        let phases = expected_phases(&control).into_boxed_slice();
        let mappings = exact_mappings(certified)?.into_boxed_slice();
        let expressions =
            SemanticCExpressionLayer::from_conditional_return_funnel(certified, &control)?;
        let render_permit = certify_conditional_return_funnel_region(
            certified.origin(),
            certified.ledger(),
            mappings.iter().cloned(),
            &control,
        )?;
        let function = Self {
            schema_version: CERTIFIED_CONDITIONAL_FUNNEL_RETURN_FUNCTION_SCHEMA_VERSION,
            scope: ConditionalFunnelReturnFunctionScope::ClosedConditionalFunnelWithOneSharedTerminalReturn,
            name: format!("certified_sub_{:x}", certified.topology().entry_addr()),
            origin: certified.origin().clone(),
            control,
            carrier,
            phases,
            mappings,
            expressions,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_conditional_funnel_return() {
            return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        function.validate_render_expressions()?;
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> ConditionalFunnelReturnFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn control(&self) -> &CertifiedConditionalReturnFunnelControl {
        &self.control
    }

    pub const fn carrier(&self) -> &ConditionalFunnelCarrierManifest {
        &self.carrier
    }

    pub const fn phases(&self) -> &[ConditionalFunnelPhase] {
        &self.phases
    }

    pub const fn mappings(&self) -> &[TypedRegionMapping] {
        &self.mappings
    }

    pub const fn expressions(&self) -> &SemanticCExpressionLayer {
        &self.expressions
    }

    pub const fn render_permit(&self) -> &CertifiedRenderPermit {
        &self.render_permit
    }

    pub fn audit(&self) -> ConditionalFunnelReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        if self.schema_version != CERTIFIED_CONDITIONAL_FUNNEL_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("conditional-funnel schema mismatch".to_string());
        }
        if self.scope
            != ConditionalFunnelReturnFunctionScope::ClosedConditionalFunnelWithOneSharedTerminalReturn
        {
            invalid.push("conditional-funnel scope mismatch".to_string());
        }
        if self.control.origin() != &self.origin || self.control.carrier().origin() != &self.origin
        {
            invalid.push("control and carrier do not share the exact artifact origin".to_string());
        }
        if self.carrier != expected_carrier(&self.control) {
            invalid.push("carrier kind, producer, binding, or local width mismatch".to_string());
        }
        if self.phases.as_ref() != expected_phases(&self.control).as_slice() {
            invalid.push("typed funnel phases are incomplete or out of order".to_string());
        }
        let expected_phase_counts = counts(self.phases.iter().map(|phase| phase.kind));
        if expected_phase_counts.get(&ConditionalFunnelPhaseKind::Predicate) != Some(&1)
            || expected_phase_counts.get(&ConditionalFunnelPhaseKind::TrueCandidateAssignment)
                != Some(&1)
            || expected_phase_counts.get(&ConditionalFunnelPhaseKind::FalseCandidateAssignment)
                != Some(&1)
            || expected_phase_counts.get(&ConditionalFunnelPhaseKind::CarrierMerge) != Some(&1)
            || expected_phase_counts.get(&ConditionalFunnelPhaseKind::SharedReturn) != Some(&1)
            || expected_phase_counts
                .get(&ConditionalFunnelPhaseKind::ReturnTransform)
                .copied()
                .unwrap_or_default()
                != self.control.return_value_chain().len()
        {
            invalid.push("typed funnel phases are missing or duplicated".to_string());
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
            invalid.push("conditional-funnel mapping manifest is not exact and closed".to_string());
        }
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::ConditionalReturnFunnelFunction,
            CERTIFIED_CONDITIONAL_FUNNEL_RETURN_FUNCTION_SCHEMA_VERSION,
            &self.mappings,
        ) {
            invalid
                .push("conditional-funnel render permit does not match the manifest".to_string());
        }
        if self.validate_control_interface().is_err() {
            invalid.push("control, carrier, and function interface mismatch".to_string());
        }
        if self.validate_render_expressions().is_err() {
            invalid.push(
                "predicate, candidates, or return chain are not exactly renderable".to_string(),
            );
        }
        ConditionalFunnelReturnFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, ConditionalFunnelReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_conditional_funnel_return()
            || !self.render_permit.authorizes_certified_c()
        {
            return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        self.validate_control_interface()?;
        self.validate_render_expressions()?;
        let interface = self
            .expressions
            .function_interface()
            .ok_or(ConditionalFunnelReturnFunctionError::MissingFunctionInterface)?;
        let return_ty = return_type(interface)?;
        let local_ty = uint_type(self.carrier.width_bits)?;
        let local = value_name(self.carrier.binding);
        let condition = self.render_value(self.control.branch_control().condition(), false)?;
        let true_value = self.render_value(self.control.true_candidate().value(), false)?;
        let false_value = self.render_value(self.control.false_candidate().value(), false)?;
        let returned = self.render_return_chain()?;

        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        write!(&mut output, "\n{return_ty} {}(", self.name).expect("String writes cannot fail");
        render_parameters(&mut output, interface)?;
        output.push_str(") {\n");
        output.push_str("\t(void)r2s_wrap_add;\n");
        output.push_str("\t(void)r2s_wrap_sub;\n");
        output.push_str("\t(void)r2s_wrap_mul;\n");
        output.push_str("\t(void)r2s_shl;\n");
        output.push_str("\t(void)r2s_lshr;\n");
        output.push_str("\t(void)r2s_ashr;\n");
        output.push_str("\t(void)r2s_signed_key;\n");
        output.push_str("\t(void)r2s_sext;\n");
        writeln!(&mut output, "\t{local_ty} {local};").expect("String writes cannot fail");
        writeln!(
            &mut output,
            "\tif ((uint8_t)({condition}) != UINT8_C(0)) {{"
        )
        .expect("String writes cannot fail");
        writeln!(&mut output, "\t\t{local} = ({local_ty})({true_value});")
            .expect("String writes cannot fail");
        output.push_str("\t} else {\n");
        writeln!(&mut output, "\t\t{local} = ({local_ty})({false_value});")
            .expect("String writes cannot fail");
        output.push_str("\t}\n");
        writeln!(&mut output, "\treturn ({return_ty})({returned});")
            .expect("String writes cannot fail");
        output.push_str("}\n");
        Ok(output)
    }

    fn validate_control_interface(&self) -> Result<(), ConditionalFunnelReturnFunctionError> {
        let interface = self
            .expressions
            .function_interface()
            .ok_or(ConditionalFunnelReturnFunctionError::MissingFunctionInterface)?;
        let expected_width = self
            .control
            .return_storage()
            .size
            .checked_mul(8)
            .ok_or(ConditionalFunnelReturnFunctionError::InvalidWidth(0))?;
        match interface.return_kind() {
            SemanticCFunctionReturn::Register { storage, ty }
                if *storage == self.control.return_storage()
                    && ty.width_bits() == expected_width
                    && self.control.return_value().binding().width_bits() == expected_width =>
            {
                supported_width(expected_width)
            }
            _ => Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                vec!["shared return does not match the exact ABI register".to_string()],
            )),
        }
    }

    fn validate_render_expressions(&self) -> Result<(), ConditionalFunnelReturnFunctionError> {
        self.validate_value_inputs(self.control.branch_control().condition(), false, None)?;
        self.validate_value_inputs(self.control.true_candidate().value(), false, None)?;
        self.validate_value_inputs(self.control.false_candidate().value(), false, None)?;
        let carrier_binding = self.carrier.binding;
        let carrier_inputs = self
            .expressions
            .input_origins()
            .iter()
            .filter(|(_, origin)| {
                matches!(
                    origin,
                    SemanticCInputOrigin::ConditionalReturnCarrier { .. }
                )
            })
            .collect::<Vec<_>>();
        if self.control.return_value_chain().is_empty() {
            if self.control.return_value().binding() != carrier_binding
                || !carrier_inputs.is_empty()
            {
                return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                    vec!["empty return chain does not return the exact carrier".to_string()],
                ));
            }
        } else {
            let exact_carrier_input = matches!(
                carrier_inputs.as_slice(),
                [(binding, SemanticCInputOrigin::ConditionalReturnCarrier { producer })]
                    if **binding == carrier_binding && *producer == self.carrier.producer
            );
            if !exact_carrier_input {
                return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                    vec!["return chain lacks its exact proof-derived carrier input".to_string()],
                ));
            }
        }
        let mut previous = carrier_binding;
        for value in self.control.return_value_chain() {
            self.validate_value_inputs(value, true, Some(previous))?;
            let producer = value.producer().ok_or(
                ConditionalFunnelReturnFunctionError::InvalidComposition(vec![
                    "return transform has no producer".to_string(),
                ]),
            )?;
            let entity = self
                .expressions
                .entity_for_producer(producer)
                .filter(|entity| entity.output() == value.binding())
                .ok_or(ConditionalFunnelReturnFunctionError::MissingExpression(
                    producer,
                ))?;
            let sources = self.expressions.source_bindings(entity.root())?;
            if sources != BTreeSet::from([previous]) {
                return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                    vec![
                        "return transform does not consume exactly the previous phase".to_string(),
                    ],
                ));
            }
            previous = value.binding();
        }
        if previous != self.control.return_value().binding() {
            return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                vec!["return chain does not produce the exact returned binding".to_string()],
            ));
        }
        Ok(())
    }

    fn validate_value_inputs(
        &self,
        value: &MachineValueUse,
        allow_carrier: bool,
        exact_local_dependency: Option<MachineValueBinding>,
    ) -> Result<(), ConditionalFunnelReturnFunctionError> {
        if value.constant().is_some() {
            return supported_width(value.binding().width_bits());
        }
        let Some(producer) = value.producer() else {
            return match self.expressions.input_origins().get(&value.binding()) {
                Some(SemanticCInputOrigin::AbiParameter { .. }) => Ok(()),
                Some(SemanticCInputOrigin::ConditionalReturnCarrier { producer })
                    if allow_carrier && *producer == self.carrier.producer =>
                {
                    Ok(())
                }
                None if exact_local_dependency == Some(value.binding()) => Ok(()),
                _ => Err(ConditionalFunnelReturnFunctionError::MissingExpression(
                    self.control.branch_control().producer(),
                )),
            };
        };
        let entity = self
            .expressions
            .entity_for_producer(producer)
            .filter(|entity| entity.output() == value.binding())
            .ok_or(ConditionalFunnelReturnFunctionError::MissingExpression(
                producer,
            ))?;
        for binding in self.expressions.source_bindings(entity.root())? {
            match self.expressions.input_origins().get(&binding) {
                Some(SemanticCInputOrigin::AbiParameter { .. }) => {}
                Some(SemanticCInputOrigin::ConditionalReturnCarrier { producer })
                    if allow_carrier && *producer == self.carrier.producer => {}
                None if exact_local_dependency == Some(binding) => {}
                _ => {
                    return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                        vec!["rendered value depends on a non-ABI, non-carrier source".to_string()],
                    ));
                }
            }
        }
        Ok(())
    }

    fn render_value(
        &self,
        value: &MachineValueUse,
        allow_carrier: bool,
    ) -> Result<String, ConditionalFunnelReturnFunctionError> {
        self.validate_value_inputs(value, allow_carrier, None)?;
        if let Some(constant) = value.constant() {
            let ty = uint_type(constant.width_bits())?;
            return Ok(format!("(({ty})UINT64_C(0x{:x}))", constant.bits()));
        }
        let Some(producer) = value.producer() else {
            return Ok(value_name(value.binding()));
        };
        let entity = self
            .expressions
            .entity_for_producer(producer)
            .filter(|entity| entity.output() == value.binding())
            .ok_or(ConditionalFunnelReturnFunctionError::MissingExpression(
                producer,
            ))?;
        Ok(self.expressions.render_expr(entity.root())?)
    }

    fn render_return_chain(&self) -> Result<String, ConditionalFunnelReturnFunctionError> {
        let mut rendered = value_name(self.carrier.binding);
        let mut previous = self.carrier.binding;
        for value in self.control.return_value_chain() {
            let producer =
                value
                    .producer()
                    .ok_or(ConditionalFunnelReturnFunctionError::MissingExpression(
                        self.control.return_control().producer(),
                    ))?;
            let entity = self
                .expressions
                .entity_for_producer(producer)
                .filter(|entity| entity.output() == value.binding())
                .ok_or(ConditionalFunnelReturnFunctionError::MissingExpression(
                    producer,
                ))?;
            let (expression, substitutions) = self.expressions.render_expr_substituting_input(
                entity.root(),
                previous,
                &format!("({rendered})"),
            )?;
            if substitutions != 1 {
                return Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                    vec!["return transform does not render its input exactly once".to_string()],
                ));
            }
            rendered = expression;
            previous = value.binding();
        }
        Ok(rendered)
    }
}

fn expected_carrier(
    control: &CertifiedConditionalReturnFunnelControl,
) -> ConditionalFunnelCarrierManifest {
    match control.carrier() {
        CertifiedConditionalReturnCarrier::RegisterPhi(state) => ConditionalFunnelCarrierManifest {
            kind: ConditionalFunnelCarrierKind::RegisterPhi,
            producer: state.producer(),
            binding: state.phi().binding(),
            width_bits: state.phi().binding().width_bits(),
        },
        CertifiedConditionalReturnCarrier::PrivateStackScalar(state) => {
            ConditionalFunnelCarrierManifest {
                kind: ConditionalFunnelCarrierKind::PrivateStackScalar,
                producer: state.producer(),
                binding: state.loaded_value().binding(),
                width_bits: state.width_bytes().saturating_mul(8),
            }
        }
    }
}

fn expected_phases(
    control: &CertifiedConditionalReturnFunnelControl,
) -> Vec<ConditionalFunnelPhase> {
    let carrier = expected_carrier(control);
    let mut phases = vec![
        ConditionalFunnelPhase {
            kind: ConditionalFunnelPhaseKind::Predicate,
            producer: control.branch_control().producer(),
            value: control.branch_control().condition().binding(),
        },
        ConditionalFunnelPhase {
            kind: ConditionalFunnelPhaseKind::TrueCandidateAssignment,
            producer: control.true_candidate().producer(),
            value: control.true_candidate().value().binding(),
        },
        ConditionalFunnelPhase {
            kind: ConditionalFunnelPhaseKind::FalseCandidateAssignment,
            producer: control.false_candidate().producer(),
            value: control.false_candidate().value().binding(),
        },
        ConditionalFunnelPhase {
            kind: ConditionalFunnelPhaseKind::CarrierMerge,
            producer: carrier.producer,
            value: carrier.binding,
        },
    ];
    phases.extend(
        control
            .return_value_chain()
            .iter()
            .map(|value| ConditionalFunnelPhase {
                kind: ConditionalFunnelPhaseKind::ReturnTransform,
                producer: value.producer().expect("sealed return-transform producer"),
                value: value.binding(),
            }),
    );
    phases.push(ConditionalFunnelPhase {
        kind: ConditionalFunnelPhaseKind::SharedReturn,
        producer: control.return_control().producer(),
        value: control.return_value().binding(),
    });
    phases
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

fn render_parameters(
    output: &mut String,
    interface: &SemanticCFunctionInterface,
) -> Result<(), ConditionalFunnelReturnFunctionError> {
    if interface.parameters().is_empty() {
        output.push_str("void");
        return Ok(());
    }
    for (position, parameter) in interface.parameters().iter().enumerate() {
        if position > 0 {
            output.push_str(", ");
        }
        let name = parameter
            .value()
            .map(value_name)
            .unwrap_or_else(|| format!("arg_{}", parameter.index()));
        write!(output, "{} {name}", storage_type(parameter.ty())?)
            .expect("String writes cannot fail");
    }
    Ok(())
}

fn return_type(
    interface: &SemanticCFunctionInterface,
) -> Result<&'static str, ConditionalFunnelReturnFunctionError> {
    match interface.return_kind() {
        SemanticCFunctionReturn::Register { ty, .. } => Ok(storage_type(ty)?),
        SemanticCFunctionReturn::Void => {
            Err(ConditionalFunnelReturnFunctionError::InvalidComposition(
                vec!["conditional funnel has no value return".to_string()],
            ))
        }
    }
}

fn supported_width(width: u32) -> Result<(), ConditionalFunnelReturnFunctionError> {
    uint_type(width).map(|_| ())
}

fn uint_type(width: u32) -> Result<&'static str, ConditionalFunnelReturnFunctionError> {
    match width {
        8 => Ok("uint8_t"),
        16 => Ok("uint16_t"),
        32 => Ok("uint32_t"),
        64 => Ok("uint64_t"),
        _ => Err(ConditionalFunnelReturnFunctionError::InvalidWidth(width)),
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut counts = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConditionalFunnelReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl ConditionalFunnelReturnFunctionAuditReport {
    pub fn has_exact_conditional_funnel_return(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SourceStackSlotSpec, StackAddressBase,
    };

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("conditional-funnel-return-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("x0", 8, 8));
        arch.add_register(RegisterDef::new("arg0", 16, 8));
        arch.add_register(RegisterDef::new("pc", 24, 8));
        arch
    }

    fn interface(revision: &[u8], stack: bool) -> SourceFunctionInterface {
        let slots = stack
            .then(|| SourceStackSlotSpec::new(StackAddressBase::StackPointer, storage(0, 8), -4, 4))
            .into_iter();
        SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, storage(16, 8))],
            SourceFunctionReturn::Register {
                storage: storage(8, 8),
            },
            slots,
        )
        .expect("conditional funnel interface")
    }

    fn branch_entry() -> R2ILBlock {
        let mut block = R2ILBlock::new(0x7000, 4);
        let condition = Varnode::unique(0x10, 1);
        block.push(R2ILOp::IntEqual {
            dst: condition.clone(),
            a: Varnode::register(16, 8),
            b: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7020, 8),
            cond: condition,
        });
        block
    }

    fn register_blocks() -> Vec<R2ILBlock> {
        let mut false_arm = R2ILBlock::new(0x7004, 4);
        false_arm.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0, 8),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7030, 8),
        });
        let mut true_arm = R2ILBlock::new(0x7020, 4);
        true_arm.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(1, 8),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7030, 8),
        });
        let mut join = R2ILBlock::new(0x7030, 4);
        join.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        vec![branch_entry(), false_arm, true_arm, join]
    }

    fn stack_address(unique: u64) -> (R2ILOp, Varnode) {
        let address = Varnode::unique(unique, 8);
        (
            R2ILOp::IntAdd {
                dst: address.clone(),
                a: Varnode::register(0, 8),
                b: Varnode::constant((-4_i64) as u64, 8),
            },
            address,
        )
    }

    fn store_arm(addr: u64, value: u64, unique: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        let (address_op, address) = stack_address(unique);
        block.push(address_op);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: Varnode::constant(value, 4),
        });
        block.push(R2ILOp::Branch {
            target: Varnode::ram(0x7030, 8),
        });
        block
    }

    fn stack_blocks() -> Vec<R2ILBlock> {
        let mut forwarder = R2ILBlock::new(0x7004, 4);
        forwarder.push(R2ILOp::Branch {
            target: Varnode::ram(0x7008, 8),
        });
        let mut join = R2ILBlock::new(0x7030, 4);
        let (address_op, address) = stack_address(0x50);
        let loaded = Varnode::unique(0x60, 4);
        join.push(address_op);
        join.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: address,
        });
        join.push(R2ILOp::IntZExt {
            dst: Varnode::register(8, 8),
            src: loaded,
        });
        join.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        vec![
            branch_entry(),
            forwarder,
            store_arm(0x7008, 0, 0x30),
            store_arm(0x7020, 1, 0x40),
            join,
        ]
    }

    fn register_artifact(revision: &[u8]) -> SsaArtifact {
        SsaArtifact::raw_with_interface(
            &register_blocks(),
            Some(&arch()),
            interface(revision, false),
        )
        .expect("register funnel artifact")
    }

    fn stack_artifact(revision: &[u8]) -> SsaArtifact {
        SsaArtifact::for_decompile_with_interface(
            &stack_blocks(),
            Some(&arch()),
            interface(revision, true),
        )
        .expect("stack funnel artifact")
    }

    fn compile_and_run(source: &str, name: &str, inputs: &[u64]) -> Vec<u64> {
        let executable = std::env::temp_dir().join(format!(
            "r2dec-conditional-funnel-{}-{name}",
            std::process::id()
        ));
        let mut translation_unit = source.to_string();
        translation_unit.push_str("\n#include <stdio.h>\nint main(void) {\n");
        for input in inputs {
            writeln!(
                &mut translation_unit,
                "\tprintf(\"%llu\\n\", (unsigned long long)certified_sub_7000(UINT64_C(0x{input:x})));"
            )
            .expect("String writes cannot fail");
        }
        translation_unit.push_str("\treturn 0;\n}\n");
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                "-x",
                "c",
                "-",
                "-o",
            ])
            .arg(&executable)
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("C compiler required");
        compiler
            .stdin
            .as_mut()
            .expect("compiler stdin")
            .write_all(translation_unit.as_bytes())
            .expect("write C source");
        let compiled = compiler.wait_with_output().expect("wait for compiler");
        assert!(
            compiled.status.success(),
            "generated C failed:\n{translation_unit}\n{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let executed = Command::new(&executable)
            .output()
            .expect("run compiled conditional funnel");
        let _ = std::fs::remove_file(&executable);
        assert!(executed.status.success());
        String::from_utf8(executed.stdout)
            .expect("utf8 output")
            .lines()
            .map(|line| line.parse().expect("numeric result"))
            .collect()
    }

    fn deterministic_inputs() -> [u64; 8] {
        [
            0,
            1,
            6,
            7,
            8,
            u64::MAX,
            0x9e37_79b9_7f4a_7c15,
            0xd1b5_4a32_d192_ed03,
        ]
    }

    #[test]
    fn register_phi_funnel_compiles_and_matches_bounded_inputs() {
        let function = CertifiedConditionalFunnelReturnFunction::from_artifact(&register_artifact(
            b"conditional-funnel-register-v1",
        ))
        .expect("register funnel function");
        assert!(function.audit().has_exact_conditional_funnel_return());
        assert!(function.render_permit().authorizes_certified_c());
        assert_eq!(
            function.carrier().kind(),
            ConditionalFunnelCarrierKind::RegisterPhi
        );
        assert_eq!(function.carrier().width_bits(), 64);
        let source = function.render_certified_c().expect("register funnel C");
        assert_eq!(source.matches("\tif ((uint8_t)(").count(), 1);
        assert_eq!(source.matches("\t} else {").count(), 1);
        let local = value_name(function.carrier().binding());
        assert_eq!(
            source
                .lines()
                .filter(|line| line.starts_with("\treturn (uint64_t)(") && line.contains(&local))
                .count(),
            1
        );
        assert_eq!(source.matches(&format!("\t\t{local} = ")).count(), 2);
        let inputs = deterministic_inputs();
        let actual = compile_and_run(&source, "register", &inputs);
        let expected = inputs.map(|input| u64::from(input == 7));
        assert_eq!(actual, expected);
    }

    #[test]
    fn return_substitution_uses_binding_identity_not_name_substrings() {
        let function = CertifiedConditionalFunnelReturnFunction::from_artifact(&stack_artifact(
            b"conditional-funnel-identity-substitution-v1",
        ))
        .expect("private stack funnel function");
        let [transform] = function.control().return_value_chain() else {
            panic!("one return transform");
        };
        let producer = transform.producer().expect("transform producer");
        let entity = function
            .expressions()
            .entity_for_producer(producer)
            .expect("transform expression");
        let binding_name = value_name(function.carrier().binding());
        let decoy = format!("{binding_name}0 + UINT64_C(0x17)");
        let (rendered, substitutions) = function
            .expressions()
            .render_expr_substituting_input(entity.root(), function.carrier().binding(), &decoy)
            .expect("structural substitution");
        assert_eq!(substitutions, 1);
        assert_eq!(rendered.matches(&decoy).count(), 1);
        assert!(rendered.contains("UINT64_C(0x17)"));
    }

    #[test]
    fn private_stack_funnel_hides_memory_and_matches_bounded_inputs() {
        let function = CertifiedConditionalFunnelReturnFunction::from_artifact(&stack_artifact(
            b"conditional-funnel-stack-v1",
        ))
        .expect("private stack funnel function");
        assert!(function.audit().has_exact_conditional_funnel_return());
        assert_eq!(
            function.carrier().kind(),
            ConditionalFunnelCarrierKind::PrivateStackScalar
        );
        assert_eq!(function.carrier().width_bits(), 32);
        assert_eq!(
            function.control().false_candidate().forwarder(),
            Some(0x7004)
        );
        assert_eq!(function.control().return_value_chain().len(), 1);
        assert!(matches!(
            function
                .expressions()
                .input_origins()
                .get(&function.carrier().binding()),
            Some(SemanticCInputOrigin::ConditionalReturnCarrier { producer })
                if *producer == function.carrier().producer()
        ));
        let source = function
            .render_certified_c()
            .expect("private stack funnel C");
        assert!(source.contains("\tuint32_t v_"));
        assert!(!source.contains("r2s_load"));
        assert!(!source.contains("r2s_store"));
        assert!(!source.contains("*("));
        assert!(!source.contains("sp_"));
        assert!(!source.contains("fp_"));
        let inputs = deterministic_inputs();
        let actual = compile_and_run(&source, "stack", &inputs);
        let expected = inputs.map(|input| u64::from(input == 7));
        assert_eq!(actual, expected);
    }

    #[test]
    fn assignment_carrier_phase_and_mapping_mutations_fail_before_rendering() {
        let baseline = CertifiedConditionalFunnelReturnFunction::from_artifact(&register_artifact(
            b"conditional-funnel-mutations-v1",
        ))
        .expect("baseline register funnel");
        let true_index = baseline
            .phases
            .iter()
            .position(|phase| phase.kind == ConditionalFunnelPhaseKind::TrueCandidateAssignment)
            .expect("true assignment");
        let false_index = baseline
            .phases
            .iter()
            .position(|phase| phase.kind == ConditionalFunnelPhaseKind::FalseCandidateAssignment)
            .expect("false assignment");

        let mut dropped = baseline.clone();
        let mut phases = dropped.phases.to_vec();
        phases.remove(true_index);
        dropped.phases = phases.into_boxed_slice();
        assert!(!dropped.audit().has_exact_conditional_funnel_return());
        assert!(dropped.render_certified_c().is_err());

        let mut duplicated = baseline.clone();
        let mut phases = duplicated.phases.to_vec();
        phases.insert(false_index, phases[false_index]);
        duplicated.phases = phases.into_boxed_slice();
        assert!(!duplicated.audit().has_exact_conditional_funnel_return());

        let mut swapped = baseline.clone();
        let mut phases = swapped.phases.to_vec();
        phases.swap(true_index, false_index);
        swapped.phases = phases.into_boxed_slice();
        assert!(!swapped.audit().has_exact_conditional_funnel_return());

        let mut wrong_width = baseline.clone();
        wrong_width.carrier.width_bits = 32;
        assert!(!wrong_width.audit().has_exact_conditional_funnel_return());

        let mut wrong_carrier = baseline.clone();
        wrong_carrier.carrier.kind = ConditionalFunnelCarrierKind::PrivateStackScalar;
        assert!(!wrong_carrier.audit().has_exact_conditional_funnel_return());

        let mut wrong_phase = baseline.clone();
        wrong_phase.phases.swap(0, 1);
        assert!(!wrong_phase.audit().has_exact_conditional_funnel_return());

        let mut wrong_mapping = baseline;
        wrong_mapping.mappings = wrong_mapping.mappings[1..].to_vec().into_boxed_slice();
        assert!(!wrong_mapping.audit().has_exact_conditional_funnel_return());
    }

    #[test]
    fn control_origin_and_permit_mutations_fail_audit() {
        let register = CertifiedConditionalFunnelReturnFunction::from_artifact(&register_artifact(
            b"conditional-funnel-audit-register-v1",
        ))
        .expect("register function");
        let other = CertifiedConditionalFunnelReturnFunction::from_artifact(&register_artifact(
            b"conditional-funnel-audit-register-v2",
        ))
        .expect("other register function");
        let stack = CertifiedConditionalFunnelReturnFunction::from_artifact(&stack_artifact(
            b"conditional-funnel-audit-stack-v1",
        ))
        .expect("stack function");

        let mut wrong_origin = register.clone();
        wrong_origin.origin = other.origin.clone();
        assert!(!wrong_origin.audit().has_exact_conditional_funnel_return());

        let mut wrong_control = register.clone();
        wrong_control.control = stack.control.clone();
        assert!(!wrong_control.audit().has_exact_conditional_funnel_return());

        let mut wrong_permit = register;
        wrong_permit.render_permit = other.render_permit;
        assert!(!wrong_permit.audit().has_exact_conditional_funnel_return());
        assert!(wrong_permit.render_certified_c().is_err());
    }

    #[test]
    fn construction_requires_exactly_one_funnel() {
        let mut no_funnel = register_blocks();
        no_funnel[1].ops[0] = R2ILOp::Copy {
            dst: Varnode::register(8, 4),
            src: Varnode::constant(0, 4),
        };
        let artifact = SsaArtifact::raw_with_interface(
            &no_funnel,
            Some(&arch()),
            interface(b"conditional-funnel-missing", false),
        )
        .expect("non-funnel artifact");
        assert!(matches!(
            CertifiedConditionalFunnelReturnFunction::from_artifact(&artifact),
            Err(ConditionalFunnelReturnFunctionError::MissingUniqueFunnel(0))
        ));
    }
}
