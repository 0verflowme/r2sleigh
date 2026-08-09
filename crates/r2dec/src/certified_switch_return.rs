//! Closed semantic-C composition for one exact switch with terminal returns.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_SWITCH_TERMINAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedMachineProjection, CertifiedRenderPermit, CertifiedSourceTerminator,
    CertifiedSwitchControl, CertifiedTypedRegionKind, RenderAuthorizationError, TypedRegionMapping,
    certify_switch_terminal_return_region,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalInstructionSite, MachineBuildError, SemanticObligationId,
    SsaArtifact,
};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionBuildError, RegionObligationMapping,
};
use crate::semantic_c::{
    SemanticCError, SemanticCExprId, SemanticCExprKind, SemanticCFunctionInterface,
    SemanticCFunctionReturn, SemanticCInputOrigin, SemanticCReturn, storage_type, value_name,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_SWITCH_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_SWITCH_TERMINAL_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SwitchReturnFunctionScope {
    ClosedSelectorAndConstantTerminalReturns,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SwitchReturnOutcome {
    Void,
    Value { width_bits: u32, bits: u64 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSwitchReturnArm {
    layer: SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
    outcome: SwitchReturnOutcome,
}

impl CertifiedSwitchReturnArm {
    fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, SwitchReturnFunctionError> {
        let block_addr = accounting.block_addr();
        let report = accounting.audit();
        let Some(block) = accounting.source_block() else {
            return Err(SwitchReturnFunctionError::InvalidReturnArm(block_addr));
        };
        let [returned] = accounting.semantic_returns() else {
            return Err(SwitchReturnFunctionError::InvalidReturnArm(block_addr));
        };
        if !report.has_exact_source_accounting()
            || report.has_residuals()
            || accounting.return_controls().len() != 1
            || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || block.instructions().last() != Some(&returned.producer())
            || !accounting.memory_statements().is_empty()
            || !accounting.direct_calls().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || !accounting.switch_controls().is_empty()
        {
            return Err(SwitchReturnFunctionError::InvalidReturnArm(block_addr));
        }
        let return_producer = returned.producer();
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let returned = layer
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == return_producer)
            .ok_or(SwitchReturnFunctionError::InvalidReturnArm(block_addr))?;
        let outcome = constant_return_outcome(&layer, returned)?;
        let arm = Self {
            layer,
            return_producer,
            outcome,
        };
        if !arm.has_exact_terminal_return() {
            return Err(SwitchReturnFunctionError::InvalidReturnArm(block_addr));
        }
        Ok(arm)
    }

    pub const fn layer(&self) -> &SemanticCBlockStepLayer {
        &self.layer
    }

    pub const fn return_producer(&self) -> CanonicalInstructionId {
        self.return_producer
    }

    pub const fn outcome(&self) -> SwitchReturnOutcome {
        self.outcome
    }

    pub fn block_addr(&self) -> u64 {
        self.layer.accounting().block_addr()
    }

    pub fn returned(&self) -> Option<&SemanticCReturn> {
        self.layer
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == self.return_producer)
    }

    fn has_exact_terminal_return(&self) -> bool {
        let accounting = self.layer.accounting();
        let Some(block) = accounting.source_block() else {
            return false;
        };
        let Some(returned) = self.returned() else {
            return false;
        };
        self.layer.audit().has_exact_source_order()
            && accounting.audit().has_exact_source_accounting()
            && !accounting.audit().has_residuals()
            && matches!(block.terminator(), CertifiedSourceTerminator::Return)
            && block.successors().is_empty()
            && block.instructions().last() == Some(&self.return_producer)
            && self.layer.steps().last().map(|step| step.source()) == Some(self.return_producer)
            && accounting.return_controls().len() == 1
            && accounting.memory_statements().is_empty()
            && accounting.direct_calls().is_empty()
            && accounting.direct_controls().is_empty()
            && accounting.conditional_controls().is_empty()
            && accounting.switch_controls().is_empty()
            && constant_return_outcome(&self.layer, returned).ok() == Some(self.outcome)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSwitchReturnCase {
    value: u64,
    target: u64,
    arm: CertifiedSwitchReturnArm,
}

impl CertifiedSwitchReturnCase {
    pub const fn value(&self) -> u64 {
        self.value
    }

    pub const fn target(&self) -> u64 {
        self.target
    }

    pub const fn arm(&self) -> &CertifiedSwitchReturnArm {
        &self.arm
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSwitchReturnFunction {
    schema_version: u32,
    scope: SwitchReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    header: SemanticCBlockStepLayer,
    switch_control: CertifiedSwitchControl,
    cases: Box<[CertifiedSwitchReturnCase]>,
    default_target: u64,
    default_arm: CertifiedSwitchReturnArm,
    mappings: Box<[RegionObligationMapping]>,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SwitchReturnFunctionError {
    Machine(MachineBuildError),
    Accounting(RegionBuildError),
    Statement(SemanticCStatementError),
    Authorization(RenderAuthorizationError),
    MissingSwitchControl(u64),
    InvalidHeader,
    InvalidSelector,
    InvalidReturnArm(u64),
    NonConstantReturn(u64),
    InvalidComposition(Vec<String>),
    MissingFunctionInterface,
    SemanticC(SemanticCError),
}

impl std::fmt::Display for SwitchReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "switch return function failed: {self:?}")
    }
}

impl std::error::Error for SwitchReturnFunctionError {}

impl From<MachineBuildError> for SwitchReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for SwitchReturnFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<SemanticCStatementError> for SwitchReturnFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<RenderAuthorizationError> for SwitchReturnFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl From<SemanticCError> for SwitchReturnFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

impl CertifiedSwitchReturnFunction {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, SwitchReturnFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(artifact)?;
        Self::from_projection(&certified)
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, SwitchReturnFunctionError> {
        let header_addr = certified.topology().entry_addr();
        let switch_control = certified
            .switch_control_for_block(header_addr)
            .cloned()
            .ok_or(SwitchReturnFunctionError::MissingSwitchControl(header_addr))?;
        let header_accounting =
            CertifiedSingleBlockAccounting::from_projection_block(certified, header_addr)?;
        let header_report = header_accounting.audit();
        if !header_report.has_exact_source_accounting() {
            return Err(SwitchReturnFunctionError::InvalidComposition(
                header_report.invalid().to_vec(),
            ));
        }
        if header_report.has_residuals()
            || header_accounting.switch_controls() != [switch_control.clone()]
            || !header_accounting.memory_statements().is_empty()
            || !header_accounting.direct_calls().is_empty()
            || !header_accounting.direct_controls().is_empty()
            || !header_accounting.conditional_controls().is_empty()
            || !header_accounting.return_controls().is_empty()
        {
            return Err(SwitchReturnFunctionError::InvalidHeader);
        }
        validate_selector(&header_accounting, &switch_control)?;
        let header = SemanticCBlockStepLayer::from_accounting(header_accounting)?;

        let mut cases = Vec::with_capacity(switch_control.topology().cases().len());
        for (value, target) in switch_control.topology().cases() {
            let arm = CertifiedSwitchReturnArm::from_accounting(
                CertifiedSingleBlockAccounting::from_projection_block(certified, *target)?,
            )?;
            cases.push(CertifiedSwitchReturnCase {
                value: *value,
                target: *target,
                arm,
            });
        }
        let default_target = switch_control.topology().default_target();
        let default_arm = CertifiedSwitchReturnArm::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, default_target)?,
        )?;

        let mappings = std::iter::once(header.accounting())
            .chain(cases.iter().map(|case| case.arm.layer().accounting()))
            .chain([default_arm.layer().accounting()])
            .flat_map(CertifiedSingleBlockAccounting::mappings)
            .cloned()
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let typed_mappings = typed_region_mappings(
            std::iter::once(header.accounting())
                .chain(cases.iter().map(|case| case.arm.layer().accounting()))
                .chain([default_arm.layer().accounting()]),
        );
        let render_permit = certify_switch_terminal_return_region(
            certified.origin(),
            certified.ledger(),
            typed_mappings,
            switch_control.topology(),
            &switch_control,
        )?;
        let function = Self {
            schema_version: CERTIFIED_SWITCH_RETURN_FUNCTION_SCHEMA_VERSION,
            scope: SwitchReturnFunctionScope::ClosedSelectorAndConstantTerminalReturns,
            name: format!("certified_sub_{header_addr:x}"),
            origin: certified.origin().clone(),
            header,
            switch_control,
            cases: cases.into_boxed_slice(),
            default_target,
            default_arm,
            mappings,
            render_permit,
        };
        let report = function.audit();
        if !report.has_exact_switch_returns() {
            return Err(SwitchReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SwitchReturnFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn header(&self) -> &SemanticCBlockStepLayer {
        &self.header
    }

    pub const fn switch_control(&self) -> &CertifiedSwitchControl {
        &self.switch_control
    }

    pub const fn cases(&self) -> &[CertifiedSwitchReturnCase] {
        &self.cases
    }

    pub const fn default_target(&self) -> u64 {
        self.default_target
    }

    pub const fn default_arm(&self) -> &CertifiedSwitchReturnArm {
        &self.default_arm
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn render_permit(&self) -> &CertifiedRenderPermit {
        &self.render_permit
    }

    pub fn audit(&self) -> SwitchReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        let header_accounting = self.header.accounting();
        if self.schema_version != CERTIFIED_SWITCH_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("switch-return schema mismatch".to_string());
        }
        if self.scope != SwitchReturnFunctionScope::ClosedSelectorAndConstantTerminalReturns {
            invalid.push("switch-return scope mismatch".to_string());
        }
        if self.origin != *header_accounting.origin()
            || self.origin != *self.switch_control.origin()
            || self
                .cases
                .iter()
                .any(|case| self.origin != *case.arm.layer().accounting().origin())
            || self.origin != *self.default_arm.layer().accounting().origin()
        {
            invalid.push("switch children do not share one exact artifact origin".to_string());
        }
        let interface = header_accounting.expression_layer().function_interface();
        if interface.is_none()
            || self.cases.iter().any(|case| {
                case.arm
                    .layer()
                    .accounting()
                    .expression_layer()
                    .function_interface()
                    != interface
            })
            || self
                .default_arm
                .layer()
                .accounting()
                .expression_layer()
                .function_interface()
                != interface
        {
            invalid
                .push("switch children do not share one function interface revision".to_string());
        }
        if !self.header.audit().has_exact_source_order()
            || header_accounting.audit().has_residuals()
            || header_accounting.switch_controls() != [self.switch_control.clone()]
            || validate_selector(header_accounting, &self.switch_control).is_err()
            || self
                .cases
                .iter()
                .any(|case| !case.arm.has_exact_terminal_return())
            || !self.default_arm.has_exact_terminal_return()
        {
            invalid.push("selector, header, or terminal return evidence is not exact".to_string());
        }

        let topology = self.origin.topology();
        let header_addr = header_accounting.block_addr();
        let expected_cases = self.switch_control.topology().cases();
        let actual_cases = self
            .cases
            .iter()
            .map(|case| (case.value, case.target))
            .collect::<Vec<_>>();
        let targets = actual_cases
            .iter()
            .map(|(_, target)| *target)
            .chain([self.default_target])
            .collect::<BTreeSet<_>>();
        if topology.entry_addr() != header_addr
            || topology.blocks().len() != targets.len() + 1
            || actual_cases.as_slice() != expected_cases
            || self.default_target != self.switch_control.topology().default_target()
            || self.default_arm.block_addr() != self.default_target
            || self
                .cases
                .iter()
                .any(|case| case.arm.block_addr() != case.target)
            || targets.len() != self.cases.len() + 1
            || topology
                .block(header_addr)
                .is_none_or(|block| !block.predecessors().is_empty())
            || targets.iter().any(|target| {
                topology
                    .block(*target)
                    .is_none_or(|block| block.predecessors() != [header_addr])
            })
        {
            invalid.push("case/default topology is not exactly closed".to_string());
        }
        if std::iter::once(&self.header)
            .chain(self.cases.iter().map(|case| case.arm.layer()))
            .chain([self.default_arm.layer()])
            .any(|layer| {
                !layer.accounting().memory_statements().is_empty()
                    || !layer.accounting().direct_calls().is_empty()
                    || layer
                        .accounting()
                        .expression_layer()
                        .input_origins()
                        .values()
                        .any(|origin| matches!(origin, SemanticCInputOrigin::StackSlot { .. }))
            })
            || self
                .origin
                .source()
                .instructions()
                .keys()
                .any(|id| matches!(id.site, CanonicalInstructionSite::Phi(_)))
        {
            invalid.push("memory, call, stack, or phi semantics entered switch subset".to_string());
        }

        let expected_mappings = std::iter::once(header_accounting)
            .chain(self.cases.iter().map(|case| case.arm.layer().accounting()))
            .chain([self.default_arm.layer().accounting()])
            .flat_map(CertifiedSingleBlockAccounting::mappings)
            .cloned()
            .collect::<Vec<_>>();
        let counts = counts(
            self.mappings
                .iter()
                .map(RegionObligationMapping::obligation),
        );
        let expected = self
            .origin
            .source()
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let actual = counts.keys().copied().collect::<BTreeSet<_>>();
        let missing = expected.difference(&actual).copied().collect();
        let unexpected = actual.difference(&expected).copied().collect();
        let duplicate = counts
            .iter()
            .filter_map(|(id, count)| (*count > 1).then_some(*id))
            .collect();
        if self.mappings.as_ref() != expected_mappings.as_slice()
            || expected_mappings.len() != expected.len()
            || self.mappings.iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    crate::certified_region::RegionObligationDisposition::Residualized { .. }
                )
            })
        {
            invalid.push("switch mappings are not disjoint, complete, and closed".to_string());
        }
        let typed_mappings = typed_region_mappings(
            std::iter::once(header_accounting)
                .chain(self.cases.iter().map(|case| case.arm.layer().accounting()))
                .chain([self.default_arm.layer().accounting()]),
        );
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::SwitchTerminalReturnFunction,
            CERTIFIED_SWITCH_RETURN_FUNCTION_SCHEMA_VERSION,
            &typed_mappings,
        ) {
            invalid.push("render permit does not match the closed switch".to_string());
        }
        SwitchReturnFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, SwitchReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_switch_returns() || !self.render_permit.authorizes_certified_c() {
            return Err(SwitchReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let interface = self
            .header
            .accounting()
            .expression_layer()
            .function_interface()
            .ok_or(SwitchReturnFunctionError::MissingFunctionInterface)?;
        let selector = self.switch_control.selector().binding();
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        write!(&mut output, "{} {}(", return_type(interface)?, self.name)
            .expect("String writes cannot fail");
        render_parameters(&mut output, interface)?;
        output.push_str(") {\n");
        writeln!(
            &mut output,
            "\tswitch ((uint64_t){}) {{",
            value_name(selector)
        )
        .expect("String writes cannot fail");
        for case in &self.cases {
            writeln!(&mut output, "\tcase UINT64_C(0x{:x}):", case.value)
                .expect("String writes cannot fail");
            render_return(&mut output, case.arm.outcome(), "\t\t", interface)?;
        }
        output.push_str("\tdefault:\n");
        render_return(&mut output, self.default_arm.outcome(), "\t\t", interface)?;
        output.push_str("\t}\n}\n");
        Ok(output)
    }
}

fn validate_selector(
    accounting: &CertifiedSingleBlockAccounting,
    control: &CertifiedSwitchControl,
) -> Result<(), SwitchReturnFunctionError> {
    let selector = control.selector();
    let interface = accounting
        .expression_layer()
        .function_interface()
        .ok_or(SwitchReturnFunctionError::MissingFunctionInterface)?;
    if interface
        .parameters()
        .get(control.parameter_index() as usize)
        .filter(|parameter| {
            parameter.index() == control.parameter_index()
                && parameter.storage() == control.parameter_storage()
                && parameter.value() == Some(selector.binding())
                && parameter.ty() == selector.ty()
        })
        .is_none()
    {
        return Err(SwitchReturnFunctionError::InvalidSelector);
    }
    if selector.producer().is_some()
        || selector.constant().is_some()
        || selector.memory_access().is_some()
    {
        return Err(SwitchReturnFunctionError::InvalidSelector);
    }
    Ok(())
}

fn constant_return_outcome(
    layer: &SemanticCBlockStepLayer,
    returned: &SemanticCReturn,
) -> Result<SwitchReturnOutcome, SwitchReturnFunctionError> {
    match returned.values() {
        [] => Ok(SwitchReturnOutcome::Void),
        [value] => {
            let expression = constant_expression(layer, value.expression(), 0).ok_or(
                SwitchReturnFunctionError::NonConstantReturn(layer.accounting().block_addr()),
            )?;
            Ok(SwitchReturnOutcome::Value {
                width_bits: value.binding().width_bits(),
                bits: expression,
            })
        }
        _ => Err(SwitchReturnFunctionError::InvalidReturnArm(
            layer.accounting().block_addr(),
        )),
    }
}

fn constant_expression(
    layer: &SemanticCBlockStepLayer,
    expression: SemanticCExprId,
    depth: u32,
) -> Option<u64> {
    if depth > 16 {
        return None;
    }
    match layer
        .accounting()
        .expression_layer()
        .expr(expression)?
        .kind()
    {
        SemanticCExprKind::Constant { value, .. } => Some(value.bits()),
        SemanticCExprKind::Copy { input } => constant_expression(layer, *input, depth + 1),
        _ => None,
    }
}

fn typed_region_mappings<'a>(
    accountings: impl IntoIterator<Item = &'a CertifiedSingleBlockAccounting>,
) -> Vec<TypedRegionMapping> {
    let accountings = accountings.into_iter().collect::<Vec<_>>();
    accountings
        .iter()
        .flat_map(|accounting| accounting.mappings())
        .filter_map(|mapping| {
            let [effect] = accountings[0].ledger().effects(mapping.obligation()) else {
                return None;
            };
            Some(TypedRegionMapping::new(
                mapping.obligation(),
                effect.disposition().clone(),
            ))
        })
        .collect()
}

fn return_type(
    interface: &SemanticCFunctionInterface,
) -> Result<&'static str, SwitchReturnFunctionError> {
    match interface.return_kind() {
        SemanticCFunctionReturn::Void => Ok("void"),
        SemanticCFunctionReturn::Register { ty, .. } => Ok(storage_type(ty)?),
    }
}

fn render_parameters(
    output: &mut String,
    interface: &SemanticCFunctionInterface,
) -> Result<(), SwitchReturnFunctionError> {
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

fn render_return(
    output: &mut String,
    outcome: SwitchReturnOutcome,
    indent: &str,
    interface: &SemanticCFunctionInterface,
) -> Result<(), SwitchReturnFunctionError> {
    match (interface.return_kind(), outcome) {
        (SemanticCFunctionReturn::Void, SwitchReturnOutcome::Void) => {
            writeln!(output, "{indent}return;").expect("String writes cannot fail");
        }
        (
            SemanticCFunctionReturn::Register { ty, .. },
            SwitchReturnOutcome::Value { width_bits, bits },
        ) if ty.width_bits() == width_bits => {
            writeln!(
                output,
                "{indent}return (({})UINT64_C(0x{bits:x}));",
                storage_type(ty)?
            )
            .expect("String writes cannot fail");
        }
        _ => return Err(SwitchReturnFunctionError::InvalidHeader),
    }
    Ok(())
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SwitchReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl SwitchReturnFunctionAuditReport {
    pub fn has_exact_switch_returns(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }

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
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SwitchReturnDifferentialCase {
    selector: u64,
    source_target: u64,
    source: SwitchReturnOutcome,
    certified: SwitchReturnOutcome,
    rendered: SwitchReturnOutcome,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SwitchReturnDifferentialReport {
    cases: Box<[SwitchReturnDifferentialCase]>,
}

impl SwitchReturnDifferentialReport {
    pub const fn cases(&self) -> &[SwitchReturnDifferentialCase] {
        &self.cases
    }

    pub fn all_match(&self) -> bool {
        self.cases
            .iter()
            .all(|case| case.source == case.certified && case.source == case.rendered)
    }
}

/// Bounded independent check of source switch routing, certified arms, and the
/// strict rendered switch grammar. It covers every case plus one default probe.
pub fn check_switch_return_differential(
    artifact: &SsaArtifact,
    max_paths: u32,
) -> Result<SwitchReturnDifferentialReport, String> {
    let function = CertifiedSwitchReturnFunction::from_artifact(artifact)
        .map_err(|error| format!("switch candidate not admitted: {error}"))?;
    let required = function.cases.len().saturating_add(1);
    if max_paths == 0 || required > max_paths as usize {
        return Err("switch differential path budget exceeded".to_string());
    }
    let rendered = function
        .render_certified_c()
        .map_err(|error| format!("switch rendering failed: {error}"))?;
    let rendered_arms = parse_rendered_arms(&rendered)?;
    let (source_cases, source_default) = artifact
        .function()
        .switch_info(artifact.function().entry)
        .ok_or_else(|| "source switch topology is missing".to_string())?;
    let source_default =
        source_default.ok_or_else(|| "source switch default is missing".to_string())?;
    let case_values = source_cases
        .iter()
        .map(|(value, _)| *value)
        .collect::<BTreeSet<_>>();
    let default_probe = (0..=u64::MAX)
        .find(|value| !case_values.contains(value))
        .ok_or_else(|| "no representable default selector probe".to_string())?;
    let selectors = case_values.into_iter().chain([default_probe]);
    let mut reports = Vec::with_capacity(required);
    for selector in selectors {
        let source_target = source_cases
            .iter()
            .find_map(|(value, target)| (*value == selector).then_some(*target))
            .unwrap_or(source_default);
        let selected = function.cases.iter().find(|case| case.value == selector);
        let certified = selected
            .map(|case| case.arm.outcome)
            .unwrap_or(function.default_arm.outcome);
        let source = source_return_outcome(artifact, source_target)?;
        let rendered_label = selected.map(|_| Some(selector)).unwrap_or(None);
        let rendered = rendered_arms
            .get(&rendered_label)
            .copied()
            .ok_or_else(|| "rendered switch omitted a selected arm".to_string())?;
        reports.push(SwitchReturnDifferentialCase {
            selector,
            source_target,
            source,
            certified,
            rendered,
        });
    }
    let report = SwitchReturnDifferentialReport {
        cases: reports.into_boxed_slice(),
    };
    if !report.all_match() {
        return Err("switch differential mismatch".to_string());
    }
    Ok(report)
}

fn source_return_outcome(
    artifact: &SsaArtifact,
    block_addr: u64,
) -> Result<SwitchReturnOutcome, String> {
    let returns = artifact
        .certificates()
        .returns
        .iter()
        .filter(|returned| returned.block_addr == block_addr)
        .collect::<Vec<_>>();
    match returns.as_slice() {
        [] => Ok(SwitchReturnOutcome::Void),
        [returned] => {
            let value = artifact
                .graph()
                .value(returned.value)
                .ok_or_else(|| "source return value is missing".to_string())?;
            let bits = value.var.constant_bits().or_else(|| {
                artifact
                    .graph()
                    .def_inst(returned.value)
                    .and_then(|instruction| artifact.graph().inst(instruction))
                    .and_then(|instruction| instruction.inputs.first())
                    .and_then(|input| artifact.graph().value(*input))
                    .and_then(|input| input.var.constant_bits())
            });
            Ok(SwitchReturnOutcome::Value {
                width_bits: value.var.size.saturating_mul(8),
                bits: bits
                    .ok_or_else(|| "source return is not independently constant".to_string())?,
            })
        }
        _ => Err("source arm has ambiguous return certificates".to_string()),
    }
}

fn parse_rendered_arms(
    rendered: &str,
) -> Result<BTreeMap<Option<u64>, SwitchReturnOutcome>, String> {
    let mut result = BTreeMap::new();
    let mut pending = None;
    for line in rendered.lines() {
        if let Some(value) = line
            .strip_prefix("\tcase UINT64_C(0x")
            .and_then(|value| value.strip_suffix("):"))
        {
            pending =
                Some(Some(u64::from_str_radix(value, 16).map_err(|_| {
                    "rendered case label is malformed".to_string()
                })?));
        } else if line == "\tdefault:" {
            pending = Some(None);
        } else if let Some(label) = pending {
            let outcome = if line == "\t\treturn;" {
                SwitchReturnOutcome::Void
            } else {
                let (ty, bits) = line
                    .strip_prefix("\t\treturn ((")
                    .and_then(|line| line.strip_suffix("));"))
                    .and_then(|line| line.split_once(")UINT64_C(0x"))
                    .ok_or_else(|| "rendered switch return is malformed".to_string())?;
                let width_bits = match ty {
                    "uint8_t" => 8,
                    "uint16_t" => 16,
                    "uint32_t" => 32,
                    "uint64_t" => 64,
                    _ => return Err("rendered switch return type is unsupported".to_string()),
                };
                SwitchReturnOutcome::Value {
                    width_bits,
                    bits: u64::from_str_radix(bits, 16)
                        .map_err(|_| "rendered return constant is malformed".to_string())?,
                }
            };
            if result.insert(label, outcome).is_some() {
                return Err("rendered switch duplicated a label".to_string());
            }
            pending = None;
        }
    }
    if pending.is_some() || !result.contains_key(&None) {
        return Err("rendered switch has an incomplete default arm".to_string());
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SwitchCase, SwitchInfo, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn,
    };

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("switch-return-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch.add_register(RegisterDef::new("rsi", 24, 8));
        arch
    }

    fn interface(parameter_storage: CanonicalStorageId) -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"switch-return-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            SourceFunctionReturn::Register {
                storage: storage(0, 8),
            },
            [],
        )
        .expect("function interface")
    }

    fn source_blocks() -> Vec<R2ILBlock> {
        let mut header = R2ILBlock::new(0x9000, 4);
        header.push(R2ILOp::BranchInd {
            target: Varnode::register(8, 8),
        });
        header.set_switch_info(SwitchInfo {
            switch_addr: 0x9000,
            min_val: 1,
            max_val: 7,
            default_target: Some(0x9060),
            cases: vec![
                SwitchCase {
                    value: 1,
                    target: 0x9020,
                },
                SwitchCase {
                    value: 7,
                    target: 0x9040,
                },
            ],
        });
        let arm = |addr, value| {
            let mut arm = R2ILBlock::new(addr, 4);
            arm.push(R2ILOp::Copy {
                dst: Varnode::register(0, 8),
                src: Varnode::constant(value, 8),
            });
            arm.push(R2ILOp::Return {
                target: Varnode::register(16, 8),
            });
            arm
        };
        vec![header, arm(0x9020, 11), arm(0x9040, 22), arm(0x9060, 33)]
    }

    fn artifact() -> SsaArtifact {
        SsaArtifact::raw_with_interface(&source_blocks(), Some(&arch()), interface(storage(8, 8)))
            .expect("switch-return artifact")
    }

    fn compile(source: &str) {
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                "-fsyntax-only",
                "-x",
                "c",
                "-",
            ])
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("C compiler required");
        compiler
            .stdin
            .as_mut()
            .expect("compiler stdin")
            .write_all(source.as_bytes())
            .expect("write C source");
        let output = compiler.wait_with_output().expect("wait for compiler");
        assert!(
            output.status.success(),
            "generated C failed:\n{}\n{}",
            source,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn exact_closed_switch_return_is_authorized_compiles_and_differentiates() {
        let artifact = artifact();
        let function =
            CertifiedSwitchReturnFunction::from_artifact(&artifact).expect("closed switch return");
        assert!(function.audit().has_exact_switch_returns());
        assert!(function.render_permit().authorizes_certified_c());
        assert_eq!(function.switch_control().parameter_storage(), storage(8, 8));
        let source = function.render_certified_c().expect("certified switch C");
        assert!(source.contains("switch ((uint64_t)v_"));
        assert!(source.contains("case UINT64_C(0x1):"));
        assert!(source.contains("default:"));
        compile(&source);
        let differential =
            check_switch_return_differential(&artifact, 3).expect("bounded switch differential");
        assert_eq!(differential.cases().len(), 3);
        assert!(differential.all_match());
    }

    #[test]
    fn deleted_duplicated_reordered_cases_and_returns_fail_audit() {
        let function = CertifiedSwitchReturnFunction::from_artifact(&artifact())
            .expect("closed switch return");
        let mut deleted = function.clone();
        deleted.cases = deleted.cases[1..].to_vec().into_boxed_slice();
        assert!(!deleted.audit().has_exact_switch_returns());

        let mut duplicated = function.clone();
        duplicated.cases = duplicated
            .cases
            .iter()
            .cloned()
            .chain([duplicated.cases[0].clone()])
            .collect::<Vec<_>>()
            .into_boxed_slice();
        assert!(!duplicated.audit().has_exact_switch_returns());

        let mut reordered = function.clone();
        reordered.cases.swap(0, 1);
        assert!(!reordered.audit().has_exact_switch_returns());

        let mut reordered_returns = function.clone();
        let first = reordered_returns.cases[0].arm.clone();
        reordered_returns.cases[0].arm = reordered_returns.cases[1].arm.clone();
        reordered_returns.cases[1].arm = first;
        assert!(!reordered_returns.audit().has_exact_switch_returns());

        let mut deleted_return = function;
        deleted_return.default_arm.return_producer = deleted_return.switch_control.producer();
        assert!(!deleted_return.audit().has_exact_switch_returns());
    }

    #[test]
    fn missing_interface_and_wrong_parameter_storage_fail_closed() {
        let blocks = source_blocks();
        let no_interface =
            SsaArtifact::raw(&blocks, Some(&arch())).expect("switch without interface");
        assert!(matches!(
            CertifiedSwitchReturnFunction::from_artifact(&no_interface),
            Err(SwitchReturnFunctionError::MissingSwitchControl(0x9000))
        ));

        let wrong_storage =
            SsaArtifact::raw_with_interface(&blocks, Some(&arch()), interface(storage(24, 8)))
                .expect("switch with wrong parameter storage");
        assert!(matches!(
            CertifiedSwitchReturnFunction::from_artifact(&wrong_storage),
            Err(SwitchReturnFunctionError::MissingSwitchControl(0x9000))
        ));
    }

    #[test]
    fn bounded_differential_refuses_insufficient_path_budget() {
        assert_eq!(
            check_switch_return_differential(&artifact(), 2),
            Err("switch differential path budget exceeded".to_string())
        );
    }
}
