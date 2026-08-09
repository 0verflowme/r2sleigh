//! Closed semantic-C composition for one exact carrier-free loop and return.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_CARRIER_FREE_LOOP_TERMINAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedClosedNaturalLoopControl, CertifiedMachineProjection, CertifiedSourceTerminator,
    CertifiedTypedRegionKind, LedgerClosureError, TypedRegionMapping,
    certify_carrier_free_loop_terminal_return_region,
};
use r2ssa::{
    BlockTerminator, CanonicalInstructionId, CanonicalInstructionSite, MachineBuildError,
    SemanticObligationId, SsaArtifact, TrustedSsaArtifact,
};
use serde::Serialize;

use crate::certified_control::{CertifiedDirectTransferBlockRegion, DirectTransferRegionError};
use crate::certified_loop::{
    CertifiedHeaderTestedLoopFragment, HeaderTestedLoopError, LoopContinuationArm,
};
use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionBuildError,
    RegionObligationDisposition, RegionObligationMapping, TypedOutputSealError,
};
use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCExprId, SemanticCExprKind,
    SemanticCFunctionInterface, SemanticCFunctionReturn, SemanticCInputOrigin, SemanticCReturn,
    logical_return_type, render_logical_return_statement, storage_type, value_name,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_CARRIER_FREE_LOOP_TERMINAL_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum LoopReturnFunctionScope {
    ClosedOwnedPreheaderInvariantAbiConditionEmptyBackedgeAndConstantReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum LoopReturnValue {
    Void,
    Value { width_bits: u32, bits: u64 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum LoopExecutionOutcome {
    Returned(LoopReturnValue),
    BoundedNontermination { iterations: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedLoopReturnExit {
    layer: SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
    value: LoopReturnValue,
}

impl CertifiedLoopReturnExit {
    fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, LoopReturnFunctionError> {
        let block_addr = accounting.block_addr();
        let Some(block) = accounting.source_block() else {
            return Err(LoopReturnFunctionError::InvalidExit(block_addr));
        };
        let [returned] = accounting.semantic_returns() else {
            return Err(LoopReturnFunctionError::InvalidExit(block_addr));
        };
        if !accounting.audit().has_exact_source_accounting()
            || accounting.audit().has_residuals()
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
            return Err(LoopReturnFunctionError::InvalidExit(block_addr));
        }
        let return_producer = returned.producer();
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let returned = layer
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == return_producer)
            .ok_or(LoopReturnFunctionError::InvalidExit(block_addr))?;
        let value = constant_return_value(&layer, returned)?;
        let exit = Self {
            layer,
            return_producer,
            value,
        };
        if !exit.has_exact_terminal_return() {
            return Err(LoopReturnFunctionError::InvalidExit(block_addr));
        }
        Ok(exit)
    }

    pub const fn layer(&self) -> &SemanticCBlockStepLayer {
        &self.layer
    }

    pub const fn return_producer(&self) -> CanonicalInstructionId {
        self.return_producer
    }

    pub const fn value(&self) -> LoopReturnValue {
        self.value
    }

    pub fn block_addr(&self) -> u64 {
        self.layer.accounting().block_addr()
    }

    fn returned(&self) -> Option<&SemanticCReturn> {
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
            && constant_return_value(&self.layer, returned).ok() == Some(self.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedLoopReturnFunction {
    schema_version: u32,
    scope: LoopReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    loop_control: CertifiedClosedNaturalLoopControl,
    preheader: CertifiedDirectTransferBlockRegion,
    loop_fragment: CertifiedHeaderTestedLoopFragment,
    exit: CertifiedLoopReturnExit,
    output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoopReturnFunctionError {
    Machine(MachineBuildError),
    Accounting(RegionBuildError),
    Direct(DirectTransferRegionError),
    Loop(HeaderTestedLoopError),
    Statement(SemanticCStatementError),
    LedgerClosure(LedgerClosureError),
    TypedOutputSeal(TypedOutputSealError),
    MissingClosedLoopControl(u64),
    InvalidCondition,
    InvalidExit(u64),
    NonConstantReturn(u64),
    ReturnTypeMismatch,
    InvalidComposition(Vec<String>),
    MissingFunctionInterface,
    SemanticC(SemanticCError),
}

impl std::fmt::Display for LoopReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "loop return function failed: {self:?}")
    }
}

impl std::error::Error for LoopReturnFunctionError {}

impl From<MachineBuildError> for LoopReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for LoopReturnFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<DirectTransferRegionError> for LoopReturnFunctionError {
    fn from(error: DirectTransferRegionError) -> Self {
        Self::Direct(error)
    }
}

impl From<HeaderTestedLoopError> for LoopReturnFunctionError {
    fn from(error: HeaderTestedLoopError) -> Self {
        Self::Loop(error)
    }
}

impl From<SemanticCStatementError> for LoopReturnFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<LedgerClosureError> for LoopReturnFunctionError {
    fn from(error: LedgerClosureError) -> Self {
        Self::LedgerClosure(error)
    }
}

impl From<TypedOutputSealError> for LoopReturnFunctionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
    }
}

impl From<SemanticCError> for LoopReturnFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

impl CertifiedLoopReturnFunction {
    pub fn from_artifact(artifact: &TrustedSsaArtifact) -> Result<Self, LoopReturnFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(artifact)?;
        Self::from_projection(&certified)
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, LoopReturnFunctionError> {
        let preheader_addr = certified.topology().entry_addr();
        let preheader_block = certified
            .topology()
            .block(preheader_addr)
            .ok_or_else(|| LoopReturnFunctionError::InvalidComposition(Vec::new()))?;
        let header_addr = match preheader_block.terminator() {
            CertifiedSourceTerminator::Branch { target } => *target,
            _ => {
                return Err(LoopReturnFunctionError::InvalidComposition(vec![
                    "loop function entry is not an owned direct preheader".to_string(),
                ]));
            }
        };
        let loop_control = certified
            .closed_natural_loop_control_for_header(header_addr)
            .cloned()
            .ok_or(LoopReturnFunctionError::MissingClosedLoopControl(
                header_addr,
            ))?;
        let preheader = CertifiedDirectTransferBlockRegion::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, preheader_addr)?,
        )?;
        let loop_fragment =
            CertifiedHeaderTestedLoopFragment::from_projection(certified, header_addr)?;
        let exit = CertifiedLoopReturnExit::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(
                certified,
                loop_control.routing().exit(),
            )?,
        )?;
        validate_condition(loop_fragment.header().body().accounting(), &loop_control)?;

        let accountings = [
            preheader.body().accounting(),
            loop_fragment.header().body().accounting(),
            loop_fragment.body_latch().body().accounting(),
            exit.layer().accounting(),
        ];
        let ledger_closure = certify_carrier_free_loop_terminal_return_region(
            certified.origin(),
            certified.ledger(),
            typed_region_mappings(accountings),
            &loop_control,
        )?;
        let output_seal = CertifiedTypedOutputSeal::new(
            ledger_closure,
            CertifiedTypedRegionKind::CarrierFreeLoopTerminalReturnFunction,
            CERTIFIED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION,
            accountings,
        )?;
        let function = Self {
            schema_version: CERTIFIED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION,
            scope:
                LoopReturnFunctionScope::ClosedOwnedPreheaderInvariantAbiConditionEmptyBackedgeAndConstantReturn,
            name: format!("certified_sub_{preheader_addr:x}"),
            origin: certified.origin().clone(),
            loop_control,
            preheader,
            loop_fragment,
            exit,
            output_seal,
        };
        let report = function.audit();
        if !report.has_exact_loop_return() {
            return Err(LoopReturnFunctionError::InvalidComposition(report.invalid));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> LoopReturnFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn loop_control(&self) -> &CertifiedClosedNaturalLoopControl {
        &self.loop_control
    }

    pub const fn preheader(&self) -> &CertifiedDirectTransferBlockRegion {
        &self.preheader
    }

    pub const fn loop_fragment(&self) -> &CertifiedHeaderTestedLoopFragment {
        &self.loop_fragment
    }

    pub const fn exit(&self) -> &CertifiedLoopReturnExit {
        &self.exit
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        self.output_seal.mappings()
    }

    pub fn audit(&self) -> LoopReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        let accountings = [
            self.preheader.body().accounting(),
            self.loop_fragment.header().body().accounting(),
            self.loop_fragment.body_latch().body().accounting(),
            self.exit.layer().accounting(),
        ];
        if self.schema_version != CERTIFIED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("loop-return schema mismatch".to_string());
        }
        if self.scope
            != LoopReturnFunctionScope::ClosedOwnedPreheaderInvariantAbiConditionEmptyBackedgeAndConstantReturn
        {
            invalid.push("loop-return scope mismatch".to_string());
        }
        if accountings
            .iter()
            .any(|accounting| accounting.origin() != &self.origin)
            || self.loop_control.origin() != &self.origin
        {
            invalid.push("loop children do not share one exact artifact origin".to_string());
        }
        let interface = accountings[0].expression_layer().function_interface();
        if interface.is_none()
            || accountings
                .iter()
                .any(|accounting| accounting.expression_layer().function_interface() != interface)
            || interface.is_some_and(|interface| interface.parameters().len() != 1)
        {
            invalid.push(
                "loop children do not share one exact single-parameter interface".to_string(),
            );
        }
        if !self
            .preheader
            .audit()
            .has_exact_direct_transfer_accounting()
            || self.preheader.has_remaining_obligation_residuals()
            || !self.loop_fragment.audit().has_exact_loop_accounting()
            || self.loop_fragment.has_remaining_obligation_residuals()
            || !self.exit.has_exact_terminal_return()
            || validate_condition(
                self.loop_fragment.header().body().accounting(),
                &self.loop_control,
            )
            .is_err()
        {
            invalid.push("preheader, loop routing, condition, or exit is not exact".to_string());
        }
        if self.preheader.transfer() != self.loop_control.preheader_transfer()
            || self.loop_fragment.routing() != self.loop_control.routing()
            || self.loop_fragment.open_entry_predecessor()
                != self.preheader.body().accounting().block_addr()
            || self.preheader.open_successor() != self.loop_control.routing().header()
            || self.loop_fragment.open_exit_successor() != self.exit.block_addr()
        {
            invalid.push("closed loop control differs from composed children".to_string());
        }

        let topology = self.origin.topology();
        let preheader_addr = self.preheader.body().accounting().block_addr();
        let header_addr = self.loop_control.routing().header();
        let body_addr = self.loop_control.routing().body_latch();
        let exit_addr = self.exit.block_addr();
        if topology.entry_addr() != preheader_addr
            || topology.blocks().len() != 4
            || BTreeSet::from([preheader_addr, header_addr, body_addr, exit_addr]).len() != 4
            || topology
                .block(preheader_addr)
                .is_none_or(|block| !block.predecessors().is_empty())
            || topology
                .block(exit_addr)
                .is_none_or(|block| block.predecessors() != [header_addr])
        {
            invalid.push("loop function topology is not exactly closed".to_string());
        }
        if accountings.iter().any(|accounting| {
            !accounting.memory_statements().is_empty()
                || !accounting.direct_calls().is_empty()
                || accounting
                    .expression_layer()
                    .input_origins()
                    .values()
                    .any(|origin| matches!(origin, SemanticCInputOrigin::StackSlot { .. }))
        }) || self
            .origin
            .source()
            .instructions()
            .keys()
            .any(|id| matches!(id.site, CanonicalInstructionSite::Phi(_)))
        {
            invalid.push("memory, call, stack, or phi semantics entered loop subset".to_string());
        }
        let body_accounting = self.loop_fragment.body_latch().body().accounting();
        if body_accounting.mappings().iter().any(|mapping| {
            mapping.obligation().kind != r2ssa::SemanticObligationKind::ControlTransfer
        }) {
            invalid.push("carrier-free loop body is not an empty sealed backedge".to_string());
        }
        if self.origin.source().obligations().keys().any(|id| {
            matches!(
                id.kind,
                r2ssa::SemanticObligationKind::LoopCarriedState
                    | r2ssa::SemanticObligationKind::LiveStateTransition
            )
        }) {
            invalid.push("loop state obligations entered carrier-free subset".to_string());
        }

        let expected_mappings = accountings
            .into_iter()
            .flat_map(CertifiedSingleBlockAccounting::mappings)
            .cloned()
            .collect::<Vec<_>>();
        let counts = counts(
            self.output_seal
                .mappings()
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
        if self.output_seal.mappings() != expected_mappings.as_slice()
            || expected_mappings.len() != expected.len()
            || self.output_seal.mappings().iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::Residualized { .. }
                )
            })
        {
            invalid.push("loop mappings are not disjoint, complete, and closed".to_string());
        }
        if !self.output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::CarrierFreeLoopTerminalReturnFunction,
            CERTIFIED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION,
            accountings,
        ) {
            invalid.push("typed output seal does not match the closed loop".to_string());
        }
        LoopReturnFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, LoopReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_loop_return() {
            return Err(LoopReturnFunctionError::InvalidComposition(report.invalid));
        }
        let interface = self
            .preheader
            .body()
            .accounting()
            .expression_layer()
            .function_interface()
            .ok_or(LoopReturnFunctionError::MissingFunctionInterface)?;
        let condition = self.loop_control.condition().binding();
        let operator = match self.loop_fragment.continuation_arm() {
            LoopContinuationArm::True => "!=",
            LoopContinuationArm::False => "==",
        };
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        output.push('\n');
        write!(&mut output, "{} {}(", return_type(interface)?, self.name)
            .expect("String writes cannot fail");
        render_parameters(&mut output, interface)?;
        output.push_str(") {\n");
        writeln!(
            &mut output,
            "\twhile ((uint8_t){} {operator} UINT8_C(0x0)) {{",
            value_name(condition)
        )
        .expect("String writes cannot fail");
        output.push_str("\t}\n");
        render_return(&mut output, self.exit.value(), "\t", interface)?;
        output.push_str("}\n");
        Ok(output)
    }
}

fn validate_condition(
    accounting: &CertifiedSingleBlockAccounting,
    control: &CertifiedClosedNaturalLoopControl,
) -> Result<(), LoopReturnFunctionError> {
    let interface = accounting
        .expression_layer()
        .function_interface()
        .ok_or(LoopReturnFunctionError::MissingFunctionInterface)?;
    let condition = control.condition();
    if interface.parameters().len() != 1
        || interface
            .parameters()
            .get(control.parameter_index() as usize)
            .filter(|parameter| {
                parameter.index() == control.parameter_index()
                    && parameter.storage() == control.parameter_abi_storage()
                    && parameter.value() == Some(condition.binding())
                    && parameter.ty() == condition.ty()
                    && control.parameter_graph_storage().size.checked_mul(8)
                        == Some(parameter.ty().width_bits())
            })
            .is_none()
        || condition.binding().width_bits() != 8
        || condition.producer().is_some()
        || condition.constant().is_some()
        || condition.memory_access().is_some()
    {
        return Err(LoopReturnFunctionError::InvalidCondition);
    }
    Ok(())
}

fn constant_return_value(
    layer: &SemanticCBlockStepLayer,
    returned: &SemanticCReturn,
) -> Result<LoopReturnValue, LoopReturnFunctionError> {
    match returned.values() {
        [] => Ok(LoopReturnValue::Void),
        [value] => {
            let bits = constant_expression(layer, value.expression(), 0).ok_or(
                LoopReturnFunctionError::NonConstantReturn(layer.accounting().block_addr()),
            )?;
            Ok(LoopReturnValue::Value {
                width_bits: value.binding().width_bits(),
                bits,
            })
        }
        _ => Err(LoopReturnFunctionError::InvalidExit(
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

fn typed_region_mappings(
    accountings: [&CertifiedSingleBlockAccounting; 4],
) -> Vec<TypedRegionMapping> {
    accountings
        .into_iter()
        .flat_map(CertifiedSingleBlockAccounting::mappings)
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
) -> Result<&'static str, LoopReturnFunctionError> {
    Ok(logical_return_type(interface)?)
}

fn render_parameters(
    output: &mut String,
    interface: &SemanticCFunctionInterface,
) -> Result<(), LoopReturnFunctionError> {
    let [parameter] = interface.parameters() else {
        return Err(LoopReturnFunctionError::InvalidCondition);
    };
    let name = parameter
        .value()
        .map(value_name)
        .ok_or(LoopReturnFunctionError::InvalidCondition)?;
    write!(output, "{} {name}", storage_type(parameter.ty())?).expect("String writes cannot fail");
    Ok(())
}

fn render_return(
    output: &mut String,
    value: LoopReturnValue,
    indent: &str,
    interface: &SemanticCFunctionInterface,
) -> Result<(), LoopReturnFunctionError> {
    match (interface.return_kind(), value) {
        (SemanticCFunctionReturn::Void, LoopReturnValue::Void) => {
            writeln!(
                output,
                "{indent}{}",
                render_logical_return_statement(interface, None)?
            )
            .expect("String writes cannot fail");
        }
        (
            SemanticCFunctionReturn::Register { ty, .. },
            LoopReturnValue::Value { width_bits, bits },
        ) if ty.width_bits() == width_bits => {
            let carrier = format!("(({})UINT64_C(0x{bits:x}))", storage_type(ty)?);
            writeln!(
                output,
                "{indent}{}",
                render_logical_return_statement(interface, Some(&carrier))?
            )
            .expect("String writes cannot fail");
        }
        _ => return Err(LoopReturnFunctionError::ReturnTypeMismatch),
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
pub struct LoopReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl LoopReturnFunctionAuditReport {
    pub fn has_exact_loop_return(&self) -> bool {
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
pub struct LoopReturnDifferentialCase {
    condition: u8,
    source: LoopExecutionOutcome,
    certified: LoopExecutionOutcome,
    rendered: LoopExecutionOutcome,
}

impl LoopReturnDifferentialCase {
    pub const fn condition(&self) -> u8 {
        self.condition
    }

    pub const fn source(&self) -> LoopExecutionOutcome {
        self.source
    }

    pub const fn certified(&self) -> LoopExecutionOutcome {
        self.certified
    }

    pub const fn rendered(&self) -> LoopExecutionOutcome {
        self.rendered
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LoopReturnDifferentialReport {
    cases: Box<[LoopReturnDifferentialCase]>,
}

impl LoopReturnDifferentialReport {
    pub const fn cases(&self) -> &[LoopReturnDifferentialCase] {
        &self.cases
    }

    pub fn all_match(&self) -> bool {
        self.cases
            .iter()
            .all(|case| case.source == case.certified && case.source == case.rendered)
    }
}

/// Bounded independent check over zero/nonzero ABI conditions. The report
/// explicitly distinguishes a terminal exit from a loop still traversing its
/// backedge when the bound is exhausted.
pub fn check_loop_return_differential(
    trusted: &TrustedSsaArtifact,
    max_iterations: u32,
) -> Result<LoopReturnDifferentialReport, String> {
    if max_iterations == 0 {
        return Err("loop differential iteration budget is zero".to_string());
    }
    let function = CertifiedLoopReturnFunction::from_artifact(trusted)
        .map_err(|error| format!("loop candidate not admitted: {error}"))?;
    let artifact = trusted.artifact();
    let rendered = function
        .render_certified_c()
        .map_err(|error| format!("loop rendering failed: {error}"))?;
    let rendered_continue_on_true = parse_rendered_polarity(&rendered)?;
    let rendered_return = parse_rendered_return(&rendered)?;
    let source_continue_on_true = source_continue_on_true(artifact, &function)?;
    let source_return = source_return_value(artifact, function.exit.block_addr())?;
    let certified_continue_on_true = function.loop_control.routing().continuation_on_true();
    let mut cases = Vec::with_capacity(2);
    for condition in [0_u8, 1_u8] {
        let source = execute_invariant_loop(
            condition,
            source_continue_on_true,
            source_return,
            max_iterations,
        );
        let certified = execute_invariant_loop(
            condition,
            certified_continue_on_true,
            function.exit.value,
            max_iterations,
        );
        let rendered = execute_invariant_loop(
            condition,
            rendered_continue_on_true,
            rendered_return,
            max_iterations,
        );
        cases.push(LoopReturnDifferentialCase {
            condition,
            source,
            certified,
            rendered,
        });
    }
    let report = LoopReturnDifferentialReport {
        cases: cases.into_boxed_slice(),
    };
    if !report.all_match() {
        return Err("loop differential mismatch".to_string());
    }
    Ok(report)
}

fn execute_invariant_loop(
    condition: u8,
    continue_on_true: bool,
    returned: LoopReturnValue,
    max_iterations: u32,
) -> LoopExecutionOutcome {
    let continues = (condition != 0) == continue_on_true;
    if continues {
        LoopExecutionOutcome::BoundedNontermination {
            iterations: max_iterations,
        }
    } else {
        LoopExecutionOutcome::Returned(returned)
    }
}

fn source_continue_on_true(
    artifact: &SsaArtifact,
    function: &CertifiedLoopReturnFunction,
) -> Result<bool, String> {
    let header_addr = function.loop_control.routing().header();
    let body_addr = function.loop_control.routing().body_latch();
    let exit_addr = function.loop_control.routing().exit();
    let header = artifact
        .function()
        .cfg()
        .get_block(header_addr)
        .ok_or_else(|| "source loop header is missing".to_string())?;
    let BlockTerminator::ConditionalBranch {
        true_target,
        false_target,
    } = &header.terminator
    else {
        return Err("source loop header is not conditional".to_string());
    };
    if *true_target == body_addr && *false_target == exit_addr {
        Ok(true)
    } else if *true_target == exit_addr && *false_target == body_addr {
        Ok(false)
    } else {
        Err("source loop polarity is not exact".to_string())
    }
}

fn source_return_value(artifact: &SsaArtifact, block_addr: u64) -> Result<LoopReturnValue, String> {
    let returns = artifact
        .certificates()
        .returns
        .iter()
        .filter(|returned| returned.block_addr == block_addr)
        .collect::<Vec<_>>();
    match returns.as_slice() {
        [] => Ok(LoopReturnValue::Void),
        [returned] => {
            let value = artifact
                .graph()
                .value(returned.value)
                .ok_or_else(|| "source loop return value is missing".to_string())?;
            let bits = value.var.constant_bits().or_else(|| {
                artifact
                    .graph()
                    .def_inst(returned.value)
                    .and_then(|instruction| artifact.graph().inst(instruction))
                    .and_then(|instruction| instruction.inputs.first())
                    .and_then(|input| artifact.graph().value(*input))
                    .and_then(|input| input.var.constant_bits())
            });
            Ok(LoopReturnValue::Value {
                width_bits: value.var.size.saturating_mul(8),
                bits: bits.ok_or_else(|| {
                    "source loop return is not independently constant".to_string()
                })?,
            })
        }
        _ => Err("source loop exit has ambiguous return certificates".to_string()),
    }
}

fn parse_rendered_polarity(rendered: &str) -> Result<bool, String> {
    let lines = rendered
        .lines()
        .filter(|line| line.starts_with("\twhile ("))
        .collect::<Vec<_>>();
    let [line] = lines.as_slice() else {
        return Err("rendered loop has missing or ambiguous while".to_string());
    };
    if line.starts_with("\twhile ((uint8_t)v_") && line.ends_with(" != UINT8_C(0x0)) {") {
        Ok(true)
    } else if line.starts_with("\twhile ((uint8_t)v_") && line.ends_with(" == UINT8_C(0x0)) {") {
        Ok(false)
    } else {
        Err("rendered loop condition is malformed".to_string())
    }
}

fn parse_rendered_return(rendered: &str) -> Result<LoopReturnValue, String> {
    let returns = rendered
        .lines()
        .filter(|line| line.starts_with("\treturn"))
        .collect::<Vec<_>>();
    let [line] = returns.as_slice() else {
        return Err("rendered loop return is missing or ambiguous".to_string());
    };
    if *line == "\treturn;" {
        return Ok(LoopReturnValue::Void);
    }
    let (ty, bits) = line
        .strip_prefix("\treturn ((")
        .and_then(|line| line.strip_suffix("));"))
        .and_then(|line| line.split_once(")UINT64_C(0x"))
        .ok_or_else(|| "rendered loop return is malformed".to_string())?;
    let width_bits = match ty {
        "uint8_t" => 8,
        "uint16_t" => 16,
        "uint32_t" => 32,
        "uint64_t" => 64,
        _ => return Err("rendered loop return type is unsupported".to_string()),
    };
    Ok(LoopReturnValue::Value {
        width_bits,
        bits: u64::from_str_radix(bits, 16)
            .map_err(|_| "rendered loop return constant is malformed".to_string())?,
    })
}
