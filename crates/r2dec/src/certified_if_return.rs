//! Closed semantic-C composition for one exact conditional with two returns.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_CONDITIONAL_TERMINAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedLedgerClosure, CertifiedMachineProjection, CertifiedSourceTerminator,
    CertifiedTypedRegionKind, LedgerClosureError, TypedRegionMapping,
    certify_conditional_terminal_return_region,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalInstructionSite, MachineBuildError, MachineValueBinding,
    SemanticObligationId, TrustedSsaArtifact,
};
use serde::Serialize;

use crate::certified_control::{
    CertifiedConditionalTransferBlockRegion, ConditionalTransferRegionError,
};
use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionBuildError,
    RegionObligationMapping, TypedOutputSealError,
};
use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCFunctionInterface, SemanticCFunctionReturn,
    SemanticCInputOrigin, SemanticCReturn, logical_return_type, render_logical_return_statement,
    storage_type, value_name,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_CONDITIONAL_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_CONDITIONAL_TERMINAL_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ConditionalReturnFunctionScope {
    ClosedThreeBlockConditionalWithTerminalReturns,
}

/// One terminal-return child. It has no render permit of its own; only the
/// closed parent can authorize executable C for the complete source inventory.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalReturnArm {
    layer: SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
}

impl CertifiedConditionalReturnArm {
    fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, ConditionalReturnFunctionError> {
        let report = accounting.audit();
        if !report.has_exact_source_accounting() || report.has_residuals() {
            return Err(ConditionalReturnFunctionError::InvalidReturnArm(
                accounting.block_addr(),
            ));
        }
        let Some(block) = accounting.source_block() else {
            return Err(ConditionalReturnFunctionError::InvalidReturnArm(
                accounting.block_addr(),
            ));
        };
        let [returned] = accounting.semantic_returns() else {
            return Err(ConditionalReturnFunctionError::InvalidReturnArm(
                accounting.block_addr(),
            ));
        };
        if accounting.return_controls().len() != 1
            || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || block.instructions().last() != Some(&returned.producer())
            || !accounting.memory_statements().is_empty()
            || !accounting.direct_calls().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            return Err(ConditionalReturnFunctionError::InvalidReturnArm(
                accounting.block_addr(),
            ));
        }
        let return_producer = returned.producer();
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let arm = Self {
            layer,
            return_producer,
        };
        if !arm.has_exact_terminal_return() {
            return Err(ConditionalReturnFunctionError::InvalidReturnArm(
                arm.block_addr(),
            ));
        }
        Ok(arm)
    }

    pub const fn layer(&self) -> &SemanticCBlockStepLayer {
        &self.layer
    }

    pub const fn return_producer(&self) -> CanonicalInstructionId {
        self.return_producer
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
        let Some(interface) = accounting.expression_layer().function_interface() else {
            return false;
        };
        let [returned] = accounting.semantic_returns() else {
            return false;
        };
        let return_matches = match (interface.return_kind(), returned.values()) {
            (SemanticCFunctionReturn::Void, []) => true,
            (SemanticCFunctionReturn::Register { storage, ty }, [value]) => {
                value.slot()
                    == r2ssa::CallBoundarySlot::Register {
                        index: 0,
                        storage: *storage,
                    }
                    && accounting
                        .expression_layer()
                        .expr_type(value.expression())
                        .is_ok_and(|actual| actual == ty)
                    && self.return_value_precedes_terminator(value.binding())
            }
            _ => false,
        };
        self.layer.audit().has_exact_source_order()
            && accounting.audit().has_exact_source_accounting()
            && !accounting.audit().has_residuals()
            && matches!(block.terminator(), CertifiedSourceTerminator::Return)
            && block.successors().is_empty()
            && block.instructions().last() == Some(&self.return_producer)
            && self.layer.steps().last().map(|step| step.source()) == Some(self.return_producer)
            && accounting.return_controls().len() == 1
            && returned.producer() == self.return_producer
            && accounting.memory_statements().is_empty()
            && accounting.direct_calls().is_empty()
            && accounting.direct_controls().is_empty()
            && accounting.conditional_controls().is_empty()
            && return_matches
    }

    fn return_value_precedes_terminator(&self, binding: MachineValueBinding) -> bool {
        let return_position = self
            .layer
            .steps()
            .iter()
            .position(|step| step.source() == self.return_producer);
        let value_position = self.layer.steps().iter().position(|step| {
            step.value().is_some_and(|reference| {
                self.layer
                    .resolve_value(reference)
                    .is_some_and(|entity| entity.output() == binding)
            })
        });
        matches!((value_position, return_position), (Some(value), Some(ret)) if value < ret)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalReturnFunction {
    schema_version: u32,
    scope: ConditionalReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    header: CertifiedConditionalTransferBlockRegion,
    true_arm: CertifiedConditionalReturnArm,
    false_arm: CertifiedConditionalReturnArm,
    true_addr: u64,
    false_addr: u64,
    mappings: Box<[RegionObligationMapping]>,
    typed_output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConditionalReturnFunctionError {
    Machine(MachineBuildError),
    Accounting(RegionBuildError),
    Conditional(ConditionalTransferRegionError),
    Statement(SemanticCStatementError),
    LedgerClosure(LedgerClosureError),
    TypedOutputSeal(TypedOutputSealError),
    InvalidReturnArm(u64),
    InvalidComposition(Vec<String>),
    MissingFunctionInterface,
    UnsupportedInput,
    MissingCondition,
    MissingReturnedEntity,
    SemanticC(SemanticCError),
}

impl std::fmt::Display for ConditionalReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "conditional return function failed: {self:?}")
    }
}

impl std::error::Error for ConditionalReturnFunctionError {}

impl From<MachineBuildError> for ConditionalReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for ConditionalReturnFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<ConditionalTransferRegionError> for ConditionalReturnFunctionError {
    fn from(error: ConditionalTransferRegionError) -> Self {
        Self::Conditional(error)
    }
}

impl From<SemanticCStatementError> for ConditionalReturnFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<LedgerClosureError> for ConditionalReturnFunctionError {
    fn from(error: LedgerClosureError) -> Self {
        Self::LedgerClosure(error)
    }
}

impl From<TypedOutputSealError> for ConditionalReturnFunctionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
    }
}

impl From<SemanticCError> for ConditionalReturnFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn typed_region_mappings(
    accountings: [&CertifiedSingleBlockAccounting; 3],
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

impl CertifiedConditionalReturnFunction {
    pub fn from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, ConditionalReturnFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(trusted)?;
        Self::from_projection(&certified)
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, ConditionalReturnFunctionError> {
        let header_addr = certified.topology().entry_addr();
        let header_block = certified
            .topology()
            .block(header_addr)
            .ok_or_else(|| ConditionalReturnFunctionError::InvalidComposition(Vec::new()))?;
        let (true_addr, false_addr) = match header_block.terminator() {
            CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => (*true_target, *false_target),
            _ => {
                return Err(ConditionalReturnFunctionError::InvalidComposition(vec![
                    "entry is not a conditional transfer".to_string(),
                ]));
            }
        };
        let header = CertifiedConditionalTransferBlockRegion::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, header_addr)?,
        )?;
        let true_arm = CertifiedConditionalReturnArm::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, true_addr)?,
        )?;
        let false_arm = CertifiedConditionalReturnArm::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, false_addr)?,
        )?;
        let mappings = header
            .mappings()
            .iter()
            .chain(true_arm.layer().accounting().mappings())
            .chain(false_arm.layer().accounting().mappings())
            .cloned()
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let typed_mappings = typed_region_mappings([
            header.body().accounting(),
            true_arm.layer().accounting(),
            false_arm.layer().accounting(),
        ]);
        let ledger_closure: CertifiedLedgerClosure = certify_conditional_terminal_return_region(
            certified.origin(),
            certified.ledger(),
            typed_mappings,
            header_addr,
            true_addr,
            false_addr,
        )?;
        let typed_output_seal = CertifiedTypedOutputSeal::new(
            ledger_closure,
            CertifiedTypedRegionKind::ConditionalTerminalReturnFunction,
            CERTIFIED_CONDITIONAL_RETURN_FUNCTION_SCHEMA_VERSION,
            [
                header.body().accounting(),
                true_arm.layer().accounting(),
                false_arm.layer().accounting(),
            ],
        )?;
        let function = Self {
            schema_version: CERTIFIED_CONDITIONAL_RETURN_FUNCTION_SCHEMA_VERSION,
            scope: ConditionalReturnFunctionScope::ClosedThreeBlockConditionalWithTerminalReturns,
            name: format!("certified_sub_{header_addr:x}"),
            origin: certified.origin().clone(),
            header,
            true_arm,
            false_arm,
            true_addr,
            false_addr,
            mappings,
            typed_output_seal,
        };
        let report = function.audit();
        if !report.has_exact_conditional_returns() {
            return Err(ConditionalReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> ConditionalReturnFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn header(&self) -> &CertifiedConditionalTransferBlockRegion {
        &self.header
    }

    pub const fn true_arm(&self) -> &CertifiedConditionalReturnArm {
        &self.true_arm
    }

    pub const fn false_arm(&self) -> &CertifiedConditionalReturnArm {
        &self.false_arm
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub fn audit(&self) -> ConditionalReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        let header_accounting = self.header.body().accounting();
        let true_accounting = self.true_arm.layer().accounting();
        let false_accounting = self.false_arm.layer().accounting();
        if self.schema_version != CERTIFIED_CONDITIONAL_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("conditional-return schema mismatch".to_string());
        }
        if self.scope
            != ConditionalReturnFunctionScope::ClosedThreeBlockConditionalWithTerminalReturns
        {
            invalid.push("conditional-return scope mismatch".to_string());
        }
        if self.origin != *header_accounting.origin()
            || self.origin != *true_accounting.origin()
            || self.origin != *false_accounting.origin()
        {
            invalid.push("children do not share one exact artifact origin".to_string());
        }
        let interfaces = [
            header_accounting.expression_layer().function_interface(),
            true_accounting.expression_layer().function_interface(),
            false_accounting.expression_layer().function_interface(),
        ];
        if interfaces[0].is_none()
            || interfaces[0] != interfaces[1]
            || interfaces[0] != interfaces[2]
        {
            invalid.push("children do not share one exact function interface revision".to_string());
        }
        if !self
            .header
            .audit()
            .has_exact_conditional_transfer_accounting()
            || self.header.has_remaining_obligation_residuals()
            || !self.true_arm.has_exact_terminal_return()
            || !self.false_arm.has_exact_terminal_return()
        {
            invalid.push("nested conditional or terminal-return region is not exact".to_string());
        }
        let topology = self.origin.topology();
        let header_addr = header_accounting.block_addr();
        let selected = BTreeSet::from([header_addr, self.true_addr, self.false_addr]);
        if topology.entry_addr() != header_addr
            || topology.blocks().len() != 3
            || selected.len() != 3
            || self.header.open_true_successor() != self.true_addr
            || self.header.open_false_successor() != self.false_addr
            || self.true_arm.block_addr() != self.true_addr
            || self.false_arm.block_addr() != self.false_addr
            || topology
                .block(header_addr)
                .is_none_or(|block| !block.predecessors().is_empty())
            || topology
                .block(self.true_addr)
                .is_none_or(|block| block.predecessors() != [header_addr])
            || topology
                .block(self.false_addr)
                .is_none_or(|block| block.predecessors() != [header_addr])
        {
            invalid.push("closed topology or true/false edge polarity mismatch".to_string());
        }
        if [
            self.header.body(),
            self.true_arm.layer(),
            self.false_arm.layer(),
        ]
        .into_iter()
        .any(|layer| {
            !layer.accounting().memory_statements().is_empty()
                || !layer.accounting().direct_calls().is_empty()
                || layer
                    .accounting()
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
            invalid.push("memory, call, stack, or phi semantics entered closed subset".to_string());
        }

        let expected_mappings = self
            .header
            .mappings()
            .iter()
            .chain(true_accounting.mappings())
            .chain(false_accounting.mappings())
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
        {
            invalid.push("combined mappings are not disjoint and complete".to_string());
        }
        if !self.typed_output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::ConditionalTerminalReturnFunction,
            CERTIFIED_CONDITIONAL_RETURN_FUNCTION_SCHEMA_VERSION,
            [header_accounting, true_accounting, false_accounting],
        ) {
            invalid.push("typed-output seal does not match the closed composition".to_string());
        }
        ConditionalReturnFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, ConditionalReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_conditional_returns() {
            return Err(ConditionalReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let interface = self
            .header
            .body()
            .accounting()
            .expression_layer()
            .function_interface()
            .ok_or(ConditionalReturnFunctionError::MissingFunctionInterface)?;
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        write!(&mut output, "\n{} {}(", return_type(interface)?, self.name)
            .expect("String writes cannot fail");
        render_parameters(&mut output, interface)?;
        output.push_str(") {\n");
        for parameter in interface.parameters() {
            let name = parameter
                .value()
                .map(value_name)
                .unwrap_or_else(|| format!("arg_{}", parameter.index()));
            writeln!(&mut output, "\t(void){name};").expect("String writes cannot fail");
        }
        render_value_steps(&mut output, self.header.body(), "\t")?;
        let condition = render_condition(self)?;
        writeln!(
            &mut output,
            "\tif ((uint8_t)({condition}) != UINT8_C(0)) {{"
        )
        .expect("String writes cannot fail");
        render_return_arm(&mut output, &self.true_arm, "\t\t", interface)?;
        output.push_str("\t} else {\n");
        render_return_arm(&mut output, &self.false_arm, "\t\t", interface)?;
        output.push_str("\t}\n}\n");
        Ok(output)
    }
}

fn return_type(
    interface: &SemanticCFunctionInterface,
) -> Result<&'static str, ConditionalReturnFunctionError> {
    Ok(logical_return_type(interface)?)
}

fn render_parameters(
    output: &mut String,
    interface: &SemanticCFunctionInterface,
) -> Result<(), ConditionalReturnFunctionError> {
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

fn render_value_steps(
    output: &mut String,
    layer: &SemanticCBlockStepLayer,
    indent: &str,
) -> Result<(), ConditionalReturnFunctionError> {
    let expressions = layer.accounting().expression_layer();
    for step in layer.steps() {
        let Some(reference) = step.value() else {
            continue;
        };
        let entity = layer
            .resolve_value(reference)
            .ok_or(ConditionalReturnFunctionError::MissingReturnedEntity)?;
        writeln!(
            output,
            "{indent}{} {} = {};",
            storage_type(expressions.expr_type(entity.root())?)?,
            value_name(entity.output()),
            expressions.render_expr(entity.root())?
        )
        .expect("String writes cannot fail");
        writeln!(output, "{indent}(void){};", value_name(entity.output()))
            .expect("String writes cannot fail");
    }
    Ok(())
}

fn render_condition(
    function: &CertifiedConditionalReturnFunction,
) -> Result<String, ConditionalReturnFunctionError> {
    let condition = function.header.transfer().condition();
    if let Some(value) = condition.constant() {
        return Ok(format!("((uint8_t)UINT64_C(0x{:x}))", value.bits()));
    }
    let binding = condition.binding();
    let expressions = function.header.body().accounting().expression_layer();
    let produced = function.header.body().steps().iter().any(|step| {
        step.value().is_some_and(|reference| {
            function
                .header
                .body()
                .resolve_value(reference)
                .is_some_and(|entity| entity.output() == binding)
        })
    });
    let abi_input = expressions
        .input_origins()
        .get(&binding)
        .is_some_and(|origin| matches!(origin, SemanticCInputOrigin::AbiParameter { .. }));
    if binding.width_bits() == 8 && (produced || abi_input) {
        Ok(value_name(binding))
    } else {
        Err(ConditionalReturnFunctionError::MissingCondition)
    }
}

fn render_return_arm(
    output: &mut String,
    arm: &CertifiedConditionalReturnArm,
    indent: &str,
    interface: &SemanticCFunctionInterface,
) -> Result<(), ConditionalReturnFunctionError> {
    render_value_steps(output, arm.layer(), indent)?;
    let returned = arm
        .returned()
        .ok_or(ConditionalReturnFunctionError::MissingReturnedEntity)?;
    match returned.values() {
        [] => writeln!(
            output,
            "{indent}{}",
            render_logical_return_statement(interface, None)?
        )
        .expect("String writes cannot fail"),
        [value] => writeln!(
            output,
            "{indent}{}",
            render_logical_return_statement(interface, Some(&value_name(value.binding())))?
        )
        .expect("String writes cannot fail"),
        _ => return Err(ConditionalReturnFunctionError::MissingReturnedEntity),
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
pub struct ConditionalReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl ConditionalReturnFunctionAuditReport {
    pub fn has_exact_conditional_returns(&self) -> bool {
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
