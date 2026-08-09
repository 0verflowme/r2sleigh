//! Closed semantic-C composition for one void direct call followed by return.
//!
//! The source representation uses two canonical blocks: the call is the entry
//! block terminator and its sole fallthrough is a terminal-return block. The
//! callee is reached through a call-site-specific external adapter. This keeps
//! the call side effect explicit without claiming to model callee behavior.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_DIRECT_CALL_TERMINAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedLedgerClosure, CertifiedMachineProjection, CertifiedSourceTerminator,
    CertifiedTypedRegionKind, LedgerClosureError, TypedRegionMapping,
    certify_direct_call_terminal_return_region,
};
use r2ssa::{
    CallBoundarySlot, CanonicalInstructionId, CanonicalInstructionSite, MachineBuildError,
    MachineType, MachineValueBinding, SemanticObligationId, SsaArtifact,
};
use serde::Serialize;

use crate::certified_call::{CertifiedDirectCallBlockRegion, DirectCallRegionError};
use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionBuildError,
    RegionObligationMapping, TypedOutputSealError,
};
use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCCallArgumentValue, SemanticCError, SemanticCExprKind,
    SemanticCFunctionInterface, SemanticCFunctionReturn, SemanticCInputOrigin, SemanticCReturn,
    storage_type, value_name,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_DIRECT_CALL_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_DIRECT_CALL_TERMINAL_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum DirectCallReturnFunctionScope {
    ClosedTwoBlockVoidDirectCallThenTerminalReturn,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DirectCallArgumentManifest {
    slot: CallBoundarySlot,
    binding: MachineValueBinding,
    ty: MachineType,
}

impl DirectCallArgumentManifest {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn ty(&self) -> &MachineType {
        &self.ty
    }
}

/// Terminal-return child with no independent whole-function authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDirectCallReturnBlock {
    layer: SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
}

impl CertifiedDirectCallReturnBlock {
    fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, DirectCallReturnFunctionError> {
        let report = accounting.audit();
        let Some(block) = accounting.source_block() else {
            return Err(DirectCallReturnFunctionError::InvalidReturnBlock(
                accounting.block_addr(),
            ));
        };
        let [returned] = accounting.semantic_returns() else {
            return Err(DirectCallReturnFunctionError::InvalidReturnBlock(
                accounting.block_addr(),
            ));
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
        {
            return Err(DirectCallReturnFunctionError::InvalidReturnBlock(
                accounting.block_addr(),
            ));
        }
        let return_producer = returned.producer();
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let returned = Self {
            layer,
            return_producer,
        };
        if !returned.has_exact_terminal_return() {
            return Err(DirectCallReturnFunctionError::InvalidReturnBlock(
                returned.block_addr(),
            ));
        }
        Ok(returned)
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
                    == (CallBoundarySlot::Register {
                        index: 0,
                        storage: *storage,
                    })
                    && accounting
                        .expression_layer()
                        .expr_type(value.expression())
                        .is_ok_and(|actual| actual == ty)
                    && value_precedes(&self.layer, value.binding(), self.return_producer)
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
}

/// Complete proof-bearing function for the narrow direct-call/return subset.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDirectCallReturnFunction {
    schema_version: u32,
    scope: DirectCallReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    call_block: CertifiedDirectCallBlockRegion,
    return_block: CertifiedDirectCallReturnBlock,
    return_addr: u64,
    call_target: u64,
    call_interface_revision: Box<[u8]>,
    calling_convention: String,
    arguments: Box<[DirectCallArgumentManifest]>,
    mappings: Box<[RegionObligationMapping]>,
    typed_output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DirectCallReturnFunctionError {
    Machine(MachineBuildError),
    Accounting(RegionBuildError),
    Call(DirectCallRegionError),
    Statement(SemanticCStatementError),
    LedgerClosure(LedgerClosureError),
    TypedOutputSeal(TypedOutputSealError),
    InvalidTopology,
    InvalidReturnBlock(u64),
    MissingFunctionInterface,
    UnsupportedInput,
    InvalidComposition(Vec<String>),
    MissingValue(CanonicalInstructionId),
    SemanticC(SemanticCError),
}

impl std::fmt::Display for DirectCallReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "direct-call return function failed: {self:?}")
    }
}

impl std::error::Error for DirectCallReturnFunctionError {}

impl From<MachineBuildError> for DirectCallReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for DirectCallReturnFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<DirectCallRegionError> for DirectCallReturnFunctionError {
    fn from(error: DirectCallRegionError) -> Self {
        Self::Call(error)
    }
}

impl From<SemanticCStatementError> for DirectCallReturnFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<LedgerClosureError> for DirectCallReturnFunctionError {
    fn from(error: LedgerClosureError) -> Self {
        Self::LedgerClosure(error)
    }
}

impl From<TypedOutputSealError> for DirectCallReturnFunctionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
    }
}

impl From<SemanticCError> for DirectCallReturnFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn typed_region_mappings(
    accountings: [&CertifiedSingleBlockAccounting; 2],
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

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

fn value_precedes(
    layer: &SemanticCBlockStepLayer,
    binding: MachineValueBinding,
    boundary: CanonicalInstructionId,
) -> bool {
    let boundary_position = layer
        .steps()
        .iter()
        .position(|step| step.source() == boundary);
    let value_position = layer.steps().iter().position(|step| {
        step.value().is_some_and(|reference| {
            layer
                .resolve_value(reference)
                .is_some_and(|entity| entity.output() == binding)
        })
    });
    matches!((value_position, boundary_position), (Some(value), Some(end)) if value < end)
}

impl CertifiedDirectCallReturnFunction {
    /// Build the complete proof chain from one immutable source artifact.
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, DirectCallReturnFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(artifact)?;
        Self::from_projection(&certified)
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, DirectCallReturnFunctionError> {
        let entry_addr = certified.topology().entry_addr();
        let entry = certified
            .topology()
            .block(entry_addr)
            .ok_or(DirectCallReturnFunctionError::InvalidTopology)?;
        let return_addr = match entry.terminator() {
            CertifiedSourceTerminator::Call {
                fallthrough: Some(fallthrough),
                ..
            } => *fallthrough,
            _ => return Err(DirectCallReturnFunctionError::InvalidTopology),
        };
        let call_block = CertifiedDirectCallBlockRegion::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, entry_addr)?,
        )?;
        let return_block = CertifiedDirectCallReturnBlock::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, return_addr)?,
        )?;
        let call_target = call_block.call().target();
        let call_interface_revision = call_block.call().interface_revision().to_vec();
        let calling_convention = call_block.call().calling_convention().to_string();
        let arguments = call_block
            .call()
            .arguments()
            .iter()
            .map(|argument| DirectCallArgumentManifest {
                slot: argument.slot(),
                binding: argument.binding(),
                ty: argument.ty().clone(),
            })
            .collect::<Vec<_>>();
        let mappings = call_block
            .mappings()
            .iter()
            .chain(return_block.layer().accounting().mappings())
            .cloned()
            .collect::<Vec<_>>();
        let typed_mappings = typed_region_mappings([
            call_block.body().accounting(),
            return_block.layer().accounting(),
        ]);
        let ledger_closure: CertifiedLedgerClosure = certify_direct_call_terminal_return_region(
            certified.origin(),
            certified.ledger(),
            typed_mappings,
            entry_addr,
            return_addr,
        )?;
        let typed_output_seal = CertifiedTypedOutputSeal::new(
            ledger_closure,
            CertifiedTypedRegionKind::DirectCallTerminalReturnFunction,
            CERTIFIED_DIRECT_CALL_RETURN_FUNCTION_SCHEMA_VERSION,
            [
                call_block.body().accounting(),
                return_block.layer().accounting(),
            ],
        )?;
        let function = Self {
            schema_version: CERTIFIED_DIRECT_CALL_RETURN_FUNCTION_SCHEMA_VERSION,
            scope: DirectCallReturnFunctionScope::ClosedTwoBlockVoidDirectCallThenTerminalReturn,
            name: format!("certified_call_sub_{entry_addr:x}"),
            origin: certified.origin().clone(),
            call_block,
            return_block,
            return_addr,
            call_target,
            call_interface_revision: call_interface_revision.into_boxed_slice(),
            calling_convention,
            arguments: arguments.into_boxed_slice(),
            mappings: mappings.into_boxed_slice(),
            typed_output_seal,
        };
        let report = function.audit();
        if !report.has_exact_direct_call_return() {
            return Err(DirectCallReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        function.render_body()?;
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> DirectCallReturnFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn call_block(&self) -> &CertifiedDirectCallBlockRegion {
        &self.call_block
    }

    pub const fn return_block(&self) -> &CertifiedDirectCallReturnBlock {
        &self.return_block
    }

    pub const fn call_target(&self) -> u64 {
        self.call_target
    }

    pub const fn arguments(&self) -> &[DirectCallArgumentManifest] {
        &self.arguments
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub fn call_adapter_name(&self) -> String {
        let identity = self.call_block.raw_identity();
        format!(
            "r2s_call_{:016x}_at_{:016x}_{}",
            self.call_target,
            identity.block_addr(),
            identity.op_index()
        )
    }

    pub fn audit(&self) -> DirectCallReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        let call_accounting = self.call_block.body().accounting();
        let return_accounting = self.return_block.layer().accounting();
        if self.schema_version != CERTIFIED_DIRECT_CALL_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("direct-call return schema mismatch".to_string());
        }
        if self.scope
            != DirectCallReturnFunctionScope::ClosedTwoBlockVoidDirectCallThenTerminalReturn
        {
            invalid.push("direct-call return scope mismatch".to_string());
        }
        if self.name != format!("certified_call_sub_{:x}", call_accounting.block_addr()) {
            invalid.push("direct-call return function name differs from source entry".to_string());
        }
        if self.origin != *call_accounting.origin() || self.origin != *return_accounting.origin() {
            invalid.push("children do not share one exact artifact origin".to_string());
        }
        let interfaces = [
            call_accounting.expression_layer().function_interface(),
            return_accounting.expression_layer().function_interface(),
        ];
        if interfaces[0].is_none()
            || interfaces[0] != interfaces[1]
            || interfaces[0].is_some_and(|interface| !interface.stack_slots().is_empty())
        {
            invalid.push("children do not share one exact function interface".to_string());
        }
        if !self.call_block.audit().has_exact_direct_call()
            || self.call_block.has_remaining_obligation_residuals()
            || !self.return_block.has_exact_terminal_return()
            || !return_is_call_independent(&self.return_block)
        {
            invalid.push("nested call or call-independent return block is not exact".to_string());
        }
        let entry_addr = call_accounting.block_addr();
        let topology = self.origin.topology();
        if topology.entry_addr() != entry_addr
            || topology.blocks().len() != 2
            || self.return_addr == entry_addr
            || self.call_block.open_fallthrough_successor() != self.return_addr
            || self.return_block.block_addr() != self.return_addr
            || topology
                .block(entry_addr)
                .is_none_or(|block| !block.predecessors().is_empty())
            || topology
                .block(self.return_addr)
                .is_none_or(|block| block.predecessors() != [entry_addr])
        {
            invalid.push("closed two-block call/fallthrough/return topology mismatch".to_string());
        }
        if [self.call_block.body(), self.return_block.layer()]
            .into_iter()
            .any(|layer| {
                !layer.accounting().memory_statements().is_empty()
                    || !layer.accounting().direct_controls().is_empty()
                    || !layer.accounting().conditional_controls().is_empty()
                    || layer
                        .accounting()
                        .expression_layer()
                        .input_origins()
                        .values()
                        .any(|origin| {
                            matches!(
                                origin,
                                SemanticCInputOrigin::StackSlot { .. }
                                    | SemanticCInputOrigin::UnclassifiedSource
                            )
                        })
            })
            || self
                .origin
                .source()
                .instructions()
                .keys()
                .any(|id| matches!(id.site, CanonicalInstructionSite::Phi(_)))
        {
            invalid.push(
                "memory, control, stack, unclassified, or phi semantics entered subset".to_string(),
            );
        }

        let call = self.call_block.call();
        let actual_arguments = call
            .arguments()
            .iter()
            .map(|argument| DirectCallArgumentManifest {
                slot: argument.slot(),
                binding: argument.binding(),
                ty: argument.ty().clone(),
            })
            .collect::<Vec<_>>();
        if self.call_target != call.target()
            || self.call_interface_revision.as_ref() != call.interface_revision()
            || self.calling_convention != call.calling_convention()
            || self.arguments.as_ref() != actual_arguments.as_slice()
            || !call_arguments_renderable(&self.call_block)
        {
            invalid
                .push("call target, interface, or ordered argument manifest mismatch".to_string());
        }

        let expected_mappings = self
            .call_block
            .mappings()
            .iter()
            .chain(return_accounting.mappings())
            .cloned()
            .collect::<Vec<_>>();
        let mapping_counts = counts(
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
        let actual = mapping_counts.keys().copied().collect::<BTreeSet<_>>();
        let missing = expected.difference(&actual).copied().collect();
        let unexpected = actual.difference(&expected).copied().collect();
        let duplicate = mapping_counts
            .iter()
            .filter_map(|(id, count)| (*count > 1).then_some(*id))
            .collect();
        if self.mappings.as_ref() != expected_mappings.as_slice()
            || expected_mappings.len() != expected.len()
        {
            invalid.push("combined obligation mappings are not disjoint and complete".to_string());
        }
        if !self.typed_output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::DirectCallTerminalReturnFunction,
            CERTIFIED_DIRECT_CALL_RETURN_FUNCTION_SCHEMA_VERSION,
            [call_accounting, return_accounting],
        ) {
            invalid.push(
                "typed-output seal does not match closed call/return composition".to_string(),
            );
        }
        DirectCallReturnFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    /// Render strict C11. The external adapter name is source-call-site
    /// specific, and the adapter prototype retains the certified argument
    /// order and widths.
    pub fn render_certified_c(&self) -> Result<String, DirectCallReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_direct_call_return() {
            return Err(DirectCallReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        self.render_body()
    }

    fn render_body(&self) -> Result<String, DirectCallReturnFunctionError> {
        let interface = self
            .call_block
            .body()
            .accounting()
            .expression_layer()
            .function_interface()
            .ok_or(DirectCallReturnFunctionError::MissingFunctionInterface)?;
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        write!(&mut output, "\nextern void {}(", self.call_adapter_name())
            .expect("String writes cannot fail");
        render_call_parameter_types(&mut output, self.call_block.call())?;
        output.push_str(");\n\n");
        write!(&mut output, "{} {}(", return_type(interface)?, self.name)
            .expect("String writes cannot fail");
        render_function_parameters(&mut output, interface)?;
        output.push_str(") {\n");
        for parameter in interface.parameters() {
            let name = parameter
                .value()
                .map(value_name)
                .unwrap_or_else(|| format!("arg_{}", parameter.index()));
            writeln!(&mut output, "\t(void){name};").expect("String writes cannot fail");
        }
        render_value_steps(&mut output, self.call_block.body())?;
        write!(&mut output, "\t{}(", self.call_adapter_name()).expect("String writes cannot fail");
        for (position, argument) in self.call_block.call().arguments().iter().enumerate() {
            if position > 0 {
                output.push_str(", ");
            }
            output.push_str(&render_call_argument(argument)?);
        }
        output.push_str(");\n");
        render_value_steps(&mut output, self.return_block.layer())?;
        let returned =
            self.return_block
                .returned()
                .ok_or(DirectCallReturnFunctionError::MissingValue(
                    self.return_block.return_producer(),
                ))?;
        match returned.values() {
            [] => output.push_str("\treturn;\n"),
            [value] => writeln!(&mut output, "\treturn {};", value_name(value.binding()))
                .expect("String writes cannot fail"),
            _ => {
                return Err(DirectCallReturnFunctionError::MissingValue(
                    self.return_block.return_producer(),
                ));
            }
        }
        output.push_str("}\n");
        Ok(output)
    }
}

fn call_arguments_renderable(call_block: &CertifiedDirectCallBlockRegion) -> bool {
    let layer = call_block.body();
    let expressions = layer.accounting().expression_layer();
    call_block
        .call()
        .arguments()
        .iter()
        .all(|argument| match argument.value() {
            SemanticCCallArgumentValue::Expression(expression) => {
                expressions.expr(*expression).is_some()
                    && value_precedes(layer, argument.binding(), call_block.call_producer())
            }
            SemanticCCallArgumentValue::Constant(value) => {
                value.width_bits() == argument.ty().width_bits()
            }
            SemanticCCallArgumentValue::AbiParameter { index, input } => expressions
                .function_interface()
                .and_then(|interface| interface.parameters().get(*index as usize))
                .is_some_and(|parameter| {
                    parameter.index() == *index
                        && parameter.value() == Some(*input)
                        && parameter.ty() == argument.ty()
                }),
        })
}

fn return_is_call_independent(return_block: &CertifiedDirectCallReturnBlock) -> bool {
    let Some(returned) = return_block.returned() else {
        return false;
    };
    if returned.values().len() > 1 {
        return false;
    }
    let Some(value) = returned.values().first() else {
        return true;
    };
    let expressions = return_block.layer().accounting().expression_layer();
    let mut pending = vec![value.expression()];
    let mut visited = BTreeSet::new();
    while let Some(expression) = pending.pop() {
        if !visited.insert(expression) {
            continue;
        }
        let Some(expression) = expressions.expr(expression) else {
            return false;
        };
        if expression
            .source_instructions()
            .iter()
            .any(|source| source.block_addr != return_block.block_addr())
        {
            return false;
        }
        match expression.kind() {
            SemanticCExprKind::Input { .. } | SemanticCExprKind::MemoryRead { .. } => return false,
            SemanticCExprKind::Constant { .. } => {}
            SemanticCExprKind::Copy { input }
            | SemanticCExprKind::BitwiseNot { input }
            | SemanticCExprKind::BooleanNot { input }
            | SemanticCExprKind::Cast { input, .. }
            | SemanticCExprKind::Extract { input, .. } => pending.push(*input),
            SemanticCExprKind::Arithmetic { left, right, .. }
            | SemanticCExprKind::ArithmeticFlag { left, right, .. }
            | SemanticCExprKind::Bitwise { left, right, .. }
            | SemanticCExprKind::Boolean { left, right, .. }
            | SemanticCExprKind::Compare { left, right, .. } => {
                pending.extend([*left, *right]);
            }
            SemanticCExprKind::Shift { value, count, .. } => {
                pending.extend([*value, *count]);
            }
            SemanticCExprKind::Select {
                condition,
                if_true,
                if_false,
            } => pending.extend([*condition, *if_true, *if_false]),
        }
    }
    true
}

fn return_type(
    interface: &SemanticCFunctionInterface,
) -> Result<&'static str, DirectCallReturnFunctionError> {
    match interface.return_kind() {
        SemanticCFunctionReturn::Void => Ok("void"),
        SemanticCFunctionReturn::Register { ty, .. } => Ok(storage_type(ty)?),
    }
}

fn render_function_parameters(
    output: &mut String,
    interface: &SemanticCFunctionInterface,
) -> Result<(), DirectCallReturnFunctionError> {
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

fn render_call_parameter_types(
    output: &mut String,
    call: &crate::semantic_c::SemanticCDirectCall,
) -> Result<(), DirectCallReturnFunctionError> {
    if call.arguments().is_empty() {
        output.push_str("void");
        return Ok(());
    }
    for (position, argument) in call.arguments().iter().enumerate() {
        if position > 0 {
            output.push_str(", ");
        }
        output.push_str(storage_type(argument.ty())?);
    }
    Ok(())
}

fn render_value_steps(
    output: &mut String,
    layer: &SemanticCBlockStepLayer,
) -> Result<(), DirectCallReturnFunctionError> {
    let expressions = layer.accounting().expression_layer();
    for step in layer.steps() {
        let Some(reference) = step.value() else {
            continue;
        };
        let entity = layer
            .resolve_value(reference)
            .ok_or(DirectCallReturnFunctionError::MissingValue(step.source()))?;
        writeln!(
            output,
            "\t{} {} = {};",
            storage_type(expressions.expr_type(entity.root())?)?,
            value_name(entity.output()),
            expressions.render_expr(entity.root())?
        )
        .expect("String writes cannot fail");
        writeln!(output, "\t(void){};", value_name(entity.output()))
            .expect("String writes cannot fail");
    }
    Ok(())
}

fn render_call_argument(
    argument: &crate::semantic_c::SemanticCCallArgument,
) -> Result<String, DirectCallReturnFunctionError> {
    Ok(match argument.value() {
        SemanticCCallArgumentValue::Expression(_) => value_name(argument.binding()),
        SemanticCCallArgumentValue::Constant(value) => format!(
            "(({})UINT64_C(0x{:x}))",
            storage_type(argument.ty())?,
            value.bits()
        ),
        SemanticCCallArgumentValue::AbiParameter { input, .. } => value_name(*input),
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DirectCallReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl DirectCallReturnFunctionAuditReport {
    pub fn has_exact_direct_call_return(&self) -> bool {
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

#[cfg(test)]
mod tests {
    use super::*;

    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCallArgumentSpec,
        SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface, SourceFunctionInterface,
        SourceFunctionReturn, SourceStackSlotSpec, StackAddressBase,
    };

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("direct-call-return-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rsi", 16, 8));
        arch.add_register(RegisterDef::new("rdx", 24, 8));
        arch.add_register(RegisterDef::new("rip", 32, 8));
        arch.add_register(RegisterDef::new("rsp", 40, 8));
        arch
    }

    fn artifact(
        function_return: SourceFunctionReturn,
        call_result: SourceCallResult,
        complete_call: bool,
        include_function_interface: bool,
        include_memory_effect: bool,
    ) -> SsaArtifact {
        let target = Varnode::ram(0x8600, 8);
        let mut entry = R2ILBlock::new(0x8500, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x11, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(16, 8),
            src: Varnode::register(24, 8),
        });
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let mut returned = R2ILBlock::new(0x8504, 4);
        if include_memory_effect {
            returned.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x40, 8),
                val: Varnode::constant(1, 1),
            });
        }
        if matches!(function_return, SourceFunctionReturn::Register { .. }) {
            returned.push(R2ILOp::Copy {
                dst: Varnode::register(0, 8),
                src: Varnode::constant(7, 8),
            });
        }
        returned.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });
        let revision = b"direct-call-return-revision-1".to_vec();
        let function_interface = include_function_interface.then(|| {
            SourceFunctionInterface::new(
                revision.clone(),
                "caller-test-abi",
                [SourceAbiParameterSpec::new(0, storage(24))],
                function_return,
                [],
            )
            .expect("function interface")
        });
        let identity =
            SourceCallSiteIdentity::new(0x8500, 2, CanonicalStorageId::from_varnode(&target));
        let call_interface = SourceCallSiteInterface::new(
            revision,
            identity,
            complete_call,
            "callee-test-abi",
            [
                SourceCallArgumentSpec::new(0, storage(8)),
                SourceCallArgumentSpec::new(1, storage(16)),
            ],
            false,
            false,
            call_result,
        )
        .expect("call interface");
        SsaArtifact::raw_with_interfaces(
            &[entry, returned],
            Some(&arch()),
            function_interface,
            vec![call_interface],
        )
        .expect("call/return artifact")
    }

    fn register_return() -> SourceFunctionReturn {
        SourceFunctionReturn::Register {
            storage: storage(0),
        }
    }

    fn parameter_dependent_return_artifact() -> SsaArtifact {
        let target = Varnode::ram(0x8600, 8);
        let mut entry = R2ILBlock::new(0x8500, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(24, 8),
        });
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let mut returned = R2ILBlock::new(0x8504, 4);
        returned.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(24, 8),
        });
        returned.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });
        let revision = b"dependent-call-return-revision-1".to_vec();
        let function_interface = SourceFunctionInterface::new(
            revision.clone(),
            "caller-test-abi",
            [SourceAbiParameterSpec::new(0, storage(24))],
            register_return(),
            [],
        )
        .expect("function interface");
        let identity =
            SourceCallSiteIdentity::new(0x8500, 1, CanonicalStorageId::from_varnode(&target));
        let call_interface = SourceCallSiteInterface::new(
            revision,
            identity,
            true,
            "callee-test-abi",
            [SourceCallArgumentSpec::new(0, storage(8))],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("call interface");
        SsaArtifact::raw_with_interfaces(
            &[entry, returned],
            Some(&arch()),
            Some(function_interface),
            vec![call_interface],
        )
        .expect("dependent call/return artifact")
    }

    fn zero_argument_artifact(with_stack_slot: bool) -> SsaArtifact {
        let target = Varnode::ram(0x8610, 8);
        let mut entry = R2ILBlock::new(0x8520, 4);
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let mut returned = R2ILBlock::new(0x8524, 4);
        returned.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });
        let revision = b"zero-argument-call-return-revision-1".to_vec();
        let function_interface = SourceFunctionInterface::new(
            revision.clone(),
            "caller-test-abi",
            [],
            SourceFunctionReturn::Void,
            with_stack_slot.then(|| {
                SourceStackSlotSpec::new(StackAddressBase::StackPointer, storage(40), 0, 8)
            }),
        )
        .expect("function interface");
        let identity =
            SourceCallSiteIdentity::new(0x8520, 0, CanonicalStorageId::from_varnode(&target));
        let call_interface = SourceCallSiteInterface::new(
            revision,
            identity,
            true,
            "callee-test-abi",
            [],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("call interface");
        SsaArtifact::raw_with_interfaces(
            &[entry, returned],
            Some(&arch()),
            Some(function_interface),
            vec![call_interface],
        )
        .expect("zero-argument call/return artifact")
    }

    fn assert_refused(artifact: &SsaArtifact) {
        assert!(CertifiedDirectCallReturnFunction::from_artifact(artifact).is_err());
    }

    #[test]
    fn synthetic_direct_call_fixtures_are_refused_without_typed_machine_roles() {
        for function_return in [register_return(), SourceFunctionReturn::Void] {
            let artifact = artifact(function_return, SourceCallResult::Void, true, true, false);
            assert_refused(&artifact);
        }

        assert_refused(&zero_argument_artifact(false));
    }

    #[test]
    fn synthetic_direct_call_certificate_baseline_is_refused() {
        let artifact = artifact(register_return(), SourceCallResult::Void, true, true, false);
        assert_refused(&artifact);
    }

    #[test]
    fn synthetic_direct_call_differential_baseline_is_refused() {
        let artifact = artifact(register_return(), SourceCallResult::Void, true, true, false);
        assert_refused(&artifact);
    }

    #[test]
    fn missing_incomplete_and_nonvoid_call_interfaces_are_rejected() {
        let missing = artifact(
            register_return(),
            SourceCallResult::Void,
            true,
            false,
            false,
        );
        assert!(CertifiedDirectCallReturnFunction::from_artifact(&missing).is_err());

        let incomplete = artifact(
            register_return(),
            SourceCallResult::Void,
            false,
            true,
            false,
        );
        assert!(CertifiedDirectCallReturnFunction::from_artifact(&incomplete).is_err());

        let nonvoid = artifact(
            register_return(),
            SourceCallResult::Register {
                storage: storage(0),
            },
            true,
            true,
            false,
        );
        assert!(CertifiedDirectCallReturnFunction::from_artifact(&nonvoid).is_err());

        assert!(
            CertifiedDirectCallReturnFunction::from_artifact(
                &parameter_dependent_return_artifact()
            )
            .is_err(),
            "post-call values depending on pre-call register state need an explicit clobber model"
        );

        assert!(
            CertifiedDirectCallReturnFunction::from_artifact(&zero_argument_artifact(true))
                .is_err(),
            "stack resources are outside the direct-call return subset"
        );

        let memory = artifact(register_return(), SourceCallResult::Void, true, true, true);
        assert!(
            CertifiedDirectCallReturnFunction::from_artifact(&memory).is_err(),
            "memory effects are outside the direct-call return subset"
        );
    }

    #[test]
    fn literal_same_block_call_return_and_unsupported_effects_are_rejected() {
        let target = Varnode::ram(0x8600, 8);
        let mut block = R2ILBlock::new(0x8500, 4);
        block.push(R2ILOp::Call {
            target: target.clone(),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });
        let revision = b"same-block-call-return-revision-1".to_vec();
        let identity =
            SourceCallSiteIdentity::new(0x8500, 0, CanonicalStorageId::from_varnode(&target));
        let call_interface = SourceCallSiteInterface::new(
            revision.clone(),
            identity,
            true,
            "callee-test-abi",
            [],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("call interface");
        let function_interface = SourceFunctionInterface::new(
            revision,
            "caller-test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("function interface");
        let same_block = SsaArtifact::raw_with_interfaces(
            &[block],
            Some(&arch()),
            Some(function_interface),
            vec![call_interface],
        )
        .expect("same-block artifact");
        assert!(CertifiedDirectCallReturnFunction::from_artifact(&same_block).is_err());

        let mut entry = R2ILBlock::new(0x8500, 4);
        entry.push(R2ILOp::Call {
            target: Varnode::ram(0x8600, 8),
        });
        let mut returned = R2ILBlock::new(0x8504, 4);
        returned.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x40, 8),
            val: Varnode::constant(1, 1),
        });
        returned.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });
        let unsupported = SsaArtifact::raw(&[entry, returned], Some(&arch()))
            .expect("unsupported call/memory artifact");
        assert!(CertifiedDirectCallReturnFunction::from_artifact(&unsupported).is_err());
    }
}
