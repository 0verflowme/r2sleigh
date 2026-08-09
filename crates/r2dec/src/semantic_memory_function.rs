//! Closed semantic-C functions with certified plain RAM memory effects.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedMachineProjection, CertifiedMemoryExecutionPolicy, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedRenderPermit, CertifiedSourceTerminator,
    CertifiedTypedRegionKind, RenderAuthorizationError, TypedRegionMapping,
    certify_plain_ram_memory_return_region,
};
use r2ssa::{
    CanonicalInstructionId, MachineAddressSpace, MachineBuildError, MachineMemoryEndianness,
    MachineType, MachineValueBinding, MachineValueUse, SemanticInstructionState, SsaArtifact,
};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionBuildError, RegionObligationDisposition,
};
use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCExprId, SemanticCExprKind,
    SemanticCFunctionReturn, SemanticCInputOrigin, SemanticCReturn, storage_type, value_name,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedMemorySemanticCFunctionScope {
    SingleTerminalReturnBlockWithPlainRamMemory,
}

/// A sealed complete function for the narrow plain-RAM helper ABI.
///
/// The duplicated memory and return manifests are intentional mutation guards:
/// rendering is permitted only while they exactly match the source-ordered
/// typed block and the final source return.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedMemorySemanticCFunction {
    schema_version: u32,
    scope: CertifiedMemorySemanticCFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    layer: SemanticCBlockStepLayer,
    memory_order: Box<[CanonicalInstructionId]>,
    return_producer: CanonicalInstructionId,
    returned_value: Option<MachineValueBinding>,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CertifiedMemorySemanticCFunctionError {
    Machine(MachineBuildError),
    Region(RegionBuildError),
    Statement(SemanticCStatementError),
    Authorization(RenderAuthorizationError),
    MissingFunctionInterface,
    NotClosedTerminalReturn,
    MissingMemory,
    UnsupportedInput,
    UnsupportedMemory(CanonicalInstructionId),
    InvalidReturn,
    UndefinedValue(MachineValueBinding),
    InvalidFunction(Vec<String>),
    SemanticC(SemanticCError),
}

impl std::fmt::Display for CertifiedMemorySemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified memory semantic C function failed: {self:?}")
    }
}

impl std::error::Error for CertifiedMemorySemanticCFunctionError {}

impl From<MachineBuildError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Region(error)
    }
}

impl From<SemanticCStatementError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<RenderAuthorizationError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
    }
}

impl From<SemanticCError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn typed_region_mappings(accounting: &CertifiedSingleBlockAccounting) -> Vec<TypedRegionMapping> {
    accounting
        .mappings()
        .iter()
        .filter_map(|mapping| {
            let [effect] = accounting.ledger().effects(mapping.obligation()) else {
                return None;
            };
            Some(TypedRegionMapping::new(
                mapping.obligation(),
                effect.disposition().clone(),
            ))
        })
        .collect()
}

fn memory_order(layer: &SemanticCBlockStepLayer) -> Vec<CanonicalInstructionId> {
    layer
        .steps()
        .iter()
        .filter_map(|step| step.memory().map(|_| step.source()))
        .collect()
}

impl CertifiedMemorySemanticCFunction {
    /// Construct the complete proof chain internally from one immutable source
    /// artifact. No caller-supplied permit or typed node can cross this seam.
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, CertifiedMemorySemanticCFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(artifact)?;
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)?;
        let accounting_audit = accounting.audit();
        if !accounting_audit.has_exact_source_accounting() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source accounting does not exactly cover the selected artifact".to_string()],
            ));
        }
        if accounting_audit.has_residuals()
            || accounting.mappings().iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::Residualized { .. }
                )
            })
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source accounting retains residual obligations".to_string()],
            ));
        }
        if accounting.expression_layer().function_interface().is_none() {
            return Err(CertifiedMemorySemanticCFunctionError::MissingFunctionInterface);
        }
        if accounting
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
        {
            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedInput);
        }
        let Some(block) = accounting.source_block() else {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source accounting does not select exactly one block".to_string()],
            ));
        };
        if accounting.topology().entry_addr() != block.addr()
            || !block.predecessors().is_empty()
            || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || !accounting.direct_calls().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || accounting.instructions().iter().any(|instruction| {
                instruction.state() == SemanticInstructionState::UnsupportedUnknown
                    || matches!(
                        instruction.source().site,
                        r2ssa::CanonicalInstructionSite::Phi(_)
                    )
            })
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source block is not one closed supported terminal-return block".to_string()],
            ));
        }
        let [returned] = accounting.semantic_returns() else {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn);
        };
        if accounting.return_controls().len() != 1
            || block.instructions().last() != Some(&returned.producer())
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn);
        }
        let returned_value = match returned.values() {
            [] => None,
            [value] => Some(value.binding()),
            _ => return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn),
        };
        let return_producer = returned.producer();
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        if layer.steps().last().map(|step| step.source()) != Some(return_producer) {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn);
        }
        let memory_order = memory_order(&layer);
        if memory_order.is_empty() {
            return Err(CertifiedMemorySemanticCFunctionError::MissingMemory);
        }
        let mappings = typed_region_mappings(layer.accounting());
        let render_permit = certify_plain_ram_memory_return_region(
            layer.accounting().origin(),
            layer.accounting().ledger(),
            mappings,
        )?;
        let function = Self {
            schema_version: CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope:
                CertifiedMemorySemanticCFunctionScope::SingleTerminalReturnBlockWithPlainRamMemory,
            name: format!("certified_mem_sub_{:x}", layer.accounting().block_addr()),
            origin: layer.accounting().origin().clone(),
            layer,
            memory_order: memory_order.into_boxed_slice(),
            return_producer,
            returned_value,
            render_permit,
        };
        let audit = function.audit();
        if !audit.has_exact_closed_memory_return() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                audit.invalid,
            ));
        }
        function.render_body()?;
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedMemorySemanticCFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn layer(&self) -> &SemanticCBlockStepLayer {
        &self.layer
    }

    pub const fn memory_order(&self) -> &[CanonicalInstructionId] {
        &self.memory_order
    }

    pub const fn render_permit(&self) -> &CertifiedRenderPermit {
        &self.render_permit
    }

    pub fn returned(&self) -> Option<&SemanticCReturn> {
        self.layer
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == self.return_producer)
    }

    pub fn audit(&self) -> CertifiedMemorySemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        let accounting = self.layer.accounting();
        let mappings = typed_region_mappings(accounting);
        if self.schema_version != CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("memory function schema mismatch".to_string());
        }
        if self.scope
            != CertifiedMemorySemanticCFunctionScope::SingleTerminalReturnBlockWithPlainRamMemory
        {
            invalid.push("memory function scope mismatch".to_string());
        }
        if self.origin != *accounting.origin() {
            invalid.push("memory function origin mismatch".to_string());
        }
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::PlainRamMemoryTerminalReturnFunction,
            CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            &mappings,
        ) {
            invalid.push("memory function render permit mismatch".to_string());
        }
        if !self.layer.audit().has_exact_source_order()
            || !accounting.audit().has_exact_source_accounting()
            || accounting.audit().has_residuals()
        {
            invalid.push("memory function source accounting is not exact".to_string());
        }
        let Some(block) = accounting.source_block() else {
            invalid.push("memory function has no source block".to_string());
            return CertifiedMemorySemanticCFunctionAuditReport { invalid };
        };
        if accounting.topology().entry_addr() != block.addr()
            || !block.predecessors().is_empty()
            || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || block.instructions().last() != Some(&self.return_producer)
            || self.layer.steps().last().map(|step| step.source()) != Some(self.return_producer)
            || !accounting.direct_calls().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            invalid.push("memory function is not one closed terminal-return block".to_string());
        }
        if accounting.instructions().iter().any(|instruction| {
            instruction.state() == SemanticInstructionState::UnsupportedUnknown
                || matches!(
                    instruction.source().site,
                    r2ssa::CanonicalInstructionSite::Phi(_)
                )
        }) {
            invalid.push("memory function contains unsupported source semantics".to_string());
        }
        if accounting
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
        {
            invalid.push("memory function contains a stack or unclassified input".to_string());
        }
        let actual_memory_order = memory_order(&self.layer);
        if actual_memory_order.is_empty()
            || actual_memory_order.as_slice() != self.memory_order.as_ref()
        {
            invalid.push("memory effect manifest differs from source order".to_string());
        }
        let returned = self.returned();
        let actual_returned_value = returned.and_then(|returned| match returned.values() {
            [] => Some(None),
            [value] => Some(Some(value.binding())),
            _ => None,
        });
        if accounting.semantic_returns().len() != 1
            || accounting.return_controls().len() != 1
            || actual_returned_value != Some(self.returned_value)
        {
            invalid.push(
                "returned value manifest differs from the exact interface return".to_string(),
            );
        }
        if let Err(error) = self.validate_render_sequence() {
            invalid.push(format!("memory render sequence is invalid: {error}"));
        }
        CertifiedMemorySemanticCFunctionAuditReport { invalid }
    }

    /// Render strict C11 whose only memory operations are calls through the
    /// declared width/endian-specific RAM helper ABI.
    pub fn render_certified_c(&self) -> Result<String, CertifiedMemorySemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_closed_memory_return() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                report.invalid,
            ));
        }
        self.render_body()
    }

    fn render_body(&self) -> Result<String, CertifiedMemorySemanticCFunctionError> {
        self.validate_render_sequence()?;
        let expressions = self.layer.accounting().expression_layer();
        let interface = expressions
            .function_interface()
            .ok_or(CertifiedMemorySemanticCFunctionError::MissingFunctionInterface)?;
        let return_type = match interface.return_kind() {
            SemanticCFunctionReturn::Void => "void",
            SemanticCFunctionReturn::Register { ty, .. } => storage_type(ty)?,
        };
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        output.push('\n');
        output.push_str(PLAIN_RAM_HELPER_DECLARATIONS);
        write!(&mut output, "\n{return_type} {}(", self.name).expect("String writes cannot fail");
        if interface.parameters().is_empty() {
            output.push_str("void");
        } else {
            for (position, parameter) in interface.parameters().iter().enumerate() {
                if position > 0 {
                    output.push_str(", ");
                }
                let name = parameter
                    .value()
                    .map(value_name)
                    .unwrap_or_else(|| format!("arg_{}", parameter.index()));
                write!(&mut output, "{} {name}", storage_type(parameter.ty())?)
                    .expect("String writes cannot fail");
            }
        }
        output.push_str(") {\n");
        for parameter in interface.parameters() {
            let name = parameter
                .value()
                .map(value_name)
                .unwrap_or_else(|| format!("arg_{}", parameter.index()));
            writeln!(&mut output, "\t(void){name};").expect("String writes cannot fail");
        }
        for step in self.layer.steps() {
            if let Some(reference) = step.memory() {
                let statement = self.layer.resolve_memory_statement(reference).ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                )?;
                let helper = memory_helper_name(statement);
                let address = render_value_use(statement.address());
                match statement.kind() {
                    CertifiedMemoryStatementKind::Read { result } => {
                        writeln!(
                            &mut output,
                            "\t{} {} = {helper}((uint64_t)({address}));",
                            storage_type(result.ty())?,
                            value_name(result.binding())
                        )
                        .expect("String writes cannot fail");
                    }
                    CertifiedMemoryStatementKind::Write { value } => {
                        writeln!(
                            &mut output,
                            "\t{helper}((uint64_t)({address}), ({})({}));",
                            storage_type(value.ty())?,
                            render_value_use(value)
                        )
                        .expect("String writes cannot fail");
                    }
                }
                continue;
            }
            let Some(reference) = step.value() else {
                continue;
            };
            let entity = self.layer.resolve_value(reference).ok_or(
                CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
            )?;
            writeln!(
                &mut output,
                "\t{} {} = {};",
                storage_type(expressions.expr_type(entity.root())?)?,
                value_name(entity.output()),
                expressions.render_expr(entity.root())?
            )
            .expect("String writes cannot fail");
        }
        match self.returned_value {
            None => output.push_str("\treturn;\n"),
            Some(binding) => writeln!(&mut output, "\treturn {};", value_name(binding))
                .expect("String writes cannot fail"),
        }
        output.push_str("}\n");
        Ok(output)
    }

    fn validate_render_sequence(&self) -> Result<(), CertifiedMemorySemanticCFunctionError> {
        let expressions = self.layer.accounting().expression_layer();
        let interface = expressions
            .function_interface()
            .ok_or(CertifiedMemorySemanticCFunctionError::MissingFunctionInterface)?;
        let mut defined = interface
            .parameters()
            .iter()
            .filter_map(|parameter| parameter.value())
            .collect::<BTreeSet<_>>();
        let mut observed_memory = Vec::new();
        for step in self.layer.steps() {
            if let Some(reference) = step.memory() {
                let statement = self.layer.resolve_memory_statement(reference).ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                )?;
                validate_memory_statement(statement)?;
                require_value_use_defined(statement.address(), &defined)?;
                observed_memory.push(statement.producer());
                match statement.kind() {
                    CertifiedMemoryStatementKind::Read { result } => {
                        let entity = step
                            .value()
                            .and_then(|reference| self.layer.resolve_value(reference))
                            .filter(|entity| entity.output() == result.binding())
                            .ok_or(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ))?;
                        let expression = expressions.expr(entity.root()).ok_or(
                            CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                        )?;
                        let SemanticCExprKind::MemoryRead {
                            access,
                            object,
                            space,
                            endianness,
                            word_size_bytes,
                            address,
                            width_bits,
                        } = expression.kind()
                        else {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        };
                        if *access != statement.access()
                            || *object != statement.object()
                            || *space != statement.space()
                            || *endianness != statement.endianness()
                            || *word_size_bytes != statement.word_size_bytes()
                            || *width_bits != statement.width_bits()
                            || expression.ty() != result.ty()
                            || !expression_matches_value_use(
                                expressions,
                                *address,
                                statement.address(),
                            )
                        {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        }
                        defined.insert(result.binding());
                    }
                    CertifiedMemoryStatementKind::Write { value } => {
                        if step.value().is_some() {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        }
                        require_value_use_defined(value, &defined)?;
                    }
                }
                continue;
            }
            if let Some(reference) = step.value() {
                let entity = self.layer.resolve_value(reference).ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                )?;
                let mut inputs = BTreeSet::new();
                collect_expression_inputs(
                    expressions,
                    entity.root(),
                    &mut BTreeSet::new(),
                    &mut inputs,
                )?;
                if let Some(undefined) = inputs.iter().find(|binding| !defined.contains(binding)) {
                    return Err(CertifiedMemorySemanticCFunctionError::UndefinedValue(
                        *undefined,
                    ));
                }
                expressions.render_expr(entity.root())?;
                defined.insert(entity.output());
            }
        }
        if observed_memory.as_slice() != self.memory_order.as_ref() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["memory effect order mismatch".to_string()],
            ));
        }
        match (interface.return_kind(), self.returned_value) {
            (SemanticCFunctionReturn::Void, None) => {}
            (SemanticCFunctionReturn::Register { ty, .. }, Some(binding))
                if binding.width_bits() == ty.width_bits() && defined.contains(&binding) => {}
            _ => return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn),
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedMemorySemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl CertifiedMemorySemanticCFunctionAuditReport {
    pub fn has_exact_closed_memory_return(&self) -> bool {
        self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}

fn validate_memory_statement(
    statement: &CertifiedMemoryStatement,
) -> Result<(), CertifiedMemorySemanticCFunctionError> {
    if statement.space() != MachineAddressSpace::Ram
        || statement.word_size_bytes() != 1
        || !matches!(statement.width_bits(), 8 | 16 | 32 | 64)
        || !matches!(
            statement.endianness(),
            MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
        )
        || statement.execution()
            != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrderViaHelper
        || !matches!(
            statement.address().ty(),
            MachineType::Address {
                space: MachineAddressSpace::Ram,
                width_bits: 8 | 16 | 32 | 64,
                ..
            }
        )
    {
        return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
            statement.producer(),
        ));
    }
    Ok(())
}

fn require_value_use_defined(
    value: &MachineValueUse,
    defined: &BTreeSet<MachineValueBinding>,
) -> Result<(), CertifiedMemorySemanticCFunctionError> {
    if value.constant().is_none() && !defined.contains(&value.binding()) {
        return Err(CertifiedMemorySemanticCFunctionError::UndefinedValue(
            value.binding(),
        ));
    }
    Ok(())
}

fn expression_matches_value_use(
    expressions: &crate::semantic_c::SemanticCExpressionLayer,
    expression: SemanticCExprId,
    value: &MachineValueUse,
) -> bool {
    expressions.expr(expression).is_some_and(|expression| {
        expression.ty() == value.ty()
            && match (expression.kind(), value.constant()) {
                (
                    SemanticCExprKind::Constant {
                        binding,
                        value: actual,
                    },
                    Some(expected),
                ) => *binding == value.binding() && *actual == expected,
                (SemanticCExprKind::Input { binding }, None) => *binding == value.binding(),
                _ => false,
            }
    })
}

fn collect_expression_inputs(
    expressions: &crate::semantic_c::SemanticCExpressionLayer,
    expression: SemanticCExprId,
    visited: &mut BTreeSet<SemanticCExprId>,
    inputs: &mut BTreeSet<MachineValueBinding>,
) -> Result<(), CertifiedMemorySemanticCFunctionError> {
    if !visited.insert(expression) {
        return Ok(());
    }
    let expression =
        expressions
            .expr(expression)
            .ok_or(CertifiedMemorySemanticCFunctionError::SemanticC(
                SemanticCError::MissingSemanticExpression(expression),
            ))?;
    match expression.kind() {
        SemanticCExprKind::Input { binding } => {
            inputs.insert(*binding);
        }
        SemanticCExprKind::Constant { .. } => {}
        SemanticCExprKind::MemoryRead { .. } => {
            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                expression
                    .source_instructions()
                    .iter()
                    .next_back()
                    .copied()
                    .unwrap_or(CanonicalInstructionId {
                        block_addr: 0,
                        site: r2ssa::CanonicalInstructionSite::Op(0),
                    }),
            ));
        }
        SemanticCExprKind::Copy { input }
        | SemanticCExprKind::BitwiseNot { input }
        | SemanticCExprKind::BooleanNot { input }
        | SemanticCExprKind::Cast { input, .. }
        | SemanticCExprKind::Extract { input, .. } => {
            collect_expression_inputs(expressions, *input, visited, inputs)?;
        }
        SemanticCExprKind::Arithmetic { left, right, .. }
        | SemanticCExprKind::ArithmeticFlag { left, right, .. }
        | SemanticCExprKind::Bitwise { left, right, .. }
        | SemanticCExprKind::Boolean { left, right, .. }
        | SemanticCExprKind::Compare { left, right, .. } => {
            collect_expression_inputs(expressions, *left, visited, inputs)?;
            collect_expression_inputs(expressions, *right, visited, inputs)?;
        }
        SemanticCExprKind::Shift { value, count, .. } => {
            collect_expression_inputs(expressions, *value, visited, inputs)?;
            collect_expression_inputs(expressions, *count, visited, inputs)?;
        }
        SemanticCExprKind::Select {
            condition,
            if_true,
            if_false,
        } => {
            collect_expression_inputs(expressions, *condition, visited, inputs)?;
            collect_expression_inputs(expressions, *if_true, visited, inputs)?;
            collect_expression_inputs(expressions, *if_false, visited, inputs)?;
        }
    }
    Ok(())
}

pub(crate) fn render_value_use(value: &MachineValueUse) -> String {
    value.constant().map_or_else(
        || value_name(value.binding()),
        |constant| format!("UINT64_C(0x{:x})", constant.bits()),
    )
}

pub(crate) fn memory_helper_name(statement: &CertifiedMemoryStatement) -> &'static str {
    match (
        statement.kind(),
        statement.endianness(),
        statement.width_bits(),
    ) {
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 8) => {
            "r2s_ram_read_le_u8"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 16) => {
            "r2s_ram_read_le_u16"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 32) => {
            "r2s_ram_read_le_u32"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 64) => {
            "r2s_ram_read_le_u64"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 8) => {
            "r2s_ram_read_be_u8"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 16) => {
            "r2s_ram_read_be_u16"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 32) => {
            "r2s_ram_read_be_u32"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 64) => {
            "r2s_ram_read_be_u64"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 8) => {
            "r2s_ram_write_le_u8"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 16) => {
            "r2s_ram_write_le_u16"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 32) => {
            "r2s_ram_write_le_u32"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 64) => {
            "r2s_ram_write_le_u64"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 8) => {
            "r2s_ram_write_be_u8"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 16) => {
            "r2s_ram_write_be_u16"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 32) => {
            "r2s_ram_write_be_u32"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 64) => {
            "r2s_ram_write_be_u64"
        }
        _ => unreachable!("memory statement is validated before helper selection"),
    }
}

pub(crate) const PLAIN_RAM_HELPER_DECLARATIONS: &str = r#"extern uint8_t r2s_ram_read_le_u8(uint64_t byte_address);
extern uint16_t r2s_ram_read_le_u16(uint64_t byte_address);
extern uint32_t r2s_ram_read_le_u32(uint64_t byte_address);
extern uint64_t r2s_ram_read_le_u64(uint64_t byte_address);
extern uint8_t r2s_ram_read_be_u8(uint64_t byte_address);
extern uint16_t r2s_ram_read_be_u16(uint64_t byte_address);
extern uint32_t r2s_ram_read_be_u32(uint64_t byte_address);
extern uint64_t r2s_ram_read_be_u64(uint64_t byte_address);
extern void r2s_ram_write_le_u8(uint64_t byte_address, uint8_t value);
extern void r2s_ram_write_le_u16(uint64_t byte_address, uint16_t value);
extern void r2s_ram_write_le_u32(uint64_t byte_address, uint32_t value);
extern void r2s_ram_write_le_u64(uint64_t byte_address, uint64_t value);
extern void r2s_ram_write_be_u8(uint64_t byte_address, uint8_t value);
extern void r2s_ram_write_be_u16(uint64_t byte_address, uint16_t value);
extern void r2s_ram_write_be_u32(uint64_t byte_address, uint32_t value);
extern void r2s_ram_write_be_u64(uint64_t byte_address, uint64_t value);
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceFunctionInterface, SourceFunctionReturn,
    };

    fn compile(source: &str) {
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Wno-unused-function",
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

    fn interface(return_kind: SourceFunctionReturn) -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"memory-semantic-function-revision-1".to_vec(),
            "test-register-abi",
            [],
            return_kind,
            [],
        )
        .expect("explicit interface")
    }

    fn arch(endianness: Endianness, width_bytes: u32, word_size: u32) -> ArchSpec {
        let mut arch = ArchSpec::new("memory-semantic-function-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("ret", 0, width_bytes));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        let mut ram = AddressSpace::ram(8);
        ram.word_size = word_size;
        arch.add_space(ram);
        arch.set_memory_endianness(endianness);
        arch
    }

    fn return_storage(width_bytes: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: width_bytes,
        }
    }

    fn load_return(endianness: Endianness, width_bytes: u32) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x8100 + u64::from(width_bytes), 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0, width_bytes),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x40, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        SsaArtifact::raw_with_interface(
            &[block],
            Some(&arch(endianness, width_bytes, 1)),
            interface(SourceFunctionReturn::Register {
                storage: return_storage(width_bytes),
            }),
        )
        .expect("load-return artifact")
    }

    fn ordered_aliasing() -> SsaArtifact {
        let mut block = R2ILBlock::new(0x8200, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x40, 8),
            val: Varnode::constant(0xaa, 1),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(0, 1),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x40, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        SsaArtifact::raw_with_interface(
            &[block],
            Some(&arch(Endianness::Little, 1, 1)),
            interface(SourceFunctionReturn::Register {
                storage: return_storage(1),
            }),
        )
        .expect("ordered alias artifact")
    }

    #[test]
    fn width_endian_helper_calls_are_declared_structured_and_compile_as_c11() {
        for endianness in [Endianness::Little, Endianness::Big] {
            for width_bytes in [1, 2, 4, 8] {
                let function = CertifiedMemorySemanticCFunction::from_artifact(&load_return(
                    endianness,
                    width_bytes,
                ))
                .unwrap_or_else(|error| {
                    panic!("certified memory function {endianness:?}/{width_bytes}: {error:?}")
                });
                let source = function.render_certified_c().expect("strict helper C");
                let endian = if endianness == Endianness::Little {
                    "le"
                } else {
                    "be"
                };
                let width = width_bytes * 8;
                let helper = format!("r2s_ram_read_{endian}_u{width}");
                assert_eq!(source.matches(&format!("{helper}((uint64_t)(")).count(), 1);
                assert!(source.contains(&format!(
                    "extern uint{width}_t {helper}(uint64_t byte_address);"
                )));
                assert!(!source.contains("volatile"));
                assert!(!source.contains("uint8_t *"));
                assert!(source.contains("\treturn v_"));
                compile(&source);
            }
        }
    }

    #[test]
    fn store_void_uses_one_explicit_helper_and_exact_void_return() {
        let mut block = R2ILBlock::new(0x8300, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x44, 8),
            val: Varnode::constant(0x1122, 2),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let artifact = SsaArtifact::raw_with_interface(
            &[block],
            Some(&arch(Endianness::Big, 2, 1)),
            interface(SourceFunctionReturn::Void),
        )
        .expect("store-void artifact");
        let function =
            CertifiedMemorySemanticCFunction::from_artifact(&artifact).expect("store function");
        let source = function.render_certified_c().expect("store C");
        assert_eq!(
            source.matches("r2s_ram_write_be_u16((uint64_t)(").count(),
            1
        );
        assert!(source.contains("void certified_mem_sub_8300(void)"));
        assert!(source.contains("\treturn;"));
        compile(&source);
    }

    #[test]
    fn mutation_guards_reject_drop_duplicate_reorder_and_return_value_changes() {
        let original = CertifiedMemorySemanticCFunction::from_artifact(&ordered_aliasing())
            .expect("ordered function");
        assert_eq!(original.memory_order.len(), 2);

        let mut dropped = original.clone();
        dropped.memory_order = dropped.memory_order[1..].to_vec().into_boxed_slice();
        assert!(!dropped.audit().has_exact_closed_memory_return());
        assert!(dropped.render_certified_c().is_err());

        let mut duplicated = original.clone();
        let mut order = duplicated.memory_order.to_vec();
        order.push(order[0]);
        duplicated.memory_order = order.into_boxed_slice();
        assert!(!duplicated.audit().has_exact_closed_memory_return());
        assert!(duplicated.render_certified_c().is_err());

        let mut reordered = original.clone();
        reordered.memory_order.reverse();
        assert!(!reordered.audit().has_exact_closed_memory_return());
        assert!(reordered.render_certified_c().is_err());

        let mut wrong_return = original;
        wrong_return.returned_value = Some(
            wrong_return.layer.accounting().memory_statements()[0]
                .address()
                .binding(),
        );
        assert!(!wrong_return.audit().has_exact_closed_memory_return());
        assert!(wrong_return.render_certified_c().is_err());
    }

    #[test]
    fn missing_memory_and_word_addressing_are_refused() {
        let mut no_memory = R2ILBlock::new(0x8400, 4);
        no_memory.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let no_memory = SsaArtifact::raw_with_interface(
            &[no_memory],
            Some(&arch(Endianness::Little, 1, 1)),
            interface(SourceFunctionReturn::Void),
        )
        .expect("memory-free artifact");
        assert!(matches!(
            CertifiedMemorySemanticCFunction::from_artifact(&no_memory),
            Err(CertifiedMemorySemanticCFunctionError::MissingMemory)
                | Err(CertifiedMemorySemanticCFunctionError::Authorization(_))
        ));

        let mut word_block = R2ILBlock::new(0x8404, 4);
        word_block.push(R2ILOp::Load {
            dst: Varnode::register(0, 1),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x40, 8),
        });
        word_block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let word_artifact = SsaArtifact::raw_with_interface(
            &[word_block],
            Some(&arch(Endianness::Little, 1, 2)),
            interface(SourceFunctionReturn::Register {
                storage: return_storage(1),
            }),
        )
        .expect("word-addressed artifact");
        assert!(CertifiedMemorySemanticCFunction::from_artifact(&word_artifact).is_err());
    }
}
