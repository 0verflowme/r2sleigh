//! Fully authorized semantic-C functions for the currently admitted subset.

use std::fmt::Write as _;

use r2cert::CertifiedMachineProjection;
use r2ssa::{MachineBuildError, TrustedSsaArtifact};
use serde::Serialize;

use crate::certified_region::{CertifiedSingleBlockAccounting, RegionBuildError};
use crate::certified_return::{CertifiedTerminalReturnBlockRegion, TerminalReturnRegionError};
use crate::semantic_c::{
    SemanticCError, SemanticCFunctionReturn, SemanticCHelperSet, SemanticCInputOrigin,
    insert_semantic_c_helpers, logical_return_type, render_logical_parameter_declarations,
    render_logical_return_statement, render_parameter_graph_binding_prologue,
    render_projected_parameter_inputs, storage_type,
    value_name,
};

pub const CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedSemanticCFunctionScope {
    SingleTerminalReturnBlockWithoutMemory,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSemanticCFunction {
    schema_version: u32,
    scope: CertifiedSemanticCFunctionScope,
    name: String,
    region: CertifiedTerminalReturnBlockRegion,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CertifiedSemanticCFunctionError {
    Machine(MachineBuildError),
    Region(RegionBuildError),
    TerminalReturn(TerminalReturnRegionError),
    InvalidRegion(Vec<String>),
    MissingFunctionInterface,
    MissingReturnProjection,
    MemoryRequiresSemanticRenderer,
    StackAddressRequiresMemoryRenderer,
    MissingReturnedEntity,
    SemanticC(SemanticCError),
}

impl std::fmt::Display for CertifiedSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified semantic C function failed: {self:?}")
    }
}

impl std::error::Error for CertifiedSemanticCFunctionError {}

impl From<SemanticCError> for CertifiedSemanticCFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

impl From<MachineBuildError> for CertifiedSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for CertifiedSemanticCFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Region(error)
    }
}

impl From<TerminalReturnRegionError> for CertifiedSemanticCFunctionError {
    fn from(error: TerminalReturnRegionError) -> Self {
        Self::TerminalReturn(error)
    }
}

impl CertifiedSemanticCFunction {
    /// Build the complete admitted authorization chain from one source-retaining
    /// trusted SSA artifact. No child certificate or render token crosses this boundary.
    pub fn from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, CertifiedSemanticCFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(trusted)?;
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)?;
        let region = CertifiedTerminalReturnBlockRegion::from_accounting(
            accounting,
            certified.frame_preservation(),
        )?;
        Self::from_terminal_region(region)
    }

    pub fn from_terminal_region(
        region: CertifiedTerminalReturnBlockRegion,
    ) -> Result<Self, CertifiedSemanticCFunctionError> {
        let report = region.audit();
        if !report.has_exact_terminal_return() {
            return Err(CertifiedSemanticCFunctionError::InvalidRegion(
                report.invalid().to_vec(),
            ));
        }
        let accounting = region.layer().accounting();
        if accounting.expression_layer().function_interface().is_none() {
            return Err(CertifiedSemanticCFunctionError::MissingFunctionInterface);
        }
        if !accounting.memory_statements().is_empty() {
            return Err(CertifiedSemanticCFunctionError::MemoryRequiresSemanticRenderer);
        }
        if accounting
            .expression_layer()
            .input_origins()
            .values()
            .any(|origin| matches!(origin, SemanticCInputOrigin::StackSlot { .. }))
        {
            return Err(CertifiedSemanticCFunctionError::StackAddressRequiresMemoryRenderer);
        }
        let returned = region
            .returned()
            .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
        let interface = accounting
            .expression_layer()
            .function_interface()
            .ok_or(CertifiedSemanticCFunctionError::MissingFunctionInterface)?;
        let return_matches = match (interface.return_kind(), interface.return_projection()) {
            (SemanticCFunctionReturn::Void, None) => {
                returned.values().is_empty() && returned.register_compositions().is_empty()
            }
            (SemanticCFunctionReturn::Register { storage, ty }, Some(projection))
                if projection.physical_ty() == ty =>
            {
                returned.single_operand().is_some_and(|operand| {
                    matches!(
                        operand.slot(),
                        r2ssa::CallBoundarySlot::Register {
                            index: 0,
                            storage: actual,
                        } if actual == *storage
                    ) && operand.physical_width_bits() == ty.width_bits()
                        && region.operand_is_grounded_before_return(operand)
                })
            }
            _ => false,
        };
        if !return_matches {
            return Err(CertifiedSemanticCFunctionError::MissingReturnProjection);
        }
        Ok(Self {
            schema_version: CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: CertifiedSemanticCFunctionScope::SingleTerminalReturnBlockWithoutMemory,
            name: format!("certified_sub_{:x}", accounting.block_addr()),
            region,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedSemanticCFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn region(&self) -> &CertifiedTerminalReturnBlockRegion {
        &self.region
    }

    /// Render the authorized carrier-safe C11 subset. The exact source-logical
    /// return projection is honored; cosmetic names remain non-authoritative.
    pub fn render_certified_c(&self) -> Result<String, CertifiedSemanticCFunctionError> {
        let report = self.region.audit();
        if self.schema_version != CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION
            || self.scope != CertifiedSemanticCFunctionScope::SingleTerminalReturnBlockWithoutMemory
            || !report.has_exact_terminal_return()
        {
            return Err(CertifiedSemanticCFunctionError::InvalidRegion(
                report.invalid().to_vec(),
            ));
        }
        let accounting = self.region.layer().accounting();
        let expressions = accounting.expression_layer();
        let interface = expressions
            .function_interface()
            .ok_or(CertifiedSemanticCFunctionError::MissingFunctionInterface)?;
        let return_type = logical_return_type(interface)?;
        let mut output = String::new();
        let mut helpers = SemanticCHelperSet::default();
        output.push_str("#include <stdint.h>\n\n");
        let helper_insertion = output.len();
        write!(&mut output, "\n{return_type} {}(", self.name).expect("String writes cannot fail");
        output.push_str(&render_logical_parameter_declarations(interface)?);
        output.push_str(") {\n");
        output.push_str(&render_parameter_graph_binding_prologue(interface)?);
        output.push_str(&render_projected_parameter_inputs(expressions)?);
        for step in self.region.layer().steps() {
            let Some(reference) = step.value() else {
                continue;
            };
            let entity = self
                .region
                .layer()
                .resolve_value(reference)
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            let expression = expressions.render_expr(entity.root(), &mut helpers)?;
            writeln!(
                &mut output,
                "\t{} {} = {expression};",
                storage_type(expressions.expr_type(entity.root())?)?,
                value_name(entity.output())
            )
            .expect("String writes cannot fail");
        }
        let returned = self
            .region
            .returned()
            .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
        let return_value = match interface.return_kind() {
            SemanticCFunctionReturn::Void
                if returned.values().is_empty() && returned.register_compositions().is_empty() =>
            {
                None
            }
            SemanticCFunctionReturn::Register { storage, ty } => {
                let operand = returned
                    .single_operand()
                    .filter(|operand| {
                        matches!(
                            operand.slot(),
                            r2ssa::CallBoundarySlot::Register {
                                index: 0,
                                storage: actual,
                            } if actual == *storage
                        ) && operand.physical_width_bits() == ty.width_bits()
                            && self.region.operand_is_grounded_before_return(*operand)
                    })
                    .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
                Some(expressions.render_return_operand_with_helpers(operand, &mut helpers)?)
            }
            _ => return Err(CertifiedSemanticCFunctionError::MissingReturnedEntity),
        };
        writeln!(
            &mut output,
            "\t{}",
            render_logical_return_statement(interface, return_value.as_deref(), &mut helpers)?
        )
        .expect("String writes cannot fail");
        output.push_str("}\n");
        insert_semantic_c_helpers(&mut output, helper_insertion, &helpers);
        Ok(output)
    }
}
