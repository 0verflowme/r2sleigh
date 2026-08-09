//! Fully authorized semantic-C functions for the currently admitted subset.

use std::fmt::Write as _;

use r2cert::CertifiedMachineProjection;
use r2ssa::{MachineBuildError, TrustedSsaArtifact};
use serde::Serialize;

use crate::certified_region::{CertifiedSingleBlockAccounting, RegionBuildError};
use crate::certified_return::{CertifiedTerminalReturnBlockRegion, TerminalReturnRegionError};
use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCFunctionReturn, SemanticCInputOrigin,
    storage_type, value_name,
};

pub const CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 = 2;

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
        let region = CertifiedTerminalReturnBlockRegion::from_accounting(accounting)?;
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
        if let [value] = returned.values() {
            let return_position = region
                .layer()
                .steps()
                .iter()
                .position(|step| step.source() == region.return_producer())
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            let value_position = region
                .layer()
                .steps()
                .iter()
                .position(|step| {
                    step.value().is_some_and(|reference| {
                        region
                            .layer()
                            .resolve_value(reference)
                            .is_some_and(|entity| entity.output() == value.binding())
                    })
                })
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            if value_position >= return_position {
                return Err(CertifiedSemanticCFunctionError::MissingReturnedEntity);
            }
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

    /// Render the authorized unsigned-carrier C11 subset. Recovered source
    /// types and cosmetic names are deliberately not consulted.
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
        let return_type = match interface.return_kind() {
            SemanticCFunctionReturn::Void => "void",
            SemanticCFunctionReturn::Register { ty, .. } => storage_type(ty)?,
        };
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
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
        for step in self.region.layer().steps() {
            let Some(reference) = step.value() else {
                continue;
            };
            let entity = self
                .region
                .layer()
                .resolve_value(reference)
                .ok_or(CertifiedSemanticCFunctionError::MissingReturnedEntity)?;
            let expression = expressions.render_expr(entity.root())?;
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
        match returned.values() {
            [] => output.push_str("\treturn;\n"),
            [value] => writeln!(&mut output, "\treturn {};", value_name(value.binding()))
                .expect("String writes cannot fail"),
            _ => return Err(CertifiedSemanticCFunctionError::MissingReturnedEntity),
        }
        output.push_str("}\n");
        Ok(output)
    }
}
