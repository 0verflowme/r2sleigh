//! Closed terminal-return regions built from origin-bearing accounting.

use r2cert::{
    CERTIFIED_TERMINAL_RETURN_REGION_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedRenderPermit, CertifiedSourceTerminator, CertifiedTypedRegionKind,
    RenderAuthorizationError, TypedRegionMapping, certify_terminal_return_region,
};
use r2ssa::{CanonicalInstructionId, SemanticObligationKind};
use serde::Serialize;

use crate::certified_region::{CertifiedSingleBlockAccounting, RegionObligationDisposition};
use crate::semantic_c::{SemanticCFunctionReturn, SemanticCReturn};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION: u32 =
    CERTIFIED_TERMINAL_RETURN_REGION_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum TerminalReturnRegionScope {
    ClosedSingleBlockReturn,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedTerminalReturnBlockRegion {
    schema_version: u32,
    scope: TerminalReturnRegionScope,
    origin: CertifiedArtifactOrigin,
    layer: SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
    render_permit: CertifiedRenderPermit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminalReturnRegionError {
    Statement(SemanticCStatementError),
    ResidualObligations,
    MissingFunctionInterface,
    NotTerminalReturn,
    InvalidReturnCardinality,
    ReturnIsNotFinalStep,
    Authorization(RenderAuthorizationError),
    InvalidConstructedRegion(Vec<String>),
}

impl std::fmt::Display for TerminalReturnRegionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "terminal return region construction failed: {self:?}")
    }
}

impl std::error::Error for TerminalReturnRegionError {}

impl From<SemanticCStatementError> for TerminalReturnRegionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<RenderAuthorizationError> for TerminalReturnRegionError {
    fn from(error: RenderAuthorizationError) -> Self {
        Self::Authorization(error)
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

impl CertifiedTerminalReturnBlockRegion {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, TerminalReturnRegionError> {
        let report = accounting.audit();
        if !report.has_exact_source_accounting() {
            return Err(TerminalReturnRegionError::Statement(
                SemanticCStatementError::InvalidAccounting,
            ));
        }
        if report.has_residuals() {
            return Err(TerminalReturnRegionError::ResidualObligations);
        }
        if accounting.expression_layer().function_interface().is_none() {
            return Err(TerminalReturnRegionError::MissingFunctionInterface);
        }
        let Some(block) = accounting.source_block() else {
            return Err(TerminalReturnRegionError::NotTerminalReturn);
        };
        if !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            return Err(TerminalReturnRegionError::NotTerminalReturn);
        }
        let [returned] = accounting.semantic_returns() else {
            return Err(TerminalReturnRegionError::InvalidReturnCardinality);
        };
        if accounting.return_controls().len() != 1 {
            return Err(TerminalReturnRegionError::InvalidReturnCardinality);
        }
        let return_producer = returned.producer();
        if block.instructions().last() != Some(&return_producer) {
            return Err(TerminalReturnRegionError::ReturnIsNotFinalStep);
        }
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        if layer.steps().last().map(|step| step.source()) != Some(return_producer) {
            return Err(TerminalReturnRegionError::ReturnIsNotFinalStep);
        }
        let mappings = typed_region_mappings(layer.accounting());
        let render_permit = certify_terminal_return_region(
            layer.accounting().origin(),
            layer.accounting().ledger(),
            mappings,
        )?;
        let region = Self {
            schema_version: CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION,
            scope: TerminalReturnRegionScope::ClosedSingleBlockReturn,
            origin: layer.accounting().origin().clone(),
            layer,
            return_producer,
            render_permit,
        };
        let report = region.audit();
        if !report.has_exact_terminal_return() {
            return Err(TerminalReturnRegionError::InvalidConstructedRegion(
                report.invalid,
            ));
        }
        Ok(region)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> TerminalReturnRegionScope {
        self.scope
    }

    pub const fn layer(&self) -> &SemanticCBlockStepLayer {
        &self.layer
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn return_producer(&self) -> CanonicalInstructionId {
        self.return_producer
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

    pub fn audit(&self) -> TerminalReturnRegionAuditReport {
        let mut invalid = Vec::new();
        let statement_report = self.layer.audit();
        let accounting = self.layer.accounting();
        let accounting_report = accounting.audit();
        if self.schema_version != CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION {
            invalid.push("terminal return schema mismatch".to_string());
        }
        if self.scope != TerminalReturnRegionScope::ClosedSingleBlockReturn {
            invalid.push("terminal return scope mismatch".to_string());
        }
        if self.origin != *accounting.origin() {
            invalid.push("terminal return origin does not match nested accounting".to_string());
        }
        let mappings = typed_region_mappings(accounting);
        if !self.render_permit.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::TerminalReturnBlock,
            CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION,
            &mappings,
        ) {
            invalid.push("terminal return render permit does not match region".to_string());
        }
        if !statement_report.has_exact_source_order()
            || !accounting_report.has_exact_source_accounting()
        {
            invalid.push("nested source accounting is not exact".to_string());
        }
        if accounting_report.has_residuals() {
            invalid.push("terminal return region retains residual obligations".to_string());
        }
        let Some(interface) = accounting.expression_layer().function_interface() else {
            invalid.push("terminal return lacks an explicit function interface".to_string());
            return TerminalReturnRegionAuditReport { invalid };
        };
        let source_is_terminal_return = accounting.source_block().is_some_and(|block| {
            matches!(block.terminator(), CertifiedSourceTerminator::Return)
                && block.successors().is_empty()
                && block.instructions().last() == Some(&self.return_producer)
        });
        if !source_is_terminal_return
            || self.layer.steps().last().map(|step| step.source()) != Some(self.return_producer)
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            invalid.push("return is not the exact closed block terminator".to_string());
        }
        let returned = accounting
            .semantic_returns()
            .iter()
            .filter(|returned| returned.producer() == self.return_producer)
            .collect::<Vec<_>>();
        let controls = accounting
            .return_controls()
            .iter()
            .filter(|control| control.producer() == self.return_producer)
            .collect::<Vec<_>>();
        if returned.len() != 1
            || controls.len() != 1
            || accounting.semantic_returns().len() != 1
            || accounting.return_controls().len() != 1
        {
            invalid.push("return evidence cardinality mismatch".to_string());
        } else {
            let expected = returned[0].source_obligations();
            let mapped = accounting
                .mappings()
                .iter()
                .filter_map(|mapping| {
                    matches!(
                        mapping.disposition(),
                        RegionObligationDisposition::AbsorbedIntoReturn { producer }
                            if *producer == self.return_producer
                    )
                    .then_some(mapping.obligation())
                })
                .collect::<std::collections::BTreeSet<_>>();
            if &mapped != expected
                || mapped.iter().any(|obligation| {
                    !matches!(
                        obligation.kind,
                        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
                    )
                })
            {
                invalid.push("return obligation mapping mismatch".to_string());
            }
            let interface_matches = match (interface.return_kind(), returned[0].values()) {
                (SemanticCFunctionReturn::Void, []) => true,
                (SemanticCFunctionReturn::Register { storage, .. }, [value]) => matches!(
                    value.slot(),
                    r2ssa::CallBoundarySlot::Register {
                        index: 0,
                        storage: actual,
                    } if actual == *storage
                ),
                _ => false,
            };
            if !interface_matches {
                invalid.push("semantic return does not match function interface".to_string());
            }
        }
        TerminalReturnRegionAuditReport { invalid }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TerminalReturnRegionAuditReport {
    invalid: Vec<String>,
}

impl TerminalReturnRegionAuditReport {
    pub fn has_exact_terminal_return(&self) -> bool {
        self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2cert::CertifiedMachineProjection;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SsaArtifact,
    };

    fn accounting(return_kind: SourceFunctionReturn) -> CertifiedSingleBlockAccounting {
        let mut block = R2ILBlock::new(0x7100, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(8, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let mut arch = ArchSpec::new("terminal-return-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        let interface = SourceFunctionInterface::new(
            b"terminal-return-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(
                0,
                CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset: 8,
                    size: 8,
                },
            )],
            return_kind,
            [],
        )
        .expect("explicit interface");
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("terminal return artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("terminal return projection");
        CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("terminal return accounting")
    }

    fn register_return() -> SourceFunctionReturn {
        SourceFunctionReturn::Register {
            storage: CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            },
        }
    }

    #[test]
    fn exact_register_and_void_returns_form_closed_terminal_regions() {
        for return_kind in [register_return(), SourceFunctionReturn::Void] {
            let region =
                CertifiedTerminalReturnBlockRegion::from_accounting(accounting(return_kind))
                    .expect("closed return region");
            assert!(region.audit().has_exact_terminal_return());
            assert_eq!(
                region
                    .layer()
                    .accounting()
                    .audit()
                    .residualized_obligations(),
                []
            );
            assert!(region.returned().is_some());
        }
    }

    #[test]
    fn wrong_return_identity_and_foreign_return_shape_fail_audit() {
        let mut wrong =
            CertifiedTerminalReturnBlockRegion::from_accounting(accounting(register_return()))
                .expect("closed return region");
        wrong.return_producer = CanonicalInstructionId {
            block_addr: 0x7100,
            site: r2ssa::CanonicalInstructionSite::Op(0),
        };
        assert!(!wrong.audit().has_exact_terminal_return());

        let foreign_void = CertifiedTerminalReturnBlockRegion::from_accounting(accounting(
            SourceFunctionReturn::Void,
        ))
        .expect("void return region");
        let mut swapped =
            CertifiedTerminalReturnBlockRegion::from_accounting(accounting(register_return()))
                .expect("register return region");
        swapped.layer = foreign_void.layer;
        assert!(!swapped.audit().has_exact_terminal_return());
    }
}
