//! Closed terminal-return regions built from origin-bearing accounting.

use r2cert::{
    CERTIFIED_TERMINAL_RETURN_REGION_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedFramePreservation, CertifiedSourceTerminator, CertifiedTypedRegionKind,
    LedgerClosureError, TypedRegionMapping, certify_terminal_return_region_with_frame,
};
use r2ssa::{CanonicalInstructionId, MachineValueBinding, SemanticObligationKind};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionObligationDisposition,
    TypedOutputSealError,
};
use crate::semantic_c::{
    SemanticCExprId, SemanticCFunctionReturn, SemanticCReturn, SemanticCReturnOperand,
};
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
    typed_output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminalReturnRegionError {
    Statement(SemanticCStatementError),
    ResidualObligations,
    MissingFunctionInterface,
    FramePreservationMismatch,
    NotTerminalReturn,
    InvalidReturnCardinality,
    ReturnIsNotFinalStep,
    LedgerClosure(LedgerClosureError),
    TypedOutputSeal(TypedOutputSealError),
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

impl From<LedgerClosureError> for TerminalReturnRegionError {
    fn from(error: LedgerClosureError) -> Self {
        Self::LedgerClosure(error)
    }
}

impl From<TypedOutputSealError> for TerminalReturnRegionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
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

fn frame_preservation_matches_accounting(
    accounting: &CertifiedSingleBlockAccounting,
    frame_preservation: Option<&CertifiedFramePreservation>,
) -> bool {
    let authority = accounting.expression_layer().frame_mechanics().authority();
    match (authority, frame_preservation) {
        (None, None) => true,
        (Some(authority), Some(frame)) => {
            frame.origin() == accounting.origin()
                && frame.frame_pointer_storage() == authority.frame_pointer_storage()
                && frame.saved_range() == authority.saved_range()
                && frame
                    .restores()
                    .iter()
                    .map(|restore| restore.return_control().producer())
                    .eq(authority.return_order().iter().copied())
        }
        _ => false,
    }
}

fn producer_precedes_return_in_block(
    source_order: &[CanonicalInstructionId],
    producer: CanonicalInstructionId,
    return_producer: CanonicalInstructionId,
) -> bool {
    if producer.block_addr != return_producer.block_addr {
        return false;
    }
    let exact_position = |expected| {
        let mut positions = source_order
            .iter()
            .enumerate()
            .filter_map(|(position, source)| (*source == expected).then_some(position));
        let position = positions.next()?;
        positions.next().is_none().then_some(position)
    };
    let producer_position = exact_position(producer);
    let return_position = exact_position(return_producer);
    matches!((producer_position, return_position), (Some(value), Some(ret)) if value < ret)
}

fn component_is_grounded_before_return(
    layer: &SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
    producer: CanonicalInstructionId,
    binding: MachineValueBinding,
    expression: SemanticCExprId,
) -> bool {
    let source_order = layer
        .steps()
        .iter()
        .map(|step| step.source())
        .collect::<Vec<_>>();
    producer_precedes_return_in_block(&source_order, producer, return_producer)
        && layer.steps().iter().any(|step| {
            step.source() == producer
                && step.value().is_some_and(|reference| {
                    layer.resolve_value(reference).is_some_and(|entity| {
                        entity.producer() == producer
                            && entity.output() == binding
                            && entity.root() == expression
                    })
                })
        })
}

fn return_operand_is_grounded_before_return(
    layer: &SemanticCBlockStepLayer,
    return_producer: CanonicalInstructionId,
    operand: SemanticCReturnOperand<'_>,
) -> bool {
    match operand {
        SemanticCReturnOperand::Direct(value) => component_is_grounded_before_return(
            layer,
            return_producer,
            value.producer(),
            value.binding(),
            value.expression(),
        ),
        SemanticCReturnOperand::RegisterComposition(composition) => {
            component_is_grounded_before_return(
                layer,
                return_producer,
                composition.base().producer(),
                composition.base().binding(),
                composition.base().expression(),
            ) && composition.overlays().iter().all(|overlay| {
                component_is_grounded_before_return(
                    layer,
                    return_producer,
                    overlay.definition().producer(),
                    overlay.definition().binding(),
                    overlay.definition().expression(),
                )
            })
        }
    }
}

impl CertifiedTerminalReturnBlockRegion {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
        frame_preservation: Option<&CertifiedFramePreservation>,
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
        if !frame_preservation_matches_accounting(&accounting, frame_preservation) {
            return Err(TerminalReturnRegionError::FramePreservationMismatch);
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
        let ledger_closure = certify_terminal_return_region_with_frame(
            layer.accounting().origin(),
            layer.accounting().ledger(),
            mappings,
            frame_preservation,
        )?;
        let typed_output_seal = CertifiedTypedOutputSeal::new(
            ledger_closure,
            CertifiedTypedRegionKind::TerminalReturnBlock,
            CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION,
            [layer.accounting()],
        )?;
        let region = Self {
            schema_version: CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION,
            scope: TerminalReturnRegionScope::ClosedSingleBlockReturn,
            origin: layer.accounting().origin().clone(),
            layer,
            return_producer,
            typed_output_seal,
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

    pub fn returned(&self) -> Option<&SemanticCReturn> {
        self.layer
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == self.return_producer)
    }

    pub(crate) fn operand_is_grounded_before_return(
        &self,
        operand: SemanticCReturnOperand<'_>,
    ) -> bool {
        return_operand_is_grounded_before_return(&self.layer, self.return_producer, operand)
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
        if !self.typed_output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::TerminalReturnBlock,
            CERTIFIED_TERMINAL_RETURN_REGION_SCHEMA_VERSION,
            [accounting],
        ) {
            invalid.push("terminal return typed-output seal does not match region".to_string());
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
            let returned = returned[0];
            let interface_matches = match interface.return_kind() {
                SemanticCFunctionReturn::Void => {
                    returned.values().is_empty() && returned.register_compositions().is_empty()
                }
                SemanticCFunctionReturn::Register { storage, ty } => {
                    returned.single_operand().is_some_and(|operand| {
                        matches!(
                            operand.slot(),
                            r2ssa::CallBoundarySlot::Register {
                                index: 0,
                                storage: actual,
                            } if actual == *storage
                        ) && operand.physical_width_bits() == ty.width_bits()
                            && self.operand_is_grounded_before_return(operand)
                    })
                }
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
    use r2ssa::CanonicalInstructionSite;

    fn id(block_addr: u64, ordinal: u64) -> CanonicalInstructionId {
        CanonicalInstructionId {
            block_addr,
            site: CanonicalInstructionSite::Op(ordinal),
        }
    }

    #[test]
    fn composed_return_components_require_exact_same_block_precedence() {
        let base = id(0x1000, 0);
        let overlay = id(0x1000, 1);
        let returned = id(0x1000, 2);
        let order = [base, overlay, returned];
        assert!(producer_precedes_return_in_block(&order, base, returned));
        assert!(producer_precedes_return_in_block(&order, overlay, returned));
        assert!(!producer_precedes_return_in_block(
            &order, returned, returned
        ));
        assert!(!producer_precedes_return_in_block(
            &order,
            id(0x1000, 9),
            returned
        ));
        assert!(!producer_precedes_return_in_block(
            &order,
            id(0x2000, 0),
            returned
        ));
        assert!(!producer_precedes_return_in_block(
            &[base, returned, overlay],
            overlay,
            returned
        ));
    }

    #[test]
    fn duplicate_component_or_return_steps_cannot_satisfy_precedence() {
        let base = id(0x1000, 0);
        let returned = id(0x1000, 1);
        assert!(!producer_precedes_return_in_block(
            &[base, base, returned],
            base,
            returned
        ));
        assert!(!producer_precedes_return_in_block(
            &[base, returned, returned],
            base,
            returned
        ));
    }
}
