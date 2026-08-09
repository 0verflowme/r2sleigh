//! Proof-preserving local direct, conditional, and fallthrough fragments.
//!
//! This is deliberately not a function-level or executable-C certificate. It
//! retains exact source-order accounting for one selected block and proves only
//! its terminal transfer on normal body completion. Successors remain open
//! composition ports.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{CertifiedConditionalControl, CertifiedDirectControl};
use r2ssa::{SemanticObligationId, SemanticObligationKind};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionObligationDisposition, RegionObligationMapping,
};
use crate::semantic_c::SemanticCIdentityScope;
use crate::semantic_stmt::{
    SemanticCBlockStepLayer, SemanticCStatementError, SemanticCStatementScope,
};

pub const CERTIFIED_DIRECT_TRANSFER_REGION_SCHEMA_VERSION: u32 = 2;
pub const CERTIFIED_CONDITIONAL_TRANSFER_REGION_SCHEMA_VERSION: u32 = 1;
pub const CERTIFIED_FALLTHROUGH_TRANSFER_REGION_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum DirectTransferRegionScope {
    SingleBlockNormalCompletionToOneStaticSuccessor,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDirectTransferBlockRegion {
    schema_version: u32,
    scope: DirectTransferRegionScope,
    identity_scope: SemanticCIdentityScope,
    body: SemanticCBlockStepLayer,
    transfer: CertifiedDirectControl,
    mappings: Box<[RegionObligationMapping]>,
    open_successor: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectTransferRegionError {
    InvalidAccounting,
    StatementLayer(SemanticCStatementError),
    MissingOrAmbiguousTransfer,
    InvalidConstructedRegion(Vec<String>),
}

impl std::fmt::Display for DirectTransferRegionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "direct-transfer region construction failed: {self:?}")
    }
}

impl std::error::Error for DirectTransferRegionError {}

impl From<SemanticCStatementError> for DirectTransferRegionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::StatementLayer(error)
    }
}

impl CertifiedDirectTransferBlockRegion {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, DirectTransferRegionError> {
        if !accounting.audit().has_exact_source_accounting() {
            return Err(DirectTransferRegionError::InvalidAccounting);
        }
        if !accounting.conditional_controls().is_empty() {
            return Err(DirectTransferRegionError::MissingOrAmbiguousTransfer);
        }
        let [transfer] = accounting.direct_controls() else {
            return Err(DirectTransferRegionError::MissingOrAmbiguousTransfer);
        };
        let transfer = transfer.clone();
        let mappings = accounting.mappings().to_vec().into_boxed_slice();
        let open_successor = transfer.target();
        let body = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let region = Self {
            schema_version: CERTIFIED_DIRECT_TRANSFER_REGION_SCHEMA_VERSION,
            scope: DirectTransferRegionScope::SingleBlockNormalCompletionToOneStaticSuccessor,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            body,
            transfer,
            mappings,
            open_successor,
        };
        let report = region.audit();
        if !report.has_exact_direct_transfer_accounting() {
            return Err(DirectTransferRegionError::InvalidConstructedRegion(
                report.invalid,
            ));
        }
        Ok(region)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> DirectTransferRegionScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn body(&self) -> &SemanticCBlockStepLayer {
        &self.body
    }

    pub const fn transfer(&self) -> &CertifiedDirectControl {
        &self.transfer
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn open_successor(&self) -> u64 {
        self.open_successor
    }

    /// Whether selected source obligations remain residual. The open successor
    /// is unresolved regardless of this result.
    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.body.accounting().audit().has_residuals()
    }

    pub fn audit(&self) -> DirectTransferRegionAuditReport {
        let accounting = self.body.accounting();
        let body_report = self.body.audit();
        let accounting_report = accounting.audit();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_DIRECT_TRANSFER_REGION_SCHEMA_VERSION {
            invalid.push("direct-transfer region schema mismatch".to_string());
        }
        if self.scope != DirectTransferRegionScope::SingleBlockNormalCompletionToOneStaticSuccessor
        {
            invalid.push("direct-transfer region scope mismatch".to_string());
        }
        if self.identity_scope != accounting.identity_scope()
            || self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
        {
            invalid.push("direct-transfer identity scope mismatch".to_string());
        }
        if self.body.scope()
            != SemanticCStatementScope::SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit
            || !body_report.has_exact_source_order()
            || !accounting_report.has_exact_source_accounting()
        {
            invalid.push("embedded source-ordered body is not exact".to_string());
        }
        if self.mappings.as_ref() != accounting.mappings() {
            invalid.push("final mappings differ from certified block accounting".to_string());
        }
        if accounting.direct_controls() != [self.transfer.clone()]
            || accounting.direct_control_for_producer(self.transfer.producer())
                != Some(&self.transfer)
            || !accounting.conditional_controls().is_empty()
        {
            invalid.push("direct transfer differs from retained accounting evidence".to_string());
        }

        let source_block = accounting.source_block();
        let expected_source = source_block.and_then(|block| block.instructions().last().copied());
        let topology_matches = source_block.is_some_and(|block| {
            matches!(
                block.terminator(),
                r2cert::CertifiedSourceTerminator::Branch { target }
                    if *target == self.open_successor
                        && *target == self.transfer.target()
            ) && block.successors() == [self.open_successor]
                && accounting.topology().block(self.open_successor).is_some()
                && block.addr() != self.open_successor
        });
        if !topology_matches
            || expected_source != Some(self.transfer.producer())
            || self.body.steps().last().map(|step| step.source()) != expected_source
        {
            invalid.push("direct transfer does not match the terminal topology step".to_string());
        }

        let control_mappings = self
            .mappings
            .iter()
            .filter(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
            })
            .collect::<Vec<_>>();
        let transfer_mapping_matches = matches!(
            control_mappings.as_slice(),
            [mapping]
                if mapping.obligation() == self.transfer.source_obligation()
                    && mapping.obligation().kind == SemanticObligationKind::ControlTransfer
                    && matches!(
                        mapping.disposition(),
                        RegionObligationDisposition::AbsorbedIntoControl { producer }
                            if *producer == self.transfer.producer()
                    )
        );
        if !transfer_mapping_matches {
            invalid.push("direct transfer does not own exactly one control mapping".to_string());
        }

        let expected = accounting
            .mappings()
            .iter()
            .map(RegionObligationMapping::obligation)
            .collect::<BTreeSet<_>>();
        let counts = counts(
            self.mappings
                .iter()
                .map(RegionObligationMapping::obligation),
        );
        let missing = expected
            .iter()
            .copied()
            .filter(|id| !counts.contains_key(id))
            .collect();
        let duplicate = counts
            .iter()
            .filter_map(|(id, count)| (*count > 1).then_some(*id))
            .collect();
        let unexpected = counts
            .keys()
            .copied()
            .filter(|id| !expected.contains(id))
            .collect();

        DirectTransferRegionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            remaining_obligation_residuals: accounting_report.has_residuals(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DirectTransferRegionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    remaining_obligation_residuals: bool,
}

impl DirectTransferRegionAuditReport {
    pub fn has_exact_direct_transfer_accounting(&self) -> bool {
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

    /// Whether selected source obligations remain residual. This says nothing
    /// about the still-open successor port.
    pub const fn has_remaining_obligation_residuals(&self) -> bool {
        self.remaining_obligation_residuals
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ConditionalTransferRegionScope {
    SingleBlockNormalCompletionToTwoArmLabeledStaticSuccessors,
}

/// One exact terminal conditional transfer with two arm-labelled open ports.
///
/// This proves only predicate selection and transfer on normal completion of
/// the retained source-ordered body. It does not own either successor, prove a
/// join or `if` region, establish return behavior, or authorize executable C.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalTransferBlockRegion {
    schema_version: u32,
    scope: ConditionalTransferRegionScope,
    identity_scope: SemanticCIdentityScope,
    body: SemanticCBlockStepLayer,
    transfer: CertifiedConditionalControl,
    mappings: Box<[RegionObligationMapping]>,
    open_true_successor: u64,
    open_false_successor: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionalTransferRegionError {
    InvalidAccounting,
    StatementLayer(SemanticCStatementError),
    MissingOrAmbiguousTransfer,
    InvalidConstructedRegion(Vec<String>),
}

impl std::fmt::Display for ConditionalTransferRegionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "conditional-transfer region construction failed: {self:?}"
        )
    }
}

impl std::error::Error for ConditionalTransferRegionError {}

impl From<SemanticCStatementError> for ConditionalTransferRegionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::StatementLayer(error)
    }
}

impl CertifiedConditionalTransferBlockRegion {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, ConditionalTransferRegionError> {
        if !accounting.audit().has_exact_source_accounting() {
            return Err(ConditionalTransferRegionError::InvalidAccounting);
        }
        if !accounting.direct_controls().is_empty() {
            return Err(ConditionalTransferRegionError::MissingOrAmbiguousTransfer);
        }
        let [transfer] = accounting.conditional_controls() else {
            return Err(ConditionalTransferRegionError::MissingOrAmbiguousTransfer);
        };
        let transfer = transfer.clone();
        let mappings = accounting.mappings().to_vec().into_boxed_slice();
        let open_true_successor = transfer.true_target();
        let open_false_successor = transfer.false_target();
        let body = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let region = Self {
            schema_version: CERTIFIED_CONDITIONAL_TRANSFER_REGION_SCHEMA_VERSION,
            scope: ConditionalTransferRegionScope::SingleBlockNormalCompletionToTwoArmLabeledStaticSuccessors,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            body,
            transfer,
            mappings,
            open_true_successor,
            open_false_successor,
        };
        let report = region.audit();
        if !report.has_exact_conditional_transfer_accounting() {
            return Err(ConditionalTransferRegionError::InvalidConstructedRegion(
                report.invalid,
            ));
        }
        Ok(region)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> ConditionalTransferRegionScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn body(&self) -> &SemanticCBlockStepLayer {
        &self.body
    }

    pub const fn transfer(&self) -> &CertifiedConditionalControl {
        &self.transfer
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn open_true_successor(&self) -> u64 {
        self.open_true_successor
    }

    pub const fn open_false_successor(&self) -> u64 {
        self.open_false_successor
    }

    /// Whether selected source obligations remain residual. Both successor
    /// ports remain open regardless of this result.
    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.body.accounting().audit().has_residuals()
    }

    pub fn audit(&self) -> ConditionalTransferRegionAuditReport {
        let accounting = self.body.accounting();
        let body_report = self.body.audit();
        let accounting_report = accounting.audit();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_CONDITIONAL_TRANSFER_REGION_SCHEMA_VERSION {
            invalid.push("conditional-transfer region schema mismatch".to_string());
        }
        if self.scope
            != ConditionalTransferRegionScope::SingleBlockNormalCompletionToTwoArmLabeledStaticSuccessors
        {
            invalid.push("conditional-transfer region scope mismatch".to_string());
        }
        if self.identity_scope != accounting.identity_scope()
            || self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
        {
            invalid.push("conditional-transfer identity scope mismatch".to_string());
        }
        if self.body.scope()
            != SemanticCStatementScope::SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit
            || !body_report.has_exact_source_order()
            || !accounting_report.has_exact_source_accounting()
        {
            invalid.push("embedded source-ordered body is not exact".to_string());
        }
        if self.mappings.as_ref() != accounting.mappings() {
            invalid.push("final mappings differ from certified block accounting".to_string());
        }
        if accounting.conditional_controls() != [self.transfer.clone()]
            || accounting.conditional_control_for_producer(self.transfer.producer())
                != Some(&self.transfer)
            || !accounting.direct_controls().is_empty()
        {
            invalid
                .push("conditional transfer differs from retained accounting evidence".to_string());
        }

        let source_block = accounting.source_block();
        let expected_source = source_block.and_then(|block| block.instructions().last().copied());
        let expected_successors =
            BTreeSet::from([self.open_true_successor, self.open_false_successor]);
        let topology_matches = source_block.is_some_and(|block| {
            matches!(
                block.terminator(),
                r2cert::CertifiedSourceTerminator::ConditionalBranch {
                    true_target,
                    false_target,
                } if *true_target == self.open_true_successor
                    && *false_target == self.open_false_successor
                    && *true_target == self.transfer.true_target()
                    && *false_target == self.transfer.false_target()
            ) && block.successors().len() == 2
                && block.successors().iter().copied().collect::<BTreeSet<_>>()
                    == expected_successors
                && block.addr() != self.open_true_successor
                && block.addr() != self.open_false_successor
                && self.open_true_successor != self.open_false_successor
        });
        if !topology_matches
            || expected_source != Some(self.transfer.producer())
            || self.body.steps().last().map(|step| step.source()) != expected_source
        {
            invalid
                .push("conditional transfer does not match the terminal topology step".to_string());
        }

        let control_mappings = self
            .mappings
            .iter()
            .filter(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
            })
            .collect::<Vec<_>>();
        let expected_control_obligations = self.transfer.source_obligations();
        let mapped_control_obligations = control_mappings
            .iter()
            .map(|mapping| mapping.obligation())
            .collect::<BTreeSet<_>>();
        let control_mappings_match = control_mappings.len() == 2
            && expected_control_obligations.len() == 2
            && mapped_control_obligations == expected_control_obligations
            && control_mappings.iter().all(|mapping| {
                matches!(
                    mapping.obligation().kind,
                    SemanticObligationKind::ControlPredicate
                        | SemanticObligationKind::ControlTransfer
                ) && matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { producer }
                        if *producer == self.transfer.producer()
                )
            });
        if !control_mappings_match {
            invalid.push(
                "conditional transfer does not own exactly one predicate and transfer mapping"
                    .to_string(),
            );
        }

        let expected = accounting
            .mappings()
            .iter()
            .map(RegionObligationMapping::obligation)
            .collect::<BTreeSet<_>>();
        let counts = counts(
            self.mappings
                .iter()
                .map(RegionObligationMapping::obligation),
        );
        let missing = expected
            .iter()
            .copied()
            .filter(|id| !counts.contains_key(id))
            .collect();
        let duplicate = counts
            .iter()
            .filter_map(|(id, count)| (*count > 1).then_some(*id))
            .collect();
        let unexpected = counts
            .keys()
            .copied()
            .filter(|id| !expected.contains(id))
            .collect();

        ConditionalTransferRegionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            remaining_obligation_residuals: accounting_report.has_residuals(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConditionalTransferRegionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    remaining_obligation_residuals: bool,
}

impl ConditionalTransferRegionAuditReport {
    pub fn has_exact_conditional_transfer_accounting(&self) -> bool {
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

    /// Whether selected source obligations remain residual. This says nothing
    /// about the two still-open successor ports.
    pub const fn has_remaining_obligation_residuals(&self) -> bool {
        self.remaining_obligation_residuals
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FallthroughTransferRegionScope {
    SingleBlockNormalCompletionToStructuralSuccessor,
}

/// One exact implicit fallthrough with no fabricated producer or obligation.
///
/// The open successor is certified solely from retained source topology. This
/// fragment does not turn the edge into an instruction-owned control effect,
/// own the successor, or authorize executable C.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFallthroughTransferBlockRegion {
    schema_version: u32,
    scope: FallthroughTransferRegionScope,
    identity_scope: SemanticCIdentityScope,
    body: SemanticCBlockStepLayer,
    mappings: Box<[RegionObligationMapping]>,
    open_successor: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FallthroughTransferRegionError {
    InvalidAccounting,
    StatementLayer(SemanticCStatementError),
    MissingOrInvalidFallthrough,
    InvalidConstructedRegion(Vec<String>),
}

impl std::fmt::Display for FallthroughTransferRegionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fallthrough region construction failed: {self:?}")
    }
}

impl std::error::Error for FallthroughTransferRegionError {}

impl From<SemanticCStatementError> for FallthroughTransferRegionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::StatementLayer(error)
    }
}

impl CertifiedFallthroughTransferBlockRegion {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, FallthroughTransferRegionError> {
        if !accounting.audit().has_exact_source_accounting() {
            return Err(FallthroughTransferRegionError::InvalidAccounting);
        }
        if !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || accounting.mappings().iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
            })
        {
            return Err(FallthroughTransferRegionError::MissingOrInvalidFallthrough);
        }
        let Some(source_block) = accounting.source_block() else {
            return Err(FallthroughTransferRegionError::MissingOrInvalidFallthrough);
        };
        let r2cert::CertifiedSourceTerminator::Fallthrough { next } = source_block.terminator()
        else {
            return Err(FallthroughTransferRegionError::MissingOrInvalidFallthrough);
        };
        if source_block.successors() != [*next]
            || source_block.addr() == *next
            || accounting.topology().block(*next).is_none()
        {
            return Err(FallthroughTransferRegionError::MissingOrInvalidFallthrough);
        }
        let mappings = accounting.mappings().to_vec().into_boxed_slice();
        let open_successor = *next;
        let body = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let region = Self {
            schema_version: CERTIFIED_FALLTHROUGH_TRANSFER_REGION_SCHEMA_VERSION,
            scope: FallthroughTransferRegionScope::SingleBlockNormalCompletionToStructuralSuccessor,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            body,
            mappings,
            open_successor,
        };
        let report = region.audit();
        if !report.has_exact_fallthrough_accounting() {
            return Err(FallthroughTransferRegionError::InvalidConstructedRegion(
                report.invalid,
            ));
        }
        Ok(region)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> FallthroughTransferRegionScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn body(&self) -> &SemanticCBlockStepLayer {
        &self.body
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn open_successor(&self) -> u64 {
        self.open_successor
    }

    /// Whether selected source obligations remain residual. The structural
    /// successor remains open regardless of this result.
    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.body.accounting().audit().has_residuals()
    }

    pub fn audit(&self) -> FallthroughTransferRegionAuditReport {
        let accounting = self.body.accounting();
        let body_report = self.body.audit();
        let accounting_report = accounting.audit();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_FALLTHROUGH_TRANSFER_REGION_SCHEMA_VERSION {
            invalid.push("fallthrough region schema mismatch".to_string());
        }
        if self.scope
            != FallthroughTransferRegionScope::SingleBlockNormalCompletionToStructuralSuccessor
        {
            invalid.push("fallthrough region scope mismatch".to_string());
        }
        if self.identity_scope != accounting.identity_scope()
            || self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
        {
            invalid.push("fallthrough identity scope mismatch".to_string());
        }
        if self.body.scope()
            != SemanticCStatementScope::SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit
            || !body_report.has_exact_source_order()
            || !accounting_report.has_exact_source_accounting()
        {
            invalid.push("embedded source-ordered body is not exact".to_string());
        }
        if self.mappings.as_ref() != accounting.mappings() {
            invalid.push("final mappings differ from certified block accounting".to_string());
        }
        if !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || self.mappings.iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
            })
        {
            invalid.push("fallthrough fabricates instruction-owned control evidence".to_string());
        }

        let topology_matches = accounting.source_block().is_some_and(|block| {
            matches!(
                block.terminator(),
                r2cert::CertifiedSourceTerminator::Fallthrough { next }
                    if *next == self.open_successor
            ) && block.successors() == [self.open_successor]
                && block.addr() != self.open_successor
                && accounting.topology().block(self.open_successor).is_some()
        });
        if !topology_matches {
            invalid.push("fallthrough does not match exact retained topology".to_string());
        }

        let expected = accounting
            .mappings()
            .iter()
            .map(RegionObligationMapping::obligation)
            .collect::<BTreeSet<_>>();
        let counts = counts(
            self.mappings
                .iter()
                .map(RegionObligationMapping::obligation),
        );
        let missing = expected
            .iter()
            .copied()
            .filter(|id| !counts.contains_key(id))
            .collect();
        let duplicate = counts
            .iter()
            .filter_map(|(id, count)| (*count > 1).then_some(*id))
            .collect();
        let unexpected = counts
            .keys()
            .copied()
            .filter(|id| !expected.contains(id))
            .collect();

        FallthroughTransferRegionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            remaining_obligation_residuals: accounting_report.has_residuals(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FallthroughTransferRegionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    remaining_obligation_residuals: bool,
}

impl FallthroughTransferRegionAuditReport {
    pub fn has_exact_fallthrough_accounting(&self) -> bool {
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

    /// Whether selected obligations remain residual. This says nothing about
    /// the still-open structural successor.
    pub const fn has_remaining_obligation_residuals(&self) -> bool {
        self.remaining_obligation_residuals
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2cert::CertifiedMachineProjection;
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::SsaArtifact;

    fn direct_accounting() -> CertifiedSingleBlockAccounting {
        let mut entry = R2ILBlock::new(0x7000, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x7010, 8),
        });
        let target = R2ILBlock::new(0x7010, 4);
        let artifact = SsaArtifact::raw(&[entry, target], None).expect("direct branch artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("direct branch certification");
        CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7000)
            .expect("entry accounting")
    }

    fn conditional_accounting(condition: Varnode) -> CertifiedSingleBlockAccounting {
        let mut entry = R2ILBlock::new(0x7100, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7110, 8),
            cond: condition,
        });
        let fallthrough = R2ILBlock::new(0x7104, 4);
        let taken = R2ILBlock::new(0x7110, 4);
        let artifact = SsaArtifact::raw(&[entry, fallthrough, taken], None)
            .expect("conditional branch artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("conditional branch certification");
        CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7100)
            .expect("conditional entry accounting")
    }

    fn produced_condition_accounting() -> CertifiedSingleBlockAccounting {
        let condition = Varnode::unique(0x10, 1);
        let mut entry = R2ILBlock::new(0x7120, 4);
        entry.push(R2ILOp::Copy {
            dst: condition.clone(),
            src: Varnode::constant(1, 1),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7130, 8),
            cond: condition,
        });
        let fallthrough = R2ILBlock::new(0x7124, 4);
        let taken = R2ILBlock::new(0x7130, 4);
        let artifact = SsaArtifact::raw(&[entry, fallthrough, taken], None)
            .expect("produced-condition artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("produced-condition certification");
        CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7120)
            .expect("produced-condition accounting")
    }

    fn fallthrough_accounting(with_value: bool) -> CertifiedSingleBlockAccounting {
        let mut entry = R2ILBlock::new(0x7150, 4);
        if with_value {
            entry.push(R2ILOp::Copy {
                dst: Varnode::unique(0x10, 1),
                src: Varnode::constant(1, 1),
            });
        }
        let mut successor = R2ILBlock::new(0x7154, 4);
        successor.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let artifact =
            SsaArtifact::raw(&[entry, successor], None).expect("fallthrough source artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("fallthrough source certification");
        CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7150)
            .expect("fallthrough accounting")
    }

    #[test]
    fn direct_transfer_region_retains_one_open_successor_without_whole_function_claim() {
        let region = CertifiedDirectTransferBlockRegion::from_accounting(direct_accounting())
            .expect("direct transfer region");
        let report = region.audit();

        assert!(report.has_exact_direct_transfer_accounting(), "{report:?}");
        assert!(!report.has_remaining_obligation_residuals(), "{report:?}");
        assert_eq!(region.open_successor(), 0x7010);
        assert_eq!(region.transfer().target(), 0x7010);
        assert!(region.body().audit().requires_control_region());
        assert_eq!(region.mappings().len(), 1);
        assert!(matches!(
            region.mappings()[0].disposition(),
            RegionObligationDisposition::AbsorbedIntoControl { .. }
        ));
    }

    #[test]
    fn fallthrough_and_conditional_blocks_do_not_form_direct_transfer_regions() {
        let empty = R2ILBlock::new(0x7020, 4);
        let successor = R2ILBlock::new(0x7024, 4);
        let artifact = SsaArtifact::raw(&[empty, successor], None).expect("fallthrough artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("fallthrough certification");
        let accounting = CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7020)
            .expect("fallthrough accounting");
        assert!(matches!(
            CertifiedDirectTransferBlockRegion::from_accounting(accounting),
            Err(DirectTransferRegionError::MissingOrAmbiguousTransfer)
        ));

        let mut entry = R2ILBlock::new(0x7030, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7040, 8),
            cond: Varnode::constant(1, 1),
        });
        let fallthrough = R2ILBlock::new(0x7034, 4);
        let taken = R2ILBlock::new(0x7040, 4);
        let artifact =
            SsaArtifact::raw(&[entry, fallthrough, taken], None).expect("conditional artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("conditional certification");
        let accounting = CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7030)
            .expect("conditional accounting");
        assert!(matches!(
            CertifiedDirectTransferBlockRegion::from_accounting(accounting),
            Err(DirectTransferRegionError::MissingOrAmbiguousTransfer)
        ));
    }

    #[test]
    fn direct_transfer_region_mutations_fail_audit() {
        let region = CertifiedDirectTransferBlockRegion::from_accounting(direct_accounting())
            .expect("direct transfer region");

        let mut corrupted = region.clone();
        corrupted.schema_version += 1;
        assert!(!corrupted.audit().has_exact_direct_transfer_accounting());
        let mut corrupted = region.clone();
        corrupted.open_successor += 4;
        assert!(!corrupted.audit().has_exact_direct_transfer_accounting());
        let mut corrupted = region.clone();
        corrupted.mappings = Box::new([]);
        assert!(!corrupted.audit().has_exact_direct_transfer_accounting());
        let mut corrupted = region;
        let mapping = corrupted.mappings[0].clone();
        corrupted.mappings = vec![mapping.clone(), mapping].into_boxed_slice();
        assert!(!corrupted.audit().has_exact_direct_transfer_accounting());
    }

    #[test]
    fn conditional_transfer_region_retains_two_arm_labeled_open_successors() {
        let region = CertifiedConditionalTransferBlockRegion::from_accounting(
            conditional_accounting(Varnode::constant(1, 1)),
        )
        .expect("conditional transfer region");
        let report = region.audit();

        assert!(
            report.has_exact_conditional_transfer_accounting(),
            "{report:?}"
        );
        assert!(!report.has_remaining_obligation_residuals(), "{report:?}");
        assert_eq!(region.open_true_successor(), 0x7110);
        assert_eq!(region.open_false_successor(), 0x7104);
        assert_eq!(region.transfer().true_target(), 0x7110);
        assert_eq!(region.transfer().false_target(), 0x7104);
        assert!(region.body().audit().requires_control_region());
        assert_eq!(
            region
                .mappings()
                .iter()
                .filter(|mapping| matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                ))
                .count(),
            2
        );
    }

    #[test]
    fn produced_condition_is_grounded_in_the_exact_expression_entity() {
        let region = CertifiedConditionalTransferBlockRegion::from_accounting(
            produced_condition_accounting(),
        )
        .expect("produced-condition transfer region");
        let condition_producer = region
            .transfer()
            .condition()
            .producer()
            .expect("produced condition");
        let entity = region
            .body()
            .accounting()
            .expression_layer()
            .entity_for_producer(condition_producer)
            .expect("condition expression entity");

        assert_eq!(entity.output(), region.transfer().condition().binding());
        assert!(region.audit().has_exact_conditional_transfer_accounting());
    }

    #[test]
    fn direct_and_fallthrough_blocks_do_not_form_conditional_transfer_regions() {
        assert!(matches!(
            CertifiedConditionalTransferBlockRegion::from_accounting(direct_accounting()),
            Err(ConditionalTransferRegionError::MissingOrAmbiguousTransfer)
        ));

        let empty = R2ILBlock::new(0x7140, 4);
        let successor = R2ILBlock::new(0x7144, 4);
        let artifact = SsaArtifact::raw(&[empty, successor], None).expect("fallthrough artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("fallthrough certification");
        let accounting = CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x7140)
            .expect("fallthrough accounting");
        assert!(matches!(
            CertifiedConditionalTransferBlockRegion::from_accounting(accounting),
            Err(ConditionalTransferRegionError::MissingOrAmbiguousTransfer)
        ));
    }

    #[test]
    fn conditional_transfer_region_mutations_and_foreign_proof_fail_audit() {
        let region = CertifiedConditionalTransferBlockRegion::from_accounting(
            conditional_accounting(Varnode::constant(1, 1)),
        )
        .expect("conditional transfer region");

        let mut corrupted = region.clone();
        corrupted.schema_version += 1;
        assert!(
            !corrupted
                .audit()
                .has_exact_conditional_transfer_accounting()
        );
        let mut corrupted = region.clone();
        std::mem::swap(
            &mut corrupted.open_true_successor,
            &mut corrupted.open_false_successor,
        );
        assert!(
            !corrupted
                .audit()
                .has_exact_conditional_transfer_accounting()
        );
        let mut corrupted = region.clone();
        corrupted.open_true_successor = corrupted.open_false_successor;
        assert!(
            !corrupted
                .audit()
                .has_exact_conditional_transfer_accounting()
        );
        let mut corrupted = region.clone();
        corrupted.mappings = Box::new([]);
        assert!(
            !corrupted
                .audit()
                .has_exact_conditional_transfer_accounting()
        );
        let mut corrupted = region.clone();
        let mapping = corrupted.mappings[0].clone();
        corrupted.mappings = vec![mapping.clone(), mapping].into_boxed_slice();
        assert!(
            !corrupted
                .audit()
                .has_exact_conditional_transfer_accounting()
        );

        let foreign = CertifiedConditionalTransferBlockRegion::from_accounting(
            conditional_accounting(Varnode::constant(0, 1)),
        )
        .expect("foreign conditional transfer region");
        let mut corrupted = region;
        corrupted.transfer = foreign.transfer;
        assert!(
            !corrupted
                .audit()
                .has_exact_conditional_transfer_accounting()
        );
    }

    #[test]
    fn empty_and_value_blocks_form_topology_only_fallthrough_regions() {
        for with_value in [false, true] {
            let region = CertifiedFallthroughTransferBlockRegion::from_accounting(
                fallthrough_accounting(with_value),
            )
            .expect("fallthrough region");
            let report = region.audit();

            assert!(report.has_exact_fallthrough_accounting(), "{report:?}");
            assert_eq!(report.has_remaining_obligation_residuals(), with_value);
            assert_eq!(region.open_successor(), 0x7154);
            assert!(region.body().audit().requires_control_region());
            assert!(region.body().accounting().direct_controls().is_empty());
            assert!(region.body().accounting().conditional_controls().is_empty());
            assert!(region.mappings().iter().all(|mapping| !matches!(
                mapping.disposition(),
                RegionObligationDisposition::AbsorbedIntoControl { .. }
            )));
        }
    }

    #[test]
    fn explicit_control_and_unresolved_last_block_do_not_form_fallthrough_regions() {
        for accounting in [
            direct_accounting(),
            conditional_accounting(Varnode::constant(1, 1)),
        ] {
            assert!(matches!(
                CertifiedFallthroughTransferBlockRegion::from_accounting(accounting),
                Err(FallthroughTransferRegionError::MissingOrInvalidFallthrough)
            ));
        }

        let block = R2ILBlock::new(0x7170, 4);
        let artifact = SsaArtifact::raw(&[block], None).expect("last empty block artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("last empty block certification");
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("last empty block accounting");
        assert!(matches!(
            CertifiedFallthroughTransferBlockRegion::from_accounting(accounting),
            Err(FallthroughTransferRegionError::MissingOrInvalidFallthrough)
        ));
    }

    #[test]
    fn fallthrough_region_mutations_fail_audit() {
        let region =
            CertifiedFallthroughTransferBlockRegion::from_accounting(fallthrough_accounting(true))
                .expect("fallthrough region");

        let mut corrupted = region.clone();
        corrupted.schema_version += 1;
        assert!(!corrupted.audit().has_exact_fallthrough_accounting());
        let mut corrupted = region.clone();
        corrupted.open_successor += 4;
        assert!(!corrupted.audit().has_exact_fallthrough_accounting());
        let mut corrupted = region.clone();
        corrupted.mappings = Box::new([]);
        assert!(!corrupted.audit().has_exact_fallthrough_accounting());
        let mut corrupted = region;
        let mapping = corrupted.mappings[0].clone();
        corrupted.mappings = vec![mapping.clone(), mapping].into_boxed_slice();
        assert!(!corrupted.audit().has_exact_fallthrough_accounting());
    }
}
