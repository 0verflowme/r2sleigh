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
