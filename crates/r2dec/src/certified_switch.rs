//! Topology-only switch boundary with labeled open successor ports.
//!
//! The retained witness proves a final indirect branch and exact case/default
//! topology. Its transfer remains residual because no authoritative selector
//! relation exists yet. This is not a structured or executable C `switch`.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedMachineFunction, CertifiedMachineProjection,
    CertifiedSwitchTopology,
};
use r2ssa::{SemanticObligationId, SemanticObligationKind};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionBuildError, RegionObligationDisposition,
    RegionObligationMapping, RegionResidualReason,
};
use crate::semantic_c::SemanticCIdentityScope;
use crate::semantic_stmt::{
    SemanticCBlockStepLayer, SemanticCStatementError, SemanticCStatementScope,
};

pub const CERTIFIED_SWITCH_TOPOLOGY_FRAGMENT_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SwitchTopologyFragmentScope {
    FinalIndirectBranchWithResidualTransferAndOpenLabeledPorts,
}

/// One exact switch-shaped topology boundary with no selector claim.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSwitchTopologyFragment {
    schema_version: u32,
    scope: SwitchTopologyFragmentScope,
    identity_scope: SemanticCIdentityScope,
    body: SemanticCBlockStepLayer,
    witness: CertifiedSwitchTopology,
    mappings: Box<[RegionObligationMapping]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchTopologyFragmentError {
    MissingCertifiedTopology(u64),
    Accounting(RegionBuildError),
    StatementLayer(SemanticCStatementError),
    InvalidAccounting,
    InvalidConstructedFragment(Vec<String>),
}

impl std::fmt::Display for SwitchTopologyFragmentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "switch-topology fragment construction failed: {self:?}")
    }
}

impl std::error::Error for SwitchTopologyFragmentError {}

impl From<RegionBuildError> for SwitchTopologyFragmentError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<SemanticCStatementError> for SwitchTopologyFragmentError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::StatementLayer(error)
    }
}

impl CertifiedSwitchTopologyFragment {
    pub fn from_projection(
        certified: &CertifiedMachineProjection,
        block_addr: u64,
    ) -> Result<Self, SwitchTopologyFragmentError> {
        let witness = certified
            .switch_topology_for_block(block_addr)
            .cloned()
            .ok_or(SwitchTopologyFragmentError::MissingCertifiedTopology(
                block_addr,
            ))?;
        Self::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block(certified, block_addr)?,
            witness,
        )
    }

    pub fn from_certified(
        certified: &CertifiedMachineFunction,
        block_addr: u64,
    ) -> Result<Self, SwitchTopologyFragmentError> {
        let witness = certified
            .switch_topology_for_block(block_addr)
            .cloned()
            .ok_or(SwitchTopologyFragmentError::MissingCertifiedTopology(
                block_addr,
            ))?;
        Self::from_accounting(
            CertifiedSingleBlockAccounting::from_certified_block(certified, block_addr)?,
            witness,
        )
    }

    fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
        witness: CertifiedSwitchTopology,
    ) -> Result<Self, SwitchTopologyFragmentError> {
        if !accounting.audit().has_exact_source_accounting()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            return Err(SwitchTopologyFragmentError::InvalidAccounting);
        }
        let mappings = accounting.mappings().to_vec().into_boxed_slice();
        let body = SemanticCBlockStepLayer::from_accounting(accounting)?;
        let fragment = Self {
			schema_version: CERTIFIED_SWITCH_TOPOLOGY_FRAGMENT_SCHEMA_VERSION,
			scope: SwitchTopologyFragmentScope::FinalIndirectBranchWithResidualTransferAndOpenLabeledPorts,
			identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
			body,
			witness,
			mappings,
		};
        let report = fragment.audit();
        if !report.has_exact_switch_topology_accounting() {
            return Err(SwitchTopologyFragmentError::InvalidConstructedFragment(
                report.invalid,
            ));
        }
        Ok(fragment)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SwitchTopologyFragmentScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn body(&self) -> &SemanticCBlockStepLayer {
        &self.body
    }

    pub const fn witness(&self) -> &CertifiedSwitchTopology {
        &self.witness
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    /// Ordered `(case_value, open_successor_address)` ports.
    pub const fn open_case_ports(&self) -> &[(u64, u64)] {
        self.witness.cases()
    }

    pub const fn open_default_port(&self) -> u64 {
        self.witness.default_target()
    }

    /// Always true for a valid fragment: the indirect transfer is deliberately
    /// residual until authoritative selector evidence exists.
    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.body.accounting().audit().has_residuals()
    }

    pub fn audit(&self) -> SwitchTopologyAuditReport {
        let accounting = self.body.accounting();
        let accounting_report = accounting.audit();
        let body_report = self.body.audit();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_SWITCH_TOPOLOGY_FRAGMENT_SCHEMA_VERSION {
            invalid.push("switch-topology fragment schema mismatch".to_string());
        }
        if self.scope
			!= SwitchTopologyFragmentScope::FinalIndirectBranchWithResidualTransferAndOpenLabeledPorts
		{
			invalid.push("switch-topology fragment scope mismatch".to_string());
		}
        if self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
            || self.identity_scope != accounting.identity_scope()
        {
            invalid.push("switch-topology identity scope mismatch".to_string());
        }
        if self.body.scope()
            != SemanticCStatementScope::SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit
            || !body_report.has_exact_source_order()
            || !accounting_report.has_exact_source_accounting()
        {
            invalid.push("embedded switch source body is not exact".to_string());
        }
        if self.witness.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || self.witness.origin() != accounting.origin()
            || self.witness.producer().block_addr != accounting.block_addr()
        {
            invalid.push("switch witness differs from selected artifact origin".to_string());
        }
        if self.mappings.as_ref() != accounting.mappings()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            invalid.push("switch mappings or control evidence differ from accounting".to_string());
        }

        let source_matches = accounting.source_block().is_some_and(|block| {
            matches!(
                block.terminator(),
                r2cert::CertifiedSourceTerminator::Switch {
                    switch_addr,
                    terminal_instruction_addr,
                    min_value,
                    max_value,
                    cases,
                    default,
                }
                    if cases.as_ref() == self.witness.cases()
                        && *default == Some(self.witness.default_target())
                        && *switch_addr == self.witness.switch_addr()
                        && switch_addr == terminal_instruction_addr
                        && *min_value == self.witness.min_value()
                        && *max_value == self.witness.max_value()
            ) && block.instructions().last() == Some(&self.witness.producer())
        });
        if !source_matches
            || self.body.steps().last().map(|step| step.source()) != Some(self.witness.producer())
        {
            invalid.push("switch witness does not match the terminal source step".to_string());
        }

        let transfer_mappings = self
            .mappings
            .iter()
            .filter(|mapping| mapping.obligation().kind == SemanticObligationKind::ControlTransfer)
            .collect::<Vec<_>>();
        let residual_transfer_matches = matches!(
            transfer_mappings.as_slice(),
            [mapping]
                if mapping.obligation() == self.witness.source_obligation()
                    && matches!(
                        mapping.disposition(),
                        RegionObligationDisposition::Residualized {
                            reason: RegionResidualReason::ControlRequiresCertifiedRegion
                        }
                    )
        );
        if !residual_transfer_matches
            || self.mappings.iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
            })
        {
            invalid.push("switch indirect transfer is not exactly residual".to_string());
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

        SwitchTopologyAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            remaining_obligation_residuals: accounting_report.has_residuals(),
        }
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SwitchTopologyAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    remaining_obligation_residuals: bool,
}

impl SwitchTopologyAuditReport {
    /// Exact selected-block accounting with one deliberately residual indirect
    /// transfer. This never means semantic closure or rendering permission.
    pub fn has_exact_switch_topology_accounting(&self) -> bool {
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

    pub const fn has_remaining_obligation_residuals(&self) -> bool {
        self.remaining_obligation_residuals
    }
}
