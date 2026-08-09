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

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, OpMetadata, R2ILBlock, R2ILOp, SwitchCase, SwitchInfo, Varnode};
    use r2ssa::SsaArtifact;

    fn switch_artifact(
        target_register: u64,
        default_target: Option<u64>,
        cases: Vec<SwitchCase>,
        include_branch_ind: bool,
        earlier_return: bool,
    ) -> SsaArtifact {
        switch_artifact_with_metadata(
            target_register,
            default_target,
            cases,
            include_branch_ind,
            earlier_return.then(|| R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }),
            0x7800,
            0,
            1,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn switch_artifact_with_metadata(
        target_register: u64,
        default_target: Option<u64>,
        cases: Vec<SwitchCase>,
        include_branch_ind: bool,
        earlier_op: Option<R2ILOp>,
        switch_addr: u64,
        min_val: u64,
        max_val: u64,
        terminal_instruction_addr: Option<u64>,
    ) -> SsaArtifact {
        let mut header = R2ILBlock::new(0x7800, 4);
        if let Some(earlier_op) = earlier_op {
            header.push(earlier_op);
        }
        if include_branch_ind {
            header.push(R2ILOp::BranchInd {
                target: Varnode::register(target_register, 8),
            });
        } else {
            header.push(R2ILOp::Copy {
                dst: Varnode::unique(0x10, 8),
                src: Varnode::constant(0, 8),
            });
        }
        if let Some(instruction_addr) = terminal_instruction_addr {
            header.set_op_metadata(
                header.ops.len() - 1,
                OpMetadata {
                    instruction_addr: Some(instruction_addr),
                    ..OpMetadata::default()
                },
            );
        }
        header.set_switch_info(SwitchInfo {
            switch_addr,
            min_val,
            max_val,
            default_target,
            cases,
        });
        let mut case_zero = R2ILBlock::new(0x7810, 4);
        case_zero.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut case_one = R2ILBlock::new(0x7820, 4);
        case_one.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut default = R2ILBlock::new(0x7830, 4);
        default.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::raw(&[header, case_zero, case_one, default], None).expect("switch artifact")
    }

    fn distinct_cases() -> Vec<SwitchCase> {
        vec![
            SwitchCase {
                value: 0,
                target: 0x7810,
            },
            SwitchCase {
                value: 1,
                target: 0x7820,
            },
        ]
    }

    #[test]
    fn exact_switch_topology_keeps_labeled_ports_and_residual_transfer() {
        assert_eq!(CERTIFIED_SWITCH_TOPOLOGY_FRAGMENT_SCHEMA_VERSION, 1);
        assert_eq!(
            serde_json::to_value(
                SwitchTopologyFragmentScope::FinalIndirectBranchWithResidualTransferAndOpenLabeledPorts
            )
            .expect("serialized switch scope"),
            serde_json::json!(
                "FinalIndirectBranchWithResidualTransferAndOpenLabeledPorts"
            )
        );
        let artifact = switch_artifact(0, Some(0x7830), distinct_cases(), true, false);
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("switch topology certification");
        let fragment = CertifiedSwitchTopologyFragment::from_projection(&certified, 0x7800)
            .expect("switch topology fragment");
        let report = fragment.audit();

        assert!(report.has_exact_switch_topology_accounting(), "{report:?}");
        assert!(report.has_remaining_obligation_residuals());
        assert_eq!(fragment.open_case_ports(), [(0, 0x7810), (1, 0x7820)]);
        assert_eq!(fragment.open_default_port(), 0x7830);
        assert_eq!(
            fragment.witness().schema_version(),
            CERTIFICATION_SCHEMA_VERSION
        );
        assert_eq!(fragment.witness().switch_addr(), 0x7800);
        assert_eq!(fragment.witness().min_value(), 0);
        assert_eq!(fragment.witness().max_value(), 1);
        assert_eq!(fragment.mappings().len(), 1);
        assert_eq!(
            fragment.mappings()[0].obligation().kind,
            SemanticObligationKind::ControlTransfer
        );

        let certified = CertifiedMachineFunction::from_artifact(&artifact)
            .expect("strict switch topology certification");
        let fragment = CertifiedSwitchTopologyFragment::from_certified(&certified, 0x7800)
            .expect("strict switch topology fragment");
        assert!(fragment.audit().has_exact_switch_topology_accounting());
    }

    #[test]
    fn incomplete_or_unbound_switch_metadata_has_no_witness() {
        let missing_default = switch_artifact(0, None, distinct_cases(), true, false);
        assert!(matches!(
            CertifiedMachineProjection::from_artifact(&missing_default),
            Err(r2ssa::MachineBuildError::TopologyMismatch)
        ));
        let shared_target = switch_artifact(
            0,
            Some(0x7830),
            vec![
                SwitchCase {
                    value: 0,
                    target: 0x7810,
                },
                SwitchCase {
                    value: 1,
                    target: 0x7810,
                },
            ],
            true,
            false,
        );
        assert!(matches!(
            CertifiedMachineProjection::from_artifact(&shared_target),
            Err(r2ssa::MachineBuildError::TopologyMismatch)
        ));
        let fixtures = [
            switch_artifact(0, Some(0x7830), distinct_cases(), false, false),
            switch_artifact(0, Some(0x7830), distinct_cases(), true, true),
            switch_artifact(
                0,
                Some(0x7830),
                vec![
                    SwitchCase {
                        value: 0,
                        target: 0x7810,
                    },
                    SwitchCase {
                        value: 0,
                        target: 0x7820,
                    },
                ],
                true,
                false,
            ),
            switch_artifact(
                0,
                Some(0x7830),
                vec![
                    SwitchCase {
                        value: 0,
                        target: 0x7810,
                    },
                    SwitchCase {
                        value: 1,
                        target: 0x7820,
                    },
                    SwitchCase {
                        value: 2,
                        target: 0x7900,
                    },
                ],
                true,
                false,
            ),
        ];
        for (index, artifact) in fixtures.into_iter().enumerate() {
            let certified =
                CertifiedMachineProjection::from_artifact(&artifact).unwrap_or_else(|error| {
                    panic!("incomplete switch fixture {index} should remain residual: {error:?}")
                });
            assert!(certified.switch_topology_for_block(0x7800).is_none());
            assert!(matches!(
                CertifiedSwitchTopologyFragment::from_projection(&certified, 0x7800),
                Err(SwitchTopologyFragmentError::MissingCertifiedTopology(
                    0x7800
                ))
            ));
        }
    }

    #[test]
    fn malformed_switch_source_metadata_has_no_witness() {
        let fixtures = [
            switch_artifact_with_metadata(
                0,
                Some(0x7830),
                distinct_cases(),
                true,
                None,
                0x7801,
                0,
                1,
                None,
            ),
            switch_artifact_with_metadata(
                0,
                Some(0x7830),
                distinct_cases(),
                true,
                None,
                0x7800,
                2,
                1,
                None,
            ),
            switch_artifact_with_metadata(
                0,
                Some(0x7830),
                distinct_cases(),
                true,
                None,
                0x7800,
                1,
                2,
                None,
            ),
        ];
        for artifact in fixtures {
            let certified = CertifiedMachineProjection::from_artifact(&artifact)
                .expect("malformed switch remains residual");
            assert!(certified.switch_topology_for_block(0x7800).is_none());
        }

        let associated = switch_artifact_with_metadata(
            0,
            Some(0x7830),
            distinct_cases(),
            true,
            None,
            0x7802,
            0,
            1,
            Some(0x7802),
        );
        let certified = CertifiedMachineProjection::from_artifact(&associated)
            .expect("source-associated switch certification");
        assert_eq!(
            certified
                .switch_topology_for_block(0x7800)
                .map(CertifiedSwitchTopology::switch_addr),
            Some(0x7802)
        );
    }

    #[test]
    fn switch_rejects_unrepresentable_typed_target_addresses() {
        let mut header = R2ILBlock::new(0x7800, 4);
        header.push(R2ILOp::BranchInd {
            target: Varnode::register(0, 4),
        });
        header.set_switch_info(SwitchInfo {
            switch_addr: 0x7800,
            min_val: 0,
            max_val: 0,
            default_target: Some(0x7830),
            cases: vec![SwitchCase {
                value: 0,
                target: 0x1_0000_0000,
            }],
        });
        let mut oversized = R2ILBlock::new(0x1_0000_0000, 4);
        oversized.push(R2ILOp::Return {
            target: Varnode::constant(0, 4),
        });
        let mut default = R2ILBlock::new(0x7830, 4);
        default.push(R2ILOp::Return {
            target: Varnode::constant(0, 4),
        });
        let mut arch = ArchSpec::new("32-bit-switch-target-test");
        arch.addr_size = 4;
        let artifact = SsaArtifact::raw(&[header, oversized, default], Some(&arch))
            .expect("typed switch artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("unrepresentable switch remains residual");

        assert!(certified.switch_topology_for_block(0x7800).is_none());
    }

    #[test]
    fn earlier_terminal_or_trap_operations_prevent_switch_witnesses() {
        let earlier_ops = [
            R2ILOp::Branch {
                target: Varnode::ram(0x7810, 8),
            },
            R2ILOp::CBranch {
                target: Varnode::ram(0x7810, 8),
                cond: Varnode::constant(1, 1),
            },
            R2ILOp::BranchInd {
                target: Varnode::register(8, 8),
            },
            R2ILOp::Breakpoint,
        ];
        for earlier_op in earlier_ops {
            let artifact = switch_artifact_with_metadata(
                0,
                Some(0x7830),
                distinct_cases(),
                true,
                Some(earlier_op),
                0x7800,
                0,
                1,
                None,
            );
            let certified = CertifiedMachineProjection::from_artifact(&artifact)
                .expect("earlier terminating semantics remain residual");
            assert!(certified.switch_topology_for_block(0x7800).is_none());
        }
    }

    #[test]
    fn switch_fragment_mutations_and_foreign_witness_fail_audit() {
        let artifact = switch_artifact(0, Some(0x7830), distinct_cases(), true, false);
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("switch topology certification");
        let fragment = CertifiedSwitchTopologyFragment::from_projection(&certified, 0x7800)
            .expect("switch topology fragment");
        let foreign_artifact = switch_artifact(8, Some(0x7830), distinct_cases(), true, false);
        let foreign_certified = CertifiedMachineProjection::from_artifact(&foreign_artifact)
            .expect("foreign switch topology certification");
        let foreign = CertifiedSwitchTopologyFragment::from_projection(&foreign_certified, 0x7800)
            .expect("foreign switch fragment");

        let mut corrupted = fragment.clone();
        corrupted.schema_version += 1;
        assert!(!corrupted.audit().has_exact_switch_topology_accounting());
        let mut corrupted = fragment.clone();
        corrupted.mappings = Box::new([]);
        assert!(!corrupted.audit().has_exact_switch_topology_accounting());
        let mut corrupted = fragment;
        corrupted.witness = foreign.witness;
        assert!(!corrupted.audit().has_exact_switch_topology_accounting());
    }
}
