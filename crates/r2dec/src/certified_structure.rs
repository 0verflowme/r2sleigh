//! Proof-preserving composition of the first admitted structured control shape.
//!
//! The only positive shape here is a strict three-block diamond: one certified
//! conditional header, two single-entry certified-transfer arms, and one
//! shared open join port. An arm may transfer explicitly or by exact source
//! fallthrough. The fragment does not own the join, prove function exit, or
//! authorize executable C.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{CertifiedMachineFunction, CertifiedMachineProjection, CertifiedSourceTopology};
use r2ssa::SemanticObligationId;
use serde::Serialize;

use crate::certified_control::{
    CertifiedConditionalTransferBlockRegion, CertifiedDirectTransferBlockRegion,
    CertifiedFallthroughTransferBlockRegion, ConditionalTransferRegionError,
    DirectTransferRegionError, FallthroughTransferRegionError,
};
use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionBuildError, RegionObligationMapping,
};
use crate::semantic_c::SemanticCIdentityScope;

pub const CERTIFIED_IF_ELSE_DIAMOND_SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum IfElseDiamondScope {
    ThreeBlockSingleEntryArmsWithOpenJoin,
}

/// One strict-diamond arm with an exact normal-completion transfer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedDiamondArm {
    Direct(Box<CertifiedDirectTransferBlockRegion>),
    Fallthrough(Box<CertifiedFallthroughTransferBlockRegion>),
}

impl CertifiedDiamondArm {
    fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, IfElseDiamondError> {
        let block_addr = accounting.block_addr();
        match accounting.source_block().map(|block| block.terminator()) {
            Some(r2cert::CertifiedSourceTerminator::Branch { .. }) => Ok(Self::Direct(Box::new(
                CertifiedDirectTransferBlockRegion::from_accounting(accounting)?,
            ))),
            Some(r2cert::CertifiedSourceTerminator::Fallthrough { .. }) => {
                Ok(Self::Fallthrough(Box::new(
                    CertifiedFallthroughTransferBlockRegion::from_accounting(accounting)?,
                )))
            }
            _ => Err(IfElseDiamondError::UnsupportedArm(block_addr)),
        }
    }

    pub fn body(&self) -> &crate::semantic_stmt::SemanticCBlockStepLayer {
        match self {
            Self::Direct(region) => region.body(),
            Self::Fallthrough(region) => region.body(),
        }
    }

    pub fn as_direct(&self) -> Option<&CertifiedDirectTransferBlockRegion> {
        match self {
            Self::Direct(region) => Some(region),
            Self::Fallthrough(_) => None,
        }
    }

    pub fn as_fallthrough(&self) -> Option<&CertifiedFallthroughTransferBlockRegion> {
        match self {
            Self::Direct(_) => None,
            Self::Fallthrough(region) => Some(region),
        }
    }

    pub fn mappings(&self) -> &[RegionObligationMapping] {
        match self {
            Self::Direct(region) => region.mappings(),
            Self::Fallthrough(region) => region.mappings(),
        }
    }

    pub fn open_successor(&self) -> u64 {
        match self {
            Self::Direct(region) => region.open_successor(),
            Self::Fallthrough(region) => region.open_successor(),
        }
    }

    pub fn identity_scope(&self) -> SemanticCIdentityScope {
        match self {
            Self::Direct(region) => region.identity_scope(),
            Self::Fallthrough(region) => region.identity_scope(),
        }
    }

    pub fn has_remaining_obligation_residuals(&self) -> bool {
        match self {
            Self::Direct(region) => region.has_remaining_obligation_residuals(),
            Self::Fallthrough(region) => region.has_remaining_obligation_residuals(),
        }
    }

    fn has_exact_transfer_accounting(&self) -> bool {
        match self {
            Self::Direct(region) => region.audit().has_exact_direct_transfer_accounting(),
            Self::Fallthrough(region) => region.audit().has_exact_fallthrough_accounting(),
        }
    }
}

/// A strict conditional diamond with an unowned join composition port.
///
/// True/false polarity comes from the certified header and is never recovered
/// from successor order. Each arm is one certified explicit or fallthrough
/// transfer block. This proves neither join execution nor behavior after it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedIfElseDiamondFragment {
    schema_version: u32,
    scope: IfElseDiamondScope,
    identity_scope: SemanticCIdentityScope,
    header: CertifiedConditionalTransferBlockRegion,
    true_arm: CertifiedDiamondArm,
    false_arm: CertifiedDiamondArm,
    mappings: Box<[RegionObligationMapping]>,
    open_join_successor: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IfElseDiamondError {
    MissingHeader(u64),
    HeaderIsNotConditional(u64),
    Accounting(RegionBuildError),
    Conditional(ConditionalTransferRegionError),
    Direct(DirectTransferRegionError),
    Fallthrough(FallthroughTransferRegionError),
    UnsupportedArm(u64),
    InvalidConstructedFragment(Vec<String>),
}

impl std::fmt::Display for IfElseDiamondError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "if/else diamond construction failed: {self:?}")
    }
}

impl std::error::Error for IfElseDiamondError {}

impl From<RegionBuildError> for IfElseDiamondError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<ConditionalTransferRegionError> for IfElseDiamondError {
    fn from(error: ConditionalTransferRegionError) -> Self {
        Self::Conditional(error)
    }
}

impl From<DirectTransferRegionError> for IfElseDiamondError {
    fn from(error: DirectTransferRegionError) -> Self {
        Self::Direct(error)
    }
}

impl From<FallthroughTransferRegionError> for IfElseDiamondError {
    fn from(error: FallthroughTransferRegionError) -> Self {
        Self::Fallthrough(error)
    }
}

impl CertifiedIfElseDiamondFragment {
    pub fn from_projection(
        certified: &CertifiedMachineProjection,
        header_addr: u64,
    ) -> Result<Self, IfElseDiamondError> {
        let (true_addr, false_addr) = conditional_arm_addresses(certified.topology(), header_addr)?;
        Self::from_accountings(
            CertifiedSingleBlockAccounting::from_projection_block(certified, header_addr)?,
            CertifiedSingleBlockAccounting::from_projection_block(certified, true_addr)?,
            CertifiedSingleBlockAccounting::from_projection_block(certified, false_addr)?,
        )
    }

    pub fn from_certified(
        certified: &CertifiedMachineFunction,
        header_addr: u64,
    ) -> Result<Self, IfElseDiamondError> {
        let (true_addr, false_addr) = conditional_arm_addresses(certified.topology(), header_addr)?;
        Self::from_accountings(
            CertifiedSingleBlockAccounting::from_certified_block(certified, header_addr)?,
            CertifiedSingleBlockAccounting::from_certified_block(certified, true_addr)?,
            CertifiedSingleBlockAccounting::from_certified_block(certified, false_addr)?,
        )
    }

    fn from_accountings(
        header: CertifiedSingleBlockAccounting,
        true_arm: CertifiedSingleBlockAccounting,
        false_arm: CertifiedSingleBlockAccounting,
    ) -> Result<Self, IfElseDiamondError> {
        let header = CertifiedConditionalTransferBlockRegion::from_accounting(header)?;
        let true_arm = CertifiedDiamondArm::from_accounting(true_arm)?;
        let false_arm = CertifiedDiamondArm::from_accounting(false_arm)?;
        let mappings = header
            .mappings()
            .iter()
            .chain(true_arm.mappings())
            .chain(false_arm.mappings())
            .cloned()
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let open_join_successor = true_arm.open_successor();
        let fragment = Self {
            schema_version: CERTIFIED_IF_ELSE_DIAMOND_SCHEMA_VERSION,
            scope: IfElseDiamondScope::ThreeBlockSingleEntryArmsWithOpenJoin,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            header,
            true_arm,
            false_arm,
            mappings,
            open_join_successor,
        };
        let report = fragment.audit();
        if !report.has_exact_diamond_accounting() {
            return Err(IfElseDiamondError::InvalidConstructedFragment(
                report.invalid,
            ));
        }
        Ok(fragment)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> IfElseDiamondScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn header(&self) -> &CertifiedConditionalTransferBlockRegion {
        &self.header
    }

    pub const fn true_arm(&self) -> &CertifiedDiamondArm {
        &self.true_arm
    }

    pub const fn false_arm(&self) -> &CertifiedDiamondArm {
        &self.false_arm
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn open_join_successor(&self) -> u64 {
        self.open_join_successor
    }

    /// Whether any selected header/arm obligation remains residual. The join
    /// port remains open regardless of this result.
    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.header.has_remaining_obligation_residuals()
            || self.true_arm.has_remaining_obligation_residuals()
            || self.false_arm.has_remaining_obligation_residuals()
    }

    pub fn audit(&self) -> IfElseDiamondAuditReport {
        let header_accounting = self.header.body().accounting();
        let true_accounting = self.true_arm.body().accounting();
        let false_accounting = self.false_arm.body().accounting();
        let topology = header_accounting.topology();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_IF_ELSE_DIAMOND_SCHEMA_VERSION {
            invalid.push("if/else diamond schema mismatch".to_string());
        }
        if self.scope != IfElseDiamondScope::ThreeBlockSingleEntryArmsWithOpenJoin {
            invalid.push("if/else diamond scope mismatch".to_string());
        }
        if self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
            || self.identity_scope != self.header.identity_scope()
            || self.identity_scope != self.true_arm.identity_scope()
            || self.identity_scope != self.false_arm.identity_scope()
        {
            invalid.push("if/else diamond identity scope mismatch".to_string());
        }
        if !self
            .header
            .audit()
            .has_exact_conditional_transfer_accounting()
            || !self.true_arm.has_exact_transfer_accounting()
            || !self.false_arm.has_exact_transfer_accounting()
        {
            invalid.push("nested terminal-transfer region is not exact".to_string());
        }
        if topology != true_accounting.topology() || topology != false_accounting.topology() {
            invalid.push("diamond blocks do not retain one exact source topology".to_string());
        }
        if header_accounting.origin() != true_accounting.origin()
            || header_accounting.origin() != false_accounting.origin()
        {
            invalid.push("diamond blocks do not share one exact artifact origin".to_string());
        }

        let header_addr = header_accounting.block_addr();
        let true_addr = true_accounting.block_addr();
        let false_addr = false_accounting.block_addr();
        let selected = BTreeSet::from([header_addr, true_addr, false_addr]);
        if selected.len() != 3
            || self.header.open_true_successor() != true_addr
            || self.header.open_false_successor() != false_addr
            || self.true_arm.open_successor() != self.open_join_successor
            || self.false_arm.open_successor() != self.open_join_successor
            || selected.contains(&self.open_join_successor)
            || topology.block(self.open_join_successor).is_none()
        {
            invalid.push("diamond arm polarity or shared open join mismatch".to_string());
        }

        let true_predecessors = predecessors(topology, true_addr);
        let false_predecessors = predecessors(topology, false_addr);
        if true_predecessors != BTreeSet::from([header_addr])
            || false_predecessors != BTreeSet::from([header_addr])
        {
            invalid.push("diamond arms are not single-entry from the header".to_string());
        }

        let expected_mappings = self
            .header
            .mappings()
            .iter()
            .chain(self.true_arm.mappings())
            .chain(self.false_arm.mappings())
            .cloned()
            .collect::<Vec<_>>();
        if self.mappings.as_ref() != expected_mappings.as_slice() {
            invalid.push("diamond mappings differ from nested source accounting".to_string());
        }
        let expected = expected_mappings
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
        if expected.len() != expected_mappings.len() {
            invalid.push("nested diamond regions overlap source obligations".to_string());
        }

        IfElseDiamondAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            remaining_obligation_residuals: self.has_remaining_obligation_residuals(),
        }
    }
}

fn conditional_arm_addresses(
    topology: &CertifiedSourceTopology,
    header_addr: u64,
) -> Result<(u64, u64), IfElseDiamondError> {
    let block = topology
        .block(header_addr)
        .ok_or(IfElseDiamondError::MissingHeader(header_addr))?;
    match block.terminator() {
        r2cert::CertifiedSourceTerminator::ConditionalBranch {
            true_target,
            false_target,
        } => Ok((*true_target, *false_target)),
        _ => Err(IfElseDiamondError::HeaderIsNotConditional(header_addr)),
    }
}

fn predecessors(topology: &CertifiedSourceTopology, target: u64) -> BTreeSet<u64> {
    topology
        .blocks()
        .iter()
        .filter(|block| block.successors().contains(&target))
        .map(|block| block.addr())
        .collect()
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IfElseDiamondAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    remaining_obligation_residuals: bool,
}

impl IfElseDiamondAuditReport {
    pub fn has_exact_diamond_accounting(&self) -> bool {
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
    /// the still-open join composition port.
    pub const fn has_remaining_obligation_residuals(&self) -> bool {
        self.remaining_obligation_residuals
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::SsaArtifact;

    fn diamond_artifact(extra_side_entry: bool, divergent_joins: bool) -> SsaArtifact {
        let mut header = R2ILBlock::new(0x7200, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7220, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut false_arm = R2ILBlock::new(0x7204, 4);
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7230, 8),
        });
        let mut true_arm = R2ILBlock::new(0x7220, 4);
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(if divergent_joins { 0x7240 } else { 0x7230 }, 8),
        });
        let mut join = R2ILBlock::new(0x7230, 4);
        join.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut blocks = vec![header, false_arm, true_arm, join];
        if divergent_joins {
            let mut other_join = R2ILBlock::new(0x7240, 4);
            other_join.push(R2ILOp::Return {
                target: Varnode::constant(0, 8),
            });
            blocks.push(other_join);
        }
        if extra_side_entry {
            let mut outer = R2ILBlock::new(0x71f0, 4);
            outer.push(R2ILOp::CBranch {
                target: Varnode::ram(0x7200, 8),
                cond: Varnode::constant(1, 1),
            });
            let mut side = R2ILBlock::new(0x71f4, 4);
            side.push(R2ILOp::Branch {
                target: Varnode::ram(0x7220, 8),
            });
            blocks.insert(0, side);
            blocks.insert(0, outer);
        }
        SsaArtifact::raw(&blocks, None).expect("diamond artifact")
    }

    fn payload_diamond_artifact(
        header_condition: u64,
        true_value: u64,
        false_value: u64,
    ) -> SsaArtifact {
        let mut header = R2ILBlock::new(0x7300, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7320, 8),
            cond: Varnode::constant(header_condition, 1),
        });
        let mut false_arm = R2ILBlock::new(0x7304, 4);
        false_arm.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::constant(0x9000, 8),
            val: Varnode::constant(false_value, 4),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7330, 8),
        });
        let mut true_arm = R2ILBlock::new(0x7320, 4);
        true_arm.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::constant(0x9004, 8),
            val: Varnode::constant(true_value, 4),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7330, 8),
        });
        let mut join = R2ILBlock::new(0x7330, 4);
        join.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::raw(&[header, false_arm, true_arm, join], None)
            .expect("payload diamond artifact")
    }

    fn empty_arm_diamond_artifact(empty_true_arm: bool, condition_value: u64) -> SsaArtifact {
        let mut header = R2ILBlock::new(0x7400, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7420, 8),
            cond: Varnode::constant(condition_value, 1),
        });
        let mut false_arm = R2ILBlock::new(0x7404, 0x2c);
        if empty_true_arm {
            false_arm = R2ILBlock::new(0x7404, 4);
            false_arm.push(R2ILOp::Branch {
                target: Varnode::ram(0x7430, 8),
            });
        }
        let mut true_arm = R2ILBlock::new(0x7420, 0x10);
        if !empty_true_arm {
            true_arm = R2ILBlock::new(0x7420, 4);
            true_arm.push(R2ILOp::Branch {
                target: Varnode::ram(0x7430, 8),
            });
        }
        let mut join = R2ILBlock::new(0x7430, 4);
        join.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::raw(&[header, false_arm, true_arm, join], None)
            .expect("empty-arm diamond artifact")
    }

    #[test]
    fn strict_diamond_preserves_polarity_and_exposes_one_open_join() {
        let artifact = diamond_artifact(false, false);
        let certified =
            CertifiedMachineProjection::from_artifact(&artifact).expect("diamond certification");
        let fragment = CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7200)
            .expect("strict diamond fragment");
        let report = fragment.audit();

        assert!(report.has_exact_diamond_accounting(), "{report:?}");
        assert!(!report.has_remaining_obligation_residuals());
        assert_eq!(fragment.header().open_true_successor(), 0x7220);
        assert_eq!(fragment.header().open_false_successor(), 0x7204);
        assert_eq!(fragment.true_arm().body().accounting().block_addr(), 0x7220);
        assert_eq!(
            fragment.false_arm().body().accounting().block_addr(),
            0x7204
        );
        assert_eq!(fragment.open_join_successor(), 0x7230);
        assert_eq!(fragment.mappings().len(), 4);
    }

    #[test]
    fn divergent_joins_and_side_entries_are_rejected() {
        for artifact in [diamond_artifact(false, true), diamond_artifact(true, false)] {
            let certified = CertifiedMachineProjection::from_artifact(&artifact)
                .expect("control certification");
            assert!(matches!(
                CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7200),
                Err(IfElseDiamondError::InvalidConstructedFragment(_))
            ));
        }
    }

    #[test]
    fn return_arm_is_not_inferred_as_a_diamond_arm() {
        let mut header = R2ILBlock::new(0x7260, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x7270, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut false_arm = R2ILBlock::new(0x7264, 4);
        false_arm.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut true_arm = R2ILBlock::new(0x7270, 4);
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x7280, 8),
        });
        let join = R2ILBlock::new(0x7280, 4);
        let artifact = SsaArtifact::raw(&[header, false_arm, true_arm, join], None)
            .expect("return-arm artifact");
        let certified =
            CertifiedMachineProjection::from_artifact(&artifact).expect("return-arm certification");

        assert!(matches!(
            CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7260),
            Err(IfElseDiamondError::UnsupportedArm(0x7264))
        ));
    }

    #[test]
    fn empty_true_and_false_arms_use_topology_only_fallthrough() {
        for empty_true_arm in [false, true] {
            let artifact = empty_arm_diamond_artifact(empty_true_arm, 1);
            let certified = CertifiedMachineProjection::from_artifact(&artifact)
                .expect("empty-arm certification");
            let fragment = CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7400)
                .expect("empty-arm diamond fragment");
            let report = fragment.audit();

            assert!(report.has_exact_diamond_accounting(), "{report:?}");
            assert_eq!(fragment.open_join_successor(), 0x7430);
            assert_eq!(
                fragment.true_arm().as_fallthrough().is_some(),
                empty_true_arm
            );
            assert_eq!(
                fragment.false_arm().as_fallthrough().is_some(),
                !empty_true_arm
            );
            assert_eq!(fragment.true_arm().as_direct().is_some(), !empty_true_arm);
            assert_eq!(fragment.false_arm().as_direct().is_some(), empty_true_arm);
        }
    }

    #[test]
    fn diamond_mutations_fail_audit() {
        let artifact = diamond_artifact(false, false);
        let certified =
            CertifiedMachineProjection::from_artifact(&artifact).expect("diamond certification");
        let fragment = CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7200)
            .expect("strict diamond fragment");

        let mut corrupted = fragment.clone();
        corrupted.schema_version += 1;
        assert!(!corrupted.audit().has_exact_diamond_accounting());
        let mut corrupted = fragment.clone();
        corrupted.open_join_successor = 0x7240;
        assert!(!corrupted.audit().has_exact_diamond_accounting());
        let mut corrupted = fragment.clone();
        std::mem::swap(&mut corrupted.true_arm, &mut corrupted.false_arm);
        assert!(!corrupted.audit().has_exact_diamond_accounting());
        let mut corrupted = fragment.clone();
        corrupted.mappings = Box::new([]);
        assert!(!corrupted.audit().has_exact_diamond_accounting());
        let mut corrupted = fragment;
        let mapping = corrupted.mappings[0].clone();
        corrupted.mappings = vec![mapping.clone(), mapping].into_boxed_slice();
        assert!(!corrupted.audit().has_exact_diamond_accounting());
    }

    #[test]
    fn coincident_topology_foreign_children_fail_origin_audit() {
        let certify = |artifact: SsaArtifact| {
            let certified = CertifiedMachineProjection::from_artifact(&artifact)
                .expect("payload diamond certification");
            CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7300)
                .expect("payload diamond fragment")
        };
        let original = certify(payload_diamond_artifact(1, 2, 3));
        let foreign_header = certify(payload_diamond_artifact(0, 2, 3));
        let foreign_true = certify(payload_diamond_artifact(1, 4, 3));
        let foreign_false = certify(payload_diamond_artifact(1, 2, 5));

        assert_eq!(
            original.header.body().accounting().topology(),
            foreign_true.header.body().accounting().topology()
        );
        assert_ne!(
            original.header.body().accounting().origin(),
            foreign_true.header.body().accounting().origin()
        );

        let mut corrupted = original.clone();
        corrupted.header = foreign_header.header;
        assert!(!corrupted.audit().has_exact_diamond_accounting());
        let mut corrupted = original.clone();
        corrupted.true_arm = foreign_true.true_arm;
        assert!(!corrupted.audit().has_exact_diamond_accounting());
        let mut corrupted = original;
        corrupted.false_arm = foreign_false.false_arm;
        assert!(!corrupted.audit().has_exact_diamond_accounting());
    }

    #[test]
    fn coincident_topology_foreign_fallthrough_arm_fails_origin_audit() {
        let certify = |condition_value| {
            let artifact = empty_arm_diamond_artifact(false, condition_value);
            let certified = CertifiedMachineProjection::from_artifact(&artifact)
                .expect("fallthrough-origin certification");
            CertifiedIfElseDiamondFragment::from_projection(&certified, 0x7400)
                .expect("fallthrough-origin fragment")
        };
        let original = certify(1);
        let foreign = certify(2);
        assert!(original.false_arm().as_fallthrough().is_some());
        assert!(foreign.false_arm().as_fallthrough().is_some());

        let mut corrupted = original;
        corrupted.false_arm = foreign.false_arm;
        assert!(!corrupted.audit().has_exact_diamond_accounting());
    }
}
