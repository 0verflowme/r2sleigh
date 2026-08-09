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
