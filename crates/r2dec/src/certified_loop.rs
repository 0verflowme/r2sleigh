//! Proof-preserving composition of the first admitted loop shape.
//!
//! The positive subset is deliberately narrow: one conditional header, one
//! single-entry direct-transfer body/latch, exactly one external predecessor
//! port, one open exit port, and no loop-carried-state obligations. This proves
//! structure and source accounting only; it does not execute the exit or
//! authorize a rendered `while` statement.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedMachineFunction, CertifiedMachineProjection,
    CertifiedNaturalLoopRouting, CertifiedSourceTopology,
};
use r2ssa::{SemanticObligationId, SemanticObligationKind};
use serde::Serialize;

use crate::certified_control::{
    CertifiedConditionalTransferBlockRegion, CertifiedDirectTransferBlockRegion,
    ConditionalTransferRegionError, DirectTransferRegionError,
};
use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionBuildError, RegionObligationMapping,
};
use crate::semantic_c::SemanticCIdentityScope;

pub const CERTIFIED_HEADER_TESTED_LOOP_SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum HeaderTestedLoopScope {
    TwoBlockCarrierFreeSingleExternalPredecessorWithOpenEntryAndExitPorts,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum LoopContinuationArm {
    True,
    False,
}

/// A two-block header-tested loop with open predecessor and exit composition ports.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedHeaderTestedLoopFragment {
    schema_version: u32,
    scope: HeaderTestedLoopScope,
    identity_scope: SemanticCIdentityScope,
    header: CertifiedConditionalTransferBlockRegion,
    body_latch: CertifiedDirectTransferBlockRegion,
    routing: CertifiedNaturalLoopRouting,
    mappings: Box<[RegionObligationMapping]>,
    continuation_arm: LoopContinuationArm,
    open_entry_predecessor: u64,
    open_exit_successor: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeaderTestedLoopError {
    MissingHeader(u64),
    MissingCertifiedRouting(u64),
    Accounting(RegionBuildError),
    Conditional(ConditionalTransferRegionError),
    Direct(DirectTransferRegionError),
    InvalidConstructedFragment(Vec<String>),
}

impl std::fmt::Display for HeaderTestedLoopError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "header-tested loop construction failed: {self:?}")
    }
}

impl std::error::Error for HeaderTestedLoopError {}

impl From<RegionBuildError> for HeaderTestedLoopError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<ConditionalTransferRegionError> for HeaderTestedLoopError {
    fn from(error: ConditionalTransferRegionError) -> Self {
        Self::Conditional(error)
    }
}

impl From<DirectTransferRegionError> for HeaderTestedLoopError {
    fn from(error: DirectTransferRegionError) -> Self {
        Self::Direct(error)
    }
}

impl CertifiedHeaderTestedLoopFragment {
    pub fn from_projection(
        certified: &CertifiedMachineProjection,
        header_addr: u64,
    ) -> Result<Self, HeaderTestedLoopError> {
        let routing = certified
            .natural_loop_routing_for_header(header_addr)
            .cloned()
            .ok_or(HeaderTestedLoopError::MissingCertifiedRouting(header_addr))?;
        let body_addr = routing.body_latch();
        let continuation_arm = if routing.continuation_on_true() {
            LoopContinuationArm::True
        } else {
            LoopContinuationArm::False
        };
        Self::from_accountings(
            CertifiedSingleBlockAccounting::from_projection_block(certified, header_addr)?,
            CertifiedSingleBlockAccounting::from_projection_block(certified, body_addr)?,
            routing,
            continuation_arm,
        )
    }

    pub fn from_certified(
        certified: &CertifiedMachineFunction,
        header_addr: u64,
    ) -> Result<Self, HeaderTestedLoopError> {
        let routing = certified
            .natural_loop_routing_for_header(header_addr)
            .cloned()
            .ok_or(HeaderTestedLoopError::MissingCertifiedRouting(header_addr))?;
        let body_addr = routing.body_latch();
        let continuation_arm = if routing.continuation_on_true() {
            LoopContinuationArm::True
        } else {
            LoopContinuationArm::False
        };
        Self::from_accountings(
            CertifiedSingleBlockAccounting::from_certified_block(certified, header_addr)?,
            CertifiedSingleBlockAccounting::from_certified_block(certified, body_addr)?,
            routing,
            continuation_arm,
        )
    }

    fn from_accountings(
        header: CertifiedSingleBlockAccounting,
        body_latch: CertifiedSingleBlockAccounting,
        routing: CertifiedNaturalLoopRouting,
        continuation_arm: LoopContinuationArm,
    ) -> Result<Self, HeaderTestedLoopError> {
        let header = CertifiedConditionalTransferBlockRegion::from_accounting(header)?;
        let body_latch = CertifiedDirectTransferBlockRegion::from_accounting(body_latch)?;
        let header_addr = header.body().accounting().block_addr();
        let body_addr = body_latch.body().accounting().block_addr();
        let topology = header.body().accounting().topology();
        let header_block = topology
            .block(header_addr)
            .ok_or(HeaderTestedLoopError::MissingHeader(header_addr))?;
        let external_predecessors = header_block
            .predecessors()
            .iter()
            .copied()
            .filter(|predecessor| *predecessor != body_addr)
            .collect::<Vec<_>>();
        let [open_entry_predecessor] = external_predecessors.as_slice() else {
            return Err(HeaderTestedLoopError::InvalidConstructedFragment(vec![
                "loop header does not have exactly one external entry".to_string(),
            ]));
        };
        let open_exit_successor = match continuation_arm {
            LoopContinuationArm::True => header.open_false_successor(),
            LoopContinuationArm::False => header.open_true_successor(),
        };
        let mappings = header
            .mappings()
            .iter()
            .chain(body_latch.mappings())
            .cloned()
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let fragment = Self {
            schema_version: CERTIFIED_HEADER_TESTED_LOOP_SCHEMA_VERSION,
			scope:
				HeaderTestedLoopScope::TwoBlockCarrierFreeSingleExternalPredecessorWithOpenEntryAndExitPorts,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            header,
            body_latch,
            routing,
            mappings,
            continuation_arm,
            open_entry_predecessor: *open_entry_predecessor,
            open_exit_successor,
        };
        let report = fragment.audit();
        if !report.has_exact_loop_accounting() {
            return Err(HeaderTestedLoopError::InvalidConstructedFragment(
                report.invalid,
            ));
        }
        Ok(fragment)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> HeaderTestedLoopScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn header(&self) -> &CertifiedConditionalTransferBlockRegion {
        &self.header
    }

    pub const fn body_latch(&self) -> &CertifiedDirectTransferBlockRegion {
        &self.body_latch
    }

    pub const fn routing(&self) -> &CertifiedNaturalLoopRouting {
        &self.routing
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn continuation_arm(&self) -> LoopContinuationArm {
        self.continuation_arm
    }

    pub const fn open_entry_predecessor(&self) -> u64 {
        self.open_entry_predecessor
    }

    pub const fn open_exit_successor(&self) -> u64 {
        self.open_exit_successor
    }

    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.header.has_remaining_obligation_residuals()
            || self.body_latch.has_remaining_obligation_residuals()
    }

    pub fn audit(&self) -> HeaderTestedLoopAuditReport {
        let header_accounting = self.header.body().accounting();
        let body_accounting = self.body_latch.body().accounting();
        let topology = header_accounting.topology();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_HEADER_TESTED_LOOP_SCHEMA_VERSION {
            invalid.push("header-tested loop schema mismatch".to_string());
        }
        if self.scope
			!= HeaderTestedLoopScope::TwoBlockCarrierFreeSingleExternalPredecessorWithOpenEntryAndExitPorts
		{
            invalid.push("header-tested loop scope mismatch".to_string());
        }
        if self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
            || self.identity_scope != self.header.identity_scope()
            || self.identity_scope != self.body_latch.identity_scope()
        {
            invalid.push("header-tested loop identity scope mismatch".to_string());
        }
        if !self
            .header
            .audit()
            .has_exact_conditional_transfer_accounting()
            || !self
                .body_latch
                .audit()
                .has_exact_direct_transfer_accounting()
        {
            invalid.push("nested loop transfer region is not exact".to_string());
        }
        if topology != body_accounting.topology()
            || header_accounting.origin() != body_accounting.origin()
            || self.routing.origin() != header_accounting.origin()
        {
            invalid.push("loop blocks do not share one exact artifact origin".to_string());
        }

        let header_addr = header_accounting.block_addr();
        let body_addr = body_accounting.block_addr();
        let selected = BTreeSet::from([header_addr, body_addr]);
        let continuation_successor = match self.continuation_arm {
            LoopContinuationArm::True => self.header.open_true_successor(),
            LoopContinuationArm::False => self.header.open_false_successor(),
        };
        let exit_successor = match self.continuation_arm {
            LoopContinuationArm::True => self.header.open_false_successor(),
            LoopContinuationArm::False => self.header.open_true_successor(),
        };
        let distinct_ports = BTreeSet::from([
            header_addr,
            body_addr,
            self.open_entry_predecessor,
            self.open_exit_successor,
        ]);
        if selected.len() != 2
            || distinct_ports.len() != 4
            || continuation_successor != body_addr
            || exit_successor != self.open_exit_successor
            || self.body_latch.open_successor() != header_addr
            || topology.block(self.open_entry_predecessor).is_none()
            || topology.block(self.open_exit_successor).is_none()
        {
            invalid.push("loop polarity, backedge, or open port mismatch".to_string());
        }
        if self.routing.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || self.routing.header() != header_addr
            || self.routing.body_latch() != body_addr
            || self.routing.exit() != self.open_exit_successor
            || self.routing.entry_predecessor() != self.open_entry_predecessor
            || self.routing.continuation_on_true()
                != (self.continuation_arm == LoopContinuationArm::True)
            || self.routing.header_control() != self.header.transfer()
            || self.routing.body_transfer() != self.body_latch.transfer()
        {
            invalid.push("loop routing differs from sealed natural-loop evidence".to_string());
        }

        let header_predecessors = predecessors(topology, header_addr);
        let body_predecessors = predecessors(topology, body_addr);
        if header_predecessors != BTreeSet::from([self.open_entry_predecessor, body_addr])
            || body_predecessors != BTreeSet::from([header_addr])
        {
            invalid.push("loop header/body are not exact single-entry blocks".to_string());
        }

        let expected_mappings = self
            .header
            .mappings()
            .iter()
            .chain(self.body_latch.mappings())
            .cloned()
            .collect::<Vec<_>>();
        if self.mappings.as_ref() != expected_mappings.as_slice() {
            invalid.push("loop mappings differ from nested source accounting".to_string());
        }
        if self.mappings.iter().any(|mapping| {
            matches!(
                mapping.obligation().kind,
                SemanticObligationKind::LoopCarriedState
                    | SemanticObligationKind::LiveStateTransition
            )
        }) {
            invalid.push("carrier-free loop contains loop-state obligations".to_string());
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
            invalid.push("nested loop regions overlap source obligations".to_string());
        }

        HeaderTestedLoopAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            remaining_obligation_residuals: self.has_remaining_obligation_residuals(),
        }
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
pub struct HeaderTestedLoopAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    remaining_obligation_residuals: bool,
}

impl HeaderTestedLoopAuditReport {
    /// Whether every selected header/body obligation is accounted exactly once
    /// and the sealed routing shape is intact. This may still be true with
    /// residual obligations and never authorizes rendering or execution.
    pub fn has_exact_loop_accounting(&self) -> bool {
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
