//! Proof-preserving open direct-call boundaries.
//!
//! This region owns one exact, final, explicitly void direct call and its
//! source-ordered argument preparation. The callee and fallthrough are open
//! composition ports. It proves no callee behavior, post-call state, native-C
//! rendering, or whole-function semantics.

use std::collections::BTreeSet;

use r2cert::{CertifiedArtifactOrigin, CertifiedDirectCall, CertifiedSourceTerminator};
use r2ssa::{
    CallBoundarySlot, CanonicalInstructionId, SemanticObligationId, SemanticObligationKind,
    SourceCallResult, SourceCallSiteIdentity,
};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, RegionObligationDisposition, RegionObligationMapping,
};
use crate::semantic_c::{SemanticCDirectCall, SemanticCIdentityScope};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_DIRECT_CALL_REGION_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum DirectCallRegionScope {
    SingleBlockVoidDirectCallWithOpenCalleeAndFallthrough,
}

/// One exact void direct-call boundary with two deliberately open ports.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDirectCallBlockRegion {
    schema_version: u32,
    scope: DirectCallRegionScope,
    identity_scope: SemanticCIdentityScope,
    body: SemanticCBlockStepLayer,
    call_producer: CanonicalInstructionId,
    certified_call: CertifiedDirectCall,
    semantic_call: SemanticCDirectCall,
    mappings: Box<[RegionObligationMapping]>,
    open_callee_target: u64,
    open_fallthrough_successor: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectCallRegionError {
    InvalidAccounting,
    StatementLayer(SemanticCStatementError),
    ResidualObligations(Vec<SemanticObligationId>),
    UnsupportedEffects,
    MissingOrAmbiguousCall,
    CallIsNotFinalStep,
    InvalidConstructedRegion(Vec<String>),
}

impl std::fmt::Display for DirectCallRegionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "direct-call region construction failed: {self:?}")
    }
}

impl std::error::Error for DirectCallRegionError {}

impl From<SemanticCStatementError> for DirectCallRegionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::StatementLayer(error)
    }
}

impl CertifiedDirectCallBlockRegion {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, DirectCallRegionError> {
        let accounting_report = accounting.audit();
        if !accounting_report.has_exact_source_accounting() {
            return Err(DirectCallRegionError::InvalidAccounting);
        }
        if accounting_report.has_residuals() {
            return Err(DirectCallRegionError::ResidualObligations(
                accounting_report.residualized_obligations().to_vec(),
            ));
        }
        if !accounting.memory_statements().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || !accounting.return_controls().is_empty()
            || !accounting.semantic_returns().is_empty()
        {
            return Err(DirectCallRegionError::UnsupportedEffects);
        }
        let [certified_call] = accounting.direct_calls() else {
            return Err(DirectCallRegionError::MissingOrAmbiguousCall);
        };
        let [semantic_call] = accounting.semantic_calls() else {
            return Err(DirectCallRegionError::MissingOrAmbiguousCall);
        };
        if certified_call.producer() != semantic_call.producer() {
            return Err(DirectCallRegionError::MissingOrAmbiguousCall);
        }
        let call_producer = certified_call.producer();
        let Some(source_block) = accounting.source_block() else {
            return Err(DirectCallRegionError::CallIsNotFinalStep);
        };
        let topology_matches = matches!(
            source_block.terminator(),
            CertifiedSourceTerminator::Call {
                target,
                fallthrough: Some(fallthrough),
            } if *target == certified_call.target()
                && *fallthrough == certified_call.fallthrough()
        ) && source_block.successors() == [certified_call.fallthrough()]
            && accounting
                .topology()
                .block(certified_call.fallthrough())
                .is_some()
            && source_block.addr() != certified_call.target()
            && source_block.addr() != certified_call.fallthrough()
            && certified_call.target() != certified_call.fallthrough()
            && source_block.instructions().last() == Some(&call_producer);
        if !topology_matches {
            return Err(DirectCallRegionError::CallIsNotFinalStep);
        }
        let mappings = accounting.mappings().to_vec().into_boxed_slice();
        let open_callee_target = certified_call.target();
        let open_fallthrough_successor = certified_call.fallthrough();
        let certified_call = certified_call.clone();
        let semantic_call = semantic_call.clone();
        let body = SemanticCBlockStepLayer::from_accounting(accounting)?;
        if body.steps().last().map(|step| step.source()) != Some(call_producer) {
            return Err(DirectCallRegionError::CallIsNotFinalStep);
        }
        let region = Self {
            schema_version: CERTIFIED_DIRECT_CALL_REGION_SCHEMA_VERSION,
            scope: DirectCallRegionScope::SingleBlockVoidDirectCallWithOpenCalleeAndFallthrough,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            body,
            call_producer,
            certified_call,
            semantic_call,
            mappings,
            open_callee_target,
            open_fallthrough_successor,
        };
        let report = region.audit();
        if !report.has_exact_direct_call() {
            return Err(DirectCallRegionError::InvalidConstructedRegion(
                report.invalid,
            ));
        }
        Ok(region)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> DirectCallRegionScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        self.body.accounting().origin()
    }

    pub const fn body(&self) -> &SemanticCBlockStepLayer {
        &self.body
    }

    pub const fn call_producer(&self) -> CanonicalInstructionId {
        self.call_producer
    }

    pub const fn witness(&self) -> &CertifiedDirectCall {
        &self.certified_call
    }

    pub const fn call(&self) -> &SemanticCDirectCall {
        &self.semantic_call
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn raw_identity(&self) -> SourceCallSiteIdentity {
        self.certified_call.raw_identity()
    }

    pub const fn interface_revision(&self) -> &[u8] {
        self.certified_call.interface_revision()
    }

    pub fn calling_convention(&self) -> &str {
        self.certified_call.calling_convention()
    }

    /// Static callee address whose behavior remains outside this region.
    pub const fn open_callee_target(&self) -> u64 {
        self.open_callee_target
    }

    /// Normal continuation whose post-call state remains outside this region.
    pub const fn open_fallthrough_successor(&self) -> u64 {
        self.open_fallthrough_successor
    }

    /// Valid regions close selected source obligations, while both semantic ports
    /// remain open independently of obligation accounting.
    pub fn has_remaining_obligation_residuals(&self) -> bool {
        self.body.accounting().audit().has_residuals()
    }

    pub fn audit(&self) -> DirectCallRegionAuditReport {
        let accounting = self.body.accounting();
        let accounting_report = accounting.audit();
        let body_report = self.body.audit();
        let mut invalid = Vec::new();

        if self.schema_version != CERTIFIED_DIRECT_CALL_REGION_SCHEMA_VERSION {
            invalid.push("direct-call region schema mismatch".to_string());
        }
        if self.scope
            != DirectCallRegionScope::SingleBlockVoidDirectCallWithOpenCalleeAndFallthrough
        {
            invalid.push("direct-call region scope mismatch".to_string());
        }
        if self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles
            || self.identity_scope != accounting.identity_scope()
        {
            invalid.push("direct-call identity scope mismatch".to_string());
        }
        if !body_report.has_exact_source_order() || !accounting_report.has_exact_source_accounting()
        {
            invalid.push("embedded direct-call source accounting is not exact".to_string());
        }
        if accounting_report.has_residuals() {
            invalid.push("direct-call region retains residual obligations".to_string());
        }
        if !accounting.memory_statements().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || !accounting.return_controls().is_empty()
            || !accounting.semantic_returns().is_empty()
        {
            invalid.push("direct-call region contains unsupported effects or control".to_string());
        }
        if accounting.direct_calls() != [self.certified_call.clone()]
            || accounting.semantic_calls() != [self.semantic_call.clone()]
            || self.certified_call.producer() != self.call_producer
            || self.semantic_call.producer() != self.call_producer
        {
            invalid.push("direct-call evidence cardinality or producer mismatch".to_string());
        }
        if self.certified_call.call_site() != self.semantic_call.call_site()
            || self.certified_call.raw_identity() != self.semantic_call.raw_identity()
            || self.certified_call.interface_revision() != self.semantic_call.interface_revision()
            || self.certified_call.calling_convention() != self.semantic_call.calling_convention()
            || self.certified_call.target() != self.semantic_call.target()
            || self.certified_call.fallthrough() != self.semantic_call.fallthrough()
            || self.certified_call.arguments().len() != self.semantic_call.arguments().len()
            || self.certified_call.source_obligations() != *self.semantic_call.source_obligations()
        {
            invalid.push("semantic direct call differs from certified call evidence".to_string());
        }

        let source_interface = accounting
            .origin()
            .machine_context()
            .source()
            .call_site_interface(self.certified_call.call_site());
        let source_interface_matches = source_interface.is_some_and(|interface| {
            interface.identity() == self.certified_call.raw_identity()
                && interface.revision_identity() == self.certified_call.interface_revision()
                && interface.is_complete()
                && !interface.is_variadic()
                && !interface.is_noreturn()
                && interface.result() == SourceCallResult::Void
                && interface.calling_convention() == self.certified_call.calling_convention()
                && interface.arguments().len() == self.certified_call.arguments().len()
                && interface
                    .arguments()
                    .iter()
                    .zip(self.certified_call.arguments())
                    .all(|(source, certified)| {
                        matches!(
                            certified.slot(),
                            CallBoundarySlot::Register { index, storage }
                                if index == source.index() && storage == source.storage()
                        )
                    })
        });
        if !source_interface_matches
            || self.certified_call.interface_revision().is_empty()
            || self.certified_call.calling_convention().trim().is_empty()
        {
            invalid.push("call identity is not owned by the retained source interface".to_string());
        }

        let topology_matches = accounting.source_block().is_some_and(|block| {
            matches!(
                block.terminator(),
                CertifiedSourceTerminator::Call {
                    target,
                    fallthrough: Some(fallthrough),
                } if *target == self.open_callee_target
                    && *fallthrough == self.open_fallthrough_successor
            ) && block.successors() == [self.open_fallthrough_successor]
                && accounting
                    .topology()
                    .block(self.open_fallthrough_successor)
                    .is_some()
                && block.addr() != self.open_callee_target
                && block.addr() != self.open_fallthrough_successor
                && self.open_callee_target != self.open_fallthrough_successor
                && block.instructions().last() == Some(&self.call_producer)
        });
        if !topology_matches
            || self.certified_call.target() != self.open_callee_target
            || self.certified_call.fallthrough() != self.open_fallthrough_successor
            || self.body.steps().last().map(|step| step.source()) != Some(self.call_producer)
        {
            invalid.push("direct call is not the exact final open boundary".to_string());
        }

        if self.mappings.as_ref() != accounting.mappings() {
            invalid.push("direct-call mappings differ from nested accounting".to_string());
        }
        let call_obligations = self.certified_call.source_obligations();
        let mapped_call_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoCall { producer }
                        if *producer == self.call_producer
                )
                .then_some(mapping.obligation())
            })
            .collect::<BTreeSet<_>>();
        if mapped_call_obligations != call_obligations
            || mapped_call_obligations.iter().any(|obligation| {
                !matches!(
                    obligation.kind,
                    SemanticObligationKind::Call | SemanticObligationKind::CallArgument
                )
            })
            || self.mappings.iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::Residualized { .. }
                        | RegionObligationDisposition::AbsorbedIntoStatement { .. }
                        | RegionObligationDisposition::AbsorbedIntoControl { .. }
                        | RegionObligationDisposition::AbsorbedIntoReturn { .. }
                )
            })
        {
            invalid.push("direct-call obligation mappings are not exact".to_string());
        }

        DirectCallRegionAuditReport { invalid }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DirectCallRegionAuditReport {
    invalid: Vec<String>,
}

impl DirectCallRegionAuditReport {
    pub fn has_exact_direct_call(&self) -> bool {
        self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}
