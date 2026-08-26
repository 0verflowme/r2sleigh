//! Authority-bound observations of the legacy renderer's final AST decisions.
//!
//! This module owns the only production allocator for render observation IDs.
//! It is intentionally not wired into lowering yet: Stage 5 callers will mark
//! exact occurrences, run every AST rewrite, then seal the dense source V/U/W
//! snapshot from the final wrapped nodes.

#![allow(
    dead_code,
    reason = "Stage 5 journal foundation is sealed before production cutover"
)]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use r2ssa::{
    InstId, MachineUseDisposition, MachineWriteDisposition, SSAFunction, SemanticObligationId,
    SsaArtifact, SsaArtifactAuthority, UseSite, ValueId,
};
use r2types::SourceOwnedFunctionFacts;

use crate::ast::{
    BinaryOp, CExpr, CFunction, CStmt, RenderObservationInspectError, RenderObservationNode,
    RenderObservationStripError, inspect_and_strip_render_observations,
    inspect_render_observations,
};
use crate::binding_plan::{BindingPlan, BindingPlanSourceMismatch, ValueDisposition};
use crate::codegen::{EmissionReadyFunction, prepare_function_for_emission};
use crate::normalize::{
    NormalizationOriginError, NormalizationOrigins, NormalizedOpProjection, NormalizedOpSite,
};
use crate::shadow_report::{
    LegacyAnalysisSnapshot, LegacyBindingId, LegacyUseCell, LegacyUseObservation, LegacyValueCell,
    LegacyValueObservation, LegacyWriteCell, LegacyWriteObservation,
};
use crate::symbol::{SymbolId, SymbolTable};
use crate::{
    BindingMachineProjectionFailure, BindingObservationJournalFailure,
    BindingShadowAuditFailure,
};

/// Opaque dense identity of one exact marked AST occurrence.
///
/// It is deliberately neither serializable nor deserializable. Production
/// construction is private to [`LegacyObservationJournal`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RenderObservationId(u32);

impl RenderObservationId {
    pub(crate) const fn index(self) -> u32 {
        self.0
    }

    pub(crate) fn from_dense_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("validated observation domain fits u32"))
    }

    #[cfg(test)]
    pub(crate) const fn from_index(index: u32) -> Self {
        Self(index)
    }
}

/// Capability required to expose a marked emission tree for journal sealing.
/// Its constructor is private to this module, so no other lowering or codegen
/// caller can bypass the marked-draft boundary.
pub(crate) struct ObservationSealAuthority(());

impl ObservationSealAuthority {
    fn new() -> Self {
        Self(())
    }
}

#[cfg(test)]
pub(crate) const fn test_render_observation_id(index: u32) -> RenderObservationId {
    RenderObservationId::from_index(index)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservationTarget {
    Value(ValueId),
    Use {
        site: UseSite,
        observation: LegacyUseObservation,
    },
    Write {
        inst: InstId,
        observation: LegacyWriteObservation,
    },
    /// One exact cell from the source-owned semantic obligation inventory.
    ///
    /// Unlike the legacy fold-side proof vector, this target belongs to one
    /// concrete AST occurrence. If a later rewrite deletes that occurrence,
    /// the final inspection never visits this target and therefore cannot
    /// count the obligation as rendered.
    Effect(SemanticObligationId),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum LegacyObservationJournalError {
    SourceAuthority,
    BindingPlan(BindingPlanSourceMismatch),
    Normalization(NormalizationOriginError),
    TooManyObservations,
    InvalidValue(ValueId),
    InvalidUse(UseSite),
    InvalidWrite(InstId),
    InvalidEffectObligation(SemanticObligationId),
    OutputlessWrite(InstId),
    InvalidNormalizedSite(NormalizedOpSite),
    MissingNormalizedBlock(u64),
    MissingNormalizedSiteContext,
    InvalidNormalizedInput {
        site: NormalizedOpSite,
        input_idx: usize,
    },
    MissingNormalizedOutput(NormalizedOpSite),
    RefusedRenderedUse(UseSite),
    RefusedRenderedWrite(InstId),
    RenderedValueRequired(ValueId),
    PlannedElidedValueRendered {
        value: ValueId,
        reason: r2ssa::ledger::ElisionReason,
    },
    PlannedRefusedValueRendered {
        value: ValueId,
        reason: crate::binding_plan::ValueRefusal,
    },
    MissingPlannedValue(ValueId),
    InvalidPlannedInline {
        value: ValueId,
        expr: r2ssa::MachineExprId,
    },
    ExactUseRequiresRenderedOccurrence(UseSite),
    ExactWriteRequiresRenderedOccurrence(InstId),
    SymbolTableMismatch,
    UnownedBindingSymbol {
        value: ValueId,
        symbol: SymbolId,
    },
    ConflictingValue(ValueId),
    ConflictingUse(UseSite),
    ConflictingWrite(InstId),
    Markers(RenderObservationStripError),
}

impl From<&r2ssa::MachineBuildError> for BindingMachineProjectionFailure {
    fn from(error: &r2ssa::MachineBuildError) -> Self {
        use r2ssa::MachineBuildError as Error;
        match error {
            Error::UntrustedArtifactProvenance => Self::UntrustedArtifactProvenance,
            Error::IncompleteObligationInventory => Self::IncompleteObligationInventory,
            Error::MissingGraphValue(value) => Self::MissingGraphValue { value: *value },
            Error::MissingGraphBlock(block) => Self::MissingGraphBlock { block: *block },
            Error::DuplicateBlockAddress(address) => {
                Self::DuplicateBlockAddress { address: *address }
            }
            Error::TopologyMismatch => Self::TopologyMismatch,
            Error::MachineContextMismatch => Self::MachineContextMismatch,
            Error::MissingInstruction(inst) => Self::MissingInstruction { inst: *inst },
            Error::MissingInstructionDisposition(inst) => {
                Self::MissingInstructionDisposition { inst: *inst }
            }
            Error::MissingUseDisposition(site) => Self::MissingUseDisposition { site: *site },
            Error::MissingWriteDisposition(inst) => Self::MissingWriteDisposition { inst: *inst },
            Error::MissingOutput(inst) => Self::MissingOutput { inst: *inst },
            Error::InvalidValueWidth { value, size_bytes } => Self::InvalidValueWidth {
                value: *value,
                size_bytes: *size_bytes,
            },
            Error::ConstantTooWide { value, width_bits } => Self::ConstantTooWide {
                value: *value,
                width_bits: *width_bits,
            },
            Error::WrongOperandCount {
                inst,
                expected,
                actual,
            } => Self::WrongOperandCount {
                inst: *inst,
                expected: *expected,
                actual: *actual,
            },
            Error::WidthMismatch {
                inst,
                expected_bits,
                actual_bits,
            } => Self::WidthMismatch {
                inst: *inst,
                expected_bits: *expected_bits,
                actual_bits: *actual_bits,
            },
            Error::InvalidCastWidth {
                inst,
                kind,
                from_bits,
                to_bits,
            } => Self::InvalidCastWidth {
                inst: *inst,
                kind: *kind,
                from_bits: *from_bits,
                to_bits: *to_bits,
            },
            Error::InvalidSubpiece {
                inst,
                source_bits,
                result_bits,
                lsb_bits,
            } => Self::InvalidSubpiece {
                inst: *inst,
                source_bits: *source_bits,
                result_bits: *result_bits,
                lsb_bits: *lsb_bits,
            },
            Error::InvalidChild { expr, child } => Self::InvalidChild {
                expr_index: expr.index(),
                child_index: child.index(),
            },
            Error::InvalidExpressionType { expr } => Self::InvalidExpressionType {
                expr_index: expr.index(),
            },
            Error::DuplicateEntity(value) => Self::DuplicateEntity { value: *value },
            Error::EntityMismatch(inst) => Self::EntityMismatch { inst: *inst },
            Error::ObligationMismatch(inst) => Self::ObligationMismatch { inst: *inst },
            Error::UseDispositionMismatch(site) => Self::UseDispositionMismatch { site: *site },
            Error::WriteDispositionMismatch(inst) => Self::WriteDispositionMismatch { inst: *inst },
            Error::ObligationSourceMismatch(instruction) => Self::ObligationSourceMismatch {
                instruction: *instruction,
            },
            Error::UnsupportedOperation { inst, .. } => Self::UnsupportedOperation { inst: *inst },
        }
    }
}

fn binding_plan_failure(error: &BindingPlanSourceMismatch) -> BindingObservationJournalFailure {
    match error {
        BindingPlanSourceMismatch::Authority => {
            BindingObservationJournalFailure::BindingPlanAuthority
        }
        BindingPlanSourceMismatch::MachineProjection(error) => {
            BindingObservationJournalFailure::BindingPlanMachineProjection(error.into())
        }
        BindingPlanSourceMismatch::ValueTopology { index, value } => {
            BindingObservationJournalFailure::BindingPlanValueTopology {
                index: *index,
                value: *value,
            }
        }
        BindingPlanSourceMismatch::DispositionCount { expected, actual } => {
            BindingObservationJournalFailure::BindingPlanDispositionCount {
                expected: *expected,
                actual: *actual,
            }
        }
        BindingPlanSourceMismatch::BindingCount { expected, actual } => {
            BindingObservationJournalFailure::BindingPlanBindingCount {
                expected: *expected,
                actual: *actual,
            }
        }
        BindingPlanSourceMismatch::InvalidBindingReference { value, binding } => {
            BindingObservationJournalFailure::BindingPlanInvalidBindingReference {
                value: *value,
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::NonBoundValue { value } => {
            BindingObservationJournalFailure::BindingPlanNonBoundValue { value: *value }
        }
        BindingPlanSourceMismatch::CertificateMembership { binding } => {
            BindingObservationJournalFailure::BindingPlanCertificateMembership {
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::DeclarationWidth { binding } => {
            BindingObservationJournalFailure::BindingPlanDeclarationWidth {
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::InvalidLiteralInline { value } => {
            BindingObservationJournalFailure::BindingPlanInvalidLiteralInline { value: *value }
        }
        BindingPlanSourceMismatch::InvalidElisionProof { value } => {
            BindingObservationJournalFailure::BindingPlanInvalidElisionProof { value: *value }
        }
        BindingPlanSourceMismatch::UnexpectedValueDisposition { value } => {
            BindingObservationJournalFailure::BindingPlanUnexpectedValueDisposition {
                value: *value,
            }
        }
        BindingPlanSourceMismatch::StackObjectCount { expected, actual } => {
            BindingObservationJournalFailure::BindingPlanStackObjectCount {
                expected: *expected,
                actual: *actual,
            }
        }
        BindingPlanSourceMismatch::UnexpectedStackObjectDisposition { object } => {
            BindingObservationJournalFailure::BindingPlanUnexpectedStackObjectDisposition {
                object: *object,
            }
        }
        BindingPlanSourceMismatch::StackObjectCertificate { object, binding } => {
            BindingObservationJournalFailure::BindingPlanStackObjectCertificate {
                object: *object,
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::StackObjectDeclarationWidth { object, binding } => {
            BindingObservationJournalFailure::BindingPlanStackObjectDeclarationWidth {
                object: *object,
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::ParameterCount { expected, actual } => {
            BindingObservationJournalFailure::BindingPlanParameterCount {
                expected: *expected,
                actual: *actual,
            }
        }
        BindingPlanSourceMismatch::UnexpectedParameterDisposition { slot } => {
            BindingObservationJournalFailure::BindingPlanUnexpectedParameterDisposition {
                slot: *slot,
            }
        }
        BindingPlanSourceMismatch::ParameterCertificate { slot, binding } => {
            BindingObservationJournalFailure::BindingPlanParameterCertificate {
                slot: *slot,
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::ParameterDeclarationWidth { slot, binding } => {
            BindingObservationJournalFailure::BindingPlanParameterDeclarationWidth {
                slot: *slot,
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::ParameterRole { slot, binding } => {
            BindingObservationJournalFailure::BindingPlanParameterRole {
                slot: *slot,
                binding_index: binding.index(),
            }
        }
        BindingPlanSourceMismatch::BindingRole { binding } => {
            BindingObservationJournalFailure::BindingPlanBindingRole {
                binding_index: binding.index(),
            }
        }
    }
}

fn normalization_failure(error: NormalizationOriginError) -> BindingObservationJournalFailure {
    match error {
        NormalizationOriginError::SourceAuthority => {
            BindingObservationJournalFailure::NormalizationSourceAuthority
        }
        NormalizationOriginError::BlockTopology => {
            BindingObservationJournalFailure::NormalizationBlockTopology
        }
        NormalizationOriginError::RowCount { block } => {
            BindingObservationJournalFailure::NormalizationRowCount {
                block_address: block,
            }
        }
        NormalizationOriginError::OriginalInstruction { block, op_idx } => {
            BindingObservationJournalFailure::NormalizationOriginalInstruction {
                block_address: block,
                op_idx,
            }
        }
        NormalizationOriginError::OriginalCoverage => {
            BindingObservationJournalFailure::NormalizationOriginalCoverage
        }
        NormalizationOriginError::PhiEdge { block, op_idx } => {
            BindingObservationJournalFailure::NormalizationPhiEdge {
                block_address: block,
                op_idx,
            }
        }
        NormalizationOriginError::RelocatedInitializer { block, op_idx } => {
            BindingObservationJournalFailure::NormalizationRelocatedInitializer {
                block_address: block,
                op_idx,
            }
        }
        NormalizationOriginError::RemovedPhi => {
            BindingObservationJournalFailure::NormalizationRemovedPhi
        }
        NormalizationOriginError::RemovedPhiEdge => {
            BindingObservationJournalFailure::NormalizationRemovedPhiEdge
        }
        NormalizationOriginError::InvalidCarrierCertificates => {
            BindingObservationJournalFailure::NormalizationInvalidCarrierCertificates
        }
    }
}

impl From<&LegacyObservationJournalError> for BindingObservationJournalFailure {
    fn from(error: &LegacyObservationJournalError) -> Self {
        match error {
            LegacyObservationJournalError::SourceAuthority => Self::SourceAuthority,
            LegacyObservationJournalError::BindingPlan(error) => binding_plan_failure(error),
            LegacyObservationJournalError::Normalization(error) => normalization_failure(*error),
            LegacyObservationJournalError::TooManyObservations => Self::TooManyObservations,
            LegacyObservationJournalError::InvalidValue(value) => {
                Self::InvalidValue { value: *value }
            }
            LegacyObservationJournalError::InvalidUse(site) => Self::InvalidUse { site: *site },
            LegacyObservationJournalError::InvalidWrite(inst) => Self::InvalidWrite { inst: *inst },
            LegacyObservationJournalError::InvalidEffectObligation(obligation) => {
                Self::InvalidEffectObligation {
                    obligation: *obligation,
                }
            }
            LegacyObservationJournalError::OutputlessWrite(inst) => {
                Self::OutputlessWrite { inst: *inst }
            }
            LegacyObservationJournalError::InvalidNormalizedSite(site) => {
                Self::InvalidNormalizedSite {
                    block: site.block,
                    op_idx: site.op_idx,
                }
            }
            LegacyObservationJournalError::MissingNormalizedBlock(address) => {
                Self::MissingNormalizedBlock { address: *address }
            }
            LegacyObservationJournalError::MissingNormalizedSiteContext => {
                Self::MissingNormalizedSiteContext
            }
            LegacyObservationJournalError::InvalidNormalizedInput { site, input_idx } => {
                Self::InvalidNormalizedInput {
                    block: site.block,
                    op_idx: site.op_idx,
                    input_idx: *input_idx,
                }
            }
            LegacyObservationJournalError::MissingNormalizedOutput(site) => {
                Self::MissingNormalizedOutput {
                    block: site.block,
                    op_idx: site.op_idx,
                }
            }
            LegacyObservationJournalError::RefusedRenderedUse(site) => {
                Self::RefusedRenderedUse { site: *site }
            }
            LegacyObservationJournalError::RefusedRenderedWrite(inst) => {
                Self::RefusedRenderedWrite { inst: *inst }
            }
            LegacyObservationJournalError::RenderedValueRequired(value) => {
                Self::RenderedValueRequired { value: *value }
            }
            LegacyObservationJournalError::PlannedElidedValueRendered { value, .. } => {
                Self::PlannedElidedValueRendered { value: *value }
            }
            LegacyObservationJournalError::PlannedRefusedValueRendered { value, .. } => {
                Self::PlannedRefusedValueRendered { value: *value }
            }
            LegacyObservationJournalError::MissingPlannedValue(value) => {
                Self::MissingPlannedValue { value: *value }
            }
            LegacyObservationJournalError::InvalidPlannedInline { value, expr } => {
                Self::InvalidPlannedInline {
                    value: *value,
                    expr_index: expr.index(),
                }
            }
            LegacyObservationJournalError::ExactUseRequiresRenderedOccurrence(site) => {
                Self::ExactUseRequiresRenderedOccurrence { site: *site }
            }
            LegacyObservationJournalError::ExactWriteRequiresRenderedOccurrence(inst) => {
                Self::ExactWriteRequiresRenderedOccurrence { inst: *inst }
            }
            LegacyObservationJournalError::SymbolTableMismatch => Self::SymbolTableMismatch,
            LegacyObservationJournalError::UnownedBindingSymbol { value, symbol } => {
                Self::UnownedBindingSymbol {
                    value: *value,
                    symbol_index: symbol.index(),
                }
            }
            LegacyObservationJournalError::ConflictingValue(value) => {
                Self::ConflictingValue { value: *value }
            }
            LegacyObservationJournalError::ConflictingUse(site) => {
                Self::ConflictingUse { site: *site }
            }
            LegacyObservationJournalError::ConflictingWrite(inst) => {
                Self::ConflictingWrite { inst: *inst }
            }
            LegacyObservationJournalError::Markers(
                RenderObservationStripError::DomainTooLarge { expected_count },
            ) => Self::ObservationDomainTooLarge {
                expected_count: *expected_count,
            },
            LegacyObservationJournalError::Markers(
                RenderObservationStripError::CapacityUnavailable { expected_count },
            ) => Self::ObservationCapacityUnavailable {
                expected_count: *expected_count,
            },
            LegacyObservationJournalError::Markers(RenderObservationStripError::OutOfRange {
                id,
                expected_count,
            }) => Self::ObservationOutOfRange {
                observation_id: id.index(),
                expected_count: *expected_count,
            },
            LegacyObservationJournalError::Markers(RenderObservationStripError::Duplicate {
                id,
            }) => Self::DuplicateObservation {
                observation_id: id.index(),
            },
        }
    }
}

/// Final coverage of one dense source domain after marker inspection.
///
/// The four disposition counts are deliberately disjoint. This lets an
/// external gate reconstruct the exact coverage equation instead of treating
/// refusal as a successful kind of "accounted" output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyObservationDomainCoverage {
    pub(crate) total: usize,
    pub(crate) rendered: usize,
    pub(crate) justified_elision: usize,
    pub(crate) refused: usize,
    pub(crate) unaccounted: usize,
}

impl LegacyObservationDomainCoverage {
    fn from_counts(
        total: usize,
        rendered: usize,
        justified_elision: usize,
        refused: usize,
        unaccounted: usize,
    ) -> Self {
        Self {
            total,
            rendered,
            justified_elision,
            refused,
            unaccounted,
        }
    }

    pub(crate) fn equations_hold(self) -> bool {
        self.rendered
            .checked_add(self.justified_elision)
            .and_then(|count| count.checked_add(self.refused))
            .and_then(|count| count.checked_add(self.unaccounted))
            == Some(self.total)
    }

    pub(crate) fn is_complete(self) -> bool {
        self.equations_hold() && self.unaccounted == 0
    }

    pub(crate) fn passes_quality(self) -> bool {
        self.is_complete() && self.refused == 0
    }
}

/// Dense V/U/W coverage sealed from the final marker-bearing emission tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyObservationCoverage {
    pub(crate) values: LegacyObservationDomainCoverage,
    pub(crate) uses: LegacyObservationDomainCoverage,
    pub(crate) writes: LegacyObservationDomainCoverage,
}

impl LegacyObservationCoverage {
    pub(crate) fn equations_hold(self) -> bool {
        self.values.equations_hold() && self.uses.equations_hold() && self.writes.equations_hold()
    }

    pub(crate) fn is_complete(self) -> bool {
        self.values.is_complete() && self.uses.is_complete() && self.writes.is_complete()
    }

    pub(crate) fn passes_quality(self) -> bool {
        self.values.passes_quality()
            && self.uses.passes_quality()
            && self.writes.passes_quality()
    }
}

/// One dense legacy snapshot and the independently visible coverage that
/// produced it. Missing cells remain `LegacyAbsent` in the snapshot while the
/// coverage keeps them distinguishable from explicit final decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SealedLegacyObservations {
    snapshot: LegacyAnalysisSnapshot,
    coverage: LegacyObservationCoverage,
    effects: SurvivingEffectObservations,
}

impl SealedLegacyObservations {
    pub(crate) const fn snapshot(&self) -> &LegacyAnalysisSnapshot {
        &self.snapshot
    }

    pub(crate) const fn coverage(&self) -> LegacyObservationCoverage {
        self.coverage
    }

    pub(crate) const fn effects(&self) -> &SurvivingEffectObservations {
        &self.effects
    }
}

/// Final occurrence counts for the canonical source obligation domain.
///
/// The map is opened from the source inventory before lowering. A zero count
/// therefore means that no marker for that exact source cell survived the
/// finished AST; it never means that the source cell was omitted from the
/// accounting domain. Counts remain visible so duplicated render occurrences
/// cannot collapse into a misleading boolean "rendered" answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SurvivingEffectObservations {
    occurrences: BTreeMap<SemanticObligationId, usize>,
}

impl SurvivingEffectObservations {
    fn empty(source: &SsaArtifact) -> Self {
        Self {
            occurrences: source
                .obligations()
                .obligations()
                .keys()
                .map(|id| (*id, 0))
                .collect(),
        }
    }

    pub(crate) fn occurrence_count(&self, id: SemanticObligationId) -> Option<usize> {
        self.occurrences.get(&id).copied()
    }

    pub(crate) fn surviving(
        &self) -> impl Iterator<Item = (SemanticObligationId, usize)> + '_ {
        self.occurrences
            .iter()
            .filter_map(|(id, count)| (*count > 0).then_some((*id, *count)))
    }
}

/// Sealed, source-authority-bound recorder for one legacy rendering run.
pub(crate) struct LegacyObservationJournal {
    authority: SsaArtifactAuthority,
    plan: Rc<BindingPlan>,
    normalized_projections: Vec<Box<[NormalizedOpProjection]>>,
    symbols: Rc<RefCell<SymbolTable>>,
    value_is_literal: Box<[bool]>,
    values: Box<[Option<LegacyValueObservation>]>,
    uses: Box<[Box<[Option<LegacyUseObservation>]>]>,
    write_has_output: Box<[bool]>,
    writes: Box<[Option<LegacyWriteObservation>]>,
    effect_occurrences: BTreeMap<SemanticObligationId, usize>,
    targets: Vec<ObservationTarget>,
}

enum LegacyObservationSeal {
    Complete(SealedLegacyObservations),
    BindingFailure {
        error: LegacyObservationJournalError,
        effects: SurvivingEffectObservations,
    },
}

/// Internal ownership boundary for an AST that may still contain markers.
///
/// There is deliberately no function accessor. A marked tree can become
/// visible to another decompiler module only by sealing it, which first runs
/// emission preparation and then strips every marker transactionally.
pub(crate) struct MarkedNativeDraft {
    function: CFunction,
    journal: LegacyObservationJournal,
    placement: Option<NativePlacementInput>,
}

struct NativePlacementInput {
    regions: crate::structured_region::SealedStructuredRegionArtifact,
    names: Rc<crate::binding_plan::BindingNameResolution>,
}

#[derive(Debug)]
enum NativePlacementFailure {
    Analysis(crate::placement::PlacementAnalysisError),
    Application(crate::placement::PlacementApplicationError),
    MissingBindingRole { binding: crate::binding_plan::BindingId },
    UndeclaredNames { count: usize },
    RegionFinalization(crate::structured_region::StructuredRegionFinalizationError),
}

impl MarkedNativeDraft {
    pub(crate) fn new(function: CFunction, journal: LegacyObservationJournal) -> Self {
        Self {
            function,
            journal,
            placement: None,
        }
    }

    pub(crate) fn new_with_placement(
        function: CFunction,
        journal: LegacyObservationJournal,
        regions: Option<crate::structured_region::SealedStructuredRegionArtifact>,
        names: Rc<crate::binding_plan::BindingNameResolution>,
    ) -> Self {
        Self {
            function,
            journal,
            placement: regions.map(|regions| NativePlacementInput { regions, names }),
        }
    }

    fn derive_and_apply_placement(
        &mut self,
        source: &SourceOwnedFunctionFacts,
    ) -> Result<(), NativePlacementFailure> {
        let Some(placement) = self.placement.as_ref() else {
            return Ok(());
        };
        let occurrences = crate::placement::collect_final_placement_occurrences(
            &self.function,
            &placement.regions,
            source.source(),
            &placement.names,
            self.journal.placement_target_count(),
            |id| self.journal.placement_target(id),
        )
        .map_err(NativePlacementFailure::Analysis)?;
        let mut externally_declared = BTreeSet::new();
        for (binding, _) in placement.names.plan().bindings() {
            match placement.names.binding_is_externally_declared(binding) {
                Some(true) => {
                    externally_declared.insert(binding);
                }
                Some(false) => {}
                None => return Err(NativePlacementFailure::MissingBindingRole { binding }),
            }
        }
        let decisions = crate::placement::derive_placement_decisions(
            &placement.regions,
            source.source().function(),
            placement.names.plan().binding_count(),
            &externally_declared,
            occurrences.reads(),
            occurrences.writes(),
        )
        .map_err(NativePlacementFailure::Analysis)?;
        crate::placement::apply_placement_decisions(
            &mut self.function,
            &placement.regions,
            &placement.names,
            &decisions,
            occurrences.writes(),
        )
        .map_err(NativePlacementFailure::Application)?;
        let undeclared = crate::unrendered::names_mentioned_without_a_declaration(&self.function);
        if !undeclared.is_empty() {
            return Err(NativePlacementFailure::UndeclaredNames {
                count: undeclared.len(),
            });
        }
        Ok(())
    }

    pub(crate) fn seal(
        self,
        source: &SourceOwnedFunctionFacts,
    ) -> Result<SealedNativeFunction, LegacyObservationJournalError> {
        let mut ready = prepare_function_for_emission(&self.function);
        let plan = Rc::clone(&self.journal.plan);
        let observations = self.journal.seal(source, &mut ready)?;
        Ok(SealedNativeFunction {
            ready,
            observations: Some(observations),
            fallback_effects: None,
            effect_audit: crate::EffectObligationAudit::NOT_RUN,
            observation_failure: None,
            plan,
        })
    }

    /// Finish the native product without allowing shadow-audit failure to
    /// change the rendered program.
    ///
    /// The strict [`Self::seal`] API remains available to tests of the journal
    /// contract. Production shadowing uses this boundary: a failed audit is
    /// retained as unavailable evidence, every internal marker is discarded,
    /// and the same prepared native AST remains the emission product.
    pub(crate) fn finish_non_consuming(
        mut self,
        source: &SourceOwnedFunctionFacts,
        recording_failure: Option<LegacyObservationJournalError>,
    ) -> SealedNativeFunction {
        let placement_failure = self.derive_and_apply_placement(source).err();
        let mut ready = prepare_function_for_emission(&self.function);
        let plan = Rc::clone(&self.journal.plan);
        let (observations, fallback_effects, observation_failure) = if let Some(error) = recording_failure {
            let effects = match self.journal.seal_effects_only(source, &mut ready) {
                Ok(effects) => effects,
                Err(_) => {
                    let mut authority = ObservationSealAuthority::new();
                    ready.discard_observation_markers(&mut authority);
                    SurvivingEffectObservations::empty(source.source())
                }
            };
            (
                None,
                Some(effects),
                Some(BindingShadowAuditFailure::JournalRecording(
                    BindingObservationJournalFailure::from(&error),
                )),
            )
        } else {
            match self.journal.seal_preserving_effects(source, &mut ready) {
                Ok(LegacyObservationSeal::Complete(observations)) => {
                    (Some(observations), None, None)
                }
                Ok(LegacyObservationSeal::BindingFailure { error, effects }) => {
                    let mut authority = ObservationSealAuthority::new();
                    ready.discard_observation_markers(&mut authority);
                    (
                        None,
                        Some(effects),
                        Some(BindingShadowAuditFailure::JournalSeal(
                            BindingObservationJournalFailure::from(&error),
                        )),
                    )
                }
                Err(error) => {
                    let mut authority = ObservationSealAuthority::new();
                    ready.discard_observation_markers(&mut authority);
                    (
                        None,
                        Some(SurvivingEffectObservations::empty(source.source())),
                        Some(BindingShadowAuditFailure::JournalSeal(
                            BindingObservationJournalFailure::from(&error),
                        )),
                    )
                }
            }
        };
        let region_failure = if placement_failure.is_none() {
            self.placement.as_ref().and_then(|placement| {
                ready
                    .strip_structured_region_markers(&placement.regions)
                    .err()
                    .map(NativePlacementFailure::RegionFinalization)
            })
        } else {
            None
        };
        if let Some(failure) = placement_failure.or(region_failure) {
            let function_name = ready.function().name.clone();
            ready = prepare_function_for_emission(
                &crate::residual_function_for_render_boundary(
                    &function_name,
                    &format!("placement refusal: {failure:?}"),
                ),
            );
        }
        SealedNativeFunction {
            ready,
            observations,
            fallback_effects,
            effect_audit: crate::EffectObligationAudit::NOT_RUN,
            observation_failure,
            plan,
        }
    }
}

/// Marker-free exact emission tree paired with the observations sealed from it.
pub(crate) struct SealedNativeFunction {
    ready: EmissionReadyFunction,
    observations: Option<SealedLegacyObservations>,
    /// Exact effect stream when the independent legacy V/U/W audit failed.
    /// A run owns effects here or inside `observations`, never in both.
    fallback_effects: Option<SurvivingEffectObservations>,
    effect_audit: crate::EffectObligationAudit,
    observation_failure: Option<BindingShadowAuditFailure>,
    plan: Rc<BindingPlan>,
}

impl SealedNativeFunction {
    /// Build a marker-free native product when the observation journal could
    /// not be initialized. The missing audit remains explicit to the caller.
    pub(crate) fn without_observations(
        function: CFunction,
        plan: Rc<BindingPlan>,
        source: &SsaArtifact,
        failure: BindingShadowAuditFailure,
    ) -> Self {
        Self {
            ready: prepare_function_for_emission(&function),
            observations: None,
            fallback_effects: Some(SurvivingEffectObservations::empty(source)),
            effect_audit: crate::EffectObligationAudit::NOT_RUN,
            observation_failure: Some(failure),
            plan,
        }
    }

    pub(crate) const fn emission(&self) -> &EmissionReadyFunction {
        &self.ready
    }

    pub(crate) fn observations(&self) -> &LegacyAnalysisSnapshot {
        self.observations
            .as_ref()
            .map(SealedLegacyObservations::snapshot)
            .expect("strictly sealed native function must retain observations")
    }

    pub(crate) fn observation_coverage(&self) -> LegacyObservationCoverage {
        self.observations
            .as_ref()
            .map(SealedLegacyObservations::coverage)
            .expect("strictly sealed native function must retain observation coverage")
    }

    pub(crate) fn audit_observations(
        &self,
    ) -> Result<(&LegacyAnalysisSnapshot, LegacyObservationCoverage), BindingShadowAuditFailure> {
        self.observations
            .as_ref()
            .map(|observations| (observations.snapshot(), observations.coverage()))
            .ok_or_else(|| {
                self.observation_failure
                    .expect("missing observations retain a typed failure category")
            })
    }

    pub(crate) fn plan(&self) -> &BindingPlan {
        &self.plan
    }

    pub(crate) fn effect_observations(&self) -> &SurvivingEffectObservations {
        self.observations
            .as_ref()
            .map(SealedLegacyObservations::effects)
            .or(self.fallback_effects.as_ref())
            .expect("every native function retains the source effect domain")
    }

    /// Finalize native admission from the exact sealed effect stream.
    ///
    /// The public audit retains the tuple even when admission fails. Refused
    /// output is comment-only: keeping the executable body beside a refusal
    /// would still expose unproven semantics to ordinary decompile callers.
    pub(crate) fn finalize_effect_ledger(&mut self, ledger: &r2ssa::ledger::ObligationLedger) {
        self.effect_audit = crate::EffectObligationAudit::from_ledger(ledger);
        if !self.effect_audit.is_admitted() {
            let function_name = self.ready.function().name.clone();
            let reason = format!(
                "r2dec residual: source effect closure refused native C ({} refused, {} unaccounted, {} conflicting)",
                self.effect_audit.refused,
                self.effect_audit.unaccounted,
                self.effect_audit.conflicts,
            );
            self.ready = prepare_function_for_emission(
                &crate::residual_function_for_render_boundary(&function_name, &reason),
            );
        }
        let mut function = self.ready.function().clone();
        crate::note_unproven_constructs(&mut function, Some(ledger));
        self.ready = prepare_function_for_emission(&function);
    }

    pub(crate) const fn effect_obligation_audit(&self) -> crate::EffectObligationAudit {
        self.effect_audit
    }

    pub(crate) fn into_function(self) -> CFunction {
        self.ready.into_function()
    }
}

impl LegacyObservationJournal {
    pub(crate) fn placement_target_count(&self) -> usize {
        self.targets.len()
    }

    pub(crate) fn placement_target(
        &self,
        id: RenderObservationId,
    ) -> Option<crate::placement::PlacementObservationTarget> {
        match self.targets.get(id.index() as usize)? {
            ObservationTarget::Use { site, .. } => {
                Some(crate::placement::PlacementObservationTarget::Use(*site))
            }
            ObservationTarget::Write { inst, .. } => {
                Some(crate::placement::PlacementObservationTarget::Write(*inst))
            }
            ObservationTarget::Value(_) | ObservationTarget::Effect(_) => {
                Some(crate::placement::PlacementObservationTarget::Other)
            }
        }
    }

    pub(crate) fn new(
        source: &SourceOwnedFunctionFacts,
        normalized: &SSAFunction,
        origins: &NormalizationOrigins,
        plan: Rc<BindingPlan>,
        symbols: Rc<RefCell<SymbolTable>>,
    ) -> Result<Self, LegacyObservationJournalError> {
        plan.validate_source(source.source())
            .map_err(LegacyObservationJournalError::BindingPlan)?;
        origins
            .validate(normalized, source.source(), source.report().render())
            .map_err(LegacyObservationJournalError::Normalization)?;

        let graph = source.source().graph();
        let mut normalized_projections: Vec<Box<[NormalizedOpProjection]>> =
            vec![Vec::new().into_boxed_slice(); graph.blocks.len()];
        for block_id in graph.block_order.iter().copied() {
            let block = graph
                .block(block_id)
                .and_then(|block| normalized.get_block(block.addr))
                .ok_or(LegacyObservationJournalError::Normalization(
                    NormalizationOriginError::BlockTopology,
                ))?;
            let rows = (0..block.ops.len())
                .map(|op_idx| {
                    let site = NormalizedOpSite {
                        block: block_id,
                        op_idx,
                    };
                    origins
                        .projection(site, source.source())
                        .map_err(LegacyObservationJournalError::Normalization)?
                        .ok_or(LegacyObservationJournalError::InvalidNormalizedSite(site))
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_boxed_slice();
            normalized_projections[block_id.0 as usize] = rows;
        }
        let value_is_literal = graph
            .values
            .iter()
            .map(|value| value.var.constant_bits().is_some())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let values = vec![None; graph.values.len()].into_boxed_slice();
        let uses = graph
            .insts
            .iter()
            .map(|inst| vec![None; inst.inputs.len()].into_boxed_slice())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let write_has_output = graph
            .insts
            .iter()
            .map(|inst| inst.output.is_some())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let writes = vec![None; graph.insts.len()].into_boxed_slice();
        let effect_occurrences = source
            .source()
            .obligations()
            .obligations()
            .keys()
            .copied()
            .map(|id| (id, 0))
            .collect();

        let mut journal = Self {
            authority: source.source().authority().clone(),
            plan,
            normalized_projections,
            symbols,
            value_is_literal,
            values,
            uses,
            write_has_output,
            writes,
            effect_occurrences,
            targets: Vec::new(),
        };
        journal.record_upstream_nonrendered_dispositions(source, origins)?;
        Ok(journal)
    }

    /// Seed only decisions whose upstream disposition proves that no rendered
    /// occurrence may exist. Bound, inline, and exact machine cells remain
    /// absent until a marker actually survives final emission.
    fn record_upstream_nonrendered_dispositions(
        &mut self,
        source: &SourceOwnedFunctionFacts,
        origins: &NormalizationOrigins,
    ) -> Result<(), LegacyObservationJournalError> {
        let graph = source.source().graph();
        let nonrendered_values = (0..self.values.len())
            .filter_map(|index| {
                let value = ValueId(index as u32);
                matches!(
                    self.plan.disposition(value),
                    Some(ValueDisposition::Elided { .. } | ValueDisposition::Refused { .. })
                )
                .then_some(value)
            })
            .collect::<Vec<_>>();
        let mut elided_uses =
            std::collections::BTreeMap::<UseSite, r2ssa::ledger::ElisionReason>::new();
        let mut elided_writes =
            std::collections::BTreeMap::<InstId, r2ssa::ledger::ElisionReason>::new();
        for value in source.source().unobserved_merges().iter() {
            let Some(inst) = graph.def_inst(value) else {
                return Err(LegacyObservationJournalError::InvalidValue(value));
            };
            let Some(definition) = graph.inst(inst) else {
                return Err(LegacyObservationJournalError::InvalidWrite(inst));
            };
            if !matches!(definition.payload, r2ssa::InstPayload::Phi { .. })
                || definition.output != Some(value)
            {
                return Err(LegacyObservationJournalError::InvalidWrite(inst));
            }
            elided_writes.insert(inst, r2ssa::ledger::ElisionReason::UnobservedMerge);
            for input_idx in 0..definition.inputs.len() {
                elided_uses.insert(
                    UseSite { inst, input_idx },
                    r2ssa::ledger::ElisionReason::UnobservedMerge,
                );
            }
        }
        for site in origins.noop_sites() {
            match elided_uses
                .insert(site, r2ssa::ledger::ElisionReason::RedundantPhiEdge)
            {
                Some(r2ssa::ledger::ElisionReason::RedundantPhiEdge) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
            }
        }
        let refused_uses = self
            .plan
            .machine_projection()
            .use_dispositions()
            .iter()
            .enumerate()
            .flat_map(|(inst, row)| {
                row.iter().enumerate().filter_map(move |(input_idx, disposition)| {
                    matches!(disposition, MachineUseDisposition::Refused(_)).then_some(UseSite {
                        inst: InstId(inst as u32),
                        input_idx,
                    },
                        )
                })
            })
            .collect::<Vec<_>>();
        let refused_writes = self
            .plan
            .machine_projection()
            .write_dispositions()
            .iter()
            .enumerate()
            .filter_map(|(inst, disposition)| {
                matches!(disposition, Some(MachineWriteDisposition::Refused(_)))
                    .then_some(InstId(inst as u32))
            })
            .collect::<Vec<_>>();

        for value in nonrendered_values {
            self.record_nonrendered_value(value)?;
        }
        for (site, reason) in elided_uses {
            let slot = self.use_slot_mut(site)?;
            record_same(slot, LegacyUseObservation::Elided(reason))
                .map_err(|()| LegacyObservationJournalError::ConflictingUse(site))?;
        }
        for (inst, reason) in elided_writes {
            let slot = self.write_slot_mut(inst)?;
            record_same(slot, LegacyWriteObservation::Elided(reason))
                .map_err(|()| LegacyObservationJournalError::ConflictingWrite(inst))?;
        }
        for site in refused_uses {
            self.record_refused_use(site)?;
        }
        for inst in refused_writes {
            self.record_refused_write(inst)?;
        }
        Ok(())
    }

    fn allocate_pair(
        &mut self,
        first: ObservationTarget,
        second: ObservationTarget,
    ) -> Result<(RenderObservationId, RenderObservationId), LegacyObservationJournalError> {
        let first_index = u32::try_from(self.targets.len())
            .map_err(|_| LegacyObservationJournalError::TooManyObservations)?;
        let second_index = first_index
            .checked_add(1)
            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        self.targets.push(first);
        self.targets.push(second);
        Ok((
            RenderObservationId(first_index),
            RenderObservationId(second_index),
        ))
    }

    fn allocate_many(
        &mut self,
        targets: Vec<ObservationTarget>,
    ) -> Result<Vec<RenderObservationId>, LegacyObservationJournalError> {
        let first = u32::try_from(self.targets.len())
            .map_err(|_| LegacyObservationJournalError::TooManyObservations)?;
        let count = u32::try_from(targets.len())
            .map_err(|_| LegacyObservationJournalError::TooManyObservations)?;
        if count > 0 {
            first
                .checked_add(count - 1)
                .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        }
        let ids = (0..count)
            .map(|offset| RenderObservationId(first + offset))
            .collect();
        self.targets.extend(targets);
        Ok(ids)
    }

    fn duplicate_observation_target(
        &mut self,
        id: RenderObservationId,
    ) -> Result<RenderObservationId, LegacyObservationJournalError> {
        let index = usize::try_from(id.index()).map_err(|_| {
            LegacyObservationJournalError::Markers(RenderObservationStripError::OutOfRange {
                id,
                expected_count: self.targets.len(),
            })
        })?;
        let target = self.targets.get(index).cloned().ok_or_else(|| {
            LegacyObservationJournalError::Markers(RenderObservationStripError::OutOfRange {
                id,
                expected_count: self.targets.len(),
            })
        })?;
        self.allocate_many(vec![target])?
            .into_iter()
            .next()
            .ok_or(LegacyObservationJournalError::TooManyObservations)
    }

    /// Clone a cached semantic fold while assigning fresh IDs to its concrete
    /// AST occurrence. The new IDs retain the exact authority-bound targets of
    /// the cached template; no use, value, or write identity is reconstructed.
    pub(crate) fn clone_render_occurrence(
        &mut self,
        stmts: &[CStmt],
    ) -> Result<Vec<CStmt>, LegacyObservationJournalError> {
        let mut clone = stmts.to_vec();
        crate::ast::remap_render_observation_ids(&mut clone, &mut |id| {
            self.duplicate_observation_target(id)
        })?;
        Ok(clone)
    }

    fn allocate_normalized_output_targets(
        &mut self,
        site: NormalizedOpSite,
    ) -> Result<(RenderObservationId, RenderObservationId), LegacyObservationJournalError> {
        let output = self.normalized_output(site)?;
        self.value_slot(output.value)?;
        let write = self.rendered_write_observation(output.inst)?;
        self.allocate_pair(
            ObservationTarget::Value(output.value),
            ObservationTarget::Write {
                inst: output.inst,
                observation: write,
            },
        )
    }

    /// Mark one value occurrence and every original use represented by the
    /// exact normalized operand that produced it.
    ///
    /// Callers cannot supply a `ValueId`, `UseSite`, or machine disposition:
    /// all three come from the authority-checked normalization projection and
    /// binding plan retained by this journal.
    pub(crate) fn observe_normalized_input_expr(
        &mut self,
        site: NormalizedOpSite,
        input_idx: usize,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let marked = self.observe_normalized_input_value_expr(site, input_idx, expr)?;
        self.observe_normalized_input_uses_expr(site, input_idx, marked)
    }

    /// Mark the base SSA value before any per-use machine projection is
    /// applied. This keeps one value disposition independent from the several
    /// exact widths or slices at which that value may be consumed.
    pub(crate) fn observe_normalized_input_value_expr(
        &mut self,
        site: NormalizedOpSite,
        input_idx: usize,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let input = self
            .normalized_projection(site)?
            .inputs
            .get(input_idx)
            .cloned()
            .ok_or(LegacyObservationJournalError::InvalidNormalizedInput { site, input_idx })?;
        let value = input.value;
        self.value_slot(value)?;
        let id = self
            .allocate_many(vec![ObservationTarget::Value(value)])?
            .into_iter()
            .next()
            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        Ok(CExpr::observed(id, expr))
    }

    /// Mark every exact original use outside the already-projected expression.
    pub(crate) fn observe_normalized_input_uses_expr(
        &mut self,
        site: NormalizedOpSite,
        input_idx: usize,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let input = self
            .normalized_projection(site)?
            .inputs
            .get(input_idx)
            .cloned()
            .ok_or(LegacyObservationJournalError::InvalidNormalizedInput { site, input_idx })?;
        let mut targets = Vec::with_capacity(input.uses.len());
        for use_site in input.uses {
            let observation = self.rendered_use_observation(use_site)?;
            targets.push(ObservationTarget::Use {
                site: use_site,
                observation,
            });
        }
        let mut marked = expr;
        for id in self.allocate_many(targets)? {
            marked = CExpr::observed(id, marked);
        }
        Ok(marked)
    }

    /// Mark one rendered definition and its source write using the exact
    /// normalized output projection.
    pub(crate) fn observe_normalized_output_stmt(
        &mut self,
        site: NormalizedOpSite,
        stmt: CStmt,
    ) -> Result<CStmt, LegacyObservationJournalError> {
        let (value_id, write_id) = self.allocate_normalized_output_targets(site)?;
        Ok(CStmt::observed(write_id, CStmt::observed(value_id, stmt)))
    }

    /// Mark one rendered definition that survives inside an expression.
    ///
    /// This is the expression twin of [`Self::observe_normalized_output_stmt`].
    /// Both value and write identity come exclusively from the authority-bound
    /// normalized output projection retained by this journal.
    pub(crate) fn observe_normalized_output_expr(
        &mut self,
        site: NormalizedOpSite,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let (value_id, write_id) = self.allocate_normalized_output_targets(site)?;
        Ok(CExpr::observed(write_id, CExpr::observed(value_id, expr)))
    }

    fn allocate_effect_targets(
        &mut self,
        obligation_ids: &BTreeSet<SemanticObligationId>,
    ) -> Result<Vec<RenderObservationId>, LegacyObservationJournalError> {
        for id in obligation_ids {
            if !self.effect_occurrences.contains_key(id) {
                return Err(LegacyObservationJournalError::InvalidEffectObligation(*id));
            }
        }
        self.allocate_many(
            obligation_ids
                .iter()
                .copied()
                .map(ObservationTarget::Effect)
                .collect(),
        )
    }

    /// Attach exact source-obligation cells to one concrete statement.
    ///
    /// Call this only after the upstream render certificate has selected the
    /// exact obligation IDs discharged by the construct. The IDs are checked
    /// against this journal's source-owned inventory, allocated in canonical
    /// order, and counted only if this statement occurrence reaches sealing.
    pub(crate) fn observe_effect_stmt(
        &mut self,
        obligation_ids: &BTreeSet<SemanticObligationId>,
        stmt: CStmt,
    ) -> Result<CStmt, LegacyObservationJournalError> {
        let mut marked = stmt;
        for id in self.allocate_effect_targets(obligation_ids)? {
            marked = CStmt::observed(id, marked);
        }
        Ok(marked)
    }

    /// Expression twin of [`Self::observe_effect_stmt`].
    pub(crate) fn observe_effect_expr(
        &mut self,
        obligation_ids: &BTreeSet<SemanticObligationId>,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let mut marked = expr;
        for id in self.allocate_effect_targets(obligation_ids)? {
            marked = CExpr::observed(id, marked);
        }
        Ok(marked)
    }

    /// Record a value only when the sealed plan proves that no rendered AST
    /// occurrence is allowed for it.
    pub(crate) fn record_nonrendered_value(
        &mut self,
        value: ValueId,
    ) -> Result<(), LegacyObservationJournalError> {
        let observation = match self.plan.disposition(value) {
            Some(ValueDisposition::Elided { reason, .. }) => {
                LegacyValueObservation::Elided(*reason)
            }
            Some(ValueDisposition::Refused { reason }) => LegacyValueObservation::Refused(*reason),
            Some(ValueDisposition::Bound { .. } | ValueDisposition::Inline { .. }) | None => {
                return Err(LegacyObservationJournalError::RenderedValueRequired(value));
            }
        };
        let slot = self.value_slot_mut(value)?;
        record_same(slot, observation)
            .map_err(|()| LegacyObservationJournalError::ConflictingValue(value))
    }

    /// Record an upstream refusal for a use that therefore has no AST node.
    pub(crate) fn record_refused_use(
        &mut self,
        site: UseSite,
    ) -> Result<(), LegacyObservationJournalError> {
        let observation = match self.plan.use_disposition(site) {
            Some(MachineUseDisposition::Refused(reason)) => LegacyUseObservation::Refused(*reason),
            Some(
                MachineUseDisposition::Exact(_) | MachineUseDisposition::MemoryAddress(_))
            | None => {
                return Err(
                    LegacyObservationJournalError::ExactUseRequiresRenderedOccurrence(site),
                );
            }
        };
        let slot = self.use_slot_mut(site)?;
        record_same(slot, observation)
            .map_err(|()| LegacyObservationJournalError::ConflictingUse(site))
    }

    /// Record an upstream refusal for a write that therefore has no AST node.
    pub(crate) fn record_refused_write(
        &mut self,
        inst: InstId,
    ) -> Result<(), LegacyObservationJournalError> {
        let observation = match self.plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Refused(reason)) => {
                LegacyWriteObservation::Refused(*reason)
            }
            Some(MachineWriteDisposition::Exact(_)) | None => {
                return Err(
                    LegacyObservationJournalError::ExactWriteRequiresRenderedOccurrence(inst),
                );
            }
        };
        let slot = self.write_slot_mut(inst)?;
        record_same(slot, observation)
            .map_err(|()| LegacyObservationJournalError::ConflictingWrite(inst))
    }

    fn normalized_projection(
        &self,
        site: NormalizedOpSite,
    ) -> Result<&NormalizedOpProjection, LegacyObservationJournalError> {
        self.normalized_projections
            .get(site.block.0 as usize)
            .and_then(|rows| rows.get(site.op_idx))
            .ok_or(LegacyObservationJournalError::InvalidNormalizedSite(site))
    }

    fn normalized_output(
        &self,
        site: NormalizedOpSite,
    ) -> Result<crate::normalize::NormalizedOutputProjection, LegacyObservationJournalError> {
        self.normalized_projection(site)?
            .output
            .ok_or(LegacyObservationJournalError::MissingNormalizedOutput(site))
    }

    fn rendered_use_observation(
        &self,
        site: UseSite,
    ) -> Result<LegacyUseObservation, LegacyObservationJournalError> {
        match self.plan.use_disposition(site) {
            Some(MachineUseDisposition::Exact(slice)) => Ok(LegacyUseObservation::Exact(*slice)),
            Some(MachineUseDisposition::MemoryAddress(address)) => {
                Ok(LegacyUseObservation::MemoryAddress(*address))
            }
            Some(MachineUseDisposition::Refused(_)) => {
                Err(LegacyObservationJournalError::RefusedRenderedUse(site))
            }
            None => Err(LegacyObservationJournalError::InvalidUse(site)),
        }
    }

    fn rendered_write_observation(
        &self,
        inst: InstId,
    ) -> Result<LegacyWriteObservation, LegacyObservationJournalError> {
        match self.plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Exact(write)) => {
                Ok(LegacyWriteObservation::Exact(*write))
            }
            Some(MachineWriteDisposition::Refused(_)) => {
                Err(LegacyObservationJournalError::RefusedRenderedWrite(inst))
            }
            None => Err(LegacyObservationJournalError::InvalidWrite(inst)),
        }
    }

    /// Seal only the source-effect occurrence stream.
    ///
    /// Binding shadow recording is diagnostic and may already have failed by
    /// this point. Effect markers have an independent source domain, so that
    /// failure must not erase the exact effect occurrences that reached the
    /// final emission tree.
    fn seal_effects_only(
        self,
        source: &SourceOwnedFunctionFacts,
        ready: &mut EmissionReadyFunction,
    ) -> Result<SurvivingEffectObservations, LegacyObservationJournalError> {
        if self.authority != *source.source().authority() {
            return Err(LegacyObservationJournalError::SourceAuthority);
        }
        let mut seal_authority = ObservationSealAuthority::new();
        let function = ready.function_mut_for_observation_seal(&mut seal_authority);
        let mut effect_occurrences = self.effect_occurrences;
        let targets = self.targets;
        inspect_and_strip_render_observations(
            function,
            targets.len(),
            |id, _node| -> Result<(), LegacyObservationJournalError> {
                let target = targets.get(id.index() as usize).copied().ok_or_else(|| {
                    LegacyObservationJournalError::Markers(
                        RenderObservationStripError::OutOfRange {
                            id,
                            expected_count: targets.len(),
                        },
                    )
                })?;
                if let ObservationTarget::Effect(id) = target {
                    let occurrences = effect_occurrences
                        .get_mut(&id)
                        .ok_or(LegacyObservationJournalError::InvalidEffectObligation(id))?;
                    *occurrences = occurrences
                        .checked_add(1)
                        .ok_or(LegacyObservationJournalError::TooManyObservations)?;
                }
                Ok(())
            },
        )
        .map_err(|error| match error {
            RenderObservationInspectError::Markers(error) => {
                LegacyObservationJournalError::Markers(error)
            }
            RenderObservationInspectError::Observer(error) => error,
        })?;
        Ok(SurvivingEffectObservations {
            occurrences: effect_occurrences,
        })
    }

    pub(crate) fn seal(
        self,
        source: &SourceOwnedFunctionFacts,
        ready: &mut EmissionReadyFunction,
    ) -> Result<SealedLegacyObservations, LegacyObservationJournalError> {
        match self.seal_preserving_effects(source, ready)? {
            LegacyObservationSeal::Complete(observations) => Ok(observations),
            LegacyObservationSeal::BindingFailure { error, .. } => Err(error),
        }
    }

    /// Inspect the final marker tree once, always accumulating the independent
    /// effect stream while retaining the first legacy binding-classification
    /// failure. A binding failure leaves the marker tree unchanged so the
    /// caller can discard it only after taking ownership of the effect counts.
    fn seal_preserving_effects(
        mut self,
        source: &SourceOwnedFunctionFacts,
        ready: &mut EmissionReadyFunction,
    ) -> Result<LegacyObservationSeal, LegacyObservationJournalError> {
        if self.authority != *source.source().authority() {
            return Err(LegacyObservationJournalError::SourceAuthority);
        }
        let mut seal_authority = ObservationSealAuthority::new();
        let function = ready.function_mut_for_observation_seal(&mut seal_authority);
        if !Rc::ptr_eq(&self.symbols, &function.symbols) {
            return Err(LegacyObservationJournalError::SymbolTableMismatch);
        }

        let mut values = std::mem::take(&mut self.values);
        let mut uses = std::mem::take(&mut self.uses);
        let mut writes = std::mem::take(&mut self.writes);
        let mut effect_occurrences = std::mem::take(&mut self.effect_occurrences);
        let targets = &self.targets;
        let value_is_literal = &self.value_is_literal;
        let plan = &self.plan;
        let symbol_bindings = declared_legacy_bindings(function);
        let mut binding_failure = None;
        inspect_render_observations(
            function,
            targets.len(),
            |id, node| -> Result<(), LegacyObservationJournalError> {
                let target = targets.get(id.index() as usize).copied().ok_or_else(|| {
                    LegacyObservationJournalError::Markers(
                        RenderObservationStripError::OutOfRange {
                            id,
                            expected_count: targets.len(),
                        },
                    )
                })?;
                if binding_failure.is_some() && !matches!(target, ObservationTarget::Effect(_)) {
                    return Ok(());
                }
                let result = match target {
                    ObservationTarget::Value(value) => {
                        match plan.disposition(value) {
                            Some(ValueDisposition::Elided { reason, .. }) => {
                                binding_failure = Some(
                                    LegacyObservationJournalError::PlannedElidedValueRendered {
                                        value,
                                        reason: *reason,
                                    },
                                );
                                return Ok(());
                            }
                            Some(ValueDisposition::Refused { reason }) => {
                                binding_failure = Some(
                                    LegacyObservationJournalError::PlannedRefusedValueRendered {
                                        value,
                                        reason: *reason,
                                    },
                                );
                                return Ok(());
                            }
                            Some(ValueDisposition::Bound { .. } | ValueDisposition::Inline { .. },
                            )
                            | None => {}
                        }
                        classify_value_node(value, node, value_is_literal, &symbol_bindings)
                            .and_then(|observation| {
                                record_same(&mut values[value.0 as usize], observation).map_err(
                                    |()| LegacyObservationJournalError::ConflictingValue(value),
                                )
                            })
                    }
                    ObservationTarget::Use { site, observation } => {
                        record_same(&mut uses[site.inst.0 as usize][site.input_idx], observation)
                            .map_err(|()| LegacyObservationJournalError::ConflictingUse(site))
                    }
                    ObservationTarget::Write { inst, observation } => {
                        record_same(&mut writes[inst.0 as usize], observation)
                            .map_err(|()| LegacyObservationJournalError::ConflictingWrite(inst))
                    }
                    ObservationTarget::Effect(id) => {
                        let occurrences = effect_occurrences
                            .get_mut(&id)
                            .ok_or(LegacyObservationJournalError::InvalidEffectObligation(id))?;
                        *occurrences = occurrences
                            .checked_add(1)
                            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
                        return Ok(());
                    }
                };
                if let Err(error) = result {
                    binding_failure = Some(error);
                }
                Ok(())
            },
        )
        .map_err(|error| match error {
            RenderObservationInspectError::Markers(error) => {
                LegacyObservationJournalError::Markers(error)
            }
            RenderObservationInspectError::Observer(error) => error,
        })?;

        if let Some(error) = binding_failure {
            return Ok(LegacyObservationSeal::BindingFailure {
                error,
                effects: SurvivingEffectObservations {
                    occurrences: effect_occurrences,
                },
            });
        }

        let mut seal_authority = ObservationSealAuthority::new();
        ready.discard_observation_markers(&mut seal_authority);
        self.values = values;
        self.uses = uses;
        self.writes = writes;
        self.effect_occurrences = effect_occurrences;
        Ok(LegacyObservationSeal::Complete(
            self.into_sealed_observations(source),
        ))
    }

    fn final_coverage(&self) -> LegacyObservationCoverage {
        let value_total = self.values.len();
        let value_rendered = self
            .values
            .iter()
            .filter(|cell| {
                matches!(
                    cell,
                    Some(
                        LegacyValueObservation::Bound { .. }
                            | LegacyValueObservation::InlineConstant
                            | LegacyValueObservation::InlineNonLiteral
                    )
                )
            })
            .count();
        let value_justified_elision = self
            .values
            .iter()
            .filter(|cell| matches!(cell, Some(LegacyValueObservation::Elided(_))))
            .count();
        let value_refused = self
            .values
            .iter()
            .filter(|cell| matches!(cell, Some(LegacyValueObservation::Refused(_))))
            .count();
        let value_unaccounted = self.values.iter().filter(|cell| cell.is_none()).count();

        let use_total = self.uses.iter().map(|row| row.len()).sum();
        let use_rendered = self
            .uses
            .iter()
            .flat_map(|row| row.iter())
            .filter(|cell| {
                matches!(
                    cell,
                    Some(
                        LegacyUseObservation::Exact(_)
                            | LegacyUseObservation::MemoryAddress(_)
                    )
                )
            })
            .count();
        let use_refused = self
            .uses
            .iter()
            .flat_map(|row| row.iter())
            .filter(|cell| matches!(cell, Some(LegacyUseObservation::Refused(_))))
            .count();
        let use_justified_elision = self
            .uses
            .iter()
            .flat_map(|row| row.iter())
            .filter(|cell| matches!(cell, Some(LegacyUseObservation::Elided(_))))
            .count();
        let use_unaccounted = self
            .uses
            .iter()
            .flat_map(|row| row.iter())
            .filter(|cell| cell.is_none())
            .count();

        let write_total = self
            .write_has_output
            .iter()
            .filter(|has_output| **has_output)
            .count();
        let write_rendered = self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .filter(|(cell, has_output)| {
                **has_output && matches!(cell, Some(LegacyWriteObservation::Exact(_)))
            })
            .count();
        let write_refused = self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .filter(|(cell, has_output)| {
                **has_output && matches!(cell, Some(LegacyWriteObservation::Refused(_)))
            })
            .count();
        let write_justified_elision = self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .filter(|(cell, has_output)| {
                **has_output && matches!(cell, Some(LegacyWriteObservation::Elided(_)))
            })
            .count();
        let write_unaccounted = self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .filter(|(cell, has_output)| **has_output && cell.is_none())
            .count();

        LegacyObservationCoverage {
            values: LegacyObservationDomainCoverage::from_counts(
                value_total,
                value_rendered,
                value_justified_elision,
                value_refused,
                value_unaccounted,
            ),
            uses: LegacyObservationDomainCoverage::from_counts(
                use_total,
                use_rendered,
                use_justified_elision,
                use_refused,
                use_unaccounted,
            ),
            writes: LegacyObservationDomainCoverage::from_counts(
                write_total,
                write_rendered,
                write_justified_elision,
                write_refused,
                write_unaccounted,
            ),
        }
    }

    fn into_sealed_observations(
        mut self,
        source: &SourceOwnedFunctionFacts,
    ) -> SealedLegacyObservations {
        let coverage = self.final_coverage();
        let effects = SurvivingEffectObservations {
            occurrences: std::mem::take(&mut self.effect_occurrences),
        };
        let snapshot = self.into_snapshot(source);
        SealedLegacyObservations {
            snapshot,
            coverage,
            effects,
        }
    }

    fn into_snapshot(self, source: &SourceOwnedFunctionFacts) -> LegacyAnalysisSnapshot {
        let values = self
            .values
            .into_vec()
            .into_iter()
            .enumerate()
            .map(|(index, observation)| LegacyValueCell {
                value: ValueId(index as u32),
                observation: observation.unwrap_or(LegacyValueObservation::LegacyAbsent),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let uses = self
            .uses
            .into_vec()
            .into_iter()
            .enumerate()
            .map(|(inst, row)| {
                row.into_vec()
                    .into_iter()
                    .enumerate()
                    .map(|(input_idx, observation)| LegacyUseCell {
                        site: UseSite {
                            inst: InstId(inst as u32),
                            input_idx,
                        },
                        observation: observation.unwrap_or(LegacyUseObservation::LegacyAbsent),
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice()
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let writes = self
            .writes
            .into_vec()
            .into_iter()
            .zip(self.write_has_output)
            .enumerate()
            .map(|(index, (observation, has_output))| {
                has_output.then_some(LegacyWriteCell {
                    inst: InstId(index as u32),
                    observation: observation.unwrap_or(LegacyWriteObservation::LegacyAbsent),
                })
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        LegacyAnalysisSnapshot::new(source, values, uses, writes)
    }

    fn value_slot(
        &self,
        value: ValueId,
    ) -> Result<&Option<LegacyValueObservation>, LegacyObservationJournalError> {
        self.values
            .get(value.0 as usize)
            .ok_or(LegacyObservationJournalError::InvalidValue(value))
    }

    fn value_slot_mut(
        &mut self,
        value: ValueId,
    ) -> Result<&mut Option<LegacyValueObservation>, LegacyObservationJournalError> {
        self.values
            .get_mut(value.0 as usize)
            .ok_or(LegacyObservationJournalError::InvalidValue(value))
    }

    fn use_slot(
        &self,
        site: UseSite,
    ) -> Result<&Option<LegacyUseObservation>, LegacyObservationJournalError> {
        self.uses
            .get(site.inst.0 as usize)
            .and_then(|row| row.get(site.input_idx))
            .ok_or(LegacyObservationJournalError::InvalidUse(site))
    }

    fn use_slot_mut(
        &mut self,
        site: UseSite,
    ) -> Result<&mut Option<LegacyUseObservation>, LegacyObservationJournalError> {
        self.uses
            .get_mut(site.inst.0 as usize)
            .and_then(|row| row.get_mut(site.input_idx))
            .ok_or(LegacyObservationJournalError::InvalidUse(site))
    }

    fn write_slot(
        &self,
        inst: InstId,
    ) -> Result<&Option<LegacyWriteObservation>, LegacyObservationJournalError> {
        let has_output = self
            .write_has_output
            .get(inst.0 as usize)
            .copied()
            .ok_or(LegacyObservationJournalError::InvalidWrite(inst))?;
        if !has_output {
            return Err(LegacyObservationJournalError::OutputlessWrite(inst));
        }
        self.writes
            .get(inst.0 as usize)
            .ok_or(LegacyObservationJournalError::InvalidWrite(inst))
    }

    fn write_slot_mut(
        &mut self,
        inst: InstId,
    ) -> Result<&mut Option<LegacyWriteObservation>, LegacyObservationJournalError> {
        self.write_slot(inst)?;
        Ok(&mut self.writes[inst.0 as usize])
    }
}

fn record_same<T: Copy + Eq>(slot: &mut Option<T>, observation: T) -> Result<(), ()> {
    match slot {
        Some(existing) if *existing != observation => Err(()),
        Some(_) => Ok(()),
        None => {
            *slot = Some(observation);
            Ok(())
        }
    }
}

fn classify_value_node(
    value: ValueId,
    node: RenderObservationNode<'_>,
    value_is_literal: &[bool],
    symbol_bindings: &BTreeMap<SymbolId, LegacyBindingId>,
) -> Result<LegacyValueObservation, LegacyObservationJournalError> {
    let (expr, statement_level) = match node {
        RenderObservationNode::Expr(expr) => (expr.unobserved(), false),
        RenderObservationNode::Stmt(stmt) => match stmt.unobserved() {
            CStmt::Decl { name, .. } => return classify_symbol(value, *name, symbol_bindings),
            CStmt::Expr(expr) => (expr.unobserved(), true),
            CStmt::Return(Some(expr)) => (expr.unobserved(), false),
            _ => return Ok(LegacyValueObservation::InlineNonLiteral),
        },
    };
    if let CExpr::Var(symbol) = expr {
        return classify_symbol(value, *symbol, symbol_bindings);
    }
    if let CExpr::Binary { op, left, .. } = expr
        && (*op == BinaryOp::Assign
            || (statement_level
                && matches!(
                    op,
                    BinaryOp::AddAssign
                        | BinaryOp::SubAssign
                        | BinaryOp::MulAssign
                        | BinaryOp::DivAssign
                        | BinaryOp::ModAssign
                        | BinaryOp::BitAndAssign
                        | BinaryOp::BitOrAssign
                        | BinaryOp::BitXorAssign
                        | BinaryOp::ShlAssign
                        | BinaryOp::ShrAssign
                )))
        && let CExpr::Var(symbol) = left.unobserved()
    {
        return classify_symbol(value, *symbol, symbol_bindings);
    }
    let source_literal = value_is_literal
        .get(value.0 as usize)
        .copied()
        .ok_or(LegacyObservationJournalError::InvalidValue(value))?;
    if source_literal
        && matches!(
            expr,
            CExpr::IntLit(_)
                | CExpr::UIntLit(_)
                | CExpr::FloatLit(_)
                | CExpr::StringLit(_)
                | CExpr::CharLit(_)
        )
    {
        Ok(LegacyValueObservation::InlineConstant)
    } else {
        Ok(LegacyValueObservation::InlineNonLiteral)
    }
}

fn classify_symbol(
    value: ValueId,
    symbol: SymbolId,
    symbol_bindings: &BTreeMap<SymbolId, LegacyBindingId>,
) -> Result<LegacyValueObservation, LegacyObservationJournalError> {
    let binding = symbol_bindings
        .get(&symbol)
        .copied()
        .ok_or(LegacyObservationJournalError::UnownedBindingSymbol {
            value,
            symbol })?;
    Ok(LegacyValueObservation::Bound { binding })
}

fn declared_legacy_bindings(function: &CFunction) -> BTreeMap<SymbolId, LegacyBindingId> {
    let mut bindings = BTreeMap::new();
    let mut mark = |symbol: SymbolId| {
        if !bindings.contains_key(&symbol) {
            let index = u32::try_from(bindings.len())
                .expect("a SymbolId-indexed table cannot exceed the legacy binding domain");
            bindings.insert(symbol, LegacyBindingId(index));
        }
    };
    for param in &function.params {
        mark(param.name);
    }
    for local in &function.locals {
        mark(local.name);
    }
    for stmt in &function.body {
        visit_stmt_declarations(stmt, &mut mark);
    }
    bindings
}

fn visit_stmt_declarations(stmt: &CStmt, visit: &mut impl FnMut(SymbolId)) {
    match stmt.unobserved() {
        CStmt::Decl { name, .. } => visit(*name),
        CStmt::Block(stmts) => {
            for stmt in stmts {
                visit_stmt_declarations(stmt, visit);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            visit_stmt_declarations(then_body, visit);
            if let Some(else_body) = else_body {
                visit_stmt_declarations(else_body, visit);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            visit_stmt_declarations(body, visit);
        }
        CStmt::StructuredRegion { stmt, .. } => visit_stmt_declarations(stmt, visit),
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                visit_stmt_declarations(init, visit);
            }
            visit_stmt_declarations(body, visit);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                for stmt in &case.body {
                    visit_stmt_declarations(stmt, visit);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    visit_stmt_declarations(stmt, visit);
                }
            }
        }
        CStmt::Observed { .. } => unreachable!("unobserved statement returned a wrapper"),
        CStmt::Expr(_)
        | CStmt::Return(_)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use r2il::{
        AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef,
        RegisterProjection, RegisterProjectionDisposition, RegisterStorage, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceFunctionInterface, SourceFunctionReturn,
        SsaArtifact,
    };

    use super::*;
    use crate::ast::{CLocal, CType};
    use crate::binding_plan::{BindingId, ValueDisposition, ValueRefusal};
    use crate::symbol::{SymbolOrigin, SymbolRole};

    fn source_owned() -> SourceOwnedFunctionFacts {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(2, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::unique(0x20, 8),
        });
        source_owned_from_blocks(&[block])
    }

    fn source_owned_from_blocks(blocks: &[R2ILBlock]) -> SourceOwnedFunctionFacts {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        arch.register_projections = [(0, 8), (0x28, 8), (0x30, 8)]
            .into_iter()
            .map(|(offset, size)| RegisterProjection {
                written: RegisterStorage { offset, size },
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: RegisterStorage { offset, size },
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: u64::from(size) * 8,
                    },
                },
            })
            .collect();
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"observation-journal-test".to_vec(),
            "sysv64",
            std::iter::empty(),
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            std::iter::empty(),
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .expect("exact test source interface");
        let source = Arc::new(
            SsaArtifact::for_decompile_with_interface(blocks, Some(&arch), interface)
                .expect("test SSA artifact"),
        );
        let request = r2types::TypeWritebackAnalysisRequest::new(
            Arc::clone(&source),
            r2types::ParsedExternalContext::default(),
        )
        .expect("source-owned request");
        r2types::build_source_owned_type_writeback_analysis(request)
            .expect("source-owned analysis")
            .finalize_for_decompile(r2types::DecompileFinalization {
                kind: r2types::DecompileRouteKind::Standard,
                reason: "observation journal test".to_string(),
                fallback_comment: None,
            })
            .expect("source-owned finalization")
    }

    fn journal_fixture() -> (
        SourceOwnedFunctionFacts,
        BindingPlan,
        CFunction,
        LegacyObservationJournal,
    ) {
        let source = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("sealed binding plan");
        let function = CFunction::new("journal", CType::Void);
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            Rc::new(plan.clone()),
            Rc::clone(&function.symbols),
        )
        .expect("authority-bound journal");
        (source, plan, function, journal)
    }

    #[test]
    fn effect_observations_count_only_final_ast_occurrences() {
        let (source, _plan, mut function, mut journal) = journal_fixture();
        let obligation = *source
            .source()
            .obligations()
            .obligations()
            .keys()
            .next()
            .expect("fixture has source obligations");
        let obligations = BTreeSet::from([obligation]);

        let surviving = journal
            .observe_effect_stmt(&obligations, CStmt::Return(None))
            .expect("source-owned effect marker");
        let deleted = journal
            .observe_effect_stmt(&obligations, CStmt::Empty)
            .expect("second concrete marker occurrence");
        function.body.push(surviving);
        drop(deleted);

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("final effect occurrences seal");
        assert_eq!(sealed.effects().occurrence_count(obligation), Some(1));
        assert_eq!(sealed.effects().surviving().collect::<Vec<_>>(), [(obligation, 1)]);
    }

    #[test]
    fn duplicate_surviving_effect_occurrence_is_a_codegen_refusal() {
        let (source, _plan, mut function, mut journal) = journal_fixture();
        let obligation = *source
            .source()
            .obligations()
            .obligations()
            .keys()
            .next()
            .expect("fixture has source obligations");
        let obligations = BTreeSet::from([obligation]);
        function.body = vec![
            journal
                .observe_effect_stmt(&obligations, CStmt::Return(None))
                .expect("first concrete effect occurrence"),
            journal
                .observe_effect_stmt(&obligations, CStmt::Return(None))
                .expect("second concrete effect occurrence"),
        ];

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("final effect occurrences seal");
        assert_eq!(sealed.effects().occurrence_count(obligation), Some(2));

        let origins =
            NormalizationOrigins::for_unchanged(source.source().function(), source.source());
        let ledger = crate::effect_ledger::build_obligation_ledger(
            source.source(),
            &origins,
            sealed.effects(),
        );
        assert_eq!(
            ledger.outcome(&obligation),
            r2ssa::ledger::Outcome::Refused {
                layer: r2ssa::ledger::LedgerLayer::Codegen,
                reason: r2ssa::ledger::RefusalReason::DuplicateRenderedOccurrence,
            }
        );
    }

    #[test]
    fn effect_observations_reject_cells_outside_source_inventory() {
        let (source, _plan, _function, mut journal) = journal_fixture();
        let mut obligation = *source
            .source()
            .obligations()
            .obligations()
            .keys()
            .next()
            .expect("fixture has source obligations");
        obligation.instruction.block_addr ^= 1;
        let obligations = BTreeSet::from([obligation]);

        assert_eq!(
            journal.observe_effect_expr(&obligations, CExpr::UIntLit(0)),
            Err(LegacyObservationJournalError::InvalidEffectObligation(
                obligation
            ))
        );
    }

    fn first_bound(plan: &BindingPlan, source: &SourceOwnedFunctionFacts) -> (ValueId, BindingId) {
        source
            .source()
            .graph()
            .values
            .iter()
            .find_map(|value| match plan.disposition(value.id) {
                Some(ValueDisposition::Bound { binding }) => Some((value.id, *binding)),
                _ => None,
            })
            .expect("fixture has a bound value")
    }

    #[test]
    fn source_certified_dead_phi_accounts_for_value_edges_and_write() {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1008, 8),
        });
        let mut left = R2ILBlock::new(0x1004, 4);
        left.push(R2ILOp::Copy {
            dst: Varnode::unique(0x90, 8),
            src: Varnode::constant(11, 8),
        });
        left.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut right = R2ILBlock::new(0x1008, 4);
        right.push(R2ILOp::Copy {
            dst: Varnode::unique(0x90, 8),
            src: Varnode::constant(12, 8),
        });
        right.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut join = R2ILBlock::new(0x100c, 4);
        join.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let source = source_owned_from_blocks(&[entry, left, right, join]);
        let dead = source
            .source()
            .unobserved_merges()
            .iter()
            .find(|value| {
                source.source().graph().value(*value).is_some_and(|value| {
                    value.canonical_storage.is_some_and(|storage| {
                        storage.space == CanonicalStorageSpace::Unique
                            && storage.offset == 0x90
                            && storage.size == 8
                    })
                })
            })
            .expect("unused unique-space merge");
        let definition = source
            .source()
            .graph()
            .def_inst(dead)
            .expect("dead merge definition");
        let input_count = source
            .source()
            .graph()
            .inst(definition)
            .expect("dead merge instruction")
            .inputs
            .len();
        let plan = Rc::new(BindingPlan::build_shadow(&source).expect("dead-merge-aware plan"));
        let function = CFunction::new("dead_phi", CType::Void);
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            plan,
            Rc::clone(&function.symbols),
        )
        .expect("journal seeds exact dead-phi cells");
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("empty output keeps certified elisions");

        assert_eq!(
            sealed.snapshot().value_observation(dead),
            Some(LegacyValueObservation::Elided(
                r2ssa::ledger::ElisionReason::UnobservedMerge
            ))
        );
        for input_idx in 0..input_count {
            assert_eq!(
                sealed.snapshot().use_observation(UseSite {
                    inst: definition,
                    input_idx,
                }),
                Some(LegacyUseObservation::Elided(
                    r2ssa::ledger::ElisionReason::UnobservedMerge
                ))
            );
        }
        assert_eq!(
            sealed.snapshot().write_observation(definition),
            Some(LegacyWriteObservation::Elided(
                r2ssa::ledger::ElisionReason::UnobservedMerge
            ))
        );
        assert!(sealed.coverage().equations_hold());
        assert!(sealed.coverage().values.justified_elision >= 1);
        assert!(sealed.coverage().uses.justified_elision >= input_count);
        assert!(sealed.coverage().writes.justified_elision >= 1);
    }

    #[test]
    fn normalized_identity_phi_edge_is_a_precise_elision_not_an_absence() {
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(1, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x2004, 8),
        });
        let mut header = R2ILBlock::new(0x2004, 4);
        header.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x2014, 8),
        });
        let mut choose_latch = R2ILBlock::new(0x2008, 4);
        choose_latch.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x2010, 8),
        });
        let mut identity_latch = R2ILBlock::new(0x200c, 4);
        identity_latch.push(R2ILOp::Branch {
            target: Varnode::constant(0x2004, 8),
        });
        let mut update_latch = R2ILBlock::new(0x2010, 4);
        update_latch.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        update_latch.push(R2ILOp::Branch {
            target: Varnode::constant(0x2004, 8),
        });
        let mut exit = R2ILBlock::new(0x2014, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let source = source_owned_from_blocks(&[
            entry,
            header,
            choose_latch,
            identity_latch,
            update_latch,
            exit,
        ]);
        let render = source.report().render().expect("render facts");
        let (normalized, origins) = crate::normalize::materialize_certified_loop_carriers(
            source.source().function(),
            source.source(),
            render,
        )
        .expect("certified carrier normalization");
        let noop_sites = origins.noop_sites().collect::<Vec<_>>();
        assert_eq!(noop_sites.len(), 1, "self-carried edge is the sole no-op");

        let plan = Rc::new(BindingPlan::build_shadow(&source).expect("sealed plan"));
        let function = CFunction::new("identity_phi", CType::Void);
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            plan,
            Rc::clone(&function.symbols),
        )
        .expect("normalization-backed journal");
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("no-op certificate survives sealing");

        assert_eq!(
            sealed.snapshot().use_observation(noop_sites[0]),
            Some(LegacyUseObservation::Elided(
                r2ssa::ledger::ElisionReason::RedundantPhiEdge
            ))
        );
        assert!(sealed.coverage().equations_hold());
        assert!(sealed.coverage().uses.justified_elision >= 1);
    }

    fn first_bound_rendered_input(
        plan: &BindingPlan,
        source: &SourceOwnedFunctionFacts,
    ) -> (ValueId, BindingId, NormalizedOpSite, usize) {
        let graph = source.source().graph();
        graph
            .insts
            .iter()
            .find_map(|inst| {
                let (block_addr, op_idx) = source.source().inst_op_site(inst.id)?;
                let block = graph.block_id_for_addr(block_addr)?;
                inst.inputs
                    .iter()
                    .copied()
                    .enumerate()
                    .find_map(|(input_idx, value)| {
                        let ValueDisposition::Bound { binding } = plan.disposition(value)? else {
                            return None;
                        };
                        matches!(
                            plan.use_disposition(UseSite {
                                inst: inst.id,
                                input_idx,
                            }),
                            Some(
                                MachineUseDisposition::Exact(_)
                                    | MachineUseDisposition::MemoryAddress(_)
                            )
                        )
                        .then_some((
                            value,
                            *binding,
                            NormalizedOpSite { block, op_idx },
                            input_idx,
                        ))
                    })
            })
            .expect("fixture has an exactly projected bound input")
    }

    fn first_bound_rendered_output(
        plan: &BindingPlan,
        source: &SourceOwnedFunctionFacts,
    ) -> (ValueId, BindingId, InstId, NormalizedOpSite) {
        let graph = source.source().graph();
        graph
            .insts
            .iter()
            .find_map(|inst| {
                let value = inst.output?;
                let ValueDisposition::Bound { binding } = plan.disposition(value)? else {
                    return None;
                };
                if !matches!(
                    plan.write_disposition(inst.id),
                    Some(MachineWriteDisposition::Exact(_))
                ) {
                    return None;
                }
                let (block_addr, op_idx) = source.source().inst_op_site(inst.id)?;
                let block = graph.block_id_for_addr(block_addr)?;
                Some((value, *binding, inst.id, NormalizedOpSite { block, op_idx }))
            })
            .expect("fixture has an exactly projected bound output")
    }

    fn replace_observed_expr_semantic(expr: &mut CExpr, replacement: CExpr) {
        let mut semantic = expr;
        while let CExpr::Observed { expr, .. } = semantic {
            semantic = expr;
        }
        *semantic = replacement;
    }

    fn declare_legacy_symbol(
        function: &CFunction,
        plan: &BindingPlan,
        binding: BindingId,
        name: &str,
    ) -> SymbolId {
        function.symbols.borrow_mut().declare(
            name,
            plan.binding(binding)
                .expect("dense binding")
                .declaration_type()
                .clone(),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        )
    }

    fn declare_legacy_local(
        function: &mut CFunction,
        plan: &BindingPlan,
        binding: BindingId,
        name: &str,
    ) -> SymbolId {
        let symbol = declare_legacy_symbol(function, plan, binding, name);
        function.locals.push(CLocal {
            ty: plan
                .binding(binding)
                .expect("dense binding")
                .declaration_type()
                .clone(),
            name: symbol,
            stack_offset: None,
        });
        symbol
    }

    #[test]
    fn every_private_journal_error_has_a_stable_public_seal_cause() {
        let function = CFunction::new("seal_cause", CType::Void);
        let symbol = function.symbols.borrow_mut().declare(
            "unowned",
            CType::Int(32),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        );
        let site = UseSite {
            inst: InstId(17),
            input_idx: 3,
        };
        let normalized_site = NormalizedOpSite {
            block: r2ssa::BlockId(5),
            op_idx: 7,
        };
        let marker = test_render_observation_id(11);
        let inline_expr = {
            let source = source_owned();
            let plan = BindingPlan::build_shadow(&source).expect("sealed binding plan");
            source
                .source()
                .graph()
                .values
                .iter()
                .find_map(|value| match plan.disposition(value.id) {
                    Some(ValueDisposition::Inline { expr, .. }) => Some(*expr),
                    _ => None,
                })
                .expect("fixture inline expression")
        };
        let cases = [
            (
                LegacyObservationJournalError::SourceAuthority,
                BindingObservationJournalFailure::SourceAuthority,
            ),
            (
                LegacyObservationJournalError::BindingPlan(
                    BindingPlanSourceMismatch::Authority),
                BindingObservationJournalFailure::BindingPlanAuthority,
            ),
            (
                LegacyObservationJournalError::Normalization(
                    NormalizationOriginError::BlockTopology,
                ),
                BindingObservationJournalFailure::NormalizationBlockTopology,
            ),
            (
                LegacyObservationJournalError::TooManyObservations,
                BindingObservationJournalFailure::TooManyObservations,
            ),
            (
                LegacyObservationJournalError::InvalidValue(ValueId(13)),
                BindingObservationJournalFailure::InvalidValue { value: ValueId(13) },
            ),
            (
                LegacyObservationJournalError::InvalidUse(site),
                BindingObservationJournalFailure::InvalidUse { site },
            ),
            (
                LegacyObservationJournalError::InvalidWrite(InstId(19)),
                BindingObservationJournalFailure::InvalidWrite { inst: InstId(19) },
            ),
            (
                LegacyObservationJournalError::OutputlessWrite(InstId(23)),
                BindingObservationJournalFailure::OutputlessWrite { inst: InstId(23) },
            ),
            (
                LegacyObservationJournalError::InvalidNormalizedSite(normalized_site),
                BindingObservationJournalFailure::InvalidNormalizedSite {
                    block: r2ssa::BlockId(5),
                    op_idx: 7,
                },
            ),
            (
                LegacyObservationJournalError::MissingNormalizedBlock(0x1234),
                BindingObservationJournalFailure::MissingNormalizedBlock { address: 0x1234 },
            ),
            (
                LegacyObservationJournalError::MissingNormalizedSiteContext,
                BindingObservationJournalFailure::MissingNormalizedSiteContext,
            ),
            (
                LegacyObservationJournalError::InvalidNormalizedInput {
                    site: normalized_site,
                    input_idx: 9,
                },
                BindingObservationJournalFailure::InvalidNormalizedInput {
                    block: r2ssa::BlockId(5),
                    op_idx: 7,
                    input_idx: 9,
                },
            ),
            (
                LegacyObservationJournalError::MissingNormalizedOutput(normalized_site),
                BindingObservationJournalFailure::MissingNormalizedOutput {
                    block: r2ssa::BlockId(5),
                    op_idx: 7,
                },
            ),
            (
                LegacyObservationJournalError::RefusedRenderedUse(site),
                BindingObservationJournalFailure::RefusedRenderedUse { site },
            ),
            (
                LegacyObservationJournalError::RefusedRenderedWrite(InstId(29)),
                BindingObservationJournalFailure::RefusedRenderedWrite { inst: InstId(29) },
            ),
            (
                LegacyObservationJournalError::RenderedValueRequired(ValueId(31)),
                BindingObservationJournalFailure::RenderedValueRequired { value: ValueId(31) },
            ),
            (
                LegacyObservationJournalError::PlannedElidedValueRendered {
                    value: ValueId(32),
                    reason: r2ssa::ledger::ElisionReason::DeadUnusedTemporary,
                },
                BindingObservationJournalFailure::PlannedElidedValueRendered {
                    value: ValueId(32) },
            ),
            (
                LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value: ValueId(33),
                    reason: ValueRefusal::MissingBindingCertificate {
                        value: ValueId(33) },
                },
                BindingObservationJournalFailure::PlannedRefusedValueRendered {
                    value: ValueId(33),
                },
            ),
            (
                LegacyObservationJournalError::MissingPlannedValue(ValueId(34)),
                BindingObservationJournalFailure::MissingPlannedValue {
                    value: ValueId(34) },
            ),
            (
                LegacyObservationJournalError::InvalidPlannedInline {
                    value: ValueId(35),
                    expr: inline_expr,
                },
                BindingObservationJournalFailure::InvalidPlannedInline {
                    value: ValueId(35),
                    expr_index: inline_expr.index(),
                },
            ),
            (
                LegacyObservationJournalError::ExactUseRequiresRenderedOccurrence(site),
                BindingObservationJournalFailure::ExactUseRequiresRenderedOccurrence { site },
            ),
            (
                LegacyObservationJournalError::ExactWriteRequiresRenderedOccurrence(InstId(37)),
                BindingObservationJournalFailure::ExactWriteRequiresRenderedOccurrence {
                    inst: InstId(37),
                },
            ),
            (
                LegacyObservationJournalError::SymbolTableMismatch,
                BindingObservationJournalFailure::SymbolTableMismatch,
            ),
            (
                LegacyObservationJournalError::UnownedBindingSymbol {
                    value: ValueId(40),
                    symbol,
                },
                BindingObservationJournalFailure::UnownedBindingSymbol {
                    value: ValueId(40),
                    symbol_index: symbol.index(),
                },
            ),
            (
                LegacyObservationJournalError::ConflictingValue(ValueId(41)),
                BindingObservationJournalFailure::ConflictingValue { value: ValueId(41) },
            ),
            (
                LegacyObservationJournalError::ConflictingUse(site),
                BindingObservationJournalFailure::ConflictingUse { site },
            ),
            (
                LegacyObservationJournalError::ConflictingWrite(InstId(43)),
                BindingObservationJournalFailure::ConflictingWrite { inst: InstId(43) },
            ),
            (
                LegacyObservationJournalError::Markers(
                    RenderObservationStripError::DomainTooLarge { expected_count: 47 },
                ),
                BindingObservationJournalFailure::ObservationDomainTooLarge {
                    expected_count: 47 },
            ),
            (
                LegacyObservationJournalError::Markers(
                    RenderObservationStripError::CapacityUnavailable { expected_count: 53 },
                ),
                BindingObservationJournalFailure::ObservationCapacityUnavailable {
                    expected_count: 53,
                },
            ),
            (
                LegacyObservationJournalError::Markers(
                    RenderObservationStripError::OutOfRange {
                        id: marker,
                        expected_count: 59,
                    }),
                BindingObservationJournalFailure::ObservationOutOfRange {
                    observation_id: 11,
                    expected_count: 59,
                },
            ),
            (
                LegacyObservationJournalError::Markers(RenderObservationStripError::Duplicate {
                    id: marker,
                }),
                BindingObservationJournalFailure::DuplicateObservation {
                    observation_id: 11 },
            ),
        ];

        for (private, public) in cases {
            assert_eq!(BindingObservationJournalFailure::from(&private), public);
            assert!(!public.kind().is_empty());
        }
    }

    #[test]
    fn normalized_issuance_is_idempotent_and_raw_bound_recording_is_rejected() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "old_value");
        let first = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("first projected occurrence");
        let second = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("second projected occurrence");
        function.body = vec![CStmt::Expr(first), CStmt::Expr(second)];
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("same projected cell is idempotent");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );

        let (_source, plan, _function, mut journal) = journal_fixture();
        let (value, _) = first_bound(&plan, &_source);
        assert_eq!(
            journal.record_nonrendered_value(value),
            Err(LegacyObservationJournalError::RenderedValueRequired(value))
        );
    }

    #[test]
    fn cached_render_clone_reissues_unique_ids_for_the_same_targets() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "cached_value");
        let marked = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("template occurrence");
        let template = vec![CStmt::Expr(marked)];
        let cloned = journal
            .clone_render_occurrence(&template)
            .expect("fresh cached occurrence");
        function.body.extend(template);
        function.body.extend(cloned);

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("fresh occurrence IDs must not collide");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );
    }

    #[test]
    fn normalized_output_expression_is_idempotent_and_reports_dense_coverage() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, inst, site) = first_bound_rendered_output(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "inline_output");
        let first = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("first output expression");
        let second = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("second output expression");
        function.body = vec![CStmt::Expr(first), CStmt::Expr(second)];

        let expected_write = match plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Exact(write)) => LegacyWriteObservation::Exact(*write),
            other => panic!("expected exact write, got {other:?}"),
        };
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("identical output decisions are idempotent");

        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );
        assert_eq!(
            sealed.snapshot().write_observation(inst),
            Some(expected_write)
        );

        let coverage = sealed.coverage();
        let graph = source.source().graph();
        assert_eq!(coverage.values.total, graph.values.len());
        assert_eq!(
            coverage.uses.total,
            graph
                .insts
                .iter()
                .map(|inst| inst.inputs.len())
                .sum::<usize>()
        );
        assert_eq!(
            coverage.writes.total,
            graph
                .insts
                .iter()
                .filter(|inst| inst.output.is_some())
                .count()
        );
        assert_eq!(coverage.values.rendered, 1);
        assert_eq!(coverage.uses.rendered, 0);
        assert_eq!(coverage.writes.rendered, 1);
        assert_eq!(coverage.values.refused, 0);
        assert_eq!(coverage.uses.refused, 0);
        assert_eq!(coverage.writes.refused, 0);
        assert!(coverage.equations_hold());
    }

    #[test]
    fn compound_assignment_keeps_statement_level_output_bound_to_its_lhs() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, inst, site) = first_bound_rendered_output(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "accumulator");
        let assignment = CStmt::Expr(CExpr::assign(
            CExpr::Var(symbol),
            CExpr::binary(BinaryOp::Add, CExpr::Var(symbol), CExpr::IntLit(1)),
        ));
        let marked = journal
            .observe_normalized_output_stmt(site, assignment)
            .expect("marked output statement");
        let rewritten = crate::structure::ControlFlowStructurer::cleanup(
            function.symbols.as_ref(),
            marked);
        function.body = vec![rewritten, CStmt::Return(Some(CExpr::Var(symbol)))];

        let expected_write = match plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Exact(write)) => LegacyWriteObservation::Exact(*write),
            other => panic!("expected exact write, got {other:?}"),
        };
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("compound output remains exactly classifiable");

        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );
        assert_eq!(
            sealed.snapshot().write_observation(inst),
            Some(expected_write)
        );
        assert!(matches!(
            ready.function().body.first().map(CStmt::unobserved),
            Some(CStmt::Expr(CExpr::Binary {
                op: BinaryOp::AddAssign,
                ..
            }))
        ));
    }

    #[test]
    fn conflicting_output_expression_decisions_are_transactional() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, _inst, site) = first_bound_rendered_output(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "conflicting_output");
        let bound = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("bound output expression");
        let inline = journal
            .observe_normalized_output_expr(site, CExpr::IntLit(7))
            .expect("inline output expression");
        function.body = vec![CStmt::Expr(bound), CStmt::Expr(inline)];

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let unchanged = ready.function_for_marker_test().clone();
        assert_eq!(
            journal.seal(&source, &mut ready),
            Err(LegacyObservationJournalError::ConflictingValue(value))
        );
        assert_eq!(ready.function_for_marker_test(), &unchanged);
    }

    #[test]
    fn production_binding_classification_failure_keeps_later_effect_occurrences() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, _inst, site) = first_bound_rendered_output(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "conflicting_output");
        let bound = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("bound output expression");
        let inline = journal
            .observe_normalized_output_expr(site, CExpr::IntLit(7))
            .expect("inline output expression");
        let obligation = *source
            .source()
            .obligations()
            .obligations()
            .keys()
            .next()
            .expect("fixture has a source effect");
        let effect = journal
            .observe_effect_stmt(&BTreeSet::from([obligation]), CStmt::Return(None))
            .expect("independent effect occurrence");
        function.body = vec![CStmt::Expr(bound), CStmt::Expr(inline), effect];

        let native = MarkedNativeDraft::new(function, journal)
            .finish_non_consuming(&source, None);
        assert_eq!(
            native.audit_observations(),
            Err(BindingShadowAuditFailure::JournalSeal(
                BindingObservationJournalFailure::ConflictingValue { value },
            ))
        );
        assert_eq!(
            native.effect_observations().occurrence_count(obligation),
            Some(1),
            "a V/U/W classification failure must not stop the final effect traversal"
        );
    }

    #[test]
    fn final_rewritten_node_drives_value_classification() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&function, &plan, binding, "rewritten_value");
        let marked = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        function.body = vec![CStmt::Return(Some(marked))];
        let CStmt::Return(Some(expr)) = &mut function.body[0] else {
            panic!("marked return expression")
        };
        replace_observed_expr_semantic(expr, CExpr::IntLit(7));

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("sealed final observations");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::InlineNonLiteral)
        );
        assert!(!matches!(
            &ready.function().body[0],
            CStmt::Return(Some(CExpr::Observed { .. }))
        ));
    }

    #[test]
    fn invalid_or_duplicate_markers_leave_ast_unchanged() {
        let (source, plan, mut duplicate_function, mut duplicate_journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&duplicate_function, &plan, binding, "duplicate_value");
        let marked = duplicate_journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        duplicate_function.body = vec![CStmt::Expr(marked.clone()), CStmt::Expr(marked)];
        let mut duplicate_ready =
            crate::codegen::prepare_function_for_emission(&duplicate_function);
        let unchanged = duplicate_ready.function_for_marker_test().clone();
        assert!(matches!(
            duplicate_journal.seal(&source, &mut duplicate_ready),
            Err(LegacyObservationJournalError::Markers(
                RenderObservationStripError::Duplicate { .. }
            ))
        ));
        assert_eq!(duplicate_ready.function_for_marker_test(), &unchanged);

        let (source, plan, mut range_function, mut range_journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&range_function, &plan, binding, "range_value");
        let mut marked = range_journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        let CExpr::Observed { id, .. } = &mut marked else {
            panic!("marked expression")
        };
        *id = test_render_observation_id(2);
        range_function.body = vec![CStmt::Expr(marked)];
        let mut range_ready = crate::codegen::prepare_function_for_emission(&range_function);
        let unchanged = range_ready.function_for_marker_test().clone();
        assert!(matches!(
            range_journal.seal(&source, &mut range_ready),
            Err(LegacyObservationJournalError::Markers(
                RenderObservationStripError::OutOfRange { .. }
            ))
        ));
        assert_eq!(range_ready.function_for_marker_test(), &unchanged);
    }

    #[test]
    fn production_audit_failure_keeps_the_marker_free_native_product() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&function, &plan, binding, "duplicate_native_value");
        let marked = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        let CExpr::Observed {
            id: duplicate_id, ..
        } = &marked
        else {
            panic!("rendered input must carry an observation")
        };
        let duplicate_id = duplicate_id.index();
        function.body = vec![CStmt::Expr(marked.clone()), CStmt::Expr(marked)];

        let mut expected_function = function.clone();
        crate::ast::discard_render_observations(&mut expected_function);
        let expected = crate::codegen::prepare_function_for_emission(&expected_function);
        let native =
            MarkedNativeDraft::new(function, journal).finish_non_consuming(&source, None);

        assert_eq!(
            native.audit_observations(),
            Err(BindingShadowAuditFailure::JournalSeal(
                BindingObservationJournalFailure::DuplicateObservation {
                    observation_id: duplicate_id,
                },
            ))
        );
        assert_eq!(native.emission().function(), expected.function());
        assert!(!crate::ast::has_render_observations(
            native.emission().function()
        ));
    }

    #[test]
    fn production_recording_failure_keeps_its_exact_cause_and_native_product() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&function, &plan, binding, "recording_value");
        let marked = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        let obligation = *source
            .source()
            .obligations()
            .obligations()
            .keys()
            .next()
            .expect("fixture has a source effect");
        let marked = journal
            .observe_effect_expr(&BTreeSet::from([obligation]), marked)
            .expect("independent effect marker");
        function.body = vec![CStmt::Expr(marked)];

        let mut expected_function = function.clone();
        crate::ast::discard_render_observations(&mut expected_function);
        let expected = crate::codegen::prepare_function_for_emission(&expected_function);
        let native = MarkedNativeDraft::new(function, journal).finish_non_consuming(
            &source,
            Some(LegacyObservationJournalError::MissingNormalizedSiteContext),
        );

        assert_eq!(
            native.audit_observations(),
            Err(BindingShadowAuditFailure::JournalRecording(
                BindingObservationJournalFailure::MissingNormalizedSiteContext,
            ))
        );
        assert_eq!(native.emission().function(), expected.function());
        assert!(!crate::ast::has_render_observations(
            native.emission().function()
        ));
        assert_eq!(
            native.effect_observations().occurrence_count(obligation),
            Some(1),
            "binding recording failure must not erase the final effect stream"
        );
    }

    #[test]
    fn journal_construction_does_not_allocate_candidate_symbols() {
        let (source, plan, function, _journal) = journal_fixture();
        let (_, binding) = first_bound(&plan, &source);
        let requested = plan
            .binding(binding)
            .and_then(|binding| binding.presentation_name_hint())
            .unwrap_or("candidate_name");
        let symbol = declare_legacy_symbol(&function, &plan, binding, requested);
        assert_eq!(function.symbols.borrow().name(symbol), requested);
    }

    #[test]
    fn bound_marker_requires_and_observes_a_surviving_declaration() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "surviving_value");
        function.body = vec![CStmt::Expr(
            journal
                .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
                .expect("value marker"),
        )];
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("declared binding is authoritative");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );

        let (source, plan, mut function, mut journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&function, &plan, binding, "undeclared_value");
        function.body = vec![CStmt::Expr(
            journal
                .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
                .expect("value marker"),
        )];
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let unchanged = ready.function_for_marker_test().clone();
        assert_eq!(
            journal.seal(&source, &mut ready),
            Err(LegacyObservationJournalError::UnownedBindingSymbol {
                value,
                symbol })
        );
        assert_eq!(ready.function_for_marker_test(), &unchanged);
    }
}
