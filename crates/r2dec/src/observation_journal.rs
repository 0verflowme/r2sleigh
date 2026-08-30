//! Authority-bound observations of the legacy renderer's final AST decisions.
//!
//! This module owns the only production allocator for render observation IDs.
//! Callers mark exact occurrences, run every AST rewrite, then seal the dense
//! source V/U/W snapshot from the final wrapped nodes.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use r2ssa::{
    InstId, MachineUseDisposition, MachineWriteDisposition, SSAFunction, SemanticObligationId,
    SsaArtifact, SsaArtifactAuthority, UseSite, ValueId,
};
use r2types::SourceOwnedFunctionFacts;

#[cfg(test)]
use crate::ast::inspect_and_strip_render_observations;
use crate::ast::{
    BinaryOp, CExpr, CFunction, CStmt, RenderObservationInspectError, RenderObservationNode,
    RenderObservationStripError, inspect_render_observations,
};
use crate::binding_plan::{
    BindingNameResolution, BindingPlan, BindingPlanSourceMismatch, StackObjectDisposition,
    ValueDisposition,
};
use crate::codegen::{EmissionReadyFunction, prepare_function_for_emission};
use crate::normalize::{
    NormalizationOriginError, NormalizationOrigins, NormalizedOpOrigin, NormalizedOpProjection,
    NormalizedOpSite,
};
use crate::shadow_report::{
    LegacyAnalysisSnapshot, LegacyBindingId, LegacyUseCell, LegacyUseObservation, LegacyValueCell,
    LegacyValueObservation, LegacyWriteCell, LegacyWriteObservation,
};
use crate::symbol::{SymbolId, SymbolTable};
use crate::{
    BindingMachineProjectionFailure, BindingObservationJournalFailure, BindingShadowAuditFailure,
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
    CertifiedValueRead {
        value: ValueId,
        at: InstId,
        binding: crate::binding_plan::BindingId,
        symbol: SymbolId,
    },
    Use {
        site: UseSite,
        observation: LegacyUseObservation,
        /// Where the normalized operation consuming this use is emitted.
        block: u64,
    },
    Write {
        inst: InstId,
        observation: LegacyWriteObservation,
        /// Where the normalized definition is emitted, which is not the
        /// original instruction's block when normalization materialized it.
        block: u64,
    },
    StackAccess {
        access: r2ssa::StructuredAccessId,
        object: r2ssa::ObjectId,
        binding: crate::binding_plan::BindingId,
        symbol: SymbolId,
        is_write: bool,
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
    InvalidCertifiedValueRead {
        value: ValueId,
        at: InstId,
    },
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
            LegacyObservationJournalError::InvalidCertifiedValueRead { value, at } => {
                Self::InvalidCertifiedValueRead {
                    value: *value,
                    at: *at,
                }
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
    #[cfg(test)]
    pub(crate) fn equations_hold(self) -> bool {
        self.values.equations_hold() && self.uses.equations_hold() && self.writes.equations_hold()
    }

    pub(crate) fn is_complete(self) -> bool {
        self.values.is_complete() && self.uses.is_complete() && self.writes.is_complete()
    }

    pub(crate) fn passes_quality(self) -> bool {
        self.values.passes_quality() && self.uses.passes_quality() && self.writes.passes_quality()
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
    coalesced_carriers: Box<CoalescedCarrierEffectElisions>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CoalescedCarrierEffectElisions {
    coalesced_carrier_uses: BTreeSet<UseSite>,
    coalesced_carrier_phis: BTreeSet<InstId>,
}

impl SurvivingEffectObservations {
    pub(crate) fn occurrence_count(&self, id: SemanticObligationId) -> Option<usize> {
        self.occurrences.get(&id).copied()
    }

    pub(crate) fn is_coalesced_carrier_use(&self, site: UseSite) -> bool {
        self.coalesced_carriers
            .coalesced_carrier_uses
            .contains(&site)
    }

    pub(crate) fn is_coalesced_carrier_phi(&self, inst: InstId) -> bool {
        self.coalesced_carriers
            .coalesced_carrier_phis
            .contains(&inst)
    }

    #[cfg(test)]
    pub(crate) fn surviving(&self) -> impl Iterator<Item = (SemanticObligationId, usize)> + '_ {
        self.occurrences
            .iter()
            .filter_map(|(id, count)| (*count > 0).then_some((*id, *count)))
    }
}

/// Sealed, source-authority-bound recorder for one legacy rendering run.
pub(crate) struct LegacyObservationJournal {
    authority: SsaArtifactAuthority,
    source: std::sync::Arc<SsaArtifact>,
    plan: Rc<BindingPlan>,
    names: Rc<BindingNameResolution>,
    normalized_projections: Vec<Box<[NormalizedOpProjection]>>,
    /// Synthetic carrier copies whose exact incoming use is discharged by
    /// binding coalescing. Lowering queries this same derived answer before it
    /// suppresses the `x = x` operation.
    coalesced_carrier_copy_sites: BTreeSet<NormalizedOpSite>,
    coalesced_carrier_uses: BTreeSet<UseSite>,
    /// Removed carrier phis for which every incoming edge is already accounted
    /// by SSA identity or one of `coalesced_carrier_copy_sites`.
    coalesced_carrier_phi_writes: BTreeSet<InstId>,
    /// Merges normalization removed by materializing every incoming edge, so
    /// the copies on those edges are what write them.
    materialized_removed_phis: BTreeSet<InstId>,
    /// Definitions placement dropped because nothing reads what they produce.
    placement_elided_writes: BTreeSet<InstId>,
    /// Observations that went with the statements placement discarded.
    ///
    /// Named exactly, never inferred from what is unaccounted: the seal refuses
    /// a function whose cells are empty, and filling in whatever is empty would
    /// answer that check instead of answering to it.
    placement_elided_observations: BTreeSet<crate::ast::RenderObservationId>,
    symbols: Rc<RefCell<SymbolTable>>,
    value_is_literal: Box<[bool]>,
    values: Box<[Option<LegacyValueObservation>]>,
    uses: Box<[Box<[Option<LegacyUseObservation>]>]>,
    write_has_output: Box<[bool]>,
    writes: Box<[Option<LegacyWriteObservation>]>,
    effect_occurrences: BTreeMap<SemanticObligationId, usize>,
    targets: Vec<ObservationTarget>,
}

/// Transaction boundary for render markers allocated by one tentative AST
/// route. The source V/U/W domains are immutable after journal construction;
/// only the dense target tail changes while lowering candidate trees.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ObservationJournalCheckpoint {
    target_len: usize,
}

enum LegacyObservationSeal {
    Complete(SealedLegacyObservations),
    BindingFailure(LegacyObservationJournalError),
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
    MissingStructuredRegionArtifact,
    Analysis(crate::placement::PlacementAnalysisError),
    Application(crate::placement::PlacementApplicationError),
    MissingBindingRole {
        binding: crate::binding_plan::BindingId,
    },
    UndeclaredNames {
        count: usize,
    },
    RegionFinalization(crate::structured_region::StructuredRegionFinalizationError),
}

fn region_marker_refusal(
    error: crate::structured_region::StructuredRegionFinalizationError,
) -> crate::PlacementAuditRefusal {
    use crate::PlacementAuditRefusal as Refusal;
    use crate::structured_region::StructuredRegionFinalizationError as Error;

    match error {
        Error::UnsealedMarker => Refusal::RegionMarkerUnsealed,
        Error::ForeignMarker { anchor } => Refusal::RegionMarkerForeign {
            anchor_index: anchor.index(),
        },
        Error::DuplicateMarker { region } => Refusal::RegionMarkerDuplicate {
            region_index: region.index(),
        },
        Error::MissingMarker { region } => Refusal::RegionMarkerMissing {
            region_index: region.index(),
        },
        Error::ParentMismatch { region } => Refusal::RegionMarkerParentMismatch {
            region_index: region.index(),
        },
        Error::OutOfOrder { region, expected } => Refusal::RegionMarkerOutOfOrder {
            region_index: region.index(),
            expected_region_index: expected.index(),
        },
    }
}

fn observation_marker_refusal(
    error: crate::ast::RenderObservationStripError,
) -> crate::PlacementAuditRefusal {
    use crate::PlacementAuditRefusal as Refusal;
    use crate::ast::RenderObservationStripError as Error;

    match error {
        Error::DomainTooLarge { expected_count } => {
            Refusal::ObservationDomainTooLarge { expected_count }
        }
        Error::CapacityUnavailable { expected_count } => {
            Refusal::ObservationCapacityUnavailable { expected_count }
        }
        Error::OutOfRange { id, expected_count } => Refusal::ObservationOutOfRange {
            observation_id: id.index(),
            expected_count,
        },
        Error::Duplicate { id } => Refusal::DuplicateObservation {
            observation_id: id.index(),
        },
    }
}

fn placement_refusal(
    refusal: crate::binding_plan::PlacementRefusal,
) -> crate::PlacementAuditRefusal {
    use crate::PlacementAuditRefusal as Public;
    use crate::binding_plan::PlacementRefusal as Private;

    match refusal {
        Private::NoDominatingRegion { binding } => Public::NoDominatingRegion {
            binding_index: binding.index(),
        },
        Private::MissingDefinition { binding } => Public::MissingDefinition {
            binding_index: binding.index(),
        },
        Private::ReadBeforeAssignment {
            binding,
            read: crate::binding_plan::PlacementRead::Use(site),
        } => Public::ReadBeforeAssignment {
            binding_index: binding.index(),
            instruction_id: site.inst.0,
            input_index: site.input_idx,
        },
        Private::ReadBeforeAssignment {
            binding,
            read: crate::binding_plan::PlacementRead::CertifiedValue { value, at },
        } => Public::CertifiedValueReadBeforeAssignment {
            binding_index: binding.index(),
            value_id: value.0,
            instruction_id: at.0,
        },
        Private::ReadBeforeAssignment {
            binding,
            read: crate::binding_plan::PlacementRead::StackAccess(access),
        } => Public::StackAccessReadBeforeAssignment {
            binding_index: binding.index(),
            instruction_id: access.inst.0,
            access_ordinal: access.ordinal,
        },
        Private::ReadBeforeAssignment {
            binding,
            read: crate::binding_plan::PlacementRead::PreservedCarrierWrite(inst),
        } => Public::PreservedCarrierReadBeforeAssignment {
            binding_index: binding.index(),
            instruction_id: inst.0,
        },
        Private::UnprovableExecutionOrder { binding } => Public::UnprovableExecutionOrder {
            binding_index: binding.index(),
        },
    }
}

fn placement_analysis_refusal(
    error: crate::placement::PlacementAnalysisError,
) -> crate::PlacementAuditRefusal {
    use crate::PlacementAuditRefusal as Refusal;
    use crate::placement::PlacementAnalysisError as Error;

    match error {
        Error::SourceAuthorityMismatch => Refusal::SourceAuthorityMismatch,
        Error::BindingOutsidePlan { binding } => Refusal::BindingOutsidePlan {
            binding_index: binding.index(),
        },
        Error::RegionOutsideArtifact { region } => Refusal::RegionOutsideArtifact {
            region_index: region.index(),
        },
        Error::BlockOutsideFunction { block } => Refusal::BlockOutsideFunction {
            block_address: block,
        },
        Error::RegionDoesNotDominateOccurrence { region, block } => {
            Refusal::RegionDoesNotDominateOccurrence {
                region_index: region.index(),
                block_address: block,
            }
        }
        Error::ExternalBindingOutsidePlan { binding } => Refusal::ExternalBindingOutsidePlan {
            binding_index: binding.index(),
        },
        Error::RegionMarkers(error) => region_marker_refusal(error),
        Error::ObservationMarkers(error) => observation_marker_refusal(error),
        Error::MissingObservationTarget { observation } => Refusal::MissingObservationTarget {
            observation_id: observation.index(),
        },
        Error::InvalidUse { site } => Refusal::InvalidUse {
            instruction_id: site.inst.0,
            input_index: site.input_idx,
        },
        Error::InvalidWrite { inst } => Refusal::InvalidWrite {
            instruction_id: inst.0,
        },
        Error::InvalidCertifiedValueRead { value, at } => Refusal::InvalidCertifiedValueRead {
            value_id: value.0,
            instruction_id: at.0,
        },
        Error::MissingPlannedValue { value } => Refusal::MissingPlannedValue { value_id: value.0 },
        Error::RefusedPlannedValue { value } => Refusal::RefusedPlannedValue { value_id: value.0 },
        Error::UnscopedObservation { observation } => Refusal::UnscopedObservation {
            observation_id: observation.index(),
        },
        Error::AmbiguousExecutionOrder { observation } => {
            Refusal::AmbiguousObservationExecutionOrder {
                observation_id: observation.index(),
            }
        }
        Error::UnauthorizedProgramVariable { symbol } => Refusal::UnauthorizedProgramVariable {
            symbol_index: symbol.index(),
        },
        Error::UnobservedBindingRead { binding } => Refusal::UnobservedBindingRead {
            binding_index: binding.index(),
        },
        Error::UnobservedBindingWrite { binding } => Refusal::UnobservedBindingWrite {
            binding_index: binding.index(),
        },
    }
}

fn placement_application_refusal(
    error: crate::placement::PlacementApplicationError,
) -> crate::PlacementAuditRefusal {
    use crate::PlacementAuditRefusal as Refusal;
    use crate::placement::PlacementApplicationError as Error;

    match error {
        Error::Refused(refusal) => placement_refusal(refusal),
        Error::MissingBinding { binding } => Refusal::MissingBinding {
            binding_index: binding.index(),
        },
        Error::MissingBindingSymbol { binding } => Refusal::MissingBindingSymbol {
            binding_index: binding.index(),
        },
        Error::ExternalBindingMissingParameter { binding } => {
            Refusal::ExternalBindingMissingParameter {
                binding_index: binding.index(),
            }
        }
        Error::MissingRegion { region } => Refusal::MissingRegion {
            region_index: region.index(),
        },
        Error::DuplicateRegion { region } => Refusal::DuplicateRegion {
            region_index: region.index(),
        },
        Error::MissingInlineWrite { inst } => Refusal::MissingInlineWrite {
            instruction_id: inst.0,
        },
        Error::DuplicateInlineWrite { inst } => Refusal::DuplicateInlineWrite {
            instruction_id: inst.0,
        },
    }
}

impl From<NativePlacementFailure> for crate::PlacementAuditRefusal {
    fn from(failure: NativePlacementFailure) -> Self {
        match failure {
            NativePlacementFailure::MissingStructuredRegionArtifact => {
                Self::MissingStructuredRegionArtifact
            }
            NativePlacementFailure::Analysis(error) => placement_analysis_refusal(error),
            NativePlacementFailure::Application(error) => placement_application_refusal(error),
            NativePlacementFailure::MissingBindingRole { binding } => Self::MissingBindingRole {
                binding_index: binding.index(),
            },
            NativePlacementFailure::UndeclaredNames { count } => Self::UndeclaredNames { count },
            NativePlacementFailure::RegionFinalization(error) => region_marker_refusal(error),
        }
    }
}

impl MarkedNativeDraft {
    #[cfg(test)]
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
            return Err(NativePlacementFailure::MissingStructuredRegionArtifact);
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
        let mut entry_declared = BTreeSet::new();
        for (binding, _) in placement.names.plan().bindings() {
            match placement.names.binding_is_externally_declared(binding) {
                Some(true) => {
                    externally_declared.insert(binding);
                }
                Some(false) => {}
                None => return Err(NativePlacementFailure::MissingBindingRole { binding }),
            }
            match placement.names.binding_is_entry_declared(binding) {
                Some(true) => {
                    entry_declared.insert(binding);
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
            &entry_declared,
            occurrences.reads(),
            occurrences.writes(),
        )
        .map_err(NativePlacementFailure::Analysis)?;
        // Which writes lost their statements is only known once the decisions
        // have been applied: one can be declined because the tree still
        // mentions the symbol, and one binding's removal can take away the last
        // reader of another. Asking afterwards is what keeps the obligations
        // these statements carried closed out against what was actually
        // emitted rather than against what was planned.
        let removals = crate::placement::apply_placement_decisions(
            &mut self.function,
            &placement.regions,
            &placement.names,
            &decisions,
            occurrences.writes(),
        )
        .map_err(NativePlacementFailure::Application)?;
        for binding in removals.bindings {
            for occurrence in occurrences.writes().iter().filter(|w| w.binding == binding) {
                self.journal.placement_elided_writes.insert(occurrence.inst);
            }
        }
        self.journal
            .placement_elided_observations
            .extend(removals.observations);
        let undeclared = crate::unrendered::names_mentioned_without_a_declaration(&self.function);
        if !undeclared.is_empty() {
            return Err(NativePlacementFailure::UndeclaredNames {
                count: undeclared.len(),
            });
        }
        Ok(())
    }

    #[cfg(test)]
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
            placement_audit: crate::PlacementAudit::NotRun,
            observation_failure: None,
            plan,
        })
    }

    /// Seal the final native tree as a required render proof.
    ///
    /// A missing marker, conflicting observation, or journal failure rejects
    /// the native product. The caller may cross the typed residual boundary,
    /// but it cannot recover the marker-free executable tree from this draft.
    #[expect(
        clippy::result_large_err,
        reason = "the typed refusal retains the complete value/use/write ledger at the final audit boundary"
    )]
    pub(crate) fn finish_enforcing(
        mut self,
        source: &SourceOwnedFunctionFacts,
        recording_failure: Option<LegacyObservationJournalError>,
    ) -> Result<SealedNativeFunction, BindingShadowAuditFailure> {
        let placement_failure = self
            .derive_and_apply_placement(source)
            .err()
            .map(crate::PlacementAuditRefusal::from);
        let mut ready = prepare_function_for_emission(&self.function);
        let plan = Rc::clone(&self.journal.plan);
        if let Some(error) = recording_failure {
            return Err(BindingShadowAuditFailure::JournalRecording(
                BindingObservationJournalFailure::from(&error),
            ));
        }
        // A placement that ran and refused is reported before the seal, because
        // it is the cause of the seal failure it produces rather than an
        // independent finding. When placement cannot declare a binding, the
        // seal then observes a rendered name that owns no declaration and
        // refuses with `UnownedBindingSymbol`, naming the symbol instead of the
        // phase that failed to declare it. Sealing first reported that symptom
        // and discarded the cause.
        //
        // A draft carrying no placement input at all is a different case: no
        // placement ran, so nothing links its absence to what the seal finds,
        // and the seal keeps precedence.
        if self.placement.is_some()
            && let Some(refusal) = placement_failure
        {
            return Err(BindingShadowAuditFailure::Placement(refusal));
        }
        let observations = match self.journal.seal_preserving_effects(source, &mut ready) {
            Ok(LegacyObservationSeal::Complete(observations)) => observations,
            Ok(LegacyObservationSeal::BindingFailure(error)) | Err(error) => {
                return Err(BindingShadowAuditFailure::JournalSeal(
                    BindingObservationJournalFailure::from(&error),
                ));
            }
        };
        if let Some(refusal) = placement_failure {
            return Err(BindingShadowAuditFailure::Placement(refusal));
        }
        if let Some(placement) = self.placement.as_ref() {
            ready
                .strip_structured_region_markers(&placement.regions)
                .map_err(|error| {
                    BindingShadowAuditFailure::Placement(crate::PlacementAuditRefusal::from(
                        NativePlacementFailure::RegionFinalization(error),
                    ))
                })?;
        }
        let coverage = observations.coverage();
        if !coverage.passes_quality() {
            return Err(BindingShadowAuditFailure::NonQualityObservations {
                observations: coverage.into(),
            });
        }
        Ok(SealedNativeFunction {
            ready,
            observations: Some(observations),
            fallback_effects: None,
            effect_audit: crate::EffectObligationAudit::NOT_RUN,
            placement_audit: crate::PlacementAudit::Applied,
            observation_failure: None,
            plan,
        })
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
    placement_audit: crate::PlacementAudit,
    observation_failure: Option<BindingShadowAuditFailure>,
    plan: Rc<BindingPlan>,
}

impl SealedNativeFunction {
    pub(crate) const fn emission(&self) -> &EmissionReadyFunction {
        &self.ready
    }

    #[cfg(test)]
    pub(crate) fn observations(&self) -> &LegacyAnalysisSnapshot {
        self.observations
            .as_ref()
            .map(SealedLegacyObservations::snapshot)
            .expect("strictly sealed native function must retain observations")
    }

    #[expect(
        clippy::result_large_err,
        reason = "audit consumers receive the complete typed failure ledger rather than a lossy summary"
    )]
    pub(crate) fn audit_observations(
        &self,
    ) -> Result<(&LegacyAnalysisSnapshot, LegacyObservationCoverage), BindingShadowAuditFailure>
    {
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

    pub(crate) const fn placement_audit(&self) -> crate::PlacementAudit {
        self.placement_audit
    }

    pub(crate) fn into_function(self) -> CFunction {
        self.ready.into_function()
    }
}

impl LegacyObservationJournal {
    pub(crate) fn checkpoint(&self) -> ObservationJournalCheckpoint {
        ObservationJournalCheckpoint {
            target_len: self.targets.len(),
        }
    }

    /// Discard markers allocated by a candidate tree that will not be emitted.
    ///
    /// The checkpoint comes from this journal immediately before the candidate
    /// route. Dense observation IDs allocated after it are unreachable once
    /// that tree is dropped, so truncating the tail preserves all earlier IDs.
    pub(crate) fn rollback(&mut self, checkpoint: ObservationJournalCheckpoint) {
        assert!(
            checkpoint.target_len <= self.targets.len(),
            "an observation checkpoint cannot point past its issuing journal"
        );
        self.targets.truncate(checkpoint.target_len);
    }

    pub(crate) fn placement_target_count(&self) -> usize {
        self.targets.len()
    }

    pub(crate) fn placement_target(
        &self,
        id: RenderObservationId,
    ) -> Option<crate::placement::PlacementObservationTarget> {
        match self.targets.get(id.index() as usize)? {
            ObservationTarget::CertifiedValueRead {
                value,
                at,
                binding,
                symbol,
            } => Some(
                crate::placement::PlacementObservationTarget::CertifiedValueRead {
                    value: *value,
                    at: *at,
                    binding: *binding,
                    symbol: *symbol,
                },
            ),
            ObservationTarget::Use { site, block, .. } => Some(
                self.source
                    .graph()
                    .inst(site.inst)
                    .and_then(|inst| inst.inputs.get(site.input_idx))
                    .and_then(|value| self.plan.disposition(*value))
                    .and_then(|disposition| {
                        matches!(disposition, ValueDisposition::Bound { .. }).then_some(
                            crate::placement::PlacementObservationTarget::Use {
                                site: *site,
                                block: *block,
                            },
                        )
                    })
                    .unwrap_or(crate::placement::PlacementObservationTarget::Other),
            ),
            ObservationTarget::Write {
                inst,
                observation,
                block,
            } => Some(
                self.source
                    .graph()
                    .inst(*inst)
                    .and_then(|inst| inst.output)
                    .and_then(|value| self.plan.disposition(value))
                    .and_then(|disposition| {
                        matches!(disposition, ValueDisposition::Bound { .. }).then(|| {
                            match observation {
                                LegacyWriteObservation::Exact(projection) => {
                                    crate::placement::PlacementObservationTarget::Write {
                                        inst: *inst,
                                        projection: *projection,
                                        block: *block,
                                    }
                                }
                                _ => crate::placement::PlacementObservationTarget::Other,
                            }
                        })
                    })
                    .unwrap_or(crate::placement::PlacementObservationTarget::Other),
            ),
            ObservationTarget::StackAccess {
                access,
                object,
                binding,
                symbol,
                is_write,
            } => Some(crate::placement::PlacementObservationTarget::StackAccess {
                access: *access,
                object: *object,
                binding: *binding,
                symbol: *symbol,
                is_write: *is_write,
            }),
            ObservationTarget::Value(_) | ObservationTarget::Effect(_) => {
                Some(crate::placement::PlacementObservationTarget::Other)
            }
        }
    }

    pub(crate) fn new(
        source: &SourceOwnedFunctionFacts,
        normalized: &SSAFunction,
        origins: &NormalizationOrigins,
        names: Rc<BindingNameResolution>,
        symbols: Rc<RefCell<SymbolTable>>,
    ) -> Result<Self, LegacyObservationJournalError> {
        let plan = Rc::clone(names.plan());
        plan.validate_source(source.source())
            .map_err(LegacyObservationJournalError::BindingPlan)?;
        if !names.owns_symbol_table(&symbols) {
            return Err(LegacyObservationJournalError::SymbolTableMismatch);
        }
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
        let mut coalesced_carrier_copy_sites = BTreeSet::new();
        for block_id in graph.block_order.iter().copied() {
            let Some(block) = graph
                .block(block_id)
                .and_then(|block| normalized.get_block(block.addr))
            else {
                return Err(LegacyObservationJournalError::Normalization(
                    NormalizationOriginError::BlockTopology,
                ));
            };
            for (op_idx, op) in block.ops.iter().enumerate() {
                let site = NormalizedOpSite {
                    block: block_id,
                    op_idx,
                };
                let Some(NormalizedOpOrigin::PhiEdgeCopy(origin)) = origins.origin(site) else {
                    continue;
                };
                if !matches!(
                    origin.certified_entity,
                    Some(r2ssa::SemanticId::LoopCarrier(_))
                ) || !matches!(op, r2ssa::SSAOp::Copy { src, .. } if src.version != 0)
                {
                    continue;
                }
                let projection = &normalized_projections[block_id.0 as usize][op_idx];
                let Some(output) = projection.output else {
                    continue;
                };
                let Some(input) = projection
                    .inputs
                    .iter()
                    .find(|input| input.uses.contains(&origin.incoming))
                else {
                    continue;
                };
                if matches!(
                    (plan.disposition(input.value), plan.disposition(output.value)),
                    (
                        Some(ValueDisposition::Bound { binding: input }),
                        Some(ValueDisposition::Bound { binding: output }),
                    ) if input == output
                ) {
                    coalesced_carrier_copy_sites.insert(site);
                }
            }
        }
        let coalesced_carrier_uses = coalesced_carrier_copy_sites
            .iter()
            .filter_map(|site| {
                normalized_projections
                    .get(site.block.0 as usize)
                    .and_then(|rows| rows.get(site.op_idx))
            })
            .flat_map(|projection| {
                projection
                    .inputs
                    .iter()
                    .flat_map(|input| input.uses.iter().copied())
            })
            .collect::<BTreeSet<_>>();
        let coalesced_carrier_phi_writes = origins
            .removed_phis()
            .iter()
            .filter(|removed| {
                source
                    .report()
                    .render()
                    .and_then(|render| render.loop_carrier_for_value(removed.definition.value))
                    .is_some()
                    && removed.incoming_sites.iter().all(|site| {
                        removed.noop_sites().contains(site) || coalesced_carrier_uses.contains(site)
                    })
            })
            .map(|removed| removed.definition.inst)
            .collect::<BTreeSet<_>>();
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
        let materialized_removed_phis = origins
            .removed_phis()
            .iter()
            .filter(|removed| {
                let materialized = origins.materialized_phi_edges(removed.definition.inst);
                removed
                    .incoming_sites
                    .iter()
                    .all(|site| removed.noop_sites().contains(site) || materialized.contains(site))
            })
            .map(|removed| removed.definition.inst)
            .collect::<BTreeSet<_>>();
        let mut journal = Self {
            authority: source.source().authority().clone(),
            source: source.shared_source(),
            plan,
            names,
            normalized_projections,
            coalesced_carrier_copy_sites,
            coalesced_carrier_uses,
            coalesced_carrier_phi_writes,
            materialized_removed_phis,
            placement_elided_writes: BTreeSet::new(),
            placement_elided_observations: BTreeSet::new(),
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
        for certificate in source
            .source()
            .certificates()
            .stack_frame_round_trips
            .values()
        {
            for inst in &certificate.insts {
                let Some(definition) = graph.inst(*inst) else {
                    return Err(LegacyObservationJournalError::InvalidWrite(*inst));
                };
                for input_idx in 0..definition.inputs.len() {
                    let site = UseSite {
                        inst: *inst,
                        input_idx,
                    };
                    match elided_uses.insert(site, r2ssa::ledger::ElisionReason::StackFrame) {
                        Some(r2ssa::ledger::ElisionReason::StackFrame) | None => {}
                        Some(_) => {
                            return Err(LegacyObservationJournalError::ConflictingUse(site));
                        }
                    }
                }
                if definition.output.is_some() {
                    match elided_writes.insert(*inst, r2ssa::ledger::ElisionReason::StackFrame) {
                        Some(r2ssa::ledger::ElisionReason::StackFrame) | None => {}
                        Some(_) => {
                            return Err(LegacyObservationJournalError::ConflictingWrite(*inst));
                        }
                    }
                }
            }
        }
        for certificate in source
            .source()
            .certificates()
            .machine_return_controls
            .values()
        {
            for site in &certificate.uses {
                match elided_uses.insert(*site, r2ssa::ledger::ElisionReason::ReturnControl) {
                    Some(r2ssa::ledger::ElisionReason::ReturnControl) | None => {}
                    Some(_) => {
                        return Err(LegacyObservationJournalError::ConflictingUse(*site));
                    }
                }
            }
            for inst in &certificate.insts {
                let Some(definition) = graph.inst(*inst) else {
                    return Err(LegacyObservationJournalError::InvalidWrite(*inst));
                };
                if definition.output.is_some() {
                    match elided_writes.insert(*inst, r2ssa::ledger::ElisionReason::ReturnControl) {
                        Some(r2ssa::ledger::ElisionReason::ReturnControl) | None => {}
                        Some(_) => {
                            return Err(LegacyObservationJournalError::ConflictingWrite(*inst));
                        }
                    }
                }
            }
        }
        for site in &source.source().certificates().stack_geometry.uses {
            // A stack-root value has no standalone C occurrence, but an exact
            // stack-object address operand still has its own contextual
            // per-use projection.  The value and use ledgers are independent:
            // seed only geometry uses that disappear with their defining
            // operation, and let the rendered memory-address marker account
            // for the surviving operand.
            if matches!(
                self.plan.use_disposition(*site),
                Some(MachineUseDisposition::MemoryAddress(_))
            ) {
                continue;
            }
            match elided_uses.insert(*site, r2ssa::ledger::ElisionReason::DeadStackBase) {
                Some(r2ssa::ledger::ElisionReason::DeadStackBase) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(*site)),
            }
        }
        for inst in &source.source().certificates().stack_geometry.insts {
            let Some(definition) = graph.inst(*inst) else {
                return Err(LegacyObservationJournalError::InvalidWrite(*inst));
            };
            if definition.output.is_some() {
                match elided_writes.insert(*inst, r2ssa::ledger::ElisionReason::DeadStackBase) {
                    Some(r2ssa::ledger::ElisionReason::DeadStackBase) | None => {}
                    Some(_) => {
                        return Err(LegacyObservationJournalError::ConflictingWrite(*inst));
                    }
                }
            }
        }
        // The SSA liveness owner publishes the complete pure domain outside
        // the transitive observation slice.  Seed non-phi operations here;
        // dead merges retain their more specific reason below.  Earlier
        // machine/frame certificates win deterministically when domains
        // overlap.
        for site in source.source().unobserved_merges().unobserved_uses() {
            if source
                .source()
                .graph()
                .inst(site.inst)
                .is_some_and(|inst| matches!(inst.payload, r2ssa::InstPayload::Phi { .. }))
            {
                continue;
            }
            elided_uses
                .entry(*site)
                .or_insert(r2ssa::ledger::ElisionReason::UnobservedValue);
        }
        for inst in source.source().unobserved_merges().unobserved_insts() {
            let Some(definition) = graph.inst(*inst) else {
                return Err(LegacyObservationJournalError::InvalidWrite(*inst));
            };
            if matches!(definition.payload, r2ssa::InstPayload::Phi { .. }) {
                continue;
            }
            if definition.output.is_some() {
                elided_writes
                    .entry(*inst)
                    .or_insert(r2ssa::ledger::ElisionReason::UnobservedValue);
            }
        }
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
        for site in crate::binding_plan::certified_return_control_sites(source.source()) {
            match elided_uses.insert(site, r2ssa::ledger::ElisionReason::ReturnControl) {
                Some(r2ssa::ledger::ElisionReason::ReturnControl) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
            }
        }
        for inst in crate::binding_plan::certified_return_control_insts(source.source()) {
            let Some(definition) = graph.inst(inst) else {
                return Err(LegacyObservationJournalError::InvalidWrite(inst));
            };
            if definition.output.is_some() {
                match elided_writes.insert(inst, r2ssa::ledger::ElisionReason::ReturnControl) {
                    Some(r2ssa::ledger::ElisionReason::ReturnControl) | None => {}
                    Some(_) => return Err(LegacyObservationJournalError::ConflictingWrite(inst)),
                }
            }
            // The instruction renders nothing, so it reads nothing. Its write
            // was already accounted on that ground and its operands stand on
            // the same one: an occurrence inside a statement no structured
            // form emits is not a read. On AArch64 the return address arrives
            // through a copy of the link register and the copy's operand is
            // control-only in its own right, so this was never needed; on
            // amd64 `ret` lifts to a load of the return address through the
            // stack pointer, and the stack pointer is read elsewhere for
            // ordinary reasons, so nothing else could ever close that cell.
            for input_idx in 0..definition.inputs.len() {
                let site = UseSite { inst, input_idx };
                match elided_uses.insert(site, r2ssa::ledger::ElisionReason::ReturnControl) {
                    Some(r2ssa::ledger::ElisionReason::ReturnControl) | None => {}
                    Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
                }
            }
        }
        for site in crate::binding_plan::certified_direct_control_target_sites(source.source()) {
            match elided_uses.insert(site, r2ssa::ledger::ElisionReason::DirectControlTarget) {
                Some(r2ssa::ledger::ElisionReason::DirectControlTarget) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
            }
        }
        // A direct call names its callee. The name comes from the symbol
        // table, not from any object the function holds, so the operand's
        // occurrence is not a read and the value it names is elided beside it.
        for site in crate::binding_plan::certified_direct_call_target_sites(source.source()) {
            match elided_uses.insert(site, r2ssa::ledger::ElisionReason::DirectCallTarget) {
                Some(r2ssa::ledger::ElisionReason::DirectCallTarget) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
            }
        }
        for inst in crate::binding_plan::certified_direct_call_target_insts(source.source()) {
            let Some(definition) = graph.inst(inst) else {
                return Err(LegacyObservationJournalError::InvalidWrite(inst));
            };
            if definition.output.is_some() {
                match elided_writes.insert(inst, r2ssa::ledger::ElisionReason::DirectCallTarget) {
                    Some(r2ssa::ledger::ElisionReason::DirectCallTarget) | None => {}
                    Some(_) => return Err(LegacyObservationJournalError::ConflictingWrite(inst)),
                }
            }
            for input_idx in 0..definition.inputs.len() {
                let site = UseSite { inst, input_idx };
                match elided_uses.insert(site, r2ssa::ledger::ElisionReason::DirectCallTarget) {
                    Some(r2ssa::ledger::ElisionReason::DirectCallTarget) | None => {}
                    Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
                }
            }
        }
        for site in origins.noop_sites() {
            match elided_uses.insert(site, r2ssa::ledger::ElisionReason::RedundantPhiEdge) {
                Some(r2ssa::ledger::ElisionReason::RedundantPhiEdge) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
            }
        }
        let coalesced_carrier_uses = self
            .coalesced_carrier_uses
            .iter()
            .copied()
            .collect::<Vec<_>>();
        for site in coalesced_carrier_uses {
            match elided_uses.insert(site, r2ssa::ledger::ElisionReason::CoalescedCarrierEdge) {
                Some(r2ssa::ledger::ElisionReason::CoalescedCarrierEdge) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
            }
        }
        for inst in self.coalesced_carrier_phi_writes.iter().copied() {
            match elided_writes.insert(inst, r2ssa::ledger::ElisionReason::CoalescedCarrierPhi) {
                Some(r2ssa::ledger::ElisionReason::CoalescedCarrierPhi) | None => {}
                Some(_) => return Err(LegacyObservationJournalError::ConflictingWrite(inst)),
            }
        }
        let removed_phis = origins
            .removed_phis()
            .iter()
            .map(|origin| origin.definition.inst)
            .collect::<BTreeSet<_>>();
        for inst in &graph.insts {
            if removed_phis.contains(&inst.id)
                || !matches!(inst.payload, r2ssa::InstPayload::Phi { .. })
            {
                continue;
            }
            let Some(output) = inst.output else {
                return Err(LegacyObservationJournalError::InvalidWrite(inst.id));
            };
            let Some(ValueDisposition::Bound {
                binding: output_binding,
            }) = self.plan.disposition(output)
            else {
                continue;
            };
            if !inst.inputs.iter().all(|input| {
                matches!(
                    self.plan.disposition(*input),
                    Some(ValueDisposition::Bound { binding }) if binding == output_binding
                )
            }) {
                continue;
            }
            for input_idx in 0..inst.inputs.len() {
                let site = UseSite {
                    inst: inst.id,
                    input_idx,
                };
                match elided_uses.insert(site, r2ssa::ledger::ElisionReason::CoalescedImmutablePhi)
                {
                    Some(r2ssa::ledger::ElisionReason::CoalescedImmutablePhi) | None => {}
                    Some(_) => return Err(LegacyObservationJournalError::ConflictingUse(site)),
                }
            }
            match elided_writes.insert(inst.id, r2ssa::ledger::ElisionReason::CoalescedImmutablePhi)
            {
                Some(r2ssa::ledger::ElisionReason::CoalescedImmutablePhi) | None => {}
                Some(_) => {
                    return Err(LegacyObservationJournalError::ConflictingWrite(inst.id));
                }
            }
        }
        let refused_uses = self
            .plan
            .machine_projection()
            .use_dispositions()
            .iter()
            .enumerate()
            .flat_map(|(inst, row)| {
                row.iter()
                    .enumerate()
                    .filter_map(move |(input_idx, disposition)| {
                        matches!(disposition, MachineUseDisposition::Refused(_)).then_some(
                            UseSite {
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

        // A value the obligation ledger certifies as structurally unused is
        // defined by an instruction nothing can render: the ledger has already
        // established that it is structural, owns no semantic obligation, and
        // that the program never reads what it produces. An unused call
        // clobber is the case -- `murmur3_32` at -O0 leaves nine of them at its
        // one call -- and the write cell those definitions carry has no other
        // answerer, because there is no statement to answer with. This is
        // deliberately not done for every elided value: most elisions mean some
        // other rendering answers for the value, and claiming its definition
        // renders nothing would take the cell away from whatever does.
        for value in &nonrendered_values {
            if !matches!(
                self.plan.disposition(*value),
                Some(ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::UnusedStructuralValue,
                    ..
                })
            ) {
                continue;
            }
            let Some(inst) = graph.def_inst(*value) else {
                continue;
            };
            if graph.inst(inst).and_then(|inst| inst.output) != Some(*value) {
                continue;
            }
            elided_writes
                .entry(inst)
                .or_insert(r2ssa::ledger::ElisionReason::UnusedStructuralValue);
        }
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
        let target = self.targets.get(index).cloned().ok_or({
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
        let projection = self.normalized_projection(site)?;
        let block = projection.block;
        let output = projection
            .output
            .ok_or(LegacyObservationJournalError::MissingNormalizedOutput(site))?;
        self.value_slot(output.value)?;
        let write = self.rendered_write_observation(output.inst)?;
        self.allocate_pair(
            ObservationTarget::Value(output.value),
            ObservationTarget::Write {
                inst: output.inst,
                observation: write,
                block,
            },
        )
    }

    /// Mark one value occurrence and every original use represented by the
    /// exact normalized operand that produced it.
    ///
    /// Callers cannot supply a `ValueId`, `UseSite`, or machine disposition:
    /// all three come from the authority-checked normalization projection and
    /// binding plan retained by this journal.
    #[cfg(test)]
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

    /// Mark one exact semantic value read that has no graph [`UseSite`].
    ///
    /// Return values are certified at the return instruction by the source
    /// boundary contract, while the lifted `Return` operand itself is the
    /// control target. This marker carries that exact `(ValueId, InstId)` into
    /// final declaration placement without inventing an operand index.
    pub(crate) fn observe_certified_value_read_expr(
        &mut self,
        value: ValueId,
        at: InstId,
        symbol: SymbolId,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        self.value_slot(value)?;
        // The same boundary record the final placement audit will consult.
        // Two tables answering for one read is how a marker survives here and
        // is refused there, so they ask one question.
        if !crate::placement::certified_boundary_read(&self.source, value, at) {
            return Err(LegacyObservationJournalError::InvalidCertifiedValueRead { value, at });
        }
        let Some(ValueDisposition::Bound { binding }) = self.plan.disposition(value) else {
            return Err(LegacyObservationJournalError::RenderedValueRequired(value));
        };
        if !crate::placement::expr_reads_symbol(&expr, symbol) {
            return Err(LegacyObservationJournalError::RenderedValueRequired(value));
        }
        let mut ids = self
            .allocate_many(vec![
                ObservationTarget::Value(value),
                ObservationTarget::CertifiedValueRead {
                    value,
                    at,
                    binding: *binding,
                    symbol,
                },
            ])?
            .into_iter();
        let value_id = ids
            .next()
            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        let read_id = ids
            .next()
            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        Ok(CExpr::observed(read_id, CExpr::observed(value_id, expr)))
    }

    /// Mark one exact rendered access to a source-owned stack-object binding.
    ///
    /// The structured access owns the object, the binding plan owns the
    /// object-to-binding projection, and name resolution owns the symbol. A
    /// non-stack memory access returns unchanged; no address spelling or stack
    /// offset is consulted here.
    pub(crate) fn observe_stack_access_expr(
        &mut self,
        access: r2ssa::StructuredAccessId,
        is_write: bool,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let fact = self
            .source
            .structured()
            .memory_accesses
            .get(&access)
            .filter(|fact| {
                fact.id == access && fact.is_write == is_write && fact.provenance_complete
            })
            .ok_or(LegacyObservationJournalError::InvalidUse(UseSite {
                inst: access.inst,
                input_idx: 0,
            }))?;
        let Some(disposition) = self.plan.stack_object_disposition(fact.object) else {
            return Ok(expr);
        };
        let StackObjectDisposition::Bound { binding } = disposition else {
            return Err(LegacyObservationJournalError::InvalidUse(UseSite {
                inst: access.inst,
                input_idx: 0,
            }));
        };
        let symbol = self.names.symbol_for_binding(binding).ok_or(
            LegacyObservationJournalError::InvalidUse(UseSite {
                inst: access.inst,
                input_idx: 0,
            }),
        )?;
        if !crate::placement::expr_reads_symbol(&expr, symbol) {
            return Err(LegacyObservationJournalError::InvalidUse(UseSite {
                inst: access.inst,
                input_idx: 0,
            }));
        }
        let id = self
            .allocate_many(vec![ObservationTarget::StackAccess {
                access,
                object: fact.object,
                binding,
                symbol,
                is_write,
            }])?
            .into_iter()
            .next()
            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        Ok(CExpr::observed(id, expr))
    }

    /// Account the merge a normalization removed by materializing its edges.
    ///
    /// The copies on those edges are what write the merge, so the phi itself
    /// has no occurrence of its own. This fills only slots the renderer left
    /// empty: where the phi does still render, that observation already stands
    /// and is not replaced, which is why this cannot be declared up front.
    fn account_materialized_phi_occurrences(&mut self) {
        let graph = self.source.graph();
        for inst in self.materialized_removed_phis.clone() {
            let reason = r2ssa::ledger::ElisionReason::MaterializedPhiEdges;
            if let Some(slot) = self.writes.get_mut(inst.0 as usize)
                && slot.is_none()
            {
                *slot = Some(LegacyWriteObservation::Elided(reason));
            }
            let inputs = graph.inst(inst).map_or(0, |inst| inst.inputs.len());
            for input_idx in 0..inputs {
                if let Some(row) = self.uses.get_mut(inst.0 as usize)
                    && let Some(slot) = row.get_mut(input_idx)
                    && slot.is_none()
                {
                    *slot = Some(LegacyUseObservation::Elided(reason));
                }
            }
        }

        // Definitions placement dropped because nothing reads what they
        // produce. What they did besides producing that value is answered by
        // the effect ledger, which is why removing the statement does not lose
        // an obligation; here only the value, use and write cells they carried
        // are closed out.
        let reason = r2ssa::ledger::ElisionReason::DeadUnusedTemporary;
        for inst in self.placement_elided_writes.clone() {
            if let Some(slot) = self.writes.get_mut(inst.0 as usize)
                && slot.is_none()
            {
                *slot = Some(LegacyWriteObservation::Elided(reason));
            }
            let Some(instruction) = graph.inst(inst) else {
                continue;
            };
            if let Some(output) = instruction.output
                && let Some(slot) = self.values.get_mut(output.0 as usize)
                && slot.is_none()
            {
                *slot = Some(LegacyValueObservation::Elided(reason));
            }
            for input_idx in 0..instruction.inputs.len() {
                if let Some(row) = self.uses.get_mut(inst.0 as usize)
                    && let Some(slot) = row.get_mut(input_idx)
                    && slot.is_none()
                {
                    *slot = Some(LegacyUseObservation::Elided(reason));
                }
            }
        }

        // Every cell the discarded statements carried. Walking the writes
        // reaches only what a defining instruction produced, and a
        // caller-supplied value is version zero with no defining instruction at
        // all -- the stack pointer is exactly that -- so its cell is reachable
        // only through the observation that named it.
        //
        // These are the observations placement reported removing, not the cells
        // that happen to be empty. Filling in whatever is empty would satisfy
        // the seal by silencing it, and the seal is the only thing that catches
        // a value the renderer was supposed to emit and did not.
        let reason = r2ssa::ledger::ElisionReason::DeadUnreadBinding;
        for id in self.placement_elided_observations.clone() {
            let Some(target) = self.targets.get(id.index() as usize).copied() else {
                continue;
            };
            match target {
                ObservationTarget::Value(value) => {
                    if let Some(slot) = self.values.get_mut(value.0 as usize)
                        && slot.is_none()
                    {
                        *slot = Some(LegacyValueObservation::Elided(reason));
                    }
                }
                ObservationTarget::Use { site, .. } => {
                    if let Some(row) = self.uses.get_mut(site.inst.0 as usize)
                        && let Some(slot) = row.get_mut(site.input_idx)
                        && slot.is_none()
                    {
                        *slot = Some(LegacyUseObservation::Elided(reason));
                    }
                }
                ObservationTarget::Write { inst, .. } => {
                    if let Some(slot) = self.writes.get_mut(inst.0 as usize)
                        && slot.is_none()
                    {
                        *slot = Some(LegacyWriteObservation::Elided(reason));
                    }
                }
                // A stack access answers through the object it addresses, and a
                // certified read through the value it reads; an effect answers
                // to the effect ledger. None of the three owns a cell here.
                ObservationTarget::StackAccess { .. }
                | ObservationTarget::CertifiedValueRead { .. }
                | ObservationTarget::Effect(_) => {}
            }
        }
    }

    fn first_unaccounted_render_observation(&self) -> Option<LegacyObservationJournalError> {
        // Each of the three loops below names the exact cell it found empty
        // under `R2DEC_TRACE_REFUSAL`, the same switch the lowering refusals
        // use. A seal failure otherwise reports only that some value, use or
        // write went unaccounted, and finding which one back from that cost
        // four separate investigations.
        for (index, observation) in self.values.iter().enumerate() {
            if observation.is_none() {
                let value = ValueId(index as u32);
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    let graph = self.source.graph();
                    eprintln!(
                        "unaccounted value {value:?} disposition {:?} def {:?} uses={uses} storage={storage:?}",
                        self.plan.disposition(value),
                        graph
                            .def_inst(value)
                            .and_then(|inst| graph.inst(inst))
                            .map(|inst| format!("{:?}", inst.payload)
                                .chars()
                                .take(130)
                                .collect::<String>()),
                        uses = graph.use_sites(value).len(),
                        storage = graph
                            .value(value)
                            .and_then(|v| v.canonical_storage)
                            .map(|s| (s.space, s.offset, s.size))
                    );
                    for site in graph.use_sites(value) {
                        eprintln!(
                            "   use {site:?} -> {:?}",
                            graph
                                .inst(site.inst)
                                .map(|inst| format!("{:?}", inst.payload)
                                    .chars()
                                    .take(110)
                                    .collect::<String>())
                        );
                    }
                }
                return Some(LegacyObservationJournalError::RenderedValueRequired(value));
            }
        }
        for (inst, row) in self.uses.iter().enumerate() {
            for (input_idx, observation) in row.iter().enumerate() {
                if observation.is_none() {
                    if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                        let graph = self.source.graph();
                        eprintln!(
                            "unaccounted use inst={inst} input={input_idx} payload={:?}",
                            graph.inst(InstId(inst as u32)).map(|inst| format!(
                                "{:?}",
                                inst.payload
                            )
                            .chars()
                            .take(120)
                            .collect::<String>())
                        );
                    }
                    return Some(
                        LegacyObservationJournalError::ExactUseRequiresRenderedOccurrence(
                            UseSite {
                                inst: InstId(inst as u32),
                                input_idx,
                            },
                        ),
                    );
                }
            }
        }
        for (index, (observation, has_output)) in self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .enumerate()
        {
            if *has_output && observation.is_none() {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    let graph = self.source.graph();
                    eprintln!(
                        "unaccounted write inst={index} payload={:?}",
                        graph
                            .inst(InstId(index as u32))
                            .map(|inst| format!("{:?}", inst.payload)
                                .chars()
                                .take(120)
                                .collect::<String>())
                    );
                }
                return Some(
                    LegacyObservationJournalError::ExactWriteRequiresRenderedOccurrence(InstId(
                        index as u32,
                    )),
                );
            }
        }
        None
    }

    /// Mark every exact original use outside the already-projected expression.
    pub(crate) fn observe_normalized_input_uses_expr(
        &mut self,
        site: NormalizedOpSite,
        input_idx: usize,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let projection = self.normalized_projection(site)?;
        let block = projection.block;
        let input = projection
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
                block,
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
    #[cfg(test)]
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
        if matches!(stmt.unobserved(), CStmt::Comment(_) | CStmt::Empty) {
            return Ok(stmt);
        }
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
            Some(MachineUseDisposition::Exact(_) | MachineUseDisposition::MemoryAddress(_))
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

    pub(crate) fn is_coalesced_carrier_copy(&self, site: NormalizedOpSite) -> bool {
        self.coalesced_carrier_copy_sites.contains(&site)
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
    #[cfg(test)]
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
                let target = targets.get(id.index() as usize).copied().ok_or({
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
            coalesced_carriers: Box::new(CoalescedCarrierEffectElisions {
                coalesced_carrier_uses: self.coalesced_carrier_uses,
                coalesced_carrier_phis: self.coalesced_carrier_phi_writes,
            }),
        })
    }

    #[cfg(test)]
    pub(crate) fn seal(
        self,
        source: &SourceOwnedFunctionFacts,
        ready: &mut EmissionReadyFunction,
    ) -> Result<SealedLegacyObservations, LegacyObservationJournalError> {
        match self.seal_preserving_effects(source, ready)? {
            LegacyObservationSeal::Complete(observations) => Ok(observations),
            LegacyObservationSeal::BindingFailure(error) => Err(error),
        }
    }

    /// Inspect the final marker tree once while retaining the first legacy
    /// binding-classification failure. Effect occurrences are sealed only with
    /// a fully classified product; a binding failure leaves the tree unchanged
    /// and exposes neither executable C nor a partial effect stream.
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
                let target = targets.get(id.index() as usize).copied().ok_or({
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
                    ObservationTarget::CertifiedValueRead { .. } => Ok(()),
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
                            Some(
                                ValueDisposition::Bound { .. } | ValueDisposition::Inline { .. },
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
                    ObservationTarget::Use {
                        site, observation, ..
                    } => record_same(&mut uses[site.inst.0 as usize][site.input_idx], observation)
                        .map_err(|()| LegacyObservationJournalError::ConflictingUse(site)),
                    ObservationTarget::Write {
                        inst, observation, ..
                    } => record_same(&mut writes[inst.0 as usize], observation)
                        .map_err(|()| LegacyObservationJournalError::ConflictingWrite(inst)),
                    ObservationTarget::StackAccess { .. } => Ok(()),
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
            return Ok(LegacyObservationSeal::BindingFailure(error));
        }

        let mut seal_authority = ObservationSealAuthority::new();
        ready.discard_observation_markers(&mut seal_authority);
        self.values = values;
        self.uses = uses;
        self.writes = writes;
        self.effect_occurrences = effect_occurrences;
        self.account_materialized_phi_occurrences();
        if let Some(error) = self.first_unaccounted_render_observation() {
            return Ok(LegacyObservationSeal::BindingFailure(error));
        }
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
                    Some(LegacyUseObservation::Exact(_) | LegacyUseObservation::MemoryAddress(_))
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
            coalesced_carriers: Box::new(CoalescedCarrierEffectElisions {
                coalesced_carrier_uses: std::mem::take(&mut self.coalesced_carrier_uses),
                coalesced_carrier_phis: std::mem::take(&mut self.coalesced_carrier_phi_writes),
            }),
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
        .ok_or(LegacyObservationJournalError::UnownedBindingSymbol { value, symbol })?;
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
    use crate::binding_plan::{BindingId, BindingNameResolution, ValueDisposition, ValueRefusal};
    use crate::structured_region::{
        StructuredRegionKind, StructuredRegionMarker, seal_structured_body,
    };
    use crate::symbol::{ExternalKind, SymbolRole};

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
        journal_fixture_for_source(source_owned())
    }

    fn test_binding_names(
        source: &SourceOwnedFunctionFacts,
        plan: Rc<BindingPlan>,
        symbols: Rc<RefCell<SymbolTable>>,
    ) -> Rc<BindingNameResolution> {
        Rc::new(
            BindingNameResolution::build(source, plan, symbols)
                .expect("authority-bound test binding names"),
        )
    }

    fn journal_fixture_for_source(
        source: SourceOwnedFunctionFacts,
    ) -> (
        SourceOwnedFunctionFacts,
        BindingPlan,
        CFunction,
        LegacyObservationJournal,
    ) {
        let plan = BindingPlan::build_shadow(&source).expect("sealed binding plan");
        let function = CFunction::new("journal", CType::Void);
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let names =
            test_binding_names(&source, Rc::new(plan.clone()), Rc::clone(&function.symbols));
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            names,
            Rc::clone(&function.symbols),
        )
        .expect("authority-bound journal");
        (source, plan, function, journal)
    }

    #[test]
    fn mixed_use_return_control_elides_only_the_exact_return_use() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x80, 8),
            src: Varnode::register(0x30, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let source = source_owned_from_blocks(&[block]);
        let graph = source.source().graph();
        let control_sites = crate::binding_plan::certified_return_control_sites(source.source());
        let control_site = *control_sites.iter().next().expect("certified return use");
        assert_eq!(control_sites.len(), 1);
        let return_control = graph
            .inst(control_site.inst)
            .and_then(|inst| inst.inputs.get(control_site.input_idx))
            .copied()
            .expect("return control value");
        assert_eq!(graph.use_sites(return_control).len(), 2);
        assert!(
            !crate::binding_plan::certified_return_control_values(source.source())
                .contains(&return_control)
        );

        let plan = BindingPlan::build_shadow(&source).expect("mixed-use binding plan");
        assert!(matches!(
            plan.disposition(return_control),
            Some(ValueDisposition::Bound { .. })
        ));
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let function = CFunction::new("mixed_return_control", CType::Void);
        let names = test_binding_names(&source, Rc::new(plan), Rc::clone(&function.symbols));
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            names,
            Rc::clone(&function.symbols),
        )
        .expect("mixed-use journal");

        assert_eq!(
            journal.uses[control_site.inst.0 as usize][control_site.input_idx],
            Some(LegacyUseObservation::Elided(
                r2ssa::ledger::ElisionReason::ReturnControl
            ))
        );
        let ordinary_site = graph
            .use_sites(return_control)
            .iter()
            .copied()
            .find(|site| *site != control_site)
            .expect("ordinary non-control use");
        assert_ne!(
            journal.uses[ordinary_site.inst.0 as usize][ordinary_site.input_idx],
            Some(LegacyUseObservation::Elided(
                r2ssa::ledger::ElisionReason::ReturnControl
            ))
        );
    }

    #[test]
    fn certified_value_read_rejects_forged_expression_at_allocation_and_seal() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let source = source_owned_from_blocks(&[block]);
        let certificate = source
            .source()
            .certificates()
            .returns
            .first()
            .cloned()
            .expect("exact source return-value certificate");
        let plan = Rc::new(BindingPlan::build_shadow(&source).expect("return binding plan"));
        let mut function = CFunction::new("certified_read", CType::Int(64));
        let names = Rc::new(
            BindingNameResolution::build(&source, Rc::clone(&plan), Rc::clone(&function.symbols))
                .expect("sealed return names"),
        );
        let symbol = names
            .symbol_for_value(certificate.value)
            .expect("certified return has one planned symbol");
        let binding = match plan.disposition(certificate.value) {
            Some(ValueDisposition::Bound { binding }) => *binding,
            other => panic!("certified return must be bound, got {other:?}"),
        };
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let mut journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            Rc::clone(&names),
            Rc::clone(&function.symbols),
        )
        .expect("return observation journal");

        for forged in [
            CExpr::IntLit(7),
            CExpr::External {
                name: "forged_return".to_string(),
                kind: ExternalKind::Global,
            },
        ] {
            assert_eq!(
                journal.observe_certified_value_read_expr(
                    certificate.value,
                    certificate.at,
                    symbol,
                    forged,
                ),
                Err(LegacyObservationJournalError::RenderedValueRequired(
                    certificate.value
                ))
            );
        }

        let marked = journal
            .observe_certified_value_read_expr(
                certificate.value,
                certificate.at,
                symbol,
                CExpr::Var(symbol),
            )
            .expect("valid exact certified read marker");
        let CExpr::Observed { id, .. } = marked else {
            panic!("journal returns an observed expression")
        };
        let forged_after_allocation = CExpr::observed(id, CExpr::IntLit(7));
        let sealed = seal_structured_body(
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::Block),
                    CStmt::Return(Some(forged_after_allocation)),
                ),
            ),
            source.source().authority(),
        )
        .expect("sealed marked return");
        let (statement, regions) = sealed.into_marked_parts();
        function.body = vec![statement];

        assert_eq!(
            crate::placement::collect_final_placement_occurrences(
                &function,
                &regions,
                source.source(),
                &names,
                journal.placement_target_count(),
                |id| journal.placement_target(id),
            ),
            Err(crate::placement::PlacementAnalysisError::UnobservedBindingRead { binding })
        );
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
            .expect("empty statement cannot claim an effect occurrence");
        function.body.push(surviving);
        drop(deleted);

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let effects = journal
            .seal_effects_only(&source, &mut ready)
            .expect("final effect occurrences seal independently of V/U/W");
        assert_eq!(effects.occurrence_count(obligation), Some(1));
        assert_eq!(effects.surviving().collect::<Vec<_>>(), [(obligation, 1)]);
    }

    #[test]
    fn residual_memory_effect_is_a_typed_refusal_not_a_rendered_occurrence() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(0x28, 8),
            val: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });
        let source = source_owned_from_blocks(&[block]);
        let (source, _plan, mut function, mut journal) = journal_fixture_for_source(source);
        let obligation = source
            .source()
            .obligations()
            .obligations()
            .keys()
            .copied()
            .find(|id| id.kind == r2ssa::SemanticObligationKind::ObservableMemoryWrite)
            .expect("fixture has an observable memory-write obligation");
        let obligations = BTreeSet::from([obligation]);
        let residual = journal
            .observe_effect_stmt(
                &obligations,
                CStmt::Comment("unsupported exact memory store".to_string()),
            )
            .expect("residual is accepted without claiming the effect");
        let empty = journal
            .observe_effect_stmt(&obligations, CStmt::Empty)
            .expect("empty statement is accepted without claiming the effect");
        assert!(matches!(residual, CStmt::Comment(_)));
        assert_eq!(empty, CStmt::Empty);
        function.body = vec![residual, empty];

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let effects = journal
            .seal_effects_only(&source, &mut ready)
            .expect("effect observations seal independently of V/U/W");
        assert_eq!(effects.occurrence_count(obligation), Some(0));

        let origins =
            NormalizationOrigins::for_unchanged(source.source().function(), source.source());
        let ledger =
            crate::effect_ledger::build_obligation_ledger(source.source(), &origins, &effects);
        assert_eq!(
            ledger.outcome(&obligation),
            r2ssa::ledger::Outcome::Refused {
                layer: r2ssa::ledger::LedgerLayer::Codegen,
                reason: r2ssa::ledger::RefusalReason::BlockNotRendered,
            }
        );
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
        let effects = journal
            .seal_effects_only(&source, &mut ready)
            .expect("final effect occurrences seal independently of V/U/W");
        assert_eq!(effects.occurrence_count(obligation), Some(2));

        let origins =
            NormalizationOrigins::for_unchanged(source.source().function(), source.source());
        let ledger =
            crate::effect_ledger::build_obligation_ledger(source.source(), &origins, &effects);
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
        join.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(0, 8),
        });
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
        let support_values = source
            .source()
            .graph()
            .inst(definition)
            .expect("dead merge instruction")
            .inputs
            .clone();
        let plan = Rc::new(BindingPlan::build_shadow(&source).expect("dead-merge-aware plan"));
        let function = CFunction::new("dead_phi", CType::Void);
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let names = test_binding_names(&source, plan, Rc::clone(&function.symbols));
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            names,
            Rc::clone(&function.symbols),
        )
        .expect("journal seeds exact dead-phi cells");
        assert_eq!(
            journal.values[dead.0 as usize],
            Some(LegacyValueObservation::Elided(
                r2ssa::ledger::ElisionReason::UnobservedMerge
            ))
        );
        for support in support_values {
            assert_eq!(
                journal.values[support.0 as usize],
                Some(LegacyValueObservation::Elided(
                    r2ssa::ledger::ElisionReason::UnobservedValue
                )),
                "a pure value used only by the dead merge is certified non-rendered"
            );
        }
        for input_idx in 0..input_count {
            assert_eq!(
                journal.uses[definition.0 as usize][input_idx],
                Some(LegacyUseObservation::Elided(
                    r2ssa::ledger::ElisionReason::UnobservedMerge
                ))
            );
        }
        assert_eq!(
            journal.writes[definition.0 as usize],
            Some(LegacyWriteObservation::Elided(
                r2ssa::ledger::ElisionReason::UnobservedMerge
            ))
        );
        let coverage = journal.final_coverage();
        assert!(coverage.equations_hold());
        assert!(coverage.values.justified_elision >= 1);
        assert!(coverage.uses.justified_elision >= input_count);
        assert!(coverage.writes.justified_elision >= 1);
    }

    #[test]
    fn immutable_phi_coalesced_by_one_binding_accounts_for_edges_and_definition() {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1008, 8),
        });
        let mut left = R2ILBlock::new(0x1004, 4);
        left.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(11, 8),
        });
        left.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut right = R2ILBlock::new(0x1008, 4);
        right.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
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
        let graph = source.source().graph();
        let definition = graph
            .insts
            .iter()
            .find(|inst| {
                matches!(inst.payload, r2ssa::InstPayload::Phi { .. })
                    && inst.output.is_some_and(|output| {
                        !source.source().unobserved_merges().contains(output)
                            && graph.value(output).is_some_and(|value| {
                                value.canonical_storage.is_some_and(|storage| {
                                    storage.space == CanonicalStorageSpace::Register
                                        && storage.offset == 0
                                })
                            })
                    })
            })
            .expect("live immutable return merge");
        let output = definition.output.expect("phi output");
        let plan = Rc::new(BindingPlan::build_shadow(&source).expect("coalesced phi plan"));
        let output_binding = match plan.disposition(output) {
            Some(ValueDisposition::Bound { binding }) => *binding,
            other => panic!("live merge output must be bound: {other:?}"),
        };
        assert!(definition.inputs.iter().all(|input| matches!(
            plan.disposition(*input),
            Some(ValueDisposition::Bound { binding }) if *binding == output_binding
        )));

        let function = CFunction::new("coalesced_phi", CType::Int(64));
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let names = test_binding_names(&source, plan, Rc::clone(&function.symbols));
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            names,
            Rc::clone(&function.symbols),
        )
        .expect("journal certifies immutable coalesced phi");

        assert_eq!(journal.values[output.0 as usize], None);
        for input_idx in 0..definition.inputs.len() {
            assert_eq!(
                journal.uses[definition.id.0 as usize][input_idx],
                Some(LegacyUseObservation::Elided(
                    r2ssa::ledger::ElisionReason::CoalescedImmutablePhi
                ))
            );
        }
        assert_eq!(
            journal.writes[definition.id.0 as usize],
            Some(LegacyWriteObservation::Elided(
                r2ssa::ledger::ElisionReason::CoalescedImmutablePhi
            ))
        );
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
        let names = test_binding_names(&source, plan, Rc::clone(&function.symbols));
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            names,
            Rc::clone(&function.symbols),
        )
        .expect("normalization-backed journal");
        assert_eq!(
            journal.uses[noop_sites[0].inst.0 as usize][noop_sites[0].input_idx],
            Some(LegacyUseObservation::Elided(
                r2ssa::ledger::ElisionReason::RedundantPhiEdge
            ))
        );
        assert!(
            !journal.coalesced_carrier_copy_sites.is_empty(),
            "the non-entry carrier update must derive one coalesced edge disposition"
        );
        for site in journal.coalesced_carrier_copy_sites.iter().copied() {
            for source_use in journal
                .normalized_projection(site)
                .expect("sealed carrier projection")
                .inputs
                .iter()
                .flat_map(|input| input.uses.iter().copied())
            {
                assert_eq!(
                    journal.uses[source_use.inst.0 as usize][source_use.input_idx],
                    Some(LegacyUseObservation::Elided(
                        r2ssa::ledger::ElisionReason::CoalescedCarrierEdge
                    ))
                );
            }
        }
        assert!(
            !journal.coalesced_carrier_phi_writes.is_empty(),
            "all certified carrier edges in the fixture are identities after coalescing"
        );
        for inst in journal.coalesced_carrier_phi_writes.iter().copied() {
            assert_eq!(
                journal.writes[inst.0 as usize],
                Some(LegacyWriteObservation::Elided(
                    r2ssa::ledger::ElisionReason::CoalescedCarrierPhi
                ))
            );
        }
        let coverage = journal.final_coverage();
        assert!(coverage.equations_hold());
        assert!(coverage.uses.justified_elision >= 1);
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
        let symbol =
            function
                .symbols
                .borrow_mut()
                .declare("unowned", CType::Int(32), SymbolRole::Carrier);
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
                LegacyObservationJournalError::BindingPlan(BindingPlanSourceMismatch::Authority),
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
                LegacyObservationJournalError::InvalidCertifiedValueRead {
                    value: ValueId(14),
                    at: InstId(15),
                },
                BindingObservationJournalFailure::InvalidCertifiedValueRead {
                    value: ValueId(14),
                    at: InstId(15),
                },
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
                BindingObservationJournalFailure::PlannedElidedValueRendered { value: ValueId(32) },
            ),
            (
                LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value: ValueId(33),
                    reason: ValueRefusal::MissingBindingCertificate { value: ValueId(33) },
                },
                BindingObservationJournalFailure::PlannedRefusedValueRendered {
                    value: ValueId(33),
                },
            ),
            (
                LegacyObservationJournalError::MissingPlannedValue(ValueId(34)),
                BindingObservationJournalFailure::MissingPlannedValue { value: ValueId(34) },
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
                BindingObservationJournalFailure::ObservationDomainTooLarge { expected_count: 47 },
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
                LegacyObservationJournalError::Markers(RenderObservationStripError::OutOfRange {
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
                BindingObservationJournalFailure::DuplicateObservation { observation_id: 11 },
            ),
        ];

        for (private, public) in cases {
            assert_eq!(BindingObservationJournalFailure::from(&private), public);
            assert!(!public.kind().is_empty());
        }
    }

    #[test]
    fn rendered_value_cannot_be_recorded_as_nonrendered() {
        let (source, plan, _function, mut journal) = journal_fixture();
        let (value, _) = first_bound(&plan, &source);
        assert_eq!(
            journal.record_nonrendered_value(value),
            Err(LegacyObservationJournalError::RenderedValueRequired(value))
        );
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
    fn production_binding_classification_failure_refuses_the_native_product() {
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

        let result = MarkedNativeDraft::new(function, journal).finish_enforcing(&source, None);
        assert!(matches!(
            result,
            Err(BindingShadowAuditFailure::JournalSeal(
                BindingObservationJournalFailure::ConflictingValue { value: actual },
            )) if actual == value
        ));
    }

    #[test]
    fn invalid_or_duplicate_markers_leave_ast_unchanged() {
        let (source, plan, mut duplicate_function, mut duplicate_journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
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
    fn production_audit_failure_refuses_the_native_product() {
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

        let result = MarkedNativeDraft::new(function, journal).finish_enforcing(&source, None);
        assert!(matches!(
            result,
            Err(BindingShadowAuditFailure::JournalSeal(
                BindingObservationJournalFailure::DuplicateObservation {
                    observation_id: actual,
                },
            )) if actual == duplicate_id
        ));
    }

    #[test]
    fn production_recording_failure_refuses_with_its_exact_cause() {
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

        let result = MarkedNativeDraft::new(function, journal).finish_enforcing(
            &source,
            Some(LegacyObservationJournalError::MissingNormalizedSiteContext),
        );
        assert!(matches!(
            result,
            Err(BindingShadowAuditFailure::JournalRecording(
                BindingObservationJournalFailure::MissingNormalizedSiteContext,
            ))
        ));
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
    fn bound_marker_rejects_a_symbol_without_a_surviving_declaration() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
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
            Err(LegacyObservationJournalError::UnownedBindingSymbol { value, symbol })
        );
        assert_eq!(ready.function_for_marker_test(), &unchanged);
    }
}
