//! Non-consuming Stage 4 comparison of legacy lowering observations with a
//! sealed [`BindingPlan`].
//!
//! The report owns no machine projection facts.  Use and write evidence is a
//! dense key back into the projection retained by the plan.  Likewise, value
//! evidence names the sealed value disposition instead of repeating a binding
//! certificate.  This keeps the report diagnostic: it cannot become a second
//! renderer input by accident.

use r2ssa::{
    InstId, MachineUseDisposition, MachineUseRefusal, MachineUseSlice, MachineValueUse,
    MachineWriteDisposition, MachineWriteProjection, MachineWriteRefusal, SsaArtifactAuthority,
    UseSite, ValueId,
};
use r2types::SourceOwnedFunctionFacts;

use crate::binding_plan::{
    BindingPlan, BindingPlanBuildError, BindingPlanSourceMismatch, CanonicalComponentId,
    UpstreamShadowOracle, UpstreamValueDisposition, ValueDisposition, ValueRefusal,
    build_upstream_shadow_oracle,
};

/// Legacy identity for one purported C object.
///
/// The numeric value is intentionally absent from the final report.  A legacy
/// class is compared by its complete `ValueId` member set, so renumbering old
/// renderer locals cannot affect classification or ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct LegacyBindingId(pub(crate) u32);

/// What the legacy value analysis claimed for one dense `ValueId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LegacyValueObservation {
    Bound {
        binding: LegacyBindingId,
    },
    InlineConstant,
    /// A surviving expression that is not a source-backed literal proof.
    InlineNonLiteral,
    Elided(r2ssa::ledger::ElisionReason),
    Refused(ValueRefusal),
    LegacyAbsent,
}

/// What the legacy renderer claimed for one graph input.
///
/// `LegacyAbsent` is an observation of no answer.  It is never interpreted as
/// refusal; only an exact upstream refusal can justify a refused use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LegacyUseObservation {
    Exact(MachineUseSlice),
    MemoryAddress(MachineValueUse),
    Elided(r2ssa::ledger::ElisionReason),
    Refused(MachineUseRefusal),
    LegacyAbsent,
}

/// What the legacy renderer claimed for one output-producing instruction.
///
/// `LegacyAbsent` is deliberately distinct from every typed refusal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LegacyWriteObservation {
    Exact(MachineWriteProjection),
    Elided(r2ssa::ledger::ElisionReason),
    Refused(MachineWriteRefusal),
    LegacyAbsent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyValueCell {
    pub(crate) value: ValueId,
    pub(crate) observation: LegacyValueObservation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyUseCell {
    pub(crate) site: UseSite,
    pub(crate) observation: LegacyUseObservation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyWriteCell {
    pub(crate) inst: InstId,
    pub(crate) observation: LegacyWriteObservation,
}

/// Dense, read-only snapshot of the old analysis at the shadow boundary.
///
/// Values are indexed by `ValueId`, use rows by `InstId` and input index, and
/// writes by `InstId` (`None` iff the graph instruction is outputless).  The
/// constructor does not repair topology; [`ShadowReport::build`] checks every
/// key against the exact source graph before classifying anything.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LegacyAnalysisSnapshot {
    authority: SsaArtifactAuthority,
    values: Box<[LegacyValueCell]>,
    uses: Box<[Box<[LegacyUseCell]>]>,
    writes: Box<[Option<LegacyWriteCell>]>,
}

impl LegacyAnalysisSnapshot {
    pub(crate) fn new(
        source: &SourceOwnedFunctionFacts,
        values: impl Into<Box<[LegacyValueCell]>>,
        uses: impl Into<Box<[Box<[LegacyUseCell]>]>>,
        writes: impl Into<Box<[Option<LegacyWriteCell>]>>,
    ) -> Self {
        Self {
            authority: source.source().authority().clone(),
            values: values.into(),
            uses: uses.into(),
            writes: writes.into(),
        }
    }

    /// Construct the honest Stage 4 baseline when the old renderer has no
    /// canonical per-use or per-write table to expose.
    #[cfg(test)]
    pub(crate) fn with_absent_machine_observations(
        source: &SourceOwnedFunctionFacts,
        values: impl Into<Box<[LegacyValueCell]>>,
    ) -> Self {
        let graph = source.source().graph();
        let uses = graph
            .insts
            .iter()
            .map(|inst| {
                (0..inst.inputs.len())
                    .map(|input_idx| LegacyUseCell {
                        site: UseSite {
                            inst: inst.id,
                            input_idx,
                        },
                        observation: LegacyUseObservation::LegacyAbsent,
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice()
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let writes = graph
            .insts
            .iter()
            .map(|inst| {
                inst.output.map(|_| LegacyWriteCell {
                    inst: inst.id,
                    observation: LegacyWriteObservation::LegacyAbsent,
                })
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        Self::new(source, values, uses, writes)
    }

    #[cfg(test)]
    pub(crate) fn use_observation(&self, site: UseSite) -> Option<LegacyUseObservation> {
        self.uses
            .get(site.inst.0 as usize)?
            .get(site.input_idx)
            .filter(|cell| cell.site == site)
            .map(|cell| cell.observation)
    }
}

/// Typed pointer to the canonical evidence used for a classification.
///
/// These variants are lookup keys, not cached answers.  Machine geometry and
/// refusal reasons remain in `BindingPlan::machine_projection`; binding
/// membership remains in the sealed value disposition and its upstream
/// certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ShadowEvidenceKey {
    UpstreamBindingComponent {
        value: ValueId,
        component: CanonicalComponentId,
    },
    UpstreamLiteral {
        value: ValueId,
    },
    UpstreamValueElision {
        value: ValueId,
    },
    UpstreamValueRefusal {
        value: ValueId,
    },
    MachineUse {
        site: UseSite,
    },
    MachineWrite {
        inst: InstId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WrongReason {
    LegacyAbsent,
    DispositionMismatch,
    EquivalenceClassMismatch,
}

/// Judgment of one side against canonical evidence, before the two sides are
/// compared with each other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SideJudgment {
    Correct,
    Wrong(WrongReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BothWrongRelation {
    Equal,
    Different,
}

/// Full old-vs-shadow classification.
///
/// Equal observations do not imply correctness: `BothWrong(Equal)` is a
/// first-class outcome and contributes to the failing `both_wrong` count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ShadowClassification {
    AgreeCorrect,
    OldWrong,
    ShadowWrong,
    BothWrong(BothWrongRelation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CanonicalDispositionKind {
    Representable,
    Refused,
}

/// One dense classified cell.  It contains no canonical disposition payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ShadowCell<K> {
    key: K,
    evidence: ShadowEvidenceKey,
    canonical_kind: CanonicalDispositionKind,
    old: SideJudgment,
    shadow: SideJudgment,
    observations_equal: bool,
    classification: ShadowClassification,
}

impl<K: Copy> ShadowCell<K> {
    #[cfg(test)]
    pub(crate) const fn key(&self) -> K {
        self.key
    }

    #[cfg(test)]
    pub(crate) const fn old_judgment(&self) -> SideJudgment {
        self.old
    }

    #[cfg(test)]
    pub(crate) const fn shadow_judgment(&self) -> SideJudgment {
        self.shadow
    }

    #[cfg(test)]
    pub(crate) const fn classification(&self) -> ShadowClassification {
        self.classification
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct DomainLedger {
    pub(crate) total: usize,
    pub(crate) observed: usize,
    pub(crate) agree_correct: usize,
    pub(crate) old_wrong: usize,
    pub(crate) shadow_wrong: usize,
    pub(crate) both_wrong_equal: usize,
    pub(crate) both_wrong_different: usize,
    pub(crate) unclassified: usize,
    pub(crate) refused: usize,
}

impl DomainLedger {
    fn from_cells<'a, K: 'a>(total: usize, cells: impl Iterator<Item = &'a ShadowCell<K>>) -> Self {
        // `total` comes from an independent enumeration of the exact source
        // graph. `observed` comes only from report cells. Keeping those paths
        // separate makes deletion/duplication visible in the ledger equation.
        let mut ledger = Self {
            total,
            ..Self::default()
        };
        for cell in cells {
            ledger.observed += 1;
            ledger.refused += usize::from(cell.canonical_kind == CanonicalDispositionKind::Refused);
            match cell.classification {
                ShadowClassification::AgreeCorrect => ledger.agree_correct += 1,
                ShadowClassification::OldWrong => ledger.old_wrong += 1,
                ShadowClassification::ShadowWrong => ledger.shadow_wrong += 1,
                ShadowClassification::BothWrong(BothWrongRelation::Equal) => {
                    ledger.both_wrong_equal += 1;
                }
                ShadowClassification::BothWrong(BothWrongRelation::Different) => {
                    ledger.both_wrong_different += 1;
                }
            }
        }
        ledger
    }

    pub(crate) const fn classified(self) -> usize {
        self.agree_correct
            + self.old_wrong
            + self.shadow_wrong
            + self.both_wrong_equal
            + self.both_wrong_different
    }

    pub(crate) const fn both_wrong(self) -> usize {
        self.both_wrong_equal + self.both_wrong_different
    }

    pub(crate) const fn shadow_wrong_total(self) -> usize {
        self.shadow_wrong + self.both_wrong()
    }

    pub(crate) const fn equations_hold(self) -> bool {
        self.total == self.observed
            && self.observed == self.classified() + self.unclassified
            && self.classified()
                == self.agree_correct + self.old_wrong + self.shadow_wrong + self.both_wrong()
            && self.both_wrong() == self.both_wrong_equal + self.both_wrong_different
    }

    /// Stage 4 soundness gate.  Legacy errors are findings; shadow errors,
    /// unclassified cells, and both-wrong cells fail the cutover gate.
    #[cfg(test)]
    pub(crate) const fn passes_stage4(self) -> bool {
        self.equations_hold()
            && self.shadow_wrong_total() == 0
            && self.both_wrong() == 0
            && self.unclassified == 0
    }

    /// Quality is stricter than soundness: even an upstream-justified refusal
    /// remains visible failure rather than an earned semantic pass.
    pub(crate) const fn passes_quality(self) -> bool {
        self.equations_hold()
            && self.shadow_wrong_total() == 0
            && self.both_wrong() == 0
            && self.unclassified == 0
            && self.refused == 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ShadowLedger {
    pub(crate) values: DomainLedger,
    pub(crate) uses: DomainLedger,
    pub(crate) writes: DomainLedger,
}

impl ShadowLedger {
    pub(crate) const fn equations_hold(self) -> bool {
        self.values.equations_hold() && self.uses.equations_hold() && self.writes.equations_hold()
    }

    #[cfg(test)]
    pub(crate) const fn passes_stage4(self) -> bool {
        self.values.passes_stage4() && self.uses.passes_stage4() && self.writes.passes_stage4()
    }

    pub(crate) const fn passes_quality(self) -> bool {
        self.values.passes_quality() && self.uses.passes_quality() && self.writes.passes_quality()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ShadowReportError {
    SourceMismatch(BindingPlanSourceMismatch),
    LegacyAuthority,
    UpstreamOracle(BindingPlanBuildError),
    EmptyCanonicalDomains,
    GraphValueTopology {
        index: usize,
        value: ValueId,
    },
    GraphInstTopology {
        index: usize,
        inst: InstId,
    },
    LegacyValueCount {
        expected: usize,
        actual: usize,
    },
    LegacyValueTopology {
        index: usize,
        value: ValueId,
    },
    LegacyUseRowCount {
        expected: usize,
        actual: usize,
    },
    LegacyUseCount {
        inst: InstId,
        expected: usize,
        actual: usize,
    },
    LegacyUseTopology {
        expected: UseSite,
        actual: UseSite,
    },
    LegacyWriteCount {
        expected: usize,
        actual: usize,
    },
    LegacyWritePresence {
        inst: InstId,
        expected: bool,
    },
    LegacyWriteTopology {
        expected: InstId,
        actual: InstId,
    },
    MissingPlanValue {
        value: ValueId,
    },
    MissingPlanUse {
        site: UseSite,
    },
    MissingPlanWrite {
        inst: InstId,
    },
    MissingCanonicalValue {
        value: ValueId,
    },
    MissingCanonicalComponent {
        component: CanonicalComponentId,
    },
    MissingCanonicalUse {
        site: UseSite,
    },
    MissingCanonicalWrite {
        inst: InstId,
    },
    InvalidPlanValue {
        value: ValueId,
    },
    InvalidLegacyBinding {
        binding: LegacyBindingId,
    },
    ReportValueCount {
        expected: usize,
        actual: usize,
    },
    ReportUseRowCount {
        expected: usize,
        actual: usize,
    },
    ReportUseCount {
        inst: InstId,
        expected: usize,
        actual: usize,
    },
    ReportWriteCount {
        expected: usize,
        actual: usize,
    },
    ReportWritePresence {
        inst: InstId,
        expected: bool,
    },
    ReportClassification {
        evidence: ShadowEvidenceKey,
    },
    ReportCellMismatch {
        evidence: ShadowEvidenceKey,
        field: ReportCellField,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReportCellField {
    Key,
    Evidence,
    CanonicalKind,
    OldJudgment,
    ShadowJudgment,
    ObservationEquality,
    Classification,
}

/// Dense Stage 4 diagnostic report.  It is deliberately not a lowering input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ShadowReport {
    values: Box<[ShadowCell<ValueId>]>,
    uses: Box<[Box<[ShadowCell<UseSite>]>]>,
    writes: Box<[Option<ShadowCell<InstId>>]>,
}

mod classification;

#[cfg(test)]
use classification::classify_sides;
impl ShadowReport {
    #[cfg(test)]
    pub(crate) const fn uses(&self) -> &[Box<[ShadowCell<UseSite>]>] {
        &self.uses
    }

    pub(crate) fn ledger(&self, source_owned: &SourceOwnedFunctionFacts) -> ShadowLedger {
        let graph = source_owned.source().graph();
        ShadowLedger {
            values: DomainLedger::from_cells(graph.values.len(), self.values.iter()),
            uses: DomainLedger::from_cells(
                graph.insts.iter().map(|inst| inst.inputs.len()).sum(),
                self.uses.iter().flat_map(|row| row.iter()),
            ),
            writes: DomainLedger::from_cells(
                graph
                    .insts
                    .iter()
                    .filter(|inst| inst.output.is_some())
                    .count(),
                self.writes.iter().filter_map(Option::as_ref),
            ),
        }
    }
}

#[cfg(test)]
mod tests;
