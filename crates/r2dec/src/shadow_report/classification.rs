use std::collections::{BTreeMap, BTreeSet};

use crate::binding_plan::BindingId;

use super::*;

pub(super) fn classify_sides(
    old: SideJudgment,
    shadow: SideJudgment,
    observations_equal: bool,
) -> ShadowClassification {
    match (old, shadow) {
        (SideJudgment::Correct, SideJudgment::Correct) => ShadowClassification::AgreeCorrect,
        (SideJudgment::Wrong(_), SideJudgment::Correct) => ShadowClassification::OldWrong,
        (SideJudgment::Correct, SideJudgment::Wrong(_)) => ShadowClassification::ShadowWrong,
        (SideJudgment::Wrong(_), SideJudgment::Wrong(_)) => {
            ShadowClassification::BothWrong(if observations_equal {
                BothWrongRelation::Equal
            } else {
                BothWrongRelation::Different
            })
        }
    }
}

/// Run-local interned identity of one exact sorted member set.
///
/// IDs are shared by canonical, candidate, and legacy observations only after
/// exact member equality. Each unique set is stored once, so per-value
/// normalization is `Copy` instead of cloning a whole equivalence class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ValueClassId(u32);

#[derive(Default)]
struct ValueClassInterner {
    classes: BTreeMap<Box<[ValueId]>, ValueClassId>,
}

impl ValueClassInterner {
    fn intern(&mut self, members: impl IntoIterator<Item = ValueId>) -> ValueClassId {
        let members = members.into_iter().collect::<Vec<_>>().into_boxed_slice();
        if let Some(id) = self.classes.get(members.as_ref()) {
            return *id;
        }
        let id = ValueClassId(self.classes.len() as u32);
        self.classes.insert(members, id);
        id
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NormalizedValueObservation {
    Bound(ValueClassId),
    InlineConstant,
    InlineNonLiteral,
    Elided(r2ssa::ledger::ElisionReason),
    Refused(ValueRefusal),
    LegacyAbsent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NormalizedUseObservation {
    Exact(MachineUseSlice),
    MemoryAddress(r2ssa::MachineValueUse),
    Elided(r2ssa::ledger::ElisionReason),
    Refused(MachineUseRefusal),
    LegacyAbsent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NormalizedWriteObservation {
    Exact(MachineWriteProjection),
    Elided(r2ssa::ledger::ElisionReason),
    Refused(MachineWriteRefusal),
    LegacyAbsent,
}

struct ValueClassIndexes {
    canonical: BTreeMap<CanonicalComponentId, ValueClassId>,
    candidate: BTreeMap<BindingId, ValueClassId>,
    legacy: BTreeMap<LegacyBindingId, ValueClassId>,
}

impl ShadowReport {
    pub(crate) fn build(
        plan: &BindingPlan,
        source_owned: &SourceOwnedFunctionFacts,
        legacy: &LegacyAnalysisSnapshot,
    ) -> Result<Self, ShadowReportError> {
        derive_report(plan, source_owned, legacy)
    }

    pub(crate) fn validate_against(
        &self,
        plan: &BindingPlan,
        source_owned: &SourceOwnedFunctionFacts,
        legacy: &LegacyAnalysisSnapshot,
    ) -> Result<(), ShadowReportError> {
        let expected = derive_report(plan, source_owned, legacy)?;
        compare_reports(self, &expected)?;
        if !self.ledger(source_owned).equations_hold() {
            return Err(ShadowReportError::ReportClassification {
                evidence: first_evidence(&expected)
                    .ok_or(ShadowReportError::EmptyCanonicalDomains)?,
            });
        }
        Ok(())
    }
}

fn derive_report(
    plan: &BindingPlan,
    source_owned: &SourceOwnedFunctionFacts,
    legacy: &LegacyAnalysisSnapshot,
) -> Result<ShadowReport, ShadowReportError> {
    let source = source_owned.source();
    plan.validate_source(source)
        .map_err(ShadowReportError::SourceMismatch)?;
    validate_graph_topology(source.graph())?;
    validate_legacy_snapshot(source, legacy)?;
    // The plan's projection, not a second one: `validate_source` above has
    // already proven it is what this source produces, and the oracle's
    // independence is from the plan's decisions rather than from its arena.
    let canonical = build_upstream_shadow_oracle(source_owned, plan.machine_projection())
        .map_err(ShadowReportError::UpstreamOracle)?;
    let graph = source.graph();
    let classes = value_class_indexes(plan, graph, legacy, &canonical)?;

    // V, U, and W are deliberately enumerated by independent graph walks.
    // Neither a candidate plan table nor a legacy snapshot defines a domain.
    let values = graph
        .values
        .iter()
        .map(|graph_value| {
            let value = graph_value.id;
            let canonical_observation = normalized_upstream_value(&canonical, value, &classes)?;
            let candidate_observation = normalized_candidate_value(plan, value, &classes)?;
            let old_observation =
                normalized_legacy_value(legacy.values[value.0 as usize].observation, &classes)?;
            let evidence = upstream_value_evidence(&canonical, value)?;
            let old_judgment = judge_value(old_observation, canonical_observation);
            let shadow_judgment = judge_value(candidate_observation, canonical_observation);
            let observations_equal = old_observation == candidate_observation;
            Ok(ShadowCell {
                key: value,
                evidence,
                canonical_kind: canonical_value_kind(canonical_observation),
                old: old_judgment,
                shadow: shadow_judgment,
                observations_equal,
                classification: classify_sides(old_judgment, shadow_judgment, observations_equal),
            })
        })
        .collect::<Result<Vec<_>, ShadowReportError>>()?
        .into_boxed_slice();

    let uses = graph
        .insts
        .iter()
        .map(|inst| {
            (0..inst.inputs.len())
                .map(|input_idx| {
                    let site = UseSite {
                        inst: inst.id,
                        input_idx,
                    };
                    let canonical_disposition = canonical
                        .use_disposition(site)
                        .ok_or(ShadowReportError::MissingCanonicalUse { site })?;
                    let candidate_disposition = plan
                        .use_disposition(site)
                        .ok_or(ShadowReportError::MissingPlanUse { site })?;
                    let canonical_observation = normalized_machine_use(canonical_disposition);
                    let candidate_observation = normalized_machine_use(candidate_disposition);
                    let old_observation = normalized_legacy_use(
                        legacy.uses[inst.id.0 as usize][input_idx].observation,
                    );
                    let old_judgment = judge_use(old_observation, canonical_observation);
                    let shadow_judgment = judge_use(candidate_observation, canonical_observation);
                    let observations_equal = old_observation == candidate_observation;
                    Ok(ShadowCell {
                        key: site,
                        evidence: ShadowEvidenceKey::MachineUse { site },
                        canonical_kind: canonical_use_kind(canonical_disposition),
                        old: old_judgment,
                        shadow: shadow_judgment,
                        observations_equal,
                        classification: classify_sides(
                            old_judgment,
                            shadow_judgment,
                            observations_equal,
                        ),
                    })
                })
                .collect::<Result<Vec<_>, ShadowReportError>>()
                .map(Vec::into_boxed_slice)
        })
        .collect::<Result<Vec<_>, ShadowReportError>>()?
        .into_boxed_slice();

    let writes = graph
        .insts
        .iter()
        .map(|inst| {
            let Some(_) = inst.output else {
                return Ok(None);
            };
            let canonical_disposition = canonical
                .write_disposition(inst.id)
                .ok_or(ShadowReportError::MissingCanonicalWrite { inst: inst.id })?;
            let candidate_disposition = plan
                .write_disposition(inst.id)
                .ok_or(ShadowReportError::MissingPlanWrite { inst: inst.id })?;
            let canonical_observation = normalized_machine_write(canonical_disposition);
            let candidate_observation = normalized_machine_write(candidate_disposition);
            let old_observation = normalized_legacy_write(
                legacy.writes[inst.id.0 as usize]
                    .expect("legacy write presence validated")
                    .observation,
            );
            let old_judgment = judge_write(old_observation, canonical_observation);
            let shadow_judgment = judge_write(candidate_observation, canonical_observation);
            let observations_equal = old_observation == candidate_observation;
            Ok(Some(ShadowCell {
                key: inst.id,
                evidence: ShadowEvidenceKey::MachineWrite { inst: inst.id },
                canonical_kind: canonical_write_kind(canonical_disposition),
                old: old_judgment,
                shadow: shadow_judgment,
                observations_equal,
                classification: classify_sides(old_judgment, shadow_judgment, observations_equal),
            }))
        })
        .collect::<Result<Vec<_>, ShadowReportError>>()?
        .into_boxed_slice();

    let report = ShadowReport {
        values,
        uses,
        writes,
    };
    if !graph.insts.is_empty()
        && report.values.is_empty()
        && report.uses.iter().all(|row| row.is_empty())
        && report.writes.iter().all(Option::is_none)
    {
        return Err(ShadowReportError::EmptyCanonicalDomains);
    }
    Ok(report)
}

fn value_class_indexes(
    plan: &BindingPlan,
    graph: &r2ssa::SsaGraph,
    legacy: &LegacyAnalysisSnapshot,
    canonical: &UpstreamShadowOracle<'_>,
) -> Result<ValueClassIndexes, ShadowReportError> {
    let mut interner = ValueClassInterner::default();

    let canonical_components = graph
        .values
        .iter()
        .filter_map(|value| match canonical.value_disposition(value.id) {
            Some(UpstreamValueDisposition::Bound { component }) => Some(Ok(component)),
            Some(_) => None,
            None => Some(Err(ShadowReportError::MissingCanonicalValue {
                value: value.id,
            })),
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let mut canonical_classes = BTreeMap::new();
    for component in canonical_components {
        let members = canonical
            .component(component)
            .ok_or(ShadowReportError::MissingCanonicalComponent { component })?;
        canonical_classes.insert(component, interner.intern(members.iter().copied()));
    }

    let mut candidate_members = BTreeMap::<BindingId, Vec<ValueId>>::new();
    for value in &graph.values {
        match plan.disposition(value.id) {
            Some(ValueDisposition::Bound { binding }) => {
                candidate_members
                    .entry(*binding)
                    .or_default()
                    .push(value.id);
            }
            Some(_) => {}
            None => return Err(ShadowReportError::MissingPlanValue { value: value.id }),
        }
    }
    let candidate = candidate_members
        .into_iter()
        .map(|(binding, members)| (binding, interner.intern(members)))
        .collect();

    let mut legacy_members = BTreeMap::<LegacyBindingId, Vec<ValueId>>::new();
    for cell in &legacy.values {
        if let LegacyValueObservation::Bound { binding } = cell.observation {
            legacy_members.entry(binding).or_default().push(cell.value);
        }
    }
    let legacy = legacy_members
        .into_iter()
        .map(|(binding, members)| (binding, interner.intern(members)))
        .collect();

    Ok(ValueClassIndexes {
        canonical: canonical_classes,
        candidate,
        legacy,
    })
}

fn normalized_upstream_value(
    canonical: &UpstreamShadowOracle<'_>,
    value: ValueId,
    classes: &ValueClassIndexes,
) -> Result<NormalizedValueObservation, ShadowReportError> {
    match canonical
        .value_disposition(value)
        .ok_or(ShadowReportError::MissingCanonicalValue { value })?
    {
        UpstreamValueDisposition::Bound { component } => classes
            .canonical
            .get(&component)
            .copied()
            .map(NormalizedValueObservation::Bound)
            .ok_or(ShadowReportError::MissingCanonicalComponent { component }),
        UpstreamValueDisposition::InlineConstant => Ok(NormalizedValueObservation::InlineConstant),
        UpstreamValueDisposition::InlineExpression => {
            Ok(NormalizedValueObservation::InlineNonLiteral)
        }
        UpstreamValueDisposition::Elided(reason) => Ok(NormalizedValueObservation::Elided(reason)),
        UpstreamValueDisposition::Refused(reason) => {
            Ok(NormalizedValueObservation::Refused(reason))
        }
    }
}

fn normalized_candidate_value(
    plan: &BindingPlan,
    value: ValueId,
    classes: &ValueClassIndexes,
) -> Result<NormalizedValueObservation, ShadowReportError> {
    match plan
        .disposition(value)
        .ok_or(ShadowReportError::MissingPlanValue { value })?
    {
        ValueDisposition::Bound { binding } => classes
            .candidate
            .get(binding)
            .copied()
            .map(NormalizedValueObservation::Bound)
            .ok_or(ShadowReportError::InvalidPlanValue { value }),
        // The plan inlines two kinds of value and the oracle tells them apart:
        // a constant, and a computed value rendered where it is read. Calling
        // both a constant here disagreed with the oracle on every function
        // that folded anything, which is nearly all of them.
        ValueDisposition::Inline { expr, .. } => Ok(
            match plan
                .machine_projection()
                .expr(*expr)
                .map(|node| node.kind())
            {
                Some(r2ssa::MachineExprKind::Constant { binding, .. })
                    if binding.value() == value =>
                {
                    NormalizedValueObservation::InlineConstant
                }
                _ => NormalizedValueObservation::InlineNonLiteral,
            },
        ),
        ValueDisposition::Elided { reason, .. } => Ok(NormalizedValueObservation::Elided(*reason)),
        ValueDisposition::Refused { reason } => Ok(NormalizedValueObservation::Refused(*reason)),
    }
}

fn normalized_legacy_value(
    observation: LegacyValueObservation,
    classes: &ValueClassIndexes,
) -> Result<NormalizedValueObservation, ShadowReportError> {
    match observation {
        LegacyValueObservation::Bound { binding } => classes
            .legacy
            .get(&binding)
            .copied()
            .map(NormalizedValueObservation::Bound)
            .ok_or(ShadowReportError::InvalidLegacyBinding { binding }),
        LegacyValueObservation::InlineConstant => Ok(NormalizedValueObservation::InlineConstant),
        LegacyValueObservation::InlineNonLiteral => {
            Ok(NormalizedValueObservation::InlineNonLiteral)
        }
        LegacyValueObservation::Elided(reason) => Ok(NormalizedValueObservation::Elided(reason)),
        LegacyValueObservation::Refused(reason) => Ok(NormalizedValueObservation::Refused(reason)),
        LegacyValueObservation::LegacyAbsent => Ok(NormalizedValueObservation::LegacyAbsent),
    }
}

fn upstream_value_evidence(
    canonical: &UpstreamShadowOracle<'_>,
    value: ValueId,
) -> Result<ShadowEvidenceKey, ShadowReportError> {
    match canonical
        .value_disposition(value)
        .ok_or(ShadowReportError::MissingCanonicalValue { value })?
    {
        UpstreamValueDisposition::Bound { component } => {
            Ok(ShadowEvidenceKey::UpstreamBindingComponent { value, component })
        }
        UpstreamValueDisposition::InlineConstant => {
            Ok(ShadowEvidenceKey::UpstreamLiteral { value })
        }
        UpstreamValueDisposition::InlineExpression => {
            Ok(ShadowEvidenceKey::UpstreamInlineExpression { value })
        }
        UpstreamValueDisposition::Elided(_) => {
            Ok(ShadowEvidenceKey::UpstreamValueElision { value })
        }
        UpstreamValueDisposition::Refused(_) => {
            Ok(ShadowEvidenceKey::UpstreamValueRefusal { value })
        }
    }
}

fn judge_value(
    observed: NormalizedValueObservation,
    canonical: NormalizedValueObservation,
) -> SideJudgment {
    if observed == canonical {
        return SideJudgment::Correct;
    }
    match observed {
        NormalizedValueObservation::LegacyAbsent => SideJudgment::Wrong(WrongReason::LegacyAbsent),
        NormalizedValueObservation::Bound(_)
            if matches!(canonical, NormalizedValueObservation::Bound(_)) =>
        {
            SideJudgment::Wrong(WrongReason::EquivalenceClassMismatch)
        }
        _ => SideJudgment::Wrong(WrongReason::DispositionMismatch),
    }
}

fn canonical_value_kind(canonical: NormalizedValueObservation) -> CanonicalDispositionKind {
    if matches!(canonical, NormalizedValueObservation::Refused(_)) {
        CanonicalDispositionKind::Refused
    } else {
        CanonicalDispositionKind::Representable
    }
}

fn normalized_machine_use(disposition: &MachineUseDisposition) -> NormalizedUseObservation {
    match *disposition {
        MachineUseDisposition::Exact(slice) => NormalizedUseObservation::Exact(slice),
        MachineUseDisposition::MemoryAddress(address) => {
            NormalizedUseObservation::MemoryAddress(address)
        }
        MachineUseDisposition::Refused(reason) => NormalizedUseObservation::Refused(reason),
    }
}

fn normalized_legacy_use(observation: LegacyUseObservation) -> NormalizedUseObservation {
    match observation {
        LegacyUseObservation::Exact(slice) => NormalizedUseObservation::Exact(slice),
        LegacyUseObservation::MemoryAddress(address) => {
            NormalizedUseObservation::MemoryAddress(address)
        }
        LegacyUseObservation::Elided(reason) => NormalizedUseObservation::Elided(reason),
        LegacyUseObservation::Refused(reason) => NormalizedUseObservation::Refused(reason),
        LegacyUseObservation::LegacyAbsent => NormalizedUseObservation::LegacyAbsent,
    }
}

fn judge_use(
    observed: NormalizedUseObservation,
    canonical: NormalizedUseObservation,
) -> SideJudgment {
    if observed == canonical {
        SideJudgment::Correct
    } else if matches!(observed, NormalizedUseObservation::LegacyAbsent) {
        SideJudgment::Wrong(WrongReason::LegacyAbsent)
    } else {
        SideJudgment::Wrong(WrongReason::DispositionMismatch)
    }
}

fn canonical_use_kind(disposition: &MachineUseDisposition) -> CanonicalDispositionKind {
    match disposition {
        MachineUseDisposition::Exact(_) | MachineUseDisposition::MemoryAddress(_) => {
            CanonicalDispositionKind::Representable
        }
        MachineUseDisposition::Refused(_) => CanonicalDispositionKind::Refused,
    }
}

fn normalized_machine_write(disposition: &MachineWriteDisposition) -> NormalizedWriteObservation {
    match *disposition {
        MachineWriteDisposition::Exact(write) => NormalizedWriteObservation::Exact(write),
        MachineWriteDisposition::Refused(reason) => NormalizedWriteObservation::Refused(reason),
    }
}

fn normalized_legacy_write(observation: LegacyWriteObservation) -> NormalizedWriteObservation {
    match observation {
        LegacyWriteObservation::Exact(write) => NormalizedWriteObservation::Exact(write),
        LegacyWriteObservation::Elided(reason) => NormalizedWriteObservation::Elided(reason),
        LegacyWriteObservation::Refused(reason) => NormalizedWriteObservation::Refused(reason),
        LegacyWriteObservation::LegacyAbsent => NormalizedWriteObservation::LegacyAbsent,
    }
}

fn judge_write(
    observed: NormalizedWriteObservation,
    canonical: NormalizedWriteObservation,
) -> SideJudgment {
    if observed == canonical {
        SideJudgment::Correct
    } else if matches!(observed, NormalizedWriteObservation::LegacyAbsent) {
        SideJudgment::Wrong(WrongReason::LegacyAbsent)
    } else {
        SideJudgment::Wrong(WrongReason::DispositionMismatch)
    }
}

fn canonical_write_kind(disposition: &MachineWriteDisposition) -> CanonicalDispositionKind {
    match disposition {
        MachineWriteDisposition::Exact(_) => CanonicalDispositionKind::Representable,
        MachineWriteDisposition::Refused(_) => CanonicalDispositionKind::Refused,
    }
}

fn validate_graph_topology(graph: &r2ssa::SsaGraph) -> Result<(), ShadowReportError> {
    for (index, value) in graph.values.iter().enumerate() {
        if value.id.0 as usize != index {
            return Err(ShadowReportError::GraphValueTopology {
                index,
                value: value.id,
            });
        }
    }
    for (index, inst) in graph.insts.iter().enumerate() {
        if inst.id.0 as usize != index {
            return Err(ShadowReportError::GraphInstTopology {
                index,
                inst: inst.id,
            });
        }
    }
    Ok(())
}

fn validate_legacy_snapshot(
    source: &r2ssa::SsaArtifact,
    legacy: &LegacyAnalysisSnapshot,
) -> Result<(), ShadowReportError> {
    if legacy.authority != *source.authority() {
        return Err(ShadowReportError::LegacyAuthority);
    }
    let graph = source.graph();
    if legacy.values.len() != graph.values.len() {
        return Err(ShadowReportError::LegacyValueCount {
            expected: graph.values.len(),
            actual: legacy.values.len(),
        });
    }
    for (index, cell) in legacy.values.iter().enumerate() {
        if cell.value.0 as usize != index {
            return Err(ShadowReportError::LegacyValueTopology {
                index,
                value: cell.value,
            });
        }
    }
    if legacy.uses.len() != graph.insts.len() {
        return Err(ShadowReportError::LegacyUseRowCount {
            expected: graph.insts.len(),
            actual: legacy.uses.len(),
        });
    }
    if legacy.writes.len() != graph.insts.len() {
        return Err(ShadowReportError::LegacyWriteCount {
            expected: graph.insts.len(),
            actual: legacy.writes.len(),
        });
    }
    for inst in &graph.insts {
        let row = &legacy.uses[inst.id.0 as usize];
        if row.len() != inst.inputs.len() {
            return Err(ShadowReportError::LegacyUseCount {
                inst: inst.id,
                expected: inst.inputs.len(),
                actual: row.len(),
            });
        }
        for (input_idx, cell) in row.iter().enumerate() {
            let expected = UseSite {
                inst: inst.id,
                input_idx,
            };
            if cell.site != expected {
                return Err(ShadowReportError::LegacyUseTopology {
                    expected,
                    actual: cell.site,
                });
            }
        }
        let write = &legacy.writes[inst.id.0 as usize];
        if write.is_some() != inst.output.is_some() {
            return Err(ShadowReportError::LegacyWritePresence {
                inst: inst.id,
                expected: inst.output.is_some(),
            });
        }
        if let Some(write) = write
            && write.inst != inst.id
        {
            return Err(ShadowReportError::LegacyWriteTopology {
                expected: inst.id,
                actual: write.inst,
            });
        }
    }
    Ok(())
}

fn compare_reports(
    actual: &ShadowReport,
    expected: &ShadowReport,
) -> Result<(), ShadowReportError> {
    if actual.values.len() != expected.values.len() {
        return Err(ShadowReportError::ReportValueCount {
            expected: expected.values.len(),
            actual: actual.values.len(),
        });
    }
    if actual.uses.len() != expected.uses.len() {
        return Err(ShadowReportError::ReportUseRowCount {
            expected: expected.uses.len(),
            actual: actual.uses.len(),
        });
    }
    if actual.writes.len() != expected.writes.len() {
        return Err(ShadowReportError::ReportWriteCount {
            expected: expected.writes.len(),
            actual: actual.writes.len(),
        });
    }
    for (actual, expected) in actual.values.iter().zip(expected.values.iter()) {
        compare_cell(actual, expected)?;
    }
    for (inst_index, (actual, expected)) in actual.uses.iter().zip(expected.uses.iter()).enumerate()
    {
        if actual.len() != expected.len() {
            return Err(ShadowReportError::ReportUseCount {
                inst: InstId(inst_index as u32),
                expected: expected.len(),
                actual: actual.len(),
            });
        }
        for (actual, expected) in actual.iter().zip(expected.iter()) {
            compare_cell(actual, expected)?;
        }
    }
    for (inst_index, (actual, expected)) in
        actual.writes.iter().zip(expected.writes.iter()).enumerate()
    {
        if actual.is_some() != expected.is_some() {
            return Err(ShadowReportError::ReportWritePresence {
                inst: InstId(inst_index as u32),
                expected: expected.is_some(),
            });
        }
        if let (Some(actual), Some(expected)) = (actual, expected) {
            compare_cell(actual, expected)?;
        }
    }
    Ok(())
}

fn compare_cell<K: Copy + PartialEq>(
    actual: &ShadowCell<K>,
    expected: &ShadowCell<K>,
) -> Result<(), ShadowReportError> {
    let mismatch = if actual.key != expected.key {
        Some(ReportCellField::Key)
    } else if actual.evidence != expected.evidence {
        Some(ReportCellField::Evidence)
    } else if actual.canonical_kind != expected.canonical_kind {
        Some(ReportCellField::CanonicalKind)
    } else if actual.old != expected.old {
        Some(ReportCellField::OldJudgment)
    } else if actual.shadow != expected.shadow {
        Some(ReportCellField::ShadowJudgment)
    } else if actual.observations_equal != expected.observations_equal {
        Some(ReportCellField::ObservationEquality)
    } else if actual.classification != expected.classification {
        Some(ReportCellField::Classification)
    } else {
        None
    };
    if let Some(field) = mismatch {
        return Err(ShadowReportError::ReportCellMismatch {
            evidence: expected.evidence,
            field,
        });
    }
    Ok(())
}

fn first_evidence(report: &ShadowReport) -> Option<ShadowEvidenceKey> {
    report
        .values
        .first()
        .map(|cell| cell.evidence)
        .or_else(|| {
            report
                .uses
                .iter()
                .find_map(|row| row.first().map(|cell| cell.evidence))
        })
        .or_else(|| {
            report
                .writes
                .iter()
                .find_map(|cell| cell.as_ref().map(|cell| cell.evidence))
        })
}
