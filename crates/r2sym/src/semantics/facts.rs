use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use r2il::ArchSpec;
use r2ssa::{
    InterprocFunctionId, PreparedInterprocSummarySet, SsaArtifact, SummaryMemoryEffect,
    SummaryMemoryEffectKind, SummaryMemoryRegion,
};
use serde::{Deserialize, Serialize};
use z3::Context;

use crate::backward::{
    BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
    BackwardMemoryRegion, compile_branch_preconditions,
};
use crate::control::SymExecutionControl;
use crate::path::{ExploreConfig, PathExplorer};
use crate::runtime::{seed_default_state_for_arch, seed_default_state_for_prepared};
use crate::semantics::{
    SemanticArtifact, SemanticArtifactBody, SemanticEvidence, SemanticEvidenceAmbiguity,
    SemanticEvidenceCoverage, SemanticEvidenceProvenance, SemanticEvidenceReason,
};
use crate::sim::{SummaryProfile, SummaryRegistry};
use crate::solver::SatResult;
use crate::{SemanticMemoryAddress, SymState};

use super::region::{
    ControlFact, Judged, MemoryFact, NativeRegionSummary, NativeWorkerSummary, RegionKey,
    SemanticRegion, TargetFact,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolicReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicFunctionFactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
}

#[derive(Debug, Clone, Default)]
pub(super) struct CollectedNativeSemanticRegions {
    pub regions: BTreeMap<RegionKey, SemanticRegion>,
    pub diagnostics: SymbolicFunctionFactDiagnostics,
    pub region_summaries: Vec<NativeRegionSummary>,
    pub worker_summaries: Vec<NativeWorkerSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BranchObservation {
    block_addr: u64,
    true_target: u64,
    false_target: u64,
    true_status: SymbolicReachabilityStatus,
    false_status: SymbolicReachabilityStatus,
    true_condition: Option<String>,
    false_condition: Option<String>,
    true_compiled: Option<BackwardConditionSummary>,
    false_compiled: Option<BackwardConditionSummary>,
}

fn target_status_evidence(status: SymbolicReachabilityStatus) -> SemanticEvidence {
    match status {
        SymbolicReachabilityStatus::Reachable | SymbolicReachabilityStatus::Unreachable => {
            SemanticEvidence::exact()
        }
        SymbolicReachabilityStatus::Unknown => {
            SemanticEvidence::residual(SemanticEvidenceReason::ResidualSearchRequired)
        }
    }
}

fn push_unique_judged<T: PartialEq>(dst: &mut Vec<Judged<T>>, value: Judged<T>) {
    if !dst.contains(&value) {
        dst.push(value);
    }
}

fn ensure_semantic_region(
    by_anchor: &mut BTreeMap<u64, SemanticRegion>,
    anchor: u64,
) -> &mut SemanticRegion {
    by_anchor.entry(anchor).or_insert_with(|| SemanticRegion {
        anchor,
        frontier: BTreeSet::new(),
        control: Vec::new(),
        memory: Vec::new(),
        pre: Vec::new(),
        post: Vec::new(),
        targets: Vec::new(),
    })
}

fn push_region_memory_terms(
    region: &mut SemanticRegion,
    terms: impl IntoIterator<Item = BackwardMemoryCondition>,
) {
    for term in terms {
        push_unique_judged(
            &mut region.memory,
            Judged::new(MemoryFact { term: term.clone() }, term.evidence().clone()),
        );
    }
}

fn push_branch_observation_region(
    by_anchor: &mut BTreeMap<u64, SemanticRegion>,
    branch: &BranchObservation,
    diagnostics: &SymbolicFunctionFactDiagnostics,
) {
    let region = ensure_semantic_region(by_anchor, branch.block_addr);
    region.frontier.insert(branch.true_target);
    region.frontier.insert(branch.false_target);

    let true_evidence = if branch.true_compiled.is_some() || branch.true_condition.is_some() {
        control_fact_evidence(
            branch.true_compiled.as_ref(),
            branch.true_condition.as_deref(),
            diagnostics,
        )
    } else {
        target_status_evidence(branch.true_status)
    };
    let false_evidence = if branch.false_compiled.is_some() || branch.false_condition.is_some() {
        control_fact_evidence(
            branch.false_compiled.as_ref(),
            branch.false_condition.as_deref(),
            diagnostics,
        )
    } else {
        target_status_evidence(branch.false_status)
    };

    push_unique_judged(
        &mut region.control,
        Judged::new(
            ControlFact {
                target: branch.true_target,
                status: branch.true_status,
                branch_truth: Some(true),
                condition: branch.true_condition.clone(),
                compiled: branch.true_compiled.clone(),
            },
            true_evidence.clone(),
        ),
    );
    push_unique_judged(
        &mut region.control,
        Judged::new(
            ControlFact {
                target: branch.false_target,
                status: branch.false_status,
                branch_truth: Some(false),
                condition: branch.false_condition.clone(),
                compiled: branch.false_compiled.clone(),
            },
            false_evidence.clone(),
        ),
    );
    push_unique_judged(
        &mut region.targets,
        Judged::new(
            TargetFact {
                target: branch.true_target,
                status: branch.true_status,
                branch_truth: Some(true),
            },
            true_evidence,
        ),
    );
    push_unique_judged(
        &mut region.targets,
        Judged::new(
            TargetFact {
                target: branch.false_target,
                status: branch.false_status,
                branch_truth: Some(false),
            },
            false_evidence,
        ),
    );
    if let Some(compiled) = branch
        .true_compiled
        .as_ref()
        .filter(|compiled| compiled.evidence().allows_narrowing())
    {
        push_region_memory_terms(region, compiled.memory_terms.iter().cloned());
    }
    if let Some(compiled) = branch
        .false_compiled
        .as_ref()
        .filter(|compiled| compiled.evidence().allows_narrowing())
    {
        push_region_memory_terms(region, compiled.memory_terms.iter().cloned());
    }
}

fn build_canonical_regions(
    branch_observations: &[BranchObservation],
    summary_memory_terms: &BTreeMap<u64, Vec<BackwardMemoryCondition>>,
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> BTreeMap<RegionKey, SemanticRegion> {
    let mut by_anchor = BTreeMap::<u64, SemanticRegion>::new();
    for branch in branch_observations {
        push_branch_observation_region(&mut by_anchor, branch, diagnostics);
    }
    for (&anchor, terms) in summary_memory_terms {
        let region = ensure_semantic_region(&mut by_anchor, anchor);
        push_region_memory_terms(region, terms.iter().cloned());
    }
    by_anchor
        .into_values()
        .map(|region| (region.key(), region))
        .collect()
}

fn append_large_cfg_memory_transfer_terms(
    func: &SsaArtifact,
    regions: &mut BTreeMap<RegionKey, SemanticRegion>,
) -> Vec<NativeWorkerSummary> {
    let transfers = super::native_worker::large_cfg_memory_transfers(func);
    if transfers.is_empty() {
        return Vec::new();
    }
    let mut worker_summaries = Vec::new();
    let mut by_anchor = BTreeMap::<u64, SemanticRegion>::new();
    for region in std::mem::take(regions).into_values() {
        by_anchor.insert(region.anchor, region);
    }
    for transfer in transfers {
        let region = ensure_semantic_region(&mut by_anchor, transfer.block_addr);
        worker_summaries.push(super::native_worker::summary_for_transfer(transfer));
        let term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Argument {
                index: transfer.dst_arg,
            },
            address: SemanticMemoryAddress::bounded(0, 0)
                .expect("single-point summary memory bound"),
            size: transfer.size,
            evidence: SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(SemanticEvidenceProvenance::Stable)
                .with_budget_limited(true),
            binding: Some(format!(
                "copy_arg{}_to_arg{}",
                transfer.src_arg, transfer.dst_arg
            )),
            expr: format!("copy arg{} -> arg{}", transfer.src_arg, transfer.dst_arg),
            value_expr: Some(format!("*arg{}", transfer.src_arg)),
            exact_value: false,
        };
        push_region_memory_terms(region, [term]);
    }
    *regions = by_anchor
        .into_values()
        .map(|region| (region.key(), region))
        .collect();
    worker_summaries
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct JoinedLargeCfgMemoryTermKey {
    kind: SummaryMemoryEffectKind,
    region: BackwardMemoryRegion,
    size: u32,
}

#[derive(Debug, Clone)]
struct JoinedLargeCfgMemoryTerm {
    key: JoinedLargeCfgMemoryTermKey,
    offset_lo: i64,
    offset_hi: i64,
    exact_offset: bool,
    effect_count: usize,
}

fn summary_memory_location_expr(arg_index: usize, offset: i64) -> String {
    if offset == 0 {
        format!("*arg{arg_index}")
    } else if offset > 0 {
        format!("*(arg{arg_index} + 0x{:x})", offset as u64)
    } else {
        format!("*(arg{arg_index} - 0x{:x})", offset.unsigned_abs())
    }
}

fn summary_effect_expr(kind: SummaryMemoryEffectKind, arg_index: usize, offset: i64) -> String {
    let action = match kind {
        SummaryMemoryEffectKind::Read => "read",
        SummaryMemoryEffectKind::Write => "write",
        SummaryMemoryEffectKind::Escape => "escape",
        SummaryMemoryEffectKind::Free => "free",
    };
    format!(
        "{action} {}",
        summary_memory_location_expr(arg_index, offset)
    )
}

fn summary_effect_range_expr(
    kind: SummaryMemoryEffectKind,
    region: &BackwardMemoryRegion,
    offset_lo: i64,
    offset_hi: i64,
) -> String {
    if let BackwardMemoryRegion::Argument { index } = region
        && offset_lo == offset_hi
    {
        return summary_effect_expr(kind, *index, offset_lo);
    }
    let action = match kind {
        SummaryMemoryEffectKind::Read => "read",
        SummaryMemoryEffectKind::Write => "write",
        SummaryMemoryEffectKind::Escape => "escape",
        SummaryMemoryEffectKind::Free => "free",
    };
    let region = match region {
        BackwardMemoryRegion::Argument { index } => format!("arg{index}"),
        BackwardMemoryRegion::Region(region) => region.name.clone(),
    };
    format!("{action} {region}[{offset_lo}..{offset_hi}]")
}

fn summary_effect_binding(kind: SummaryMemoryEffectKind, region: &BackwardMemoryRegion) -> String {
    let action = match kind {
        SummaryMemoryEffectKind::Read => "read",
        SummaryMemoryEffectKind::Write => "write",
        SummaryMemoryEffectKind::Escape => "escape",
        SummaryMemoryEffectKind::Free => "free",
    };
    match region {
        BackwardMemoryRegion::Argument { index } => format!("{action}_arg{index}"),
        BackwardMemoryRegion::Region(region) => format!("{action}_{}", region.name),
    }
}

fn joined_large_cfg_memory_term_evidence(term: &JoinedLargeCfgMemoryTerm) -> SemanticEvidence {
    let widened = term.effect_count > 1 || term.offset_lo != term.offset_hi || !term.exact_offset;
    SemanticEvidence::likely(SemanticEvidenceReason::LargeCfg)
        .with_coverage(SemanticEvidenceCoverage::Bounded)
        .with_provenance(SemanticEvidenceProvenance::Stable)
        .with_ambiguity(if widened {
            SemanticEvidenceAmbiguity::Bounded
        } else {
            SemanticEvidenceAmbiguity::Single
        })
}

fn large_cfg_summary_memory_term_seed(
    effect: &SummaryMemoryEffect,
) -> Option<JoinedLargeCfgMemoryTerm> {
    let region = match effect.location.region {
        SummaryMemoryRegion::Arg { index } => BackwardMemoryRegion::Argument { index },
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => return None,
    };
    let (offset_lo, offset_hi, size, exact_offset) = effect
        .location
        .range
        .map(|range| {
            (
                range.offset_lo,
                range.offset_hi,
                range.width.unwrap_or(0),
                range.offset_lo == range.offset_hi,
            )
        })
        .unwrap_or((0, 0, 0, false));
    Some(JoinedLargeCfgMemoryTerm {
        key: JoinedLargeCfgMemoryTermKey {
            kind: effect.kind,
            region,
            size,
        },
        offset_lo,
        offset_hi,
        exact_offset,
        effect_count: 1,
    })
}

fn join_large_cfg_memory_term(
    left: &mut JoinedLargeCfgMemoryTerm,
    right: JoinedLargeCfgMemoryTerm,
) {
    let old_lo = left.offset_lo;
    let old_hi = left.offset_hi;
    left.offset_lo = left.offset_lo.min(right.offset_lo);
    left.offset_hi = left.offset_hi.max(right.offset_hi);
    left.exact_offset = left.exact_offset
        && right.exact_offset
        && old_lo == right.offset_lo
        && old_hi == right.offset_hi;
    left.effect_count += right.effect_count;
}

fn materialize_joined_large_cfg_memory_term(
    term: JoinedLargeCfgMemoryTerm,
) -> BackwardMemoryCondition {
    let address = if term.exact_offset {
        SemanticMemoryAddress::exact(term.offset_lo)
    } else {
        SemanticMemoryAddress::bounded(term.offset_lo, term.offset_hi)
            .expect("joined large-CFG memory bounds")
    };
    BackwardMemoryCondition {
        region: term.key.region.clone(),
        address,
        size: term.key.size,
        evidence: joined_large_cfg_memory_term_evidence(&term),
        binding: Some(summary_effect_binding(term.key.kind, &term.key.region)),
        expr: summary_effect_range_expr(
            term.key.kind,
            &term.key.region,
            term.offset_lo,
            term.offset_hi,
        ),
        value_expr: None,
        exact_value: false,
    }
}

fn joined_large_cfg_summary_memory_terms(
    effects: &[SummaryMemoryEffect],
) -> Vec<BackwardMemoryCondition> {
    let mut joined = BTreeMap::<JoinedLargeCfgMemoryTermKey, JoinedLargeCfgMemoryTerm>::new();
    for seed in effects
        .iter()
        .filter_map(large_cfg_summary_memory_term_seed)
    {
        if let Some(existing) = joined.get_mut(&seed.key) {
            join_large_cfg_memory_term(existing, seed);
        } else {
            joined.insert(seed.key.clone(), seed);
        }
    }
    joined
        .into_values()
        .map(materialize_joined_large_cfg_memory_term)
        .collect()
}

pub fn augment_semantic_artifact_with_interproc_summary(
    artifact: &mut SemanticArtifact,
    summaries: &PreparedInterprocSummarySet,
) -> usize {
    let prepared = artifact.shared_prepared();
    if !summaries.matches_root(&prepared) {
        return 0;
    }
    let Some(root) = summaries.report().root else {
        return 0;
    };
    if root != InterprocFunctionId(prepared.entry) {
        return 0;
    }
    let Some(summary) = summaries
        .report()
        .summaries
        .get(&root)
        .filter(|summary| summary.id == root)
    else {
        return 0;
    };
    let anchor = root.0;
    let SemanticArtifactBody::Native(native) = &artifact.report().body else {
        return 0;
    };

    let mut worker_summaries = native.summary.worker_summaries.clone();
    worker_summaries
        .extend(super::native_worker::summaries_from_interproc_summary_unbounded(anchor, summary));
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let worker_summaries_changed = worker_summaries != native.summary.worker_summaries;

    let terms = joined_large_cfg_summary_memory_terms(&summary.memory_effects);
    if !worker_summaries_changed && terms.is_empty() {
        return 0;
    }
    if !artifact.retain_interproc_provenance(summaries) {
        return 0;
    }
    let SemanticArtifactBody::Native(native) = &mut artifact.report_mut().body else {
        return 0;
    };
    if worker_summaries_changed {
        native.summary.worker_summaries = worker_summaries;
    }
    if terms.is_empty() {
        return 0;
    }

    let before = native
        .regions
        .values()
        .map(|region| region.memory.len())
        .sum::<usize>();
    let mut by_anchor = BTreeMap::<u64, SemanticRegion>::new();
    for region in std::mem::take(&mut native.regions).into_values() {
        by_anchor.insert(region.anchor, region);
    }
    let region = ensure_semantic_region(&mut by_anchor, anchor);
    push_region_memory_terms(region, terms);
    native.regions = by_anchor
        .into_values()
        .map(|region| (region.key(), region))
        .collect();
    let after = native
        .regions
        .values()
        .map(|region| region.memory.len())
        .sum::<usize>();
    after.saturating_sub(before)
}

fn control_fact_evidence(
    summary: Option<&BackwardConditionSummary>,
    condition: Option<&str>,
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> SemanticEvidence {
    let branch_budget_limited = diagnostics.skipped_large_cfg;
    match summary {
        Some(summary) => match summary.precision {
            BackwardConditionPrecision::Exact => summary.evidence(),
            BackwardConditionPrecision::OverApprox => summary
                .evidence()
                .with_budget_limited(branch_budget_limited)
                .with_reason(SemanticEvidenceReason::PartialPathCoverage),
            BackwardConditionPrecision::ResidualSearchRequired => {
                let simplified = summary.simplified.trim();
                let has_guard = !simplified.is_empty() && simplified != "true" && simplified != "1";
                if summary.supported_paths > 0
                    && has_guard
                    && summary.backward_memory_residual_fallbacks == 0
                {
                    SemanticEvidence::likely(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_provenance(SemanticEvidenceProvenance::Normalized)
                        .with_budget_limited(branch_budget_limited)
                        .with_reason(SemanticEvidenceReason::PartialPathCoverage)
                } else if summary.supported_paths > 0 && has_guard {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_provenance(SemanticEvidenceProvenance::Normalized)
                        .with_budget_limited(branch_budget_limited)
                } else if condition.is_some() {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_budget_limited(branch_budget_limited)
                } else {
                    SemanticEvidence::residual(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_budget_limited(branch_budget_limited)
                }
            }
            BackwardConditionPrecision::Unsupported => {
                if condition.is_some() {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_budget_limited(branch_budget_limited)
                } else {
                    SemanticEvidence::residual(SemanticEvidenceReason::ValueOpaque)
                        .with_budget_limited(branch_budget_limited)
                }
            }
        },
        None => condition
            .map(|_| {
                SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                    .with_coverage(SemanticEvidenceCoverage::Bounded)
                    .with_budget_limited(branch_budget_limited)
            })
            .unwrap_or_else(|| {
                SemanticEvidence::residual(SemanticEvidenceReason::GuardOpaque)
                    .with_budget_limited(branch_budget_limited)
            }),
    }
}

fn symbolic_condition_hint(summary: Option<&BackwardConditionSummary>) -> Option<String> {
    summary
        .map(|compiled| compiled.simplified.trim().to_string())
        .filter(|text| !text.is_empty() && text != "true")
}

/// Worklist steps a symbolic fact extraction may take.
///
/// This was 250 wall-clock milliseconds, which made the set of facts a
/// function proved depend on how busy the machine was.
const SYMBOLIC_FACT_MAX_STEPS: u64 = 2_500;

/// Whether branch reachability may fall back to a forward search from the
/// function entry when the compiled backward condition is not exact.
///
/// The search is the expensive half of semantic compilation: two explorations
/// per conditional branch, each popping up to 256 states for up to 2,500
/// steps, and every symbolic load inside a step builds fresh solvers over the
/// whole path condition and enumerates up to 256 concrete targets. On zlib's
/// `inflateStateCheck` -- eleven blocks, seven branches, walking
/// `strm->state->strm` -- that did not finish in fifteen minutes.
///
/// What the search produces is a `Reachable`/`Unreachable` status per branch
/// target. Every consumer of that status was traced: it feeds control claims,
/// which gate only the worker, VM and structuring routes -- the ones a large
/// or dispatch-shaped CFG takes. Types come from the interprocedural summary
/// and from the backward compiler's memory terms, both computed before the
/// search. The plain native route reads none of it. Measured on the corpus:
/// with the search disabled, zero of fifty-four rendered files changed.
///
/// So the search runs where a consumer exists and nowhere else. Where it is
/// skipped and the backward condition is not exact, the status is `Unknown`,
/// which is what it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForwardSearch {
    /// Explore forward when the backward condition cannot decide.
    Run,
    /// Report `Unknown` instead; no route on this path reads the answer.
    Skip,
}

fn symbolic_fact_explorer<'ctx>(
    ctx: &'ctx Context,
    execution: &SymExecutionControl,
) -> PathExplorer<'ctx> {
    let mut explorer = PathExplorer::with_config_and_execution_control(
        ctx,
        ExploreConfig {
            subsumption_states: true,
            max_states: 256,
            max_depth: 96,
            max_completed_paths: Some(8),
            max_steps: Some(SYMBOLIC_FACT_MAX_STEPS),
            merge_states: false,
            ..ExploreConfig::default()
        },
        execution.clone(),
    );
    explorer.set_target_guided_queries(true);
    explorer
}

fn collect_branch_blocks(func: &SsaArtifact) -> Vec<(u64, u64, u64)> {
    func.cfg()
        .block_addrs()
        .filter_map(|block_addr| {
            let block = func.cfg().get_block(block_addr)?;
            match block.terminator {
                r2ssa::BlockTerminator::ConditionalBranch {
                    true_target,
                    false_target,
                } => Some((block_addr, true_target, false_target)),
                _ => None,
            }
        })
        .collect()
}

fn large_cfg_branch_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    match summary.switch_block_count {
        0 => 8,
        1..=2 => 10,
        _ => 12,
    }
}

fn limited_branch_blocks(func: &SsaArtifact, limit: usize) -> Vec<(u64, u64, u64)> {
    if limit == 0 {
        return Vec::new();
    }

    let mut queue = VecDeque::from([func.entry]);
    let mut visited = BTreeSet::new();
    let mut selected = Vec::new();

    while let Some(block_addr) = queue.pop_front() {
        if !visited.insert(block_addr) {
            continue;
        }

        if let Some(block) = func.cfg().get_block(block_addr)
            && let r2ssa::BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } = block.terminator
        {
            selected.push((block_addr, true_target, false_target));
            if selected.len() >= limit {
                break;
            }
        }

        for successor in func.successors(block_addr) {
            if !visited.contains(&successor) {
                queue.push_back(successor);
            }
        }
    }

    if selected.is_empty() {
        collect_branch_blocks(func)
            .into_iter()
            .take(limit)
            .collect()
    } else {
        selected
    }
}

fn symbolic_reachability_status(
    feasible_paths: usize,
    budget_exhausted: bool,
) -> SymbolicReachabilityStatus {
    if feasible_paths > 0 {
        SymbolicReachabilityStatus::Reachable
    } else if budget_exhausted {
        SymbolicReachabilityStatus::Unknown
    } else {
        SymbolicReachabilityStatus::Unreachable
    }
}

fn collect_branch_observations_for_branch_blocks<'ctx, F>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    arch: &ArchSpec,
    branch_blocks: &[(u64, u64, u64)],
    forward_search: ForwardSearch,
    execution: &SymExecutionControl,
    install_hooks: F,
) -> (Vec<BranchObservation>, SymbolicFunctionFactDiagnostics)
where
    F: Fn(&mut PathExplorer<'ctx>),
{
    let skip_forward = matches!(forward_search, ForwardSearch::Skip);
    let mut branch_facts = Vec::new();
    let mut diagnostics = SymbolicFunctionFactDiagnostics::default();
    for &(block_addr, true_target, false_target) in branch_blocks {
        diagnostics.branches_evaluated += 1;
        let predicate_uses_call_result = predicate_depends_on_call_result(func, block_addr);

        let make_state = || {
            let mut state = SymState::new_symbolic(ctx, func.entry);
            if func.provenance_kind() == r2ssa::SsaArtifactProvenanceKind::Manual {
                seed_default_state_for_arch(&mut state, func, Some(arch));
            } else {
                let _ = seed_default_state_for_prepared(&mut state, func);
            }
            state
        };

        let mut true_explorer = symbolic_fact_explorer(ctx, execution);
        install_hooks(&mut true_explorer);
        let true_initial_state = make_state();
        let ((compiled_true_status, true_compiled), (compiled_false_status, false_compiled)) =
            compiled_branch_reachability_statuses(
                &true_explorer,
                func,
                &true_initial_state,
                block_addr,
            );
        let true_condition = symbolic_condition_hint(true_compiled.as_ref());
        let true_status = if let Some(status) = compiled_true_status {
            status
        } else if skip_forward || predicate_uses_call_result || func_contains_calls(func) {
            SymbolicReachabilityStatus::Unknown
        } else {
            let paths = true_explorer.find_paths_to(func, make_state(), true_target);
            symbolic_reachability_status(paths.len(), true_explorer.budget_exhausted())
        };

        let false_condition = symbolic_condition_hint(false_compiled.as_ref());
        let false_status = if let Some(status) = compiled_false_status {
            status
        } else if skip_forward || predicate_uses_call_result || func_contains_calls(func) {
            SymbolicReachabilityStatus::Unknown
        } else {
            let mut false_explorer = symbolic_fact_explorer(ctx, execution);
            install_hooks(&mut false_explorer);
            let paths = false_explorer.find_paths_to(func, make_state(), false_target);
            symbolic_reachability_status(paths.len(), false_explorer.budget_exhausted())
        };

        if matches!(true_status, SymbolicReachabilityStatus::Unknown)
            || matches!(false_status, SymbolicReachabilityStatus::Unknown)
        {
            diagnostics.branches_unknown += 1;
        }
        if matches!(
            (true_status, false_status),
            (
                SymbolicReachabilityStatus::Reachable,
                SymbolicReachabilityStatus::Unreachable
            ) | (
                SymbolicReachabilityStatus::Unreachable,
                SymbolicReachabilityStatus::Reachable
            )
        ) {
            diagnostics.branches_pruned += 1;
        }

        branch_facts.push(BranchObservation {
            block_addr,
            true_target,
            false_target,
            true_status,
            false_status,
            true_condition,
            false_condition,
            true_compiled,
            false_compiled,
        });
    }

    (branch_facts, diagnostics)
}

fn install_symbolic_fact_hooks<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    arch: &ArchSpec,
    summary_profile: SummaryProfile,
    symbol_map: &HashMap<u64, String>,
) {
    let Some(registry) =
        SummaryRegistry::with_profile_for_arch_and_symbols(arch, symbol_map, summary_profile)
    else {
        return;
    };
    let _ = registry.install_known_symbols_for_function(explorer, func, symbol_map);
}

type CompiledReachability = (
    Option<SymbolicReachabilityStatus>,
    Option<BackwardConditionSummary>,
);

fn compiled_branch_reachability_statuses<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    block_addr: u64,
) -> (CompiledReachability, CompiledReachability) {
    if func_contains_calls(func) {
        return ((None, None), (None, None));
    }
    let Some((true_compiled, false_compiled)) =
        compile_branch_preconditions(func, initial_state, block_addr)
    else {
        return ((None, None), (None, None));
    };
    let evaluate = |compiled: crate::backward::CompiledBackwardCondition| {
        let status = if matches!(
            compiled.summary.precision,
            BackwardConditionPrecision::Exact
        ) {
            match explorer
                .solver()
                .sat_with_constraint(initial_state, &compiled.predicate)
            {
                SatResult::Sat => Some(SymbolicReachabilityStatus::Reachable),
                SatResult::Unsat => Some(SymbolicReachabilityStatus::Unreachable),
                SatResult::Unknown => None,
            }
        } else {
            None
        };
        (status, Some(compiled.summary))
    };
    (evaluate(true_compiled), evaluate(false_compiled))
}

fn func_contains_calls(func: &SsaArtifact) -> bool {
    func.blocks().any(|block| {
        block
            .ops
            .iter()
            .any(|op| matches!(op, r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. }))
    })
}

fn local_memory_store_value_ids(
    func: &SsaArtifact,
    inst_id: r2ssa::graph::InstId,
    size: u32,
) -> Vec<r2ssa::graph::ValueId> {
    let Some(uses) = func.memory().uses_by_inst.get(&inst_id) else {
        return Vec::new();
    };
    let mut values = Vec::new();
    for use_fact in uses {
        if use_fact.location.size != size {
            continue;
        }
        for (def_inst, defs) in &func.memory().defs_by_inst {
            for def in defs {
                if def.next_version != use_fact.version || def.location != use_fact.location {
                    continue;
                }
                let Some(inst) = func.graph().inst(*def_inst) else {
                    continue;
                };
                let r2ssa::graph::InstPayload::Op(r2ssa::SSAOp::Store { val, .. }) = &inst.payload
                else {
                    continue;
                };
                if let Some(value_id) = func.graph().value_id_for_var(val) {
                    values.push(value_id);
                }
            }
        }
    }
    values
}

fn value_depends_on_call_result(
    func: &SsaArtifact,
    value_id: r2ssa::graph::ValueId,
    visited: &mut BTreeSet<r2ssa::graph::ValueId>,
) -> bool {
    if !visited.insert(value_id) {
        return false;
    }

    let Some(inst_id) = func.graph().def_inst(value_id) else {
        return false;
    };
    let Some(inst) = func.graph().inst(inst_id) else {
        return false;
    };

    match &inst.payload {
        r2ssa::graph::InstPayload::Phi { .. } => inst
            .inputs
            .iter()
            .copied()
            .any(|input| value_depends_on_call_result(func, input, visited)),
        r2ssa::graph::InstPayload::Op(op) => match op {
            r2ssa::SSAOp::CallDefine { .. } => true,
            r2ssa::SSAOp::Load { dst, .. } => local_memory_store_value_ids(func, inst_id, dst.size)
                .into_iter()
                .any(|stored| value_depends_on_call_result(func, stored, visited)),
            _ => inst
                .inputs
                .iter()
                .copied()
                .any(|input| value_depends_on_call_result(func, input, visited)),
        },
    }
}

fn predicate_depends_on_call_result(func: &SsaArtifact, block_addr: u64) -> bool {
    let Some(predicate) = func
        .predicates()
        .predicates
        .values()
        .find(|fact| fact.block_addr == block_addr)
    else {
        return false;
    };
    let mut visited = BTreeSet::new();
    value_depends_on_call_result(func, predicate.condition, &mut visited)
}

pub(super) fn collect_large_cfg_canonical_semantic_regions_with_limit(
    ctx: &Context,
    func: &SsaArtifact,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    branch_limit: usize,
    execution: &SymExecutionControl,
) -> CollectedNativeSemanticRegions {
    let mut collected = if branch_limit == 0 {
        CollectedNativeSemanticRegions {
            regions: BTreeMap::new(),
            diagnostics: SymbolicFunctionFactDiagnostics {
                skipped_large_cfg: true,
                ..SymbolicFunctionFactDiagnostics::default()
            },
            region_summaries: Vec::new(),
            worker_summaries: Vec::new(),
        }
    } else {
        let branch_blocks = limited_branch_blocks(func, branch_limit);
        // This is the collection the worker, summary-island and structuring
        // routes read their control claims from, so the forward search has a
        // consumer here and runs, bounded by `branch_limit`.
        let (branch_facts, diagnostics) = collect_branch_observations_for_branch_blocks(
            ctx,
            func,
            arch,
            &branch_blocks,
            ForwardSearch::Run,
            execution,
            |explorer| {
                install_symbolic_fact_hooks(explorer, func, arch, summary_profile, symbol_map);
            },
        );
        CollectedNativeSemanticRegions {
            regions: build_canonical_regions(&branch_facts, &BTreeMap::new(), &diagnostics),
            diagnostics,
            region_summaries: Vec::new(),
            worker_summaries: Vec::new(),
        }
    };
    let mut canonical_worker_domain = Vec::new();
    // Interprocedural memory terms are authority-bearing and may only enter
    // through `augment_semantic_artifact_with_interproc_summary`, which checks
    // a retained `PreparedInterprocSummarySet` against the exact artifact.
    // This ownerless collection path remains residual for those terms.
    canonical_worker_domain.extend(append_large_cfg_memory_transfer_terms(
        func,
        &mut collected.regions,
    ));
    canonical_worker_domain
        .extend(super::native_worker::classify_function_worker_summaries_unbounded(func));
    collected.region_summaries =
        super::native_worker::classify_native_region_summaries(func, &canonical_worker_domain);
    collected.worker_summaries =
        super::native_worker::bounded_worker_summaries(canonical_worker_domain);
    collected.diagnostics.skipped_large_cfg = true;
    collected
}

pub(super) fn collect_canonical_semantic_regions_with_profile(
    ctx: &Context,
    func: &SsaArtifact,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    execution: &SymExecutionControl,
) -> CollectedNativeSemanticRegions {
    let Some(arch) = arch else {
        return CollectedNativeSemanticRegions {
            regions: BTreeMap::new(),
            diagnostics: SymbolicFunctionFactDiagnostics {
                skipped_missing_arch: true,
                ..SymbolicFunctionFactDiagnostics::default()
            },
            region_summaries: Vec::new(),
            worker_summaries: Vec::new(),
        };
    };

    let cfg_summary = func.function().cfg_risk_summary();
    let branch_count = func.predicates().predicates.len();
    if cfg_summary.block_count > 96 || branch_count > 96 || cfg_summary.switch_block_count > 8 {
        return collect_large_cfg_canonical_semantic_regions_with_limit(
            ctx,
            func,
            arch,
            symbol_map,
            summary_profile,
            large_cfg_branch_limit(func),
            execution,
        );
    }

    let branch_blocks = collect_branch_blocks(func);
    // A function on this path -- a CFG under the large-CFG thresholds with no
    // dispatch evidence -- can only take the plain native route, and that route
    // reads no reachability status. The backward compiler still answers every
    // branch it can decide exactly; the rest are `Unknown`.
    let (branch_facts, diagnostics) = collect_branch_observations_for_branch_blocks(
        ctx,
        func,
        arch,
        &branch_blocks,
        ForwardSearch::Skip,
        execution,
        |explorer| {
            install_symbolic_fact_hooks(explorer, func, arch, summary_profile, symbol_map);
        },
    );
    CollectedNativeSemanticRegions {
        regions: build_canonical_regions(&branch_facts, &BTreeMap::new(), &diagnostics),
        diagnostics,
        region_summaries: Vec::new(),
        worker_summaries: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::{
        ArtifactGranularity, ExecutionModel, NativeArtifactBody, NativeFunctionSummary,
        NativeWorkerSummaryKind, RefinementStage, SemanticArtifactDiagnostics,
        SemanticArtifactReport,
    };
    use r2il::{R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, InterprocSolveConfig, SourceAbiParameterSpec,
        SourceFunctionInterface, SourceFunctionReturn,
    };

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn exact_affine_aarch64_fixture() -> (ArchSpec, SourceFunctionInterface) {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("x1", 0x08, 8));
        arch.add_register(RegisterDef::sub("w1", 0x08, 4, "x1"));
        arch.add_register(RegisterDef::new("sp", 0x10, 8));
        arch.add_register(RegisterDef::new("lr", 0x18, 8));
        let interface = SourceFunctionInterface::new_exact(
            b"affine-memory-evidence-v1".to_vec(),
            "aarch64",
            [
                SourceAbiParameterSpec::new(0, register_storage(0x00, 8)),
                SourceAbiParameterSpec::new(1, register_storage(0x08, 8)),
            ],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(0x18, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0x10, 8)))
        .expect("coherent affine memory interface");
        (arch, interface)
    }

    #[test]
    fn disjoint_parameter_store_preserves_exact_branch_input() {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        let interface = SourceFunctionInterface::new_exact(
            b"disjoint-parameter-store-v1".to_vec(),
            "aarch64",
            [SourceAbiParameterSpec::new(0, register_storage(0x00, 8))],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("exact untyped x0 parameter interface");

        let mut branch = r2il::R2ILBlock::new(0x1000, 4);
        branch.push(r2il::R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
            val: Varnode::constant(0, 4),
        });
        branch.push(r2il::R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0x00, 8),
            b: Varnode::constant(4, 8),
        });
        branch.push(r2il::R2ILOp::Load {
            dst: Varnode::unique(0x20, 1),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        branch.push(r2il::R2ILOp::IntEqual {
            dst: Varnode::unique(0x30, 1),
            a: Varnode::unique(0x20, 1),
            b: Varnode::constant(0x41, 1),
        });
        branch.push(r2il::R2ILOp::CBranch {
            target: Varnode::constant(0x1010, 8),
            cond: Varnode::unique(0x30, 1),
        });
        let mut false_exit = r2il::R2ILBlock::new(0x1004, 4);
        false_exit.push(r2il::R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut true_exit = r2il::R2ILBlock::new(0x1010, 4);
        true_exit.push(r2il::R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });
        let artifact = SsaArtifact::for_symbolic_with_interface(
            &[branch, false_exit, true_exit],
            Some(&arch),
            interface,
        )
        .expect("memory branch fixture should build SSA");
        let ctx = Context::thread_local();

        let (observations, diagnostics) = collect_branch_observations_for_branch_blocks(
            &ctx,
            &artifact,
            &arch,
            &[(0x1000, 0x1010, 0x1004)],
            ForwardSearch::Run,
            &SymExecutionControl::default(),
            |_| {},
        );

        assert_eq!(observations.len(), 1);
        assert_eq!(
            observations[0].true_status,
            SymbolicReachabilityStatus::Reachable
        );
        assert_eq!(
            observations[0].false_status,
            SymbolicReachabilityStatus::Reachable
        );
        assert_eq!(diagnostics.branches_pruned, 0);
        assert_eq!(diagnostics.branches_unknown, 0);
        assert!(matches!(
            observations[0]
                .true_compiled
                .as_ref()
                .map(|compiled| compiled.precision),
            Some(BackwardConditionPrecision::Exact)
        ));
        let memory_terms = &observations[0]
            .true_compiled
            .as_ref()
            .expect("compiled branch")
            .memory_terms;
        assert_eq!(memory_terms.len(), 1);
        assert!(matches!(
            memory_terms[0].region,
            crate::BackwardMemoryRegion::Argument { index: 0 }
        ));
        assert_eq!(memory_terms[0].address.offset_lo(), 4);
        assert_eq!(memory_terms[0].address.offset_hi(), 4);
        assert!(memory_terms[0].address.is_exact_offset());
    }

    #[test]
    fn branch_through_a_loaded_pointer_compiles_exactly_on_a_pointee_region() {
        // `if (*(*(x0 + 0x38) + 0) == 0x41)`: the pointer is loaded from the
        // parameter's memory and dereferenced again. Before pointee objects
        // existed the second load had no structural location, the backward
        // condition was ResidualSearchRequired, and only a forward search
        // could answer -- fifteen minutes on zlib's inflateStateCheck.
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        let interface = SourceFunctionInterface::new_exact(
            b"pointee-branch-v1".to_vec(),
            "aarch64",
            [SourceAbiParameterSpec::new(0, register_storage(0x00, 8))],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("exact untyped x0 parameter interface");

        let mut branch = r2il::R2ILBlock::new(0x1000, 4);
        branch.push(r2il::R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0x00, 8),
            b: Varnode::constant(0x38, 8),
        });
        branch.push(r2il::R2ILOp::Load {
            dst: Varnode::unique(0x20, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        branch.push(r2il::R2ILOp::Load {
            dst: Varnode::unique(0x30, 1),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x20, 8),
        });
        branch.push(r2il::R2ILOp::IntEqual {
            dst: Varnode::unique(0x40, 1),
            a: Varnode::unique(0x30, 1),
            b: Varnode::constant(0x41, 1),
        });
        branch.push(r2il::R2ILOp::CBranch {
            target: Varnode::constant(0x1010, 8),
            cond: Varnode::unique(0x40, 1),
        });
        let mut false_exit = r2il::R2ILBlock::new(0x1004, 4);
        false_exit.push(r2il::R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut true_exit = r2il::R2ILBlock::new(0x1010, 4);
        true_exit.push(r2il::R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });
        let artifact = SsaArtifact::for_symbolic_with_interface(
            &[branch, false_exit, true_exit],
            Some(&arch),
            interface,
        )
        .expect("pointee branch fixture should build SSA");
        let ctx = Context::thread_local();

        let (observations, diagnostics) = collect_branch_observations_for_branch_blocks(
            &ctx,
            &artifact,
            &arch,
            &[(0x1000, 0x1010, 0x1004)],
            ForwardSearch::Skip,
            &SymExecutionControl::default(),
            |_| {},
        );

        assert_eq!(observations.len(), 1);
        assert_eq!(diagnostics.branches_unknown, 0, "{observations:#?}");
        let compiled = observations[0]
            .true_compiled
            .as_ref()
            .expect("compiled pointee branch");
        assert_eq!(
            compiled.precision,
            BackwardConditionPrecision::Exact,
            "{compiled:#?}"
        );
        assert_eq!(compiled.backward_memory_residual_fallbacks, 0);
        let pointee = compiled
            .memory_terms
            .iter()
            .find(|term| {
                matches!(
                    &term.region,
                    crate::BackwardMemoryRegion::Region(region)
                        if region.kind == crate::MemoryRegionKind::Pointee
                )
            })
            .expect("a memory term on the pointee region");
        let crate::BackwardMemoryRegion::Region(region) = &pointee.region else {
            unreachable!();
        };
        assert_eq!(region.root_parameter, Some(0));
        assert_eq!(region.name, "*(arg0 + 0x38)");
        assert_eq!(pointee.address.offset_lo(), 0);
        assert!(pointee.address.is_exact_offset());
    }

    #[test]
    fn disjoint_affine_parameter_store_preserves_exact_branch_input() {
        let (arch, interface) = exact_affine_aarch64_fixture();

        let mut branch = r2il::R2ILBlock::new(0x1000, 4);
        branch.push(r2il::R2ILOp::IntSub {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        branch.push(r2il::R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
            val: Varnode::register(0x00, 8),
        });
        branch.push(r2il::R2ILOp::Load {
            dst: Varnode::unique(0x20, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        branch.push(r2il::R2ILOp::IntSExt {
            dst: Varnode::unique(0x30, 8),
            src: Varnode::register(0x08, 4),
        });
        branch.push(r2il::R2ILOp::IntMult {
            dst: Varnode::unique(0x40, 8),
            a: Varnode::unique(0x30, 8),
            b: Varnode::constant(40, 8),
        });
        branch.push(r2il::R2ILOp::IntAdd {
            dst: Varnode::unique(0x50, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::unique(0x40, 8),
        });
        branch.push(r2il::R2ILOp::IntAdd {
            dst: Varnode::unique(0x60, 8),
            a: Varnode::unique(0x50, 8),
            b: Varnode::constant(16, 8),
        });
        branch.push(r2il::R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x60, 8),
            val: Varnode::constant(0, 4),
        });
        branch.push(r2il::R2ILOp::IntAdd {
            dst: Varnode::unique(0x70, 8),
            a: Varnode::unique(0x50, 8),
            b: Varnode::constant(4, 8),
        });
        branch.push(r2il::R2ILOp::Load {
            dst: Varnode::unique(0x80, 2),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x70, 8),
        });
        branch.push(r2il::R2ILOp::IntEqual {
            dst: Varnode::unique(0x90, 1),
            a: Varnode::unique(0x80, 2),
            b: Varnode::constant(0x4241, 2),
        });
        branch.push(r2il::R2ILOp::CBranch {
            target: Varnode::constant(0x1010, 8),
            cond: Varnode::unique(0x90, 1),
        });
        let mut false_exit = r2il::R2ILBlock::new(0x1004, 4);
        false_exit.push(r2il::R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut true_exit = r2il::R2ILBlock::new(0x1010, 4);
        true_exit.push(r2il::R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });
        let artifact = SsaArtifact::for_decompile_with_interface(
            &[branch, false_exit, true_exit],
            Some(&arch),
            interface,
        )
        .expect("affine memory branch fixture should build SSA");
        assert_eq!(
            artifact.provenance_kind(),
            r2ssa::SsaArtifactProvenanceKind::Manual
        );
        let ctx = Context::thread_local();

        let (observations, diagnostics) = collect_branch_observations_for_branch_blocks(
            &ctx,
            &artifact,
            &arch,
            &[(0x1000, 0x1010, 0x1004)],
            ForwardSearch::Run,
            &SymExecutionControl::default(),
            |_| {},
        );

        assert_eq!(observations.len(), 1);
        assert_eq!(diagnostics.branches_unknown, 0);
        let compiled = observations[0]
            .true_compiled
            .as_ref()
            .expect("compiled affine branch");
        assert_eq!(
            compiled.precision,
            BackwardConditionPrecision::Exact,
            "{compiled:#?}"
        );
        assert_eq!(compiled.backward_memory_residual_fallbacks, 0);
        assert_eq!(compiled.memory_terms.len(), 1);
        let term = &compiled.memory_terms[0];
        assert!(matches!(
            term.region,
            crate::BackwardMemoryRegion::Argument { index: 0 }
        ));
        assert_eq!((term.address.offset_lo(), term.address.offset_hi()), (4, 4));
        assert!(!term.address.is_exact_offset());
        assert!(term.has_exact_address());
        assert_eq!(term.address.terms().len(), 1);
        assert_eq!(term.address.terms()[0].coefficient, 40);
    }

    #[test]
    fn large_cfg_memory_transfer_pass_detects_copy_shaped_store() {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("x1", 0x08, 8));

        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::Load {
            dst: Varnode::unique(0, 1),
            space: SpaceId::Ram,
            addr: Varnode::register(0x08, 8),
        });
        block.push(r2il::R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
            val: Varnode::unique(0, 1),
        });

        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch))
            .expect("copy-shaped fixture should build SSA");
        let transfers = crate::semantics::native_worker::large_cfg_memory_transfers(&artifact);

        assert!(
            transfers.contains(&crate::semantics::native_worker::LargeCfgMemoryTransfer {
                block_addr: 0x1000,
                dst_arg: 0,
                src_arg: 1,
                size: 1,
            })
        );
    }

    #[test]
    fn large_cfg_memory_transfer_pass_tracks_pointer_and_value_plumbing() {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("x1", 0x08, 8));

        let src_addr = Varnode::unique(0x10, 8);
        let dst_addr = Varnode::unique(0x11, 8);
        let loaded = Varnode::unique(0x12, 1);
        let widened = Varnode::unique(0x13, 8);
        let casted = Varnode::unique(0x14, 8);

        let mut block = r2il::R2ILBlock::new(0x1010, 4);
        block.push(r2il::R2ILOp::PtrAdd {
            dst: src_addr.clone(),
            base: Varnode::register(0x08, 8),
            index: Varnode::constant(4, 8),
            element_size: 1,
        });
        block.push(r2il::R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: src_addr,
        });
        block.push(r2il::R2ILOp::IntZExt {
            dst: widened.clone(),
            src: loaded,
        });
        block.push(r2il::R2ILOp::Cast {
            dst: casted.clone(),
            src: widened,
        });
        block.push(r2il::R2ILOp::PtrAdd {
            dst: dst_addr.clone(),
            base: Varnode::register(0x00, 8),
            index: Varnode::constant(8, 8),
            element_size: 1,
        });
        block.push(r2il::R2ILOp::Store {
            space: SpaceId::Ram,
            addr: dst_addr,
            val: casted,
        });

        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch))
            .expect("plumbed copy-shaped fixture should build SSA");
        let transfers = crate::semantics::native_worker::large_cfg_memory_transfers(&artifact);

        assert!(
            transfers.contains(&crate::semantics::native_worker::LargeCfgMemoryTransfer {
                block_addr: 0x1010,
                dst_arg: 0,
                src_arg: 1,
                size: 8,
            })
        );
    }

    #[test]
    fn large_cfg_summary_join_preserves_distinct_memory_effect_classes() {
        let mut effects = (0..48)
            .map(|index| SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: r2ssa::SummaryMemoryLocation {
                    region: SummaryMemoryRegion::Arg { index: 0 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: index * 8,
                        offset_hi: index * 8 + 7,
                        width: Some(8),
                    }),
                },
            })
            .collect::<Vec<_>>();
        effects.push(SummaryMemoryEffect {
            kind: SummaryMemoryEffectKind::Write,
            location: r2ssa::SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: 1 },
                range: Some(r2ssa::SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 7,
                    width: Some(8),
                }),
            },
        });

        let terms = joined_large_cfg_summary_memory_terms(&effects);

        assert_eq!(terms.len(), 2);
        assert!(terms.iter().any(|term| {
            term.binding.as_deref() == Some("read_arg0")
                && matches!(term.region, BackwardMemoryRegion::Argument { index: 0 })
                && term.address.offset_lo() == 0
                && term.address.offset_hi() == 383
                && !term.address.is_exact_offset()
                && !term.evidence().budget_limited
        }));
        assert!(terms.iter().any(|term| {
            term.binding.as_deref() == Some("write_arg1")
                && matches!(term.region, BackwardMemoryRegion::Argument { index: 1 })
        }));
    }

    #[test]
    fn large_cfg_summary_join_keeps_distinct_args_beyond_old_count_cap() {
        let effects = (0..40)
            .map(|index| SummaryMemoryEffect {
                kind: SummaryMemoryEffectKind::Read,
                location: r2ssa::SummaryMemoryLocation {
                    region: SummaryMemoryRegion::Arg { index },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 0,
                        offset_hi: 7,
                        width: Some(8),
                    }),
                },
            })
            .collect::<Vec<_>>();

        let terms = joined_large_cfg_summary_memory_terms(&effects);

        assert_eq!(terms.len(), 40);
        assert!(terms.iter().any(|term| {
            term.binding.as_deref() == Some("read_arg39")
                && matches!(term.region, BackwardMemoryRegion::Argument { index: 39 })
        }));
    }

    #[test]
    fn interproc_summary_augmentation_adds_native_memory_terms() {
        let root = InterprocFunctionId(0x3000);
        let (arch, interface) = exact_affine_aarch64_fixture();
        let mut block = R2ILBlock::new(0x3000, 1);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
            val: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let prepared = Arc::new(
            SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("source summary SSA"),
        );
        let summaries = r2ssa::solve_prepared_interproc_summary_set(
            Arc::clone(&prepared),
            &[r2ssa::PreparedInterprocFunctionInput {
                id: root,
                name: Some("sym.copy_worker".to_string()),
                prepared: &prepared,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("prepared summary");
        let root_summary = summaries
            .report()
            .summaries
            .get(&root)
            .expect("root summary");
        assert!(root_summary.has_unknown_calls);
        assert_eq!(
            root_summary.return_relation,
            r2ssa::SummaryReturnRelation::Unknown
        );
        let mut artifact = SemanticArtifact::new(
            prepared,
            SemanticArtifactReport {
                schema_version: crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
                stage: RefinementStage::Residual,
                granularity: ArtifactGranularity::SummaryOnly,
                execution: ExecutionModel::Native,
                body: SemanticArtifactBody::Native(NativeArtifactBody {
                    summary: NativeFunctionSummary {
                        slice_class: crate::SliceClass::Worker,
                        role_identity: None,
                        closure_functions: 1,
                        helper_functions: 0,
                        region_summaries: Vec::new(),
                        worker_summaries: Vec::new(),
                    },
                    regions: BTreeMap::new(),
                }),
                diagnostics: SemanticArtifactDiagnostics {
                    branches_evaluated: 0,
                    branches_pruned: 0,
                    branches_unknown: 0,
                    skipped_missing_arch: false,
                    skipped_large_cfg: true,
                    residual_reasons: vec![crate::ResidualReason::LargeCfg],
                    interpreter: None,
                    ambiguous_targets: Vec::new(),
                },
            },
        )
        .expect("current semantic facts schema");

        let added = augment_semantic_artifact_with_interproc_summary(&mut artifact, &summaries);

        assert_eq!(added, 7);
        assert!(!artifact.has_helper_provenance());
        let native = artifact.native_body().expect("native semantic body");
        assert!(native.summary.worker_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MemoryWrite)
                && summary.out_param_indices().contains(&0)
        }));
        let region = native.regions.values().next().expect("summary region");
        assert!(region.memory.iter().any(|term| {
            term.value.term.binding.as_deref() == Some("write_arg0")
                && matches!(
                    term.value.term.region,
                    BackwardMemoryRegion::Argument { index: 0 }
                )
        }));
    }

    #[test]
    fn interproc_summary_augmentation_rejects_foreign_rebuilt_owner() {
        let (arch, interface) = exact_affine_aarch64_fixture();
        let mut block = R2ILBlock::new(0x3000, 1);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
            val: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let requested = Arc::new(
            SsaArtifact::for_decompile_with_interface(
                std::slice::from_ref(&block),
                Some(&arch),
                interface.clone(),
            )
            .expect("requested SSA"),
        );
        let foreign = Arc::new(
            SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("foreign rebuilt SSA"),
        );
        let summaries = r2ssa::solve_prepared_interproc_summary_set(
            Arc::clone(&foreign),
            &[r2ssa::PreparedInterprocFunctionInput {
                id: InterprocFunctionId(foreign.entry),
                name: None,
                prepared: &foreign,
            }],
            InterprocSolveConfig::default(),
        )
        .expect("foreign prepared summary");
        let mut artifact = SemanticArtifact::new(
            requested,
            SemanticArtifactReport {
                schema_version: crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
                stage: RefinementStage::Residual,
                granularity: ArtifactGranularity::SummaryOnly,
                execution: ExecutionModel::Native,
                body: SemanticArtifactBody::Native(NativeArtifactBody {
                    summary: NativeFunctionSummary {
                        slice_class: crate::SliceClass::Worker,
                        role_identity: None,
                        closure_functions: 1,
                        helper_functions: 0,
                        region_summaries: Vec::new(),
                        worker_summaries: Vec::new(),
                    },
                    regions: BTreeMap::new(),
                }),
                diagnostics: SemanticArtifactDiagnostics {
                    branches_evaluated: 0,
                    branches_pruned: 0,
                    branches_unknown: 0,
                    skipped_missing_arch: false,
                    skipped_large_cfg: true,
                    residual_reasons: vec![crate::ResidualReason::LargeCfg],
                    interpreter: None,
                    ambiguous_targets: Vec::new(),
                },
            },
        )
        .expect("current semantic facts schema");
        let before = artifact.report().clone();

        assert_eq!(
            augment_semantic_artifact_with_interproc_summary(&mut artifact, &summaries),
            0
        );
        assert_eq!(artifact.report(), &before);
        assert!(!artifact.has_helper_provenance());
    }
}
