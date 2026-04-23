use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use r2il::ArchSpec;
use r2ssa::{InterprocFunctionId, SsaArtifact};
use serde::{Deserialize, Serialize};
use z3::Context;

use crate::SymState;
use crate::backward::{
    BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
    compile_branch_precondition_with_summaries,
};
use crate::path::{ExploreConfig, PathExplorer};
use crate::runtime::seed_default_state_for_arch;
use crate::semantics::{
    SemanticEvidence, SemanticEvidenceCoverage, SemanticEvidenceProvenance, SemanticEvidenceReason,
};
use crate::sim::{
    DerivedSummaryCompletion, DerivedSummarySet, PreparedFunctionScope, SummaryProfile,
    SummaryRegistry,
};
use crate::solver::SatResult;

use super::region::{ControlFact, Judged, MemoryFact, RegionKey, SemanticRegion, TargetFact};

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

fn derived_summary_memory_term_evidence(
    completion: DerivedSummaryCompletion,
    exact_value: bool,
) -> SemanticEvidence {
    match completion {
        DerivedSummaryCompletion::Exact if exact_value => SemanticEvidence::exact(),
        DerivedSummaryCompletion::Exact => SemanticEvidence::exact(),
        DerivedSummaryCompletion::OverApprox => {
            SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
        }
        DerivedSummaryCompletion::BudgetExhausted => {
            SemanticEvidence::heuristic(SemanticEvidenceReason::SummaryBudget)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
                .with_budget_limited(true)
        }
        DerivedSummaryCompletion::Unknown => {
            SemanticEvidence::heuristic(SemanticEvidenceReason::ValueOpaque)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
        }
    }
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

fn derive_summary_memory_terms_by_anchor<'ctx>(
    func: &SsaArtifact,
    branch_blocks: &[(u64, u64, u64)],
    derived: &DerivedSummarySet<'ctx>,
) -> BTreeMap<u64, Vec<BackwardMemoryCondition>> {
    let hot_blocks = branch_blocks
        .iter()
        .flat_map(|(block, true_target, false_target)| [*block, *true_target, *false_target])
        .collect::<BTreeSet<_>>();
    let mut by_anchor = BTreeMap::<u64, Vec<BackwardMemoryCondition>>::new();
    let max_islands = branch_blocks.len().max(1) * 3;

    let mut call_blocks = func
        .call_sites()
        .by_id
        .values()
        .filter_map(|call| {
            let target = call.direct_target?;
            let summary = derived.summaries.get(&InterprocFunctionId(target))?;
            if summary
                .cases
                .iter()
                .all(|case| case.memory_writes.is_empty())
            {
                return None;
            }
            let (block_addr, _) = func.inst_op_site(call.at)?;
            Some((!hot_blocks.contains(&block_addr), block_addr, summary))
        })
        .collect::<Vec<_>>();
    call_blocks.sort_by_key(|(cold_block, block_addr, _)| (*cold_block, *block_addr));

    for (_, block_addr, summary) in call_blocks.into_iter().take(max_islands) {
        let terms = by_anchor.entry(block_addr).or_default();
        for case in &summary.cases {
            for write in &case.memory_writes {
                let exact_value = write.value.is_concrete();
                let evidence =
                    derived_summary_memory_term_evidence(summary.completion, exact_value);
                let term = BackwardMemoryCondition {
                    region: crate::BackwardMemoryRegion::Argument {
                        index: write.arg_index,
                    },
                    offset_lo: write.offset,
                    offset_hi: write.offset,
                    size: write.size,
                    exact_offset: matches!(summary.completion, DerivedSummaryCompletion::Exact),
                    evidence,
                    binding: None,
                    expr: summary_memory_location_expr(write.arg_index, write.offset),
                    value_expr: Some(write.value.to_string()),
                    exact_value,
                };
                if !terms.contains(&term) {
                    terms.push(term);
                }
            }
        }
    }

    by_anchor
}

fn symbolic_condition_hint(summary: Option<&BackwardConditionSummary>) -> Option<String> {
    summary
        .map(|compiled| compiled.simplified.trim().to_string())
        .filter(|text| !text.is_empty() && text != "true")
}

fn symbolic_fact_explorer<'ctx>(ctx: &'ctx Context) -> PathExplorer<'ctx> {
    let mut explorer = PathExplorer::with_config(
        ctx,
        ExploreConfig {
            subsumption_states: true,
            max_states: 256,
            max_depth: 96,
            max_completed_paths: Some(8),
            merge_states: false,
            ..ExploreConfig::default()
        },
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
    install_hooks: F,
) -> (Vec<BranchObservation>, SymbolicFunctionFactDiagnostics)
where
    F: Fn(&mut PathExplorer<'ctx>),
{
    let mut branch_facts = Vec::new();
    let mut diagnostics = SymbolicFunctionFactDiagnostics::default();
    for &(block_addr, true_target, false_target) in branch_blocks {
        diagnostics.branches_evaluated += 1;
        let predicate_uses_call_result = predicate_depends_on_call_result(func, block_addr);

        let make_state = || {
            let mut state = SymState::new(ctx, func.entry);
            seed_default_state_for_arch(&mut state, func, Some(arch));
            state
        };

        let mut true_explorer = symbolic_fact_explorer(ctx);
        install_hooks(&mut true_explorer);
        let true_initial_state = make_state();
        let (compiled_true_status, true_compiled) = compiled_branch_reachability_status(
            &true_explorer,
            func,
            &true_initial_state,
            block_addr,
            true,
        );
        let true_condition = symbolic_condition_hint(true_compiled.as_ref());
        let true_status = if let Some(status) = compiled_true_status {
            status
        } else if predicate_uses_call_result || func_contains_calls(func) {
            SymbolicReachabilityStatus::Unknown
        } else {
            let paths = true_explorer.find_paths_to(func, make_state(), true_target);
            symbolic_reachability_status(paths.len(), true_explorer.budget_exhausted())
        };

        let mut false_explorer = symbolic_fact_explorer(ctx);
        install_hooks(&mut false_explorer);
        let false_initial_state = make_state();
        let (compiled_false_status, false_compiled) = compiled_branch_reachability_status(
            &false_explorer,
            func,
            &false_initial_state,
            block_addr,
            false,
        );
        let false_condition = symbolic_condition_hint(false_compiled.as_ref());
        let false_status = if let Some(status) = compiled_false_status {
            status
        } else if predicate_uses_call_result || func_contains_calls(func) {
            SymbolicReachabilityStatus::Unknown
        } else {
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

fn install_derived_summary_set<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    registry: &SummaryRegistry<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    derived: &DerivedSummarySet<'ctx>,
    symbol_map: &HashMap<u64, String>,
) {
    let prepared = scope
        .and_then(|scope| scope.root())
        .map(|root| &root.prepared)
        .unwrap_or(func);
    let _ = registry.install_interproc_summaries_for_function(
        explorer,
        prepared,
        &derived.interproc,
        symbol_map,
    );
    let _ = registry.install_derived_summaries_for_function(
        explorer,
        prepared,
        &derived.summaries,
        symbol_map,
    );
    let _ = registry.install_known_symbols_for_function(explorer, prepared, symbol_map);
}

fn install_symbolic_fact_hooks<'ctx>(
    ctx: &'ctx Context,
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    summary_profile: SummaryProfile,
    symbol_map: &HashMap<u64, String>,
) {
    let Some(registry) =
        SummaryRegistry::with_profile_for_arch_and_symbols(arch, symbol_map, summary_profile)
    else {
        return;
    };
    if let Some(scope) = scope {
        let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
        install_derived_summary_set(explorer, &registry, func, Some(scope), &derived, symbol_map);
        return;
    }
    let _ = registry.install_known_symbols_for_function(explorer, func, symbol_map);
}

fn compiled_branch_reachability_status<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    block_addr: u64,
    truth: bool,
) -> (
    Option<SymbolicReachabilityStatus>,
    Option<BackwardConditionSummary>,
) {
    let derived_summaries = explorer.derived_call_summary_views();
    if func_contains_calls(func) && derived_summaries.is_empty() {
        return (None, None);
    }
    let Some(compiled) = compile_branch_precondition_with_summaries(
        func,
        initial_state,
        block_addr,
        truth,
        &derived_summaries,
    ) else {
        return (None, None);
    };
    let summary = compiled.summary;
    if !matches!(summary.precision, BackwardConditionPrecision::Exact) {
        return (None, Some(summary));
    }
    let status = match explorer
        .solver()
        .sat_with_constraint(initial_state, &compiled.predicate)
    {
        SatResult::Sat => Some(SymbolicReachabilityStatus::Reachable),
        SatResult::Unsat => Some(SymbolicReachabilityStatus::Unreachable),
        SatResult::Unknown => None,
    };
    (status, Some(summary))
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

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_canonical_semantic_regions_with_derived<'ctx>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    registry: &SummaryRegistry<'ctx>,
    derived: &DerivedSummarySet<'ctx>,
) -> CollectedNativeSemanticRegions {
    collect_canonical_semantic_regions_with_derived_for_branch_blocks(
        ctx,
        func,
        scope,
        arch,
        &collect_branch_blocks(func),
        summary_profile,
        registry,
        derived,
        symbol_map,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_canonical_semantic_regions_with_derived_for_branch_blocks<'ctx>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    branch_blocks: &[(u64, u64, u64)],
    summary_profile: SummaryProfile,
    registry: &SummaryRegistry<'ctx>,
    derived: &DerivedSummarySet<'ctx>,
    symbol_map: &HashMap<u64, String>,
) -> CollectedNativeSemanticRegions {
    let (branch_facts, diagnostics) =
        collect_branch_observations_for_branch_blocks(ctx, func, arch, branch_blocks, |explorer| {
            install_derived_summary_set(explorer, registry, func, scope, derived, symbol_map);
        });
    let _ = summary_profile;
    CollectedNativeSemanticRegions {
        regions: build_canonical_regions(
            &branch_facts,
            &derive_summary_memory_terms_by_anchor(func, branch_blocks, derived),
            &diagnostics,
        ),
        diagnostics,
    }
}

pub(super) fn collect_large_cfg_canonical_semantic_regions_with_limit(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    branch_limit: usize,
) -> CollectedNativeSemanticRegions {
    let branch_blocks = limited_branch_blocks(func, branch_limit.max(1));
    let mut collected = if let Some(scope) = scope {
        if let Some(registry) =
            SummaryRegistry::with_profile_for_arch_and_symbols(arch, symbol_map, summary_profile)
        {
            let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
            collect_canonical_semantic_regions_with_derived_for_branch_blocks(
                ctx,
                func,
                Some(scope),
                arch,
                &branch_blocks,
                summary_profile,
                &registry,
                &derived,
                symbol_map,
            )
        } else {
            let (branch_facts, diagnostics) = collect_branch_observations_for_branch_blocks(
                ctx,
                func,
                arch,
                &branch_blocks,
                |explorer| {
                    install_symbolic_fact_hooks(
                        ctx,
                        explorer,
                        func,
                        None,
                        arch,
                        summary_profile,
                        symbol_map,
                    );
                },
            );
            CollectedNativeSemanticRegions {
                regions: build_canonical_regions(&branch_facts, &BTreeMap::new(), &diagnostics),
                diagnostics,
            }
        }
    } else {
        let (branch_facts, diagnostics) = collect_branch_observations_for_branch_blocks(
            ctx,
            func,
            arch,
            &branch_blocks,
            |explorer| {
                install_symbolic_fact_hooks(
                    ctx,
                    explorer,
                    func,
                    None,
                    arch,
                    summary_profile,
                    symbol_map,
                );
            },
        );
        CollectedNativeSemanticRegions {
            regions: build_canonical_regions(&branch_facts, &BTreeMap::new(), &diagnostics),
            diagnostics,
        }
    };
    collected.diagnostics.skipped_large_cfg = true;
    collected
}

pub(super) fn collect_canonical_semantic_regions_with_scope_and_profile(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> CollectedNativeSemanticRegions {
    let Some(arch) = arch else {
        return CollectedNativeSemanticRegions {
            regions: BTreeMap::new(),
            diagnostics: SymbolicFunctionFactDiagnostics {
                skipped_missing_arch: true,
                ..SymbolicFunctionFactDiagnostics::default()
            },
        };
    };

    let cfg_summary = func.function().cfg_risk_summary();
    if cfg_summary.block_count > 96 || cfg_summary.switch_block_count > 8 {
        return collect_large_cfg_canonical_semantic_regions_with_limit(
            ctx,
            func,
            scope,
            arch,
            symbol_map,
            summary_profile,
            large_cfg_branch_limit(func),
        );
    }

    if let Some(scope) = scope {
        let Some(registry) =
            SummaryRegistry::with_profile_for_arch_and_symbols(arch, symbol_map, summary_profile)
        else {
            return CollectedNativeSemanticRegions::default();
        };
        let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
        return collect_canonical_semantic_regions_with_derived(
            ctx,
            func,
            Some(scope),
            arch,
            symbol_map,
            summary_profile,
            &registry,
            &derived,
        );
    }

    let branch_blocks = collect_branch_blocks(func);
    let (branch_facts, diagnostics) = collect_branch_observations_for_branch_blocks(
        ctx,
        func,
        arch,
        &branch_blocks,
        |explorer| {
            install_symbolic_fact_hooks(
                ctx,
                explorer,
                func,
                None,
                arch,
                summary_profile,
                symbol_map,
            );
        },
    );
    CollectedNativeSemanticRegions {
        regions: build_canonical_regions(&branch_facts, &BTreeMap::new(), &diagnostics),
        diagnostics,
    }
}
