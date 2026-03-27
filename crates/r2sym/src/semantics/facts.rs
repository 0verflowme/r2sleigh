use std::collections::{BTreeSet, HashMap};

use r2il::ArchSpec;
use r2ssa::SsaArtifact;
use serde::{Deserialize, Serialize};
use z3::Context;

use crate::SymState;
use crate::backward::{
    BackwardConditionPrecision, BackwardConditionSummary,
    compile_branch_precondition_with_summaries,
};
use crate::path::{ExploreConfig, PathExplorer};
use crate::runtime::seed_default_state_for_arch;
use crate::sim::{DerivedSummarySet, PreparedFunctionScope, SummaryProfile, SummaryRegistry};
use crate::solver::SatResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolicReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicBranchFact {
    pub block_addr: u64,
    pub true_target: u64,
    pub false_target: u64,
    pub true_status: SymbolicReachabilityStatus,
    pub false_status: SymbolicReachabilityStatus,
    pub true_condition: Option<String>,
    pub false_condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub true_compiled: Option<BackwardConditionSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub false_compiled: Option<BackwardConditionSummary>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicFunctionFactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicFunctionFacts {
    pub branch_facts: Vec<SymbolicBranchFact>,
    pub diagnostics: SymbolicFunctionFactDiagnostics,
}

impl SymbolicFunctionFacts {
    pub fn branch_fact_for_block(&self, block_addr: u64) -> Option<&SymbolicBranchFact> {
        self.branch_facts
            .iter()
            .find(|fact| fact.block_addr == block_addr)
    }
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
    let Some(registry) = SummaryRegistry::with_profile_for_arch(arch, summary_profile) else {
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
pub(super) fn collect_symbolic_function_facts_with_derived<'ctx>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    registry: &SummaryRegistry<'ctx>,
    derived: &DerivedSummarySet<'ctx>,
) -> SymbolicFunctionFacts {
    let mut facts = SymbolicFunctionFacts::default();
    let branch_blocks = func
        .cfg()
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
        .collect::<Vec<_>>();

    for (block_addr, true_target, false_target) in branch_blocks {
        facts.diagnostics.branches_evaluated += 1;
        let predicate_uses_call_result = predicate_depends_on_call_result(func, block_addr);

        let make_state = || {
            let mut state = SymState::new(ctx, func.entry);
            seed_default_state_for_arch(&mut state, func, Some(arch));
            state
        };

        let mut true_explorer = symbolic_fact_explorer(ctx);
        install_derived_summary_set(
            &mut true_explorer,
            registry,
            func,
            scope,
            derived,
            symbol_map,
        );
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
        install_derived_summary_set(
            &mut false_explorer,
            registry,
            func,
            scope,
            derived,
            symbol_map,
        );
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
            facts.diagnostics.branches_unknown += 1;
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
            facts.diagnostics.branches_pruned += 1;
        }

        facts.branch_facts.push(SymbolicBranchFact {
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

    let _ = summary_profile;
    facts
}

pub fn collect_symbolic_function_facts(
    ctx: &Context,
    func: &SsaArtifact,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
) -> SymbolicFunctionFacts {
    collect_symbolic_function_facts_with_scope(ctx, func, None, arch, symbol_map)
}

pub fn collect_symbolic_function_facts_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
) -> SymbolicFunctionFacts {
    let mut facts = SymbolicFunctionFacts::default();
    let Some(arch) = arch else {
        facts.diagnostics.skipped_missing_arch = true;
        return facts;
    };

    let cfg_summary = func.function().cfg_risk_summary();
    if cfg_summary.block_count > 96 || cfg_summary.switch_block_count > 8 {
        facts.diagnostics.skipped_large_cfg = true;
        return facts;
    }

    if let Some(scope) = scope {
        let Some(registry) = SummaryRegistry::with_profile_for_arch(arch, SummaryProfile::Default)
        else {
            return facts;
        };
        let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
        return collect_symbolic_function_facts_with_derived(
            ctx,
            func,
            Some(scope),
            arch,
            symbol_map,
            SummaryProfile::Default,
            &registry,
            &derived,
        );
    }

    let branch_blocks = func
        .cfg()
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
        .collect::<Vec<_>>();

    for (block_addr, true_target, false_target) in branch_blocks {
        facts.diagnostics.branches_evaluated += 1;
        let predicate_uses_call_result = predicate_depends_on_call_result(func, block_addr);

        let make_state = || {
            let mut state = SymState::new(ctx, func.entry);
            seed_default_state_for_arch(&mut state, func, Some(arch));
            state
        };

        let mut true_explorer = symbolic_fact_explorer(ctx);
        install_symbolic_fact_hooks(
            ctx,
            &mut true_explorer,
            func,
            None,
            arch,
            SummaryProfile::Default,
            symbol_map,
        );
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
        install_symbolic_fact_hooks(
            ctx,
            &mut false_explorer,
            func,
            None,
            arch,
            SummaryProfile::Default,
            symbol_map,
        );
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
            facts.diagnostics.branches_unknown += 1;
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
            facts.diagnostics.branches_pruned += 1;
        }

        facts.branch_facts.push(SymbolicBranchFact {
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

    facts
}
