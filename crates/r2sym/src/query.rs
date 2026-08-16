//! Typed query-oriented symbolic analysis APIs.
//!
//! This module wraps the lower-level path exploration engine in reusable,
//! analysis-oriented queries that can be consumed by the plugin or other
//! analysis layers without exposing command-shaped policy.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs::OpenOptions;
use std::io::Write;
use std::time::Duration;

use r2il::ArchSpec;
use z3::Context;
use z3::ast::{Ast, BV, Bool};

use r2ssa::{
    AssumptionSubject, AssumptionUsageReport, AssumptionValue, CompareKind,
    PreparedAssumptionBindingKind, SSAOp, SSAVar, SsaArtifact,
};

#[cfg(test)]
use crate::BackwardConditionPrecision;
use crate::SymState;
use crate::backward::{
    BackwardConditionSummary, CompiledBackwardCondition,
    compile_branch_precondition_with_summaries, compile_target_precondition_with_summaries,
    compile_value_postcondition_with_summaries,
};
use crate::constraints::build_final_constraint_graph_for_path;
use crate::path::{ExploreConfig, ExploreStats, PathExplorer, PathResult, SolvedPath};
use crate::runtime::install_runtime_hooks_for_scope;
use crate::semantics::{
    SemanticArtifact, TargetQueryExecutionRoute, TargetQueryRouteInput, VmStepSummary,
    build_vm_step_summary, classify_interpreter_like,
};
use crate::sim::{PreparedFunctionScope, SummaryProfile, SummaryRegistry};
use crate::solver::{SatResult, SolverStats};
use crate::state::ExitStatus;
use crate::tactics::SolveTacticConfig;
use crate::verification::{
    EvidenceSummary, LiftedReplayBackend, SolveStatus, SolveVerification, SolveVerificationRequest,
    SolveWitness, VerificationRequirement, evidence_summary_for_route_and_stats,
    solution_extraction_allowed, verification_requirement_for_route_and_stats, verify_solve_result,
};

const MAX_VM_COMPILED_STEPS: usize = 8;

fn debug_query_route_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_QUERY_ROUTE").is_some()
}

fn debug_query_route_log(message: &str) {
    if !debug_query_route_enabled() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_QUERY_ROUTE_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_query_route.log".to_string());
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(file, "{message}");
    }
}

fn debug_query_phase_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_QUERY_PHASES").is_some()
}

fn debug_query_phase_log(message: &str) {
    if !debug_query_phase_enabled() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_QUERY_PHASES_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_query_phases.log".to_string());
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(file, "{message}");
    }
}

#[derive(Debug, Clone, Default)]
struct QueryAssumptionOutcome {
    usage: AssumptionUsageReport,
    conditioned: bool,
    conflicted: bool,
}

fn apply_predicate_assumption_to_state<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    state: &mut SymState<'ctx>,
    block_addr: u64,
    truth: bool,
) -> Result<bool, String> {
    let derived_summaries = explorer.derived_call_summary_views();
    let Some(compiled) = compile_branch_precondition_with_summaries(
        func,
        state,
        block_addr,
        truth,
        &derived_summaries,
    ) else {
        return Ok(false);
    };
    match explorer
        .solver()
        .sat_with_constraint(state, &compiled.predicate)
    {
        SatResult::Sat
            if compiled.summary.evidence().allows_hard_proof()
                || compiled.summary.evidence().allows_narrowing() =>
        {
            state.add_constraint(compiled.predicate);
            Ok(true)
        }
        SatResult::Sat | SatResult::Unknown => Ok(false),
        SatResult::Unsat => Err(format!(
            "branch assumption for block 0x{block_addr:x} contradicts symbolic state"
        )),
    }
}

fn assumption_usage_for_query<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    state: &mut SymState<'ctx>,
) -> QueryAssumptionOutcome {
    let mut usage = AssumptionUsageReport::default();
    let mut conditioned = false;
    let mut conflicted = false;

    for binding in &func.facts().applied_assumption_bindings {
        match (&binding.binding, &binding.assumption.value) {
            (
                PreparedAssumptionBindingKind::Predicate {
                    block_addr, truth, ..
                },
                AssumptionValue::Branch { .. },
            ) => match apply_predicate_assumption_to_state(
                explorer,
                func,
                state,
                *block_addr,
                *truth,
            ) {
                Ok(true) => {
                    usage.mark_applied(&binding.assumption);
                    conditioned = true;
                }
                Ok(false) => usage.mark_ignored(&binding.assumption),
                Err(reason) => {
                    usage.mark_conflict(&binding.assumption, reason);
                    conflicted = true;
                }
            },
            (
                PreparedAssumptionBindingKind::Register {
                    state_name, bits, ..
                },
                value,
            ) => {
                let Some(current) = state.registers().get(state_name).cloned() else {
                    usage.mark_ignored(&binding.assumption);
                    continue;
                };
                match apply_assumption_value_to_sym(
                    state,
                    &binding.assumption,
                    &current,
                    *bits,
                    value,
                ) {
                    Ok(true) => {
                        usage.mark_applied(&binding.assumption);
                        conditioned = true;
                    }
                    Ok(false) => usage.mark_ignored(&binding.assumption),
                    Err(reason) => {
                        usage.mark_conflict(&binding.assumption, reason);
                        conflicted = true;
                    }
                }
            }
            _ => {}
        }
    }

    for assumption in func.facts().assumptions.iter() {
        if matches!(assumption.subject, AssumptionSubject::MemoryWindow { .. }) {
            match apply_memory_window_assumption(state, assumption) {
                Ok(true) => {
                    usage.mark_applied(assumption);
                    conditioned = true;
                }
                Ok(false) => usage.mark_ignored(assumption),
                Err(reason) => {
                    usage.mark_conflict(assumption, reason);
                    conflicted = true;
                }
            }
        }
    }

    for assumption in func.facts().assumptions.iter() {
        usage.mark_ignored(assumption);
    }

    QueryAssumptionOutcome {
        usage,
        conditioned,
        conflicted,
    }
}

fn apply_assumption_value_to_sym<'ctx>(
    state: &mut SymState<'ctx>,
    assumption: &r2ssa::AnalysisAssumption,
    value: &crate::value::SymValue<'ctx>,
    bits: u32,
    assumption_value: &AssumptionValue,
) -> Result<bool, String> {
    match assumption_value {
        AssumptionValue::Constant { value: rhs } => {
            if let Some(existing) = value.as_concrete() {
                if existing != *rhs {
                    return Err(format!(
                        "assumption constant 0x{rhs:x} contradicts concrete value 0x{existing:x}"
                    ));
                }
                return Ok(true);
            }
            state.constrain_eq(value, *rhs);
            Ok(true)
        }
        AssumptionValue::Range { min, max } => {
            if min > max {
                return Err("invalid range assumption".to_string());
            }
            if let Some(existing) = value.as_concrete() {
                if existing < *min || existing > *max {
                    return Err(format!(
                        "assumption range [{min:#x}, {max:#x}] excludes concrete value {existing:#x}"
                    ));
                }
                return Ok(true);
            }
            state.constrain_range(value, *min, *max);
            Ok(true)
        }
        AssumptionValue::FiniteSet { values } => {
            if values.is_empty() {
                return Err("empty finite-set assumption".to_string());
            }
            if let Some(existing) = value.as_concrete() {
                if !values.contains(&existing) {
                    return Err(format!(
                        "finite-set assumption excludes concrete value {existing:#x}"
                    ));
                }
                return Ok(true);
            }
            let bv = value.to_bv(state.context());
            let ors = values
                .iter()
                .map(|item| bv.eq(BV::from_u64(*item, bits.max(1))))
                .collect::<Vec<_>>();
            let refs = ors.iter().collect::<Vec<_>>();
            state.add_constraint(Bool::or(&refs));
            Ok(true)
        }
        AssumptionValue::EnumDomain { values, .. } => {
            let values = values.iter().map(|value| *value as u64).collect::<Vec<_>>();
            apply_assumption_value_to_sym(
                state,
                assumption,
                value,
                bits,
                &AssumptionValue::FiniteSet { values },
            )
        }
        AssumptionValue::TypeHint { .. } => Ok(false),
        AssumptionValue::Branch { .. } => match &assumption.subject {
            AssumptionSubject::Predicate { .. } => Ok(true),
            _ => Ok(false),
        },
    }
}

fn apply_memory_window_assumption<'ctx>(
    state: &mut SymState<'ctx>,
    assumption: &r2ssa::AnalysisAssumption,
) -> Result<bool, String> {
    let AssumptionSubject::MemoryWindow { addr, size } = &assumption.subject else {
        return Ok(false);
    };
    let Some(region) = state
        .symbolic_memory()
        .iter()
        .find(|region| region.addr == *addr && region.size == *size)
        .cloned()
    else {
        return Ok(false);
    };
    if *size > 8 {
        return Ok(false);
    }
    apply_assumption_value_to_sym(
        state,
        assumption,
        &region.value,
        region.value.bits(),
        &assumption.value,
    )
}

/// Query execution strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryMode {
    /// Use the current forward symbolic execution engine.
    ForwardOnly,
    /// Reserve a slot for future target-guided pruning.
    TargetGuided,
}

/// Typed configuration for engine-level symbolic queries.
#[derive(Debug, Clone)]
pub struct SymQueryConfig {
    /// Core exploration budgets and strategy.
    pub explore: ExploreConfig,
    /// Query execution mode.
    pub mode: QueryMode,
    /// Summary profile to use when installing function summaries.
    pub summary_profile: SummaryProfile,
    /// Candidate-generation tactics used after exact semantic summaries.
    pub solve_tactics: SolveTacticConfig,
}

impl Default for SymQueryConfig {
    fn default() -> Self {
        let explore = ExploreConfig {
            subsumption_states: true,
            ..ExploreConfig::default()
        };
        Self {
            explore,
            mode: QueryMode::ForwardOnly,
            summary_profile: SummaryProfile::Default,
            solve_tactics: SolveTacticConfig::default(),
        }
    }
}

impl SymQueryConfig {
    /// Build a path explorer for this query configuration.
    pub fn make_explorer<'ctx>(&self, ctx: &'ctx Context) -> PathExplorer<'ctx> {
        self.make_explorer_with_execution_control(ctx, crate::SymExecutionControl::default())
    }

    /// Build a path explorer with caller-owned cancellation and deadline control.
    pub fn make_explorer_with_execution_control<'ctx>(
        &self,
        ctx: &'ctx Context,
        execution: crate::SymExecutionControl,
    ) -> PathExplorer<'ctx> {
        let mut explorer =
            PathExplorer::with_config_and_execution_control(ctx, self.explore.clone(), execution);
        explorer.set_target_guided_queries(matches!(self.mode, QueryMode::TargetGuided));
        explorer.set_solve_tactic_config(self.solve_tactics.clone());
        explorer
    }
}

/// Recommend a query-depth budget based on the SSA op count and symbolic input surface.
///
/// Depth is currently counted per executed SSA op, not per basic block. A flat budget
/// can therefore under-approximate string/hash loops and other byte-at-a-time workers.
/// This helper keeps the budget tied to concrete function cost and the current symbolic
/// input surface instead of hard-coding sample-specific constants downstream.
pub fn recommended_query_max_depth(func: &SsaArtifact, initial_state: &SymState<'_>) -> usize {
    let cfg_risk = func.function().cfg_risk_summary();
    let total_ops = func
        .blocks()
        .map(|block| block.ops.len())
        .sum::<usize>()
        .max(1);
    let max_block_ops = func
        .blocks()
        .map(|block| block.ops.len())
        .max()
        .unwrap_or(1)
        .max(1);
    let symbolic_surface = initial_state.symbolic_inputs().len().clamp(1, 16);
    let bounded_copy_loop_work = estimated_bounded_copy_loop_work(func);
    let loop_multiplier = if func.function().cfg_risk_summary().back_edge_count == 0 {
        symbolic_surface.saturating_add(4)
    } else {
        symbolic_surface.saturating_add(2)
    };
    let base_budget = total_ops
        .saturating_mul(loop_multiplier)
        .max(max_block_ops.saturating_mul(loop_multiplier.saturating_mul(2)));
    let budget = base_budget.max(
        total_ops
            .saturating_add(bounded_copy_loop_work)
            .saturating_add(max_block_ops.saturating_mul(loop_multiplier)),
    );
    if cfg_risk.block_count >= 64 || cfg_risk.back_edge_count > 0 {
        budget.max(4096)
    } else {
        budget
    }
}

/// Recommend a query timeout budget for the current function shape.
///
/// Large bounded copy loops often materialize runtime code byte-by-byte before any
/// symbolic branching happens. Those routes need more wall-clock time even when the
/// actual search frontier stays small.
pub fn recommended_query_timeout(func: &SsaArtifact) -> Duration {
    let cfg_risk = func.function().cfg_risk_summary();
    let bounded_copy_loop_work = estimated_bounded_copy_loop_work(func);
    if bounded_copy_loop_work >= 32 * 1024 {
        Duration::from_secs(180)
    } else if bounded_copy_loop_work >= 8 * 1024 {
        Duration::from_secs(120)
    } else if cfg_risk.block_count >= 64 || cfg_risk.back_edge_count > 0 {
        Duration::from_secs(60)
    } else {
        Duration::from_secs(20)
    }
}

const CONTINUATION_QUERY_MAX_DEPTH_CAP: usize = 8_192;
const CONTINUATION_QUERY_MAX_STATES_CAP: usize = 256;
const CONTINUATION_QUERY_TIMEOUT_CAP: Duration = Duration::from_secs(10);
const CONTINUATION_SEEDED_STATE_CAP: usize = 1;

#[derive(Debug, Clone)]
pub struct QueryExecutionPolicy {
    pub route: crate::TargetQueryRoutePlan,
    pub evidence_summary: EvidenceSummary,
    pub verification_requirement: VerificationRequirement,
    pub max_states: usize,
    pub max_depth: usize,
    pub timeout: Option<Duration>,
    pub install_scope_summaries: bool,
    pub install_runtime_hooks: bool,
}

impl QueryExecutionPolicy {
    pub fn for_route(
        config: &SymQueryConfig,
        func: &SsaArtifact,
        initial_state: &SymState<'_>,
        route: crate::TargetQueryRoutePlan,
    ) -> Self {
        let max_states =
            recommended_query_max_states_for_route(config.explore.max_states, Some(&route));
        let max_depth = config
            .explore
            .max_depth
            .max(recommended_query_max_depth_for_route(
                func,
                initial_state,
                Some(&route),
            ));
        let current_timeout = config
            .explore
            .timeout
            .unwrap_or_else(|| Duration::from_secs(20));
        let recommended_timeout = recommended_query_timeout_for_route(func, Some(&route));
        let timeout = if route_is_continuation_seeded(Some(&route)) {
            current_timeout.min(recommended_timeout)
        } else {
            current_timeout.max(recommended_timeout)
        };
        let route_only_stats = ExploreStats::default();
        let evidence_summary =
            evidence_summary_for_route_and_stats(&route, &route_only_stats, None);
        let verification_requirement =
            verification_requirement_for_route_and_stats(&route, &route_only_stats, None);
        Self {
            install_scope_summaries: !route_skips_eager_scope_summaries(&route),
            install_runtime_hooks: true,
            evidence_summary,
            verification_requirement,
            route,
            max_states,
            max_depth,
            timeout: Some(timeout),
        }
    }
}

pub fn apply_query_execution_policy(config: &mut SymQueryConfig, policy: &QueryExecutionPolicy) {
    config.explore.max_states = policy.max_states;
    config.explore.max_depth = policy.max_depth;
    config.explore.timeout = policy.timeout;
}

pub fn route_skips_eager_scope_summaries(route: &crate::TargetQueryRoutePlan) -> bool {
    matches!(
        &route.target_plan,
        crate::TargetQueryPlan::Residual { reasons }
            if reasons.iter().any(|reason| reason == "LargeCfg")
    )
}

pub struct SymbolicHookInstallContext<'ctx, 'a> {
    z3_ctx: &'ctx Context,
    prepared: &'a SsaArtifact,
    scope: &'a PreparedFunctionScope,
    arch: Option<&'a ArchSpec>,
    symbol_map: &'a std::collections::HashMap<u64, String>,
    summary_profile: SummaryProfile,
    policy: &'a QueryExecutionPolicy,
}

impl<'ctx, 'a> SymbolicHookInstallContext<'ctx, 'a> {
    pub fn new(
        z3_ctx: &'ctx Context,
        prepared: &'a SsaArtifact,
        scope: &'a PreparedFunctionScope,
        arch: Option<&'a ArchSpec>,
        symbol_map: &'a std::collections::HashMap<u64, String>,
        summary_profile: SummaryProfile,
        policy: &'a QueryExecutionPolicy,
    ) -> Self {
        Self {
            z3_ctx,
            prepared,
            scope,
            arch,
            symbol_map,
            summary_profile,
            policy,
        }
    }
}

pub fn install_symbolic_hooks_for_query_policy<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    context: SymbolicHookInstallContext<'ctx, '_>,
) {
    let SymbolicHookInstallContext {
        z3_ctx,
        prepared,
        scope,
        arch,
        symbol_map,
        summary_profile,
        policy,
    } = context;
    let Some(scope) = scope.exact_for_artifact(prepared) else {
        return;
    };
    if policy.install_scope_summaries
        && let Some(arch) = arch
        && let Some(registry) =
            SummaryRegistry::with_profile_for_arch_and_symbols(arch, symbol_map, summary_profile)
    {
        let _ = registry.install_scope_summaries_for_explorer(
            explorer,
            z3_ctx,
            prepared,
            scope,
            Some(arch),
            symbol_map,
        );
    }
    if policy.install_runtime_hooks {
        install_runtime_hooks_for_scope(explorer, prepared, scope, arch, symbol_map);
    }
}

fn route_is_continuation_seeded(route: Option<&crate::TargetQueryRoutePlan>) -> bool {
    route.is_some_and(|route| {
        matches!(
            route.execution,
            TargetQueryExecutionRoute::ContinuationSeeded { .. }
        )
    })
}

pub fn recommended_query_max_depth_for_route(
    func: &SsaArtifact,
    initial_state: &SymState<'_>,
    route: Option<&crate::TargetQueryRoutePlan>,
) -> usize {
    let budget = recommended_query_max_depth(func, initial_state);
    if route_is_continuation_seeded(route) {
        budget.min(CONTINUATION_QUERY_MAX_DEPTH_CAP)
    } else {
        budget
    }
}

pub fn recommended_query_max_states_for_route(
    current_max_states: usize,
    route: Option<&crate::TargetQueryRoutePlan>,
) -> usize {
    if route_is_continuation_seeded(route) {
        current_max_states.min(CONTINUATION_QUERY_MAX_STATES_CAP)
    } else {
        current_max_states
    }
}

pub fn recommended_query_timeout_for_route(
    func: &SsaArtifact,
    route: Option<&crate::TargetQueryRoutePlan>,
) -> Duration {
    let timeout = recommended_query_timeout(func);
    if route_is_continuation_seeded(route) {
        timeout.min(CONTINUATION_QUERY_TIMEOUT_CAP)
    } else {
        timeout
    }
}

fn estimated_bounded_copy_loop_work(func: &SsaArtifact) -> usize {
    func.predicates()
        .predicates
        .values()
        .filter_map(|predicate| estimate_bounded_copy_loop_work(func, predicate))
        .sum()
}

fn estimate_bounded_copy_loop_work(
    func: &SsaArtifact,
    predicate: &r2ssa::PredicateFact,
) -> Option<usize> {
    let self_loop = predicate.true_target == predicate.block_addr
        || predicate.false_target == predicate.block_addr;
    if !self_loop {
        return None;
    }

    let block = func.function().get_block(predicate.block_addr)?;
    let has_load = block.ops.iter().any(|op| matches!(op, SSAOp::Load { .. }));
    let has_store = block.ops.iter().any(|op| matches!(op, SSAOp::Store { .. }));
    if !has_load || !has_store {
        return None;
    }

    let comparison = predicate.comparison.as_ref()?;
    let bound = [comparison.lhs, comparison.rhs]
        .into_iter()
        .filter_map(|value_id| func.value_var(value_id))
        .filter_map(ssa_const_value)
        .max()?;

    let trip_count = match comparison.kind {
        CompareKind::Less => bound,
        CompareKind::LessEqual => bound.saturating_add(1),
        _ => return None,
    };

    if trip_count == 0 {
        return None;
    }

    let capped_trip_count = trip_count.min(1 << 20) as usize;
    Some(block.ops.len().max(1).saturating_mul(capped_trip_count))
}

fn ssa_const_value(var: &SSAVar) -> Option<u64> {
    let value = var.name.strip_prefix("const:")?;
    u64::from_str_radix(value, 16).ok()
}

/// Completion state for queries that may stop on budgets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryCompletion {
    /// Exploration finished without hitting timeout or state budgets.
    Complete,
    /// Exploration stopped because a configured budget was exhausted.
    BudgetExhausted,
    /// Cooperative cancellation stopped exploration.
    Cancelled,
    /// A caller-provided deadline stopped exploration.
    DeadlineExceeded,
}

/// Reachability result status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
    BudgetExhausted,
    Cancelled,
    DeadlineExceeded,
}

/// Compact summary of a path condition reaching a given program counter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathConditionTerm {
    pub expr: String,
}

/// Typed symbolic path-condition artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicConditionSet {
    pub simplified: String,
    pub terms: Vec<PathConditionTerm>,
    pub num_constraints: usize,
}

/// Compact summary of a path condition reaching a given program counter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathConditionSummary {
    pub final_pc: u64,
    pub depth: usize,
    pub exit_status: ExitStatus,
    pub feasible: bool,
    pub num_constraints: usize,
    pub condition: String,
    pub path_condition: SymbolicConditionSet,
}

/// Result of asking whether a target can be reached.
#[derive(Debug)]
pub struct ReachabilityResult<'ctx> {
    pub status: ReachabilityStatus,
    pub target_addr: u64,
    pub selected_route: crate::TargetQueryRoutePlan,
    pub compiled_precondition: Option<BackwardConditionSummary>,
    pub paths: Vec<PathResult<'ctx>>,
    pub assumption_usage: AssumptionUsageReport,
    pub assumption_conditioned: bool,
    pub summary_conditioned: bool,
    pub stats: ExploreStats,
    pub solver_stats: SolverStats,
}

/// Result of asking for the conditions that hold at a target PC.
#[derive(Debug)]
pub struct PathConditionResult<'ctx> {
    pub completion: QueryCompletion,
    pub target_pc: u64,
    pub selected_route: crate::TargetQueryRoutePlan,
    pub compiled_precondition: Option<BackwardConditionSummary>,
    pub conditions: Vec<PathConditionSummary>,
    pub matching_paths: Vec<PathResult<'ctx>>,
    pub assumption_usage: AssumptionUsageReport,
    pub assumption_conditioned: bool,
    pub summary_conditioned: bool,
    pub stats: ExploreStats,
    pub solver_stats: SolverStats,
}

/// Result of solving for a concrete target.
#[derive(Debug)]
pub struct SolveResult<'ctx> {
    pub status: SolveStatus,
    pub target_addr: u64,
    pub selected_route: crate::TargetQueryRoutePlan,
    pub compiled_precondition: Option<BackwardConditionSummary>,
    pub matched_paths: Vec<PathResult<'ctx>>,
    pub selected_path_index: Option<usize>,
    pub solution: Option<SolvedPath>,
    pub assumption_usage: AssumptionUsageReport,
    pub assumption_conditioned: bool,
    pub summary_conditioned: bool,
    pub verification: SolveVerification,
    pub witness: SolveWitness,
    pub stats: ExploreStats,
    pub solver_stats: SolverStats,
}

/// Function-level symbolic summary with collected paths.
#[derive(Debug)]
pub struct SymbolicFunctionSummary<'ctx> {
    pub completion: QueryCompletion,
    pub paths: Vec<PathResult<'ctx>>,
    pub feasible_paths: usize,
    pub stats: ExploreStats,
    pub solver_stats: SolverStats,
}

struct TargetQueryPaths<'ctx> {
    selected_route: crate::TargetQueryRoutePlan,
    compiled_precondition: Option<BackwardConditionSummary>,
    matched_paths: Vec<PathResult<'ctx>>,
    exact_unsat: bool,
    summary_conditioned: bool,
}

fn completion_from_stats(stats: &ExploreStats) -> QueryCompletion {
    if matches!(
        stats.execution_stop,
        Some(crate::SymExecutionStopReason::Cancelled)
    ) {
        QueryCompletion::Cancelled
    } else if matches!(
        stats.execution_stop,
        Some(crate::SymExecutionStopReason::DeadlineExceeded)
    ) {
        QueryCompletion::DeadlineExceeded
    } else if stats.timed_out || stats.max_states_exhausted {
        QueryCompletion::BudgetExhausted
    } else {
        QueryCompletion::Complete
    }
}

fn condition_string<'ctx>(state: &SymState<'ctx>) -> String {
    match state.constraints() {
        [] => "true".to_string(),
        [constraint] => constraint.simplify().to_string(),
        _ => state.path_condition().simplify().to_string(),
    }
}

fn symbolic_condition_set<'ctx>(state: &SymState<'ctx>) -> SymbolicConditionSet {
    let terms = state
        .constraints()
        .iter()
        .map(|constraint| PathConditionTerm {
            expr: constraint.simplify().to_string(),
        })
        .collect();
    SymbolicConditionSet {
        simplified: condition_string(state),
        terms,
        num_constraints: state.num_constraints(),
    }
}

fn condition_summary<'ctx>(path: &PathResult<'ctx>) -> PathConditionSummary {
    let path_condition = symbolic_condition_set(&path.state);
    PathConditionSummary {
        final_pc: path.final_pc(),
        depth: path.depth,
        exit_status: path.exit_status.clone(),
        feasible: path.feasible,
        num_constraints: path.num_constraints(),
        condition: path_condition.simplified.clone(),
        path_condition,
    }
}

enum PreconditionApplication<'ctx> {
    Continue {
        initial_state: Box<SymState<'ctx>>,
        narrowed_state: Option<Box<SymState<'ctx>>>,
        compiled_precondition: Option<BackwardConditionSummary>,
        summary_conditioned: bool,
    },
    ExactUnsat {
        compiled_precondition: BackwardConditionSummary,
        summary_conditioned: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompiledPreconditionMode {
    Necessary,
    NarrowOnly,
}

fn compiled_mode_from_guidance(mode: crate::QueryGuidanceMode) -> CompiledPreconditionMode {
    match mode {
        crate::QueryGuidanceMode::Necessary => CompiledPreconditionMode::Necessary,
        crate::QueryGuidanceMode::NarrowOnly => CompiledPreconditionMode::NarrowOnly,
    }
}

fn build_target_query_inputs<'a>(
    explorer: &mut PathExplorer<'_>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    artifact: Option<&'a SemanticArtifact>,
    target_addr: u64,
    assumption_conflicted: bool,
    allow_continuation_bridge: bool,
) -> TargetQueryRouteInput<'a> {
    let artifact = artifact.filter(|artifact| artifact.shares_artifact(func));
    let mut inputs = artifact
        .map(|artifact| artifact.target_query_route_input(target_addr, assumption_conflicted))
        .unwrap_or_else(|| TargetQueryRouteInput {
            route: crate::TargetQueryRoutePlan::dynamic_fallback(),
            condition_source: None,
            memory_terms: Vec::new(),
            allow_exact_proof: !assumption_conflicted,
        });
    if allow_continuation_bridge
        && let Some(bridge_target) =
            explorer.exception_bridge_target_in_scope(func, scope, target_addr)
        && bridge_target != target_addr
        && !matches!(
            inputs.route.execution,
            TargetQueryExecutionRoute::Refuse { .. }
        )
    {
        inputs.route.execution = TargetQueryExecutionRoute::ContinuationSeeded {
            bridge_target,
            route: Box::new(inputs.route.execution.clone()),
        };
        debug_query_route_log(&format!(
            "target=0x{target_addr:x} route=ContinuationSeeded bridge=0x{bridge_target:x}"
        ));
    } else {
        debug_query_route_log(&format!(
            "target=0x{target_addr:x} route={:?}",
            inputs.route.execution
        ));
    }
    inputs
}

pub fn selected_target_query_route_in_scope(
    explorer: &mut PathExplorer<'_>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    artifact: Option<&SemanticArtifact>,
    target_addr: u64,
    assumption_conflicted: bool,
) -> crate::TargetQueryRoutePlan {
    let scope = scope.and_then(|scope| scope.exact_for_artifact(func));
    build_target_query_inputs(
        explorer,
        func,
        scope,
        artifact,
        target_addr,
        assumption_conflicted,
        true,
    )
    .route
}

fn route_uses_summary_guidance(
    route: &TargetQueryExecutionRoute,
    has_derived_summaries: bool,
) -> bool {
    if !has_derived_summaries {
        return false;
    }
    match route {
        TargetQueryExecutionRoute::ContinuationSeeded { route, .. } => {
            route_uses_summary_guidance(route, has_derived_summaries)
        }
        TargetQueryExecutionRoute::ArtifactCondition { .. }
        | TargetQueryExecutionRoute::DynamicTargetCompile { .. }
        | TargetQueryExecutionRoute::VmTargetCompile { .. } => true,
        TargetQueryExecutionRoute::ArtifactMemoryOnly
        | TargetQueryExecutionRoute::ResidualOnly { .. }
        | TargetQueryExecutionRoute::Refuse { .. } => false,
    }
}

fn state_is_continuation_seed<'ctx>(state: &SymState<'ctx>) -> bool {
    state.pending_exception().is_some() || state.runtime_region_for_pc(state.pc()).is_some()
}

fn stats_show_summary_guidance(stats: &ExploreStats) -> bool {
    stats.target_summary_rank_hits > 0 || stats.target_pruned_summary_contradiction > 0
}

#[cfg_attr(test, allow(dead_code))]
#[cfg(test)]
fn precision_rank(precision: BackwardConditionPrecision) -> u8 {
    match precision {
        BackwardConditionPrecision::Exact => 3,
        BackwardConditionPrecision::OverApprox => 2,
        BackwardConditionPrecision::ResidualSearchRequired => 1,
        BackwardConditionPrecision::Unsupported => 0,
    }
}

fn vm_exit_guard_allows_target(
    bindings: &BTreeMap<String, u64>,
    arm: &crate::VmTransferArm,
    target_addr: u64,
) -> bool {
    let guards = arm
        .exit_guards
        .iter()
        .filter(|guard| guard.target == target_addr)
        .collect::<Vec<_>>();
    if guards.is_empty() {
        return true;
    }
    let mut saw_reliable = false;
    for guarded in guards {
        let evidence = guarded.guard.evidence();
        if !evidence.is_usable() {
            return true;
        }
        if !evidence.allows_narrowing() {
            if matches!(guarded.guard.evaluate(bindings), Some(true)) {
                return true;
            }
            continue;
        }
        saw_reliable = true;
        match guarded.guard.evaluate(bindings) {
            Some(true) => return true,
            Some(false) => {}
            None => return true,
        }
    }
    !saw_reliable
}

fn vm_arm_reaches_target(
    bindings: &BTreeMap<String, u64>,
    arm: &crate::VmTransferArm,
    target_addr: u64,
) -> bool {
    arm.handler_target == target_addr
        || arm.region_blocks.contains(&target_addr)
        || (arm.exit_targets.contains(&target_addr)
            && vm_exit_guard_allows_target(bindings, arm, target_addr))
}

fn vm_arm_for_case(vm_step: &VmStepSummary, case_value: u64) -> Option<&crate::VmTransferArm> {
    vm_step
        .transfers
        .iter()
        .find(|arm| arm.case_values.contains(&case_value))
}

fn vm_selector_bindings(vm_step: &VmStepSummary, case_value: u64) -> BTreeMap<String, u64> {
    let mut bindings = BTreeMap::new();
    if let Some(selector) = vm_step.selector.as_ref() {
        bindings.insert(selector.clone(), case_value);
    }
    bindings
}

fn vm_apply_confident_state_updates(
    bindings: &BTreeMap<String, u64>,
    updates: &[crate::VmStateUpdate],
) -> BTreeMap<String, u64> {
    let mut next = bindings.clone();
    for update in updates {
        if !update.evidence().allows_narrowing() {
            continue;
        }
        if let Some(value) = update.value.evaluate_u64(&next) {
            next.insert(update.output.clone(), value);
        }
    }
    next
}

fn vm_apply_confident_memory_writes(
    bindings: &BTreeMap<String, u64>,
    writes: &[crate::VmMemoryCondition],
) -> BTreeMap<String, u64> {
    let mut next = bindings.clone();
    for write in writes {
        if !write.evidence().allows_narrowing() {
            continue;
        }
        let Some(binding) = write.binding.as_ref() else {
            continue;
        };
        let Some(value) = write.value.as_ref() else {
            continue;
        };
        let Some(value) = value.evaluate_u64(&next) else {
            continue;
        };
        next.insert(binding.clone(), value);
    }
    next
}

fn vm_next_case_value(
    bindings: &BTreeMap<String, u64>,
    arm: &crate::VmTransferArm,
    selector_name: Option<&str>,
    dispatch_header: u64,
    loop_header: u64,
) -> Option<(u64, BTreeMap<String, u64>)> {
    if !arm.redispatch || arm.truncated {
        return None;
    }
    let can_redispatch = arm.exit_targets.iter().any(|target| {
        (*target == dispatch_header || *target == loop_header)
            && vm_exit_guard_allows_target(bindings, arm, *target)
    }) || arm.exit_targets.is_empty();
    if !can_redispatch {
        return None;
    }
    let mut next_bindings = vm_apply_confident_state_updates(bindings, &arm.state_updates);
    let selector_update = arm.selector_update.as_ref()?;
    if !selector_update.evidence().allows_narrowing() {
        return None;
    }
    let next_case = selector_update.value.evaluate_u64(&next_bindings)?;
    next_bindings = vm_apply_confident_memory_writes(&next_bindings, &arm.memory_writes);
    next_bindings.insert(selector_update.output.clone(), next_case);
    if let Some(selector_name) = selector_name {
        next_bindings.insert(selector_name.to_string(), next_case);
    }
    Some((next_case, next_bindings))
}

fn vm_case_reaches_target(vm_step: &VmStepSummary, initial_case: u64, target_addr: u64) -> bool {
    let initial_bindings = vm_selector_bindings(vm_step, initial_case);
    let mut queue = VecDeque::from([(initial_case, initial_bindings, 0usize)]);
    let mut seen = BTreeSet::new();

    while let Some((case_value, bindings, depth)) = queue.pop_front() {
        let binding_key = bindings
            .iter()
            .map(|(name, value)| (name.clone(), *value))
            .collect::<Vec<_>>();
        if !seen.insert((case_value, binding_key)) {
            continue;
        }
        let Some(arm) = vm_arm_for_case(vm_step, case_value) else {
            continue;
        };
        if vm_arm_reaches_target(&bindings, arm, target_addr) {
            return true;
        }
        if depth >= MAX_VM_COMPILED_STEPS.saturating_sub(1) || !arm.redispatch {
            continue;
        }
        let Some((next_case, next_bindings)) = vm_next_case_value(
            &bindings,
            arm,
            vm_step.selector.as_deref(),
            vm_step.dispatch_header,
            vm_step.loop_header,
        ) else {
            continue;
        };
        queue.push_back((next_case, next_bindings, depth + 1));
    }

    false
}

fn vm_target_case_values(vm_step: &VmStepSummary, target_addr: u64) -> Vec<u64> {
    let mut case_values = BTreeSet::new();

    for arm in &vm_step.transfers {
        for case_value in arm.case_values.iter().copied() {
            if vm_case_reaches_target(vm_step, case_value, target_addr) {
                case_values.insert(case_value);
            }
        }
    }

    case_values.into_iter().collect()
}

fn compile_vm_target_precondition_with_summaries<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    target_addr: u64,
    call_summaries: &std::collections::HashMap<u64, crate::backward::DerivedCallSummaryView<'ctx>>,
) -> Option<CompiledBackwardCondition> {
    let interpreter = classify_interpreter_like(func)?;
    let vm_step = build_vm_step_summary(func, &interpreter)?;
    let case_values = vm_target_case_values(&vm_step, target_addr);
    if case_values.is_empty() {
        return None;
    }
    let selector = func
        .function()
        .infer_switch_selector_var(vm_step.dispatch_header)?;
    let ctx = initial_state.context();
    compile_value_postcondition_with_summaries(
        func,
        initial_state,
        vm_step.dispatch_header,
        selector,
        {
            let case_values = case_values.clone();
            move |value| {
                let selector_bv = value.to_bv(ctx);
                let disjuncts = case_values
                    .iter()
                    .map(|value| {
                        selector_bv.eq(z3::ast::BV::from_u64(*value, selector_bv.get_size()))
                    })
                    .collect::<Vec<_>>();
                match disjuncts.as_slice() {
                    [] => z3::ast::Bool::from_bool(false),
                    [single] => single.clone(),
                    _ => {
                        let refs = disjuncts.iter().collect::<Vec<_>>();
                        z3::ast::Bool::or(&refs)
                    }
                }
            }
        },
        call_summaries,
    )
}

#[cfg_attr(test, allow(dead_code))]
#[cfg(test)]
fn prefer_compiled_precondition(
    current: Option<&CompiledBackwardCondition>,
    candidate: &CompiledBackwardCondition,
) -> bool {
    let Some(current) = current else {
        return true;
    };
    let current_rank = precision_rank(current.summary.precision);
    let candidate_rank = precision_rank(candidate.summary.precision);
    if candidate_rank != current_rank {
        return candidate_rank > current_rank;
    }
    if candidate.summary.backward_memory_residual_fallbacks
        != current.summary.backward_memory_residual_fallbacks
    {
        return candidate.summary.backward_memory_residual_fallbacks
            < current.summary.backward_memory_residual_fallbacks;
    }
    if candidate.summary.memory_terms.len() != current.summary.memory_terms.len() {
        return candidate.summary.memory_terms.len() > current.summary.memory_terms.len();
    }
    if candidate.summary.supported_paths != current.summary.supported_paths {
        return candidate.summary.supported_paths > current.summary.supported_paths;
    }
    candidate.summary.total_paths < current.summary.total_paths
}

fn parse_const_u64_text(text: &str) -> Option<u64> {
    let trimmed = text.trim();
    if let Some(hex) = trimmed.strip_prefix("0x") {
        return u64::from_str_radix(hex, 16).ok();
    }
    if let Some(hex) = trimmed.strip_prefix("const:") {
        return u64::from_str_radix(hex, 16).ok();
    }
    trimmed.parse::<u64>().ok()
}

fn constrain_region_backed_memory_term<'ctx>(
    narrowed: &mut SymState<'ctx>,
    term: &crate::backward::BackwardMemoryCondition,
    rhs: u64,
) -> bool {
    if !term.exact_value {
        return false;
    }
    let (base_addr, offset_values) = match (&term.region, term.concrete_offset_range()) {
        (crate::backward::BackwardMemoryRegion::Region(region), Some((offset_lo, offset_hi)))
            if offset_hi >= offset_lo =>
        {
            let Some(def) = narrowed.memory.region_def(region.id) else {
                return false;
            };
            let Some(base_addr) = def.base_addr else {
                return false;
            };
            let Some(span) = offset_hi.checked_sub(offset_lo) else {
                return false;
            };
            if span > 8 {
                return false;
            }
            let offset_values = (offset_lo..=offset_hi).collect::<Vec<_>>();
            (base_addr, offset_values)
        }
        _ => return false,
    };
    let mut predicates = Vec::new();
    for offset in offset_values {
        let Some(addr) = base_addr.checked_add_signed(offset) else {
            continue;
        };
        let value = narrowed.mem_read(&crate::SymValue::concrete(addr, 64), term.size);
        predicates.push(
            value
                .to_bv(narrowed.context())
                .eq(BV::from_u64(rhs, value.bits())),
        );
    }
    match predicates.as_slice() {
        [] => false,
        [single] => {
            narrowed.add_constraint(single.clone());
            true
        }
        _ => {
            let refs = predicates.iter().collect::<Vec<_>>();
            narrowed.add_constraint(Bool::or(&refs));
            true
        }
    }
}

fn apply_memory_term_narrowing<'ctx>(
    state: &SymState<'ctx>,
    terms: &[&crate::backward::BackwardMemoryCondition],
) -> Option<Box<SymState<'ctx>>> {
    let mut narrowed = state.fork();
    let mut applied = 0usize;
    for term in terms {
        if !term.evidence().allows_narrowing() || !term.exact_value {
            continue;
        }
        let Some(value_expr) = term.value_expr.as_deref() else {
            continue;
        };
        let Some(rhs) = parse_const_u64_text(value_expr) else {
            continue;
        };
        if let Some(binding) = term.binding.as_ref()
            && let Some(value) = narrowed.symbolic_inputs().get(binding).cloned()
        {
            narrowed.constrain_eq(&value, rhs);
            applied += 1;
            continue;
        }
        if constrain_region_backed_memory_term(&mut narrowed, term, rhs) {
            applied += 1;
        }
    }
    (applied > 0).then_some(Box::new(narrowed))
}

fn apply_compiled_precondition_with_mode<'ctx>(
    explorer: &PathExplorer<'ctx>,
    mut initial_state: SymState<'ctx>,
    compiled: crate::CompiledBackwardCondition,
    mode: CompiledPreconditionMode,
    allow_exact_proof: bool,
) -> PreconditionApplication<'ctx> {
    let summary = compiled.summary.clone();
    let evidence = summary.evidence();
    match explorer
        .solver()
        .sat_with_constraint(&initial_state, &compiled.predicate)
    {
        SatResult::Unsat
            if mode == CompiledPreconditionMode::Necessary
                && allow_exact_proof
                && evidence.allows_hard_proof() =>
        {
            PreconditionApplication::ExactUnsat {
                compiled_precondition: summary,
                summary_conditioned: false,
            }
        }
        SatResult::Sat => {
            if mode == CompiledPreconditionMode::Necessary
                && allow_exact_proof
                && evidence.allows_hard_proof()
            {
                initial_state.add_constraint(compiled.predicate);
                PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state: None,
                    compiled_precondition: Some(summary),
                    summary_conditioned: false,
                }
            } else if evidence.allows_narrowing() {
                let mut narrowed_state = initial_state.fork();
                narrowed_state.add_constraint(compiled.predicate);
                PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state: Some(Box::new(narrowed_state)),
                    compiled_precondition: Some(summary),
                    summary_conditioned: false,
                }
            } else {
                PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state: None,
                    compiled_precondition: Some(summary),
                    summary_conditioned: false,
                }
            }
        }
        SatResult::Unknown | SatResult::Unsat => PreconditionApplication::Continue {
            initial_state: Box::new(initial_state),
            narrowed_state: None,
            compiled_precondition: Some(summary),
            summary_conditioned: false,
        },
    }
}

fn find_paths_with_compiled_narrowing<'ctx, F>(
    explorer: &mut PathExplorer<'ctx>,
    initial_state: SymState<'ctx>,
    narrowed_state: Option<Box<SymState<'ctx>>>,
    mut search: F,
) -> Vec<PathResult<'ctx>>
where
    F: FnMut(&mut PathExplorer<'ctx>, SymState<'ctx>) -> Vec<PathResult<'ctx>>,
{
    if let Some(narrowed_state) = narrowed_state {
        let matches = search(explorer, *narrowed_state);
        if !matches.is_empty() || explorer.search_stopped() {
            return matches;
        }
    }
    search(explorer, initial_state)
}

fn find_first_path_with_compiled_narrowing<'ctx, F>(
    explorer: &mut PathExplorer<'ctx>,
    initial_state: SymState<'ctx>,
    narrowed_state: Option<Box<SymState<'ctx>>>,
    mut search: F,
) -> Option<PathResult<'ctx>>
where
    F: FnMut(&mut PathExplorer<'ctx>, SymState<'ctx>) -> Option<PathResult<'ctx>>,
{
    if let Some(narrowed_state) = narrowed_state {
        let matched = search(explorer, *narrowed_state);
        if matched.is_some() || explorer.search_stopped() {
            return matched;
        }
    }
    search(explorer, initial_state)
}

fn apply_best_compiled_precondition_for_inputs<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    initial_state: SymState<'ctx>,
    target_addr: u64,
    query_inputs: &TargetQueryRouteInput<'_>,
) -> PreconditionApplication<'ctx> {
    let derived_summaries = explorer.derived_call_summary_views();
    let memory_terms = query_inputs.memory_terms.clone();
    let target_is_local = func.get_block(target_addr).is_some();
    let route_summary_conditioned =
        route_uses_summary_guidance(&query_inputs.route.execution, !derived_summaries.is_empty());
    match query_inputs.route.execution {
        TargetQueryExecutionRoute::ContinuationSeeded { .. } => PreconditionApplication::Continue {
            initial_state: Box::new(initial_state),
            narrowed_state: None,
            compiled_precondition: None,
            summary_conditioned: route_summary_conditioned,
        },
        TargetQueryExecutionRoute::ArtifactCondition { mode } => {
            let compiled = query_inputs.condition_source.and_then(|source| {
                compile_branch_precondition_with_summaries(
                    func,
                    &initial_state,
                    source.block_addr,
                    source.branch_truth,
                    &derived_summaries,
                )
                .map(|compiled| (compiled, mode))
            });
            if compiled.is_none()
                && let Some(narrowed_state) =
                    apply_memory_term_narrowing(&initial_state, &memory_terms)
            {
                let compiled_precondition = query_inputs
                    .condition_source
                    .map(|source| source.summary)
                    .filter(|summary| !summary.evidence().allows_hard_proof())
                    .cloned();
                return PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state: Some(narrowed_state),
                    compiled_precondition,
                    summary_conditioned: route_summary_conditioned,
                };
            }
            let Some((compiled, mode)) = compiled else {
                let narrowed_state = apply_memory_term_narrowing(&initial_state, &memory_terms);
                return PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state,
                    compiled_precondition: None,
                    summary_conditioned: route_summary_conditioned,
                };
            };
            match apply_compiled_precondition_with_mode(
                explorer,
                initial_state,
                compiled,
                compiled_mode_from_guidance(mode),
                query_inputs.allow_exact_proof,
            ) {
                PreconditionApplication::Continue {
                    initial_state,
                    narrowed_state,
                    compiled_precondition,
                    ..
                } => {
                    let narrowed_state = narrowed_state.or_else(|| {
                        apply_memory_term_narrowing(initial_state.as_ref(), &memory_terms)
                    });
                    PreconditionApplication::Continue {
                        initial_state,
                        narrowed_state,
                        compiled_precondition,
                        summary_conditioned: route_summary_conditioned,
                    }
                }
                PreconditionApplication::ExactUnsat {
                    compiled_precondition,
                    ..
                } => PreconditionApplication::ExactUnsat {
                    compiled_precondition,
                    summary_conditioned: route_summary_conditioned,
                },
            }
        }
        TargetQueryExecutionRoute::ArtifactMemoryOnly => {
            let narrowed_state = apply_memory_term_narrowing(&initial_state, &memory_terms);
            let compiled_precondition = query_inputs
                .condition_source
                .map(|source| source.summary)
                .filter(|summary| !summary.evidence().allows_hard_proof())
                .cloned();
            PreconditionApplication::Continue {
                initial_state: Box::new(initial_state),
                narrowed_state,
                compiled_precondition,
                summary_conditioned: false,
            }
        }
        TargetQueryExecutionRoute::DynamicTargetCompile { reason: _, mode } => {
            if !target_is_local {
                let narrowed_state = apply_memory_term_narrowing(&initial_state, &memory_terms);
                return PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state,
                    compiled_precondition: None,
                    summary_conditioned: false,
                };
            }
            let compiled = compile_target_precondition_with_summaries(
                func,
                &initial_state,
                target_addr,
                &derived_summaries,
            );
            match compiled {
                Some(compiled) => match apply_compiled_precondition_with_mode(
                    explorer,
                    initial_state,
                    compiled,
                    compiled_mode_from_guidance(mode),
                    query_inputs.allow_exact_proof,
                ) {
                    PreconditionApplication::Continue {
                        initial_state,
                        narrowed_state,
                        compiled_precondition,
                        ..
                    } => {
                        let narrowed_state = narrowed_state.or_else(|| {
                            apply_memory_term_narrowing(initial_state.as_ref(), &memory_terms)
                        });
                        PreconditionApplication::Continue {
                            initial_state,
                            narrowed_state,
                            compiled_precondition,
                            summary_conditioned: route_summary_conditioned,
                        }
                    }
                    PreconditionApplication::ExactUnsat {
                        compiled_precondition,
                        ..
                    } => PreconditionApplication::ExactUnsat {
                        compiled_precondition,
                        summary_conditioned: route_summary_conditioned,
                    },
                },
                None => {
                    let narrowed_state = apply_memory_term_narrowing(&initial_state, &memory_terms);
                    PreconditionApplication::Continue {
                        initial_state: Box::new(initial_state),
                        narrowed_state,
                        compiled_precondition: None,
                        summary_conditioned: false,
                    }
                }
            }
        }
        TargetQueryExecutionRoute::VmTargetCompile { reason: _ } => {
            if !target_is_local {
                let narrowed_state = apply_memory_term_narrowing(&initial_state, &memory_terms);
                return PreconditionApplication::Continue {
                    initial_state: Box::new(initial_state),
                    narrowed_state,
                    compiled_precondition: None,
                    summary_conditioned: false,
                };
            }
            let compiled = compile_vm_target_precondition_with_summaries(
                func,
                &initial_state,
                target_addr,
                &derived_summaries,
            );
            match compiled {
                Some(compiled) => match apply_compiled_precondition_with_mode(
                    explorer,
                    initial_state,
                    compiled,
                    CompiledPreconditionMode::Necessary,
                    query_inputs.allow_exact_proof,
                ) {
                    PreconditionApplication::Continue {
                        initial_state,
                        narrowed_state,
                        compiled_precondition,
                        ..
                    } => {
                        let narrowed_state = narrowed_state.or_else(|| {
                            apply_memory_term_narrowing(initial_state.as_ref(), &memory_terms)
                        });
                        PreconditionApplication::Continue {
                            initial_state,
                            narrowed_state,
                            compiled_precondition,
                            summary_conditioned: route_summary_conditioned,
                        }
                    }
                    PreconditionApplication::ExactUnsat {
                        compiled_precondition,
                        ..
                    } => PreconditionApplication::ExactUnsat {
                        compiled_precondition,
                        summary_conditioned: route_summary_conditioned,
                    },
                },
                None => {
                    let narrowed_state = apply_memory_term_narrowing(&initial_state, &memory_terms);
                    PreconditionApplication::Continue {
                        initial_state: Box::new(initial_state),
                        narrowed_state,
                        compiled_precondition: None,
                        summary_conditioned: false,
                    }
                }
            }
        }
        TargetQueryExecutionRoute::ResidualOnly { .. }
        | TargetQueryExecutionRoute::Refuse { .. } => PreconditionApplication::Continue {
            initial_state: Box::new(initial_state),
            narrowed_state: None,
            compiled_precondition: None,
            summary_conditioned: false,
        },
    }
}

#[cfg(test)]
fn apply_best_compiled_precondition<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    artifact: Option<&SemanticArtifact>,
    initial_state: SymState<'ctx>,
    target_addr: u64,
    assumption_conflicted: bool,
) -> PreconditionApplication<'ctx> {
    let query_inputs = artifact
        .map(|artifact| artifact.target_query_route_input(target_addr, assumption_conflicted))
        .unwrap_or_else(|| TargetQueryRouteInput {
            route: crate::TargetQueryRoutePlan::dynamic_fallback(),
            condition_source: None,
            memory_terms: Vec::new(),
            allow_exact_proof: !assumption_conflicted,
        });
    apply_best_compiled_precondition_for_inputs(
        explorer,
        func,
        initial_state,
        target_addr,
        &query_inputs,
    )
}

fn execute_target_query_paths_from_inputs<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    initial_state: SymState<'ctx>,
    target_addr: u64,
    query_inputs: &TargetQueryRouteInput<'_>,
) -> TargetQueryPaths<'ctx> {
    let selected_route = query_inputs.route.clone();
    match apply_best_compiled_precondition_for_inputs(
        explorer,
        func,
        initial_state,
        target_addr,
        query_inputs,
    ) {
        PreconditionApplication::Continue {
            initial_state,
            narrowed_state,
            compiled_precondition,
            summary_conditioned,
        } => TargetQueryPaths {
            selected_route,
            compiled_precondition,
            matched_paths: find_paths_with_compiled_narrowing(
                explorer,
                *initial_state,
                narrowed_state,
                |explorer, state| explorer.find_paths_to_in_scope(func, scope, state, target_addr),
            ),
            exact_unsat: false,
            summary_conditioned,
        },
        PreconditionApplication::ExactUnsat {
            compiled_precondition,
            summary_conditioned,
        } => TargetQueryPaths {
            selected_route,
            compiled_precondition: Some(compiled_precondition),
            matched_paths: Vec::new(),
            exact_unsat: true,
            summary_conditioned,
        },
    }
}

fn execute_target_query_first_path_from_inputs<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    initial_state: SymState<'ctx>,
    target_addr: u64,
    query_inputs: &TargetQueryRouteInput<'_>,
) -> TargetQueryPaths<'ctx> {
    let selected_route = query_inputs.route.clone();
    match apply_best_compiled_precondition_for_inputs(
        explorer,
        func,
        initial_state,
        target_addr,
        query_inputs,
    ) {
        PreconditionApplication::Continue {
            initial_state,
            narrowed_state,
            compiled_precondition,
            summary_conditioned,
        } => TargetQueryPaths {
            selected_route,
            compiled_precondition,
            matched_paths: find_first_path_with_compiled_narrowing(
                explorer,
                *initial_state,
                narrowed_state,
                |explorer, state| explorer.find_path_to_in_scope(func, scope, state, target_addr),
            )
            .into_iter()
            .collect(),
            exact_unsat: false,
            summary_conditioned,
        },
        PreconditionApplication::ExactUnsat {
            compiled_precondition,
            summary_conditioned,
        } => TargetQueryPaths {
            selected_route,
            compiled_precondition: Some(compiled_precondition),
            matched_paths: Vec::new(),
            exact_unsat: true,
            summary_conditioned,
        },
    }
}

fn continuation_seed_states<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    bridge_paths: Vec<PathResult<'ctx>>,
) -> Vec<SymState<'ctx>> {
    let mut seeds = Vec::new();
    for path in bridge_paths {
        if let Ok(next_states) = explorer.advance_current_block_in_scope(func, scope, path.state) {
            seeds.extend(next_states.into_iter().filter(state_is_continuation_seed));
        }
        if explorer.search_stopped() {
            break;
        }
    }
    seeds
}

fn rank_continuation_seeds<'ctx>(mut seeds: Vec<SymState<'ctx>>) -> Vec<SymState<'ctx>> {
    seeds.sort_by_key(|state| (state.num_constraints(), state.depth, state.pc()));
    seeds.truncate(CONTINUATION_SEEDED_STATE_CAP);
    seeds
}

fn continuation_followup_execution_route(
    route: &TargetQueryExecutionRoute,
) -> TargetQueryExecutionRoute {
    match route {
        TargetQueryExecutionRoute::DynamicTargetCompile { reason, .. } => {
            TargetQueryExecutionRoute::ResidualOnly {
                reasons: vec![
                    format!(
                        "continuation-seeded follow-up downgraded dynamic target compile: {reason}"
                    ),
                    "continuation-seeded runtime execution".to_string(),
                ],
            }
        }
        TargetQueryExecutionRoute::VmTargetCompile { reason } => {
            TargetQueryExecutionRoute::ResidualOnly {
                reasons: vec![
                    format!("continuation-seeded follow-up downgraded vm target compile: {reason}"),
                    "continuation-seeded runtime execution".to_string(),
                ],
            }
        }
        other => other.clone(),
    }
}

fn execute_target_query_paths<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    artifact: Option<&SemanticArtifact>,
    initial_state: SymState<'ctx>,
    target_addr: u64,
    assumption_conflicted: bool,
) -> TargetQueryPaths<'ctx> {
    let query_inputs = build_target_query_inputs(
        explorer,
        func,
        scope,
        artifact,
        target_addr,
        assumption_conflicted,
        true,
    );
    if let TargetQueryExecutionRoute::ContinuationSeeded {
        bridge_target,
        route,
    } = &query_inputs.route.execution
    {
        let mut bridge_inputs = build_target_query_inputs(
            explorer,
            func,
            scope,
            artifact,
            *bridge_target,
            assumption_conflicted,
            false,
        );
        bridge_inputs.route.execution = TargetQueryExecutionRoute::ResidualOnly {
            reasons: vec!["continuation bridge search".to_string()],
        };
        let bridge_paths = explorer.with_prune_infeasible(false, |explorer| {
            execute_target_query_paths_from_inputs(
                explorer,
                func,
                scope,
                initial_state,
                *bridge_target,
                &bridge_inputs,
            )
        });
        let mut summary_conditioned = bridge_paths.summary_conditioned;
        if bridge_paths.exact_unsat || bridge_paths.matched_paths.is_empty() {
            return TargetQueryPaths {
                selected_route: query_inputs.route.clone(),
                compiled_precondition: bridge_paths.compiled_precondition,
                matched_paths: Vec::new(),
                exact_unsat: bridge_paths.exact_unsat,
                summary_conditioned,
            };
        }

        let bridge_compiled_precondition = bridge_paths.compiled_precondition;
        let seeded_states = rank_continuation_seeds(continuation_seed_states(
            explorer,
            func,
            scope,
            bridge_paths.matched_paths,
        ));
        if seeded_states.is_empty() {
            return TargetQueryPaths {
                selected_route: query_inputs.route.clone(),
                compiled_precondition: bridge_compiled_precondition,
                matched_paths: Vec::new(),
                exact_unsat: false,
                summary_conditioned,
            };
        }

        let mut final_inputs = query_inputs.clone();
        final_inputs.route.execution = continuation_followup_execution_route(route);
        let mut matched_paths = Vec::new();
        let mut compiled_precondition = None;
        let mut any_exact_unsat = false;
        for state in seeded_states {
            let next = explorer.with_exception_bridge_guidance(false, |explorer| {
                execute_target_query_paths_from_inputs(
                    explorer,
                    func,
                    scope,
                    state,
                    target_addr,
                    &final_inputs,
                )
            });
            if compiled_precondition.is_none() {
                compiled_precondition = next.compiled_precondition;
            }
            summary_conditioned |= next.summary_conditioned;
            any_exact_unsat |= next.exact_unsat;
            matched_paths.extend(next.matched_paths);
            if explorer.search_stopped() {
                break;
            }
        }
        let no_matches = matched_paths.is_empty();

        return TargetQueryPaths {
            selected_route: query_inputs.route,
            compiled_precondition: compiled_precondition.or(bridge_compiled_precondition),
            matched_paths,
            exact_unsat: no_matches && any_exact_unsat,
            summary_conditioned,
        };
    }

    execute_target_query_paths_from_inputs(
        explorer,
        func,
        scope,
        initial_state,
        target_addr,
        &query_inputs,
    )
}

fn execute_target_query_first_path<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    artifact: Option<&SemanticArtifact>,
    initial_state: SymState<'ctx>,
    target_addr: u64,
    assumption_conflicted: bool,
) -> TargetQueryPaths<'ctx> {
    let query_inputs = build_target_query_inputs(
        explorer,
        func,
        scope,
        artifact,
        target_addr,
        assumption_conflicted,
        true,
    );
    if let TargetQueryExecutionRoute::ContinuationSeeded {
        bridge_target,
        route,
    } = &query_inputs.route.execution
    {
        debug_query_phase_log(&format!(
            "continuation:start target=0x{target_addr:x} bridge=0x{bridge_target:x}"
        ));
        let mut bridge_inputs = build_target_query_inputs(
            explorer,
            func,
            scope,
            artifact,
            *bridge_target,
            assumption_conflicted,
            false,
        );
        bridge_inputs.route.execution = TargetQueryExecutionRoute::ResidualOnly {
            reasons: vec!["continuation bridge search".to_string()],
        };
        debug_query_phase_log(&format!(
            "continuation:bridge_search target=0x{bridge_target:x} route={:?}",
            bridge_inputs.route.execution
        ));
        let bridge_selected_route = bridge_inputs.route.clone();
        let bridge_paths = explorer.with_prune_infeasible(false, |explorer| TargetQueryPaths {
            selected_route: bridge_selected_route,
            compiled_precondition: None,
            matched_paths: explorer
                .find_path_to_in_scope(func, scope, initial_state, *bridge_target)
                .into_iter()
                .collect(),
            exact_unsat: false,
            summary_conditioned: false,
        });
        debug_query_phase_log(&format!(
            "continuation:bridge_done target=0x{bridge_target:x} matched={} exact_unsat={} budget_exhausted={}",
            bridge_paths.matched_paths.len(),
            bridge_paths.exact_unsat,
            explorer.search_stopped(),
        ));
        let mut summary_conditioned = bridge_paths.summary_conditioned;
        let Some(bridge_path) = bridge_paths.matched_paths.into_iter().next() else {
            return TargetQueryPaths {
                selected_route: query_inputs.route.clone(),
                compiled_precondition: bridge_paths.compiled_precondition,
                matched_paths: Vec::new(),
                exact_unsat: bridge_paths.exact_unsat,
                summary_conditioned,
            };
        };

        let bridge_compiled_precondition = bridge_paths.compiled_precondition;
        let seeded_states = rank_continuation_seeds(continuation_seed_states(
            explorer,
            func,
            scope,
            vec![bridge_path],
        ));
        debug_query_phase_log(&format!(
            "continuation:seeded count={} budget_exhausted={}",
            seeded_states.len(),
            explorer.search_stopped(),
        ));
        let Some(state) = seeded_states.into_iter().next() else {
            return TargetQueryPaths {
                selected_route: query_inputs.route.clone(),
                compiled_precondition: bridge_compiled_precondition,
                matched_paths: Vec::new(),
                exact_unsat: false,
                summary_conditioned,
            };
        };

        let mut final_inputs = query_inputs.clone();
        final_inputs.route.execution = continuation_followup_execution_route(route);
        debug_query_phase_log(&format!(
            "continuation:final_search target=0x{target_addr:x} route={:?}",
            final_inputs.route.execution
        ));
        let next = explorer.with_exception_bridge_guidance(false, |explorer| {
            execute_target_query_first_path_from_inputs(
                explorer,
                func,
                scope,
                state,
                target_addr,
                &final_inputs,
            )
        });
        debug_query_phase_log(&format!(
            "continuation:final_done target=0x{target_addr:x} matched={} exact_unsat={} budget_exhausted={}",
            next.matched_paths.len(),
            next.exact_unsat,
            explorer.search_stopped(),
        ));
        summary_conditioned |= next.summary_conditioned;
        return TargetQueryPaths {
            selected_route: query_inputs.route,
            compiled_precondition: next.compiled_precondition.or(bridge_compiled_precondition),
            matched_paths: next.matched_paths,
            exact_unsat: next.exact_unsat,
            summary_conditioned,
        };
    }

    execute_target_query_first_path_from_inputs(
        explorer,
        func,
        scope,
        initial_state,
        target_addr,
        &query_inputs,
    )
}

impl<'ctx> PathExplorer<'ctx> {
    /// Ask whether a target address is reachable and collect the matching paths.
    pub fn can_reach(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> ReachabilityResult<'ctx> {
        self.can_reach_with_artifact_in_scope(func, None, None, initial_state, target_addr)
    }

    pub fn can_reach_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> ReachabilityResult<'ctx> {
        self.can_reach_with_artifact_in_scope(func, scope, None, initial_state, target_addr)
    }

    pub fn can_reach_with_artifact(
        &mut self,
        func: &SsaArtifact,
        artifact: Option<&SemanticArtifact>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> ReachabilityResult<'ctx> {
        self.can_reach_with_artifact_in_scope(func, None, artifact, initial_state, target_addr)
    }

    pub fn can_reach_with_artifact_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        artifact: Option<&SemanticArtifact>,
        mut initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> ReachabilityResult<'ctx> {
        let scope = scope.and_then(|scope| scope.exact_for_artifact(func));
        let assumption_outcome = assumption_usage_for_query(self, func, &mut initial_state);
        let query = execute_target_query_paths(
            self,
            func,
            scope,
            artifact,
            initial_state,
            target_addr,
            assumption_outcome.conflicted,
        );
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let summary_conditioned = query.summary_conditioned || stats_show_summary_guidance(&stats);
        let status = if !query.matched_paths.is_empty() {
            ReachabilityStatus::Reachable
        } else if matches!(
            stats.execution_stop,
            Some(crate::SymExecutionStopReason::Cancelled)
        ) {
            ReachabilityStatus::Cancelled
        } else if matches!(
            stats.execution_stop,
            Some(crate::SymExecutionStopReason::DeadlineExceeded)
        ) {
            ReachabilityStatus::DeadlineExceeded
        } else if self.budget_exhausted() {
            ReachabilityStatus::BudgetExhausted
        } else {
            ReachabilityStatus::Unreachable
        };
        ReachabilityResult {
            status,
            target_addr,
            selected_route: query.selected_route,
            compiled_precondition: query.compiled_precondition,
            paths: query.matched_paths,
            assumption_usage: assumption_outcome.usage,
            assumption_conditioned: assumption_outcome.conditioned,
            summary_conditioned,
            stats,
            solver_stats,
        }
    }

    /// Collect path conditions for states that reach a target PC.
    pub fn path_conditions_at(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_pc: u64,
    ) -> PathConditionResult<'ctx> {
        self.path_conditions_at_with_artifact_in_scope(func, None, None, initial_state, target_pc)
    }

    pub fn path_conditions_at_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        target_pc: u64,
    ) -> PathConditionResult<'ctx> {
        self.path_conditions_at_with_artifact_in_scope(func, scope, None, initial_state, target_pc)
    }

    pub fn path_conditions_at_with_artifact(
        &mut self,
        func: &SsaArtifact,
        artifact: Option<&SemanticArtifact>,
        initial_state: SymState<'ctx>,
        target_pc: u64,
    ) -> PathConditionResult<'ctx> {
        self.path_conditions_at_with_artifact_in_scope(
            func,
            None,
            artifact,
            initial_state,
            target_pc,
        )
    }

    pub fn path_conditions_at_with_artifact_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        artifact: Option<&SemanticArtifact>,
        mut initial_state: SymState<'ctx>,
        target_pc: u64,
    ) -> PathConditionResult<'ctx> {
        let scope = scope.and_then(|scope| scope.exact_for_artifact(func));
        let assumption_outcome = assumption_usage_for_query(self, func, &mut initial_state);
        let query = execute_target_query_paths(
            self,
            func,
            scope,
            artifact,
            initial_state,
            target_pc,
            assumption_outcome.conflicted,
        );
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let summary_conditioned = query.summary_conditioned || stats_show_summary_guidance(&stats);
        let conditions = query.matched_paths.iter().map(condition_summary).collect();
        PathConditionResult {
            completion: completion_from_stats(&stats),
            target_pc,
            selected_route: query.selected_route,
            compiled_precondition: query.compiled_precondition,
            conditions,
            matching_paths: query.matched_paths,
            assumption_usage: assumption_outcome.usage,
            assumption_conditioned: assumption_outcome.conditioned,
            summary_conditioned,
            stats,
            solver_stats,
        }
    }

    /// Solve for a concrete model that reaches a target address.
    pub fn solve_for_target(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> SolveResult<'ctx> {
        self.solve_for_target_with_artifact_in_scope(func, None, None, initial_state, target_addr)
    }

    pub fn solve_for_target_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> SolveResult<'ctx> {
        self.solve_for_target_with_artifact_in_scope(func, scope, None, initial_state, target_addr)
    }

    pub fn solve_for_target_with_artifact(
        &mut self,
        func: &SsaArtifact,
        artifact: Option<&SemanticArtifact>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> SolveResult<'ctx> {
        self.solve_for_target_with_artifact_in_scope(
            func,
            None,
            artifact,
            initial_state,
            target_addr,
        )
    }

    pub fn solve_for_target_with_artifact_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        artifact: Option<&SemanticArtifact>,
        mut initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> SolveResult<'ctx> {
        let scope = scope.and_then(|scope| scope.exact_for_artifact(func));
        let assumption_outcome = assumption_usage_for_query(self, func, &mut initial_state);
        let validation_initial_state = initial_state.fork();
        let query = execute_target_query_first_path(
            self,
            func,
            scope,
            artifact,
            initial_state,
            target_addr,
            assumption_outcome.conflicted,
        );
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let summary_conditioned = query.summary_conditioned || stats_show_summary_guidance(&stats);
        let selected_path_index = query
            .matched_paths
            .iter()
            .enumerate()
            .min_by_key(|(idx, path)| (path.num_constraints(), path.depth, *idx))
            .map(|(idx, _)| idx);
        let constraint_graph = selected_path_index
            .map(|idx| &query.matched_paths[idx])
            .map(|path| {
                build_final_constraint_graph_for_path(
                    func,
                    path,
                    &stats.runtime_loop_exact_recurrences,
                    target_addr,
                    None,
                )
            })
            .unwrap_or_default();
        let solution = if solution_extraction_allowed(&query.selected_route, &stats) {
            selected_path_index.and_then(|idx| self.solve_path(&query.matched_paths[idx]))
        } else {
            None
        };
        let tactic_solution = if solution_extraction_allowed(&query.selected_route, &stats) {
            selected_path_index.and_then(|idx| {
                self.solve_path_with_constraint_graph_tactics(
                    &query.matched_paths[idx],
                    &constraint_graph,
                    &stats.runtime_loop_exact_recurrences,
                )
            })
        } else {
            None
        };
        let solution = tactic_solution.or(solution);
        let mut replay_backend = LiftedReplayBackend::new(self);
        let (status, verification, witness) = verify_solve_result(
            SolveVerificationRequest {
                func,
                scope,
                selected_route: &query.selected_route,
                stats: &stats,
                validation_initial_state,
                target_addr,
                exact_unsat: query.exact_unsat,
                selected_path_index,
                solution: solution.as_ref(),
                constraint_graph: &constraint_graph,
            },
            &mut replay_backend,
        );
        SolveResult {
            status,
            target_addr,
            selected_route: query.selected_route,
            compiled_precondition: query.compiled_precondition,
            matched_paths: query.matched_paths,
            selected_path_index,
            solution,
            assumption_usage: assumption_outcome.usage,
            assumption_conditioned: assumption_outcome.conditioned,
            summary_conditioned,
            verification,
            witness,
            stats,
            solver_stats,
        }
    }

    /// Explore a function and return a typed symbolic summary over its paths.
    pub fn summarize_function(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
    ) -> SymbolicFunctionSummary<'ctx> {
        let paths = self.explore(func, initial_state);
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let feasible_paths = paths.iter().filter(|path| path.feasible).count();
        SymbolicFunctionSummary {
            completion: completion_from_stats(&stats),
            paths,
            feasible_paths,
            stats,
            solver_stats,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use super::{
        CompiledPreconditionMode, PreconditionApplication, apply_best_compiled_precondition,
        apply_compiled_precondition_with_mode, prefer_compiled_precondition, vm_target_case_values,
    };
    use crate::{
        ArtifactGranularity, BackwardConditionPrecision, BackwardConditionSummary,
        BackwardMemoryCondition, BackwardMemoryRegion, ControlFact, ExecutionModel, Judged,
        MemoryFact, NativeArtifactBody, NativeFunctionSummary, RefinementStage, RegionKey,
        ResidualReason, SatResult, SemanticArtifact, SemanticArtifactBody,
        SemanticArtifactDiagnostics, SemanticArtifactReport, SemanticEvidence,
        SemanticEvidenceReason, SemanticRegion, SliceClass, SymQueryConfig, SymState, TargetFact,
        TargetQueryExecutionRoute, TargetQueryPlan, VmBinaryOp, VmGuardCondition, VmGuardedExit,
        VmStateUpdate, VmStepSummary, VmTransferArm, VmValueExpr,
    };
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
    use r2ssa::{
        AnalysisAssumption, AssumptionProvenance, AssumptionScope, AssumptionSet,
        AssumptionSubject, AssumptionValue, SsaArtifact, ValueId,
    };
    use z3::Context;
    use z3::ast::BV;

    const RDI: u64 = 56;
    const TMP0: u64 = 0x80;
    const TMP1: u64 = 0x88;

    fn test_prepared() -> Arc<SsaArtifact> {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        Arc::new(SsaArtifact::for_symbolic(&[block], None).expect("test SSA"))
    }

    fn bind_test_report(report: SemanticArtifactReport) -> SemanticArtifact {
        SemanticArtifact::new(test_prepared(), report).expect("current query test semantic schema")
    }

    fn test_semantic_artifact_for(
        prepared: Arc<SsaArtifact>,
        stage: RefinementStage,
        slice_class: SliceClass,
        residual_reasons: Vec<ResidualReason>,
        regions: Vec<SemanticRegion>,
        diagnostics: SemanticArtifactDiagnostics,
    ) -> SemanticArtifact {
        let regions: BTreeMap<RegionKey, SemanticRegion> = regions
            .into_iter()
            .map(|region| {
                (
                    RegionKey::new(region.anchor, region.frontier.clone()),
                    region,
                )
            })
            .collect();
        let granularity = if matches!(stage, RefinementStage::Compiled | RefinementStage::Residual)
            && !regions.is_empty()
        {
            ArtifactGranularity::Regioned
        } else {
            ArtifactGranularity::WholeFunction
        };
        SemanticArtifact::new(
            prepared,
            SemanticArtifactReport {
                schema_version: crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
                stage,
                granularity,
                execution: ExecutionModel::Native,
                body: SemanticArtifactBody::Native(NativeArtifactBody {
                    summary: NativeFunctionSummary {
                        slice_class,
                        role_identity: None,
                        closure_functions: 0,
                        helper_functions: 0,
                        derived_summaries: 0,
                        derived_diagnostics: crate::sim::DerivedSummaryDiagnostics::default(),
                        region_summaries: Vec::new(),
                        worker_summaries: Vec::new(),
                    },
                    regions,
                }),
                diagnostics: SemanticArtifactDiagnostics {
                    residual_reasons,
                    ..diagnostics
                },
            },
        )
        .expect("current query test semantic schema")
    }

    fn test_semantic_artifact(
        stage: RefinementStage,
        slice_class: SliceClass,
        residual_reasons: Vec<ResidualReason>,
        regions: Vec<SemanticRegion>,
        diagnostics: SemanticArtifactDiagnostics,
    ) -> SemanticArtifact {
        test_semantic_artifact_for(
            test_prepared(),
            stage,
            slice_class,
            residual_reasons,
            regions,
            diagnostics,
        )
    }

    fn make_region(anchor: u64, frontier: &[u64]) -> SemanticRegion {
        SemanticRegion {
            anchor,
            frontier: frontier.iter().copied().collect(),
            control: Vec::new(),
            memory: Vec::new(),
            pre: Vec::new(),
            post: Vec::new(),
            targets: Vec::new(),
        }
    }

    fn default_diagnostics() -> SemanticArtifactDiagnostics {
        SemanticArtifactDiagnostics {
            branches_evaluated: 0,
            branches_pruned: 0,
            branches_unknown: 0,
            skipped_missing_arch: false,
            skipped_large_cfg: false,
            residual_reasons: Vec::new(),
            interpreter: None,
            ambiguous_targets: Vec::new(),
        }
    }

    #[test]
    fn target_query_drops_semantics_from_rebuilt_identical_ssa() {
        let blocks = make_residual_precondition_blocks();
        let requested = Arc::new(SsaArtifact::for_symbolic(&blocks, None).expect("requested SSA"));
        let rebuilt = Arc::new(SsaArtifact::for_symbolic(&blocks, None).expect("rebuilt SSA"));
        let mut region = make_region(0x1000, &[0x1010, 0x1004]);
        region.control.push(Judged::new(
            ControlFact {
                target: 0x1010,
                status: crate::SymbolicReachabilityStatus::Reachable,
                branch_truth: Some(true),
                condition: Some("guard".to_string()),
                compiled: Some(BackwardConditionSummary {
                    simplified: "guard".to_string(),
                    terms: vec!["guard".to_string()],
                    memory_terms: Vec::new(),
                    backward_memory_substitutions: 0,
                    backward_memory_candidate_enumerations: 0,
                    backward_memory_residual_fallbacks: 0,
                    precision: BackwardConditionPrecision::Exact,
                    supported_paths: 1,
                    total_paths: 1,
                }),
            },
            SemanticEvidence::exact(),
        ));
        region.targets.push(Judged::new(
            TargetFact {
                target: 0x1010,
                status: crate::SymbolicReachabilityStatus::Reachable,
                branch_truth: Some(true),
            },
            SemanticEvidence::exact(),
        ));
        let artifact = test_semantic_artifact_for(
            Arc::clone(&requested),
            RefinementStage::Compiled,
            SliceClass::Worker,
            Vec::new(),
            vec![region],
            default_diagnostics(),
        );
        let ctx = Context::thread_local();
        let mut explorer = SymQueryConfig::default().make_explorer(&ctx);

        let exact = super::build_target_query_inputs(
            &mut explorer,
            &requested,
            None,
            Some(&artifact),
            0x1010,
            false,
            false,
        )
        .route;
        assert!(matches!(
            exact.execution,
            TargetQueryExecutionRoute::ArtifactCondition { .. }
        ));

        let foreign = super::build_target_query_inputs(
            &mut explorer,
            &rebuilt,
            None,
            Some(&artifact),
            0x1010,
            false,
            false,
        )
        .route;
        assert_eq!(foreign, crate::TargetQueryRoutePlan::dynamic_fallback());
    }

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    fn make_residual_precondition_blocks() -> Vec<R2ILBlock> {
        vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::IntEqual {
                        dst: make_reg(TMP0, 1),
                        a: make_reg(RDI, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(TMP0, 1),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::IntCarry {
                        dst: make_reg(TMP1, 1),
                        a: make_reg(RDI, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(TMP1, 1),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1008,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
            },
        ]
    }

    fn make_bounded_copy_loop_blocks() -> Vec<R2ILBlock> {
        vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Load {
                        dst: make_reg(TMP0, 1),
                        space: SpaceId::Ram,
                        addr: make_const(0x2000, 8),
                    },
                    R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: make_const(0x3000, 8),
                        val: make_reg(TMP0, 1),
                    },
                    R2ILOp::IntLess {
                        dst: make_reg(TMP1, 1),
                        a: make_reg(RDI, 8),
                        b: make_const(0x1000, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1000, 8),
                        cond: make_reg(TMP1, 1),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
            },
        ]
    }

    fn make_vm_step_summary_with_transfers(transfers: Vec<VmTransferArm>) -> VmStepSummary {
        VmStepSummary {
            kind: crate::InterpreterKind::SwitchDispatch,
            loop_header: 0x1000,
            dispatch_header: 0x1000,
            selector: Some("RDI_0".to_string()),
            dispatch_targets: vec![0x1004, 0x1008, 0x1010],
            default_target: Some(0x1010),
            case_values_by_target: BTreeMap::from([
                (0x1004, vec![0]),
                (0x1008, vec![1]),
                (0x1010, vec![2]),
            ]),
            loop_latches: vec![0x1000],
            state_inputs: vec!["RDI_0".to_string()],
            state_outputs: vec!["RDI_1".to_string()],
            step_blocks: vec![0x1000, 0x1004, 0x1008, 0x1010],
            handler_regions: BTreeMap::new(),
            handler_state_inputs: BTreeMap::new(),
            handler_state_outputs: BTreeMap::new(),
            handler_state_updates: BTreeMap::new(),
            handler_exit_guards: BTreeMap::new(),
            handler_memory_read_effects: BTreeMap::new(),
            handler_memory_write_effects: BTreeMap::new(),
            handler_memory_reads: BTreeMap::new(),
            handler_memory_writes: BTreeMap::new(),
            handler_calls: BTreeMap::new(),
            handler_conditional_branches: BTreeMap::new(),
            handler_exit_targets: BTreeMap::new(),
            redispatch_handlers: Vec::new(),
            returning_handlers: Vec::new(),
            truncated_handlers: Vec::new(),
            transfers,
        }
    }

    #[test]
    fn residual_compiled_preconditions_do_not_constrain_forward_search() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);

        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let original_constraints = state.num_constraints();
        match apply_best_compiled_precondition(&explorer, &func, None, state, 0x1010, false) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition: _,
                ..
            } => {
                assert_eq!(initial_state.num_constraints(), original_constraints);
                assert!(narrowed_state.is_none());
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("residual precondition should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn non_local_targets_skip_dynamic_precondition_compile() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);

        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let original_constraints = state.num_constraints();
        match apply_best_compiled_precondition(&explorer, &func, None, state, 0x4000, false) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(compiled_precondition.is_none());
                assert!(narrowed_state.is_none());
                assert_eq!(initial_state.num_constraints(), original_constraints);
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("non-local targets should bypass dynamic backward compilation")
            }
        }
    }

    #[test]
    fn register_assumptions_condition_query_results() {
        let blocks = make_residual_precondition_blocks();
        let base = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let reg_name = base
            .graph()
            .values
            .iter()
            .find(|value| value.var.version == 0 && value.var.is_register() && value.var.size == 8)
            .expect("version-zero input register")
            .var
            .name
            .clone();
        let func = base.with_assumptions(&AssumptionSet::new(vec![AnalysisAssumption {
            id: Some("force-rdi".to_string()),
            subject: AssumptionSubject::Register { name: reg_name },
            value: AssumptionValue::Constant { value: 1 },
            scope: AssumptionScope::Query,
            provenance: AssumptionProvenance::User,
        }]));
        let (state_name, bits) = func
            .facts()
            .applied_assumption_bindings
            .iter()
            .find_map(|binding| match &binding.binding {
                r2ssa::PreparedAssumptionBindingKind::Register {
                    state_name, bits, ..
                } => Some((state_name.clone(), *bits)),
                _ => None,
            })
            .expect("register assumption binding");
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic(&state_name, bits);

        let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
        let reach = explorer.can_reach(&func, state, 0x1010);
        assert_eq!(reach.status, super::ReachabilityStatus::Reachable);
        assert!(reach.assumption_conditioned);
        assert!(!reach.summary_conditioned);
        assert_eq!(reach.assumption_usage.applied.len(), 1);
        assert!(reach.assumption_usage.ignored.is_empty());
        assert!(reach.assumption_usage.conflicts.is_empty());
        assert!(matches!(
            reach.assumption_usage.applied[0].value,
            AssumptionValue::Constant { value: 1 }
        ));
    }

    #[test]
    fn likely_compiled_preconditions_seed_narrowed_search_state() {
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);
        let original_constraints = state.num_constraints();

        let compiled = crate::CompiledBackwardCondition {
            predicate: z3::ast::Bool::from_bool(true),
            summary: BackwardConditionSummary {
                simplified: "guard".to_string(),
                terms: vec!["guard".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: BackwardConditionPrecision::OverApprox,
                supported_paths: 1,
                total_paths: 2,
            },
        };

        match apply_compiled_precondition_with_mode(
            &explorer,
            state,
            compiled,
            CompiledPreconditionMode::Necessary,
            true,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                let compiled = compiled_precondition.expect("compiled precondition");
                assert_eq!(compiled.precision, BackwardConditionPrecision::OverApprox);
                assert_eq!(initial_state.num_constraints(), original_constraints);
                assert_eq!(
                    narrowed_state.expect("narrowed state").num_constraints(),
                    original_constraints + 1
                );
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("likely precondition should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn exact_preconditions_in_narrow_only_mode_do_not_shortcut_unsat() {
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);

        let compiled = crate::CompiledBackwardCondition {
            predicate: z3::ast::Bool::from_bool(false),
            summary: BackwardConditionSummary {
                simplified: "guard".to_string(),
                terms: vec!["guard".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            },
        };

        match apply_compiled_precondition_with_mode(
            &explorer,
            state,
            compiled,
            CompiledPreconditionMode::NarrowOnly,
            true,
        ) {
            PreconditionApplication::Continue {
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(narrowed_state.is_none());
                assert_eq!(
                    compiled_precondition
                        .expect("compiled precondition")
                        .precision,
                    BackwardConditionPrecision::Exact
                );
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("narrow-only exact precondition should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn exact_preconditions_in_narrow_only_mode_seed_narrowed_state() {
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);
        let original_constraints = state.num_constraints();

        let compiled = crate::CompiledBackwardCondition {
            predicate: z3::ast::Bool::from_bool(true),
            summary: BackwardConditionSummary {
                simplified: "guard".to_string(),
                terms: vec!["guard".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            },
        };

        match apply_compiled_precondition_with_mode(
            &explorer,
            state,
            compiled,
            CompiledPreconditionMode::NarrowOnly,
            true,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert_eq!(initial_state.num_constraints(), original_constraints);
                assert_eq!(
                    narrowed_state.expect("narrowed state").num_constraints(),
                    original_constraints + 1
                );
                assert_eq!(
                    compiled_precondition
                        .expect("compiled precondition")
                        .precision,
                    BackwardConditionPrecision::Exact
                );
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("narrow-only exact precondition should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn exact_preconditions_disable_unsat_shortcuts_when_exact_proof_is_disallowed() {
        let ctx = Context::thread_local();
        let state = SymState::new(&ctx, 0x1000);
        let explorer = SymQueryConfig::default().make_explorer(&ctx);

        let compiled = crate::CompiledBackwardCondition {
            predicate: z3::ast::Bool::from_bool(false),
            summary: BackwardConditionSummary {
                simplified: "guard".to_string(),
                terms: vec!["guard".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            },
        };
        match apply_compiled_precondition_with_mode(
            &explorer,
            state,
            compiled,
            CompiledPreconditionMode::Necessary,
            false,
        ) {
            PreconditionApplication::Continue {
                compiled_precondition,
                ..
            } => {
                assert_eq!(
                    compiled_precondition
                        .expect("compiled precondition")
                        .precision,
                    BackwardConditionPrecision::Exact
                );
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("exact-proof downgrade must disable exact unsat shortcuts")
            }
        }
    }

    #[test]
    fn bounded_copy_loops_raise_recommended_query_max_depth() {
        let blocks = make_bounded_copy_loop_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let state = SymState::new(&ctx, 0x1000);

        let budget = super::recommended_query_max_depth(&func, &state);

        assert!(
            budget >= 16_384,
            "bounded copy loop budget should scale with trip count, got {budget}"
        );
    }

    #[test]
    fn bounded_copy_loops_raise_recommended_query_timeout() {
        let blocks = make_bounded_copy_loop_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");

        assert!(
            super::recommended_query_timeout(&func) >= std::time::Duration::from_secs(120),
            "bounded copy loop timeout should exceed default budget"
        );
    }

    #[test]
    fn continuation_seeded_routes_cap_recommended_query_max_depth() {
        let blocks = make_bounded_copy_loop_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let state = SymState::new(&ctx, 0x1000);
        let route = crate::TargetQueryRoutePlan {
            target_plan: crate::TargetQueryPlan::Ready {
                mode: crate::QueryGuidanceMode::NarrowOnly,
            },
            execution: crate::TargetQueryExecutionRoute::ContinuationSeeded {
                bridge_target: 0x1010,
                route: Box::new(crate::TargetQueryExecutionRoute::DynamicTargetCompile {
                    reason: "test".to_string(),
                    mode: crate::QueryGuidanceMode::NarrowOnly,
                }),
            },
        };

        let budget = super::recommended_query_max_depth_for_route(&func, &state, Some(&route));

        assert!(
            budget <= super::CONTINUATION_QUERY_MAX_DEPTH_CAP,
            "continuation-seeded route should cap inflated depth budget, got {budget}"
        );
    }

    #[test]
    fn continuation_seeded_routes_cap_recommended_query_max_states() {
        let route = crate::TargetQueryRoutePlan {
            target_plan: crate::TargetQueryPlan::Ready {
                mode: crate::QueryGuidanceMode::NarrowOnly,
            },
            execution: crate::TargetQueryExecutionRoute::ContinuationSeeded {
                bridge_target: 0x1010,
                route: Box::new(crate::TargetQueryExecutionRoute::DynamicTargetCompile {
                    reason: "test".to_string(),
                    mode: crate::QueryGuidanceMode::NarrowOnly,
                }),
            },
        };

        let max_states = super::recommended_query_max_states_for_route(1_000, Some(&route));

        assert_eq!(max_states, super::CONTINUATION_QUERY_MAX_STATES_CAP);
    }

    #[test]
    fn continuation_seeded_routes_cap_recommended_query_timeout() {
        let blocks = make_bounded_copy_loop_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let route = crate::TargetQueryRoutePlan {
            target_plan: crate::TargetQueryPlan::Ready {
                mode: crate::QueryGuidanceMode::NarrowOnly,
            },
            execution: crate::TargetQueryExecutionRoute::ContinuationSeeded {
                bridge_target: 0x1010,
                route: Box::new(crate::TargetQueryExecutionRoute::DynamicTargetCompile {
                    reason: "test".to_string(),
                    mode: crate::QueryGuidanceMode::NarrowOnly,
                }),
            },
        };

        let timeout = super::recommended_query_timeout_for_route(&func, Some(&route));

        assert!(
            timeout <= std::time::Duration::from_secs(30),
            "continuation-seeded route should cap inflated timeout, got {timeout:?}"
        );
    }

    #[test]
    fn continuation_followup_downgrades_dynamic_target_compile() {
        let route = crate::TargetQueryExecutionRoute::DynamicTargetCompile {
            reason: "LargeCfg".to_string(),
            mode: crate::QueryGuidanceMode::NarrowOnly,
        };

        match super::continuation_followup_execution_route(&route) {
            crate::TargetQueryExecutionRoute::ResidualOnly { reasons } => {
                assert!(
                    reasons
                        .iter()
                        .any(|reason| reason.contains("dynamic target compile")),
                    "expected dynamic compile downgrade reason, got {reasons:?}"
                );
            }
            other => panic!("expected residual-only continuation follow-up, got {other:?}"),
        }
    }

    #[test]
    fn continuation_followup_keeps_artifact_guided_routes() {
        let route = crate::TargetQueryExecutionRoute::ArtifactCondition {
            mode: crate::QueryGuidanceMode::Necessary,
        };

        assert_eq!(super::continuation_followup_execution_route(&route), route);
    }

    #[test]
    fn artifact_memory_terms_seed_narrowed_state_without_branch_recompile() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.new_symbolic_input("sym_mem", 8);
        let original_constraints = state.num_constraints();
        let target_term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Argument { index: 0 },
            address: crate::SemanticMemoryAddress::exact(0),
            size: 1,
            evidence: SemanticEvidence::exact(),
            binding: Some("sym_mem".to_string()),
            expr: "0x2a".to_string(),
            value_expr: Some("0x2a".to_string()),
            exact_value: true,
        };
        let other_branch_term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Argument { index: 0 },
            address: crate::SemanticMemoryAddress::exact(0),
            size: 1,
            evidence: SemanticEvidence::exact(),
            binding: Some("sym_mem".to_string()),
            expr: "0x2b".to_string(),
            value_expr: Some("0x2b".to_string()),
            exact_value: true,
        };

        let artifact = test_semantic_artifact(
            RefinementStage::Residual,
            SliceClass::Worker,
            vec![ResidualReason::LargeCfg],
            vec![{
                let mut region = make_region(0xdead, &[0x2000, 0x2010]);
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x2000,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "guard".to_string(),
                            terms: vec!["guard".to_string()],
                            memory_terms: vec![target_term.clone()],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x2010,
                        status: crate::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                        condition: Some("!guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "!guard".to_string(),
                            terms: vec!["!guard".to_string()],
                            memory_terms: vec![other_branch_term.clone()],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.targets.push(Judged::new(
                    TargetFact {
                        target: 0x2000,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                    },
                    SemanticEvidence::exact(),
                ));
                region.targets.push(Judged::new(
                    TargetFact {
                        target: 0x2010,
                        status: crate::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                    },
                    SemanticEvidence::exact(),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: target_term.clone(),
                    },
                    SemanticEvidence::exact(),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: other_branch_term.clone(),
                    },
                    SemanticEvidence::exact(),
                ));
                region
            }],
            default_diagnostics(),
        );

        match apply_best_compiled_precondition(
            &explorer,
            &func,
            Some(&artifact),
            state,
            0x2000,
            false,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(compiled_precondition.is_none());
                assert_eq!(initial_state.num_constraints(), original_constraints);
                let narrowed_state = narrowed_state.expect("narrowed state");
                assert_eq!(narrowed_state.num_constraints(), original_constraints + 1);
                let narrowed_value = narrowed_state
                    .symbolic_inputs()
                    .get("sym_mem")
                    .expect("symbolic input")
                    .to_bv(&ctx);
                assert!(matches!(
                    explorer.solver().sat_with_constraint(
                        &narrowed_state,
                        &narrowed_value.eq(BV::from_u64(0x2a, 8))
                    ),
                    SatResult::Sat
                ));
                assert!(matches!(
                    explorer.solver().sat_with_constraint(
                        &narrowed_state,
                        &narrowed_value.eq(BV::from_u64(0x2b, 8))
                    ),
                    SatResult::Unsat
                ));
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("memory-term-only narrowing should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn artifact_region_memory_terms_seed_narrowed_state_without_symbolic_binding() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        let symbolic_byte = state.new_symbolic_input("global_byte", 8);
        let global_region = state.define_memory_region(
            crate::MemoryRegionKind::Global,
            "ram:0x2000",
            Some(0x2000),
            Some(1),
        );
        state.mem_write(&crate::SymValue::concrete(0x2000, 64), &symbolic_byte, 1);
        let original_constraints = state.num_constraints();
        let target_term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Region(crate::backward::BackwardRegionRef {
                id: global_region,
                kind: crate::MemoryRegionKind::Global,
                name: "ram:0x2000".to_string(),
            }),
            address: crate::SemanticMemoryAddress::exact(0),
            size: 1,
            evidence: SemanticEvidence::exact(),
            binding: None,
            expr: "*(ram:0x2000 + 0)".to_string(),
            value_expr: Some("0x2a".to_string()),
            exact_value: true,
        };
        let other_branch_term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Region(crate::backward::BackwardRegionRef {
                id: global_region,
                kind: crate::MemoryRegionKind::Global,
                name: "ram:0x2000".to_string(),
            }),
            address: crate::SemanticMemoryAddress::exact(0),
            size: 1,
            evidence: SemanticEvidence::exact(),
            binding: None,
            expr: "*(ram:0x2000 + 0)".to_string(),
            value_expr: Some("0x2b".to_string()),
            exact_value: true,
        };

        let artifact = test_semantic_artifact(
            RefinementStage::Residual,
            SliceClass::Worker,
            vec![ResidualReason::LargeCfg],
            vec![{
                let mut region = make_region(0xdead, &[0x2000, 0x2010]);
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x2000,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "guard".to_string(),
                            terms: vec!["guard".to_string()],
                            memory_terms: vec![target_term.clone()],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x2010,
                        status: crate::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                        condition: Some("!guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "!guard".to_string(),
                            terms: vec!["!guard".to_string()],
                            memory_terms: vec![other_branch_term.clone()],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.targets.push(Judged::new(
                    TargetFact {
                        target: 0x2000,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                    },
                    SemanticEvidence::exact(),
                ));
                region.targets.push(Judged::new(
                    TargetFact {
                        target: 0x2010,
                        status: crate::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                    },
                    SemanticEvidence::exact(),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: target_term.clone(),
                    },
                    SemanticEvidence::exact(),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: other_branch_term.clone(),
                    },
                    SemanticEvidence::exact(),
                ));
                region
            }],
            default_diagnostics(),
        );

        match apply_best_compiled_precondition(
            &explorer,
            &func,
            Some(&artifact),
            state,
            0x2000,
            false,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(compiled_precondition.is_none());
                assert_eq!(initial_state.num_constraints(), original_constraints);
                let narrowed_state = narrowed_state.expect("narrowed state");
                assert_eq!(narrowed_state.num_constraints(), original_constraints + 1);
                let narrowed_value = narrowed_state
                    .mem_read(&crate::SymValue::concrete(0x2000, 64), 1)
                    .to_bv(&ctx);
                assert!(matches!(
                    explorer.solver().sat_with_constraint(
                        &narrowed_state,
                        &narrowed_value.eq(BV::from_u64(0x2a, 8))
                    ),
                    SatResult::Sat
                ));
                assert!(matches!(
                    explorer.solver().sat_with_constraint(
                        &narrowed_state,
                        &narrowed_value.eq(BV::from_u64(0x2b, 8))
                    ),
                    SatResult::Unsat
                ));
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("region-backed memory-term narrowing should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn affine_region_memory_term_refuses_concrete_seed_without_index_value() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let symbolic_byte = state.new_symbolic_input("global_byte", 8);
        let global_region = state.define_memory_region(
            crate::MemoryRegionKind::Global,
            "ram:0x2000",
            Some(0x2000),
            Some(1),
        );
        state.mem_write(&crate::SymValue::concrete(0x2000, 64), &symbolic_byte, 1);
        let original_constraints = state.num_constraints();
        let term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Region(crate::backward::BackwardRegionRef {
                id: global_region,
                kind: crate::MemoryRegionKind::Global,
                name: "ram:0x2000".to_string(),
            }),
            address: crate::SemanticMemoryAddress::affine(
                vec![r2ssa::AffineAddressTerm {
                    value: ValueId(7),
                    coefficient: 40,
                }],
                4,
            )
            .expect("valid affine address"),
            size: 1,
            evidence: SemanticEvidence::exact(),
            binding: None,
            expr: "*(ram:0x2000 + 40*v7 + 4)".to_string(),
            value_expr: Some("0x2a".to_string()),
            exact_value: true,
        };

        assert!(term.has_exact_address());
        assert!(!super::constrain_region_backed_memory_term(
            &mut state, &term, 0x2a
        ));
        assert_eq!(state.num_constraints(), original_constraints);
    }

    #[test]
    fn unrepresentable_bounded_memory_span_refuses_narrowing() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        let global_region = state.define_memory_region(
            crate::MemoryRegionKind::Global,
            "ram:0x2000",
            Some(0x2000),
            None,
        );
        let original_constraints = state.num_constraints();
        let term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Region(crate::backward::BackwardRegionRef {
                id: global_region,
                kind: crate::MemoryRegionKind::Global,
                name: "ram:0x2000".to_string(),
            }),
            address: crate::SemanticMemoryAddress::bounded(i64::MIN, i64::MAX)
                .expect("ordered bounds"),
            size: 1,
            evidence: SemanticEvidence::likely(SemanticEvidenceReason::AliasAmbiguity),
            binding: None,
            expr: "*(ram:0x2000 + unknown)".to_string(),
            value_expr: Some("0x2a".to_string()),
            exact_value: true,
        };

        assert!(!super::constrain_region_backed_memory_term(
            &mut state, &term, 0x2a
        ));
        assert_eq!(state.num_constraints(), original_constraints);
    }

    #[test]
    fn region_memory_bag_without_target_local_compiled_memory_does_not_seed_narrowed_state() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.new_symbolic_input("sym_mem", 8);
        let original_constraints = state.num_constraints();

        let artifact = test_semantic_artifact(
            RefinementStage::Residual,
            SliceClass::Worker,
            vec![ResidualReason::LargeCfg],
            vec![{
                let mut region = make_region(0xdead, &[0x2000, 0x2010]);
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x2000,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "guard".to_string(),
                            terms: vec!["guard".to_string()],
                            memory_terms: Vec::new(),
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: BackwardMemoryCondition {
                            region: BackwardMemoryRegion::Argument { index: 0 },
                            address: crate::SemanticMemoryAddress::exact(0),
                            size: 1,
                            evidence: SemanticEvidence::exact(),
                            binding: Some("sym_mem".to_string()),
                            expr: "0x2a".to_string(),
                            value_expr: Some("0x2a".to_string()),
                            exact_value: true,
                        },
                    },
                    SemanticEvidence::exact(),
                ));
                region
            }],
            default_diagnostics(),
        );

        match apply_best_compiled_precondition(
            &explorer,
            &func,
            Some(&artifact),
            state,
            0x2000,
            false,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(compiled_precondition.is_none());
                assert_eq!(initial_state.num_constraints(), original_constraints);
                assert!(narrowed_state.is_none());
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("region-bag-only memory facts should not seed targeted narrowing")
            }
        }
    }

    #[test]
    fn worker_island_memory_terms_seed_narrowed_state_without_branch_recompile() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.new_symbolic_input("sym_mem", 8);
        let original_constraints = state.num_constraints();
        let target_term = BackwardMemoryCondition {
            region: BackwardMemoryRegion::Argument { index: 0 },
            address: crate::SemanticMemoryAddress::exact(0),
            size: 1,
            evidence: SemanticEvidence::exact(),
            binding: Some("sym_mem".to_string()),
            expr: "0x2a".to_string(),
            value_expr: Some("0x2a".to_string()),
            exact_value: true,
        };

        let actionable = BackwardConditionSummary {
            simplified: "worker_guard".to_string(),
            terms: vec!["worker_guard".to_string()],
            memory_terms: vec![target_term.clone()],
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::OverApprox,
            supported_paths: 1,
            total_paths: 2,
        };
        let artifact = test_semantic_artifact(
            RefinementStage::Compiled,
            SliceClass::Worker,
            Vec::new(),
            vec![{
                let mut region = make_region(0xdead, &[0x2000, 0x2010]);
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x2000,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: None,
                        condition: Some("worker_guard".to_string()),
                        compiled: Some(actionable.clone()),
                    },
                    SemanticEvidence::likely(SemanticEvidenceReason::DerivedFromRanking),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: target_term.clone(),
                    },
                    SemanticEvidence::exact(),
                ));
                region
            }],
            default_diagnostics(),
        );

        match apply_best_compiled_precondition(
            &explorer,
            &func,
            Some(&artifact),
            state,
            0x2000,
            false,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition: _,
                ..
            } => {
                assert_eq!(initial_state.num_constraints(), original_constraints);
                let narrowed_state = narrowed_state.expect("narrowed state");
                assert_eq!(narrowed_state.num_constraints(), original_constraints + 1);
                let narrowed_value = narrowed_state
                    .symbolic_inputs()
                    .get("sym_mem")
                    .expect("symbolic input")
                    .to_bv(&ctx);
                assert!(matches!(
                    explorer.solver().sat_with_constraint(
                        &narrowed_state,
                        &narrowed_value.eq(BV::from_u64(0x2a, 8))
                    ),
                    SatResult::Sat
                ));
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("worker-island memory narrowing should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn necessary_worker_island_still_prefers_real_compiled_precondition() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);
        let original_constraints = state.num_constraints();

        let artifact = test_semantic_artifact(
            RefinementStage::Compiled,
            SliceClass::Worker,
            Vec::new(),
            vec![{
                let mut region = make_region(0x1000, &[0x1010, 0x1004]);
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x1010,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: None,
                        condition: Some("guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "guard".to_string(),
                            terms: vec!["guard".to_string()],
                            memory_terms: Vec::new(),
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x1004,
                        status: crate::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: None,
                        condition: None,
                        compiled: None,
                    },
                    SemanticEvidence::exact(),
                ));
                region.memory.push(Judged::new(
                    MemoryFact {
                        term: BackwardMemoryCondition {
                            region: BackwardMemoryRegion::Argument { index: 0 },
                            address: crate::SemanticMemoryAddress::exact(0),
                            size: 1,
                            evidence: SemanticEvidence::exact(),
                            binding: Some("reg:56_0".to_string()),
                            expr: "0x1".to_string(),
                            value_expr: Some("0x1".to_string()),
                            exact_value: true,
                        },
                    },
                    SemanticEvidence::exact(),
                ));
                region
            }],
            default_diagnostics(),
        );

        match apply_best_compiled_precondition(
            &explorer,
            &func,
            Some(&artifact),
            state,
            0x1010,
            false,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(initial_state.num_constraints() >= original_constraints);
                assert!(narrowed_state.is_none());
                assert!(compiled_precondition.is_some());
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("necessary worker islands should use the real compiled precondition path")
            }
        }
    }

    #[test]
    fn target_condition_source_only_marks_unique_region_targets_as_necessary() {
        let artifact = test_semantic_artifact(
            RefinementStage::Compiled,
            SliceClass::Worker,
            Vec::new(),
            vec![{
                let mut region = make_region(0x1000, &[0x1010, 0x1004]);
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x1010,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("guard".to_string()),
                        compiled: Some(BackwardConditionSummary {
                            simplified: "guard".to_string(),
                            terms: vec!["guard".to_string()],
                            memory_terms: Vec::new(),
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    SemanticEvidence::exact(),
                ));
                region.control.push(Judged::new(
                    ControlFact {
                        target: 0x1004,
                        status: crate::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(false),
                        condition: Some("other_guard".to_string()),
                        compiled: None,
                    },
                    SemanticEvidence::exact(),
                ));
                region
            }],
            default_diagnostics(),
        );

        let actionable = artifact
            .target_condition_source(0x1010, false)
            .expect("actionable target condition source");
        assert!(
            matches!(
                artifact.target_query_plan(0x1010),
                crate::TargetQueryPlan::Ready {
                    mode: crate::QueryGuidanceMode::NarrowOnly
                }
            ),
            "multi-exit regions must not be treated as necessary-for-target"
        );
        assert_eq!(actionable.block_addr, 0x1000);
        assert!(
            artifact.target_condition_source(0x1010, true).is_none(),
            "hard-proof target narrowing must reject non-necessary regions"
        );
    }

    #[test]
    fn target_local_memory_terms_follow_the_authoritative_target_source_region() {
        let exact = SemanticEvidence::exact();
        let likely = SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage);
        let artifact = test_semantic_artifact(
            RefinementStage::Compiled,
            SliceClass::Worker,
            Vec::new(),
            vec![
                {
                    let mut region = make_region(0x1000, &[0x1010]);
                    region.control.push(Judged::new(
                        ControlFact {
                            target: 0x1010,
                            status: crate::SymbolicReachabilityStatus::Reachable,
                            branch_truth: Some(true),
                            condition: Some("exact_guard".to_string()),
                            compiled: Some(BackwardConditionSummary {
                                simplified: "exact_guard".to_string(),
                                terms: vec!["exact_guard".to_string()],
                                memory_terms: vec![BackwardMemoryCondition {
                                    region: BackwardMemoryRegion::Argument { index: 0 },
                                    address: crate::SemanticMemoryAddress::exact(0),
                                    size: 1,
                                    evidence: exact.clone(),
                                    binding: Some("sym_mem".to_string()),
                                    expr: "0x2a".to_string(),
                                    value_expr: Some("0x2a".to_string()),
                                    exact_value: true,
                                }],
                                backward_memory_substitutions: 0,
                                backward_memory_candidate_enumerations: 0,
                                backward_memory_residual_fallbacks: 0,
                                precision: BackwardConditionPrecision::Exact,
                                supported_paths: 1,
                                total_paths: 1,
                            }),
                        },
                        exact.clone(),
                    ));
                    region
                },
                {
                    let mut region = make_region(0x1004, &[0x1010]);
                    region.control.push(Judged::new(
                        ControlFact {
                            target: 0x1010,
                            status: crate::SymbolicReachabilityStatus::Reachable,
                            branch_truth: Some(true),
                            condition: Some("weaker_guard".to_string()),
                            compiled: Some(BackwardConditionSummary {
                                simplified: "weaker_guard".to_string(),
                                terms: vec!["weaker_guard".to_string()],
                                memory_terms: vec![BackwardMemoryCondition {
                                    region: BackwardMemoryRegion::Argument { index: 0 },
                                    address: crate::SemanticMemoryAddress::exact(0),
                                    size: 1,
                                    evidence: likely.clone(),
                                    binding: Some("sym_mem".to_string()),
                                    expr: "0x2b".to_string(),
                                    value_expr: Some("0x2b".to_string()),
                                    exact_value: true,
                                }],
                                backward_memory_substitutions: 0,
                                backward_memory_candidate_enumerations: 0,
                                backward_memory_residual_fallbacks: 0,
                                precision: BackwardConditionPrecision::OverApprox,
                                supported_paths: 1,
                                total_paths: 2,
                            }),
                        },
                        likely.clone(),
                    ));
                    region
                },
            ],
            default_diagnostics(),
        );

        assert!(matches!(
            artifact.target_query_plan(0x1010),
            crate::TargetQueryPlan::Residual { .. }
        ));
        let route = artifact.target_query_route_plan(0x1010);
        assert!(matches!(
            route.target_plan,
            TargetQueryPlan::Residual { .. }
        ));
        assert!(matches!(
            route.execution,
            TargetQueryExecutionRoute::ResidualOnly { .. }
        ));
        assert!(
            artifact.target_condition_source(0x1010, false).is_none(),
            "materially conflicting target sources must not collapse into one authoritative source"
        );
        let memory_terms = artifact.actionable_memory_terms_for_target(0x1010);
        assert!(
            memory_terms.is_empty(),
            "materially conflicting target-local memory terms must refuse narrowing"
        );
    }

    #[test]
    fn weaker_secondary_target_source_does_not_seed_narrowing() {
        let blocks = make_residual_precondition_blocks();
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let explorer = SymQueryConfig::default().make_explorer(&ctx);
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);
        state.new_symbolic_input("sym_mem", 8);

        let exact = SemanticEvidence::exact();
        let likely = SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage);
        let artifact = test_semantic_artifact(
            RefinementStage::Compiled,
            SliceClass::Worker,
            Vec::new(),
            vec![
                {
                    let mut region = make_region(0x1000, &[0x1010, 0x1004]);
                    region.control.push(Judged::new(
                        ControlFact {
                            target: 0x1010,
                            status: crate::SymbolicReachabilityStatus::Reachable,
                            branch_truth: Some(true),
                            condition: Some("guard".to_string()),
                            compiled: Some(BackwardConditionSummary {
                                simplified: "guard".to_string(),
                                terms: vec!["guard".to_string()],
                                memory_terms: Vec::new(),
                                backward_memory_substitutions: 0,
                                backward_memory_candidate_enumerations: 0,
                                backward_memory_residual_fallbacks: 0,
                                precision: BackwardConditionPrecision::Exact,
                                supported_paths: 1,
                                total_paths: 1,
                            }),
                        },
                        exact.clone(),
                    ));
                    region
                },
                {
                    let mut region = make_region(0x1004, &[0x1010, 0x1008]);
                    region.control.push(Judged::new(
                        ControlFact {
                            target: 0x1010,
                            status: crate::SymbolicReachabilityStatus::Reachable,
                            branch_truth: Some(true),
                            condition: Some("worker_guard".to_string()),
                            compiled: Some(BackwardConditionSummary {
                                simplified: "worker_guard".to_string(),
                                terms: vec!["worker_guard".to_string()],
                                memory_terms: vec![BackwardMemoryCondition {
                                    region: BackwardMemoryRegion::Argument { index: 0 },
                                    address: crate::SemanticMemoryAddress::exact(0),
                                    size: 1,
                                    evidence: likely.clone(),
                                    binding: Some("sym_mem".to_string()),
                                    expr: "0x2a".to_string(),
                                    value_expr: Some("0x2a".to_string()),
                                    exact_value: true,
                                }],
                                backward_memory_substitutions: 0,
                                backward_memory_candidate_enumerations: 0,
                                backward_memory_residual_fallbacks: 0,
                                precision: BackwardConditionPrecision::OverApprox,
                                supported_paths: 1,
                                total_paths: 2,
                            }),
                        },
                        likely.clone(),
                    ));
                    region
                },
            ],
            default_diagnostics(),
        );

        match apply_best_compiled_precondition(
            &explorer,
            &func,
            Some(&artifact),
            state,
            0x1010,
            false,
        ) {
            PreconditionApplication::Continue {
                initial_state,
                narrowed_state,
                compiled_precondition,
                ..
            } => {
                assert!(compiled_precondition.is_none());
                assert!(
                    narrowed_state.is_none(),
                    "conflicting source regions must refuse targeted narrowing"
                );
                let sym_mem = initial_state
                    .symbolic_inputs()
                    .get("sym_mem")
                    .expect("symbolic input")
                    .to_bv(&ctx);
                assert!(matches!(
                    explorer
                        .solver()
                        .sat_with_constraint(&initial_state, &sym_mem.eq(BV::from_u64(0x2a, 8))),
                    SatResult::Sat
                ));
                assert!(matches!(
                    explorer
                        .solver()
                        .sat_with_constraint(&initial_state, &sym_mem.eq(BV::from_u64(0x2b, 8))),
                    SatResult::Sat
                ));
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("secondary source disagreement should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn vm_artifacts_preserve_interpreter_slice_class() {
        let artifact = bind_test_report(SemanticArtifactReport {
            schema_version: crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
            stage: RefinementStage::Compiled,
            granularity: ArtifactGranularity::SummaryOnly,
            execution: ExecutionModel::Vm,
            body: SemanticArtifactBody::Vm(Box::new(crate::VmArtifactBody {
                interpreter: None,
                step_summary: Some(make_vm_step_summary_with_transfers(Vec::new())),
                transfer_summary: None,
            })),
            diagnostics: default_diagnostics(),
        });

        assert_eq!(artifact.slice_class(), Some(SliceClass::InterpreterSwitch));
    }

    #[test]
    fn vm_target_case_values_include_redispatch_cases() {
        let vm_step = make_vm_step_summary_with_transfers(vec![
            VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![0],
                region_blocks: vec![0x1004],
                exit_targets: vec![0x1000],
                exit_guards: Vec::new(),
                state_updates: vec![VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "0x1".to_string(),
                    value: VmValueExpr::Const(1),
                    exact: true,
                }],
                selector_update: Some(VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "0x1".to_string(),
                    value: VmValueExpr::Const(1),
                    exact: true,
                }),
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: true,
                may_return: false,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1008,
                case_values: vec![1],
                region_blocks: vec![0x1008, 0x1014],
                exit_targets: vec![0x1014],
                exit_guards: Vec::new(),
                state_updates: Vec::new(),
                selector_update: None,
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
        ]);

        assert_eq!(vm_target_case_values(&vm_step, 0x1014), vec![0, 1]);
    }

    #[test]
    fn vm_target_case_values_follow_exact_state_updates_across_redispatch() {
        let vm_step = make_vm_step_summary_with_transfers(vec![
            VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![0],
                region_blocks: vec![0x1004],
                exit_targets: vec![0x1000],
                exit_guards: Vec::new(),
                state_updates: vec![VmStateUpdate {
                    output: "TMP_1".to_string(),
                    expr: "0x1".to_string(),
                    value: VmValueExpr::Const(1),
                    exact: true,
                }],
                selector_update: Some(VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "TMP_1".to_string(),
                    value: VmValueExpr::Var("TMP_1".to_string()),
                    exact: true,
                }),
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: true,
                may_return: false,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1008,
                case_values: vec![1],
                region_blocks: vec![0x1008, 0x1014],
                exit_targets: vec![0x1014],
                exit_guards: Vec::new(),
                state_updates: Vec::new(),
                selector_update: None,
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
        ]);

        assert_eq!(vm_target_case_values(&vm_step, 0x1014), vec![0, 1]);
    }

    #[test]
    fn vm_target_case_values_follow_bounded_selector_algebra() {
        let vm_step = make_vm_step_summary_with_transfers(vec![
            VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![0],
                region_blocks: vec![0x1004],
                exit_targets: vec![0x1000],
                exit_guards: Vec::new(),
                state_updates: vec![VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "(RDI_0 + 0x1)".to_string(),
                    value: VmValueExpr::Binary {
                        op: VmBinaryOp::Add,
                        lhs: Box::new(VmValueExpr::Var("RDI_0".to_string())),
                        rhs: Box::new(VmValueExpr::Const(1)),
                    },
                    exact: true,
                }],
                selector_update: Some(VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "(RDI_0 + 0x1)".to_string(),
                    value: VmValueExpr::Binary {
                        op: VmBinaryOp::Add,
                        lhs: Box::new(VmValueExpr::Var("RDI_0".to_string())),
                        rhs: Box::new(VmValueExpr::Const(1)),
                    },
                    exact: true,
                }),
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: true,
                may_return: false,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1008,
                case_values: vec![1],
                region_blocks: vec![0x1008],
                exit_targets: vec![0x1000],
                exit_guards: Vec::new(),
                state_updates: vec![VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "(RDI_0 + 0x1)".to_string(),
                    value: VmValueExpr::Binary {
                        op: VmBinaryOp::Add,
                        lhs: Box::new(VmValueExpr::Var("RDI_0".to_string())),
                        rhs: Box::new(VmValueExpr::Const(1)),
                    },
                    exact: true,
                }],
                selector_update: Some(VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "(RDI_0 + 0x1)".to_string(),
                    value: VmValueExpr::Binary {
                        op: VmBinaryOp::Add,
                        lhs: Box::new(VmValueExpr::Var("RDI_0".to_string())),
                        rhs: Box::new(VmValueExpr::Const(1)),
                    },
                    exact: true,
                }),
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: true,
                may_return: false,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1010,
                case_values: vec![2],
                region_blocks: vec![0x1010, 0x1014],
                exit_targets: vec![0x1014],
                exit_guards: Vec::new(),
                state_updates: Vec::new(),
                selector_update: None,
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
        ]);

        assert_eq!(vm_target_case_values(&vm_step, 0x1014), vec![0, 1, 2]);
    }

    #[test]
    fn vm_target_case_values_respect_exact_exit_guards() {
        let vm_step = make_vm_step_summary_with_transfers(vec![
            VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![0],
                region_blocks: vec![0x1004],
                exit_targets: vec![0x1014, 0x1000],
                exit_guards: vec![VmGuardedExit {
                    target: 0x1014,
                    guard: VmGuardCondition {
                        expr: "(RDI_0 == 0x1)".to_string(),
                        value: VmValueExpr::Binary {
                            op: VmBinaryOp::Eq,
                            lhs: Box::new(VmValueExpr::Var("RDI_0".to_string())),
                            rhs: Box::new(VmValueExpr::Const(1)),
                        },
                        expect_nonzero: true,
                        exact: true,
                    },
                }],
                state_updates: Vec::new(),
                selector_update: None,
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: false,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1008,
                case_values: vec![1],
                region_blocks: vec![0x1008],
                exit_targets: vec![0x1014],
                exit_guards: Vec::new(),
                state_updates: Vec::new(),
                selector_update: None,
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
        ]);

        assert_eq!(vm_target_case_values(&vm_step, 0x1014), vec![1]);
    }

    #[test]
    fn vm_target_case_values_follow_exact_memory_writes_across_redispatch() {
        let binding = "mem:r7:0:1".to_string();
        let vm_step = make_vm_step_summary_with_transfers(vec![
            VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![0],
                region_blocks: vec![0x1004],
                exit_targets: vec![0x1000],
                exit_guards: Vec::new(),
                state_updates: Vec::new(),
                selector_update: Some(VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "0x1".to_string(),
                    value: VmValueExpr::Const(1),
                    exact: true,
                }),
                memory_reads: Vec::new(),
                memory_writes: vec![crate::VmMemoryCondition {
                    region: crate::VmMemoryRegionRef {
                        id: 7,
                        kind: crate::MemoryRegionKind::Global,
                        name: "ram:0x4000".to_string(),
                    },
                    address: crate::SemanticMemoryAddress::exact(0),
                    size: 1,
                    binding: Some(binding.clone()),
                    expr: "*0x4000".to_string(),
                    value_expr: Some("0x1".to_string()),
                    value: Some(VmValueExpr::Const(1)),
                    exact_value: true,
                }],
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: true,
                may_return: false,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1008,
                case_values: vec![2],
                region_blocks: vec![0x1008],
                exit_targets: vec![0x1000],
                exit_guards: Vec::new(),
                state_updates: Vec::new(),
                selector_update: Some(VmStateUpdate {
                    output: "RDI_1".to_string(),
                    expr: "0x1".to_string(),
                    value: VmValueExpr::Const(1),
                    exact: true,
                }),
                memory_reads: Vec::new(),
                memory_writes: vec![crate::VmMemoryCondition {
                    region: crate::VmMemoryRegionRef {
                        id: 7,
                        kind: crate::MemoryRegionKind::Global,
                        name: "ram:0x4000".to_string(),
                    },
                    address: crate::SemanticMemoryAddress::exact(0),
                    size: 1,
                    binding: Some(binding.clone()),
                    expr: "*0x4000".to_string(),
                    value_expr: Some("0x0".to_string()),
                    value: Some(VmValueExpr::Const(0)),
                    exact_value: true,
                }],
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: true,
                may_return: false,
                truncated: false,
            },
            VmTransferArm {
                handler_target: 0x1010,
                case_values: vec![1],
                region_blocks: vec![0x1010],
                exit_targets: vec![0x1014],
                exit_guards: vec![VmGuardedExit {
                    target: 0x1014,
                    guard: VmGuardCondition {
                        expr: binding.clone(),
                        value: VmValueExpr::Var(binding.clone()),
                        expect_nonzero: true,
                        exact: true,
                    },
                }],
                state_updates: Vec::new(),
                selector_update: None,
                memory_reads: Vec::new(),
                memory_writes: Vec::new(),
                residual_guards: false,
                residual_memory_effects: false,
                exact: true,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
        ]);

        assert_eq!(vm_target_case_values(&vm_step, 0x1014), vec![0, 1]);
    }

    #[test]
    fn exact_compiled_preconditions_prefer_fewer_residual_fallbacks() {
        let current = crate::CompiledBackwardCondition {
            predicate: z3::ast::Bool::from_bool(true),
            summary: BackwardConditionSummary {
                simplified: "x".to_string(),
                terms: vec!["x".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 2,
                precision: BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            },
        };
        let candidate = crate::CompiledBackwardCondition {
            predicate: z3::ast::Bool::from_bool(true),
            summary: BackwardConditionSummary {
                simplified: "y".to_string(),
                terms: vec!["y".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 1,
                precision: BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            },
        };

        assert!(prefer_compiled_precondition(Some(&current), &candidate));
        assert!(!prefer_compiled_precondition(Some(&candidate), &current));
    }
}
