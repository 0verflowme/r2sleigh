//! Typed query-oriented symbolic analysis APIs.
//!
//! This module wraps the lower-level path exploration engine in reusable,
//! analysis-oriented queries that can be consumed by the plugin or other
//! analysis layers without exposing command-shaped policy.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use z3::Context;
use z3::ast::Ast;

use r2ssa::SsaArtifact;

use crate::SymState;
use crate::backward::{
    BackwardConditionPrecision, BackwardConditionSummary, CompiledBackwardCondition,
    compile_target_precondition_with_summaries, compile_value_postcondition_with_summaries,
};
use crate::path::{ExploreConfig, ExploreStats, PathExplorer, PathResult, SolvedPath};
use crate::semantics::{VmStepSummary, build_vm_step_summary, classify_interpreter_like};
use crate::sim::SummaryProfile;
use crate::solver::{SatResult, SolverStats};
use crate::state::ExitStatus;

const MAX_VM_COMPILED_STEPS: usize = 8;

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
        }
    }
}

impl SymQueryConfig {
    /// Build a path explorer for this query configuration.
    pub fn make_explorer<'ctx>(&self, ctx: &'ctx Context) -> PathExplorer<'ctx> {
        let mut explorer = PathExplorer::with_config(ctx, self.explore.clone());
        explorer.set_target_guided_queries(matches!(self.mode, QueryMode::TargetGuided));
        explorer
    }
}

/// Completion state for queries that may stop on budgets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryCompletion {
    /// Exploration finished without hitting timeout or state budgets.
    Complete,
    /// Exploration stopped because a configured budget was exhausted.
    BudgetExhausted,
}

/// Reachability result status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
    BudgetExhausted,
}

/// Solve result status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveStatus {
    Solved,
    Unsat,
    Unknown,
    BudgetExhausted,
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
    pub compiled_precondition: Option<BackwardConditionSummary>,
    pub paths: Vec<PathResult<'ctx>>,
    pub stats: ExploreStats,
    pub solver_stats: SolverStats,
}

/// Result of asking for the conditions that hold at a target PC.
#[derive(Debug)]
pub struct PathConditionResult<'ctx> {
    pub completion: QueryCompletion,
    pub target_pc: u64,
    pub compiled_precondition: Option<BackwardConditionSummary>,
    pub conditions: Vec<PathConditionSummary>,
    pub matching_paths: Vec<PathResult<'ctx>>,
    pub stats: ExploreStats,
    pub solver_stats: SolverStats,
}

/// Result of solving for a concrete target.
#[derive(Debug)]
pub struct SolveResult<'ctx> {
    pub status: SolveStatus,
    pub target_addr: u64,
    pub compiled_precondition: Option<BackwardConditionSummary>,
    pub matched_paths: Vec<PathResult<'ctx>>,
    pub selected_path_index: Option<usize>,
    pub solution: Option<SolvedPath>,
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

fn completion_from_stats(stats: &ExploreStats) -> QueryCompletion {
    if stats.timed_out || stats.max_states_exhausted {
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
        compiled_precondition: Option<BackwardConditionSummary>,
    },
    ExactUnsat {
        compiled_precondition: BackwardConditionSummary,
    },
}

fn precision_rank(precision: BackwardConditionPrecision) -> u8 {
    match precision {
        BackwardConditionPrecision::Exact => 3,
        BackwardConditionPrecision::OverApprox => 2,
        BackwardConditionPrecision::ResidualSearchRequired => 1,
        BackwardConditionPrecision::Unsupported => 0,
    }
}

fn vm_arm_reaches_target(arm: &crate::VmTransferArm, target_addr: u64) -> bool {
    arm.handler_target == target_addr
        || arm.region_blocks.contains(&target_addr)
        || arm.exit_targets.contains(&target_addr)
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

fn vm_apply_exact_state_updates(
    bindings: &BTreeMap<String, u64>,
    updates: &[crate::VmStateUpdate],
) -> BTreeMap<String, u64> {
    let mut next = bindings.clone();
    for update in updates {
        if !update.exact {
            continue;
        }
        if let Some(value) = update.value.evaluate_u64(&next) {
            next.insert(update.output.clone(), value);
        }
    }
    next
}

fn vm_next_case_value(
    bindings: &BTreeMap<String, u64>,
    arm: &crate::VmTransferArm,
    selector_name: Option<&str>,
) -> Option<(u64, BTreeMap<String, u64>)> {
    if !arm.redispatch || arm.truncated {
        return None;
    }
    let mut next_bindings = vm_apply_exact_state_updates(bindings, &arm.state_updates);
    let selector_update = arm.selector_update.as_ref()?;
    if !selector_update.exact {
        return None;
    }
    let next_case = selector_update.value.evaluate_u64(&next_bindings)?;
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
        if vm_arm_reaches_target(arm, target_addr) {
            return true;
        }
        if depth >= MAX_VM_COMPILED_STEPS.saturating_sub(1) || !arm.redispatch {
            continue;
        }
        let Some((next_case, next_bindings)) =
            vm_next_case_value(&bindings, arm, vm_step.selector.as_deref())
        else {
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

fn apply_compiled_precondition<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    mut initial_state: SymState<'ctx>,
    target_addr: u64,
) -> PreconditionApplication<'ctx> {
    let derived_summaries = explorer.derived_call_summary_views();
    let mut compiled = compile_target_precondition_with_summaries(
        func,
        &initial_state,
        target_addr,
        &derived_summaries,
    );
    if compiled.as_ref().is_none_or(|compiled| {
        !matches!(
            compiled.summary.precision,
            BackwardConditionPrecision::Exact
        )
    }) && let Some(vm_compiled) = compile_vm_target_precondition_with_summaries(
        func,
        &initial_state,
        target_addr,
        &derived_summaries,
    ) && prefer_compiled_precondition(compiled.as_ref(), &vm_compiled)
    {
        compiled = Some(vm_compiled);
    }
    let Some(compiled) = compiled else {
        return PreconditionApplication::Continue {
            initial_state: Box::new(initial_state),
            compiled_precondition: None,
        };
    };

    let summary = compiled.summary.clone();
    let exact = matches!(summary.precision, BackwardConditionPrecision::Exact);
    match explorer
        .solver()
        .sat_with_constraint(&initial_state, &compiled.predicate)
    {
        SatResult::Unsat if exact => PreconditionApplication::ExactUnsat {
            compiled_precondition: summary,
        },
        SatResult::Sat => {
            if exact {
                initial_state.add_constraint(compiled.predicate);
            }
            PreconditionApplication::Continue {
                initial_state: Box::new(initial_state),
                compiled_precondition: Some(summary),
            }
        }
        SatResult::Unknown | SatResult::Unsat => PreconditionApplication::Continue {
            initial_state: Box::new(initial_state),
            compiled_precondition: Some(summary),
        },
    }
}

impl<'ctx> PathExplorer<'ctx> {
    /// Ask whether a target address is reachable and collect the matching paths.
    pub fn can_reach(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> ReachabilityResult<'ctx> {
        let (paths, compiled_precondition) =
            match apply_compiled_precondition(self, func, initial_state, target_addr) {
                PreconditionApplication::Continue {
                    initial_state,
                    compiled_precondition,
                } => (
                    self.find_paths_to(func, *initial_state, target_addr),
                    compiled_precondition,
                ),
                PreconditionApplication::ExactUnsat {
                    compiled_precondition,
                } => (Vec::new(), Some(compiled_precondition)),
            };
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let status = if !paths.is_empty() {
            ReachabilityStatus::Reachable
        } else if self.budget_exhausted() {
            ReachabilityStatus::BudgetExhausted
        } else {
            ReachabilityStatus::Unreachable
        };
        ReachabilityResult {
            status,
            target_addr,
            compiled_precondition,
            paths,
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
        let (matching_paths, compiled_precondition) =
            match apply_compiled_precondition(self, func, initial_state, target_pc) {
                PreconditionApplication::Continue {
                    initial_state,
                    compiled_precondition,
                } => (
                    self.find_paths_to(func, *initial_state, target_pc),
                    compiled_precondition,
                ),
                PreconditionApplication::ExactUnsat {
                    compiled_precondition,
                } => (Vec::new(), Some(compiled_precondition)),
            };
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let conditions = matching_paths.iter().map(condition_summary).collect();
        PathConditionResult {
            completion: completion_from_stats(&stats),
            target_pc,
            compiled_precondition,
            conditions,
            matching_paths,
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
        let (matched_paths, compiled_precondition, exact_unsat) =
            match apply_compiled_precondition(self, func, initial_state, target_addr) {
                PreconditionApplication::Continue {
                    initial_state,
                    compiled_precondition,
                } => (
                    self.find_paths_to(func, *initial_state, target_addr),
                    compiled_precondition,
                    false,
                ),
                PreconditionApplication::ExactUnsat {
                    compiled_precondition,
                } => (Vec::new(), Some(compiled_precondition), true),
            };
        let stats = self.stats().clone();
        let solver_stats = self.solver().stats();
        let selected_path_index = matched_paths
            .iter()
            .enumerate()
            .min_by_key(|(idx, path)| (path.num_constraints(), path.depth, *idx))
            .map(|(idx, _)| idx);
        let solution = selected_path_index.and_then(|idx| self.solve_path(&matched_paths[idx]));
        let status = match (
            exact_unsat,
            selected_path_index,
            solution.as_ref(),
            completion_from_stats(&stats),
        ) {
            (true, _, _, _) => SolveStatus::Unsat,
            (false, _, Some(_), _) => SolveStatus::Solved,
            (false, None, _, QueryCompletion::BudgetExhausted) => SolveStatus::BudgetExhausted,
            (false, None, _, QueryCompletion::Complete) => SolveStatus::Unsat,
            (false, Some(_), None, QueryCompletion::BudgetExhausted) => {
                SolveStatus::BudgetExhausted
            }
            (false, Some(_), None, _) => SolveStatus::Unknown,
        };
        SolveResult {
            status,
            target_addr,
            compiled_precondition,
            matched_paths,
            selected_path_index,
            solution,
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

    use super::{
        PreconditionApplication, apply_compiled_precondition, prefer_compiled_precondition,
        vm_target_case_values,
    };
    use crate::{
        BackwardConditionPrecision, BackwardConditionSummary, SymQueryConfig, SymState, VmBinaryOp,
        VmStateUpdate, VmStepSummary, VmTransferArm, VmValueExpr,
    };
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
    use r2ssa::SsaArtifact;
    use z3::Context;

    const RDI: u64 = 56;
    const TMP0: u64 = 0x80;
    const TMP1: u64 = 0x88;

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
        match apply_compiled_precondition(&explorer, &func, state, 0x1010) {
            PreconditionApplication::Continue {
                initial_state,
                compiled_precondition,
            } => {
                let compiled = compiled_precondition.expect("compiled precondition");
                assert_eq!(
                    compiled.precision,
                    crate::BackwardConditionPrecision::ResidualSearchRequired
                );
                assert_eq!(initial_state.num_constraints(), original_constraints);
            }
            PreconditionApplication::ExactUnsat { .. } => {
                panic!("residual precondition should not shortcut as exact unsat")
            }
        }
    }

    #[test]
    fn vm_target_case_values_include_redispatch_cases() {
        let vm_step = make_vm_step_summary_with_transfers(vec![
            VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![0],
                region_blocks: vec![0x1004],
                exit_targets: vec![0x1000],
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
                state_updates: Vec::new(),
                selector_update: None,
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
                state_updates: Vec::new(),
                selector_update: None,
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
                state_updates: Vec::new(),
                selector_update: None,
                exact: true,
                redispatch: false,
                may_return: true,
                truncated: false,
            },
        ]);

        assert_eq!(vm_target_case_values(&vm_step, 0x1014), vec![0, 1, 2]);
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
