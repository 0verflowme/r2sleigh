//! Path exploration strategies for symbolic execution.
//!
//! This module provides different strategies for exploring paths
//! during symbolic execution, including DFS, BFS, and coverage-guided.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::fs::OpenOptions;
use std::io::Write;
use std::rc::Rc;
use std::time::{Duration, Instant};

use r2ssa::{AbiProfile, BlockTerminator, SSAOp, SsaArtifact, observe_call_arguments};
use z3::Context;

use crate::backward::DerivedCallSummaryView;
use crate::constraints::FinalConstraintGraph;
use crate::executor::SymExecutor;
use crate::loops::{self, ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, LoopSummaryKind};
use crate::sim::{
    CallConv, DerivedFunctionSummary, PreparedFunctionScope, evaluate_derived_summary_guidance,
};
use crate::solver::SymSolver;
use crate::spec::ExplorationSpec;
use crate::state::{ExitStatus, RuntimeBlockReason, SymState};
use crate::tactics::{
    SolveTacticConfig, constrain_exact_fold_inputs, constrain_exact_recurrence_candidate,
    tactic_candidates_for_constraint_graph,
};

const TARGET_DISTANCE_CACHE_LIMIT: usize = 128;
const EXACT_RUNTIME_LOOP_MAX_ITERS: u64 = 4096;
const EXACT_RUNTIME_LOOP_MAX_BLOCK_STEPS: u64 = 200_000;
const SYMBOLIC_CONTINUATION_MAX_TARGETS: usize = 512;

#[derive(Debug, Default)]
struct TargetDistanceCache {
    entries: HashMap<(u64, u64), (HashMap<u64, usize>, u64)>,
    order: BTreeMap<u64, (u64, u64)>,
    next_ticket: u64,
}

impl TargetDistanceCache {
    fn new() -> Self {
        Self {
            entries: HashMap::new(),
            order: BTreeMap::new(),
            next_ticket: 1,
        }
    }

    fn allocate_ticket(&mut self) -> u64 {
        let ticket = self.next_ticket;
        self.next_ticket = self.next_ticket.wrapping_add(1).max(1);
        ticket
    }

    fn get(&mut self, key: &(u64, u64)) -> Option<HashMap<u64, usize>> {
        let new_ticket = self.allocate_ticket();
        let (distances, old_ticket) = self.entries.get_mut(key)?;
        let distances = distances.clone();
        let previous_ticket = *old_ticket;
        *old_ticket = new_ticket;
        self.order.remove(&previous_ticket);
        self.order.insert(new_ticket, *key);
        Some(distances)
    }

    fn insert(&mut self, key: (u64, u64), distances: HashMap<u64, usize>) {
        let ticket = self.allocate_ticket();
        if let Some((_, old_ticket)) = self.entries.insert(key, (distances, ticket)) {
            self.order.remove(&old_ticket);
        }
        self.order.insert(ticket, key);
        while self.entries.len() > TARGET_DISTANCE_CACHE_LIMIT {
            let Some((_, evicted_key)) = self.order.pop_first() else {
                break;
            };
            self.entries.remove(&evicted_key);
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.entries.len()
    }
}

fn debug_target_guidance_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_TARGET_GUIDANCE").is_some()
}

fn debug_target_guidance_log(message: &str) {
    if !debug_target_guidance_enabled() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_TARGET_GUIDANCE_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_target_guidance.log".to_string());
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(file, "{message}");
    }
}

fn debug_target_match_unsat_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_TARGET_MATCH_UNSAT").is_some()
}

fn debug_target_match_unsat_log(message: &str) {
    if !debug_target_match_unsat_enabled() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_TARGET_MATCH_UNSAT_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_target_match_unsat.log".to_string());
    if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = writeln!(file, "{message}");
    }
}

fn debug_log_target_unsat_state(state: &SymState<'_>, target_addr: u64) {
    if !debug_target_match_unsat_enabled() {
        return;
    }
    let mut registers = state
        .registers()
        .iter()
        .filter_map(|(name, value)| {
            let interesting = ["AL_", "EAX_", "RAX_", "RCX_", "RDI_", "RDX_", "RSP_"]
                .iter()
                .any(|prefix| name.starts_with(prefix));
            interesting.then(|| match value.as_concrete() {
                Some(value) => format!("{name}={value:#x}"),
                None => format!("{name}=sym({}b)", value.bits()),
            })
        })
        .collect::<Vec<_>>();
    registers.sort();
    debug_target_match_unsat_log(&format!(
        "target=0x{target_addr:x} pc=0x{:x} prev_pc={} depth={} constraints={} regs=[{}]",
        state.pc,
        state
            .prev_pc()
            .map(|pc| format!("0x{pc:x}"))
            .unwrap_or_else(|| "none".to_string()),
        state.depth,
        state.num_constraints(),
        registers.join(", ")
    ));
}

/// Configuration for path exploration.
#[derive(Debug, Clone)]
pub struct ExploreConfig {
    /// Maximum number of states to explore.
    pub max_states: usize,
    /// Maximum number of completed paths to collect during full exploration.
    pub max_completed_paths: Option<usize>,
    /// Maximum execution depth per path.
    pub max_depth: usize,
    /// Timeout for the entire exploration.
    pub timeout: Option<Duration>,
    /// Exploration strategy.
    pub strategy: ExploreStrategy,
    /// Whether to prune infeasible paths early.
    pub prune_infeasible: bool,
    /// Whether to merge states at join points.
    pub merge_states: bool,
    /// Whether to drop same-PC states that are already covered by weaker states.
    pub subsumption_states: bool,
}

impl Default for ExploreConfig {
    fn default() -> Self {
        Self {
            max_states: 1000,
            max_completed_paths: None,
            max_depth: 100,
            timeout: Some(Duration::from_secs(60)),
            strategy: ExploreStrategy::Dfs,
            prune_infeasible: true,
            merge_states: false,
            subsumption_states: false,
        }
    }
}

/// Exploration strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExploreStrategy {
    /// Depth-first search.
    Dfs,
    /// Breadth-first search.
    Bfs,
    /// Random path selection.
    Random,
}

/// Result of exploring a single path.
#[derive(Debug)]
pub struct PathResult<'ctx> {
    /// The final state of this path.
    pub state: SymState<'ctx>,
    /// How the path terminated.
    pub exit_status: ExitStatus,
    /// Execution depth.
    pub depth: usize,
    /// Whether the path is feasible (constraints satisfiable).
    pub feasible: bool,
}

impl<'ctx> PathResult<'ctx> {
    /// Create a new path result.
    pub fn new(state: SymState<'ctx>, feasible: bool) -> Self {
        let exit_status = state.exit_status.clone().unwrap_or(ExitStatus::Return);
        let depth = state.depth;
        Self {
            state,
            exit_status,
            depth,
            feasible,
        }
    }

    /// Get the final program counter.
    pub fn final_pc(&self) -> u64 {
        self.state.pc
    }

    /// Get the number of path constraints.
    pub fn num_constraints(&self) -> usize {
        self.state.num_constraints()
    }

    /// Get all register names in the final state.
    pub fn register_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.state.register_names().cloned().collect();
        names.sort();
        names
    }

    /// Get a register value (returns None if symbolic or not set).
    pub fn get_concrete_register(&self, name: &str) -> Option<u64> {
        self.state.get_register(name).as_concrete()
    }

    /// Check if a register is symbolic.
    pub fn is_register_symbolic(&self, name: &str) -> bool {
        self.state.get_register(name).is_symbolic()
    }
}

/// Concrete values extracted from a solved path.
#[derive(Debug, Clone, Default)]
pub struct SolvedPath {
    /// Concrete input values (symbolic variable name -> value).
    pub inputs: BTreeMap<String, u64>,
    /// Concrete multi-byte input buffers (input source name -> bytes).
    pub input_buffers: BTreeMap<String, Vec<u8>>,
    /// Concrete register values at path end.
    pub registers: BTreeMap<String, u64>,
    /// Concrete memory bytes for tracked symbolic regions.
    pub memory: BTreeMap<String, Vec<u8>>,
    /// Final program counter.
    pub final_pc: u64,
    /// Path constraints that were satisfied.
    pub num_constraints: usize,
    /// Optional provenance when the candidate was produced by a solve tactic.
    pub generation: Option<SolvedPathGeneration>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolvedPathGenerationKind {
    ExactRecurrenceConstraintTactic,
    MitmConstraintTactic,
    DomainConstraintTactic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolvedPathGeneration {
    pub kind: SolvedPathGenerationKind,
    pub reason: String,
    pub constrained_bytes: usize,
}

/// Result of a spec-driven exploration run.
#[derive(Debug, Default)]
pub struct SpecExploreResult<'ctx> {
    /// Feasible paths that matched a find predicate.
    pub found_paths: Vec<PathResult<'ctx>>,
    /// Number of states pruned by avoid predicates.
    pub avoided_states: usize,
    /// Number of states pruned as infeasible.
    pub unsat_states: usize,
    /// Number of states that ended in an execution error.
    pub errored_states: usize,
    /// Number of completed states that did not hit a find predicate.
    pub completed_states: usize,
    /// Non-fatal diagnostics gathered during execution.
    pub diagnostics: Vec<String>,
}

/// Path explorer for symbolic execution.
pub struct PathExplorer<'ctx> {
    /// The Z3 context.
    _ctx: &'ctx Context,
    /// The symbolic executor.
    executor: SymExecutor<'ctx>,
    /// The constraint solver.
    solver: SymSolver<'ctx>,
    /// Configuration.
    config: ExploreConfig,
    /// Statistics.
    stats: ExploreStats,
    /// Whether query helpers should prioritize states closer to their target.
    target_guided_queries: bool,
    /// Whether target-guided queries may first route through exception-dispatch bridge sites.
    exception_bridge_guidance_enabled: bool,
    /// Whether unsupported runtime loop summaries may produce residual states.
    residual_runtime_loop_summaries_enabled: bool,
    /// Derived helper summaries registered for direct-call targets.
    derived_call_summaries: HashMap<u64, RegisteredDerivedCallSummary<'ctx>>,
    /// Cached reverse-distance maps keyed by (function entry, target address).
    target_distance_cache: TargetDistanceCache,
    /// Candidate-generation tactics used during model extraction.
    solve_tactic_config: SolveTacticConfig,
}

/// Statistics from path exploration.
#[derive(Debug, Clone, Default)]
pub struct ExploreStats {
    /// Number of states explored.
    pub states_explored: usize,
    /// Number of paths completed.
    pub paths_completed: usize,
    /// Number of infeasible paths pruned.
    pub paths_pruned: usize,
    /// Number of paths that hit max depth.
    pub paths_max_depth: usize,
    /// Maximum depth reached.
    pub max_depth_reached: usize,
    /// Total execution time.
    pub total_time: Duration,
    /// Whether exploration stopped because the timeout budget expired.
    pub timed_out: bool,
    /// Whether exploration stopped because the max_states budget was exhausted.
    pub max_states_exhausted: bool,
    /// Number of queued states discarded because another state subsumed them.
    pub states_subsumed: usize,
    /// Number of implication checks attempted for same-PC subsumption.
    pub subsumption_checks: usize,
    /// Number of implication checks that found a covering state.
    pub subsumption_hits: usize,
    /// Number of target-guided queue pops that differed from the base strategy order.
    pub target_guided_reorders: usize,
    /// Number of states dropped because their PC cannot reach the target in the CFG.
    pub target_pruned_cfg_unreachable: usize,
    /// Number of states dropped because an exact helper summary had no satisfiable case.
    pub target_pruned_summary_contradiction: usize,
    /// Number of target-guided states whose ranking/pruning used derived summary metadata.
    pub target_summary_rank_hits: usize,
    /// Number of states that reached the target PC but were unsatisfiable.
    pub target_match_unsat: usize,
    /// Number of states blocked by a missing exception handler.
    pub runtime_missing_exception_handler: usize,
    /// Number of states that entered runtime code without a materialized executable alias.
    pub runtime_missing_materialized_code: usize,
    /// Number of states that could not resume from an exception continuation.
    pub runtime_missing_continuation_seed: usize,
    /// Number of states that reached runtime code with unresolved provenance.
    pub runtime_region_provenance_unknown: usize,
    /// Number of symbolic runtime breakpoint dispatch candidates forked.
    pub runtime_symbolic_breakpoint_forks: usize,
    /// Number of symbolic runtime breakpoint candidates proven infeasible before enqueue.
    pub runtime_symbolic_breakpoint_pruned: usize,
    /// Number of residual summaries used to accelerate runtime breakpoint loops.
    pub runtime_breakpoint_loop_summaries: usize,
    /// Number of exact summaries used to accelerate runtime breakpoint loops.
    pub runtime_breakpoint_loop_exact_summaries: usize,
    /// Number of exact loop summaries derived by recurrence algebra.
    pub runtime_loop_exact_recurrence_summaries: usize,
    /// Canonical exact recurrence evidence derived by loop algebra.
    pub runtime_loop_exact_recurrences: Vec<ExactLoopRecurrenceEvidence>,
    /// Exact memory-fold recurrences derived by loop algebra.
    pub runtime_loop_exact_folds: Vec<ExactLoopFoldEvidence>,
    /// Number of runtime loop summaries refused for soundness or missing context.
    pub runtime_loop_refusals: usize,
    /// Number of runtime loop candidates with unknown carried state.
    pub runtime_loop_unknown_carried_state: usize,
    /// Number of runtime loop candidates downgraded because exact iteration budget was exceeded.
    pub runtime_loop_budget_residuals: usize,
}

#[derive(Clone)]
struct RegisteredDerivedCallSummary<'ctx> {
    summary: Rc<DerivedFunctionSummary<'ctx>>,
    callconv: CallConv,
}

#[derive(Clone, Default)]
struct BlockSummaryRank {
    has_summary: bool,
    has_exact_summary: bool,
    min_case_count: usize,
}

struct TargetGuidanceContext {
    target_addr: u64,
    distances: HashMap<u64, usize>,
    reachable_blocks: HashSet<u64>,
    call_targets_by_block: HashMap<u64, Vec<u64>>,
    block_summary_rank: HashMap<u64, BlockSummaryRank>,
    allow_cross_function_states: bool,
}

#[derive(Clone, Copy, Default)]
struct StateSummaryGuidance {
    summary_hits: usize,
    min_feasible_cases: usize,
    contradictory: bool,
}

#[derive(Clone, Copy)]
struct ResolvedBlock<'a> {
    func: &'a SsaArtifact,
    block: &'a r2ssa::FunctionSSABlock,
    static_addr: u64,
    runtime_addr: u64,
    runtime_aliased: bool,
}

struct StateWorklist<'ctx> {
    strategy: ExploreStrategy,
    ready: VecDeque<usize>,
    same_pc: HashMap<u64, VecDeque<usize>>,
    slots: Vec<Option<SymState<'ctx>>>,
    live_states: usize,
}

impl<'ctx> StateWorklist<'ctx> {
    fn new(strategy: ExploreStrategy) -> Self {
        Self {
            strategy,
            ready: VecDeque::new(),
            same_pc: HashMap::new(),
            slots: Vec::new(),
            live_states: 0,
        }
    }

    fn push(&mut self, state: SymState<'ctx>) -> usize {
        let id = self.slots.len();
        let pc = state.pc;
        self.slots.push(Some(state));
        self.ready.push_back(id);
        self.same_pc.entry(pc).or_default().push_back(id);
        self.live_states += 1;
        id
    }

    fn state(&self, id: usize) -> Option<&SymState<'ctx>> {
        self.slots.get(id)?.as_ref()
    }

    fn same_pc_ids(&self, pc: u64) -> Vec<usize> {
        self.same_pc
            .get(&pc)
            .map(|bucket| bucket.iter().copied().collect())
            .unwrap_or_default()
    }

    fn remove_slot(&mut self, id: usize) -> Option<SymState<'ctx>> {
        self.take_slot(id)
    }

    fn pop_next(&mut self) -> Option<SymState<'ctx>> {
        loop {
            let id = match self.strategy {
                ExploreStrategy::Dfs => self.ready.pop_back(),
                ExploreStrategy::Bfs => self.ready.pop_front(),
                ExploreStrategy::Random => {
                    if self.ready.is_empty() {
                        None
                    } else if self.live_states.is_multiple_of(2) {
                        self.ready.pop_front()
                    } else {
                        self.ready.pop_back()
                    }
                }
            }?;

            if let Some(state) = self.take_slot(id) {
                return Some(state);
            }
        }
    }

    fn default_candidate(&mut self) -> Option<usize> {
        match self.strategy {
            ExploreStrategy::Dfs => {
                while let Some(id) = self.ready.back().copied() {
                    if self.state(id).is_some() {
                        return Some(id);
                    }
                    self.ready.pop_back();
                }
                None
            }
            ExploreStrategy::Bfs => {
                while let Some(id) = self.ready.front().copied() {
                    if self.state(id).is_some() {
                        return Some(id);
                    }
                    self.ready.pop_front();
                }
                None
            }
            ExploreStrategy::Random => {
                if self.ready.is_empty() {
                    return None;
                }
                if self.live_states.is_multiple_of(2) {
                    while let Some(id) = self.ready.front().copied() {
                        if self.state(id).is_some() {
                            return Some(id);
                        }
                        self.ready.pop_front();
                    }
                } else {
                    while let Some(id) = self.ready.back().copied() {
                        if self.state(id).is_some() {
                            return Some(id);
                        }
                        self.ready.pop_back();
                    }
                }
                None
            }
        }
    }

    fn take_same_pc(&mut self, pc: u64) -> Option<SymState<'ctx>> {
        loop {
            let id = {
                let bucket = self.same_pc.get_mut(&pc)?;
                match self.strategy {
                    ExploreStrategy::Dfs => bucket.pop_back(),
                    ExploreStrategy::Bfs => bucket.pop_front(),
                    ExploreStrategy::Random => {
                        if bucket.is_empty() {
                            None
                        } else if self.live_states.is_multiple_of(2) {
                            bucket.pop_front()
                        } else {
                            bucket.pop_back()
                        }
                    }
                }
            }?;

            let remove_bucket = self.same_pc.get(&pc).is_some_and(VecDeque::is_empty);
            if remove_bucket {
                self.same_pc.remove(&pc);
            }

            if let Some(state) = self.take_slot(id) {
                return Some(state);
            }
        }
    }

    fn take_slot(&mut self, id: usize) -> Option<SymState<'ctx>> {
        let slot = self.slots.get_mut(id)?;
        let state = slot.take()?;
        self.live_states = self.live_states.saturating_sub(1);
        Some(state)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TargetGuidedQueueEntry {
    rank: (
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
    ),
    id: usize,
}

impl Ord for TargetGuidedQueueEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.rank
            .cmp(&other.rank)
            .then_with(|| self.id.cmp(&other.id))
    }
}

impl PartialOrd for TargetGuidedQueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

enum DriverAction<'ctx> {
    Continue(Box<SymState<'ctx>>),
    Skip,
    Finish,
}

enum DriverMode<'ctx> {
    Explore {
        results: Vec<PathResult<'ctx>>,
    },
    FindFirst {
        target_addr: u64,
        require_feasible: bool,
        found: Option<PathResult<'ctx>>,
    },
    FindAll {
        target_addr: u64,
        require_feasible: bool,
        matches: Vec<PathResult<'ctx>>,
    },
    Avoid {
        avoid_set: HashSet<u64>,
        found: Option<PathResult<'ctx>>,
    },
    Spec {
        find_set: HashSet<u64>,
        avoid_set: HashSet<u64>,
        max_finds: usize,
        result: SpecExploreResult<'ctx>,
    },
}

impl<'ctx> DriverMode<'ctx> {
    fn explore_path_cap_reached(&self, max_completed_paths: Option<usize>) -> bool {
        let Some(limit) = max_completed_paths else {
            return false;
        };
        match self {
            DriverMode::Explore { results } => results.len() >= limit,
            _ => false,
        }
    }

    fn on_timeout(&mut self) -> bool {
        if let DriverMode::Spec { result, .. } = self {
            result.diagnostics.push("exploration timed out".to_string());
        }
        true
    }

    fn on_max_states(&mut self) -> bool {
        if let DriverMode::Spec { result, .. } = self {
            result
                .diagnostics
                .push("exploration stopped at max_states budget".to_string());
        }
        true
    }

    fn on_unsat_pruned(&mut self) {
        if let DriverMode::Spec { result, .. } = self {
            result.unsat_states += 1;
        }
    }

    fn on_state_popped(
        &mut self,
        explorer: &mut PathExplorer<'ctx>,
        state: SymState<'ctx>,
    ) -> DriverAction<'ctx> {
        match self {
            DriverMode::Explore { .. } => DriverAction::Continue(Box::new(state)),
            DriverMode::FindFirst {
                target_addr,
                require_feasible,
                found,
            } => {
                if explorer.state_matches_target(&state, *target_addr) {
                    if !*require_feasible || explorer.solver.is_sat(&state) {
                        *found = Some(PathResult::new(state, true));
                        DriverAction::Finish
                    } else {
                        debug_log_target_unsat_state(&state, *target_addr);
                        explorer.stats.target_match_unsat += 1;
                        DriverAction::Skip
                    }
                } else {
                    DriverAction::Continue(Box::new(state))
                }
            }
            DriverMode::FindAll {
                target_addr,
                require_feasible,
                matches,
            } => {
                if explorer.state_matches_target(&state, *target_addr) {
                    if !*require_feasible || explorer.solver.is_sat(&state) {
                        explorer.record_depth(state.depth);
                        explorer.stats.paths_completed += 1;
                        matches.push(PathResult::new(state, true));
                    } else {
                        debug_log_target_unsat_state(&state, *target_addr);
                        explorer.stats.target_match_unsat += 1;
                    }
                    DriverAction::Skip
                } else {
                    DriverAction::Continue(Box::new(state))
                }
            }
            DriverMode::Avoid { avoid_set, .. } => {
                if explorer.state_hits_any_target(&state, avoid_set) {
                    DriverAction::Skip
                } else {
                    DriverAction::Continue(Box::new(state))
                }
            }
            DriverMode::Spec {
                find_set,
                avoid_set,
                max_finds,
                result,
            } => {
                if explorer.state_hits_any_target(&state, avoid_set) {
                    result.avoided_states += 1;
                    return DriverAction::Skip;
                }
                if explorer.state_hits_any_target(&state, find_set) {
                    if explorer.solver.is_sat(&state) {
                        explorer.record_depth(state.depth);
                        explorer.stats.paths_completed += 1;
                        result.found_paths.push(PathResult::new(state, true));
                        if result.found_paths.len() >= *max_finds {
                            return DriverAction::Finish;
                        }
                    } else {
                        explorer.stats.paths_pruned += 1;
                        result.unsat_states += 1;
                    }
                    DriverAction::Skip
                } else {
                    DriverAction::Continue(Box::new(state))
                }
            }
        }
    }

    fn on_depth_limit(
        &mut self,
        explorer: &mut PathExplorer<'ctx>,
        mut state: SymState<'ctx>,
        max_completed_paths: Option<usize>,
    ) -> DriverAction<'ctx> {
        match self {
            DriverMode::Explore { results } => {
                state.terminate(ExitStatus::MaxDepth);
                explorer.record_depth(state.depth);
                explorer.stats.paths_max_depth += 1;
                results.push(PathResult::new(state, true));
                if self.explore_path_cap_reached(max_completed_paths) {
                    DriverAction::Finish
                } else {
                    DriverAction::Skip
                }
            }
            DriverMode::FindFirst { .. } => DriverAction::Skip,
            DriverMode::FindAll { .. } => {
                explorer.stats.paths_max_depth += 1;
                DriverAction::Skip
            }
            DriverMode::Avoid { found, .. } => {
                if explorer.solver.is_sat(&state) {
                    *found = Some(PathResult::new(state, true));
                    DriverAction::Finish
                } else {
                    DriverAction::Skip
                }
            }
            DriverMode::Spec { result, .. } => {
                explorer.stats.paths_max_depth += 1;
                result.completed_states += 1;
                DriverAction::Skip
            }
        }
    }

    fn on_missing_block(
        &mut self,
        explorer: &mut PathExplorer<'ctx>,
        mut state: SymState<'ctx>,
        block_addr: u64,
        max_completed_paths: Option<usize>,
    ) -> DriverAction<'ctx> {
        explorer.record_runtime_missing_block(&state, block_addr);
        match self {
            DriverMode::Explore { results } => {
                state.terminate(ExitStatus::Return);
                results.push(PathResult::new(state, true));
                explorer.stats.paths_completed += 1;
                if self.explore_path_cap_reached(max_completed_paths) {
                    DriverAction::Finish
                } else {
                    DriverAction::Skip
                }
            }
            DriverMode::FindFirst { .. } | DriverMode::FindAll { .. } => DriverAction::Skip,
            DriverMode::Avoid { found, .. } => {
                if explorer.solver.is_sat(&state) {
                    *found = Some(PathResult::new(state, true));
                    DriverAction::Finish
                } else {
                    DriverAction::Skip
                }
            }
            DriverMode::Spec { result, .. } => {
                result
                    .diagnostics
                    .push(format!("no SSA block at 0x{block_addr:x}"));
                result.completed_states += 1;
                explorer.stats.paths_completed += 1;
                DriverAction::Skip
            }
        }
    }

    fn on_terminated_state(
        &mut self,
        explorer: &mut PathExplorer<'ctx>,
        state: SymState<'ctx>,
        block_addr: u64,
        max_completed_paths: Option<usize>,
    ) -> DriverAction<'ctx> {
        explorer.record_runtime_exit_status(&state.exit_status);
        match self {
            DriverMode::Explore { results } => {
                explorer.record_depth(state.depth);
                let feasible = explorer.solver.is_sat(&state);
                results.push(PathResult::new(state, feasible));
                explorer.stats.paths_completed += 1;
                if self.explore_path_cap_reached(max_completed_paths) {
                    return DriverAction::Finish;
                }
            }
            DriverMode::FindFirst { .. }
            | DriverMode::FindAll { .. }
            | DriverMode::Avoid { .. } => {}
            DriverMode::Spec { result, .. } => {
                explorer.stats.paths_completed += 1;
                result.diagnostics.push(format!(
                    "state terminated at 0x{:x} with {:?}",
                    block_addr, state.exit_status
                ));
                match &state.exit_status {
                    Some(ExitStatus::Error(_)) | Some(ExitStatus::RuntimeBlocked(_)) => {
                        result.errored_states += 1
                    }
                    _ => result.completed_states += 1,
                }
            }
        }
        DriverAction::Skip
    }

    fn on_execute_error(
        &mut self,
        explorer: &mut PathExplorer<'ctx>,
        mut state: SymState<'ctx>,
        block_addr: u64,
        error: String,
        max_completed_paths: Option<usize>,
    ) -> DriverAction<'ctx> {
        match self {
            DriverMode::Explore { results } => {
                explorer.record_depth(state.depth);
                state.terminate(ExitStatus::Error(error));
                results.push(PathResult::new(state, false));
                explorer.stats.paths_completed += 1;
                if self.explore_path_cap_reached(max_completed_paths) {
                    return DriverAction::Finish;
                }
            }
            DriverMode::FindAll { .. } => {
                explorer.stats.paths_completed += 1;
            }
            DriverMode::Spec { result, .. } => {
                explorer.stats.paths_completed += 1;
                result.errored_states += 1;
                result
                    .diagnostics
                    .push(format!("execution error at 0x{block_addr:x}: {error}"));
            }
            DriverMode::FindFirst { .. } | DriverMode::Avoid { .. } => {}
        }
        DriverAction::Skip
    }

    fn allow_enqueue(&mut self, state: &SymState<'ctx>) -> bool {
        match self {
            DriverMode::Avoid { .. } => true,
            DriverMode::Spec {
                avoid_set, result, ..
            } => {
                let static_pc = state.resolve_runtime_pc(state.pc).unwrap_or(state.pc);
                if avoid_set.contains(&state.pc) || avoid_set.contains(&static_pc) {
                    result.avoided_states += 1;
                    false
                } else {
                    true
                }
            }
            _ => true,
        }
    }
}

impl<'ctx> PathExplorer<'ctx> {
    fn state_matches_target(&self, state: &SymState<'ctx>, target_addr: u64) -> bool {
        state.pc == target_addr || self.effective_static_pc(state) == target_addr
    }

    fn state_hits_any_target(&self, state: &SymState<'ctx>, targets: &HashSet<u64>) -> bool {
        targets.contains(&state.pc) || targets.contains(&self.effective_static_pc(state))
    }

    fn max_inline_runahead_depth_delta(&self) -> usize {
        self.config
            .max_depth
            .saturating_mul(64)
            .max(self.config.max_depth)
    }

    fn finalize_active_state_after_block(
        &self,
        func: &SsaArtifact,
        state: &mut SymState<'ctx>,
        block_runtime_addr: u64,
        block_static_addr: u64,
    ) {
        state.pc = state
            .remap_static_pc_to_runtime(state.pc)
            .unwrap_or(state.pc);
        if state.pc == block_runtime_addr
            && let Some(next) = self.fallthrough_target(func, block_static_addr)
        {
            state.pc = state.remap_static_pc_to_runtime(next).unwrap_or(next);
        }
        state.set_prev_pc(Some(block_runtime_addr));
    }

    fn patch_pending_exception_resume_pc(
        &self,
        func: &SsaArtifact,
        state: &mut SymState<'ctx>,
        block_static_addr: u64,
    ) {
        let Some(pending) = state.pending_exception() else {
            return;
        };
        if state.pc != pending.handler_addr {
            return;
        }
        let Some(resume_static_pc) = self.fallthrough_target(func, block_static_addr) else {
            return;
        };
        let resume_pc = state
            .remap_static_pc_to_runtime(resume_static_pc)
            .unwrap_or(resume_static_pc);
        let _ = state.set_pending_exception_resume_pc(resume_pc);
    }

    fn record_runtime_block_reason(&mut self, reason: RuntimeBlockReason) {
        match reason {
            RuntimeBlockReason::MissingExceptionHandler => {
                self.stats.runtime_missing_exception_handler += 1;
            }
            RuntimeBlockReason::MissingRuntimeMaterializedCode => {
                self.stats.runtime_missing_materialized_code += 1;
            }
            RuntimeBlockReason::MissingContinuationSeed => {
                self.stats.runtime_missing_continuation_seed += 1;
            }
            RuntimeBlockReason::RuntimeRegionProvenanceUnknown => {
                self.stats.runtime_region_provenance_unknown += 1;
            }
        }
    }

    fn record_runtime_exit_status(&mut self, status: &Option<ExitStatus>) {
        if let Some(ExitStatus::RuntimeBlocked(reason)) = status {
            self.record_runtime_block_reason(*reason);
        }
    }

    fn record_runtime_missing_block(&mut self, state: &SymState<'ctx>, block_addr: u64) {
        if let Some(region) = state.runtime_region_for_pc(block_addr) {
            if !region.executable || region.source_base.is_none() {
                self.record_runtime_block_reason(
                    RuntimeBlockReason::MissingRuntimeMaterializedCode,
                );
            } else {
                self.record_runtime_block_reason(
                    RuntimeBlockReason::RuntimeRegionProvenanceUnknown,
                );
            }
        }
    }

    fn runtime_continuation_candidate_targets(
        &self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        state: &SymState<'ctx>,
    ) -> Vec<u64> {
        let mut candidates = BTreeSet::new();
        let mut collect = |function: &SsaArtifact| {
            for static_pc in function.cfg().block_addrs() {
                if let Some(runtime_pc) = state.remap_static_pc_to_runtime(static_pc) {
                    candidates.insert(runtime_pc);
                }
            }
        };
        collect(root);
        if let Some(scope) = scope {
            for function in scope.functions().values() {
                collect(&function.prepared);
            }
        }
        candidates
            .into_iter()
            .take(SYMBOLIC_CONTINUATION_MAX_TARGETS)
            .collect()
    }

    fn fork_symbolic_exception_resume_targets(
        &mut self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        state: &SymState<'ctx>,
    ) -> Vec<SymState<'ctx>> {
        if !matches!(
            &state.exit_status,
            Some(ExitStatus::RuntimeBlocked(
                RuntimeBlockReason::MissingContinuationSeed
            ))
        ) {
            return Vec::new();
        }
        let Some(pending) = state.pending_exception() else {
            return Vec::new();
        };
        let rip = state.mem_read(
            &crate::SymValue::concrete(pending.context_addr.saturating_add(0xf8), 64),
            8,
        );
        if rip.as_concrete().is_some() || rip.is_unknown() {
            return Vec::new();
        }

        let mut resumed = Vec::new();
        let candidates = self.runtime_continuation_candidate_targets(root, scope, state);
        let candidates_checked = candidates.len();
        for candidate in candidates {
            let candidate_value = crate::SymValue::concrete(candidate, rip.bits());
            if !self.solver.can_be_equal(state, &rip, &candidate_value) {
                continue;
            }
            let mut forked = state.fork();
            forked.active = true;
            forked.exit_status = None;
            forked.constrain_eq(&rip, candidate);
            forked.pc = candidate;
            forked.set_prev_pc(None);
            forked.clear_pending_exception();
            resumed.push(forked);
        }
        if !resumed.is_empty() {
            debug_target_guidance_log(&format!(
                "symbolic_exception_resume_forks count={} candidates_checked={}",
                resumed.len(),
                candidates_checked
            ));
        }
        resumed
    }

    fn resolve_scope_function<'a>(
        &self,
        root: &'a SsaArtifact,
        scope: Option<&'a PreparedFunctionScope>,
        pc: u64,
    ) -> Option<&'a SsaArtifact> {
        if root.get_block(pc).is_some() {
            return Some(root);
        }
        scope
            .and_then(|scope| scope.function_containing_block(pc))
            .map(|function| &function.prepared)
    }

    fn exception_bridge_guidance_target(
        &mut self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        target_addr: u64,
    ) -> Option<u64> {
        if !self.exception_bridge_guidance_enabled {
            return None;
        }
        let scope = scope?;
        let target_func = self.resolve_scope_function(root, Some(scope), target_addr);
        if target_func.is_some_and(|target_func| target_func.entry == root.entry) {
            let distances = self.target_distance_map(root, target_addr);
            if distances.contains_key(&root.entry) {
                return None;
            }
        }

        let observations = observe_call_arguments(root, &AbiProfile::windows_x64());
        let mut registration_sites = Vec::new();
        let mut raise_sites = Vec::new();

        for (call_id, call) in &root.call_sites().by_id {
            let Some(target) = root.resolved_call_target(call) else {
                continue;
            };
            match self.executor.call_hook_tag(target) {
                Some(crate::executor::CallHookTag::WindowsAddVectoredExceptionHandler) => {
                    if observations.contains_key(call_id) {
                        if let Some((block_addr, _)) = root.inst_op_site(call.at) {
                            registration_sites.push(block_addr);
                        } else {
                            registration_sites.push(0);
                        }
                    }
                }
                Some(crate::executor::CallHookTag::WindowsRaiseException) => {
                    if let Some((block_addr, _)) = root.inst_op_site(call.at) {
                        raise_sites.push(block_addr);
                    }
                }
                _ => {}
            }
        }

        raise_sites.sort_unstable();
        raise_sites.dedup();
        registration_sites.sort_unstable();
        registration_sites.dedup();

        if raise_sites.is_empty() || registration_sites.is_empty() {
            return None;
        }

        raise_sites.into_iter().next()
    }

    pub(crate) fn exception_bridge_target_in_scope(
        &mut self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        target_addr: u64,
    ) -> Option<u64> {
        self.exception_bridge_guidance_target(root, scope, target_addr)
    }

    pub(crate) fn advance_current_block_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        mut state: SymState<'ctx>,
    ) -> Result<Vec<SymState<'ctx>>, String> {
        let mut active_states = Vec::new();
        if let Some(dispatched) = self.dispatch_runtime_breakpoint(&mut state) {
            active_states.push(dispatched);
        }
        let Some(block) = self.resolve_block(func, scope, &state) else {
            let missing_pc = state.pc;
            self.record_runtime_missing_block(&state, missing_pc);
            return Err(format!("missing block at 0x{missing_pc:x}"));
        };
        let block_addr = block.runtime_addr;
        let block_static_addr = block.static_addr;
        let block_func = block.func;

        let mut enqueue_forked_state = |explorer: &mut Self, mut forked: SymState<'ctx>| {
            explorer.remap_state_pc_after_block(&mut forked, block);
            forked.set_prev_pc(Some(block_addr));
            if forked.is_terminated() {
                explorer.record_runtime_exit_status(&forked.exit_status);
                explorer.stats.paths_completed += 1;
            } else {
                active_states.push(forked);
            }
        };

        match self.executor.execute_block(&mut state, block.block) {
            Ok(forked_states) => {
                self.record_depth(state.depth);
                for forked in forked_states {
                    enqueue_forked_state(self, forked);
                }
                if state.is_terminated() {
                    self.record_runtime_exit_status(&state.exit_status);
                    self.stats.paths_completed += 1;
                } else {
                    self.patch_pending_exception_resume_pc(
                        block_func,
                        &mut state,
                        block_static_addr,
                    );
                    self.finalize_active_state_after_block(
                        block_func,
                        &mut state,
                        block_addr,
                        block_static_addr,
                    );
                    active_states.push(state);
                }
                Ok(active_states)
            }
            Err(error) => Err(error.to_string()),
        }
    }

    fn resolve_block<'a>(
        &self,
        func: &'a SsaArtifact,
        scope: Option<&'a PreparedFunctionScope>,
        state: &SymState<'ctx>,
    ) -> Option<ResolvedBlock<'a>> {
        if let Some(block) = func.get_block(state.pc) {
            return Some(ResolvedBlock {
                func,
                block,
                static_addr: state.pc,
                runtime_addr: state.pc,
                runtime_aliased: false,
            });
        }
        if let Some(scope_func) = self.resolve_scope_function(func, scope, state.pc)
            && let Some(block) = scope_func.get_block(state.pc)
        {
            return Some(ResolvedBlock {
                func: scope_func,
                block,
                static_addr: state.pc,
                runtime_addr: state.pc,
                runtime_aliased: false,
            });
        }
        let static_addr = state.resolve_runtime_pc(state.pc)?;
        let scope_func = self.resolve_scope_function(func, scope, static_addr)?;
        let block = scope_func.get_block(static_addr)?;
        Some(ResolvedBlock {
            func: scope_func,
            block,
            static_addr,
            runtime_addr: state.pc,
            runtime_aliased: true,
        })
    }

    fn effective_static_pc(&self, state: &SymState<'ctx>) -> u64 {
        state.resolve_runtime_pc(state.pc).unwrap_or(state.pc)
    }

    fn dispatch_runtime_breakpoint(
        &mut self,
        state: &mut SymState<'ctx>,
    ) -> Option<SymState<'ctx>> {
        if state.dispatch_runtime_breakpoint_if_ready() {
            return None;
        }
        if let Some(breakpoint) = &state.runtime().active_breakpoint
            && breakpoint.breakpoint.as_concrete().is_none()
        {
            let pc = crate::SymValue::concrete(state.pc, breakpoint.breakpoint.bits());
            if !self.solver.can_be_equal(state, &breakpoint.breakpoint, &pc) {
                self.stats.runtime_symbolic_breakpoint_pruned += 1;
                return None;
            }
        }
        let dispatched = state.fork_symbolic_runtime_breakpoint_at(state.pc);
        if dispatched.is_some() {
            self.stats.runtime_symbolic_breakpoint_forks += 1;
        }
        dispatched
    }

    fn summarize_runtime_breakpoint_loop(
        &mut self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        block_func: &SsaArtifact,
        block: &r2ssa::FunctionSSABlock,
        state: &SymState<'ctx>,
    ) -> Option<SymState<'ctx>> {
        let branch = loops::runtime_counter_threshold_branch(block)?;
        if !self.residual_runtime_loop_summaries_enabled
            && let Some(exact) =
                self.exact_runtime_breakpoint_loop_runahead(root, scope, block, state, &branch)
        {
            let summary = loops::bounded_exact_summary(block.addr, &branch, 0, exact);
            self.stats.runtime_breakpoint_loop_exact_summaries += 1;
            debug_target_guidance_log(&format!(
                "runtime_loop_exact_summary target=0x{:x} from=0x{:x}",
                branch.target, block.addr
            ));
            return summary.resulting_state;
        }
        let summary = loops::summarize_residual_runtime_loop(
            self._ctx,
            block_func,
            block,
            state,
            &branch,
            self.residual_runtime_loop_summaries_enabled,
        );
        match summary.kind {
            LoopSummaryKind::Exact | LoopSummaryKind::BoundedExact => {
                self.stats.runtime_breakpoint_loop_exact_summaries += 1;
                if summary.kind == LoopSummaryKind::Exact {
                    self.stats.runtime_loop_exact_recurrence_summaries += 1;
                }
                self.record_exact_loop_recurrences(summary.exact_recurrences.iter().cloned());
                summary.resulting_state
            }
            LoopSummaryKind::Residual => {
                for reason in &summary.reasons {
                    if reason == "runtime_loop_unknown_carried_state" {
                        self.stats.runtime_loop_unknown_carried_state += 1;
                    }
                    if reason == "runtime_loop_iteration_budget" {
                        self.stats.runtime_loop_budget_residuals += 1;
                    }
                }
                if summary.resulting_state.is_some() {
                    self.stats.runtime_breakpoint_loop_summaries += 1;
                }
                debug_target_guidance_log(&format!(
                    "runtime_loop_summary kind={:?} target={} from=0x{:x} iterations={} carried={} reasons={}",
                    summary.kind,
                    summary
                        .exit_target
                        .map(|target| format!("0x{target:x}"))
                        .unwrap_or_else(|| "none".to_string()),
                    summary.header,
                    summary
                        .iterations
                        .map(|iterations| iterations.to_string())
                        .unwrap_or_else(|| "unknown".to_string()),
                    summary.carried_state.len(),
                    summary.reasons.join(","),
                ));
                summary.resulting_state
            }
            LoopSummaryKind::Refused => {
                self.stats.runtime_loop_refusals += 1;
                debug_target_guidance_log(&format!(
                    "runtime_loop_summary_refused block=0x{:x} reasons={}",
                    summary.header,
                    summary.reasons.join(","),
                ));
                None
            }
        }
    }

    fn record_exact_loop_recurrences(
        &mut self,
        recurrences: impl IntoIterator<Item = ExactLoopRecurrenceEvidence>,
    ) {
        const MAX_RECORDED_EXACT_RECURRENCES: usize = 128;
        for recurrence in recurrences {
            if self.stats.runtime_loop_exact_recurrences.len() >= MAX_RECORDED_EXACT_RECURRENCES {
                break;
            }
            if !self
                .stats
                .runtime_loop_exact_recurrences
                .contains(&recurrence)
            {
                self.stats.runtime_loop_exact_recurrences.push(recurrence);
            }
        }
        self.stats
            .runtime_loop_exact_recurrences
            .sort_by(|lhs, rhs| {
                (
                    lhs.header,
                    lhs.exit_target,
                    lhs.accumulator.as_str(),
                    format!("{:?}", lhs.kind),
                )
                    .cmp(&(
                        rhs.header,
                        rhs.exit_target,
                        rhs.accumulator.as_str(),
                        format!("{:?}", rhs.kind),
                    ))
            });
        let folds = self
            .stats
            .runtime_loop_exact_recurrences
            .iter()
            .filter_map(ExactLoopRecurrenceEvidence::as_fold)
            .collect::<Vec<_>>();
        self.record_exact_loop_folds(folds);
    }

    fn record_exact_loop_folds(&mut self, folds: impl IntoIterator<Item = ExactLoopFoldEvidence>) {
        const MAX_RECORDED_EXACT_FOLDS: usize = 128;
        for fold in folds {
            if self.stats.runtime_loop_exact_folds.len() >= MAX_RECORDED_EXACT_FOLDS {
                break;
            }
            if !self.stats.runtime_loop_exact_folds.contains(&fold) {
                self.stats.runtime_loop_exact_folds.push(fold);
            }
        }
        self.stats.runtime_loop_exact_folds.sort_by(|lhs, rhs| {
            (
                lhs.header,
                lhs.exit_target,
                lhs.accumulator.as_str(),
                lhs.term.addr.as_str(),
            )
                .cmp(&(
                    rhs.header,
                    rhs.exit_target,
                    rhs.accumulator.as_str(),
                    rhs.term.addr.as_str(),
                ))
        });
    }

    fn exact_runtime_breakpoint_loop_runahead(
        &mut self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        block: &r2ssa::FunctionSSABlock,
        state: &SymState<'ctx>,
        branch: &loops::RuntimeLoopBranch,
    ) -> Option<SymState<'ctx>> {
        if state.pending_exception().is_none() || state.runtime().runtime_regions.is_empty() {
            debug_target_guidance_log(&format!(
                "runtime_loop_exact_skip block=0x{:x} reason=missing_runtime_context",
                block.addr
            ));
            return None;
        }
        let mut target_probe = state.fork();
        target_probe.pc = branch.target;
        if self.resolve_block(root, scope, &target_probe).is_none() {
            debug_target_guidance_log(&format!(
                "runtime_loop_exact_skip block=0x{:x} reason=missing_target target=0x{:x}",
                block.addr, branch.target
            ));
            return None;
        }
        let Some(counter) = loops::concrete_state_var_at_block_entry(state, block, &branch.counter)
        else {
            debug_target_guidance_log(&format!(
                "runtime_loop_exact_skip block=0x{:x} reason=unknown_counter counter={}",
                block.addr,
                branch.counter.display_name()
            ));
            return None;
        };
        let Some(remaining) = branch.threshold.checked_sub(counter) else {
            debug_target_guidance_log(&format!(
                "runtime_loop_exact_skip block=0x{:x} reason=counter_past_threshold counter={} threshold={}",
                block.addr, counter, branch.threshold
            ));
            return None;
        };
        if !(8..=EXACT_RUNTIME_LOOP_MAX_ITERS).contains(&remaining) {
            debug_target_guidance_log(&format!(
                "runtime_loop_exact_skip block=0x{:x} reason=iteration_budget remaining={} threshold={}",
                block.addr, remaining, branch.threshold
            ));
            return None;
        }

        let mut runahead = state.fork();
        let mut guard_visits = 0u64;
        for block_step in 0..EXACT_RUNTIME_LOOP_MAX_BLOCK_STEPS {
            if let Some(dispatched) = self.dispatch_runtime_breakpoint(&mut runahead) {
                runahead = dispatched;
            }
            let static_pc = self.effective_static_pc(&runahead);
            if static_pc == branch.target {
                debug_target_guidance_log(&format!(
                    "runtime_loop_exact_summary target=0x{:x} from=0x{:x} guard_visits={} block_steps={}",
                    branch.target, block.addr, guard_visits, block_step
                ));
                return Some(runahead);
            }
            if runahead.is_terminated() {
                debug_target_guidance_log(&format!(
                    "runtime_loop_exact_skip block=0x{:x} reason=terminated block_steps={} status={:?}",
                    block.addr, block_step, runahead.exit_status
                ));
                return None;
            }
            if static_pc == block.addr {
                guard_visits = guard_visits.saturating_add(1);
                if guard_visits > remaining.saturating_add(1) {
                    debug_target_guidance_log(&format!(
                        "runtime_loop_exact_skip block=0x{:x} reason=guard_visit_budget visits={} remaining={}",
                        block.addr, guard_visits, remaining
                    ));
                    return None;
                }
            }
            let Some(resolved) = self.resolve_block(root, scope, &runahead) else {
                debug_target_guidance_log(&format!(
                    "runtime_loop_exact_skip block=0x{:x} reason=missing_block static_pc=0x{:x} runtime_pc=0x{:x}",
                    block.addr, static_pc, runahead.pc
                ));
                return None;
            };
            let forked = self
                .executor
                .execute_block(&mut runahead, resolved.block)
                .ok()?;
            if !forked.is_empty() {
                debug_target_guidance_log(&format!(
                    "runtime_loop_exact_skip block=0x{:x} reason=forked block_steps={} forks={}",
                    block.addr,
                    block_step,
                    forked.len()
                ));
                return None;
            }
            if runahead.is_terminated() {
                debug_target_guidance_log(&format!(
                    "runtime_loop_exact_skip block=0x{:x} reason=terminated block_steps={} status={:?}",
                    block.addr, block_step, runahead.exit_status
                ));
                return None;
            }
            self.patch_pending_exception_resume_pc(
                resolved.func,
                &mut runahead,
                resolved.static_addr,
            );
            self.finalize_active_state_after_block(
                resolved.func,
                &mut runahead,
                resolved.runtime_addr,
                resolved.static_addr,
            );
        }
        debug_target_guidance_log(&format!(
            "runtime_loop_exact_skip block=0x{:x} reason=block_step_budget budget={}",
            block.addr, EXACT_RUNTIME_LOOP_MAX_BLOCK_STEPS
        ));
        None
    }

    fn direct_call_fork_targets(
        &self,
        root: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        block: &r2ssa::FunctionSSABlock,
    ) -> Option<HashSet<u64>> {
        let targets = block
            .ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::Call { target } => loops::parse_address_var(target),
                _ => None,
            })
            .filter(|target| self.executor.call_hook_tag(*target).is_none())
            .filter(|target| self.resolve_scope_function(root, scope, *target).is_some())
            .collect::<HashSet<_>>();
        (!targets.is_empty()).then_some(targets)
    }

    fn remap_state_pc_after_block(&self, state: &mut SymState<'ctx>, block: ResolvedBlock<'_>) {
        if !block.runtime_aliased || state.pc == block.runtime_addr {
            return;
        }
        if let Some(runtime_pc) = state.remap_static_pc_to_runtime(state.pc) {
            state.pc = runtime_pc;
        }
    }

    /// Create a new path explorer.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            _ctx: ctx,
            executor: SymExecutor::new(ctx),
            solver: SymSolver::new(ctx),
            config: ExploreConfig::default(),
            stats: ExploreStats::default(),
            target_guided_queries: false,
            exception_bridge_guidance_enabled: true,
            residual_runtime_loop_summaries_enabled: true,
            derived_call_summaries: HashMap::new(),
            target_distance_cache: TargetDistanceCache::new(),
            solve_tactic_config: SolveTacticConfig::default(),
        }
    }

    /// Create a path explorer with configuration.
    pub fn with_config(ctx: &'ctx Context, config: ExploreConfig) -> Self {
        let solver = if let Some(timeout) = config.timeout {
            SymSolver::with_timeout(ctx, timeout)
        } else {
            SymSolver::new(ctx)
        };

        Self {
            _ctx: ctx,
            executor: SymExecutor::new(ctx),
            solver,
            config,
            stats: ExploreStats::default(),
            target_guided_queries: false,
            exception_bridge_guidance_enabled: true,
            residual_runtime_loop_summaries_enabled: true,
            derived_call_summaries: HashMap::new(),
            target_distance_cache: TargetDistanceCache::new(),
            solve_tactic_config: SolveTacticConfig::default(),
        }
    }

    /// Get the exploration statistics.
    pub fn stats(&self) -> &ExploreStats {
        &self.stats
    }

    pub fn set_solve_tactic_config(&mut self, config: SolveTacticConfig) {
        self.solve_tactic_config = config;
    }

    pub fn solve_tactic_config(&self) -> &SolveTacticConfig {
        &self.solve_tactic_config
    }

    pub(crate) fn with_isolated_stats<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, ExploreStats) {
        let previous = std::mem::take(&mut self.stats);
        let result = f(self);
        let isolated = std::mem::take(&mut self.stats);
        self.stats = previous;
        (result, isolated)
    }

    /// Get the solver for additional queries.
    pub fn solver(&self) -> &SymSolver<'ctx> {
        &self.solver
    }

    pub(crate) fn with_prune_infeasible<T>(
        &mut self,
        prune_infeasible: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = self.config.prune_infeasible;
        self.config.prune_infeasible = prune_infeasible;
        let result = f(self);
        self.config.prune_infeasible = previous;
        result
    }

    pub(crate) fn with_exception_bridge_guidance<T>(
        &mut self,
        enabled: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = self.exception_bridge_guidance_enabled;
        self.exception_bridge_guidance_enabled = enabled;
        let result = f(self);
        self.exception_bridge_guidance_enabled = previous;
        result
    }

    pub(crate) fn with_residual_runtime_loop_summaries<T>(
        &mut self,
        enabled: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = self.residual_runtime_loop_summaries_enabled;
        self.residual_runtime_loop_summaries_enabled = enabled;
        let result = f(self);
        self.residual_runtime_loop_summaries_enabled = previous;
        result
    }

    /// Enable target-guided ordering for query-only helpers.
    pub fn set_target_guided_queries(&mut self, enabled: bool) {
        self.target_guided_queries = enabled;
    }

    /// Whether target-guided ordering is enabled for query helpers.
    pub fn target_guided_queries_enabled(&self) -> bool {
        self.target_guided_queries
    }

    /// Register a call hook for a concrete target address.
    pub fn register_call_hook<F>(&mut self, addr: u64, hook: F)
    where
        F: Fn(&mut SymState<'ctx>) -> crate::executor::CallHookResult + 'ctx,
    {
        self.derived_call_summaries.remove(&addr);
        self.executor
            .register_call_hook(addr, move |state| Ok(hook(state)));
    }

    pub fn register_tagged_call_hook<F>(
        &mut self,
        addr: u64,
        tag: crate::executor::CallHookTag,
        hook: F,
    ) where
        F: Fn(&mut SymState<'ctx>) -> crate::executor::CallHookResult + 'ctx,
    {
        self.derived_call_summaries.remove(&addr);
        self.executor
            .register_tagged_call_hook(addr, tag, move |state| Ok(hook(state)));
    }

    pub(crate) fn register_derived_call_hook<F>(
        &mut self,
        addr: u64,
        summary: Rc<DerivedFunctionSummary<'ctx>>,
        callconv: CallConv,
        hook: F,
    ) where
        F: Fn(&mut SymState<'ctx>) -> crate::executor::CallHookResult + 'ctx,
    {
        self.derived_call_summaries
            .insert(addr, RegisteredDerivedCallSummary { summary, callconv });
        self.executor
            .register_call_hook(addr, move |state| Ok(hook(state)));
    }

    pub(crate) fn derived_call_summary_views(&self) -> HashMap<u64, DerivedCallSummaryView<'ctx>> {
        self.derived_call_summaries
            .iter()
            .map(|(addr, registered)| {
                (
                    *addr,
                    DerivedCallSummaryView {
                        summary: registered.summary.clone(),
                        callconv: registered.callconv.clone(),
                    },
                )
            })
            .collect()
    }

    /// Solve a path's constraints and extract concrete values.
    ///
    /// Returns None if the path is infeasible.
    pub fn solve_path(&self, path: &PathResult<'ctx>) -> Option<SolvedPath> {
        if !path.feasible {
            return None;
        }

        // Get a model from the solver
        let model = self.solver.solve(&path.state)?;

        let mut solved = SolvedPath {
            final_pc: path.state.pc,
            num_constraints: path.state.num_constraints(),
            ..Default::default()
        };

        // Extract concrete register values
        for (name, value) in path.state.registers() {
            if let Some(concrete) = model.eval(value) {
                solved.registers.insert(name.clone(), concrete);
            }
        }

        // Include explicitly tracked symbolic inputs.
        for (name, value) in path.state.symbolic_inputs() {
            if let Some(concrete) = model.eval(value) {
                solved.inputs.entry(name.clone()).or_insert(concrete);
            }
        }

        // Try to identify symbolic inputs (variables starting with "sym_").
        for (name, value) in path.state.registers() {
            if solved.inputs.contains_key(name) {
                continue;
            }
            if (name.starts_with("sym_") || value.is_symbolic())
                && let Some(concrete) = model.eval(value)
            {
                solved.inputs.insert(name.clone(), concrete);
            }
        }

        // Extract tracked symbolic memory buffers.
        for region in path.state.symbolic_memory() {
            if let Some(bytes) = model.eval_bytes(&region.value, region.size as usize) {
                solved.memory.insert(region.name.clone(), bytes);
            }
        }

        for input in path.state.symbolic_fd_inputs().values() {
            let bytes: Option<Vec<u8>> = input
                .bytes
                .iter()
                .map(|byte| model.eval(byte).map(|v| v as u8))
                .collect();
            if let Some(bytes) = bytes {
                solved.input_buffers.insert(input.name.clone(), bytes);
            }
        }

        Some(solved)
    }

    /// Solve a path after applying constraint-graph tactics and exact input-domain tactics.
    pub fn solve_path_with_constraint_graph_tactics(
        &self,
        path: &PathResult<'ctx>,
        graph: &FinalConstraintGraph,
        recurrences: &[ExactLoopRecurrenceEvidence],
    ) -> Option<SolvedPath> {
        if !path.feasible || !self.solve_tactic_config.enabled {
            return None;
        }
        let folds = loops::exact_fold_evidence_from_recurrences(recurrences);

        if !graph.is_empty() {
            for candidate in tactic_candidates_for_constraint_graph(
                graph,
                Some(&path.state),
                &self.solve_tactic_config,
            ) {
                let mut state = path.state.fork();
                let report = constrain_exact_recurrence_candidate(
                    &mut state,
                    &candidate.recurrence,
                    &candidate.bytes,
                );
                if report.constrained_bytes == 0 {
                    continue;
                }
                let constrained_path = PathResult {
                    state,
                    exit_status: path.exit_status.clone(),
                    depth: path.depth,
                    feasible: path.feasible,
                };
                if let Some(mut solution) = self.solve_path(&constrained_path) {
                    solution.generation = Some(SolvedPathGeneration {
                        kind: if candidate.used_mitm {
                            SolvedPathGenerationKind::MitmConstraintTactic
                        } else {
                            SolvedPathGenerationKind::ExactRecurrenceConstraintTactic
                        },
                        reason: candidate.reason,
                        constrained_bytes: report.constrained_bytes,
                    });
                    return Some(solution);
                }
            }
        }

        for domain in &self.solve_tactic_config.preferred_domains {
            let mut state = path.state.fork();
            let report = constrain_exact_fold_inputs(
                &mut state,
                &folds,
                domain,
                self.solve_tactic_config.max_constrained_bytes,
            );
            if report.constrained_bytes == 0 {
                continue;
            }
            let constrained_path = PathResult {
                state,
                exit_status: path.exit_status.clone(),
                depth: path.depth,
                feasible: path.feasible,
            };
            if let Some(mut solution) = self.solve_path(&constrained_path) {
                solution.generation = Some(SolvedPathGeneration {
                    kind: SolvedPathGenerationKind::DomainConstraintTactic,
                    reason: "exact fold input-domain constraint".to_string(),
                    constrained_bytes: report.constrained_bytes,
                });
                return Some(solution);
            }
        }
        None
    }

    /// Solve all feasible paths and return concrete solutions.
    pub fn solve_all_paths(&self, paths: &[PathResult<'ctx>]) -> Vec<Option<SolvedPath>> {
        paths.iter().map(|p| self.solve_path(p)).collect()
    }

    /// Whether the most recent exploration stopped because of a budget limit.
    pub fn budget_exhausted(&self) -> bool {
        self.stats.timed_out || self.stats.max_states_exhausted
    }

    fn record_depth(&mut self, depth: usize) {
        if depth > self.stats.max_depth_reached {
            self.stats.max_depth_reached = depth;
        }
    }

    fn state_rank(&self, state: &SymState<'ctx>, id: usize) -> (usize, usize, usize) {
        (state.num_constraints(), state.depth, id)
    }

    fn prune_subsumed_same_pc_state(
        &mut self,
        worklist: &mut StateWorklist<'ctx>,
        state: SymState<'ctx>,
    ) -> Option<SymState<'ctx>> {
        if !self.config.subsumption_states || state.is_terminated() {
            return Some(state);
        }

        let candidate_ids = worklist.same_pc_ids(state.pc);
        if candidate_ids.is_empty() {
            return Some(state);
        }

        let state_fingerprint = state.semantic_fingerprint();
        let state_rank = self.state_rank(&state, worklist.slots.len());
        let mut keep_state = true;

        for candidate_id in candidate_ids {
            let Some(existing) = worklist.state(candidate_id) else {
                continue;
            };
            if existing.is_terminated() || existing.semantic_fingerprint() != state_fingerprint {
                continue;
            }

            self.stats.subsumption_checks += 1;
            let existing_subsumes_new = self.solver.implies(&state, existing);
            let new_subsumes_existing = self.solver.implies(existing, &state);

            match (existing_subsumes_new, new_subsumes_existing) {
                (Some(true), Some(true)) => {
                    let existing_rank = self.state_rank(existing, candidate_id);
                    if existing_rank <= state_rank {
                        self.stats.subsumption_hits += 1;
                        self.stats.states_subsumed += 1;
                        keep_state = false;
                        break;
                    }
                    if worklist.remove_slot(candidate_id).is_some() {
                        self.stats.subsumption_hits += 1;
                        self.stats.states_subsumed += 1;
                    }
                }
                (Some(true), _) => {
                    self.stats.subsumption_hits += 1;
                    self.stats.states_subsumed += 1;
                    keep_state = false;
                    break;
                }
                (_, Some(true)) => {
                    if worklist.remove_slot(candidate_id).is_some() {
                        self.stats.subsumption_hits += 1;
                        self.stats.states_subsumed += 1;
                    }
                }
                _ => {}
            }
        }

        keep_state.then_some(state)
    }

    fn drive_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        mode: &mut DriverMode<'ctx>,
    ) {
        let start_time = Instant::now();
        let mut worklist = StateWorklist::new(self.config.strategy);
        worklist.push(initial_state);

        'worklist: while let Some(mut state) = worklist.pop_next() {
            if self.config.merge_states
                && let Some(other) = worklist.take_same_pc(state.pc)
            {
                state = state.merge_with(&other);
            }

            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
                && mode.on_timeout()
            {
                self.stats.timed_out = true;
                break;
            }

            match mode.on_state_popped(self, state) {
                DriverAction::Continue(next_state) => state = *next_state,
                DriverAction::Skip => continue,
                DriverAction::Finish => break,
            }

            if self.stats.states_explored >= self.config.max_states && mode.on_max_states() {
                self.stats.max_states_exhausted = true;
                break;
            }

            if state.depth >= self.config.max_depth {
                match mode.on_depth_limit(self, state, self.config.max_completed_paths) {
                    DriverAction::Continue(next_state) => state = *next_state,
                    DriverAction::Skip => continue,
                    DriverAction::Finish => break,
                }
            }

            self.stats.states_explored += 1;

            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                mode.on_unsat_pruned();
                continue;
            }

            let inline_start_depth = state.depth;
            let mut revisit_current_state = false;
            loop {
                if let Some(timeout) = self.config.timeout
                    && start_time.elapsed() > timeout
                    && mode.on_timeout()
                {
                    self.stats.timed_out = true;
                    break 'worklist;
                }

                if std::mem::take(&mut revisit_current_state) {
                    match mode.on_state_popped(self, state) {
                        DriverAction::Continue(next_state) => state = *next_state,
                        DriverAction::Skip => continue 'worklist,
                        DriverAction::Finish => break 'worklist,
                    }
                }

                let Some(block) = self.resolve_block(func, scope, &state) else {
                    let missing_pc = state.pc;
                    match mode.on_missing_block(
                        self,
                        state,
                        missing_pc,
                        self.config.max_completed_paths,
                    ) {
                        DriverAction::Finish => break 'worklist,
                        DriverAction::Continue(_) | DriverAction::Skip => continue 'worklist,
                    }
                };
                let block_addr = block.runtime_addr;
                let block_static_addr = block.static_addr;
                let block_func = block.func;
                match self.executor.execute_block(&mut state, block.block) {
                    Ok(forked_states) => {
                        self.record_depth(state.depth);

                        let had_forks = !forked_states.is_empty();
                        for mut forked in forked_states {
                            self.remap_state_pc_after_block(&mut forked, block);
                            forked.set_prev_pc(Some(block_addr));
                            if mode.allow_enqueue(&forked)
                                && let Some(forked) =
                                    self.prune_subsumed_same_pc_state(&mut worklist, forked)
                            {
                                worklist.push(forked);
                            }
                        }

                        if !state.is_terminated() {
                            self.patch_pending_exception_resume_pc(
                                block_func,
                                &mut state,
                                block_static_addr,
                            );
                            self.finalize_active_state_after_block(
                                block_func,
                                &mut state,
                                block_addr,
                                block_static_addr,
                            );
                            if mode.allow_enqueue(&state) {
                                let can_inline_continue = !had_forks
                                    && state.depth.saturating_sub(inline_start_depth)
                                        < self.max_inline_runahead_depth_delta();
                                if can_inline_continue {
                                    revisit_current_state = true;
                                    continue;
                                }
                                if let Some(state) =
                                    self.prune_subsumed_same_pc_state(&mut worklist, state)
                                {
                                    worklist.push(state);
                                }
                            }
                        } else {
                            match mode.on_terminated_state(
                                self,
                                state,
                                block_addr,
                                self.config.max_completed_paths,
                            ) {
                                DriverAction::Finish => break 'worklist,
                                DriverAction::Continue(_) | DriverAction::Skip => {
                                    continue 'worklist;
                                }
                            }
                        }
                        break;
                    }
                    Err(e) => match mode.on_execute_error(
                        self,
                        state,
                        block_addr,
                        e.to_string(),
                        self.config.max_completed_paths,
                    ) {
                        DriverAction::Finish => break 'worklist,
                        DriverAction::Continue(_) | DriverAction::Skip => continue 'worklist,
                    },
                }
            }
        }

        self.stats.total_time = start_time.elapsed();
    }

    fn target_guidance_context(
        &mut self,
        func: &SsaArtifact,
        target_addr: u64,
        allow_cross_function_states: bool,
    ) -> TargetGuidanceContext {
        let distances = self.target_distance_map(func, target_addr);
        let reachable_blocks = distances.keys().copied().collect::<HashSet<_>>();
        let mut call_targets_by_block: HashMap<u64, Vec<u64>> = HashMap::new();
        let mut block_summary_rank: HashMap<u64, BlockSummaryRank> = HashMap::new();

        for call in func.call_sites().by_id.values() {
            let Some(target) = func.resolved_call_target(call) else {
                continue;
            };
            let Some((block_addr, _)) = func.inst_op_site(call.at) else {
                continue;
            };
            call_targets_by_block
                .entry(block_addr)
                .or_default()
                .push(target);

            let Some(binding) = self.derived_call_summaries.get(&target) else {
                continue;
            };
            let entry = block_summary_rank
                .entry(block_addr)
                .or_insert_with(|| BlockSummaryRank {
                    has_summary: false,
                    has_exact_summary: false,
                    min_case_count: usize::MAX,
                });
            entry.has_summary = true;
            entry.has_exact_summary |= matches!(
                binding.summary.completion,
                crate::sim::DerivedSummaryCompletion::Exact
            );
            entry.min_case_count = entry.min_case_count.min(binding.summary.cases.len());
        }

        TargetGuidanceContext {
            target_addr,
            distances,
            reachable_blocks,
            call_targets_by_block,
            block_summary_rank,
            allow_cross_function_states,
        }
    }

    fn symbolic_fanout_proxy(&self, state: &SymState<'ctx>) -> usize {
        state
            .registers()
            .values()
            .filter(|value| value.is_symbolic())
            .count()
            .saturating_add(state.symbolic_inputs().len())
            .saturating_add(state.symbolic_memory().len())
            .saturating_add(state.symbolic_fd_inputs().len())
    }

    fn state_summary_guidance(
        &self,
        guidance: &TargetGuidanceContext,
        state: &SymState<'ctx>,
    ) -> StateSummaryGuidance {
        let static_pc = self.effective_static_pc(state);
        let Some(targets) = guidance.call_targets_by_block.get(&static_pc) else {
            return StateSummaryGuidance::default();
        };

        let mut result = StateSummaryGuidance {
            summary_hits: 0,
            min_feasible_cases: usize::MAX,
            contradictory: false,
        };

        for target in targets {
            let Some(binding) = self.derived_call_summaries.get(target) else {
                continue;
            };
            let summary_guidance = evaluate_derived_summary_guidance(
                state,
                &binding.summary,
                &binding.callconv,
                &self.solver,
            );
            if !summary_guidance.summary_known {
                continue;
            }
            result.summary_hits += 1;
            result.min_feasible_cases = result
                .min_feasible_cases
                .min(summary_guidance.feasible_cases.max(1));
            if summary_guidance.contradictory {
                result.contradictory = true;
                break;
            }
        }

        if result.summary_hits == 0 {
            StateSummaryGuidance::default()
        } else {
            result
        }
    }

    fn target_enqueue_allowed(
        &mut self,
        guidance: &TargetGuidanceContext,
        state: &SymState<'ctx>,
    ) -> bool {
        let static_pc = self.effective_static_pc(state);
        let runtime_continuation_bridge =
            state.pending_exception().is_some() || state.runtime_region_for_pc(state.pc).is_some();
        if !guidance.reachable_blocks.contains(&static_pc)
            && !guidance.allow_cross_function_states
            && !runtime_continuation_bridge
        {
            self.stats.target_pruned_cfg_unreachable += 1;
            debug_target_guidance_log(&format!(
                "cfg_prune target=0x{:x} runtime_pc=0x{:x} static_pc=0x{:x} prev_pc={} terminated={} depth={}",
                guidance.target_addr,
                state.pc,
                static_pc,
                state
                    .prev_pc()
                    .map(|pc| format!("0x{pc:x}"))
                    .unwrap_or_else(|| "none".to_string()),
                state.is_terminated(),
                state.depth,
            ));
            return false;
        }

        let summary_guidance = self.state_summary_guidance(guidance, state);
        if summary_guidance.summary_hits > 0 {
            self.stats.target_summary_rank_hits += 1;
        }
        if summary_guidance.contradictory {
            self.stats.target_pruned_summary_contradiction += 1;
            return false;
        }
        true
    }

    fn enqueue_target_guided_state(
        &mut self,
        worklist: &mut StateWorklist<'ctx>,
        target_heap: &mut BinaryHeap<Reverse<TargetGuidedQueueEntry>>,
        guidance: &TargetGuidanceContext,
        mode: &mut DriverMode<'ctx>,
        state: SymState<'ctx>,
    ) {
        if !mode.allow_enqueue(&state) || !self.target_enqueue_allowed(guidance, &state) {
            return;
        }
        let Some(state) = self.prune_subsumed_same_pc_state(worklist, state) else {
            return;
        };
        let id = worklist.push(state);
        if let Some(state) = worklist.state(id) {
            target_heap.push(Reverse(TargetGuidedQueueEntry {
                rank: self.state_target_rank(state, id, guidance),
                id,
            }));
        }
    }

    fn drive_target_guided_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        mode: &mut DriverMode<'ctx>,
        target_addr: u64,
        allow_cross_function_states: bool,
    ) {
        let start_time = Instant::now();
        let mut worklist = StateWorklist::new(self.config.strategy);
        let mut target_heap: BinaryHeap<Reverse<TargetGuidedQueueEntry>> = BinaryHeap::new();
        let guidance = self.target_guidance_context(func, target_addr, allow_cross_function_states);
        if self.target_enqueue_allowed(&guidance, &initial_state)
            && let Some(state) = self.prune_subsumed_same_pc_state(&mut worklist, initial_state)
        {
            let id = worklist.push(state);
            if let Some(state) = worklist.state(id) {
                target_heap.push(Reverse(TargetGuidedQueueEntry {
                    rank: self.state_target_rank(state, id, &guidance),
                    id,
                }));
            }
        }

        'worklist: while let Some((mut state, reordered)) =
            self.pop_target_guided_state(&mut worklist, &mut target_heap)
        {
            if reordered {
                self.stats.target_guided_reorders += 1;
            }
            if self.config.merge_states
                && let Some(other) = worklist.take_same_pc(state.pc)
            {
                state = state.merge_with(&other);
            }

            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
                && mode.on_timeout()
            {
                self.stats.timed_out = true;
                break;
            }

            match mode.on_state_popped(self, state) {
                DriverAction::Continue(next_state) => state = *next_state,
                DriverAction::Skip => continue,
                DriverAction::Finish => break,
            }

            if self.stats.states_explored >= self.config.max_states && mode.on_max_states() {
                self.stats.max_states_exhausted = true;
                break;
            }

            if state.depth >= self.config.max_depth {
                match mode.on_depth_limit(self, state, self.config.max_completed_paths) {
                    DriverAction::Continue(next_state) => state = *next_state,
                    DriverAction::Skip => continue,
                    DriverAction::Finish => break,
                }
            }

            self.stats.states_explored += 1;

            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                debug_target_guidance_log(&format!(
                    "unsat_prune target=0x{:x} runtime_pc=0x{:x} static_pc=0x{:x} prev_pc={} terminated={} depth={} constraints={}",
                    guidance.target_addr,
                    state.pc,
                    self.effective_static_pc(&state),
                    state
                        .prev_pc()
                        .map(|pc| format!("0x{pc:x}"))
                        .unwrap_or_else(|| "none".to_string()),
                    state.is_terminated(),
                    state.depth,
                    state.num_constraints(),
                ));
                mode.on_unsat_pruned();
                continue;
            }

            let inline_start_depth = state.depth;
            let mut revisit_current_state = false;
            loop {
                let mut had_runtime_dispatch = false;
                if let Some(timeout) = self.config.timeout
                    && start_time.elapsed() > timeout
                    && mode.on_timeout()
                {
                    self.stats.timed_out = true;
                    break 'worklist;
                }

                if std::mem::take(&mut revisit_current_state) {
                    match mode.on_state_popped(self, state) {
                        DriverAction::Continue(next_state) => state = *next_state,
                        DriverAction::Skip => continue 'worklist,
                        DriverAction::Finish => break 'worklist,
                    }
                }

                if let Some(dispatched) = self.dispatch_runtime_breakpoint(&mut state) {
                    had_runtime_dispatch = true;
                    self.enqueue_target_guided_state(
                        &mut worklist,
                        &mut target_heap,
                        &guidance,
                        mode,
                        dispatched,
                    );
                }

                if !self.target_enqueue_allowed(&guidance, &state) {
                    continue 'worklist;
                }

                let Some(block) = self.resolve_block(func, scope, &state) else {
                    let missing_pc = state.pc;
                    match mode.on_missing_block(
                        self,
                        state,
                        missing_pc,
                        self.config.max_completed_paths,
                    ) {
                        DriverAction::Finish => break 'worklist,
                        DriverAction::Continue(_) | DriverAction::Skip => continue 'worklist,
                    }
                };
                let block_addr = block.runtime_addr;
                let block_static_addr = block.static_addr;
                let block_func = block.func;
                debug_target_guidance_log(&format!(
                    "block_exec target=0x{:x} runtime_pc=0x{:x} static_pc=0x{:x} depth={} states={} constraints={}",
                    guidance.target_addr,
                    block_addr,
                    block_static_addr,
                    state.depth,
                    self.stats.states_explored,
                    state.num_constraints(),
                ));

                if let Some(summarized) = self.summarize_runtime_breakpoint_loop(
                    func,
                    scope,
                    block_func,
                    block.block,
                    &state,
                ) {
                    self.enqueue_target_guided_state(
                        &mut worklist,
                        &mut target_heap,
                        &guidance,
                        mode,
                        summarized,
                    );
                    continue 'worklist;
                }

                let direct_call_targets = self.direct_call_fork_targets(func, scope, block.block);
                if let Some(targets) = direct_call_targets.as_ref() {
                    let mut targets = targets.iter().copied().collect::<Vec<_>>();
                    targets.sort_unstable();
                    debug_target_guidance_log(&format!(
                        "direct_call_fork_targets block=0x{:x} targets={:?}",
                        block_static_addr, targets
                    ));
                }
                let previous_direct_call_targets = self
                    .executor
                    .replace_direct_call_fork_targets(direct_call_targets);
                let execution = self.executor.execute_block(&mut state, block.block);
                self.executor
                    .replace_direct_call_fork_targets(previous_direct_call_targets);

                match execution {
                    Ok(forked_states) => {
                        self.record_depth(state.depth);
                        debug_target_guidance_log(&format!(
                            "block_done target=0x{:x} runtime_pc=0x{:x} static_pc=0x{:x} depth={} forks={} terminated={}",
                            guidance.target_addr,
                            block_addr,
                            block_static_addr,
                            state.depth,
                            forked_states.len(),
                            state.is_terminated(),
                        ));

                        let had_forks = !forked_states.is_empty();
                        for mut forked in forked_states {
                            self.remap_state_pc_after_block(&mut forked, block);
                            forked.set_prev_pc(Some(block_addr));
                            self.enqueue_target_guided_state(
                                &mut worklist,
                                &mut target_heap,
                                &guidance,
                                mode,
                                forked,
                            );
                        }

                        if !state.is_terminated() {
                            self.patch_pending_exception_resume_pc(
                                block_func,
                                &mut state,
                                block_static_addr,
                            );
                            self.finalize_active_state_after_block(
                                block_func,
                                &mut state,
                                block_addr,
                                block_static_addr,
                            );
                            if mode.allow_enqueue(&state)
                                && self.target_enqueue_allowed(&guidance, &state)
                            {
                                let can_inline_continue = !had_forks
                                    && !had_runtime_dispatch
                                    && state.depth.saturating_sub(inline_start_depth)
                                        < self.max_inline_runahead_depth_delta();
                                if can_inline_continue {
                                    revisit_current_state = true;
                                    continue;
                                }
                                if let Some(state) =
                                    self.prune_subsumed_same_pc_state(&mut worklist, state)
                                {
                                    let id = worklist.push(state);
                                    if let Some(state) = worklist.state(id) {
                                        target_heap.push(Reverse(TargetGuidedQueueEntry {
                                            rank: self.state_target_rank(state, id, &guidance),
                                            id,
                                        }));
                                    }
                                }
                            }
                        } else {
                            let resumed =
                                self.fork_symbolic_exception_resume_targets(func, scope, &state);
                            if !resumed.is_empty() {
                                for resumed_state in resumed {
                                    self.enqueue_target_guided_state(
                                        &mut worklist,
                                        &mut target_heap,
                                        &guidance,
                                        mode,
                                        resumed_state,
                                    );
                                }
                                continue 'worklist;
                            }
                            match mode.on_terminated_state(
                                self,
                                state,
                                block_addr,
                                self.config.max_completed_paths,
                            ) {
                                DriverAction::Finish => break 'worklist,
                                DriverAction::Continue(_) | DriverAction::Skip => {
                                    continue 'worklist;
                                }
                            }
                        }
                        break;
                    }
                    Err(e) => match mode.on_execute_error(
                        self,
                        state,
                        block_addr,
                        e.to_string(),
                        self.config.max_completed_paths,
                    ) {
                        DriverAction::Finish => break 'worklist,
                        DriverAction::Continue(_) | DriverAction::Skip => continue 'worklist,
                    },
                }
            }
        }

        self.stats.total_time = start_time.elapsed();
    }

    fn target_distance_map(&mut self, func: &SsaArtifact, target_addr: u64) -> HashMap<u64, usize> {
        let key = (func.entry, target_addr);
        if let Some(cached) = self.target_distance_cache.get(&key) {
            return cached;
        }
        let distances = self.compute_target_distance_map(func, target_addr);
        self.target_distance_cache.insert(key, distances.clone());
        distances
    }

    fn compute_target_distance_map(
        &self,
        func: &SsaArtifact,
        target_addr: u64,
    ) -> HashMap<u64, usize> {
        let mut predecessors: HashMap<u64, Vec<u64>> = HashMap::new();
        for addr in func.cfg().block_addrs() {
            let Some(block) = func.cfg().get_block(addr) else {
                continue;
            };
            for succ in block.successors() {
                predecessors.entry(succ).or_default().push(addr);
            }
        }

        let mut distances: HashMap<u64, usize> = HashMap::new();
        let mut queue = VecDeque::new();
        distances.insert(target_addr, 0);
        queue.push_back(target_addr);

        while let Some(addr) = queue.pop_front() {
            let distance = distances[&addr];
            for pred in predecessors.get(&addr).into_iter().flatten() {
                if distances.contains_key(pred) {
                    continue;
                }
                distances.insert(*pred, distance.saturating_add(1));
                queue.push_back(*pred);
            }
        }

        distances
    }

    fn pop_target_guided_state(
        &mut self,
        worklist: &mut StateWorklist<'ctx>,
        heap: &mut BinaryHeap<Reverse<TargetGuidedQueueEntry>>,
    ) -> Option<(SymState<'ctx>, bool)> {
        loop {
            while let Some(Reverse(entry)) = heap.peek() {
                if worklist.state(entry.id).is_some() {
                    break;
                }
                heap.pop();
            }

            let Reverse(entry) = heap.pop()?;
            let default_candidate = worklist.default_candidate();
            let reordered = default_candidate.is_some_and(|candidate| candidate != entry.id);
            if let Some(state) = worklist.take_slot(entry.id) {
                return Some((state, reordered));
            }
        }
    }

    fn state_target_rank(
        &self,
        state: &SymState<'ctx>,
        id: usize,
        guidance: &TargetGuidanceContext,
    ) -> (
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
        usize,
    ) {
        let static_pc = self.effective_static_pc(state);
        let reachable = guidance.reachable_blocks.contains(&static_pc);
        let runtime_continuation_bridge =
            state.pending_exception().is_some() || state.runtime_region_for_pc(state.pc).is_some();
        let runtime_walk_penalty = usize::from(
            state.pending_exception().is_none() && state.runtime_region_for_pc(state.pc).is_some(),
        );
        let reachability_penalty = usize::from(!(reachable || runtime_continuation_bridge));
        let distance = if reachable {
            guidance
                .distances
                .get(&static_pc)
                .copied()
                .unwrap_or(usize::MAX)
        } else if runtime_continuation_bridge {
            0
        } else {
            usize::MAX
        };
        let summary_rank = guidance
            .block_summary_rank
            .get(&static_pc)
            .cloned()
            .unwrap_or_default();
        let summary_known_penalty = usize::from(!summary_rank.has_summary);
        let summary_exact_penalty = usize::from(!summary_rank.has_exact_summary);
        let summary_case_rank = if summary_rank.has_summary {
            summary_rank.min_case_count
        } else {
            usize::MAX
        };
        (
            reachability_penalty,
            distance,
            summary_known_penalty,
            summary_exact_penalty,
            summary_case_rank,
            runtime_walk_penalty,
            self.symbolic_fanout_proxy(state),
            state.num_constraints(),
            state.depth,
            id,
        )
    }

    /// Explore all paths in a function.
    pub fn explore(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
    ) -> Vec<PathResult<'ctx>> {
        self.explore_in_scope(func, None, initial_state)
    }

    pub fn explore_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
    ) -> Vec<PathResult<'ctx>> {
        if self.config.max_completed_paths == Some(0) {
            return Vec::new();
        }
        let mut mode = DriverMode::Explore {
            results: Vec::new(),
        };
        self.drive_in_scope(func, scope, initial_state, &mut mode);
        match mode {
            DriverMode::Explore { results } => results,
            _ => unreachable!("explore should always use explore mode"),
        }
    }

    fn fallthrough_target(&self, func: &SsaArtifact, block_addr: u64) -> Option<u64> {
        let block = func.cfg().get_block(block_addr)?;
        match block.terminator {
            BlockTerminator::Fallthrough { next } => Some(next),
            BlockTerminator::ConditionalBranch { false_target, .. } => Some(false_target),
            BlockTerminator::Call { fallthrough, .. } => fallthrough,
            BlockTerminator::IndirectCall { fallthrough } => fallthrough,
            BlockTerminator::Branch { target } => Some(target),
            _ => None,
        }
    }

    /// Explore paths to find inputs that reach a target address.
    pub fn find_path_to(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> Option<PathResult<'ctx>> {
        self.find_path_to_in_scope(func, None, initial_state, target_addr)
    }

    pub fn find_path_to_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> Option<PathResult<'ctx>> {
        self.find_path_to_in_scope_with_feasibility(func, scope, initial_state, target_addr, true)
    }

    fn find_path_to_in_scope_with_feasibility(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
        require_feasible: bool,
    ) -> Option<PathResult<'ctx>> {
        let mut mode = DriverMode::FindFirst {
            target_addr,
            require_feasible,
            found: None,
        };
        let bridge_target = self.exception_bridge_guidance_target(func, scope, target_addr);
        let guidance_target = bridge_target.unwrap_or(target_addr);
        let guidance_func = if bridge_target.is_some() {
            Some(func)
        } else {
            self.resolve_scope_function(func, scope, target_addr)
        };
        let allow_cross_function_states = bridge_target.is_none()
            && guidance_func.is_some_and(|guidance_func| guidance_func.entry != func.entry);
        debug_target_guidance_log(&format!(
            "search_setup target=0x{:x} bridge={} guidance_entry={} target_guided={} cross={}",
            target_addr,
            bridge_target
                .map(|target| format!("0x{target:x}"))
                .unwrap_or_else(|| "none".to_string()),
            guidance_func
                .map(|function| format!("0x{:x}", function.entry))
                .unwrap_or_else(|| "none".to_string()),
            self.target_guided_queries,
            allow_cross_function_states,
        ));
        if self.target_guided_queries && guidance_func.is_some() {
            self.drive_target_guided_in_scope(
                guidance_func.unwrap_or(func),
                scope,
                initial_state,
                &mut mode,
                guidance_target,
                allow_cross_function_states,
            );
        } else {
            self.drive_in_scope(func, scope, initial_state, &mut mode);
        }
        match mode {
            DriverMode::FindFirst { found, .. } => found,
            _ => unreachable!("find_path_to should always use first-match mode"),
        }
    }

    /// Explore paths to collect all feasible states that reach a target address.
    pub fn find_paths_to(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> Vec<PathResult<'ctx>> {
        self.find_paths_to_in_scope(func, None, initial_state, target_addr)
    }

    pub fn find_paths_to_in_scope(
        &mut self,
        func: &SsaArtifact,
        scope: Option<&PreparedFunctionScope>,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> Vec<PathResult<'ctx>> {
        let mut mode = DriverMode::FindAll {
            target_addr,
            require_feasible: true,
            matches: Vec::new(),
        };
        let bridge_target = self.exception_bridge_guidance_target(func, scope, target_addr);
        let guidance_target = bridge_target.unwrap_or(target_addr);
        let guidance_func = if bridge_target.is_some() {
            Some(func)
        } else {
            self.resolve_scope_function(func, scope, target_addr)
        };
        let allow_cross_function_states = bridge_target.is_none()
            && guidance_func.is_some_and(|guidance_func| guidance_func.entry != func.entry);
        if self.target_guided_queries && guidance_func.is_some() {
            self.drive_target_guided_in_scope(
                guidance_func.unwrap_or(func),
                scope,
                initial_state,
                &mut mode,
                guidance_target,
                allow_cross_function_states,
            );
        } else {
            self.drive_in_scope(func, scope, initial_state, &mut mode);
        }
        match mode {
            DriverMode::FindAll { matches, .. } => matches,
            _ => unreachable!("find_paths_to should always use all-match mode"),
        }
    }

    /// Explore paths to find inputs that avoid a target address.
    pub fn find_path_avoiding(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        avoid_addrs: &[u64],
    ) -> Option<PathResult<'ctx>> {
        let mut mode = DriverMode::Avoid {
            avoid_set: avoid_addrs.iter().copied().collect(),
            found: None,
        };
        self.drive_in_scope(func, None, initial_state, &mut mode);
        match mode {
            DriverMode::Avoid { found, .. } => found,
            _ => unreachable!("find_path_avoiding should always use avoid mode"),
        }
    }

    /// Run a typed exploration specification.
    pub fn run_spec(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        spec: &ExplorationSpec,
    ) -> Result<SpecExploreResult<'ctx>, String> {
        let mut mode = DriverMode::Spec {
            find_set: spec.find_addresses()?.into_iter().collect(),
            avoid_set: spec.avoid_addresses()?.into_iter().collect(),
            max_finds: spec.max_finds(),
            result: SpecExploreResult::default(),
        };
        self.drive_in_scope(func, None, initial_state, &mut mode);
        match mode {
            DriverMode::Spec { result, .. } => Ok(result),
            _ => unreachable!("run_spec should always use spec mode"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{InterprocFunctionId, SsaArtifact};
    use z3::ast::BV;

    use crate::SymValue;
    use crate::executor::CallHookResult;
    use crate::sim::{
        CallConv, DerivedFunctionSummary, DerivedSummaryCase, DerivedSummaryCompletion,
    };

    const RAX: u64 = 0;
    const RDI: u64 = 56;
    const TMP0: u64 = 0x80;
    const TMP1: u64 = 0x88;
    const TMP2: u64 = 0x90;

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(val: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size,
            meta: None,
        }
    }

    fn make_ram(addr: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Ram,
            offset: addr,
            size,
            meta: None,
        }
    }

    fn make_x86_64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("AL", RAX, 1));
        arch.add_register(RegisterDef::new("EAX", RAX, 4));
        arch.add_register(RegisterDef::new("RAX", RAX, 8));
        arch.add_register(RegisterDef::new("RDI", RDI, 8));
        arch
    }

    #[test]
    fn test_explore_config_default() {
        let config = ExploreConfig::default();
        assert_eq!(config.max_states, 1000);
        assert_eq!(config.max_completed_paths, None);
        assert_eq!(config.max_depth, 100);
        assert!(config.prune_infeasible);
        assert!(!config.subsumption_states);
    }

    #[test]
    fn test_path_explorer_creation() {
        let ctx = Context::thread_local();

        let explorer = PathExplorer::new(&ctx);
        assert_eq!(explorer.stats().states_explored, 0);
    }

    #[test]
    fn test_explore_stats() {
        let stats = ExploreStats::default();
        assert_eq!(stats.states_explored, 0);
        assert_eq!(stats.paths_completed, 0);
    }

    #[test]
    fn test_state_worklist_same_pc_lookup_skips_popped_entries() {
        let ctx = Context::thread_local();
        let mut worklist = StateWorklist::new(ExploreStrategy::Bfs);

        worklist.push(SymState::new(&ctx, 0x1000));
        worklist.push(SymState::new(&ctx, 0x2000));
        worklist.push(SymState::new(&ctx, 0x1000));

        let first = worklist.pop_next().expect("first state should exist");
        assert_eq!(first.pc, 0x1000);

        let merged = worklist
            .take_same_pc(0x1000)
            .expect("queued same-pc state should still be found");
        assert_eq!(merged.pc, 0x1000);

        let remaining = worklist.pop_next().expect("non-merged state should remain");
        assert_eq!(remaining.pc, 0x2000);
        assert!(worklist.pop_next().is_none());
        assert!(worklist.take_same_pc(0x1000).is_none());
    }

    #[test]
    fn test_target_guided_heap_prefers_best_and_skips_stale_entries() {
        let ctx = Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let mut worklist = StateWorklist::new(ExploreStrategy::Dfs);

        let id_a = worklist.push(SymState::new(&ctx, 0x1000));
        let id_b = worklist.push(SymState::new(&ctx, 0x2000));
        let id_c = worklist.push(SymState::new(&ctx, 0x3000));

        let guidance = TargetGuidanceContext {
            target_addr: 0x2000,
            distances: HashMap::from([(0x1000, 2), (0x2000, 0), (0x3000, 1)]),
            reachable_blocks: HashSet::from([0x1000, 0x2000, 0x3000]),
            call_targets_by_block: HashMap::new(),
            block_summary_rank: HashMap::new(),
            allow_cross_function_states: false,
        };

        let mut heap: BinaryHeap<Reverse<TargetGuidedQueueEntry>> = BinaryHeap::new();
        for id in [id_a, id_b, id_c] {
            let state = worklist.state(id).expect("live state");
            heap.push(Reverse(TargetGuidedQueueEntry {
                rank: explorer.state_target_rank(state, id, &guidance),
                id,
            }));
        }

        let (state, reordered) = explorer
            .pop_target_guided_state(&mut worklist, &mut heap)
            .expect("best state should exist");
        assert_eq!(state.pc, 0x2000);
        assert!(
            reordered,
            "best state should differ from DFS default candidate"
        );

        assert!(
            worklist.remove_slot(id_c).is_some(),
            "simulate a stale heap entry"
        );

        let (state, reordered) = explorer
            .pop_target_guided_state(&mut worklist, &mut heap)
            .expect("remaining state should exist");
        assert_eq!(state.pc, 0x1000);
        assert!(
            !reordered,
            "after skipping stale entries, the chosen state should match the live default candidate"
        );
    }

    #[test]
    fn test_target_distance_map_reuses_cache_for_same_entry_and_target() {
        let ctx = Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1008, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("symbolic function");

        let first = explorer.target_distance_map(&func, 0x1008);
        let second = explorer.target_distance_map(&func, 0x1008);

        assert_eq!(first, second);
        assert_eq!(explorer.target_distance_cache.len(), 1);
        assert_eq!(first.get(&0x1008), Some(&0));
        assert_eq!(first.get(&0x1004), Some(&1));
        assert_eq!(first.get(&0x1000), Some(&2));
    }

    #[test]
    fn test_same_pc_subsumption_prefers_weaker_constraint_state() {
        let ctx = Context::thread_local();
        let mut config = ExploreConfig {
            subsumption_states: true,
            ..ExploreConfig::default()
        };
        config.prune_infeasible = false;
        let mut explorer = PathExplorer::with_config(&ctx, config);
        let mut worklist = StateWorklist::new(ExploreStrategy::Dfs);

        let mut existing = SymState::new(&ctx, 0x1000);
        existing.make_symbolic("sym_input", 64);
        let input = existing.get_register("sym_input");
        existing.add_constraint(input.to_bv(&ctx).bvult(z3::ast::BV::from_u64(10, 64)));
        worklist.push(existing);

        let mut stronger = SymState::new(&ctx, 0x1000);
        stronger.make_symbolic("sym_input", 64);
        let input = stronger.get_register("sym_input");
        stronger.add_constraint(input.to_bv(&ctx).bvult(z3::ast::BV::from_u64(10, 64)));
        stronger.add_constraint(input.to_bv(&ctx).bvult(z3::ast::BV::from_u64(5, 64)));

        let pruned = explorer.prune_subsumed_same_pc_state(&mut worklist, stronger);
        assert!(
            pruned.is_none(),
            "stronger same-pc state should be subsumed"
        );
        assert_eq!(explorer.stats.subsumption_checks, 1);
        assert_eq!(explorer.stats.subsumption_hits, 1);
        assert_eq!(explorer.stats.states_subsumed, 1);
        assert_eq!(worklist.live_states, 1);
    }

    #[test]
    fn test_same_pc_subsumption_replaces_stronger_constraint_state() {
        let ctx = Context::thread_local();
        let mut config = ExploreConfig {
            subsumption_states: true,
            ..ExploreConfig::default()
        };
        config.prune_infeasible = false;
        let mut explorer = PathExplorer::with_config(&ctx, config);
        let mut worklist = StateWorklist::new(ExploreStrategy::Dfs);

        let mut stronger = SymState::new(&ctx, 0x1000);
        stronger.make_symbolic("sym_input", 64);
        let input = stronger.get_register("sym_input");
        stronger.add_constraint(input.to_bv(&ctx).bvult(z3::ast::BV::from_u64(10, 64)));
        stronger.add_constraint(input.to_bv(&ctx).bvult(z3::ast::BV::from_u64(5, 64)));
        worklist.push(stronger);

        let mut weaker = SymState::new(&ctx, 0x1000);
        weaker.make_symbolic("sym_input", 64);
        let input = weaker.get_register("sym_input");
        weaker.add_constraint(input.to_bv(&ctx).bvult(z3::ast::BV::from_u64(10, 64)));
        let kept = explorer.prune_subsumed_same_pc_state(&mut worklist, weaker);

        assert!(kept.is_some(), "weaker same-pc state should survive");
        assert_eq!(explorer.stats.subsumption_checks, 1);
        assert_eq!(explorer.stats.subsumption_hits, 1);
        assert_eq!(explorer.stats.states_subsumed, 1);
        assert_eq!(worklist.live_states, 0);
    }

    #[test]
    fn test_same_pc_subsumption_tie_break_prefers_shallower_state() {
        let ctx = Context::thread_local();
        let config = ExploreConfig {
            subsumption_states: true,
            ..ExploreConfig::default()
        };
        let mut explorer = PathExplorer::with_config(&ctx, config);
        let mut worklist = StateWorklist::new(ExploreStrategy::Random);

        let mut existing = SymState::new(&ctx, 0x1000);
        existing.make_symbolic("sym_input", 64);
        existing.step();
        worklist.push(existing);

        let mut new_state = SymState::new(&ctx, 0x1000);
        new_state.make_symbolic("sym_input", 64);
        let kept = explorer.prune_subsumed_same_pc_state(&mut worklist, new_state);

        assert!(
            kept.is_some(),
            "shallower state should replace deeper equivalent state"
        );
        assert_eq!(worklist.live_states, 0);
        assert_eq!(explorer.stats.subsumption_hits, 1);
        assert_eq!(explorer.stats.states_subsumed, 1);
    }

    #[test]
    fn test_path_result_methods() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("rax", SymValue::concrete(42, 64));
        state.make_symbolic("rbx", 64);
        state.set_register("aaa", SymValue::concrete(7, 64));

        let result = PathResult::new(state, true);

        assert_eq!(result.final_pc(), 0x1000);
        assert_eq!(result.num_constraints(), 0);
        assert_eq!(
            result.register_names(),
            vec!["aaa".to_string(), "rax".to_string(), "rbx".to_string()]
        );
        assert_eq!(result.get_concrete_register("rax"), Some(42));
        assert!(result.is_register_symbolic("rbx"));
    }

    #[test]
    fn test_solve_path_with_constraints() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("sym_input", 64);

        // Add constraint: sym_input < 100
        let input = state.get_register("sym_input");
        let hundred = SymValue::concrete(100, 64);
        let cmp = input.ult(&ctx, &hundred);
        state.add_true_constraint(&cmp);

        let result = PathResult::new(state, true);
        let explorer = PathExplorer::new(&ctx);

        let solved = explorer.solve_path(&result);
        assert!(solved.is_some());

        let solved = solved.unwrap();
        assert_eq!(solved.final_pc, 0x1000);
        assert_eq!(solved.num_constraints, 1);

        // The input should be less than 100
        if let Some(&value) = solved.inputs.get("sym_input") {
            assert!(value < 100, "Input should be < 100, got {}", value);
        }
    }

    #[test]
    fn test_solved_path_default() {
        let solved = SolvedPath::default();
        assert!(solved.inputs.is_empty());
        assert!(solved.input_buffers.is_empty());
        assert!(solved.registers.is_empty());
        assert!(solved.memory.is_empty());
        assert_eq!(solved.final_pc, 0);
        assert_eq!(solved.num_constraints, 0);
    }

    #[test]
    fn test_solve_path_emits_stable_map_order() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.new_symbolic_input("z_input", 64);
        state.new_symbolic_input("a_input", 64);
        state.set_register("z_reg", SymValue::concrete(3, 64));
        state.set_register("a_reg", SymValue::concrete(1, 64));
        state.set_register("m_reg", SymValue::concrete(9, 64));

        let result = PathResult::new(state, true);
        let explorer = PathExplorer::new(&ctx);
        let solved = explorer.solve_path(&result).expect("path should solve");

        assert_eq!(
            solved.inputs.keys().cloned().collect::<Vec<_>>(),
            vec!["a_input".to_string(), "z_input".to_string()]
        );
        assert_eq!(
            solved.registers.keys().cloned().collect::<Vec<_>>(),
            vec![
                "a_reg".to_string(),
                "m_reg".to_string(),
                "z_reg".to_string()
            ]
        );
    }

    #[test]
    fn test_target_guided_prunes_exact_summary_contradiction() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Call {
                    target: make_const(0x2000, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1010, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(TMP0, 1),
                    src: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("symbolic function");

        let mut explorer = PathExplorer::new(&ctx);
        explorer.set_target_guided_queries(true);

        let arg0 = SymValue::new_symbolic(&ctx, "summary_arg0", 64);
        let guard = arg0.to_bv(&ctx).eq(BV::from_u64(1, 64));
        let summary = Rc::new(DerivedFunctionSummary {
            id: InterprocFunctionId(0x2000),
            name: Some("contradict_helper".to_string()),
            arg_count_hint: 1,
            arg_symbols: vec![(0, arg0)],
            memory_inputs: Vec::new(),
            cases: vec![DerivedSummaryCase {
                guard,
                return_value: None,
                memory_writes: Vec::new(),
            }],
            completion: DerivedSummaryCompletion::Exact,
        });
        explorer.register_derived_call_hook(0x2000, summary, CallConv::x86_64_sysv(), |_state| {
            CallHookResult::Fallthrough
        });

        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("RDI_0", SymValue::concrete(2, 64));

        let paths = explorer.find_paths_to(&func, state, 0x1010);
        assert!(paths.is_empty(), "contradictory exact summary should prune");
        assert_eq!(explorer.stats().target_pruned_summary_contradiction, 1);
    }

    #[test]
    fn test_runtime_alias_region_becomes_queryable() {
        let ctx = Context::thread_local();
        let blocks = vec![
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("symbolic function");
        let mut state = SymState::new(&ctx, 0x6000_0000);
        let _ = state.define_runtime_region("jit_blob", 0x6000_0000, 0x100, true);
        state.note_runtime_store_copy(
            0x6000_0000,
            1,
            Some(&crate::RuntimeValueProvenance {
                source_addr: 0x2000,
                size: 1,
            }),
        );

        let mut explorer = PathExplorer::new(&ctx);
        let found = explorer.find_path_to(&func, state, 0x6000_0004);

        assert!(found.is_some(), "runtime-mapped target should be reachable");
        assert_eq!(explorer.stats().runtime_missing_materialized_code, 0);
    }

    #[test]
    fn test_runtime_alias_region_matches_static_source_target() {
        let ctx = Context::thread_local();
        let blocks = vec![
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("symbolic function");
        let mut state = SymState::new(&ctx, 0x6000_0000);
        let _ = state.define_runtime_region("jit_blob", 0x6000_0000, 0x100, true);
        state.note_runtime_store_copy(
            0x6000_0000,
            1,
            Some(&crate::RuntimeValueProvenance {
                source_addr: 0x2000,
                size: 1,
            }),
        );

        let mut explorer = PathExplorer::new(&ctx);
        let found = explorer.find_path_to(&func, state, 0x2004);

        assert!(
            found.is_some(),
            "runtime-mapped execution should match the static source target"
        );
    }

    #[test]
    fn test_block_entry_concrete_lookup_uses_selected_phi_source() {
        let ctx = Context::thread_local();
        let counter = r2ssa::SSAVar::new("RCX", 7, 8);
        let block = r2ssa::FunctionSSABlock {
            addr: 0x1400,
            size: 4,
            phis: vec![r2ssa::PhiNode {
                dst: counter.clone(),
                sources: vec![
                    (0x1000, r2ssa::SSAVar::new("RCX", 4, 8)),
                    (0x1200, r2ssa::SSAVar::new("RCX", 6, 8)),
                ],
            }],
            ops: Vec::new(),
        };
        let mut state = SymState::new(&ctx, 0x1400);
        state.set_prev_pc(Some(0x1000));
        state.set_register("RCX_4", SymValue::concrete(0, 64));
        state.set_register("RCX_6", SymValue::concrete(0xdead_beef_cafe_1337, 64));
        state.set_register("RCX_7", SymValue::concrete(0xcccc_cccc_cccc_cccc, 64));

        assert_eq!(
            loops::concrete_state_var_at_block_entry(&state, &block, &counter),
            Some(0),
            "loop summaries must read the incoming phi source, not a stale phi destination"
        );
    }

    #[test]
    fn test_target_guided_follows_scoped_direct_call_thunk() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let root_blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
                R2ILOp::Return {
                    target: make_const(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let thunk_blocks = vec![
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x3000, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let root = SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic");
        let thunk = SsaArtifact::for_symbolic(&thunk_blocks, Some(&arch)).expect("thunk symbolic");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("thunk".to_string()),
                    prepared: thunk,
                },
            ],
        )
        .expect("scope");

        let mut explorer = PathExplorer::new(&ctx);
        explorer.set_target_guided_queries(true);
        let found = explorer.find_path_to_in_scope(
            &root,
            Some(&scope),
            SymState::new(&ctx, 0x1000),
            0x3000,
        );

        assert!(
            found.is_some(),
            "target-guided queries should follow direct calls into scoped thunk/helper blocks"
        );
        assert_eq!(found.unwrap().final_pc(), 0x3000);
    }

    #[test]
    fn test_runtime_missing_materialized_code_is_tracked() {
        let ctx = Context::thread_local();
        let blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("symbolic function");
        let mut state = SymState::new(&ctx, 0x6000_0000);
        let _ = state.define_runtime_region("jit_blob", 0x6000_0000, 0x100, true);

        let mut explorer = PathExplorer::new(&ctx);
        let found = explorer.find_paths_to(&func, state, 0x6000_0004);

        assert!(
            found.is_empty(),
            "unmaterialized runtime region should not be queryable"
        );
        assert_eq!(explorer.stats().runtime_missing_materialized_code, 1);
    }

    #[test]
    fn test_deterministic_linear_runahead_reaches_target_past_depth_budget() {
        let ctx = Context::thread_local();
        let mut blocks = Vec::new();
        for idx in 0..16u64 {
            let addr = 0x1000 + idx * 4;
            let next = addr + 4;
            let ops = if idx == 15 {
                vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }]
            } else {
                vec![R2ILOp::Branch {
                    target: make_const(next, 8),
                }]
            };
            blocks.push(R2ILBlock {
                addr,
                size: 4,
                ops,
                switch_info: None,
                op_metadata: Default::default(),
            });
        }
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("symbolic function");

        let mut explorer = PathExplorer::with_config(
            &ctx,
            ExploreConfig {
                max_depth: 5,
                ..ExploreConfig::default()
            },
        );
        let target = 0x1000 + 15 * 4;
        let found = explorer.find_path_to(&func, SymState::new(&ctx, 0x1000), target);

        assert!(
            found.is_some(),
            "deterministic linear chain should run ahead to the far target"
        );
        let found = found.unwrap();
        assert_eq!(found.final_pc(), target);
        assert!(
            found.depth > 5,
            "execution depth should still reflect the concrete block work"
        );
        assert_eq!(explorer.stats().paths_max_depth, 0);
    }

    #[test]
    fn test_target_guided_symbolic_byte_loop_reaches_concrete_terminator() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Load {
                        dst: make_reg(TMP0, 1),
                        addr: make_reg(RDI, 8),
                        space: SpaceId::Ram,
                    },
                    R2ILOp::IntZExt {
                        dst: make_reg(RAX, 4),
                        src: make_reg(TMP0, 1),
                    },
                    R2ILOp::IntZExt {
                        dst: make_reg(RAX, 8),
                        src: make_reg(RAX, 4),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1010, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::IntZExt {
                        dst: make_reg(RAX, 4),
                        src: make_reg(RAX, 1),
                    },
                    R2ILOp::IntAdd {
                        dst: make_reg(RDI, 8),
                        a: make_reg(RDI, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Load {
                        dst: make_reg(TMP0, 1),
                        addr: make_reg(RDI, 8),
                        space: SpaceId::Ram,
                    },
                    R2ILOp::IntZExt {
                        dst: make_reg(RAX, 4),
                        src: make_reg(TMP0, 1),
                    },
                    R2ILOp::IntZExt {
                        dst: make_reg(RAX, 8),
                        src: make_reg(RAX, 4),
                    },
                    R2ILOp::IntAnd {
                        dst: make_reg(TMP1, 1),
                        a: make_reg(RAX, 1),
                        b: make_reg(RAX, 1),
                    },
                    R2ILOp::IntEqual {
                        dst: make_reg(TMP2, 1),
                        a: make_reg(TMP1, 1),
                        b: make_const(0, 1),
                    },
                    R2ILOp::BoolNot {
                        dst: make_reg(TMP0 + 1, 1),
                        src: make_reg(TMP2, 1),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(TMP0 + 1, 1),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1014,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("symbolic function");

        let mut state = SymState::new(&ctx, 0x1000);
        let region = state.define_memory_region(
            crate::MemoryRegionKind::Input,
            "argv_like",
            Some(0x2000),
            Some(0x10),
        );
        state.set_register("RDI_0", SymValue::concrete(0x2000, 64));
        let byte0 = state.new_symbolic_input("loop_byte_0", 8);
        let byte1 = state.new_symbolic_input("loop_byte_1", 8);
        state.add_constraint(byte0.to_bv(&ctx).eq(BV::from_u64(0, 8)).not());
        state.add_constraint(byte1.to_bv(&ctx).eq(BV::from_u64(0, 8)).not());
        state.mem_write(&SymValue::concrete(0x2000, 64), &byte0, 1);
        state.mem_write(&SymValue::concrete(0x2001, 64), &byte1, 1);
        state.seed_region_bytes(region, 2, &[0]);

        let mut explorer = PathExplorer::new(&ctx);
        explorer.set_target_guided_queries(true);
        let paths = explorer.find_paths_to(&func, state, 0x1014);

        assert_eq!(paths.len(), 1, "terminator exit should remain reachable");
        assert_eq!(paths[0].final_pc(), 0x1014);
        assert_eq!(
            explorer.stats().target_match_unsat,
            1,
            "only the impossible symbolic early exit should be unsat"
        );
    }

    #[test]
    fn test_target_guidance_keeps_pending_exception_bridge_states() {
        let ctx = Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let guidance = TargetGuidanceContext {
            target_addr: 0x1000,
            distances: HashMap::from([(0x1000, 0)]),
            reachable_blocks: HashSet::from([0x1000]),
            call_targets_by_block: HashMap::new(),
            block_summary_rank: HashMap::new(),
            allow_cross_function_states: false,
        };
        let (_, context_addr) = {
            let mut tmp = SymState::new(&ctx, 0x2000);
            tmp.allocate_heap_region("context", 0x400)
        };
        let mut state = SymState::new(&ctx, 0x2000);
        state.set_pending_exception(crate::state::PendingExceptionContinuation {
            handler_addr: 0x2000,
            exception_code: 0x8000_0004,
            exception_pointers_addr: 0x7000_0000,
            exception_record_addr: 0x7000_0100,
            context_addr,
        });

        assert!(
            explorer.target_enqueue_allowed(&guidance, &state),
            "pending exception continuation should bypass root-CFG pruning"
        );
    }

    #[test]
    fn test_target_guidance_keeps_runtime_region_bridge_states() {
        let ctx = Context::thread_local();
        let mut explorer = PathExplorer::new(&ctx);
        let guidance = TargetGuidanceContext {
            target_addr: 0x2004,
            distances: HashMap::from([(0x2004, 0)]),
            reachable_blocks: HashSet::from([0x2004]),
            call_targets_by_block: HashMap::new(),
            block_summary_rank: HashMap::new(),
            allow_cross_function_states: false,
        };
        let mut state = SymState::new(&ctx, 0x6000_0000);
        let _ = state.define_runtime_region("jit_blob", 0x6000_0000, 0x100, true);

        assert!(
            explorer.target_enqueue_allowed(&guidance, &state),
            "runtime-materialized states should bypass root-CFG pruning"
        );
    }

    #[test]
    fn test_pending_exception_resume_pc_uses_block_fallthrough() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Call {
                    target: make_const(0x4000, 8),
                }],
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
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("symbolic function");
        let mut state = SymState::new(&ctx, 0x2000);
        let (_, context_addr) = state.allocate_heap_region("context", 0x400);
        state.set_pending_exception(crate::state::PendingExceptionContinuation {
            handler_addr: 0x2000,
            exception_code: 0x8000_0004,
            exception_pointers_addr: 0x7000_0000,
            exception_record_addr: 0x7000_0100,
            context_addr,
        });

        let explorer = PathExplorer::new(&ctx);
        explorer.patch_pending_exception_resume_pc(&func, &mut state, 0x1000);

        assert_eq!(
            state
                .mem_read(
                    &SymValue::concrete(context_addr.saturating_add(0xF8), 64),
                    8
                )
                .as_concrete(),
            Some(0x1004)
        );
    }

    #[test]
    fn test_exception_handler_target_guidance_uses_raise_site_bridge() {
        let ctx = Context::thread_local();
        let mut arch = make_x86_64_arch();
        arch.add_register(RegisterDef::new("RCX", 0x80, 8));
        arch.add_register(RegisterDef::new("RDX", 0x88, 8));
        arch.add_register(RegisterDef::new("R8", 0x90, 8));
        arch.add_register(RegisterDef::new("R9", 0x98, 8));

        let root_blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0x2000, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x5000, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1010, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(0x8000_0004, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x90, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x98, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x5008, 8),
                    },
                    R2ILOp::Return {
                        target: make_const(0, 8),
                    },
                ],
            },
        ];
        let handler_blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        }];
        let root = SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic");
        let handler =
            SsaArtifact::for_symbolic(&handler_blocks, Some(&arch)).expect("handler symbolic");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("handler".to_string()),
                    prepared: handler,
                },
            ],
        )
        .expect("scope");

        let mut explorer = PathExplorer::new(&ctx);
        explorer.register_tagged_call_hook(
            0x5000,
            crate::executor::CallHookTag::WindowsAddVectoredExceptionHandler,
            |_| CallHookResult::Fallthrough,
        );
        explorer.register_tagged_call_hook(
            0x5008,
            crate::executor::CallHookTag::WindowsRaiseException,
            |_| CallHookResult::Fallthrough,
        );

        assert_eq!(
            explorer.exception_bridge_guidance_target(&root, Some(&scope), 0x2000),
            Some(0x1010)
        );
    }

    #[test]
    fn test_runtime_target_guidance_uses_raise_site_bridge() {
        let ctx = Context::thread_local();
        let mut arch = make_x86_64_arch();
        arch.add_register(RegisterDef::new("RCX", 0x80, 8));
        arch.add_register(RegisterDef::new("RDX", 0x88, 8));
        arch.add_register(RegisterDef::new("R8", 0x90, 8));
        arch.add_register(RegisterDef::new("R9", 0x98, 8));

        let root_blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0x2000, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x5000, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1010, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(0x8000_0004, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x90, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x98, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x5008, 8),
                    },
                    R2ILOp::Return {
                        target: make_const(0, 8),
                    },
                ],
            },
        ];
        let handler_blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        }];
        let root = SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic");
        let handler =
            SsaArtifact::for_symbolic(&handler_blocks, Some(&arch)).expect("handler symbolic");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("handler".to_string()),
                    prepared: handler,
                },
            ],
        )
        .expect("scope");

        let mut explorer = PathExplorer::new(&ctx);
        explorer.register_tagged_call_hook(
            0x5000,
            crate::executor::CallHookTag::WindowsAddVectoredExceptionHandler,
            |_| CallHookResult::Fallthrough,
        );
        explorer.register_tagged_call_hook(
            0x5008,
            crate::executor::CallHookTag::WindowsRaiseException,
            |_| CallHookResult::Fallthrough,
        );

        assert_eq!(
            explorer.exception_bridge_guidance_target(&root, Some(&scope), 0x7000),
            Some(0x1010)
        );
    }

    #[test]
    fn test_cfg_unreachable_local_target_uses_raise_site_bridge() {
        let ctx = Context::thread_local();
        let mut arch = make_x86_64_arch();
        arch.add_register(RegisterDef::new("RCX", 0x80, 8));
        arch.add_register(RegisterDef::new("RDX", 0x88, 8));
        arch.add_register(RegisterDef::new("R8", 0x90, 8));
        arch.add_register(RegisterDef::new("R9", 0x98, 8));

        let root_blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0x2000, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x5000, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1010, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(0x8000_0004, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x90, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x98, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x5008, 8),
                    },
                    R2ILOp::Return {
                        target: make_const(0, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1020,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
            },
        ];
        let handler_blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        }];
        let root = SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic");
        let handler =
            SsaArtifact::for_symbolic(&handler_blocks, Some(&arch)).expect("handler symbolic");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("handler".to_string()),
                    prepared: handler,
                },
            ],
        )
        .expect("scope");

        let mut explorer = PathExplorer::new(&ctx);
        explorer.register_tagged_call_hook(
            0x5000,
            crate::executor::CallHookTag::WindowsAddVectoredExceptionHandler,
            |_| CallHookResult::Fallthrough,
        );
        explorer.register_tagged_call_hook(
            0x5008,
            crate::executor::CallHookTag::WindowsRaiseException,
            |_| CallHookResult::Fallthrough,
        );

        assert_eq!(
            explorer.exception_bridge_guidance_target(&root, Some(&scope), 0x1020),
            Some(0x1010)
        );
    }

    #[test]
    fn test_import_mediated_exception_calls_use_raise_site_bridge() {
        let ctx = Context::thread_local();
        let mut arch = make_x86_64_arch();
        arch.add_register(RegisterDef::new("RCX", 0x80, 8));
        arch.add_register(RegisterDef::new("RDX", 0x88, 8));
        arch.add_register(RegisterDef::new("R8", 0x90, 8));
        arch.add_register(RegisterDef::new("R9", 0x98, 8));

        let addveh_target = Varnode {
            space: SpaceId::Unique,
            offset: 0x500,
            size: 8,
            meta: None,
        };
        let raise_target = Varnode {
            space: SpaceId::Unique,
            offset: 0x508,
            size: 8,
            meta: None,
        };
        let root_blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0x2000, 8),
                    },
                    R2ILOp::Copy {
                        dst: addveh_target.clone(),
                        src: make_ram(0x5000, 8),
                    },
                    R2ILOp::CallInd {
                        target: addveh_target,
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1010, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(0x8000_0004, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x90, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x98, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: raise_target.clone(),
                        src: make_ram(0x5008, 8),
                    },
                    R2ILOp::CallInd {
                        target: raise_target,
                    },
                    R2ILOp::Return {
                        target: make_const(0, 8),
                    },
                ],
            },
        ];
        let handler_blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        }];
        let root = SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic");
        let handler =
            SsaArtifact::for_symbolic(&handler_blocks, Some(&arch)).expect("handler symbolic");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some("handler".to_string()),
                    prepared: handler,
                },
            ],
        )
        .expect("scope");

        let mut explorer = PathExplorer::new(&ctx);
        explorer.register_tagged_call_hook(
            0x5000,
            crate::executor::CallHookTag::WindowsAddVectoredExceptionHandler,
            |_| CallHookResult::Fallthrough,
        );
        explorer.register_tagged_call_hook(
            0x5008,
            crate::executor::CallHookTag::WindowsRaiseException,
            |_| CallHookResult::Fallthrough,
        );

        assert_eq!(
            explorer.exception_bridge_guidance_target(&root, Some(&scope), 0x2000),
            Some(0x1010)
        );
    }

    #[test]
    fn test_import_mediated_bridge_works_with_installed_runtime_hooks() {
        let ctx = Context::thread_local();
        let mut arch = make_x86_64_arch();
        arch.add_register(RegisterDef::new("RCX", 0x80, 8));
        arch.add_register(RegisterDef::new("RDX", 0x88, 8));
        arch.add_register(RegisterDef::new("R8", 0x90, 8));
        arch.add_register(RegisterDef::new("R9", 0x98, 8));

        let addveh_target = Varnode {
            space: SpaceId::Unique,
            offset: 0x520,
            size: 8,
            meta: None,
        };
        let raise_target = Varnode {
            space: SpaceId::Unique,
            offset: 0x528,
            size: 8,
            meta: None,
        };
        let root_blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0x2000, 8),
                    },
                    R2ILOp::Copy {
                        dst: addveh_target.clone(),
                        src: make_ram(0x1400a6010, 8),
                    },
                    R2ILOp::CallInd {
                        target: addveh_target,
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1010, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0x80, 8),
                        src: make_const(0x8000_0004, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x88, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x90, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0x98, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: raise_target.clone(),
                        src: make_ram(0x1400a6000, 8),
                    },
                    R2ILOp::CallInd {
                        target: raise_target,
                    },
                    R2ILOp::Return {
                        target: make_const(0, 8),
                    },
                ],
            },
        ];
        let root = SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            }],
        )
        .expect("scope");

        let mut explorer = PathExplorer::new(&ctx);
        let symbol_map = HashMap::from([
            (
                0x1400a6010,
                "sym.imp.KERNEL32.dll_AddVectoredExceptionHandler".to_string(),
            ),
            (
                0x1400a6000,
                "sym.imp.KERNEL32.dll_RaiseException".to_string(),
            ),
        ]);
        crate::install_runtime_hooks_for_scope(&mut explorer, &scope, Some(&arch), &symbol_map);

        assert_eq!(
            explorer.exception_bridge_guidance_target(&root, Some(&scope), 0x7000),
            Some(0x1010)
        );
    }
}
