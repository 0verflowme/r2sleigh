//! Path exploration strategies for symbolic execution.
//!
//! This module provides different strategies for exploring paths
//! during symbolic execution, including DFS, BFS, and coverage-guided.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

use r2ssa::{BlockTerminator, SsaArtifact};
use z3::Context;

use crate::executor::SymExecutor;
use crate::solver::SymSolver;
use crate::spec::ExplorationSpec;
use crate::state::{ExitStatus, SymState};

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

    fn push(&mut self, state: SymState<'ctx>) {
        let id = self.slots.len();
        let pc = state.pc;
        self.slots.push(Some(state));
        self.ready.push_back(id);
        self.same_pc.entry(pc).or_default().push_back(id);
        self.live_states += 1;
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
        found: Option<PathResult<'ctx>>,
    },
    FindAll {
        target_addr: u64,
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
            DriverMode::FindFirst { target_addr, found } => {
                if state.pc == *target_addr {
                    if explorer.solver.is_sat(&state) {
                        *found = Some(PathResult::new(state, true));
                        DriverAction::Finish
                    } else {
                        DriverAction::Skip
                    }
                } else {
                    DriverAction::Continue(Box::new(state))
                }
            }
            DriverMode::FindAll {
                target_addr,
                matches,
            } => {
                if state.pc == *target_addr {
                    if explorer.solver.is_sat(&state) {
                        explorer.record_depth(state.depth);
                        explorer.stats.paths_completed += 1;
                        matches.push(PathResult::new(state, true));
                    }
                    DriverAction::Skip
                } else {
                    DriverAction::Continue(Box::new(state))
                }
            }
            DriverMode::Avoid { avoid_set, .. } => {
                if avoid_set.contains(&state.pc) {
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
                if avoid_set.contains(&state.pc) {
                    result.avoided_states += 1;
                    return DriverAction::Skip;
                }
                if find_set.contains(&state.pc) {
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
                    Some(ExitStatus::Error(_)) => result.errored_states += 1,
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
            DriverMode::Avoid { avoid_set, .. } => !avoid_set.contains(&state.pc),
            DriverMode::Spec {
                avoid_set, result, ..
            } => {
                if avoid_set.contains(&state.pc) {
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
    /// Create a new path explorer.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            _ctx: ctx,
            executor: SymExecutor::new(ctx),
            solver: SymSolver::new(ctx),
            config: ExploreConfig::default(),
            stats: ExploreStats::default(),
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
        }
    }

    /// Get the exploration statistics.
    pub fn stats(&self) -> &ExploreStats {
        &self.stats
    }

    /// Get the solver for additional queries.
    pub fn solver(&self) -> &SymSolver<'ctx> {
        &self.solver
    }

    /// Register a call hook for a concrete target address.
    pub fn register_call_hook<F>(&mut self, addr: u64, hook: F)
    where
        F: Fn(&mut SymState<'ctx>) -> crate::executor::CallHookResult + 'ctx,
    {
        self.executor
            .register_call_hook(addr, move |state| Ok(hook(state)));
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

    /// Solve all feasible paths and return concrete solutions.
    pub fn solve_all_paths(&self, paths: &[PathResult<'ctx>]) -> Vec<Option<SolvedPath>> {
        paths.iter().map(|p| self.solve_path(p)).collect()
    }

    fn record_depth(&mut self, depth: usize) {
        if depth > self.stats.max_depth_reached {
            self.stats.max_depth_reached = depth;
        }
    }

    fn drive(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        mode: &mut DriverMode<'ctx>,
    ) {
        let start_time = Instant::now();
        let mut worklist = StateWorklist::new(self.config.strategy);
        worklist.push(initial_state);

        while let Some(mut state) = worklist.pop_next() {
            if self.config.merge_states
                && let Some(other) = worklist.take_same_pc(state.pc)
            {
                state = state.merge_with(&other);
            }

            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
                && mode.on_timeout()
            {
                break;
            }

            match mode.on_state_popped(self, state) {
                DriverAction::Continue(next_state) => state = *next_state,
                DriverAction::Skip => continue,
                DriverAction::Finish => break,
            }

            if self.stats.states_explored >= self.config.max_states && mode.on_max_states() {
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

            let block_addr = state.pc;
            let Some(block) = func.get_block(block_addr) else {
                match mode.on_missing_block(
                    self,
                    state,
                    block_addr,
                    self.config.max_completed_paths,
                ) {
                    DriverAction::Finish => break,
                    DriverAction::Continue(_) | DriverAction::Skip => continue,
                }
            };

            match self.executor.execute_block(&mut state, block) {
                Ok(forked_states) => {
                    self.record_depth(state.depth);

                    for mut forked in forked_states {
                        forked.set_prev_pc(Some(block_addr));
                        if mode.allow_enqueue(&forked) {
                            worklist.push(forked);
                        }
                    }

                    if !state.is_terminated() {
                        if state.pc == block_addr
                            && let Some(next) = self.fallthrough_target(func, block_addr)
                        {
                            state.pc = next;
                        }
                        state.set_prev_pc(Some(block_addr));
                        if mode.allow_enqueue(&state) {
                            worklist.push(state);
                        }
                    } else {
                        match mode.on_terminated_state(
                            self,
                            state,
                            block_addr,
                            self.config.max_completed_paths,
                        ) {
                            DriverAction::Finish => break,
                            DriverAction::Continue(_) | DriverAction::Skip => continue,
                        }
                    }
                }
                Err(e) => match mode.on_execute_error(
                    self,
                    state,
                    block_addr,
                    e.to_string(),
                    self.config.max_completed_paths,
                ) {
                    DriverAction::Finish => break,
                    DriverAction::Continue(_) | DriverAction::Skip => continue,
                },
            }
        }

        self.stats.total_time = start_time.elapsed();
    }

    /// Explore all paths in a function.
    pub fn explore(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
    ) -> Vec<PathResult<'ctx>> {
        if self.config.max_completed_paths == Some(0) {
            return Vec::new();
        }
        let mut mode = DriverMode::Explore {
            results: Vec::new(),
        };
        self.drive(func, initial_state, &mut mode);
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
        let mut mode = DriverMode::FindFirst {
            target_addr,
            found: None,
        };
        self.drive(func, initial_state, &mut mode);
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
        let mut mode = DriverMode::FindAll {
            target_addr,
            matches: Vec::new(),
        };
        self.drive(func, initial_state, &mut mode);
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
        self.drive(func, initial_state, &mut mode);
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
        self.drive(func, initial_state, &mut mode);
        match mode {
            DriverMode::Spec { result, .. } => Ok(result),
            _ => unreachable!("run_spec should always use spec mode"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SymValue;

    #[test]
    fn test_explore_config_default() {
        let config = ExploreConfig::default();
        assert_eq!(config.max_states, 1000);
        assert_eq!(config.max_completed_paths, None);
        assert_eq!(config.max_depth, 100);
        assert!(config.prune_infeasible);
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
}
