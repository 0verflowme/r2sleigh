//! Path exploration strategies for symbolic execution.
//!
//! This module provides different strategies for exploring paths
//! during symbolic execution, including DFS, BFS, and coverage-guided.

use std::collections::{HashSet, VecDeque};
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
        self.state.register_names().cloned().collect()
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
    pub inputs: std::collections::HashMap<String, u64>,
    /// Concrete multi-byte input buffers (input source name -> bytes).
    pub input_buffers: std::collections::HashMap<String, Vec<u8>>,
    /// Concrete register values at path end.
    pub registers: std::collections::HashMap<String, u64>,
    /// Concrete memory bytes for tracked symbolic regions.
    pub memory: std::collections::HashMap<String, Vec<u8>>,
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

    /// Explore all paths in a function.
    pub fn explore(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
    ) -> Vec<PathResult<'ctx>> {
        let start_time = Instant::now();
        let mut results = Vec::new();
        let mut worklist: VecDeque<SymState<'ctx>> = VecDeque::new();
        worklist.push_back(initial_state);

        while let Some(mut state) = self.next_state(&mut worklist) {
            if self.config.merge_states
                && let Some(other) = take_merge_candidate(&mut worklist, state.pc)
            {
                state = state.merge_with(&other);
            }
            // Check timeout
            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
            {
                break;
            }

            // Check state limit
            if self.stats.states_explored >= self.config.max_states {
                break;
            }

            self.stats.states_explored += 1;

            // Check depth limit
            if state.depth >= self.config.max_depth {
                state.terminate(ExitStatus::MaxDepth);
                self.stats.paths_max_depth += 1;
                results.push(PathResult::new(state, true));
                continue;
            }

            // Check feasibility
            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                continue;
            }

            // Get current block
            let block_addr = state.pc;
            let Some(block) = func.get_block(block_addr) else {
                // No block at this address - path ends
                state.terminate(ExitStatus::Return);
                results.push(PathResult::new(state, true));
                self.stats.paths_completed += 1;
                continue;
            };

            // Execute the block
            match self.executor.execute_block(&mut state, block) {
                Ok(forked_states) => {
                    // Add forked states to worklist
                    for mut forked in forked_states {
                        forked.set_prev_pc(Some(block_addr));
                        worklist.push_back(forked);
                    }

                    // Update max depth before potentially moving state
                    if state.depth > self.stats.max_depth_reached {
                        self.stats.max_depth_reached = state.depth;
                    }

                    // Check if state terminated
                    if state.is_terminated() {
                        let feasible = self.solver.is_sat(&state);
                        results.push(PathResult::new(state, feasible));
                        self.stats.paths_completed += 1;
                    } else {
                        // Continue exploring this path
                        // Update PC to next block if not changed by control flow
                        if state.pc == block_addr
                            && let Some(next) = self.fallthrough_target(func, block_addr)
                        {
                            state.pc = next;
                        }
                        state.set_prev_pc(Some(block_addr));
                        worklist.push_back(state);
                    }
                }
                Err(e) => {
                    // Update max depth before moving state
                    if state.depth > self.stats.max_depth_reached {
                        self.stats.max_depth_reached = state.depth;
                    }
                    state.terminate(ExitStatus::Error(format!("{}", e)));
                    results.push(PathResult::new(state, false));
                    self.stats.paths_completed += 1;
                }
            }
        }

        self.stats.total_time = start_time.elapsed();
        results
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

    /// Get the next state from the worklist based on strategy.
    fn next_state(&self, worklist: &mut VecDeque<SymState<'ctx>>) -> Option<SymState<'ctx>> {
        match self.config.strategy {
            ExploreStrategy::Dfs => worklist.pop_back(),
            ExploreStrategy::Bfs => worklist.pop_front(),
            ExploreStrategy::Random => {
                if worklist.is_empty() {
                    None
                } else {
                    // Simple random: alternate between front and back
                    if worklist.len().is_multiple_of(2) {
                        worklist.pop_front()
                    } else {
                        worklist.pop_back()
                    }
                }
            }
        }
    }

    /// Explore paths to find inputs that reach a target address.
    pub fn find_path_to(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> Option<PathResult<'ctx>> {
        let start_time = Instant::now();
        let mut worklist: VecDeque<SymState<'ctx>> = VecDeque::new();
        worklist.push_back(initial_state);

        while let Some(mut state) = self.next_state(&mut worklist) {
            if self.config.merge_states
                && let Some(other) = take_merge_candidate(&mut worklist, state.pc)
            {
                state = state.merge_with(&other);
            }
            // Check timeout
            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
            {
                break;
            }

            // Check if we reached the target
            if state.pc == target_addr {
                let feasible = self.solver.is_sat(&state);
                if feasible {
                    return Some(PathResult::new(state, true));
                }
                continue;
            }

            // Check limits
            if self.stats.states_explored >= self.config.max_states {
                break;
            }
            if state.depth >= self.config.max_depth {
                continue;
            }

            self.stats.states_explored += 1;

            // Check feasibility
            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                continue;
            }

            // Get and execute block
            let block_addr = state.pc;
            let Some(block) = func.get_block(block_addr) else {
                continue;
            };

            if let Ok(forked_states) = self.executor.execute_block(&mut state, block) {
                for mut forked in forked_states {
                    forked.set_prev_pc(Some(block_addr));
                    worklist.push_back(forked);
                }

                if !state.is_terminated() {
                    if state.pc == block_addr
                        && let Some(next) = self.fallthrough_target(func, block_addr)
                    {
                        state.pc = next;
                    }
                    state.set_prev_pc(Some(block_addr));
                    worklist.push_back(state);
                }
            }
        }

        None
    }

    /// Explore paths to collect all feasible states that reach a target address.
    pub fn find_paths_to(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        target_addr: u64,
    ) -> Vec<PathResult<'ctx>> {
        let start_time = Instant::now();
        let mut matches = Vec::new();
        let mut worklist: VecDeque<SymState<'ctx>> = VecDeque::new();
        worklist.push_back(initial_state);

        while let Some(mut state) = self.next_state(&mut worklist) {
            if self.config.merge_states
                && let Some(other) = take_merge_candidate(&mut worklist, state.pc)
            {
                state = state.merge_with(&other);
            }
            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
            {
                break;
            }

            if state.pc == target_addr {
                let feasible = self.solver.is_sat(&state);
                if feasible {
                    if state.depth > self.stats.max_depth_reached {
                        self.stats.max_depth_reached = state.depth;
                    }
                    self.stats.paths_completed += 1;
                    matches.push(PathResult::new(state, true));
                }
                continue;
            }

            if self.stats.states_explored >= self.config.max_states {
                break;
            }
            if state.depth >= self.config.max_depth {
                self.stats.paths_max_depth += 1;
                continue;
            }

            self.stats.states_explored += 1;

            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                continue;
            }

            let block_addr = state.pc;
            let Some(block) = func.get_block(block_addr) else {
                continue;
            };

            match self.executor.execute_block(&mut state, block) {
                Ok(forked_states) => {
                    for mut forked in forked_states {
                        forked.set_prev_pc(Some(block_addr));
                        worklist.push_back(forked);
                    }

                    if !state.is_terminated() {
                        if state.pc == block_addr
                            && let Some(next) = self.fallthrough_target(func, block_addr)
                        {
                            state.pc = next;
                        }
                        state.set_prev_pc(Some(block_addr));
                        worklist.push_back(state);
                    }
                }
                Err(_) => {
                    self.stats.paths_completed += 1;
                }
            }
        }

        self.stats.total_time = start_time.elapsed();
        matches
    }

    /// Explore paths to find inputs that avoid a target address.
    pub fn find_path_avoiding(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        avoid_addrs: &[u64],
    ) -> Option<PathResult<'ctx>> {
        let avoid_set: HashSet<u64> = avoid_addrs.iter().copied().collect();
        let start_time = Instant::now();
        let mut worklist: VecDeque<SymState<'ctx>> = VecDeque::new();
        worklist.push_back(initial_state);

        while let Some(mut state) = self.next_state(&mut worklist) {
            if self.config.merge_states
                && let Some(other) = take_merge_candidate(&mut worklist, state.pc)
            {
                state = state.merge_with(&other);
            }
            // Check timeout
            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
            {
                break;
            }

            // Check if we hit an avoided address
            if avoid_set.contains(&state.pc) {
                continue;
            }

            // Check limits
            if self.stats.states_explored >= self.config.max_states {
                break;
            }
            if state.depth >= self.config.max_depth {
                let feasible = self.solver.is_sat(&state);
                if feasible {
                    return Some(PathResult::new(state, true));
                }
                continue;
            }

            self.stats.states_explored += 1;

            // Check feasibility
            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                continue;
            }

            // Get and execute block
            let block_addr = state.pc;
            let Some(block) = func.get_block(block_addr) else {
                // Reached end without hitting avoided addresses
                let feasible = self.solver.is_sat(&state);
                if feasible {
                    return Some(PathResult::new(state, true));
                }
                continue;
            };

            if let Ok(forked_states) = self.executor.execute_block(&mut state, block) {
                for mut forked in forked_states {
                    forked.set_prev_pc(Some(block_addr));
                    if !avoid_set.contains(&forked.pc) {
                        worklist.push_back(forked);
                    }
                }

                if !state.is_terminated() && !avoid_set.contains(&state.pc) {
                    if state.pc == block_addr
                        && let Some(next) = self.fallthrough_target(func, block_addr)
                    {
                        state.pc = next;
                    }
                    state.set_prev_pc(Some(block_addr));
                    worklist.push_back(state);
                }
            }
        }

        None
    }

    /// Run a typed exploration specification.
    pub fn run_spec(
        &mut self,
        func: &SsaArtifact,
        initial_state: SymState<'ctx>,
        spec: &ExplorationSpec,
    ) -> Result<SpecExploreResult<'ctx>, String> {
        let find_set: HashSet<u64> = spec.find_addresses()?.into_iter().collect();
        let avoid_set: HashSet<u64> = spec.avoid_addresses()?.into_iter().collect();
        let max_finds = spec.max_finds();
        let start_time = Instant::now();
        let mut result = SpecExploreResult::default();
        let mut worklist: VecDeque<SymState<'ctx>> = VecDeque::new();
        worklist.push_back(initial_state);

        while let Some(mut state) = self.next_state(&mut worklist) {
            if self.config.merge_states
                && let Some(other) = take_merge_candidate(&mut worklist, state.pc)
            {
                state = state.merge_with(&other);
            }

            if let Some(timeout) = self.config.timeout
                && start_time.elapsed() > timeout
            {
                result.diagnostics.push("exploration timed out".to_string());
                break;
            }

            if avoid_set.contains(&state.pc) {
                result.avoided_states += 1;
                continue;
            }

            if find_set.contains(&state.pc) {
                let feasible = self.solver.is_sat(&state);
                if feasible {
                    self.stats.paths_completed += 1;
                    if state.depth > self.stats.max_depth_reached {
                        self.stats.max_depth_reached = state.depth;
                    }
                    result.found_paths.push(PathResult::new(state, true));
                    if result.found_paths.len() >= max_finds {
                        break;
                    }
                } else {
                    self.stats.paths_pruned += 1;
                    result.unsat_states += 1;
                }
                continue;
            }

            if self.stats.states_explored >= self.config.max_states {
                result
                    .diagnostics
                    .push("exploration stopped at max_states budget".to_string());
                break;
            }

            if state.depth >= self.config.max_depth {
                self.stats.paths_max_depth += 1;
                result.completed_states += 1;
                continue;
            }

            self.stats.states_explored += 1;

            if self.config.prune_infeasible && !self.solver.is_sat(&state) {
                self.stats.paths_pruned += 1;
                result.unsat_states += 1;
                continue;
            }

            let block_addr = state.pc;
            let Some(block) = func.get_block(block_addr) else {
                result
                    .diagnostics
                    .push(format!("no SSA block at 0x{block_addr:x}"));
                result.completed_states += 1;
                self.stats.paths_completed += 1;
                continue;
            };

            match self.executor.execute_block(&mut state, block) {
                Ok(forked_states) => {
                    for mut forked in forked_states {
                        forked.set_prev_pc(Some(block_addr));
                        if !avoid_set.contains(&forked.pc) {
                            worklist.push_back(forked);
                        } else {
                            result.avoided_states += 1;
                        }
                    }

                    if !state.is_terminated() {
                        if state.pc == block_addr
                            && let Some(next) = self.fallthrough_target(func, block_addr)
                        {
                            state.pc = next;
                        }
                        state.set_prev_pc(Some(block_addr));
                        if !avoid_set.contains(&state.pc) {
                            worklist.push_back(state);
                        } else {
                            result.avoided_states += 1;
                        }
                    } else {
                        self.stats.paths_completed += 1;
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
                Err(e) => {
                    self.stats.paths_completed += 1;
                    result.errored_states += 1;
                    result
                        .diagnostics
                        .push(format!("execution error at 0x{block_addr:x}: {e}"));
                }
            }
        }

        self.stats.total_time = start_time.elapsed();
        Ok(result)
    }
}

fn take_merge_candidate<'ctx>(
    worklist: &mut VecDeque<SymState<'ctx>>,
    pc: u64,
) -> Option<SymState<'ctx>> {
    let len = worklist.len();
    for idx in 0..len {
        if worklist[idx].pc == pc {
            return worklist.remove(idx);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SymValue;

    #[test]
    fn test_explore_config_default() {
        let config = ExploreConfig::default();
        assert_eq!(config.max_states, 1000);
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
    fn test_path_result_methods() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("rax", SymValue::concrete(42, 64));
        state.make_symbolic("rbx", 64);

        let result = PathResult::new(state, true);

        assert_eq!(result.final_pc(), 0x1000);
        assert_eq!(result.num_constraints(), 0);
        assert!(result.register_names().contains(&"rax".to_string()));
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
}
