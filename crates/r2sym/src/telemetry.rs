use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use serde::Serialize;

#[derive(Debug, Clone, Default, Serialize)]
pub struct ExploreConfigSnapshot {
    pub strategy: String,
    pub max_states: usize,
    pub max_depth: usize,
    pub timeout_ms: u64,
    pub max_symbolic_targets: usize,
    pub prune_infeasible: bool,
    pub merge_states: bool,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct ExploreLimitStats {
    pub hit_state_cap: bool,
    pub hit_timeout: bool,
    pub paths_max_depth: usize,
    pub max_depth_reached: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct ExitCounts {
    pub returns: usize,
    pub exits: usize,
    pub errors: usize,
    pub unimplemented: usize,
    pub max_depth: usize,
    pub infeasible: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct SolverStats {
    pub checks: usize,
    pub sat: usize,
    pub unsat: usize,
    pub unknown: usize,
    pub model_queries: usize,
    pub solve_queries: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct MemoryStats {
    pub symbolic_reads: usize,
    pub symbolic_writes: usize,
    pub address_enumerations: usize,
    pub enumerated_targets: usize,
    pub truncated_enumerations: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct SearchStats {
    pub merge_attempts: usize,
    pub merges_performed: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct IndirectStats {
    pub switch_indirect_resolved: usize,
    pub recovered_targets: usize,
    pub unresolved_symbolic_indirects: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct ExploreStats {
    pub states_explored: usize,
    pub paths_completed: usize,
    pub paths_pruned: usize,
    pub paths_max_depth: usize,
    pub max_depth_reached: usize,
    #[serde(skip_serializing)]
    pub total_time: Duration,
    pub config: ExploreConfigSnapshot,
    pub limits: ExploreLimitStats,
    pub exit_counts: ExitCounts,
    pub solver: SolverStats,
    pub memory: MemoryStats,
    pub search: SearchStats,
    pub indirect: IndirectStats,
}

#[derive(Debug, Clone, Default)]
pub struct ExploreTelemetry {
    pub solver: SolverStats,
    pub memory: MemoryStats,
    pub search: SearchStats,
    pub indirect: IndirectStats,
}

pub(crate) type TelemetryHandle = Rc<RefCell<ExploreTelemetry>>;

pub(crate) fn new_telemetry() -> TelemetryHandle {
    Rc::new(RefCell::new(ExploreTelemetry::default()))
}
