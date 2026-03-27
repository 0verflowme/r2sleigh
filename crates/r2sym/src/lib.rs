//! Symbolic execution engine for r2sleigh.
//!
//! This crate provides symbolic execution capabilities for r2il/r2ssa,
//! using Z3 as the constraint solver backend.
//!
//! ## Architecture
//!
//! - [`value`]: Symbolic values (concrete, symbolic, or unknown)
//! - [`state`]: Symbolic execution state (registers, memory, constraints)
//! - [`memory`]: Symbolic memory model
//! - [`executor`]: Steps through SSA operations symbolically
//! - [`solver`]: Z3 solver wrapper
//! - [`path`]: Path exploration strategies
//!
//! ## Example
//!
//! ```ignore
//! use r2sym::{ExploreConfig, PathExplorer, SymState};
//! use r2ssa::SsaArtifact;
//!
//! let func = SsaArtifact::for_symbolic(&blocks, None).unwrap();
//! let ctx = z3::Context::thread_local();
//!
//! let mut state = SymState::new(&ctx, func.entry);
//! state.make_symbolic("rdi", 64);
//!
//! let mut explorer = PathExplorer::with_config(&ctx, ExploreConfig::default());
//! let results = explorer.explore(&func, state);
//! for path in results {
//!     if let Some(model) = explorer.solve_path(&path) {
//!         println!("Found inputs: {:?}", model.inputs);
//!     }
//! }
//! ```

pub mod backward;
pub mod executor;
pub mod memory;
pub mod path;
pub mod query;
pub mod r2api;
pub mod replay;
pub mod runtime;
pub mod semantics;
pub mod sim;
pub mod solver;
pub mod spec;
pub mod state;
pub mod value;

pub use backward::{
    BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
    BackwardMemoryRegion, BackwardRegionRef, CompiledBackwardCondition,
    compile_derived_summary_return_postcondition, compile_target_precondition,
};
pub use executor::{CallHookResult, SymExecutor};
pub use memory::{
    MemoryRegionId, MemoryRegionKind, RegionPointer, ResolvedPointerSet, SymMemory,
    SymbolicMemoryRegionDef,
};
pub use path::{ExploreConfig, PathExplorer, PathResult, SolvedPath};
pub use query::{
    PathConditionResult, PathConditionSummary, PathConditionTerm, QueryCompletion, QueryMode,
    ReachabilityResult, ReachabilityStatus, SolveResult, SolveStatus, SymQueryConfig,
    SymbolicConditionSet, SymbolicFunctionSummary,
};
pub use r2api::{R2Api, R2Error};
pub use replay::{
    ReplayMemoryOverlay, ReplayMemoryWindow, ReplayRegisterOverlay, ReplayRegisterValue,
    ReplaySeed, apply_replay_seed_to_state, seed_replay_state_for_arch,
};
pub use runtime::{seed_default_state_for_arch, seed_memory_regions_for_arch};
pub use semantics::{
    CompiledFunctionSemantics, CompiledSemanticArtifact, CompiledSemanticMode,
    InterpreterDispatchSummary, InterpreterKind, ResidualReason, SemanticCapability, SemanticMode,
    SliceClass, SymbolicBranchFact, SymbolicFunctionFactDiagnostics, SymbolicFunctionFacts,
    SymbolicReachabilityStatus, VmStateUpdate, VmStepSummary, VmTransferArm, VmValueExpr,
    collect_symbolic_function_facts, collect_symbolic_function_facts_with_scope,
    compile_function_semantics_with_scope, compile_semantic_artifact_with_scope, stable_scope_hash,
};
pub use sim::{
    CallConv, CallInfo, DerivedFunctionSummary, DerivedSummaryCase, DerivedSummaryCompletion,
    DerivedSummaryDiagnostics, DerivedSummaryInput, DerivedSummarySet, FunctionSummary,
    PreparedFunctionScope, ScopedPreparedFunction, SummaryEffect, SummaryInstallStats,
    SummaryProfile, SummaryRegistry,
};
pub use solver::{SatResult, SolverStats, SymModel, SymSolver};
pub use spec::{
    AddressValue, BudgetSpec, ExplorationSpec, InputSpec, MergeSpec, PredicateSpec, RuntimeSpec,
    StartSpec, StrategySpec,
};
pub use state::{RuntimeState, SymState, SymbolicFdInput, SymbolicMemoryRegion};
pub use value::SymValue;

/// Error types for symbolic execution.
#[derive(Debug, thiserror::Error)]
pub enum SymError {
    /// Z3 solver error.
    #[error("Z3 solver error: {0}")]
    SolverError(String),

    /// Unsupported operation.
    #[error("Unsupported operation: {0}")]
    UnsupportedOp(String),

    /// Memory access error.
    #[error("Memory error: {0}")]
    MemoryError(String),

    /// Path explosion (too many states).
    #[error("Path explosion: {0} states")]
    PathExplosion(usize),

    /// Timeout during exploration.
    #[error("Exploration timeout")]
    Timeout,
}

pub type SymResult<T> = Result<T, SymError>;
