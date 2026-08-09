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
pub mod constraints;
pub mod control;
pub mod executor;
pub mod kernel;
pub mod loops;
pub mod memory;
mod memory_address;
pub mod path;
pub mod query;
pub mod r2api;
pub mod replay;
pub mod runtime;
pub mod semantic_report;
pub mod semantics;
pub mod sim;
pub mod solver;
pub mod spec;
pub mod state;
pub mod tactics;
pub mod value;
pub mod verification;

pub use backward::{
    BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
    BackwardMemoryRegion, BackwardRegionRef, CompiledBackwardCondition,
    compile_derived_summary_return_postcondition, compile_target_precondition,
};
pub use constraints::{
    FinalConstraint, FinalConstraintGraph, FinalConstraintPrecision, FinalConstraintSource,
    FoldAggregateConstraint, FoldAggregateRangeConstraint, InputByteConstraint,
    InputLengthConstraint, RecurrenceAggregateConstraint, RecurrenceAggregateRangeConstraint,
    aggregate_exact_fold_bytes, build_exact_fold_constraint_graph,
    build_final_constraint_graph_for_path, build_model_conditioned_recurrence_constraint_graph,
    exact_fold_model_bytes,
};
pub use control::{SymCancellationToken, SymExecutionControl, SymExecutionStopReason};
pub use executor::{CallHookResult, SymExecutor};
pub use kernel::{
    CallEdgePolicy, ConcreteExecutionBackend, ConcreteMemorySeed, ConcreteRunRequest,
    ConcreteRunResult, ConcreteStopReason, ConcreteTraceEvidence, EdgeId, FactPrecision,
    FunctionClosureBudget, FunctionClosureEntry, FunctionClosureExclusion,
    FunctionClosureExclusionReason, FunctionClosurePlan, FunctionClosureReason, FunctionId,
    NodeId as SemanticNodeId, RegionId as SemanticRegionId, RuntimeRegionFact, SemanticEdge,
    SemanticEdgeAction, SemanticEdgeKind, SemanticEvidenceKind, SemanticEvidenceRecord,
    SemanticNode, SemanticNodeKind, SemanticProgramGraph,
};
pub use loops::{
    ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, ExactLoopRecurrenceKind, LoopCarriedVar,
    LoopFoldOperation, LoopMemoryTerm, LoopMemoryTermKind, LoopRecurrence, LoopRecurrenceKind,
    LoopRotateDirection, LoopSummary, LoopSummaryKind, LoopTransitionExpr, LoopTransitionSystem,
    LoopVarRole, RuntimeLoopBranch, exact_fold_evidence_from_recurrences,
};
pub use memory::{
    MemoryRegionId, MemoryRegionKind, RegionPointer, ResolvedPointerSet, SymMemory,
    SymbolicMemoryRegionDef,
};
pub use memory_address::SemanticMemoryAddress;
pub use path::{
    ExploreConfig, PathExplorer, PathResult, PublicSolvedPath, SolvedPath, SolvedPathGeneration,
    SolvedPathGenerationKind,
};
pub use query::{
    PathConditionResult, PathConditionSummary, PathConditionTerm, QueryCompletion,
    QueryExecutionPolicy, QueryMode, ReachabilityResult, ReachabilityStatus, SolveResult,
    SymQueryConfig, SymbolicConditionSet, SymbolicFunctionSummary, apply_query_execution_policy,
    install_symbolic_hooks_for_query_policy, recommended_query_max_depth,
    recommended_query_max_depth_for_route, recommended_query_max_states_for_route,
    recommended_query_timeout, recommended_query_timeout_for_route,
    route_skips_eager_scope_summaries, selected_target_query_route_in_scope,
};
pub use r2api::{R2Api, R2Error};
pub use replay::{
    ReplayMemoryOverlay, ReplayMemoryWindow, ReplayRegisterOverlay, ReplayRegisterValue,
    ReplaySeed, apply_replay_seed_to_state, seed_replay_state_for_arch,
    stable_replay_seed_fingerprint,
};
pub use runtime::{
    install_runtime_hooks_for_scope, seed_default_state_for_arch, seed_memory_regions_for_arch,
    seed_scope_state_for_arch,
};
pub use semantic_report::{
    CompiledSemanticInfo, InterpreterDispatchInfo, MemorySummaryInfo, VmGuardConditionInfo,
    VmGuardedExitInfo, VmMemoryConditionInfo, VmStateUpdateInfo, VmStepSummaryInfo,
    VmTransferArmInfo, compiled_semantic_info, compiled_semantic_info_with_replay_seed,
};
pub use semantics::{
    ArtifactBuildPlan, ArtifactGranularity, CheckedClaim, ControlFact, DecompilePlan,
    ExecutionModel, InterpreterDispatchSummary, InterpreterKind, Judged, MemoryFact,
    NativeArtifactBody, NativeFunctionSummary, NativeLoopSummary, NativeMemoryAccessKind,
    NativeMemoryAccessSummary, NativeParserKind, NativeParserReturnPredicate,
    NativeParserReturnPredicateKind, NativeParserSummary, NativeReductionSummary,
    NativeRegionSummary, NativeTableWalkSummary, NativeWorkerByteTransform, NativeWorkerFold,
    NativeWorkerFoldOperation, NativeWorkerLoopSummary, NativeWorkerNameRouteFacts,
    NativeWorkerPredicate, NativeWorkerRoleIdentity, NativeWorkerRoleSource, NativeWorkerSummary,
    NativeWorkerSummaryApplicability, NativeWorkerSummaryApplicabilitySource,
    NativeWorkerSummaryKind, NativeWorkerSummaryRouteKind, NativeWorkerSummaryRoutePolicy,
    NativeWorkerTerminator, PROOF_COVERAGE_SCHEMA_VERSION, ProofCoverage, ProofFailure,
    ProofObligation, ProofObligationKind, ProofOwner, QueryGuidanceMode, QueryPlan,
    RefinementStage, RegionKey, RenderPermission, RenderPermissionKind, ResidualReason,
    SEMANTIC_ARTIFACT_SCHEMA_VERSION, SEMANTIC_CLAIM_SCHEMA_VERSION, SemanticArtifact,
    SemanticArtifactBody, SemanticArtifactDiagnostics, SemanticClaim, SemanticClaimKind,
    SemanticClaimSource, SemanticClaimSummary, SemanticCompilationResult, SemanticConfidence,
    SemanticEvidence, SemanticEvidenceAmbiguity, SemanticEvidenceCoverage,
    SemanticEvidenceProvenance, SemanticEvidenceReason, SemanticEvidenceSoundness,
    SemanticPredicate, SemanticRegion, SemanticSeedMode, SemanticTargetConditionSource,
    SemanticTypeSeedKind, SliceClass, SummaryRoleCertificate, SummaryRouteCertificate,
    SummaryRouteCertificateKind, SymbolicReachabilityStatus, TargetFact, TargetQueryExecutionRoute,
    TargetQueryPlan, TargetQueryRoutePlan, TypePlan, VmArtifactBody, VmBinaryOp, VmGuardCondition,
    VmGuardedExit, VmMemoryCondition, VmMemoryRegionRef, VmStateUpdate, VmStepSummary,
    VmTransferArm, VmUnaryOp, VmValueExpr, augment_semantic_artifact_with_interproc_summary,
    compile_function_semantics_with_scope, compile_function_semantics_with_scope_and_replay_seed,
    compile_named_native_worker_summary_artifact, compile_native_worker_summary_artifact,
    compile_query_semantic_artifact_with_scope,
    compile_query_semantic_artifact_with_scope_and_replay_seed,
    compile_semantic_artifact_default_with_scope, compile_semantic_artifact_with_scope,
    compile_semantic_artifact_with_scope_and_replay_seed,
    compile_summary_dense_worker_artifact_from_interproc_summary,
    function_semantic_summary_seed_for_name, function_semantic_summary_seed_for_name_with_linkage,
    has_native_worker_summary_family, has_program_orchestrator_summary_family,
    has_strong_vm_evidence, is_anonymous_semantic_route_name,
    is_autogenerated_semantic_function_name, native_worker_summary_applicability_for_summary,
    native_worker_summary_route_policy_for_summary, normalize_native_worker_role_name,
    semantic_summary_has_modeled_evidence, semantic_summary_has_runtime_copy_role,
    stable_scope_hash, strong_vm_step_summary,
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
pub use state::{
    PendingExceptionContinuation, RuntimeBlockReason, RuntimeRegionAlias, RuntimeState,
    RuntimeValueProvenance, SymState, SymbolicFdInput, SymbolicMemoryRegion,
};
pub use tactics::{
    InputByteDomain, SolveTacticCandidate, SolveTacticConfig, TacticConstraintReport,
    algebraic_preimage_candidate, algebraic_preimage_for_target, constrain_exact_fold_candidate,
    constrain_exact_fold_inputs, constrain_exact_recurrence_candidate,
    tactic_candidates_for_constraint_graph,
};
pub use value::SymValue;
pub use verification::{
    CandidateReplayBackend, CandidateReplayRequest, EvidenceSummary, LiftedReplayBackend,
    ModelValidation, SolveCandidateShape, SolveStatus, SolveTacticEvidence, SolveTacticKind,
    SolveTacticStatus, SolveVerification, SolveVerificationRequest, SolveWitness,
    UnavailableReplayBackend, VerificationRequirement, evidence_summary_for_route_and_stats,
    solution_extraction_allowed, solve_tactics_for_exact_folds,
    solve_tactics_for_exact_recurrences, verification_requirement_for_route_and_stats,
    verify_solve_result,
};

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

    /// Cooperative cancellation was requested.
    #[error("Symbolic execution cancelled")]
    Cancelled,

    /// The caller-provided deadline expired.
    #[error("Symbolic execution deadline exceeded")]
    DeadlineExceeded,
}

impl From<SymExecutionStopReason> for SymError {
    fn from(reason: SymExecutionStopReason) -> Self {
        match reason {
            SymExecutionStopReason::Cancelled => Self::Cancelled,
            SymExecutionStopReason::DeadlineExceeded => Self::DeadlineExceeded,
        }
    }
}

pub type SymResult<T> = Result<T, SymError>;
