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

pub(crate) mod backward;
pub(crate) mod control;
pub(crate) mod executor;
pub(crate) mod loops;
pub(crate) mod memory;
mod memory_address;
pub mod path;
pub(crate) mod runtime;
pub(crate) mod semantic_report;
pub(crate) mod semantics;
pub mod sim;
pub(crate) mod solver;
pub(crate) mod state;
pub(crate) mod value;

pub use backward::{
    BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
    BackwardMemoryRegion, BackwardRegionRef, CompiledBackwardCondition,
    compile_target_precondition,
};
pub use control::{SymCancellationToken, SymExecutionControl, SymExecutionStopReason};
pub use executor::{CallHookResult, SymExecutor};
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
pub use path::{ExploreConfig, PathExplorer, PathResult, PublicSolvedPath, SolvedPath};
pub use runtime::{
    seed_default_state_for_arch, seed_default_state_for_prepared, seed_memory_regions_for_arch,
    seed_memory_regions_for_prepared,
};
pub use semantic_report::{
    CompiledSemanticInfo, InterpreterDispatchInfo, MemorySummaryInfo, VmGuardConditionInfo,
    VmGuardedExitInfo, VmMemoryConditionInfo, VmStateUpdateInfo, VmStepSummaryInfo,
    VmTransferArmInfo, compiled_semantic_info,
};
pub use semantics::{
    ArtifactBuildPlan, ArtifactGranularity, ControlFact, DecompilePlan, ExecutionModel,
    InterpreterDispatchSummary, InterpreterKind, Judged, MemoryFact, NativeArtifactBody,
    NativeFunctionSummary, NativeLoopSummary, NativeMemoryAccessKind, NativeMemoryAccessSummary,
    NativeParserKind, NativeParserReturnPredicate, NativeParserReturnPredicateKind,
    NativeParserSummary, NativeReductionSummary, NativeRegionSummary, NativeTableWalkSummary,
    NativeWorkerByteTransform, NativeWorkerFold, NativeWorkerFoldOperation,
    NativeWorkerLoopSummary, NativeWorkerPredicate, NativeWorkerRoleIdentity,
    NativeWorkerRoleSource, NativeWorkerSummary, NativeWorkerSummaryApplicability,
    NativeWorkerSummaryApplicabilitySource, NativeWorkerSummaryKind, NativeWorkerSummaryRouteKind,
    NativeWorkerSummaryRoutePolicy, NativeWorkerTerminator, QueryGuidanceMode, QueryPlan,
    RefinementStage, RegionKey, ResidualReason, SEMANTIC_ARTIFACT_SCHEMA_VERSION,
    SEMANTIC_CLAIM_SCHEMA_VERSION, SemanticArtifact, SemanticArtifactBody,
    SemanticArtifactDiagnostics, SemanticArtifactReport, SemanticClaim, SemanticClaimKind,
    SemanticClaimSource, SemanticClaimSummary, SemanticConfidence, SemanticEvidence,
    SemanticEvidenceAmbiguity, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason, SemanticEvidenceSoundness, SemanticPredicate, SemanticRegion,
    SemanticTargetConditionSource, SemanticTypeSeedKind, SliceClass, SummaryRoleCertificate,
    SummaryRouteCertificate, SummaryRouteCertificateKind, SymbolicReachabilityStatus, TargetFact,
    TargetQueryExecutionRoute, TargetQueryPlan, TargetQueryRoutePlan, TypePlan, VmArtifactBody,
    VmBinaryOp, VmGuardCondition, VmGuardedExit, VmMemoryCondition, VmMemoryRegionRef,
    VmStateUpdate, VmStepSummary, VmTransferArm, VmUnaryOp, VmValueExpr,
    augment_semantic_artifact_with_interproc_summary, compile_function_semantics,
    compile_function_semantics_with_control, compile_native_worker_summary_artifact,
    compile_semantic_artifact, compile_semantic_artifact_default,
    compile_semantic_artifact_default_with_control,
    compile_summary_dense_worker_artifact_from_interproc_summary,
    function_semantic_summary_seed_for_name, function_semantic_summary_seed_for_name_with_linkage,
    has_program_orchestrator_summary_family, has_strong_vm_evidence,
    is_anonymous_semantic_route_name, is_autogenerated_semantic_function_name,
    native_worker_summary_applicability_for_summary,
    native_worker_summary_route_policy_for_summary, normalize_native_worker_role_name,
    semantic_summary_has_modeled_evidence, semantic_summary_has_runtime_copy_role,
    strong_vm_step_summary,
};
pub use sim::{
    CallConv, CallInfo, FunctionSummary, SummaryEffect, SummaryInstallStats, SummaryProfile,
    SummaryRegistry,
};
pub use solver::{SatResult, SolverStats, SymModel, SymSolver};
pub use state::{
    PendingExceptionContinuation, RuntimeBlockReason, RuntimeRegionAlias, RuntimeState,
    RuntimeValueProvenance, SymState, SymbolicFdInput, SymbolicMemoryRegion,
};
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
