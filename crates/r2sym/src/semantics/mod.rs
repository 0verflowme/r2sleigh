mod artifact;
mod cache;
mod classify;
mod compiler;
pub(crate) mod facts;
pub(crate) mod native_worker;
mod plan;
mod region;
mod vm;

pub(crate) use artifact::TargetQueryRouteInput;
pub use artifact::{
    ResidualReason, SemanticArtifact, SemanticArtifactBody, SemanticConfidence, SemanticEvidence,
    SemanticEvidenceAmbiguity, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason, SemanticEvidenceSoundness, SliceClass,
};
pub use cache::{
    SEMANTIC_ARTIFACT_SCHEMA_VERSION, SemanticCompilationResult, SemanticSeedMode,
    stable_scope_hash,
};
pub use compiler::compile_semantic_artifact_default_with_scope;
pub use compiler::{
    compile_function_semantics_with_scope, compile_function_semantics_with_scope_and_replay_seed,
    compile_named_native_worker_summary_artifact, compile_native_worker_summary_artifact,
    compile_query_semantic_artifact_with_scope,
    compile_query_semantic_artifact_with_scope_and_replay_seed,
    compile_semantic_artifact_with_scope, compile_semantic_artifact_with_scope_and_replay_seed,
    compile_summary_dense_worker_artifact_from_interproc_summary,
};
pub use facts::{SymbolicReachabilityStatus, augment_semantic_artifact_with_interproc_summary};
pub use native_worker::{
    has_native_worker_summary_family, has_program_orchestrator_summary_family,
};
pub use plan::{
    ArtifactBuildPlan, DecompilePlan, QueryGuidanceMode, QueryPlan, TargetQueryExecutionRoute,
    TargetQueryPlan, TargetQueryRoutePlan, TypePlan,
};
pub use region::{
    ArtifactGranularity, ControlFact, ExecutionModel, Judged, MemoryFact, NativeArtifactBody,
    NativeFunctionSummary, NativeLoopSummary, NativeMemoryAccessKind, NativeMemoryAccessSummary,
    NativeParserKind, NativeParserSummary, NativeReductionSummary, NativeRegionSummary,
    NativeSummarySpecificity, NativeWorkerFold, NativeWorkerFoldOperation, NativeWorkerLoopSummary,
    NativeWorkerSummary, NativeWorkerSummaryKind, NativeWorkerTerminator, RefinementStage,
    RegionKey, SemanticArtifactDiagnostics, SemanticPredicate, SemanticRegion,
    SemanticTargetConditionSource, TargetFact, VmArtifactBody,
};
pub use vm::{
    InterpreterDispatchSummary, InterpreterKind, VmBinaryOp, VmGuardCondition, VmGuardedExit,
    VmMemoryCondition, VmMemoryRegionRef, VmStateUpdate, VmStepSummary, VmTransferArm, VmUnaryOp,
    VmValueExpr, has_strong_vm_evidence, strong_vm_step_summary,
};
pub(crate) use vm::{build_vm_step_summary, classify_interpreter_like};
