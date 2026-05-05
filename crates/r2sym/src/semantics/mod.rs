mod artifact;
mod cache;
mod classify;
mod compiler;
pub(crate) mod facts;
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
    compile_query_semantic_artifact_with_scope,
    compile_query_semantic_artifact_with_scope_and_replay_seed,
    compile_semantic_artifact_with_scope, compile_semantic_artifact_with_scope_and_replay_seed,
};
pub use facts::{SymbolicReachabilityStatus, augment_semantic_artifact_with_interproc_summary};
pub use plan::{
    ArtifactBuildPlan, DecompilePlan, QueryGuidanceMode, QueryPlan, TargetQueryExecutionRoute,
    TargetQueryPlan, TargetQueryRoutePlan, TypePlan,
};
pub use region::{
    ArtifactGranularity, ControlFact, ExecutionModel, Judged, MemoryFact, NativeArtifactBody,
    NativeFunctionSummary, RefinementStage, RegionKey, SemanticArtifactDiagnostics,
    SemanticPredicate, SemanticRegion, SemanticTargetConditionSource, TargetFact, VmArtifactBody,
};
pub use vm::{
    InterpreterDispatchSummary, InterpreterKind, VmBinaryOp, VmGuardCondition, VmGuardedExit,
    VmMemoryCondition, VmMemoryRegionRef, VmStateUpdate, VmStepSummary, VmTransferArm, VmUnaryOp,
    VmValueExpr,
};
pub(crate) use vm::{build_vm_step_summary, classify_interpreter_like};
