mod artifact;
mod cache;
mod classify;
mod compiler;
pub(crate) mod facts;
mod plan;
mod region;
mod vm;

pub use artifact::{
    ResidualReason, SemanticArtifact, SemanticArtifactBody, SemanticConfidence, SemanticEvidence,
    SemanticEvidenceAmbiguity, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason, SemanticEvidenceSoundness, SliceClass,
};
pub use cache::{SEMANTIC_ARTIFACT_SCHEMA_VERSION, stable_scope_hash};
pub use compiler::compile_semantic_artifact_default_with_scope;
pub use compiler::{compile_function_semantics_with_scope, compile_semantic_artifact_with_scope};
pub use facts::SymbolicReachabilityStatus;
pub use plan::{
    ArtifactBuildPlan, DecompilePlan, QueryGuidanceMode, QueryPlan, TargetQueryPlan,
    TargetQueryRoutePlan, TypePlan,
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
