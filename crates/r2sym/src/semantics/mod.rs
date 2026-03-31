mod artifact;
mod cache;
mod classify;
mod compiler;
mod facts;
mod vm;

pub use artifact::{
    CompiledFunctionSemantics, CompiledSemanticArtifact, CompiledSemanticMode, ResidualReason,
    SemanticCapability, SemanticConfidence, SemanticEvidence, SemanticEvidenceAmbiguity,
    SemanticEvidenceCoverage, SemanticEvidenceProvenance, SemanticEvidenceReason,
    SemanticEvidenceSoundness, SemanticMode, SliceClass,
};
pub use cache::stable_scope_hash;
pub use compiler::compile_semantic_artifact_default_with_scope;
pub use compiler::{compile_function_semantics_with_scope, compile_semantic_artifact_with_scope};
pub use facts::{
    SymbolicBranchFact, SymbolicControlFact, SymbolicControlIsland, SymbolicControlIslandKind,
    SymbolicFunctionFactDiagnostics, SymbolicFunctionFacts, SymbolicMemoryIsland,
    SymbolicMemoryIslandKind, SymbolicReachabilityStatus, SymbolicWorkerIsland,
    collect_symbolic_function_facts, collect_symbolic_function_facts_with_scope,
};
pub use vm::{
    InterpreterDispatchSummary, InterpreterKind, VmBinaryOp, VmGuardCondition, VmGuardedExit,
    VmMemoryCondition, VmMemoryRegionRef, VmStateUpdate, VmStepSummary, VmTransferArm, VmUnaryOp,
    VmValueExpr,
};
pub(crate) use vm::{build_vm_step_summary, classify_interpreter_like};
