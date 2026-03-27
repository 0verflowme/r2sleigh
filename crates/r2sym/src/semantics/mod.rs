mod artifact;
mod cache;
mod classify;
mod compiler;
mod facts;
mod vm;

pub use artifact::{
    CompiledFunctionSemantics, CompiledSemanticArtifact, CompiledSemanticMode, ResidualReason,
    SemanticCapability, SemanticMode, SliceClass,
};
pub use cache::stable_scope_hash;
pub use compiler::{compile_function_semantics_with_scope, compile_semantic_artifact_with_scope};
pub use facts::{
    SymbolicBranchFact, SymbolicFunctionFactDiagnostics, SymbolicFunctionFacts,
    SymbolicReachabilityStatus, collect_symbolic_function_facts,
    collect_symbolic_function_facts_with_scope,
};
pub use vm::{
    InterpreterDispatchSummary, InterpreterKind, VmStateUpdate, VmStepSummary, VmTransferArm,
    VmValueExpr,
};
pub(crate) use vm::{build_vm_step_summary, classify_interpreter_like};
