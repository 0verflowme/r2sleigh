//! SSA (Static Single Assignment) form for r2il.
//!
//! This crate provides SSA transformation for r2il blocks, enabling
//! dataflow analysis and optimizations.
//!
//! ## Modules
//!
//! - [`block`]: Single-block SSA conversion
//! - [`cfg`]: Control flow graph representation
//! - [`defuse`]: Def-use chain analysis
//! - [`domtree`]: Dominator tree computation
//! - [`function`]: Function-level SSA with phi nodes
//! - [`op`]: SSA operation types
//! - [`phi`]: Phi-node placement algorithm
//! - [`rename`]: SSA renaming algorithm
//! - [`taint`]: Taint analysis on SSA def-use chains
//! - [`var`]: SSA variable representation

pub mod assumption;
pub mod block;
pub mod cfg;
pub mod defuse;
pub mod domtree;
pub mod function;
pub mod graph;
pub mod interproc;
mod naming;
pub mod op;
pub mod optimize;
pub mod phi;
pub mod rename;
pub mod semantic;
pub mod taint;
pub mod var;

pub use assumption::{
    AnalysisAssumption, AnalysisAssumptionConflict, AssumptionProvenance, AssumptionScope,
    AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue,
};
pub use block::SSABlock;
pub use cfg::{BasicBlock, BlockTerminator, CFG, CFGEdge};
pub use defuse::{
    BackwardSlice, DefUseInfo, SliceOpRef, backward_slice_from_op, backward_slice_from_var, def_use,
};
pub use function::{
    CFGRiskSummary, DecompilePrepFacts, DefRef, DefSite, FunctionPrepareMode, PhiNode,
    SSABlock as FunctionSSABlock, SSAFunction, SourceRef, SourceSite, SsaArtifact,
    StackAddressBase, StackAddressRoot, SwitchInfo,
};
pub use graph::{
    BlockId, GraphBlock, GraphInst, GraphValue, InstId, InstPayload, SsaGraph, UseSite, ValueId,
};
pub use interproc::{
    AbiProfile, CallArgObservation, FunctionSemanticSummary, InterprocFunctionId,
    InterprocFunctionInput, InterprocSolveConfig, InterprocSummaryDiagnostics, InterprocSummarySet,
    SummaryAllocationEffect, SummaryArgEffect, SummaryAtomicEffect, SummaryAtomicOp,
    SummaryAtomicOrdering, SummaryLifetimeEffect, SummaryLifetimeOp, SummaryMemoryEffect,
    SummaryMemoryEffectKind, SummaryMemoryLocation, SummaryMemoryRange, SummaryMemoryRegion,
    SummaryReturnRelation, SummarySyncEffect, SummarySyncOp, SummaryTransferEffect,
    SummaryTransferLength, observe_call_arguments, solve_interproc_summary_set,
};
pub use op::SSAOp;
pub use optimize::{DecompilePrepConfig, OptimizationConfig, OptimizationStats, optimize_function};
pub use semantic::{
    BlockAssumption, CallMemoryEffect, CallSiteFact, CallSiteFacts, CallSiteId,
    CallsiteCertificate, CompareKind, CompareProvenance, GlobalObjectKey, IfRegionCertificate,
    LoopCertificate, LoopId, MemoryAccessCertificate, MemoryDefFact, MemoryLocation, MemoryPhiFact,
    MemorySSAFacts, MemoryUseFact, MemoryVersion, ObjectFact, ObjectId, ObjectKind, ObjectModel,
    PredicateFact, PredicateFacts, PredicateId, PreparedAssumptionBinding,
    PreparedAssumptionBindingKind, PreparedFunctionCertificates, PreparedFunctionFacts,
    PreparedProofFailure, ProofNodeId, ReturnValueCertificate, StackSlotCertificate,
    StructuredAccessId, StructuredDataflowFacts, StructuredLoopFact, StructuredLoopKind,
    StructuredMemoryAccessFact, StructuredRecursiveCallFact, SwitchCertificate,
    SwitchPredicateFact,
};
pub use taint::{DefaultTaintPolicy, TaintAnalysis, TaintLabel, TaintPolicy, TaintResult};
pub use var::SSAVar;
