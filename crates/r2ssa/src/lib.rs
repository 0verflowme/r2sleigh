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

pub mod abi;
pub mod address;
pub mod assumption;
pub mod block;
pub mod cfg;
pub mod data_ref;
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

pub use abi::AbiProfile;
pub use address::{AddressProvenanceFacts, AffineAddressTerm, ParameterAddressExpression};
pub use assumption::{
    AnalysisAssumption, AnalysisAssumptionConflict, AssumptionProvenance, AssumptionScope,
    AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue,
};
pub use block::SSABlock;
pub use cfg::{BasicBlock, BlockTerminator, CFG, CFGEdge};
pub use data_ref::{
    DataRefFact, DataRefKind, data_refs_from_blocks, data_refs_from_ssa_with_op_sources,
    parse_const_value,
};
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
    CallArgObservation, FunctionSemanticLinkage, FunctionSemanticSummary, InterprocFunctionId,
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
    BlockAssumption, CallArgumentCertificate, CallArgumentLocation, CallMemoryEffect,
    CallResultCertificate, CallResultValueRelation, CallSiteFact, CallSiteFacts, CallSiteId,
    CallsiteCertificate, CompareKind, CompareProvenance, ControlDomain, ControlDomainFacts,
    ControlDomainId, ControlGuard, GlobalObjectKey, IfRegionCertificate, LoopCarrierEdgeValue,
    LoopCarrierFact, LoopCarrierUpdateFact, LoopCertificate, LoopId, MemoryAccessCertificate,
    MemoryDefFact, MemoryLocation, MemoryPhiFact, MemorySSAFacts, MemoryUseFact, MemoryVersion,
    ObjectFact, ObjectId, ObjectKind, ObjectModel, PredicateFact, PredicateFacts, PredicateId,
    PreparedAssumptionBinding, PreparedAssumptionBindingKind, PreparedFunctionCertificates,
    PreparedFunctionFacts, PreparedProofFailure, ProofNodeId, RelativeMemoryAddress, ReturnCarrier,
    ReturnValueCertificate, SemanticId, StackSlotCertificate, StructuredAccessId,
    StructuredDataflowFacts, StructuredLoopFact, StructuredLoopKind, StructuredMemoryAccessFact,
    StructuredRecursiveCallFact, SwitchCertificate, SwitchPredicateFact, ValueOwner,
};
pub use taint::{DefaultTaintPolicy, TaintAnalysis, TaintLabel, TaintPolicy, TaintResult};
pub use var::{SSAVar, SSAVarNameKind};
