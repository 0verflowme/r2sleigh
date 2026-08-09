//! SSA (Static Single Assignment) form for r2il.
//!
//! This crate provides SSA transformation for r2il blocks, enabling
//! dataflow analysis and optimizations.
//!
//! ## Modules
//!
//! - [`block`]: Single-block SSA conversion
//! - [`cfg`](mod@cfg): Control flow graph representation
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
pub mod aggregate_access;
pub mod assumption;
pub mod block;
pub mod branchless_guard;
pub mod canonical_fnv_o0;
pub mod cfg;
pub mod conditional_return;
pub mod control;
pub mod data_ref;
pub mod defuse;
pub mod domtree;
pub mod function;
pub mod graph;
pub mod interproc;
pub mod machine;
pub mod machine_context;
mod naming;
pub mod nested_wrap32_guard_o0;
pub mod obligation;
pub mod op;
pub mod optimize;
pub mod phi;
pub mod private_frame;
pub mod rename;
pub mod semantic;
pub mod struct_array_index;
pub mod sum_array;
pub mod taint;
pub mod var;
pub mod x86_frame;

pub use abi::AbiProfile;
pub use address::{AddressProvenanceFacts, AffineAddressTerm, ParameterAddressExpression};
pub use aggregate_access::{
    AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION, AggregateAccessBinding, AggregateAccessProjection,
    AggregateAccessProjectionFacts,
};
pub use assumption::{
    AnalysisAssumption, AnalysisAssumptionConflict, AssumptionProvenance, AssumptionScope,
    AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue,
};
pub use block::SSABlock;
pub use branchless_guard::{
    BRANCHLESS_GUARD_FACT_SCHEMA_VERSION, BranchlessGuardAbiFact, BranchlessGuardFact,
    BranchlessGuardFlagPacketFact, BranchlessGuardFrameFact, BranchlessGuardKind,
    BranchlessGuardParameterFact, BranchlessGuardReturnFact,
};
pub use canonical_fnv_o0::{
    CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION, CanonicalFnvFoldO0AbiFact,
    CanonicalFnvFoldO0AccessFact, CanonicalFnvFoldO0AsciiFact,
    CanonicalFnvFoldO0ExternalReadAliasPolicyFact, CanonicalFnvFoldO0Fact,
    CanonicalFnvFoldO0FrameFact, CanonicalFnvFoldO0HashFact, CanonicalFnvFoldO0IndexFact,
    CanonicalFnvFoldO0MemoryFact, CanonicalFnvFoldO0ParameterHomeRelayFact,
    CanonicalFnvFoldO0PredicateFact, CanonicalFnvFoldO0ReturnFact, CanonicalFnvFoldO0SlotFact,
    CanonicalFnvFoldO0TopologyFact,
};
pub use cfg::{BasicBlock, BlockTerminator, CFG, CFGEdge};
pub use conditional_return::{
    ConditionalReturnCandidateFact, ConditionalReturnCarrierFact, ConditionalReturnFunnelFact,
    ConditionalReturnPhiInputFact, ConditionalReturnRegisterPhiFact,
    ConditionalReturnStackSlotFact,
};
pub use control::{
    SsaCancellationToken, SsaExecutionControl, SsaExecutionStopReason, SsaPrepareError,
    SsaWorkControl,
};
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
pub use machine::{
    MachineAddressProvenance, MachineAddressSpace, MachineArithmeticFlagOp, MachineArithmeticMode,
    MachineArithmeticOp, MachineBitVector, MachineBitwiseOp, MachineBooleanOp, MachineBuildError,
    MachineCastKind, MachineComparisonOp, MachineEntity, MachineExpr, MachineExprArena, MachineExprId,
    MachineExprKind, MachineFunction, MachineOvershiftBehavior, MachineProjection,
    MachineProjectionFailure, MachineShiftKind, MachineSignedness, MachineStackBase, MachineType,
    MachineValueBinding, MachineValueUse, machine_address_provenance,
};
pub use machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineAbiModel, MachineAbiRegisterSlot,
    MachineMemoryEndianness, MachineMemoryModel, MachineMemorySpace,
    SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION, SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION,
    SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceAbiParameterSpec, SourceAggregateLayout,
    SourceAggregateMember, SourceCallArgumentSpec, SourceCallResult, SourceCallSiteIdentity,
    SourceCallSiteInterface, SourceCallSiteInterfaceError, SourceCarrierKind,
    SourceCarrierProjection, SourceFunctionInterface, SourceFunctionInterfaceError,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceStackSlotRole,
    SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeGraphError, SourceTypeKind,
};
pub use nested_wrap32_guard_o0::{
    NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION, NestedWrap32GuardO0AbiFact,
    NestedWrap32GuardO0AccessFact, NestedWrap32GuardO0ArithmeticFact,
    NestedWrap32GuardO0ComparisonFact, NestedWrap32GuardO0Fact, NestedWrap32GuardO0FlagPacketFact,
    NestedWrap32GuardO0FrameFact, NestedWrap32GuardO0InstructionClass,
    NestedWrap32GuardO0InstructionDisposition, NestedWrap32GuardO0ParameterFact,
    NestedWrap32GuardO0PhiLayerFact, NestedWrap32GuardO0PhysicalRange,
    NestedWrap32GuardO0ReturnFact, NestedWrap32GuardO0SlotFact, NestedWrap32GuardO0SlotsFact,
    NestedWrap32GuardO0TopologyFact,
};
pub use obligation::{
    CanonicalInstructionId, CanonicalInstructionSite, ObligationCoverageReport,
    ObligationInventoryFailure, ObligationInventoryFailureKind, SEMANTIC_OBLIGATION_SCHEMA_VERSION,
    SemanticInstructionDisposition, SemanticInstructionState, SemanticMemoryOrdering,
    SemanticObligation, SemanticObligationComponent, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind,
};
pub use op::SSAOp;
pub use optimize::{DecompilePrepConfig, OptimizationConfig, OptimizationStats, optimize_function};
pub use private_frame::{
    PRIVATE_FRAME_FACT_SCHEMA_VERSION, PrivateFrameAccessMemoryFact, PrivateFrameFact,
    PrivateFrameHomeFact, PrivateFrameHomeReloadFact, PrivateFrameLocalFact,
    PrivateFramePhysicalRangeFact, PrivateFrameRegisterCopyFact, PrivateFrameReturnAddressFact,
    PrivateFrameSavedFramePointerFact, PrivateFrameStackUpdateFact,
};
pub use semantic::{
    BlockAssumption, CANONICAL_FNV_FOLD_LOOP_FACT_SCHEMA_VERSION, CallArgumentCertificate,
    CallArgumentLocation, CallBoundarySlot, CallBoundaryValueFact, CallMemoryEffect,
    CallResultCertificate, CallResultValueRelation, CallSiteFact, CallSiteFacts, CallSiteId,
    CallsiteCertificate, CanonicalCountedLoopFact, CanonicalFnvFoldAbiFact,
    CanonicalFnvFoldAsciiFact, CanonicalFnvFoldByteLoadFact, CanonicalFnvFoldCarrierFact,
    CanonicalFnvFoldGuardFact, CanonicalFnvFoldHashFact, CanonicalFnvFoldLoopFact,
    CanonicalFnvFoldPointerFact, CanonicalFnvFoldRecurrenceFact, CanonicalFnvFoldReturnFact,
    CanonicalFnvFoldTopologyFact, CanonicalFnvFoldUnsignedLessWitness, CompareKind,
    CompareProvenance, ControlDomain, ControlDomainFacts, ControlDomainId, ControlGuard,
    GlobalObjectKey, IfRegionCertificate, LoopCarrierEdgeValue, LoopCarrierFact,
    LoopCarrierUpdateFact, LoopCertificate, LoopId, MemoryAccessCertificate, MemoryDefFact,
    MemoryLocation, MemoryPhiFact, MemorySSAFacts, MemoryUseFact, MemoryVersion, ObjectFact,
    ObjectId, ObjectKind, ObjectModel, PredicateFact, PredicateFacts, PredicateId,
    PreparedAssumptionBinding, PreparedAssumptionBindingKind, PreparedFunctionCertificates,
    PreparedFunctionFacts, PreparedProofFailure, ProofNodeId, RelativeMemoryAddress, ReturnCarrier,
    ReturnValueCertificate, SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION, SemanticId,
    SourceBoundaryFacts, SourceCallBoundaryFact, SourceFormalParameterFact,
    SourceReturnBoundaryFact, SourceReturnRegisterCompositionFact,
    SourceReturnRegisterDefinitionFact, SourceReturnRegisterOverlayFact, StackSlotCertificate,
    StructuredAccessId, StructuredDataflowFacts, StructuredLoopFact, StructuredLoopKind,
    StructuredMemoryAccessFact, StructuredRecursiveCallFact, SwitchCertificate,
    SwitchPredicateFact, ValueOwner,
};
pub use struct_array_index::{
    STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION, StructArrayIndexAbiFact, StructArrayIndexAccessFact,
    StructArrayIndexAccessKind, StructArrayIndexFact, StructArrayIndexFlagPacketFact,
    StructArrayIndexHomeFact, StructArrayIndexHomeReloadFact, StructArrayIndexLowering,
    StructArrayIndexParameterFact, StructArrayIndexReturnFact, StructArrayIndexScaleFact,
    StructArrayIndexTypeFact,
};
pub use sum_array::{
    SUM_ARRAY_FACT_SCHEMA_VERSION, SumArrayAbiFact, SumArrayFact, SumArrayFrameFact,
    SumArrayHomeFact, SumArrayHomeReloadFact, SumArrayHomeRole, SumArrayInstructionClass,
    SumArrayInstructionDispositionFact, SumArrayLowering, SumArrayO2Fact, SumArrayO2FrameFact,
    SumArrayO2GuardFact, SumArrayO2LaneFact, SumArrayO2ReductionFact, SumArrayO2ReturnFact,
    SumArrayO2ReturnPath, SumArrayO2ScalarTailFact, SumArrayO2TopologyFact,
    SumArrayO2VectorLoopFact, SumArrayO2VectorReadFact, SumArrayParameterFact,
    SumArrayPredicateFact, SumArrayReadFact, SumArrayRefusalFact, SumArrayRefusalReason,
    SumArrayReturnFact, SumArrayScalarLoopFact, SumArrayTypeFact,
};
pub use taint::{DefaultTaintPolicy, TaintAnalysis, TaintLabel, TaintPolicy, TaintResult};
pub use var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar, SSAVarNameKind};
pub use x86_frame::{X86FrameRelativeRange, X86StandardFrameFact};
