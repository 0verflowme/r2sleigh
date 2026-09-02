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

pub(crate) mod abi;
pub(crate) mod address;
pub(crate) mod aggregate_access;
pub(crate) mod assumption;
pub mod block;
pub mod cfg;
pub(crate) mod control;
pub(crate) mod data_ref;
pub(crate) mod deadphi;
pub(crate) mod defuse;
pub mod domtree;
pub(crate) mod execution;
pub(crate) mod fingerprint;
pub mod function;
pub mod graph;
pub(crate) mod indirect;
pub(crate) mod integrity;
pub mod interproc;
pub mod ledger;
pub(crate) mod liveout;
pub(crate) mod machine;
pub(crate) mod machine_context;
pub(crate) mod mirror;
mod naming;
pub(crate) mod obligation;
pub(crate) mod op;
pub(crate) mod optimize;
pub(crate) mod phi;
pub mod proven;
pub(crate) mod reaching_rules;
pub mod recover_interface;
pub(crate) mod rename;
pub(crate) mod semantic;
pub mod span;
pub mod taint;
pub(crate) mod var;

pub use abi::AbiProfile;
pub use address::{AddressProvenanceFacts, AffineAddressTerm, ParameterAddressExpression};
pub use aggregate_access::{
    AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION, AggregateAccessBinding, AggregateAccessProjection,
    AggregateAccessProjectionFacts, AggregateElementIndexProjection,
};
pub use assumption::{
    AnalysisAssumption, AnalysisAssumptionConflict, AssumptionProvenance, AssumptionScope,
    AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue,
};
pub use block::SSABlock;
pub use cfg::{BasicBlock, BlockTerminator, CFG, CFGEdge};
pub use control::{
    SsaCancellationToken, SsaExecutionControl, SsaExecutionStopReason, SsaPrepareError,
    SsaWorkControl,
};
pub use data_ref::{
    DataRefFact, DataRefKind, data_refs_from_artifact_with_op_sources, data_refs_from_blocks,
    parse_const_value,
};
pub use defuse::{
    BackwardSlice, DefUseInfo, SliceOpRef, backward_slice_from_op, backward_slice_from_var, def_use,
};
pub use execution::{
    ArtifactBlockId, ArtifactInstId, ArtifactValueId, EntryStorageError, ExecutionBlockRef,
    ExecutionEffect, ExecutionInstRef, ExecutionOpcode, ExecutionOperands, ExecutionOperation,
    ExecutionPhiIncoming, ExecutionValueRef, ExecutionViewError, SsaExecutionView,
};
pub use fingerprint::{SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION, stable_ssa_semantic_fingerprint};
pub use function::{
    CFGRiskSummary, DecompilePrepFacts, DefRef, DefSite, FunctionPrepareMode,
    GenuineNativeInstructionSpan, PhiNode, SSABlock as FunctionSSABlock, SSAFunction, SourceRef,
    SourceSite, SsaArtifact, SsaArtifactAuthority, SsaArtifactProvenanceKind, StackAddressBase,
    StackAddressRoot, SwitchInfo, TrustedSsaArtifact,
};
pub use graph::{
    BlockId, GraphBlock, GraphInst, GraphValue, InstId, InstPayload, SsaGraph, UseSite, ValueId,
};
pub use integrity::{ScalarWidthRule, SsaIntegrityError, SsaValueSite, validate_ssa_function};
pub use interproc::{
    CallArgObservation, FunctionSemanticLinkage, FunctionSemanticSummary, InterprocFunctionId,
    InterprocFunctionInput, InterprocSolveConfig, InterprocSummaryDiagnostics, InterprocSummarySet,
    PreparedInterprocFunctionInput, PreparedInterprocSummaryError, PreparedInterprocSummarySet,
    SummaryAllocationEffect, SummaryArgEffect, SummaryAtomicEffect, SummaryAtomicOp,
    SummaryAtomicOrdering, SummaryLifetimeEffect, SummaryLifetimeOp, SummaryMemoryEffect,
    SummaryMemoryEffectKind, SummaryMemoryLocation, SummaryMemoryRange, SummaryMemoryRegion,
    SummaryReturnRelation, SummarySyncEffect, SummarySyncOp, SummaryTransferEffect,
    SummaryTransferLength, observe_call_arguments, solve_interproc_summary_set,
    solve_prepared_interproc_summary_set,
};
pub use machine::{
    MachineAddressProvenance, MachineAddressSpace, MachineArithmeticFlagOp, MachineArithmeticMode,
    MachineArithmeticOp, MachineBitVector, MachineBitwiseOp, MachineBooleanOp, MachineBuildError,
    MachineCastKind, MachineComparisonOp, MachineDirectValueGeometry, MachineEntity, MachineExpr,
    MachineExprArena, MachineExprId, MachineExprKind, MachineFunction, MachineOvershiftBehavior,
    MachineProjection, MachineProjectionFailure, MachineRegisterValueGeometry, MachineShiftKind,
    MachineSignedness, MachineStackBase, MachineType, MachineUseConversion, MachineUseDisposition,
    MachineUseRefusal, MachineUseSlice, MachineValueBinding, MachineValueGeometryDisposition,
    MachineValueGeometryRefusal, MachineValueUse, MachineWriteDisposition, MachineWriteProjection,
    MachineWriteRefusal, MachineZeroDivisorBehavior, machine_address_provenance,
};
pub use machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineAbiModel, MachineAbiRegisterSlot,
    MachineArchitectureFamily, MachineMemoryEndianness, MachineMemoryModel, MachineMemorySpace,
    MachineRegisterGeometryState, SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceAbiClass,
    SourceAbiParameterSpec, SourceAggregateLayout, SourceAggregateMember, SourceCallArgumentSpec,
    SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface,
    SourceCallSiteInterfaceError, SourceCarrierKind, SourceCarrierProjection,
    SourceConventionSlots, SourceFunctionInterface, SourceFunctionInterfaceError,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceMachineRoles,
    SourceMachineRolesError, SourceStackAllocationContract, SourceStackGrowth, SourceStackSlotRole,
    SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeGraphError, SourceTypeKind,
};
pub use obligation::{
    CanonicalInstructionId, CanonicalInstructionSite, ObligationCoverageReport,
    ObligationInventoryFailure, ObligationInventoryFailureKind, SEMANTIC_OBLIGATION_SCHEMA_VERSION,
    SemanticInstructionDisposition, SemanticInstructionState, SemanticMemoryOrdering,
    SemanticObligation, SemanticObligationComponent, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind, SemanticSourceSite,
};
pub use op::SSAOp;
pub use optimize::{DecompilePrepConfig, OptimizationConfig, OptimizationStats, optimize_function};
pub use r2sleigh_lift::{
    GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION, GenuineLiftedFunction, GenuineLiftedFunctionAuthority,
    TrustedLiftedFunction,
};
pub use r2source::{OwnedFunctionSnapshot, RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION};
pub use semantic::{
    BlockAssumption, CallArgumentCertificate, CallArgumentLocation, CallBoundarySlot,
    CallBoundaryValueFact, CallMemoryEffect, CallResultCertificate, CallResultValueRelation,
    CallSiteFact, CallSiteFacts, CallSiteId, CalleeStackAllocationCertificate, CallsiteCertificate,
    CompareKind, CompareProvenance, ControlDomain, ControlDomainFacts, ControlDomainId,
    ControlGuard, GlobalObjectKey, IfRegionCertificate, InductionFact, InductionStep,
    LoopCarrierEdgeValue, LoopCarrierFact, LoopCarrierMemberFact, LoopCarrierMemberRole,
    LoopCarrierUpdateFact, LoopCertificate, LoopId, MachineReturnControlCertificate,
    MemoryAccessCertificate, MemoryDefFact, MemoryLocation, MemoryObjectKey, MemoryPhiFact,
    MemorySSAFacts, MemoryUseFact, MemoryVersion, ObjectFact, ObjectId, ObjectKind, ObjectModel,
    ObjectSpaceId, ParameterObjectKey, PredicateFact, PredicateFacts, PredicateId,
    PreparedAssumptionBinding, PreparedAssumptionBindingKind, PreparedFunctionCertificates,
    PreparedFunctionFacts, PreparedProofFailure, ProofNodeId, RelativeMemoryAddress, ReturnCarrier,
    ReturnValueCertificate, ReturnValueOverlay, SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION,
    SemanticId, SourceBoundaryFacts, SourceCallArgumentFact, SourceCallArgumentValue,
    SourceCallBoundaryFact, SourceFormalParameterFact, SourceReturnAddressFact,
    SourceReturnBoundaryFact, SourceReturnRegisterCompositionFact,
    SourceReturnRegisterDefinitionFact, SourceReturnRegisterOverlayFact,
    SourceReturnStackPointerFact, StackFrameRoundTripCertificate, StackGeometryCertificate,
    StackObjectKey, StackSlotCertificate, StructuredAccessId, StructuredDataflowFacts,
    StructuredLoopFact, StructuredLoopKind, StructuredMemoryAccessFact,
    StructuredRecursiveCallFact, SwitchCertificate, SwitchPredicateFact, ValueOwner,
};
pub use taint::{DefaultTaintPolicy, TaintAnalysis, TaintLabel, TaintPolicy, TaintResult};
pub use var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar, SSAVarNameKind};
