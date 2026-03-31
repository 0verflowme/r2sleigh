pub mod constraint;
pub mod context;
pub mod convert;
pub mod external;
pub mod facts;
pub mod inference;
pub mod lattice;
pub mod model;
pub mod oracle;
pub mod signature;
pub mod solver;
pub mod writeback;

pub use constraint::{Constraint, ConstraintSource, MemoryCapability};
pub use context::{
    ExternalBaseTypeJson, ExternalBaseTypeKind, ExternalContextJson, ExternalRegisterParamSpec,
    ExternalSignatureJson, ExternalSignatureParamJson, ExternalStackBase, ExternalStackSlotRole,
    ExternalStackSlotSpec, ExternalStackVarSpec, ExternalVarJson, ExternalVarKind,
    KnownSignatureJson, ParsedExternalContext, StackSlotKey, apply_main_signature_override,
    canonical_main_signature_spec, is_c_main_function, is_generic_arg_name,
    merge_signature_with_register_params, normalize_function_basename, parse_external_context_json,
};
pub use convert::{CTypeLike, to_c_type_like};
pub use external::{
    ExternalEnum, ExternalField, ExternalStruct, ExternalTypeDb, ExternalUnion,
    normalize_external_type_name,
};
pub use facts::{
    CalleeArgEffect, CalleeFact, CalleeMemoryEffect, CalleeMemoryEffectKind, CalleeMemoryLocation,
    CalleeMemoryRange, CalleeMemoryRegion, CalleeReturnRelation, FunctionParamSpec,
    FunctionSignatureSpec, FunctionType, FunctionTypeFactInputs, FunctionTypeFacts,
    FunctionTypeFactsBuilder, InterprocFactDiagnostics, LocalFieldAccessFact, ResolvedFieldLayout,
    SymbolicBranchFact, SymbolicCompiledCondition, SymbolicConditionPrecision, SymbolicControlFact,
    SymbolicControlIsland, SymbolicControlIslandKind, SymbolicFactDiagnostics,
    SymbolicInterpreterDispatch, SymbolicInterpreterKind, SymbolicMemoryCondition,
    SymbolicMemoryRegion, SymbolicMemoryRegionKind, SymbolicMemoryRegionRef,
    SymbolicReachabilityStatus, SymbolicSemanticCapability, SymbolicSemanticConfidence,
    SymbolicSemanticEvidence, SymbolicSemanticEvidenceAmbiguity, SymbolicSemanticEvidenceCoverage,
    SymbolicSemanticEvidenceProvenance, SymbolicSemanticEvidenceReason,
    SymbolicSemanticEvidenceSoundness, SymbolicSemanticFacts, SymbolicSemanticMode,
    SymbolicSemanticResidualReason, SymbolicSemanticSliceClass, SymbolicVmBinaryOp,
    SymbolicVmGuardCondition, SymbolicVmGuardedExit, SymbolicVmStateUpdate, SymbolicVmStepSummary,
    SymbolicVmTransferArm, SymbolicVmTransferSummary, SymbolicVmUnaryOp, SymbolicVmValueExpr,
    VisibleBinding, VisibleBindingKind, parse_type_like_spec,
};
pub use inference::{CombinedTypeOracle, TypeInference};
pub use model::{Signedness, StructField, StructShape, Type, TypeArena, TypeId};
pub use oracle::{LayoutOracle, TypeOracle};
pub use signature::{ResolvedSignature, SignatureRegistry};
pub use solver::{SolvedTypes, SolverConfig, SolverDiagnostics, TypeSolver};
pub use writeback::{
    GlobalTypeLinkCandidate, InferredSignature, InferredSignatureParam, LocalStructArtifacts,
    RecoveredVariable, StructDeclCandidate, StructDeclSource, StructFieldCandidate,
    TypeWritebackAnalysis, TypeWritebackAnalysisInput, TypeWritebackDiagnostics, TypeWritebackPlan,
    VarRenameCandidate, VarTypeCandidate, WritebackEvidence, WritebackSource,
    augment_local_struct_artifacts_with_symbolic_facts, build_type_writeback_analysis,
};
