pub mod constraint;
pub mod context;
pub mod convert;
pub mod external;
pub mod facts;
pub mod function_facts;
pub mod inference;
pub mod lattice;
pub mod model;
pub mod oracle;
pub mod prepare;
pub mod signature;
pub mod signature_infer;
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
    VisibleBinding, VisibleBindingKind, parse_type_like_spec,
};
pub use function_facts::FunctionFacts;
pub use inference::{CombinedTypeOracle, TypeInference};
pub use model::{Signedness, StructField, StructShape, Type, TypeArena, TypeId};
pub use oracle::{LayoutOracle, TypeOracle};
pub use prepare::{
    ArgAliasMap, BaseRegList, SignatureTypeEvidenceContext, TypeHint, TypeHintRank, X86_ARG_REGS,
    X86_FRAME_BASES, collect_pointer_arg_slots, collect_signature_type_evidence_context,
    merge_type_hint, recover_vars_arch_profile, recover_vars_from_ssa, scalar_register_family_key,
    size_to_type, ssa_var_block_key, ssa_var_key,
};
pub use signature::{ResolvedSignature, SignatureRegistry};
pub use signature_infer::{
    RecoveredSignatureParam, SignatureParamCandidate, SignatureTypeEvidence,
    build_inferred_signature, collect_signature_type_evidence_for_var, collect_version0_input_regs,
    compute_callconv_inference, compute_signature_confidence,
    enrich_known_function_signatures_from_names, format_afs_signature,
    infer_signature_from_prepared_ssa, infer_signature_return_type,
    materialize_signature_type_like, merge_initial_signature_type_evidence,
    merge_pointer_slot_evidence_into_signature_params, render_signature_type,
    resolve_evidence_driven_signature_type,
};
pub use solver::{SolvedTypes, SolverConfig, SolverDiagnostics, TypeSolver};
pub use writeback::{
    GlobalTypeLinkCandidate, InferredSignature, InferredSignatureParam, LocalStructArtifacts,
    RecoveredVariable, StructDeclCandidate, StructDeclSource, StructFieldCandidate,
    TypeWritebackAnalysis, TypeWritebackAnalysisInput, TypeWritebackDiagnostics, TypeWritebackPlan,
    TypeWritebackSemanticInputs, VarRenameCandidate, VarTypeCandidate, WritebackEvidence,
    WritebackSource, augment_local_struct_artifacts_with_semantics,
    build_semantic_type_fallback_plan, build_type_writeback_analysis,
    build_type_writeback_analysis_with_semantics, infer_local_struct_artifacts_from_ssa,
    semantic_artifact_prefers_bounded_type_plan,
};
