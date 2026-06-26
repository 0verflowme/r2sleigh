pub mod callee;
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
pub mod role_registry;
pub mod signature;
pub mod signature_infer;
pub mod solver;
pub mod writeback;

pub use callee::{
    CalleeArityDecision, CalleeAritySource, CalleeCallArgPolicy, CalleeClass, CalleeIdentity,
    CalleeIdentityContext, CalleeIdentityEvidence, CalleeIdentityKey, CalleeResolutionFacts,
    CalleeTargetIdentityRequest, CalleeTargetPolicyDecision, CalleeTargetPolicySource,
    CalleeTargetResolutionRequest, CalleeTargetResolutionSource, CallsiteKey,
    ResolvedCalleeIdentity, ResolvedCalleeTarget, callee_name_is_import_like,
    callee_name_is_runtime_copy, callee_name_is_windows_runtime_registration,
    normalize_callee_name,
};
pub use constraint::{Constraint, ConstraintSource, MemoryCapability};
pub use context::{
    ExternalAssumptionPayloadParseError, ExternalBaseTypeJson, ExternalBaseTypeKind,
    ExternalBaseTypeMemberJson, ExternalCalleeJson, ExternalCalleeLinkageJson, ExternalContextJson,
    ExternalContextMetadataJson, ExternalEnumVariantJson, ExternalRegisterParamSpec,
    ExternalSignatureJson, ExternalSignatureParamJson, ExternalStackBase, ExternalStackSlotRole,
    ExternalStackSlotSpec, ExternalStackVarSpec, ExternalVarJson, ExternalVarKind,
    KnownSignatureJson, ParsedExternalContext, StackSlotKey, apply_main_signature_override,
    canonical_main_signature_spec, function_type_facts_from_parsed_context, is_c_main_function,
    is_generic_arg_name, merge_signature_with_register_params, normalize_function_basename,
    parse_external_assumption_payload_json, parse_external_context, parse_external_context_json,
};
pub use convert::{CTypeLike, to_c_type_like};
pub use external::{
    ExternalAggregateKind, ExternalEnum, ExternalField, ExternalStruct, ExternalTypeDb,
    ExternalTypedef, ExternalUnion, normalize_external_type_name,
};
pub use facts::{
    ArrayIndexBase, ArrayIndexCertificate, CalleeAllocationEffect, CalleeArgEffect,
    CalleeAtomicEffect, CalleeAtomicOp, CalleeAtomicOrdering, CalleeFact, CalleeLifetimeEffect,
    CalleeLifetimeOp, CalleeLinkage, CalleeMemoryEffect, CalleeMemoryEffectKind,
    CalleeMemoryLocation, CalleeMemoryRange, CalleeMemoryRegion, CalleeModelPolicyEvidence,
    CalleeReturnRelation, CalleeSyncEffect, CalleeSyncOp, CalleeTransferEffect,
    CalleeTransferLength, FieldAccessCertificate, FunctionParamSpec, FunctionSignatureProjection,
    FunctionSignatureSpec, FunctionType, FunctionTypeFactInputs, FunctionTypeFacts,
    FunctionTypeFactsBuilder, InterprocFactDiagnostics, LocalFieldAccessFact, OutParamCertificate,
    OutParamCertificateEvidence, OutParamCertificateSource, ResolvedFieldLayout,
    SIGNATURE_PROJECTION_STRONG_CONFIDENCE, SIGNATURE_PROJECTION_WEAK_CONFIDENCE,
    SignatureCertificate, SignatureCertificateSource, SignatureProjectionRejection,
    SignatureProjectionResult, SignatureProjectionSource, VisibleBinding, VisibleBindingKind,
    is_generic_signature_type, parse_type_like_spec, signature_hint_can_replace_existing,
    signature_param_count_is_authoritative, signature_param_name_is_weak,
    signature_projection_is_exact, signature_return_hint_can_replace_existing, signature_strength,
    summary_hint_can_replace_weak_existing,
};
pub use function_facts::{
    AnalysisPlans, CallArgumentValueFact, CallsiteArgumentFacts, DecompileCapabilityView,
    DecompileRouteFacts, DecompileRouteKind, FunctionCallsiteFacts, FunctionFacts,
    InterprocSummaryView, RegisterCallArgumentLocationFact, StackCallArgumentLocationFact,
    SummaryEffectRollup, SummaryHelperView, SummaryOutParamFact,
};
pub use inference::{CombinedTypeOracle, TypeInference};
pub use model::{Signedness, StructField, StructShape, Type, TypeArena, TypeId};
pub use oracle::{LayoutOracle, TypeOracle};
pub use prepare::{
    ArgAliasMap, BaseRegList, MetadataScalarKind, SignatureTypeEvidenceContext, TypeHint,
    TypeHintRank, X86_ARG_REGS, X86_FRAME_BASES, collect_pointer_arg_slots,
    collect_signature_type_evidence_context, merge_type_hint, recover_vars_arch_profile,
    recover_vars_from_ssa, scalar_metadata_type_hint, scalar_register_family_key,
    size_to_signed_int_type, size_to_type, size_to_unsigned_int_type, ssa_var_block_key,
    ssa_var_key, type_hint_from_value_metadata,
};
pub use r2ssa::AssumptionUsageReport;
pub use role_registry::{
    normalize_role_name, semantic_typedef_is_authoritative, signature_hint_for_role_identity,
    signature_hint_for_summary_kinds, type_projection_for_role_identity,
};
pub use signature::{ResolvedSignature, SignatureRegistry};
pub use signature_infer::{
    RecoveredSignatureParam, SignatureParamCandidate, SignatureTypeEvidence,
    build_inferred_signature, collect_signature_type_evidence_for_var, collect_version0_input_regs,
    compute_callconv_inference, compute_signature_confidence,
    enrich_known_function_signatures_from_names, format_afs_signature,
    infer_signature_from_prepared_ssa, infer_signature_return_type,
    inferred_signature_from_signature_spec, materialize_signature_type_like,
    merge_initial_signature_type_evidence, merge_pointer_slot_evidence_into_signature_params,
    render_signature_type, resolve_evidence_driven_signature_type,
};
pub use solver::{SolvedTypes, SolverConfig, SolverDiagnostics, TypeSolver};
pub use writeback::{
    CALLCONV_WRITEBACK_MIN_CONFIDENCE, GlobalTypeLinkCandidate, InferredSignature,
    InferredSignatureParam, LocalStructArtifacts, MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE,
    RecoveredVariable, SIGNATURE_WRITEBACK_MAX_BLOCKS, SIGNATURE_WRITEBACK_MIN_CONFIDENCE,
    SignatureRegisterArgRenameDecision, SignatureWritebackActionDecision,
    SignatureWritebackActionKind, SignatureWritebackDecision, StructDeclCandidate,
    StructDeclSource, StructFieldCandidate, TYPE_WRITEBACK_RENAME_MIN_CONFIDENCE_DEFAULT,
    TYPE_WRITEBACK_STRUCT_MIN_CONFIDENCE_DEFAULT, TYPE_WRITEBACK_TYPE_MIN_CONFIDENCE_DEFAULT,
    TypeWritebackAnalysis, TypeWritebackAnalysisInput, TypeWritebackApplyDecision,
    TypeWritebackApplyMode, TypeWritebackApplyPolicy, TypeWritebackAuthorityReport,
    TypeWritebackDiagnostics, TypeWritebackMutation, TypeWritebackMutationBudget,
    TypeWritebackMutationKind, TypeWritebackMutationPlan, TypeWritebackPlan,
    TypeWritebackRenameApplyDecision, TypeWritebackSemanticInputs, VarRenameCandidate,
    VarTypeCandidate, WritebackEvidence, WritebackSource,
    apply_semantic_artifact_signature_hint_to_inferred,
    augment_function_type_facts_with_summary_evidence,
    augment_local_struct_artifacts_with_semantics, build_semantic_type_fallback_plan,
    build_type_writeback_analysis, build_type_writeback_analysis_with_semantics,
    callconv_writeback_arch_supported, canonicalize_writeback_apply_type_name,
    field_access_certificates_from_struct_artifacts, infer_local_struct_artifacts_from_ssa,
    inferred_signature_to_function_type_facts, local_field_accesses_from_struct_artifacts,
    semantic_artifact_prefers_bounded_type_plan, signature_certificate_source_names,
    signature_hint_for_semantic_artifact, signature_projection_for_semantic_artifact,
    signature_register_arg_duplicate_delete_required, signature_register_arg_rename_decision,
    signature_register_arg_stack_conflict_delete_required,
    signature_register_arg_type_apply_required, signature_register_arg_var_score,
    signature_writeback_action_decision, signature_writeback_arch_supported,
    signature_writeback_decision, signature_writeback_size_eligible,
    type_writeback_authority_report, type_writeback_authority_report_with_policy,
    type_writeback_global_type_link_apply_decision, type_writeback_mutation_plan,
    type_writeback_mutation_plan_with_policy,
    type_writeback_stack_arg_name_conflict_delete_required,
    type_writeback_var_rename_apply_decision, type_writeback_var_type_apply_decision,
    writeback_apply_type_name_is_generic, writeback_apply_type_name_is_opaque_placeholder,
    writeback_type_materialization_key, writeback_type_materialization_required,
    writeback_type_name_is_generic, writeback_type_name_is_opaque_placeholder,
    writeback_var_name_is_generated,
};
