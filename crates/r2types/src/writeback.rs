use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::{Hash, Hasher};

use r2ssa::{
    FunctionSemanticSummary, InterprocSummarySet, SSABlock, SSAOp, SSAVar, SummaryArgEffect,
    SummaryMemoryEffect, SummaryMemoryEffectKind, SummaryMemoryRegion, SummaryReturnRelation,
};

use crate::context::{
    ExternalStackBase, ExternalStackSlotRole, ExternalStackVarSpec, ParsedExternalContext,
    StackSlotKey, apply_main_signature_override, is_c_main_function, is_generic_arg_name,
    stack_slots_from_legacy_external_stack_vars,
};
use crate::convert::CTypeLike;
use crate::external::{
    ExternalField, ExternalStruct, ExternalTypeDb, normalize_external_type_name,
};
use crate::facts::{
    CalleeArgEffect, CalleeFact, CalleeMemoryEffect, CalleeMemoryEffectKind, CalleeMemoryLocation,
    CalleeMemoryRange, CalleeMemoryRegion, CalleeReturnRelation, FunctionParamSpec,
    FunctionSignatureSpec, FunctionTypeFactInputs, FunctionTypeFacts, InterprocFactDiagnostics,
    LocalFieldAccessFact, SymbolicMemoryCondition, SymbolicMemoryRegion, SymbolicSemanticFacts,
    VisibleBinding, VisibleBindingKind, parse_type_like_spec,
};
use crate::model::Signedness;
use crate::prepare::recover_vars_arch_profile;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WritebackSource {
    LocalInferred,
    SignatureRegistry,
    ExistingState,
    ExternalTypeDb,
    DataflowRanked,
}

impl WritebackSource {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::LocalInferred => "local_inferred",
            Self::SignatureRegistry => "signature_registry",
            Self::ExistingState => "existing_state",
            Self::ExternalTypeDb => "external_type_db",
            Self::DataflowRanked => "dataflow_ranked",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WritebackEvidence {
    SsaVarRecovery,
    ExternalSignatureCurrent,
    CanonicalMainSignature,
    SsaFieldOffsetPattern,
    ExistingStackType,
    ExternalStackAnnotation,
    ExternalStackName,
    ExternalParamName,
}

impl WritebackEvidence {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::SsaVarRecovery => "ssa-var-recovery",
            Self::ExternalSignatureCurrent => "afcfj-current",
            Self::CanonicalMainSignature => "canonical-main-signature",
            Self::SsaFieldOffsetPattern => "ssa-field-offset-pattern",
            Self::ExistingStackType => "afvj-existing-type",
            Self::ExternalStackAnnotation => "afvj-stack-annotation",
            Self::ExternalStackName => "stack-var-name-from-afvj",
            Self::ExternalParamName => "afcfj-param-name",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructDeclSource {
    LocalInferred,
    ExternalTypeDb,
}

impl StructDeclSource {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::LocalInferred => "local_inferred",
            Self::ExternalTypeDb => "external_type_db",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferredSignatureParam {
    pub name: String,
    pub param_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferredSignature {
    pub function_name: String,
    pub signature: String,
    pub ret_type: String,
    pub params: Vec<InferredSignatureParam>,
    pub callconv: String,
    pub arch: String,
    pub confidence: u8,
    pub callconv_confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecoveredVariable {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    #[serde(rename = "type")]
    pub var_type: String,
    pub isarg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reg: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructFieldCandidate {
    pub name: String,
    pub offset: u64,
    pub field_type: String,
    pub confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDeclCandidate {
    pub name: String,
    pub decl: String,
    pub confidence: u8,
    pub source: StructDeclSource,
    pub fields: Vec<StructFieldCandidate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalTypeLinkCandidate {
    pub addr: u64,
    pub target_type: String,
    pub confidence: u8,
    pub source: WritebackSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarTypeCandidate {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    pub var_type: String,
    pub isarg: bool,
    pub reg: Option<String>,
    pub size: u32,
    pub confidence: u8,
    pub source: WritebackSource,
    pub evidence: Vec<WritebackEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarRenameCandidate {
    pub name: String,
    pub target_name: String,
    pub confidence: u8,
    pub source: WritebackSource,
    pub evidence: Vec<WritebackEvidence>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypeWritebackDiagnostics {
    pub conflicts: Vec<String>,
    pub warnings: Vec<String>,
    pub solver_warnings: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LocalStructArtifacts {
    pub struct_decls: Vec<StructDeclCandidate>,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeWritebackPlan {
    pub signature: InferredSignature,
    pub var_type_candidates: Vec<VarTypeCandidate>,
    pub var_rename_candidates: Vec<VarRenameCandidate>,
    pub struct_decls: Vec<StructDeclCandidate>,
    pub global_type_links: Vec<GlobalTypeLinkCandidate>,
    pub diagnostics: TypeWritebackDiagnostics,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeWritebackAnalysis {
    pub signature: InferredSignature,
    pub type_facts: FunctionTypeFacts,
    pub plan: TypeWritebackPlan,
}

pub struct TypeWritebackAnalysisInput<'a> {
    pub function_name: &'a str,
    pub ptr_bits: u32,
    pub inferred_signature: InferredSignature,
    pub recovered_vars: &'a [RecoveredVariable],
    pub ssa_blocks: &'a [SSABlock],
    pub parsed_context: ParsedExternalContext,
    pub local_structs: LocalStructArtifacts,
    pub interproc_summary_set: Option<InterprocSummarySet>,
    pub diagnostics: TypeWritebackDiagnostics,
}

pub struct TypeWritebackSemanticInputs<'a> {
    pub symbolic_facts: &'a SymbolicSemanticFacts,
    pub local_field_accesses: &'a [LocalFieldAccessFact],
}

#[derive(Debug, Clone, Default)]
struct SignatureContextMaps {
    param_types: HashMap<usize, String>,
    param_names: HashMap<usize, String>,
}

struct VarTypeCandidateContext<'a> {
    current_context_maps: &'a SignatureContextMaps,
    merged_signature: Option<&'a FunctionSignatureSpec>,
    slot_type_overrides: &'a HashMap<usize, String>,
    stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    existing_types: &'a HashMap<String, String>,
    ptr_bits: u32,
    is_main_signature: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum VisibleBindingKey {
    Param(usize),
    Stack(StackSlotKey),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GlobalAddrExpr {
    base: u64,
    offset: i64,
    confidence: u8,
}

fn summary_arg_effect_to_callee(effect: &SummaryArgEffect) -> CalleeArgEffect {
    CalleeArgEffect {
        read: effect.read,
        write: effect.write,
        escape: effect.escape,
        free: effect.free,
    }
}

fn summary_return_relation_to_callee(relation: &SummaryReturnRelation) -> CalleeReturnRelation {
    match relation {
        SummaryReturnRelation::Unknown => CalleeReturnRelation::Unknown,
        SummaryReturnRelation::Void => CalleeReturnRelation::Void,
        SummaryReturnRelation::Arg(idx) => CalleeReturnRelation::Arg(*idx),
        SummaryReturnRelation::Const(value) => CalleeReturnRelation::Const(*value),
        SummaryReturnRelation::HeapAlloc => CalleeReturnRelation::HeapAlloc,
        SummaryReturnRelation::Global(address) => CalleeReturnRelation::Global(*address),
    }
}

fn summary_memory_effect_to_callee(effect: &SummaryMemoryEffect) -> CalleeMemoryEffect {
    let kind = match effect.kind {
        SummaryMemoryEffectKind::Read => CalleeMemoryEffectKind::Read,
        SummaryMemoryEffectKind::Write => CalleeMemoryEffectKind::Write,
        SummaryMemoryEffectKind::Escape => CalleeMemoryEffectKind::Escape,
        SummaryMemoryEffectKind::Free => CalleeMemoryEffectKind::Free,
    };
    let location = CalleeMemoryLocation {
        region: match effect.location.region {
            SummaryMemoryRegion::Arg { index } => CalleeMemoryRegion::Arg { index },
            SummaryMemoryRegion::Global { address } => CalleeMemoryRegion::Global { address },
            SummaryMemoryRegion::HeapReturn => CalleeMemoryRegion::HeapReturn,
            SummaryMemoryRegion::Unknown => CalleeMemoryRegion::Unknown,
        },
        range: effect.location.range.map(|range| CalleeMemoryRange {
            offset_lo: range.offset_lo,
            offset_hi: range.offset_hi,
            width: range.width,
        }),
    };
    CalleeMemoryEffect { kind, location }
}

fn summary_param_type_hints(summary: &FunctionSemanticSummary) -> BTreeMap<usize, CTypeLike> {
    let pointer_ty = CTypeLike::Pointer(Box::new(CTypeLike::Void));
    let mut hints = BTreeMap::new();
    let mut max_idx = summary.arg_effects.keys().copied().max().unwrap_or(0);
    for effect in &summary.memory_effects {
        if let SummaryMemoryRegion::Arg { index } = effect.location.region {
            max_idx = max_idx.max(index);
        }
    }
    for idx in 0..=max_idx {
        if summary_suggests_pointer_param(summary, idx) {
            hints.insert(idx, pointer_ty.clone());
        }
    }
    hints
}

fn summary_return_type_hint(
    summary: &FunctionSemanticSummary,
    param_type_hints: &BTreeMap<usize, CTypeLike>,
) -> Option<CTypeLike> {
    match summary.return_relation {
        SummaryReturnRelation::HeapAlloc => Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
        SummaryReturnRelation::Arg(idx) => param_type_hints.get(&idx).cloned(),
        _ => None,
    }
}

fn summary_to_callee_fact(summary: &FunctionSemanticSummary) -> CalleeFact {
    let param_type_hints = summary_param_type_hints(summary);
    let return_type_hint = summary_return_type_hint(summary, &param_type_hints);
    CalleeFact {
        function_id: summary.id.0,
        name: summary.name.clone(),
        direct_callees: summary.direct_callees.iter().copied().collect(),
        callsite_count: summary.callsite_count,
        has_unknown_calls: summary.has_unknown_calls,
        arg_effects: summary
            .arg_effects
            .iter()
            .map(|(idx, effect)| (*idx, summary_arg_effect_to_callee(effect)))
            .collect(),
        memory_effects: summary
            .memory_effects
            .iter()
            .map(summary_memory_effect_to_callee)
            .collect(),
        param_type_hints,
        return_type_hint,
        return_relation: summary_return_relation_to_callee(&summary.return_relation),
        reads_global_memory: summary.reads_global_memory,
        writes_global_memory: summary.writes_global_memory,
        touches_unknown_memory: summary.touches_unknown_memory,
    }
}

fn infer_interproc_return_type(
    summary: &FunctionSemanticSummary,
    merged_signature: Option<&FunctionSignatureSpec>,
    inferred_signature: &InferredSignature,
    ptr_bits: u32,
) -> Option<CTypeLike> {
    match summary.return_relation {
        SummaryReturnRelation::HeapAlloc => Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
        SummaryReturnRelation::Arg(idx) => merged_signature
            .and_then(|signature| signature.params.get(idx))
            .and_then(|param| param.ty.clone())
            .filter(|ty| !is_generic_signature_type(Some(ty)))
            .or_else(|| {
                inferred_signature
                    .params
                    .get(idx)
                    .and_then(|param| parse_type_like_spec(&param.param_type, ptr_bits))
                    .filter(|ty| !is_generic_signature_type(Some(ty)))
            }),
        _ => None,
    }
}

fn summary_suggests_pointer_param(summary: &FunctionSemanticSummary, idx: usize) -> bool {
    summary
        .arg_effects
        .get(&idx)
        .is_some_and(|effect| effect.read || effect.write || effect.escape || effect.free)
        || summary.memory_effects.iter().any(|effect| {
            matches!(effect.location.region, SummaryMemoryRegion::Arg { index } if index == idx)
        })
}

fn maybe_upgrade_param_to_pointer(
    summary: &FunctionSemanticSummary,
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
) {
    let pointer_ty = CTypeLike::Pointer(Box::new(CTypeLike::Void));

    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }

    let Some(signature) = merged_signature.as_mut() else {
        return;
    };

    for idx in 0..signature.params.len().max(inferred_signature.params.len()) {
        if !summary_suggests_pointer_param(summary, idx) {
            continue;
        }

        let merged_param = signature.params.get_mut(idx);
        let inferred_param = inferred_signature.params.get_mut(idx);

        let merged_is_generic = merged_param.as_ref().is_some_and(|param| {
            param.ty.as_ref().is_none_or(|ty| {
                is_generic_signature_type(Some(ty))
                    || matches!(
                        ty,
                        CTypeLike::Int {
                            bits,
                            signedness: Signedness::Signed
                                | Signedness::Unsigned
                                | Signedness::Unknown,
                        } if *bits == ptr_bits
                    )
            })
        });

        let inferred_is_generic = inferred_param.as_ref().is_some_and(|param| {
            is_generic_type_string(&param.param_type)
                || matches!(
                    parse_type_like_spec(&param.param_type, ptr_bits),
                    Some(CTypeLike::Int {
                        bits,
                        signedness: Signedness::Signed
                            | Signedness::Unsigned
                            | Signedness::Unknown,
                    }) if bits == ptr_bits
                )
        });

        if merged_is_generic && let Some(param) = merged_param {
            param.ty = Some(pointer_ty.clone());
        }
        if inferred_is_generic && let Some(param) = inferred_param {
            param.param_type = render_signature_type(&pointer_ty, ptr_bits);
        }
    }
}

fn apply_interproc_summary_to_signature(
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    summary_set: Option<&InterprocSummarySet>,
    ptr_bits: u32,
) {
    let Some(summary_set) = summary_set else {
        return;
    };
    let Some(root) = summary_set.root else {
        return;
    };
    let Some(summary) = summary_set.summaries.get(&root) else {
        return;
    };
    maybe_upgrade_param_to_pointer(summary, merged_signature, inferred_signature, ptr_bits);
    let Some(ret_ty) = infer_interproc_return_type(
        summary,
        merged_signature.as_ref(),
        inferred_signature,
        ptr_bits,
    ) else {
        return;
    };

    let should_override = merged_signature
        .as_ref()
        .and_then(|signature| signature.ret_type.as_ref())
        .is_none_or(|ty| {
            is_generic_signature_type(Some(ty))
                || matches!(
                    (&ret_ty, ty),
                    (
                        CTypeLike::Pointer(_),
                        CTypeLike::Int {
                            bits,
                            signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
                        }
                    ) if *bits == ptr_bits
                )
        });
    if !should_override {
        return;
    }

    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }
    if let Some(signature) = merged_signature.as_mut() {
        signature.ret_type = Some(ret_ty.clone());
    }

    if is_generic_type_string(&inferred_signature.ret_type)
        || matches!(
            parse_type_like_spec(&inferred_signature.ret_type, ptr_bits),
            Some(CTypeLike::Int {
                bits,
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
            }) if bits == ptr_bits
        )
    {
        inferred_signature.ret_type = render_signature_type(&ret_ty, ptr_bits);
    }
}

fn build_type_writeback_analysis_inner(
    mut input: TypeWritebackAnalysisInput<'_>,
    semantic_inputs: Option<TypeWritebackSemanticInputs<'_>>,
) -> TypeWritebackAnalysis {
    if input.parsed_context.stack_slots.is_empty()
        && !input.parsed_context.external_stack_vars.is_empty()
    {
        input.parsed_context.stack_slots =
            stack_slots_from_legacy_external_stack_vars(&input.parsed_context.external_stack_vars);
    }

    let mut merged_signature = merge_local_signature_into_merged_signature(
        input.parsed_context.merged_signature.clone(),
        inferred_signature_to_spec(&input.inferred_signature, input.ptr_bits),
    );
    canonicalize_param_home_stack_slots(
        merged_signature.as_ref(),
        &input.parsed_context.register_params,
        &mut input.parsed_context.stack_slots,
        input.ssa_blocks,
        input.ptr_bits,
    );
    apply_main_signature_override(input.function_name, &mut merged_signature);
    merged_signature = merge_recovered_arg_types_into_signature(
        merged_signature,
        input.recovered_vars,
        input.ptr_bits,
        input.function_name,
    );
    apply_interproc_summary_to_signature(
        &mut merged_signature,
        &mut input.inferred_signature,
        input.interproc_summary_set.as_ref(),
        input.ptr_bits,
    );

    let mut diagnostics = input.diagnostics;
    diagnostics.solver_warnings = input.parsed_context.diagnostics.clone();

    let external_structs = collect_external_struct_candidates_from_db(
        &input.parsed_context.external_type_db,
        input.ptr_bits,
    );
    let mut local_structs = input.local_structs;
    if let Some(semantic) = semantic_inputs.as_ref() {
        augment_local_struct_artifacts_with_local_field_accesses(
            &mut local_structs,
            semantic.local_field_accesses,
            input.ptr_bits,
        );
        augment_local_struct_artifacts_with_symbolic_facts(
            &mut local_structs,
            semantic.symbolic_facts,
            input.ptr_bits,
        );
    }
    align_local_structs_with_external(
        &mut local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &local_structs.slot_field_profiles,
        &external_structs,
    );
    prefer_stronger_local_struct_overrides(
        &local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &local_structs.slot_field_profiles,
    );
    prune_conflicting_local_struct_overrides(
        &merged_signature,
        &mut local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &mut local_structs.slot_field_profiles,
        input.ptr_bits,
    );

    let struct_decls = dedup_struct_decls(
        external_structs
            .into_iter()
            .chain(local_structs.struct_decls)
            .collect(),
    );

    let mut type_db = input.parsed_context.external_type_db.clone();
    merge_local_structs_into_type_db(&mut type_db, &struct_decls);
    let merged_signature = merge_slot_type_overrides_into_signature(
        merged_signature,
        &local_structs.slot_type_overrides,
        input.ptr_bits,
    );
    let current_context_maps = signature_context_maps(merged_signature.as_ref(), input.ptr_bits);
    apply_signature_context_overrides(
        &mut input.inferred_signature,
        merged_signature.as_ref(),
        input.ptr_bits,
    );
    let existing_types =
        parse_existing_var_types_from_specs(&input.parsed_context.stack_slots, input.ptr_bits);
    let is_main_signature = is_c_main_function(input.function_name);
    let var_type_ctx = VarTypeCandidateContext {
        current_context_maps: &current_context_maps,
        merged_signature: merged_signature.as_ref(),
        slot_type_overrides: &local_structs.slot_type_overrides,
        stack_slots: &input.parsed_context.stack_slots,
        existing_types: &existing_types,
        ptr_bits: input.ptr_bits,
        is_main_signature,
    };
    let var_type_candidates =
        build_var_type_candidates(input.recovered_vars, &var_type_ctx, &mut diagnostics);
    let var_rename_candidates = build_var_rename_candidates(
        input.recovered_vars,
        &current_context_maps.param_names,
        &input.parsed_context.stack_slots,
    );
    let visible_bindings = build_visible_bindings(
        merged_signature.as_ref(),
        &input.parsed_context.register_params,
        &input.parsed_context.stack_slots,
        input.recovered_vars,
        &var_type_candidates,
        &var_rename_candidates,
        input.ptr_bits,
    );
    let mut type_facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
        merged_signature: merged_signature.clone(),
        known_function_signatures: input.parsed_context.known_function_signatures.clone(),
        register_params: input.parsed_context.register_params.clone(),
        stack_slots: input.parsed_context.stack_slots.clone(),
        visible_bindings,
        callee_facts: input
            .interproc_summary_set
            .as_ref()
            .map(|summary_set| {
                summary_set
                    .summaries
                    .iter()
                    .filter(|(id, _)| Some(**id) != summary_set.root)
                    .map(|(id, summary)| (id.0, summary_to_callee_fact(summary)))
                    .collect()
            })
            .unwrap_or_default(),
        external_stack_vars: if input.parsed_context.stack_slots.is_empty() {
            input.parsed_context.external_stack_vars.clone()
        } else {
            HashMap::new()
        },
        external_type_db: type_db,
        slot_type_overrides: local_structs.slot_type_overrides.clone(),
        slot_field_profiles: local_structs.slot_field_profiles.clone(),
        symbolic_facts: semantic_inputs
            .as_ref()
            .map(|semantic| semantic.symbolic_facts.clone())
            .unwrap_or_default(),
        local_field_accesses: semantic_inputs
            .as_ref()
            .map(|semantic| semantic.local_field_accesses.to_vec())
            .unwrap_or_default(),
        interproc_diagnostics: input
            .interproc_summary_set
            .as_ref()
            .map(|summary_set| InterprocFactDiagnostics {
                iterations: summary_set.diagnostics.iterations,
                max_iterations: summary_set.diagnostics.max_iterations,
                converged: summary_set.diagnostics.converged,
                scope_size: summary_set.diagnostics.scope_size,
                scc_count: summary_set.diagnostics.scc_count,
                max_scc_size: summary_set.diagnostics.max_scc_size,
            })
            .unwrap_or_default(),
        diagnostics: diagnostics.solver_warnings.clone(),
    })
    .build();
    if let Some(semantic) = semantic_inputs.as_ref()
        && semantic.symbolic_facts.diagnostics.branches_pruned > 0
    {
        type_facts.diagnostics.push(format!(
            "symbolic pruned {} branch arm(s)",
            semantic.symbolic_facts.diagnostics.branches_pruned
        ));
    }
    let global_type_links = score_global_type_links(
        input.ssa_blocks,
        &struct_decls,
        &var_type_candidates,
        input.ptr_bits,
    );

    let plan = TypeWritebackPlan {
        signature: input.inferred_signature.clone(),
        var_type_candidates,
        var_rename_candidates,
        struct_decls: struct_decls.clone(),
        global_type_links,
        diagnostics: diagnostics.clone(),
    };

    TypeWritebackAnalysis {
        signature: input.inferred_signature,
        type_facts,
        plan,
    }
}

pub fn build_type_writeback_analysis(
    input: TypeWritebackAnalysisInput<'_>,
) -> TypeWritebackAnalysis {
    build_type_writeback_analysis_inner(input, None)
}

pub fn build_type_writeback_analysis_with_semantics(
    input: TypeWritebackAnalysisInput<'_>,
    semantic_inputs: TypeWritebackSemanticInputs<'_>,
) -> TypeWritebackAnalysis {
    build_type_writeback_analysis_inner(input, Some(semantic_inputs))
}

fn symbolic_semantic_mode_label(mode: crate::facts::SymbolicSemanticMode) -> &'static str {
    match mode {
        crate::facts::SymbolicSemanticMode::Raw => "raw",
        crate::facts::SymbolicSemanticMode::Compiled => "compiled",
        crate::facts::SymbolicSemanticMode::IslandCompiled => "island_compiled",
        crate::facts::SymbolicSemanticMode::Residual => "residual",
        crate::facts::SymbolicSemanticMode::VmSummary => "vm_summary",
    }
}

fn symbolic_slice_class_label(
    slice_class: crate::facts::SymbolicSemanticSliceClass,
) -> &'static str {
    match slice_class {
        crate::facts::SymbolicSemanticSliceClass::Wrapper => "wrapper",
        crate::facts::SymbolicSemanticSliceClass::Worker => "worker",
        crate::facts::SymbolicSemanticSliceClass::RecursiveGroup => "recursive_group",
        crate::facts::SymbolicSemanticSliceClass::InterpreterSwitch => "interpreter_switch",
        crate::facts::SymbolicSemanticSliceClass::InterpreterIndirect => "interpreter_indirect",
        crate::facts::SymbolicSemanticSliceClass::GenericLarge => "generic_large",
    }
}

fn symbolic_residual_reason_label(
    reason: crate::facts::SymbolicSemanticResidualReason,
) -> &'static str {
    match reason {
        crate::facts::SymbolicSemanticResidualReason::MissingArch => "missing_arch",
        crate::facts::SymbolicSemanticResidualReason::LargeCfg => "large_cfg",
        crate::facts::SymbolicSemanticResidualReason::SummaryBudgetExhausted => {
            "summary_budget_exhausted"
        }
        crate::facts::SymbolicSemanticResidualReason::SccBudgetExhausted => "scc_budget_exhausted",
        crate::facts::SymbolicSemanticResidualReason::InterpreterRequiresStepSummary => {
            "interpreter_requires_step_summary"
        }
    }
}

fn semantic_fallback_warning(symbolic_facts: &SymbolicSemanticFacts) -> String {
    let slice_class = symbolic_facts
        .slice_class()
        .map(symbolic_slice_class_label)
        .unwrap_or("unknown");
    let mode = symbolic_facts
        .semantic_mode()
        .map(symbolic_semantic_mode_label)
        .unwrap_or("unknown");
    let mut warning = format!("semantic fallback: {slice_class} slice in {mode} mode");
    if !symbolic_facts.diagnostics.residual_reasons.is_empty() {
        warning.push_str(" (");
        warning.push_str(
            &symbolic_facts
                .diagnostics
                .residual_reasons
                .iter()
                .map(|reason| symbolic_residual_reason_label(*reason))
                .collect::<Vec<_>>()
                .join(", "),
        );
        warning.push(')');
    }
    if !symbolic_facts.branch_facts.is_empty()
        || !symbolic_facts.worker_islands.is_empty()
        || !symbolic_facts.control_islands.is_empty()
        || !symbolic_facts.memory_islands.is_empty()
    {
        warning.push_str(&format!(
            "; branch_facts={}, worker_islands={}, control_islands={}, memory_islands={}, actionable_conditions={}, exact_conditions={}",
            symbolic_facts.branch_facts.len(),
            symbolic_facts.worker_islands.len(),
            symbolic_facts.control_islands.len(),
            symbolic_facts.memory_islands.len(),
            symbolic_facts.actionable_compiled_condition_count(),
            symbolic_facts.exact_compiled_condition_count(),
        ));
    }
    warning
}

pub fn build_semantic_type_fallback_plan(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    symbolic_facts: &SymbolicSemanticFacts,
) -> TypeWritebackPlan {
    let mut warnings = vec![semantic_fallback_warning(symbolic_facts)];
    if !symbolic_facts.type_ready() {
        warnings.push("type analysis not ready from semantic capability".to_string());
    }
    let mut local_structs = LocalStructArtifacts::default();
    augment_local_struct_artifacts_with_symbolic_facts(
        &mut local_structs,
        symbolic_facts,
        ptr_bits,
    );
    let mut signature = InferredSignature {
        function_name: function_name.to_string(),
        signature: format!("void {}(void)", function_name),
        ret_type: "void".to_string(),
        params: Vec::new(),
        callconv: "unknown".to_string(),
        arch: arch_name.to_string(),
        confidence: 0,
        callconv_confidence: 0,
    };
    if let Some(merged_signature) = merge_slot_type_overrides_into_signature(
        inferred_signature_to_spec(&signature, ptr_bits),
        &local_structs.slot_type_overrides,
        ptr_bits,
    ) {
        apply_signature_context_overrides(&mut signature, Some(&merged_signature), ptr_bits);
    }
    if !local_structs.struct_decls.is_empty() {
        warnings.push(format!(
            "semantic worker islands projected {} struct candidate(s)",
            local_structs.struct_decls.len()
        ));
    }

    TypeWritebackPlan {
        signature,
        var_type_candidates: Vec::new(),
        var_rename_candidates: Vec::new(),
        struct_decls: local_structs.struct_decls,
        global_type_links: Vec::new(),
        diagnostics: TypeWritebackDiagnostics {
            conflicts: Vec::new(),
            warnings,
            solver_warnings: Vec::new(),
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LocalAddrExpr {
    slot: usize,
    offset: i64,
    confidence: u8,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct InferredLocalFieldEvidence {
    reads: u32,
    writes: u32,
    widths: BTreeMap<u32, u32>,
    type_votes: BTreeMap<String, u32>,
}

type LocalFieldEvidenceMap = HashMap<usize, BTreeMap<u64, InferredLocalFieldEvidence>>;

fn collect_pointer_arg_slot_map(arch_name: Option<&str>, ptr_bits: u32) -> HashMap<String, usize> {
    let (arg_regs, _, _) = recover_vars_arch_profile(arch_name);
    let arch_name = arch_name.unwrap_or_default().to_ascii_lowercase();
    let is_arm64 = arch_name.contains("aarch64") || arch_name.contains("arm64");
    let is_x86_64 = arch_name.contains("x86-64")
        || arch_name.contains("x86_64")
        || arch_name.contains("amd64")
        || arch_name.contains("x64");
    let is_riscv64 = arch_name.contains("riscv64") || arch_name.contains("rv64");

    let mut out = HashMap::new();
    for (idx, (canonical, aliases)) in arg_regs.iter().enumerate() {
        let include_alias = |alias: &str| -> bool {
            if ptr_bits <= 32 {
                return true;
            }
            let alias = alias.to_ascii_lowercase();
            if is_arm64 {
                return alias.starts_with('x');
            }
            if is_x86_64 {
                return alias.starts_with('r');
            }
            if is_riscv64 {
                return alias.starts_with('x') || alias.starts_with('a');
            }
            alias == (*canonical).to_ascii_lowercase()
        };

        if include_alias(canonical) {
            out.insert((*canonical).to_string(), idx);
        }
        for alias in *aliases {
            if include_alias(alias) {
                out.insert((*alias).to_string(), idx);
            }
        }
    }
    out
}

fn parse_ssa_const_offset(name: &str, ptr_bits: u32) -> Option<i64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);

    let raw = if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).ok()?
    } else if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        dec.parse::<u64>().ok()?
    } else {
        u64::from_str_radix(val_str, 16).ok()?
    };
    Some(signed_offset_from_const(raw, ptr_bits))
}

pub fn infer_local_struct_artifacts_from_ssa(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
    ptr_bits: u32,
    diagnostics: &mut TypeWritebackDiagnostics,
) -> LocalStructArtifacts {
    let pointer_arg_slot_map = collect_pointer_arg_slot_map(arch_name, ptr_bits);
    let (_, stack_bases, frame_bases) = recover_vars_arch_profile(arch_name);
    let mut addr_exprs: HashMap<String, LocalAddrExpr> = HashMap::new();
    let mut stack_addr_offsets: HashMap<String, i64> = HashMap::new();
    let mut stack_slot_values: HashMap<(u64, i64), LocalAddrExpr> = HashMap::new();
    let mut slot_field_evidence: LocalFieldEvidenceMap = HashMap::new();
    let offset_bound = 0x4000i64;
    let block_ops: HashMap<u64, HashMap<String, SSAOp>> = ssa_blocks
        .iter()
        .map(|block| {
            let ops = block
                .ops
                .iter()
                .filter_map(|op| {
                    op.dst()
                        .map(|dst| (ssa_var_block_key(block.addr, dst), op.clone()))
                })
                .collect::<HashMap<_, _>>();
            (block.addr, ops)
        })
        .collect();

    fn is_scaled_index_like(
        block_addr: u64,
        var: &SSAVar,
        ops_by_block: &HashMap<u64, HashMap<String, SSAOp>>,
        addr_exprs: &HashMap<String, LocalAddrExpr>,
        depth: u32,
    ) -> bool {
        if depth > 8 || var.is_const() {
            return false;
        }
        let key = ssa_var_block_key(block_addr, var);
        if addr_exprs.contains_key(&key) {
            return false;
        }
        let Some(op) = ops_by_block.get(&block_addr).and_then(|ops| ops.get(&key)) else {
            return true;
        };
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                is_scaled_index_like(block_addr, src, ops_by_block, addr_exprs, depth + 1)
            }
            SSAOp::IntMult { a, b, .. } => {
                (parse_ssa_const_offset(&a.name, 64).is_some()
                    && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1))
                    || (parse_ssa_const_offset(&b.name, 64).is_some()
                        && is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1))
            }
            SSAOp::IntLeft { a, b, .. } => {
                parse_ssa_const_offset(&b.name, 64).is_some()
                    && is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1)
            }
            SSAOp::IntSub { a, b, .. } => {
                parse_ssa_const_offset(&a.name, 64) == Some(0)
                    && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1)
            }
            SSAOp::Load { .. } | SSAOp::Phi { .. } => true,
            _ => false,
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            op.for_each_source(&mut |src: &SSAVar| {
                if src.version != 0 {
                    return;
                }
                let key = src.name.to_ascii_lowercase();
                if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                    addr_exprs
                        .entry(ssa_var_block_key(block.addr, src))
                        .or_insert(LocalAddrExpr {
                            slot,
                            offset: 0,
                            confidence: 92,
                        });
                }
            });
        }
    }

    let is_stack_base = |name: &str| stack_bases.contains(&name) || frame_bases.contains(&name);

    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                let addr_of = |var: &SSAVar, map: &HashMap<String, LocalAddrExpr>| {
                    if var.version == 0 {
                        let key = var.name.to_ascii_lowercase();
                        if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                            return Some(LocalAddrExpr {
                                slot,
                                offset: 0,
                                confidence: 92,
                            });
                        }
                    }
                    map.get(&ssa_var_block_key(block.addr, var)).copied()
                };
                let stack_slot_of = |var: &SSAVar, stack_map: &HashMap<String, i64>| {
                    stack_map.get(&ssa_var_block_key(block.addr, var)).copied()
                };
                let set_expr =
                    |dst: &SSAVar,
                     expr: LocalAddrExpr,
                     map: &mut HashMap<String, LocalAddrExpr>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev.confidence >= expr.confidence => false,
                            _ => {
                                map.insert(key, expr);
                                true
                            }
                        }
                    };
                let set_stack_slot = |dst: &SSAVar, offset: i64, map: &mut HashMap<String, i64>| {
                    let key = ssa_var_block_key(block.addr, dst);
                    match map.get(&key).copied() {
                        Some(prev) if prev == offset => false,
                        _ => {
                            map.insert(key, offset);
                            true
                        }
                    }
                };

                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src } => {
                        if let Some(mut expr) = addr_of(src, &addr_exprs) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                        if let Some(offset) = stack_slot_of(src, &stack_addr_offsets) {
                            changed |= set_stack_slot(dst, offset, &mut stack_addr_offsets);
                        }
                    }
                    SSAOp::Phi { dst, sources } => {
                        let mut selected = None;
                        let mut selected_slot = None;
                        for src in sources {
                            let Some(expr) = addr_of(src, &addr_exprs) else {
                                selected = None;
                                break;
                            };
                            selected = match selected {
                                None => Some(expr),
                                Some(prev)
                                    if prev.slot == expr.slot && prev.offset == expr.offset =>
                                {
                                    Some(LocalAddrExpr {
                                        slot: prev.slot,
                                        offset: prev.offset,
                                        confidence: prev.confidence.max(expr.confidence),
                                    })
                                }
                                _ => None,
                            };
                            let Some(slot) = stack_slot_of(src, &stack_addr_offsets) else {
                                selected_slot = None;
                                break;
                            };
                            selected_slot = match selected_slot {
                                None => Some(slot),
                                Some(prev) if prev == slot => Some(prev),
                                _ => None,
                            };
                            if selected.is_none() {
                                break;
                            }
                        }
                        if let Some(mut expr) = selected {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                        if let Some(slot) = selected_slot {
                            changed |= set_stack_slot(dst, slot, &mut stack_addr_offsets);
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        if let Some(off) = parse_ssa_const_offset(&b.name, ptr_bits) {
                            let a_lower = a.name.to_ascii_lowercase();
                            if is_stack_base(a_lower.as_str()) {
                                changed |= set_stack_slot(dst, off, &mut stack_addr_offsets);
                            }
                        }
                        if let Some(off) = parse_ssa_const_offset(&a.name, ptr_bits) {
                            let b_lower = b.name.to_ascii_lowercase();
                            if is_stack_base(b_lower.as_str()) {
                                changed |= set_stack_slot(dst, off, &mut stack_addr_offsets);
                            }
                        }
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                        {
                            let off = base.offset.saturating_add(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    LocalAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(a, &addr_exprs)
                            && is_scaled_index_like(block.addr, b, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                LocalAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&a.name, ptr_bits)
                        {
                            let off = base.offset.saturating_add(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    LocalAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && is_scaled_index_like(block.addr, a, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                LocalAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        }
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        if let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits) {
                            let a_lower = a.name.to_ascii_lowercase();
                            if is_stack_base(a_lower.as_str()) {
                                changed |= set_stack_slot(
                                    dst,
                                    delta.saturating_neg(),
                                    &mut stack_addr_offsets,
                                );
                            }
                        }
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                        {
                            let off = base.offset.saturating_sub(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    LocalAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(a, &addr_exprs)
                            && is_scaled_index_like(block.addr, b, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                LocalAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        }
                    }
                    SSAOp::Store { addr, val, .. } => {
                        if let Some(offset) = stack_slot_of(addr, &stack_addr_offsets)
                            && let Some(mut expr) = addr_of(val, &addr_exprs)
                        {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            let key = (block.addr, offset);
                            match stack_slot_values.get(&key).copied() {
                                Some(prev) if prev.confidence >= expr.confidence => {}
                                _ => {
                                    stack_slot_values.insert(key, expr);
                                    changed = true;
                                }
                            }
                        }
                    }
                    SSAOp::Load { dst, addr, .. } => {
                        if let Some(offset) = stack_slot_of(addr, &stack_addr_offsets)
                            && let Some(mut expr) =
                                stack_slot_values.get(&(block.addr, offset)).copied()
                        {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            let resolve_addr = |addr: &SSAVar| -> Option<LocalAddrExpr> {
                if addr.version == 0 {
                    let key = addr.name.to_ascii_lowercase();
                    if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                        return Some(LocalAddrExpr {
                            slot,
                            offset: 0,
                            confidence: 92,
                        });
                    }
                }
                addr_exprs
                    .get(&ssa_var_block_key(block.addr, addr))
                    .copied()
            };
            match op {
                SSAOp::Load { dst, addr, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = slot_field_evidence
                            .entry(expr.slot)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.reads = entry.reads.saturating_add(1);
                        *entry.widths.entry(dst.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(dst.size)).or_insert(0) += 1;
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = slot_field_evidence
                            .entry(expr.slot)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.writes = entry.writes.saturating_add(1);
                        *entry.widths.entry(val.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(val.size)).or_insert(0) += 1;
                    }
                }
                _ => {}
            }
        }
    }

    let mut struct_decls = Vec::new();
    let mut slot_type_overrides = HashMap::new();
    let mut slot_field_profiles = HashMap::new();
    let mut slots: Vec<usize> = slot_field_evidence.keys().copied().collect();
    slots.sort_unstable();

    for slot in slots {
        let Some(fields_map) = slot_field_evidence.get(&slot) else {
            continue;
        };
        if fields_map.is_empty() {
            continue;
        }
        let mut shape = String::new();
        let mut fields = Vec::new();
        let mut normalized_fields = BTreeMap::new();
        let mut confidence_acc = 0u32;
        for (offset, evidence) in fields_map {
            let total_votes: u32 = evidence.type_votes.values().copied().sum();
            let Some((field_type, field_votes)) = evidence
                .type_votes
                .iter()
                .max_by_key(|(_, count)| **count)
                .map(|(ty, count)| (ty.clone(), *count))
            else {
                continue;
            };
            if evidence.type_votes.len() > 1 {
                diagnostics.conflicts.push(format!(
                    "slot {slot} field +0x{offset:x} conflicting type votes {:?}",
                    evidence.type_votes
                ));
            }
            let strength = ((field_votes.saturating_mul(100)) / total_votes.max(1)) as u8;
            let rw_bonus = if evidence.reads > 0 && evidence.writes > 0 {
                10
            } else {
                0
            };
            let field_conf = 70u8.saturating_add(strength / 3).saturating_add(rw_bonus);
            confidence_acc = confidence_acc.saturating_add(field_conf as u32);
            shape.push_str(&format!("{offset:x}:{field_type};"));
            normalized_fields.insert(*offset, field_type.clone());
            fields.push(StructFieldCandidate {
                name: format!("f_{offset:x}"),
                offset: *offset,
                field_type,
                confidence: field_conf,
            });
        }
        if fields.is_empty() {
            continue;
        }
        let avg_conf = (confidence_acc / fields.len() as u32).clamp(1, 100) as u8;
        let allow_single_field = fields.len() == 1 && avg_conf >= 94;
        if fields.len() < 2 && !allow_single_field {
            continue;
        }
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hasher);
        let struct_name = format!("sla_struct_{:016x}", hasher.finish());
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        struct_decls.push(StructDeclCandidate {
            name: struct_name.clone(),
            decl,
            confidence: avg_conf.max(84),
            source: StructDeclSource::LocalInferred,
            fields,
        });
        slot_field_profiles.insert(slot, normalized_fields);
        slot_type_overrides.insert(slot, format!("struct {struct_name} *"));
    }

    LocalStructArtifacts {
        struct_decls,
        slot_type_overrides,
        slot_field_profiles,
    }
}

pub fn augment_local_struct_artifacts_with_symbolic_facts(
    local_structs: &mut LocalStructArtifacts,
    symbolic_facts: &SymbolicSemanticFacts,
    ptr_bits: u32,
) {
    let mut projected_profiles = BTreeMap::<usize, BTreeMap<u64, String>>::new();
    for island in &symbolic_facts.worker_islands {
        if !(island.confidence.is_reliable() && island.evidence.is_reliable()) {
            continue;
        }
        for term in &island.memory_terms {
            let Some((slot, offset, field_type)) = symbolic_memory_term_slot_field(term, ptr_bits)
            else {
                continue;
            };
            projected_profiles
                .entry(slot)
                .or_default()
                .entry(offset)
                .or_insert(field_type);
        }
    }
    if projected_profiles.is_empty() {
        for island in &symbolic_facts.memory_islands {
            if !(island.confidence.is_reliable() && island.evidence.is_reliable()) {
                continue;
            }
            for term in &island.terms {
                let Some((slot, offset, field_type)) =
                    symbolic_memory_term_slot_field(term, ptr_bits)
                else {
                    continue;
                };
                projected_profiles
                    .entry(slot)
                    .or_default()
                    .entry(offset)
                    .or_insert(field_type);
            }
        }
    }
    if projected_profiles.is_empty() {
        for compiled in symbolic_facts
            .branch_facts
            .iter()
            .filter_map(|fact| fact.actionable_compiled_condition())
            .chain(
                symbolic_facts
                    .worker_islands
                    .iter()
                    .filter_map(|island| island.actionable_compiled_condition()),
            )
            .chain(
                symbolic_facts
                    .control_islands
                    .iter()
                    .filter_map(|island| island.actionable_compiled_condition()),
            )
        {
            if !(compiled.confidence.is_reliable() && compiled.evidence.is_reliable()) {
                continue;
            }
            for term in &compiled.memory_terms {
                let Some((slot, offset, field_type)) =
                    symbolic_memory_term_slot_field(term, ptr_bits)
                else {
                    continue;
                };
                projected_profiles
                    .entry(slot)
                    .or_default()
                    .entry(offset)
                    .or_insert(field_type);
            }
        }
    }

    for (slot, projected) in projected_profiles {
        let profile = local_structs.slot_field_profiles.entry(slot).or_default();
        for (offset, field_type) in projected {
            profile.entry(offset).or_insert(field_type);
        }
        if profile.is_empty() || local_structs.slot_type_overrides.contains_key(&slot) {
            continue;
        }
        let struct_name = format!("sla_struct_symbolic_arg{}", slot + 1);
        let fields = profile
            .iter()
            .map(|(offset, field_type)| StructFieldCandidate {
                name: format!("f_{offset:x}"),
                offset: *offset,
                field_type: field_type.clone(),
                confidence: 84,
            })
            .collect::<Vec<_>>();
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        if !local_structs
            .struct_decls
            .iter()
            .any(|candidate| candidate.name.eq_ignore_ascii_case(&struct_name))
        {
            local_structs.struct_decls.push(StructDeclCandidate {
                name: struct_name.clone(),
                decl,
                confidence: 84,
                source: StructDeclSource::LocalInferred,
                fields,
            });
        }
        local_structs
            .slot_type_overrides
            .insert(slot, format!("struct {struct_name} *"));
    }
}

fn augment_local_struct_artifacts_with_local_field_accesses(
    local_structs: &mut LocalStructArtifacts,
    local_field_accesses: &[LocalFieldAccessFact],
    ptr_bits: u32,
) {
    let mut projected_profiles = BTreeMap::<usize, BTreeMap<u64, String>>::new();
    for access in local_field_accesses {
        let field_type = access
            .field_type
            .clone()
            .unwrap_or_else(|| access.field_name.clone());
        projected_profiles
            .entry(access.slot)
            .or_default()
            .entry(access.field_offset)
            .or_insert(field_type);
    }

    for (slot, projected) in projected_profiles {
        let profile = local_structs.slot_field_profiles.entry(slot).or_default();
        for (offset, field_type) in projected {
            profile.entry(offset).or_insert(field_type);
        }
        if profile.is_empty() || local_structs.slot_type_overrides.contains_key(&slot) {
            continue;
        }

        let allow_single_field = profile.len() == 1;
        if profile.len() < 2 && !allow_single_field {
            continue;
        }
        let mut shape = String::new();
        let fields = profile
            .iter()
            .map(|(offset, field_type)| {
                shape.push_str(&format!("{offset:x}:{field_type};"));
                StructFieldCandidate {
                    name: format!("f_{offset:x}"),
                    offset: *offset,
                    field_type: field_type.clone(),
                    confidence: 90,
                }
            })
            .collect::<Vec<_>>();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hasher);
        let struct_name = format!("sla_struct_{:016x}", hasher.finish());
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        if !local_structs
            .struct_decls
            .iter()
            .any(|candidate| candidate.name.eq_ignore_ascii_case(&struct_name))
        {
            local_structs.struct_decls.push(StructDeclCandidate {
                name: struct_name.clone(),
                decl,
                confidence: 90,
                source: StructDeclSource::LocalInferred,
                fields,
            });
        }
        local_structs
            .slot_type_overrides
            .insert(slot, format!("struct {struct_name} *"));
    }
}

fn symbolic_memory_term_slot_field(
    term: &SymbolicMemoryCondition,
    _ptr_bits: u32,
) -> Option<(usize, u64, String)> {
    if !(term.confidence.is_reliable() && term.evidence.is_reliable()) {
        return None;
    }
    let slot = match term.region {
        SymbolicMemoryRegion::Argument { index } => index,
        SymbolicMemoryRegion::Region(_) => return None,
    };
    if !term.exact_offset && term.offset_lo != term.offset_hi {
        return None;
    }
    if term.offset_lo < 0 || term.offset_hi < 0 || term.offset_lo != term.offset_hi {
        return None;
    }
    Some((slot, term.offset_lo as u64, size_to_type(term.size)))
}

fn canonicalize_param_home_stack_slots(
    merged_signature: Option<&FunctionSignatureSpec>,
    register_params: &[crate::context::ExternalRegisterParamSpec],
    stack_slots: &mut BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    ssa_blocks: &[SSABlock],
    ptr_bits: u32,
) {
    if register_params.is_empty() || stack_slots.is_empty() || ssa_blocks.is_empty() {
        return;
    }

    let trivial_value_sources = collect_trivial_value_sources(ssa_blocks);
    let mut slot_addr_by_var = HashMap::<String, StackSlotKey>::new();
    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } => {
                    if let Some(slot_key) = stack_slot_key_from_add_sub(a, b, false, ptr_bits) {
                        slot_addr_by_var.insert(dst.display_name(), slot_key);
                    }
                }
                SSAOp::IntSub { dst, a, b } => {
                    if let Some(slot_key) = stack_slot_key_from_add_sub(a, b, true, ptr_bits) {
                        slot_addr_by_var.insert(dst.display_name(), slot_key);
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    let Some(slot_key) = slot_addr_by_var.get(&addr.display_name()).cloned() else {
                        continue;
                    };
                    let rooted_val = resolve_trivial_value_root(&trivial_value_sources, val);
                    let Some((param_index, param_reg)) =
                        register_params.iter().enumerate().find_map(|(idx, param)| {
                            register_family_matches(&param.reg, &rooted_val.name)
                                .then_some((idx, param.reg.clone()))
                        })
                    else {
                        continue;
                    };
                    if rooted_val.version != 0 {
                        continue;
                    }
                    let Some(slot) = stack_slots.get_mut(&slot_key) else {
                        continue;
                    };
                    if !matches!(
                        slot.role,
                        ExternalStackSlotRole::Unknown | ExternalStackSlotRole::Local
                    ) {
                        continue;
                    }
                    let param_name = merged_signature
                        .and_then(|sig| sig.params.get(param_index))
                        .map(|param| param.name.clone())
                        .filter(|name| !name.is_empty())
                        .unwrap_or_else(|| format!("arg{}", param_index + 1));
                    slot.role = ExternalStackSlotRole::ParamHome;
                    slot.param_index = Some(param_index);
                    slot.param_name = Some(param_name.clone());
                    slot.source_reg = Some(param_reg);
                    if is_low_quality_stack_name(&slot.name) || slot.name.is_empty() {
                        slot.name = format!("{param_name}_home");
                    }
                }
                _ => {}
            }
        }
    }
}

fn collect_trivial_value_sources(ssa_blocks: &[SSABlock]) -> HashMap<SSAVar, SSAVar> {
    let mut trivial_value_sources = HashMap::new();
    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src } => {
                    trivial_value_sources.insert(dst.clone(), src.clone());
                }
                SSAOp::Subpiece { dst, src, offset } if *offset == 0 => {
                    trivial_value_sources.insert(dst.clone(), src.clone());
                }
                _ => {}
            }
        }
    }
    trivial_value_sources
}

fn resolve_trivial_value_root(
    trivial_value_sources: &HashMap<SSAVar, SSAVar>,
    value: &SSAVar,
) -> SSAVar {
    let mut current = value.clone();
    let mut seen = HashSet::new();
    while seen.insert(current.clone()) {
        let Some(next) = trivial_value_sources.get(&current) else {
            break;
        };
        current = next.clone();
    }
    current
}

fn stack_slot_key_from_add_sub(
    a: &SSAVar,
    b: &SSAVar,
    is_sub: bool,
    ptr_bits: u32,
) -> Option<StackSlotKey> {
    let base = stack_base_from_var(a)?;
    let raw = parse_const_value(&b.name)?;
    let offset = signed_offset_from_const(raw, ptr_bits);
    Some(StackSlotKey {
        base,
        offset: if is_sub { -offset } else { offset },
    })
}

fn stack_base_from_var(var: &SSAVar) -> Option<ExternalStackBase> {
    let lower = var.name.to_ascii_lowercase();
    match lower.as_str() {
        "rbp" | "ebp" | "bp" | "fp" => Some(ExternalStackBase::FramePointer),
        "rsp" | "esp" | "sp" => Some(ExternalStackBase::StackPointer),
        _ => None,
    }
}

fn register_family_matches(expected: &str, actual: &str) -> bool {
    let expected = expected.to_ascii_lowercase();
    let actual = actual.to_ascii_lowercase();
    if expected == actual {
        return true;
    }

    fn family(name: &str) -> Option<&str> {
        match name {
            "rax" | "eax" | "ax" | "al" | "ah" => Some("ax"),
            "rbx" | "ebx" | "bx" | "bl" | "bh" => Some("bx"),
            "rcx" | "ecx" | "cx" | "cl" | "ch" => Some("cx"),
            "rdx" | "edx" | "dx" | "dl" | "dh" => Some("dx"),
            "rsi" | "esi" | "si" | "sil" => Some("si"),
            "rdi" | "edi" | "di" | "dil" => Some("di"),
            "rbp" | "ebp" | "bp" | "bpl" => Some("bp"),
            "rsp" | "esp" | "sp" | "spl" => Some("sp"),
            "r8" | "r8d" | "r8w" | "r8b" => Some("8"),
            "r9" | "r9d" | "r9w" | "r9b" => Some("9"),
            "r10" | "r10d" | "r10w" | "r10b" => Some("10"),
            "r11" | "r11d" | "r11w" | "r11b" => Some("11"),
            "r12" | "r12d" | "r12w" | "r12b" => Some("12"),
            "r13" | "r13d" | "r13w" | "r13b" => Some("13"),
            "r14" | "r14d" | "r14w" | "r14b" => Some("14"),
            "r15" | "r15d" | "r15w" | "r15b" => Some("15"),
            _ => None,
        }
    }

    family(&expected) == family(&actual)
}

fn inferred_signature_to_spec(
    signature: &InferredSignature,
    ptr_bits: u32,
) -> Option<FunctionSignatureSpec> {
    let ret_type = parse_type_like_spec(&signature.ret_type, ptr_bits);
    let params = signature
        .params
        .iter()
        .map(|param| FunctionParamSpec {
            name: param.name.clone(),
            ty: parse_type_like_spec(&param.param_type, ptr_bits),
        })
        .collect::<Vec<_>>();
    if ret_type.is_none() && params.iter().all(|param| param.ty.is_none()) {
        return None;
    }
    Some(FunctionSignatureSpec { ret_type, params })
}

fn merge_local_signature_into_merged_signature(
    external: Option<FunctionSignatureSpec>,
    local: Option<FunctionSignatureSpec>,
) -> Option<FunctionSignatureSpec> {
    match (external, local) {
        (None, None) => None,
        (Some(signature), None) => Some(signature),
        (None, Some(signature)) => Some(signature),
        (Some(mut external), Some(local)) => {
            let external_param_count_is_authoritative =
                signature_param_count_is_authoritative(&external);
            if local_signature_should_override_external(
                local.ret_type.as_ref(),
                external.ret_type.as_ref(),
            ) {
                external.ret_type = local.ret_type;
            } else if is_generic_signature_type(external.ret_type.as_ref()) {
                external.ret_type = local.ret_type.or(external.ret_type);
            }

            if !external_param_count_is_authoritative && external.params.len() < local.params.len()
            {
                external
                    .params
                    .resize_with(local.params.len(), || FunctionParamSpec {
                        name: String::new(),
                        ty: None,
                    });
            }

            for (idx, local_param) in local.params.into_iter().enumerate() {
                if idx >= external.params.len() {
                    continue;
                }
                let target = &mut external.params[idx];
                if target.name.is_empty() {
                    target.name = format!("arg{}", idx + 1);
                }
                if !is_generic_arg_name(&local_param.name) && is_generic_arg_name(&target.name) {
                    target.name = local_param.name.clone();
                }
                if local_signature_should_override_external(
                    local_param.ty.as_ref(),
                    target.ty.as_ref(),
                ) {
                    target.ty = local_param.ty;
                } else if is_generic_signature_type(target.ty.as_ref()) {
                    target.ty = local_param.ty.or(target.ty.take());
                }
            }

            Some(external)
        }
    }
}

fn local_signature_should_override_external(
    local: Option<&CTypeLike>,
    external: Option<&CTypeLike>,
) -> bool {
    let Some(local) = local else {
        return false;
    };
    match external {
        None => true,
        Some(external) if is_generic_signature_type(Some(external)) => true,
        Some(external) => local_scalar_override_should_apply(local, external),
    }
}

fn local_scalar_override_should_apply(local: &CTypeLike, external: &CTypeLike) -> bool {
    match (local, external) {
        (CTypeLike::Bool, CTypeLike::Bool) => false,
        (
            CTypeLike::Bool,
            CTypeLike::Int {
                bits: external_bits,
                ..
            },
        ) => *external_bits >= 8,
        (
            CTypeLike::Int {
                bits: local_bits,
                signedness: local_signedness,
            },
            CTypeLike::Int {
                bits: external_bits,
                signedness: external_signedness,
            },
        ) => {
            *local_bits < *external_bits
                || (*local_bits == *external_bits
                    && matches!(local_signedness, Signedness::Signed)
                    && !matches!(external_signedness, Signedness::Signed))
        }
        _ => false,
    }
}

fn merge_recovered_arg_types_into_signature(
    mut signature: Option<FunctionSignatureSpec>,
    vars: &[RecoveredVariable],
    ptr_bits: u32,
    function_name: &str,
) -> Option<FunctionSignatureSpec> {
    if is_c_main_function(function_name) {
        return signature;
    }

    let local_arg_types = collect_recovered_arg_types(vars, ptr_bits);
    if local_arg_types.is_empty() {
        return signature;
    }

    let max_slot = local_arg_types.keys().copied().max()?;
    let sig = signature.get_or_insert_with(Default::default);
    let allow_param_count_extension = !signature_param_count_is_authoritative(sig);
    while allow_param_count_extension && sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, local_ty) in local_arg_types {
        if slot >= sig.params.len() {
            continue;
        }
        let param = &mut sig.params[slot];
        if param.name.is_empty() {
            param.name = format!("arg{}", slot + 1);
        }
        if local_signature_should_override_external(Some(&local_ty), param.ty.as_ref())
            || is_generic_signature_type(param.ty.as_ref())
        {
            param.ty = Some(local_ty);
        }
    }

    signature
}

fn collect_recovered_arg_types(
    vars: &[RecoveredVariable],
    ptr_bits: u32,
) -> BTreeMap<usize, CTypeLike> {
    let mut out = BTreeMap::new();
    for var in vars {
        if !var.isarg {
            continue;
        }
        let Some(slot) = var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok())
        else {
            continue;
        };
        let Some(candidate) = parse_type_like_spec(&var.var_type, ptr_bits) else {
            continue;
        };
        if is_generic_signature_type(Some(&candidate)) {
            continue;
        }
        match out.get(&slot) {
            Some(current)
                if !local_signature_should_override_external(Some(&candidate), Some(current)) => {}
            _ => {
                out.insert(slot, candidate);
            }
        }
    }
    out
}

fn stack_base_for_recovered_var_kind(kind: &str) -> Option<ExternalStackBase> {
    match kind {
        "b" => Some(ExternalStackBase::FramePointer),
        "s" => Some(ExternalStackBase::StackPointer),
        _ => None,
    }
}

fn stack_slot_key_for_recovered_var(var: &RecoveredVariable) -> Option<StackSlotKey> {
    Some(StackSlotKey {
        base: stack_base_for_recovered_var_kind(&var.kind)?,
        offset: var.delta,
    })
}

fn slot_spec_for_recovered_var<'a>(
    var: &RecoveredVariable,
    stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackVarSpec>,
) -> Option<&'a ExternalStackVarSpec> {
    if let Some(slot_key) = stack_slot_key_for_recovered_var(var) {
        return stack_slots.get(&slot_key);
    }
    None
}

fn slot_role_is_hidden(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::ParamHome
            | ExternalStackSlotRole::SavedReg
            | ExternalStackSlotRole::SavedFp
    )
}

fn slot_role_allows_external_local_identity(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::Local
            | ExternalStackSlotRole::StackArg
            | ExternalStackSlotRole::Unknown
    )
}

fn visible_binding_kind_for_slot_role(role: ExternalStackSlotRole) -> VisibleBindingKind {
    match role {
        ExternalStackSlotRole::Local => VisibleBindingKind::Local,
        ExternalStackSlotRole::StackArg => VisibleBindingKind::Param,
        ExternalStackSlotRole::ParamHome => VisibleBindingKind::HiddenHome,
        ExternalStackSlotRole::SavedReg | ExternalStackSlotRole::SavedFp => {
            VisibleBindingKind::HiddenSaved
        }
        ExternalStackSlotRole::Unknown => VisibleBindingKind::Unknown,
    }
}

fn visible_binding_key_for_recovered_var(var: &RecoveredVariable) -> Option<VisibleBindingKey> {
    if let Some(slot_key) = stack_slot_key_for_recovered_var(var) {
        return Some(VisibleBindingKey::Stack(slot_key));
    }
    if var.isarg {
        return var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok())
            .map(VisibleBindingKey::Param);
    }
    None
}

fn name_is_low_signal_binding(name: &str) -> bool {
    is_low_quality_stack_name(name) || is_generic_arg_name(name)
}

fn binding_type_is_unknown(ty: Option<&CTypeLike>) -> bool {
    matches!(ty, None | Some(CTypeLike::Unknown))
}

fn merge_visible_binding(existing: &mut VisibleBinding, candidate: VisibleBinding) {
    let VisibleBinding {
        name,
        ty,
        kind,
        stack_slot,
        param_index,
        source_reg,
    } = candidate;
    let existing_low_signal = name_is_low_signal_binding(&existing.name);
    let candidate_low_signal = name_is_low_signal_binding(&name);
    if existing.name.is_empty() || (existing_low_signal && !candidate_low_signal) {
        existing.name = name;
    }

    if binding_type_is_unknown(existing.ty.as_ref()) && !binding_type_is_unknown(ty.as_ref()) {
        existing.ty = ty;
    }

    if matches!(existing.kind, VisibleBindingKind::Unknown)
        || (matches!(existing.kind, VisibleBindingKind::Local)
            && matches!(kind, VisibleBindingKind::StackObject))
    {
        existing.kind = kind;
    }

    if existing.stack_slot.is_none() && stack_slot.is_some() {
        existing.stack_slot = stack_slot;
    }
    if existing.param_index.is_none() && param_index.is_some() {
        existing.param_index = param_index;
    }
    if existing.source_reg.is_none() && source_reg.is_some() {
        existing.source_reg = source_reg;
    }
}

fn build_visible_bindings(
    merged_signature: Option<&FunctionSignatureSpec>,
    register_params: &[crate::context::ExternalRegisterParamSpec],
    stack_slots: &BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    recovered_vars: &[RecoveredVariable],
    var_type_candidates: &[VarTypeCandidate],
    var_rename_candidates: &[VarRenameCandidate],
    ptr_bits: u32,
) -> Vec<VisibleBinding> {
    let mut bindings = BTreeMap::<VisibleBindingKey, VisibleBinding>::new();

    for (idx, param) in merged_signature
        .map(|sig| sig.params.iter().enumerate().collect::<Vec<_>>())
        .unwrap_or_default()
    {
        bindings.insert(
            VisibleBindingKey::Param(idx),
            VisibleBinding {
                name: if is_generic_arg_name(&param.name) {
                    format!("arg{}", idx + 1)
                } else {
                    param.name.clone()
                },
                ty: param.ty.clone(),
                kind: VisibleBindingKind::Param,
                stack_slot: None,
                param_index: Some(idx),
                source_reg: register_params.get(idx).map(|param| param.reg.clone()),
            },
        );
    }

    for (idx, reg_param) in register_params.iter().enumerate() {
        let candidate = VisibleBinding {
            name: if reg_param.name.is_empty() {
                format!("arg{}", idx + 1)
            } else {
                reg_param.name.clone()
            },
            ty: reg_param.ty.clone(),
            kind: VisibleBindingKind::Param,
            stack_slot: None,
            param_index: Some(idx),
            source_reg: Some(reg_param.reg.clone()),
        };
        bindings
            .entry(VisibleBindingKey::Param(idx))
            .and_modify(|existing| merge_visible_binding(existing, candidate.clone()))
            .or_insert(candidate);
    }

    let rename_map = var_rename_candidates
        .iter()
        .map(|candidate| (candidate.name.as_str(), candidate.target_name.clone()))
        .collect::<HashMap<_, _>>();
    let type_map = var_type_candidates
        .iter()
        .filter_map(|candidate| {
            parse_type_like_spec(&candidate.var_type, ptr_bits)
                .map(|ty| (candidate.name.as_str(), ty))
        })
        .collect::<HashMap<_, _>>();

    for (slot_key, slot_spec) in stack_slots {
        let key = slot_spec
            .param_index
            .filter(|_| matches!(slot_spec.role, ExternalStackSlotRole::StackArg))
            .map(VisibleBindingKey::Param)
            .unwrap_or_else(|| VisibleBindingKey::Stack(slot_key.clone()));
        let candidate = VisibleBinding {
            name: slot_spec
                .param_name
                .as_ref()
                .filter(|_| matches!(slot_spec.role, ExternalStackSlotRole::StackArg))
                .cloned()
                .or_else(|| (!slot_spec.name.is_empty()).then(|| slot_spec.name.clone()))
                .unwrap_or_else(|| match key {
                    VisibleBindingKey::Param(idx) => format!("arg{}", idx + 1),
                    VisibleBindingKey::Stack(_) => "local".to_string(),
                }),
            ty: slot_spec.ty.clone(),
            kind: visible_binding_kind_for_slot_role(slot_spec.role),
            stack_slot: Some(slot_key.clone()),
            param_index: slot_spec.param_index,
            source_reg: slot_spec.source_reg.clone(),
        };
        bindings
            .entry(key)
            .and_modify(|existing| merge_visible_binding(existing, candidate.clone()))
            .or_insert(candidate);
    }

    for var in recovered_vars {
        let Some(key) = visible_binding_key_for_recovered_var(var) else {
            continue;
        };
        let candidate_name = rename_map
            .get(var.name.as_str())
            .cloned()
            .unwrap_or_else(|| var.name.clone());
        let candidate = VisibleBinding {
            name: sanitize_c_identifier(&candidate_name).unwrap_or(candidate_name),
            ty: type_map
                .get(var.name.as_str())
                .cloned()
                .or_else(|| parse_type_like_spec(&var.var_type, ptr_bits)),
            kind: if var.isarg {
                VisibleBindingKind::Param
            } else if matches!(key, VisibleBindingKey::Stack(_)) {
                VisibleBindingKind::Local
            } else {
                VisibleBindingKind::Unknown
            },
            stack_slot: match &key {
                VisibleBindingKey::Stack(slot_key) => Some(slot_key.clone()),
                VisibleBindingKey::Param(_) => None,
            },
            param_index: match key {
                VisibleBindingKey::Param(idx) => Some(idx),
                VisibleBindingKey::Stack(_) => None,
            },
            source_reg: var.reg.clone(),
        };
        bindings
            .entry(key)
            .and_modify(|existing| merge_visible_binding(existing, candidate.clone()))
            .or_insert(candidate);
    }

    bindings.into_values().collect()
}

fn build_var_type_candidates(
    vars: &[RecoveredVariable],
    ctx: &VarTypeCandidateContext<'_>,
    diagnostics: &mut TypeWritebackDiagnostics,
) -> Vec<VarTypeCandidate> {
    let mut out = Vec::with_capacity(vars.len());
    for var in vars {
        let slot_spec = slot_spec_for_recovered_var(var, ctx.stack_slots);
        if slot_spec.is_some_and(|spec| slot_role_is_hidden(spec.role)) {
            continue;
        }

        let mut source = WritebackSource::LocalInferred;
        let mut confidence = if var.var_type.contains('*') {
            92
        } else if var.isarg {
            88
        } else {
            84
        };
        let mut evidence = vec![WritebackEvidence::SsaVarRecovery];
        let mut chosen_type = var.var_type.clone();
        let arg_slot = var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok());

        if let Some(slot) = arg_slot
            && let Some(sig_ty) = ctx.current_context_maps.param_types.get(&slot)
            && !is_generic_type_string(sig_ty)
        {
            chosen_type = sig_ty.clone();
            confidence = 96;
            source = WritebackSource::SignatureRegistry;
            evidence.push(WritebackEvidence::ExternalSignatureCurrent);
        } else if let Some(slot) = arg_slot
            && let Some(sig_ty) = ctx
                .merged_signature
                .and_then(|sig| sig.params.get(slot))
                .and_then(|param| param.ty.as_ref())
                .map(|ty| render_signature_type(ty, ctx.ptr_bits))
            && !is_generic_type_string(&sig_ty)
        {
            chosen_type = sig_ty;
            confidence = 96;
            source = WritebackSource::SignatureRegistry;
            if ctx.is_main_signature {
                evidence.push(WritebackEvidence::CanonicalMainSignature);
            } else {
                evidence.push(WritebackEvidence::ExternalSignatureCurrent);
            }
        } else if let Some(slot) = arg_slot
            && let Some(struct_ty) = ctx.slot_type_overrides.get(&slot)
            && is_generic_type_string(&chosen_type)
        {
            chosen_type = struct_ty.clone();
            confidence = 90;
            source = WritebackSource::LocalInferred;
            evidence.push(WritebackEvidence::SsaFieldOffsetPattern);
        }

        if let Some(existing_ty) = ctx.existing_types.get(&var.name)
            && !is_generic_type_string(existing_ty)
        {
            if is_generic_type_string(&chosen_type) {
                chosen_type = existing_ty.clone();
                confidence = 98;
                source = WritebackSource::ExistingState;
                evidence.push(WritebackEvidence::ExistingStackType);
            } else if !existing_ty.eq_ignore_ascii_case(&chosen_type) {
                diagnostics.conflicts.push(format!(
                    "var `{}` existing type `{}` conflicts with inferred `{}`",
                    var.name, existing_ty, chosen_type
                ));
            }
        }

        if let Some(ext) = slot_spec
            && let Some(ext_ty) = ext.ty.as_ref()
            && slot_role_allows_external_local_identity(ext.role)
        {
            let ext_ty_str = render_signature_type(ext_ty, ctx.ptr_bits);
            let external_should_override = !is_generic_type_string(&ext_ty_str)
                && (is_generic_type_string(&chosen_type)
                    || (matches!(source, WritebackSource::LocalInferred)
                        && is_low_signal_storage_scalar_type(&chosen_type, ctx.ptr_bits)));
            if external_should_override {
                chosen_type = ext_ty_str;
                confidence = 97;
                source = WritebackSource::ExternalTypeDb;
                evidence.push(WritebackEvidence::ExternalStackAnnotation);
            }
        }

        let chosen_type = normalize_external_type_name(&chosen_type);
        out.push(VarTypeCandidate {
            name: var.name.clone(),
            kind: var.kind.clone(),
            delta: var.delta,
            var_type: chosen_type.clone(),
            isarg: var.isarg,
            reg: var.reg.clone(),
            size: estimate_c_type_size_bytes(&chosen_type, ctx.ptr_bits) as u32,
            confidence,
            source,
            evidence,
        });
    }
    out
}

fn build_var_rename_candidates(
    vars: &[RecoveredVariable],
    param_names: &HashMap<usize, String>,
    stack_slots: &BTreeMap<StackSlotKey, ExternalStackVarSpec>,
) -> Vec<VarRenameCandidate> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();

    for var in vars {
        let slot_spec = slot_spec_for_recovered_var(var, stack_slots);

        if let Some(ext) = slot_spec
            && ext.name != var.name
            && is_low_quality_stack_name(&var.name)
            && !is_low_quality_stack_name(&ext.name)
            && slot_role_allows_external_local_identity(ext.role)
        {
            let target_name = sanitize_c_identifier(&ext.name).unwrap_or_else(|| ext.name.clone());
            let edge = format!("{}->{target_name}", var.name);
            if !target_name.is_empty() && target_name != var.name && seen.insert(edge) {
                out.push(VarRenameCandidate {
                    name: var.name.clone(),
                    target_name,
                    confidence: 94,
                    source: WritebackSource::ExternalTypeDb,
                    evidence: vec![WritebackEvidence::ExternalStackName],
                });
            }
        }

        if let Some(ext) = slot_spec
            && matches!(ext.role, ExternalStackSlotRole::StackArg)
            && let Some(param_name) = ext.param_name.as_ref()
            && is_low_quality_stack_name(&var.name)
        {
            let target_name =
                sanitize_c_identifier(param_name).unwrap_or_else(|| param_name.clone());
            let edge = format!("{}->{target_name}", var.name);
            if !target_name.is_empty() && target_name != var.name && seen.insert(edge) {
                out.push(VarRenameCandidate {
                    name: var.name.clone(),
                    target_name,
                    confidence: 95,
                    source: WritebackSource::SignatureRegistry,
                    evidence: vec![WritebackEvidence::ExternalParamName],
                });
            }
        }

        let arg_slot = var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok());
        if let Some(slot) = arg_slot
            && let Some(param_name) = param_names.get(&slot)
            && is_generic_arg_name(&var.name)
        {
            let target_name =
                sanitize_c_identifier(param_name).unwrap_or_else(|| param_name.clone());
            let edge = format!("{}->{target_name}", var.name);
            if !target_name.is_empty() && target_name != var.name && seen.insert(edge) {
                out.push(VarRenameCandidate {
                    name: var.name.clone(),
                    target_name,
                    confidence: 95,
                    source: WritebackSource::SignatureRegistry,
                    evidence: vec![WritebackEvidence::ExternalParamName],
                });
            }
        }
    }

    out
}

fn signature_context_maps(
    signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) -> SignatureContextMaps {
    let mut maps = SignatureContextMaps::default();
    let Some(signature) = signature else {
        return maps;
    };
    for (idx, param) in signature.params.iter().enumerate() {
        if let Some(ty) = param.ty.as_ref() {
            let ty_str = render_signature_type(ty, ptr_bits);
            if !is_generic_type_string(&ty_str) {
                maps.param_types.insert(idx, ty_str);
            }
        }
        if !is_generic_arg_name(&param.name) {
            maps.param_names.insert(idx, param.name.clone());
        }
    }
    maps
}

fn apply_signature_context_overrides(
    signature_out: &mut InferredSignature,
    signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) {
    let Some(signature) = signature else {
        return;
    };

    let authoritative_param_count = signature_param_count_is_authoritative(signature);
    if authoritative_param_count && signature_out.params.len() > signature.params.len() {
        signature_out.params.truncate(signature.params.len());
    }

    while signature_out.params.len() < signature.params.len() {
        let idx = signature_out.params.len();
        let param_type = signature
            .params
            .get(idx)
            .and_then(|param| param.ty.as_ref())
            .map(|ty| render_signature_type(ty, ptr_bits))
            .unwrap_or_else(|| "void *".to_string());
        signature_out.params.push(InferredSignatureParam {
            name: format!("arg{}", idx + 1),
            param_type,
        });
    }

    if let Some(ret_ty) = signature.ret_type.as_ref() {
        let ret_ty = render_signature_type(ret_ty, ptr_bits);
        if !is_generic_type_string(&ret_ty) {
            signature_out.ret_type = ret_ty;
        }
    }

    for (idx, param) in signature.params.iter().enumerate() {
        if let Some(ty) = param.ty.as_ref() {
            let ty_str = render_signature_type(ty, ptr_bits);
            if !is_generic_type_string(&ty_str)
                && let Some(inferred_param) = signature_out.params.get_mut(idx)
            {
                inferred_param.param_type = ty_str;
            }
        }
        if !is_generic_arg_name(&param.name)
            && let Some(inferred_param) = signature_out.params.get_mut(idx)
        {
            inferred_param.name = param.name.clone();
        }
    }

    signature_out.signature = format_signature(
        &signature_out.function_name,
        &signature_out.ret_type,
        &signature_out.params,
    );
    signature_out.confidence = signature_out.confidence.max(signature_strength(signature));
}

fn signature_strength(signature: &FunctionSignatureSpec) -> u8 {
    let has_type_info =
        signature.ret_type.is_some() || signature.params.iter().any(|param| param.ty.is_some());
    let has_named_params = signature
        .params
        .iter()
        .any(|param| !is_generic_arg_name(&param.name));
    if has_type_info || has_named_params {
        96
    } else {
        80
    }
}

fn signature_param_count_is_authoritative(signature: &FunctionSignatureSpec) -> bool {
    if signature.params.is_empty() {
        return false;
    }
    signature_strength(signature) >= 96
}

fn is_generic_signature_type(ty: Option<&CTypeLike>) -> bool {
    match ty {
        None => true,
        Some(CTypeLike::Unknown | CTypeLike::Void) => true,
        Some(CTypeLike::Pointer(inner)) => {
            matches!(inner.as_ref(), CTypeLike::Unknown | CTypeLike::Void)
        }
        _ => false,
    }
}

fn signature_param_allows_local_struct_override(
    param: Option<&FunctionParamSpec>,
    ptr_bits: u32,
) -> bool {
    let Some(param) = param else {
        return true;
    };

    if is_generic_signature_type(param.ty.as_ref()) {
        return true;
    }

    is_generic_arg_name(&param.name)
        && matches!(
            param.ty.as_ref(),
            Some(CTypeLike::Int { bits, .. }) if *bits == ptr_bits
        )
}

fn merge_slot_type_overrides_into_signature(
    mut signature: Option<FunctionSignatureSpec>,
    slot_type_overrides: &HashMap<usize, String>,
    ptr_bits: u32,
) -> Option<FunctionSignatureSpec> {
    if slot_type_overrides.is_empty() {
        return signature;
    }

    let max_slot = slot_type_overrides.keys().copied().max()?;
    let sig = signature.get_or_insert_with(Default::default);
    let allow_param_count_extension = !signature_param_count_is_authoritative(sig);
    while allow_param_count_extension && sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, raw_ty) in slot_type_overrides {
        if *slot >= sig.params.len() {
            continue;
        }
        let Some(parsed) = parse_type_like_spec(raw_ty, ptr_bits) else {
            continue;
        };
        let param = &mut sig.params[*slot];
        if signature_param_allows_local_struct_override(Some(param), ptr_bits) {
            param.ty = Some(parsed);
        }
    }

    signature
}

fn signature_param_blocks_local_struct_override(
    signature: &Option<FunctionSignatureSpec>,
    slot: usize,
    ptr_bits: u32,
) -> bool {
    let Some(param) = signature.as_ref().and_then(|sig| sig.params.get(slot)) else {
        return false;
    };
    if signature_param_allows_local_struct_override(Some(param), ptr_bits) {
        return false;
    }

    let Some(ty) = param.ty.as_ref() else {
        return false;
    };
    match ty {
        CTypeLike::Pointer(inner) => !matches!(
            inner.as_ref(),
            CTypeLike::Unknown | CTypeLike::Void | CTypeLike::Struct(_) | CTypeLike::Union(_)
        ),
        _ => true,
    }
}

fn prune_conflicting_local_struct_overrides(
    merged_signature: &Option<FunctionSignatureSpec>,
    struct_decls: &mut Vec<StructDeclCandidate>,
    slot_type_overrides: &mut HashMap<usize, String>,
    slot_field_profiles: &mut HashMap<usize, BTreeMap<u64, String>>,
    ptr_bits: u32,
) {
    let blocked_slots = slot_type_overrides
        .keys()
        .copied()
        .filter(|slot| {
            signature_param_blocks_local_struct_override(merged_signature, *slot, ptr_bits)
        })
        .collect::<Vec<_>>();
    if blocked_slots.is_empty() {
        return;
    }

    for slot in &blocked_slots {
        slot_type_overrides.remove(slot);
        slot_field_profiles.remove(slot);
    }

    let referenced_local_names = slot_type_overrides
        .values()
        .filter_map(|ty| ty.trim().strip_prefix("struct "))
        .filter_map(|rest| rest.trim_end().strip_suffix(" *"))
        .map(|name| name.to_ascii_lowercase())
        .collect::<HashSet<_>>();

    struct_decls.retain(|decl| {
        decl.source != StructDeclSource::LocalInferred
            || referenced_local_names.contains(&decl.name.to_ascii_lowercase())
    });
}

fn collect_external_struct_candidates_from_db(
    db: &ExternalTypeDb,
    ptr_bits: u32,
) -> Vec<StructDeclCandidate> {
    let mut keys: Vec<String> = db.structs.keys().cloned().collect();
    keys.sort();

    let mut out = Vec::new();
    for key in keys {
        let Some(st) = db.structs.get(&key) else {
            continue;
        };
        if is_opaque_placeholder_type_name(&st.name) || st.fields.is_empty() {
            continue;
        }
        let mut fields = Vec::new();
        for (offset, field) in &st.fields {
            let raw_ty = field.ty.clone().unwrap_or_else(|| "uint8_t".to_string());
            fields.push(StructFieldCandidate {
                name: field.name.clone(),
                offset: *offset,
                field_type: normalize_external_type_name(&raw_ty),
                confidence: 95,
            });
        }
        let Some(decl) = build_struct_decl(&st.name, &fields, ptr_bits) else {
            continue;
        };
        out.push(StructDeclCandidate {
            name: st.name.clone(),
            decl,
            confidence: 95,
            source: StructDeclSource::ExternalTypeDb,
            fields,
        });
    }
    out
}

fn merge_local_structs_into_type_db(db: &mut ExternalTypeDb, struct_decls: &[StructDeclCandidate]) {
    for decl in struct_decls {
        let key = decl.name.to_ascii_lowercase();
        let mut fields = BTreeMap::new();
        for field in &decl.fields {
            fields.insert(
                field.offset,
                ExternalField {
                    name: field.name.clone(),
                    offset: field.offset,
                    ty: Some(field.field_type.clone()),
                },
            );
        }
        let candidate = ExternalStruct {
            name: decl.name.clone(),
            fields,
        };
        match db.structs.entry(key) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(candidate);
            }
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                if decl.source == StructDeclSource::LocalInferred
                    && is_generated_local_struct_name(&decl.name)
                {
                    entry.insert(candidate);
                }
            }
        }
    }
}

fn dedup_struct_decls(mut decls: Vec<StructDeclCandidate>) -> Vec<StructDeclCandidate> {
    decls.sort_by(|a, b| {
        a.name
            .to_ascii_lowercase()
            .cmp(&b.name.to_ascii_lowercase())
    });
    let mut merged: Vec<StructDeclCandidate> = Vec::new();
    for decl in decls {
        if let Some(existing) = merged
            .iter_mut()
            .find(|existing| existing.name.eq_ignore_ascii_case(&decl.name))
        {
            if should_replace_struct_decl(existing, &decl) {
                *existing = decl;
            }
        } else {
            merged.push(decl);
        }
    }
    merged
}

fn should_replace_struct_decl(
    existing: &StructDeclCandidate,
    candidate: &StructDeclCandidate,
) -> bool {
    candidate.source == StructDeclSource::LocalInferred
        && is_generated_local_struct_name(&candidate.name)
        && existing.name.eq_ignore_ascii_case(&candidate.name)
}

fn struct_fields_signature(fields: &[StructFieldCandidate]) -> Vec<(u64, String)> {
    let mut out: Vec<(u64, String)> = fields
        .iter()
        .map(|f| (f.offset, f.field_type.to_ascii_lowercase()))
        .collect();
    out.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    out
}

fn parse_struct_ptr_type_name(ty: &str) -> Option<String> {
    ty.trim()
        .strip_prefix("struct ")
        .and_then(|rest| rest.strip_suffix(" *"))
        .map(str::to_string)
}

fn local_struct_profile_score(
    decl: &StructDeclCandidate,
    profile: &BTreeMap<u64, String>,
) -> Option<(usize, usize, usize, i32)> {
    if decl.source != StructDeclSource::LocalInferred || profile.is_empty() {
        return None;
    }

    let field_map = decl
        .fields
        .iter()
        .map(|field| (field.offset, field.field_type.to_ascii_lowercase()))
        .collect::<BTreeMap<_, _>>();

    let mut offset_matches = 0usize;
    let mut typed_matches = 0usize;
    for (offset, ty) in profile {
        let Some(field_ty) = field_map.get(offset) else {
            continue;
        };
        offset_matches += 1;
        if field_ty == &ty.to_ascii_lowercase() {
            typed_matches += 1;
        }
    }

    (offset_matches > 0).then_some((
        offset_matches,
        typed_matches,
        decl.fields.len(),
        i32::from(decl.confidence),
    ))
}

fn prefer_stronger_local_struct_overrides(
    struct_decls: &[StructDeclCandidate],
    slot_type_overrides: &mut HashMap<usize, String>,
    slot_field_profiles: &HashMap<usize, BTreeMap<u64, String>>,
) {
    for (slot, ty) in slot_type_overrides.iter_mut() {
        let Some(profile) = slot_field_profiles.get(slot) else {
            continue;
        };
        if profile.is_empty() {
            continue;
        }

        let current_name = parse_struct_ptr_type_name(ty);
        let current_decl = current_name.as_ref().and_then(|name| {
            struct_decls
                .iter()
                .find(|decl| decl.name.eq_ignore_ascii_case(name))
        });
        if current_decl.is_some_and(|decl| decl.source == StructDeclSource::ExternalTypeDb)
            || current_name.is_some() && current_decl.is_none()
        {
            continue;
        }

        let current_score = current_decl.and_then(|decl| local_struct_profile_score(decl, profile));
        let best_local = struct_decls
            .iter()
            .filter_map(|decl| {
                local_struct_profile_score(decl, profile).map(|score| (score, decl.name.clone()))
            })
            .max_by(|(left_score, left_name), (right_score, right_name)| {
                left_score
                    .cmp(right_score)
                    .then_with(|| left_name.cmp(right_name))
            });

        let Some((best_score, best_name)) = best_local else {
            continue;
        };
        if current_score.is_none_or(|score| best_score > score) {
            *ty = format!("struct {} *", best_name);
        }
    }
}

fn structurally_compatible(local_fields: &[(u64, String)], ext_fields: &[(u64, String)]) -> bool {
    if local_fields.is_empty() || ext_fields.is_empty() {
        return false;
    }
    let mut matches = 0usize;
    for (off, ty) in local_fields {
        if ext_fields
            .iter()
            .any(|(eoff, ety)| eoff == off && ety == ty)
        {
            matches += 1;
        }
    }
    matches >= local_fields.len().min(2)
}

fn align_local_structs_with_external(
    struct_decls: &mut [StructDeclCandidate],
    slot_type_overrides: &mut HashMap<usize, String>,
    slot_field_profiles: &HashMap<usize, BTreeMap<u64, String>>,
    external_structs: &[StructDeclCandidate],
) {
    let mut local_to_external: HashMap<String, String> = HashMap::new();
    for local in struct_decls.iter_mut() {
        if local.source != StructDeclSource::LocalInferred {
            continue;
        }
        let local_sig = struct_fields_signature(&local.fields);
        for ext in external_structs {
            let ext_sig = struct_fields_signature(&ext.fields);
            if structurally_compatible(&local_sig, &ext_sig) {
                local_to_external.insert(local.name.clone(), ext.name.clone());
                local.confidence = local.confidence.max(92);
                break;
            }
        }
    }

    for (slot, ty) in slot_type_overrides.iter_mut() {
        let Some(profile) = slot_field_profiles.get(slot) else {
            continue;
        };
        if profile.is_empty() {
            continue;
        }
        let replacement = external_structs.iter().find_map(|ext| {
            let ext_sig = struct_fields_signature(&ext.fields);
            let local_sig: Vec<(u64, String)> = profile
                .iter()
                .map(|(off, ty)| (*off, ty.to_ascii_lowercase()))
                .collect();
            if structurally_compatible(&local_sig, &ext_sig) {
                Some(ext.name.clone())
            } else {
                None
            }
        });
        if let Some(ext_name) = replacement {
            *ty = format!("struct {} *", ext_name);
            continue;
        }
        if let Some(local_name) = ty
            .strip_prefix("struct ")
            .and_then(|s| s.strip_suffix(" *"))
            .map(str::to_string)
            && let Some(ext_name) = local_to_external.get(&local_name)
        {
            *ty = format!("struct {} *", ext_name);
        }
    }
}

fn score_global_type_links(
    ssa_blocks: &[SSABlock],
    struct_decls: &[StructDeclCandidate],
    var_type_candidates: &[VarTypeCandidate],
    ptr_bits: u32,
) -> Vec<GlobalTypeLinkCandidate> {
    let per_addr_profiles = infer_global_field_profiles(ssa_blocks, ptr_bits);
    if per_addr_profiles.is_empty() {
        return Vec::new();
    }

    let mut per_type_weight: BTreeMap<String, i32> = BTreeMap::new();
    let mut decl_profiles: BTreeMap<String, BTreeMap<u64, String>> = BTreeMap::new();
    for decl in struct_decls {
        let key = format!("struct {} *", decl.name);
        if is_generic_type_string(&key) {
            continue;
        }
        let source_boost = if decl.source == StructDeclSource::ExternalTypeDb {
            12
        } else {
            0
        };
        per_type_weight.insert(
            key.clone(),
            32 + source_boost + (decl.confidence as i32 / 6) + (decl.fields.len() as i32).min(16),
        );
        decl_profiles.insert(
            key,
            decl.fields
                .iter()
                .map(|field| {
                    (
                        field.offset,
                        normalize_external_type_name(&field.field_type).to_ascii_lowercase(),
                    )
                })
                .collect(),
        );
    }
    for var in var_type_candidates {
        if var.var_type.starts_with("struct ")
            && var.var_type.ends_with(" *")
            && !is_generic_type_string(&var.var_type)
        {
            *per_type_weight.entry(var.var_type.clone()).or_insert(30) +=
                4 + (var.confidence as i32 / 12);
        }
    }
    if per_type_weight.is_empty() {
        return Vec::new();
    }

    let mut per_addr_best: BTreeMap<u64, (String, i32)> = BTreeMap::new();
    for (addr, profile) in per_addr_profiles {
        if profile.is_empty() {
            continue;
        }
        let observed_fields = profile.len();
        let mut best: Option<(String, i32)> = None;
        for (ty, base_score) in &per_type_weight {
            let Some(decl_profile) = decl_profiles.get(ty) else {
                continue;
            };
            if observed_fields == 1 && decl_profile.len() > 1 {
                continue;
            }

            let mut exact_matches = 0i32;
            let mut declared_offsets = 0i32;
            let mut evidence_weight = 0i32;
            for (offset, evidence) in &profile {
                let Some(decl_ty) = decl_profile.get(offset) else {
                    continue;
                };
                declared_offsets += 1;
                if decl_ty
                    == &normalize_external_type_name(&evidence.field_type).to_ascii_lowercase()
                {
                    exact_matches += 1;
                    evidence_weight +=
                        1 + evidence.reads.min(4) as i32 + evidence.writes.min(4) as i32;
                }
            }
            if exact_matches == 0 {
                continue;
            }
            if observed_fields > 1 && exact_matches < observed_fields.min(2) as i32 {
                continue;
            }

            let score =
                *base_score + exact_matches * 18 + declared_offsets * 6 + evidence_weight.min(18);
            match best {
                Some((ref prev_ty, prev_score))
                    if prev_score > score || (prev_score == score && prev_ty <= ty) => {}
                _ => best = Some((ty.clone(), score)),
            }
        }
        if let Some(candidate) = best {
            per_addr_best.insert(addr, candidate);
        }
    }

    per_addr_best
        .into_iter()
        .map(|(addr, (target_type, score))| GlobalTypeLinkCandidate {
            addr,
            target_type,
            confidence: score.clamp(1, 99) as u8,
            source: WritebackSource::DataflowRanked,
        })
        .collect()
}

fn infer_global_field_profiles(
    ssa_blocks: &[SSABlock],
    ptr_bits: u32,
) -> BTreeMap<u64, BTreeMap<u64, InferredGlobalFieldEvidence>> {
    let mut addr_exprs: HashMap<String, GlobalAddrExpr> = HashMap::new();
    let mut field_evidence: BTreeMap<u64, BTreeMap<u64, InferredGlobalFieldEvidence>> =
        BTreeMap::new();
    let offset_bound = 0x4000i64;

    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                let addr_of = |var: &SSAVar, map: &HashMap<String, GlobalAddrExpr>| {
                    parse_const_value(&var.name)
                        .filter(|base| *base >= 0x10000)
                        .map(|base| GlobalAddrExpr {
                            base,
                            offset: 0,
                            confidence: 92,
                        })
                        .or_else(|| map.get(&ssa_var_block_key(block.addr, var)).copied())
                };
                let set_expr =
                    |dst: &SSAVar,
                     expr: GlobalAddrExpr,
                     map: &mut HashMap<String, GlobalAddrExpr>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev.confidence >= expr.confidence => false,
                            _ => {
                                map.insert(key, expr);
                                true
                            }
                        }
                    };
                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src } => {
                        if let Some(mut expr) = addr_of(src, &addr_exprs) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    SSAOp::Phi { dst, sources } => {
                        let mut selected = None;
                        for src in sources {
                            let Some(expr) = addr_of(src, &addr_exprs) else {
                                selected = None;
                                break;
                            };
                            selected = match selected {
                                None => Some(expr),
                                Some(prev)
                                    if prev.base == expr.base && prev.offset == expr.offset =>
                                {
                                    Some(GlobalAddrExpr {
                                        base: prev.base,
                                        offset: prev.offset,
                                        confidence: prev.confidence.max(expr.confidence),
                                    })
                                }
                                _ => None,
                            };
                            if selected.is_none() {
                                break;
                            }
                        }
                        if let Some(mut expr) = selected {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(raw) = parse_const_value(&b.name)
                        {
                            let off = base
                                .offset
                                .saturating_add(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && let Some(raw) = parse_const_value(&a.name)
                        {
                            let off = base
                                .offset
                                .saturating_add(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(raw) = parse_const_value(&b.name)
                        {
                            let off = base
                                .offset
                                .saturating_sub(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    SSAOp::PtrAdd {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        if let Some(base_expr) = addr_of(base, &addr_exprs)
                            && let Some(raw) = parse_const_value(&index.name)
                        {
                            let scaled = signed_offset_from_const(raw, ptr_bits)
                                .saturating_mul((*element_size).into());
                            let off = base_expr.offset.saturating_add(scaled);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base_expr.base,
                                        offset: off,
                                        confidence: base_expr.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    SSAOp::PtrSub {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        if let Some(base_expr) = addr_of(base, &addr_exprs)
                            && let Some(raw) = parse_const_value(&index.name)
                        {
                            let scaled = signed_offset_from_const(raw, ptr_bits)
                                .saturating_mul((*element_size).into());
                            let off = base_expr.offset.saturating_sub(scaled);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base_expr.base,
                                        offset: off,
                                        confidence: base_expr.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            let resolve_addr = |addr: &SSAVar| -> Option<GlobalAddrExpr> {
                parse_const_value(&addr.name)
                    .filter(|base| *base >= 0x10000)
                    .map(|base| GlobalAddrExpr {
                        base,
                        offset: 0,
                        confidence: 92,
                    })
                    .or_else(|| {
                        addr_exprs
                            .get(&ssa_var_block_key(block.addr, addr))
                            .copied()
                    })
            };
            match op {
                SSAOp::Load { dst, addr, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = field_evidence
                            .entry(expr.base)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.reads = entry.reads.saturating_add(1);
                        entry.field_type = size_to_type(dst.size);
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = field_evidence
                            .entry(expr.base)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.writes = entry.writes.saturating_add(1);
                        entry.field_type = size_to_type(val.size);
                    }
                }
                _ => {}
            }
        }
    }

    field_evidence
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct InferredGlobalFieldEvidence {
    reads: u32,
    writes: u32,
    field_type: String,
}

fn parse_existing_var_types_from_specs(
    stack_vars: &BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    ptr_bits: u32,
) -> HashMap<String, String> {
    stack_vars
        .values()
        .filter(|var| slot_role_allows_external_local_identity(var.role))
        .filter_map(|var| {
            let ty = var
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, ptr_bits))?;
            Some((var.name.clone(), normalize_external_type_name(&ty)))
        })
        .collect()
}

fn estimate_c_type_size_bytes(ty: &str, ptr_bits: u32) -> u64 {
    if let Some(parsed) = parse_type_like_spec(ty, ptr_bits)
        && let Some(size) = estimate_type_like_size_bytes(&parsed, ptr_bits)
        && size > 0
    {
        return size;
    }

    let lower = normalize_external_type_name(ty).trim().to_ascii_lowercase();
    if lower.contains('*') {
        return (ptr_bits / 8).max(1) as u64;
    }
    if lower == "double" || lower == "long double" {
        return 8;
    }
    1
}

fn estimate_type_like_size_bytes(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Void | CTypeLike::Unknown | CTypeLike::Function => None,
        CTypeLike::Bool => Some(1),
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        CTypeLike::Pointer(_) => Some((ptr_bits / 8).max(1) as u64),
        CTypeLike::Array(inner, Some(count)) => estimate_type_like_size_bytes(inner, ptr_bits)
            .map(|inner_size| inner_size.saturating_mul(*count as u64)),
        CTypeLike::Array(inner, None) => estimate_type_like_size_bytes(inner, ptr_bits),
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) => None,
    }
}

fn render_signature_type(ty: &CTypeLike, ptr_bits: u32) -> String {
    crate::render_signature_type(ty, ptr_bits)
}

fn format_signature(
    function_name: &str,
    ret_type: &str,
    params: &[InferredSignatureParam],
) -> String {
    crate::format_afs_signature(function_name, ret_type, params)
}

fn build_struct_decl(
    struct_name: &str,
    fields: &[StructFieldCandidate],
    _ptr_bits: u32,
) -> Option<String> {
    if fields.is_empty() {
        return None;
    }
    let body = fields
        .iter()
        .map(|field| {
            format!(
                "    {} {};",
                normalize_external_type_name(&field.field_type),
                field.name
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    Some(format!("struct {struct_name} {{\n{body}\n}};"))
}

fn is_opaque_placeholder_type_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    let stripped = lower
        .trim_start_matches("struct ")
        .trim_start_matches("union ")
        .trim_start_matches("enum ");
    stripped.starts_with("anon_") || stripped.starts_with("type_0x") || lower.contains(" type_0x")
}

fn is_generated_local_struct_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .trim_start_matches("struct ")
        .starts_with("sla_struct_")
}

fn is_generic_type_string(ty: &str) -> bool {
    let normalized = normalize_external_type_name(ty);
    let lower = normalized.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return true;
    }
    if lower.starts_with("byte[") {
        return true;
    }
    if is_opaque_placeholder_type_name(&lower) {
        return true;
    }
    matches!(
        lower.as_str(),
        "void *"
            | "void*"
            | "char *"
            | "char*"
            | "const char *"
            | "const char*"
            | "signed char *"
            | "signed char*"
            | "unsigned char *"
            | "unsigned char*"
            | "int"
            | "unsigned"
            | "unsigned int"
            | "long"
            | "unsigned long"
    )
}

fn is_low_signal_storage_scalar_type(ty: &str, ptr_bits: u32) -> bool {
    parse_type_like_spec(ty, ptr_bits).is_some_and(|parsed| matches!(parsed, CTypeLike::Int { .. }))
}

fn sanitize_c_identifier(raw: &str) -> Option<String> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    let mut out = String::with_capacity(trimmed.len());
    for ch in trimmed.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.chars().next().is_some_and(|ch| ch.is_ascii_digit()) {
        out.insert(0, '_');
    }
    if out.chars().all(|c| c == '_') {
        None
    } else {
        Some(out)
    }
}

fn is_low_quality_stack_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("var_")
        || lower.starts_with("local_")
        || lower.starts_with("stack_")
        || lower == "saved_fp"
        || is_generic_arg_name(&lower)
}

fn parse_const_value(name: &str) -> Option<u64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);

    if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }

    if let Ok(v) = val_str.parse::<u64>() {
        return Some(v);
    }
    u64::from_str_radix(val_str, 16).ok()
}

fn size_to_type(size: u32) -> String {
    match size {
        1 => "int8_t".to_string(),
        2 => "int16_t".to_string(),
        4 => "int32_t".to_string(),
        8 => "int64_t".to_string(),
        _ => format!("byte[{size}]"),
    }
}

fn signed_offset_from_const(raw: u64, ptr_bits: u32) -> i64 {
    let bits = ptr_bits.clamp(8, 64);
    if bits == 64 {
        return raw as i64;
    }
    let mask = (1u64 << bits) - 1;
    let sign = 1u64 << (bits - 1);
    let v = raw & mask;
    if (v & sign) != 0 {
        (v | (!mask)) as i64
    } else {
        v as i64
    }
}

fn ssa_var_block_key(block_addr: u64, var: &SSAVar) -> String {
    format!(
        "{}_{}@{block_addr:x}",
        var.name.to_ascii_lowercase(),
        var.version
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn main_signature_canonicalization_updates_signature_output() {
        let parsed_context = ParsedExternalContext::default();
        let input = TypeWritebackAnalysisInput {
            function_name: "sym.main",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.main".to_string(),
                signature: "void sym.main ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        };
        let analysis = build_type_writeback_analysis(input);
        assert_eq!(analysis.signature.ret_type, "int32_t");
        assert_eq!(analysis.signature.params.len(), 3);
        assert_eq!(analysis.signature.params[0].name, "argc");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .unwrap()
                .params[1]
                .name,
            "argv"
        );
    }

    #[test]
    fn interproc_heap_alloc_summary_upgrades_pointer_sized_scalar_return() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(
                root,
                FunctionSemanticSummary {
                    id: root,
                    name: Some("sym.alloc_wrapper".to_string()),
                    arg_count_hint: Some(1),
                    direct_callees: BTreeSet::from([0x5000]),
                    callsite_count: 1,
                    has_unknown_calls: false,
                    arg_effects: BTreeMap::new(),
                    memory_effects: Vec::new(),
                    return_relation: SummaryReturnRelation::HeapAlloc,
                    reads_global_memory: false,
                    writes_global_memory: false,
                    touches_unknown_memory: false,
                },
            )]),
            diagnostics: Default::default(),
        };
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_wrapper",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_wrapper".to_string(),
                signature: "int64_t sym.alloc_wrapper ()".to_string(),
                ret_type: "int64_t".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "void*");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.clone()),
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Void)))
        );
    }

    #[test]
    fn interproc_returned_arg_summary_propagates_param_type_and_callee_facts() {
        let root = r2ssa::InterprocFunctionId(0x401100);
        let helper = r2ssa::InterprocFunctionId(0x401200);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([
                (
                    root,
                    FunctionSemanticSummary {
                        id: root,
                        name: Some("sym.identity".to_string()),
                        arg_count_hint: Some(1),
                        direct_callees: BTreeSet::from([helper.0]),
                        callsite_count: 1,
                        has_unknown_calls: false,
                        arg_effects: BTreeMap::new(),
                        memory_effects: Vec::new(),
                        return_relation: SummaryReturnRelation::Arg(0),
                        reads_global_memory: false,
                        writes_global_memory: false,
                        touches_unknown_memory: false,
                    },
                ),
                (
                    helper,
                    FunctionSemanticSummary {
                        id: helper,
                        name: Some("sym.helper".to_string()),
                        arg_count_hint: Some(1),
                        direct_callees: BTreeSet::new(),
                        callsite_count: 0,
                        has_unknown_calls: false,
                        arg_effects: BTreeMap::from([(
                            0,
                            SummaryArgEffect {
                                read: true,
                                write: false,
                                escape: false,
                                free: false,
                            },
                        )]),
                        memory_effects: Vec::new(),
                        return_relation: SummaryReturnRelation::Arg(0),
                        reads_global_memory: false,
                        writes_global_memory: false,
                        touches_unknown_memory: false,
                    },
                ),
            ]),
            diagnostics: Default::default(),
        };
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.identity",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.identity".to_string(),
                signature: "int64_t sym.identity (char * src)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "src".to_string(),
                    param_type: "char *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "int8_t*");
        let callee = analysis
            .type_facts
            .callee_facts
            .get(&helper.0)
            .expect("helper callee fact");
        assert_eq!(callee.name.as_deref(), Some("sym.helper"));
        assert!(callee.arg_effects.get(&0).is_some_and(|effect| effect.read));
        assert_eq!(callee.return_relation, CalleeReturnRelation::Arg(0));
    }

    #[test]
    fn local_inferred_scalar_param_narrows_external_wide_signature() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
            }],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let vars = [RecoveredVariable {
            name: "arg0".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "int32_t".to_string(),
            isarg: true,
            reg: Some("x0".to_string()),
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym._check_secret",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym._check_secret".to_string(),
                signature: "int64_t sym._check_secret (int32_t arg1)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "int32_t".to_string(),
                }],
                callconv: String::new(),
                arch: "aarch64".to_string(),
                confidence: 90,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "int32_t");
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        let merged = analysis
            .type_facts
            .merged_signature
            .as_ref()
            .expect("merged signature");
        assert_eq!(
            merged.params[0].ty,
            Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            })
        );
    }

    #[test]
    fn recovered_arg_types_narrow_external_signature_when_local_signature_is_still_wide() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
            }],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let vars = [RecoveredVariable {
            name: "arg0".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "int32_t".to_string(),
            isarg: true,
            reg: Some("x0".to_string()),
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym._check_secret",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym._check_secret".to_string(),
                signature: "int64_t sym._check_secret (uint64_t arg1)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "uint64_t".to_string(),
                }],
                callconv: String::new(),
                arch: "aarch64".to_string(),
                confidence: 90,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "int32_t");
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.first())
                .and_then(|param| param.ty.clone()),
            Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            })
        );
    }

    #[test]
    fn authoritative_external_signature_keeps_param_count_over_longer_local_signature() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            }))),
            params: vec![
                FunctionParamSpec {
                    name: "src".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Signed,
                    }))),
                },
                FunctionParamSpec {
                    name: "len".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 64,
                        signedness: Signedness::Unsigned,
                    }),
                },
            ],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_and_copy",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_and_copy".to_string(),
                signature: "int8_t * sym.alloc_and_copy (int8_t * src, uint8_t len, int64_t arg3, int64_t arg4)".to_string(),
                ret_type: "int8_t *".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "src".to_string(),
                        param_type: "int8_t *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "len".to_string(),
                        param_type: "uint8_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "arg3".to_string(),
                        param_type: "int64_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "arg4".to_string(),
                        param_type: "int64_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params.len(), 2);
        assert_eq!(analysis.signature.params[0].name, "src");
        assert_eq!(analysis.signature.params[1].name, "len");
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| matches!(binding.kind, VisibleBindingKind::Param)
                    && binding.param_index == Some(0)
                    && binding.name == "src"),
            "expected visible param binding for src, got {:?}",
            analysis.type_facts.visible_bindings
        );
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| matches!(binding.kind, VisibleBindingKind::Param)
                    && binding.param_index == Some(1)
                    && binding.name == "len"),
            "expected visible param binding for len, got {:?}",
            analysis.type_facts.visible_bindings
        );
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .expect("merged signature")
                .params
                .len(),
            2
        );
    }

    #[test]
    fn stack_var_preference_renames_and_types_generic_stack_slots() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context
            .external_stack_vars
            .insert(-0x10, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            },
            spec,
        );
        let vars = [RecoveredVariable {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: -0x10,
            var_type: "byte[4]".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f".to_string().as_str(),
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: String::new(),
                arch: String::new(),
                confidence: 0,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(analysis.plan.var_rename_candidates[0].target_name, "count");
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| matches!(binding.kind, VisibleBindingKind::Local)
                    && binding
                        .stack_slot
                        .as_ref()
                        .is_some_and(|slot| slot.base == ExternalStackBase::FramePointer
                            && slot.offset == -0x10)
                    && binding.name == "count"),
            "expected visible local binding for count, got {:?}",
            analysis.type_facts.visible_bindings
        );
    }

    #[test]
    fn param_home_slots_do_not_surface_as_visible_local_writeback_candidates() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "arr_home".to_string(),
            ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::ParamHome,
            param_index: Some(0),
            param_name: Some("arr".to_string()),
            source_reg: Some("rdi".to_string()),
        };
        parsed_context
            .external_stack_vars
            .insert(0x10, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: 0x10,
            },
            spec,
        );

        let vars = [RecoveredVariable {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: 0x10,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis.plan.var_type_candidates.is_empty(),
            "param-home slots should not emit visible local type candidates: {:?}",
            analysis.plan.var_type_candidates
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "param-home slots should not emit visible local rename candidates: {:?}",
            analysis.plan.var_rename_candidates
        );
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(
                    |binding| matches!(binding.kind, VisibleBindingKind::HiddenHome)
                        && binding.name == "arr_home"
                ),
            "expected hidden param-home binding, got {:?}",
            analysis.type_facts.visible_bindings
        );
    }

    #[test]
    fn generic_unknown_param_home_slots_are_canonicalized_from_entry_stores() {
        let mut parsed_context = ParsedExternalContext {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                params: vec![
                    FunctionParamSpec {
                        name: "arr".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    },
                    FunctionParamSpec {
                        name: "idx".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                    FunctionParamSpec {
                        name: "v".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                ],
            }),
            register_params: vec![
                crate::context::ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    reg: "rdi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rsi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg3".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rdx".to_string(),
                },
            ],
            ..Default::default()
        };
        for (offset, name) in [(-8, "arr"), (-12, "var_ch"), (-16, "var_10h")] {
            parsed_context.stack_slots.insert(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                },
                ExternalStackVarSpec {
                    name: name.to_string(),
                    ty: None,
                    base: ExternalStackBase::FramePointer,
                    role: ExternalStackSlotRole::Unknown,
                    param_index: None,
                    param_name: None,
                    source_reg: None,
                },
            );
        }

        let ssa_blocks = [SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 1, 8),
                    val: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 2, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 2, 8),
                    val: SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 3, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 3, 8),
                    val: SSAVar::new("EDX", 0, 4),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature:
                    "int32_t sym.test_struct_array_index(void * arr, int32_t idx, int32_t v)"
                        .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "arr".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "idx".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "v".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        for (offset, expected_name, expected_idx) in
            [(-8, "arr", 0usize), (-12, "idx", 1), (-16, "v", 2)]
        {
            let slot = analysis
                .type_facts
                .stack_slots
                .get(&StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                })
                .expect("canonicalized slot");
            assert_eq!(slot.role, ExternalStackSlotRole::ParamHome);
            assert_eq!(slot.param_index, Some(expected_idx));
            assert_eq!(slot.param_name.as_deref(), Some(expected_name));
        }
    }

    #[test]
    fn generic_unknown_param_home_slots_are_canonicalized_from_entry_store_copies() {
        let mut parsed_context = ParsedExternalContext {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                params: vec![
                    FunctionParamSpec {
                        name: "arr".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    },
                    FunctionParamSpec {
                        name: "idx".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                    FunctionParamSpec {
                        name: "v".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                ],
            }),
            register_params: vec![
                crate::context::ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    reg: "rdi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rsi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg3".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rdx".to_string(),
                },
            ],
            ..Default::default()
        };
        for (offset, name) in [(-8, "arr"), (-12, "var_ch"), (-16, "var_10h")] {
            parsed_context.stack_slots.insert(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                },
                ExternalStackVarSpec {
                    name: name.to_string(),
                    ty: None,
                    base: ExternalStackBase::FramePointer,
                    role: ExternalStackSlotRole::Unknown,
                    param_index: None,
                    param_name: None,
                    source_reg: None,
                },
            );
        }

        let ssa_blocks = [SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_arr", 1, 8),
                    src: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 1, 8),
                    val: SSAVar::new("tmp:spill_arr", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 2, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_idx", 1, 4),
                    src: SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 2, 8),
                    val: SSAVar::new("tmp:spill_idx", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 3, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_v", 1, 4),
                    src: SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 3, 8),
                    val: SSAVar::new("tmp:spill_v", 1, 4),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature:
                    "int32_t sym.test_struct_array_index(void * arr, int32_t idx, int32_t v)"
                        .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "arr".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "idx".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "v".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        for (offset, expected_name, expected_idx) in
            [(-8, "arr", 0usize), (-12, "idx", 1), (-16, "v", 2)]
        {
            let slot = analysis
                .type_facts
                .stack_slots
                .get(&StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                })
                .expect("canonicalized slot");
            assert_eq!(slot.role, ExternalStackSlotRole::ParamHome);
            assert_eq!(slot.param_index, Some(expected_idx));
            assert_eq!(slot.param_name.as_deref(), Some(expected_name));
        }
    }

    #[test]
    fn writeback_does_not_cross_apply_frame_slots_to_stack_pointer_temps() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "len".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Unsigned,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.external_stack_vars.insert(-8, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -8,
            },
            spec,
        );

        let vars = [RecoveredVariable {
            name: "var_8h".to_string(),
            kind: "s".to_string(),
            delta: -8,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.plan.var_type_candidates.len(), 1);
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "void *");
        assert_eq!(
            analysis.plan.var_type_candidates[0].source,
            WritebackSource::LocalInferred
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "stack-pointer temps must not inherit frame-slot names: {:?}",
            analysis.plan.var_rename_candidates
        );
    }

    #[test]
    fn writeback_does_not_use_offset_only_legacy_slots_when_canonical_slots_exist() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "len".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Unsigned,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.external_stack_vars.insert(-8, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -8,
            },
            spec,
        );

        let vars = [RecoveredVariable {
            name: "var_8h".to_string(),
            kind: "x".to_string(),
            delta: -8,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.plan.var_type_candidates.len(), 1);
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "void *");
        assert_eq!(
            analysis.plan.var_type_candidates[0].source,
            WritebackSource::LocalInferred
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "unknown-base recovered vars must not inherit names from offset-only legacy slots when canonical slots exist: {:?}",
            analysis.plan.var_rename_candidates
        );
    }

    #[test]
    fn writeback_canonicalizes_legacy_only_stack_var_input() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.external_stack_vars.insert(-0x10, spec);

        let vars = [RecoveredVariable {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: -0x10,
            var_type: "byte[4]".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(analysis.plan.var_rename_candidates[0].target_name, "count");
        assert!(
            analysis.type_facts.stack_slots.contains_key(&StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            }),
            "legacy-only input should be canonicalized into stack_slots: {:?}",
            analysis.type_facts.stack_slots
        );
    }

    #[test]
    fn local_external_struct_reconciliation_prefers_external_names() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.external_type_db.structs.insert(
            "node".to_string(),
            ExternalStruct {
                name: "node".to_string(),
                fields: BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "value".to_string(),
                            offset: 0,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "next".to_string(),
                            offset: 8,
                            ty: Some("struct node *".to_string()),
                        },
                    ),
                ]),
            },
        );
        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_deadbeef".to_string(),
                decl: "struct sla_struct_deadbeef { int32_t f_0; struct node *f_8; };".to_string(),
                confidence: 90,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_0".to_string(),
                        offset: 0,
                        field_type: "int32_t".to_string(),
                        confidence: 90,
                    },
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "struct node *".to_string(),
                        confidence: 90,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_deadbeef *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (0u64, "int32_t".to_string()),
                    (8u64, "struct node *".to_string()),
                ]),
            )]),
        };
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: String::new(),
                arch: String::new(),
                confidence: 0,
                callconv_confidence: 0,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });
        assert_eq!(
            analysis
                .type_facts
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct node *")
        );
    }

    #[test]
    fn local_generated_struct_replaces_stale_generated_external_layout() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.external_type_db.structs.insert(
            "sla_struct_420703e08f70f00e".to_string(),
            ExternalStruct {
                name: "sla_struct_420703e08f70f00e".to_string(),
                fields: BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "_pad_0".to_string(),
                            offset: 0,
                            ty: Some("uint8_t".to_string()),
                        },
                    ),
                    (
                        4,
                        ExternalField {
                            name: "f_8".to_string(),
                            offset: 4,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "_pad_c".to_string(),
                            offset: 8,
                            ty: Some("uint8_t".to_string()),
                        },
                    ),
                    (
                        12,
                        ExternalField {
                            name: "f_34".to_string(),
                            offset: 12,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                ]),
            },
        );
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arr".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
            }],
        });

        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_420703e08f70f00e".to_string(),
                decl: "struct sla_struct_420703e08f70f00e { int32_t f_8; int32_t f_34; };"
                    .to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_34".to_string(),
                        offset: 0x34,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_420703e08f70f00e *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (8u64, "int32_t".to_string()),
                    (0x34u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature: "int32_t sym.test_struct_array_index (void * arr)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arr".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let struct_entry = analysis
            .type_facts
            .external_type_db
            .structs
            .get("sla_struct_420703e08f70f00e")
            .expect("expected merged local struct entry");
        assert_eq!(
            struct_entry.fields.get(&8).map(|field| field.name.as_str()),
            Some("f_8")
        );
        assert_eq!(
            struct_entry
                .fields
                .get(&0x34)
                .map(|field| field.name.as_str()),
            Some("f_34")
        );
        assert!(
            !struct_entry.fields.contains_key(&4) && !struct_entry.fields.contains_key(&12),
            "stale generated external layout should be replaced, got {:?}",
            struct_entry.fields
        );
        assert!(
            analysis
                .plan
                .struct_decls
                .iter()
                .find(|decl| decl.name == "sla_struct_420703e08f70f00e")
                .is_some_and(|decl| decl.source == StructDeclSource::LocalInferred),
            "expected plan to keep the current local synthetic struct"
        );
    }

    #[test]
    fn local_struct_override_replaces_weak_generic_ptr_sized_integer_param() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Signed,
                }),
            }],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_deadbeef".to_string(),
                decl: "struct sla_struct_deadbeef { int32_t f_8; int32_t f_34; };".to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_34".to_string(),
                        offset: 52,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_deadbeef *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (8u64, "int32_t".to_string()),
                    (52u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature: "int32_t sym.test_struct_array_index (int64_t arg1)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(
            analysis
                .type_facts
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_deadbeef *")
        );
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.first())
                .and_then(|param| param.ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                "sla_struct_deadbeef".to_string(),
            ))))
        );
    }

    #[test]
    fn interproc_heap_alloc_summary_upgrades_generic_return_type() {
        let mut summary_set = r2ssa::InterprocSummarySet::default();
        let root = r2ssa::InterprocFunctionId(0x401000);
        summary_set.root = Some(root);
        summary_set.summaries.insert(
            root,
            r2ssa::FunctionSemanticSummary {
                id: root,
                name: Some("sym.alloc_wrapper".to_string()),
                arg_count_hint: Some(1),
                direct_callees: BTreeSet::new(),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::new(),
                memory_effects: Vec::new(),
                return_relation: r2ssa::SummaryReturnRelation::HeapAlloc,
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );
        summary_set.diagnostics = r2ssa::InterprocSummaryDiagnostics {
            iterations: 2,
            max_iterations: 8,
            converged: true,
            scope_size: 1,
            scc_count: 1,
            max_scc_size: 1,
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_wrapper",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_wrapper".to_string(),
                signature: "void * sym.alloc_wrapper (int64_t n)".to_string(),
                ret_type: "unknown_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "n".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Void)))
        );
        assert_eq!(analysis.type_facts.interproc_diagnostics.scope_size, 1);
    }

    #[test]
    fn interproc_returned_arg_summary_exports_callee_facts() {
        let mut summary_set = r2ssa::InterprocSummarySet::default();
        let root = r2ssa::InterprocFunctionId(0x401000);
        let helper = r2ssa::InterprocFunctionId(0x401080);
        summary_set.root = Some(root);
        summary_set.summaries.insert(
            root,
            r2ssa::FunctionSemanticSummary {
                id: root,
                name: Some("sym.wrapper_user".to_string()),
                arg_count_hint: Some(2),
                direct_callees: BTreeSet::from([helper.0]),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::new(),
                memory_effects: Vec::new(),
                return_relation: r2ssa::SummaryReturnRelation::Unknown,
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );
        summary_set.summaries.insert(
            helper,
            r2ssa::FunctionSemanticSummary {
                id: helper,
                name: Some("sym.memcpy_like".to_string()),
                arg_count_hint: Some(2),
                direct_callees: BTreeSet::new(),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::from([
                    (
                        0,
                        r2ssa::SummaryArgEffect {
                            read: false,
                            write: true,
                            escape: true,
                            free: false,
                        },
                    ),
                    (
                        1,
                        r2ssa::SummaryArgEffect {
                            read: true,
                            write: false,
                            escape: false,
                            free: false,
                        },
                    ),
                ]),
                memory_effects: vec![
                    r2ssa::SummaryMemoryEffect {
                        kind: r2ssa::SummaryMemoryEffectKind::Write,
                        location: r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                            range: None,
                        },
                    },
                    r2ssa::SummaryMemoryEffect {
                        kind: r2ssa::SummaryMemoryEffectKind::Read,
                        location: r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                            range: None,
                        },
                    },
                ],
                return_relation: r2ssa::SummaryReturnRelation::Arg(0),
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.wrapper_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.wrapper_user".to_string(),
                signature: "void * sym.wrapper_user (void * dst, void * src)".to_string(),
                ret_type: "void *".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "dst".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "src".to_string(),
                        param_type: "void *".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 85,
                callconv_confidence: 85,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let helper_fact = analysis
            .type_facts
            .callee_facts
            .get(&helper.0)
            .expect("helper callee fact");
        assert_eq!(helper_fact.return_relation, CalleeReturnRelation::Arg(0));
        assert!(
            helper_fact
                .arg_effects
                .get(&0)
                .is_some_and(|effect| effect.write && effect.escape)
        );
        assert!(
            helper_fact
                .arg_effects
                .get(&1)
                .is_some_and(|effect| effect.read && !effect.write)
        );
        assert!(helper_fact.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                crate::facts::CalleeMemoryEffect {
                    kind: crate::facts::CalleeMemoryEffectKind::Write,
                    location: crate::facts::CalleeMemoryLocation {
                        region: crate::facts::CalleeMemoryRegion::Arg { index: 0 },
                        ..
                    },
                }
            )
        }));
        assert!(helper_fact.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                crate::facts::CalleeMemoryEffect {
                    kind: crate::facts::CalleeMemoryEffectKind::Read,
                    location: crate::facts::CalleeMemoryLocation {
                        region: crate::facts::CalleeMemoryRegion::Arg { index: 1 },
                        ..
                    },
                }
            )
        }));
    }

    #[test]
    fn interproc_memory_effect_summary_upgrades_generic_pointer_like_params() {
        let root = r2ssa::InterprocFunctionId(0x401300);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(
                root,
                FunctionSemanticSummary {
                    id: root,
                    name: Some("sym.ptr_user".to_string()),
                    arg_count_hint: Some(1),
                    direct_callees: BTreeSet::new(),
                    callsite_count: 0,
                    has_unknown_calls: false,
                    arg_effects: BTreeMap::from([(
                        0,
                        SummaryArgEffect {
                            read: true,
                            write: true,
                            escape: false,
                            free: false,
                        },
                    )]),
                    memory_effects: vec![r2ssa::SummaryMemoryEffect {
                        kind: r2ssa::SummaryMemoryEffectKind::Write,
                        location: r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                            range: Some(r2ssa::SummaryMemoryRange {
                                offset_lo: 0,
                                offset_hi: 7,
                                width: Some(8),
                            }),
                        },
                    }],
                    return_relation: SummaryReturnRelation::Void,
                    reads_global_memory: false,
                    writes_global_memory: false,
                    touches_unknown_memory: false,
                },
            )]),
            diagnostics: Default::default(),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.ptr_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.ptr_user".to_string(),
                signature: "void sym.ptr_user (int64_t p)".to_string(),
                ret_type: "void".to_string(),
                params: vec![InferredSignatureParam {
                    name: "p".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 70,
                callconv_confidence: 70,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "void*");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.first())
                .and_then(|param| param.ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Void)))
        );
    }

    #[test]
    fn symbolic_actionable_memory_terms_seed_local_struct_profiles() {
        let compiled = crate::facts::SymbolicCompiledCondition {
            simplified: "arg0->f_8 == 0".to_string(),
            terms: vec!["arg0->f_8 == 0".to_string()],
            memory_terms: vec![crate::facts::SymbolicMemoryCondition {
                region: crate::facts::SymbolicMemoryRegion::Argument { index: 0 },
                offset_lo: 8,
                offset_hi: 8,
                size: 4,
                exact_offset: true,
                evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                confidence: crate::facts::SymbolicSemanticConfidence::Exact,
                binding: None,
                expr: "*(arg0 + 8)".to_string(),
                value_expr: None,
                exact_value: false,
            }],
            backward_memory_substitutions: 1,
            backward_memory_candidate_enumerations: 1,
            backward_memory_residual_fallbacks: 0,
            precision: crate::facts::SymbolicConditionPrecision::Exact,
            evidence: crate::facts::SymbolicSemanticEvidence::exact(),
            confidence: crate::facts::SymbolicSemanticConfidence::Exact,
            supported_paths: 1,
            total_paths: 1,
        };
        let symbolic_facts = crate::facts::SymbolicSemanticFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: vec![crate::facts::SymbolicControlIsland {
                kind: crate::facts::SymbolicControlIslandKind::LargeCfgBranchFrontier,
                anchor_block: 0x401000,
                frontier_targets: vec![0x401020],
                facts: vec![crate::facts::SymbolicControlFact {
                    target: 0x401020,
                    status: crate::facts::SymbolicReachabilityStatus::Reachable,
                    condition: Some("arg0->f_8 == 0".to_string()),
                    compiled: Some(compiled),
                    evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                    confidence: crate::facts::SymbolicSemanticConfidence::Exact,
                }],
                evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                confidence: crate::facts::SymbolicSemanticConfidence::Exact,
            }],
            memory_islands: Vec::new(),
            diagnostics: crate::facts::SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };
        let mut local_structs = LocalStructArtifacts::default();

        augment_local_struct_artifacts_with_symbolic_facts(&mut local_structs, &symbolic_facts, 64);

        assert_eq!(
            local_structs
                .slot_field_profiles
                .get(&0)
                .and_then(|profile| profile.get(&8))
                .map(String::as_str),
            Some("int32_t")
        );
        assert_eq!(
            local_structs
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_symbolic_arg1 *")
        );
        assert!(
            local_structs
                .struct_decls
                .iter()
                .any(|decl| decl.name == "sla_struct_symbolic_arg1")
        );
    }

    #[test]
    fn symbolic_memory_islands_seed_local_struct_profiles_without_control_islands() {
        let symbolic_facts = crate::facts::SymbolicSemanticFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: vec![crate::facts::SymbolicMemoryIsland {
                kind: crate::facts::SymbolicMemoryIslandKind::ConditionFrontier,
                anchor_block: 0x401000,
                terms: vec![crate::facts::SymbolicMemoryCondition {
                    region: crate::facts::SymbolicMemoryRegion::Argument { index: 0 },
                    offset_lo: 8,
                    offset_hi: 8,
                    size: 4,
                    exact_offset: true,
                    evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                    confidence: crate::facts::SymbolicSemanticConfidence::Exact,
                    binding: None,
                    expr: "*(arg0 + 8)".to_string(),
                    value_expr: None,
                    exact_value: false,
                }],
                evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                confidence: crate::facts::SymbolicSemanticConfidence::Exact,
            }],
            diagnostics: crate::facts::SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };
        let mut local_structs = LocalStructArtifacts::default();

        augment_local_struct_artifacts_with_symbolic_facts(&mut local_structs, &symbolic_facts, 64);

        assert_eq!(
            local_structs
                .slot_field_profiles
                .get(&0)
                .and_then(|profile| profile.get(&8))
                .map(String::as_str),
            Some("int32_t")
        );
        assert_eq!(
            local_structs
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_symbolic_arg1 *")
        );
    }

    #[test]
    fn semantic_type_fallback_plan_uses_typed_symbolic_summary() {
        let symbolic_facts = crate::facts::SymbolicSemanticFacts {
            branch_facts: vec![crate::facts::SymbolicBranchFact {
                block_addr: 0x401000,
                true_target: 0x401010,
                false_target: 0x401020,
                true_status: crate::facts::SymbolicReachabilityStatus::Reachable,
                false_status: crate::facts::SymbolicReachabilityStatus::Unreachable,
                true_condition: Some("x == 0".to_string()),
                false_condition: Some("x != 0".to_string()),
                true_compiled: None,
                false_compiled: None,
            }],
            worker_islands: Vec::new(),
            control_islands: vec![crate::facts::SymbolicControlIsland {
                kind: crate::facts::SymbolicControlIslandKind::LargeCfgBranchFrontier,
                anchor_block: 0x401000,
                frontier_targets: vec![0x401010],
                facts: vec![crate::facts::SymbolicControlFact {
                    target: 0x401010,
                    status: crate::facts::SymbolicReachabilityStatus::Reachable,
                    condition: Some("x == 0".to_string()),
                    compiled: Some(crate::facts::SymbolicCompiledCondition {
                        simplified: "x == 0".to_string(),
                        terms: vec!["x == 0".to_string()],
                        memory_terms: Vec::new(),
                        backward_memory_substitutions: 0,
                        backward_memory_candidate_enumerations: 0,
                        backward_memory_residual_fallbacks: 0,
                        precision: crate::facts::SymbolicConditionPrecision::Exact,
                        evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                        confidence: crate::facts::SymbolicSemanticConfidence::Exact,
                        supported_paths: 1,
                        total_paths: 1,
                    }),
                    evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                    confidence: crate::facts::SymbolicSemanticConfidence::Exact,
                }],
                evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                confidence: crate::facts::SymbolicSemanticConfidence::Exact,
            }],
            memory_islands: vec![crate::facts::SymbolicMemoryIsland {
                kind: crate::facts::SymbolicMemoryIslandKind::LargeCfgConditionFrontier,
                anchor_block: 0x401000,
                terms: vec![crate::facts::SymbolicMemoryCondition {
                    region: crate::facts::SymbolicMemoryRegion::Argument { index: 0 },
                    offset_lo: 8,
                    offset_hi: 8,
                    size: 4,
                    exact_offset: true,
                    evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                    confidence: crate::facts::SymbolicSemanticConfidence::Exact,
                    binding: None,
                    expr: "*(arg0 + 8)".to_string(),
                    value_expr: None,
                    exact_value: false,
                }],
                evidence: crate::facts::SymbolicSemanticEvidence::exact(),
                confidence: crate::facts::SymbolicSemanticConfidence::Exact,
            }],
            diagnostics: crate::facts::SymbolicFactDiagnostics {
                skipped_large_cfg: true,
                semantic_mode: Some(crate::facts::SymbolicSemanticMode::Residual),
                semantic_capability: Some(crate::facts::SymbolicSemanticCapability {
                    query_ready: true,
                    type_ready: false,
                    decompile_ready: true,
                }),
                slice_class: Some(crate::facts::SymbolicSemanticSliceClass::Worker),
                residual_reasons: vec![crate::facts::SymbolicSemanticResidualReason::LargeCfg],
                ..Default::default()
            },
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };

        let plan = build_semantic_type_fallback_plan("fcn.401000", "x86-64", 64, &symbolic_facts);

        assert_eq!(plan.signature.params.len(), 1);
        assert!(plan.signature.params[0].param_type.contains("struct "));
        assert_eq!(plan.struct_decls.len(), 1);
        assert!(plan
            .diagnostics
            .warnings
            .iter()
            .any(|warning| warning.contains("semantic fallback: worker slice in residual mode")));
        assert!(
            plan.diagnostics
                .warnings
                .iter()
                .any(|warning| warning.contains("memory_islands=1"))
        );
        assert!(plan
            .diagnostics
            .warnings
            .iter()
            .any(|warning| warning.contains("type analysis not ready from semantic capability")));
        assert!(
            plan.diagnostics
                .warnings
                .iter()
                .any(|warning| warning.contains("projected 1 struct candidate"))
        );
    }
}
