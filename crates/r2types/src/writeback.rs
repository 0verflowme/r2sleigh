use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::{SSABlock, SSAOp, SSAVar};

use crate::context::{
    ExternalStackVarSpec, ParsedExternalContext, apply_main_signature_override, is_c_main_function,
    is_generic_arg_name,
};
use crate::convert::CTypeLike;
use crate::external::{
    ExternalField, ExternalStruct, ExternalTypeDb, normalize_external_type_name,
};
use crate::facts::{
    FunctionParamSpec, FunctionSignatureSpec, FunctionTypeFactInputs, FunctionTypeFacts,
    parse_type_like_spec,
};
use crate::model::Signedness;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveredVariable {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    pub var_type: String,
    pub isarg: bool,
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
    pub diagnostics: TypeWritebackDiagnostics,
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
    external_stack_vars: &'a HashMap<i64, ExternalStackVarSpec>,
    existing_types: &'a HashMap<String, String>,
    ptr_bits: u32,
    is_main_signature: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GlobalAddrExpr {
    base: u64,
    offset: i64,
    confidence: u8,
}

pub fn build_type_writeback_analysis(
    mut input: TypeWritebackAnalysisInput<'_>,
) -> TypeWritebackAnalysis {
    let mut merged_signature = merge_local_signature_into_merged_signature(
        input.parsed_context.merged_signature.clone(),
        inferred_signature_to_spec(&input.inferred_signature, input.ptr_bits),
    );
    apply_main_signature_override(input.function_name, &mut merged_signature);
    merged_signature = merge_recovered_arg_types_into_signature(
        merged_signature,
        input.recovered_vars,
        input.ptr_bits,
        input.function_name,
    );

    let mut diagnostics = input.diagnostics;
    diagnostics.solver_warnings = input.parsed_context.diagnostics.clone();

    let external_structs = collect_external_struct_candidates_from_db(
        &input.parsed_context.external_type_db,
        input.ptr_bits,
    );
    let mut local_structs = input.local_structs;
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
    let type_facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
        merged_signature: merged_signature.clone(),
        known_function_signatures: input.parsed_context.known_function_signatures.clone(),
        register_params: input.parsed_context.register_params.clone(),
        external_stack_vars: input.parsed_context.external_stack_vars.clone(),
        external_type_db: type_db,
        slot_type_overrides: local_structs.slot_type_overrides.clone(),
        slot_field_profiles: local_structs.slot_field_profiles.clone(),
        diagnostics: diagnostics.solver_warnings.clone(),
        ..FunctionTypeFactInputs::default()
    })
    .build();

    let existing_types =
        parse_existing_var_types_from_specs(&input.parsed_context.external_stack_vars);
    let is_main_signature = is_c_main_function(input.function_name);
    let var_type_ctx = VarTypeCandidateContext {
        current_context_maps: &current_context_maps,
        merged_signature: merged_signature.as_ref(),
        slot_type_overrides: &local_structs.slot_type_overrides,
        external_stack_vars: &input.parsed_context.external_stack_vars,
        existing_types: &existing_types,
        ptr_bits: input.ptr_bits,
        is_main_signature,
    };
    let var_type_candidates =
        build_var_type_candidates(input.recovered_vars, &var_type_ctx, &mut diagnostics);
    let var_rename_candidates = build_var_rename_candidates(
        input.recovered_vars,
        &current_context_maps.param_names,
        &input.parsed_context.external_stack_vars,
    );
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
            if local_signature_should_override_external(
                local.ret_type.as_ref(),
                external.ret_type.as_ref(),
            ) {
                external.ret_type = local.ret_type;
            } else if is_generic_signature_type(external.ret_type.as_ref()) {
                external.ret_type = local.ret_type.or(external.ret_type);
            }

            if external.params.len() < local.params.len() {
                external
                    .params
                    .resize_with(local.params.len(), || FunctionParamSpec {
                        name: String::new(),
                        ty: None,
                    });
            }

            for (idx, local_param) in local.params.into_iter().enumerate() {
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
    while sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, local_ty) in local_arg_types {
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

fn build_var_type_candidates(
    vars: &[RecoveredVariable],
    ctx: &VarTypeCandidateContext<'_>,
    diagnostics: &mut TypeWritebackDiagnostics,
) -> Vec<VarTypeCandidate> {
    let mut out = Vec::with_capacity(vars.len());
    for var in vars {
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

        if (var.kind == "b" || var.kind == "s")
            && let Some(ext) = ctx.external_stack_vars.get(&var.delta)
            && let Some(ext_ty) = ext.ty.as_ref()
        {
            let ext_ty_str = render_signature_type(ext_ty, ctx.ptr_bits);
            if !is_generic_type_string(&ext_ty_str) && is_generic_type_string(&chosen_type) {
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
    external_stack_vars: &HashMap<i64, ExternalStackVarSpec>,
) -> Vec<VarRenameCandidate> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();

    for var in vars {
        if (var.kind == "b" || var.kind == "s")
            && let Some(ext) = external_stack_vars.get(&var.delta)
            && ext.name != var.name
            && is_low_quality_stack_name(&var.name)
            && !is_low_quality_stack_name(&ext.name)
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
    while sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, raw_ty) in slot_type_overrides {
        let Some(parsed) = parse_type_like_spec(raw_ty, ptr_bits) else {
            continue;
        };
        let param = &mut sig.params[*slot];
        if is_generic_signature_type(param.ty.as_ref()) {
            param.ty = Some(parsed);
        }
    }

    signature
}

fn signature_param_blocks_local_struct_override(
    signature: &Option<FunctionSignatureSpec>,
    slot: usize,
) -> bool {
    let Some(ty) = signature
        .as_ref()
        .and_then(|sig| sig.params.get(slot))
        .and_then(|param| param.ty.as_ref())
    else {
        return false;
    };

    if matches!(ty, CTypeLike::Unknown | CTypeLike::Void) {
        return false;
    }

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
) {
    let blocked_slots = slot_type_overrides
        .keys()
        .copied()
        .filter(|slot| signature_param_blocks_local_struct_override(merged_signature, *slot))
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
        db.structs.entry(key).or_insert_with(|| {
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
            ExternalStruct {
                name: decl.name.clone(),
                fields,
            }
        });
    }
}

fn dedup_struct_decls(mut decls: Vec<StructDeclCandidate>) -> Vec<StructDeclCandidate> {
    let mut seen = HashSet::new();
    let mut merged = Vec::new();
    decls.sort_by(|a, b| {
        a.name
            .to_ascii_lowercase()
            .cmp(&b.name.to_ascii_lowercase())
    });
    for decl in decls {
        if seen.insert(decl.name.to_ascii_lowercase()) {
            merged.push(decl);
        }
    }
    merged
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
    stack_vars: &HashMap<i64, ExternalStackVarSpec>,
) -> HashMap<String, String> {
    stack_vars
        .values()
        .filter_map(|var| {
            let ty = var.ty.as_ref().map(|ty| render_signature_type(ty, 64))?;
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
    render_type_like(&materialize_signature_type_like(ty.clone(), ptr_bits))
}

fn materialize_signature_type_like(ty: CTypeLike, ptr_bits: u32) -> CTypeLike {
    match ty {
        CTypeLike::Pointer(inner) => {
            if matches!(*inner, CTypeLike::Unknown | CTypeLike::Void)
                || matches!(
                    inner.as_ref(),
                    CTypeLike::Struct(name)
                        | CTypeLike::Union(name)
                        | CTypeLike::Enum(name)
                        if is_unmaterialized_aggregate_name(name)
                )
            {
                return CTypeLike::Pointer(Box::new(CTypeLike::Void));
            }
            CTypeLike::Pointer(Box::new(materialize_signature_type_like(*inner, ptr_bits)))
        }
        CTypeLike::Array(inner, len) => {
            if matches!(*inner, CTypeLike::Unknown | CTypeLike::Void) {
                return CTypeLike::Array(
                    Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }),
                    len,
                );
            }
            CTypeLike::Array(
                Box::new(materialize_signature_type_like(*inner, ptr_bits)),
                len,
            )
        }
        CTypeLike::Unknown => fallback_scalar_type_like(ptr_bits),
        CTypeLike::Struct(name) if is_unmaterialized_aggregate_name(&name) => {
            fallback_scalar_type_like(ptr_bits)
        }
        CTypeLike::Union(name) if is_unmaterialized_aggregate_name(&name) => {
            fallback_scalar_type_like(ptr_bits)
        }
        CTypeLike::Enum(name) if is_unmaterialized_aggregate_name(&name) => {
            fallback_scalar_type_like(ptr_bits)
        }
        other => other,
    }
}

fn fallback_scalar_type_like(ptr_bits: u32) -> CTypeLike {
    CTypeLike::Int {
        bits: if ptr_bits >= 64 { 64 } else { 32 },
        signedness: Signedness::Signed,
    }
}

fn render_type_like(ty: &CTypeLike) -> String {
    match ty {
        CTypeLike::Void => "void".to_string(),
        CTypeLike::Bool => "bool".to_string(),
        CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Signed,
        } => "int8_t".to_string(),
        CTypeLike::Int {
            bits: 16,
            signedness: Signedness::Signed,
        } => "int16_t".to_string(),
        CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Signed,
        } => "int32_t".to_string(),
        CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Signed,
        } => "int64_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Signed | Signedness::Unknown,
        } => {
            format!("int{bits}_t")
        }
        CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Unsigned,
        } => "uint8_t".to_string(),
        CTypeLike::Int {
            bits: 16,
            signedness: Signedness::Unsigned,
        } => "uint16_t".to_string(),
        CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Unsigned,
        } => "uint32_t".to_string(),
        CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Unsigned,
        } => "uint64_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        } => format!("uint{bits}_t"),
        CTypeLike::Float(32) => "float".to_string(),
        CTypeLike::Float(64) => "double".to_string(),
        CTypeLike::Float(bits) => format!("float{bits}"),
        CTypeLike::Pointer(inner) => format!("{}*", render_type_like(inner)),
        CTypeLike::Array(inner, Some(size)) => format!("{}[{}]", render_type_like(inner), size),
        CTypeLike::Array(inner, None) => format!("{}[]", render_type_like(inner)),
        CTypeLike::Struct(name) => format!("struct {name}"),
        CTypeLike::Union(name) => format!("union {name}"),
        CTypeLike::Enum(name) => format!("enum {name}"),
        CTypeLike::Function => "void (*)()".to_string(),
        CTypeLike::Unknown => "/* unknown */".to_string(),
    }
}

fn format_signature(
    function_name: &str,
    ret_type: &str,
    params: &[InferredSignatureParam],
) -> String {
    let args = params
        .iter()
        .map(|param| format!("{},{}", param.param_type, param.name))
        .collect::<Vec<_>>()
        .join(",");
    format!("{ret_type} {function_name} ({args})")
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

fn is_unmaterialized_aggregate_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower.is_empty() || lower == "anon" || lower.starts_with("anon_")
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
    fn stack_var_preference_renames_and_types_generic_stack_slots() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.external_stack_vars.insert(
            -0x10,
            ExternalStackVarSpec {
                name: "count".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                base: Some("bp".to_string()),
            },
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
            diagnostics: TypeWritebackDiagnostics::default(),
        });
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(analysis.plan.var_rename_candidates[0].target_name, "count");
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
}
