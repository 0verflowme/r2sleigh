use crate::blocks::BlockSlice;
use crate::context::{PluginCtxView, require_ctx_view};
use crate::helpers::{effective_ptr_bits, resolve_function_name};
use crate::{ArchSpec, R2ILBlock, R2ILContext};
#[cfg(test)]
use crate::{InferredParamJson, InferredSignatureCcJson};
use std::ffi::CString;
#[cfg(test)]
use std::hash::Hash;
use std::os::raw::c_char;
use std::ptr;
use std::sync::OnceLock;

pub(crate) struct FunctionInput<'a> {
    pub(crate) ctx: PluginCtxView<'a>,
    pub(crate) blocks: BlockSlice,
    pub(crate) function_name: String,
}

pub(crate) type FunctionAnalysis = r2engine::EngineAnalysis;
#[cfg(test)]
pub(crate) type FunctionAnalysisArtifact = r2engine::EngineAnalysisArtifact;

#[cfg(test)]
type FunctionAnalysisCacheKey = r2engine::AnalysisCacheKey;
#[cfg(test)]
type FunctionArtifactCacheKey = r2engine::ArtifactCacheKey;

#[cfg(test)]
fn hash_debug_payload<T: std::fmt::Debug>(value: &T) -> u64 {
    r2engine::stable_fnv1a_debug_hash(value)
}

#[cfg(test)]
fn hash_optional_arch(arch: Option<&ArchSpec>) -> u64 {
    arch.map(hash_debug_payload).unwrap_or(0)
}

#[cfg(test)]
pub(crate) fn hash_string_payload(payload: &str) -> u64 {
    r2engine::stable_fnv1a_hash(payload)
}

#[cfg(test)]
fn hash_value<T: Hash>(value: &T) -> u64 {
    r2engine::stable_fnv1a_hash(value)
}

#[cfg(test)]
fn hash_blocks(blocks: &[R2ILBlock]) -> u64 {
    r2engine::stable_blocks_hash(blocks)
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
fn function_artifact_cache_key_parts_hashed(
    function_name: &str,
    function_addr: u64,
    arch: Option<&ArchSpec>,
    blocks: &[R2ILBlock],
    semantic_metadata_enabled: bool,
    typed_context_hash: u64,
    assumptions_hash: u64,
    interproc_scope_hash: u64,
    interproc_max_iterations: usize,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionArtifactCacheKey> {
    let analysis = FunctionAnalysisCacheKey::from_hashes(
        function_addr,
        hash_string_payload(function_name),
        hash_optional_arch(arch),
        hash_blocks(blocks),
        typed_context_hash,
        assumptions_hash,
        r2engine::function_analysis_depth_hash(semantic_metadata_enabled),
    );
    let interproc_budget_hash = hash_value(&(
        "interproc-scope-budget-v1",
        interproc_scope_hash,
        interproc_max_iterations,
    ));
    Some(FunctionArtifactCacheKey::from_hashes(
        analysis,
        interproc_budget_hash,
        r2sym::stable_scope_hash(symbolic_scope),
    ))
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
fn function_artifact_cache_key_parts(
    function_name: &str,
    arch: Option<&ArchSpec>,
    blocks: &[R2ILBlock],
    semantic_metadata_enabled: bool,
    external_context_json: &str,
    interproc_scope_hash: u64,
    interproc_max_iterations: usize,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionArtifactCacheKey> {
    let ptr_bits = arch.map(effective_ptr_bits).unwrap_or(64);
    let parsed = r2engine::parse_external_context_json_for_engine(external_context_json, ptr_bits);
    function_artifact_cache_key_parts_hashed(
        function_name,
        0,
        arch,
        blocks,
        semantic_metadata_enabled,
        parsed.context_identity_hash,
        parsed.assumptions_hash,
        interproc_scope_hash,
        interproc_max_iterations,
        symbolic_scope,
    )
}

#[cfg(test)]
fn session_context_identity_hash(external_context_json: &str, ptr_bits: u32) -> u64 {
    r2engine::parse_external_context_json_for_engine(external_context_json, ptr_bits)
        .context_identity_hash
}

pub(crate) struct FunctionFactsStore {
    engine_session: r2engine::EngineSession,
}

impl FunctionFactsStore {
    fn new() -> Self {
        Self {
            engine_session: r2engine::EngineSession::default(),
        }
    }
}

pub(crate) fn function_facts_store() -> &'static FunctionFactsStore {
    static STORE: OnceLock<FunctionFactsStore> = OnceLock::new();
    STORE.get_or_init(FunctionFactsStore::new)
}

pub(crate) fn engine_session() -> &'static r2engine::EngineSession {
    &function_facts_store().engine_session
}

#[cfg(test)]
fn rename_function_analysis_artifact(
    artifact: FunctionAnalysisArtifact,
    function_name: &str,
) -> FunctionAnalysisArtifact {
    r2engine::rename_engine_analysis_artifact(artifact, function_name)
}

fn cache_counters_json(counters: r2engine::CacheCounters) -> String {
    let hits = counters.hits;
    let misses = counters.misses;
    let insertions = counters.insertions;
    let evictions = counters.evictions;
    let lookups = counters.total_lookups();
    format!(
        "{{\"hits\":{hits},\"misses\":{misses},\"lookups\":{lookups},\"insertions\":{insertions},\"evictions\":{evictions}}}"
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_decompile_render_cache_stats_json() -> *mut c_char {
    let profile = engine_session().profile(r2engine::EngineProfileRequest {
        reset_after_read: false,
    });
    let json = cache_counters_json(profile.metrics.renders);
    CString::new(json).map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_engine_cache_stats_json() -> *mut c_char {
    let profile = engine_session().profile(r2engine::EngineProfileRequest {
        reset_after_read: false,
    });
    let metrics = profile.metrics;
    let analysis = metrics.analysis;
    let artifacts = metrics.artifacts;
    let renders = metrics.renders;
    let total = profile.total;
    let json = format!(
        "{{\"analysis\":{},\"artifacts\":{},\"renders\":{},\"total\":{}}}",
        cache_counters_json(analysis),
        cache_counters_json(artifacts),
        cache_counters_json(renders),
        cache_counters_json(total)
    );
    CString::new(json).map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_decompile_render_cache_stats_reset() {
    let _ = engine_session().profile(r2engine::EngineProfileRequest {
        reset_after_read: true,
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_engine_cache_stats_reset() {
    let _ = engine_session().profile(r2engine::EngineProfileRequest {
        reset_after_read: true,
    });
}

#[cfg(test)]
fn type_like_to_string(ty: &r2types::CTypeLike) -> String {
    r2types::render_c_type_like(ty)
}

pub(crate) type VarProt = r2types::RecoveredVariable;
#[cfg(test)]
pub(crate) type TypeHintRank = r2types::TypeHintRank;
#[cfg(test)]
pub(crate) type TypeHint = r2types::TypeHint;

fn build_var_recovery_ssa_blocks(
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
) -> Option<Vec<r2ssa::SSABlock>> {
    let func = r2ssa::SSAFunction::from_blocks_raw(blocks, arch)?;
    Some(
        func.blocks()
            .map(|block| r2ssa::SSABlock {
                addr: block.addr,
                size: block.size,
                ops: block.ops.clone(),
            })
            .collect(),
    )
}

pub(crate) fn build_function_input<'a>(
    ctx: *const R2ILContext,
    blocks: *const *const crate::R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
) -> Option<FunctionInput<'a>> {
    let ctx = require_ctx_view(ctx)?;
    let blocks = unsafe { BlockSlice::from_ffi(blocks, num_blocks)? };
    Some(FunctionInput {
        ctx,
        blocks,
        function_name: resolve_function_name(fcn_addr, fcn_name),
    })
}

pub(crate) fn build_function_analysis_from_parts(
    function_name: &str,
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
) -> Option<FunctionAnalysis> {
    engine_session().prepare_analysis(function_name, blocks, arch)
}

pub(crate) fn build_function_analysis(input: &FunctionInput<'_>) -> Option<FunctionAnalysis> {
    build_function_analysis_from_parts(
        &input.function_name,
        input.blocks.as_slice(),
        input.ctx.arch,
    )
}

#[cfg(test)]
pub(crate) type InterprocScopeFacts = r2engine::InterprocScopeFacts;
#[cfg(test)]
pub(crate) type InterprocSeedEntry = r2engine::InterprocSeedEntry;

#[cfg(test)]
pub(crate) fn empty_interproc_scope_facts() -> InterprocScopeFacts {
    r2engine::InterprocScopeFacts::empty()
}

#[cfg(test)]
pub(crate) fn interproc_scope_facts_from_seed_entries<I>(entries: I) -> InterprocScopeFacts
where
    I: IntoIterator<Item = (u64, Option<String>, Option<usize>)>,
{
    r2engine::interproc_scope_facts_from_seed_entries(entries)
}

#[cfg(test)]
pub(crate) fn interproc_scope_facts_from_typed_seed_entries<I>(entries: I) -> InterprocScopeFacts
where
    I: IntoIterator<Item = InterprocSeedEntry>,
{
    r2engine::interproc_scope_facts_from_typed_seed_entries(entries)
}

pub(crate) fn infer_signature_cc_from_analysis(
    input: &FunctionInput<'_>,
    analysis: &FunctionAnalysis,
) -> Option<r2types::InferredSignature> {
    let ptr_bits = input
        .ctx
        .arch
        .as_ref()
        .map(|arch| effective_ptr_bits(arch))
        .unwrap_or(64);
    r2engine::infer_signature_from_analysis_with_register_names(
        r2engine::EngineSignatureInferenceWithRegisterNamesRequest {
            function_name: &input.function_name,
            arch: input.ctx.arch,
            ptr_bits,
            semantic_metadata_enabled: input.ctx.semantic_metadata_enabled,
            r2il_blocks: input.blocks.as_slice(),
            reg_type_hints: std::collections::HashMap::new(),
            analysis,
        },
        |vn| input.ctx.disasm.register_name(vn),
    )
}

#[allow(dead_code)]
pub(crate) fn infer_signature_cc_inner(
    input: &FunctionInput<'_>,
) -> Option<r2types::InferredSignature> {
    let analysis = build_function_analysis(input)?;
    infer_signature_cc_from_analysis(input, &analysis)
}

#[cfg(test)]
fn apply_signature_context_overrides(
    sig: &mut InferredSignatureCcJson,
    signature: Option<&r2types::FunctionSignatureSpec>,
) -> (
    std::collections::HashMap<usize, String>,
    std::collections::HashMap<usize, String>,
) {
    let mut param_types = std::collections::HashMap::new();
    let mut param_names = std::collections::HashMap::new();

    if let Some(signature) = signature {
        while sig.params.len() < signature.params.len() {
            let idx = sig.params.len();
            let param_type = signature
                .params
                .get(idx)
                .and_then(|param| param.ty.as_ref())
                .map(type_like_to_string)
                .unwrap_or_else(|| "void *".to_string());
            sig.params.push(InferredParamJson {
                name: format!("arg{}", idx + 1),
                param_type,
            });
        }
        if let Some(ret_ty) = signature.ret_type.as_ref()
            && !matches!(ret_ty, r2types::CTypeLike::Unknown)
        {
            let ret_ty_str = type_like_to_string(ret_ty);
            sig.ret_type = ret_ty_str;
        }
        for (idx, param) in signature.params.iter().enumerate() {
            if let Some(ty) = param.ty.as_ref() {
                let ty_str = type_like_to_string(ty);
                param_types.insert(idx, ty_str.clone());
                if !matches!(ty, r2types::CTypeLike::Unknown)
                    && let Some(inferred_param) = sig.params.get_mut(idx)
                {
                    inferred_param.param_type = ty_str;
                }
            }
            if !crate::is_generic_arg_name(&param.name) {
                param_names.insert(idx, param.name.clone());
                if let Some(inferred_param) = sig.params.get_mut(idx) {
                    inferred_param.name = param.name.clone();
                }
            }
        }
        sig.signature = crate::format_afs_signature(&sig.function_name, &sig.ret_type, &sig.params);
        sig.confidence = sig.confidence.max(signature_strength(signature));
    }

    (param_types, param_names)
}

#[cfg(test)]
pub(crate) fn apply_main_signature_override(
    function_name: &str,
    signature_cc: &mut InferredSignatureCcJson,
    merged_signature: &mut Option<r2types::FunctionSignatureSpec>,
) {
    let mut canonicalized = merged_signature.clone();
    if !r2types::apply_main_signature_override(function_name, &mut canonicalized) {
        return;
    }

    let Some(main_signature) = canonicalized else {
        return;
    };
    signature_cc.ret_type = main_signature
        .ret_type
        .as_ref()
        .map(type_like_to_string)
        .unwrap_or_else(|| "int32_t".to_string());
    signature_cc.params = main_signature
        .params
        .iter()
        .map(|param| InferredParamJson {
            name: param.name.clone(),
            param_type: param
                .ty
                .as_ref()
                .map(type_like_to_string)
                .unwrap_or_else(|| "void *".to_string()),
        })
        .collect();
    signature_cc.signature = crate::format_afs_signature(
        &signature_cc.function_name,
        &signature_cc.ret_type,
        &signature_cc.params,
    );
    signature_cc.confidence = signature_cc.confidence.max(96);
    *merged_signature = Some(main_signature);
}

#[cfg(test)]
fn signature_strength(signature: &r2types::FunctionSignatureSpec) -> u8 {
    let has_type_info =
        signature.ret_type.is_some() || signature.params.iter().any(|param| param.ty.is_some());
    let has_named_params = signature
        .params
        .iter()
        .any(|param| !crate::is_generic_arg_name(&param.name));
    if has_type_info || has_named_params {
        96
    } else {
        80
    }
}

#[allow(dead_code)]
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_detached_function_analysis_artifact(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
    semantic_metadata_enabled: bool,
    reg_type_hints: &std::collections::HashMap<String, TypeHint>,
    external_context_json: &str,
) -> Option<FunctionAnalysisArtifact> {
    build_detached_function_analysis_artifact_with_scope_and_semantics(
        blocks,
        function_name,
        arch,
        ptr_bits,
        semantic_metadata_enabled,
        reg_type_hints,
        external_context_json,
        None,
        None,
    )
}

#[cfg(test)]
#[allow(dead_code, clippy::too_many_arguments)]
pub(crate) fn build_detached_function_analysis_artifact_with_scope(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
    semantic_metadata_enabled: bool,
    reg_type_hints: &std::collections::HashMap<String, TypeHint>,
    external_context_json: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionAnalysisArtifact> {
    build_detached_function_analysis_artifact_with_scope_and_semantics(
        blocks,
        function_name,
        arch,
        ptr_bits,
        semantic_metadata_enabled,
        reg_type_hints,
        external_context_json,
        symbolic_scope,
        None,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_detached_function_analysis_artifact_with_scope_and_semantics(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
    semantic_metadata_enabled: bool,
    reg_type_hints: &std::collections::HashMap<String, TypeHint>,
    external_context_json: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    precomputed_semantic_artifact: Option<r2sym::SemanticArtifact>,
) -> Option<FunctionAnalysisArtifact> {
    build_detached_function_analysis_artifact_with_scope_and_optional_semantics(
        blocks,
        function_name,
        arch,
        ptr_bits,
        semantic_metadata_enabled,
        reg_type_hints,
        external_context_json,
        symbolic_scope,
        precomputed_semantic_artifact,
        true,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_detached_function_analysis_artifact_with_scope_and_optional_semantics(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
    semantic_metadata_enabled: bool,
    reg_type_hints: &std::collections::HashMap<String, TypeHint>,
    external_context_json: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    precomputed_semantic_artifact: Option<r2sym::SemanticArtifact>,
    compile_missing_semantics: bool,
) -> Option<FunctionAnalysisArtifact> {
    let parsed_context =
        r2engine::parse_external_context_json_for_engine(external_context_json, ptr_bits);
    let scope_facts = empty_interproc_scope_facts();
    let request = r2engine::EngineAnalyzeRequest::from_input_with_compile_missing_semantics(
        r2engine::EngineAnalyzeRequestInput {
            function_name: function_name.to_string(),
            function_addr: blocks.first().map(|block| block.addr).unwrap_or_default(),
            blocks: blocks.to_vec(),
            arch: arch.cloned(),
            ptr_bits: Some(ptr_bits),
            semantic_metadata_enabled,
            reg_type_hints: reg_type_hints.clone(),
            parsed_context: parsed_context.parsed_context,
            external_context_fallback_hash: parsed_context.fallback_hash,
            scope_facts,
            interproc_max_iterations: 1,
            symbolic_scope: symbolic_scope.cloned(),
            precomputed_semantic_artifact,
            include_interproc_summary_set: false,
        },
        compile_missing_semantics,
    );
    engine_session()
        .analyze(request)
        .map(|response| rename_function_analysis_artifact(response.artifact, function_name))
}

#[derive(Debug, serde::Serialize)]
pub(crate) struct DataRef {
    pub(crate) from: u64,
    pub(crate) to: u64,
    #[serde(rename = "type")]
    pub(crate) ref_type: String,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighRecoveredVar {
    name: *const c_char,
    type_name: *const c_char,
    reg: *const c_char,
    delta: i64,
    kind: c_char,
    is_arg: i32,
}

pub struct R2SleighRecoveredVars {
    vars: Vec<R2SleighRecoveredVar>,
    _strings: Vec<CString>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighDataRef {
    from: u64,
    to: u64,
    ref_kind: c_char,
}

pub struct R2SleighDataRefs {
    refs: Vec<R2SleighDataRef>,
}

fn push_owned_cstring(strings: &mut Vec<CString>, value: Option<&str>) -> *const c_char {
    let Some(value) = value.filter(|value| !value.is_empty()) else {
        return ptr::null();
    };
    let Ok(cstr) = CString::new(value) else {
        return ptr::null();
    };
    let ptr = cstr.as_ptr();
    strings.push(cstr);
    ptr
}

fn ffi_recovered_vars_from_vars(vars: &[VarProt]) -> R2SleighRecoveredVars {
    let mut strings = Vec::new();
    let vars = vars
        .iter()
        .map(|var| R2SleighRecoveredVar {
            name: push_owned_cstring(&mut strings, Some(var.name.as_str())),
            type_name: push_owned_cstring(&mut strings, Some(var.var_type.as_str())),
            reg: push_owned_cstring(&mut strings, var.reg.as_deref()),
            delta: var.delta,
            kind: var.kind.as_bytes().first().copied().unwrap_or(b's') as c_char,
            is_arg: i32::from(var.isarg),
        })
        .collect();
    R2SleighRecoveredVars {
        vars,
        _strings: strings,
    }
}

fn data_ref_from_fact(fact: &r2ssa::DataRefFact) -> DataRef {
    DataRef {
        from: fact.from,
        to: fact.to,
        ref_type: fact.kind.as_str().to_string(),
    }
}

fn ffi_data_refs_from_refs(refs: &[r2ssa::DataRefFact]) -> R2SleighDataRefs {
    R2SleighDataRefs {
        refs: refs
            .iter()
            .map(|reference| R2SleighDataRef {
                from: reference.from,
                to: reference.to,
                ref_kind: reference.kind.as_char() as c_char,
            })
            .collect(),
    }
}

#[cfg(test)]
pub(crate) fn merge_type_hint(
    hints: &mut std::collections::HashMap<String, TypeHint>,
    key: String,
    incoming: TypeHint,
) {
    r2types::merge_type_hint(hints, key, incoming);
}

#[cfg(test)]
pub(crate) fn collect_register_type_hints(
    r2il_blocks: &[R2ILBlock],
    disasm: &crate::Disassembler,
) -> std::collections::HashMap<String, TypeHint> {
    r2engine::collect_register_type_hints_with_names(r2il_blocks, |vn| disasm.register_name(vn))
}

#[cfg(test)]
pub(crate) const X86_ARG_REGS: &[(&str, &[&str])] = r2types::X86_ARG_REGS;
#[cfg(test)]
pub(crate) const X86_FRAME_BASES: &[&str] = r2types::X86_FRAME_BASES;
#[cfg(test)]
type ArgAliasMap = r2types::ArgAliasMap;
#[cfg(test)]
type BaseRegList = r2types::BaseRegList;

#[cfg(test)]
pub(crate) fn recover_vars_arch_profile(
    arch: Option<&ArchSpec>,
) -> (ArgAliasMap, BaseRegList, BaseRegList) {
    r2types::recover_vars_arch_profile(arch.map(|spec| spec.name.as_str()))
}

#[cfg(test)]
pub(crate) fn ssa_var_block_key(block_addr: u64, var: &r2ssa::SSAVar) -> String {
    r2types::ssa_var_block_key(block_addr, var)
}

#[cfg(test)]
pub(crate) fn scalar_register_family_key(name: &str) -> String {
    r2types::scalar_register_family_key(name)
}

#[cfg(test)]
pub(crate) fn collect_signature_type_evidence_context(
    ssa_blocks: &[r2ssa::SSABlock],
) -> r2types::SignatureTypeEvidenceContext {
    r2types::collect_signature_type_evidence_context(ssa_blocks)
}

#[cfg(test)]
pub(crate) fn merge_register_type_hints(
    metadata_hints: &std::collections::HashMap<String, TypeHint>,
    usage_hints: &std::collections::HashMap<String, TypeHint>,
    arg_regs: ArgAliasMap,
) -> std::collections::HashMap<String, TypeHint> {
    let mut merged = std::collections::HashMap::new();

    for (reg, hint) in metadata_hints {
        merge_type_hint(&mut merged, reg.clone(), hint.clone());
    }
    for (reg, hint) in usage_hints {
        merge_type_hint(&mut merged, reg.clone(), hint.clone());
    }

    for (canonical, aliases) in arg_regs {
        let candidates: Vec<TypeHint> = std::iter::once(*canonical)
            .chain(aliases.iter().copied())
            .filter_map(|name| merged.get(name).cloned())
            .collect();
        if let Some(best) = candidates
            .into_iter()
            .max_by(|a, b| a.rank.cmp(&b.rank).then_with(|| b.ty.cmp(&a.ty)))
        {
            merge_type_hint(&mut merged, (*canonical).to_string(), best.clone());
            for alias in *aliases {
                merge_type_hint(&mut merged, alias.to_string(), best.clone());
            }
        }
    }

    merged
}

#[cfg(test)]
pub(crate) fn merge_pointer_slot_evidence(
    inferred_params: &mut [r2types::SignatureParamCandidate],
    pointer_arg_slots: &std::collections::BTreeSet<usize>,
) {
    r2types::merge_pointer_slot_evidence_into_signature_params(inferred_params, pointer_arg_slots);
}

#[cfg(test)]
pub(crate) fn recover_vars_from_ssa(
    ssa_blocks: &[r2ssa::SSABlock],
    arch: Option<&ArchSpec>,
    metadata_reg_type_hints: &std::collections::HashMap<String, TypeHint>,
    semantic_metadata_enabled: bool,
) -> Vec<VarProt> {
    r2engine::recover_vars_from_ssa(
        ssa_blocks,
        arch,
        metadata_reg_type_hints,
        semantic_metadata_enabled,
    )
}

#[cfg(test)]
pub(crate) fn add_stack_var(
    vars: &mut Vec<VarProt>,
    seen_slots: &mut std::collections::HashMap<(bool, i64), usize>,
    base_reg: &str,
    frame_bases: &[&str],
    offset: i64,
    size: u32,
    type_override: Option<String>,
) {
    let is_frame_base = frame_bases.contains(&base_reg);
    let slot_key = (is_frame_base, offset);
    if let Some(existing_idx) = seen_slots.get(&slot_key).copied() {
        if let Some(override_ty) = type_override
            && override_ty == "void *"
            && let Some(existing) = vars.get_mut(existing_idx)
            && existing.var_type != "void *"
        {
            existing.var_type = override_ty;
        }
        return;
    }

    let is_arg = if is_frame_base { offset > 0 } else { false };

    let var_name = if is_arg && offset > 8 {
        format!("arg_{:x}h", offset.unsigned_abs())
    } else {
        format!("var_{:x}h", offset.unsigned_abs())
    };

    let kind = if is_frame_base { "b" } else { "s" };

    vars.push(VarProt {
        name: var_name,
        kind: kind.to_string(),
        delta: offset,
        var_type: type_override.unwrap_or_else(|| size_to_type(size)),
        isarg: is_arg && offset > 8,
        reg: None,
    });
    seen_slots.insert(slot_key, vars.len().saturating_sub(1));
}

#[cfg(test)]
pub(crate) fn parse_const_value(name: &str) -> Option<u64> {
    r2ssa::parse_const_value(name)
}

#[cfg(test)]
pub(crate) fn size_to_type(size: u32) -> String {
    r2types::size_to_type(size)
}

#[cfg(test)]
pub(crate) fn get_data_refs_from_ssa_with_op_sources(
    ssa_blocks: &[r2ssa::SSABlock],
    op_sources: Option<&[Vec<u64>]>,
) -> Vec<DataRef> {
    r2ssa::data_refs_from_ssa_with_op_sources(ssa_blocks, op_sources)
        .iter()
        .map(data_ref_from_fact)
        .collect()
}

fn recover_vars_for_ffi(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> Option<Vec<VarProt>> {
    let input = build_function_input(ctx, blocks, num_blocks, 0, ptr::null())?;
    let ssa_blocks = build_var_recovery_ssa_blocks(input.blocks.as_slice(), input.ctx.arch)?;

    let semantic_metadata_enabled = input.ctx.semantic_metadata_enabled;

    if ssa_blocks.is_empty() {
        return None;
    }

    Some(r2engine::recover_vars_from_ssa_with_register_names(
        r2engine::EngineRecoverVarsRequest {
            ssa_blocks: &ssa_blocks,
            r2il_blocks: input.blocks.as_slice(),
            arch: input.ctx.arch,
            semantic_metadata_enabled,
            metadata_reg_type_hints: std::collections::HashMap::new(),
        },
        |vn| input.ctx.disasm.register_name(vn),
    ))
}

/// Recover variables from SSA analysis.
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_recover_vars(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
) -> *mut c_char {
    let Some(vars) = recover_vars_for_ffi(ctx, blocks, num_blocks, fcn_addr) else {
        return ptr::null_mut();
    };

    match serde_json::to_string(&vars) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_recover_vars_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
) -> *mut R2SleighRecoveredVars {
    let Some(vars) = recover_vars_for_ffi(ctx, blocks, num_blocks, fcn_addr) else {
        return ptr::null_mut();
    };
    Box::into_raw(Box::new(ffi_recovered_vars_from_vars(&vars)))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_recovered_vars_items(
    vars: *const R2SleighRecoveredVars,
    count: *mut usize,
) -> *const R2SleighRecoveredVar {
    if vars.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let vars = unsafe { &*vars };
    if !count.is_null() {
        unsafe {
            *count = vars.vars.len();
        }
    }
    vars.vars.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_recovered_vars_free(vars: *mut R2SleighRecoveredVars) {
    if !vars.is_null() {
        unsafe {
            drop(Box::from_raw(vars));
        }
    }
}

fn data_refs_for_ffi(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> Option<Vec<r2ssa::DataRefFact>> {
    let input = build_function_input(ctx, blocks, num_blocks, 0, ptr::null())?;
    r2ssa::data_refs_from_blocks(input.blocks.as_slice(), input.ctx.arch, input.ctx.disasm)
}

/// Get data flow references from def-use analysis.
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_data_refs(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
) -> *mut c_char {
    let Some(refs) = data_refs_for_ffi(ctx, blocks, num_blocks, fcn_addr) else {
        return ptr::null_mut();
    };
    let refs: Vec<DataRef> = refs.iter().map(data_ref_from_fact).collect();
    match serde_json::to_string(&refs) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_data_refs_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
) -> *mut R2SleighDataRefs {
    let Some(refs) = data_refs_for_ffi(ctx, blocks, num_blocks, fcn_addr) else {
        return ptr::null_mut();
    };
    Box::into_raw(Box::new(ffi_data_refs_from_refs(&refs)))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_data_refs_items(
    refs: *const R2SleighDataRefs,
    count: *mut usize,
) -> *const R2SleighDataRef {
    if refs.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let refs = unsafe { &*refs };
    if !count.is_null() {
        unsafe {
            *count = refs.refs.len();
        }
    }
    refs.refs.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_data_refs_free(refs: *mut R2SleighDataRefs) {
    if !refs.is_null() {
        unsafe {
            drop(Box::from_raw(refs));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ArchSpec, TypeEvidence, collect_type_evidence_for_var, infer_signature_return_type,
        resolve_evidence_driven_type,
    };

    fn signed_type(bits: u32) -> r2types::CTypeLike {
        r2types::CTypeLike::Int {
            bits,
            signedness: r2types::Signedness::Signed,
        }
    }

    fn void_ptr_type() -> r2types::CTypeLike {
        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Void))
    }

    fn const_return_blocks(addr: u64, value: u64) -> Vec<r2il::R2ILBlock> {
        let mut block = r2il::R2ILBlock::new(addr, 4);
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(value, 8),
        });
        vec![block]
    }

    fn empty_interproc_hash() -> u64 {
        empty_interproc_scope_facts().identity_hash()
    }

    #[test]
    fn detached_summary_probe_rejects_resolved_name_without_evidence() {
        let blocks = const_return_blocks(0x4b30, 0);
        assert!(
            r2engine::native_worker_summary_artifact(&blocks, "fcn.00004b30", None, None, true,)
                .is_none(),
            "a bounded probe with only an autogenerated raw name should not invent semantics"
        );

        assert!(
            r2engine::native_worker_summary_artifact(
                &blocks,
                "readlinebuffer_delim",
                None,
                None,
                true,
            )
            .is_none(),
            "a resolved display name alone should not seed canonical worker semantics"
        );
    }

    #[test]
    fn get_data_refs_resolves_const_add_chain_target() {
        let block = r2ssa::SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    src: r2ssa::SSAVar::new("const:dead0000", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:target", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    b: r2ssa::SSAVar::new("const:beef", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:load", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:target", 1, 8),
                },
            ],
        };

        let refs = get_data_refs_from_ssa_with_op_sources(&[block], None);
        assert!(
            refs.iter()
                .any(|r| { r.from == 0x401000 && r.to == 0xdeadbeef && r.ref_type == "d" }),
            "const add chain should emit DATA xref to the computed target"
        );
    }

    #[test]
    fn interproc_seed_entries_require_typed_linkage_for_helper_summaries() {
        let raw_facts = interproc_scope_facts_from_seed_entries([(
            0x2000,
            Some("sym.imp.malloc".to_string()),
            None,
        )]);
        assert!(
            raw_facts
                .summaries()
                .get(&r2ssa::InterprocFunctionId(0x2000))
                .is_none(),
            "tuple seed import names must remain hints only"
        );

        let facts = interproc_scope_facts_from_typed_seed_entries([InterprocSeedEntry {
            id: 0x2000,
            name: Some("malloc".to_string()),
            arg_count_hint: None,
            linkage: r2ssa::FunctionSemanticLinkage::Imported,
        }]);
        let summary = facts
            .summaries()
            .get(&r2ssa::InterprocFunctionId(0x2000))
            .expect("typed imported seed summary should exist");

        assert_eq!(
            summary.return_relation,
            r2ssa::SummaryReturnRelation::HeapAlloc
        );
        assert_eq!(
            summary.linkage,
            r2ssa::FunctionSemanticLinkage::Imported,
            "helper semantics require typed FFI linkage"
        );
    }

    #[test]
    fn get_data_refs_ignores_small_const_add_chain() {
        let block = r2ssa::SSABlock {
            addr: 0x402000,
            size: 4,
            ops: vec![r2ssa::SSAOp::IntAdd {
                dst: r2ssa::SSAVar::new("tmp:small", 1, 8),
                a: r2ssa::SSAVar::new("const:40", 0, 8),
                b: r2ssa::SSAVar::new("const:2", 0, 8),
            }],
        };

        let refs = get_data_refs_from_ssa_with_op_sources(&[block], None);
        assert!(
            !refs.iter().any(|r| r.to == 0x42),
            "small immediate constants should not be treated as addresses"
        );
    }

    #[test]
    fn get_data_refs_resolves_const_add_chain_across_blocks() {
        let block_a = r2ssa::SSABlock {
            addr: 0x403000,
            size: 4,
            ops: vec![r2ssa::SSAOp::Copy {
                dst: r2ssa::SSAVar::new("tmp:base", 1, 8),
                src: r2ssa::SSAVar::new("const:dead0000", 0, 8),
            }],
        };
        let block_b = r2ssa::SSABlock {
            addr: 0x403004,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:target", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    b: r2ssa::SSAVar::new("const:beef", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:load", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:target", 1, 8),
                },
            ],
        };

        let refs = get_data_refs_from_ssa_with_op_sources(&[block_a, block_b], None);
        assert!(
            refs.iter()
                .any(|r| { r.from == 0x403004 && r.to == 0xdeadbeef && r.ref_type == "d" }),
            "const add chain split across blocks should emit DATA xref to the computed target"
        );
    }

    #[test]
    fn get_data_refs_uses_per_op_source_addr_when_available() {
        let block = r2ssa::SSABlock {
            addr: 0x404000,
            size: 0x20,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    src: r2ssa::SSAVar::new("const:404d00", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:target", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    b: r2ssa::SSAVar::new("const:108", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:load", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:target", 1, 8),
                },
            ],
        };
        let op_sources = vec![vec![0x404008, 0x40400c, 0x404010]];

        let refs = get_data_refs_from_ssa_with_op_sources(&[block], Some(&op_sources));
        assert!(
            refs.iter()
                .any(|r| { r.from == 0x40400c && r.to == 0x404e08 && r.ref_type == "d" }),
            "computed add-chain xref should use the IntAdd op source address: {refs:?}"
        );
    }

    #[test]
    fn get_data_refs_uses_per_op_source_addr_for_const_sub_chain() {
        let block = r2ssa::SSABlock {
            addr: 0x405000,
            size: 0x20,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    src: r2ssa::SSAVar::new("const:405000", 0, 8),
                },
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("tmp:target", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    b: r2ssa::SSAVar::new("const:108", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:load", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:target", 1, 8),
                },
            ],
        };
        let op_sources = vec![vec![0x405008, 0x40500c, 0x405010]];

        let refs = get_data_refs_from_ssa_with_op_sources(&[block], Some(&op_sources));
        assert!(
            refs.iter()
                .any(|r| { r.from == 0x40500c && r.to == 0x404ef8 && r.ref_type == "d" }),
            "computed sub-chain xref should use the IntSub op source address: {refs:?}"
        );
    }

    #[test]
    fn get_data_refs_ignores_small_const_sub_chain() {
        let block = r2ssa::SSABlock {
            addr: 0x406000,
            size: 4,
            ops: vec![r2ssa::SSAOp::IntSub {
                dst: r2ssa::SSAVar::new("tmp:small", 1, 8),
                a: r2ssa::SSAVar::new("const:40", 0, 8),
                b: r2ssa::SSAVar::new("const:2", 0, 8),
            }],
        };

        let refs = get_data_refs_from_ssa_with_op_sources(&[block], None);
        assert!(
            !refs.iter().any(|r| r.to == 0x3e),
            "small immediate sub constants should not be treated as addresses"
        );
    }

    #[test]
    fn get_data_refs_resolves_const_add_chain_through_stack_spills() {
        let block = r2ssa::SSABlock {
            addr: 0x100001138,
            size: 0x3c,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("const:404d00", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 4, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    a: r2ssa::SSAVar::new("X8", 4, 8),
                    b: r2ssa::SSAVar::new("const:108", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("SP", 1, 8),
                    val: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("tmp:cmp", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("const:404e08", 0, 8),
                },
            ],
        };
        let op_sources = vec![vec![
            0x100001138,
            0x10000113c,
            0x100001140,
            0x100001144,
            0x100001148,
            0x10000114c,
            0x100001150,
            0x100001154,
        ]];

        let refs = get_data_refs_from_ssa_with_op_sources(&[block], Some(&op_sources));
        assert!(
            refs.iter().any(|r| r.to == 0x404e08 && r.ref_type == "d"),
            "stack-spilled const add chain should emit DATA xref to the recovered target: {refs:?}"
        );
    }

    #[test]
    fn recover_vars_usage_pointer_inference_promotes_x86_arg_type() {
        let arch = ArchSpec::new("x86-64");
        let block = r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:1000", 1, 8),
                    a: r2ssa::SSAVar::new("rdi", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:2000", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:1000", 1, 8),
                },
            ],
        };

        let hints = std::collections::HashMap::new();
        let vars = recover_vars_from_ssa(&[block], Some(&arch), &hints, true);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(
            arg0.var_type, "void *",
            "address-role usage should infer pointer type for arg0"
        );
    }

    #[test]
    fn recover_vars_usage_pointer_inference_handles_spill_reload_scaled_index() {
        let arch = ArchSpec::new("x86-64");
        let block = r2ssa::SSABlock {
            addr: 0x2000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                    a: r2ssa::SSAVar::new("rbp", 0, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                    val: r2ssa::SSAVar::new("rdi", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:arr", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("tmp:idx64", 1, 8),
                    src: r2ssa::SSAVar::new("esi", 0, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("tmp:scale", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:idx64", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:elem", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:arr", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:scale", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:val", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:elem", 1, 8),
                },
            ],
        };

        let hints = std::collections::HashMap::new();
        let vars = recover_vars_from_ssa(&[block], Some(&arch), &hints, true);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(
            arg0.var_type, "int32_t *",
            "spill/reload + scaled index should recover pointee width on arg0"
        );
    }

    #[test]
    fn recover_vars_usage_pointer_inference_handles_shift_scaled_index() {
        let arch = ArchSpec::new("x86-64");
        let block = r2ssa::SSABlock {
            addr: 0x2100,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                    a: r2ssa::SSAVar::new("rbp", 0, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                    val: r2ssa::SSAVar::new("rdi", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:arr", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("tmp:idx64", 1, 8),
                    src: r2ssa::SSAVar::new("esi", 0, 4),
                },
                r2ssa::SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("tmp:scale", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:idx64", 1, 8),
                    b: r2ssa::SSAVar::new("const:2", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:elem", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:arr", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:scale", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:val", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:elem", 1, 8),
                },
            ],
        };

        let hints = std::collections::HashMap::new();
        let vars = recover_vars_from_ssa(&[block], Some(&arch), &hints, true);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(
            arg0.var_type, "int32_t *",
            "shift-scaled index should recover pointee width on arg0"
        );
    }

    #[test]
    fn recover_vars_without_semantic_metadata_still_uses_structural_pointer_evidence() {
        let arch = ArchSpec::new("x86-64");
        let block = r2ssa::SSABlock {
            addr: 0x3000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:addr", 1, 8),
                    a: r2ssa::SSAVar::new("rdi", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:val", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:addr", 1, 8),
                },
            ],
        };

        let mut hints = std::collections::HashMap::new();
        merge_type_hint(&mut hints, "rdi".to_string(), TypeHint::pointer());
        let vars = recover_vars_from_ssa(&[block], Some(&arch), &hints, false);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(
            arg0.var_type, "void *",
            "structural SSA pointer evidence must remain active without semantic metadata"
        );
    }

    #[test]
    fn recover_vars_without_semantic_metadata_ignores_metadata_only_pointer_hint() {
        let arch = ArchSpec::new("x86-64");
        let block = r2ssa::SSABlock {
            addr: 0x3000,
            size: 4,
            ops: vec![r2ssa::SSAOp::Copy {
                dst: r2ssa::SSAVar::new("tmp:value", 1, 8),
                src: r2ssa::SSAVar::new("rdi", 0, 8),
            }],
        };

        let mut hints = std::collections::HashMap::new();
        merge_type_hint(&mut hints, "rdi".to_string(), TypeHint::pointer());
        let vars = recover_vars_from_ssa(&[block], Some(&arch), &hints, false);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(arg0.var_type, "int64_t");
    }

    #[test]
    fn recover_vars_safe_array_access_pattern_marks_rdi_pointer() {
        let arch = ArchSpec::new("x86-64");
        let blocks = vec![
            r2ssa::SSABlock {
                addr: 0x4014dc,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                        a: r2ssa::SSAVar::new("RBP", 0, 8),
                        b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("tmp:6b00", 1, 8),
                        src: r2ssa::SSAVar::new("RDI", 0, 8),
                    },
                    r2ssa::SSAOp::Store {
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                        val: r2ssa::SSAVar::new("tmp:6b00", 1, 8),
                    },
                ],
            },
            r2ssa::SSABlock {
                addr: 0x4014e0,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4600", 1, 8),
                        a: r2ssa::SSAVar::new("RBP", 0, 8),
                        b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("tmp:7000", 1, 4),
                        src: r2ssa::SSAVar::new("ESI", 0, 4),
                    },
                    r2ssa::SSAOp::Store {
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4600", 1, 8),
                        val: r2ssa::SSAVar::new("tmp:7000", 1, 4),
                    },
                ],
            },
            r2ssa::SSABlock {
                addr: 0x4014f7,
                size: 4,
                ops: vec![r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("EAX", 0, 4),
                }],
            },
            r2ssa::SSABlock {
                addr: 0x4014f9,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::IntMult {
                        dst: r2ssa::SSAVar::new("tmp:4c80", 1, 8),
                        a: r2ssa::SSAVar::new("RAX", 0, 8),
                        b: r2ssa::SSAVar::new("const:4", 0, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("RDX", 1, 8),
                        src: r2ssa::SSAVar::new("tmp:4c80", 1, 8),
                    },
                ],
            },
            r2ssa::SSABlock {
                addr: 0x401501,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                        a: r2ssa::SSAVar::new("RBP", 0, 8),
                        b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                    },
                    r2ssa::SSAOp::Load {
                        dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("RAX", 1, 8),
                        src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    },
                ],
            },
            r2ssa::SSABlock {
                addr: 0x401505,
                size: 4,
                ops: vec![r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("RDX", 0, 8),
                }],
            },
            r2ssa::SSABlock {
                addr: 0x401508,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::Load {
                        dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("RAX", 0, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("EAX", 1, 4),
                        src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    },
                    r2ssa::SSAOp::IntZExt {
                        dst: r2ssa::SSAVar::new("RAX", 1, 8),
                        src: r2ssa::SSAVar::new("EAX", 1, 4),
                    },
                ],
            },
        ];

        let hints = std::collections::HashMap::new();
        let vars = recover_vars_from_ssa(&blocks, Some(&arch), &hints, true);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(
            arg0.var_type, "void *",
            "safe-array style spill/reload indexed deref should type arr arg as pointer"
        );
        let arg1 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rsi"))
            .expect("rsi argument should be recovered");
        assert_ne!(
            arg1.var_type, "void *",
            "index argument should remain non-pointer in this pattern"
        );
    }

    #[test]
    fn recover_vars_safe_array_access_minimal_two_block_pattern_marks_rdi_pointer() {
        let arch = ArchSpec::new("x86-64");
        let blocks = vec![
            r2ssa::SSABlock {
                addr: 0x5000,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                        a: r2ssa::SSAVar::new("RBP", 1, 8),
                        b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("tmp:6b00", 1, 8),
                        src: r2ssa::SSAVar::new("RDI", 0, 8),
                    },
                    r2ssa::SSAOp::Store {
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                        val: r2ssa::SSAVar::new("tmp:6b00", 1, 8),
                    },
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                        a: r2ssa::SSAVar::new("RBP", 1, 8),
                        b: r2ssa::SSAVar::new("const:ffffffffffffffec", 0, 8),
                    },
                    r2ssa::SSAOp::Store {
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                        val: r2ssa::SSAVar::new("ESI", 0, 4),
                    },
                ],
            },
            r2ssa::SSABlock {
                addr: 0x5010,
                size: 4,
                ops: vec![
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4700", 9, 8),
                        a: r2ssa::SSAVar::new("RBP", 1, 8),
                        b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                    },
                    r2ssa::SSAOp::Load {
                        dst: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4700", 9, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("RAX", 4, 8),
                        src: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                    },
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4700", 10, 8),
                        a: r2ssa::SSAVar::new("RBP", 1, 8),
                        b: r2ssa::SSAVar::new("const:ffffffffffffffec", 0, 8),
                    },
                    r2ssa::SSAOp::Load {
                        dst: r2ssa::SSAVar::new("tmp:11f00", 5, 4),
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4700", 10, 8),
                    },
                    r2ssa::SSAOp::IntSExt {
                        dst: r2ssa::SSAVar::new("RCX", 2, 8),
                        src: r2ssa::SSAVar::new("tmp:11f00", 5, 4),
                    },
                    r2ssa::SSAOp::IntMult {
                        dst: r2ssa::SSAVar::new("tmp:4900", 2, 8),
                        a: r2ssa::SSAVar::new("RCX", 2, 8),
                        b: r2ssa::SSAVar::new("const:4", 0, 8),
                    },
                    r2ssa::SSAOp::IntAdd {
                        dst: r2ssa::SSAVar::new("tmp:4a00", 2, 8),
                        a: r2ssa::SSAVar::new("RAX", 4, 8),
                        b: r2ssa::SSAVar::new("tmp:4900", 2, 8),
                    },
                    r2ssa::SSAOp::Load {
                        dst: r2ssa::SSAVar::new("tmp:11f00", 6, 4),
                        space: "ram".to_string(),
                        addr: r2ssa::SSAVar::new("tmp:4a00", 2, 8),
                    },
                    r2ssa::SSAOp::Copy {
                        dst: r2ssa::SSAVar::new("EAX", 4, 4),
                        src: r2ssa::SSAVar::new("tmp:11f00", 6, 4),
                    },
                    r2ssa::SSAOp::IntZExt {
                        dst: r2ssa::SSAVar::new("RAX", 5, 8),
                        src: r2ssa::SSAVar::new("EAX", 4, 4),
                    },
                ],
            },
        ];

        let hints = std::collections::HashMap::new();
        let vars = recover_vars_from_ssa(&blocks, Some(&arch), &hints, true);
        let arg0 = vars
            .iter()
            .find(|v| v.reg.as_deref() == Some("rdi"))
            .expect("rdi argument should be recovered");
        assert_eq!(
            arg0.var_type, "int32_t *",
            "two-block spill/reload + scaled-index pattern should recover pointee width"
        );
    }

    #[test]
    fn signature_context_overrides_extend_empty_param_list() {
        let mut sig = InferredSignatureCcJson {
            function_name: "main".to_string(),
            signature: "int32_t main(void)".to_string(),
            ret_type: "int32_t".to_string(),
            params: Vec::new(),
            callconv: String::new(),
            arch: "aarch64".to_string(),
            confidence: 80,
            callconv_confidence: 0,
        };
        let merged = Some(r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 32,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![
                r2types::FunctionParamSpec {
                    name: "argc".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    }),
                },
                r2types::FunctionParamSpec {
                    name: "argv".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        })),
                    ))),
                },
            ],
        });

        apply_signature_context_overrides(&mut sig, merged.as_ref());

        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.params[0].name, "argc");
        assert_eq!(sig.params[0].param_type, "int32_t");
        assert_eq!(sig.params[1].name, "argv");
        assert_eq!(sig.params[1].param_type, "int8_t**");
    }

    #[test]
    fn scalar_register_family_key_merges_arm64_x_and_w_aliases() {
        assert_eq!(scalar_register_family_key("X0"), "aarch64:gpr:0");
        assert_eq!(scalar_register_family_key("w0"), "aarch64:gpr:0");
        assert_eq!(scalar_register_family_key("fp"), "aarch64:gpr:29");
        assert_eq!(scalar_register_family_key("lr"), "aarch64:gpr:30");
    }

    #[test]
    fn scalar_width_hints_narrow_arm64_x_family_from_w_family_usage() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("W8", 1, 4),
                    src: r2ssa::SSAVar::new("W0", 0, 4),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    src: r2ssa::SSAVar::new("W8", 1, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    a: r2ssa::SSAVar::new("X0", 0, 8),
                    b: r2ssa::SSAVar::new("const:1", 0, 8),
                },
            ],
        }];

        let evidence = collect_signature_type_evidence_context(&blocks);
        assert_eq!(
            evidence.width_bits.get("x0_0"),
            Some(&32),
            "{:?}",
            evidence.width_bits
        );
        assert_eq!(
            evidence.width_bits.get("x9_1"),
            Some(&32),
            "{:?}",
            evidence.width_bits
        );
        assert_eq!(
            evidence.width_bits.get("x10_1"),
            Some(&32),
            "{:?}",
            evidence.width_bits
        );
    }

    #[test]
    fn recover_vars_prefers_arm64_family_width_hint_for_wide_arg_carrier() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAnd {
                    dst: r2ssa::SSAVar::new("W9", 1, 4),
                    a: r2ssa::SSAVar::new("W0", 0, 4),
                    b: r2ssa::SSAVar::new("const:ff", 0, 4),
                },
            ],
        }];

        let arch = ArchSpec::new("aarch64");
        let vars = recover_vars_from_ssa(
            &blocks,
            Some(&arch),
            &std::collections::HashMap::new(),
            true,
        );
        let arg0 = vars.iter().find(|var| var.name == "arg0").expect("arg0");
        assert_eq!(arg0.var_type, "int32_t");
    }

    #[test]
    fn main_signature_override_is_canonical_and_caps_extra_params() {
        let mut sig = InferredSignatureCcJson {
            function_name: "main".to_string(),
            signature: "int32_t main(void)".to_string(),
            ret_type: "int32_t".to_string(),
            params: vec![InferredParamJson {
                name: "arg1".to_string(),
                param_type: "void *".to_string(),
            }],
            callconv: String::new(),
            arch: "aarch64".to_string(),
            confidence: 80,
            callconv_confidence: 0,
        };
        let mut merged = Some(r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 32,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![
                r2types::FunctionParamSpec {
                    name: "argc".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "argv".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "envp".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "arg_550h".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Signed,
                    }),
                },
            ],
        });

        apply_main_signature_override("sym._main", &mut sig, &mut merged);

        assert_eq!(
            sig.params
                .iter()
                .map(|param| (param.name.as_str(), param.param_type.as_str()))
                .collect::<Vec<_>>(),
            vec![("argc", "int"), ("argv", "int8_t**"), ("envp", "int8_t**"),]
        );
        let merged = merged.expect("main signature");
        assert_eq!(merged.params.len(), 3);
        assert_eq!(merged.params[0].name, "argc");
        assert_eq!(merged.params[1].name, "argv");
        assert_eq!(merged.params[2].name, "envp");
    }

    #[test]
    fn merge_register_type_hints_prefers_pointer_over_integer_aliases() {
        let mut metadata = std::collections::HashMap::new();
        merge_type_hint(
            &mut metadata,
            "edi".to_string(),
            TypeHint {
                rank: TypeHintRank::Integer,
                ty: "int32_t".to_string(),
            },
        );
        let mut usage = std::collections::HashMap::new();
        merge_type_hint(&mut usage, "rdi".to_string(), TypeHint::pointer());

        let merged = merge_register_type_hints(&metadata, &usage, X86_ARG_REGS);
        assert_eq!(
            merged.get("rdi").map(|hint| hint.ty.as_str()),
            Some("void *")
        );
        assert_eq!(
            merged.get("edi").map(|hint| hint.ty.as_str()),
            Some("void *")
        );
    }

    #[test]
    fn add_stack_var_upgrades_existing_slot_to_pointer_when_confident() {
        let mut vars = Vec::new();
        let mut seen_slots = std::collections::HashMap::new();
        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rbp",
            X86_FRAME_BASES,
            -8,
            8,
            None,
        );
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].var_type, "int64_t");

        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rbp",
            X86_FRAME_BASES,
            -8,
            8,
            Some("void *".to_string()),
        );
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].var_type, "void *");
    }

    #[test]
    fn add_stack_var_keeps_bp_and_sp_slots_distinct_at_same_offset() {
        let mut vars = Vec::new();
        let mut seen_slots = std::collections::HashMap::new();

        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rsp",
            X86_FRAME_BASES,
            -8,
            8,
            Some("void *".to_string()),
        );
        add_stack_var(
            &mut vars,
            &mut seen_slots,
            "rbp",
            X86_FRAME_BASES,
            -8,
            8,
            None,
        );

        assert_eq!(vars.len(), 2);
        assert!(
            vars.iter()
                .any(|var| var.kind == "s" && var.delta == -8 && var.var_type == "void *")
        );
        assert!(
            vars.iter()
                .any(|var| var.kind == "b" && var.delta == -8 && var.var_type == "int64_t")
        );
    }

    #[test]
    fn pointer_slot_evidence_marks_param_as_pointer_without_direct_overwrite() {
        let mut inferred_params = vec![r2types::SignatureParamCandidate {
            name: "arg1".to_string(),
            ty: r2types::CTypeLike::Int {
                bits: 64,
                signedness: r2types::Signedness::Signed,
            },
            arg_index: 1,
            size_bytes: 8,
            evidence: TypeEvidence::default(),
        }];
        let mut pointer_slots = std::collections::BTreeSet::new();
        pointer_slots.insert(0);

        merge_pointer_slot_evidence(&mut inferred_params, &pointer_slots);
        assert_eq!(
            inferred_params[0].evidence.pointer_proven, 1,
            "single-parameter fallback should contribute high-confidence pointer evidence"
        );
    }

    #[test]
    fn scalar_only_argument_evidence_prefers_integer_type() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAnd {
                    dst: r2ssa::SSAVar::new("tmp:masked", 1, 4),
                    a: r2ssa::SSAVar::new("esi", 0, 4),
                    b: r2ssa::SSAVar::new("const:ff", 0, 4),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("tmp:eq", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:masked", 1, 4),
                    b: r2ssa::SSAVar::new("const:0", 0, 4),
                },
            ],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let initial_ty = r2types::CTypeLike::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("esi", 0, 4),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 4, 64, &evidence);
        assert_eq!(ty, signed_type(32));
    }

    #[test]
    fn deref_argument_evidence_prefers_pointer_type() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1100,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:val", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("rdi", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("eax", 1, 4),
                    a: r2ssa::SSAVar::new("tmp:val", 1, 4),
                    b: r2ssa::SSAVar::new("const:1", 0, 4),
                },
            ],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let initial_ty = r2types::CTypeLike::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("rdi", 0, 8),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 8, 64, &evidence);
        assert_eq!(ty, void_ptr_type());
    }

    #[test]
    fn mixed_pointer_and_scalar_evidence_stays_conservative() {
        let evidence = TypeEvidence {
            pointer_proven: 1,
            scalar_likely: 1,
            ..TypeEvidence::default()
        };
        let ty = resolve_evidence_driven_type(r2types::CTypeLike::Unknown, 8, 64, &evidence);
        assert_eq!(ty, void_ptr_type());
    }

    #[test]
    fn bool_like_branch_only_argument_prefers_bool() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1200,
            size: 4,
            ops: vec![r2ssa::SSAOp::CBranch {
                target: r2ssa::SSAVar::new("const:1300", 0, 8),
                cond: r2ssa::SSAVar::new("dil", 0, 1),
            }],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let initial_ty = r2types::CTypeLike::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("dil", 0, 1),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 1, 64, &evidence);
        assert_eq!(ty, r2types::CTypeLike::Bool);
    }

    #[test]
    fn return_type_evidence_prefers_scalar_for_arithmetic_result() {
        let mut block = r2il::R2ILBlock::new(0x1300, 4);
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0x10, 4),
            a: r2il::Varnode::unique(0x20, 4),
            b: r2il::Varnode::constant(1, 4),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::unique(0x10, 4),
        });
        let func = r2ssa::SSAFunction::from_blocks_with_arch(&[block], None).expect("ssa function");
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1300,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:10", 1, 4),
                    a: r2ssa::SSAVar::new("tmp:20", 0, 4),
                    b: r2ssa::SSAVar::new("const:1", 0, 4),
                },
                r2ssa::SSAOp::Return {
                    target: r2ssa::SSAVar::new("tmp:10", 1, 4),
                },
            ],
        }];
        let evidence_ctx = collect_signature_type_evidence_context(&blocks);
        let mut type_inference = r2types::TypeInference::new(64);
        type_inference.infer_function(&func);
        let (ret_ty, _) = infer_signature_return_type(&func, &type_inference, 64, &evidence_ctx);
        assert_eq!(
            ret_ty,
            r2types::CTypeLike::Int {
                bits: 32,
                signedness: r2types::Signedness::Unknown,
            }
        );
    }

    #[test]
    fn recover_vars_profile_covers_arm64_arm32_and_mips() {
        let arm64 = ArchSpec::new("aarch64");
        let (arm64_args, _, _) = recover_vars_arch_profile(Some(&arm64));
        assert_eq!(arm64_args.len(), 8, "arm64 should expose x0..x7 args");
        assert_eq!(arm64_args[0].0, "x0");
        assert!(arm64_args[0].1.contains(&"w0"));

        let arm32 = ArchSpec::new("arm");
        let (arm32_args, _, _) = recover_vars_arch_profile(Some(&arm32));
        assert_eq!(arm32_args.len(), 4, "arm32 should expose r0..r3 args");
        assert_eq!(arm32_args[3].0, "r3");

        let mips = ArchSpec::new("mips");
        let (mips_args, _, _) = recover_vars_arch_profile(Some(&mips));
        assert_eq!(mips_args.len(), 4, "mips should expose a0..a3 args");
        assert!(mips_args[0].1.contains(&"$a0"));
    }

    #[test]
    fn function_artifact_cache_key_distinguishes_symbolic_scope() {
        let arch = ArchSpec::new("x86-64");
        let root_blocks = const_return_blocks(0x1000, 0);
        let helper_a_blocks = const_return_blocks(0x2000, 1);
        let helper_b_blocks = const_return_blocks(0x2000, 2);

        let root_prepared =
            r2ssa::SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic ssa");
        let helper_a_prepared = r2ssa::SsaArtifact::for_symbolic(&helper_a_blocks, Some(&arch))
            .expect("helper a symbolic ssa");
        let helper_b_prepared = r2ssa::SsaArtifact::for_symbolic(&helper_b_blocks, Some(&arch))
            .expect("helper b symbolic ssa");

        let scope_a = r2sym::PreparedFunctionScope::new(
            0x1000,
            vec![
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root_prepared.clone(),
                },
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x2000),
                    name: Some("helper".to_string()),
                    prepared: helper_a_prepared,
                },
            ],
        )
        .expect("scope a");
        let scope_b = r2sym::PreparedFunctionScope::new(
            0x1000,
            vec![
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root_prepared,
                },
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x2000),
                    name: Some("helper".to_string()),
                    prepared: helper_b_prepared,
                },
            ],
        )
        .expect("scope b");
        let interproc_hash = empty_interproc_hash();

        let key_without_scope = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            interproc_hash,
            1,
            None,
        )
        .expect("root-only cache key");
        let key_a = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            interproc_hash,
            1,
            Some(&scope_a),
        )
        .expect("scoped cache key a");
        let key_a_repeat = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            interproc_hash,
            1,
            Some(&scope_a),
        )
        .expect("scoped cache key a repeat");
        let key_b = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            interproc_hash,
            1,
            Some(&scope_b),
        )
        .expect("scoped cache key b");

        assert_eq!(
            key_a, key_a_repeat,
            "same symbolic scope should hash stably"
        );
        assert_ne!(
            key_without_scope, key_a,
            "scope-aware artifacts must not alias the root-only cache key"
        );
        assert_ne!(
            key_a, key_b,
            "different helper closures must not alias the same artifact cache entry"
        );
    }

    #[test]
    fn function_artifact_cache_key_distinguishes_function_name() {
        let arch = ArchSpec::new("x86-64");
        let blocks = const_return_blocks(0x1000, 0);
        let interproc_hash = empty_interproc_hash();
        let first = function_artifact_cache_key_parts(
            "sym.first",
            Some(&arch),
            &blocks,
            true,
            "{}",
            interproc_hash,
            1,
            None,
        )
        .expect("first cache key");
        let second = function_artifact_cache_key_parts(
            "sym.second",
            Some(&arch),
            &blocks,
            true,
            "{}",
            interproc_hash,
            1,
            None,
        )
        .expect("second cache key");

        assert_ne!(
            first, second,
            "name-sensitive writeback artifacts must not alias across functions"
        );
    }

    #[test]
    fn function_artifact_cache_key_distinguishes_interproc_iteration_budget() {
        let arch = ArchSpec::new("x86-64");
        let blocks = const_return_blocks(0x1000, 0);
        let scope_hash = interproc_scope_facts_from_seed_entries([(
            0x2000,
            Some("sym.imp.malloc".to_string()),
            Some(1),
        )])
        .identity_hash();
        let first = function_artifact_cache_key_parts(
            "sym.root",
            Some(&arch),
            &blocks,
            true,
            "{}",
            scope_hash,
            1,
            None,
        )
        .expect("low budget cache key");
        let second = function_artifact_cache_key_parts(
            "sym.root",
            Some(&arch),
            &blocks,
            true,
            "{}",
            scope_hash,
            4,
            None,
        )
        .expect("high budget cache key");

        assert_ne!(
            first, second,
            "interproc summary artifacts must invalidate when the fixpoint budget changes"
        );
    }

    #[test]
    fn function_artifact_cache_key_uses_typed_context_identity() {
        let arch = ArchSpec::new("x86-64");
        let blocks = const_return_blocks(0x1000, 0);
        let first_context = r#"{"context":{"schema_version":1,"dirty_epoch":7,"context_hash":42},"signature":{"name":"sym.root"}}"#;
        let reordered_context = r#"{"signature":{"name":"sym.root"},"context":{"context_hash":42,"dirty_epoch":7,"schema_version":1}}"#;
        let changed_epoch_context = r#"{"context":{"schema_version":1,"dirty_epoch":8,"context_hash":42},"signature":{"name":"sym.root"}}"#;
        let changed_type_epoch_context = r#"{"context":{"schema_version":1,"dirty_epoch":7,"type_dirty_epoch":2,"context_hash":42},"signature":{"name":"sym.root"}}"#;
        let interproc_hash = empty_interproc_hash();

        let first = function_artifact_cache_key_parts(
            "sym.root",
            Some(&arch),
            &blocks,
            true,
            first_context,
            interproc_hash,
            1,
            None,
        )
        .expect("first cache key");
        let reordered = function_artifact_cache_key_parts(
            "sym.root",
            Some(&arch),
            &blocks,
            true,
            reordered_context,
            interproc_hash,
            1,
            None,
        )
        .expect("reordered cache key");
        let changed_epoch = function_artifact_cache_key_parts(
            "sym.root",
            Some(&arch),
            &blocks,
            true,
            changed_epoch_context,
            interproc_hash,
            1,
            None,
        )
        .expect("changed epoch cache key");
        let changed_type_epoch = function_artifact_cache_key_parts(
            "sym.root",
            Some(&arch),
            &blocks,
            true,
            changed_type_epoch_context,
            interproc_hash,
            1,
            None,
        )
        .expect("changed type epoch cache key");

        assert_eq!(
            first, reordered,
            "typed radare2 context identity should avoid raw JSON order sensitivity"
        );
        assert_ne!(
            first, changed_epoch,
            "dirty epoch must invalidate cached session facts"
        );
        assert_ne!(
            first, changed_type_epoch,
            "global type epoch must invalidate cached session facts"
        );
    }

    #[test]
    fn function_artifact_cache_key_distinguishes_function_address() {
        let arch = ArchSpec::new("x86-64");
        let blocks = const_return_blocks(0x1000, 0);
        let interproc_hash = empty_interproc_hash();
        let first = function_artifact_cache_key_parts_hashed(
            "sym.root",
            0x1000,
            Some(&arch),
            &blocks,
            true,
            session_context_identity_hash("{}", 64),
            0,
            interproc_hash,
            1,
            None,
        )
        .expect("first cache key");
        let second = function_artifact_cache_key_parts_hashed(
            "sym.root",
            0x2000,
            Some(&arch),
            &blocks,
            true,
            session_context_identity_hash("{}", 64),
            0,
            interproc_hash,
            1,
            None,
        )
        .expect("second cache key");

        assert_ne!(
            first, second,
            "session artifact cache entries must not alias across function addresses"
        );
    }
}
