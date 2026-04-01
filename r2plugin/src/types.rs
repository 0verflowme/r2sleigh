#[cfg(test)]
use crate::InferredParam;
use crate::blocks::BlockSlice;
use crate::context::{PluginCtxView, require_ctx_view};
use crate::decompiler::build_decompiler_env;
use crate::helpers::{effective_ptr_bits, resolve_function_name};
use crate::{
    ArchSpec, Disassembler, InferredParamJson, InferredSignatureCcJson, R2ILBlock, R2ILContext,
};
use std::collections::{BTreeMap, HashMap};
use std::ffi::CString;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::{self, Write};
use std::os::raw::c_char;
use std::ptr;
use std::sync::{Arc, OnceLock, RwLock};

const ANALYSIS_CACHE_LIMIT: usize = 256;

fn should_reuse_decompile_ssa_for_pattern_analysis(prepared: &r2ssa::SsaArtifact) -> bool {
    let summary = prepared.function().cfg_risk_summary();
    summary.block_count >= 96
        && summary.switch_block_count > 0
        && summary.max_switch_cases >= 32
        && summary.back_edge_count == 0
}

pub(crate) struct FunctionInput<'a> {
    pub(crate) ctx: PluginCtxView<'a>,
    pub(crate) blocks: BlockSlice,
    pub(crate) function_addr: u64,
    pub(crate) function_name: String,
}

#[derive(Clone)]
pub(crate) struct FunctionAnalysis {
    pub(crate) ssa_func: r2ssa::SsaArtifact,
    pub(crate) pattern_ssa_func: r2ssa::SsaArtifact,
}

#[derive(Clone)]
pub(crate) struct FunctionAnalysisArtifact {
    pub(crate) ssa_func: r2ssa::SsaArtifact,
    pub(crate) pattern_ssa_func: r2ssa::SsaArtifact,
    pub(crate) function_facts: r2types::FunctionFacts,
    pub(crate) writeback_plan: r2types::TypeWritebackPlan,
    pub(crate) interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionAnalysisCacheKey {
    arch_hash: u64,
    blocks_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionArtifactCacheKey {
    analysis: FunctionAnalysisCacheKey,
    semantic_metadata_enabled: bool,
    external_context_hash: u64,
    interproc_scope_hash: u64,
    symbolic_scope_hash: u64,
}

struct HasherWriter<'a, H: Hasher>(&'a mut H);

impl<H: Hasher> Write for HasherWriter<'_, H> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn hash_json_value<T: serde::Serialize>(value: &T) -> Option<u64> {
    let mut hasher = DefaultHasher::new();
    let mut writer = HasherWriter(&mut hasher);
    serde_json::to_writer(&mut writer, value).ok()?;
    Some(hasher.finish())
}

fn hash_optional_arch(arch: Option<&ArchSpec>) -> u64 {
    arch.and_then(hash_json_value).unwrap_or(0)
}

fn hash_string_payload(payload: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    payload.hash(&mut hasher);
    hasher.finish()
}

fn function_analysis_cache_key_parts(
    _function_name: &str,
    arch: Option<&ArchSpec>,
    blocks: &[R2ILBlock],
) -> Option<FunctionAnalysisCacheKey> {
    Some(FunctionAnalysisCacheKey {
        arch_hash: hash_optional_arch(arch),
        blocks_hash: hash_json_value(&blocks)?,
    })
}

fn function_artifact_cache_key_parts(
    function_name: &str,
    arch: Option<&ArchSpec>,
    blocks: &[R2ILBlock],
    semantic_metadata_enabled: bool,
    external_context_json: &str,
    interproc_scope_json: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionArtifactCacheKey> {
    Some(FunctionArtifactCacheKey {
        analysis: function_analysis_cache_key_parts(function_name, arch, blocks)?,
        semantic_metadata_enabled,
        external_context_hash: hash_string_payload(external_context_json),
        interproc_scope_hash: hash_string_payload(interproc_scope_json),
        symbolic_scope_hash: r2sym::stable_scope_hash(symbolic_scope),
    })
}

fn analysis_cache() -> &'static RwLock<HashMap<FunctionAnalysisCacheKey, Arc<FunctionAnalysis>>> {
    static CACHE: OnceLock<RwLock<HashMap<FunctionAnalysisCacheKey, Arc<FunctionAnalysis>>>> =
        OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

fn artifact_cache()
-> &'static RwLock<HashMap<FunctionArtifactCacheKey, Arc<FunctionAnalysisArtifact>>> {
    static CACHE: OnceLock<
        RwLock<HashMap<FunctionArtifactCacheKey, Arc<FunctionAnalysisArtifact>>>,
    > = OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

fn cache_insert_bounded<K, V>(cache: &RwLock<HashMap<K, Arc<V>>>, key: K, value: Arc<V>)
where
    K: Eq + Hash,
{
    let mut guard = cache.write().expect("plugin cache write lock poisoned");
    if guard.len() >= ANALYSIS_CACHE_LIMIT {
        guard.clear();
    }
    guard.insert(key, value);
}

fn rename_function_analysis(analysis: FunctionAnalysis, function_name: &str) -> FunctionAnalysis {
    let FunctionAnalysis {
        ssa_func,
        pattern_ssa_func,
    } = analysis;
    FunctionAnalysis {
        ssa_func: ssa_func.with_name(function_name),
        pattern_ssa_func: pattern_ssa_func.with_name(function_name),
    }
}

fn rename_function_analysis_artifact(
    artifact: FunctionAnalysisArtifact,
    function_name: &str,
) -> FunctionAnalysisArtifact {
    let FunctionAnalysisArtifact {
        ssa_func,
        pattern_ssa_func,
        function_facts,
        writeback_plan,
        interproc_summary_set,
    } = artifact;
    FunctionAnalysisArtifact {
        ssa_func: ssa_func.with_name(function_name),
        pattern_ssa_func: pattern_ssa_func.with_name(function_name),
        function_facts,
        writeback_plan,
        interproc_summary_set,
    }
}

#[cfg(test)]
fn type_like_to_ctype(ty: &r2types::CTypeLike) -> r2dec::CType {
    match ty {
        r2types::CTypeLike::Void => r2dec::CType::Void,
        r2types::CTypeLike::Bool => r2dec::CType::Bool,
        r2types::CTypeLike::Int { bits, signedness } => match signedness {
            r2types::Signedness::Unsigned => r2dec::CType::UInt(*bits),
            r2types::Signedness::Signed | r2types::Signedness::Unknown => r2dec::CType::Int(*bits),
        },
        r2types::CTypeLike::Float(bits) => r2dec::CType::Float(*bits),
        r2types::CTypeLike::Pointer(inner) => {
            r2dec::CType::Pointer(Box::new(type_like_to_ctype(inner)))
        }
        r2types::CTypeLike::Array(inner, len) => {
            r2dec::CType::Array(Box::new(type_like_to_ctype(inner)), *len)
        }
        r2types::CTypeLike::Struct(name) => r2dec::CType::Struct(name.clone()),
        r2types::CTypeLike::Union(name) => r2dec::CType::Union(name.clone()),
        r2types::CTypeLike::Enum(name) => r2dec::CType::Enum(name.clone()),
        r2types::CTypeLike::Function | r2types::CTypeLike::Unknown => r2dec::CType::Unknown,
    }
}

pub(crate) fn signature_to_json(sig: &r2types::InferredSignature) -> InferredSignatureCcJson {
    InferredSignatureCcJson {
        function_name: sig.function_name.clone(),
        signature: sig.signature.clone(),
        ret_type: sig.ret_type.clone(),
        params: sig
            .params
            .iter()
            .map(|param| InferredParamJson {
                name: param.name.clone(),
                param_type: param.param_type.clone(),
            })
            .collect(),
        callconv: sig.callconv.clone(),
        arch: sig.arch.clone(),
        confidence: sig.confidence,
        callconv_confidence: sig.callconv_confidence,
    }
}

pub(crate) type VarProt = r2types::RecoveredVariable;
pub(crate) type TypeHintRank = r2types::TypeHintRank;
pub(crate) type TypeHint = r2types::TypeHint;

fn var_prot_to_writeback(var: &VarProt) -> r2types::RecoveredVariable {
    var.clone()
}

fn local_field_accesses_to_writeback(
    accesses: Vec<r2dec::LocalStructFieldAccess>,
) -> Vec<r2types::LocalFieldAccessFact> {
    accesses
        .into_iter()
        .map(|access| r2types::LocalFieldAccessFact {
            slot: access.arg_index,
            field_offset: access.field_offset,
            field_name: format!("f_{:x}", access.field_offset),
            field_type: Some(r2types::size_to_type(access.access_size)),
        })
        .collect()
}

fn recovered_signature_params_from_var_recovery(
    params: Vec<&r2dec::variable::VarInfo>,
) -> Vec<r2types::RecoveredSignatureParam> {
    params
        .into_iter()
        .map(|param| r2types::RecoveredSignatureParam {
            name: param.name.clone(),
            ssa_var: param.ssa_var.clone(),
            initial_ty: crate::ctype_to_type_like(&param.ty),
        })
        .collect()
}

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
        function_addr: fcn_addr,
        function_name: resolve_function_name(fcn_addr, fcn_name),
    })
}

fn function_artifact_cache_key(
    input: &FunctionInput<'_>,
    external_context_json: &str,
    interproc_scope_json: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionArtifactCacheKey> {
    function_artifact_cache_key_parts(
        &input.function_name,
        input.ctx.arch,
        input.blocks.as_slice(),
        input.ctx.semantic_metadata_enabled,
        external_context_json,
        interproc_scope_json,
        symbolic_scope,
    )
}

pub(crate) fn build_function_analysis_from_parts(
    function_name: &str,
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
) -> Option<FunctionAnalysis> {
    let cache_key = function_analysis_cache_key_parts(function_name, arch, blocks)?;
    if let Some(cached) = analysis_cache()
        .read()
        .expect("plugin cache read lock poisoned")
        .get(&cache_key)
        .cloned()
    {
        return Some(rename_function_analysis((*cached).clone(), function_name));
    }

    let ssa_func = r2ssa::SsaArtifact::for_decompile(blocks, arch)?.with_name(function_name);
    let pattern_ssa_func = if should_reuse_decompile_ssa_for_pattern_analysis(&ssa_func) {
        ssa_func.clone()
    } else {
        r2ssa::SsaArtifact::for_patterns(blocks, arch)?.with_name(function_name)
    };
    let analysis = FunctionAnalysis {
        ssa_func,
        pattern_ssa_func,
    };
    cache_insert_bounded(analysis_cache(), cache_key, Arc::new(analysis.clone()));
    Some(rename_function_analysis(analysis, function_name))
}

pub(crate) fn build_function_analysis(input: &FunctionInput<'_>) -> Option<FunctionAnalysis> {
    build_function_analysis_from_parts(
        &input.function_name,
        input.blocks.as_slice(),
        input.ctx.arch,
    )
}

pub(crate) fn collect_detached_semantic_artifact(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&ArchSpec>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<r2sym::SemanticArtifact> {
    let analysis = build_function_analysis_from_parts(function_name, blocks, arch)?;
    Some(r2sym::compile_semantic_artifact_default_with_scope(
        &z3::Context::thread_local(),
        &analysis.ssa_func,
        symbolic_scope,
        arch,
    ))
}

#[derive(Debug, Clone, Default, serde::Deserialize)]
struct InterprocScopeSeedNameJson {
    id: u64,
    name: String,
}

#[derive(Debug, Clone, Default, serde::Deserialize)]
struct InterprocScopeInputJson {
    #[serde(default)]
    summaries: Vec<r2ssa::FunctionSemanticSummary>,
    #[serde(default)]
    seeds: Vec<InterprocScopeSeedNameJson>,
    #[serde(default)]
    payloads: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Default, serde::Deserialize)]
struct InterprocScopeSignaturePayloadJson {
    #[serde(default)]
    function_name: String,
    #[serde(default)]
    params: Vec<serde_json::Value>,
}

fn parse_interproc_seed_summaries(
    scope_json: &str,
) -> BTreeMap<r2ssa::InterprocFunctionId, r2ssa::FunctionSemanticSummary> {
    let Ok(scope) = serde_json::from_str::<InterprocScopeInputJson>(scope_json) else {
        return BTreeMap::new();
    };
    let mut seeds = BTreeMap::new();

    for summary in scope.summaries {
        seeds.insert(summary.id, summary);
    }
    for payload in scope.payloads {
        let Some(interproc) = payload.get("interproc") else {
            continue;
        };
        let Some(summary_value) = interproc.get("summary") else {
            continue;
        };
        let Ok(mut summary) =
            serde_json::from_value::<r2ssa::FunctionSemanticSummary>(summary_value.clone())
        else {
            continue;
        };
        if payload.get("params").is_some()
            && let Ok(signature) =
                serde_json::from_value::<InterprocScopeSignaturePayloadJson>(payload.clone())
            && !signature.function_name.trim().is_empty()
        {
            summary.arg_count_hint = Some(signature.params.len());
        }
        seeds.insert(summary.id, summary);
    }
    for seed in scope.seeds {
        let id = r2ssa::InterprocFunctionId(seed.id);
        if let Some(summary) = r2ssa::FunctionSemanticSummary::seed_for_name(id, &seed.name) {
            seeds.insert(id, summary);
        } else {
            seeds
                .entry(id)
                .or_insert_with(|| r2ssa::FunctionSemanticSummary::unknown(id, Some(seed.name)));
        }
    }

    seeds
}

pub(crate) fn build_interproc_summary_set(
    input: &FunctionInput<'_>,
    analysis: &FunctionAnalysis,
    scope_json: &str,
    max_iterations: usize,
) -> r2ssa::InterprocSummarySet {
    let root = r2ssa::InterprocFunctionId(input.function_addr);
    let seeds = parse_interproc_seed_summaries(scope_json);
    r2ssa::solve_interproc_summary_set(
        &[r2ssa::InterprocFunctionInput {
            id: root,
            name: Some(input.function_name.clone()),
            prepared: &analysis.ssa_func,
        }],
        input.ctx.arch,
        Some(root),
        &seeds,
        r2ssa::InterprocSolveConfig {
            max_iterations: max_iterations.max(1),
        },
    )
}

pub(crate) fn infer_signature_cc_from_analysis(
    input: &FunctionInput<'_>,
    analysis: &FunctionAnalysis,
) -> Option<r2types::InferredSignature> {
    let env = build_decompiler_env(&input.ctx);
    let pattern_ssa_blocks = analysis.pattern_ssa_func.local_ssa_blocks();

    let mut var_recovery =
        r2dec::VariableRecovery::new(&env.cfg.sp_name, &env.cfg.fp_name, env.cfg.ptr_size);
    var_recovery.recover(&analysis.ssa_func);

    let pointer_arg_slots = if input.ctx.semantic_metadata_enabled {
        let reg_type_hints = collect_register_type_hints(input.blocks.as_slice(), input.ctx.disasm);
        let recovered_vars =
            recover_vars_from_ssa(&pattern_ssa_blocks, input.ctx.arch, &reg_type_hints, true);
        collect_pointer_arg_slots(&recovered_vars)
    } else {
        std::collections::BTreeSet::new()
    };
    let recovered_params = recovered_signature_params_from_var_recovery(var_recovery.parameters());

    Some(r2types::infer_signature_from_prepared_ssa(
        &input.function_name,
        &env.arch_name,
        env.ptr_bits,
        &analysis.ssa_func,
        &pattern_ssa_blocks,
        &recovered_params,
        &pointer_arg_slots,
    ))
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
                .map(|ty| type_like_to_ctype(ty).to_string())
                .unwrap_or_else(|| "void *".to_string());
            sig.params.push(InferredParamJson {
                name: format!("arg{}", idx + 1),
                param_type,
            });
        }
        if let Some(ret_ty) = signature.ret_type.as_ref() {
            let ret_ty = type_like_to_ctype(ret_ty);
            let ret_ty_str = ret_ty.to_string();
            if !matches!(ret_ty, r2dec::CType::Unknown) {
                sig.ret_type = ret_ty_str;
            }
        }
        for (idx, param) in signature.params.iter().enumerate() {
            if let Some(ty) = param.ty.as_ref() {
                let ty_str = type_like_to_ctype(ty).to_string();
                param_types.insert(idx, ty_str.clone());
                if !matches!(type_like_to_ctype(ty), r2dec::CType::Unknown)
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
    if !r2types::is_c_main_function(function_name) {
        return;
    }

    let main_signature = r2types::canonical_main_signature_spec();
    signature_cc.ret_type = main_signature
        .ret_type
        .as_ref()
        .map(|ty| type_like_to_ctype(ty).to_string())
        .unwrap_or_else(|| "int32_t".to_string());
    signature_cc.params = main_signature
        .params
        .iter()
        .map(|param| InferredParamJson {
            name: param.name.clone(),
            param_type: param
                .ty
                .as_ref()
                .map(|ty| type_like_to_ctype(ty).to_string())
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

pub(crate) fn build_function_analysis_artifact_from_analysis_with_semantic_artifact(
    input: &FunctionInput<'_>,
    analysis: FunctionAnalysis,
    external_context_json: &str,
    interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    semantic_artifact: r2sym::SemanticArtifact,
) -> Option<FunctionAnalysisArtifact> {
    let ptr_bits = input
        .ctx
        .arch
        .as_ref()
        .map(|arch| effective_ptr_bits(arch))
        .unwrap_or(64);
    let signature = infer_signature_cc_from_analysis(input, &analysis)?;
    let parsed_context = r2types::parse_external_context_json(external_context_json, ptr_bits);

    let pattern_ssa_blocks = analysis.pattern_ssa_func.local_ssa_blocks();
    let decompiler_env = build_decompiler_env(&input.ctx);
    let decompiler_cfg = decompiler_env.cfg;
    let mut diagnostics = r2types::TypeWritebackDiagnostics::default();
    let local_structs = r2types::infer_local_struct_artifacts_from_ssa(
        &pattern_ssa_blocks,
        Some(decompiler_env.arch_name.as_str()),
        ptr_bits,
        &mut diagnostics,
    );
    let local_field_accesses = local_field_accesses_to_writeback(
        r2dec::infer_local_struct_field_accesses(&analysis.pattern_ssa_func, &decompiler_cfg),
    );
    let reg_type_hints = if input.ctx.semantic_metadata_enabled {
        collect_register_type_hints(input.blocks.as_slice(), input.ctx.disasm)
    } else {
        std::collections::HashMap::new()
    };
    let vars = recover_vars_from_ssa(
        &pattern_ssa_blocks,
        input.ctx.arch,
        &reg_type_hints,
        input.ctx.semantic_metadata_enabled,
    );
    let recovered_vars = vars.iter().map(var_prot_to_writeback).collect::<Vec<_>>();
    let writeback = r2types::build_type_writeback_analysis_with_semantics(
        r2types::TypeWritebackAnalysisInput {
            function_name: &input.function_name,
            ptr_bits,
            inferred_signature: signature.clone(),
            recovered_vars: &recovered_vars,
            ssa_blocks: &pattern_ssa_blocks,
            parsed_context,
            local_structs,
            interproc_summary_set: interproc_summary_set.clone(),
            diagnostics,
        },
        r2types::TypeWritebackSemanticInputs {
            artifact: &semantic_artifact,
            local_field_accesses: &local_field_accesses,
        },
    );
    Some(FunctionAnalysisArtifact {
        ssa_func: analysis.ssa_func,
        pattern_ssa_func: analysis.pattern_ssa_func,
        function_facts: writeback.function_facts,
        writeback_plan: writeback.plan,
        interproc_summary_set,
    })
}

pub(crate) fn build_function_analysis_artifact_from_analysis(
    input: &FunctionInput<'_>,
    analysis: FunctionAnalysis,
    external_context_json: &str,
    interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionAnalysisArtifact> {
    let semantic_artifact = r2sym::compile_semantic_artifact_default_with_scope(
        &z3::Context::thread_local(),
        &analysis.ssa_func,
        symbolic_scope,
        input.ctx.arch,
    );
    build_function_analysis_artifact_from_analysis_with_semantic_artifact(
        input,
        analysis,
        external_context_json,
        interproc_summary_set,
        semantic_artifact,
    )
}

#[allow(dead_code)]
pub(crate) fn build_function_analysis_artifact(
    input: &FunctionInput<'_>,
    external_context_json: &str,
    interproc_scope_json: &str,
    interproc_max_iterations: usize,
) -> Option<FunctionAnalysisArtifact> {
    build_function_analysis_artifact_with_scope(
        input,
        external_context_json,
        interproc_scope_json,
        interproc_max_iterations,
        None,
    )
}

pub(crate) fn build_function_analysis_artifact_with_scope(
    input: &FunctionInput<'_>,
    external_context_json: &str,
    interproc_scope_json: &str,
    interproc_max_iterations: usize,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionAnalysisArtifact> {
    let cache_key = function_artifact_cache_key(
        input,
        external_context_json,
        interproc_scope_json,
        symbolic_scope,
    );
    if let Some(cache_key) = cache_key.as_ref()
        && let Some(cached) = artifact_cache()
            .read()
            .expect("plugin cache read lock poisoned")
            .get(cache_key)
            .cloned()
    {
        return Some(rename_function_analysis_artifact(
            (*cached).clone(),
            &input.function_name,
        ));
    }

    let analysis = build_function_analysis(input)?;
    let interproc_summary_set = build_interproc_summary_set(
        input,
        &analysis,
        interproc_scope_json,
        interproc_max_iterations,
    );
    let artifact = build_function_analysis_artifact_from_analysis(
        input,
        analysis,
        external_context_json,
        Some(interproc_summary_set),
        symbolic_scope,
    )?;
    if let Some(cache_key) = cache_key {
        cache_insert_bounded(artifact_cache(), cache_key, Arc::new(artifact.clone()));
    }
    Some(rename_function_analysis_artifact(
        artifact,
        &input.function_name,
    ))
}

pub(crate) fn get_cached_function_analysis_artifact_with_scope(
    input: &FunctionInput<'_>,
    external_context_json: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<FunctionAnalysisArtifact> {
    let cache_key =
        function_artifact_cache_key(input, external_context_json, "{}", symbolic_scope)?;
    artifact_cache()
        .read()
        .expect("plugin cache read lock poisoned")
        .get(&cache_key)
        .cloned()
        .map(|artifact| {
            rename_function_analysis_artifact((*artifact).clone(), &input.function_name)
        })
}

pub(crate) fn alias_cached_function_analysis_artifact(
    input: &FunctionInput<'_>,
    source_external_context_json: &str,
    target_external_context_json: &str,
) -> bool {
    let Some(source_key) =
        function_artifact_cache_key(input, source_external_context_json, "{}", None)
    else {
        return false;
    };
    let Some(target_key) =
        function_artifact_cache_key(input, target_external_context_json, "{}", None)
    else {
        return false;
    };
    let Some(cached) = artifact_cache()
        .read()
        .expect("plugin cache read lock poisoned")
        .get(&source_key)
        .cloned()
    else {
        return false;
    };
    cache_insert_bounded(artifact_cache(), target_key, cached);
    true
}

#[allow(dead_code)]
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
    let cache_key = function_artifact_cache_key_parts(
        function_name,
        arch,
        blocks,
        semantic_metadata_enabled,
        external_context_json,
        "{}",
        symbolic_scope,
    );
    if let Some(cache_key) = cache_key.as_ref()
        && let Some(cached) = artifact_cache()
            .read()
            .expect("plugin cache read lock poisoned")
            .get(cache_key)
            .cloned()
    {
        return Some(rename_function_analysis_artifact(
            (*cached).clone(),
            function_name,
        ));
    }

    let analysis = build_function_analysis_from_parts(function_name, blocks, arch)?;
    let pattern_ssa_blocks = analysis.pattern_ssa_func.local_ssa_blocks();

    let (arch_name, _, cfg) = r2dec::DecompilerConfig::for_arch(arch);
    let mut var_recovery = r2dec::VariableRecovery::new(&cfg.sp_name, &cfg.fp_name, cfg.ptr_size);
    var_recovery.recover(&analysis.ssa_func);
    let pointer_arg_slots = if semantic_metadata_enabled {
        let recovered_vars = recover_vars_from_ssa(&pattern_ssa_blocks, arch, reg_type_hints, true);
        collect_pointer_arg_slots(&recovered_vars)
    } else {
        std::collections::BTreeSet::new()
    };
    let recovered_params = recovered_signature_params_from_var_recovery(var_recovery.parameters());
    let signature = r2types::infer_signature_from_prepared_ssa(
        function_name,
        &arch_name,
        ptr_bits,
        &analysis.ssa_func,
        &pattern_ssa_blocks,
        &recovered_params,
        &pointer_arg_slots,
    );
    let parsed_context = r2types::parse_external_context_json(external_context_json, ptr_bits);

    let mut diagnostics = r2types::TypeWritebackDiagnostics::default();
    let local_structs = r2types::infer_local_struct_artifacts_from_ssa(
        &pattern_ssa_blocks,
        Some(arch_name.as_str()),
        ptr_bits,
        &mut diagnostics,
    );
    let local_field_accesses = local_field_accesses_to_writeback(
        r2dec::infer_local_struct_field_accesses(&analysis.pattern_ssa_func, &cfg),
    );
    let semantic_artifact = precomputed_semantic_artifact.unwrap_or_else(|| {
        r2sym::compile_semantic_artifact_default_with_scope(
            &z3::Context::thread_local(),
            &analysis.ssa_func,
            symbolic_scope,
            arch,
        )
    });
    let vars = recover_vars_from_ssa(
        &pattern_ssa_blocks,
        arch,
        reg_type_hints,
        semantic_metadata_enabled,
    );
    let recovered_vars = vars.iter().map(var_prot_to_writeback).collect::<Vec<_>>();
    let writeback = r2types::build_type_writeback_analysis_with_semantics(
        r2types::TypeWritebackAnalysisInput {
            function_name,
            ptr_bits,
            inferred_signature: signature.clone(),
            recovered_vars: &recovered_vars,
            ssa_blocks: &pattern_ssa_blocks,
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics,
        },
        r2types::TypeWritebackSemanticInputs {
            artifact: &semantic_artifact,
            local_field_accesses: &local_field_accesses,
        },
    );
    let artifact = FunctionAnalysisArtifact {
        ssa_func: analysis.ssa_func,
        pattern_ssa_func: analysis.pattern_ssa_func,
        function_facts: writeback.function_facts,
        writeback_plan: writeback.plan,
        interproc_summary_set: None,
    };
    if let Some(cache_key) = cache_key {
        cache_insert_bounded(artifact_cache(), cache_key, Arc::new(artifact.clone()));
    }
    Some(rename_function_analysis_artifact(artifact, function_name))
}

#[derive(Debug, serde::Serialize)]
pub(crate) struct DataRef {
    pub(crate) from: u64,
    pub(crate) to: u64,
    #[serde(rename = "type")]
    pub(crate) ref_type: String,
}

pub(crate) fn merge_type_hint(
    hints: &mut std::collections::HashMap<String, TypeHint>,
    key: String,
    incoming: TypeHint,
) {
    r2types::merge_type_hint(hints, key, incoming);
}

fn size_to_signed_int_type(size: u32) -> String {
    match size {
        1 => "int8_t".to_string(),
        2 => "int16_t".to_string(),
        4 => "int32_t".to_string(),
        8 => "int64_t".to_string(),
        _ => format!("int{}_t", size.saturating_mul(8)),
    }
}

fn size_to_unsigned_int_type(size: u32) -> String {
    match size {
        1 => "uint8_t".to_string(),
        2 => "uint16_t".to_string(),
        4 => "uint32_t".to_string(),
        8 => "uint64_t".to_string(),
        _ => format!("uint{}_t", size.saturating_mul(8)),
    }
}

fn scalar_kind_to_type(kind: r2il::ScalarKind, size: u32) -> Option<TypeHint> {
    match kind {
        r2il::ScalarKind::Bool => Some(TypeHint {
            rank: TypeHintRank::Integer,
            ty: "bool".to_string(),
        }),
        r2il::ScalarKind::SignedInt => Some(TypeHint {
            rank: TypeHintRank::Integer,
            ty: size_to_signed_int_type(size),
        }),
        r2il::ScalarKind::UnsignedInt => Some(TypeHint {
            rank: TypeHintRank::Integer,
            ty: size_to_unsigned_int_type(size),
        }),
        r2il::ScalarKind::Float => {
            let ty = match size {
                4 => "float".to_string(),
                8 => "double".to_string(),
                16 => "long double".to_string(),
                _ => "float".to_string(),
            };
            Some(TypeHint {
                rank: TypeHintRank::Float,
                ty,
            })
        }
        r2il::ScalarKind::Bitvector | r2il::ScalarKind::Unknown => None,
    }
}

fn metadata_type_hint(vn: &r2il::Varnode) -> Option<TypeHint> {
    let meta = vn.meta.as_ref()?;

    if let Some(pointer_hint) = meta.pointer_hint
        && !matches!(pointer_hint, r2il::PointerHint::Unknown)
    {
        return Some(TypeHint::pointer());
    }

    let scalar_kind = meta.scalar_kind?;
    scalar_kind_to_type(scalar_kind, vn.size)
}

pub(crate) fn collect_register_type_hints(
    r2il_blocks: &[R2ILBlock],
    disasm: &Disassembler,
) -> std::collections::HashMap<String, TypeHint> {
    let mut hints: std::collections::HashMap<String, TypeHint> = std::collections::HashMap::new();

    for block in r2il_blocks {
        for op in &block.ops {
            for vn in crate::op_all_varnodes(op) {
                if !vn.is_register() {
                    continue;
                }
                let Some(hint) = metadata_type_hint(vn) else {
                    continue;
                };
                let Some(name) = disasm.register_name(vn) else {
                    continue;
                };

                let key = name.to_ascii_lowercase();
                merge_type_hint(&mut hints, key, hint);
            }
        }
    }

    hints
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

pub(crate) fn ssa_var_key(var: &r2ssa::SSAVar) -> String {
    r2types::ssa_var_key(var)
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

pub(crate) fn collect_pointer_arg_slots(vars: &[VarProt]) -> std::collections::BTreeSet<usize> {
    r2types::collect_pointer_arg_slots(vars)
}

#[cfg(test)]
pub(crate) fn merge_pointer_slot_evidence(
    inferred_params: &mut [InferredParam],
    pointer_arg_slots: &std::collections::BTreeSet<usize>,
) {
    if pointer_arg_slots.is_empty() {
        return;
    }

    let param_count = inferred_params.len();
    for (fallback_idx, param) in inferred_params.iter_mut().enumerate() {
        let explicit_slot = if param.arg_index == usize::MAX {
            None
        } else {
            Some(param.arg_index)
        };
        let slot = explicit_slot.unwrap_or(fallback_idx);
        let fallback_slot_match = pointer_arg_slots.contains(&fallback_idx)
            && (explicit_slot.is_none() || param_count == 1);
        if pointer_arg_slots.contains(&slot) || fallback_slot_match {
            param.evidence.pointer_proven = param.evidence.pointer_proven.max(1);
        }
    }
}

pub(crate) fn recover_vars_from_ssa(
    ssa_blocks: &[r2ssa::SSABlock],
    arch: Option<&ArchSpec>,
    metadata_reg_type_hints: &std::collections::HashMap<String, TypeHint>,
    semantic_typing_enabled: bool,
) -> Vec<VarProt> {
    r2types::recover_vars_from_ssa(
        ssa_blocks,
        arch.map(|spec| spec.name.as_str()),
        metadata_reg_type_hints,
        semantic_typing_enabled,
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

pub(crate) fn parse_const_value(name: &str) -> Option<u64> {
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

#[cfg(test)]
pub(crate) fn size_to_type(size: u32) -> String {
    r2types::size_to_type(size)
}

fn parse_const_addr(name: &str) -> Option<u64> {
    let addr = parse_const_value(name)?;
    if addr >= 0x10000 { Some(addr) } else { None }
}

fn resolve_const_value(
    const_env: &std::collections::HashMap<String, u64>,
    var: &r2ssa::SSAVar,
) -> Option<u64> {
    parse_const_value(&var.name).or_else(|| const_env.get(&ssa_var_key(var)).copied())
}

fn resolve_const_addr(
    const_env: &std::collections::HashMap<String, u64>,
    var: &r2ssa::SSAVar,
) -> Option<u64> {
    resolve_const_value(const_env, var).filter(|addr| *addr >= 0x10000)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum MemorySlotKey {
    Absolute(u64),
    Stack { base: String, offset: i64 },
}

fn is_stack_base_name(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "sp" | "rsp" | "esp" | "fp" | "rbp" | "ebp" | "x29"
    )
}

fn resolve_memory_slot_key(
    addr_env: &std::collections::HashMap<String, MemorySlotKey>,
    const_env: &std::collections::HashMap<String, u64>,
    var: &r2ssa::SSAVar,
) -> Option<MemorySlotKey> {
    if let Some(addr) = resolve_const_addr(const_env, var) {
        return Some(MemorySlotKey::Absolute(addr));
    }

    let lower = var.name.to_ascii_lowercase();
    if is_stack_base_name(&lower) {
        return Some(MemorySlotKey::Stack {
            base: lower,
            offset: 0,
        });
    }

    addr_env.get(&ssa_var_key(var)).cloned()
}

fn resolve_memory_slot_with_delta(base: MemorySlotKey, delta: i64) -> Option<MemorySlotKey> {
    match base {
        MemorySlotKey::Absolute(addr) => {
            if delta >= 0 {
                addr.checked_add(delta as u64).map(MemorySlotKey::Absolute)
            } else {
                addr.checked_sub(delta.unsigned_abs())
                    .map(MemorySlotKey::Absolute)
            }
        }
        MemorySlotKey::Stack { base, offset } => offset
            .checked_add(delta)
            .map(|offset| MemorySlotKey::Stack { base, offset }),
    }
}

fn resolve_memory_slot_from_add_sub(
    addr_env: &std::collections::HashMap<String, MemorySlotKey>,
    const_env: &std::collections::HashMap<String, u64>,
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    is_sub: bool,
) -> Option<MemorySlotKey> {
    if let Some(delta_raw) = resolve_const_value(const_env, b)
        && let Ok(delta) = i64::try_from(delta_raw)
        && let Some(base) = resolve_memory_slot_key(addr_env, const_env, a)
    {
        return resolve_memory_slot_with_delta(base, if is_sub { -delta } else { delta });
    }
    if !is_sub
        && let Some(delta_raw) = resolve_const_value(const_env, a)
        && let Ok(delta) = i64::try_from(delta_raw)
        && let Some(base) = resolve_memory_slot_key(addr_env, const_env, b)
    {
        return resolve_memory_slot_with_delta(base, delta);
    }
    None
}

fn bit_width(size: u32) -> u32 {
    size.saturating_mul(8).min(64)
}

fn mask_to_bits(value: u64, bits: u32) -> u64 {
    match bits {
        0 => 0,
        64 => value,
        n => value & ((1u64 << n) - 1),
    }
}

fn sign_extend_bits(value: u64, bits: u32) -> u64 {
    if bits == 0 {
        return 0;
    }
    if bits >= 64 {
        return value;
    }
    let masked = mask_to_bits(value, bits);
    let sign_bit = 1u64 << (bits - 1);
    if (masked & sign_bit) != 0 {
        masked | (!0u64 << bits)
    } else {
        masked
    }
}

pub(crate) fn get_data_refs_from_ssa_with_op_sources(
    ssa_blocks: &[r2ssa::SSABlock],
    op_sources: Option<&[Vec<u64>]>,
) -> Vec<DataRef> {
    let mut refs = Vec::new();
    let mut const_env: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
    let mut addr_env: std::collections::HashMap<String, MemorySlotKey> =
        std::collections::HashMap::new();
    let mut stack_value_env: std::collections::HashMap<MemorySlotKey, u64> =
        std::collections::HashMap::new();

    for (block_idx, block) in ssa_blocks.iter().enumerate() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let from = op_sources
                .and_then(|blocks| blocks.get(block_idx))
                .and_then(|ops| ops.get(op_idx))
                .copied()
                .unwrap_or(block.addr);
            match op {
                r2ssa::SSAOp::Copy { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        const_env.insert(ssa_var_key(dst), value);
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::Load { addr, .. } => {
                    if let Some(target) = resolve_const_addr(&const_env, addr) {
                        refs.push(DataRef {
                            from,
                            to: target,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let r2ssa::SSAOp::Load { dst, .. } = op
                        && let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, addr)
                        && let Some(value) = stack_value_env.get(&slot).copied()
                    {
                        const_env.insert(ssa_var_key(dst), value);
                        if value >= 0x10000 {
                            refs.push(DataRef {
                                from,
                                to: value,
                                ref_type: "d".to_string(),
                            });
                        }
                    }
                }
                r2ssa::SSAOp::Store { addr, val, .. } => {
                    if let Some(target) = resolve_const_addr(&const_env, addr) {
                        refs.push(DataRef {
                            from,
                            to: target,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(value_addr) = resolve_const_addr(&const_env, val) {
                        refs.push(DataRef {
                            from,
                            to: value_addr,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, addr) {
                        if let Some(value) = resolve_const_value(&const_env, val) {
                            stack_value_env.insert(slot, value);
                        } else {
                            stack_value_env.remove(&slot);
                        }
                    }
                }
                r2ssa::SSAOp::IntAdd { dst, a, b } => {
                    if let (Some(lhs), Some(rhs)) = (
                        resolve_const_value(&const_env, a),
                        resolve_const_value(&const_env, b),
                    ) {
                        const_env.insert(ssa_var_key(dst), lhs.wrapping_add(rhs));
                    }
                    if let Some(slot) =
                        resolve_memory_slot_from_add_sub(&addr_env, &const_env, a, b, false)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = parse_const_addr(&a.name) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(addr) = parse_const_addr(&b.name) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(target) = resolve_const_addr(&const_env, dst) {
                        refs.push(DataRef {
                            from,
                            to: target,
                            ref_type: "d".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::IntSub { dst, a, b } => {
                    if let (Some(lhs), Some(rhs)) = (
                        resolve_const_value(&const_env, a),
                        resolve_const_value(&const_env, b),
                    ) {
                        const_env.insert(ssa_var_key(dst), lhs.wrapping_sub(rhs));
                    }
                    if let Some(slot) =
                        resolve_memory_slot_from_add_sub(&addr_env, &const_env, a, b, true)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = parse_const_addr(&a.name) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(addr) = parse_const_addr(&b.name) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(target) = resolve_const_addr(&const_env, dst) {
                        refs.push(DataRef {
                            from,
                            to: target,
                            ref_type: "d".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::PtrAdd {
                    dst,
                    base,
                    index,
                    element_size,
                } => {
                    if let (Some(base_val), Some(index_val)) = (
                        resolve_const_value(&const_env, base),
                        resolve_const_value(&const_env, index),
                    ) {
                        let scaled = index_val.wrapping_mul((*element_size).into());
                        const_env.insert(ssa_var_key(dst), base_val.wrapping_add(scaled));
                    }
                    if let Some(target) = resolve_const_addr(&const_env, dst) {
                        refs.push(DataRef {
                            from,
                            to: target,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(index_val) = resolve_const_value(&const_env, index)
                        && let Ok(delta) =
                            i64::try_from(index_val.wrapping_mul((*element_size).into()))
                        && let Some(base_slot) =
                            resolve_memory_slot_key(&addr_env, &const_env, base)
                        && let Some(slot) = resolve_memory_slot_with_delta(base_slot, delta)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                }
                r2ssa::SSAOp::PtrSub {
                    dst,
                    base,
                    index,
                    element_size,
                } => {
                    if let (Some(base_val), Some(index_val)) = (
                        resolve_const_value(&const_env, base),
                        resolve_const_value(&const_env, index),
                    ) {
                        let scaled = index_val.wrapping_mul((*element_size).into());
                        const_env.insert(ssa_var_key(dst), base_val.wrapping_sub(scaled));
                    }
                    if let Some(target) = resolve_const_addr(&const_env, dst) {
                        refs.push(DataRef {
                            from,
                            to: target,
                            ref_type: "d".to_string(),
                        });
                    }
                    if let Some(index_val) = resolve_const_value(&const_env, index)
                        && let Ok(delta) =
                            i64::try_from(index_val.wrapping_mul((*element_size).into()))
                        && let Some(base_slot) =
                            resolve_memory_slot_key(&addr_env, &const_env, base)
                        && let Some(slot) = resolve_memory_slot_with_delta(base_slot, -delta)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                }
                r2ssa::SSAOp::Cast { dst, src } | r2ssa::SSAOp::New { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        const_env.insert(ssa_var_key(dst), value);
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::IntZExt { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        let src_bits = bit_width(src.size);
                        let dst_bits = bit_width(dst.size);
                        let zext = mask_to_bits(value, src_bits);
                        const_env.insert(ssa_var_key(dst), mask_to_bits(zext, dst_bits));
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::IntSExt { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        let src_bits = bit_width(src.size);
                        let dst_bits = bit_width(dst.size);
                        let sext = sign_extend_bits(value, src_bits);
                        const_env.insert(ssa_var_key(dst), mask_to_bits(sext, dst_bits));
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "d".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::Call { target, .. } | r2ssa::SSAOp::Branch { target } => {
                    if let Some(addr) = resolve_const_addr(&const_env, target) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "c".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::CallInd { target, .. } | r2ssa::SSAOp::BranchInd { target } => {
                    if let Some(addr) = resolve_const_addr(&const_env, target) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "c".to_string(),
                        });
                    }
                }
                r2ssa::SSAOp::CBranch { target, .. } => {
                    if let Some(addr) = resolve_const_addr(&const_env, target) {
                        refs.push(DataRef {
                            from,
                            to: addr,
                            ref_type: "c".to_string(),
                        });
                    }
                }
                _ => {}
            }
        }
    }

    refs.sort_by_key(|r| (r.from, r.to));
    refs.dedup_by(|a, b| a.from == b.from && a.to == b.to);

    refs
}

/// Recover variables from SSA analysis.
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_recover_vars(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> *mut c_char {
    let Some(input) = build_function_input(ctx, blocks, num_blocks, 0, ptr::null()) else {
        return ptr::null_mut();
    };
    let Some(ssa_blocks) = build_var_recovery_ssa_blocks(input.blocks.as_slice(), input.ctx.arch)
    else {
        return ptr::null_mut();
    };

    let semantic_typing_enabled = input.ctx.semantic_metadata_enabled;
    let reg_type_hints = if semantic_typing_enabled {
        collect_register_type_hints(input.blocks.as_slice(), input.ctx.disasm)
    } else {
        std::collections::HashMap::new()
    };

    if ssa_blocks.is_empty() {
        return ptr::null_mut();
    }

    let vars = recover_vars_from_ssa(
        &ssa_blocks,
        input.ctx.arch,
        &reg_type_hints,
        semantic_typing_enabled,
    );

    match serde_json::to_string(&vars) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Get data flow references from def-use analysis.
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_data_refs(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> *mut c_char {
    let Some(input) = build_function_input(ctx, blocks, num_blocks, 0, ptr::null()) else {
        return ptr::null_mut();
    };

    let mut refs = Vec::new();
    let mut inst_ssa_blocks = Vec::new();
    let mut op_source_addrs = Vec::new();
    for blk in input.blocks.as_slice() {
        inst_ssa_blocks.push(r2ssa::block::to_ssa(blk, input.ctx.disasm));
        op_source_addrs.push(
            blk.ops
                .iter()
                .enumerate()
                .map(|(op_idx, _)| {
                    blk.op_metadata(op_idx)
                        .and_then(|meta| meta.instruction_addr)
                        .unwrap_or(blk.addr)
                })
                .collect::<Vec<_>>(),
        );
    }
    refs.extend(get_data_refs_from_ssa_with_op_sources(
        &inst_ssa_blocks,
        Some(&op_source_addrs),
    ));

    let Some(func) =
        r2ssa::SSAFunction::from_blocks_for_data_refs(input.blocks.as_slice(), input.ctx.arch)
    else {
        return ptr::null_mut();
    };
    let ssa_blocks: Vec<r2ssa::SSABlock> = func
        .blocks()
        .map(|block| r2ssa::SSABlock {
            addr: block.addr,
            size: block.size,
            ops: block.ops.clone(),
        })
        .collect();
    if ssa_blocks.is_empty() {
        return ptr::null_mut();
    }

    refs.extend(get_data_refs_from_ssa_with_op_sources(&ssa_blocks, None));
    refs.sort_by(|a, b| {
        a.from
            .cmp(&b.from)
            .then_with(|| a.to.cmp(&b.to))
            .then_with(|| a.ref_type.cmp(&b.ref_type))
    });
    refs.dedup_by(|a, b| a.from == b.from && a.to == b.to && a.ref_type == b.ref_type);
    match serde_json::to_string(&refs) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ArchSpec, InferredParam, TypeEvidence, collect_type_evidence_for_var,
        infer_signature_return_type, resolve_evidence_driven_type,
    };

    fn const_return_blocks(addr: u64, value: u64) -> Vec<r2il::R2ILBlock> {
        let mut block = r2il::R2ILBlock::new(addr, 4);
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(value, 8),
        });
        vec![block]
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
    fn parse_interproc_seed_summaries_prefers_recognized_seed_over_payload_summary() {
        let scope_json = serde_json::json!({
            "payloads": [{
                "interproc": {
                    "summary": {
                        "id": 0x2000u64,
                        "name": "sym.imp.malloc",
                        "direct_callees": [],
                        "callsite_count": 0,
                        "has_unknown_calls": false,
                        "arg_effects": {},
                        "return_relation": "Void",
                        "reads_global_memory": false,
                        "writes_global_memory": false,
                        "touches_unknown_memory": false
                    }
                }
            }],
            "seeds": [{
                "id": 0x2000u64,
                "name": "sym.imp.malloc"
            }]
        })
        .to_string();

        let summaries = parse_interproc_seed_summaries(&scope_json);
        let summary = summaries
            .get(&r2ssa::InterprocFunctionId(0x2000))
            .expect("seed summary should exist");

        assert_eq!(
            summary.return_relation,
            r2ssa::SummaryReturnRelation::HeapAlloc
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
                .any(|r| { r.from != 0x404000 && r.to == 0x404d6c && r.ref_type == "d" }),
            "computed add-chain xref should use a non-block-head op source address"
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
            arg0.var_type, "void *",
            "spill/reload + scaled index should preserve pointer type on arg0"
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
            arg0.var_type, "void *",
            "shift-scaled index should preserve pointer type on arg0"
        );
    }

    #[test]
    fn recover_vars_semantic_disable_falls_back_to_integer_types() {
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
            arg0.var_type, "int64_t",
            "semantic-disabled path should ignore metadata/usage pointer hints"
        );
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
            arg0.var_type, "void *",
            "two-block spill/reload + scaled-index pattern should mark rdi as pointer"
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
                    name: "arg0".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Void,
                    ))),
                },
                r2types::FunctionParamSpec {
                    name: "arg3".to_string(),
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
            vec![
                ("argc", "int32_t"),
                ("argv", "int8_t**"),
                ("envp", "int8_t**"),
            ]
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
        let mut inferred_params = vec![InferredParam {
            name: "arg1".to_string(),
            ty: r2dec::CType::Int(64),
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
        let initial_ty = r2dec::CType::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("esi", 0, 4),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 4, 64, &evidence);
        assert_eq!(ty, r2dec::CType::Int(32));
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
        let initial_ty = r2dec::CType::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("rdi", 0, 8),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 8, 64, &evidence);
        assert_eq!(ty, r2dec::CType::void_ptr());
    }

    #[test]
    fn mixed_pointer_and_scalar_evidence_stays_conservative() {
        let evidence = TypeEvidence {
            pointer_proven: 1,
            scalar_likely: 1,
            ..TypeEvidence::default()
        };
        let ty = resolve_evidence_driven_type(r2dec::CType::Unknown, 8, 64, &evidence);
        assert_eq!(ty, r2dec::CType::void_ptr());
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
        let initial_ty = r2dec::CType::Unknown;
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("dil", 0, 1),
            &initial_ty,
        );
        let ty = resolve_evidence_driven_type(initial_ty, 1, 64, &evidence);
        assert_eq!(ty, r2dec::CType::Bool);
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
        assert_eq!(ret_ty, r2dec::CType::Int(32));
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

        let key_without_scope = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            "{}",
            None,
        )
        .expect("root-only cache key");
        let key_a = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            "{}",
            Some(&scope_a),
        )
        .expect("scoped cache key a");
        let key_a_repeat = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            "{}",
            Some(&scope_a),
        )
        .expect("scoped cache key a repeat");
        let key_b = function_artifact_cache_key_parts(
            "root",
            Some(&arch),
            &root_blocks,
            true,
            "{}",
            "{}",
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
}
