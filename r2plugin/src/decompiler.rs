use crate::context::PluginCtxView;
use crate::parse_addr_name_map;
use crate::types::FunctionAnalysisArtifact;
use r2il::R2ILBlock;
#[cfg(test)]
use std::collections::HashMap;

pub(crate) struct DecompilerEnv {
    pub(crate) arch_name: String,
    pub(crate) ptr_bits: u32,
    pub(crate) cfg: r2dec::DecompilerConfig,
}

pub(crate) fn build_decompiler_env(ctx: &PluginCtxView<'_>) -> DecompilerEnv {
    let (arch_name, ptr_bits, cfg) = r2dec::DecompilerConfig::for_arch(ctx.arch);
    DecompilerEnv {
        arch_name,
        ptr_bits,
        cfg,
    }
}

#[cfg(test)]
pub(crate) fn build_decompiler_context(
    function_facts: r2types::FunctionFacts,
    function_names: HashMap<u64, String>,
    strings: HashMap<u64, String>,
    symbols: HashMap<u64, String>,
    ptr_bits: u32,
) -> r2dec::DecompilerContext {
    r2dec::DecompilerContext::from_function_facts(
        function_facts,
        function_names,
        strings,
        symbols,
        ptr_bits,
    )
}

#[cfg(test)]
pub(crate) fn decompiler_input_from_artifact(
    artifact: FunctionAnalysisArtifact,
    function_names: HashMap<u64, String>,
    strings: HashMap<u64, String>,
    symbols: HashMap<u64, String>,
    ptr_bits: u32,
) -> r2dec::DecompilerInput {
    let FunctionAnalysisArtifact {
        ssa_func,
        function_facts,
        ..
    } = artifact;
    let func_name = ssa_func
        .function()
        .name
        .clone()
        .unwrap_or_else(|| format!("sub_{:x}", ssa_func.entry));
    let cfg_summary = ssa_func.function().cfg_risk_summary();
    let route_decision = r2engine::decompile_route_decision(
        &func_name,
        &function_facts,
        Some(&ssa_func),
        &function_facts.types,
        &cfg_summary,
    );
    let context =
        build_decompiler_context(function_facts, function_names, strings, symbols, ptr_bits);
    let context = r2engine::decompiler_context_with_route_decision(context, &route_decision);
    r2dec::DecompilerInput::new(ssa_func, context)
}

pub(crate) fn render_named_native_worker_summary(
    r2il_blocks: Vec<R2ILBlock>,
    function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    ptr_bits: u32,
) -> Option<String> {
    let (arch_name, _, config) = r2dec::DecompilerConfig::for_arch(arch);
    let semantic_artifact = crate::types::collect_detached_native_worker_summary_artifact(
        &r2il_blocks,
        function_name,
        arch,
        None,
        true,
    )?;
    let type_facts = r2engine::type_facts_with_summary_projection(
        r2types::FunctionTypeFacts::default(),
        function_name,
        &arch_name,
        ptr_bits,
        &semantic_artifact,
    );
    let function_facts = r2types::FunctionFacts::new(type_facts, Some(semantic_artifact));
    let fallback_comment =
        r2engine::has_renderable_primary_summary_only_native_worker(&function_facts).then(|| {
            function_facts
                .semantics
                .as_ref()
                .map(|artifact| {
                    r2engine::summary_only_native_worker_fallback(function_name, artifact)
                })
                .unwrap_or_else(|| {
                    r2dec::artifact_guard_fallback_comment(
                        function_name,
                        "summary-only native worker without semantic artifact",
                    )
                })
        });
    render_summary_with_engine(
        &r2il_blocks,
        function_name,
        arch,
        ptr_bits,
        &function_facts,
        config,
        "",
        "",
        "",
        true,
        fallback_comment,
    )
}

#[allow(clippy::too_many_arguments)]
fn render_summary_with_engine(
    r2il_blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    ptr_bits: u32,
    function_facts: &r2types::FunctionFacts,
    config: r2dec::DecompilerConfig,
    func_names_payload: &str,
    strings_payload: &str,
    symbols_payload: &str,
    named_worker_guarded: bool,
    fallback_comment: Option<String>,
) -> Option<String> {
    let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(r2il_blocks)?.cfg_risk_summary();
    let render_cache_key =
        crate::types::decompile_render_cache_key(crate::types::DecompileRenderCacheKeyInput {
            blocks: r2il_blocks,
            function_name,
            arch,
            ptr_bits,
            function_facts,
            func_names_payload,
            strings_payload,
            symbols_payload,
        });
    crate::types::engine_session()
        .decompile_summary(r2engine::EngineSummaryDecompileRequest {
            function_name: function_name.to_string(),
            cfg_summary,
            function_facts: function_facts.clone(),
            named_worker_guarded,
            config,
            render_cache_key: Some(render_cache_key),
            fallback_comment,
        })
        .map(|response| response.output)
}

fn rename_function_artifact_for_display(
    artifact: FunctionAnalysisArtifact,
    function_name: &str,
) -> FunctionAnalysisArtifact {
    let FunctionAnalysisArtifact {
        ssa_func,
        pattern_ssa_func,
        function_facts,
        writeback_plan,
        ..
    } = artifact;
    FunctionAnalysisArtifact {
        ssa_func: ssa_func.with_name(function_name),
        pattern_ssa_func: pattern_ssa_func.with_name(function_name),
        function_facts,
        writeback_plan,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_full_decompile_on_large_stack(
    r2il_blocks: Vec<R2ILBlock>,
    fcn_addr: u64,
    func_name_str: String,
    arch: Option<r2il::ArchSpec>,
    ptr_bits: u32,
    semantic_metadata_enabled: bool,
    reg_type_hints: std::collections::HashMap<String, crate::types::TypeHint>,
    func_names_str: String,
    strings_str: String,
    symbols_str: String,
    external_context_json: String,
    cached_artifact: Option<crate::types::FunctionAnalysisArtifact>,
    type_facts_override: Option<r2types::FunctionTypeFacts>,
    symbolic_scope: Option<r2sym::PreparedFunctionScope>,
) -> String {
    const STACK_SIZE: usize = 512 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let (arch_name, _, config) = r2dec::DecompilerConfig::for_arch(arch.as_ref());
            let function_names = parse_addr_name_map(&func_names_str);
            let symbols = parse_addr_name_map(&symbols_str);
            let display_func_name = crate::helpers::resolve_decompiler_display_name(
                fcn_addr,
                &func_name_str,
                &function_names,
                &symbols,
            );
            let probe = r2engine::decompile_probe_decision(
                &r2il_blocks,
                fcn_addr,
                &func_name_str,
                &display_func_name,
            );
            let cfg_guard_reason = probe.cfg_guard_reason.clone();
            let summary_probe_name = probe.summary_probe_name.as_str();
            let mut artifact = if let Some(mut artifact) = cached_artifact {
                if let Some(type_facts_override) = type_facts_override.as_ref()
                    && let Some(signature) = type_facts_override.merged_signature.clone()
                {
                    artifact.function_facts.types.merged_signature = Some(signature);
                }
                if probe.summary_probe_needed
                    && let Some(semantic_artifact) =
                        crate::types::collect_detached_native_worker_summary_artifact(
                            &r2il_blocks,
                            summary_probe_name,
                            arch.as_ref(),
                            symbolic_scope.as_ref(),
                            true,
                        )
                {
                    let mut summary_type_seed = artifact.function_facts.types.clone();
                    if let Some(type_facts_override) = type_facts_override.as_ref()
                        && let Some(signature) = type_facts_override.merged_signature.clone()
                    {
                        summary_type_seed.merged_signature = Some(signature);
                    }
                    let summary_type_facts = r2engine::type_facts_with_summary_projection(
                        summary_type_seed,
                        summary_probe_name,
                        &arch_name,
                        ptr_bits,
                        &semantic_artifact,
                    );
                    let summary_facts =
                        r2types::FunctionFacts::new(summary_type_facts, Some(semantic_artifact.clone()));
                    let fallback_comment =
                        r2engine::has_renderable_primary_summary_only_native_worker(&summary_facts)
                            .then(|| {
                                r2engine::summary_only_native_worker_fallback(
                                    &display_func_name,
                                    &semantic_artifact,
                                )
                            });
                    if let Some(output) = render_summary_with_engine(
                        &r2il_blocks,
                        &display_func_name,
                        arch.as_ref(),
                        ptr_bits,
                        &summary_facts,
                        config.clone(),
                        &func_names_str,
                        &strings_str,
                        &symbols_str,
                        probe.named_worker_guarded,
                        fallback_comment,
                    ) {
                        return output;
                    }
                }
                artifact
            } else {
                let summary_probe_artifact = probe.summary_probe_needed.then(|| {
                    crate::types::collect_detached_native_worker_summary_artifact(
                        &r2il_blocks,
                        summary_probe_name,
                        arch.as_ref(),
                        symbolic_scope.as_ref(),
                        true,
                    )
                }).flatten();
                let mut summary_type_facts = type_facts_override.clone().unwrap_or_else(|| {
                    crate::types::external_function_type_facts_from_json(
                        &external_context_json,
                        ptr_bits,
                    )
                });
                if let Some(summary_artifact) = summary_probe_artifact.as_ref() {
                    summary_type_facts = r2engine::type_facts_with_summary_projection(
                        summary_type_facts,
                        summary_probe_name,
                        &arch_name,
                        ptr_bits,
                        summary_artifact,
                    );
                }
                let summary_facts = r2types::FunctionFacts::new(
                    summary_type_facts,
                    summary_probe_artifact.clone(),
                );
                let fallback_comment = summary_probe_artifact
                    .as_ref()
                    .filter(|_| {
                        r2engine::has_renderable_primary_summary_only_native_worker(&summary_facts)
                    })
                    .map(|summary_artifact| {
                        r2engine::summary_only_native_worker_fallback(
                            &display_func_name,
                            summary_artifact,
                        )
                    });
                if let Some(output) = render_summary_with_engine(
                    &r2il_blocks,
                    &display_func_name,
                    arch.as_ref(),
                    ptr_bits,
                    &summary_facts,
                    config.clone(),
                    &func_names_str,
                    &strings_str,
                    &symbols_str,
                    probe.named_worker_guarded,
                    fallback_comment,
                ) {
                    return output;
                }
                if probe.block_guarded {
                    return r2dec::artifact_guard_fallback_comment(
                        &display_func_name,
                        cfg_guard_reason
                            .as_deref()
                            .unwrap_or("large native worker without canonical summary"),
                    );
                }
                let Some(artifact) =
                    crate::types::build_detached_function_analysis_artifact_with_scope_and_optional_semantics(
                        &r2il_blocks,
                        &func_name_str,
                        arch.as_ref(),
                        ptr_bits,
                        semantic_metadata_enabled,
                        &reg_type_hints,
                        &external_context_json,
                        symbolic_scope.as_ref(),
                        None,
                        false,
                    )
                else {
                    return r2dec::artifact_guard_fallback_comment(
                        &func_name_str,
                        "failed to build detached analysis artifact",
                    );
                };
                artifact
            };
            artifact = rename_function_artifact_for_display(artifact, &display_func_name);

            let render_cache_key =
                crate::types::decompile_render_cache_key(crate::types::DecompileRenderCacheKeyInput {
                    blocks: &r2il_blocks,
                    function_name: &display_func_name,
                    arch: arch.as_ref(),
                    ptr_bits,
                    function_facts: &artifact.function_facts,
                    func_names_payload: &func_names_str,
                    strings_payload: &strings_str,
                    symbols_payload: &symbols_str,
                });

            let semantic_fallback_output = r2dec::semantic_fallback_comment(
                &display_func_name,
                artifact.function_facts.semantics.as_ref(),
            );
            let fallback_comment = semantic_fallback_output.or_else(|| {
                cfg_guard_reason
                    .as_ref()
                    .map(|reason| r2dec::artifact_guard_fallback_comment(&func_name_str, reason))
            });
            let response = crate::types::engine_session().decompile(r2engine::EngineDecompileRequest {
                function_name: display_func_name.clone(),
                prepared_ssa: artifact.ssa_func,
                function_facts: artifact.function_facts,
                function_names,
                strings: parse_addr_name_map(&strings_str),
                symbols,
                ptr_bits,
                config,
                render_cache_key: Some(render_cache_key),
                fallback_comment,
            });
            response.output
        });

    match handle {
        Ok(h) => match h.join() {
            Ok(output) => output,
            Err(_) => "/* r2dec: decompilation panicked (internal error) */".to_string(),
        },
        Err(e) => format!("/* r2dec: failed to spawn decompiler thread: {} */", e),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn nontrivial_program_orchestrators_use_summary_guard() {
        assert!(!r2engine::should_guard_program_orchestrator_decompile(
            1, 16
        ));
        assert!(r2engine::should_guard_program_orchestrator_decompile(5, 16));
        assert!(r2engine::should_guard_program_orchestrator_decompile(
            2, 128
        ));
    }
}
