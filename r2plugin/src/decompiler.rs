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
    let (_, _, config) = r2dec::DecompilerConfig::for_arch(arch);
    let parsed_context = r2types::ParsedExternalContext::default();
    let function_addr = r2il_blocks
        .first()
        .map(|block| block.addr)
        .unwrap_or_default();
    crate::types::engine_session()
        .decompile_summary_preprobe(r2engine::EngineSummaryPreprobeRequest {
            blocks: &r2il_blocks,
            function_addr,
            canonical_name: function_name,
            display_name: function_name,
            arch,
            ptr_bits,
            parsed_context: &parsed_context,
            symbolic_scope: None,
            type_seed: Some(r2types::FunctionTypeFacts::default()),
            config,
            func_names_payload: "",
            strings_payload: "",
            symbols_payload: "",
            fallback_if_guarded_without_summary: false,
        })
        .map(|response| response.output)
}

pub(crate) fn render_direct_named_native_worker_summary(
    function_addr: u64,
    function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    ptr_bits: u32,
) -> Option<String> {
    let (arch_name, _, config) = r2dec::DecompilerConfig::for_arch(arch);
    let parsed_context = r2types::ParsedExternalContext::default();
    let projection = r2engine::native_worker_type_projection(
        function_addr,
        function_name,
        &arch_name,
        ptr_bits,
        &parsed_context,
        true,
    )?;
    let cfg_summary = r2ssa::CFGRiskSummary {
        block_count: 0,
        loop_count: 0,
        back_edge_count: 0,
        switch_block_count: 0,
        max_switch_cases: 0,
    };
    crate::types::engine_session()
        .decompile_summary(r2engine::EngineSummaryDecompileRequest {
            function_name: function_name.to_string(),
            cfg_summary,
            function_facts: projection.function_facts,
            named_worker_guarded: true,
            config,
            render_cache_key: None,
            fallback_comment: None,
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
            let (_, _, config) = r2dec::DecompilerConfig::for_arch(arch.as_ref());
            let function_names = parse_addr_name_map(&func_names_str);
            let symbols = parse_addr_name_map(&symbols_str);
            let display_func_name = crate::helpers::resolve_decompiler_display_name(
                fcn_addr,
                &func_name_str,
                &function_names,
                &symbols,
            );
            let parsed_context =
                r2types::parse_external_context_json(&external_context_json, ptr_bits);
            let probe = r2engine::decompile_probe_decision(
                &r2il_blocks,
                fcn_addr,
                &func_name_str,
                &display_func_name,
            );
            let cfg_guard_reason = probe.cfg_guard_reason.clone();
            let mut artifact = if let Some(mut artifact) = cached_artifact {
                if let Some(type_facts_override) = type_facts_override.as_ref()
                    && let Some(signature) = type_facts_override.merged_signature.clone()
                {
                    artifact.function_facts.types.merged_signature = Some(signature);
                }
                if probe.summary_probe_needed {
                    let mut summary_type_seed = artifact.function_facts.types.clone();
                    if let Some(type_facts_override) = type_facts_override.as_ref()
                        && let Some(signature) = type_facts_override.merged_signature.clone()
                    {
                        summary_type_seed.merged_signature = Some(signature);
                    }
                    if let Some(output) =
                        crate::types::engine_session().decompile_summary_preprobe(
                            r2engine::EngineSummaryPreprobeRequest {
                                blocks: &r2il_blocks,
                                function_addr: fcn_addr,
                                canonical_name: &func_name_str,
                                display_name: &display_func_name,
                                arch: arch.as_ref(),
                                ptr_bits,
                                parsed_context: &parsed_context,
                                symbolic_scope: symbolic_scope.as_ref(),
                                type_seed: Some(summary_type_seed),
                                config: config.clone(),
                                func_names_payload: &func_names_str,
                                strings_payload: &strings_str,
                                symbols_payload: &symbols_str,
                                fallback_if_guarded_without_summary: false,
                            },
                        )
                    {
                        return output.output;
                    }
                }
                artifact
            } else {
                let summary_type_seed = type_facts_override.clone().unwrap_or_else(|| {
                    r2types::function_type_facts_from_parsed_context(
                        &display_func_name,
                        &parsed_context,
                    )
                });
                if let Some(output) =
                    crate::types::engine_session().decompile_summary_preprobe(
                        r2engine::EngineSummaryPreprobeRequest {
                            blocks: &r2il_blocks,
                            function_addr: fcn_addr,
                            canonical_name: &func_name_str,
                            display_name: &display_func_name,
                            arch: arch.as_ref(),
                            ptr_bits,
                            parsed_context: &parsed_context,
                            symbolic_scope: symbolic_scope.as_ref(),
                            type_seed: Some(summary_type_seed),
                            config: config.clone(),
                            func_names_payload: &func_names_str,
                            strings_payload: &strings_str,
                            symbols_payload: &symbols_str,
                            fallback_if_guarded_without_summary: true,
                        },
                    )
                {
                    return output.output;
                }
                if probe.block_guarded {
                    let guard_reason = if probe.summary_probe_skipped_large_cfg {
                        cfg_guard_reason
                            .as_deref()
                            .unwrap_or("large native worker without canonical summary")
                    } else {
                        "bounded native-worker preprobe without canonical summary"
                    };
                    return r2dec::artifact_guard_fallback_comment(
                        &display_func_name,
                        guard_reason,
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
    use super::*;

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

    #[test]
    fn direct_named_worker_summary_renders_without_blocks() {
        let output = render_direct_named_native_worker_summary(0x401000, "dbg.init_node", None, 64)
            .expect("direct init_node summary");

        assert!(output.contains("init_node"));
        assert!(output.contains("r2dec summary:"));
        assert!(output.contains("worker summary:"));
    }
}
