use crate::context::PluginCtxView;
use crate::parse_addr_name_map;
use crate::types::FunctionAnalysisArtifact;
use r2il::R2ILBlock;
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
    r2dec::DecompilerInput::new(
        ssa_func,
        build_decompiler_context(function_facts, function_names, strings, symbols, ptr_bits),
    )
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
    symbolic_scope: Option<r2sym::PreparedFunctionScope>,
) -> String {
    const STACK_SIZE: usize = 512 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let cfg_guard_reason = r2dec::cfg_guard_reason(&r2il_blocks);
            let (_, _, config) = r2dec::DecompilerConfig::for_arch(arch.as_ref());
            let function_names = parse_addr_name_map(&func_names_str);
            let symbols = parse_addr_name_map(&symbols_str);
            let display_func_name = crate::helpers::resolve_decompiler_display_name(
                fcn_addr,
                &func_name_str,
                &function_names,
                &symbols,
            );
            let mut artifact = if let Some(artifact) = cached_artifact {
                if let Some(route) = r2dec::detached_semantic_route_plan(
                    &display_func_name,
                    &r2il_blocks,
                    &artifact.function_facts,
                ) {
                    if let r2dec::SemanticRoutePlan::FallbackComment { comment } = route {
                        return comment;
                    }
                    if let Some(reason) = cfg_guard_reason.as_ref()
                        && matches!(route, r2dec::SemanticRoutePlan::Standard)
                    {
                        return r2dec::artifact_guard_fallback_comment(&func_name_str, reason);
                    }
                }
                artifact
            } else {
                let precomputed_semantic_artifact = cfg_guard_reason.as_ref().map_or_else(
                    || None,
                    |_| {
                        crate::types::collect_detached_semantic_artifact(
                            &r2il_blocks,
                            &func_name_str,
                            arch.as_ref(),
                            symbolic_scope.as_ref(),
                        )
                    },
                );
                if let Some(route) = r2dec::detached_semantic_route_plan(
                    &display_func_name,
                    &r2il_blocks,
                    &r2types::FunctionFacts::new(
                        r2types::FunctionTypeFacts::default(),
                        precomputed_semantic_artifact.clone(),
                    ),
                ) {
                    if let r2dec::SemanticRoutePlan::FallbackComment { comment } = route {
                        return comment;
                    }
                    if let Some(reason) = cfg_guard_reason.as_ref()
                        && matches!(route, r2dec::SemanticRoutePlan::Standard)
                    {
                        return r2dec::artifact_guard_fallback_comment(&func_name_str, reason);
                    }
                }
                let Some(artifact) =
                    crate::types::build_detached_function_analysis_artifact_with_scope_and_semantics(
                        &r2il_blocks,
                        &func_name_str,
                        arch.as_ref(),
                        ptr_bits,
                        semantic_metadata_enabled,
                        &reg_type_hints,
                        &external_context_json,
                        symbolic_scope.as_ref(),
                        precomputed_semantic_artifact,
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

            if let Some(route) = r2dec::detached_semantic_route_plan(
                &display_func_name,
                &r2il_blocks,
                &artifact.function_facts,
            ) {
                match route {
                    r2dec::SemanticRoutePlan::VmSummary { .. } => {
                        if let Some(output) =
                            r2dec::render_vm_semantic_summary(&display_func_name, &artifact.function_facts)
                        {
                            return output;
                        }
                    }
                    r2dec::SemanticRoutePlan::FallbackComment { comment } => return comment,
                    _ => {}
                }
            }

            let decompiler = r2dec::Decompiler::new(config);
            let semantic_fallback_output = r2dec::semantic_fallback_comment(
                &display_func_name,
                artifact.function_facts.semantics.as_ref(),
            );
            let input = decompiler_input_from_artifact(
                artifact,
                function_names,
                parse_addr_name_map(&strings_str),
                symbols,
                ptr_bits,
            );

            let output = decompiler.decompile_input(&input);
            if output.trim().is_empty() {
                return semantic_fallback_output.unwrap_or_else(|| {
                    cfg_guard_reason
                        .as_ref()
                        .map(|reason| r2dec::artifact_guard_fallback_comment(&func_name_str, reason))
                        .unwrap_or_else(|| {
                            format!(
                                "/* r2dec fallback: skipped decompilation for {} (empty output) */",
                                display_func_name
                            )
                        })
                });
            }
            output
        });

    match handle {
        Ok(h) => match h.join() {
            Ok(output) => output,
            Err(_) => "/* r2dec: decompilation panicked (internal error) */".to_string(),
        },
        Err(e) => format!("/* r2dec: failed to spawn decompiler thread: {} */", e),
    }
}
