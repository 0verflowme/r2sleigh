#[cfg(test)]
use crate::types::FunctionAnalysisArtifact;
use r2il::R2ILBlock;
#[cfg(test)]
use std::collections::HashMap;

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
    let callee_resolution = r2engine::decompile_callee_resolution_facts(
        &ssa_func,
        &function_facts,
        &function_names,
        &symbols,
        ptr_bits,
    );
    let context =
        build_decompiler_context(function_facts, function_names, strings, symbols, ptr_bits)
            .with_callee_resolution(Some(callee_resolution));
    let context = context
        .with_semantic_route(Some(route_decision.route.to_decompiler_route()))
        .with_render_permission(Some(route_decision.render_permission.clone()))
        .with_runtime_type_inference_policy(Some(route_decision.skip_runtime_type_inference))
        .with_prepared_semantic_view_policy(Some(route_decision.use_prepared_semantic_view));
    r2dec::DecompilerInput::new(ssa_func, context)
}

pub(crate) fn render_named_native_worker_summary(
    r2il_blocks: Vec<R2ILBlock>,
    function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    ptr_bits: u32,
) -> Option<String> {
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
            func_names_payload: "",
            strings_payload: "",
            symbols_payload: "",
            fallback_if_guarded_without_summary: false,
        })
        .map(|response| response.output)
}

pub(crate) fn run_engine_decompile_on_large_stack(
    request: r2engine::EngineFunctionDecompileRequest,
) -> String {
    const STACK_SIZE: usize = 512 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            crate::types::engine_session()
                .decompile_function(request)
                .output
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
