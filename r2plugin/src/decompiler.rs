use crate::context::PluginCtxView;
#[cfg(test)]
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
