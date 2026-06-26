#[cfg(test)]
use crate::types::FunctionAnalysisArtifact;
use r2il::R2ILBlock;
#[cfg(test)]
use std::collections::HashMap;

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
    r2engine::decompiler_input_from_prepared_facts(
        ssa_func,
        function_facts,
        function_names,
        strings,
        symbols,
        ptr_bits,
    )
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
