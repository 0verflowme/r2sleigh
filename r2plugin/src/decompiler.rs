pub(crate) fn run_engine_decompile(
    input: r2engine::EngineFunctionDecompileRequestInput,
) -> r2engine::EngineDecompileResponse {
    crate::types::engine_session().decompile_function_from_input(input)
}

#[cfg(test)]
mod tests {
    #[test]
    fn decompiler_does_not_reserve_a_worker_stack() {
        let source = include_str!("decompiler.rs");
        assert!(!source.contains(concat!("std::thread::", "Builder")));
        assert!(!source.contains(concat!("stack_", "size(")));
        assert!(!source.contains(concat!("512 * 1024", " * 1024")));
    }

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
