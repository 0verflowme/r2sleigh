pub(crate) fn run_engine_decompile_on_large_stack(
    input: r2engine::EngineFunctionDecompileRequestInput,
) -> Option<String> {
    const STACK_SIZE: usize = 512 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            crate::types::engine_session()
                .decompile_function_from_input(input)
                .output
        });

    match handle {
        Ok(h) => h.join().ok(),
        Err(_) => None,
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
