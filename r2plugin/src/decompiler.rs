use crate::context::PluginCtxView;
use crate::types::FunctionAnalysisArtifact;
use crate::{decompile_artifact_guard_fallback, parse_addr_name_map};
use r2il::{ArchSpec, R2ILBlock};
use std::collections::HashMap;

pub(crate) struct DecompilerEnv {
    pub(crate) arch_name: String,
    pub(crate) ptr_bits: u32,
    pub(crate) cfg: r2dec::DecompilerConfig,
}

pub(crate) fn normalize_sig_arch_name(arch: Option<&ArchSpec>) -> Option<String> {
    let arch = arch?;
    let lower = arch.name.to_ascii_lowercase();
    if matches!(lower.as_str(), "x86-64" | "x86_64" | "x64" | "amd64") {
        return Some("x86-64".to_string());
    }
    if matches!(lower.as_str(), "x86" | "x86-32" | "i386" | "i686") {
        return Some("x86".to_string());
    }
    Some(arch.name.clone())
}

pub(crate) fn decompiler_config_for_arch_name(
    arch_name: &str,
    ptr_bits: u32,
) -> r2dec::DecompilerConfig {
    match (arch_name, ptr_bits) {
        ("x86", 32) | ("x86-32", _) => r2dec::DecompilerConfig::x86(),
        ("x86-64", _) | ("x86_64", _) | ("x64", _) | ("amd64", _) => {
            r2dec::DecompilerConfig::x86_64()
        }
        ("arm", _) | ("ARM", _) if ptr_bits == 32 => r2dec::DecompilerConfig::arm(),
        ("aarch64", _) | ("arm64", _) | ("ARM64", _) => r2dec::DecompilerConfig::aarch64(),
        ("riscv32", _) | ("rv32", _) | ("rv32gc", _) => r2dec::DecompilerConfig::riscv32(),
        ("riscv64", _) | ("rv64", _) | ("rv64gc", _) => r2dec::DecompilerConfig::riscv64(),
        ("riscv", _) if ptr_bits == 32 => r2dec::DecompilerConfig::riscv32(),
        ("riscv", _) => r2dec::DecompilerConfig::riscv64(),
        _ => r2dec::DecompilerConfig {
            ptr_size: ptr_bits,
            ..r2dec::DecompilerConfig::default()
        },
    }
}

pub(crate) fn build_decompiler_env(ctx: &PluginCtxView<'_>) -> DecompilerEnv {
    let arch_name = normalize_sig_arch_name(ctx.arch).unwrap_or_else(|| "unknown".to_string());
    let ptr_bits = ctx.arch.map(|arch| arch.addr_size * 8).unwrap_or(64);
    let cfg = decompiler_config_for_arch_name(&arch_name, ptr_bits);
    DecompilerEnv {
        arch_name,
        ptr_bits,
        cfg,
    }
}

pub(crate) fn build_decompiler_context(
    type_facts: r2types::FunctionTypeFacts,
    function_names: HashMap<u64, String>,
    strings: HashMap<u64, String>,
    symbols: HashMap<u64, String>,
) -> r2dec::DecompilerContext {
    r2dec::DecompilerContext {
        function_names,
        strings,
        symbols,
        type_facts,
    }
}

pub(crate) fn decompiler_input_from_artifact(
    artifact: FunctionAnalysisArtifact,
    function_names: HashMap<u64, String>,
    strings: HashMap<u64, String>,
    symbols: HashMap<u64, String>,
) -> r2dec::DecompilerInput {
    r2dec::DecompilerInput::new(
        artifact.ssa_func,
        build_decompiler_context(artifact.type_facts, function_names, strings, symbols),
    )
    .with_interproc_summary_set(artifact.interproc_summary_set)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_full_decompile_on_large_stack(
    r2il_blocks: Vec<R2ILBlock>,
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
) -> String {
    const STACK_SIZE: usize = 512 * 1024 * 1024;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            if let Some(reason) = crate::decompiler_cfg_guard_reason(&r2il_blocks) {
                return decompile_artifact_guard_fallback(&func_name_str, &reason);
            }
            let arch_name =
                normalize_sig_arch_name(arch.as_ref()).unwrap_or_else(|| "unknown".to_string());
            let config = decompiler_config_for_arch_name(&arch_name, ptr_bits);
            let function_names = parse_addr_name_map(&func_names_str);
            let symbols = parse_addr_name_map(&symbols_str);
            let mut artifact = if let Some(artifact) = cached_artifact {
                artifact
            } else {
                let Some(artifact) = crate::types::build_detached_function_analysis_artifact(
                    &r2il_blocks,
                    &func_name_str,
                    arch.as_ref(),
                    ptr_bits,
                    semantic_metadata_enabled,
                    &reg_type_hints,
                    &external_context_json,
                ) else {
                    return decompile_artifact_guard_fallback(
                        &func_name_str,
                        "failed to build detached analysis artifact",
                    );
                };
                artifact
            };
            crate::types::enrich_known_function_signatures_from_names(
                &mut artifact.type_facts,
                &function_names,
                ptr_bits,
            );
            crate::types::enrich_known_function_signatures_from_names(
                &mut artifact.type_facts,
                &symbols,
                ptr_bits,
            );

            let decompiler = r2dec::Decompiler::new(config);
            let input = decompiler_input_from_artifact(
                artifact,
                function_names,
                parse_addr_name_map(&strings_str),
                symbols,
            );

            decompiler.decompile_input(&input)
        });

    match handle {
        Ok(h) => match h.join() {
            Ok(output) => output,
            Err(_) => "/* r2dec: decompilation panicked (internal error) */".to_string(),
        },
        Err(e) => format!("/* r2dec: failed to spawn decompiler thread: {} */", e),
    }
}
