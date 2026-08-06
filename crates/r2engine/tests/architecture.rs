use std::fs;
use std::path::Path;

#[test]
fn engine_route_policy_never_uses_renderer_route_type() {
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = fs::read_dir(&src_dir)
        .expect("r2engine src directory should exist")
        .map(|entry| entry.expect("source file entry should be readable").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect::<Vec<_>>();
    files.sort();

    let mut violations = Vec::new();

    for file in files {
        let rel = file
            .strip_prefix(&src_dir)
            .unwrap_or(&file)
            .to_string_lossy()
            .replace('\\', "/");
        let text = fs::read_to_string(&file).expect("source file should be UTF-8");
        for (line_idx, line) in text.lines().enumerate() {
            if !line.contains("r2dec::SemanticRoutePlan") && !line.contains("to_decompiler_route") {
                continue;
            }
            violations.push(format!("{}:{} {}", rel, line_idx + 1, line.trim()));
        }
    }

    assert!(
        violations.is_empty(),
        "r2engine route policy must not depend on renderer route types or conversion helpers.\n\
         Violations:\n{}",
        violations.join("\n")
    );
}

#[test]
fn engine_public_api_never_exposes_renderer_config_or_context_types() {
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = fs::read_dir(&src_dir)
        .expect("r2engine src directory should exist")
        .map(|entry| entry.expect("source file entry should be readable").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect::<Vec<_>>();
    files.sort();

    let mut violations = Vec::new();

    for file in files {
        let rel = file
            .strip_prefix(&src_dir)
            .unwrap_or(&file)
            .to_string_lossy()
            .replace('\\', "/");
        let text = fs::read_to_string(&file).expect("source file should be UTF-8");
        for (line_idx, line) in text.lines().enumerate() {
            let renderer_config = line.contains("r2dec::DecompilerConfig");
            let renderer_context = line.contains("r2dec::DecompilerContext");
            let renderer_input = line.contains("r2dec::DecompilerInput");
            let route_context_adapter = line.contains("decompiler_context_with_route_decision");
            if !(renderer_config || renderer_context || renderer_input || route_context_adapter) {
                continue;
            }

            let allowed_config_adapter = rel == "lib.rs"
                && renderer_config
                && (line.contains("to_decompiler_config")
                    || line.contains("r2dec::DecompilerConfig::for_arch_name"));
            let allowed_private_render_bridge = rel == "lib.rs"
                && (renderer_context || renderer_input || route_context_adapter)
                && !line.contains("pub ");
            let allowed_crate_private_route_adapter = rel == "route.rs"
                && (renderer_context || route_context_adapter)
                && (line.contains("pub(crate)")
                    || line.contains("context:")
                    || line.contains(") -> r2dec::DecompilerContext"));
            if !(allowed_config_adapter
                || allowed_private_render_bridge
                || allowed_crate_private_route_adapter)
            {
                violations.push(format!("{}:{} {}", rel, line_idx + 1, line.trim()));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "r2engine public contracts must use engine-owned render types and convert to r2dec only at the private renderer adapter boundary.\n\
         Violations:\n{}",
        violations.join("\n")
    );
}
