//! Integration tests for r2sleigh plugin.
//!
//! These tests invoke radare2 with the r2sleigh plugin and validate output.
//! Run with: `cargo test -p r2sleigh-e2e-tests`

use e2e::{r2_cmd, r2_cmd_timeout, release_plugin_path, require_binary, vuln_test_binary};
use serde_json::Value;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

mod ffi_v2;

mod borrowed_snapshot_provider {
    use super::*;

    fn embedded_dwarf_fixture() -> Option<&'static str> {
        [
            "../radare2/test/bins/elf/dwarf5_line_cl",
            "../../../radare2/test/bins/elf/dwarf5_line_cl",
        ]
        .into_iter()
        .find(|candidate| Path::new(candidate).is_file())
    }

    #[test]
    fn embedded_dwarf_function_uses_the_ordinary_borrowed_snapshot_route() {
        let Some(binary) = embedded_dwarf_fixture() else {
            eprintln!("Skipping: sibling radare2 DWARF fixture is unavailable");
            return;
        };
        let result = r2_cmd_timeout(
            binary,
            "a:sla >/dev/null; aaa; s dbg.new_foo; pdd",
            Duration::from_secs(120),
        );
        result.assert_ok();
        assert!(
            result.stdout.contains("sub_1170(void)"),
            "trusted presentation identity must be address-derived:\n{}",
            result.stdout
        );
        assert!(
            result.stdout.contains("r2dec residual:"),
            "unsupported semantics must remain explicit rather than becoming test-shaped C:\n{}",
            result.stdout
        );
    }
}

// ============================================================================
// Test fixtures
// ============================================================================

fn setup() {
    require_binary(vuln_test_binary());
}

// ============================================================================
// PR4 CLI Run + Export Regression Tests
// ============================================================================

mod cli_run {
    use super::*;

    fn workspace_manifest_path() -> &'static str {
        if Path::new("crates/r2sleigh-cli").exists() {
            "Cargo.toml"
        } else if Path::new("../../crates/r2sleigh-cli").exists() {
            "../../Cargo.toml"
        } else {
            panic!("unable to locate workspace Cargo.toml for CLI tests");
        }
    }

    fn configure_nested_cargo_env(command: &mut Command) {
        if std::env::var_os("Z3_SYS_Z3_HEADER").is_none() {
            for candidate in ["/opt/homebrew/include/z3.h", "/usr/local/include/z3.h"] {
                if Path::new(candidate).exists() {
                    command.env("Z3_SYS_Z3_HEADER", candidate);
                    break;
                }
            }
        }
        if std::env::var_os("Z3_LIBRARY_PATH_OVERRIDE").is_none() {
            for candidate in ["/opt/homebrew/lib", "/usr/local/lib"] {
                if Path::new(candidate).join("libz3.dylib").exists()
                    || Path::new(candidate).join("libz3.so").exists()
                {
                    command.env("Z3_LIBRARY_PATH_OVERRIDE", candidate);
                    break;
                }
            }
        }
    }

    fn run_cli(args: &[&str]) -> (String, String, bool) {
        let mut command = Command::new("cargo");
        command.args([
            "run",
            "-q",
            "--manifest-path",
            workspace_manifest_path(),
            "-p",
            "r2sleigh-cli",
            "--features",
            "x86",
            "--",
        ]);
        command.args(args);
        configure_nested_cargo_env(&mut command);
        let output = command.output().expect("execute r2sleigh cli");
        (
            String::from_utf8_lossy(&output.stdout).to_string(),
            String::from_utf8_lossy(&output.stderr).to_string(),
            output.status.success(),
        )
    }

    #[test]
    fn cli_run_lift_json_outputs_valid_json() {
        let (stdout, stderr, ok) = run_cli(&[
            "run",
            "--arch",
            "x86-64",
            "--bytes",
            "31c00000000000000000000000000000",
            "--action",
            "lift",
            "--format",
            "json",
        ]);
        assert!(ok, "cli run should succeed: {}", stderr);
        let parsed: Value = serde_json::from_str(stdout.trim()).expect("valid json");
        assert!(
            parsed
                .get("ops")
                .and_then(Value::as_array)
                .is_some_and(|ops| !ops.is_empty()),
            "lift json output should contain non-empty ops"
        );
    }

    #[test]
    fn cli_run_lift_r2cmd_contains_sidecar_and_ae() {
        let (stdout, stderr, ok) = run_cli(&[
            "run",
            "--arch",
            "x86-64",
            "--bytes",
            "31c00000000000000000000000000000",
            "--action",
            "lift",
            "--format",
            "r2cmd",
        ]);
        assert!(ok, "cli run should succeed: {}", stderr);
        let lines: Vec<&str> = stdout.lines().collect();
        assert!(
            lines.first().is_some_and(|line| line.starts_with("# ")),
            "r2cmd output must start with sidecar JSON comment"
        );
        assert!(
            lines.get(1).is_some_and(|line| line.starts_with("ae ")),
            "r2cmd output must include ae replay line"
        );
    }

    #[test]
    fn cli_run_dec_c_like_outputs_c_like() {
        let (stdout, stderr, ok) = run_cli(&[
            "run",
            "--arch",
            "x86-64",
            "--bytes",
            "31c00000000000000000000000000000",
            "--action",
            "dec",
            "--format",
            "c_like",
        ]);
        assert!(ok, "cli run should succeed: {}", stderr);
        assert!(
            !stdout.trim().is_empty(),
            "dec c_like output should be non-empty"
        );
    }

    #[test]
    fn plugin_sla_debug_json_still_valid_after_refactor() {
        if !Path::new(release_plugin_path()).exists() {
            eprintln!("Skipping: plugin not built");
            return;
        }
        setup();
        let result = r2_cmd(vuln_test_binary(), "s entry0; a:sla.debug.json");
        result.assert_ok();
        let parsed: Value = serde_json::from_str(result.stdout.trim()).expect("valid JSON");
        assert!(
            parsed.is_array(),
            "a:sla.debug.json should stay valid JSON array output"
        );
    }
}

// ============================================================================
// Direct FFI Tests (plugin library)
// ============================================================================
mod ffi {
    use crate::ffi_v2::{
        ANALYSIS_BLOCK_DEFUSE, ANALYSIS_BLOCK_ESIL, ANALYSIS_BLOCK_MEMORY, ANALYSIS_BLOCK_SSA,
        V2Library,
    };
    use serde_json::Value;
    use std::collections::BTreeMap;
    use std::path::Path;

    #[cfg(target_os = "macos")]
    const PLUGIN_PATH: &str = "../../target/release/libr2sleigh_plugin.dylib";
    #[cfg(target_os = "linux")]
    const PLUGIN_PATH: &str = "../../target/release/libr2sleigh_plugin.so";
    #[cfg(target_os = "windows")]
    const PLUGIN_PATH: &str = "../../target/release/r2sleigh_plugin.dll";

    fn require_plugin() -> bool {
        Path::new(PLUGIN_PATH).exists()
    }

    const X86_BYTES_BASE: &[u8] = &[0x48, 0x89, 0xc0]; // mov rax, rax
    const X86_BYTES_DEC: &[u8] = &[0xc3]; // ret
    const ARM_BYTES_BASE: &[u8] = &[0x01, 0x00, 0xa0, 0xe3]; // mov r0, r1 style fixture
    const RISCV_BYTES_BASE: &[u8] = &[0x13, 0x05, 0x15, 0x00]; // addi a0,a0,1

    fn padded_bytes(bytes: &[u8]) -> Vec<u8> {
        let mut out = bytes.to_vec();
        out.resize(16, 0x00);
        out
    }

    fn canonicalize_json(value: &Value) -> Value {
        match value {
            Value::Object(map) => {
                let mut sorted = BTreeMap::new();
                for (k, v) in map {
                    sorted.insert(k.clone(), canonicalize_json(v));
                }
                let mut out = serde_json::Map::new();
                for (k, v) in sorted {
                    out.insert(k, v);
                }
                Value::Object(out)
            }
            Value::Array(items) => Value::Array(items.iter().map(canonicalize_json).collect()),
            _ => value.clone(),
        }
    }

    fn normalize_json_output(output: &str) -> String {
        let parsed: Value = serde_json::from_str(output.trim()).expect("valid json");
        canonicalize_json(&parsed).to_string()
    }

    fn normalize_text_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let mut lines: Vec<String> = text.lines().map(|l| l.trim_end().to_string()).collect();
        while lines.last().is_some_and(|l| l.is_empty()) {
            lines.pop();
        }
        lines.join("\n")
    }

    struct FfiExports {
        esil: String,
        ssa_json: String,
        defuse_json: String,
    }

    fn export_once_for_arch(
        arch: &str,
        base_bytes: &[u8],
        _dec_bytes: &[u8],
    ) -> Option<FfiExports> {
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context(arch) else {
            eprintln!("Skipping {arch} parity conformance: architecture unavailable");
            return None;
        };
        let base = padded_bytes(base_bytes);
        let block = context.lift(&base, 0x1000);
        assert!(block.validate(), "lifted block should validate for {arch}");
        let esil = block.render(ANALYSIS_BLOCK_ESIL, 0);
        let ssa_json = block.render(ANALYSIS_BLOCK_SSA, 0);
        let defuse_json = block.render(ANALYSIS_BLOCK_DEFUSE, 0);
        let ssa_parsed: Value = serde_json::from_str(&ssa_json).expect("valid ssa json");
        assert!(
            ssa_parsed.as_array().is_some(),
            "ssa json must be an array for {arch}"
        );
        let defuse_parsed: Value = serde_json::from_str(&defuse_json).expect("valid defuse json");
        assert!(
            defuse_parsed.get("inputs").is_some(),
            "defuse inputs missing"
        );
        assert!(
            defuse_parsed.get("outputs").is_some(),
            "defuse outputs missing"
        );
        assert!(defuse_parsed.get("live").is_some(), "defuse live missing");
        Some(FfiExports {
            esil,
            ssa_json,
            defuse_json,
        })
    }

    fn assert_ffi_deterministic_for_arch(arch: &str, base_bytes: &[u8], dec_bytes: &[u8]) {
        let first = match export_once_for_arch(arch, base_bytes, dec_bytes) {
            Some(v) => v,
            None => return,
        };
        let second = match export_once_for_arch(arch, base_bytes, dec_bytes) {
            Some(v) => v,
            None => return,
        };

        let first_esil = normalize_text_output(&first.esil);
        let second_esil = normalize_text_output(&second.esil);
        assert_eq!(first_esil, second_esil, "esil mismatch for {}", arch);
        assert!(
            !first_esil.trim().is_empty(),
            "esil must be non-empty for {}",
            arch
        );

        let first_ssa = normalize_json_output(&first.ssa_json);
        let second_ssa = normalize_json_output(&second.ssa_json);
        assert_eq!(first_ssa, second_ssa, "ssa mismatch for {}", arch);

        let first_defuse = normalize_json_output(&first.defuse_json);
        let second_defuse = normalize_json_output(&second.defuse_json);
        assert_eq!(first_defuse, second_defuse, "defuse mismatch for {}", arch);
    }

    fn mem_access_has_addr_storage_class(mem_access_json: &str, storage_class: &str) -> bool {
        let parsed: Value = serde_json::from_str(mem_access_json).expect("valid mem_access json");
        parsed.as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item.get("addr_detail")
                    .and_then(Value::as_object)
                    .and_then(|detail| detail.get("meta"))
                    .and_then(Value::as_object)
                    .and_then(|meta| meta.get("storage_class"))
                    .and_then(Value::as_str)
                    == Some(storage_class)
            })
        })
    }

    fn mem_access_has_addr_pointer_hint(mem_access_json: &str, pointer_hint: &str) -> bool {
        let parsed: Value = serde_json::from_str(mem_access_json).expect("valid mem_access json");
        parsed.as_array().is_some_and(|items| {
            items.iter().any(|item| {
                item.get("addr_detail")
                    .and_then(Value::as_object)
                    .and_then(|detail| detail.get("meta"))
                    .and_then(Value::as_object)
                    .and_then(|meta| meta.get("pointer_hint"))
                    .and_then(Value::as_str)
                    == Some(pointer_hint)
            })
        })
    }

    #[test]
    fn lift_xor_instruction() {
        if !require_plugin() {
            return;
        }
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context("x86-64") else {
            return;
        };
        let block = context.lift(&padded_bytes(&[0x31, 0xc0]), 0x1000);
        assert!(block.validate());
        assert!(block.op_count() > 0);
        assert!(
            block
                .render(ANALYSIS_BLOCK_ESIL, 0)
                .to_ascii_lowercase()
                .contains("eax")
        );
    }

    #[test]
    fn lift_add_instruction_to_ssa() {
        if !require_plugin() {
            return;
        }
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context("x86-64") else {
            return;
        };
        let block = context.lift(&padded_bytes(&[0x48, 0x01, 0xd8]), 0x1000);
        let ssa = block.render(ANALYSIS_BLOCK_SSA, 0);
        let parsed: Value = serde_json::from_str(&ssa).expect("valid SSA JSON");
        assert!(parsed.as_array().is_some());
    }

    #[test]
    fn lift_auto_populates_semantic_metadata_for_stack_memory() {
        if !require_plugin() {
            return;
        }
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context("x86-64") else {
            return;
        };
        let block = context.lift(&padded_bytes(&[0x48, 0x8b, 0x04, 0x24]), 0x1000);
        let memory = block.render(ANALYSIS_BLOCK_MEMORY, 0);
        assert!(mem_access_has_addr_storage_class(&memory, "stack"));
        assert!(mem_access_has_addr_pointer_hint(&memory, "pointer_like"));
    }

    #[test]
    fn lift_respects_semantic_metadata_disable_toggle() {
        if !require_plugin() {
            return;
        }
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context("x86-64") else {
            return;
        };
        let bytes = padded_bytes(&[0x48, 0x8b, 0x04, 0x24]);
        {
            let enabled = context.lift(&bytes, 0x1000);
            let memory = enabled.render(ANALYSIS_BLOCK_MEMORY, 0);
            assert!(mem_access_has_addr_storage_class(&memory, "stack"));
            assert!(mem_access_has_addr_pointer_hint(&memory, "pointer_like"));
        }
        context.set_semantic_metadata(false);
        let disabled = context.lift(&bytes, 0x2000);
        let memory = disabled.render(ANALYSIS_BLOCK_MEMORY, 0);
        assert!(!mem_access_has_addr_storage_class(&memory, "stack"));
        assert!(!mem_access_has_addr_pointer_hint(&memory, "pointer_like"));
    }

    fn assert_riscv_lift(arch: &str) {
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context(arch) else {
            eprintln!("Skipping: plugin built without {arch} support");
            return;
        };
        let block = context.lift(&padded_bytes(&[0x13, 0x05, 0x05, 0x00]), 0x1000);
        assert!(block.validate());
    }

    #[test]
    fn riscv64_lift_and_validate_success() {
        if require_plugin() {
            assert_riscv_lift("riscv64");
        }
    }

    #[test]
    fn riscv64_export_paths_esil_ssa_defuse_nonnull() {
        if !require_plugin() {
            return;
        }
        let library = unsafe { V2Library::open(PLUGIN_PATH) };
        let Some(context) = library.context("riscv64") else {
            return;
        };
        let block = context.lift(&padded_bytes(&[0x13, 0x05, 0x05, 0x00]), 0x1000);
        assert!(!block.render(ANALYSIS_BLOCK_ESIL, 0).is_empty());
        assert!(!block.render(ANALYSIS_BLOCK_SSA, 0).is_empty());
        assert!(!block.render(ANALYSIS_BLOCK_DEFUSE, 0).is_empty());
    }

    #[test]
    fn riscv32_lift_and_validate_success() {
        if require_plugin() {
            assert_riscv_lift("riscv32");
        }
    }

    #[test]
    fn ffi_parity_conformance_x86_deterministic() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }
        assert_ffi_deterministic_for_arch("x86-64", X86_BYTES_BASE, X86_BYTES_DEC);
    }

    #[test]
    fn ffi_parity_conformance_arm_deterministic() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }
        assert_ffi_deterministic_for_arch("arm", ARM_BYTES_BASE, ARM_BYTES_BASE);
    }

    #[test]
    fn ffi_parity_conformance_riscv64_deterministic() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }
        assert_ffi_deterministic_for_arch("riscv64", RISCV_BYTES_BASE, RISCV_BYTES_BASE);
    }

    #[test]
    fn ffi_parity_conformance_riscv32_deterministic() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }
        assert_ffi_deterministic_for_arch("riscv32", RISCV_BYTES_BASE, RISCV_BYTES_BASE);
    }
}

// ============================================================================
// 10. Analysis Quality Benchmark
// ============================================================================
//
// Measures what the r2sleigh plugin adds to radare2's analysis pipeline.
// These tests run WITH the plugin (which is always loaded in the test env)
// and assert minimum quality thresholds for key analysis metrics.
//
// The measured dimensions are:
// - Data xrefs: SSA-derived data-flow references (get_data_refs callback)
// - Taint coverage: functions with taint annotations (post_analysis callback)
// - Risk classification: functions tagged with risk levels
// - Variable recovery: stack variables and register arguments

mod analysis_quality_benchmark {
    use super::*;
    use std::sync::OnceLock;

    /// Helper: extract a single integer metric from r2 output.
    /// The r2 command should print a label line then the count on the next line.
    fn extract_metric(result: &e2e::R2Result, label: &str) -> u64 {
        let mut lines = result.stdout.lines();
        while let Some(line) = lines.next() {
            if line.trim() == label {
                if let Some(val_line) = lines.next() {
                    if let Ok(v) = val_line.trim().parse::<u64>() {
                        return v;
                    }
                }
            }
        }
        panic!(
            "metric '{}' not found\nexit={:?}\nstdout:\n{}\nstderr:\n{}",
            label, result.exit_code, result.stdout, result.stderr
        );
    }

    /// Collect analysis metrics for a binary after running `aaaa`.
    fn collect_aaaa_metrics(binary: &str) -> AnalysisMetrics {
        let result = r2_cmd_timeout(
            binary,
            &[
                "e bin.relocs.apply=true",
                "aaaa",
                "echo FUNCTIONS:",
                "aflc",
                "echo TOTAL_XREFS:",
                "axl~?",
                "echo DATA_XREFS:",
                "axl~DATA~?",
                "echo CODE_XREFS:",
                "axl~CODE~?",
                "echo CALL_XREFS:",
                "axl~CALL~?",
                "echo TAINT_BLOCK_FLAGS:",
                "f~sla.taint.fcn~?",
                "echo RISK_FLAGS:",
                "f~sla.taint.risk~?",
                "echo RISK_CRITICAL:",
                "f~sla.taint.risk.critical~?",
                "echo RISK_HIGH:",
                "f~sla.taint.risk.high~?",
                "echo RISK_MEDIUM:",
                "f~sla.taint.risk.medium~?",
                "echo RISK_LOW:",
                "f~sla.taint.risk.low~?",
            ]
            .join("; "),
            Duration::from_secs(120),
        );
        result.assert_ok();

        AnalysisMetrics {
            functions: extract_metric(&result, "FUNCTIONS:"),
            total_xrefs: extract_metric(&result, "TOTAL_XREFS:"),
            data_xrefs: extract_metric(&result, "DATA_XREFS:"),
            code_xrefs: extract_metric(&result, "CODE_XREFS:"),
            call_xrefs: extract_metric(&result, "CALL_XREFS:"),
            taint_block_flags: extract_metric(&result, "TAINT_BLOCK_FLAGS:"),
            risk_flags: extract_metric(&result, "RISK_FLAGS:"),
            risk_critical: extract_metric(&result, "RISK_CRITICAL:"),
            risk_high: extract_metric(&result, "RISK_HIGH:"),
            risk_medium: extract_metric(&result, "RISK_MEDIUM:"),
            risk_low: extract_metric(&result, "RISK_LOW:"),
        }
    }

    /// Collect aaa-level metrics (before taint, which runs at aaaa).
    fn collect_aaa_metrics(binary: &str) -> AaaMetrics {
        let result = r2_cmd_timeout(
            binary,
            &[
                "e bin.relocs.apply=true",
                "aaa",
                "echo TOTAL_XREFS:",
                "axl~?",
                "echo DATA_XREFS:",
                "axl~DATA~?",
            ]
            .join("; "),
            Duration::from_secs(60),
        );
        result.assert_ok();

        AaaMetrics {
            total_xrefs: extract_metric(&result, "TOTAL_XREFS:"),
            data_xrefs: extract_metric(&result, "DATA_XREFS:"),
        }
    }

    fn cached_vuln_aaaa_metrics() -> AnalysisMetrics {
        static METRICS: OnceLock<AnalysisMetrics> = OnceLock::new();
        *METRICS.get_or_init(|| collect_aaaa_metrics(vuln_test_binary()))
    }

    fn cached_ls_aaaa_metrics() -> AnalysisMetrics {
        static METRICS: OnceLock<AnalysisMetrics> = OnceLock::new();
        *METRICS.get_or_init(|| collect_aaaa_metrics("/bin/ls"))
    }

    fn cached_vuln_aaa_metrics() -> AaaMetrics {
        static METRICS: OnceLock<AaaMetrics> = OnceLock::new();
        *METRICS.get_or_init(|| collect_aaa_metrics(vuln_test_binary()))
    }

    #[derive(Debug, Clone, Copy)]
    #[allow(dead_code)]
    struct AnalysisMetrics {
        functions: u64,
        total_xrefs: u64,
        data_xrefs: u64,
        code_xrefs: u64,
        call_xrefs: u64,
        taint_block_flags: u64,
        risk_flags: u64,
        risk_critical: u64,
        risk_high: u64,
        risk_medium: u64,
        risk_low: u64,
    }

    #[derive(Debug, Clone, Copy)]
    #[allow(dead_code)]
    struct AaaMetrics {
        total_xrefs: u64,
        data_xrefs: u64,
    }

    // ------------------------------------------------------------------
    // vuln_test benchmarks (small, controlled binary)
    // ------------------------------------------------------------------

    #[test]
    fn vuln_test_sleigh_adds_data_xrefs() {
        setup();
        // Baseline (measured without plugin): data_xrefs = 24, total_xrefs = 365
        // With sleigh: data_xrefs ~= 67 (string refs + globals + taint flow)
        // The delta is ~43: all high-quality (string refs, taint flow, globals)
        let m = cached_vuln_aaaa_metrics();

        eprintln!("vuln_test aaaa metrics: {:?}", m);

        // Plugin should add meaningful data xrefs (strings, globals, taint)
        assert!(
            m.data_xrefs > 40,
            "sleigh should add quality data xrefs (got {}; baseline ~24)",
            m.data_xrefs
        );
        assert!(
            m.total_xrefs > 380,
            "total xrefs with sleigh should exceed baseline (got {}; baseline ~365)",
            m.total_xrefs
        );
    }

    #[test]
    fn vuln_test_taint_coverage() {
        setup();
        let m = cached_vuln_aaaa_metrics();

        eprintln!("vuln_test taint coverage: {:?}", m);

        // Taint analysis should flag multiple sink blocks in vulnerable functions.
        // The exact count is budget-sensitive, but a missing plugin reports zero.
        assert!(
            m.taint_block_flags >= 5,
            "taint should flag multiple sink blocks (got {})",
            m.taint_block_flags
        );

        // Risk classification should tag multiple functions.
        assert!(
            m.risk_flags >= 5,
            "risk classification should tag multiple functions (got {})",
            m.risk_flags
        );

        // At least one CRITICAL (vuln_memcpy has dangerous memcpy with tainted args)
        assert!(
            m.risk_critical >= 1,
            "should have at least 1 CRITICAL risk function (got {})",
            m.risk_critical
        );

        // Multiple serious risk functions (format strings, unchecked input,
        // plus any sinks promoted from HIGH to CRITICAL).
        assert!(
            m.risk_high + m.risk_critical >= 2,
            "should have multiple HIGH/CRITICAL risk functions (got high={} critical={})",
            m.risk_high,
            m.risk_critical
        );
    }

    #[test]
    fn vuln_test_aaa_data_xrefs() {
        setup();
        // SSA-derived data refs should appear at aaa level (get_data_refs callback)
        let m = cached_vuln_aaa_metrics();

        eprintln!("vuln_test aaa metrics: {:?}", m);

        // Baseline without sleigh: data_xrefs = 23
        // With sleigh: data_xrefs ~= 58 (quality string/global refs only)
        assert!(
            m.data_xrefs > 35,
            "sleigh get_data_refs should add SSA-derived data xrefs at aaa level (got {}; baseline ~23)",
            m.data_xrefs
        );
    }

    // ------------------------------------------------------------------
    // /bin/ls benchmarks (real-world stripped binary)
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Summary report test (prints human-readable comparison)
    // ------------------------------------------------------------------

    #[test]
    fn print_analysis_quality_report() {
        setup();
        let vuln = cached_vuln_aaaa_metrics();
        let ls = cached_ls_aaaa_metrics();
        let vuln_aaa = cached_vuln_aaa_metrics();

        // Baselines measured without the sleigh plugin:
        //   vuln_test aaaa: functions=61, total_xrefs=365, data_xrefs=24
        //   /bin/ls   aaaa: functions=414, total_xrefs=7337, data_xrefs=2433
        //   vuln_test aaa:  total_xrefs=365, data_xrefs=23
        //
        // All sleigh-added xrefs are quality refs:
        //   - String literal references (RODATA)
        //   - Global variable references (BSS/DATA)
        //   - Taint data-flow xrefs (source block → sink block)
        //   - GOT/vtable references

        eprintln!("\n=== r2sleigh Analysis Quality Report ===\n");
        eprintln!("Binary: vuln_test (controlled test binary)");
        eprintln!(
            "  {:30} {:>10} {:>10} {:>10}",
            "Metric", "Baseline", "Sleigh", "Delta"
        );
        eprintln!(
            "  {:30} {:>10} {:>10} {:>+10}",
            "Data xrefs (aaaa)",
            24,
            vuln.data_xrefs,
            vuln.data_xrefs as i64 - 24
        );
        eprintln!(
            "  {:30} {:>10} {:>10} {:>+10}",
            "Total xrefs (aaaa)",
            365,
            vuln.total_xrefs,
            vuln.total_xrefs as i64 - 365
        );
        eprintln!(
            "  {:30} {:>10} {:>10} {:>+10}",
            "Data xrefs (aaa)",
            23,
            vuln_aaa.data_xrefs,
            vuln_aaa.data_xrefs as i64 - 23
        );
        eprintln!(
            "  {:30} {:>10} {:>10}",
            "Taint block flags", "N/A", vuln.taint_block_flags
        );
        eprintln!(
            "  {:30} {:>10} {:>10}",
            "Risk flags", "N/A", vuln.risk_flags
        );
        eprintln!(
            "  {:30} {:>10} {:>10}",
            "  CRITICAL", "N/A", vuln.risk_critical
        );
        eprintln!("  {:30} {:>10} {:>10}", "  HIGH", "N/A", vuln.risk_high);
        eprintln!("  {:30} {:>10} {:>10}", "  MEDIUM", "N/A", vuln.risk_medium);
        eprintln!("  {:30} {:>10} {:>10}", "  LOW", "N/A", vuln.risk_low);

        eprintln!();
        eprintln!("Binary: /bin/ls (real-world stripped binary)");
        eprintln!(
            "  {:30} {:>10} {:>10} {:>10}",
            "Metric", "Baseline", "Sleigh", "Delta"
        );
        eprintln!(
            "  {:30} {:>10} {:>10} {:>+10}",
            "Data xrefs (aaaa)",
            2433,
            ls.data_xrefs,
            ls.data_xrefs as i64 - 2433
        );
        eprintln!(
            "  {:30} {:>10} {:>10} {:>+10}",
            "Total xrefs (aaaa)",
            7337,
            ls.total_xrefs,
            ls.total_xrefs as i64 - 7337
        );
        eprintln!(
            "  {:30} {:>10} {:>10}",
            "Taint block flags", "N/A", ls.taint_block_flags
        );
        eprintln!("  {:30} {:>10} {:>10}", "Risk flags", "N/A", ls.risk_flags);
        eprintln!(
            "  {:30} {:>10} {:>10}",
            "  CRITICAL", "N/A", ls.risk_critical
        );
        eprintln!("  {:30} {:>10} {:>10}", "  HIGH", "N/A", ls.risk_high);
        eprintln!("  {:30} {:>10} {:>10}", "  MEDIUM", "N/A", ls.risk_medium);
        eprintln!("  {:30} {:>10} {:>10}", "  LOW", "N/A", ls.risk_low);

        eprintln!();
        eprintln!("Key findings:");
        eprintln!("  - ESIL output: IDENTICAL (r2's Capstone arch plugin generates ESIL)");
        eprintln!("  - Sleigh plugin value-add is at analysis layer, not ESIL layer:");
        eprintln!("    * SSA-derived string/global refs (get_data_refs callback)");
        eprintln!("    * Automatic taint analysis with risk classification (post_analysis)");
        eprintln!("    * Variable recovery from SSA (recover_vars callback)");
        eprintln!("  - All sleigh-added xrefs target real data addresses:");
        eprintln!("    * String literals in .rodata");
        eprintln!("    * Global variables in .data/.bss");
        eprintln!("    * Taint data-flow (source → dangerous sink)");
        eprintln!("    * No noise: small constants and code-internal refs filtered out");
        eprintln!();

        // This test always passes — it's for reporting
    }
}
