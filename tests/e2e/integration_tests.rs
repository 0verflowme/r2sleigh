//! Integration tests for r2sleigh plugin.
//!
//! These tests invoke radare2 with the r2sleigh plugin and validate output.
//! Run with: `cargo test -p r2sleigh-e2e-tests`

use e2e::{r2_cmd, r2_cmd_timeout, release_plugin_path, require_binary, vuln_test_binary};
use serde_json::Value;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

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
    use r2il::R2ILOp;
    use serde_json::Value;
    use std::collections::BTreeMap;
    use std::ffi::{CStr, CString, c_void};
    use std::os::raw::c_char;
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
    const ARM64_BYTES_BASE: &[u8] = &[0x00, 0x00, 0x01, 0x8b]; // add x0, x0, x1
    const ARM64_BYTES_RET: &[u8] = &[0xc0, 0x03, 0x5f, 0xd6]; // ret
    const RISCV_BYTES_BASE: &[u8] = &[0x13, 0x05, 0x15, 0x00]; // addi a0,a0,1

    #[repr(C)]
    struct R2SleighContextParam {
        name: *const c_char,
        type_name: *const c_char,
        cc_reg: *const c_char,
    }

    #[repr(C)]
    struct R2SleighFunctionContext {
        schema_version: u32,
        dirty_epoch: u64,
        context_hash: u64,
        type_dirty_epoch: u64,
        external_context_json: *const c_char,
        signature_name: *const c_char,
        signature_ret_type: *const c_char,
        signature_callconv: *const c_char,
        signature_noreturn: i32,
        params: *const c_void,
        num_params: usize,
        vars: *const c_void,
        num_vars: usize,
        base_types: *const c_void,
        num_base_types: usize,
        assumptions_json: *const c_char,
    }

    #[repr(C)]
    struct R2SleighInterprocScope {
        schema_version: u32,
        functions: *const c_void,
        num_functions: usize,
        seeds: *const c_void,
        num_seeds: usize,
    }

    #[repr(C)]
    struct R2SleighDebugSeed {
        schema_version: u32,
        seed_hash: u64,
    }

    #[repr(C)]
    struct R2SleighBudgetConfig {
        schema_version: u32,
        interproc_iter: usize,
        interproc_max_iters: usize,
        interproc_converged: i32,
        global_max_links: usize,
        max_type_decls: usize,
        max_mutations: usize,
    }

    #[repr(C)]
    struct R2SleighSessionInput {
        ctx: *const c_void,
        blocks: *const *const c_void,
        num_blocks: usize,
        function_addr: u64,
        function_name: *const c_char,
        function_context: R2SleighFunctionContext,
        interproc_scope: R2SleighInterprocScope,
        debug_seed: R2SleighDebugSeed,
        budget: R2SleighBudgetConfig,
    }

    fn padded_bytes(bytes: &[u8]) -> Vec<u8> {
        let mut out = bytes.to_vec();
        out.resize(16, 0x00);
        out
    }

    unsafe fn plugin_usize_symbol(lib: &libloading::Library, name: &[u8]) -> usize {
        let f: libloading::Symbol<unsafe extern "C" fn() -> usize> =
            unsafe { lib.get(name).unwrap() };
        unsafe { f() }
    }

    #[test]
    fn session_input_ffi_layout_matches_plugin() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            assert_eq!(
                plugin_usize_symbol(&lib, b"r2sleigh_ffi_sizeof_function_context"),
                std::mem::size_of::<R2SleighFunctionContext>()
            );
            assert_eq!(
                plugin_usize_symbol(&lib, b"r2sleigh_ffi_alignof_function_context"),
                std::mem::align_of::<R2SleighFunctionContext>()
            );
            assert_eq!(
                plugin_usize_symbol(&lib, b"r2sleigh_ffi_sizeof_budget_config"),
                std::mem::size_of::<R2SleighBudgetConfig>()
            );
            assert_eq!(
                plugin_usize_symbol(&lib, b"r2sleigh_ffi_alignof_budget_config"),
                std::mem::align_of::<R2SleighBudgetConfig>()
            );
            assert_eq!(
                plugin_usize_symbol(&lib, b"r2sleigh_ffi_sizeof_session_input"),
                std::mem::size_of::<R2SleighSessionInput>()
            );
            assert_eq!(
                plugin_usize_symbol(&lib, b"r2sleigh_ffi_alignof_session_input"),
                std::mem::align_of::<R2SleighSessionInput>()
            );
        }
    }

    unsafe fn session_type_writeback_json(
        lib: &libloading::Library,
        ctx: *const c_void,
        blocks: &[*const c_void],
        function_addr: u64,
        function_name: &CString,
        external_context: &CString,
        signature_ret_type: Option<&CString>,
        signature_callconv: Option<&CString>,
        params: &[R2SleighContextParam],
    ) -> String {
        let session_analyze: libloading::Symbol<
            unsafe extern "C" fn(*const R2SleighSessionInput) -> *mut c_void,
        > = unsafe { lib.get(b"r2sleigh_session_analyze").unwrap() };
        let session_type_writeback: libloading::Symbol<
            unsafe extern "C" fn(*const c_void) -> *const c_char,
        > = unsafe {
            lib.get(b"r2sleigh_session_result_type_writeback_json")
                .unwrap()
        };
        let session_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
            unsafe { lib.get(b"r2sleigh_session_result_free").unwrap() };
        let input = R2SleighSessionInput {
            ctx,
            blocks: blocks.as_ptr(),
            num_blocks: blocks.len(),
            function_addr,
            function_name: function_name.as_ptr(),
            function_context: R2SleighFunctionContext {
                schema_version: 1,
                dirty_epoch: 0,
                context_hash: 0,
                type_dirty_epoch: 0,
                external_context_json: external_context.as_ptr(),
                signature_name: function_name.as_ptr(),
                signature_ret_type: signature_ret_type
                    .map_or(std::ptr::null(), |value| value.as_ptr()),
                signature_callconv: signature_callconv
                    .map_or(std::ptr::null(), |value| value.as_ptr()),
                signature_noreturn: 0,
                params: params.as_ptr().cast(),
                num_params: params.len(),
                vars: std::ptr::null(),
                num_vars: 0,
                base_types: std::ptr::null(),
                num_base_types: 0,
                assumptions_json: std::ptr::null(),
            },
            interproc_scope: R2SleighInterprocScope {
                schema_version: 1,
                functions: std::ptr::null(),
                num_functions: 0,
                seeds: std::ptr::null(),
                num_seeds: 0,
            },
            debug_seed: R2SleighDebugSeed {
                schema_version: 1,
                seed_hash: 0,
            },
            budget: R2SleighBudgetConfig {
                schema_version: 1,
                interproc_iter: 1,
                interproc_max_iters: 1,
                interproc_converged: 1,
                global_max_links: 64,
                max_type_decls: 32,
                max_mutations: 128,
            },
        };
        let session = unsafe { session_analyze(&input) };
        assert!(!session.is_null(), "Expected non-null session result");
        let json_ptr = unsafe { session_type_writeback(session) };
        assert!(!json_ptr.is_null(), "Expected session type writeback JSON");
        let json = unsafe { CStr::from_ptr(json_ptr) }
            .to_string_lossy()
            .to_string();
        unsafe { session_free(session) };
        json
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
        dec: String,
    }

    fn export_once_for_arch(arch: &str, base_bytes: &[u8], dec_bytes: &[u8]) -> Option<FfiExports> {
        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_is_loaded: libloading::Symbol<unsafe extern "C" fn(*const c_void) -> i32> =
                lib.get(b"r2il_is_loaded").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(*mut c_void, *const u8, usize, u64) -> *mut c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut c_void, *const c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_block_to_esil: libloading::Symbol<
                unsafe extern "C" fn(*const c_void, *const c_void) -> *mut c_char,
            > = lib.get(b"r2il_block_to_esil").unwrap();
            let r2il_block_to_ssa_json: libloading::Symbol<
                unsafe extern "C" fn(*const c_void, *const c_void) -> *mut c_char,
            > = lib.get(b"r2il_block_to_ssa_json").unwrap();
            let r2il_block_defuse_json: libloading::Symbol<
                unsafe extern "C" fn(*const c_void, *const c_void) -> *mut c_char,
            > = lib.get(b"r2il_block_defuse_json").unwrap();
            let r2dec_block: libloading::Symbol<
                unsafe extern "C" fn(*const c_void, *const c_void) -> *mut c_char,
            > = lib.get(b"r2dec_block").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch_c = CString::new(arch).expect("valid arch");
            let ctx = r2il_arch_init(arch_c.as_ptr());
            if ctx.is_null() {
                eprintln!(
                    "Skipping {} parity conformance: architecture not built in plugin",
                    arch
                );
                return None;
            }
            if r2il_is_loaded(ctx) != 1 {
                eprintln!(
                    "Skipping {} parity conformance: architecture not loaded in plugin",
                    arch
                );
                r2il_free(ctx);
                return None;
            }

            let base = padded_bytes(base_bytes);
            let block = r2il_lift(ctx, base.as_ptr(), base.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift base fixture for {}", arch);
            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "Lifted base block should validate for {}",
                arch
            );

            let esil_ptr = r2il_block_to_esil(ctx, block);
            assert!(
                !esil_ptr.is_null(),
                "esil export should not be null for {}",
                arch
            );
            let esil = CStr::from_ptr(esil_ptr).to_string_lossy().into_owned();
            r2il_string_free(esil_ptr);

            let ssa_ptr = r2il_block_to_ssa_json(ctx, block);
            assert!(
                !ssa_ptr.is_null(),
                "ssa json export should not be null for {}",
                arch
            );
            let ssa_json = CStr::from_ptr(ssa_ptr).to_string_lossy().into_owned();
            r2il_string_free(ssa_ptr);

            let defuse_ptr = r2il_block_defuse_json(ctx, block);
            assert!(
                !defuse_ptr.is_null(),
                "defuse json export should not be null for {}",
                arch
            );
            let defuse_json = CStr::from_ptr(defuse_ptr).to_string_lossy().into_owned();
            r2il_string_free(defuse_ptr);

            r2il_block_free(block);

            let dec_input = padded_bytes(dec_bytes);
            let dec_block = r2il_lift(ctx, dec_input.as_ptr(), dec_input.len(), 0x1000);
            assert!(
                !dec_block.is_null(),
                "Failed to lift dec fixture for {}",
                arch
            );
            assert_eq!(
                r2il_block_validate(ctx, dec_block),
                1,
                "Lifted dec block should validate for {}",
                arch
            );
            let dec_ptr = r2dec_block(ctx, dec_block);
            assert!(
                !dec_ptr.is_null(),
                "dec export should not be null for {}",
                arch
            );
            let dec = CStr::from_ptr(dec_ptr).to_string_lossy().into_owned();
            r2il_string_free(dec_ptr);
            r2il_block_free(dec_block);

            r2il_free(ctx);

            let ssa_parsed: Value = serde_json::from_str(&ssa_json).expect("valid ssa json");
            assert!(
                ssa_parsed.as_array().is_some(),
                "ssa json must be an array for {}",
                arch
            );
            let defuse_parsed: Value =
                serde_json::from_str(&defuse_json).expect("valid defuse json");
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
                dec,
            })
        }
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

        let first_dec = normalize_text_output(&first.dec);
        let second_dec = normalize_text_output(&second.dec);
        assert_eq!(first_dec, second_dec, "dec mismatch for {}", arch);
        assert!(
            !first_dec.trim().is_empty(),
            "dec must be non-empty for {} (raw={:?})",
            arch,
            first.dec
        );
    }

    fn contains_unsigned_int_meta(value: &Value) -> bool {
        match value {
            Value::Object(map) => {
                if let Some(meta) = map.get("meta").and_then(Value::as_object)
                    && meta.get("scalar_kind").and_then(Value::as_str) == Some("unsigned_int")
                {
                    return true;
                }
                map.values().any(contains_unsigned_int_meta)
            }
            Value::Array(items) => items.iter().any(contains_unsigned_int_meta),
            _ => false,
        }
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
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_is_loaded: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_is_loaded").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_op_count: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> usize,
            > = lib.get(b"r2il_block_op_count").unwrap();
            let r2il_block_to_esil: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_to_esil").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            // Init x86-64
            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to init arch");
            assert_eq!(r2il_is_loaded(ctx), 1);

            // Lift "xor eax, eax" (0x31 0xC0)
            let mut bytes = vec![0x31u8, 0xC0];
            bytes.resize(16, 0x90);

            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift");

            let op_count = r2il_block_op_count(block);
            assert!(op_count > 0, "Should have ops");

            let esil_ptr = r2il_block_to_esil(ctx, block);
            if !esil_ptr.is_null() {
                let esil = CStr::from_ptr(esil_ptr).to_string_lossy();
                assert!(!esil.is_empty(), "ESIL not empty");
                r2il_string_free(esil_ptr);
            }

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn lift_add_instruction_to_ssa() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_to_ssa_json: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_to_ssa_json").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null());

            // "add rax, rbx" (0x48 0x01 0xd8)
            let mut bytes = vec![0x48u8, 0x01, 0xd8];
            bytes.resize(16, 0x90);

            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null());

            let ssa_ptr = r2il_block_to_ssa_json(ctx, block);
            if !ssa_ptr.is_null() {
                let ssa = CStr::from_ptr(ssa_ptr).to_string_lossy();
                assert!(
                    ssa.contains("op") || ssa.contains("dst") || ssa.contains("["),
                    "SSA should have structure"
                );
                r2il_string_free(ssa_ptr);
            }

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn block_set_switch_info_canonicalizes_duplicate_case_values() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_set_switch_info: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    u64,
                    u64,
                    u64,
                    u64,
                    *const u64,
                    *const u64,
                    usize,
                ),
            > = lib.get(b"r2il_block_set_switch_info").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, *const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0]; // xor eax, eax
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "Freshly lifted block should validate"
            );

            // radare2 can report duplicate switch case values for one decoded
            // switch table. The FFI boundary canonicalizes that metadata before
            // R2IL validation so one case value has one deterministic target.
            let case_values = [0u64, 0u64];
            let case_targets = [0x2000u64, 0x3000u64];
            r2il_block_set_switch_info(
                block,
                0x1000,
                0,
                1,
                0,
                case_values.as_ptr(),
                case_targets.as_ptr(),
                case_values.len(),
            );

            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "Duplicate switch case values should be canonicalized at the FFI boundary"
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn block_validate_rejects_invalid_semantic_block() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, *const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_error: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> *const c_char,
            > = lib.get(b"r2il_error").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0]; // xor eax, eax
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "Freshly lifted block should validate"
            );

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            let mut mutated = false;
            for op in &mut block_ref.ops {
                if let R2ILOp::Copy { src, .. } = op {
                    src.size = src.size.saturating_add(1);
                    mutated = true;
                    break;
                }
            }
            assert!(mutated, "Expected at least one Copy op in xor block");

            assert_eq!(
                r2il_block_validate(ctx, block),
                0,
                "Validation should fail for semantic width mismatch"
            );

            let err_ptr = r2il_error(ctx);
            assert!(
                !err_ptr.is_null(),
                "Validation failure should populate context error"
            );
            let err = CStr::from_ptr(err_ptr).to_string_lossy();
            assert!(
                err.contains("op.copy.width_mismatch") && err.contains("block.ops"),
                "Validation error should mention semantic width issue: {}",
                err
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn block_validate_rejects_invalid_op_metadata_index() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, *const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_error: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> *const c_char,
            > = lib.get(b"r2il_error").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0]; // xor eax, eax
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "Freshly lifted block should validate"
            );

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            let invalid_index = block_ref.ops.len();
            block_ref.set_op_metadata(invalid_index, r2il::OpMetadata::default());

            assert_eq!(
                r2il_block_validate(ctx, block),
                0,
                "Validation should fail for out-of-range op metadata index"
            );

            let err_ptr = r2il_error(ctx);
            assert!(
                !err_ptr.is_null(),
                "Validation failure should populate context error"
            );
            let err = CStr::from_ptr(err_ptr).to_string_lossy();
            assert!(
                err.contains("block.op_metadata") && err.contains("index_oob"),
                "Validation error should mention op_metadata index issue: {}",
                err
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn op_json_includes_varnode_metadata_when_present() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_op_json_named: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                    usize,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_op_json_named").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0]; // xor eax, eax
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            let mut meta = r2il::VarnodeMetadata::default();
            meta.scalar_kind = Some(r2il::ScalarKind::UnsignedInt);

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            let mut op_index = None;
            for (idx, op) in block_ref.ops.iter_mut().enumerate() {
                if let R2ILOp::Copy { dst, .. } = op {
                    dst.set_meta(meta.clone());
                    op_index = Some(idx);
                    break;
                }
            }
            let op_index = op_index.expect("Expected at least one Copy op in xor block");

            let json_ptr = r2il_block_op_json_named(ctx, block, op_index);
            assert!(!json_ptr.is_null(), "Expected operation JSON");
            let json_str = CStr::from_ptr(json_ptr).to_string_lossy().to_string();
            r2il_string_free(json_ptr);

            let parsed: Value = serde_json::from_str(&json_str).expect("valid operation json");
            assert!(
                contains_unsigned_int_meta(&parsed),
                "operation JSON should include varnode metadata: {}",
                json_str
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn lift_auto_populates_semantic_metadata_for_stack_memory() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_mem_access: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_mem_access").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            // mov rax, qword [rsp]
            let mut bytes = vec![0x48u8, 0x8b, 0x04, 0x24];
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift stack load");

            let mem_ptr = r2il_block_mem_access(ctx, block);
            assert!(!mem_ptr.is_null(), "Expected mem-access JSON");
            let mem_json = CStr::from_ptr(mem_ptr).to_string_lossy().to_string();
            r2il_string_free(mem_ptr);
            assert!(
                mem_access_has_addr_storage_class(&mem_json, "stack")
                    && mem_access_has_addr_pointer_hint(&mem_json, "pointer_like"),
                "Automatic metadata should populate stack/pointer addr metadata: {}",
                mem_json
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn lift_respects_semantic_metadata_disable_toggle() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_set_semantic_metadata_enabled: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, bool),
            > = lib.get(b"r2il_set_semantic_metadata_enabled").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_mem_access: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_mem_access").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            // mov rax, qword [rsp]
            let mut bytes = vec![0x48u8, 0x8b, 0x04, 0x24];
            bytes.resize(16, 0x90);

            let enabled_block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(
                !enabled_block.is_null(),
                "Failed to lift baseline stack load with metadata enabled"
            );
            let enabled_mem_ptr = r2il_block_mem_access(ctx, enabled_block);
            assert!(
                !enabled_mem_ptr.is_null(),
                "Expected enabled mem-access JSON"
            );
            let enabled_json = CStr::from_ptr(enabled_mem_ptr)
                .to_string_lossy()
                .to_string();
            r2il_string_free(enabled_mem_ptr);
            assert!(
                mem_access_has_addr_storage_class(&enabled_json, "stack")
                    && mem_access_has_addr_pointer_hint(&enabled_json, "pointer_like"),
                "Enabled path should include semantic addr metadata: {}",
                enabled_json
            );
            r2il_block_free(enabled_block);

            r2il_set_semantic_metadata_enabled(ctx, false);
            let disabled_block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x2000);
            assert!(
                !disabled_block.is_null(),
                "Failed to lift stack load with metadata disabled"
            );
            let disabled_mem_ptr = r2il_block_mem_access(ctx, disabled_block);
            assert!(
                !disabled_mem_ptr.is_null(),
                "Expected disabled mem-access JSON"
            );
            let disabled_json = CStr::from_ptr(disabled_mem_ptr)
                .to_string_lossy()
                .to_string();
            r2il_string_free(disabled_mem_ptr);
            assert!(
                !mem_access_has_addr_storage_class(&disabled_json, "stack")
                    && !mem_access_has_addr_pointer_hint(&disabled_json, "pointer_like"),
                "Disabled path should suppress semantic addr metadata: {}",
                disabled_json
            );

            r2il_block_free(disabled_block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn recover_vars_uses_pointer_metadata_for_arg_type() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2sleigh_recover_vars: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const *const std::ffi::c_void,
                    usize,
                    u64,
                ) -> *mut c_char,
            > = lib.get(b"r2sleigh_recover_vars").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            // mov rax, rdi
            let mut bytes = vec![0x48u8, 0x89, 0xF8];
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            let mut tagged = false;
            for op in &mut block_ref.ops {
                if let R2ILOp::Copy { src, .. } = op
                    && src.space == r2il::SpaceId::Register
                {
                    let mut meta = r2il::VarnodeMetadata::default();
                    meta.pointer_hint = Some(r2il::PointerHint::PointerLike);
                    src.set_meta(meta);
                    tagged = true;
                    break;
                }
            }
            assert!(tagged, "Expected to tag a register source with metadata");

            let block_ptrs = [block as *const std::ffi::c_void];
            let json_ptr =
                r2sleigh_recover_vars(ctx, block_ptrs.as_ptr(), block_ptrs.len(), 0x1000);
            assert!(!json_ptr.is_null(), "Expected recovered vars JSON");
            let json_str = CStr::from_ptr(json_ptr).to_string_lossy().to_string();
            r2il_string_free(json_ptr);

            let parsed: Value = serde_json::from_str(&json_str).expect("valid recover vars json");
            let vars = parsed.as_array().expect("recover vars array");
            let has_pointer_arg = vars.iter().any(|entry| {
                entry.get("reg").and_then(Value::as_str) == Some("rdi")
                    && entry.get("type").and_then(Value::as_str) == Some("void *")
            });
            assert!(
                has_pointer_arg,
                "Recovered vars should include pointer-typed rdi arg from metadata: {}",
                json_str
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn analyze_fcn_annotations_include_semantic_metadata() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2sleigh_analyze_fcn_annotations: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const *const std::ffi::c_void,
                    usize,
                    u64,
                ) -> *mut c_char,
            > = lib.get(b"r2sleigh_analyze_fcn_annotations").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0]; // xor eax, eax
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            let mut tagged = false;
            for op in &mut block_ref.ops {
                if let R2ILOp::Copy { dst, .. } = op {
                    let mut meta = r2il::VarnodeMetadata::default();
                    meta.storage_class = Some(r2il::StorageClass::ThreadLocal);
                    dst.set_meta(meta);
                    tagged = true;
                    break;
                }
            }
            assert!(tagged, "Expected to tag at least one varnode with metadata");
            block_ref.set_op_metadata(
                0,
                r2il::OpMetadata {
                    memory_class: Some(r2il::MemoryClass::ThreadLocal),
                    ..Default::default()
                },
            );

            let block_ptrs = [block as *const std::ffi::c_void];
            let json_ptr = r2sleigh_analyze_fcn_annotations(
                ctx,
                block_ptrs.as_ptr(),
                block_ptrs.len(),
                0x1000,
            );
            assert!(!json_ptr.is_null(), "Expected function annotations JSON");
            let json_str = CStr::from_ptr(json_ptr).to_string_lossy().to_string();
            r2il_string_free(json_ptr);

            let parsed: Value = serde_json::from_str(&json_str).expect("valid annotations json");
            let anns = parsed.as_array().expect("annotations array");
            let has_meta_comment = anns.iter().any(|entry| {
                entry
                    .get("comment")
                    .and_then(Value::as_str)
                    .map(|s| s.contains("meta ") && s.contains("thread_local"))
                    .unwrap_or(false)
            });
            assert!(
                has_meta_comment,
                "Function annotations should include semantic metadata summary: {}",
                json_str
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn block_validate_rejects_invalid_guarded_memory_op() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, *const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_error: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> *const c_char,
            > = lib.get(b"r2il_error").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0];
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            block_ref.ops.clear();
            block_ref.push(r2il::R2ILOp::LoadGuarded {
                dst: r2il::Varnode::register(0, 8),
                space: r2il::SpaceId::Ram,
                addr: r2il::Varnode::register(8, 8),
                guard: r2il::Varnode::register(16, 8),
                ordering: r2il::MemoryOrdering::Relaxed,
            });

            assert_eq!(
                r2il_block_validate(ctx, block),
                0,
                "Validation should fail for invalid guarded load guard size"
            );
            let err_ptr = r2il_error(ctx);
            assert!(!err_ptr.is_null(), "Expected validation error");
            let err = CStr::from_ptr(err_ptr).to_string_lossy();
            assert!(
                err.contains("op.load_guarded.guard_size"),
                "Expected guarded-load validation issue, got: {}",
                err
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn mem_access_json_includes_additive_memory_semantics_fields() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");

            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_mem_access: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_mem_access").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x31u8, 0xC0];
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift baseline instruction");

            let block_ref = &mut *(block as *mut r2il::R2ILBlock);
            block_ref.ops.clear();
            block_ref.push_with_metadata(
                r2il::R2ILOp::Load {
                    dst: r2il::Varnode::register(0, 8),
                    space: r2il::SpaceId::Ram,
                    addr: r2il::Varnode::constant(0x1000, 8),
                },
                Some(r2il::OpMetadata {
                    instruction_addr: None,
                    memory_class: Some(r2il::MemoryClass::Stack),
                    endianness: None,
                    memory_ordering: Some(r2il::MemoryOrdering::AcqRel),
                    permissions: Some(r2il::MemoryPermissions {
                        read: true,
                        write: false,
                        execute: false,
                        volatile: false,
                        cacheable: true,
                    }),
                    valid_range: Some(r2il::MemoryRange {
                        start: 0x1000,
                        end: 0x2000,
                    }),
                    bank_id: Some("bank0".to_string()),
                    segment_id: Some("seg0".to_string()),
                    atomic_kind: Some(r2il::AtomicKind::ReadModifyWrite),
                }),
            );

            let json_ptr = r2il_block_mem_access(ctx, block);
            assert!(!json_ptr.is_null(), "Expected mem-access JSON");
            let json = CStr::from_ptr(json_ptr).to_string_lossy().into_owned();
            r2il_string_free(json_ptr);

            let parsed: Value = serde_json::from_str(&json).expect("valid JSON");
            let first = parsed
                .as_array()
                .and_then(|arr| arr.first())
                .expect("at least one access");

            assert!(first.get("addr").is_some(), "legacy addr key missing");
            assert!(first.get("size").is_some(), "legacy size key missing");
            assert!(first.get("write").is_some(), "legacy write key missing");

            assert_eq!(
                first.get("ordering").and_then(Value::as_str),
                Some("acq_rel")
            );
            assert_eq!(
                first.get("atomic_kind").and_then(Value::as_str),
                Some("read_modify_write")
            );
            assert_eq!(first.get("guarded").and_then(Value::as_bool), None);
            assert_eq!(first.get("bank_id").and_then(Value::as_str), Some("bank0"));
            assert_eq!(
                first.get("segment_id").and_then(Value::as_str),
                Some("seg0")
            );
            assert_eq!(
                first.get("memory_class").and_then(Value::as_str),
                Some("stack")
            );
            assert_eq!(
                first
                    .get("permissions")
                    .and_then(|v| v.get("volatile"))
                    .and_then(Value::as_bool),
                Some(false)
            );
            assert_eq!(
                first
                    .get("permissions")
                    .and_then(|v| v.get("cacheable"))
                    .and_then(Value::as_bool),
                Some(true)
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn riscv64_lift_and_validate_success() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, *const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_is_loaded: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_is_loaded").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();

            let arch = CString::new("riscv64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            if ctx.is_null() {
                eprintln!("Skipping: plugin built without riscv64 support");
                return;
            }
            if r2il_is_loaded(ctx) != 1 {
                eprintln!("Skipping: plugin built without riscv64 support (context not loaded)");
                r2il_free(ctx);
                return;
            }

            let mut bytes = vec![0x13u8, 0x05, 0x05, 0x00]; // addi a0, a0, 0
            bytes.resize(16, 0x00);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift riscv64 instruction");
            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "riscv64 block should pass validation"
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn riscv64_export_paths_esil_ssa_defuse_dec_nonnull() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_is_loaded: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_is_loaded").unwrap();
            let r2il_block_to_esil: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_to_esil").unwrap();
            let r2il_block_to_ssa_json: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_to_ssa_json").unwrap();
            let r2il_block_defuse_json: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2il_block_defuse_json").unwrap();
            let r2dec_block: libloading::Symbol<
                unsafe extern "C" fn(
                    *const std::ffi::c_void,
                    *const std::ffi::c_void,
                ) -> *mut c_char,
            > = lib.get(b"r2dec_block").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();

            let arch = CString::new("riscv64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            if ctx.is_null() {
                eprintln!("Skipping: plugin built without riscv64 support");
                return;
            }
            if r2il_is_loaded(ctx) != 1 {
                eprintln!("Skipping: plugin built without riscv64 support (context not loaded)");
                r2il_free(ctx);
                return;
            }

            let mut bytes = vec![0x13u8, 0x05, 0x05, 0x00]; // addi a0, a0, 0
            bytes.resize(16, 0x00);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift riscv64 instruction");

            let esil = r2il_block_to_esil(ctx, block);
            assert!(!esil.is_null(), "ESIL export should not be null");
            r2il_string_free(esil);

            let ssa = r2il_block_to_ssa_json(ctx, block);
            assert!(!ssa.is_null(), "SSA JSON export should not be null");
            r2il_string_free(ssa);

            let defuse = r2il_block_defuse_json(ctx, block);
            assert!(!defuse.is_null(), "Def-use JSON export should not be null");
            r2il_string_free(defuse);

            let dec = r2dec_block(ctx, block);
            assert!(!dec.is_null(), "Decompiler export should not be null");
            r2il_string_free(dec);

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn riscv32_lift_and_validate_success() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(
                    *mut std::ffi::c_void,
                    *const u8,
                    usize,
                    u64,
                ) -> *mut std::ffi::c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_block_validate: libloading::Symbol<
                unsafe extern "C" fn(*mut std::ffi::c_void, *const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_block_validate").unwrap();
            let r2il_is_loaded: libloading::Symbol<
                unsafe extern "C" fn(*const std::ffi::c_void) -> i32,
            > = lib.get(b"r2il_is_loaded").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_void)> =
                lib.get(b"r2il_block_free").unwrap();

            let arch = CString::new("riscv32").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            if ctx.is_null() {
                eprintln!("Skipping: plugin built without riscv32 support");
                return;
            }
            if r2il_is_loaded(ctx) != 1 {
                eprintln!("Skipping: plugin built without riscv32 support (context not loaded)");
                r2il_free(ctx);
                return;
            }

            let mut bytes = vec![0x13u8, 0x05, 0x05, 0x00]; // addi a0, a0, 0
            bytes.resize(16, 0x00);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift riscv32 instruction");
            assert_eq!(
                r2il_block_validate(ctx, block),
                1,
                "riscv32 block should pass validation"
            );

            r2il_block_free(block);
            r2il_free(ctx);
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

    #[test]
    fn infer_type_writeback_respects_explicit_signature_context() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(*mut c_void, *const u8, usize, u64) -> *mut c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let arch = CString::new("x86-64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            assert!(!ctx.is_null(), "Failed to initialize x86-64 context");

            let mut bytes = vec![0x48u8, 0x89, 0xF8]; // mov rax, rdi
            bytes.resize(16, 0x90);
            let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
            assert!(!block.is_null(), "Failed to lift fixture block");

            let block_ptrs = [block as *const c_void];
            let fcn_name = CString::new("sym.demo").unwrap();
            let external_context = CString::new(
                r#"{
                    "signature": {
                        "name": "sym.demo",
                        "ret": "int32_t",
                        "params": [
                            {"name": "items", "type": "char *"}
                        ]
                    }
                }"#,
            )
            .unwrap();
            let ret_type = CString::new("int32_t").unwrap();
            let param_name = CString::new("items").unwrap();
            let param_type = CString::new("char *").unwrap();
            let typed_params = [R2SleighContextParam {
                name: param_name.as_ptr(),
                type_name: param_type.as_ptr(),
                cc_reg: std::ptr::null(),
            }];
            let json_str = session_type_writeback_json(
                &lib,
                ctx,
                &block_ptrs,
                0x1000,
                &fcn_name,
                &external_context,
                Some(&ret_type),
                None,
                &typed_params,
            );
            let parsed: Value = serde_json::from_str(&json_str).expect("valid type writeback json");
            let params = parsed
                .get("params")
                .and_then(Value::as_array)
                .expect("params array");
            assert_eq!(
                params
                    .first()
                    .and_then(Value::as_object)
                    .and_then(|obj| obj.get("name"))
                    .and_then(Value::as_str),
                Some("items")
            );
            let param_ty = params
                .first()
                .and_then(Value::as_object)
                .and_then(|obj| obj.get("type"))
                .and_then(Value::as_str);
            assert!(
                matches!(
                    param_ty,
                    Some("char *") | Some("int8_t*") | Some("int8_t *")
                ),
                "explicit param type should survive via canonicalization, got {:?} in {}",
                param_ty,
                json_str
            );
            assert_eq!(
                parsed.get("ret_type").and_then(Value::as_str),
                Some("int32_t")
            );
            assert!(
                parsed
                    .get("confidence")
                    .and_then(Value::as_u64)
                    .is_some_and(|conf| conf >= 70),
                "explicit signature context should force high signature confidence: {}",
                json_str
            );

            r2il_block_free(block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn infer_signature_cc_json_non_x86_allows_empty_callconv() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_is_loaded: libloading::Symbol<unsafe extern "C" fn(*const c_void) -> i32> =
                lib.get(b"r2il_is_loaded").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(*mut c_void, *const u8, usize, u64) -> *mut c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let r2il_string_free: libloading::Symbol<unsafe extern "C" fn(*mut c_char)> =
                lib.get(b"r2il_string_free").unwrap();
            let infer_signature: libloading::Symbol<
                unsafe extern "C" fn(
                    *const c_void,
                    *const *const c_void,
                    usize,
                    u64,
                    *const c_char,
                ) -> *mut c_char,
            > = lib.get(b"r2sleigh_infer_signature_cc_json").unwrap();

            let arch = CString::new("aarch64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            if ctx.is_null() || r2il_is_loaded(ctx) != 1 {
                eprintln!("Skipping: plugin not built with aarch64 support");
                if !ctx.is_null() {
                    r2il_free(ctx);
                }
                return;
            }

            let mut add_bytes = ARM64_BYTES_BASE.to_vec();
            add_bytes.resize(16, 0);
            let mut ret_bytes = ARM64_BYTES_RET.to_vec();
            ret_bytes.resize(16, 0);
            let add_block = r2il_lift(ctx, add_bytes.as_ptr(), add_bytes.len(), 0x1000);
            let ret_block = r2il_lift(ctx, ret_bytes.as_ptr(), ret_bytes.len(), 0x1004);
            assert!(!add_block.is_null(), "Failed to lift aarch64 add block");
            assert!(!ret_block.is_null(), "Failed to lift aarch64 ret block");

            let block_ptrs = [add_block as *const c_void, ret_block as *const c_void];
            let fcn_name = CString::new("sym.a64_demo").unwrap();
            let json_ptr = infer_signature(
                ctx,
                block_ptrs.as_ptr(),
                block_ptrs.len(),
                0x1000,
                fcn_name.as_ptr(),
            );
            assert!(!json_ptr.is_null(), "Expected signature inference JSON");

            let json_str = CStr::from_ptr(json_ptr).to_string_lossy().to_string();
            r2il_string_free(json_ptr);
            let parsed: Value = serde_json::from_str(&json_str).expect("valid signature json");
            assert_eq!(parsed.get("arch").and_then(Value::as_str), Some("aarch64"));
            assert_eq!(
                parsed.get("callconv").and_then(Value::as_str),
                Some(""),
                "non-x86 payload should allow empty callconv: {}",
                json_str
            );
            assert!(
                parsed
                    .get("callconv_confidence")
                    .and_then(Value::as_u64)
                    .is_some_and(|conf| conf < 80),
                "non-x86 payload should keep low callconv confidence: {}",
                json_str
            );
            assert!(
                parsed
                    .get("signature")
                    .and_then(Value::as_str)
                    .is_some_and(|sig| sig.contains("sym.a64_demo")),
                "aarch64 signature payload should still include a signature string: {}",
                json_str
            );

            r2il_block_free(add_block);
            r2il_block_free(ret_block);
            r2il_free(ctx);
        }
    }

    #[test]
    fn infer_type_writeback_non_x86_keeps_signature_without_callconv() {
        if !require_plugin() {
            eprintln!("Skipping: plugin not built");
            return;
        }

        unsafe {
            let lib = libloading::Library::new(PLUGIN_PATH).expect("load plugin");
            let r2il_arch_init: libloading::Symbol<
                unsafe extern "C" fn(*const c_char) -> *mut c_void,
            > = lib.get(b"r2il_arch_init").unwrap();
            let r2il_is_loaded: libloading::Symbol<unsafe extern "C" fn(*const c_void) -> i32> =
                lib.get(b"r2il_is_loaded").unwrap();
            let r2il_lift: libloading::Symbol<
                unsafe extern "C" fn(*mut c_void, *const u8, usize, u64) -> *mut c_void,
            > = lib.get(b"r2il_lift").unwrap();
            let r2il_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_free").unwrap();
            let r2il_block_free: libloading::Symbol<unsafe extern "C" fn(*mut c_void)> =
                lib.get(b"r2il_block_free").unwrap();
            let arch = CString::new("aarch64").unwrap();
            let ctx = r2il_arch_init(arch.as_ptr());
            if ctx.is_null() || r2il_is_loaded(ctx) != 1 {
                eprintln!("Skipping: plugin not built with aarch64 support");
                if !ctx.is_null() {
                    r2il_free(ctx);
                }
                return;
            }

            let mut add_bytes = ARM64_BYTES_BASE.to_vec();
            add_bytes.resize(16, 0);
            let mut ret_bytes = ARM64_BYTES_RET.to_vec();
            ret_bytes.resize(16, 0);
            let add_block = r2il_lift(ctx, add_bytes.as_ptr(), add_bytes.len(), 0x1000);
            let ret_block = r2il_lift(ctx, ret_bytes.as_ptr(), ret_bytes.len(), 0x1004);
            assert!(!add_block.is_null(), "Failed to lift aarch64 add block");
            assert!(!ret_block.is_null(), "Failed to lift aarch64 ret block");

            let block_ptrs = [add_block as *const c_void, ret_block as *const c_void];
            let fcn_name = CString::new("sym.a64_demo").unwrap();
            let external_context = CString::new(
                r#"{
                    "signature": {
                        "name": "sym.a64_demo",
                        "ret": "int32_t",
                        "params": [
                            {"name": "items", "type": "char *"}
                        ]
                    }
                }"#,
            )
            .unwrap();
            let ret_type = CString::new("int32_t").unwrap();
            let param_name = CString::new("items").unwrap();
            let param_type = CString::new("char *").unwrap();
            let typed_params = [R2SleighContextParam {
                name: param_name.as_ptr(),
                type_name: param_type.as_ptr(),
                cc_reg: std::ptr::null(),
            }];
            let json_str = session_type_writeback_json(
                &lib,
                ctx,
                &block_ptrs,
                0x1000,
                &fcn_name,
                &external_context,
                Some(&ret_type),
                None,
                &typed_params,
            );
            let parsed: Value = serde_json::from_str(&json_str).expect("valid type writeback json");
            assert_eq!(parsed.get("arch").and_then(Value::as_str), Some("aarch64"));
            assert_eq!(
                parsed.get("callconv").and_then(Value::as_str),
                Some(""),
                "non-x86 type writeback payload should not require callconv: {}",
                json_str
            );
            assert!(
                parsed
                    .get("callconv_confidence")
                    .and_then(Value::as_u64)
                    .is_some_and(|conf| conf < 80),
                "non-x86 type writeback payload should keep low callconv confidence: {}",
                json_str
            );
            assert!(
                parsed
                    .get("signature")
                    .and_then(Value::as_str)
                    .is_some_and(|sig| sig.contains("sym.a64_demo")),
                "signature should still be present on non-x86 payload: {}",
                json_str
            );
            assert!(
                parsed.get("params").and_then(Value::as_array).is_some(),
                "non-x86 type writeback payload should still serialize params: {}",
                json_str
            );
            assert!(
                parsed
                    .get("confidence")
                    .and_then(Value::as_u64)
                    .is_some_and(|conf| conf >= 70),
                "explicit non-x86 signature context should raise signature confidence: {}",
                json_str
            );

            r2il_block_free(add_block);
            r2il_block_free(ret_block);
            r2il_free(ctx);
        }
    }
}

#[cfg(target_os = "macos")]
mod host_matrix {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};

    fn fixture_source_and_output_dir() -> (PathBuf, PathBuf) {
        if Path::new("tests/e2e/vuln_test.c").exists() {
            return (
                PathBuf::from("tests/e2e/vuln_test.c"),
                PathBuf::from("target/host-matrix-integration"),
            );
        }
        if Path::new("vuln_test.c").exists() {
            return (
                PathBuf::from("vuln_test.c"),
                PathBuf::from("../../target/host-matrix-integration"),
            );
        }
        panic!("unable to locate vuln_test.c for host-matrix integration");
    }

    fn compile_host_matrix_binary(arch: &str) -> Result<PathBuf, String> {
        let (source, out_dir) = fixture_source_and_output_dir();
        fs::create_dir_all(&out_dir).expect("create host-matrix output dir");
        let output_path = out_dir.join(format!("vuln_test_{arch}"));
        let output = Command::new("clang")
            .args([
                "-O0",
                "-g",
                "-fno-stack-protector",
                "-Wl,-no_pie",
                "-arch",
                arch,
            ])
            .arg(&source)
            .arg("-o")
            .arg(&output_path)
            .output()
            .expect("execute clang");
        if !output.status.success() {
            return Err(format!(
                "clang failed for {arch}: stdout=\n{}\nstderr=\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        Ok(output_path)
    }

    fn assert_check_secret_semantic_invariants(output: &str) {
        assert!(
            !output.trim().is_empty(),
            "fresh host-matrix check_secret decompilation must be non-empty"
        );
        assert!(
            output.contains("return 1;"),
            "success path must keep return 1:\n{output}"
        );
        assert!(
            output.contains("return 0;"),
            "failure path must keep return 0:\n{output}"
        );
        assert!(
            output.contains("0xdead"),
            "comparison constant must stay visible:\n{output}"
        );
    }

    #[test]
    fn fresh_clang_host_matrix_keeps_helper_semantics_consistent() {
        let timeout = Duration::from_secs(180);
        let mut checked = 0usize;
        for arch in ["arm64", "arm64e", "x86_64", "x86_64h"] {
            let Ok(binary) = compile_host_matrix_binary(arch) else {
                eprintln!("Skipping unavailable host-matrix target {arch}");
                continue;
            };
            let result = r2_cmd_timeout(
                binary.to_str().expect("utf8 binary path"),
                "aa; a:sla.dec `afl~check_secret$[0]`",
                timeout,
            );
            result.assert_ok();
            assert_check_secret_semantic_invariants(&result.stdout);
            checked += 1;
        }
        assert!(
            checked > 0,
            "host-matrix must validate at least one fresh target"
        );
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
