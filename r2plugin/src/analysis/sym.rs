use crate::blocks::BlockSlice;
use crate::context::require_ctx_view;
use crate::{ArchSpec, R2ILBlock, R2ILContext, parse_addr_name_map};
use serde::Serialize;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};
use z3::{Config, Context};

static MERGE_STATES: AtomicBool = AtomicBool::new(false);

fn merge_states_enabled() -> bool {
    MERGE_STATES.load(Ordering::Relaxed)
}

/// Opaque symbolic state handle for C API.
/// Each context owns its own Z3 context for thread safety.
pub struct R2SymContext {
    _config: Config,
    entry_pc: u64,
    error: Option<CString>,
}

/// Initialize the symbolic execution engine.
/// Returns 1 on success, 0 on failure.
/// Note: This is an intentional no-op because contexts are created per-state.
#[unsafe(no_mangle)]
pub extern "C" fn r2sym_init() -> i32 {
    1
}

/// Clean up the symbolic execution engine.
/// Note: This is an intentional no-op because contexts are freed with their states.
#[unsafe(no_mangle)]
pub extern "C" fn r2sym_fini() {}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_state_new(entry_pc: u64) -> *mut R2SymContext {
    Box::into_raw(Box::new(R2SymContext {
        _config: Config::new(),
        entry_pc,
        error: None,
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_state_free(state: *mut R2SymContext) {
    if !state.is_null() {
        unsafe { drop(Box::from_raw(state)) }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_error(state: *const R2SymContext) -> *const c_char {
    if state.is_null() {
        return ptr::null();
    }
    unsafe {
        match &(*state).error {
            Some(s) => s.as_ptr(),
            None => ptr::null(),
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_get_pc(state: *const R2SymContext) -> u64 {
    if state.is_null() {
        return 0;
    }
    unsafe { (*state).entry_pc }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_available() -> i32 {
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_merge_is_enabled() -> i32 {
    if merge_states_enabled() { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_merge_set_enabled(enabled: i32) {
    MERGE_STATES.store(enabled != 0, Ordering::Relaxed);
}

fn sym_default_config() -> r2sym::ExploreConfig {
    r2sym::ExploreConfig {
        max_states: 100,
        max_depth: 200,
        merge_states: merge_states_enabled(),
        timeout: Some(std::time::Duration::from_secs(5)),
        ..Default::default()
    }
}

fn sym_error_json(message: &str) -> *mut c_char {
    let payload = format!(r#"{{"error":"{}"}}"#, message);
    CString::new(payload).map_or(ptr::null_mut(), |c| c.into_raw())
}

fn sym_symbol_map() -> &'static Mutex<HashMap<u64, String>> {
    static MAP: OnceLock<Mutex<HashMap<u64, String>>> = OnceLock::new();
    MAP.get_or_init(|| Mutex::new(HashMap::new()))
}

fn build_seed_interproc_summary_set(
    prepared: &r2ssa::SsaArtifact,
    symbol_map: &HashMap<u64, String>,
) -> r2ssa::InterprocSummarySet {
    let mut summaries = BTreeMap::new();
    for call in prepared.call_sites().by_id.values() {
        let Some(target) = call.direct_target else {
            continue;
        };
        let Some(name) = symbol_map.get(&target) else {
            continue;
        };
        let id = r2ssa::InterprocFunctionId(target);
        if let Some(summary) = r2ssa::FunctionSemanticSummary::seed_for_name(id, name) {
            summaries.insert(id, summary);
        }
    }
    r2ssa::InterprocSummarySet {
        root: None,
        summaries,
        diagnostics: r2ssa::InterprocSummaryDiagnostics::default(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_set_symbol_map_json(json: *const c_char) -> i32 {
    if json.is_null() {
        return 0;
    }
    let json_str = unsafe {
        match CStr::from_ptr(json).to_str() {
            Ok(s) => s,
            Err(_) => return 0,
        }
    };
    let parsed = parse_addr_name_map(json_str);
    match sym_symbol_map().lock() {
        Ok(mut map) => {
            *map = parsed;
            1
        }
        Err(_) => 0,
    }
}

#[derive(Serialize, Clone)]
struct SymExecSummary {
    paths_explored: usize,
    paths_feasible: usize,
    paths_pruned: usize,
    max_depth: usize,
    states_explored: usize,
    time_ms: u64,
}

#[derive(Serialize)]
struct SymStateInfo {
    pc: u64,
    depth: usize,
    num_constraints: usize,
    registers: std::collections::HashMap<String, String>,
}

#[derive(Serialize)]
struct PathInfo {
    path_id: usize,
    feasible: bool,
    depth: usize,
    exit_status: String,
    final_pc: String,
    num_constraints: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    solution: Option<PathSolution>,
}

#[derive(Serialize)]
struct PathSolution {
    inputs: std::collections::HashMap<String, String>,
    registers: std::collections::HashMap<String, String>,
}

#[derive(Serialize)]
struct SymTargetExploreResult {
    entry: String,
    target: String,
    matched_paths: usize,
    stats: SymExecSummary,
    paths: Vec<PathInfo>,
}

#[derive(Serialize)]
struct SymTargetSolveResult {
    entry: String,
    target: String,
    matched_paths: usize,
    found: bool,
    stats: SymExecSummary,
    #[serde(skip_serializing_if = "Option::is_none")]
    selected_path: Option<PathInfo>,
}

fn path_solution_from_result<'ctx>(
    explorer: &r2sym::PathExplorer<'ctx>,
    result: &r2sym::PathResult<'ctx>,
) -> Option<PathSolution> {
    if !result.feasible {
        return None;
    }
    explorer.solve_path(result).map(|solved| PathSolution {
        inputs: solved
            .inputs
            .into_iter()
            .map(|(k, v)| (k, format!("0x{:x}", v)))
            .collect(),
        registers: solved
            .registers
            .into_iter()
            .filter(|(name, _)| !name.starts_with("tmp:") && !name.contains("_0"))
            .map(|(k, v)| (k, format!("0x{:x}", v)))
            .collect(),
    })
}

fn path_info_from_result<'ctx>(
    path_id: usize,
    result: &r2sym::PathResult<'ctx>,
    explorer: &r2sym::PathExplorer<'ctx>,
) -> PathInfo {
    PathInfo {
        path_id,
        feasible: result.feasible,
        depth: result.depth,
        exit_status: format!("{:?}", result.exit_status),
        final_pc: format!("0x{:x}", result.final_pc()),
        num_constraints: result.num_constraints(),
        solution: path_solution_from_result(explorer, result),
    }
}

fn build_symbolic_prepared(
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
) -> Option<r2ssa::SsaArtifact> {
    r2ssa::SsaArtifact::for_symbolic(blocks, arch)
}

fn symbol_map_snapshot() -> HashMap<u64, String> {
    sym_symbol_map()
        .lock()
        .map(|map| map.clone())
        .unwrap_or_default()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_function(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    entry_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch) {
        Some(prepared) => prepared,
        None => return ptr::null_mut(),
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = r2sym::PathExplorer::with_config(&z3_ctx, sym_default_config());
        if let Some(arch) = ctx_view.arch
            && let Some(registry) = r2sym::SummaryRegistry::with_core_for_arch(arch)
        {
            let interproc = build_seed_interproc_summary_set(&prepared, &symbol_map);
            let _ =
                registry.install_known_symbols_for_function(&mut explorer, &prepared, &symbol_map);
            let _ = registry.install_interproc_summaries_for_function(
                &mut explorer,
                &prepared,
                &interproc,
                &symbol_map,
            );
        }
        let results = explorer.explore(&prepared, initial_state);
        let stats = explorer.stats().clone();
        (results, stats)
    }));

    let (results, stats) = match explore_result {
        Ok(r) => r,
        Err(_) => {
            let error_msg = r#"{"error": "symbolic execution failed (z3 context error)"}"#;
            return CString::new(error_msg).map_or(ptr::null_mut(), |c| c.into_raw());
        }
    };

    let feasible_count = results.iter().filter(|r| r.feasible).count();
    let summary = SymExecSummary {
        paths_explored: stats.paths_completed,
        paths_feasible: feasible_count,
        paths_pruned: stats.paths_pruned,
        max_depth: stats.max_depth_reached,
        states_explored: stats.states_explored,
        time_ms: stats.total_time.as_millis() as u64,
    };
    match serde_json::to_string_pretty(&summary) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_state_json(state: *const R2SymContext) -> *mut c_char {
    if state.is_null() {
        return ptr::null_mut();
    }
    let state_ref = unsafe { &*state };
    let info = SymStateInfo {
        pc: state_ref.entry_pc,
        depth: 0,
        num_constraints: 0,
        registers: std::collections::HashMap::new(),
    };
    match serde_json::to_string_pretty(&info) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_paths(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    entry_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch) {
        Some(prepared) => prepared,
        None => return ptr::null_mut(),
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = r2sym::PathExplorer::with_config(&z3_ctx, sym_default_config());
        if let Some(arch) = ctx_view.arch
            && let Some(registry) = r2sym::SummaryRegistry::with_core_for_arch(arch)
        {
            let interproc = build_seed_interproc_summary_set(&prepared, &symbol_map);
            let _ =
                registry.install_known_symbols_for_function(&mut explorer, &prepared, &symbol_map);
            let _ = registry.install_interproc_summaries_for_function(
                &mut explorer,
                &prepared,
                &interproc,
                &symbol_map,
            );
        }
        let results = explorer.explore(&prepared, initial_state);
        (results, explorer)
    }));

    let (results, explorer) = match explore_result {
        Ok(r) => r,
        Err(_) => {
            let error_msg = r#"[{"error": "symbolic execution failed (z3 context error)"}]"#;
            return CString::new(error_msg).map_or(ptr::null_mut(), |c| c.into_raw());
        }
    };

    let paths: Vec<PathInfo> = results
        .iter()
        .enumerate()
        .map(|(i, r)| path_info_from_result(i, r, &explorer))
        .collect();
    match serde_json::to_string_pretty(&paths) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_explore_to(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    entry_addr: u64,
    target_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return sym_error_json("no blocks to explore");
    };

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch) {
        Some(prepared) => prepared,
        None => return sym_error_json("failed to build SSA function"),
    };
    let symbol_map = symbol_map_snapshot();

    let z3_ctx = Context::thread_local();
    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = r2sym::PathExplorer::with_config(&z3_ctx, sym_default_config());
        if let Some(arch) = ctx_view.arch
            && let Some(registry) = r2sym::SummaryRegistry::with_core_for_arch(arch)
        {
            let interproc = build_seed_interproc_summary_set(&prepared, &symbol_map);
            let _ =
                registry.install_known_symbols_for_function(&mut explorer, &prepared, &symbol_map);
            let _ = registry.install_interproc_summaries_for_function(
                &mut explorer,
                &prepared,
                &interproc,
                &symbol_map,
            );
        }
        let matched = explorer.find_paths_to(&prepared, initial_state, target_addr);
        let stats = explorer.stats().clone();
        let paths: Vec<PathInfo> = matched
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (paths, stats)
    }));

    let (paths, stats) = match explore_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: SymExecSummary {
            paths_explored: stats.paths_completed,
            paths_feasible: paths.len(),
            paths_pruned: stats.paths_pruned,
            max_depth: stats.max_depth_reached,
            states_explored: stats.states_explored,
            time_ms: stats.total_time.as_millis() as u64,
        },
        paths,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic exploration output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_solve_to(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    entry_addr: u64,
    target_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(blocks) = (unsafe { BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return sym_error_json("no blocks to solve");
    };

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch) {
        Some(prepared) => prepared,
        None => return sym_error_json("failed to build SSA function"),
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = r2sym::PathExplorer::with_config(&z3_ctx, sym_default_config());
        if let Some(arch) = ctx_view.arch
            && let Some(registry) = r2sym::SummaryRegistry::with_core_for_arch(arch)
        {
            let interproc = build_seed_interproc_summary_set(&prepared, &symbol_map);
            let _ =
                registry.install_known_symbols_for_function(&mut explorer, &prepared, &symbol_map);
            let _ = registry.install_interproc_summaries_for_function(
                &mut explorer,
                &prepared,
                &interproc,
                &symbol_map,
            );
        }
        let matched = explorer.find_paths_to(&prepared, initial_state, target_addr);
        let stats = explorer.stats().clone();
        let selected = matched
            .iter()
            .enumerate()
            .min_by_key(|(idx, path)| (path.num_constraints(), path.depth, *idx))
            .map(|(idx, path)| path_info_from_result(idx, path, &explorer));
        (matched.len(), selected, stats)
    }));

    let (matched_paths, selected_path, stats) = match solve_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths,
        found: selected_path.is_some(),
        stats: SymExecSummary {
            paths_explored: stats.paths_completed,
            paths_feasible: matched_paths,
            paths_pruned: stats.paths_pruned,
            max_depth: stats.max_depth_reached,
            states_explored: stats.states_explored,
            time_ms: stats.total_time.as_millis() as u64,
        },
        selected_path,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic solve output"),
    }
}
