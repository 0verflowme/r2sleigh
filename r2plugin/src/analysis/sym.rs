use crate::blocks::BlockSlice;
use crate::context::require_ctx_view;
use crate::types::symbolic_vm_value_expr_from_sym;
use crate::{ArchSpec, R2ILBlock, R2ILContext, parse_addr_name_map};
use r2types::SymbolicVmValueExpr;
use serde::Serialize;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;
use std::slice;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};
use z3::{Config, Context};

static MERGE_STATES: AtomicBool = AtomicBool::new(false);
const SYM_PATHS_LIMIT: usize = 32;
const SYM_PATHS_CALL_FREE_MAX_STATES: usize = 16;
const SYM_PATHS_CALL_FREE_MAX_DEPTH: usize = 64;
const SYM_PATHS_CALL_HEAVY_MAX_STATES: usize = 8;
const SYM_PATHS_CALL_HEAVY_MAX_DEPTH: usize = 32;
const SYM_PATHS_TIMEOUT_MS: u64 = 500;
const SYM_PATHS_SOLUTION_LIMIT: usize = 4;

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

#[repr(C)]
pub struct R2ILFunctionBlocks {
    entry_addr: u64,
    name: *const c_char,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
}

#[repr(C)]
pub struct R2SymReplayRegister {
    name: *const c_char,
    value: u64,
}

#[repr(C)]
pub struct R2SymReplayMemoryWindow {
    addr: u64,
    bytes: *const u8,
    size: usize,
    label: *const c_char,
}

#[repr(C)]
pub struct R2SymReplayRegisterOverlay {
    name: *const c_char,
    symbol: *const c_char,
}

#[repr(C)]
pub struct R2SymReplayMemoryOverlay {
    addr: u64,
    size: u32,
    name: *const c_char,
}

#[repr(C)]
pub struct R2SymReplaySeed {
    checkpoint_id: u64,
    entry_addr: u64,
    registers: *const R2SymReplayRegister,
    num_registers: usize,
    memory: *const R2SymReplayMemoryWindow,
    num_memory: usize,
    register_overlays: *const R2SymReplayRegisterOverlay,
    num_register_overlays: usize,
    memory_overlays: *const R2SymReplayMemoryOverlay,
    num_memory_overlays: usize,
    tty_fds: *const i32,
    num_tty_fds: usize,
    skip_sleep_calls: i32,
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

fn sym_default_query_config() -> r2sym::SymQueryConfig {
    r2sym::SymQueryConfig {
        explore: sym_default_config(),
        mode: r2sym::QueryMode::TargetGuided,
        summary_profile: r2sym::SummaryProfile::Default,
    }
}

fn sym_paths_query_config(prepared: &r2ssa::SsaArtifact) -> r2sym::SymQueryConfig {
    let mut config = sym_default_query_config();
    if prepared.call_sites().by_id.is_empty() {
        config.explore.max_states = SYM_PATHS_CALL_FREE_MAX_STATES;
        config.explore.max_depth = SYM_PATHS_CALL_FREE_MAX_DEPTH;
    } else {
        config.explore.max_states = SYM_PATHS_CALL_HEAVY_MAX_STATES;
        config.explore.max_depth = SYM_PATHS_CALL_HEAVY_MAX_DEPTH;
    }
    config.explore.timeout = Some(std::time::Duration::from_millis(SYM_PATHS_TIMEOUT_MS));
    config.explore.max_completed_paths = Some(SYM_PATHS_LIMIT);
    config.summary_profile = r2sym::SummaryProfile::PathListing;
    config
}

fn sym_paths_solution_limit(result_count: usize, prepared: &r2ssa::SsaArtifact) -> usize {
    if !prepared.call_sites().by_id.is_empty() {
        return 0;
    }
    if result_count <= SYM_PATHS_SOLUTION_LIMIT {
        result_count
    } else {
        0
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
    sat_queries: usize,
    sat_cache_hits: usize,
    sat_cache_misses: usize,
    solve_calls: usize,
    solve_unsat_shortcuts: usize,
    time_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    semantic: Option<CompiledSemanticInfo>,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct CompiledSemanticInfo {
    pub(crate) mode: String,
    pub(crate) capability: SemanticCapabilityInfo,
    pub(crate) slice_class: String,
    pub(crate) residual_reasons: Vec<String>,
    pub(crate) closure_functions: usize,
    pub(crate) helper_functions: usize,
    pub(crate) derived_summaries: usize,
    pub(crate) summary_attempted: usize,
    pub(crate) summary_budget_exhausted: usize,
    pub(crate) summary_scc_count: usize,
    pub(crate) branches_pruned: usize,
    pub(crate) branches_unknown: usize,
    pub(crate) skipped_large_cfg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) interpreter: Option<InterpreterDispatchInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) vm_step: Option<VmStepSummaryInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) vm_transfer: Option<VmStepSummaryInfo>,
    pub(crate) cache_hit: bool,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct SemanticCapabilityInfo {
    pub(crate) query_ready: bool,
    pub(crate) type_ready: bool,
    pub(crate) decompile_ready: bool,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct InterpreterDispatchInfo {
    pub(crate) kind: String,
    pub(crate) dispatch_header: String,
    pub(crate) dispatch_targets: usize,
    pub(crate) selector: Option<String>,
    pub(crate) back_edges: usize,
    pub(crate) score: i32,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmStateUpdateInfo {
    pub(crate) output: String,
    pub(crate) expr: String,
    pub(crate) value: String,
    pub(crate) exact: bool,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmTransferArmInfo {
    pub(crate) handler_target: String,
    pub(crate) case_values: Vec<u64>,
    pub(crate) region_blocks: Vec<String>,
    pub(crate) exit_targets: Vec<String>,
    pub(crate) state_updates: Vec<VmStateUpdateInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) selector_update: Option<VmStateUpdateInfo>,
    pub(crate) exact: bool,
    pub(crate) redispatch: bool,
    pub(crate) may_return: bool,
    pub(crate) truncated: bool,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmStepSummaryInfo {
    pub(crate) kind: String,
    pub(crate) loop_header: String,
    pub(crate) dispatch_header: String,
    pub(crate) selector: Option<String>,
    pub(crate) dispatch_targets: Vec<String>,
    pub(crate) default_target: Option<String>,
    pub(crate) case_values_by_target: BTreeMap<String, Vec<u64>>,
    pub(crate) loop_latches: Vec<String>,
    pub(crate) state_inputs: Vec<String>,
    pub(crate) state_outputs: Vec<String>,
    pub(crate) step_blocks: Vec<String>,
    pub(crate) handler_regions: BTreeMap<String, Vec<String>>,
    pub(crate) handler_state_inputs: BTreeMap<String, Vec<String>>,
    pub(crate) handler_state_outputs: BTreeMap<String, Vec<String>>,
    pub(crate) handler_state_updates: BTreeMap<String, Vec<VmStateUpdateInfo>>,
    pub(crate) handler_memory_reads: BTreeMap<String, usize>,
    pub(crate) handler_memory_writes: BTreeMap<String, usize>,
    pub(crate) handler_calls: BTreeMap<String, usize>,
    pub(crate) handler_conditional_branches: BTreeMap<String, usize>,
    pub(crate) handler_exit_targets: BTreeMap<String, Vec<String>>,
    pub(crate) redispatch_handlers: Vec<String>,
    pub(crate) returning_handlers: Vec<String>,
    pub(crate) truncated_handlers: Vec<String>,
    pub(crate) transfers: Vec<VmTransferArmInfo>,
}

fn render_vm_value_expr(value: &SymbolicVmValueExpr) -> String {
    value.render()
}

fn vm_state_update_info_from_sym(update: &r2sym::VmStateUpdate) -> VmStateUpdateInfo {
    let value = symbolic_vm_value_expr_from_sym(&update.value);
    VmStateUpdateInfo {
        output: update.output.clone(),
        expr: update.expr.clone(),
        value: render_vm_value_expr(&value),
        exact: update.exact,
    }
}

fn vm_transfer_arm_info_from_sym(transfer: &r2sym::VmTransferArm) -> VmTransferArmInfo {
    VmTransferArmInfo {
        handler_target: format!("0x{:x}", transfer.handler_target),
        case_values: transfer.case_values.clone(),
        region_blocks: transfer
            .region_blocks
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        exit_targets: transfer
            .exit_targets
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        state_updates: transfer
            .state_updates
            .iter()
            .map(vm_state_update_info_from_sym)
            .collect(),
        selector_update: transfer
            .selector_update
            .as_ref()
            .map(vm_state_update_info_from_sym),
        exact: transfer.exact,
        redispatch: transfer.redispatch,
        may_return: transfer.may_return,
        truncated: transfer.truncated,
    }
}

fn vm_step_summary_info_from_sym(vm_step: &r2sym::VmStepSummary) -> VmStepSummaryInfo {
    VmStepSummaryInfo {
        kind: match vm_step.kind {
            r2sym::InterpreterKind::SwitchDispatch => "switch_dispatch".to_string(),
            r2sym::InterpreterKind::IndirectDispatch => "indirect_dispatch".to_string(),
        },
        loop_header: format!("0x{:x}", vm_step.loop_header),
        dispatch_header: format!("0x{:x}", vm_step.dispatch_header),
        selector: vm_step.selector.clone(),
        dispatch_targets: vm_step
            .dispatch_targets
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        default_target: vm_step.default_target.map(|addr| format!("0x{addr:x}")),
        case_values_by_target: vm_step
            .case_values_by_target
            .iter()
            .map(|(target, values)| (format!("0x{target:x}"), values.clone()))
            .collect(),
        loop_latches: vm_step
            .loop_latches
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        state_inputs: vm_step.state_inputs.clone(),
        state_outputs: vm_step.state_outputs.clone(),
        step_blocks: vm_step
            .step_blocks
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        handler_regions: vm_step
            .handler_regions
            .iter()
            .map(|(target, blocks)| {
                (
                    format!("0x{target:x}"),
                    blocks.iter().map(|addr| format!("0x{addr:x}")).collect(),
                )
            })
            .collect(),
        handler_state_inputs: vm_step
            .handler_state_inputs
            .iter()
            .map(|(target, inputs)| (format!("0x{target:x}"), inputs.clone()))
            .collect(),
        handler_state_outputs: vm_step
            .handler_state_outputs
            .iter()
            .map(|(target, outputs)| (format!("0x{target:x}"), outputs.clone()))
            .collect(),
        handler_state_updates: vm_step
            .handler_state_updates
            .iter()
            .map(|(target, updates)| {
                (
                    format!("0x{target:x}"),
                    updates.iter().map(vm_state_update_info_from_sym).collect(),
                )
            })
            .collect(),
        handler_memory_reads: vm_step
            .handler_memory_reads
            .iter()
            .map(|(target, count)| (format!("0x{target:x}"), *count))
            .collect(),
        handler_memory_writes: vm_step
            .handler_memory_writes
            .iter()
            .map(|(target, count)| (format!("0x{target:x}"), *count))
            .collect(),
        handler_calls: vm_step
            .handler_calls
            .iter()
            .map(|(target, count)| (format!("0x{target:x}"), *count))
            .collect(),
        handler_conditional_branches: vm_step
            .handler_conditional_branches
            .iter()
            .map(|(target, count)| (format!("0x{target:x}"), *count))
            .collect(),
        handler_exit_targets: vm_step
            .handler_exit_targets
            .iter()
            .map(|(target, exits)| {
                (
                    format!("0x{target:x}"),
                    exits.iter().map(|addr| format!("0x{addr:x}")).collect(),
                )
            })
            .collect(),
        redispatch_handlers: vm_step
            .redispatch_handlers
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        returning_handlers: vm_step
            .returning_handlers
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        truncated_handlers: vm_step
            .truncated_handlers
            .iter()
            .map(|addr| format!("0x{addr:x}"))
            .collect(),
        transfers: vm_step
            .transfers
            .iter()
            .map(vm_transfer_arm_info_from_sym)
            .collect(),
    }
}

#[derive(Serialize)]
struct SymStateInfo {
    pc: u64,
    depth: usize,
    num_constraints: usize,
    registers: BTreeMap<String, String>,
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
    inputs: BTreeMap<String, String>,
    registers: BTreeMap<String, String>,
}

#[derive(Serialize)]
struct RunPathSolution {
    inputs: BTreeMap<String, String>,
    input_buffers: BTreeMap<String, BufferSolution>,
    registers: BTreeMap<String, String>,
}

#[derive(Serialize)]
struct BufferSolution {
    hex: String,
    ascii: String,
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

#[derive(Serialize)]
struct SymRunPathInfo {
    path_id: usize,
    feasible: bool,
    depth: usize,
    exit_status: String,
    final_pc: String,
    num_constraints: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    solution: Option<RunPathSolution>,
}

#[derive(Serialize)]
struct SymRunStashCounts {
    found: usize,
    avoided: usize,
    unsat: usize,
    errored: usize,
    completed: usize,
}

#[derive(Serialize)]
struct SymRunResult {
    entry: String,
    spec: r2sym::ExplorationSpec,
    stats: SymExecSummary,
    stash_counts: SymRunStashCounts,
    found_paths: Vec<SymRunPathInfo>,
    diagnostics: Vec<String>,
}

fn build_sym_exec_summary(
    stats: &r2sym::path::ExploreStats,
    solver_stats: &r2sym::SolverStats,
    paths_feasible: usize,
    semantic: Option<&r2sym::CompiledSemanticArtifact>,
) -> SymExecSummary {
    SymExecSummary {
        paths_explored: stats.paths_completed,
        paths_feasible,
        paths_pruned: stats.paths_pruned,
        max_depth: stats.max_depth_reached,
        states_explored: stats.states_explored,
        sat_queries: solver_stats.sat_queries,
        sat_cache_hits: solver_stats.sat_cache_hits,
        sat_cache_misses: solver_stats.sat_cache_misses,
        solve_calls: solver_stats.solve_calls,
        solve_unsat_shortcuts: solver_stats.solve_unsat_shortcuts,
        time_ms: stats.total_time.as_millis() as u64,
        semantic: semantic.map(compiled_semantic_info),
    }
}

pub(crate) fn compiled_semantic_info(
    compiled: &r2sym::CompiledSemanticArtifact,
) -> CompiledSemanticInfo {
    CompiledSemanticInfo {
        mode: match compiled.mode {
            r2sym::SemanticMode::Raw => "raw".to_string(),
            r2sym::SemanticMode::Compiled => "compiled".to_string(),
            r2sym::SemanticMode::Residual => "residual".to_string(),
            r2sym::SemanticMode::VmSummary => "vm_summary".to_string(),
        },
        capability: SemanticCapabilityInfo {
            query_ready: compiled.capability.query_ready,
            type_ready: compiled.capability.type_ready,
            decompile_ready: compiled.capability.decompile_ready,
        },
        slice_class: match compiled.slice_class {
            r2sym::SliceClass::Wrapper => "wrapper".to_string(),
            r2sym::SliceClass::Worker => "worker".to_string(),
            r2sym::SliceClass::RecursiveGroup => "recursive_group".to_string(),
            r2sym::SliceClass::InterpreterSwitch => "interpreter_switch".to_string(),
            r2sym::SliceClass::InterpreterIndirect => "interpreter_indirect".to_string(),
            r2sym::SliceClass::GenericLarge => "generic_large".to_string(),
        },
        residual_reasons: compiled
            .residual_reasons
            .iter()
            .map(|reason| {
                match reason {
                    r2sym::ResidualReason::MissingArch => "missing_arch",
                    r2sym::ResidualReason::LargeCfg => "large_cfg",
                    r2sym::ResidualReason::SummaryBudgetExhausted => "summary_budget_exhausted",
                    r2sym::ResidualReason::SccBudgetExhausted => "scc_budget_exhausted",
                    r2sym::ResidualReason::InterpreterRequiresStepSummary => {
                        "interpreter_requires_step_summary"
                    }
                }
                .to_string()
            })
            .collect(),
        closure_functions: compiled.closure_functions,
        helper_functions: compiled.helper_functions,
        derived_summaries: compiled.derived_summaries,
        summary_attempted: compiled.derived_diagnostics.attempted,
        summary_budget_exhausted: compiled.derived_diagnostics.budget_exhausted
            + compiled.derived_diagnostics.scc_budget_exhausted,
        summary_scc_count: compiled.derived_diagnostics.scc_count,
        branches_pruned: compiled.symbolic_facts.diagnostics.branches_pruned,
        branches_unknown: compiled.symbolic_facts.diagnostics.branches_unknown,
        skipped_large_cfg: compiled.symbolic_facts.diagnostics.skipped_large_cfg,
        interpreter: compiled
            .interpreter
            .as_ref()
            .map(|interpreter| InterpreterDispatchInfo {
                kind: match interpreter.kind {
                    r2sym::InterpreterKind::SwitchDispatch => "switch_dispatch".to_string(),
                    r2sym::InterpreterKind::IndirectDispatch => "indirect_dispatch".to_string(),
                },
                dispatch_header: format!("0x{:x}", interpreter.dispatch_header),
                dispatch_targets: interpreter.dispatch_targets,
                selector: interpreter.selector.clone(),
                back_edges: interpreter.back_edges,
                score: interpreter.score,
            }),
        vm_step: compiled.vm_step.as_ref().map(vm_step_summary_info_from_sym),
        vm_transfer: compiled
            .vm_transfer
            .as_ref()
            .map(vm_step_summary_info_from_sym),
        cache_hit: compiled.cache_hit,
    }
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

fn buffer_solution(bytes: Vec<u8>) -> BufferSolution {
    let hex = bytes
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let ascii = bytes
        .iter()
        .map(|byte| {
            if byte.is_ascii_graphic() || *byte == b' ' {
                *byte as char
            } else {
                '.'
            }
        })
        .collect();
    BufferSolution { hex, ascii }
}

fn run_path_solution_from_result<'ctx>(
    explorer: &r2sym::PathExplorer<'ctx>,
    result: &r2sym::PathResult<'ctx>,
) -> Option<RunPathSolution> {
    if !result.feasible {
        return None;
    }
    explorer.solve_path(result).map(|solved| RunPathSolution {
        inputs: solved
            .inputs
            .into_iter()
            .map(|(k, v)| (k, format!("0x{:x}", v)))
            .collect(),
        input_buffers: solved
            .input_buffers
            .into_iter()
            .map(|(k, v)| (k, buffer_solution(v)))
            .collect(),
        registers: solved
            .registers
            .into_iter()
            .filter(|(name, _)| !name.starts_with("tmp:") && !name.contains("_0"))
            .map(|(k, v)| (k, format!("0x{:x}", v)))
            .collect(),
    })
}

fn path_info_from_result_with_solution<'ctx>(
    path_id: usize,
    result: &r2sym::PathResult<'ctx>,
    explorer: &r2sym::PathExplorer<'ctx>,
    include_solution: bool,
) -> PathInfo {
    PathInfo {
        path_id,
        feasible: result.feasible,
        depth: result.depth,
        exit_status: format!("{:?}", result.exit_status),
        final_pc: format!("0x{:x}", result.final_pc()),
        num_constraints: result.num_constraints(),
        solution: include_solution
            .then(|| path_solution_from_result(explorer, result))
            .flatten(),
    }
}

fn path_info_from_result<'ctx>(
    path_id: usize,
    result: &r2sym::PathResult<'ctx>,
    explorer: &r2sym::PathExplorer<'ctx>,
) -> PathInfo {
    path_info_from_result_with_solution(path_id, result, explorer, true)
}

fn run_path_info_from_result<'ctx>(
    path_id: usize,
    result: &r2sym::PathResult<'ctx>,
    explorer: &r2sym::PathExplorer<'ctx>,
) -> SymRunPathInfo {
    SymRunPathInfo {
        path_id,
        feasible: result.feasible,
        depth: result.depth,
        exit_status: format!("{:?}", result.exit_status),
        final_pc: format!("0x{:x}", result.final_pc()),
        num_constraints: result.num_constraints(),
        solution: run_path_solution_from_result(explorer, result),
    }
}

pub(crate) fn build_symbolic_prepared(
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
) -> Option<r2ssa::SsaArtifact> {
    r2ssa::SsaArtifact::for_symbolic(blocks, arch)
}

pub(crate) fn build_single_function_scope(
    prepared: r2ssa::SsaArtifact,
    entry_addr: u64,
    name: Option<String>,
) -> Option<r2sym::PreparedFunctionScope> {
    r2sym::PreparedFunctionScope::new(
        entry_addr,
        vec![r2sym::ScopedPreparedFunction {
            id: r2ssa::InterprocFunctionId(entry_addr),
            name,
            prepared,
        }],
    )
}

pub(crate) unsafe fn build_symbolic_scope_from_ffi(
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    arch: Option<&ArchSpec>,
    root_entry_addr: u64,
) -> Option<r2sym::PreparedFunctionScope> {
    if functions.is_null() || num_functions == 0 {
        return None;
    }

    let mut scope_functions = Vec::new();
    for index in 0..num_functions {
        let function = unsafe { &*functions.add(index) };
        let blocks = unsafe { BlockSlice::from_ffi(function.blocks, function.num_blocks) }?;
        let prepared = build_symbolic_prepared(blocks.as_slice(), arch)?;
        let name = if function.name.is_null() {
            None
        } else {
            unsafe { CStr::from_ptr(function.name).to_str().ok() }.map(str::to_string)
        };
        scope_functions.push(r2sym::ScopedPreparedFunction {
            id: r2ssa::InterprocFunctionId(function.entry_addr),
            name,
            prepared,
        });
    }
    r2sym::PreparedFunctionScope::new(root_entry_addr, scope_functions)
}

fn symbol_map_snapshot() -> HashMap<u64, String> {
    sym_symbol_map()
        .lock()
        .map(|map| map.clone())
        .unwrap_or_default()
}

fn install_symbolic_hooks<'ctx>(
    explorer: &mut r2sym::PathExplorer<'ctx>,
    scope: &r2sym::PreparedFunctionScope,
    arch: Option<&ArchSpec>,
    z3_ctx: &'ctx Context,
    symbol_map: &HashMap<u64, String>,
    summary_profile: r2sym::SummaryProfile,
) {
    if let Some(arch) = arch
        && let Some(registry) = r2sym::SummaryRegistry::with_profile_for_arch(arch, summary_profile)
    {
        let _ = registry.install_scope_summaries_for_explorer(
            explorer,
            z3_ctx,
            scope,
            Some(arch),
            symbol_map,
        );
    }
}

fn scope_root_prepared(scope: &r2sym::PreparedFunctionScope) -> Option<&r2ssa::SsaArtifact> {
    scope.root().map(|function| &function.prepared)
}

unsafe fn ffi_slice<'a, T>(ptr: *const T, len: usize) -> Result<&'a [T], &'static str> {
    if len == 0 {
        return Ok(&[]);
    }
    if ptr.is_null() {
        return Err("missing replay seed array");
    }
    Ok(unsafe { slice::from_raw_parts(ptr, len) })
}

unsafe fn ffi_string(ptr: *const c_char) -> Result<String, &'static str> {
    if ptr.is_null() {
        return Err("missing replay seed string");
    }
    unsafe { CStr::from_ptr(ptr) }
        .to_str()
        .map(str::to_string)
        .map_err(|_| "replay seed string is not valid utf-8")
}

unsafe fn replay_seed_from_ffi(
    seed: *const R2SymReplaySeed,
) -> Result<r2sym::ReplaySeed, &'static str> {
    if seed.is_null() {
        return Err("missing replay seed");
    }
    let seed = unsafe { &*seed };

    let registers = unsafe { ffi_slice(seed.registers, seed.num_registers) }?
        .iter()
        .map(|register| {
            Ok(r2sym::ReplayRegisterValue {
                name: unsafe { ffi_string(register.name) }?,
                value: register.value,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let memory = unsafe { ffi_slice(seed.memory, seed.num_memory) }?
        .iter()
        .map(|window| {
            let bytes = if window.size == 0 {
                Vec::new()
            } else if window.bytes.is_null() {
                return Err("missing replay memory bytes");
            } else {
                unsafe { slice::from_raw_parts(window.bytes, window.size) }.to_vec()
            };
            let label = if window.label.is_null() {
                None
            } else {
                Some(unsafe { ffi_string(window.label) }?)
            };
            Ok(r2sym::ReplayMemoryWindow {
                addr: window.addr,
                bytes,
                label,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let register_overlays =
        unsafe { ffi_slice(seed.register_overlays, seed.num_register_overlays) }?
            .iter()
            .map(|overlay| {
                Ok(r2sym::ReplayRegisterOverlay {
                    name: unsafe { ffi_string(overlay.name) }?,
                    symbol: unsafe { ffi_string(overlay.symbol) }?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

    let memory_overlays = unsafe { ffi_slice(seed.memory_overlays, seed.num_memory_overlays) }?
        .iter()
        .map(|overlay| {
            Ok(r2sym::ReplayMemoryOverlay {
                addr: overlay.addr,
                size: overlay.size,
                name: unsafe { ffi_string(overlay.name) }?,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let tty_fds = unsafe { ffi_slice(seed.tty_fds, seed.num_tty_fds) }?.to_vec();

    Ok(r2sym::ReplaySeed {
        checkpoint_id: (seed.checkpoint_id != 0).then_some(seed.checkpoint_id),
        entry_pc: (seed.entry_addr != 0).then_some(seed.entry_addr),
        registers,
        memory,
        register_overlays,
        memory_overlays,
        tty_fds,
        skip_sleep_calls: seed.skip_sleep_calls != 0,
    })
}

fn build_replay_seeded_state<'ctx>(
    z3_ctx: &'ctx Context,
    entry_addr: u64,
    prepared: &r2ssa::SsaArtifact,
    arch: Option<&ArchSpec>,
    replay_seed: &r2sym::ReplaySeed,
) -> r2sym::SymState<'ctx> {
    let mut initial_state =
        r2sym::SymState::new(z3_ctx, replay_seed.entry_pc.unwrap_or(entry_addr));
    r2sym::seed_replay_state_for_arch(&mut initial_state, Some(prepared), arch, replay_seed);
    initial_state
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
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let query_config = sym_paths_query_config(&prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_semantic_artifact_with_scope(
            &z3_ctx,
            &prepared,
            Some(&scope),
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        (
            explorer.summarize_function(&prepared, initial_state),
            compiled,
        )
    }));

    let (summary, compiled) = match explore_result {
        Ok(r) => r,
        Err(_) => {
            let error_msg = r#"{"error": "symbolic execution failed (z3 context error)"}"#;
            return CString::new(error_msg).map_or(ptr::null_mut(), |c| c.into_raw());
        }
    };

    let output = build_sym_exec_summary(
        &summary.stats,
        &summary.solver_stats,
        summary.feasible_paths,
        Some(&compiled),
    );
    match serde_json::to_string_pretty(&output) {
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
        registers: BTreeMap::new(),
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
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let query_config = sym_paths_query_config(&prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let summary = explorer.summarize_function(&prepared, initial_state);
        (summary, explorer)
    }));

    let (summary, explorer) = match explore_result {
        Ok(r) => r,
        Err(_) => {
            let error_msg = r#"[{"error": "symbolic execution failed (z3 context error)"}]"#;
            return CString::new(error_msg).map_or(ptr::null_mut(), |c| c.into_raw());
        }
    };

    let solution_limit = sym_paths_solution_limit(summary.paths.len(), &prepared);
    let paths: Vec<PathInfo> = summary
        .paths
        .iter()
        .enumerate()
        .map(|(i, r)| path_info_from_result_with_solution(i, r, &explorer, i < solution_limit))
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
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let symbol_map = symbol_map_snapshot();
    let query_config = sym_default_query_config();

    let z3_ctx = Context::thread_local();
    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let reach = explorer.can_reach(&prepared, initial_state, target_addr);
        let paths: Vec<PathInfo> = reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (paths, reach.stats, reach.solver_stats)
    }));

    let (paths, stats, solver_stats) = match explore_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: build_sym_exec_summary(&stats, &solver_stats, paths.len(), None),
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
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let symbol_map = symbol_map_snapshot();
    let query_config = sym_default_query_config();
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let solve = explorer.solve_for_target(&prepared, initial_state, target_addr);
        let selected = solve
            .selected_path_index
            .and_then(|idx| solve.matched_paths.get(idx).map(|path| (idx, path)))
            .map(|(idx, path)| path_info_from_result(idx, path, &explorer));
        (
            solve.matched_paths.len(),
            selected,
            solve.stats,
            solve.solver_stats,
        )
    }));

    let (matched_paths, selected_path, stats, solver_stats) = match solve_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths,
        found: selected_path.is_some(),
        stats: build_sym_exec_summary(&stats, &solver_stats, matched_paths, None),
        selected_path,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic solve output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_run_spec_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    entry_addr: u64,
    spec_json: *const c_char,
) -> *mut c_char {
    if spec_json.is_null() {
        return sym_error_json("missing exploration spec json");
    }
    let spec_text = unsafe {
        match CStr::from_ptr(spec_json).to_str() {
            Ok(text) => text,
            Err(_) => return sym_error_json("exploration spec is not valid utf-8"),
        }
    };
    let spec = match serde_json::from_str::<r2sym::ExplorationSpec>(spec_text) {
        Ok(spec) => spec,
        Err(err) => return sym_error_json(&format!("failed to parse exploration spec: {err}")),
    };
    if let Err(err) = spec.validate() {
        return sym_error_json(&err);
    }

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
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let default_config = sym_default_query_config();

    let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let start_pc = spec.start_pc(entry_addr)?;
        let mut initial_state = r2sym::SymState::new(&z3_ctx, start_pc);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        spec.apply_to_state(&mut initial_state);

        let mut explorer = r2sym::PathExplorer::with_config(
            &z3_ctx,
            spec.to_explore_config(&default_config.explore),
        );
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            default_config.summary_profile,
        );
        let result = explorer.run_spec(&prepared, initial_state, &spec)?;
        let stats = explorer.stats().clone();
        let solver_stats = explorer.solver().stats();
        let found_paths = result
            .found_paths
            .iter()
            .enumerate()
            .map(|(idx, path)| run_path_info_from_result(idx, path, &explorer))
            .collect::<Vec<_>>();
        Ok::<_, String>((result, stats, solver_stats, found_paths))
    }));

    let (result, stats, solver_stats, found_paths) = match run_result {
        Ok(Ok(value)) => value,
        Ok(Err(err)) => return sym_error_json(&err),
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };

    let output = SymRunResult {
        entry: format!("0x{:x}", entry_addr),
        spec,
        stats: build_sym_exec_summary(&stats, &solver_stats, found_paths.len(), None),
        stash_counts: SymRunStashCounts {
            found: found_paths.len(),
            avoided: result.avoided_states,
            unsat: result.unsat_states,
            errored: result.errored_states,
            completed: result.completed_states,
        },
        found_paths,
        diagnostics: result.diagnostics,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic run output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_function_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return ptr::null_mut();
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let query_config = sym_paths_query_config(prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_semantic_artifact_with_scope(
            &z3_ctx,
            prepared,
            Some(&scope),
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        (
            explorer.summarize_function(prepared, initial_state),
            compiled,
        )
    }));

    let (summary, compiled) = match explore_result {
        Ok(r) => r,
        Err(_) => {
            let error_msg = r#"{"error": "symbolic execution failed (z3 context error)"}"#;
            return CString::new(error_msg).map_or(ptr::null_mut(), |c| c.into_raw());
        }
    };

    let output = build_sym_exec_summary(
        &summary.stats,
        &summary.solver_stats,
        summary.feasible_paths,
        Some(&compiled),
    );
    match serde_json::to_string_pretty(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_compile_semantics_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let query_config = sym_default_query_config();
    let compiled = r2sym::compile_semantic_artifact_with_scope(
        &z3_ctx,
        prepared,
        Some(&scope),
        ctx_view.arch,
        &symbol_map,
        query_config.summary_profile,
    );
    match serde_json::to_string(&compiled_semantic_info(&compiled)) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize compiled semantics output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_paths_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return ptr::null_mut();
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let query_config = sym_paths_query_config(prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let summary = explorer.summarize_function(prepared, initial_state);
        (summary, explorer)
    }));

    let (summary, explorer) = match explore_result {
        Ok(r) => r,
        Err(_) => {
            let error_msg = r#"[{"error": "symbolic execution failed (z3 context error)"}]"#;
            return CString::new(error_msg).map_or(ptr::null_mut(), |c| c.into_raw());
        }
    };

    let solution_limit = sym_paths_solution_limit(summary.paths.len(), prepared);
    let paths: Vec<PathInfo> = summary
        .paths
        .iter()
        .enumerate()
        .map(|(i, r)| path_info_from_result_with_solution(i, r, &explorer, i < solution_limit))
        .collect();
    match serde_json::to_string_pretty(&paths) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_explore_to_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
    target_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let query_config = sym_default_query_config();

    let z3_ctx = Context::thread_local();
    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let reach = explorer.can_reach(prepared, initial_state, target_addr);
        let paths: Vec<PathInfo> = reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (paths, reach.stats, reach.solver_stats)
    }));

    let (paths, stats, solver_stats) = match explore_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: build_sym_exec_summary(&stats, &solver_stats, paths.len(), None),
        paths,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic exploration output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_solve_to_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
    target_addr: u64,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let query_config = sym_default_query_config();
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, prepared, ctx_view.arch);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let solve = explorer.solve_for_target(prepared, initial_state, target_addr);
        let selected = solve
            .selected_path_index
            .and_then(|idx| solve.matched_paths.get(idx).map(|path| (idx, path)))
            .map(|(idx, path)| path_info_from_result(idx, path, &explorer));
        (
            solve.matched_paths.len(),
            selected,
            solve.stats,
            solve.solver_stats,
        )
    }));

    let (matched_paths, selected_path, stats, solver_stats) = match solve_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths,
        found: selected_path.is_some(),
        stats: build_sym_exec_summary(&stats, &solver_stats, matched_paths, None),
        selected_path,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic solve output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_run_spec_json_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
    spec_json: *const c_char,
) -> *mut c_char {
    if spec_json.is_null() {
        return sym_error_json("missing exploration spec json");
    }
    let spec_text = unsafe {
        match CStr::from_ptr(spec_json).to_str() {
            Ok(text) => text,
            Err(_) => return sym_error_json("exploration spec is not valid utf-8"),
        }
    };
    let spec = match serde_json::from_str::<r2sym::ExplorationSpec>(spec_text) {
        Ok(spec) => spec,
        Err(err) => return sym_error_json(&format!("failed to parse exploration spec: {err}")),
    };
    if let Err(err) = spec.validate() {
        return sym_error_json(&err);
    }

    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let default_config = sym_default_query_config();

    let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let start_pc = spec.start_pc(entry_addr)?;
        let mut initial_state = r2sym::SymState::new(&z3_ctx, start_pc);
        r2sym::seed_default_state_for_arch(&mut initial_state, prepared, ctx_view.arch);
        spec.apply_to_state(&mut initial_state);

        let mut explorer = r2sym::PathExplorer::with_config(
            &z3_ctx,
            spec.to_explore_config(&default_config.explore),
        );
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            default_config.summary_profile,
        );
        let result = explorer.run_spec(prepared, initial_state, &spec)?;
        let stats = explorer.stats().clone();
        let solver_stats = explorer.solver().stats();
        let found_paths = result
            .found_paths
            .iter()
            .enumerate()
            .map(|(idx, path)| run_path_info_from_result(idx, path, &explorer))
            .collect::<Vec<_>>();
        Ok::<_, String>((result, stats, solver_stats, found_paths))
    }));

    let (result, stats, solver_stats, found_paths) = match run_result {
        Ok(Ok(value)) => value,
        Ok(Err(err)) => return sym_error_json(&err),
        Err(_) => return sym_error_json("symbolic execution failed (z3 context error)"),
    };

    let output = SymRunResult {
        entry: format!("0x{:x}", entry_addr),
        spec,
        stats: build_sym_exec_summary(&stats, &solver_stats, found_paths.len(), None),
        stash_counts: SymRunStashCounts {
            found: found_paths.len(),
            avoided: result.avoided_states,
            unsat: result.unsat_states,
            errored: result.errored_states,
            completed: result.completed_states,
        },
        found_paths,
        diagnostics: result.diagnostics,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize symbolic run output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_explore_to_replay_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
    target_addr: u64,
    replay_seed: *const R2SymReplaySeed,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let replay_seed = unsafe {
        match replay_seed_from_ffi(replay_seed) {
            Ok(seed) => seed,
            Err(err) => return sym_error_json(err),
        }
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let query_config = sym_default_query_config();
    let start_pc = replay_seed.entry_pc.unwrap_or(entry_addr);
    let z3_ctx = Context::thread_local();

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let initial_state =
            build_replay_seeded_state(&z3_ctx, entry_addr, prepared, ctx_view.arch, &replay_seed);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let reach = explorer.can_reach(prepared, initial_state, target_addr);
        let paths: Vec<PathInfo> = reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (paths, reach.stats, reach.solver_stats)
    }));

    let (paths, stats, solver_stats) = match explore_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic replay exploration failed (z3 context error)"),
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", start_pc),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: build_sym_exec_summary(&stats, &solver_stats, paths.len(), None),
        paths,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize replay symbolic exploration output"),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_solve_to_replay_scope(
    ctx: *const R2ILContext,
    functions: *const R2ILFunctionBlocks,
    num_functions: usize,
    entry_addr: u64,
    target_addr: u64,
    replay_seed: *const R2SymReplaySeed,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let replay_seed = unsafe {
        match replay_seed_from_ffi(replay_seed) {
            Ok(seed) => seed,
            Err(err) => return sym_error_json(err),
        }
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let query_config = sym_default_query_config();
    let start_pc = replay_seed.entry_pc.unwrap_or(entry_addr);
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let initial_state =
            build_replay_seeded_state(&z3_ctx, entry_addr, prepared, ctx_view.arch, &replay_seed);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        install_symbolic_hooks(
            &mut explorer,
            &scope,
            ctx_view.arch,
            &z3_ctx,
            &symbol_map,
            query_config.summary_profile,
        );
        let solve = explorer.solve_for_target(prepared, initial_state, target_addr);
        let selected = solve
            .selected_path_index
            .and_then(|idx| solve.matched_paths.get(idx).map(|path| (idx, path)))
            .map(|(idx, path)| path_info_from_result(idx, path, &explorer));
        (
            solve.matched_paths.len(),
            selected,
            solve.stats,
            solve.solver_stats,
        )
    }));

    let (matched_paths, selected_path, stats, solver_stats) = match solve_result {
        Ok(value) => value,
        Err(_) => return sym_error_json("symbolic replay solve failed (z3 context error)"),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", start_pc),
        target: format!("0x{:x}", target_addr),
        matched_paths,
        found: selected_path.is_some(),
        stats: build_sym_exec_summary(&stats, &solver_stats, matched_paths, None),
        selected_path,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize replay symbolic solve output"),
    }
}
