use crate::blocks::BlockSlice;
use crate::context::require_ctx_view;
use crate::helpers::effective_ptr_bits;
use crate::{ArchSpec, R2ILBlock, R2ILContext, parse_addr_name_map};
use serde::Serialize;
use serde_json::json;
use std::any::Any;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::fs::OpenOptions;
use std::io::Write;
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

fn solve_pipeline_debug_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_SOLVE_PIPELINE").is_some()
}

fn solve_pipeline_debug_log(message: &str) {
    if !solve_pipeline_debug_enabled() {
        return;
    }
    let line = format!("{message}\n");
    if let Some(path) = std::env::var_os("R2SLEIGH_DEBUG_SOLVE_PIPELINE_LOG") {
        if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
            let _ = file.write_all(line.as_bytes());
        }
        return;
    }
    let _ = std::io::stderr().write_all(line.as_bytes());
}

fn solve_pipeline_debug_stage(stage: &str) {
    solve_pipeline_debug_log(stage);
}

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
        max_states: 200,
        max_depth: 800,
        merge_states: merge_states_enabled(),
        timeout: Some(std::time::Duration::from_secs(20)),
        ..Default::default()
    }
}

fn sym_default_query_config() -> r2sym::SymQueryConfig {
    r2sym::SymQueryConfig {
        explore: sym_default_config(),
        mode: r2sym::QueryMode::TargetGuided,
        summary_profile: r2sym::SummaryProfile::Default,
        solve_tactics: r2sym::SolveTacticConfig::default(),
    }
}

fn tune_query_config_for_state(
    config: &mut r2sym::SymQueryConfig,
    prepared: &r2ssa::SsaArtifact,
    initial_state: &r2sym::SymState<'_>,
    route: Option<&r2sym::TargetQueryRoutePlan>,
) -> r2sym::QueryExecutionPolicy {
    let route = route
        .cloned()
        .unwrap_or_else(r2sym::TargetQueryRoutePlan::dynamic_fallback);
    let policy = r2sym::QueryExecutionPolicy::for_route(config, prepared, initial_state, route);
    r2sym::apply_query_execution_policy(config, &policy);
    policy
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
    let payload = json!({ "error": message }).to_string();
    CString::new(payload).map_or(ptr::null_mut(), |c| c.into_raw())
}

fn panic_payload_message(payload: &(dyn Any + Send)) -> Option<String> {
    payload.downcast_ref::<String>().cloned().or_else(|| {
        payload
            .downcast_ref::<&'static str>()
            .map(|msg| (*msg).to_string())
    })
}

fn sym_panic_json(default: &str, payload: Box<dyn Any + Send>) -> *mut c_char {
    let message = panic_payload_message(payload.as_ref())
        .map(|details| format!("{default}: {details}"))
        .unwrap_or_else(|| default.to_string());
    sym_error_json(&message)
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
    #[serde(default, skip_serializing_if = "is_zero")]
    target_pruned_cfg_unreachable: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    target_pruned_summary_contradiction: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    target_match_unsat: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_symbolic_breakpoint_forks: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_symbolic_breakpoint_pruned: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_breakpoint_loop_summaries: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_breakpoint_loop_exact_summaries: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_loop_exact_recurrence_summaries: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    runtime_loop_exact_folds: Vec<ExactLoopFoldInfo>,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_loop_refusals: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_loop_unknown_carried_state: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    runtime_loop_budget_residuals: usize,
    max_depth: usize,
    states_explored: usize,
    sat_queries: usize,
    sat_cache_hits: usize,
    sat_cache_misses: usize,
    solve_calls: usize,
    solve_unsat_shortcuts: usize,
    time_ms: u64,
    #[serde(
        default,
        skip_serializing_if = "r2ssa::AssumptionUsageReport::is_empty"
    )]
    assumption_usage: r2ssa::AssumptionUsageReport,
    #[serde(default, skip_serializing_if = "is_false")]
    assumption_conditioned: bool,
    #[serde(default, skip_serializing_if = "is_false")]
    summary_conditioned: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    runtime_diagnostics: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    semantic: Option<CompiledSemanticInfo>,
}

fn is_zero(value: &usize) -> bool {
    *value == 0
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct CompiledSemanticInfo {
    pub(crate) schema_version: u32,
    pub(crate) stage: String,
    pub(crate) granularity: String,
    pub(crate) execution: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) seed_mode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) replay_seed_fingerprint: Option<String>,
    pub(crate) query_plan: r2sym::QueryPlan,
    pub(crate) type_plan: r2sym::TypePlan,
    pub(crate) decompile_plan: r2sym::DecompilePlan,
    pub(crate) slice_class: String,
    pub(crate) residual_reasons: Vec<String>,
    pub(crate) ambiguous_target_count: usize,
    pub(crate) ambiguous_targets: Vec<String>,
    pub(crate) closure_functions: usize,
    pub(crate) helper_functions: usize,
    pub(crate) derived_summaries: usize,
    pub(crate) summary_attempted: usize,
    pub(crate) summary_budget_exhausted: usize,
    pub(crate) summary_scc_count: usize,
    pub(crate) region_count: usize,
    pub(crate) control_region_count: usize,
    pub(crate) memory_region_count: usize,
    pub(crate) memory_fact_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) memory_summaries: Vec<MemorySummaryInfo>,
    pub(crate) compiled_condition_count: usize,
    pub(crate) exact_compiled_condition_count: usize,
    pub(crate) actionable_compiled_condition_count: usize,
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

#[derive(Debug, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct MemorySummaryInfo {
    pub(crate) anchor: String,
    pub(crate) region: String,
    pub(crate) offset_lo: i64,
    pub(crate) offset_hi: i64,
    pub(crate) size: u32,
    pub(crate) exact_offset: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) binding: Option<String>,
    pub(crate) expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) value_expr: Option<String>,
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
    pub(crate) confidence: String,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmGuardConditionInfo {
    pub(crate) expr: String,
    pub(crate) value: String,
    pub(crate) expect_nonzero: bool,
    pub(crate) exact: bool,
    pub(crate) confidence: String,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmGuardedExitInfo {
    pub(crate) target: String,
    pub(crate) guard: VmGuardConditionInfo,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmMemoryConditionInfo {
    pub(crate) region: String,
    pub(crate) offset_lo: i64,
    pub(crate) offset_hi: i64,
    pub(crate) size: u32,
    pub(crate) exact_offset: bool,
    pub(crate) confidence: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) binding: Option<String>,
    pub(crate) expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) value_expr: Option<String>,
    pub(crate) exact_value: bool,
}

#[derive(Debug, Serialize, Clone)]
pub(crate) struct VmTransferArmInfo {
    pub(crate) handler_target: String,
    pub(crate) case_values: Vec<u64>,
    pub(crate) region_blocks: Vec<String>,
    pub(crate) exit_targets: Vec<String>,
    pub(crate) exit_guards: Vec<VmGuardedExitInfo>,
    pub(crate) state_updates: Vec<VmStateUpdateInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) selector_update: Option<VmStateUpdateInfo>,
    pub(crate) memory_reads: Vec<VmMemoryConditionInfo>,
    pub(crate) memory_writes: Vec<VmMemoryConditionInfo>,
    pub(crate) residual_guards: bool,
    pub(crate) residual_memory_effects: bool,
    pub(crate) exact: bool,
    pub(crate) confidence: String,
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
    pub(crate) handler_exit_guards: BTreeMap<String, Vec<VmGuardedExitInfo>>,
    pub(crate) handler_memory_read_effects: BTreeMap<String, Vec<VmMemoryConditionInfo>>,
    pub(crate) handler_memory_write_effects: BTreeMap<String, Vec<VmMemoryConditionInfo>>,
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

fn render_vm_value_expr(value: &r2sym::VmValueExpr) -> String {
    match value {
        r2sym::VmValueExpr::Const(value) => format!("0x{value:x}"),
        r2sym::VmValueExpr::Var(name) | r2sym::VmValueExpr::Expr(name) => name.clone(),
        r2sym::VmValueExpr::Unary { op, arg } => {
            let op = match op {
                r2sym::VmUnaryOp::Neg => "-",
                r2sym::VmUnaryOp::BitNot => "~",
                r2sym::VmUnaryOp::BoolNot => "!",
            };
            format!("({}{})", op, render_vm_value_expr(arg))
        }
        r2sym::VmValueExpr::Binary { op, lhs, rhs } => {
            let op = match op {
                r2sym::VmBinaryOp::Add => "+",
                r2sym::VmBinaryOp::Sub => "-",
                r2sym::VmBinaryOp::Mul => "*",
                r2sym::VmBinaryOp::Div => "/",
                r2sym::VmBinaryOp::Rem => "%",
                r2sym::VmBinaryOp::And => "&",
                r2sym::VmBinaryOp::Or => "|",
                r2sym::VmBinaryOp::Xor => "^",
                r2sym::VmBinaryOp::Shl => "<<",
                r2sym::VmBinaryOp::LShr | r2sym::VmBinaryOp::AShr => ">>",
                r2sym::VmBinaryOp::Eq => "==",
                r2sym::VmBinaryOp::Ne => "!=",
                r2sym::VmBinaryOp::Lt | r2sym::VmBinaryOp::SLt => "<",
                r2sym::VmBinaryOp::Le | r2sym::VmBinaryOp::SLe => "<=",
                r2sym::VmBinaryOp::BoolAnd => "&&",
                r2sym::VmBinaryOp::BoolOr => "||",
            };
            format!(
                "({} {} {})",
                render_vm_value_expr(lhs),
                op,
                render_vm_value_expr(rhs)
            )
        }
    }
}

fn render_semantic_confidence(confidence: r2sym::SemanticConfidence) -> String {
    match confidence {
        r2sym::SemanticConfidence::Exact => "exact",
        r2sym::SemanticConfidence::Likely => "likely",
        r2sym::SemanticConfidence::Heuristic => "heuristic",
        r2sym::SemanticConfidence::Residual => "residual",
    }
    .to_string()
}

fn vm_state_update_info_from_sym(update: &r2sym::VmStateUpdate) -> VmStateUpdateInfo {
    VmStateUpdateInfo {
        output: update.output.clone(),
        expr: update.expr.clone(),
        value: render_vm_value_expr(&update.value),
        exact: update.exact,
        confidence: render_semantic_confidence(update.confidence()),
    }
}

fn vm_guard_condition_info_from_sym(guard: &r2sym::VmGuardCondition) -> VmGuardConditionInfo {
    VmGuardConditionInfo {
        expr: guard.expr.clone(),
        value: render_vm_value_expr(&guard.value),
        expect_nonzero: guard.expect_nonzero,
        exact: guard.exact,
        confidence: render_semantic_confidence(guard.confidence()),
    }
}

fn vm_guarded_exit_info_from_sym(guarded: &r2sym::VmGuardedExit) -> VmGuardedExitInfo {
    VmGuardedExitInfo {
        target: format!("0x{:x}", guarded.target),
        guard: vm_guard_condition_info_from_sym(&guarded.guard),
    }
}

fn vm_memory_condition_info_from_sym(
    condition: &r2sym::VmMemoryCondition,
) -> VmMemoryConditionInfo {
    VmMemoryConditionInfo {
        region: format!(
            "{}:{}#{}",
            match condition.region.kind {
                r2sym::MemoryRegionKind::Stack => "stack",
                r2sym::MemoryRegionKind::Global => "global",
                r2sym::MemoryRegionKind::Input => "input",
                r2sym::MemoryRegionKind::Heap => "heap",
                r2sym::MemoryRegionKind::Replay => "replay",
                r2sym::MemoryRegionKind::EscapedUnknown => "unknown",
            },
            condition.region.name,
            condition.region.id
        ),
        offset_lo: condition.offset_lo,
        offset_hi: condition.offset_hi,
        size: condition.size,
        exact_offset: condition.exact_offset,
        confidence: render_semantic_confidence(condition.confidence()),
        binding: condition.binding.clone(),
        expr: condition.expr.clone(),
        value_expr: condition.value_expr.clone(),
        exact_value: condition.exact_value,
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
        exit_guards: transfer
            .exit_guards
            .iter()
            .map(vm_guarded_exit_info_from_sym)
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
        memory_reads: transfer
            .memory_reads
            .iter()
            .map(vm_memory_condition_info_from_sym)
            .collect(),
        memory_writes: transfer
            .memory_writes
            .iter()
            .map(vm_memory_condition_info_from_sym)
            .collect(),
        residual_guards: transfer.residual_guards,
        residual_memory_effects: transfer.residual_memory_effects,
        exact: transfer.exact,
        confidence: render_semantic_confidence(transfer.confidence()),
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
        handler_exit_guards: vm_step
            .handler_exit_guards
            .iter()
            .map(|(target, guards)| {
                (
                    format!("0x{target:x}"),
                    guards.iter().map(vm_guarded_exit_info_from_sym).collect(),
                )
            })
            .collect(),
        handler_memory_read_effects: vm_step
            .handler_memory_read_effects
            .iter()
            .map(|(target, conditions)| {
                (
                    format!("0x{target:x}"),
                    conditions
                        .iter()
                        .map(vm_memory_condition_info_from_sym)
                        .collect(),
                )
            })
            .collect(),
        handler_memory_write_effects: vm_step
            .handler_memory_write_effects
            .iter()
            .map(|(target, conditions)| {
                (
                    format!("0x{target:x}"),
                    conditions
                        .iter()
                        .map(vm_memory_condition_info_from_sym)
                        .collect(),
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
    #[serde(skip_serializing_if = "Option::is_none")]
    target_query: Option<TargetQueryInfo>,
    paths: Vec<PathInfo>,
}

#[derive(Serialize)]
struct SymTargetSolveResult {
    entry: String,
    target: String,
    status: String,
    matched_paths: usize,
    found: bool,
    target_reached_under_model: bool,
    candidate_solution_verified: bool,
    residual_reasons: Vec<String>,
    model_validation: ModelValidationInfo,
    witness: SolveWitnessInfo,
    stats: SymExecSummary,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_query: Option<TargetQueryInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    selected_path: Option<PathInfo>,
}

#[derive(Serialize)]
struct ModelValidationInfo {
    status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
}

#[derive(Serialize)]
struct SolveWitnessInfo {
    target: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    selected_path_index: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    final_pc: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    candidate: Option<SolveCandidateShapeInfo>,
    evidence: EvidenceSummaryInfo,
    verification_requirement: VerificationRequirementInfo,
    proven: bool,
}

#[derive(Serialize)]
struct SolveCandidateShapeInfo {
    input_scalars: usize,
    input_buffers: usize,
    registers: usize,
    memory_regions: usize,
    concrete_assignments: usize,
    final_pc: String,
    num_constraints: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    generation: Option<SolveCandidateGenerationInfo>,
}

#[derive(Serialize)]
struct SolveCandidateGenerationInfo {
    kind: String,
    reason: String,
    constrained_bytes: usize,
}

#[derive(Serialize)]
struct EvidenceSummaryInfo {
    precision: String,
    requires_replay: bool,
    reasons: Vec<String>,
    final_constraint_precision: String,
    exact_final_constraints: usize,
    model_conditioned_final_constraints: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    exact_loop_recurrences: Vec<ExactLoopRecurrenceInfo>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    exact_loop_folds: Vec<ExactLoopFoldInfo>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    tactics: Vec<SolveTacticInfo>,
}

#[derive(Serialize)]
struct VerificationRequirementInfo {
    status: String,
    reasons: Vec<String>,
}

#[derive(Serialize, Clone)]
struct ExactLoopFoldInfo {
    header: String,
    exit_target: String,
    iterations: u64,
    accumulator: String,
    bits: u32,
    operation: String,
    memory: LoopMemoryTermInfo,
}

#[derive(Serialize, Clone)]
struct ExactLoopRecurrenceInfo {
    header: String,
    exit_target: String,
    iterations: u64,
    accumulator: String,
    bits: u32,
    kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    constant: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    multiplier: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    addend: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    direction: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    amount: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    operation: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory: Option<LoopMemoryTermInfo>,
}

#[derive(Serialize, Clone)]
struct LoopMemoryTermInfo {
    kind: String,
    addr: String,
    bytes: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    base: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    stride: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    region: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    region_base: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    region_size: Option<u64>,
}

#[derive(Serialize, Clone)]
struct SolveTacticInfo {
    kind: String,
    status: String,
    reason: String,
    recurrence: ExactLoopRecurrenceInfo,
}

#[derive(Serialize, Clone)]
struct TargetQueryInfo {
    plan: r2sym::TargetQueryPlan,
    route: r2sym::TargetQueryRoutePlan,
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

fn is_false(value: &bool) -> bool {
    !*value
}

fn build_sym_exec_summary(
    stats: &r2sym::path::ExploreStats,
    solver_stats: &r2sym::SolverStats,
    paths_feasible: usize,
    assumption_usage: r2ssa::AssumptionUsageReport,
    assumption_conditioned: bool,
    summary_conditioned: bool,
    semantic: Option<&r2sym::SemanticArtifact>,
) -> SymExecSummary {
    build_sym_exec_summary_with_semantic_info(
        stats,
        solver_stats,
        paths_feasible,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        semantic.map(compiled_semantic_info),
    )
}

fn build_sym_exec_summary_with_semantic_info(
    stats: &r2sym::path::ExploreStats,
    solver_stats: &r2sym::SolverStats,
    paths_feasible: usize,
    assumption_usage: r2ssa::AssumptionUsageReport,
    assumption_conditioned: bool,
    summary_conditioned: bool,
    semantic: Option<CompiledSemanticInfo>,
) -> SymExecSummary {
    let mut runtime_diagnostics = Vec::new();
    if stats.runtime_missing_exception_handler > 0 {
        runtime_diagnostics.push("missing_exception_handler".to_string());
    }
    if stats.runtime_missing_materialized_code > 0 {
        runtime_diagnostics.push("missing_runtime_materialized_code".to_string());
    }
    if stats.runtime_missing_continuation_seed > 0 {
        runtime_diagnostics.push("missing_continuation_seed".to_string());
    }
    if stats.runtime_region_provenance_unknown > 0 {
        runtime_diagnostics.push("runtime_region_provenance_unknown".to_string());
    }
    if stats.timed_out && stats.runtime_symbolic_breakpoint_forks > 0 {
        runtime_diagnostics.push("runtime_symbolic_breakpoint_budget_exhausted".to_string());
    }
    if stats.runtime_breakpoint_loop_summaries > 0 {
        runtime_diagnostics.push("runtime_breakpoint_loop_summary_residual".to_string());
    }
    if stats.runtime_breakpoint_loop_exact_summaries > 0 {
        runtime_diagnostics.push("runtime_breakpoint_loop_summary_exact".to_string());
    }
    if stats.runtime_loop_exact_recurrence_summaries > 0 {
        runtime_diagnostics.push("runtime_loop_exact_recurrence_summary".to_string());
    }
    if stats.runtime_loop_unknown_carried_state > 0 {
        runtime_diagnostics.push("runtime_loop_unknown_carried_state".to_string());
    }
    if stats.runtime_loop_budget_residuals > 0 {
        runtime_diagnostics.push("runtime_loop_iteration_budget".to_string());
    }
    if stats.runtime_loop_refusals > 0 {
        runtime_diagnostics.push("runtime_loop_refused".to_string());
    }
    SymExecSummary {
        paths_explored: stats.paths_completed,
        paths_feasible,
        paths_pruned: stats.paths_pruned,
        target_pruned_cfg_unreachable: stats.target_pruned_cfg_unreachable,
        target_pruned_summary_contradiction: stats.target_pruned_summary_contradiction,
        target_match_unsat: stats.target_match_unsat,
        runtime_symbolic_breakpoint_forks: stats.runtime_symbolic_breakpoint_forks,
        runtime_symbolic_breakpoint_pruned: stats.runtime_symbolic_breakpoint_pruned,
        runtime_breakpoint_loop_summaries: stats.runtime_breakpoint_loop_summaries,
        runtime_breakpoint_loop_exact_summaries: stats.runtime_breakpoint_loop_exact_summaries,
        runtime_loop_exact_recurrence_summaries: stats.runtime_loop_exact_recurrence_summaries,
        runtime_loop_exact_folds: stats
            .runtime_loop_exact_folds
            .iter()
            .map(exact_loop_fold_info)
            .collect(),
        runtime_loop_refusals: stats.runtime_loop_refusals,
        runtime_loop_unknown_carried_state: stats.runtime_loop_unknown_carried_state,
        runtime_loop_budget_residuals: stats.runtime_loop_budget_residuals,
        max_depth: stats.max_depth_reached,
        states_explored: stats.states_explored,
        sat_queries: solver_stats.sat_queries,
        sat_cache_hits: solver_stats.sat_cache_hits,
        sat_cache_misses: solver_stats.sat_cache_misses,
        solve_calls: solver_stats.solve_calls,
        solve_unsat_shortcuts: solver_stats.solve_unsat_shortcuts,
        time_ms: stats.total_time.as_millis() as u64,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        runtime_diagnostics,
        semantic,
    }
}

fn target_query_info(route: &r2sym::TargetQueryRoutePlan) -> TargetQueryInfo {
    TargetQueryInfo {
        plan: route.target_plan.clone(),
        route: route.clone(),
    }
}

fn solve_status_string(status: r2sym::SolveStatus) -> String {
    match status {
        r2sym::SolveStatus::Solved => "solved",
        r2sym::SolveStatus::Candidate => "candidate",
        r2sym::SolveStatus::ResidualReachable => "residual_reachable",
        r2sym::SolveStatus::Unverified => "unverified",
        r2sym::SolveStatus::Unsat => "unsat",
        r2sym::SolveStatus::Unknown => "unknown",
        r2sym::SolveStatus::BudgetExhausted => "budget_exhausted",
    }
    .to_string()
}

fn solve_found(status: r2sym::SolveStatus) -> bool {
    matches!(status, r2sym::SolveStatus::Solved)
}

fn model_validation_info(validation: &r2sym::ModelValidation) -> ModelValidationInfo {
    match validation {
        r2sym::ModelValidation::NotRequired => ModelValidationInfo {
            status: "not_required".to_string(),
            reason: None,
        },
        r2sym::ModelValidation::Verified => ModelValidationInfo {
            status: "verified".to_string(),
            reason: None,
        },
        r2sym::ModelValidation::Failed { reason } => ModelValidationInfo {
            status: "failed".to_string(),
            reason: Some(reason.clone()),
        },
        r2sym::ModelValidation::Unavailable { reason } => ModelValidationInfo {
            status: "unavailable".to_string(),
            reason: Some(reason.clone()),
        },
    }
}

fn fact_precision_string(precision: r2sym::FactPrecision) -> String {
    match precision {
        r2sym::FactPrecision::Unknown => "unknown",
        r2sym::FactPrecision::UnderApprox => "under_approx",
        r2sym::FactPrecision::Residual => "residual",
        r2sym::FactPrecision::OverApprox => "over_approx",
        r2sym::FactPrecision::Exact => "exact",
    }
    .to_string()
}

fn verification_requirement_info(
    requirement: &r2sym::VerificationRequirement,
) -> VerificationRequirementInfo {
    match requirement {
        r2sym::VerificationRequirement::NotRequired => VerificationRequirementInfo {
            status: "not_required".to_string(),
            reasons: Vec::new(),
        },
        r2sym::VerificationRequirement::Required { reasons } => VerificationRequirementInfo {
            status: "required".to_string(),
            reasons: reasons.clone(),
        },
        r2sym::VerificationRequirement::Refused { reasons } => VerificationRequirementInfo {
            status: "refused".to_string(),
            reasons: reasons.clone(),
        },
    }
}

fn loop_memory_term_kind_string(kind: r2sym::LoopMemoryTermKind) -> String {
    match kind {
        r2sym::LoopMemoryTermKind::TableRead => "table_read",
        r2sym::LoopMemoryTermKind::InputRead => "input_read",
        r2sym::LoopMemoryTermKind::RuntimeBlobRead => "runtime_blob_read",
        r2sym::LoopMemoryTermKind::Unknown => "unknown",
    }
    .to_string()
}

fn loop_fold_operation_string(operation: r2sym::LoopFoldOperation) -> String {
    match operation {
        r2sym::LoopFoldOperation::Add => "add",
        r2sym::LoopFoldOperation::Xor => "xor",
    }
    .to_string()
}

fn loop_rotate_direction_string(direction: r2sym::LoopRotateDirection) -> String {
    match direction {
        r2sym::LoopRotateDirection::Left => "left",
        r2sym::LoopRotateDirection::Right => "right",
    }
    .to_string()
}

fn solve_tactic_kind_string(kind: r2sym::SolveTacticKind) -> String {
    match kind {
        r2sym::SolveTacticKind::XorFoldPreimage => "xor_fold_preimage",
        r2sym::SolveTacticKind::AddFoldPreimage => "add_fold_preimage",
        r2sym::SolveTacticKind::RotateXorRecurrence => "rotate_xor_recurrence",
        r2sym::SolveTacticKind::RotateAddRecurrence => "rotate_add_recurrence",
        r2sym::SolveTacticKind::ConcreteTableFold => "concrete_table_fold",
        r2sym::SolveTacticKind::RuntimeBlobFold => "runtime_blob_fold",
    }
    .to_string()
}

fn solve_tactic_status_string(status: r2sym::SolveTacticStatus) -> String {
    match status {
        r2sym::SolveTacticStatus::Available => "available",
        r2sym::SolveTacticStatus::EvidenceOnly => "evidence_only",
    }
    .to_string()
}

fn loop_memory_term_info(term: &r2sym::LoopMemoryTerm) -> LoopMemoryTermInfo {
    LoopMemoryTermInfo {
        kind: loop_memory_term_kind_string(term.kind),
        addr: term.addr.clone(),
        bytes: term.bytes,
        base: term.base.map(|addr| format!("0x{addr:x}")),
        stride: term.stride,
        region: term.region.clone(),
        region_base: term.region_base.map(|addr| format!("0x{addr:x}")),
        region_size: term.region_size,
    }
}

fn exact_loop_fold_info(fold: &r2sym::ExactLoopFoldEvidence) -> ExactLoopFoldInfo {
    ExactLoopFoldInfo {
        header: format!("0x{:x}", fold.header),
        exit_target: format!("0x{:x}", fold.exit_target),
        iterations: fold.iterations,
        accumulator: fold.accumulator.clone(),
        bits: fold.bits,
        operation: loop_fold_operation_string(fold.operation),
        memory: loop_memory_term_info(&fold.term),
    }
}

fn exact_loop_recurrence_info(
    recurrence: &r2sym::ExactLoopRecurrenceEvidence,
) -> ExactLoopRecurrenceInfo {
    let (kind, constant, multiplier, addend, direction, amount, operation, memory) =
        match &recurrence.kind {
            r2sym::ExactLoopRecurrenceKind::AddConst(value) => (
                "add_const".to_string(),
                Some(format!("0x{value:x}")),
                None,
                None,
                None,
                None,
                None,
                None,
            ),
            r2sym::ExactLoopRecurrenceKind::SubConst(value) => (
                "sub_const".to_string(),
                Some(format!("0x{value:x}")),
                None,
                None,
                None,
                None,
                None,
                None,
            ),
            r2sym::ExactLoopRecurrenceKind::AffineConst { multiplier, addend } => (
                "affine_const".to_string(),
                None,
                Some(format!("0x{multiplier:x}")),
                Some(format!("0x{addend:x}")),
                None,
                None,
                None,
                None,
            ),
            r2sym::ExactLoopRecurrenceKind::XorConst(value) => (
                "xor_const".to_string(),
                Some(format!("0x{value:x}")),
                None,
                None,
                None,
                None,
                None,
                None,
            ),
            r2sym::ExactLoopRecurrenceKind::Fold { operation, term } => (
                "fold".to_string(),
                None,
                None,
                None,
                None,
                None,
                Some(loop_fold_operation_string(*operation)),
                Some(loop_memory_term_info(term)),
            ),
            r2sym::ExactLoopRecurrenceKind::RotateMix {
                direction,
                amount,
                operation,
                term,
            } => (
                "rotate_mix".to_string(),
                None,
                None,
                None,
                Some(loop_rotate_direction_string(*direction)),
                Some(*amount),
                Some(loop_fold_operation_string(*operation)),
                Some(loop_memory_term_info(term)),
            ),
        };
    ExactLoopRecurrenceInfo {
        header: format!("0x{:x}", recurrence.header),
        exit_target: format!("0x{:x}", recurrence.exit_target),
        iterations: recurrence.iterations,
        accumulator: recurrence.accumulator.clone(),
        bits: recurrence.bits,
        kind,
        constant,
        multiplier,
        addend,
        direction,
        amount,
        operation,
        memory,
    }
}

fn solve_tactic_info(tactic: &r2sym::SolveTacticEvidence) -> SolveTacticInfo {
    SolveTacticInfo {
        kind: solve_tactic_kind_string(tactic.kind),
        status: solve_tactic_status_string(tactic.status),
        reason: tactic.reason.clone(),
        recurrence: exact_loop_recurrence_info(&tactic.recurrence),
    }
}

fn solve_candidate_shape_info(candidate: &r2sym::SolveCandidateShape) -> SolveCandidateShapeInfo {
    SolveCandidateShapeInfo {
        input_scalars: candidate.input_scalars,
        input_buffers: candidate.input_buffers,
        registers: candidate.registers,
        memory_regions: candidate.memory_regions,
        concrete_assignments: candidate.concrete_assignments,
        final_pc: format!("0x{:x}", candidate.final_pc),
        num_constraints: candidate.num_constraints,
        generation: candidate
            .generation
            .as_ref()
            .map(solve_candidate_generation_info),
    }
}

fn solve_candidate_generation_info(
    generation: &r2sym::SolvedPathGeneration,
) -> SolveCandidateGenerationInfo {
    SolveCandidateGenerationInfo {
        kind: match generation.kind {
            r2sym::SolvedPathGenerationKind::ExactRecurrenceConstraintTactic => {
                "exact_recurrence_constraint_tactic"
            }
            r2sym::SolvedPathGenerationKind::MitmConstraintTactic => "mitm_constraint_tactic",
            r2sym::SolvedPathGenerationKind::DomainConstraintTactic => "domain_constraint_tactic",
        }
        .to_string(),
        reason: generation.reason.clone(),
        constrained_bytes: generation.constrained_bytes,
    }
}

fn solve_witness_info(witness: &r2sym::SolveWitness) -> SolveWitnessInfo {
    SolveWitnessInfo {
        target: format!("0x{:x}", witness.target_addr),
        selected_path_index: witness.selected_path_index,
        final_pc: witness.final_pc.map(|pc| format!("0x{pc:x}")),
        candidate: witness.candidate.as_ref().map(solve_candidate_shape_info),
        evidence: EvidenceSummaryInfo {
            precision: fact_precision_string(witness.evidence.precision),
            requires_replay: witness.evidence.requires_replay,
            reasons: witness.evidence.reasons.clone(),
            final_constraint_precision: final_constraint_precision_string(
                witness.evidence.final_constraint_precision,
            ),
            exact_final_constraints: witness.evidence.exact_final_constraints,
            model_conditioned_final_constraints: witness
                .evidence
                .model_conditioned_final_constraints,
            exact_loop_recurrences: witness
                .evidence
                .exact_loop_recurrences
                .iter()
                .map(exact_loop_recurrence_info)
                .collect(),
            exact_loop_folds: witness
                .evidence
                .exact_loop_folds
                .iter()
                .map(exact_loop_fold_info)
                .collect(),
            tactics: witness
                .evidence
                .tactics
                .iter()
                .map(solve_tactic_info)
                .collect(),
        },
        verification_requirement: verification_requirement_info(&witness.verification_requirement),
        proven: witness.is_proven(),
    }
}

fn final_constraint_precision_string(precision: r2sym::FinalConstraintPrecision) -> String {
    match precision {
        r2sym::FinalConstraintPrecision::Exact => "exact",
        r2sym::FinalConstraintPrecision::ModelConditioned => "model_conditioned",
        r2sym::FinalConstraintPrecision::Residual => "residual",
        r2sym::FinalConstraintPrecision::Unknown => "unknown",
    }
    .to_string()
}

fn empty_symbolic_summary<'ctx>() -> r2sym::SymbolicFunctionSummary<'ctx> {
    r2sym::SymbolicFunctionSummary {
        completion: r2sym::QueryCompletion::Complete,
        paths: Vec::new(),
        feasible_paths: 0,
        stats: r2sym::path::ExploreStats::default(),
        solver_stats: r2sym::SolverStats::default(),
    }
}

fn should_skip_expensive_symbolic_summary(
    compiled: &r2sym::SemanticArtifact,
    prepared: &r2ssa::SsaArtifact,
) -> bool {
    compiled.diagnostics.skipped_large_cfg
        || prepared.function().cfg_risk_summary().block_count > 96
}

pub(crate) fn compiled_semantic_info(compiled: &r2sym::SemanticArtifact) -> CompiledSemanticInfo {
    compiled_semantic_info_with_seed(compiled, None)
}

fn memory_summary_region_label(region: &r2sym::BackwardMemoryRegion) -> String {
    match region {
        r2sym::BackwardMemoryRegion::Argument { index } => format!("arg{index}"),
        r2sym::BackwardMemoryRegion::Region(region) => format!("{:?}:{}", region.kind, region.name),
    }
}

fn semantic_memory_summaries(native: Option<&r2sym::NativeArtifactBody>) -> Vec<MemorySummaryInfo> {
    let mut summaries = native
        .into_iter()
        .flat_map(|body| body.regions.values())
        .flat_map(|region| {
            region.memory.iter().map(|fact| {
                let term = &fact.value.term;
                MemorySummaryInfo {
                    anchor: format!("0x{:x}", region.anchor),
                    region: memory_summary_region_label(&term.region),
                    offset_lo: term.offset_lo,
                    offset_hi: term.offset_hi,
                    size: term.size,
                    exact_offset: term.exact_offset,
                    binding: term.binding.clone(),
                    expr: term.expr.clone(),
                    value_expr: term.value_expr.clone(),
                }
            })
        })
        .collect::<Vec<_>>();
    summaries.sort();
    summaries.dedup();
    summaries
}

fn compiled_semantic_info_with_replay_seed(
    compiled: &r2sym::SemanticArtifact,
    replay_seed: &r2sym::ReplaySeed,
) -> CompiledSemanticInfo {
    compiled_semantic_info_with_seed(
        compiled,
        Some(r2sym::stable_replay_seed_fingerprint(replay_seed)),
    )
}

fn compiled_semantic_info_with_seed(
    compiled: &r2sym::SemanticArtifact,
    replay_seed_fingerprint: Option<u64>,
) -> CompiledSemanticInfo {
    let native = compiled.native_body();
    let memory_summaries = semantic_memory_summaries(native);
    let memory_fact_count = memory_summaries.len();
    CompiledSemanticInfo {
        schema_version: r2sym::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
        stage: match compiled.stage {
            r2sym::RefinementStage::Raw => "raw",
            r2sym::RefinementStage::Compiled => "compiled",
            r2sym::RefinementStage::Residual => "residual",
        }
        .to_string(),
        granularity: match compiled.granularity {
            r2sym::ArtifactGranularity::WholeFunction => "whole_function",
            r2sym::ArtifactGranularity::Regioned => "regioned",
            r2sym::ArtifactGranularity::SummaryOnly => "summary_only",
        }
        .to_string(),
        execution: match compiled.execution {
            r2sym::ExecutionModel::Native => "native",
            r2sym::ExecutionModel::Vm => "vm",
        }
        .to_string(),
        seed_mode: replay_seed_fingerprint.map(|_| "replay".to_string()),
        replay_seed_fingerprint: replay_seed_fingerprint
            .map(|fingerprint| format!("0x{fingerprint:x}")),
        query_plan: compiled.query_plan(),
        type_plan: compiled.type_plan(),
        decompile_plan: compiled.decompile_plan(),
        slice_class: compiled
            .slice_class()
            .map(|slice_class| match slice_class {
                r2sym::SliceClass::Wrapper => "wrapper",
                r2sym::SliceClass::Worker => "worker",
                r2sym::SliceClass::RecursiveGroup => "recursive_group",
                r2sym::SliceClass::InterpreterSwitch => "interpreter_switch",
                r2sym::SliceClass::InterpreterIndirect => "interpreter_indirect",
                r2sym::SliceClass::GenericLarge => "generic_large",
            })
            .unwrap_or("worker")
            .to_string(),
        residual_reasons: compiled
            .diagnostics
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
        ambiguous_target_count: compiled.ambiguous_targets().len(),
        ambiguous_targets: compiled
            .ambiguous_targets()
            .into_iter()
            .map(|target| format!("0x{target:x}"))
            .collect(),
        closure_functions: compiled
            .native_body()
            .map(|body| body.summary.closure_functions)
            .unwrap_or(0),
        helper_functions: compiled
            .native_body()
            .map(|body| body.summary.helper_functions)
            .unwrap_or(0),
        derived_summaries: compiled
            .native_body()
            .map(|body| body.summary.derived_summaries)
            .unwrap_or(0),
        summary_attempted: compiled
            .native_body()
            .map(|body| body.summary.derived_diagnostics.attempted)
            .unwrap_or(0),
        summary_budget_exhausted: compiled
            .native_body()
            .map(|body| {
                body.summary.derived_diagnostics.budget_exhausted
                    + body.summary.derived_diagnostics.scc_budget_exhausted
            })
            .unwrap_or(0),
        summary_scc_count: compiled
            .native_body()
            .map(|body| body.summary.derived_diagnostics.scc_count)
            .unwrap_or(0),
        region_count: native.map(|body| body.regions.len()).unwrap_or(0),
        control_region_count: native
            .map(|body| {
                body.regions
                    .values()
                    .filter(|region| !region.control.is_empty())
                    .count()
            })
            .unwrap_or(0),
        memory_region_count: native
            .map(|body| {
                body.regions
                    .values()
                    .filter(|region| !region.memory.is_empty())
                    .count()
            })
            .unwrap_or(0),
        memory_fact_count,
        memory_summaries,
        compiled_condition_count: compiled.actionable_control_count(),
        exact_compiled_condition_count: compiled.exact_control_count(),
        actionable_compiled_condition_count: compiled.actionable_control_count(),
        branches_pruned: compiled.diagnostics.branches_pruned,
        branches_unknown: compiled.diagnostics.branches_unknown,
        skipped_large_cfg: compiled.diagnostics.skipped_large_cfg,
        interpreter: compiled
            .vm_body()
            .and_then(|body| body.interpreter.as_ref())
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
        vm_step: compiled
            .vm_body()
            .and_then(|body| body.step_summary.as_ref())
            .map(vm_step_summary_info_from_sym),
        vm_transfer: compiled
            .vm_body()
            .and_then(|body| body.transfer_summary.as_ref())
            .map(vm_step_summary_info_from_sym),
        cache_hit: compiled.diagnostics.cache_hit,
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
            .filter(|(name, _)| is_public_solution_symbol(name))
            .map(|(k, v)| (k, format!("0x{:x}", v)))
            .collect(),
        registers: solved
            .registers
            .into_iter()
            .filter(|(name, _)| is_public_solution_register(name))
            .map(|(k, v)| (k, format!("0x{:x}", v)))
            .collect(),
    })
}

fn is_flag_like_symbol(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "cy" | "cf"
            | "ng"
            | "nf"
            | "ov"
            | "of"
            | "zr"
            | "zf"
            | "sf"
            | "pf"
            | "af"
            | "df"
            | "tmpcy"
            | "tmpng"
            | "tmpov"
            | "tmpzr"
    )
}

fn is_public_solution_symbol(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if lower.starts_with("tmp:")
        || lower.starts_with("tmp")
        || lower.starts_with("const:")
        || lower.starts_with("ram:")
        || lower.starts_with("unique:")
    {
        return false;
    }
    let base = lower.split('_').next().unwrap_or(lower.as_str());
    !is_flag_like_symbol(base) && !is_frame_scaffold_symbol(base)
}

fn is_public_solution_register(name: &str) -> bool {
    if name.contains("_0") {
        return false;
    }
    is_public_solution_symbol(name)
}

fn is_frame_scaffold_symbol(base: &str) -> bool {
    matches!(
        base,
        "sp" | "fp" | "x29" | "w29" | "x30" | "w30" | "lr" | "pc"
    )
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
            .filter(|(name, _)| is_public_solution_symbol(name))
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
            .filter(|(name, _)| is_public_solution_register(name))
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
    name: Option<&str>,
) -> Option<r2ssa::SsaArtifact> {
    let prepared = if name.is_some_and(|name| name.starts_with("runtime.materialized.")) {
        r2ssa::SsaArtifact::raw(blocks, arch)?
    } else {
        r2ssa::SsaArtifact::for_symbolic(blocks, arch)?
    };
    Some(match name {
        Some(name) if !name.is_empty() => prepared.with_name(name.to_string()),
        _ => prepared,
    })
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
        let name = if function.name.is_null() {
            None
        } else {
            unsafe { CStr::from_ptr(function.name).to_str().ok() }.map(str::to_string)
        };
        let prepared = build_symbolic_prepared(blocks.as_slice(), arch, name.as_deref())?;
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

fn scope_root_prepared(scope: &r2sym::PreparedFunctionScope) -> Option<&r2ssa::SsaArtifact> {
    scope.root().map(|function| &function.prepared)
}

fn prepared_assumption_conflicted(prepared: &r2ssa::SsaArtifact) -> bool {
    !prepared.facts().assumption_usage.conflicts.is_empty()
}

fn prepared_assumption_conditioning(
    prepared: &r2ssa::SsaArtifact,
) -> (r2ssa::AssumptionUsageReport, bool) {
    let usage = prepared.facts().assumption_usage.clone();
    let conditioned = !usage.applied.is_empty() || !usage.conflicts.is_empty();
    (usage, conditioned)
}

struct PredictedTargetQueryRouteInput<'ctx, 'a> {
    z3_ctx: &'ctx Context,
    prepared: &'a r2ssa::SsaArtifact,
    scope: Option<&'a r2sym::PreparedFunctionScope>,
    compiled: &'a r2sym::SemanticArtifact,
    target_addr: u64,
    arch: Option<&'a ArchSpec>,
    symbol_map: &'a HashMap<u64, String>,
    summary_profile: r2sym::SummaryProfile,
    assumption_conflicted: bool,
}

fn predicted_target_query_route(
    input: PredictedTargetQueryRouteInput<'_, '_>,
) -> r2sym::TargetQueryRoutePlan {
    let PredictedTargetQueryRouteInput {
        z3_ctx,
        prepared,
        scope,
        compiled,
        target_addr,
        arch,
        symbol_map,
        summary_profile,
        assumption_conflicted,
    } = input;
    let probe_config = r2sym::SymQueryConfig {
        explore: sym_default_config(),
        mode: r2sym::QueryMode::TargetGuided,
        summary_profile,
        solve_tactics: r2sym::SolveTacticConfig::default(),
    };
    let mut explorer = probe_config.make_explorer(z3_ctx);
    if let Some(scope) = scope {
        r2sym::install_runtime_hooks_for_scope(&mut explorer, scope, arch, symbol_map);
    }
    r2sym::selected_target_query_route_in_scope(
        &mut explorer,
        prepared,
        scope,
        Some(compiled),
        target_addr,
        assumption_conflicted,
    )
}

fn parse_scope_assumptions(
    external_context_json: *const c_char,
    arch: Option<&ArchSpec>,
) -> Result<r2ssa::AssumptionSet, &'static str> {
    if external_context_json.is_null() {
        return Ok(r2ssa::AssumptionSet::default());
    }
    let text = unsafe { CStr::from_ptr(external_context_json) }
        .to_str()
        .map_err(|_| "external context is not valid utf-8")?;
    let trimmed = text.trim();
    if trimmed.starts_with('[') {
        let assumptions = serde_json::from_str::<Vec<r2ssa::AnalysisAssumption>>(trimmed)
            .map_err(|_| "assumptions json is invalid")?;
        return Ok(r2ssa::AssumptionSet::new(assumptions));
    }
    let ptr_bits = arch.map(effective_ptr_bits).unwrap_or(64);
    Ok(r2types::parse_external_context_json(text, ptr_bits).assumptions)
}

fn scope_with_external_assumptions(
    scope: &r2sym::PreparedFunctionScope,
    arch: Option<&ArchSpec>,
    external_context_json: *const c_char,
) -> Result<r2sym::PreparedFunctionScope, &'static str> {
    let assumptions = parse_scope_assumptions(external_context_json, arch)?;
    let prepared = scope_root_prepared(scope).ok_or("failed to build root SSA function")?;
    let prepared = if assumptions.is_empty() {
        prepared.clone()
    } else {
        prepared.with_assumptions(&assumptions)
    };
    scope
        .with_prepared_root(&prepared)
        .ok_or("failed to build symbolic scope")
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

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch, None) {
        Some(prepared) => prepared,
        None => return ptr::null_mut(),
    };
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let mut query_config = sym_paths_query_config(&prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_semantic_artifact_with_scope(
            &z3_ctx,
            &prepared,
            Some(&scope),
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        if should_skip_expensive_symbolic_summary(&compiled, &prepared) {
            return (empty_symbolic_summary(), compiled);
        }
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let query_policy =
            tune_query_config_for_state(&mut query_config, &prepared, &initial_state, None);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        (
            explorer.summarize_function(&prepared, initial_state),
            compiled,
        )
    }));

    let (summary, compiled) = match explore_result {
        Ok(r) => r,
        Err(err) => {
            return sym_panic_json("symbolic execution failed", err);
        }
    };

    let output = build_sym_exec_summary(
        &summary.stats,
        &summary.solver_stats,
        summary.feasible_paths,
        r2ssa::AssumptionUsageReport::default(),
        false,
        false,
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

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch, None) {
        Some(prepared) => prepared,
        None => return ptr::null_mut(),
    };
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let mut query_config = sym_paths_query_config(&prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let query_policy =
            tune_query_config_for_state(&mut query_config, &prepared, &initial_state, None);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let summary = explorer.summarize_function(&prepared, initial_state);
        (summary, explorer)
    }));

    let (summary, explorer) = match explore_result {
        Ok(r) => r,
        Err(err) => {
            return sym_panic_json("symbolic execution failed", err);
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

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch, None) {
        Some(prepared) => prepared,
        None => return sym_error_json("failed to build SSA function"),
    };
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let symbol_map = symbol_map_snapshot();
    let mut query_config = sym_default_query_config();

    let z3_ctx = Context::thread_local();
    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            &z3_ctx,
            &prepared,
            Some(&scope),
            target_addr,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let selected_route = predicted_target_query_route(PredictedTargetQueryRouteInput {
            z3_ctx: &z3_ctx,
            prepared: &prepared,
            scope: Some(&scope),
            compiled: &compiled,
            target_addr,
            arch: ctx_view.arch,
            symbol_map: &symbol_map,
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(&prepared),
        });
        let query_policy = tune_query_config_for_state(
            &mut query_config,
            &prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let reach = explorer.can_reach_with_artifact_in_scope(
            &prepared,
            Some(&scope),
            Some(&compiled),
            initial_state,
            target_addr,
        );
        let paths: Vec<PathInfo> = reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (
            paths,
            reach.stats,
            reach.solver_stats,
            reach.assumption_usage,
            reach.assumption_conditioned,
            reach.summary_conditioned,
            reach.selected_route,
            compiled.clone(),
        )
    }));

    let (
        paths,
        stats,
        solver_stats,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        selected_route,
        compiled,
    ) = match explore_result {
        Ok(value) => value,
        Err(err) => return sym_panic_json("symbolic execution failed", err),
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: build_sym_exec_summary(
            &stats,
            &solver_stats,
            paths.len(),
            assumption_usage,
            assumption_conditioned,
            summary_conditioned,
            Some(&compiled),
        ),
        target_query: Some(target_query_info(&selected_route)),
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

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch, None) {
        Some(prepared) => prepared,
        None => return sym_error_json("failed to build SSA function"),
    };
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let symbol_map = symbol_map_snapshot();
    let mut query_config = sym_default_query_config();
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            &z3_ctx,
            &prepared,
            Some(&scope),
            target_addr,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        let selected_route = predicted_target_query_route(PredictedTargetQueryRouteInput {
            z3_ctx: &z3_ctx,
            prepared: &prepared,
            scope: Some(&scope),
            compiled: &compiled,
            target_addr,
            arch: ctx_view.arch,
            symbol_map: &symbol_map,
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(&prepared),
        });
        let query_policy = tune_query_config_for_state(
            &mut query_config,
            &prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let solve = explorer.solve_for_target_with_artifact_in_scope(
            &prepared,
            Some(&scope),
            Some(&compiled),
            initial_state,
            target_addr,
        );
        let selected = solve
            .selected_path_index
            .and_then(|idx| solve.matched_paths.get(idx).map(|path| (idx, path)))
            .map(|(idx, path)| {
                path_info_from_result_with_solution(idx, path, &explorer, solve_found(solve.status))
            });
        (
            solve.status,
            solve.matched_paths.len(),
            selected,
            solve.verification,
            solve.witness,
            solve.stats,
            solve.solver_stats,
            solve.assumption_usage,
            solve.assumption_conditioned,
            solve.summary_conditioned,
            solve.selected_route,
            compiled.clone(),
        )
    }));

    let (
        status,
        matched_paths,
        selected_path,
        verification,
        witness,
        stats,
        solver_stats,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        selected_route,
        compiled,
    ) = match solve_result {
        Ok(value) => value,
        Err(err) => return sym_panic_json("symbolic execution failed", err),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        status: solve_status_string(status),
        matched_paths,
        found: solve_found(status),
        target_reached_under_model: verification.target_reached_under_model,
        candidate_solution_verified: verification.candidate_solution_verified,
        residual_reasons: verification.residual_reasons.clone(),
        model_validation: model_validation_info(&verification.model_validation),
        witness: solve_witness_info(&witness),
        stats: build_sym_exec_summary(
            &stats,
            &solver_stats,
            matched_paths,
            assumption_usage,
            assumption_conditioned,
            summary_conditioned,
            Some(&compiled),
        ),
        target_query: Some(target_query_info(&selected_route)),
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

    let prepared = match build_symbolic_prepared(blocks.as_slice(), ctx_view.arch, None) {
        Some(prepared) => prepared,
        None => return sym_error_json("failed to build SSA function"),
    };
    let Some(scope) = build_single_function_scope(prepared.clone(), entry_addr, None) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let mut default_config = sym_default_query_config();

    let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let start_pc = spec.start_pc(entry_addr)?;
        let mut initial_state = r2sym::SymState::new(&z3_ctx, start_pc);
        r2sym::seed_default_state_for_arch(&mut initial_state, &prepared, ctx_view.arch);
        spec.apply_to_state(&mut initial_state);
        let query_policy =
            tune_query_config_for_state(&mut default_config, &prepared, &initial_state, None);

        let mut explorer = r2sym::PathExplorer::with_config(
            &z3_ctx,
            spec.to_explore_config(&default_config.explore),
        );
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            default_config.summary_profile,
            &query_policy,
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
        Err(err) => return sym_panic_json("symbolic execution failed", err),
    };

    let output = SymRunResult {
        entry: format!("0x{:x}", entry_addr),
        spec,
        stats: build_sym_exec_summary(
            &stats,
            &solver_stats,
            found_paths.len(),
            r2ssa::AssumptionUsageReport::default(),
            false,
            false,
            None,
        ),
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
    external_context_json: *const c_char,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return ptr::null_mut();
    };
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return ptr::null_mut();
    };
    let (assumption_usage, assumption_conditioned) = prepared_assumption_conditioning(prepared);
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let mut query_config = sym_paths_query_config(prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_semantic_artifact_with_scope(
            &z3_ctx,
            prepared,
            Some(&scope),
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        if should_skip_expensive_symbolic_summary(&compiled, prepared) {
            return (empty_symbolic_summary(), compiled);
        }
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_scope_state_for_arch(&mut initial_state, prepared, &scope, ctx_view.arch);
        let query_policy =
            tune_query_config_for_state(&mut query_config, prepared, &initial_state, None);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        (
            explorer.summarize_function(prepared, initial_state),
            compiled,
        )
    }));

    let (summary, compiled) = match explore_result {
        Ok(r) => r,
        Err(err) => {
            return sym_panic_json("symbolic execution failed", err);
        }
    };

    let output = build_sym_exec_summary(
        &summary.stats,
        &summary.solver_stats,
        summary.feasible_paths,
        assumption_usage,
        assumption_conditioned,
        false,
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
    external_context_json: *const c_char,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
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
    external_context_json: *const c_char,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return ptr::null_mut();
    };
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return ptr::null_mut();
    };
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let mut query_config = sym_paths_query_config(prepared);

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_scope_state_for_arch(&mut initial_state, prepared, &scope, ctx_view.arch);
        let query_policy =
            tune_query_config_for_state(&mut query_config, prepared, &initial_state, None);
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let summary = explorer.summarize_function(prepared, initial_state);
        (summary, explorer)
    }));

    let (summary, explorer) = match explore_result {
        Ok(r) => r,
        Err(err) => {
            return sym_panic_json("symbolic execution failed", err);
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
    external_context_json: *const c_char,
) -> *mut c_char {
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let mut query_config = sym_default_query_config();

    let z3_ctx = Context::thread_local();
    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            &z3_ctx,
            prepared,
            Some(&scope),
            target_addr,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_scope_state_for_arch(&mut initial_state, prepared, &scope, ctx_view.arch);
        let selected_route = predicted_target_query_route(PredictedTargetQueryRouteInput {
            z3_ctx: &z3_ctx,
            prepared,
            scope: Some(&scope),
            compiled: &compiled,
            target_addr,
            arch: ctx_view.arch,
            symbol_map: &symbol_map,
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(prepared),
        });
        let query_policy = tune_query_config_for_state(
            &mut query_config,
            prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let reach = explorer.can_reach_with_artifact_in_scope(
            prepared,
            Some(&scope),
            Some(&compiled),
            initial_state,
            target_addr,
        );
        let paths: Vec<PathInfo> = reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (
            paths,
            reach.stats,
            reach.solver_stats,
            reach.assumption_usage,
            reach.assumption_conditioned,
            reach.summary_conditioned,
            reach.selected_route,
            compiled.clone(),
        )
    }));

    let (
        paths,
        stats,
        solver_stats,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        selected_route,
        compiled,
    ) = match explore_result {
        Ok(value) => value,
        Err(err) => return sym_panic_json("symbolic execution failed", err),
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: build_sym_exec_summary(
            &stats,
            &solver_stats,
            paths.len(),
            assumption_usage,
            assumption_conditioned,
            summary_conditioned,
            Some(&compiled),
        ),
        target_query: Some(target_query_info(&selected_route)),
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
    external_context_json: *const c_char,
) -> *mut c_char {
    solve_pipeline_debug_stage("solve_to_scope:start");
    let Some(ctx_view) = require_ctx_view(ctx) else {
        return sym_error_json("missing disassembler context");
    };
    solve_pipeline_debug_stage("solve_to_scope:ctx_ready");
    let Some(scope) = (unsafe {
        build_symbolic_scope_from_ffi(functions, num_functions, ctx_view.arch, entry_addr)
    }) else {
        return sym_error_json("failed to build symbolic scope");
    };
    solve_pipeline_debug_log(&format!(
        "solve_to_scope:scope_ready functions={}",
        scope.functions().len()
    ));
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    solve_pipeline_debug_stage("solve_to_scope:assumptions_ready");
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    solve_pipeline_debug_log(&format!(
        "solve_to_scope:prepared_ready blocks={} call_sites={}",
        prepared.blocks().count(),
        prepared.call_sites().by_id.len()
    ));
    let symbol_map = symbol_map_snapshot();
    let mut query_config = sym_default_query_config();
    let z3_ctx = Context::thread_local();
    solve_pipeline_debug_log(&format!(
        "solve_to_scope:compile_begin target={:#x}",
        target_addr
    ));

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            &z3_ctx,
            prepared,
            Some(&scope),
            target_addr,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        solve_pipeline_debug_log(&format!(
            "solve_to_scope:compile_done stage={:?} route={:?}",
            compiled.stage,
            compiled.target_query_route_plan(target_addr)
        ));
        let mut initial_state = r2sym::SymState::new(&z3_ctx, entry_addr);
        r2sym::seed_scope_state_for_arch(&mut initial_state, prepared, &scope, ctx_view.arch);
        solve_pipeline_debug_stage("solve_to_scope:seed_ready");
        let selected_route = predicted_target_query_route(PredictedTargetQueryRouteInput {
            z3_ctx: &z3_ctx,
            prepared,
            scope: Some(&scope),
            compiled: &compiled,
            target_addr,
            arch: ctx_view.arch,
            symbol_map: &symbol_map,
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(prepared),
        });
        let query_policy = tune_query_config_for_state(
            &mut query_config,
            prepared,
            &initial_state,
            Some(&selected_route),
        );
        solve_pipeline_debug_log(&format!(
            "solve_to_scope:query_config max_states={} max_depth={} timeout_ms={}",
            query_config.explore.max_states,
            query_config.explore.max_depth,
            query_config
                .explore
                .timeout
                .map(|timeout| timeout.as_millis())
                .unwrap_or(0)
        ));
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        solve_pipeline_debug_stage("solve_to_scope:hooks_ready");
        let solve = explorer.solve_for_target_with_artifact_in_scope(
            prepared,
            Some(&scope),
            Some(&compiled),
            initial_state,
            target_addr,
        );
        solve_pipeline_debug_log(&format!(
            "solve_to_scope:solve_done status={:?} matched={} explored={} route={:?}",
            solve.status,
            solve.matched_paths.len(),
            solve.stats.states_explored,
            solve.selected_route
        ));
        let selected = solve
            .selected_path_index
            .and_then(|idx| solve.matched_paths.get(idx).map(|path| (idx, path)))
            .map(|(idx, path)| {
                path_info_from_result_with_solution(idx, path, &explorer, solve_found(solve.status))
            });
        (
            solve.status,
            solve.matched_paths.len(),
            selected,
            solve.verification,
            solve.witness,
            solve.stats,
            solve.solver_stats,
            solve.assumption_usage,
            solve.assumption_conditioned,
            solve.summary_conditioned,
            solve.selected_route,
            compiled.clone(),
        )
    }));

    let (
        status,
        matched_paths,
        selected_path,
        verification,
        witness,
        stats,
        solver_stats,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        selected_route,
        compiled,
    ) = match solve_result {
        Ok(value) => value,
        Err(err) => return sym_panic_json("symbolic execution failed", err),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", entry_addr),
        target: format!("0x{:x}", target_addr),
        status: solve_status_string(status),
        matched_paths,
        found: solve_found(status),
        target_reached_under_model: verification.target_reached_under_model,
        candidate_solution_verified: verification.candidate_solution_verified,
        residual_reasons: verification.residual_reasons.clone(),
        model_validation: model_validation_info(&verification.model_validation),
        witness: solve_witness_info(&witness),
        stats: build_sym_exec_summary(
            &stats,
            &solver_stats,
            matched_paths,
            assumption_usage,
            assumption_conditioned,
            summary_conditioned,
            Some(&compiled),
        ),
        target_query: Some(target_query_info(&selected_route)),
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
    external_context_json: *const c_char,
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
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let (assumption_usage, assumption_conditioned) = prepared_assumption_conditioning(prepared);
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();
    let mut default_config = sym_default_query_config();

    let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let start_pc = spec.start_pc(entry_addr)?;
        let mut initial_state = r2sym::SymState::new(&z3_ctx, start_pc);
        r2sym::seed_scope_state_for_arch(&mut initial_state, prepared, &scope, ctx_view.arch);
        spec.apply_to_state(&mut initial_state);
        let query_policy =
            tune_query_config_for_state(&mut default_config, prepared, &initial_state, None);

        let mut explorer = r2sym::PathExplorer::with_config(
            &z3_ctx,
            spec.to_explore_config(&default_config.explore),
        );
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            default_config.summary_profile,
            &query_policy,
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
        Err(err) => return sym_panic_json("symbolic execution failed", err),
    };

    let output = SymRunResult {
        entry: format!("0x{:x}", entry_addr),
        spec,
        stats: build_sym_exec_summary(
            &stats,
            &solver_stats,
            found_paths.len(),
            assumption_usage,
            assumption_conditioned,
            false,
            None,
        ),
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
    external_context_json: *const c_char,
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
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let mut query_config = sym_default_query_config();
    let start_pc = replay_seed.entry_pc.unwrap_or(entry_addr);
    let z3_ctx = Context::thread_local();

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            &z3_ctx,
            prepared,
            Some(&scope),
            target_addr,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
        );
        let initial_state =
            build_replay_seeded_state(&z3_ctx, entry_addr, prepared, ctx_view.arch, &replay_seed);
        let selected_route = predicted_target_query_route(PredictedTargetQueryRouteInput {
            z3_ctx: &z3_ctx,
            prepared,
            scope: Some(&scope),
            compiled: &compiled,
            target_addr,
            arch: ctx_view.arch,
            symbol_map: &symbol_map,
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(prepared),
        });
        let query_policy = tune_query_config_for_state(
            &mut query_config,
            prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let reach = explorer.can_reach_with_artifact_in_scope(
            prepared,
            Some(&scope),
            Some(&compiled),
            initial_state,
            target_addr,
        );
        let paths: Vec<PathInfo> = reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &explorer))
            .collect();
        (
            paths,
            reach.stats,
            reach.solver_stats,
            reach.assumption_usage,
            reach.assumption_conditioned,
            reach.summary_conditioned,
            reach.selected_route,
            compiled.clone(),
        )
    }));

    let (
        paths,
        stats,
        solver_stats,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        selected_route,
        compiled,
    ) = match explore_result {
        Ok(value) => value,
        Err(err) => {
            return sym_panic_json("symbolic replay exploration failed", err);
        }
    };
    let output = SymTargetExploreResult {
        entry: format!("0x{:x}", start_pc),
        target: format!("0x{:x}", target_addr),
        matched_paths: paths.len(),
        stats: build_sym_exec_summary_with_semantic_info(
            &stats,
            &solver_stats,
            paths.len(),
            assumption_usage,
            assumption_conditioned,
            summary_conditioned,
            Some(compiled_semantic_info_with_replay_seed(
                &compiled,
                &replay_seed,
            )),
        ),
        target_query: Some(target_query_info(&selected_route)),
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
    external_context_json: *const c_char,
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
    let scope = match scope_with_external_assumptions(&scope, ctx_view.arch, external_context_json)
    {
        Ok(scope) => scope,
        Err(err) => return sym_error_json(err),
    };
    let Some(prepared) = scope_root_prepared(&scope) else {
        return sym_error_json("failed to build root SSA function");
    };
    let symbol_map = symbol_map_snapshot();
    let mut query_config = sym_default_query_config();
    let start_pc = replay_seed.entry_pc.unwrap_or(entry_addr);
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let compiled = r2sym::compile_query_semantic_artifact_with_scope_and_replay_seed(
            &z3_ctx,
            prepared,
            Some(&scope),
            target_addr,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            Some(&replay_seed),
        );
        let initial_state =
            build_replay_seeded_state(&z3_ctx, entry_addr, prepared, ctx_view.arch, &replay_seed);
        let selected_route = predicted_target_query_route(PredictedTargetQueryRouteInput {
            z3_ctx: &z3_ctx,
            prepared,
            scope: Some(&scope),
            compiled: &compiled,
            target_addr,
            arch: ctx_view.arch,
            symbol_map: &symbol_map,
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(prepared),
        });
        let query_policy = tune_query_config_for_state(
            &mut query_config,
            prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(&z3_ctx);
        r2sym::install_symbolic_hooks_for_query_policy(
            &mut explorer,
            &z3_ctx,
            &scope,
            ctx_view.arch,
            &symbol_map,
            query_config.summary_profile,
            &query_policy,
        );
        let solve = explorer.solve_for_target_with_artifact_in_scope(
            prepared,
            Some(&scope),
            Some(&compiled),
            initial_state,
            target_addr,
        );
        let selected = solve
            .selected_path_index
            .and_then(|idx| solve.matched_paths.get(idx).map(|path| (idx, path)))
            .map(|(idx, path)| {
                path_info_from_result_with_solution(idx, path, &explorer, solve_found(solve.status))
            });
        (
            solve.status,
            solve.matched_paths.len(),
            selected,
            solve.verification,
            solve.witness,
            solve.stats,
            solve.solver_stats,
            solve.assumption_usage,
            solve.assumption_conditioned,
            solve.summary_conditioned,
            solve.selected_route,
            compiled.clone(),
        )
    }));

    let (
        status,
        matched_paths,
        selected_path,
        verification,
        witness,
        stats,
        solver_stats,
        assumption_usage,
        assumption_conditioned,
        summary_conditioned,
        selected_route,
        compiled,
    ) = match solve_result {
        Ok(value) => value,
        Err(err) => return sym_panic_json("symbolic replay solve failed", err),
    };
    let output = SymTargetSolveResult {
        entry: format!("0x{:x}", start_pc),
        target: format!("0x{:x}", target_addr),
        status: solve_status_string(status),
        matched_paths,
        found: solve_found(status),
        target_reached_under_model: verification.target_reached_under_model,
        candidate_solution_verified: verification.candidate_solution_verified,
        residual_reasons: verification.residual_reasons.clone(),
        model_validation: model_validation_info(&verification.model_validation),
        witness: solve_witness_info(&witness),
        stats: build_sym_exec_summary_with_semantic_info(
            &stats,
            &solver_stats,
            matched_paths,
            assumption_usage,
            assumption_conditioned,
            summary_conditioned,
            Some(compiled_semantic_info_with_replay_seed(
                &compiled,
                &replay_seed,
            )),
        ),
        target_query: Some(target_query_info(&selected_route)),
        selected_path,
    };

    match serde_json::to_string(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => sym_error_json("failed to serialize replay symbolic solve output"),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        build_sym_exec_summary, is_public_solution_register, is_public_solution_symbol,
        parse_scope_assumptions,
    };
    use std::ffi::CString;

    #[test]
    fn parse_scope_assumptions_reads_external_context_payload() {
        let json = CString::new(
            r#"{"assumptions":[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}}}]}"#,
        )
        .expect("json");
        let assumptions = parse_scope_assumptions(json.as_ptr(), None).expect("assumptions");
        assert_eq!(assumptions.items.len(), 1);
    }

    #[test]
    fn parse_scope_assumptions_reads_direct_assumption_array() {
        let json = CString::new(
            r#"[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}}}]"#,
        )
        .expect("json");
        let assumptions = parse_scope_assumptions(json.as_ptr(), None).expect("assumptions");
        assert_eq!(assumptions.items.len(), 1);
    }

    #[test]
    fn public_solution_filter_hides_temps_and_flags_but_keeps_abi_inputs() {
        for hidden in [
            "tmp:1234", "TMPZR", "TMPNG", "CY", "OV", "const:4", "ram:1000",
        ] {
            assert!(
                !is_public_solution_symbol(hidden),
                "{hidden} should not be public solution input"
            );
        }
        for visible in ["sym_input", "RDI_0", "x0_0", "arg1"] {
            assert!(
                is_public_solution_symbol(visible),
                "{visible} should stay visible as a public solution input"
            );
        }
        assert!(!is_public_solution_register("RDI_0"));
        assert!(is_public_solution_register("RDI_1"));
        for hidden in ["SP_1", "FP_1", "X29_1", "X30_1", "LR_1", "PC_1"] {
            assert!(
                !is_public_solution_register(hidden),
                "{hidden} should not be a public ARM64 solution register"
            );
        }
        assert!(is_public_solution_register("X0_1"));
    }

    #[test]
    fn sym_exec_summary_serializes_assumption_usage_when_present() {
        let summary = build_sym_exec_summary(
            &r2sym::path::ExploreStats::default(),
            &r2sym::SolverStats::default(),
            0,
            r2ssa::AssumptionUsageReport {
                applied: vec![r2ssa::AnalysisAssumption {
                    id: Some("arg0".to_string()),
                    subject: r2ssa::AssumptionSubject::Parameter { index: 0 },
                    value: r2ssa::AssumptionValue::Constant { value: 7 },
                    scope: r2ssa::AssumptionScope::Query,
                    provenance: r2ssa::AssumptionProvenance::User,
                }],
                ..r2ssa::AssumptionUsageReport::default()
            },
            true,
            false,
            None,
        );
        let json = serde_json::to_value(summary).expect("summary json");
        assert!(json.get("assumption_usage").is_some());
        assert_eq!(
            json.get("assumption_conditioned")
                .and_then(serde_json::Value::as_bool),
            Some(true)
        );
        assert_eq!(json.get("summary_conditioned"), None);
    }

    #[test]
    fn sym_exec_summary_serializes_summary_conditioning_when_present() {
        let summary = build_sym_exec_summary(
            &r2sym::path::ExploreStats::default(),
            &r2sym::SolverStats::default(),
            0,
            r2ssa::AssumptionUsageReport::default(),
            false,
            true,
            None,
        );
        let json = serde_json::to_value(summary).expect("summary json");
        assert_eq!(
            json.get("summary_conditioned")
                .and_then(serde_json::Value::as_bool),
            Some(true)
        );
    }
}
