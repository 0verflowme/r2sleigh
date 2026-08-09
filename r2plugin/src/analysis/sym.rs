use crate::blocks::BlockSlice;
use crate::context::require_ctx_view;
use crate::helpers::effective_ptr_bits;
use crate::{ArchSpec, R2ILBlock, R2ILContext};
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
use z3::Context;

static MERGE_STATES: AtomicBool = AtomicBool::new(false);

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

#[repr(C)]
pub struct R2ILFunctionBlocks {
    pub(crate) entry_addr: u64,
    pub(crate) name: *const c_char,
    pub(crate) blocks: *const *const R2ILBlock,
    pub(crate) num_blocks: usize,
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

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_merge_is_enabled() -> i32 {
    if merge_states_enabled() { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sym_merge_set_enabled(enabled: i32) {
    MERGE_STATES.store(enabled != 0, Ordering::Relaxed);
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

fn parse_sym_symbol_map_payload(json_str: &str) -> HashMap<u64, String> {
    serde_json::from_str::<HashMap<String, String>>(json_str)
        .ok()
        .map(|map| {
            map.into_iter()
                .filter_map(|(key, value)| {
                    let addr = key
                        .strip_prefix("0x")
                        .or_else(|| key.strip_prefix("0X"))
                        .and_then(|hex| u64::from_str_radix(hex, 16).ok())
                        .or_else(|| key.parse().ok());
                    addr.map(|addr| (addr, value))
                })
                .collect()
        })
        .unwrap_or_default()
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
    let parsed = parse_sym_symbol_map_payload(json_str);
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
    semantic: Option<r2sym::CompiledSemanticInfo>,
}

fn is_zero(value: &usize) -> bool {
    *value == 0
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
        semantic.map(r2sym::compiled_semantic_info),
    )
}

fn build_sym_exec_summary_with_semantic_info(
    stats: &r2sym::path::ExploreStats,
    solver_stats: &r2sym::SolverStats,
    paths_feasible: usize,
    assumption_usage: r2ssa::AssumptionUsageReport,
    assumption_conditioned: bool,
    summary_conditioned: bool,
    semantic: Option<r2sym::CompiledSemanticInfo>,
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

fn path_solution_from_result<'ctx>(
    explorer: &r2sym::PathExplorer<'ctx>,
    result: &r2sym::PathResult<'ctx>,
) -> Option<PathSolution> {
    if !result.feasible {
        return None;
    }
    explorer.solve_path(result).map(|solved| {
        let public = solved.public_solution();
        PathSolution {
            inputs: public
                .inputs
                .into_iter()
                .map(|(k, v)| (k, format!("0x{:x}", v)))
                .collect(),
            registers: public
                .registers
                .into_iter()
                .map(|(k, v)| (k, format!("0x{:x}", v)))
                .collect(),
        }
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
    explorer.solve_path(result).map(|solved| {
        let public = solved.public_solution();
        RunPathSolution {
            inputs: public
                .inputs
                .into_iter()
                .map(|(k, v)| (k, format!("0x{:x}", v)))
                .collect(),
            input_buffers: public
                .input_buffers
                .into_iter()
                .map(|(k, v)| (k, buffer_solution(v)))
                .collect(),
            registers: public
                .registers
                .into_iter()
                .map(|(k, v)| (k, format!("0x{:x}", v)))
                .collect(),
        }
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
    let prepared = r2ssa::SsaArtifact::for_symbolic(blocks, arch)?;
    Some(match name {
        Some(name) if !name.is_empty() => prepared.with_name(name.to_string()),
        _ => prepared,
    })
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

fn engine_symbolic_context<'ctx, 'a>(
    z3_ctx: &'ctx Context,
    prepared: &'a r2ssa::SsaArtifact,
    scope: Option<&'a r2sym::PreparedFunctionScope>,
    arch: Option<&'a ArchSpec>,
    symbol_map: &'a HashMap<u64, String>,
    config_profile: r2engine::EngineSymbolicConfigProfile,
    seed: r2engine::EngineSymbolicStateSeed<'a>,
) -> r2engine::EngineSymbolicContextRequest<'ctx, 'a> {
    r2engine::EngineSymbolicContextRequest {
        z3_ctx,
        prepared,
        scope,
        arch,
        symbol_map,
        merge_states: merge_states_enabled(),
        config_profile,
        seed,
    }
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
    let ptr_bits = arch.map(effective_ptr_bits).unwrap_or(64);
    r2types::parse_external_assumption_payload_json(text, ptr_bits).map_err(|err| err.message())
}

fn scope_with_external_assumptions(
    scope: &r2sym::PreparedFunctionScope,
    arch: Option<&ArchSpec>,
    external_context_json: *const c_char,
) -> Result<r2sym::PreparedFunctionScope, &'static str> {
    let assumptions = parse_scope_assumptions(external_context_json, arch)?;
    r2engine::condition_symbolic_scope_with_assumptions(scope, &assumptions)
        .map(|conditioned| conditioned.scope)
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
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::types::engine_session().symbolic_summary(r2engine::EngineSymbolicSummaryRequest {
            context: engine_symbolic_context(
                &z3_ctx,
                prepared,
                Some(&scope),
                ctx_view.arch,
                &symbol_map,
                r2engine::EngineSymbolicConfigProfile::PathListing,
                r2engine::EngineSymbolicStateSeed::Scope { entry_addr },
            ),
            compile_semantics: true,
        })
    }));

    let response = match explore_result {
        Ok(r) => r,
        Err(err) => {
            return sym_panic_json("symbolic execution failed", err);
        }
    };

    let output = build_sym_exec_summary(
        &response.summary.stats,
        &response.summary.solver_stats,
        response.summary.feasible_paths,
        response.assumption_usage,
        response.assumption_conditioned,
        false,
        response.compiled.as_ref(),
    );
    match serde_json::to_string_pretty(&output) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
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

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::types::engine_session().symbolic_paths(r2engine::EngineSymbolicPathsRequest {
            context: engine_symbolic_context(
                &z3_ctx,
                prepared,
                Some(&scope),
                ctx_view.arch,
                &symbol_map,
                r2engine::EngineSymbolicConfigProfile::PathListing,
                r2engine::EngineSymbolicStateSeed::Scope { entry_addr },
            ),
        })
    }));

    let response = match explore_result {
        Ok(r) => r,
        Err(err) => {
            return sym_panic_json("symbolic execution failed", err);
        }
    };

    let paths: Vec<PathInfo> = response
        .summary
        .paths
        .iter()
        .enumerate()
        .map(|(i, r)| {
            path_info_from_result_with_solution(
                i,
                r,
                &response.explorer,
                i < response.solution_limit,
            )
        })
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

    let z3_ctx = Context::thread_local();
    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let response = crate::types::engine_session().symbolic_target_explore(
            r2engine::EngineTargetExploreRequest {
                context: engine_symbolic_context(
                    &z3_ctx,
                    prepared,
                    Some(&scope),
                    ctx_view.arch,
                    &symbol_map,
                    r2engine::EngineSymbolicConfigProfile::DefaultQuery,
                    r2engine::EngineSymbolicStateSeed::Scope { entry_addr },
                ),
                target_addr,
            },
        );
        let paths: Vec<PathInfo> = response
            .reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &response.explorer))
            .collect();
        (
            paths,
            response.reach.stats,
            response.reach.solver_stats,
            response.reach.assumption_usage,
            response.reach.assumption_conditioned,
            response.reach.summary_conditioned,
            response.selected_route,
            response.compiled,
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
    let z3_ctx = Context::thread_local();
    solve_pipeline_debug_log(&format!(
        "solve_to_scope:compile_begin target={:#x}",
        target_addr
    ));

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let response = crate::types::engine_session().symbolic_target_solve(
            r2engine::EngineTargetSolveRequest {
                context: engine_symbolic_context(
                    &z3_ctx,
                    prepared,
                    Some(&scope),
                    ctx_view.arch,
                    &symbol_map,
                    r2engine::EngineSymbolicConfigProfile::DefaultQuery,
                    r2engine::EngineSymbolicStateSeed::Scope { entry_addr },
                ),
                target_addr,
            },
        );
        solve_pipeline_debug_log(&format!(
            "solve_to_scope:compile_done stage={:?} route={:?}",
            response.compiled.stage,
            response.compiled.target_query_route_plan(target_addr)
        ));
        solve_pipeline_debug_stage("solve_to_scope:seed_ready");
        solve_pipeline_debug_log(&format!(
            "solve_to_scope:query_config max_states={} max_depth={} timeout_ms={}",
            response.query_policy.max_states,
            response.query_policy.max_depth,
            response
                .query_policy
                .timeout
                .map(|timeout| timeout.as_millis())
                .unwrap_or(0)
        ));
        solve_pipeline_debug_stage("solve_to_scope:hooks_ready");
        solve_pipeline_debug_log(&format!(
            "solve_to_scope:solve_done status={:?} matched={} explored={} route={:?}",
            response.solve.status,
            response.solve.matched_paths.len(),
            response.solve.stats.states_explored,
            response.solve.selected_route
        ));
        let selected = response
            .solve
            .selected_path_index
            .and_then(|idx| {
                response
                    .solve
                    .matched_paths
                    .get(idx)
                    .map(|path| (idx, path))
            })
            .map(|(idx, path)| {
                path_info_from_result_with_solution(
                    idx,
                    path,
                    &response.explorer,
                    solve_found(response.solve.status),
                )
            });
        (
            response.solve.status,
            response.solve.matched_paths.len(),
            selected,
            response.solve.verification,
            response.solve.witness,
            response.solve.stats,
            response.solve.solver_stats,
            response.solve.assumption_usage,
            response.solve.assumption_conditioned,
            response.solve.summary_conditioned,
            response.selected_route,
            response.compiled,
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
    let symbol_map = symbol_map_snapshot();
    let z3_ctx = Context::thread_local();

    let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let response =
            crate::types::engine_session().symbolic_run_spec(r2engine::EngineRunSpecRequest {
                context: engine_symbolic_context(
                    &z3_ctx,
                    prepared,
                    Some(&scope),
                    ctx_view.arch,
                    &symbol_map,
                    r2engine::EngineSymbolicConfigProfile::DefaultQuery,
                    r2engine::EngineSymbolicStateSeed::Scope { entry_addr },
                ),
                spec: &spec,
            })?;
        let found_paths = response
            .result
            .found_paths
            .iter()
            .enumerate()
            .map(|(idx, path)| run_path_info_from_result(idx, path, &response.explorer))
            .collect::<Vec<_>>();
        Ok::<_, String>((
            response.result,
            response.stats,
            response.solver_stats,
            response.assumption_usage,
            response.assumption_conditioned,
            found_paths,
        ))
    }));

    let (result, stats, solver_stats, assumption_usage, assumption_conditioned, found_paths) =
        match run_result {
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
    let start_pc = replay_seed.entry_pc.unwrap_or(entry_addr);
    let z3_ctx = Context::thread_local();

    let explore_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let response = crate::types::engine_session().symbolic_target_explore(
            r2engine::EngineTargetExploreRequest {
                context: engine_symbolic_context(
                    &z3_ctx,
                    prepared,
                    Some(&scope),
                    ctx_view.arch,
                    &symbol_map,
                    r2engine::EngineSymbolicConfigProfile::DefaultQuery,
                    r2engine::EngineSymbolicStateSeed::Replay {
                        entry_addr,
                        seed: &replay_seed,
                    },
                ),
                target_addr,
            },
        );
        let paths: Vec<PathInfo> = response
            .reach
            .paths
            .iter()
            .enumerate()
            .map(|(i, r)| path_info_from_result(i, r, &response.explorer))
            .collect();
        (
            paths,
            response.reach.stats,
            response.reach.solver_stats,
            response.reach.assumption_usage,
            response.reach.assumption_conditioned,
            response.reach.summary_conditioned,
            response.selected_route,
            response.compiled,
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
            Some(r2sym::compiled_semantic_info_with_replay_seed(
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
    let start_pc = replay_seed.entry_pc.unwrap_or(entry_addr);
    let z3_ctx = Context::thread_local();

    let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let response = crate::types::engine_session().symbolic_target_solve(
            r2engine::EngineTargetSolveRequest {
                context: engine_symbolic_context(
                    &z3_ctx,
                    prepared,
                    Some(&scope),
                    ctx_view.arch,
                    &symbol_map,
                    r2engine::EngineSymbolicConfigProfile::DefaultQuery,
                    r2engine::EngineSymbolicStateSeed::Replay {
                        entry_addr,
                        seed: &replay_seed,
                    },
                ),
                target_addr,
            },
        );
        let selected = response
            .solve
            .selected_path_index
            .and_then(|idx| {
                response
                    .solve
                    .matched_paths
                    .get(idx)
                    .map(|path| (idx, path))
            })
            .map(|(idx, path)| {
                path_info_from_result_with_solution(
                    idx,
                    path,
                    &response.explorer,
                    solve_found(response.solve.status),
                )
            });
        (
            response.solve.status,
            response.solve.matched_paths.len(),
            selected,
            response.solve.verification,
            response.solve.witness,
            response.solve.stats,
            response.solve.solver_stats,
            response.solve.assumption_usage,
            response.solve.assumption_conditioned,
            response.solve.summary_conditioned,
            response.selected_route,
            response.compiled,
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
            Some(r2sym::compiled_semantic_info_with_replay_seed(
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
    use super::{build_sym_exec_summary, parse_scope_assumptions};
    use std::ffi::CString;

    #[test]
    fn parse_scope_assumptions_forwards_payload_to_typed_parser() {
        let json = CString::new(
            r#"{"assumptions":[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}}}]}"#,
        )
        .expect("json");
        let assumptions = parse_scope_assumptions(json.as_ptr(), None).expect("assumptions");

        assert_eq!(assumptions.items.len(), 1);
        assert_eq!(
            assumptions.items[0].subject,
            r2ssa::AssumptionSubject::Register {
                name: "rdi".to_string()
            }
        );
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
