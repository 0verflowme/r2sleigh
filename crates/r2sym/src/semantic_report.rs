use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

fn is_zero(value: &usize) -> bool {
    *value == 0
}

#[derive(Debug, Serialize, Clone)]
pub struct CompiledSemanticInfo {
    pub schema_version: u32,
    pub stage: String,
    pub granularity: String,
    pub execution: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seed_mode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replay_seed_fingerprint: Option<String>,
    pub query_plan: crate::QueryPlan,
    pub type_plan: crate::TypePlan,
    pub decompile_plan: crate::DecompilePlan,
    pub slice_class: String,
    pub residual_reasons: Vec<String>,
    pub ambiguous_target_count: usize,
    pub ambiguous_targets: Vec<String>,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub summary_attempted: usize,
    pub summary_budget_exhausted: usize,
    pub summary_scc_count: usize,
    pub region_count: usize,
    pub control_region_count: usize,
    pub memory_region_count: usize,
    pub memory_fact_count: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    pub native_region_summary_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub native_region_summary_kinds: Vec<String>,
    #[serde(default, skip_serializing_if = "is_zero")]
    pub native_worker_summary_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub native_worker_summary_kinds: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_summaries: Vec<MemorySummaryInfo>,
    pub compiled_condition_count: usize,
    pub exact_compiled_condition_count: usize,
    pub actionable_compiled_condition_count: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_large_cfg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interpreter_diagnostic: Option<InterpreterDispatchInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<InterpreterDispatchInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vm_step: Option<VmStepSummaryInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vm_transfer: Option<VmStepSummaryInfo>,
    pub cache_hit: bool,
}

#[derive(Debug, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemorySummaryInfo {
    pub anchor: String,
    pub region: String,
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub size: u32,
    pub exact_offset: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub address_terms: Vec<r2ssa::AffineAddressTerm>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
    pub expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value_expr: Option<String>,
}

#[derive(Debug, Serialize, Clone)]
pub struct InterpreterDispatchInfo {
    pub kind: String,
    pub dispatch_header: String,
    pub dispatch_targets: usize,
    pub selector: Option<String>,
    pub back_edges: usize,
    pub score: i32,
}

fn interpreter_dispatch_info_from_sym(
    interpreter: &crate::InterpreterDispatchSummary,
) -> InterpreterDispatchInfo {
    InterpreterDispatchInfo {
        kind: match interpreter.kind {
            crate::InterpreterKind::SwitchDispatch => "switch_dispatch".to_string(),
            crate::InterpreterKind::IndirectDispatch => "indirect_dispatch".to_string(),
        },
        dispatch_header: format!("0x{:x}", interpreter.dispatch_header),
        dispatch_targets: interpreter.dispatch_targets,
        selector: interpreter.selector.clone(),
        back_edges: interpreter.back_edges,
        score: interpreter.score,
    }
}

#[derive(Debug, Serialize, Clone)]
pub struct VmStateUpdateInfo {
    pub output: String,
    pub expr: String,
    pub value: String,
    pub exact: bool,
    pub confidence: String,
}

#[derive(Debug, Serialize, Clone)]
pub struct VmGuardConditionInfo {
    pub expr: String,
    pub value: String,
    pub expect_nonzero: bool,
    pub exact: bool,
    pub confidence: String,
}

#[derive(Debug, Serialize, Clone)]
pub struct VmGuardedExitInfo {
    pub target: String,
    pub guard: VmGuardConditionInfo,
}

#[derive(Debug, Serialize, Clone)]
pub struct VmMemoryConditionInfo {
    pub region: String,
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub size: u32,
    pub exact_offset: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub address_terms: Vec<r2ssa::AffineAddressTerm>,
    pub confidence: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
    pub expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value_expr: Option<String>,
    pub exact_value: bool,
}

#[derive(Debug, Serialize, Clone)]
pub struct VmTransferArmInfo {
    pub handler_target: String,
    pub case_values: Vec<u64>,
    pub region_blocks: Vec<String>,
    pub exit_targets: Vec<String>,
    pub exit_guards: Vec<VmGuardedExitInfo>,
    pub state_updates: Vec<VmStateUpdateInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector_update: Option<VmStateUpdateInfo>,
    pub memory_reads: Vec<VmMemoryConditionInfo>,
    pub memory_writes: Vec<VmMemoryConditionInfo>,
    pub residual_guards: bool,
    pub residual_memory_effects: bool,
    pub exact: bool,
    pub confidence: String,
    pub redispatch: bool,
    pub may_return: bool,
    pub truncated: bool,
}

#[derive(Debug, Serialize, Clone)]
pub struct VmStepSummaryInfo {
    pub kind: String,
    pub loop_header: String,
    pub dispatch_header: String,
    pub selector: Option<String>,
    pub dispatch_targets: Vec<String>,
    pub default_target: Option<String>,
    pub case_values_by_target: BTreeMap<String, Vec<u64>>,
    pub loop_latches: Vec<String>,
    pub state_inputs: Vec<String>,
    pub state_outputs: Vec<String>,
    pub step_blocks: Vec<String>,
    pub handler_regions: BTreeMap<String, Vec<String>>,
    pub handler_state_inputs: BTreeMap<String, Vec<String>>,
    pub handler_state_outputs: BTreeMap<String, Vec<String>>,
    pub handler_state_updates: BTreeMap<String, Vec<VmStateUpdateInfo>>,
    pub handler_exit_guards: BTreeMap<String, Vec<VmGuardedExitInfo>>,
    pub handler_memory_read_effects: BTreeMap<String, Vec<VmMemoryConditionInfo>>,
    pub handler_memory_write_effects: BTreeMap<String, Vec<VmMemoryConditionInfo>>,
    pub handler_memory_reads: BTreeMap<String, usize>,
    pub handler_memory_writes: BTreeMap<String, usize>,
    pub handler_calls: BTreeMap<String, usize>,
    pub handler_conditional_branches: BTreeMap<String, usize>,
    pub handler_exit_targets: BTreeMap<String, Vec<String>>,
    pub redispatch_handlers: Vec<String>,
    pub returning_handlers: Vec<String>,
    pub truncated_handlers: Vec<String>,
    pub transfers: Vec<VmTransferArmInfo>,
}

fn render_vm_value_expr(value: &crate::VmValueExpr) -> String {
    match value {
        crate::VmValueExpr::Const(value) => format!("0x{value:x}"),
        crate::VmValueExpr::Var(name) | crate::VmValueExpr::Expr(name) => name.clone(),
        crate::VmValueExpr::Unary { op, arg } => {
            let op = match op {
                crate::VmUnaryOp::Neg => "-",
                crate::VmUnaryOp::BitNot => "~",
                crate::VmUnaryOp::BoolNot => "!",
            };
            format!("({}{})", op, render_vm_value_expr(arg))
        }
        crate::VmValueExpr::Binary { op, lhs, rhs } => {
            let op = match op {
                crate::VmBinaryOp::Add => "+",
                crate::VmBinaryOp::Sub => "-",
                crate::VmBinaryOp::Mul => "*",
                crate::VmBinaryOp::Div => "/",
                crate::VmBinaryOp::Rem => "%",
                crate::VmBinaryOp::And => "&",
                crate::VmBinaryOp::Or => "|",
                crate::VmBinaryOp::Xor => "^",
                crate::VmBinaryOp::Shl => "<<",
                crate::VmBinaryOp::LShr | crate::VmBinaryOp::AShr => ">>",
                crate::VmBinaryOp::Eq => "==",
                crate::VmBinaryOp::Ne => "!=",
                crate::VmBinaryOp::Lt | crate::VmBinaryOp::SLt => "<",
                crate::VmBinaryOp::Le | crate::VmBinaryOp::SLe => "<=",
                crate::VmBinaryOp::BoolAnd => "&&",
                crate::VmBinaryOp::BoolOr => "||",
            };
            format!(
                "({} {} {})",
                render_vm_value_expr(lhs),
                op,
                render_vm_value_expr(rhs)
            )
        }
        crate::VmValueExpr::Select {
            cond,
            if_true,
            if_false,
        } => format!(
            "({} ? {} : {})",
            render_vm_value_expr(cond),
            render_vm_value_expr(if_true),
            render_vm_value_expr(if_false)
        ),
    }
}

fn render_semantic_confidence(confidence: crate::SemanticConfidence) -> String {
    match confidence {
        crate::SemanticConfidence::Exact => "exact",
        crate::SemanticConfidence::Likely => "likely",
        crate::SemanticConfidence::Heuristic => "heuristic",
        crate::SemanticConfidence::Residual => "residual",
    }
    .to_string()
}

fn vm_state_update_info_from_sym(update: &crate::VmStateUpdate) -> VmStateUpdateInfo {
    VmStateUpdateInfo {
        output: update.output.clone(),
        expr: update.expr.clone(),
        value: render_vm_value_expr(&update.value),
        exact: update.exact,
        confidence: render_semantic_confidence(update.confidence()),
    }
}

fn vm_guard_condition_info_from_sym(guard: &crate::VmGuardCondition) -> VmGuardConditionInfo {
    VmGuardConditionInfo {
        expr: guard.expr.clone(),
        value: render_vm_value_expr(&guard.value),
        expect_nonzero: guard.expect_nonzero,
        exact: guard.exact,
        confidence: render_semantic_confidence(guard.confidence()),
    }
}

fn vm_guarded_exit_info_from_sym(guarded: &crate::VmGuardedExit) -> VmGuardedExitInfo {
    VmGuardedExitInfo {
        target: format!("0x{:x}", guarded.target),
        guard: vm_guard_condition_info_from_sym(&guarded.guard),
    }
}

fn vm_memory_condition_info_from_sym(
    condition: &crate::VmMemoryCondition,
) -> VmMemoryConditionInfo {
    VmMemoryConditionInfo {
        region: format!(
            "{}:{}#{}",
            match condition.region.kind {
                crate::MemoryRegionKind::Stack => "stack",
                crate::MemoryRegionKind::Global => "global",
                crate::MemoryRegionKind::Input => "input",
                crate::MemoryRegionKind::Heap => "heap",
                crate::MemoryRegionKind::Replay => "replay",
                crate::MemoryRegionKind::EscapedUnknown => "unknown",
            },
            condition.region.name,
            condition.region.id
        ),
        offset_lo: condition.address.offset_lo(),
        offset_hi: condition.address.offset_hi(),
        size: condition.size,
        exact_offset: condition.address.is_exact_offset(),
        address_terms: condition.address.terms().to_vec(),
        confidence: render_semantic_confidence(condition.confidence()),
        binding: condition.binding.clone(),
        expr: condition.expr.clone(),
        value_expr: condition.value_expr.clone(),
        exact_value: condition.exact_value,
    }
}

fn vm_transfer_arm_info_from_sym(transfer: &crate::VmTransferArm) -> VmTransferArmInfo {
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

fn vm_step_summary_info_from_sym(vm_step: &crate::VmStepSummary) -> VmStepSummaryInfo {
    VmStepSummaryInfo {
        kind: match vm_step.kind {
            crate::InterpreterKind::SwitchDispatch => "switch_dispatch".to_string(),
            crate::InterpreterKind::IndirectDispatch => "indirect_dispatch".to_string(),
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

pub fn compiled_semantic_info(compiled: &crate::SemanticArtifact) -> CompiledSemanticInfo {
    compiled_semantic_info_with_seed(compiled, None)
}

fn memory_summary_region_label(region: &crate::BackwardMemoryRegion) -> String {
    match region {
        crate::BackwardMemoryRegion::Argument { index } => format!("arg{index}"),
        crate::BackwardMemoryRegion::Region(region) => format!("{:?}:{}", region.kind, region.name),
    }
}

fn native_worker_summary_kind_label(kind: crate::NativeWorkerSummaryKind) -> &'static str {
    match kind {
        crate::NativeWorkerSummaryKind::ProgramOrchestrator => "program_orchestrator",
        crate::NativeWorkerSummaryKind::MemoryTransfer => "memory_transfer",
        crate::NativeWorkerSummaryKind::FileTransfer => "file_transfer",
        crate::NativeWorkerSummaryKind::MemoryRead => "memory_read",
        crate::NativeWorkerSummaryKind::MemoryWrite => "memory_write",
        crate::NativeWorkerSummaryKind::MemoryEscape => "memory_escape",
        crate::NativeWorkerSummaryKind::MemoryFree => "memory_free",
        crate::NativeWorkerSummaryKind::StringScan => "string_scan",
        crate::NativeWorkerSummaryKind::HashFold => "hash_fold",
        crate::NativeWorkerSummaryKind::TableWalk => "table_walk",
        crate::NativeWorkerSummaryKind::PathWalk => "path_walk",
        crate::NativeWorkerSummaryKind::DirectoryTraversal => "directory_traversal",
        crate::NativeWorkerSummaryKind::RecordStream => "record_stream",
        crate::NativeWorkerSummaryKind::FieldSelection => "field_selection",
        crate::NativeWorkerSummaryKind::OutputStream => "output_stream",
        crate::NativeWorkerSummaryKind::FormatRender => "format_render",
        crate::NativeWorkerSummaryKind::MetadataProbe => "metadata_probe",
        crate::NativeWorkerSummaryKind::SortMerge => "sort_merge",
        crate::NativeWorkerSummaryKind::NumericTransform => "numeric_transform",
        crate::NativeWorkerSummaryKind::Parser => "parser",
        crate::NativeWorkerSummaryKind::DiagnosticWrapper => "diagnostic_wrapper",
        crate::NativeWorkerSummaryKind::FormatArgumentFetch => "format_argument_fetch",
        crate::NativeWorkerSummaryKind::Allocation => "allocation",
        crate::NativeWorkerSummaryKind::Lifetime => "lifetime",
        crate::NativeWorkerSummaryKind::Synchronization => "synchronization",
        crate::NativeWorkerSummaryKind::Atomic => "atomic",
        crate::NativeWorkerSummaryKind::Unknown => "unknown",
    }
}

fn native_worker_summary_kinds(native: Option<&crate::NativeArtifactBody>) -> Vec<String> {
    native
        .into_iter()
        .flat_map(|body| body.summary.worker_summaries.iter())
        .map(|summary| native_worker_summary_kind_label(summary.kind).to_string())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn native_region_summary_kinds(native: Option<&crate::NativeArtifactBody>) -> Vec<String> {
    native
        .into_iter()
        .flat_map(|body| body.summary.region_summaries.iter())
        .map(|summary| native_worker_summary_kind_label(summary.kind).to_string())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn semantic_memory_summaries(native: Option<&crate::NativeArtifactBody>) -> Vec<MemorySummaryInfo> {
    let mut summaries = native
        .into_iter()
        .flat_map(|body| body.regions.values())
        .flat_map(|region| {
            region.memory.iter().map(|fact| {
                let term = &fact.value.term;
                MemorySummaryInfo {
                    anchor: format!("0x{:x}", region.anchor),
                    region: memory_summary_region_label(&term.region),
                    offset_lo: term.address.offset_lo(),
                    offset_hi: term.address.offset_hi(),
                    size: term.size,
                    exact_offset: term.address.is_exact_offset(),
                    address_terms: term.address.terms().to_vec(),
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

pub fn compiled_semantic_info_with_replay_seed(
    compiled: &crate::SemanticArtifact,
    replay_seed: &crate::ReplaySeed,
) -> CompiledSemanticInfo {
    compiled_semantic_info_with_seed(
        compiled,
        Some(crate::stable_replay_seed_fingerprint(replay_seed)),
    )
}

fn compiled_semantic_info_with_seed(
    compiled: &crate::SemanticArtifact,
    replay_seed_fingerprint: Option<u64>,
) -> CompiledSemanticInfo {
    let native = compiled.native_body();
    let memory_summaries = semantic_memory_summaries(native);
    let native_worker_summary_kinds = native_worker_summary_kinds(native);
    let native_region_summary_kinds = native_region_summary_kinds(native);
    let memory_fact_count = memory_summaries.len();
    CompiledSemanticInfo {
        schema_version: crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
        stage: match compiled.stage {
            crate::RefinementStage::Raw => "raw",
            crate::RefinementStage::Compiled => "compiled",
            crate::RefinementStage::Residual => "residual",
        }
        .to_string(),
        granularity: match compiled.granularity {
            crate::ArtifactGranularity::WholeFunction => "whole_function",
            crate::ArtifactGranularity::Regioned => "regioned",
            crate::ArtifactGranularity::SummaryOnly => "summary_only",
        }
        .to_string(),
        execution: match compiled.execution {
            crate::ExecutionModel::Native => "native",
            crate::ExecutionModel::Vm => "vm",
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
                crate::SliceClass::Wrapper => "wrapper",
                crate::SliceClass::Worker => "worker",
                crate::SliceClass::RecursiveGroup => "recursive_group",
                crate::SliceClass::InterpreterSwitch => "interpreter_switch",
                crate::SliceClass::InterpreterIndirect => "interpreter_indirect",
                crate::SliceClass::GenericLarge => "generic_large",
            })
            .unwrap_or("worker")
            .to_string(),
        residual_reasons: compiled
            .diagnostics
            .residual_reasons
            .iter()
            .map(|reason| {
                match reason {
                    crate::ResidualReason::MissingArch => "missing_arch",
                    crate::ResidualReason::LargeCfg => "large_cfg",
                    crate::ResidualReason::SummaryBudgetExhausted => "summary_budget_exhausted",
                    crate::ResidualReason::SccBudgetExhausted => "scc_budget_exhausted",
                    crate::ResidualReason::InterpreterRequiresStepSummary => {
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
        native_region_summary_count: native
            .map(|body| body.summary.region_summaries.len())
            .unwrap_or(0),
        native_region_summary_kinds,
        native_worker_summary_count: native
            .map(|body| body.summary.worker_summaries.len())
            .unwrap_or(0),
        native_worker_summary_kinds,
        memory_summaries,
        compiled_condition_count: compiled.actionable_control_count(),
        exact_compiled_condition_count: compiled.exact_control_count(),
        actionable_compiled_condition_count: compiled.actionable_control_count(),
        branches_pruned: compiled.diagnostics.branches_pruned,
        branches_unknown: compiled.diagnostics.branches_unknown,
        skipped_large_cfg: compiled.diagnostics.skipped_large_cfg,
        interpreter_diagnostic: compiled
            .diagnostics
            .interpreter
            .as_ref()
            .map(interpreter_dispatch_info_from_sym),
        interpreter: compiled
            .vm_body()
            .and_then(|body| body.interpreter.as_ref())
            .map(interpreter_dispatch_info_from_sym),
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

#[cfg(test)]
mod tests {
    use crate::{
        ArtifactGranularity, ExecutionModel, NativeArtifactBody, NativeFunctionSummary,
        RefinementStage, SemanticArtifact, SemanticArtifactBody, SemanticArtifactDiagnostics,
        SliceClass,
    };

    use super::compiled_semantic_info;

    #[test]
    fn compiled_semantic_info_preserves_owner_schema_shape() {
        let artifact = SemanticArtifact {
            stage: RefinementStage::Compiled,
            granularity: ArtifactGranularity::SummaryOnly,
            execution: ExecutionModel::Native,
            body: SemanticArtifactBody::Native(NativeArtifactBody {
                summary: NativeFunctionSummary {
                    slice_class: SliceClass::Worker,
                    role_identity: None,
                    closure_functions: 3,
                    helper_functions: 2,
                    derived_summaries: 1,
                    derived_diagnostics: crate::DerivedSummaryDiagnostics {
                        attempted: 4,
                        budget_exhausted: 1,
                        scc_count: 2,
                        ..crate::DerivedSummaryDiagnostics::default()
                    },
                    region_summaries: Vec::new(),
                    worker_summaries: Vec::new(),
                },
                regions: Default::default(),
            }),
            diagnostics: SemanticArtifactDiagnostics {
                branches_evaluated: 0,
                branches_pruned: 7,
                branches_unknown: 5,
                skipped_missing_arch: false,
                skipped_large_cfg: true,
                residual_reasons: Vec::new(),
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: true,
            },
        };

        let value = serde_json::to_value(compiled_semantic_info(&artifact))
            .expect("serialize compiled semantic info");

        assert_eq!(
            value["schema_version"],
            crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION
        );
        assert_eq!(value["stage"], "compiled");
        assert_eq!(value["granularity"], "summary_only");
        assert_eq!(value["execution"], "native");
        assert_eq!(value["slice_class"], "worker");
        assert_eq!(value["closure_functions"], 3);
        assert_eq!(value["helper_functions"], 2);
        assert_eq!(value["derived_summaries"], 1);
        assert_eq!(value["summary_attempted"], 4);
        assert_eq!(value["summary_budget_exhausted"], 1);
        assert_eq!(value["summary_scc_count"], 2);
        assert_eq!(value["branches_pruned"], 7);
        assert_eq!(value["branches_unknown"], 5);
        assert_eq!(value["skipped_large_cfg"], true);
        assert_eq!(value["cache_hit"], true);
    }
}
