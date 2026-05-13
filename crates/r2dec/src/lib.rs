//! r2dec - Decompiler for r2sleigh.
//!
//! This crate provides decompilation capabilities for the r2sleigh project,
//! converting SSA form to readable C code.
//!
//! ## Overview
//!
//! The decompilation pipeline consists of:
//!
//! 1. **AST** (`ast`): C Abstract Syntax Tree representation
//! 2. **Expression Building** (`expr`): Convert SSA operations to C expressions
//! 3. **Region Identification** (`region`): Identify control flow regions
//! 4. **Control Flow Structuring** (`structure`): Convert CFG to structured code
//! 5. **Type Facts** (`r2types`): Consume inferred type/layout facts
//! 6. **Variable Recovery** (`variable`): Recover variable names and types
//! 7. **Code Generation** (`codegen`): Generate readable C source code
//!
//! ## Usage
//!
//! ```ignore
//! use r2dec::{Decompiler, DecompilerConfig};
//! use r2ssa::SSAFunction;
//!
//! let func: SSAFunction = /* ... */;
//! let config = DecompilerConfig::default();
//! let decompiler = Decompiler::new(config);
//! let c_code = decompiler.decompile(&func);
//! println!("{}", c_code);
//! ```

pub(crate) mod address;
pub(crate) mod analysis;
pub mod ast;
pub mod codegen;
pub(crate) mod consumer_fallback;
pub(crate) mod consumer_linear;
pub(crate) mod consumer_structured;
pub(crate) mod consumer_summary;
pub(crate) mod consumer_vm;
pub mod fold;
pub(crate) mod normalize;
pub(crate) mod planner;
pub(crate) mod post_rename;
pub mod region;
pub(crate) mod registers;
pub mod structure;
pub mod variable;

pub use ast::{BinaryOp, CExpr, CFunction, CStmt, CType, UnaryOp};
pub use codegen::{CodeGenConfig, CodeGenerator, generate};
pub use fold::lower_ssa_ops_to_stmts;
pub use planner::SemanticRoutePlan;
pub use region::{Region, RegionAnalyzer};
pub use structure::ControlFlowStructurer;
pub use variable::VariableRecovery;

use crate::fold::FoldingContext;
use crate::fold::context::{FoldArchConfig, FoldInputs};
use r2il::R2ILBlock;
use r2ssa::SSAFunction;
use r2ssa::SSAOp;
use r2ssa::cfg::BlockTerminator;
use r2types::{
    CTypeLike, ExternalRegisterParamSpec, ExternalTypeDb, FunctionFacts, FunctionSignatureSpec,
    FunctionType, FunctionTypeFacts, StackSlotKey, TypeInference, TypeOracle, VisibleBinding,
    VisibleBindingKind,
};
use std::collections::HashSet;
use std::fmt::Write as _;

fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

fn normalize_callee_name(name: &str) -> String {
    let mut out = name.trim().to_ascii_lowercase();
    for prefix in ["sym.imp.", "sym.", "fcn."] {
        if let Some(rest) = out.strip_prefix(prefix) {
            out = rest.to_string();
            break;
        }
    }
    if let Some((base, ver)) = out.rsplit_once('_')
        && !base.is_empty()
        && ver.chars().all(|c| c.is_ascii_digit())
    {
        return base.to_string();
    }
    out
}

fn prefer_symbolic_large_worker_decompile(function_facts: &FunctionFacts) -> bool {
    planner::prefer_symbolic_large_worker_decompile(function_facts)
}

fn should_skip_runtime_type_inference(
    prepared: Option<&r2ssa::SsaArtifact>,
    _type_facts: &FunctionTypeFacts,
    function_facts: &FunctionFacts,
) -> bool {
    planner::should_skip_runtime_type_inference(prepared, _type_facts, function_facts)
}

fn should_use_prepared_semantic_view(
    prepared: Option<&r2ssa::SsaArtifact>,
    function_facts: &FunctionFacts,
) -> bool {
    planner::should_use_prepared_semantic_view(prepared, function_facts)
}

fn should_render_bounded_semantic_worker_summary(
    function_facts: &FunctionFacts,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> bool {
    let Some(native) = semantic_artifact.native_body() else {
        return false;
    };
    let summary_only = semantic_artifact.granularity == r2sym::ArtifactGranularity::SummaryOnly;
    let no_exact_control =
        native.actionable_control_count() == 0 && native.exact_control_count() == 0;
    if !native.summary.region_summaries.is_empty() {
        return (semantic_artifact.diagnostics.skipped_large_cfg || summary_only)
            && native.has_primary_summary_islands()
            && no_exact_control;
    }
    if !native.summary.worker_summaries.is_empty() {
        return (semantic_artifact.diagnostics.skipped_large_cfg || summary_only)
            && no_exact_control;
    }
    if !function_facts.has_summary_conflicts() {
        return false;
    }
    native.regions.len() >= 4
        && native.actionable_control_count() == 0
        && native.exact_control_count() == 0
}

fn should_render_summary_island_route(semantic_artifact: &r2sym::SemanticArtifact) -> bool {
    let Some(native) = semantic_artifact.native_body() else {
        return false;
    };
    native.has_primary_summary_islands()
        || semantic_artifact.diagnostics.skipped_large_cfg
            && native.has_memory_read_write_summary_pair()
}

fn seed_runtime_type_hints_from_facts_and_recovery(
    type_facts: &FunctionTypeFacts,
    var_recovery: &VariableRecovery,
) -> std::collections::HashMap<String, CType> {
    let mut type_hints = std::collections::HashMap::new();
    let mut insert = |name: &str, ty: &CType| {
        if matches!(ty, CType::Unknown | CType::Void) {
            return;
        }
        type_hints.insert(name.to_string(), ty.clone());
        type_hints.insert(name.to_ascii_lowercase(), ty.clone());
    };

    for var in var_recovery.parameters() {
        insert(&var.name, &var.ty);
    }
    for var in var_recovery.locals() {
        insert(&var.name, &var.ty);
    }
    for binding in &type_facts.visible_bindings {
        if let Some(ty) = binding.ty.as_ref() {
            insert(&binding.name, &type_like_to_ctype(ty));
        }
    }
    for reg_param in &type_facts.register_params {
        if let Some(ty) = reg_param.ty.as_ref() {
            insert(&reg_param.name, &type_like_to_ctype(ty));
        }
    }
    for slot in type_facts.stack_slots.values() {
        if let Some(ty) = slot.ty.as_ref() {
            insert(&slot.name, &type_like_to_ctype(ty));
        }
    }

    type_hints
}

#[cfg_attr(not(test), allow(dead_code))]
fn ctype_to_type_like(ty: &CType) -> CTypeLike {
    match ty {
        CType::Void => CTypeLike::Void,
        CType::Bool => CTypeLike::Bool,
        CType::Int(bits) => CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Signed,
        },
        CType::UInt(bits) => CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Unsigned,
        },
        CType::Float(bits) => CTypeLike::Float(*bits),
        CType::Pointer(inner) => CTypeLike::Pointer(Box::new(ctype_to_type_like(inner))),
        CType::Array(inner, len) => CTypeLike::Array(Box::new(ctype_to_type_like(inner)), *len),
        CType::Struct(name) => CTypeLike::Struct(name.clone()),
        CType::Union(name) => CTypeLike::Union(name.clone()),
        CType::Enum(name) => CTypeLike::Enum(name.clone()),
        CType::Typedef(name) => CTypeLike::Typedef(name.clone()),
        CType::Function { .. } | CType::Unknown => CTypeLike::Unknown,
    }
}

fn type_like_to_ctype(ty: &CTypeLike) -> CType {
    match ty {
        CTypeLike::Void => CType::Void,
        CTypeLike::Bool => CType::Bool,
        CTypeLike::Int { bits, signedness } => match signedness {
            r2types::Signedness::Unsigned => CType::UInt(*bits),
            _ => CType::Int(*bits),
        },
        CTypeLike::Float(bits) => CType::Float(*bits),
        CTypeLike::Pointer(inner) => CType::Pointer(Box::new(type_like_to_ctype(inner))),
        CTypeLike::Array(inner, len) => CType::Array(Box::new(type_like_to_ctype(inner)), *len),
        CTypeLike::Struct(name) => CType::Struct(name.clone()),
        CTypeLike::Union(name) => CType::Union(name.clone()),
        CTypeLike::Enum(name) => CType::Enum(name.clone()),
        CTypeLike::Typedef(name) => CType::Typedef(name.clone()),
        CTypeLike::Function | CTypeLike::Unknown => CType::Unknown,
    }
}

fn format_vm_target_list(targets: &[u64]) -> String {
    if targets.is_empty() {
        return "[]".to_string();
    }
    let rendered = targets
        .iter()
        .map(|target| format!("0x{:x}", target))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{rendered}]")
}

fn format_vm_value_expr(value: &r2sym::VmValueExpr) -> String {
    match value {
        r2sym::VmValueExpr::Const(value) => format!("0x{value:x}"),
        r2sym::VmValueExpr::Var(name) | r2sym::VmValueExpr::Expr(name) => name.clone(),
        r2sym::VmValueExpr::Unary { op, arg } => {
            let op = match op {
                r2sym::VmUnaryOp::Neg => "-",
                r2sym::VmUnaryOp::BitNot => "~",
                r2sym::VmUnaryOp::BoolNot => "!",
            };
            format!("({}{})", op, format_vm_value_expr(arg))
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
                format_vm_value_expr(lhs),
                op,
                format_vm_value_expr(rhs)
            )
        }
    }
}

fn format_vm_state_updates(updates: &[r2sym::VmStateUpdate]) -> String {
    if updates.is_empty() {
        return "[]".to_string();
    }
    let rendered = updates
        .iter()
        .map(|update| format!("{}={}", update.output, format_vm_value_expr(&update.value)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{rendered}]")
}

fn format_vm_guarded_exits(guards: &[r2sym::VmGuardedExit]) -> String {
    if guards.is_empty() {
        return "[]".to_string();
    }
    let rendered = guards
        .iter()
        .map(|guard| format!("0x{:x}:{}", guard.target, guard.guard.expr))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{rendered}]")
}

fn format_vm_memory_conditions(conditions: &[r2sym::VmMemoryCondition]) -> String {
    if conditions.is_empty() {
        return "[]".to_string();
    }
    let rendered = conditions
        .iter()
        .map(|condition| {
            let region = condition.region.name.clone();
            let binding = condition
                .binding
                .as_deref()
                .map(|binding| format!(" -> {binding}"))
                .unwrap_or_default();
            let value = condition
                .value_expr
                .as_deref()
                .map(|value| format!(" = {value}"))
                .unwrap_or_default();
            format!(
                "{}@[{:#x}..{:#x}]/{}:{}{}{}",
                region,
                condition.offset_lo,
                condition.offset_hi,
                condition.size,
                condition.expr,
                binding,
                value,
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{rendered}]")
}

fn sanitize_comment_text(text: &str) -> String {
    text.replace("*/", "* /").replace(['\r', '\n'], " ")
}

fn summary_accumulator_label(name: &str) -> String {
    let lower = name.to_ascii_lowercase();
    if lower.starts_with("tmp:")
        || lower.starts_with("unique:")
        || lower.starts_with("const:")
        || lower.starts_with("ram:")
        || is_ssa_versioned_register_label(name)
    {
        "accumulator".to_string()
    } else {
        name.to_string()
    }
}

fn is_ssa_versioned_register_label(name: &str) -> bool {
    let Some((base, suffix)) = name.rsplit_once('_') else {
        return false;
    };
    !base.is_empty()
        && !suffix.is_empty()
        && suffix.bytes().all(|byte| byte.is_ascii_digit())
        && base.bytes().any(|byte| byte.is_ascii_alphabetic())
        && base
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit())
}

pub(crate) fn format_vm_summary_kind(kind: r2sym::InterpreterKind) -> &'static str {
    match kind {
        r2sym::InterpreterKind::SwitchDispatch => "switch_dispatch",
        r2sym::InterpreterKind::IndirectDispatch => "indirect_dispatch",
    }
}

pub(crate) fn is_autogenerated_function_name(name: &str) -> bool {
    let underscore_hex_addr = name
        .strip_prefix('_')
        .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_hexdigit()));
    name.is_empty()
        || name.starts_with("fcn.")
        || name.starts_with("fcn_")
        || name.starts_with("sub.")
        || name.starts_with("sub_")
        || name.starts_with("loc.")
        || underscore_hex_addr
}

pub(crate) fn semantic_mode_label(artifact: &r2sym::SemanticArtifact) -> &'static str {
    match (artifact.execution, artifact.stage, artifact.granularity) {
        (r2sym::ExecutionModel::Vm, _, _) => "vm_summary",
        (_, r2sym::RefinementStage::Raw, _) => "raw",
        (_, r2sym::RefinementStage::Compiled, r2sym::ArtifactGranularity::Regioned) => {
            "island_compiled"
        }
        (_, r2sym::RefinementStage::Compiled, _) => "compiled",
        (_, r2sym::RefinementStage::Residual, _) => "residual",
    }
}

pub(crate) fn semantic_slice_class_label(slice_class: r2sym::SliceClass) -> &'static str {
    match slice_class {
        r2sym::SliceClass::Wrapper => "wrapper",
        r2sym::SliceClass::Worker => "worker",
        r2sym::SliceClass::RecursiveGroup => "recursive_group",
        r2sym::SliceClass::InterpreterSwitch => "interpreter_switch",
        r2sym::SliceClass::InterpreterIndirect => "interpreter_indirect",
        r2sym::SliceClass::GenericLarge => "generic_large",
    }
}

pub(crate) fn semantic_residual_reason_label(reason: r2sym::ResidualReason) -> &'static str {
    match reason {
        r2sym::ResidualReason::MissingArch => "missing_arch",
        r2sym::ResidualReason::LargeCfg => "large_cfg",
        r2sym::ResidualReason::SummaryBudgetExhausted => "summary_budget_exhausted",
        r2sym::ResidualReason::SccBudgetExhausted => "scc_budget_exhausted",
        r2sym::ResidualReason::InterpreterRequiresStepSummary => {
            "interpreter_requires_step_summary"
        }
    }
}

fn native_worker_summary_kind_label(kind: r2sym::NativeWorkerSummaryKind) -> &'static str {
    match kind {
        r2sym::NativeWorkerSummaryKind::ProgramOrchestrator => "program_orchestrator",
        r2sym::NativeWorkerSummaryKind::MemoryTransfer => "memory_transfer",
        r2sym::NativeWorkerSummaryKind::FileTransfer => "file_transfer",
        r2sym::NativeWorkerSummaryKind::MemoryRead => "memory_read",
        r2sym::NativeWorkerSummaryKind::MemoryWrite => "memory_write",
        r2sym::NativeWorkerSummaryKind::MemoryEscape => "memory_escape",
        r2sym::NativeWorkerSummaryKind::MemoryFree => "memory_free",
        r2sym::NativeWorkerSummaryKind::StringScan => "string_scan",
        r2sym::NativeWorkerSummaryKind::HashFold => "hash_fold",
        r2sym::NativeWorkerSummaryKind::TableWalk => "table_walk",
        r2sym::NativeWorkerSummaryKind::PathWalk => "path_walk",
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal => "directory_traversal",
        r2sym::NativeWorkerSummaryKind::RecordStream => "record_stream",
        r2sym::NativeWorkerSummaryKind::FieldSelection => "field_selection",
        r2sym::NativeWorkerSummaryKind::OutputStream => "output_stream",
        r2sym::NativeWorkerSummaryKind::FormatRender => "format_render",
        r2sym::NativeWorkerSummaryKind::MetadataProbe => "metadata_probe",
        r2sym::NativeWorkerSummaryKind::SortMerge => "sort_merge",
        r2sym::NativeWorkerSummaryKind::NumericTransform => "numeric_transform",
        r2sym::NativeWorkerSummaryKind::Parser => "parser",
        r2sym::NativeWorkerSummaryKind::DiagnosticWrapper => "diagnostic_wrapper",
        r2sym::NativeWorkerSummaryKind::FormatArgumentFetch => "format_argument_fetch",
        r2sym::NativeWorkerSummaryKind::Allocation => "allocation",
        r2sym::NativeWorkerSummaryKind::Lifetime => "lifetime",
        r2sym::NativeWorkerSummaryKind::Synchronization => "synchronization",
        r2sym::NativeWorkerSummaryKind::Atomic => "atomic",
        r2sym::NativeWorkerSummaryKind::Unknown => "unknown",
    }
}

fn summary_memory_region_label(region: r2ssa::SummaryMemoryRegion) -> String {
    match region {
        r2ssa::SummaryMemoryRegion::Arg { index } => format!("arg{index}"),
        r2ssa::SummaryMemoryRegion::Global { address } => format!("global[0x{address:x}]"),
        r2ssa::SummaryMemoryRegion::HeapReturn => "heap_return".to_string(),
        r2ssa::SummaryMemoryRegion::Unknown => "unknown".to_string(),
    }
}

fn summary_memory_location_label(location: &r2ssa::SummaryMemoryLocation) -> String {
    let base = summary_memory_region_label(location.region);
    if let Some(range) = location.range {
        let width = range
            .width
            .map(|width| width.to_string())
            .unwrap_or_else(|| "?".to_string());
        format!(
            "{}[{}..{};w={}]",
            base, range.offset_lo, range.offset_hi, width
        )
    } else {
        base
    }
}

fn summary_transfer_length_label(len: r2ssa::SummaryTransferLength) -> String {
    match len {
        r2ssa::SummaryTransferLength::Arg(index) => format!("arg{index}"),
        r2ssa::SummaryTransferLength::Const(value) => value.to_string(),
        r2ssa::SummaryTransferLength::Unknown => "unknown".to_string(),
    }
}

fn native_worker_terminator_label(terminator: r2sym::NativeWorkerTerminator) -> String {
    match terminator {
        r2sym::NativeWorkerTerminator::None => "none".to_string(),
        r2sym::NativeWorkerTerminator::ZeroByte => "zero_byte".to_string(),
        r2sym::NativeWorkerTerminator::ByteEquals(value) => format!("byte_eq_0x{value:02x}"),
        r2sym::NativeWorkerTerminator::LengthBound => "length_bound".to_string(),
        r2sym::NativeWorkerTerminator::Unknown => "unknown".to_string(),
    }
}

fn native_worker_terminator_display_label(terminator: r2sym::NativeWorkerTerminator) -> String {
    match terminator {
        r2sym::NativeWorkerTerminator::None => "none".to_string(),
        r2sym::NativeWorkerTerminator::ZeroByte => "zero byte".to_string(),
        r2sym::NativeWorkerTerminator::ByteEquals(value) => format!("byte 0x{value:02x}"),
        r2sym::NativeWorkerTerminator::LengthBound => "length bound".to_string(),
        r2sym::NativeWorkerTerminator::Unknown => "unknown".to_string(),
    }
}

fn native_worker_fold_operation_label(operation: r2sym::NativeWorkerFoldOperation) -> &'static str {
    match operation {
        r2sym::NativeWorkerFoldOperation::Add => "add",
        r2sym::NativeWorkerFoldOperation::Xor => "xor",
        r2sym::NativeWorkerFoldOperation::RotateMix => "rotate_mix",
    }
}

fn native_parser_summary_label(parser: &r2sym::NativeParserSummary) -> String {
    match parser.kind {
        r2sym::NativeParserKind::Numeric => parser
            .base
            .map(|base| format!("base{base} numeric"))
            .unwrap_or_else(|| "numeric".to_string()),
        r2sym::NativeParserKind::Token => "token".to_string(),
        r2sym::NativeParserKind::Unknown => "unknown".to_string(),
    }
}

fn native_worker_loop_detail(loop_summary: &r2sym::NativeWorkerLoopSummary) -> String {
    let mut parts = vec![format!("loop=0x{:x}", loop_summary.header)];
    if let Some(exit) = loop_summary.exit_target {
        parts.push(format!("exit=0x{exit:x}"));
    }
    if let Some(iterations) = loop_summary.iterations {
        parts.push(format!("iters={iterations}"));
    }
    if let Some(length_arg) = loop_summary.length_arg {
        parts.push(format!("length=arg{length_arg}"));
    }
    if let Some(stride) = loop_summary.stride {
        parts.push(format!("stride={stride}"));
    }
    if let Some(terminator) = loop_summary.terminator {
        parts.push(format!(
            "term={}",
            native_worker_terminator_label(terminator)
        ));
    }
    if let Some(fold) = loop_summary.fold.as_ref() {
        parts.push(format!(
            "fold={}/{}:{}",
            native_worker_fold_operation_label(fold.operation),
            summary_accumulator_label(&fold.accumulator),
            fold.bits
        ));
    }
    parts.join(" ")
}

fn native_worker_summary_pseudocode(summary: &r2sym::NativeWorkerSummary) -> Option<String> {
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::ProgramOrchestrator => {
            Some("orchestrate program phases from argc, argv, and environment".to_string())
        }
        r2sym::NativeWorkerSummaryKind::MemoryTransfer => {
            let dst = summary.dst.as_ref().map(summary_memory_location_label)?;
            let src = summary.src.as_ref().map(summary_memory_location_label)?;
            let len = summary
                .len
                .map(summary_transfer_length_label)
                .unwrap_or_else(|| "unknown".to_string());
            Some(format!("copy {len} bytes from {src} to {dst}"))
        }
        r2sym::NativeWorkerSummaryKind::FileTransfer => {
            let dst = summary.dst.as_ref().map(summary_memory_location_label)?;
            let src = summary.src.as_ref().map(summary_memory_location_label)?;
            let len = summary
                .len
                .map(summary_transfer_length_label)
                .unwrap_or_else(|| "bounded chunks".to_string());
            Some(format!("copy file data from {src} to {dst} ({len})"))
        }
        r2sym::NativeWorkerSummaryKind::StringScan => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            let terminator = summary
                .loop_summary
                .as_ref()
                .and_then(|loop_summary| loop_summary.terminator)
                .map(native_worker_terminator_display_label)
                .unwrap_or_else(|| "zero byte".to_string());
            Some(format!("scan {memory} until {terminator}"))
        }
        r2sym::NativeWorkerSummaryKind::MemoryRead | r2sym::NativeWorkerSummaryKind::TableWalk => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            let terminator = summary
                .loop_summary
                .as_ref()
                .and_then(|loop_summary| loop_summary.terminator)
                .map(native_worker_terminator_label)
                .unwrap_or_else(|| "unknown".to_string());
            Some(format!("scan {memory} until {terminator}"))
        }
        r2sym::NativeWorkerSummaryKind::PathWalk => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("walk path components from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("traverse directory entries from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::RecordStream => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("read records from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::FieldSelection => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("select fields using {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::OutputStream => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("write output stream from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::FormatRender => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("render formatted output from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::MetadataProbe => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("probe file metadata for {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::SortMerge => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            Some(format!("merge sorted records from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::NumericTransform => {
            let dst = summary
                .dst
                .as_ref()
                .map(summary_memory_location_label)
                .unwrap_or_else(|| "return value".to_string());
            Some(format!("compute numeric transform into {dst}"))
        }
        r2sym::NativeWorkerSummaryKind::HashFold => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            let fold = summary.loop_summary.as_ref()?.fold.as_ref()?;
            Some(format!(
                "{} fold over {} into {}",
                native_worker_fold_operation_label(fold.operation),
                memory,
                summary_accumulator_label(&fold.accumulator)
            ))
        }
        r2sym::NativeWorkerSummaryKind::Parser => {
            let memory = summary.memory.as_ref().map(summary_memory_location_label)?;
            let parser = summary
                .parser
                .as_ref()
                .map(native_parser_summary_label)
                .unwrap_or_else(|| "token".to_string());
            Some(format!("parse {parser} stream from {memory}"))
        }
        r2sym::NativeWorkerSummaryKind::DiagnosticWrapper => {
            let fmt = summary
                .memory
                .as_ref()
                .map(summary_memory_location_label)
                .unwrap_or_else(|| "format argument".to_string());
            Some(format!("diagnose formatted error from {fmt}"))
        }
        r2sym::NativeWorkerSummaryKind::FormatArgumentFetch => {
            let dst = summary
                .dst
                .as_ref()
                .map(summary_memory_location_label)
                .unwrap_or_else(|| "argument table".to_string());
            let src = summary
                .src
                .as_ref()
                .map(summary_memory_location_label)
                .unwrap_or_else(|| "va_list".to_string());
            Some(format!("fetch printf arguments from {src} into {dst}"))
        }
        _ => None,
    }
}

fn sanitize_worker_ident(text: &str) -> String {
    let mut ident = String::new();
    for ch in text.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            ident.push(ch);
        } else if !ident.ends_with('_') {
            ident.push('_');
        }
    }
    let ident = ident.trim_matches('_');
    if ident.is_empty() {
        "worker_value".to_string()
    } else if ident.chars().next().is_some_and(|ch| ch.is_ascii_digit()) {
        format!("worker_{ident}")
    } else {
        ident.to_string()
    }
}

fn summary_memory_location_ident(location: &r2ssa::SummaryMemoryLocation) -> String {
    if let r2ssa::SummaryMemoryRegion::Arg { index } = location.region {
        return format!("arg{index}");
    }
    sanitize_worker_ident(&summary_memory_location_label(location))
}

fn summary_transfer_length_expr(len: Option<r2ssa::SummaryTransferLength>) -> Option<CExpr> {
    match len {
        Some(r2ssa::SummaryTransferLength::Arg(index)) => Some(CExpr::var(format!("arg{index}"))),
        Some(r2ssa::SummaryTransferLength::Const(value)) => Some(CExpr::uint(value)),
        Some(r2ssa::SummaryTransferLength::Unknown) | None => None,
    }
}

fn native_worker_terminator_expr(terminator: Option<r2sym::NativeWorkerTerminator>) -> CExpr {
    match terminator {
        Some(r2sym::NativeWorkerTerminator::ZeroByte)
        | Some(r2sym::NativeWorkerTerminator::None)
        | None => CExpr::int(0),
        Some(r2sym::NativeWorkerTerminator::ByteEquals(value)) => CExpr::uint(value.into()),
        Some(r2sym::NativeWorkerTerminator::LengthBound) => CExpr::var("length_bound"),
        Some(r2sym::NativeWorkerTerminator::Unknown) => CExpr::var("unknown_terminator"),
    }
}

fn summary_location_expr(location: &r2ssa::SummaryMemoryLocation) -> CExpr {
    CExpr::var(summary_memory_location_ident(location))
}

fn summary_worker_length(
    summary: &r2sym::NativeWorkerSummary,
) -> Option<r2ssa::SummaryTransferLength> {
    summary.len.or_else(|| {
        summary.loop_summary.as_ref().and_then(|loop_summary| {
            loop_summary
                .length_arg
                .map(r2ssa::SummaryTransferLength::Arg)
        })
    })
}

fn native_region_summary_length(
    summary: &r2sym::NativeRegionSummary,
) -> Option<r2ssa::SummaryTransferLength> {
    summary
        .memory_accesses
        .iter()
        .find_map(|access| access.len)
        .or_else(|| {
            summary.loop_summary.as_ref().and_then(|loop_summary| {
                loop_summary
                    .length_arg
                    .map(r2ssa::SummaryTransferLength::Arg)
            })
        })
}

fn semantic_evidence_allows_structured_rendering(evidence: &r2sym::SemanticEvidence) -> bool {
    evidence.allows_guarded_structuring()
}

fn native_worker_summary_allows_structured_rendering(summary: &r2sym::NativeWorkerSummary) -> bool {
    semantic_evidence_allows_structured_rendering(&summary.evidence)
}

fn native_worker_summary_allows_side_effect_rendering(
    summary: &r2sym::NativeWorkerSummary,
) -> bool {
    summary.evidence.allows_guarded_structuring()
        && matches!(
            summary.kind,
            r2sym::NativeWorkerSummaryKind::OutputStream
                | r2sym::NativeWorkerSummaryKind::FormatRender
                | r2sym::NativeWorkerSummaryKind::DiagnosticWrapper
                | r2sym::NativeWorkerSummaryKind::FormatArgumentFetch
        )
}

fn native_region_summary_allows_structured_rendering(summary: &r2sym::NativeRegionSummary) -> bool {
    semantic_evidence_allows_structured_rendering(&summary.evidence)
}

fn native_worker_summary_structured_stmt(summary: &r2sym::NativeWorkerSummary) -> Option<CStmt> {
    let allows_structured = native_worker_summary_allows_structured_rendering(summary);
    let allows_side_effect = native_worker_summary_allows_side_effect_rendering(summary);
    if !allows_structured && !allows_side_effect {
        return None;
    }
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::ProgramOrchestrator => Some(CStmt::Expr(CExpr::call(
            CExpr::var("run_program_orchestrator"),
            vec![CExpr::var("argc"), CExpr::var("argv"), CExpr::var("envp")],
        ))),
        r2sym::NativeWorkerSummaryKind::MemoryTransfer => {
            let dst = summary.dst.as_ref().map(summary_location_expr)?;
            let src = summary.src.as_ref().map(summary_location_expr)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("memcpy"),
                vec![dst, src, summary_transfer_length_expr(summary.len)?],
            )))
        }
        r2sym::NativeWorkerSummaryKind::FileTransfer => {
            let src = summary.src.as_ref().map(summary_location_expr)?;
            let dst = summary.dst.as_ref().map(summary_location_expr)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("copy_file_data_summary"),
                vec![src, dst, summary_transfer_length_expr(summary.len)?],
            )))
        }
        r2sym::NativeWorkerSummaryKind::StringScan => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            let terminator = summary
                .loop_summary
                .as_ref()
                .and_then(|loop_summary| loop_summary.terminator);
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("scan_string_summary"),
                vec![
                    CExpr::var(memory),
                    native_worker_terminator_expr(terminator),
                ],
            )))
        }
        r2sym::NativeWorkerSummaryKind::MemoryRead | r2sym::NativeWorkerSummaryKind::TableWalk => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            let terminator = summary
                .loop_summary
                .as_ref()
                .and_then(|loop_summary| loop_summary.terminator);
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("walk_table_summary"),
                vec![
                    CExpr::var(memory),
                    native_worker_terminator_expr(terminator),
                ],
            )))
        }
        r2sym::NativeWorkerSummaryKind::PathWalk => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("walk_path_summary"),
                vec![CExpr::var(memory)],
            )))
        }
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("traverse_directory_summary"),
                vec![CExpr::var(memory)],
            )))
        }
        r2sym::NativeWorkerSummaryKind::RecordStream => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("read_records_summary"),
                vec![CExpr::var(memory)],
            )))
        }
        r2sym::NativeWorkerSummaryKind::FieldSelection => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("select_fields_summary"),
                vec![CExpr::var(memory)],
            )))
        }
        r2sym::NativeWorkerSummaryKind::OutputStream => {
            let memory = summary.memory.as_ref().map(summary_location_expr)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("write_output_stream"),
                vec![memory],
            )))
        }
        r2sym::NativeWorkerSummaryKind::FormatRender => {
            let memory = summary.memory.as_ref().map(summary_location_expr)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("render_formatted_output"),
                vec![memory],
            )))
        }
        r2sym::NativeWorkerSummaryKind::MetadataProbe => {
            let memory = summary.memory.as_ref().map(summary_location_expr)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("probe_file_metadata"),
                vec![memory],
            )))
        }
        r2sym::NativeWorkerSummaryKind::SortMerge => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("merge_sorted_records_summary"),
                vec![CExpr::var(memory)],
            )))
        }
        r2sym::NativeWorkerSummaryKind::NumericTransform => {
            let dst = summary
                .dst
                .as_ref()
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("result"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("compute_numeric_transform"),
                vec![dst],
            )))
        }
        r2sym::NativeWorkerSummaryKind::HashFold => {
            let memory = summary.memory.as_ref().map(summary_memory_location_ident)?;
            let fold = summary.loop_summary.as_ref()?.fold.as_ref()?;
            let accumulator = summary_accumulator_label(&fold.accumulator);
            Some(CStmt::Expr(CExpr::assign(
                CExpr::var(accumulator.clone()),
                CExpr::call(
                    CExpr::var(format!(
                        "{}_fold_summary",
                        native_worker_fold_operation_label(fold.operation)
                    )),
                    vec![
                        CExpr::var(accumulator),
                        CExpr::var(memory),
                        summary_transfer_length_expr(summary_worker_length(summary))?,
                    ],
                ),
            )))
        }
        r2sym::NativeWorkerSummaryKind::Parser => {
            let parser = summary
                .parser
                .as_ref()
                .map(native_parser_summary_label)
                .unwrap_or_else(|| "token".to_string());
            let stream = summary
                .memory
                .as_ref()
                .map(summary_location_expr)
                .or_else(|| {
                    summary
                        .parser
                        .as_ref()
                        .and_then(|parser| parser.cursor_arg)
                        .map(|index| CExpr::var(format!("arg{index}")))
                })
                .unwrap_or_else(|| CExpr::var("parser_stream"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var(format!("parse_{}_summary", sanitize_worker_ident(&parser))),
                vec![stream],
            )))
        }
        r2sym::NativeWorkerSummaryKind::DiagnosticWrapper => {
            let fmt = summary
                .memory
                .as_ref()
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("fmt"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("diagnose_summary"),
                vec![fmt],
            )))
        }
        r2sym::NativeWorkerSummaryKind::FormatArgumentFetch => {
            let src = summary
                .src
                .as_ref()
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("va_list"));
            let dst = summary
                .dst
                .as_ref()
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("arguments_out"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("fetch_printf_arguments"),
                vec![src, dst],
            )))
        }
        r2sym::NativeWorkerSummaryKind::Allocation => {
            let len = summary
                .allocation
                .and_then(|allocation| allocation.size_arg)
                .map(r2ssa::SummaryTransferLength::Arg);
            Some(CStmt::Expr(CExpr::call(
                CExpr::var(
                    summary
                        .allocation
                        .filter(|allocation| allocation.zeroed)
                        .map(|_| "calloc_summary")
                        .unwrap_or("malloc_summary"),
                ),
                vec![summary_transfer_length_expr(len)?],
            )))
        }
        r2sym::NativeWorkerSummaryKind::MemoryFree => {
            let memory = summary
                .memory
                .as_ref()
                .or(summary.src.as_ref())
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("released_memory"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("free_summary"),
                vec![memory],
            )))
        }
        _ => None,
    }
}

fn native_region_summary_memory_ident(
    summary: &r2sym::NativeRegionSummary,
    fallback: &str,
) -> String {
    summary
        .memory_accesses
        .iter()
        .filter_map(|access| access.location.as_ref())
        .next()
        .map(summary_memory_location_ident)
        .unwrap_or_else(|| fallback.to_string())
}

fn native_region_summary_memory_expr(
    summary: &r2sym::NativeRegionSummary,
    fallback: &str,
) -> CExpr {
    summary
        .memory_accesses
        .iter()
        .filter_map(|access| access.location.as_ref())
        .next()
        .map(summary_location_expr)
        .unwrap_or_else(|| CExpr::var(fallback))
}

fn native_region_summary_structured_stmt(summary: &r2sym::NativeRegionSummary) -> Option<CStmt> {
    if !native_region_summary_allows_structured_rendering(summary) {
        return None;
    }
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::ProgramOrchestrator => Some(CStmt::Expr(CExpr::call(
            CExpr::var("run_program_orchestrator"),
            vec![CExpr::var("argc"), CExpr::var("argv"), CExpr::var("envp")],
        ))),
        r2sym::NativeWorkerSummaryKind::MemoryTransfer => {
            let access = summary
                .memory_accesses
                .iter()
                .find(|access| matches!(access.kind, r2sym::NativeMemoryAccessKind::Transfer))?;
            let dst = access.dst.as_ref().map(summary_location_expr)?;
            let src = access.src.as_ref().map(summary_location_expr)?;
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("memcpy"),
                vec![dst, src, summary_transfer_length_expr(access.len)?],
            )))
        }
        r2sym::NativeWorkerSummaryKind::FileTransfer => {
            let access = summary
                .memory_accesses
                .iter()
                .find(|access| access.src.is_some() || access.dst.is_some());
            let src = access
                .and_then(|access| access.src.as_ref())
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("src_file"));
            let dst = access
                .and_then(|access| access.dst.as_ref())
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("dst_file"));
            let len = access.and_then(|access| access.len);
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("copy_file_data_summary"),
                vec![src, dst, summary_transfer_length_expr(len)?],
            )))
        }
        r2sym::NativeWorkerSummaryKind::StringScan => {
            let memory = native_region_summary_memory_ident(summary, "string");
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("scan_string_summary"),
                vec![
                    CExpr::var(memory),
                    native_worker_terminator_expr(
                        summary
                            .loop_summary
                            .as_ref()
                            .and_then(|loop_summary| loop_summary.terminator),
                    ),
                ],
            )))
        }
        r2sym::NativeWorkerSummaryKind::PathWalk => {
            let memory = native_region_summary_memory_expr(summary, "path");
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("walk_path_summary"),
                vec![memory],
            )))
        }
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal => {
            let memory = native_region_summary_memory_expr(summary, "dir_stream");
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("traverse_directory_summary"),
                vec![memory],
            )))
        }
        r2sym::NativeWorkerSummaryKind::RecordStream
        | r2sym::NativeWorkerSummaryKind::FieldSelection
        | r2sym::NativeWorkerSummaryKind::SortMerge
        | r2sym::NativeWorkerSummaryKind::NumericTransform => {
            let memory = native_region_summary_memory_expr(
                summary,
                native_worker_summary_kind_label(summary.kind),
            );
            let callee = match summary.kind {
                r2sym::NativeWorkerSummaryKind::RecordStream => "read_records_summary",
                r2sym::NativeWorkerSummaryKind::FieldSelection => "select_fields_summary",
                r2sym::NativeWorkerSummaryKind::SortMerge => "merge_sorted_records_summary",
                r2sym::NativeWorkerSummaryKind::NumericTransform => "compute_numeric_transform",
                _ => unreachable!(),
            };
            Some(CStmt::Expr(CExpr::call(CExpr::var(callee), vec![memory])))
        }
        r2sym::NativeWorkerSummaryKind::OutputStream
        | r2sym::NativeWorkerSummaryKind::FormatRender
        | r2sym::NativeWorkerSummaryKind::MetadataProbe => {
            let memory = summary
                .memory_accesses
                .iter()
                .filter_map(|access| access.location.as_ref())
                .next()
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("summary_input"));
            let callee = match summary.kind {
                r2sym::NativeWorkerSummaryKind::OutputStream => "write_output_stream",
                r2sym::NativeWorkerSummaryKind::FormatRender => "render_formatted_output",
                r2sym::NativeWorkerSummaryKind::MetadataProbe => "probe_file_metadata",
                _ => unreachable!(),
            };
            Some(CStmt::Expr(CExpr::call(CExpr::var(callee), vec![memory])))
        }
        r2sym::NativeWorkerSummaryKind::HashFold => {
            let reduction = summary.reductions.first()?;
            let source = reduction
                .source
                .as_ref()
                .map(summary_memory_location_ident)
                .unwrap_or_else(|| "fold_source".to_string());
            let accumulator = summary_accumulator_label(&reduction.accumulator);
            Some(CStmt::Expr(CExpr::assign(
                CExpr::var(accumulator.clone()),
                CExpr::call(
                    CExpr::var(format!(
                        "{}_fold_summary",
                        native_worker_fold_operation_label(reduction.operation)
                    )),
                    vec![
                        CExpr::var(accumulator),
                        CExpr::var(source),
                        summary_transfer_length_expr(native_region_summary_length(summary))?,
                    ],
                ),
            )))
        }
        r2sym::NativeWorkerSummaryKind::Parser => {
            let parser = summary
                .parser
                .as_ref()
                .map(native_parser_summary_label)
                .unwrap_or_else(|| "token".to_string());
            let memory = native_region_summary_memory_expr(summary, "parser_stream");
            Some(CStmt::Expr(CExpr::call(
                CExpr::var(format!("parse_{}_summary", sanitize_worker_ident(&parser))),
                vec![memory],
            )))
        }
        r2sym::NativeWorkerSummaryKind::DiagnosticWrapper => {
            let fmt = summary
                .memory_accesses
                .iter()
                .filter_map(|access| access.location.as_ref())
                .next()
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("fmt"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("diagnose_summary"),
                vec![fmt],
            )))
        }
        r2sym::NativeWorkerSummaryKind::FormatArgumentFetch => {
            let access = summary
                .memory_accesses
                .iter()
                .find(|access| access.src.is_some() || access.dst.is_some());
            let src = access
                .and_then(|access| access.src.as_ref())
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("va_list"));
            let dst = access
                .and_then(|access| access.dst.as_ref())
                .map(summary_location_expr)
                .unwrap_or_else(|| CExpr::var("arguments_out"));
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("fetch_printf_arguments"),
                vec![src, dst],
            )))
        }
        r2sym::NativeWorkerSummaryKind::Allocation => {
            let len = summary
                .memory_accesses
                .iter()
                .find(|access| matches!(access.kind, r2sym::NativeMemoryAccessKind::Allocation))
                .and_then(|access| access.len);
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("malloc_summary"),
                vec![summary_transfer_length_expr(len)?],
            )))
        }
        r2sym::NativeWorkerSummaryKind::MemoryFree => {
            let memory = native_region_summary_memory_expr(summary, "released_memory");
            Some(CStmt::Expr(CExpr::call(
                CExpr::var("free_summary"),
                vec![memory],
            )))
        }
        _ => None,
    }
}

fn native_worker_summary_detail(summary: &r2sym::NativeWorkerSummary) -> String {
    let mut parts = Vec::new();
    if let Some(dst) = summary.dst.as_ref() {
        parts.push(format!("dst={}", summary_memory_location_label(dst)));
    }
    if let Some(src) = summary.src.as_ref() {
        parts.push(format!("src={}", summary_memory_location_label(src)));
    }
    if let Some(memory) = summary.memory.as_ref() {
        parts.push(format!("mem={}", summary_memory_location_label(memory)));
    }
    if let Some(len) = summary.len {
        parts.push(format!("len={}", summary_transfer_length_label(len)));
    }
    if let Some(allocation) = summary.allocation {
        parts.push(format!(
            "alloc_size={} zeroed={}",
            allocation
                .size_arg
                .map(|index| format!("arg{index}"))
                .unwrap_or_else(|| "unknown".to_string()),
            allocation.zeroed
        ));
    }
    if let Some(lifetime) = summary.lifetime {
        parts.push(format!("lifetime={:?}(arg{})", lifetime.op, lifetime.arg));
    }
    if let Some(sync) = summary.sync {
        parts.push(format!("sync={:?}(arg{})", sync.op, sync.arg));
    }
    if let Some(atomic) = summary.atomic {
        parts.push(format!("atomic={:?}/{:?}", atomic.op, atomic.ordering));
    }
    if let Some(loop_summary) = summary.loop_summary.as_ref() {
        parts.push(native_worker_loop_detail(loop_summary));
    }
    if let Some(parser) = summary.parser.as_ref() {
        parts.push(format!("parser={}", native_parser_summary_label(parser)));
        if let Some(arg) = parser.cursor_arg {
            parts.push(format!("cursor=arg{arg}"));
        }
        if let (Some(min), Some(max)) = (parser.digit_min, parser.digit_max) {
            parts.push(format!("digits=0x{min:02x}..0x{max:02x}"));
        }
        if parser.accepts_sign {
            parts.push("sign=true".to_string());
        }
    }
    let evidence = format!(
        "{:?}/{:?}/{:?}",
        summary.evidence.tier, summary.evidence.coverage, summary.evidence.provenance
    );
    format!(
        "{}: {} evidence={}",
        native_worker_summary_kind_label(summary.kind),
        parts.join(" "),
        evidence
    )
}

fn native_region_loop_detail(loop_summary: &r2sym::NativeLoopSummary) -> String {
    let mut parts = vec![format!("loop=0x{:x}", loop_summary.header)];
    if !loop_summary.body.is_empty() {
        parts.push(format!("blocks={}", loop_summary.body.len()));
    }
    if !loop_summary.exits.is_empty() {
        parts.push(format!(
            "exits={}",
            loop_summary
                .exits
                .iter()
                .map(|addr| format!("0x{addr:x}"))
                .collect::<Vec<_>>()
                .join("|")
        ));
    }
    if let Some(iterations) = loop_summary.iterations {
        parts.push(format!("iters={iterations}"));
    }
    if let Some(length_arg) = loop_summary.length_arg {
        parts.push(format!("length=arg{length_arg}"));
    }
    if let Some(stride) = loop_summary.stride {
        parts.push(format!("stride={stride}"));
    }
    if let Some(terminator) = loop_summary.terminator {
        parts.push(format!(
            "term={}",
            native_worker_terminator_label(terminator)
        ));
    }
    parts.join(" ")
}

fn native_region_access_pseudocode(access: &r2sym::NativeMemoryAccessSummary) -> Option<String> {
    match access.kind {
        r2sym::NativeMemoryAccessKind::Transfer => {
            let dst = access.dst.as_ref().map(summary_memory_location_label)?;
            let src = access.src.as_ref().map(summary_memory_location_label)?;
            let len = access
                .len
                .map(summary_transfer_length_label)
                .unwrap_or_else(|| "unknown".to_string());
            Some(format!("copy {len} bytes from {src} to {dst}"))
        }
        r2sym::NativeMemoryAccessKind::Read => {
            let memory = access
                .location
                .as_ref()
                .map(summary_memory_location_label)?;
            Some(format!("read stream from {memory}"))
        }
        r2sym::NativeMemoryAccessKind::Write => {
            let memory = access
                .location
                .as_ref()
                .map(summary_memory_location_label)?;
            Some(format!("write stream to {memory}"))
        }
        r2sym::NativeMemoryAccessKind::Atomic => {
            let memory = access
                .location
                .as_ref()
                .map(summary_memory_location_label)?;
            Some(format!("atomic update at {memory}"))
        }
        _ => None,
    }
}

fn native_region_summary_pseudocode(summary: &r2sym::NativeRegionSummary) -> Option<String> {
    if let Some(reduction) = summary.reductions.first() {
        let source = reduction
            .source
            .as_ref()
            .map(summary_memory_location_label)
            .unwrap_or_else(|| "unknown".to_string());
        return Some(format!(
            "{} fold over {} into {}",
            native_worker_fold_operation_label(reduction.operation),
            source,
            summary_accumulator_label(&reduction.accumulator)
        ));
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::StringScan)
        && let Some(access) = summary.memory_accesses.first()
    {
        let memory = access
            .location
            .as_ref()
            .map(summary_memory_location_label)?;
        return Some(format!("scan {memory} until zero byte"));
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::Parser)
        && let Some(access) = summary.memory_accesses.first()
    {
        let memory = access
            .location
            .as_ref()
            .map(summary_memory_location_label)?;
        let parser = summary
            .parser
            .as_ref()
            .map(native_parser_summary_label)
            .unwrap_or_else(|| "token".to_string());
        return Some(format!("parse {parser} stream from {memory}"));
    }
    if matches!(
        summary.kind,
        r2sym::NativeWorkerSummaryKind::DiagnosticWrapper
    ) {
        return Some("diagnose formatted error".to_string());
    }
    if matches!(
        summary.kind,
        r2sym::NativeWorkerSummaryKind::FormatArgumentFetch
    ) {
        return Some("fetch printf arguments into argument table".to_string());
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::FileTransfer) {
        return Some("copy file data across source and destination".to_string());
    }
    if matches!(
        summary.kind,
        r2sym::NativeWorkerSummaryKind::ProgramOrchestrator
    ) {
        return Some("orchestrate program phases".to_string());
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::PathWalk)
        && let Some(access) = summary.memory_accesses.first()
    {
        let memory = access
            .location
            .as_ref()
            .map(summary_memory_location_label)?;
        return Some(format!("walk path components from {memory}"));
    }
    if matches!(
        summary.kind,
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal
    ) {
        return Some("traverse directory entries".to_string());
    }
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::RecordStream => {
            return Some("read record stream".to_string());
        }
        r2sym::NativeWorkerSummaryKind::FieldSelection => {
            return Some("select fields from record stream".to_string());
        }
        r2sym::NativeWorkerSummaryKind::OutputStream => {
            return Some("write output stream".to_string());
        }
        r2sym::NativeWorkerSummaryKind::FormatRender => {
            return Some("render formatted output".to_string());
        }
        r2sym::NativeWorkerSummaryKind::MetadataProbe => {
            return Some("probe file metadata".to_string());
        }
        r2sym::NativeWorkerSummaryKind::SortMerge => {
            return Some("merge sorted record streams".to_string());
        }
        r2sym::NativeWorkerSummaryKind::NumericTransform => {
            return Some("compute numeric transform".to_string());
        }
        _ => {}
    }
    summary
        .memory_accesses
        .iter()
        .find_map(native_region_access_pseudocode)
}

fn native_region_summary_detail(summary: &r2sym::NativeRegionSummary) -> String {
    let mut parts = vec![
        format!("id=0x{:x}", summary.stable_id),
        format!("anchor=0x{:x}", summary.anchor),
        format!("blocks={}", summary.blocks.len()),
    ];
    if let Some(loop_summary) = summary.loop_summary.as_ref() {
        parts.push(native_region_loop_detail(loop_summary));
    }
    if !summary.memory_accesses.is_empty() {
        parts.push(format!("accesses={}", summary.memory_accesses.len()));
    }
    if !summary.reductions.is_empty() {
        parts.push(format!("reductions={}", summary.reductions.len()));
    }
    if let Some(parser) = summary.parser.as_ref() {
        parts.push(format!("parser={}", native_parser_summary_label(parser)));
        if let Some(arg) = parser.cursor_arg {
            parts.push(format!("cursor=arg{arg}"));
        }
    }
    let evidence = format!("{:?}/{:?}", summary.confidence, summary.evidence.coverage);
    format!(
        "{}: {} evidence={}",
        native_worker_summary_kind_label(summary.kind),
        parts.join(" "),
        evidence
    )
}

pub fn semantic_fallback_comment(
    func_name: &str,
    semantic_artifact: Option<&r2sym::SemanticArtifact>,
) -> Option<String> {
    let function_facts = r2types::FunctionFacts::new(
        r2types::FunctionTypeFacts::default(),
        semantic_artifact.cloned(),
    );
    consumer_fallback::semantic_fallback_comment(func_name, &function_facts)
}

pub fn preferred_semantic_fallback_comment(
    func_name: &str,
    semantic_artifact: Option<&r2sym::SemanticArtifact>,
) -> Option<String> {
    let function_facts = r2types::FunctionFacts::new(
        r2types::FunctionTypeFacts::default(),
        semantic_artifact.cloned(),
    );
    planner::preferred_semantic_fallback_comment(func_name, &function_facts)
}

pub fn detached_semantic_linearization_reason(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<String> {
    planner::detached_semantic_linearization_reason(func_name, blocks, function_facts)
}

pub fn detached_semantic_route_plan(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<SemanticRoutePlan> {
    planner::detached_semantic_route_plan(func_name, blocks, function_facts)
}

#[cfg_attr(not(test), allow(dead_code))]
fn preferred_semantic_linearization_reason(
    func_name: &str,
    semantic_artifact: Option<&r2sym::SemanticArtifact>,
    cfg_summary: &r2ssa::CFGRiskSummary,
) -> Option<String> {
    let function_facts = r2types::FunctionFacts::new(
        r2types::FunctionTypeFacts::default(),
        semantic_artifact.cloned(),
    );
    planner::preferred_semantic_linearization_reason(func_name, &function_facts, cfg_summary)
}

#[cfg_attr(not(test), allow(dead_code))]
fn preferred_semantic_structuring_reason(
    func_name: &str,
    semantic_artifact: Option<&r2sym::SemanticArtifact>,
    cfg_summary: &r2ssa::CFGRiskSummary,
) -> Option<String> {
    let function_facts = r2types::FunctionFacts::new(
        r2types::FunctionTypeFacts::default(),
        semantic_artifact.cloned(),
    );
    planner::preferred_semantic_structuring_reason(func_name, &function_facts, cfg_summary)
}

fn preferred_semantic_worker_reason(cfg_summary: &r2ssa::CFGRiskSummary) -> String {
    planner::preferred_semantic_worker_reason(cfg_summary)
}

pub fn cfg_guard_reason_from_summary(summary: &r2ssa::CFGRiskSummary) -> Option<String> {
    planner::cfg_guard_reason_from_summary(summary)
}

pub fn cfg_guard_reason(blocks: &[R2ILBlock]) -> Option<String> {
    planner::cfg_guard_reason(blocks)
}

pub fn block_guard_fallback_comment(func_name: &str, blocks: usize, max_blocks: usize) -> String {
    planner::block_guard_fallback_comment(func_name, blocks, max_blocks)
}

pub fn artifact_guard_fallback_comment(func_name: &str, reason: &str) -> String {
    planner::artifact_guard_fallback_comment(func_name, reason)
}

pub fn render_semantic_worker_linearization(
    plan: &r2types::TypeWritebackPlan,
    semantic_artifact: Option<&r2sym::SemanticArtifact>,
    reason: &str,
) -> String {
    consumer_linear::render_semantic_worker_linearization(plan, semantic_artifact, reason)
}

pub fn render_vm_semantic_summary(
    func_name: &str,
    function_facts: &FunctionFacts,
) -> Option<String> {
    consumer_vm::render_vm_semantic_summary(
        func_name,
        &function_facts.types,
        function_facts.semantics.as_ref()?,
    )
}

pub fn render_semantic_worker_summary(
    func_name: &str,
    function_facts: &FunctionFacts,
    route: &SemanticRoutePlan,
    config: DecompilerConfig,
) -> Option<String> {
    Decompiler::new(config).semantic_worker_summary_output_for_route(
        func_name,
        function_facts,
        route,
    )
}

fn append_summary_return_if_needed(
    body: &mut Vec<CStmt>,
    function_facts: &FunctionFacts,
    semantic_artifact: &r2sym::SemanticArtifact,
) {
    if summary_non_void_return_type(function_facts, semantic_artifact).is_none() {
        return;
    }
    if body.iter().any(summary_stmt_contains_return) {
        return;
    }
    if let Some(expr) = semantic_summary_return_expr(function_facts, semantic_artifact) {
        body.push(CStmt::Return(Some(expr)));
    } else {
        body.push(CStmt::comment(
            "summary return unresolved; value intentionally not reconstructed".to_string(),
        ));
    }
}

fn append_semantic_summary_return_to_function_if_needed(
    func: &mut CFunction,
    function_facts: &FunctionFacts,
) {
    if matches!(func.ret_type, CType::Void | CType::Unknown) {
        return;
    }
    if func.body.iter().any(summary_stmt_contains_return) {
        return;
    }
    let Some(semantic_artifact) = function_facts.semantic_artifact() else {
        return;
    };
    if let Some(expr) = semantic_summary_return_expr(function_facts, semantic_artifact) {
        func.body.push(CStmt::Return(Some(expr)));
    } else {
        func.body.push(CStmt::comment(
            "summary return unresolved; value intentionally not reconstructed".to_string(),
        ));
    }
}

fn summary_non_void_return_type(
    function_facts: &FunctionFacts,
    _semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<CType> {
    function_facts
        .types
        .merged_signature
        .as_ref()
        .and_then(|sig| sig.ret_type.as_ref())
        .map(type_like_to_ctype)
        .filter(|ty| !matches!(ty, CType::Void | CType::Unknown))
}

fn summary_stmt_contains_return(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Return(_) => true,
        CStmt::Block(stmts) => stmts.iter().any(summary_stmt_contains_return),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            summary_stmt_contains_return(then_body)
                || else_body
                    .as_ref()
                    .is_some_and(|body| summary_stmt_contains_return(body))
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            summary_stmt_contains_return(body)
        }
        CStmt::For { init, body, .. } => {
            init.as_ref()
                .is_some_and(|stmt| summary_stmt_contains_return(stmt))
                || summary_stmt_contains_return(body)
        }
        CStmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .any(|case| case.body.iter().any(summary_stmt_contains_return))
                || default
                    .as_ref()
                    .is_some_and(|stmts| stmts.iter().any(summary_stmt_contains_return))
        }
        _ => false,
    }
}

fn semantic_summary_return_expr(
    function_facts: &FunctionFacts,
    _semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<CExpr> {
    summary_rollup_return_expr(function_facts)
}

fn summary_rollup_return_expr(function_facts: &FunctionFacts) -> Option<CExpr> {
    let relation = function_facts
        .summary_rollup()?
        .root_return_relation
        .as_ref()?;
    match relation {
        r2ssa::SummaryReturnRelation::Unknown | r2ssa::SummaryReturnRelation::Void => None,
        r2ssa::SummaryReturnRelation::Arg(index) => {
            Some(CExpr::var(summary_return_arg_name(function_facts, *index)))
        }
        r2ssa::SummaryReturnRelation::Const(value) => Some(CExpr::uint(*value)),
        r2ssa::SummaryReturnRelation::HeapAlloc => Some(CExpr::var("allocated_memory")),
        r2ssa::SummaryReturnRelation::Global(address) => {
            Some(CExpr::var(format!("global_{address:x}")))
        }
    }
}

fn summary_return_arg_name(function_facts: &FunctionFacts, index: usize) -> String {
    function_facts
        .types
        .merged_signature
        .as_ref()
        .and_then(|signature| signature.params.get(index))
        .map(|param| param.name.trim())
        .filter(|name| !name.is_empty())
        .map(str::to_string)
        .unwrap_or_else(|| format!("arg{index}"))
}

fn rewrite_summary_arg_labels(output: String, type_facts: &FunctionTypeFacts) -> String {
    let Some(signature) = type_facts.merged_signature.as_ref() else {
        return output;
    };
    let mut replacements: Vec<Option<String>> = Vec::new();
    for (idx, param) in signature.params.iter().enumerate() {
        let name = param.name.trim();
        if name.is_empty() || is_generic_arg_name(name) {
            continue;
        }
        if replacements.len() <= idx {
            replacements.resize(idx + 1, None);
        }
        replacements[idx] = Some(name.to_string());
    }
    let bytes = output.as_bytes();
    let mut rewritten = String::with_capacity(output.len());
    let mut copied = 0usize;
    let mut cursor = 0usize;
    while cursor < output.len() {
        if cursor + 3 <= output.len()
            && &bytes[cursor..cursor + 3] == b"arg"
            && (cursor == 0 || !is_summary_ident_byte(bytes[cursor - 1]))
        {
            let mut end = cursor + 3;
            while end < output.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > cursor + 3
                && (end == output.len() || !bytes[end].is_ascii_alphanumeric())
                && let Ok(index) = output[cursor + 3..end].parse::<usize>()
            {
                let replacement = replacements
                    .get(index)
                    .and_then(Option::as_ref)
                    .cloned()
                    .or_else(|| {
                        (index >= signature.params.len()).then(|| format!("summary_input{index}"))
                    });
                if let Some(name) = replacement {
                    rewritten.push_str(&output[copied..cursor]);
                    rewritten.push_str(&name);
                    copied = end;
                    cursor = end;
                    continue;
                }
            }
        }

        cursor += output[cursor..]
            .chars()
            .next()
            .map(char::len_utf8)
            .unwrap_or(1);
    }
    rewritten.push_str(&output[copied..]);
    rewritten
}

fn is_summary_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn merge_params_with_external_signature(
    recovered_params: Vec<ast::CParam>,
    signature: Option<&FunctionSignatureSpec>,
) -> Vec<ast::CParam> {
    let Some(signature) = signature else {
        return recovered_params;
    };

    if signature.params.is_empty() {
        return recovered_params;
    }

    let signature_is_authoritative = signature.ret_type.is_some()
        || signature
            .params
            .iter()
            .any(|param| param.ty.is_some() || !is_generic_arg_name(&param.name));
    let target_len = if signature_is_authoritative {
        signature.params.len()
    } else {
        recovered_params.len().max(signature.params.len())
    };
    (0..target_len)
        .map(|idx| {
            let fallback_name = format!("arg{}", idx + 1);
            let mut param = recovered_params.get(idx).cloned().unwrap_or(ast::CParam {
                ty: CType::Int(32),
                name: fallback_name,
            });

            if let Some(ext) = signature.params.get(idx) {
                if !is_generic_arg_name(&ext.name) {
                    param.name = ext.name.clone();
                }
                if let Some(ext_ty) = &ext.ty {
                    param.ty = type_like_to_ctype(ext_ty);
                }
            }

            param
        })
        .collect()
}

fn register_alias_names(reg_name: &str) -> Vec<String> {
    let lower = reg_name.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return Vec::new();
    }

    match lower.as_str() {
        "rdi" | "edi" | "di" | "dil" => {
            return vec!["rdi", "edi", "di", "dil"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "rsi" | "esi" | "si" | "sil" => {
            return vec!["rsi", "esi", "si", "sil"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "rdx" | "edx" | "dx" | "dl" => {
            return vec!["rdx", "edx", "dx", "dl"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        "rcx" | "ecx" | "cx" | "cl" => {
            return vec!["rcx", "ecx", "cx", "cl"]
                .into_iter()
                .map(str::to_string)
                .collect();
        }
        _ => {}
    }

    for base in ["r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"] {
        if lower == base
            || lower == format!("{base}d")
            || lower == format!("{base}w")
            || lower == format!("{base}b")
        {
            return vec![
                base.to_string(),
                format!("{base}d"),
                format!("{base}w"),
                format!("{base}b"),
            ];
        }
    }

    if let Some(rest) = lower.strip_prefix('x')
        && rest.chars().all(|c| c.is_ascii_digit())
    {
        return vec![lower.clone(), format!("w{rest}")];
    }
    if let Some(rest) = lower.strip_prefix('w')
        && rest.chars().all(|c| c.is_ascii_digit())
    {
        return vec![format!("x{rest}"), lower];
    }

    vec![lower]
}

pub fn normalize_sig_arch_name(arch: Option<&r2il::ArchSpec>) -> Option<String> {
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

fn build_param_register_aliases(
    params: &[ast::CParam],
    recovered_params: &[(r2ssa::SSAVar, ast::CParam)],
    register_params: &[ExternalRegisterParamSpec],
    abi_arg_regs: &[String],
) -> std::collections::HashMap<String, String> {
    let mut aliases = std::collections::HashMap::new();

    for (idx, reg_name) in abi_arg_regs.iter().enumerate() {
        let Some(param) = params.get(idx) else {
            continue;
        };
        for alias in register_alias_names(reg_name) {
            aliases.insert(alias, param.name.clone());
        }
    }

    for (idx, (ssa_var, _)) in recovered_params.iter().enumerate() {
        if let Some(param) = params.get(idx) {
            aliases.insert(ssa_var.name.to_ascii_lowercase(), param.name.clone());
        }
    }

    for (idx, reg_param) in register_params.iter().enumerate() {
        let Some(param) = params.get(idx) else {
            continue;
        };
        for alias in register_alias_names(&reg_param.reg) {
            aliases.entry(alias).or_insert_with(|| param.name.clone());
        }
    }

    aliases
}

/// Decompiler configuration.
#[derive(Debug, Clone)]
pub struct DecompilerConfig {
    /// Code generation configuration.
    pub codegen: CodeGenConfig,
    /// Pointer size in bits.
    pub ptr_size: u32,
    /// Stack pointer register name.
    pub sp_name: String,
    /// Frame pointer register name.
    pub fp_name: String,
    /// Ordered argument registers for the active ABI.
    pub arg_regs: Vec<String>,
    /// Return-value registers for the active ABI.
    pub ret_regs: Vec<String>,
    /// Caller-saved registers for the active ABI.
    pub caller_saved_regs: HashSet<String>,
    /// Soft cap for function blocks before forcing fallback.
    pub max_blocks: usize,
}

impl Default for DecompilerConfig {
    fn default() -> Self {
        Self {
            codegen: CodeGenConfig::default(),
            ptr_size: 64,
            sp_name: "rsp".to_string(),
            fp_name: "rbp".to_string(),
            arg_regs: vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ],
            ret_regs: vec![
                "rax".to_string(),
                "eax".to_string(),
                "xmm0".to_string(),
                "xmm0_qa".to_string(),
                "xmm0_qb".to_string(),
                "st0".to_string(),
            ],
            caller_saved_regs: ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            max_blocks: 200,
        }
    }
}

impl DecompilerConfig {
    pub fn for_arch_name(arch_name: &str, ptr_bits: u32) -> Self {
        match (arch_name, ptr_bits) {
            ("x86", 32) | ("x86-32", _) => Self::x86(),
            ("x86-64", _) | ("x86_64", _) | ("x64", _) | ("amd64", _) => Self::x86_64(),
            ("arm", _) | ("ARM", _) if ptr_bits == 32 => Self::arm(),
            ("aarch64", _) | ("arm64", _) | ("ARM64", _) => Self::aarch64(),
            ("riscv32", _) | ("rv32", _) | ("rv32gc", _) => Self::riscv32(),
            ("riscv64", _) | ("rv64", _) | ("rv64gc", _) => Self::riscv64(),
            ("riscv", _) if ptr_bits == 32 => Self::riscv32(),
            ("riscv", _) => Self::riscv64(),
            _ => Self {
                ptr_size: ptr_bits,
                ..Self::default()
            },
        }
    }

    pub fn for_arch(arch: Option<&r2il::ArchSpec>) -> (String, u32, Self) {
        let arch_name = normalize_sig_arch_name(arch).unwrap_or_else(|| "unknown".to_string());
        let ptr_bits = arch.map(|spec| spec.addr_size * 8).unwrap_or(64);
        let config = Self::for_arch_name(&arch_name, ptr_bits);
        (arch_name, ptr_bits, config)
    }

    /// Create a configuration for 32-bit x86.
    pub fn x86() -> Self {
        Self {
            ptr_size: 32,
            sp_name: "esp".to_string(),
            fp_name: "ebp".to_string(),
            arg_regs: vec![],
            ret_regs: vec!["eax".to_string(), "xmm0".to_string(), "st0".to_string()],
            caller_saved_regs: ["eax", "ecx", "edx"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for 64-bit x86.
    pub fn x86_64() -> Self {
        Self::default()
    }

    /// Create a configuration for ARM.
    pub fn arm() -> Self {
        Self {
            ptr_size: 32,
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: ["r0", "r1", "r2", "r3"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["r0".to_string()],
            caller_saved_regs: ["r0", "r1", "r2", "r3", "r12", "lr", "ip"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for AArch64.
    pub fn aarch64() -> Self {
        Self {
            ptr_size: 64,
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["x0".to_string(), "w0".to_string()],
            caller_saved_regs: [
                "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12",
                "x13", "x14", "x15", "x16", "x17",
            ]
            .into_iter()
            .map(str::to_string)
            .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for RISC-V RV32.
    pub fn riscv32() -> Self {
        Self {
            ptr_size: 32,
            sp_name: "sp".to_string(),
            fp_name: "s0".to_string(),
            arg_regs: ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["a0".to_string()],
            caller_saved_regs: [
                "ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a0", "a1", "a2", "a3", "a4", "a5",
                "a6", "a7",
            ]
            .into_iter()
            .map(str::to_string)
            .collect(),
            ..Default::default()
        }
    }

    /// Create a configuration for RISC-V RV64.
    pub fn riscv64() -> Self {
        Self {
            ptr_size: 64,
            sp_name: "sp".to_string(),
            fp_name: "s0".to_string(),
            arg_regs: ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ret_regs: vec!["a0".to_string()],
            caller_saved_regs: [
                "ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a0", "a1", "a2", "a3", "a4", "a5",
                "a6", "a7",
            ]
            .into_iter()
            .map(str::to_string)
            .collect(),
            ..Default::default()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalStructFieldAccess {
    pub arg_index: usize,
    pub field_offset: u64,
    pub access_size: u32,
    pub is_write: bool,
}

#[derive(Debug, Clone, Default)]
pub struct DecompilerContext {
    /// Function address to name mapping.
    pub function_names: std::collections::HashMap<u64, String>,
    /// String literal addresses.
    pub strings: std::collections::HashMap<u64, String>,
    /// Symbol/global variable names.
    pub symbols: std::collections::HashMap<u64, String>,
    /// Canonical combined type and semantic facts.
    pub function_facts: FunctionFacts,
    /// Route selected by the session engine. When absent, r2dec renders the
    /// standard SSA path; route selection policy is engine-owned.
    pub semantic_route: Option<SemanticRoutePlan>,
    /// Optional engine-owned decision for whether local type inference should run.
    pub skip_runtime_type_inference: Option<bool>,
    /// Optional engine-owned decision for whether prepared semantic facts should
    /// be used during folding.
    pub use_prepared_semantic_view: Option<bool>,
}

impl DecompilerContext {
    fn canonicalize_function_facts(mut function_facts: FunctionFacts) -> FunctionFacts {
        function_facts.types = function_facts.types.canonicalized();
        function_facts.refresh_plans();
        function_facts
    }

    pub fn type_facts(&self) -> &FunctionTypeFacts {
        &self.function_facts.types
    }

    pub fn type_facts_mut(&mut self) -> &mut FunctionTypeFacts {
        &mut self.function_facts.types
    }

    pub fn semantic_artifact(&self) -> Option<&r2sym::SemanticArtifact> {
        self.function_facts.semantics.as_ref()
    }

    pub fn from_analysis_inputs(
        mut type_facts: FunctionTypeFacts,
        function_names: std::collections::HashMap<u64, String>,
        strings: std::collections::HashMap<u64, String>,
        symbols: std::collections::HashMap<u64, String>,
        ptr_bits: u32,
    ) -> Self {
        r2types::enrich_known_function_signatures_from_names(
            &mut type_facts,
            &function_names,
            ptr_bits,
        );
        r2types::enrich_known_function_signatures_from_names(&mut type_facts, &symbols, ptr_bits);
        Self {
            function_names,
            strings,
            symbols,
            function_facts: FunctionFacts::new(type_facts.canonicalized(), None),
            semantic_route: None,
            skip_runtime_type_inference: None,
            use_prepared_semantic_view: None,
        }
    }

    pub fn from_function_facts(
        mut function_facts: FunctionFacts,
        function_names: std::collections::HashMap<u64, String>,
        strings: std::collections::HashMap<u64, String>,
        symbols: std::collections::HashMap<u64, String>,
        ptr_bits: u32,
    ) -> Self {
        r2types::enrich_known_function_signatures_from_names(
            &mut function_facts.types,
            &function_names,
            ptr_bits,
        );
        r2types::enrich_known_function_signatures_from_names(
            &mut function_facts.types,
            &symbols,
            ptr_bits,
        );
        Self {
            function_names,
            strings,
            symbols,
            function_facts: Self::canonicalize_function_facts(function_facts),
            semantic_route: None,
            skip_runtime_type_inference: None,
            use_prepared_semantic_view: None,
        }
    }

    pub fn with_function_names(
        mut self,
        function_names: std::collections::HashMap<u64, String>,
    ) -> Self {
        self.function_names = function_names;
        self
    }

    pub fn with_strings(mut self, strings: std::collections::HashMap<u64, String>) -> Self {
        self.strings = strings;
        self
    }

    pub fn with_symbols(mut self, symbols: std::collections::HashMap<u64, String>) -> Self {
        self.symbols = symbols;
        self
    }

    pub fn with_type_facts(mut self, type_facts: FunctionTypeFacts) -> Self {
        self.function_facts.types = type_facts.canonicalized();
        self.function_facts.refresh_plans();
        self
    }

    pub fn with_semantic_artifact(
        mut self,
        semantic_artifact: Option<r2sym::SemanticArtifact>,
    ) -> Self {
        self.function_facts.set_semantics(semantic_artifact);
        self
    }

    pub fn with_function_facts(mut self, function_facts: FunctionFacts) -> Self {
        self.function_facts = Self::canonicalize_function_facts(function_facts);
        self
    }

    pub fn with_semantic_route(mut self, route: Option<SemanticRoutePlan>) -> Self {
        self.semantic_route = route;
        self
    }

    pub fn with_runtime_type_inference_policy(mut self, skip: Option<bool>) -> Self {
        self.skip_runtime_type_inference = skip;
        self
    }

    pub fn with_prepared_semantic_view_policy(mut self, use_view: Option<bool>) -> Self {
        self.use_prepared_semantic_view = use_view;
        self
    }

    fn route_for(&self, func_name: &str, cfg_summary: &r2ssa::CFGRiskSummary) -> SemanticRoutePlan {
        let _ = (func_name, cfg_summary);
        self.semantic_route
            .clone()
            .unwrap_or(SemanticRoutePlan::Standard)
    }
}

#[derive(Debug, Clone)]
pub struct DecompilerInput {
    pub prepared_ssa: r2ssa::SsaArtifact,
    pub interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    pub context: DecompilerContext,
}

impl DecompilerInput {
    pub fn new(prepared_ssa: r2ssa::SsaArtifact, mut context: DecompilerContext) -> Self {
        context.function_facts =
            DecompilerContext::canonicalize_function_facts(context.function_facts);
        let interproc_summary_set = context.function_facts.interproc_summary_set().cloned();
        Self {
            prepared_ssa,
            interproc_summary_set,
            context,
        }
    }

    pub fn with_context(mut self, mut context: DecompilerContext) -> Self {
        context.function_facts =
            DecompilerContext::canonicalize_function_facts(context.function_facts);
        self.interproc_summary_set = context.function_facts.interproc_summary_set().cloned();
        self.context = context;
        self
    }

    pub fn with_interproc_summary_set(
        mut self,
        interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    ) -> Self {
        self.context.function_facts.summary_view =
            r2types::InterprocSummaryView::new(interproc_summary_set.clone());
        self.interproc_summary_set = interproc_summary_set;
        self
    }
}

/// The main decompiler.
pub struct Decompiler {
    config: DecompilerConfig,
    context: DecompilerContext,
}

impl Decompiler {
    /// Create a new decompiler with the given configuration.
    pub fn new(config: DecompilerConfig) -> Self {
        Self {
            config,
            context: DecompilerContext::default(),
        }
    }

    /// Set external context (function names, strings, symbols).
    pub fn with_context(mut self, mut context: DecompilerContext) -> Self {
        context.function_facts =
            DecompilerContext::canonicalize_function_facts(context.function_facts);
        self.context = context;
        self
    }

    /// Set function names for call target resolution.
    pub fn set_function_names(&mut self, names: std::collections::HashMap<u64, String>) {
        self.context.function_names = names;
    }

    /// Set string literals for address resolution.
    pub fn set_strings(&mut self, strings: std::collections::HashMap<u64, String>) {
        self.context.strings = strings;
    }

    /// Set symbol names for global variable resolution.
    pub fn set_symbols(&mut self, symbols: std::collections::HashMap<u64, String>) {
        self.context.symbols = symbols;
    }

    /// Set externally recovered known function signatures keyed by name.
    pub fn set_known_function_signatures<T>(
        &mut self,
        signatures: std::collections::HashMap<String, T>,
    ) where
        T: Into<FunctionType>,
    {
        self.context.type_facts_mut().known_function_signatures = signatures
            .into_iter()
            .map(|(name, sig)| (name, sig.into()))
            .collect();
    }

    /// Set externally recovered host type database.
    pub fn set_external_type_db(&mut self, external_type_db: ExternalTypeDb) {
        self.context.type_facts_mut().external_type_db = external_type_db;
    }

    /// Set externally recovered type facts.
    pub fn set_type_facts(&mut self, type_facts: FunctionTypeFacts) {
        self.context.function_facts.types = type_facts.canonicalized();
        self.context.function_facts.refresh_plans();
    }

    pub fn set_function_facts(&mut self, function_facts: FunctionFacts) {
        self.context = self.context.clone().with_function_facts(function_facts);
    }

    fn vm_summary_output_for_route(
        &self,
        func_name: &str,
        function_facts: &FunctionFacts,
        route: &planner::SemanticRoutePlan,
    ) -> Option<String> {
        match route {
            planner::SemanticRoutePlan::VmSummary { .. } => {
                crate::consumer_vm::render_vm_semantic_summary(
                    func_name,
                    &function_facts.types,
                    function_facts.semantics.as_ref()?,
                )
            }
            _ => None,
        }
    }

    /// Decompile an SSA function to C code.
    pub fn decompile(&self, func: &SSAFunction) -> String {
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let semantic_route = self.context.route_for(&func_name, &func.cfg_risk_summary());
        if let SemanticRoutePlan::FallbackComment { comment } = &semantic_route {
            return comment.clone();
        }
        if let Some(output) = self.vm_summary_output_for_route(
            &func_name,
            &self.context.function_facts,
            &semantic_route,
        ) {
            return output;
        }
        if let Some(output) = self.semantic_worker_summary_output_for_route(
            &func_name,
            &self.context.function_facts,
            &semantic_route,
        ) {
            return output;
        }
        // Build the C function
        let c_func = self.build_function(func);

        // Generate code
        let mut codegen = CodeGenerator::new(self.config.codegen.clone());
        codegen.generate_function(&c_func)
    }

    /// Decompile a prepared function with an explicit typed context payload.
    pub fn decompile_input(&self, input: &DecompilerInput) -> String {
        let func = input.prepared_ssa.function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let semantic_route = input
            .context
            .route_for(&func_name, &func.cfg_risk_summary());
        if let SemanticRoutePlan::FallbackComment { comment } = &semantic_route {
            return comment.clone();
        }
        if let Some(output) = self.vm_summary_output_for_route(
            &func_name,
            &input.context.function_facts,
            &semantic_route,
        ) {
            return output;
        }
        if let Some(output) = self.semantic_worker_summary_output_for_route(
            &func_name,
            &input.context.function_facts,
            &semantic_route,
        ) {
            return output;
        }
        let c_func = self.build_function_from_input(input);
        let mut codegen = CodeGenerator::new(self.config.codegen.clone());
        codegen.generate_function(&c_func)
    }

    /// Build a C function from a prepared function + typed context payload.
    pub fn build_function_from_input(&self, input: &DecompilerInput) -> CFunction {
        let decompiler = Self::new(self.config.clone()).with_context(input.context.clone());
        decompiler.build_function_internal(
            input.prepared_ssa.function(),
            Some(&input.prepared_ssa),
            input.interproc_summary_set.as_ref(),
        )
    }

    pub(crate) fn stmt_has_content(stmt: &CStmt) -> bool {
        match stmt {
            CStmt::Empty => false,
            CStmt::Block(stmts) => !stmts.is_empty(),
            _ => true,
        }
    }

    pub(crate) fn prepend_comment(stmt: CStmt, text: String) -> CStmt {
        let comment = CStmt::comment(text);
        match stmt {
            CStmt::Empty => CStmt::Block(vec![comment]),
            CStmt::Block(mut stmts) => {
                stmts.insert(0, comment);
                CStmt::Block(stmts)
            }
            other => CStmt::Block(vec![comment, other]),
        }
    }

    fn semantic_vm_summary_comment(&self) -> Option<String> {
        let vm_body = self.context.semantic_artifact()?.vm_body()?;
        let vm_step = vm_body
            .step_summary
            .as_ref()
            .or(vm_body.transfer_summary.as_ref())?;
        let exact_transfers = vm_step
            .transfers
            .iter()
            .filter(|transfer| transfer.evidence().allows_hard_proof())
            .count();
        let likely_transfers = vm_step
            .transfers
            .iter()
            .filter(|transfer| matches!(transfer.confidence(), r2sym::SemanticConfidence::Likely))
            .count();
        let heuristic_transfers = vm_step
            .transfers
            .iter()
            .filter(|transfer| {
                matches!(transfer.confidence(), r2sym::SemanticConfidence::Heuristic)
            })
            .count();
        let redispatch_transfers = vm_step
            .transfers
            .iter()
            .filter(|transfer| transfer.redispatch)
            .count();
        let returning_transfers = vm_step
            .transfers
            .iter()
            .filter(|transfer| transfer.may_return)
            .count();
        let selector_updates = vm_step
            .transfers
            .iter()
            .filter(|transfer| transfer.selector_update.is_some())
            .count();
        let exact_exit_guards = vm_step
            .transfers
            .iter()
            .flat_map(|transfer| transfer.exit_guards.iter())
            .filter(|guard| guard.guard.evidence().allows_hard_proof())
            .count();
        let total_read_effects: usize = vm_step
            .handler_memory_read_effects
            .values()
            .map(Vec::len)
            .sum();
        let total_write_effects: usize = vm_step
            .handler_memory_write_effects
            .values()
            .map(Vec::len)
            .sum();
        let total_reads: usize = vm_step.handler_memory_reads.values().copied().sum();
        let total_writes: usize = vm_step.handler_memory_writes.values().copied().sum();

        let mut out = String::new();
        let _ = writeln!(&mut out, "r2dec semantic summary: vm_summary");
        let _ = writeln!(
            &mut out,
            "kind={} dispatch_header=0x{:x} loop_header=0x{:x} selector={} targets={} default_target={} latches={} step_blocks={} transfers={} exact_transfers={} likely_transfers={} heuristic_transfers={} redispatch_transfers={} returning_transfers={} selector_updates={} exact_exit_guards={} total_reads={} total_writes={} total_read_effects={} total_write_effects={}",
            format_vm_summary_kind(vm_step.kind),
            vm_step.dispatch_header,
            vm_step.loop_header,
            vm_step.selector.as_deref().unwrap_or("<unknown>"),
            vm_step.dispatch_targets.len(),
            vm_step
                .default_target
                .map(|target| format!("0x{:x}", target))
                .unwrap_or_else(|| "none".to_string()),
            vm_step.loop_latches.len(),
            vm_step.step_blocks.len(),
            vm_step.transfers.len(),
            exact_transfers,
            likely_transfers,
            heuristic_transfers,
            redispatch_transfers,
            returning_transfers,
            selector_updates,
            exact_exit_guards,
            total_reads,
            total_writes,
            total_read_effects,
            total_write_effects,
        );
        if !vm_step.state_inputs.is_empty() || !vm_step.state_outputs.is_empty() {
            let _ = writeln!(
                &mut out,
                "state_inputs=[{}] state_outputs=[{}]",
                vm_step.state_inputs.join(", "),
                vm_step.state_outputs.join(", "),
            );
        }

        let transfer_preview = vm_step.transfers.iter().take(4).collect::<Vec<_>>();
        if !transfer_preview.is_empty() {
            for transfer in transfer_preview {
                let selector_update = transfer
                    .selector_update
                    .as_ref()
                    .map(|update| format!("{}={}", update.output, update.expr))
                    .unwrap_or_else(|| "none".to_string());
                let _ = writeln!(
                    &mut out,
                    "transfer handler=0x{:x} cases={} blocks={} exits={} exit_guards={} updates={} selector_update={} reads={} writes={} exact={} confidence={:?} reasons={} residual_guards={} residual_memory={} redispatch={} return={} truncated={}",
                    transfer.handler_target,
                    format_vm_target_list(&transfer.case_values),
                    format_vm_target_list(&transfer.region_blocks),
                    format_vm_target_list(&transfer.exit_targets),
                    format_vm_guarded_exits(&transfer.exit_guards),
                    format_vm_state_updates(&transfer.state_updates),
                    selector_update,
                    format_vm_memory_conditions(&transfer.memory_reads),
                    format_vm_memory_conditions(&transfer.memory_writes),
                    transfer.evidence().allows_hard_proof(),
                    transfer.confidence(),
                    format_args!("{:?}", transfer.evidence().reasons),
                    transfer.residual_guards,
                    transfer.residual_memory_effects,
                    transfer.redispatch,
                    transfer.may_return,
                    transfer.truncated,
                );
            }
        }

        let mut preview_handlers = vm_step.handler_regions.keys().copied().collect::<Vec<_>>();
        preview_handlers.sort_unstable();
        for handler in preview_handlers.into_iter().take(4) {
            let regions = vm_step
                .handler_regions
                .get(&handler)
                .map(|regions| format_vm_target_list(regions))
                .unwrap_or_else(|| "[]".to_string());
            let cases = vm_step
                .case_values_by_target
                .get(&handler)
                .map(|values| format_vm_target_list(values))
                .unwrap_or_else(|| "[]".to_string());
            let updates = vm_step
                .handler_state_updates
                .get(&handler)
                .map(|updates| format_vm_state_updates(updates))
                .unwrap_or_else(|| "[]".to_string());
            let inputs = vm_step
                .handler_state_inputs
                .get(&handler)
                .map(|values| format!("[{}]", values.join(", ")))
                .unwrap_or_else(|| "[]".to_string());
            let outputs = vm_step
                .handler_state_outputs
                .get(&handler)
                .map(|values| format!("[{}]", values.join(", ")))
                .unwrap_or_else(|| "[]".to_string());
            let exits = vm_step
                .handler_exit_targets
                .get(&handler)
                .map(|values| format_vm_target_list(values))
                .unwrap_or_else(|| "[]".to_string());
            let guards = vm_step
                .handler_exit_guards
                .get(&handler)
                .map(|values| format_vm_guarded_exits(values))
                .unwrap_or_else(|| "[]".to_string());
            let read_effects = vm_step
                .handler_memory_read_effects
                .get(&handler)
                .map(|values| format_vm_memory_conditions(values))
                .unwrap_or_else(|| "[]".to_string());
            let write_effects = vm_step
                .handler_memory_write_effects
                .get(&handler)
                .map(|values| format_vm_memory_conditions(values))
                .unwrap_or_else(|| "[]".to_string());
            let _ = writeln!(
                &mut out,
                "handler 0x{:x}: regions={} cases={} inputs={} outputs={} updates={} reads={} writes={} read_effects={} write_effects={} calls={} branches={} exits={} guards={}",
                handler,
                regions,
                cases,
                inputs,
                outputs,
                updates,
                vm_step
                    .handler_memory_reads
                    .get(&handler)
                    .copied()
                    .unwrap_or(0),
                vm_step
                    .handler_memory_writes
                    .get(&handler)
                    .copied()
                    .unwrap_or(0),
                read_effects,
                write_effects,
                vm_step.handler_calls.get(&handler).copied().unwrap_or(0),
                vm_step
                    .handler_conditional_branches
                    .get(&handler)
                    .copied()
                    .unwrap_or(0),
                exits,
                guards,
            );
        }

        if !vm_step.redispatch_handlers.is_empty()
            || !vm_step.returning_handlers.is_empty()
            || !vm_step.truncated_handlers.is_empty()
        {
            let _ = writeln!(
                &mut out,
                "redispatch_handlers={} returning_handlers={} truncated_handlers={}",
                format_vm_target_list(&vm_step.redispatch_handlers),
                format_vm_target_list(&vm_step.returning_handlers),
                format_vm_target_list(&vm_step.truncated_handlers),
            );
        }

        Some(out.trim_end().to_string())
    }

    fn semantic_worker_summary_output_for_route(
        &self,
        func_name: &str,
        function_facts: &FunctionFacts,
        route: &planner::SemanticRoutePlan,
    ) -> Option<String> {
        consumer_summary::render_for_route(
            func_name,
            function_facts,
            route,
            self.config.codegen.clone(),
        )
    }

    fn linearize_function_body(
        &self,
        func: &SSAFunction,
        fold_ctx: &FoldingContext<'_>,
    ) -> Vec<CStmt> {
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let mut stmts = Vec::new();

        for block in &blocks {
            stmts.push(CStmt::Label(Self::linear_block_label(block.addr)));
            for stmt in fold_ctx.fold_block(block, block.addr) {
                if !matches!(stmt, CStmt::Empty) {
                    stmts.push(stmt);
                }
            }
            if let Some(terminator_stmt) = Self::linearized_terminator_stmt(func, fold_ctx, block) {
                stmts.push(terminator_stmt);
            }
        }

        stmts
    }

    fn linear_block_label(addr: u64) -> String {
        format!("loc_{addr:x}")
    }

    fn linearized_terminator_stmt(
        func: &SSAFunction,
        fold_ctx: &FoldingContext<'_>,
        block: &r2ssa::FunctionSSABlock,
    ) -> Option<CStmt> {
        let terminator = &func.cfg().get_block(block.addr)?.terminator;
        match terminator {
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                let cond = fold_ctx
                    .extract_condition_from_block(block)
                    .unwrap_or(CExpr::IntLit(1));
                Some(CStmt::if_stmt(
                    cond,
                    CStmt::Goto(Self::linear_block_label(*true_target)),
                    Some(CStmt::Goto(Self::linear_block_label(*false_target))),
                ))
            }
            BlockTerminator::Branch { target } | BlockTerminator::Fallthrough { next: target } => {
                Some(CStmt::Goto(Self::linear_block_label(*target)))
            }
            BlockTerminator::Call {
                fallthrough: Some(target),
                ..
            }
            | BlockTerminator::IndirectCall {
                fallthrough: Some(target),
            } => Some(CStmt::Goto(Self::linear_block_label(*target))),
            BlockTerminator::Switch { cases, default } => {
                let mut stmts = Vec::new();
                for (value, target) in cases {
                    stmts.push(CStmt::comment(format!(
                        "case {value}: goto {};",
                        Self::linear_block_label(*target)
                    )));
                }
                if let Some(target) = default {
                    stmts.push(CStmt::comment(format!(
                        "default: goto {};",
                        Self::linear_block_label(*target)
                    )));
                }
                (!stmts.is_empty()).then_some(CStmt::Block(stmts))
            }
            BlockTerminator::IndirectBranch => Some(CStmt::comment(
                "indirect branch target unresolved".to_string(),
            )),
            BlockTerminator::Call {
                fallthrough: None, ..
            }
            | BlockTerminator::IndirectCall { fallthrough: None }
            | BlockTerminator::Return
            | BlockTerminator::None => None,
        }
    }

    /// Build a C function from an SSA function.
    pub fn build_function(&self, func: &SSAFunction) -> CFunction {
        self.build_function_internal(func, None, None)
    }

    fn build_function_internal(
        &self,
        func: &SSAFunction,
        prepared: Option<&r2ssa::SsaArtifact>,
        interproc_summary_set: Option<&r2ssa::InterprocSummarySet>,
    ) -> CFunction {
        // Materialize phis on non-critical edges to reduce SSA artifacts in output.
        let normalized_func = normalize::materialize_phis(func);
        let func = &normalized_func;

        // Recover variables
        let mut var_recovery = VariableRecovery::new_with_abi(
            &self.config.sp_name,
            &self.config.fp_name,
            self.config.ptr_size,
            self.config.arg_regs.clone(),
            self.config.ret_regs.clone(),
        );
        var_recovery.set_type_facts(self.context.type_facts().clone());
        var_recovery.recover(func);

        let skip_runtime_type_inference =
            self.context.skip_runtime_type_inference.unwrap_or_else(|| {
                should_skip_runtime_type_inference(
                    prepared,
                    self.context.type_facts(),
                    &self.context.function_facts,
                )
            });
        let type_inference = (!skip_runtime_type_inference).then(|| {
            let mut type_inference = TypeInference::new_with_abi(
                self.config.ptr_size,
                self.config.arg_regs.clone(),
                self.config.ret_regs.clone(),
            );
            if !self.context.function_names.is_empty() {
                type_inference.set_function_names(self.context.function_names.clone());
            }
            type_inference
                .set_external_signature(self.context.type_facts().merged_signature.clone());
            for (name, signature) in &self.context.type_facts().known_function_signatures {
                type_inference.add_function_type(name, signature.clone());
            }
            type_inference.set_external_stack_slots(self.context.type_facts().stack_slots.clone());
            if !self
                .context
                .type_facts()
                .external_type_db
                .structs
                .is_empty()
                || !self.context.type_facts().external_type_db.unions.is_empty()
                || !self.context.type_facts().external_type_db.enums.is_empty()
            {
                type_inference
                    .set_external_type_db(self.context.type_facts().external_type_db.clone());
            }
            if let Some(prepared) = prepared {
                type_inference.set_prepared_ssa(prepared);
            } else {
                type_inference.set_decompile_prep_facts(func.decompile_prep_facts());
            }
            type_inference.infer_function(func);
            type_inference
        });
        let mut type_hints = if let Some(type_inference) = type_inference.as_ref() {
            type_inference
                .var_type_hints()
                .into_iter()
                .map(|(name, ty)| (name, type_like_to_ctype(&ty)))
                .collect::<std::collections::HashMap<_, _>>()
        } else {
            seed_runtime_type_hints_from_facts_and_recovery(
                self.context.type_facts(),
                &var_recovery,
            )
        };
        let combined_type_oracle = type_inference
            .as_ref()
            .and_then(TypeInference::combined_type_oracle);
        let type_oracle = combined_type_oracle
            .as_ref()
            .map(|oracle| oracle as &dyn TypeOracle);

        let known_function_signatures = self
            .context
            .type_facts()
            .known_function_signatures
            .iter()
            .map(|(name, ty)| (normalize_callee_name(name), ty.clone()))
            .collect::<std::collections::HashMap<_, _>>();

        let recovered_param_infos: Vec<_> = var_recovery
            .parameters()
            .iter()
            .map(|v| {
                (
                    v.ssa_var.clone(),
                    ast::CParam {
                        ty: type_inference
                            .as_ref()
                            .map(|type_inference| {
                                type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                            })
                            .unwrap_or_else(|| v.ty.clone()),
                        name: v.name.clone(),
                    },
                )
            })
            .collect();
        let params = merge_params_with_external_signature(
            recovered_param_infos
                .iter()
                .map(|(_, param)| param.clone())
                .collect(),
            self.context.type_facts().merged_signature.as_ref(),
        );
        let param_register_aliases = build_param_register_aliases(
            &params,
            &recovered_param_infos,
            &self.context.type_facts().register_params,
            &self.config.arg_regs,
        );
        for (idx, (_ssa_var, _)) in recovered_param_infos.iter().enumerate() {
            let Some(param) = params.get(idx) else {
                continue;
            };
            let param_ty = param.ty.clone();
            type_hints.insert(param.name.clone(), param_ty.clone());
            type_hints.insert(param.name.to_ascii_lowercase(), param_ty);
        }
        for (reg_alias, param_name) in &param_register_aliases {
            let Some(param) = params.iter().find(|param| param.name == *param_name) else {
                continue;
            };
            type_hints
                .entry(reg_alias.clone())
                .or_insert_with(|| param.ty.clone());
            type_hints
                .entry(reg_alias.to_ascii_lowercase())
                .or_insert_with(|| param.ty.clone());
        }
        let inferred_ret_type = type_inference
            .as_ref()
            .map(|type_inference| self.infer_return_type(func, type_inference))
            .or_else(|| {
                self.context
                    .type_facts()
                    .merged_signature
                    .as_ref()
                    .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
            })
            .unwrap_or(CType::Unknown);
        let signature_ret_type = self
            .context
            .type_facts()
            .merged_signature
            .as_ref()
            .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype));
        let fold_arch = FoldArchConfig {
            ptr_size: self.config.ptr_size,
            sp_name: self.config.sp_name.clone(),
            fp_name: self.config.fp_name.clone(),
            ret_reg_name: self
                .config
                .ret_regs
                .first()
                .cloned()
                .unwrap_or_else(|| "rax".to_string()),
            arg_regs: self.config.arg_regs.clone(),
            caller_saved_regs: self.config.caller_saved_regs.clone(),
        };
        let use_prepared_semantic_view =
            self.context.use_prepared_semantic_view.unwrap_or_else(|| {
                should_use_prepared_semantic_view(prepared, &self.context.function_facts)
            });
        let prepared_semantic_view = use_prepared_semantic_view.then(|| {
            analysis::PreparedSemanticView::build(analysis::PreparedSemanticViewInputs {
                prepared: prepared.expect("prepared semantic view requires prepared artifact"),
                interproc_summary_set,
                abi_arg_regs: &self.config.arg_regs,
                ret_reg_name: &fold_arch.ret_reg_name,
                function_names: &self.context.function_names,
                symbols: &self.context.symbols,
                callee_facts: &self.context.type_facts().callee_facts,
                stack_slots: &self.context.type_facts().stack_slots,
                visible_bindings: &self.context.type_facts().visible_bindings,
                param_register_aliases: &param_register_aliases,
            })
        });
        let fold_inputs = FoldInputs {
            arch: &fold_arch,
            function_names: &self.context.function_names,
            strings: &self.context.strings,
            symbols: &self.context.symbols,
            known_function_signatures: &known_function_signatures,
            callee_facts: &self.context.type_facts().callee_facts,
            stack_slots: &self.context.type_facts().stack_slots,
            #[cfg(test)]
            external_stack_vars: &self.context.type_facts().external_stack_vars,
            visible_bindings: &self.context.type_facts().visible_bindings,
            external_type_db: &self.context.type_facts().external_type_db,
            semantic_artifact: self.context.semantic_artifact(),
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle,
            function_return_type: signature_ret_type.as_ref().or(Some(&inferred_ret_type)),
            prepared_ssa: prepared,
            interproc_summary_set,
            summary_view: Some(&self.context.function_facts.summary_view),
            prepared_semantic_view: prepared_semantic_view.as_ref(),
            prepared_objects: prepared.map(|artifact| artifact.objects()),
            prepared_memory: prepared.map(|artifact| artifact.memory()),
            prepared_predicates: prepared.map(|artifact| artifact.predicates()),
            prepared_call_sites: prepared.map(|artifact| artifact.call_sites()),
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        fold_ctx.analyze_blocks(&fold_blocks);
        fold_ctx.analyze_function_structure(func);
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let semantic_route = self.context.route_for(&func_name, &func.cfg_risk_summary());

        // Structure control flow (primary path: folded)
        let mut structurer = ControlFlowStructurer::new(func, &fold_ctx);

        // Get set of variables that survive folding before structuring.
        let emitted_vars = structurer.emitted_var_names();
        let routed_body = consumer_structured::primary_body_for_semantic_route(
            &semantic_route,
            &mut structurer,
            || self.linearize_function_body(func, &fold_ctx),
        );
        let mut use_conservative_locals = routed_body.use_conservative_locals;
        let mut is_linear_fallback = routed_body.is_linear_fallback;
        let mut body_stmt = routed_body.body_stmt;

        if matches!(semantic_route, planner::SemanticRoutePlan::Standard)
            && !Self::stmt_has_content(&body_stmt)
        {
            if let Some(semantic_body) = structurer.structure_semantic_worker_islands(6) {
                body_stmt = consumer_structured::semantic_worker_structured_body(
                    "semantic control islands",
                    semantic_body,
                );
                use_conservative_locals = true;
                is_linear_fallback = false;
            } else {
                let folded_reason = structurer
                    .safety_reason()
                    .map(str::to_string)
                    .unwrap_or_else(|| "folded structuring produced empty output".to_string());
                let empty_fallback = consumer_fallback::recover_empty_structuring(
                    func,
                    &fold_ctx,
                    folded_reason,
                    prefer_symbolic_large_worker_decompile(&self.context.function_facts)
                        .then(|| preferred_semantic_worker_reason(&func.cfg_risk_summary()))
                        .as_deref(),
                    || self.linearize_function_body(func, &fold_ctx),
                );
                use_conservative_locals = empty_fallback.use_conservative_locals;
                is_linear_fallback = empty_fallback.is_linear_fallback;
                body_stmt = empty_fallback.body_stmt;
            }
        }

        body_stmt = fold_ctx.normalize_final_stmt_calls(body_stmt);
        body_stmt = fold_ctx.prune_dead_temp_assignments_in_stmt(body_stmt);

        if let Some(comment) = self.semantic_vm_summary_comment() {
            body_stmt = Self::prepend_comment(body_stmt, comment);
        }

        // Build the C function
        // Convert body to statements
        let body = self.stmt_to_vec(body_stmt);
        let body_visible_names = collect_stmt_var_names(&body);
        let param_name_set = params
            .iter()
            .map(|param| param.name.to_ascii_lowercase())
            .collect::<HashSet<_>>();
        let param_home_offsets = fold_ctx
            .stack_arg_aliases_map()
            .iter()
            .filter_map(|(offset, alias)| {
                param_name_set
                    .contains(&alias.to_ascii_lowercase())
                    .then_some(*offset)
            })
            .chain(
                self.context
                    .type_facts()
                    .visible_bindings
                    .iter()
                    .filter_map(|binding| {
                        matches!(binding.kind, VisibleBindingKind::HiddenHome)
                            .then(|| binding.stack_slot.as_ref().map(|slot| slot.offset))
                            .flatten()
                    }),
            )
            .collect::<HashSet<_>>();
        let body_visible_stack_offsets = collect_visible_stack_offsets(
            &body_visible_names,
            &self.context.type_facts().visible_bindings,
            &self.context.type_facts().stack_slots,
            &param_name_set,
        );

        // Collect locals -- on fallback keep locals conservatively.
        let locals: Vec<ast::CLocal> = if use_conservative_locals {
            var_recovery
                .locals()
                .iter()
                .filter(|v| {
                    !v.stack_offset
                        .is_some_and(|offset| param_home_offsets.contains(&offset))
                })
                .map(|v| ast::CLocal {
                    ty: type_inference
                        .as_ref()
                        .map(|type_inference| {
                            type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                        })
                        .unwrap_or_else(|| v.ty.clone()),
                    name: v.name.clone(),
                    stack_offset: v.stack_offset,
                })
                .collect()
        } else {
            let mut selected = var_recovery
                .locals()
                .iter()
                .filter(|v| {
                    !v.stack_offset
                        .is_some_and(|offset| param_home_offsets.contains(&offset))
                        && (emitted_vars.contains(&v.name)
                            || body_visible_names.contains(&v.name)
                            || v.stack_offset
                                .is_some_and(|offset| body_visible_stack_offsets.contains(&offset)))
                })
                .map(|v| ast::CLocal {
                    ty: type_inference
                        .as_ref()
                        .map(|type_inference| {
                            type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                        })
                        .unwrap_or_else(|| v.ty.clone()),
                    name: v.name.clone(),
                    stack_offset: v.stack_offset,
                })
                .collect::<Vec<_>>();
            let mut seen_offsets = HashSet::new();
            selected.retain(|local| match local.stack_offset {
                Some(offset) => seen_offsets.insert(offset),
                None => true,
            });
            selected
        };

        let mut c_function = CFunction {
            name: func_name,
            ret_type: self
                .context
                .type_facts()
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                .unwrap_or_else(|| inferred_ret_type.clone()),
            params,
            locals,
            body,
        };
        append_semantic_summary_return_to_function_if_needed(
            &mut c_function,
            &self.context.function_facts,
        );

        // Apply post-structuring suffix cleanup for folded/unfolded paths.
        // Linear fallback intentionally keeps its raw expression-builder output.
        if !is_linear_fallback {
            let mut known_function_names = HashSet::new();
            for name in self.context.function_names.values() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            for name in self.context.type_facts().known_function_signatures.keys() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            post_rename::rewrite_function_identifiers(&mut c_function, &known_function_names);
        }
        rewrite_reserved_param_stack_home_uses(
            &mut c_function,
            fold_ctx.stack_arg_aliases_map(),
            fold_ctx.stack_vars_map(),
            fold_ctx.inputs.visible_bindings,
            fold_ctx.inputs.stack_slots,
        );
        rewrite_stack_synonym_uses_to_declared_locals(&mut c_function, &fold_ctx);
        prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx);
        prune_unused_pure_locals(&mut c_function);

        c_function
    }

    /// Convert a CStmt to a Vec<CStmt>.
    fn stmt_to_vec(&self, stmt: CStmt) -> Vec<CStmt> {
        match stmt {
            CStmt::Block(stmts) => stmts,
            CStmt::Empty => vec![],
            other => vec![other],
        }
    }

    fn infer_return_type(&self, func: &SSAFunction, type_inference: &TypeInference) -> CType {
        let mut candidates = Vec::new();

        for block in func.blocks() {
            for op in &block.ops {
                let SSAOp::Return { target } = op else {
                    continue;
                };

                let target_name = target.name.to_ascii_lowercase();
                if target_name.starts_with("xmm0") || target_name.starts_with("st0") {
                    let bits = if target.size.saturating_mul(8) <= 32 {
                        32
                    } else {
                        64
                    };
                    candidates.push(CType::Float(bits));
                    continue;
                }

                candidates.push(type_like_to_ctype(&type_inference.get_type(target)));
            }
        }

        if candidates.is_empty() {
            return CType::Void;
        }

        let mut meaningful: Vec<CType> = candidates
            .into_iter()
            .filter(|ty| !matches!(ty, CType::Unknown))
            .collect();
        if meaningful.is_empty() {
            return CType::Int(32);
        }
        if meaningful.iter().all(|ty| ty == &meaningful[0]) {
            return meaningful.remove(0);
        }
        if let Some(float_ty) = meaningful
            .iter()
            .find(|ty| matches!(ty, CType::Float(_)))
            .cloned()
        {
            return float_ty;
        }
        meaningful.remove(0)
    }
}

fn collect_expr_var_names(expr: &CExpr, out: &mut HashSet<String>) {
    match expr {
        CExpr::Var(name) => {
            out.insert(name.clone());
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Paren(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand) => collect_expr_var_names(operand, out),
        CExpr::Comma(items) => {
            for item in items {
                collect_expr_var_names(item, out);
            }
        }
        CExpr::Binary { left, right, .. } => {
            collect_expr_var_names(left, out);
            collect_expr_var_names(right, out);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_var_names(cond, out);
            collect_expr_var_names(then_expr, out);
            collect_expr_var_names(else_expr, out);
        }
        CExpr::Call { func, args } => {
            collect_expr_var_names(func, out);
            for arg in args {
                collect_expr_var_names(arg, out);
            }
        }
        CExpr::Subscript { base, index } => {
            collect_expr_var_names(base, out);
            collect_expr_var_names(index, out);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            collect_expr_var_names(base, out);
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::CharLit(_)
        | CExpr::StringLit(_)
        | CExpr::Sizeof(_)
        | CExpr::SizeofType(_) => {}
    }
}

fn collect_stmt_var_names(stmts: &[CStmt]) -> HashSet<String> {
    fn visit_stmt(stmt: &CStmt, out: &mut HashSet<String>) {
        match stmt {
            CStmt::Empty
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Comment(_)
            | CStmt::Goto(_)
            | CStmt::Label(_) => {}
            CStmt::Expr(expr) => collect_expr_var_names(expr, out),
            CStmt::Return(expr) => {
                if let Some(expr) = expr {
                    collect_expr_var_names(expr, out);
                }
            }
            CStmt::Decl { init, .. } => {
                if let Some(init) = init {
                    collect_expr_var_names(init, out);
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    visit_stmt(stmt, out);
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                collect_expr_var_names(cond, out);
                visit_stmt(then_body, out);
                if let Some(else_body) = else_body {
                    visit_stmt(else_body, out);
                }
            }
            CStmt::While { cond, body } => {
                collect_expr_var_names(cond, out);
                visit_stmt(body, out);
            }
            CStmt::DoWhile { body, cond } => {
                visit_stmt(body, out);
                collect_expr_var_names(cond, out);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    visit_stmt(init, out);
                }
                if let Some(cond) = cond {
                    collect_expr_var_names(cond, out);
                }
                if let Some(update) = update {
                    collect_expr_var_names(update, out);
                }
                visit_stmt(body, out);
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                collect_expr_var_names(expr, out);
                for case in cases {
                    collect_expr_var_names(&case.value, out);
                    for stmt in &case.body {
                        visit_stmt(stmt, out);
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        visit_stmt(stmt, out);
                    }
                }
            }
        }
    }

    let mut names = HashSet::new();
    for stmt in stmts {
        visit_stmt(stmt, &mut names);
    }
    names
}

fn parse_visible_stack_offset(
    name: &str,
    visible_bindings: &[VisibleBinding],
    stack_slots: &std::collections::BTreeMap<StackSlotKey, r2types::ExternalStackSlotSpec>,
    param_names: &HashSet<String>,
) -> Option<i64> {
    let lower = name.trim().to_ascii_lowercase();
    if param_names.contains(&lower) {
        return None;
    }
    if lower == "saved_fp" {
        return Some(0);
    }
    if let Some(rest) = lower.strip_prefix("stack_") {
        return i64::from_str_radix(rest, 16).ok();
    }
    if let Some(rest) = lower.strip_prefix("local_") {
        return i64::from_str_radix(rest, 16).ok().map(|v| -v);
    }
    if let Some(rest) = lower.strip_prefix("arg_") {
        return i64::from_str_radix(rest, 16).ok().map(|v| -v);
    }
    if let Some(rest) = lower.strip_prefix("var_") {
        let trimmed = rest.strip_suffix('h').unwrap_or(rest);
        if !trimmed.is_empty() && trimmed.chars().all(|ch| ch.is_ascii_hexdigit()) {
            return i64::from_str_radix(trimmed, 16).ok().map(|v| -v);
        }
    }
    visible_bindings
        .iter()
        .find(|binding| binding.name.eq_ignore_ascii_case(name))
        .and_then(|binding| binding.stack_slot.as_ref().map(|slot| slot.offset))
        .or_else(|| {
            stack_slots
                .iter()
                .find(|(_, slot_spec)| slot_spec.name.eq_ignore_ascii_case(name))
                .map(|(slot_key, _)| slot_key.offset)
        })
}

fn collect_visible_stack_offsets(
    names: &HashSet<String>,
    visible_bindings: &[VisibleBinding],
    stack_slots: &std::collections::BTreeMap<StackSlotKey, r2types::ExternalStackSlotSpec>,
    param_names: &HashSet<String>,
) -> HashSet<i64> {
    names
        .iter()
        .filter_map(|name| {
            parse_visible_stack_offset(name, visible_bindings, stack_slots, param_names)
        })
        .collect()
}

fn generic_stack_home_name_for_offset(offset: i64) -> String {
    if offset < 0 {
        format!("local_{:x}", (-offset) as u64)
    } else {
        format!("stack_{:x}", offset as u64)
    }
}

fn is_low_quality_stack_home_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower == "saved_fp"
        || lower.starts_with("local_")
        || lower.starts_with("stack_")
        || lower.starts_with("arg_")
        || lower.starts_with("var_")
}

fn stack_slot_matches_rewrite_offset(slot: &StackSlotKey, offset: i64) -> bool {
    if slot.offset == offset {
        return true;
    }
    matches!(slot.base, r2types::ExternalStackBase::FramePointer) && -slot.offset == offset
}

fn rewrite_reserved_param_stack_home_uses(
    func: &mut CFunction,
    stack_arg_aliases: &std::collections::HashMap<i64, String>,
    stack_vars: &std::collections::HashMap<i64, String>,
    visible_bindings: &[VisibleBinding],
    stack_slots: &std::collections::BTreeMap<StackSlotKey, r2types::ExternalStackSlotSpec>,
) {
    let param_names = func
        .params
        .iter()
        .map(|param| param.name.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    let mut rename_map = std::collections::HashMap::new();
    for (offset, alias) in stack_arg_aliases {
        let target = alias.trim();
        if target.is_empty() || !param_names.contains(&target.to_ascii_lowercase()) {
            continue;
        }

        rename_map.insert(
            generic_stack_home_name_for_offset(*offset),
            target.to_string(),
        );

        if let Some(stack_name) = stack_vars.get(offset)
            && is_low_quality_stack_home_name(stack_name)
        {
            rename_map.insert(stack_name.to_ascii_lowercase(), target.to_string());
        }

        for binding in visible_bindings {
            if !binding
                .stack_slot
                .as_ref()
                .is_some_and(|slot| stack_slot_matches_rewrite_offset(slot, *offset))
            {
                continue;
            }
            let name = binding.name.trim();
            if !name.is_empty() && is_low_quality_stack_home_name(name) {
                rename_map.insert(name.to_ascii_lowercase(), target.to_string());
            }
        }

        for (slot_key, slot_spec) in stack_slots {
            if !stack_slot_matches_rewrite_offset(slot_key, *offset) {
                continue;
            }
            let name = slot_spec.name.trim();
            if !name.is_empty() && is_low_quality_stack_home_name(name) {
                rename_map.insert(name.to_ascii_lowercase(), target.to_string());
            }
        }
    }

    if rename_map.is_empty() {
        return;
    }

    func.locals
        .retain(|local| !rename_map.contains_key(&local.name.to_ascii_lowercase()));
    for stmt in &mut func.body {
        rewrite_stmt_reserved_param_stack_homes(stmt, &rename_map);
    }
}

fn rewrite_stmt_reserved_param_stack_homes(
    stmt: &mut CStmt,
    rename_map: &std::collections::HashMap<String, String>,
) {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => rewrite_expr_reserved_param_stack_homes(expr, rename_map, true),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                rewrite_expr_reserved_param_stack_homes(init, rename_map, true);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                rewrite_stmt_reserved_param_stack_homes(stmt, rename_map);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
            rewrite_stmt_reserved_param_stack_homes(then_body, rename_map);
            if let Some(else_body) = else_body {
                rewrite_stmt_reserved_param_stack_homes(else_body, rename_map);
            }
        }
        CStmt::While { cond, body } => {
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
            rewrite_stmt_reserved_param_stack_homes(body, rename_map);
        }
        CStmt::DoWhile { body, cond } => {
            rewrite_stmt_reserved_param_stack_homes(body, rename_map);
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                rewrite_stmt_reserved_param_stack_homes(init, rename_map);
            }
            if let Some(cond) = cond {
                rewrite_expr_reserved_param_stack_homes(cond, rename_map, true);
            }
            if let Some(update) = update {
                rewrite_expr_reserved_param_stack_homes(update, rename_map, true);
            }
            rewrite_stmt_reserved_param_stack_homes(body, rename_map);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            rewrite_expr_reserved_param_stack_homes(expr, rename_map, true);
            for case in cases {
                rewrite_expr_reserved_param_stack_homes(&mut case.value, rename_map, true);
                for stmt in &mut case.body {
                    rewrite_stmt_reserved_param_stack_homes(stmt, rename_map);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    rewrite_stmt_reserved_param_stack_homes(stmt, rename_map);
                }
            }
        }
        CStmt::Return(expr) => {
            if let Some(expr) = expr {
                rewrite_expr_reserved_param_stack_homes(expr, rename_map, true);
            }
        }
    }
}

fn rewrite_expr_reserved_param_stack_homes(
    expr: &mut CExpr,
    rename_map: &std::collections::HashMap<String, String>,
    allow_plain_var_rewrite: bool,
) {
    match expr {
        CExpr::Var(name) if allow_plain_var_rewrite => {
            if let Some(target) = rename_map.get(&name.to_ascii_lowercase()) {
                *name = target.clone();
            }
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Paren(operand)
        | CExpr::Sizeof(operand) => {
            rewrite_expr_reserved_param_stack_homes(operand, rename_map, allow_plain_var_rewrite);
        }
        CExpr::AddrOf(operand) => {
            rewrite_expr_reserved_param_stack_homes(operand, rename_map, false);
        }
        CExpr::Deref(operand) => {
            if let Some(target) = reserved_param_stack_home_target_name(operand, rename_map) {
                *expr = CExpr::Var(target);
                return;
            }
            rewrite_expr_reserved_param_stack_homes(operand, rename_map, false);
        }
        CExpr::Binary { left, right, .. } => {
            rewrite_expr_reserved_param_stack_homes(left, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(right, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            rewrite_expr_reserved_param_stack_homes(cond, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(then_expr, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(else_expr, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Call { func, args } => {
            rewrite_expr_reserved_param_stack_homes(func, rename_map, allow_plain_var_rewrite);
            for arg in args {
                rewrite_expr_reserved_param_stack_homes(arg, rename_map, allow_plain_var_rewrite);
            }
        }
        CExpr::Subscript { base, index } => {
            rewrite_expr_reserved_param_stack_homes(base, rename_map, allow_plain_var_rewrite);
            rewrite_expr_reserved_param_stack_homes(index, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            rewrite_expr_reserved_param_stack_homes(base, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Comma(items) => {
            for item in items {
                rewrite_expr_reserved_param_stack_homes(item, rename_map, allow_plain_var_rewrite);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_)
        | CExpr::Var(_) => {}
    }
}

fn reserved_param_stack_home_target_name(
    expr: &CExpr,
    rename_map: &std::collections::HashMap<String, String>,
) -> Option<String> {
    match expr {
        CExpr::Var(name) => rename_map.get(&name.to_ascii_lowercase()).cloned(),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            reserved_param_stack_home_target_name(inner, rename_map)
        }
        _ => None,
    }
}

fn rewrite_stack_synonym_uses_to_declared_locals(
    func: &mut CFunction,
    fold_ctx: &FoldingContext<'_>,
) {
    let declared_names = func
        .params
        .iter()
        .map(|param| param.name.to_ascii_lowercase())
        .chain(
            func.locals
                .iter()
                .map(|local| local.name.to_ascii_lowercase()),
        )
        .collect::<HashSet<_>>();
    let local_by_offset = func
        .locals
        .iter()
        .filter_map(|local| {
            local
                .stack_offset
                .map(|offset| (offset, local.name.clone()))
        })
        .collect::<std::collections::HashMap<_, _>>();
    let mut pointer_locals = func
        .locals
        .iter()
        .filter(|local| matches!(local.ty, CType::Pointer(_)))
        .map(|local| local.name.clone())
        .collect::<Vec<_>>();
    pointer_locals.sort();
    pointer_locals.dedup_by(|lhs, rhs| lhs.eq_ignore_ascii_case(rhs));
    let unique_pointer_local = (pointer_locals.len() == 1).then(|| pointer_locals[0].clone());
    if local_by_offset.is_empty() && unique_pointer_local.is_none() {
        return;
    }

    let mut rename_map = std::collections::HashMap::new();
    for name in collect_stmt_var_names(&func.body) {
        if declared_names.contains(&name.to_ascii_lowercase()) {
            continue;
        }
        let target = if let Some(offset) = fold_ctx.stack_offset_for_visible_storage_name(&name) {
            local_by_offset.get(&offset).cloned()
        } else if name.eq_ignore_ascii_case("slot") {
            unique_pointer_local.clone()
        } else {
            None
        };
        let Some(target) = target else {
            continue;
        };
        if !target.eq_ignore_ascii_case(&name) {
            rename_map.insert(name.to_ascii_lowercase(), target);
        }
    }
    if rename_map.is_empty() {
        return;
    }

    for stmt in &mut func.body {
        rewrite_stmt_reserved_param_stack_homes(stmt, &rename_map);
    }
}

fn prune_dead_temp_assignments_in_function_body(
    func: &mut CFunction,
    fold_ctx: &FoldingContext<'_>,
) {
    let body = CStmt::Block(std::mem::take(&mut func.body));
    func.body = match fold_ctx.prune_dead_temp_assignments_in_stmt(body) {
        CStmt::Block(stmts) => stmts,
        CStmt::Empty => Vec::new(),
        stmt => vec![stmt],
    };
}

fn prune_unused_pure_locals(func: &mut CFunction) {
    loop {
        let live_reads = collect_function_local_reads(func);
        let dead_locals = func
            .locals
            .iter()
            .map(|local| local.name.to_ascii_lowercase())
            .filter(|name| !live_reads.contains(name))
            .collect::<HashSet<_>>();

        if dead_locals.is_empty() {
            break;
        }

        func.locals
            .retain(|local| !dead_locals.contains(&local.name.to_ascii_lowercase()));
        prune_unused_pure_local_stmts(&mut func.body, &dead_locals);
    }
}

fn collect_function_local_reads(func: &CFunction) -> HashSet<String> {
    let mut reads = HashSet::new();
    for stmt in &func.body {
        collect_stmt_local_reads(stmt, &mut reads);
    }
    reads
}

fn collect_stmt_local_reads(stmt: &CStmt, reads: &mut HashSet<String>) {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) => {
            if !matches!(left.as_ref(), CExpr::Var(_)) {
                collect_expr_local_reads(left, reads);
            }
            collect_expr_local_reads(right, reads);
        }
        CStmt::Expr(expr) => collect_expr_local_reads(expr, reads),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                collect_expr_local_reads(init, reads);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                collect_stmt_local_reads(stmt, reads);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            collect_expr_local_reads(cond, reads);
            collect_stmt_local_reads(then_body, reads);
            if let Some(else_body) = else_body {
                collect_stmt_local_reads(else_body, reads);
            }
        }
        CStmt::While { cond, body } => {
            collect_expr_local_reads(cond, reads);
            collect_stmt_local_reads(body, reads);
        }
        CStmt::DoWhile { body, cond } => {
            collect_stmt_local_reads(body, reads);
            collect_expr_local_reads(cond, reads);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                collect_stmt_local_reads(init, reads);
            }
            if let Some(cond) = cond {
                collect_expr_local_reads(cond, reads);
            }
            if let Some(update) = update {
                collect_expr_local_reads(update, reads);
            }
            collect_stmt_local_reads(body, reads);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            collect_expr_local_reads(expr, reads);
            for case in cases {
                collect_expr_local_reads(&case.value, reads);
                for stmt in &case.body {
                    collect_stmt_local_reads(stmt, reads);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    collect_stmt_local_reads(stmt, reads);
                }
            }
        }
        CStmt::Return(Some(expr)) => collect_expr_local_reads(expr, reads),
        CStmt::Return(None) => {}
    }
}

fn collect_expr_local_reads(expr: &CExpr, reads: &mut HashSet<String>) {
    match expr {
        CExpr::Var(name) => {
            reads.insert(name.to_ascii_lowercase());
        }
        CExpr::Paren(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => collect_expr_local_reads(inner, reads),
        CExpr::Binary { left, right, .. } => {
            collect_expr_local_reads(left, reads);
            collect_expr_local_reads(right, reads);
        }
        CExpr::Subscript { base, index } => {
            collect_expr_local_reads(base, reads);
            collect_expr_local_reads(index, reads);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            collect_expr_local_reads(base, reads);
        }
        CExpr::Call { func, args } => {
            collect_expr_local_reads(func, reads);
            for arg in args {
                collect_expr_local_reads(arg, reads);
            }
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_local_reads(cond, reads);
            collect_expr_local_reads(then_expr, reads);
            collect_expr_local_reads(else_expr, reads);
        }
        CExpr::Comma(items) => {
            for item in items {
                collect_expr_local_reads(item, reads);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => {}
    }
}

fn prune_unused_pure_local_stmts(stmts: &mut Vec<CStmt>, dead_locals: &HashSet<String>) {
    for stmt in stmts.iter_mut() {
        prune_unused_pure_local_stmt(stmt, dead_locals);
    }
    stmts.retain(|stmt| !matches!(stmt, CStmt::Empty));
}

fn prune_unused_pure_local_stmt(stmt: &mut CStmt, dead_locals: &HashSet<String>) {
    match stmt {
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) => {
            if let CExpr::Var(name) = left.as_ref()
                && dead_locals.contains(&name.to_ascii_lowercase())
                && expr_is_pure_for_dead_local_prune(right)
            {
                *stmt = CStmt::Empty;
            }
        }
        CStmt::Decl { name, init, .. } => {
            if dead_locals.contains(&name.to_ascii_lowercase()) {
                match init.take() {
                    Some(expr) if !expr_is_pure_for_dead_local_prune(&expr) => {
                        *stmt = CStmt::Expr(expr);
                    }
                    _ => {
                        *stmt = CStmt::Empty;
                    }
                }
            }
        }
        CStmt::Block(stmts) => prune_unused_pure_local_stmts(stmts, dead_locals),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            prune_unused_pure_local_stmt(then_body, dead_locals);
            if let Some(else_body) = else_body {
                prune_unused_pure_local_stmt(else_body, dead_locals);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            prune_unused_pure_local_stmt(body, dead_locals);
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                prune_unused_pure_local_stmt(init, dead_locals);
            }
            prune_unused_pure_local_stmt(body, dead_locals);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                prune_unused_pure_local_stmts(&mut case.body, dead_locals);
            }
            if let Some(default) = default {
                prune_unused_pure_local_stmts(default, dead_locals);
            }
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

fn expr_is_pure_for_dead_local_prune(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_)
        | CExpr::Var(_) => true,
        CExpr::Paren(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => expr_is_pure_for_dead_local_prune(inner),
        CExpr::Binary { left, right, .. } => {
            expr_is_pure_for_dead_local_prune(left) && expr_is_pure_for_dead_local_prune(right)
        }
        CExpr::Subscript { base, index } => {
            expr_is_pure_for_dead_local_prune(base) && expr_is_pure_for_dead_local_prune(index)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            expr_is_pure_for_dead_local_prune(base)
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_is_pure_for_dead_local_prune(cond)
                && expr_is_pure_for_dead_local_prune(then_expr)
                && expr_is_pure_for_dead_local_prune(else_expr)
        }
        CExpr::Comma(items) => items.iter().all(expr_is_pure_for_dead_local_prune),
        CExpr::Call { .. } => false,
    }
}

pub fn infer_local_struct_field_accesses(
    func: &SSAFunction,
    config: &DecompilerConfig,
) -> Vec<LocalStructFieldAccess> {
    let cfg_summary = func.cfg_risk_summary();
    if cfg_summary.block_count >= 96
        && cfg_summary.switch_block_count > 0
        && cfg_summary.max_switch_cases >= 32
    {
        return Vec::new();
    }

    let function_names = std::collections::HashMap::new();
    let strings = std::collections::HashMap::new();
    let symbols = std::collections::HashMap::new();
    let type_hints = std::collections::HashMap::new();
    let mut param_register_aliases = std::collections::HashMap::new();
    let mut arg_slot_map = std::collections::HashMap::new();

    for (idx, reg_name) in config.arg_regs.iter().enumerate() {
        let arg_name = format!("arg{}", idx + 1);
        for alias in register_alias_names(reg_name) {
            let lower = alias.to_ascii_lowercase();
            param_register_aliases.insert(lower.clone(), arg_name.clone());
            arg_slot_map.insert(lower, idx);
        }
    }

    let env = analysis::PassEnv {
        ptr_size: config.ptr_size,
        sp_name: &config.sp_name,
        fp_name: &config.fp_name,
        ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
        function_names: &function_names,
        strings: &strings,
        symbols: &symbols,
        arg_regs: &config.arg_regs,
        param_register_aliases: &param_register_aliases,
        caller_saved_regs: &config.caller_saved_regs,
        type_hints: &type_hints,
        type_oracle: None,
    };

    let blocks: Vec<_> = func.blocks().cloned().collect();
    let use_info = analysis::UseInfo::analyze_for_local_struct_accesses(&blocks, &env);
    analysis::use_info::collect_local_struct_field_access_profiles(
        &use_info,
        func,
        &env,
        &arg_slot_map,
    )
    .into_iter()
    .map(|profile| LocalStructFieldAccess {
        arg_index: profile.arg_index,
        field_offset: profile.field_offset,
        access_size: profile.access_size,
        is_write: profile.is_write,
    })
    .collect()
}

#[cfg(test)]
pub(crate) fn test_control_fact(
    target: u64,
    status: r2sym::SymbolicReachabilityStatus,
    branch_truth: Option<bool>,
    condition: Option<&str>,
    compiled: Option<r2sym::BackwardConditionSummary>,
    evidence: r2sym::SemanticEvidence,
) -> r2sym::Judged<r2sym::ControlFact> {
    r2sym::Judged::new(
        r2sym::ControlFact {
            target,
            status,
            branch_truth,
            condition: condition.map(str::to_string),
            compiled,
        },
        evidence,
    )
}

#[cfg(test)]
pub(crate) fn test_memory_fact(
    term: r2sym::BackwardMemoryCondition,
    evidence: r2sym::SemanticEvidence,
) -> r2sym::Judged<r2sym::MemoryFact> {
    r2sym::Judged::new(r2sym::MemoryFact { term }, evidence)
}

#[cfg(test)]
pub(crate) fn test_semantic_region(
    anchor: u64,
    frontier: std::collections::BTreeSet<u64>,
    control: Vec<r2sym::Judged<r2sym::ControlFact>>,
    memory: Vec<r2sym::Judged<r2sym::MemoryFact>>,
) -> r2sym::SemanticRegion {
    let targets = control
        .iter()
        .map(|fact| {
            r2sym::Judged::new(
                r2sym::TargetFact {
                    target: fact.value.target,
                    status: fact.value.status,
                    branch_truth: fact.value.branch_truth,
                },
                fact.evidence.clone(),
            )
        })
        .collect();
    r2sym::SemanticRegion {
        anchor,
        frontier,
        control,
        memory,
        pre: Vec::new(),
        post: Vec::new(),
        targets,
    }
}

#[cfg(test)]
pub(crate) fn test_native_semantic_artifact(
    stage: r2sym::RefinementStage,
    granularity: r2sym::ArtifactGranularity,
    slice_class: r2sym::SliceClass,
    skipped_large_cfg: bool,
    residual_reasons: Vec<r2sym::ResidualReason>,
    regions: Vec<r2sym::SemanticRegion>,
) -> r2sym::SemanticArtifact {
    let regions = regions
        .into_iter()
        .map(|region| (region.key(), region))
        .collect();
    r2sym::SemanticArtifact {
        stage,
        granularity,
        execution: r2sym::ExecutionModel::Native,
        body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
            summary: r2sym::NativeFunctionSummary {
                slice_class,
                closure_functions: 0,
                helper_functions: 0,
                derived_summaries: 0,
                derived_diagnostics: Default::default(),
                region_summaries: Vec::new(),
                worker_summaries: Vec::new(),
            },
            regions,
        }),
        diagnostics: r2sym::SemanticArtifactDiagnostics {
            branches_evaluated: 0,
            branches_pruned: 0,
            branches_unknown: 0,
            skipped_missing_arch: false,
            skipped_large_cfg,
            residual_reasons,
            interpreter: None,
            ambiguous_targets: Vec::new(),
            cache_hit: false,
        },
    }
}

#[cfg(test)]
pub(crate) fn leaked_test_semantic_artifact(
    artifact: r2sym::SemanticArtifact,
) -> &'static r2sym::SemanticArtifact {
    Box::leak(Box::new(artifact))
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::SSAFunction;
    use r2types::{
        ExternalField, ExternalRegisterParamSpec, ExternalStruct, FunctionFacts, FunctionParamSpec,
        FunctionSignatureSpec, FunctionTypeFacts,
    };
    use std::collections::{BTreeMap, BTreeSet};

    fn ssa_from_ops(ops: Vec<R2ILOp>, arch: &ArchSpec) -> SSAFunction {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        SSAFunction::from_blocks_with_arch(&[block], Some(arch))
            .expect("SSA function should build")
            .with_name("stable_demo")
    }

    fn prepared_from_ops(ops: Vec<R2ILOp>, arch: &ArchSpec) -> r2ssa::SsaArtifact {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        r2ssa::SsaArtifact::for_decompile(&[block], Some(arch))
            .expect("prepared SSA should build")
            .with_name("stable_demo")
    }

    fn test_arch_for_decompile() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RSI", 0x18, 8));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch
    }

    #[test]
    fn param_register_aliases_keep_abi_order_over_misaligned_external_regs() {
        let params = vec![
            ast::CParam {
                ty: CType::Pointer(Box::new(CType::Int(32))),
                name: "arr".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "len".to_string(),
            },
        ];
        let register_params = vec![
            ExternalRegisterParamSpec {
                name: "al".to_string(),
                ty: Some(CTypeLike::Typedef("int32_t".to_string())),
                reg: "AL".to_string(),
            },
            ExternalRegisterParamSpec {
                name: "rdi".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Typedef(
                    "int32_t".to_string(),
                )))),
                reg: "rdi".to_string(),
            },
        ];
        let aliases = build_param_register_aliases(
            &params,
            &[],
            &register_params,
            &["rdi".to_string(), "rsi".to_string()],
        );

        assert_eq!(aliases.get("rdi").map(String::as_str), Some("arr"));
        assert_eq!(aliases.get("edi").map(String::as_str), Some("arr"));
        assert_eq!(aliases.get("rsi").map(String::as_str), Some("len"));
    }

    fn signature_spec(
        ret_type: Option<CType>,
        params: Vec<(&str, Option<CType>)>,
    ) -> FunctionSignatureSpec {
        FunctionSignatureSpec {
            ret_type: ret_type.as_ref().map(super::ctype_to_type_like),
            params: params
                .into_iter()
                .map(|(name, ty)| FunctionParamSpec {
                    name: name.to_string(),
                    ty: ty.as_ref().map(super::ctype_to_type_like),
                })
                .collect(),
        }
    }

    fn arg_memory_term(
        offset: i64,
        size: u32,
        evidence: r2sym::SemanticEvidence,
        value_expr: Option<&str>,
        exact_value: bool,
    ) -> r2sym::BackwardMemoryCondition {
        r2sym::BackwardMemoryCondition {
            region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
            offset_lo: offset,
            offset_hi: offset,
            size,
            exact_offset: true,
            evidence,
            binding: None,
            expr: if offset == 0 {
                "*arg0".to_string()
            } else {
                format!("*(arg0 + {offset})")
            },
            value_expr: value_expr.map(str::to_string),
            exact_value,
        }
    }

    fn compiled_summary(
        simplified: &str,
        precision: r2sym::BackwardConditionPrecision,
        supported_paths: usize,
        total_paths: usize,
        memory_terms: Vec<r2sym::BackwardMemoryCondition>,
    ) -> r2sym::BackwardConditionSummary {
        r2sym::BackwardConditionSummary {
            simplified: simplified.to_string(),
            terms: vec![simplified.to_string()],
            memory_terms,
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision,
            supported_paths,
            total_paths,
        }
    }

    fn large_cfg_worker_artifact(
        stage: r2sym::RefinementStage,
        residual_reasons: Vec<r2sym::ResidualReason>,
        regions: Vec<r2sym::SemanticRegion>,
    ) -> r2sym::SemanticArtifact {
        test_native_semantic_artifact(
            stage,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::Worker,
            true,
            residual_reasons,
            regions,
        )
    }

    #[test]
    fn test_decompiler_config_default() {
        let config = DecompilerConfig::default();
        assert_eq!(config.ptr_size, 64);
        assert_eq!(config.sp_name, "rsp");
        assert_eq!(config.fp_name, "rbp");
    }

    #[test]
    fn test_decompiler_config_x86() {
        let config = DecompilerConfig::x86();
        assert_eq!(config.ptr_size, 32);
        assert_eq!(config.sp_name, "esp");
        assert_eq!(config.fp_name, "ebp");
    }

    #[test]
    fn test_decompiler_config_arm() {
        let config = DecompilerConfig::arm();
        assert_eq!(config.ptr_size, 32);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "fp");
    }

    #[test]
    fn test_decompiler_config_aarch64() {
        let config = DecompilerConfig::aarch64();
        assert_eq!(config.ptr_size, 64);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "x29");
        assert_eq!(config.arg_regs[0], "x0");
        assert_eq!(config.ret_regs[0], "x0");
        assert!(config.caller_saved_regs.contains("x17"));
    }

    #[test]
    fn test_decompiler_config_riscv32() {
        let config = DecompilerConfig::riscv32();
        assert_eq!(config.ptr_size, 32);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "s0");
    }

    #[test]
    fn test_decompiler_config_riscv64() {
        let config = DecompilerConfig::riscv64();
        assert_eq!(config.ptr_size, 64);
        assert_eq!(config.sp_name, "sp");
        assert_eq!(config.fp_name, "s0");
    }

    #[test]
    fn reserved_param_stack_home_deref_rewrites_to_param_and_prunes_dead_pure_locals() {
        let mut func = CFunction {
            name: "dbg.test_bool_carrier_chain".to_string(),
            ret_type: CType::Int(32),
            params: vec![
                ast::CParam {
                    ty: CType::Int(32),
                    name: "x".to_string(),
                },
                ast::CParam {
                    ty: CType::Int(32),
                    name: "y".to_string(),
                },
            ],
            locals: vec![
                ast::CLocal {
                    ty: CType::Int(32),
                    name: "local_14".to_string(),
                    stack_offset: Some(-0x14),
                },
                ast::CLocal {
                    ty: CType::Int(32),
                    name: "local_18".to_string(),
                    stack_offset: Some(-0x18),
                },
                ast::CLocal {
                    ty: CType::UInt(32),
                    name: "neq".to_string(),
                    stack_offset: Some(-0x4),
                },
                ast::CLocal {
                    ty: CType::Int(64),
                    name: "widened".to_string(),
                    stack_offset: Some(-0x10),
                },
            ],
            body: vec![
                CStmt::Expr(CExpr::binary(
                    BinaryOp::Assign,
                    CExpr::Var("neq".to_string()),
                    CExpr::binary(
                        BinaryOp::Ne,
                        CExpr::Var("x".to_string()),
                        CExpr::Var("y".to_string()),
                    ),
                )),
                CStmt::Expr(CExpr::binary(
                    BinaryOp::Assign,
                    CExpr::Var("widened".to_string()),
                    CExpr::binary(
                        BinaryOp::Ne,
                        CExpr::Var("x".to_string()),
                        CExpr::Var("y".to_string()),
                    ),
                )),
                CStmt::If {
                    cond: CExpr::binary(
                        BinaryOp::Ne,
                        CExpr::Var("x".to_string()),
                        CExpr::Var("y".to_string()),
                    ),
                    then_body: Box::new(CStmt::Return(Some(CExpr::Deref(Box::new(CExpr::Var(
                        "local_14".to_string(),
                    )))))),
                    else_body: Some(Box::new(CStmt::Return(Some(CExpr::Deref(Box::new(
                        CExpr::Var("local_18".to_string()),
                    )))))),
                },
            ],
        };

        rewrite_reserved_param_stack_home_uses(
            &mut func,
            &std::collections::HashMap::from([(-0x14, "x".to_string()), (-0x18, "y".to_string())]),
            &std::collections::HashMap::new(),
            &[],
            &std::collections::BTreeMap::new(),
        );
        prune_unused_pure_locals(&mut func);

        assert!(func.locals.is_empty(), "{func:?}");
        assert_eq!(func.body.len(), 1, "{func:?}");
        let CStmt::If {
            then_body,
            else_body,
            ..
        } = &func.body[0]
        else {
            panic!("expected final if body, got {:?}", func.body);
        };
        assert_eq!(
            **then_body,
            CStmt::Return(Some(CExpr::Var("x".to_string())))
        );
        assert_eq!(
            **else_body.as_ref().expect("else branch"),
            CStmt::Return(Some(CExpr::Var("y".to_string())))
        );
    }

    #[test]
    fn test_final_function_body_prune_removes_late_dead_sleigh_temps() {
        let mut func = CFunction {
            name: "late_prune".to_string(),
            ret_type: CType::i64(),
            params: Vec::new(),
            locals: Vec::new(),
            body: vec![
                CStmt::Expr(CExpr::assign(
                    CExpr::Var("tmp_ldwn_1".to_string()),
                    CExpr::deref(CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("base".to_string()),
                        CExpr::IntLit(50),
                    )),
                )),
                CStmt::Expr(CExpr::assign(
                    CExpr::Var("tmp_stwn_1".to_string()),
                    CExpr::binary(
                        BinaryOp::Add,
                        CExpr::deref(CExpr::binary(
                            BinaryOp::Add,
                            CExpr::Var("base".to_string()),
                            CExpr::IntLit(50),
                        )),
                        CExpr::Var("arg1".to_string()),
                    ),
                )),
                CStmt::Expr(CExpr::assign(
                    CExpr::deref(CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("x0_5".to_string()),
                        CExpr::IntLit(50),
                    )),
                    CExpr::binary(
                        BinaryOp::Add,
                        CExpr::Var("arg1".to_string()),
                        CExpr::deref(CExpr::binary(
                            BinaryOp::Add,
                            CExpr::Var("base".to_string()),
                            CExpr::IntLit(50),
                        )),
                    ),
                )),
                CStmt::Return(Some(CExpr::Var("x0_5".to_string()))),
            ],
        };
        let ctx = FoldingContext::new(64);

        prune_dead_temp_assignments_in_function_body(&mut func, &ctx);

        assert_eq!(func.body.len(), 2, "{func:?}");
        assert!(
            !format!("{:?}", func.body).contains("tmp_"),
            "Sleigh load/store temps should be gone from final function body: {:?}",
            func.body
        );
        assert!(matches!(
            func.body[0],
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                ..
            })
        ));
        assert_eq!(
            func.body[1],
            CStmt::Return(Some(CExpr::Var("x0_5".to_string())))
        );
    }

    #[test]
    fn authoritative_external_signature_can_shrink_recovered_header_params() {
        let recovered = vec![
            ast::CParam {
                ty: CType::Int(32),
                name: "arg1".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg2".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg3".to_string(),
            },
        ];
        let signature = signature_spec(
            Some(CType::Pointer(Box::new(CType::Int(8)))),
            vec![
                ("src", Some(CType::Pointer(Box::new(CType::Int(8))))),
                ("len", Some(CType::UInt(64))),
            ],
        );

        let params = merge_params_with_external_signature(recovered, Some(&signature));
        assert_eq!(
            params.len(),
            2,
            "typed/named external signature should be authoritative for the visible header"
        );
        assert_eq!(params[0].name, "src");
        assert_eq!(params[1].name, "len");
        assert!(matches!(params[1].ty, CType::UInt(64)));
    }

    #[test]
    fn generic_external_signature_does_not_shrink_richer_recovered_header_params() {
        let recovered = vec![
            ast::CParam {
                ty: CType::Int(32),
                name: "arg1".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg2".to_string(),
            },
            ast::CParam {
                ty: CType::Int(32),
                name: "arg3".to_string(),
            },
        ];
        let signature = signature_spec(None, vec![("arg1", None), ("arg2", None)]);

        let params = merge_params_with_external_signature(recovered, Some(&signature));
        assert_eq!(
            params.len(),
            3,
            "generic external signature should not hide richer recovered params"
        );
        assert_eq!(params[2].name, "arg3");
    }

    #[test]
    fn external_signature_can_extend_empty_recovered_header_params() {
        let signature = signature_spec(
            None,
            vec![
                ("buf", Some(CType::Pointer(Box::new(CType::Int(8))))),
                ("count", Some(CType::UInt(64))),
            ],
        );

        let params = merge_params_with_external_signature(Vec::new(), Some(&signature));
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "buf");
        assert_eq!(params[1].name, "count");
    }

    #[test]
    fn decompile_is_stable_with_external_param_names_and_local_order() {
        let arch = test_arch_for_decompile();
        let func = ssa_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x10, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x20, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::unique(0x11, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x28, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x12, 8),
                    a: Varnode::register(0x10, 8),
                    b: Varnode::register(0x18, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x13, 8),
                    a: Varnode::unique(0x12, 8),
                    b: Varnode::unique(0x10, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x00, 8),
                    a: Varnode::unique(0x13, 8),
                    b: Varnode::unique(0x11, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::x86_64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("zzz_first", Some(CType::Int(64))),
                    ("aaa_second", Some(CType::Int(64))),
                ],
            )),
            ..FunctionTypeFacts::default()
        });

        let built_first = decompiler.build_function(&func);
        let built_second = decompiler.build_function(&func);
        let first = decompiler.decompile(&func);
        let second = decompiler.decompile(&func);

        assert_eq!(first, second, "decompiled text should be byte-stable");
        assert!(first.contains("stable_demo(int64_t zzz_first, int64_t aaa_second)"));
        assert_eq!(
            built_first
                .params
                .iter()
                .map(|param| param.name.clone())
                .collect::<Vec<_>>(),
            vec!["zzz_first".to_string(), "aaa_second".to_string()]
        );
        assert_eq!(
            built_first
                .locals
                .iter()
                .map(|local| local.name.clone())
                .collect::<Vec<_>>(),
            built_second
                .locals
                .iter()
                .map(|local| local.name.clone())
                .collect::<Vec<_>>(),
            "local declaration order should be stable across builds"
        );
    }

    #[test]
    fn decompile_is_stable_for_predicate_heavy_return() {
        let arch = test_arch_for_decompile();
        let func = ssa_from_ops(
            vec![
                R2ILOp::IntSub {
                    dst: Varnode::unique(0x20, 4),
                    a: Varnode::register(0x10, 8),
                    b: Varnode::constant(19, 4),
                },
                R2ILOp::IntEqual {
                    dst: Varnode::unique(0x21, 1),
                    a: Varnode::unique(0x20, 4),
                    b: Varnode::constant(0, 4),
                },
                R2ILOp::BoolNot {
                    dst: Varnode::unique(0x22, 1),
                    src: Varnode::unique(0x21, 1),
                },
                R2ILOp::IntZExt {
                    dst: Varnode::register(0x00, 8),
                    src: Varnode::unique(0x22, 1),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );

        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let first = decompiler.decompile(&func);
        let second = decompiler.decompile(&func);

        assert_eq!(first, second, "predicate-heavy text should be byte-stable");
        assert!(
            first.contains("return (int64_t)(arg1 !=") || first.contains("return arg1 != 19;"),
            "decompiled predicate should use a direct comparison, got:\n{first}"
        );
        assert!(
            !first.contains("0 != 0"),
            "decompiled predicate must not collapse into a dead boolean"
        );
        assert!(
            !first.contains("zf_"),
            "decompiled predicate should not leak flag temporaries"
        );
    }

    #[test]
    fn decompile_input_preserves_function_header_and_emits_stable_output() {
        let arch = test_arch_for_decompile();
        let ops = vec![
            R2ILOp::Load {
                dst: Varnode::unique(0x10, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x20, 8),
            },
            R2ILOp::IntAdd {
                dst: Varnode::register(0x00, 8),
                a: Varnode::unique(0x10, 8),
                b: Varnode::register(0x18, 8),
            },
            R2ILOp::Return {
                target: Varnode::register(0x00, 8),
            },
        ];
        let func = ssa_from_ops(ops.clone(), &arch);
        let prepared = prepared_from_ops(ops, &arch);
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("arg1", Some(CType::Int(64))),
                    ("arg2", Some(CType::Int(64))),
                ],
            )),
            ..FunctionTypeFacts::default()
        };
        let context = DecompilerContext::default().with_type_facts(type_facts);

        let mut legacy = Decompiler::new(DecompilerConfig::x86_64());
        legacy.set_type_facts(context.type_facts().clone());
        let input = DecompilerInput::new(prepared, context);
        let typed = Decompiler::new(DecompilerConfig::x86_64());

        let legacy_fn = legacy.build_function(&func);
        let typed_fn = typed.build_function_from_input(&input);
        let typed_text = typed.decompile_input(&input);

        assert_eq!(legacy_fn.name, typed_fn.name);
        assert_eq!(legacy_fn.ret_type, typed_fn.ret_type);
        assert_eq!(legacy_fn.params, typed_fn.params);
        assert!(typed_text.contains("stable_demo"));
        assert!(typed_text.contains("return"));
        assert!(typed_text.contains("arg2"));
    }

    #[test]
    fn decompile_input_honors_engine_selected_route() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let context = DecompilerContext::default().with_semantic_route(Some(
            SemanticRoutePlan::FallbackComment {
                comment: "/* engine refusal: tested route */".to_string(),
            },
        ));
        let input = DecompilerInput::new(prepared, context);

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert_eq!(output, "/* engine refusal: tested route */");
    }

    #[test]
    fn explicit_external_struct_context_drives_arm64_indexed_member_rendering() {
        use std::collections::BTreeMap;

        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("X10", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("X0", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let struct_name = "sla_struct_explicit_demo".to_string();
        let mut type_db = ExternalTypeDb::default();
        type_db.structs.insert(
            struct_name.clone(),
            ExternalStruct {
                name: struct_name.clone(),
                fields: BTreeMap::from([
                    (
                        8,
                        ExternalField {
                            name: "third".to_string(),
                            offset: 8,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        0x34,
                        ExternalField {
                            name: "fourteenth".to_string(),
                            offset: 0x34,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                ]),
            },
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("arg1", Some(CType::ptr(CType::Struct(struct_name)))),
                    ("arg2", Some(CType::Int(32))),
                    ("arg3", Some(CType::Int(32))),
                ],
            )),
            external_type_db: type_db,
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("struct sla_struct_explicit_demo* arg1")
                || output.contains("struct sla_struct_explicit_demo * arg1"),
            "explicit struct-typed header should survive, got:\n{output}"
        );
        assert!(
            output.contains("third"),
            "explicit external field metadata should drive member rendering, got:\n{output}"
        );
        assert!(
            !output.contains("&stack_8") && !output.contains("*(arg2 * 56"),
            "indexed member render should not fall back to stack-rooted pointer math, got:\n{output}"
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_recovers_observed_arm64_struct_array_offsets() {
        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X11", 1, 8),
                    src: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                    src: r2ssa::SSAVar::new("X10", 2, 8),
                },
                SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 1, 1),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 1, 1),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X9", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X9", 4, 8),
                    a: r2ssa::SSAVar::new("X9", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                    src: r2ssa::SSAVar::new("X9", 4, 8),
                },
                SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 2, 1),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 2, 1),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 2, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 2, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                    a: r2ssa::SSAVar::new("X8", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 4, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                    src: r2ssa::SSAVar::new("X10", 4, 8),
                },
                SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 3, 1),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 3, 1),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 3, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 3, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 6, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("X9", 6, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 7, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("X0", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let config = DecompilerConfig::aarch64();
        let function_names = std::collections::HashMap::new();
        let strings = std::collections::HashMap::new();
        let symbols = std::collections::HashMap::new();
        let type_hints = std::collections::HashMap::new();
        let mut param_register_aliases = std::collections::HashMap::new();
        let mut arg_slot_map = std::collections::HashMap::new();
        for (idx, reg_name) in config.arg_regs.iter().enumerate() {
            let arg_name = format!("arg{}", idx + 1);
            for alias in register_alias_names(reg_name) {
                let lower = alias.to_ascii_lowercase();
                param_register_aliases.insert(lower.clone(), arg_name.clone());
                arg_slot_map.insert(lower, idx);
            }
        }
        let env = analysis::PassEnv {
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("x0"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &config.arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &config.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let use_info = analysis::UseInfo::analyze(&blocks, &env);
        let profiles = analysis::use_info::collect_local_struct_field_access_profiles(
            &use_info,
            &func,
            &env,
            &arg_slot_map,
        );
        let accesses = infer_local_struct_field_accesses(&func, &config);
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x8
                && access.is_write),
            "expected store to arg0+0x8 in semantic field accesses, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x34
                && !access.is_write),
            "expected load from arg0+0x34 in semantic field accesses, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_recovers_observed_x86_struct_field_offsets() {
        let block = r2ssa::SSABlock {
            addr: 0x401667,
            size: 42,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RAX", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("EAX", 1, 4),
                    a: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    b: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("RIP", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym.test_struct_field");

        let config = DecompilerConfig::x86_64();
        let function_names = std::collections::HashMap::new();
        let strings = std::collections::HashMap::new();
        let symbols = std::collections::HashMap::new();
        let type_hints = std::collections::HashMap::new();
        let mut param_register_aliases = std::collections::HashMap::new();
        let mut arg_slot_map = std::collections::HashMap::new();
        for (idx, reg_name) in config.arg_regs.iter().enumerate() {
            let arg_name = format!("arg{}", idx + 1);
            for alias in register_alias_names(reg_name) {
                let lower = alias.to_ascii_lowercase();
                param_register_aliases.insert(lower.clone(), arg_name.clone());
                arg_slot_map.insert(lower, idx);
            }
        }
        let env = analysis::PassEnv {
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &config.arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &config.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let use_info = analysis::UseInfo::analyze_for_local_struct_accesses(&blocks, &env);
        let profiles = analysis::use_info::collect_local_struct_field_access_profiles(
            &use_info,
            &func,
            &env,
            &arg_slot_map,
        );
        let accesses = infer_local_struct_field_accesses(&func, &config);
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0
                && !access.is_write),
            "expected load from arg0+0x0, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x30
                && access.is_write),
            "expected store to arg0+0x30, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x30
                && !access.is_write),
            "expected load from arg0+0x30, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_recovers_observed_x86_struct_array_offsets() {
        let block = r2ssa::SSABlock {
            addr: 0x40182f,
            size: 124,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("EAX", 1, 4),
                    src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("RDX", 1, 8),
                    src: r2ssa::SSAVar::new("EAX", 1, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RAX", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 3, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RDX", 2, 8),
                    src: r2ssa::SSAVar::new("RAX", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 5, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("RDX", 3, 8),
                    a: r2ssa::SSAVar::new("RDX", 2, 8),
                    b: r2ssa::SSAVar::new("RAX", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("ECX", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("EAX", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("EAX", 3, 4),
                    a: r2ssa::SSAVar::new("EAX", 2, 4),
                    b: r2ssa::SSAVar::new("ECX", 1, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("RIP", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym.test_struct_array_index");

        let config = DecompilerConfig::x86_64();
        let function_names = std::collections::HashMap::new();
        let strings = std::collections::HashMap::new();
        let symbols = std::collections::HashMap::new();
        let type_hints = std::collections::HashMap::new();
        let mut param_register_aliases = std::collections::HashMap::new();
        let mut arg_slot_map = std::collections::HashMap::new();
        for (idx, reg_name) in config.arg_regs.iter().enumerate() {
            let arg_name = format!("arg{}", idx + 1);
            for alias in register_alias_names(reg_name) {
                let lower = alias.to_ascii_lowercase();
                param_register_aliases.insert(lower.clone(), arg_name.clone());
                arg_slot_map.insert(lower, idx);
            }
        }
        let env = analysis::PassEnv {
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &config.arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &config.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let use_info = analysis::UseInfo::analyze_for_local_struct_accesses(&blocks, &env);
        let profiles = analysis::use_info::collect_local_struct_field_access_profiles(
            &use_info,
            &func,
            &env,
            &arg_slot_map,
        );
        let accesses = infer_local_struct_field_accesses(&func, &config);
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x8
                && access.is_write),
            "expected store to arg0+0x8, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x8
                && !access.is_write),
            "expected load from arg0+0x8, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
        assert!(
            accesses.iter().any(|access| access.arg_index == 0
                && access.field_offset == 0x34
                && !access.is_write),
            "expected load from arg0+0x34, got {accesses:?}; semantic_values={:?}; forwarded={:?}; profiles={profiles:?}",
            use_info.semantic_values,
            use_info.forwarded_values
        );
    }

    #[test]
    fn infer_local_struct_field_accesses_skips_large_dense_switch_cfgs() {
        let mut blocks = Vec::new();

        let mut switch_block = R2ILBlock::new(0x1000, 1);
        switch_block.set_switch_info(r2il::SwitchInfo {
            switch_addr: 0x1000,
            min_val: 0,
            max_val: 39,
            default_target: Some(0x3000),
            cases: (0..40u64)
                .map(|idx| r2il::SwitchCase {
                    value: idx,
                    target: 0x2000 + idx * 0x10,
                })
                .collect(),
        });
        blocks.push(switch_block);

        for idx in 0..110u64 {
            let addr = if idx < 40 {
                0x2000 + idx * 0x10
            } else if idx == 40 {
                0x3000
            } else {
                0x4000 + (idx - 41) * 0x10
            };
            let mut block = R2ILBlock::new(addr, 1);
            block.push(R2ILOp::Return {
                target: Varnode::constant(0, 8),
            });
            blocks.push(block);
        }

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        let accesses = infer_local_struct_field_accesses(&func, &DecompilerConfig::x86_64());
        assert!(
            accesses.is_empty(),
            "large dense switch CFGs should skip semantic local-struct inference, got {accesses:?}"
        );
    }

    #[test]
    fn decompiler_pipeline_keeps_observed_x86_struct_array_load_exprs_semantic_before_return_join()
    {
        use std::collections::HashMap;

        let block = r2ssa::SSABlock {
            addr: 0x40182f,
            size: 124,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("EAX", 1, 4),
                    src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("RDX", 1, 8),
                    src: r2ssa::SSAVar::new("EAX", 1, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RAX", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 3, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RDX", 2, 8),
                    src: r2ssa::SSAVar::new("RAX", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 5, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("RDX", 3, 8),
                    a: r2ssa::SSAVar::new("RDX", 2, 8),
                    b: r2ssa::SSAVar::new("RAX", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("ECX", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("EAX", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("EAX", 3, 4),
                    a: r2ssa::SSAVar::new("EAX", 2, 4),
                    b: r2ssa::SSAVar::new("ECX", 1, 4),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("RIP", 0, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops.clone();
        func = func.with_name("dbg.test_struct_array_index");

        let config = DecompilerConfig::x86_64();
        let mut decompiler = Decompiler::new(config.clone());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(32)),
                vec![
                    (
                        "arr",
                        Some(CType::Pointer(Box::new(CType::Struct(
                            "sla_struct_420703e08f70f00e".to_string(),
                        )))),
                    ),
                    ("idx", Some(CType::Int(32))),
                    ("v", Some(CType::Int(32))),
                ],
            )),
            external_type_db: ExternalTypeDb {
                structs: HashMap::from([(
                    "sla_struct_420703e08f70f00e".to_string(),
                    ExternalStruct {
                        name: "sla_struct_420703e08f70f00e".to_string(),
                        fields: HashMap::from([
                            (
                                8,
                                ExternalField {
                                    name: "f_8".to_string(),
                                    offset: 8,
                                    ty: Some("int32_t".to_string()),
                                },
                            ),
                            (
                                0x34,
                                ExternalField {
                                    name: "f_34".to_string(),
                                    offset: 0x34,
                                    ty: Some("int32_t".to_string()),
                                },
                            ),
                        ])
                        .into_iter()
                        .collect(),
                    },
                )]),
                ..ExternalTypeDb::default()
            },
            ..FunctionTypeFacts::default()
        });

        let normalized_func = normalize::materialize_phis(&func);
        let func = &normalized_func;

        let mut var_recovery = VariableRecovery::new_with_abi(
            &config.sp_name,
            &config.fp_name,
            config.ptr_size,
            config.arg_regs.clone(),
            config.ret_regs.clone(),
        );
        var_recovery.set_type_facts(decompiler.context.type_facts().clone());
        var_recovery.recover(func);

        let mut type_inference = TypeInference::new_with_abi(
            config.ptr_size,
            config.arg_regs.clone(),
            config.ret_regs.clone(),
        );
        type_inference
            .set_external_signature(decompiler.context.type_facts().merged_signature.clone());
        type_inference
            .set_external_stack_slots(decompiler.context.type_facts().stack_slots.clone());
        type_inference
            .set_external_type_db(decompiler.context.type_facts().external_type_db.clone());
        type_inference.set_decompile_prep_facts(func.decompile_prep_facts());
        type_inference.infer_function(func);
        let mut type_hints = type_inference
            .var_type_hints()
            .into_iter()
            .map(|(name, ty)| (name, type_like_to_ctype(&ty)))
            .collect::<HashMap<_, _>>();
        let recovered_param_infos: Vec<_> = var_recovery
            .parameters()
            .iter()
            .map(|v| {
                (
                    v.ssa_var.clone(),
                    ast::CParam {
                        ty: type_like_to_ctype(&type_inference.get_type(&v.ssa_var)),
                        name: v.name.clone(),
                    },
                )
            })
            .collect();
        let params = merge_params_with_external_signature(
            recovered_param_infos
                .iter()
                .map(|(_, param)| param.clone())
                .collect(),
            decompiler.context.type_facts().merged_signature.as_ref(),
        );
        let param_register_aliases = build_param_register_aliases(
            &params,
            &recovered_param_infos,
            &decompiler.context.type_facts().register_params,
            &config.arg_regs,
        );
        for (idx, (_ssa_var, _)) in recovered_param_infos.iter().enumerate() {
            let Some(param) = params.get(idx) else {
                continue;
            };
            let param_ty = param.ty.clone();
            type_hints.insert(param.name.clone(), param_ty.clone());
            type_hints.insert(param.name.to_ascii_lowercase(), param_ty);
        }
        for (reg_alias, param_name) in &param_register_aliases {
            let Some(param) = params.iter().find(|param| param.name == *param_name) else {
                continue;
            };
            type_hints
                .entry(reg_alias.clone())
                .or_insert_with(|| param.ty.clone());
            type_hints
                .entry(reg_alias.to_ascii_lowercase())
                .or_insert_with(|| param.ty.clone());
        }

        let known_function_signatures = HashMap::new();
        let fold_arch = FoldArchConfig {
            ptr_size: config.ptr_size,
            sp_name: config.sp_name.clone(),
            fp_name: config.fp_name.clone(),
            ret_reg_name: config
                .ret_regs
                .first()
                .cloned()
                .unwrap_or_else(|| "rax".to_string()),
            arg_regs: config.arg_regs.clone(),
            caller_saved_regs: config.caller_saved_regs.clone(),
        };
        let combined_type_oracle = type_inference.combined_type_oracle();
        let inferred_ret_type = decompiler.infer_return_type(func, &type_inference);
        let signature_ret_type = decompiler
            .context
            .type_facts()
            .merged_signature
            .as_ref()
            .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype));
        let fold_inputs = FoldInputs {
            arch: &fold_arch,
            function_names: &decompiler.context.function_names,
            strings: &decompiler.context.strings,
            symbols: &decompiler.context.symbols,
            known_function_signatures: &known_function_signatures,
            callee_facts: &decompiler.context.type_facts().callee_facts,
            stack_slots: &decompiler.context.type_facts().stack_slots,
            #[cfg(test)]
            external_stack_vars: &decompiler.context.type_facts().external_stack_vars,
            visible_bindings: &decompiler.context.type_facts().visible_bindings,
            external_type_db: &decompiler.context.type_facts().external_type_db,
            semantic_artifact: decompiler.context.semantic_artifact(),
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle: combined_type_oracle
                .as_ref()
                .map(|oracle| oracle as &dyn TypeOracle),
            function_return_type: signature_ret_type.as_ref().or(Some(&inferred_ret_type)),
            prepared_ssa: None,
            interproc_summary_set: None,
            summary_view: Some(&decompiler.context.function_facts.summary_view),
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
            prepared_predicates: None,
            prepared_call_sites: None,
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        fold_ctx.analyze_blocks(&fold_blocks);
        fold_ctx.analyze_function_structure(func);

        let eax2 = fold_ctx.get_expr(&r2ssa::SSAVar::new("EAX", 2, 4));
        let ecx1 = fold_ctx.get_expr(&r2ssa::SSAVar::new("ECX", 1, 4));
        let stmts = fold_ctx.fold_block(&fold_blocks[0], fold_blocks[0].addr);
        let return_expr = stmts
            .iter()
            .find_map(|stmt| match stmt {
                CStmt::Return(Some(expr)) => Some(expr.clone()),
                _ => None,
            })
            .expect("expected return expression");
        let mut structurer = ControlFlowStructurer::new(func, &fold_ctx);
        let body_stmt = structurer.structure();
        let normalized_body_stmt = fold_ctx.normalize_final_stmt_calls(body_stmt.clone());
        let output = decompiler.decompile(func);

        assert!(
            matches!(eax2, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected decompiler pipeline get_expr(EAX_2) to keep member load, got {eax2:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            matches!(ecx1, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "expected decompiler pipeline get_expr(ECX_1) to keep member load, got {ecx1:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            format!("{return_expr:?}").contains("f_34")
                && format!("{return_expr:?}").contains("f_8"),
            "expected folded return to keep semantic member loads, got {return_expr:?}; eax2={eax2:?}; ecx1={ecx1:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            format!("{body_stmt:?}").contains("f_34") && format!("{body_stmt:?}").contains("f_8"),
            "expected structurer body to keep semantic member loads, got {body_stmt:?}; return_expr={return_expr:?}"
        );
        assert!(
            format!("{normalized_body_stmt:?}").contains("f_34")
                && format!("{normalized_body_stmt:?}").contains("f_8"),
            "expected normalized body to keep semantic member loads, got {normalized_body_stmt:?}; body_stmt={body_stmt:?}"
        );
        assert!(
            output.contains("[idx].f_34") && output.contains("[idx].f_8"),
            "expected final decompile output to keep semantic member loads, got:\n{output}\nbody_stmt={body_stmt:?}\nnormalized_body_stmt={normalized_body_stmt:?}"
        );
    }

    #[test]
    fn decompile_observed_arm64_struct_array_keeps_indexed_member_loads() {
        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("X10", 2, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X9", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X9", 4, 8),
                    a: r2ssa::SSAVar::new("X9", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("X9", 4, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                    a: r2ssa::SSAVar::new("X8", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 4, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("X10", 4, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 6, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("X9", 6, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
                SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 7, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:sum", 1, 8),
                    a: r2ssa::SSAVar::new("X8", 4, 8),
                    b: r2ssa::SSAVar::new("X9", 7, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X0", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:sum", 1, 8),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("PC", 1, 8),
                    src: r2ssa::SSAVar::new("X30", 0, 8),
                },
                SSAOp::Return {
                    target: r2ssa::SSAVar::new("PC", 1, 8),
                },
            ],
        };

        let raw = R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let struct_name = "sla_struct_explicit_demo_full".to_string();
        let mut type_db = ExternalTypeDb::default();
        type_db.structs.insert(
            struct_name.clone(),
            ExternalStruct {
                name: struct_name.clone(),
                fields: std::collections::BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "f_0".to_string(),
                            offset: 0,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "f_8".to_string(),
                            offset: 8,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        0x34,
                        ExternalField {
                            name: "f_34".to_string(),
                            offset: 0x34,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                ]),
            },
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::aarch64());
        decompiler.set_type_facts(FunctionTypeFacts {
            merged_signature: Some(signature_spec(
                Some(CType::Int(64)),
                vec![
                    ("arg1", Some(CType::ptr(CType::Struct(struct_name)))),
                    ("arg2", Some(CType::Int(32))),
                    ("arg3", Some(CType::Int(32))),
                ],
            )),
            external_type_db: type_db,
            ..FunctionTypeFacts::default()
        });

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("[arg2].f_8"),
            "indexed-member path should preserve field 0x8, got:\n{output}"
        );
        assert!(
            output.contains("[arg2].f_34"),
            "indexed-member path should preserve field 0x34, got:\n{output}"
        );
        assert!(
            output.contains("return")
                && !output.contains("*(arg1 +")
                && !output.contains("arg2 * 38"),
            "observed arm64 struct-array return path should stay semantic, got:\n{output}"
        );
    }

    #[test]
    fn decompiler_prepends_vm_semantic_summary_comment() {
        let func = ssa_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &test_arch_for_decompile(),
        );

        let mut decompiler = Decompiler::new(DecompilerConfig::default());
        let vm_step = r2sym::VmStepSummary {
            kind: r2sym::InterpreterKind::SwitchDispatch,
            loop_header: 0x1000,
            dispatch_header: 0x1000,
            selector: Some("vm.sel".to_string()),
            dispatch_targets: vec![0x1004, 0x1008],
            default_target: Some(0x1010),
            case_values_by_target: BTreeMap::from([(0x1004, vec![1, 2]), (0x1008, vec![3])]),
            loop_latches: vec![0x1000],
            state_inputs: vec!["state".to_string(), "pc".to_string()],
            state_outputs: vec!["state".to_string(), "pc".to_string()],
            step_blocks: vec![0x1000, 0x1004],
            handler_regions: BTreeMap::from([(0x1004, vec![0x1004, 0x1008])]),
            handler_state_inputs: BTreeMap::from([(0x1004, vec!["state".to_string()])]),
            handler_state_outputs: BTreeMap::from([(0x1004, vec!["state".to_string()])]),
            handler_state_updates: BTreeMap::from([(
                0x1004,
                vec![r2sym::VmStateUpdate {
                    output: "state".to_string(),
                    expr: "state + 1".to_string(),
                    value: r2sym::VmValueExpr::Expr("state + 1".to_string()),
                    exact: false,
                }],
            )]),
            handler_exit_guards: BTreeMap::from([(
                0x1004,
                vec![r2sym::VmGuardedExit {
                    target: 0x1008,
                    guard: r2sym::VmGuardCondition {
                        expr: "(state == 0x1)".to_string(),
                        value: r2sym::VmValueExpr::Expr("state == 0x1".to_string()),
                        expect_nonzero: true,
                        exact: false,
                    },
                }],
            )]),
            handler_memory_read_effects: BTreeMap::from([(
                0x1004,
                vec![r2sym::VmMemoryCondition {
                    region: r2sym::VmMemoryRegionRef {
                        id: 1,
                        kind: r2sym::MemoryRegionKind::Global,
                        name: "ram:0x2000".to_string(),
                    },
                    offset_lo: 0,
                    offset_hi: 0,
                    size: 1,
                    exact_offset: true,
                    binding: Some("mem:r1:0:1".to_string()),
                    expr: "vm.sel".to_string(),
                    value_expr: None,
                    value: None,
                    exact_value: false,
                }],
            )]),
            handler_memory_write_effects: BTreeMap::from([(
                0x1004,
                vec![r2sym::VmMemoryCondition {
                    region: r2sym::VmMemoryRegionRef {
                        id: 2,
                        kind: r2sym::MemoryRegionKind::Heap,
                        name: "heap_alloc@1".to_string(),
                    },
                    offset_lo: 4,
                    offset_hi: 4,
                    size: 1,
                    exact_offset: true,
                    binding: Some("mem:r2:4:1".to_string()),
                    expr: "state".to_string(),
                    value_expr: Some("state".to_string()),
                    value: Some(r2sym::VmValueExpr::Var("state".to_string())),
                    exact_value: false,
                }],
            )]),
            handler_memory_reads: BTreeMap::from([(0x1004, 1)]),
            handler_memory_writes: BTreeMap::from([(0x1004, 1)]),
            handler_calls: BTreeMap::from([(0x1004, 0)]),
            handler_conditional_branches: BTreeMap::from([(0x1004, 0)]),
            handler_exit_targets: BTreeMap::from([(0x1004, vec![0x1008])]),
            redispatch_handlers: vec![0x1000],
            returning_handlers: vec![],
            truncated_handlers: vec![],
            transfers: vec![r2sym::VmTransferArm {
                handler_target: 0x1004,
                case_values: vec![1, 2],
                region_blocks: vec![0x1004, 0x1008],
                exit_targets: vec![0x1008],
                exit_guards: vec![r2sym::VmGuardedExit {
                    target: 0x1008,
                    guard: r2sym::VmGuardCondition {
                        expr: "(state == 0x1)".to_string(),
                        value: r2sym::VmValueExpr::Expr("state == 0x1".to_string()),
                        expect_nonzero: true,
                        exact: false,
                    },
                }],
                state_updates: vec![r2sym::VmStateUpdate {
                    output: "state".to_string(),
                    expr: "state + 1".to_string(),
                    value: r2sym::VmValueExpr::Expr("state + 1".to_string()),
                    exact: false,
                }],
                selector_update: Some(r2sym::VmStateUpdate {
                    output: "vm.sel".to_string(),
                    expr: "3".to_string(),
                    value: r2sym::VmValueExpr::Const(3),
                    exact: true,
                }),
                memory_reads: vec![r2sym::VmMemoryCondition {
                    region: r2sym::VmMemoryRegionRef {
                        id: 1,
                        kind: r2sym::MemoryRegionKind::Global,
                        name: "ram:0x2000".to_string(),
                    },
                    offset_lo: 0,
                    offset_hi: 0,
                    size: 1,
                    exact_offset: true,
                    binding: Some("mem:r1:0:1".to_string()),
                    expr: "vm.sel".to_string(),
                    value_expr: None,
                    value: None,
                    exact_value: false,
                }],
                memory_writes: vec![r2sym::VmMemoryCondition {
                    region: r2sym::VmMemoryRegionRef {
                        id: 2,
                        kind: r2sym::MemoryRegionKind::Heap,
                        name: "heap_alloc@1".to_string(),
                    },
                    offset_lo: 4,
                    offset_hi: 4,
                    size: 1,
                    exact_offset: true,
                    binding: Some("mem:r2:4:1".to_string()),
                    expr: "state".to_string(),
                    value_expr: Some("state".to_string()),
                    value: Some(r2sym::VmValueExpr::Var("state".to_string())),
                    exact_value: false,
                }],
                residual_guards: false,
                residual_memory_effects: false,
                exact: false,
                redispatch: false,
                may_return: false,
                truncated: false,
            }],
        };
        let semantic_artifact = r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Residual,
            granularity: r2sym::ArtifactGranularity::SummaryOnly,
            execution: r2sym::ExecutionModel::Vm,
            body: r2sym::SemanticArtifactBody::Vm(Box::new(r2sym::VmArtifactBody {
                interpreter: None,
                step_summary: Some(vm_step),
                transfer_summary: None,
            })),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 0,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: false,
                residual_reasons: Vec::new(),
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        };
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        decompiler = decompiler.with_context(
            DecompilerContext::default()
                .with_function_facts(function_facts)
                .with_semantic_route(Some(SemanticRoutePlan::VmSummary {
                    reason: "test-selected vm summary".to_string(),
                })),
        );

        let output = decompiler.decompile(&func);
        assert!(
            output.contains("r2dec semantic summary: vm_summary"),
            "expected VM semantic summary output, got:\n{output}"
        );
        assert!(
            !output.contains("residual_") && !output.contains("state_inputs=["),
            "normal VM rendering should not expose debug-scale internals, got:\n{output}"
        );
        assert!(
            output.contains("switch (vm.sel)")
                && output.contains("case 0x1:")
                && output.contains("handler 0x1004")
                && output.contains("transfer exits=1 guards=1 updates=2 reads=1 writes=1")
                && output.contains("selector updated")
                && !output.contains("state = state + 1;")
                && !output.contains("read ram:0x2000"),
            "expected structured VM summary rendering, got:\n{output}"
        );
    }

    #[test]
    fn preferred_semantic_fallback_comment_allows_ready_large_worker_decompile() {
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                None,
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::Exact,
                    1,
                    1,
                    Vec::new(),
                )),
                r2sym::SemanticEvidence::exact(),
            )],
            Vec::new(),
        );
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region],
        );
        assert!(
            preferred_semantic_fallback_comment("fcn.401000", Some(&semantic_artifact)).is_none(),
            "expected semantically ready autogenerated large worker to keep decompilation path"
        );
        assert!(
            preferred_semantic_fallback_comment("named_worker", Some(&semantic_artifact)).is_none(),
            "expected named function to keep full decompilation path"
        );
    }

    #[test]
    fn preferred_semantic_linearization_reason_allows_ready_large_worker_linear_path() {
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            Vec::new(),
            Vec::new(),
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 107,
            loop_count: 16,
            back_edge_count: 16,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region],
        );
        let reason = preferred_semantic_linearization_reason(
            "fcn.401000",
            Some(&semantic_artifact),
            &summary,
        )
        .expect("ready large worker should prefer linearized decompile path");
        assert!(reason.contains("complex loop graph"));
    }

    #[test]
    fn preferred_semantic_linearization_reason_honors_named_worker_native_linear_plan() {
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            Vec::new(),
            Vec::new(),
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 8,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Residual, Vec::new(), vec![region]);
        let reason = preferred_semantic_linearization_reason(
            "sym._usage",
            Some(&semantic_artifact),
            &summary,
        )
        .expect("named native worker with a linear decompile plan should avoid full structuring");
        assert_eq!(reason, "guarded structuring unavailable");
    }

    #[test]
    fn decompile_input_uses_bounded_summary_for_native_linear_worker() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            Vec::new(),
            vec![
                test_semantic_region(
                    0x401000,
                    BTreeSet::from([0x401010, 0x401020]),
                    Vec::new(),
                    Vec::new(),
                ),
                test_semantic_region(
                    0x401100,
                    BTreeSet::from([0x401110, 0x401120]),
                    Vec::new(),
                    Vec::new(),
                ),
                test_semantic_region(
                    0x401200,
                    BTreeSet::from([0x401210, 0x401220]),
                    Vec::new(),
                    Vec::new(),
                ),
                test_semantic_region(
                    0x401300,
                    BTreeSet::from([0x401310, 0x401320]),
                    Vec::new(),
                    Vec::new(),
                ),
            ],
        );
        let summary_set = r2ssa::InterprocSummarySet {
            diagnostics: r2ssa::InterprocSummaryDiagnostics {
                iterations: 1,
                max_iterations: 1,
                converged: false,
                ..r2ssa::InterprocSummaryDiagnostics::default()
            },
            ..r2ssa::InterprocSummarySet::default()
        };
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Void),
                    vec![("status", Some(CType::Int(32)))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        )
        .with_summary_set(Some(summary_set));
        assert!(function_facts.has_summary_conflicts());
        let context = DecompilerContext::from_function_facts(
            function_facts,
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            64,
        )
        .with_semantic_route(Some(SemanticRoutePlan::LinearWorker {
            reason: "guarded structuring unavailable".to_string(),
        }));
        let input = DecompilerInput::new(prepared, context);
        assert!(input.context.function_facts.has_summary_conflicts());
        let output = Decompiler::new(DecompilerConfig::default()).decompile_input(&input);

        assert!(
            output.contains("void stable_demo(int32_t status)"),
            "expected signature-preserving summary output, got:\n{output}"
        );
        assert!(
            output.contains(
                "r2dec residual: semantic worker summary for guarded structuring unavailable"
            ) && output.contains("native regions: regions=4")
                && !output.contains("loc_"),
            "expected bounded semantic summary instead of linearized SSA blocks, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_renders_native_worker_effects() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::MemoryTransfer,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                memory: None,
                len: Some(r2ssa::SummaryTransferLength::Arg(2)),
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Void),
                    vec![
                        ("dst", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("src", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("len", Some(CType::Int(64))),
                    ],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.copy_worker",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(output.contains("native worker summaries: 1"));
        assert!(
            output.contains("memcpy(dst, src, len);"),
            "expected structured memcpy island, got:\n{output}"
        );
        assert!(output.contains("worker summary: memory_transfer"));
        assert!(output.contains("worker loop: copy len bytes from src to dst"));
        assert!(output.contains("dst=dst"));
        assert!(output.contains("src=src"));
        assert!(output.contains("len=len"));
    }

    #[test]
    fn semantic_worker_summary_renders_dense_native_linear_worker_without_large_cfg_skip() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::GenericLarge,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        for idx in 0..8 {
            native
                .summary
                .worker_summaries
                .push(r2sym::NativeWorkerSummary {
                    anchor: 0x402000 + idx,
                    kind: if idx % 2 == 0 {
                        r2sym::NativeWorkerSummaryKind::MemoryRead
                    } else {
                        r2sym::NativeWorkerSummaryKind::MemoryWrite
                    },
                    dst: None,
                    src: None,
                    memory: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    }),
                    len: None,
                    allocation: None,
                    lifetime: None,
                    sync: None,
                    atomic: None,
                    parser: None,
                    loop_summary: None,
                    evidence: r2sym::SemanticEvidence::likely(
                        r2sym::SemanticEvidenceReason::SummaryBudget,
                    ),
                });
        }
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Void),
                    vec![("buffer", Some(CType::Pointer(Box::new(CType::Void))))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        assert!(matches!(
            function_facts.decompile_plan(),
            Some(r2sym::DecompilePlan::NativeLinear { .. })
        ));

        let output = render_semantic_worker_summary(
            "sym.dense_worker",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("dense native-linear worker summary should render");

        assert!(output.contains("r2dec summary: semantic worker linear summary"));
        assert!(output.contains("native worker summaries: 8"));
        assert!(!output.contains("return summary_result;"));
    }

    #[test]
    fn semantic_worker_summary_does_not_invent_header_params_for_extra_summary_operands() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401010,
                kind: r2sym::NativeWorkerSummaryKind::MemoryTransfer,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                memory: None,
                len: Some(r2ssa::SummaryTransferLength::Arg(2)),
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Void),
                    vec![
                        ("dst", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("src", Some(CType::Pointer(Box::new(CType::Void)))),
                    ],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.copy_worker",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.starts_with("void sym.copy_worker(void* dst, void* src)"),
            "expected canonical signature arity to be preserved, got:\n{output}"
        );
        assert!(!output.contains("(arg2"));
        assert!(!output.contains(", arg2"));
        assert!(!output.contains("=arg2"));
        assert!(output.contains("summary_input2"));
    }

    #[test]
    fn semantic_worker_summary_keeps_unknown_length_transfer_as_residual_comment() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401018,
                kind: r2sym::NativeWorkerSummaryKind::MemoryTransfer,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                memory: None,
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Void),
                    vec![
                        ("dst", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("src", Some(CType::Pointer(Box::new(CType::Void)))),
                    ],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.copy_residual_len",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(output.contains("worker loop: copy unknown bytes from src to dst"));
        assert!(output.contains("worker summary: memory_transfer"));
        assert!(
            !output.contains("memcpy(") && !output.contains("unknown_len"),
            "unknown transfer length should stay residual/comment-only, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_respects_authoritative_empty_signature() {
        let mut semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
        semantic_artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::TableWalk,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Global { address: 0x401020 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(Some(CType::Bool), Vec::new())),
                register_params: vec![
                    ExternalRegisterParamSpec {
                        name: "arg1".to_string(),
                        ty: Some(CTypeLike::Typedef("int64_t".to_string())),
                        reg: "rdx".to_string(),
                    },
                    ExternalRegisterParamSpec {
                        name: "arg2".to_string(),
                        ty: Some(CTypeLike::Typedef("int64_t".to_string())),
                        reg: "r8".to_string(),
                    },
                ],
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "or",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "named native-worker summary projection".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.starts_with("bool or(void)"),
            "expected empty merged signature to suppress register params, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_renders_file_and_fts_worker_families() {
        let mut semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
        semantic_artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::FileTransfer,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                memory: None,
                len: Some(r2ssa::SummaryTransferLength::Arg(2)),
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::DirectoryTraversal,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 3 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        for (idx, kind) in [
            (4, r2sym::NativeWorkerSummaryKind::RecordStream),
            (5, r2sym::NativeWorkerSummaryKind::FieldSelection),
            (6, r2sym::NativeWorkerSummaryKind::FormatRender),
            (7, r2sym::NativeWorkerSummaryKind::SortMerge),
        ] {
            native
                .summary
                .worker_summaries
                .push(r2sym::NativeWorkerSummary {
                    anchor: 0x401020 + (idx as u64 * 0x10),
                    kind,
                    dst: None,
                    src: None,
                    memory: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: idx },
                        range: None,
                    }),
                    len: None,
                    allocation: None,
                    lifetime: None,
                    sync: None,
                    atomic: None,
                    parser: None,
                    loop_summary: None,
                    evidence: r2sym::SemanticEvidence::likely(
                        r2sym::SemanticEvidenceReason::SummaryBudget,
                    ),
                });
        }
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Int(32)),
                    vec![
                        ("src_fd", Some(CType::Int(32))),
                        ("dest_fd", Some(CType::Int(32))),
                        ("len", Some(CType::Int(64))),
                        ("sp", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("stream", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("fields", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("format", Some(CType::Pointer(Box::new(CType::Void)))),
                        ("files", Some(CType::Pointer(Box::new(CType::Void)))),
                    ],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.copy_file_data",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "named file worker summary".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(output.contains("copy_file_data_summary(src_fd, dest_fd, len);"));
        assert!(output.contains("worker summary: file_transfer"));
        assert!(output.contains("worker loop: copy file data from src_fd to dest_fd (len)"));
        assert!(output.contains("worker summary: directory_traversal"));
        assert!(output.contains("traverse directory entries from sp"));
        assert!(output.contains("worker summary: record_stream"));
        assert!(output.contains("read records from stream"));
        assert!(output.contains("worker summary: field_selection"));
        assert!(output.contains("select fields using fields"));
        assert!(output.contains("worker summary: format_render"));
        assert!(output.contains("render formatted output from format"));
        assert!(output.contains("worker summary: sort_merge"));
        assert!(output.contains("merge sorted records from files"));
    }

    #[test]
    fn semantic_worker_summary_renders_program_orchestrator() {
        let mut semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
        semantic_artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::ProgramOrchestrator,
                dst: None,
                src: None,
                memory: None,
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Typedef("int".to_string())),
                    vec![
                        ("argc", Some(CType::Typedef("int".to_string()))),
                        (
                            "argv",
                            Some(CType::Pointer(Box::new(CType::Pointer(Box::new(
                                CType::Int(8),
                            ))))),
                        ),
                        (
                            "envp",
                            Some(CType::Pointer(Box::new(CType::Pointer(Box::new(
                                CType::Int(8),
                            ))))),
                        ),
                    ],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "main",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "named program orchestrator summary".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("program orchestrator summary should render");

        assert!(output.contains("int main(int argc"));
        assert!(output.contains("worker summary: program_orchestrator"));
        assert!(output.contains("run_program_orchestrator(argc, argv, envp);"));
        assert!(output.contains("orchestrate program phases"));
    }

    #[test]
    fn semantic_worker_summary_renders_summary_backed_scan_loop() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::StringScan,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401020,
                    exit_target: Some(0x401040),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                    fold: None,
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym.str_worker",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.contains("scan_string_summary(arg0, 0);"),
            "expected source-like scan summary call, got:\n{output}"
        );
        assert!(!output.contains("_scan_active"));
        assert!(!output.contains("while ("));
        assert!(!output.contains("for ("));
        assert!(output.contains("worker loop: scan arg0 until zero byte"));
        assert!(output.contains("worker summary: string_scan"));
        assert!(output.contains("loop=0x401020"));
        assert!(output.contains("term=zero_byte"));
    }

    #[test]
    fn semantic_worker_summary_renders_numeric_parser_loop() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Numeric,
                    cursor_arg: Some(0),
                    base: Some(10),
                    digit_min: Some(b'0'),
                    digit_max: Some(b'9'),
                    accepts_sign: true,
                }),
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401030,
                    exit_target: Some(0x401060),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::Unknown),
                    fold: None,
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym.parse_worker",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.contains("parse_base10_numeric_summary(arg0);"),
            "expected source-like parser summary call, got:\n{output}"
        );
        assert!(!output.contains("_parse_active"));
        assert!(output.contains("worker loop: parse base10 numeric stream from arg0"));
        assert!(output.contains("parser=base10 numeric"));
        assert!(output.contains("cursor=arg0"));
        assert!(output.contains("sign=true"));
    }

    #[test]
    fn semantic_worker_summary_does_not_invent_return_without_value_evidence() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Compiled,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::MetadataProbe,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Global { address: 0x22fa0 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 0,
                        offset_hi: 7,
                        width: Some(8),
                    }),
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Void),
                    vec![("size", Some(CType::UInt(64)))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "fcn.000068f0",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("metadata summary should render");

        assert!(
            output.starts_with("void fcn.000068f0(uint64_t size)"),
            "expected canonical void return to be preserved, got:\n{output}"
        );
        assert!(!output.contains("return metadata_result;"));
        assert!(output.contains("probe_file_metadata(global_0x22fa0_0_7_w_8);"));
    }

    #[test]
    fn semantic_worker_summary_renders_length_bounded_hash_fold() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401038,
                kind: r2sym::NativeWorkerSummaryKind::HashFold,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 2 },
                    range: None,
                }),
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 0,
                        offset_hi: 0,
                        width: Some(1),
                    }),
                }),
                len: Some(r2ssa::SummaryTransferLength::Arg(1)),
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401038,
                    exit_target: Some(0x401090),
                    iterations: None,
                    length_arg: Some(1),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                    fold: Some(r2sym::NativeWorkerFold {
                        accumulator: "md5_state".to_string(),
                        bits: 32,
                        operation: r2sym::NativeWorkerFoldOperation::RotateMix,
                    }),
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym._md5_process_block",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("hash summary should render");

        assert!(
            output.contains("md5_state = rotate_mix_fold_summary(md5_state, arg0, arg1);"),
            "expected bounded fold summary call, got:\n{output}"
        );
        assert!(!output.contains("_fold_active"));
        assert!(output.contains("worker loop: rotate_mix fold over arg0[0..0;w=1] into md5_state"));
        assert!(output.contains("len=arg1"));
        assert!(output.contains("fold=rotate_mix/md5_state:32"));
    }

    #[test]
    fn semantic_worker_summary_renders_length_bounded_parser_and_scan() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401040,
                kind: r2sym::NativeWorkerSummaryKind::StringScan,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 0,
                        offset_hi: 0,
                        width: Some(1),
                    }),
                }),
                len: Some(r2ssa::SummaryTransferLength::Arg(2)),
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401040,
                    exit_target: Some(0x401080),
                    iterations: None,
                    length_arg: Some(2),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                    fold: None,
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401048,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                len: Some(r2ssa::SummaryTransferLength::Arg(2)),
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Token,
                    cursor_arg: Some(1),
                    base: None,
                    digit_min: None,
                    digit_max: None,
                    accepts_sign: false,
                }),
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401048,
                    exit_target: Some(0x401088),
                    iterations: None,
                    length_arg: Some(2),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                    fold: None,
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym.rpl_mbrtowc",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("parser and scan summary should render");

        assert!(
            output.contains("scan_string_summary(arg1, length_bound);"),
            "expected bounded scan summary call, got:\n{output}"
        );
        assert!(output.contains("scan arg1[0..0;w=1] until length bound"));
        assert!(
            output.contains("parse_token_summary(arg1);"),
            "expected bounded parser summary call, got:\n{output}"
        );
        assert!(!output.contains("_scan_active"));
        assert!(!output.contains("_parse_active"));
        assert!(!output.contains("while ("));
        assert!(!output.contains("for ("));
        assert!(output.contains("worker loop: parse token stream from arg1"));
    }

    #[test]
    fn semantic_worker_summary_renders_diagnostic_wrapper() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401040,
                kind: r2sym::NativeWorkerSummaryKind::DiagnosticWrapper,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym.diagnose",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.contains("diagnose_summary(arg1);"),
            "expected structured diagnostic summary call, got:\n{output}"
        );
        assert!(output.contains("worker loop: diagnose formatted error from arg1"));
        assert!(output.contains("worker summary: diagnostic_wrapper"));
        assert!(output.contains("mem=arg1"));
    }

    #[test]
    fn semantic_worker_summary_renders_format_argument_fetch() {
        let mut semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401050,
                kind: r2sym::NativeWorkerSummaryKind::FormatArgumentFetch,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                memory: None,
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym.printf_fetchargs",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.contains("fetch_printf_arguments(arg0, arg1);"),
            "expected structured printf argument fetch call, got:\n{output}"
        );
        assert!(output.contains("worker loop: fetch printf arguments from arg0 into arg1"));
        assert!(output.contains("worker summary: format_argument_fetch"));
        assert!(output.contains("dst=arg1"));
        assert!(output.contains("src=arg0"));
    }

    #[test]
    fn semantic_worker_summary_renders_native_region_islands() {
        let mut semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Residual, Vec::new(), Vec::new());
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401010,
                anchor: 0x401010,
                kind: r2sym::NativeWorkerSummaryKind::StringScan,
                blocks: BTreeSet::from([0x401010]),
                entries: BTreeSet::from([0x401010]),
                exits: BTreeSet::new(),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    }),
                    dst: None,
                    src: None,
                    len: None,
                    width: Some(1),
                }],
                loop_summary: Some(r2sym::NativeLoopSummary {
                    header: 0x401010,
                    body: BTreeSet::from([0x401010]),
                    entries: BTreeSet::from([0x401010]),
                    exits: BTreeSet::new(),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                }),
                reductions: Vec::new(),
                parser: None,
                residual_reasons: vec![r2sym::ResidualReason::LargeCfg],
                confidence: r2sym::SemanticConfidence::Likely,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401020,
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::HashFold,
                blocks: BTreeSet::from([0x401020]),
                entries: BTreeSet::from([0x401020]),
                exits: BTreeSet::new(),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    }),
                    dst: None,
                    src: None,
                    len: Some(r2ssa::SummaryTransferLength::Const(8)),
                    width: Some(1),
                }],
                loop_summary: None,
                reductions: vec![r2sym::NativeReductionSummary {
                    accumulator: "tmp:2c280_2".to_string(),
                    bits: 64,
                    operation: r2sym::NativeWorkerFoldOperation::Add,
                    source: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    }),
                }],
                parser: None,
                residual_reasons: Vec::new(),
                confidence: r2sym::SemanticConfidence::Likely,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "sym.scan",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "large native worker summarized as typed islands".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("summary island output");

        assert!(output.contains("native summary islands: 2"));
        assert!(
            output.contains("scan_string_summary(arg0, 0);"),
            "expected source-like region scan summary call, got:\n{output}"
        );
        assert!(
            output.contains("accumulator = add_fold_summary(accumulator, arg0, 8U);"),
            "expected raw temporary accumulator to be rendered as a semantic placeholder, got:\n{output}"
        );
        assert!(!output.contains("_scan_active"));
        assert!(!output.contains("tmp:"));
        assert!(!output.contains("while ("));
        assert!(!output.contains("for ("));
        assert!(output.contains("summary island: scan arg0 until zero byte"));
        assert!(output.contains("island summary: string_scan"));
    }

    #[test]
    fn summary_accumulator_label_hides_ssa_register_versions() {
        assert_eq!(summary_accumulator_label("RDX_4"), "accumulator");
        assert_eq!(summary_accumulator_label("tmp:2c280_2"), "accumulator");
        assert_eq!(summary_accumulator_label("sha_state"), "sha_state");
    }

    #[test]
    fn semantic_worker_summary_renders_summary_only_primary_region_without_large_cfg() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401030,
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                blocks: BTreeSet::from([0x401030]),
                entries: BTreeSet::from([0x401030]),
                exits: BTreeSet::new(),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                        range: Some(r2ssa::SummaryMemoryRange {
                            offset_lo: 0,
                            offset_hi: 0,
                            width: Some(1),
                        }),
                    }),
                    dst: None,
                    src: None,
                    len: None,
                    width: Some(1),
                }],
                loop_summary: None,
                reductions: Vec::new(),
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Token,
                    cursor_arg: Some(1),
                    base: None,
                    digit_min: None,
                    digit_max: None,
                    accepts_sign: false,
                }),
                residual_reasons: Vec::new(),
                confidence: r2sym::SemanticConfidence::Likely,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 0,
                        offset_hi: 0,
                        width: Some(1),
                    }),
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Token,
                    cursor_arg: Some(1),
                    base: None,
                    digit_min: None,
                    digit_max: None,
                    accepts_sign: false,
                }),
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "readlinebuffer_delim",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("summary-only primary region should render without a large-cfg skip bit");

        assert!(output.contains("native summary islands: 1"));
        assert!(output.contains("parse_token_summary(arg1);"));
        assert!(!output.contains("_parse_active"));
        assert!(output.contains("summary island: parse token stream from arg1[0..0;w=1]"));
        assert!(output.contains("island summary: parser"));
    }

    #[test]
    fn weak_name_hint_worker_summary_renders_as_comment_not_code() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401080,
                kind: r2sym::NativeWorkerSummaryKind::TableWalk,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401080,
                    exit_target: None,
                    iterations: None,
                    length_arg: None,
                    stride: None,
                    terminator: Some(r2sym::NativeWorkerTerminator::Unknown),
                    fold: None,
                }),
                evidence: r2sym::SemanticEvidence::heuristic(
                    r2sym::SemanticEvidenceReason::NameHint,
                )
                .with_coverage(r2sym::SemanticEvidenceCoverage::Bounded)
                .with_ambiguity(r2sym::SemanticEvidenceAmbiguity::Ranked)
                .with_budget_limited(true),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Int(32)),
                    vec![("table", Some(CType::Pointer(Box::new(CType::Int(8)))))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.name_ranked_table",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("weak summary comments should render");

        assert!(output.contains("worker loop: scan table until unknown"));
        assert!(output.contains("worker summary: table_walk"));
        assert!(!output.contains("walk_table_summary("));
        assert!(!output.contains("return walk_result;"));
        assert!(!output.contains("return summary_result;"));
        assert!(!output.contains("unresolved_return_value"));
        assert!(output.contains("summary return unresolved"));
        assert!(!output.contains("return;"));
    }

    #[test]
    fn weak_format_render_summary_stays_comment_only_without_arg_leak() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            true,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401080,
                kind: r2sym::NativeWorkerSummaryKind::FormatRender,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::heuristic(
                    r2sym::SemanticEvidenceReason::NameHint,
                )
                .with_coverage(r2sym::SemanticEvidenceCoverage::Bounded)
                .with_ambiguity(r2sym::SemanticEvidenceAmbiguity::Ranked)
                .with_budget_limited(true),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(Some(CType::Void), Vec::new())),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "dbg.print_current_files",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "named native-worker summary projection".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("weak format summary should render as bounded summary comments");

        assert!(output.contains("void dbg.print_current_files(void)"));
        assert!(output.contains("worker summary: format_render"));
        assert!(!output.contains("render_formatted_output(summary_input0);"));
        assert!(!output.contains("arg0"));
    }

    #[test]
    fn semantic_summary_return_guard_fills_nonvoid_body_without_return() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::GenericLarge,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401080,
                kind: r2sym::NativeWorkerSummaryKind::MemoryRead,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Unknown,
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                )
                .with_coverage(r2sym::SemanticEvidenceCoverage::Bounded),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(Some(CType::ptr(CType::Int(8))), Vec::new())),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let mut func = CFunction {
            name: "dbg.gettext_quote".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            locals: Vec::new(),
            body: vec![CStmt::Expr(CExpr::call(
                CExpr::var("sym.rpl_mbrtoc32"),
                Vec::new(),
            ))],
        };

        append_semantic_summary_return_to_function_if_needed(&mut func, &function_facts);

        assert!(
            matches!(func.body.last(), Some(CStmt::Comment(text)) if text.contains("summary return unresolved"))
        );
        assert!(
            !func
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "expected unresolved summary return to stay non-executable, got {func:?}"
        );
    }

    #[test]
    fn summary_dense_meaningful_native_structured_worker_routes_to_summary_islands() {
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401000, 0x401020]),
            vec![test_control_fact(
                0x401020,
                r2sym::SymbolicReachabilityStatus::Reachable,
                Some(true),
                Some("cursor != end"),
                Some(compiled_summary(
                    "cursor != end",
                    r2sym::BackwardConditionPrecision::OverApprox,
                    1,
                    1,
                    Vec::new(),
                )),
                r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage),
            )],
            Vec::new(),
        );
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            vec![region],
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        let summary_template = r2sym::NativeRegionSummary {
            stable_id: 0x401010,
            anchor: 0x401010,
            kind: r2sym::NativeWorkerSummaryKind::StringScan,
            blocks: BTreeSet::from([0x401010]),
            entries: BTreeSet::from([0x401010]),
            exits: BTreeSet::new(),
            memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                kind: r2sym::NativeMemoryAccessKind::Read,
                location: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                dst: None,
                src: None,
                len: None,
                width: Some(1),
            }],
            loop_summary: Some(r2sym::NativeLoopSummary {
                header: 0x401010,
                body: BTreeSet::from([0x401010]),
                entries: BTreeSet::from([0x401010]),
                exits: BTreeSet::new(),
                iterations: None,
                length_arg: None,
                stride: Some(1),
                terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
            }),
            reductions: Vec::new(),
            parser: None,
            residual_reasons: Vec::new(),
            confidence: r2sym::SemanticConfidence::Likely,
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        };
        for idx in 0..16 {
            let mut summary = summary_template.clone();
            summary.stable_id += idx;
            summary.anchor += idx;
            native.summary.region_summaries.push(summary);
        }

        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 17,
            loop_count: 2,
            back_edge_count: 2,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let route = planner::semantic_route_plan("dbg.worker", &function_facts, &cfg_summary);
        assert_eq!(
            route,
            planner::SemanticRoutePlan::SummaryIslands {
                reason: "summary-dense semantic worker islands".to_string()
            }
        );
    }

    #[test]
    fn generic_summary_dense_native_linear_worker_uses_standard_route() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        for idx in 0..16 {
            native
                .summary
                .worker_summaries
                .push(r2sym::NativeWorkerSummary {
                    anchor: 0x401000 + idx,
                    kind: r2sym::NativeWorkerSummaryKind::MemoryRead,
                    dst: None,
                    src: None,
                    memory: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: Some(r2ssa::SummaryMemoryRange {
                            offset_lo: idx as i64,
                            offset_hi: idx as i64,
                            width: Some(1),
                        }),
                    }),
                    len: None,
                    allocation: None,
                    lifetime: None,
                    sync: None,
                    atomic: None,
                    parser: None,
                    loop_summary: None,
                    evidence: r2sym::SemanticEvidence::likely(
                        r2sym::SemanticEvidenceReason::SummaryBudget,
                    ),
                });
        }

        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 17,
            loop_count: 2,
            back_edge_count: 2,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let route = planner::semantic_route_plan("dbg.worker", &function_facts, &cfg_summary);
        assert_eq!(route, planner::SemanticRoutePlan::Standard);
    }

    #[test]
    fn dense_summary_only_memory_worker_routes_to_summary_rendering() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        for idx in 0..24 {
            for kind in [
                r2sym::NativeWorkerSummaryKind::MemoryRead,
                r2sym::NativeWorkerSummaryKind::MemoryWrite,
            ] {
                native
                    .summary
                    .worker_summaries
                    .push(r2sym::NativeWorkerSummary {
                        anchor: 0x401000 + idx,
                        kind,
                        dst: None,
                        src: None,
                        memory: Some(r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Unknown,
                            range: Some(r2ssa::SummaryMemoryRange {
                                offset_lo: idx as i64,
                                offset_hi: idx as i64,
                                width: Some(1),
                            }),
                        }),
                        len: None,
                        allocation: None,
                        lifetime: None,
                        sync: None,
                        atomic: None,
                        parser: None,
                        loop_summary: None,
                        evidence: r2sym::SemanticEvidence::likely(
                            r2sym::SemanticEvidenceReason::SummaryBudget,
                        ),
                    });
            }
        }

        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 17,
            loop_count: 2,
            back_edge_count: 2,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let route =
            planner::semantic_route_plan("dbg.readlinebuffer_delim", &function_facts, &cfg_summary);
        assert_eq!(
            route,
            planner::SemanticRoutePlan::SummaryIslands {
                reason: "dense summary-only memory worker".to_string()
            }
        );
    }

    #[test]
    fn primary_summary_only_native_linear_worker_routes_to_summary_rendering() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401050,
                kind: r2sym::NativeWorkerSummaryKind::FormatArgumentFetch,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                memory: None,
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });

        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 39,
            loop_count: 2,
            back_edge_count: 2,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let route =
            planner::semantic_route_plan("sym.printf_fetchargs", &function_facts, &cfg_summary);
        assert_eq!(
            route,
            planner::SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string()
            }
        );
    }

    #[test]
    fn large_memory_read_write_worker_routes_to_summary_islands() {
        let mut semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::Worker,
            true,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        for (idx, (kind, access_kind)) in [
            (
                r2sym::NativeWorkerSummaryKind::MemoryRead,
                r2sym::NativeMemoryAccessKind::Read,
            ),
            (
                r2sym::NativeWorkerSummaryKind::MemoryWrite,
                r2sym::NativeMemoryAccessKind::Write,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            native
                .summary
                .region_summaries
                .push(r2sym::NativeRegionSummary {
                    stable_id: 0x401100 + idx as u64,
                    anchor: 0x401100 + idx as u64,
                    kind,
                    blocks: BTreeSet::from([0x401100 + idx as u64]),
                    entries: BTreeSet::from([0x401100 + idx as u64]),
                    exits: BTreeSet::new(),
                    memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                        kind: access_kind,
                        location: Some(r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Unknown,
                            range: None,
                        }),
                        dst: None,
                        src: None,
                        len: None,
                        width: Some(1),
                    }],
                    loop_summary: None,
                    reductions: Vec::new(),
                    parser: None,
                    residual_reasons: Vec::new(),
                    confidence: r2sym::SemanticConfidence::Likely,
                    evidence: r2sym::SemanticEvidence::likely(
                        r2sym::SemanticEvidenceReason::SummaryBudget,
                    ),
                });
        }
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 229,
            loop_count: 4,
            back_edge_count: 8,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let route = planner::semantic_route_plan(
            "sym.gobble_file.constprop.0",
            &function_facts,
            &cfg_summary,
        );
        assert_eq!(
            route,
            planner::SemanticRoutePlan::SummaryIslands {
                reason: "large native worker summarized as typed islands".to_string()
            }
        );
    }

    #[test]
    fn preferred_semantic_structuring_reason_allows_strict_large_worker_structuring_path() {
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let memory_term = arg_memory_term(0, 1, likely.clone(), Some("0x0:8"), true);
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                None,
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::OverApprox,
                    1,
                    2,
                    vec![memory_term.clone()],
                )),
                likely.clone(),
            )],
            vec![test_memory_fact(memory_term, likely.clone())],
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 107,
            loop_count: 16,
            back_edge_count: 16,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Compiled,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region],
        );
        let reason =
            preferred_semantic_structuring_reason("fcn.401000", Some(&semantic_artifact), &summary)
                .expect("strict ready large worker should prefer structured semantic path");
        assert!(reason.contains("complex loop graph"));
        assert!(
            preferred_semantic_linearization_reason(
                "fcn.401000",
                Some(&semantic_artifact),
                &summary,
            )
            .is_none(),
            "structured-ready worker should not fall back to linearization"
        );
    }

    #[test]
    fn preferred_semantic_structuring_reason_rejects_body_wide_memory_without_target_local_support()
    {
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                None,
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::OverApprox,
                    1,
                    2,
                    Vec::new(),
                )),
                likely.clone(),
            )],
            vec![test_memory_fact(
                arg_memory_term(0, 1, likely.clone(), Some("0x0:8"), true),
                likely.clone(),
            )],
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 107,
            loop_count: 16,
            back_edge_count: 16,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Compiled,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region],
        );
        assert!(
            preferred_semantic_structuring_reason("fcn.401000", Some(&semantic_artifact), &summary)
                .is_none(),
            "body-wide memory support should not overstate semantic structuring readiness"
        );
        assert!(
            preferred_semantic_linearization_reason(
                "fcn.401000",
                Some(&semantic_artifact),
                &summary,
            )
            .is_some(),
            "large workers without target-local structuring support should fall back to linearization"
        );
    }

    #[test]
    fn preferred_semantic_structuring_reason_rejects_ambiguous_target_sources() {
        let exact = r2sym::SemanticEvidence::exact();
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let summary = r2ssa::CFGRiskSummary {
            block_count: 107,
            loop_count: 16,
            back_edge_count: 16,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let region_a = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                Some(true),
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::Exact,
                    1,
                    1,
                    vec![arg_memory_term(0, 1, exact.clone(), Some("0x2a"), true)],
                )),
                exact.clone(),
            )],
            vec![test_memory_fact(
                arg_memory_term(0, 1, exact.clone(), Some("0x2a"), true),
                exact.clone(),
            )],
        );
        let region_b = test_semantic_region(
            0x401004,
            BTreeSet::from([0x401010, 0x401024]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                Some(true),
                Some("y == 1"),
                Some(compiled_summary(
                    "y == 1",
                    r2sym::BackwardConditionPrecision::OverApprox,
                    1,
                    2,
                    vec![arg_memory_term(0, 1, likely.clone(), Some("0x2b"), true)],
                )),
                likely.clone(),
            )],
            vec![test_memory_fact(
                arg_memory_term(0, 1, likely.clone(), Some("0x2b"), true),
                likely.clone(),
            )],
        );
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Compiled,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region_a, region_b],
        );
        assert!(
            semantic_artifact.target_has_ambiguous_sources(0x401010),
            "same-target conflicting worker regions must surface explicit ambiguity"
        );
        assert!(
            preferred_semantic_structuring_reason("fcn.401000", Some(&semantic_artifact), &summary)
                .is_none(),
            "ambiguous target sources must block semantic structuring"
        );
        assert!(
            preferred_semantic_linearization_reason(
                "fcn.401000",
                Some(&semantic_artifact),
                &summary,
            )
            .is_some(),
            "ambiguous target sources should downgrade to linearization instead of structuring"
        );
    }

    #[test]
    fn preferred_semantic_structuring_reason_blocks_conflicting_assumptions_and_downgrades_linearization()
     {
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let memory_term = arg_memory_term(0, 1, likely.clone(), Some("0x0:8"), true);
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                None,
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::OverApprox,
                    1,
                    2,
                    vec![memory_term.clone()],
                )),
                likely.clone(),
            )],
            vec![test_memory_fact(memory_term, likely.clone())],
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 107,
            loop_count: 16,
            back_edge_count: 16,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Compiled,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region],
        );
        let mut assumption_usage = r2ssa::AssumptionUsageReport::default();
        assumption_usage.mark_conflict(
            &r2ssa::AnalysisAssumption {
                id: Some("assumption_a".to_string()),
                subject: r2ssa::AssumptionSubject::Parameter { index: 0 },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "int32_t".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            },
            "parameter type conflict",
        );
        assumption_usage.mark_conflict(
            &r2ssa::AnalysisAssumption {
                id: Some("assumption_b".to_string()),
                subject: r2ssa::AssumptionSubject::Register {
                    name: "rax".to_string(),
                },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "int64_t".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            },
            "register type conflict",
        );
        let function_facts = r2types::FunctionFacts::new(
            r2types::FunctionTypeFacts::default(),
            Some(semantic_artifact),
        )
        .with_assumption_usage(assumption_usage);
        assert!(
            crate::planner::preferred_semantic_structuring_reason(
                "fcn.401000",
                &function_facts,
                &summary,
            )
            .is_none(),
            "assumption conflicts must block semantic structuring"
        );
        let linear_reason = crate::planner::preferred_semantic_linearization_reason(
            "fcn.401000",
            &function_facts,
            &summary,
        )
        .expect("assumption conflicts should downgrade to linearization");
        assert!(linear_reason.contains("complex loop graph"));
    }

    #[test]
    fn autogenerated_name_detection_accepts_underscore_hex_labels() {
        assert!(is_autogenerated_function_name("_140010138"));
        assert!(is_autogenerated_function_name("_401000"));
        assert!(!is_autogenerated_function_name("_named_worker"));
    }

    #[test]
    fn preferred_semantic_structuring_reason_uses_worker_label_when_cfg_is_benign() {
        let exact = r2sym::SemanticEvidence::exact();
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                None,
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::Exact,
                    1,
                    1,
                    vec![arg_memory_term(0, 1, exact.clone(), Some("0x0:8"), true)],
                )),
                exact.clone(),
            )],
            Vec::new(),
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 40,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), vec![region]);
        assert_eq!(
            preferred_semantic_structuring_reason("_140010138", Some(&semantic_artifact), &summary)
                .as_deref(),
            Some("semantic worker islands")
        );
    }

    #[test]
    fn preferred_semantic_structuring_reason_uses_control_only_worker_label_when_cfg_is_benign() {
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                None,
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::OverApprox,
                    1,
                    2,
                    Vec::new(),
                )),
                likely.clone(),
            )],
            Vec::new(),
        );
        let summary = r2ssa::CFGRiskSummary {
            block_count: 40,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), vec![region]);
        assert_eq!(
            preferred_semantic_structuring_reason(
                "_140010138",
                Some(&semantic_artifact),
                &summary,
            )
            .as_deref(),
            Some("semantic worker islands")
        );
        assert!(
            preferred_semantic_linearization_reason(
                "_140010138",
                Some(&semantic_artifact),
                &summary,
            )
            .is_none(),
            "control-only guarded regions should use the structured semantic path"
        );
    }

    #[test]
    fn semantic_fallback_comment_reports_actionable_control_islands() {
        let exact = r2sym::SemanticEvidence::exact();
        let memory_term = arg_memory_term(8, 4, exact.clone(), None, false);
        let region = test_semantic_region(
            0x401000,
            BTreeSet::from([0x401010, 0x401020]),
            vec![test_control_fact(
                0x401010,
                r2sym::SymbolicReachabilityStatus::Reachable,
                Some(true),
                Some("x == 0"),
                Some(compiled_summary(
                    "x == 0",
                    r2sym::BackwardConditionPrecision::Exact,
                    1,
                    1,
                    vec![memory_term.clone()],
                )),
                exact.clone(),
            )],
            vec![test_memory_fact(memory_term, exact.clone())],
        );
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![region],
        );
        let output = semantic_fallback_comment("_401000", Some(&semantic_artifact))
            .expect("typed semantic fallback comment");
        assert!(output.contains("semantic fallback: worker slice in residual mode"));
        assert!(output.contains("regions=1"));
        assert!(output.contains("actionable_conditions=1"));
        assert!(output.contains("exact_conditions=1"));
        assert!(output.contains("actionable_preview=[0x401000: x == 0]"));
    }

    #[test]
    fn semantic_fallback_comment_reports_assumption_conflicts() {
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let mut assumption_usage = r2ssa::AssumptionUsageReport::default();
        assumption_usage.mark_conflict(
            &r2ssa::AnalysisAssumption {
                id: Some("assumption_c".to_string()),
                subject: r2ssa::AssumptionSubject::Parameter { index: 0 },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "int32_t".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            },
            "parameter type conflict",
        );
        assumption_usage.mark_conflict(
            &r2ssa::AnalysisAssumption {
                id: Some("assumption_d".to_string()),
                subject: r2ssa::AssumptionSubject::Register {
                    name: "rdi".to_string(),
                },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "int64_t".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            },
            "register type conflict",
        );
        let function_facts = r2types::FunctionFacts::new(
            r2types::FunctionTypeFacts::default(),
            Some(semantic_artifact),
        )
        .with_assumption_usage(assumption_usage);
        let output =
            crate::consumer_fallback::semantic_fallback_comment("_401000", &function_facts)
                .expect("typed semantic fallback comment");
        assert!(
            output.contains("assumption_conflicts=2"),
            "expected fallback comment to report the assumption conflict count, got:\n{output}"
        );
    }
}
