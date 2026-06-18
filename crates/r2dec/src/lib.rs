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
pub mod highlight;
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
pub use highlight::highlight_c_ansi;
pub use planner::SemanticRoutePlan;
pub use region::{Region, RegionAnalyzer};
pub use structure::{ControlFlowStructurer, ControlRenderProof, ControlRenderProofKind};
pub use variable::VariableRecovery;

use crate::fold::FoldingContext;
use crate::fold::context::{EffectRenderProof, EffectRenderProofKind, FoldArchConfig, FoldInputs};
#[cfg(test)]
use r2il::R2ILBlock;
use r2ssa::SSAFunction;
use r2ssa::SSAOp;
use r2ssa::cfg::BlockTerminator;
use r2types::{
    CTypeLike, ExternalRegisterParamSpec, ExternalTypeDb, FunctionFacts, FunctionSignatureSpec,
    FunctionType, FunctionTypeFacts, StackSlotKey, TypeInference, TypeOracle, VisibleBinding,
    VisibleBindingKind,
};
use std::collections::{BTreeMap, BTreeSet, HashSet};
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

fn should_skip_runtime_type_inference(
    prepared: Option<&r2ssa::SsaArtifact>,
    _type_facts: &FunctionTypeFacts,
    function_facts: &FunctionFacts,
) -> bool {
    let _ = (prepared, function_facts);
    false
}

fn should_use_prepared_semantic_view(
    prepared: Option<&r2ssa::SsaArtifact>,
    function_facts: &FunctionFacts,
) -> bool {
    let _ = function_facts;
    prepared.is_some()
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

fn ctype_hint_specificity(ty: &CType) -> u8 {
    match ty {
        CType::Unknown => 0,
        CType::Void => 1,
        CType::Function { .. } => 2,
        CType::Bool | CType::Int(_) | CType::UInt(_) | CType::Float(_) => 4,
        CType::Typedef(_) | CType::Enum(_) => 5,
        CType::Struct(_) | CType::Union(_) => 6,
        CType::Array(inner, _) => 12 + ctype_hint_specificity(inner).min(12),
        CType::Pointer(inner) => 10 + ctype_hint_specificity(inner).min(12),
    }
}

fn candidate_ctype_hint_is_better(existing: &CType, candidate: &CType) -> bool {
    if integer_same_width_signedness_override(existing, candidate) {
        return true;
    }
    if integer_narrower_canonical_hint(existing, candidate) {
        return true;
    }
    ctype_hint_specificity(candidate) > ctype_hint_specificity(existing)
}

fn integer_same_width_signedness_override(existing: &CType, candidate: &CType) -> bool {
    match (existing, candidate) {
        (CType::Int(bits), CType::UInt(candidate_bits))
        | (CType::UInt(bits), CType::Int(candidate_bits)) => bits == candidate_bits,
        _ => false,
    }
}

fn integer_narrower_canonical_hint(existing: &CType, candidate: &CType) -> bool {
    let (existing_bits, candidate_bits) = match (existing, candidate) {
        (
            CType::Int(existing_bits) | CType::UInt(existing_bits),
            CType::Int(candidate_bits) | CType::UInt(candidate_bits),
        ) => (*existing_bits, *candidate_bits),
        _ => return false,
    };

    matches!(candidate_bits, 8 | 16 | 32) && candidate_bits < existing_bits
}

fn merge_runtime_type_hint(
    type_hints: &mut std::collections::HashMap<String, CType>,
    name: String,
    ty: CType,
) {
    if matches!(ty, CType::Unknown | CType::Void) {
        return;
    }
    type_hints
        .entry(name)
        .and_modify(|existing| {
            if candidate_ctype_hint_is_better(existing, &ty) {
                *existing = ty.clone();
            }
        })
        .or_insert(ty);
}

fn merge_runtime_type_hints(
    type_hints: &mut std::collections::HashMap<String, CType>,
    canonical_hints: std::collections::HashMap<String, CType>,
) {
    for (name, ty) in canonical_hints {
        merge_runtime_type_hint(type_hints, name, ty);
    }
}

fn runtime_type_hint_for_name<'a>(
    type_hints: &'a std::collections::HashMap<String, CType>,
    name: &str,
) -> Option<&'a CType> {
    type_hints
        .get(name)
        .or_else(|| type_hints.get(&name.to_ascii_lowercase()))
}

fn choose_more_specific_runtime_type(base: CType, hint: Option<&CType>) -> CType {
    match hint {
        Some(hint) if candidate_ctype_hint_is_better(&base, hint) => hint.clone(),
        _ => base,
    }
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
    if crate::analysis::utils::is_temporary_constant_or_memory_name(name)
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
    let upper_ssa_label = !base.is_empty()
        && !suffix.is_empty()
        && suffix.bytes().all(|byte| byte.is_ascii_digit())
        && base.bytes().any(|byte| byte.is_ascii_alphabetic())
        && base
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit());
    upper_ssa_label || is_known_lowercase_register_version_label(base, suffix)
}

fn is_known_lowercase_register_version_label(base: &str, suffix: &str) -> bool {
    if suffix.is_empty() || !suffix.bytes().all(|byte| byte.is_ascii_digit()) {
        return false;
    }
    let lower = base.to_ascii_lowercase();
    matches!(
        lower.as_str(),
        "rax"
            | "eax"
            | "ax"
            | "al"
            | "ah"
            | "rbx"
            | "ebx"
            | "bx"
            | "bl"
            | "bh"
            | "rcx"
            | "ecx"
            | "cx"
            | "cl"
            | "ch"
            | "rdx"
            | "edx"
            | "dx"
            | "dl"
            | "dh"
            | "rsi"
            | "esi"
            | "si"
            | "sil"
            | "rdi"
            | "edi"
            | "di"
            | "dil"
            | "rbp"
            | "ebp"
            | "bp"
            | "bpl"
            | "rsp"
            | "esp"
            | "sp"
            | "spl"
            | "rip"
            | "eip"
            | "pc"
            | "x0"
            | "w0"
            | "x1"
            | "w1"
            | "x2"
            | "w2"
            | "x3"
            | "w3"
            | "r0"
            | "r1"
            | "r2"
            | "r3"
            | "a0"
            | "a1"
            | "v0"
            | "v1"
    ) || x86_extended_register_label(&lower)
}

fn x86_extended_register_label(lower: &str) -> bool {
    let Some(rest) = lower.strip_prefix('r') else {
        return false;
    };
    let digit_len = rest
        .bytes()
        .take_while(|byte| byte.is_ascii_digit())
        .count();
    if digit_len == 0 {
        return false;
    }
    let (digits, suffix) = rest.split_at(digit_len);
    digits
        .parse::<u8>()
        .ok()
        .is_some_and(|index| (8..=15).contains(&index))
        && matches!(suffix, "" | "b" | "w" | "d")
}

pub(crate) fn format_vm_summary_kind(kind: r2sym::InterpreterKind) -> &'static str {
    match kind {
        r2sym::InterpreterKind::SwitchDispatch => "switch_dispatch",
        r2sym::InterpreterKind::IndirectDispatch => "indirect_dispatch",
    }
}

#[cfg(test)]
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

fn native_worker_predicate_label(predicate: &r2sym::NativeWorkerPredicate) -> String {
    match predicate {
        r2sym::NativeWorkerPredicate::ByteEqArg { arg } => format!("byte == arg{arg}"),
        r2sym::NativeWorkerPredicate::ByteEqConst { value } => {
            format!("byte == 0x{value:02x}")
        }
        r2sym::NativeWorkerPredicate::AnyOf(predicates) => predicates
            .iter()
            .map(native_worker_predicate_label)
            .collect::<Vec<_>>()
            .join(" || "),
        r2sym::NativeWorkerPredicate::AllOf(predicates) => predicates
            .iter()
            .map(native_worker_predicate_label)
            .collect::<Vec<_>>()
            .join(" && "),
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
        if let Some(predicate) = fold.predicate.as_ref() {
            parts.push(format!(
                "predicate={}",
                native_worker_predicate_label(predicate)
            ));
        }
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
            if let Some(fold) = summary
                .loop_summary
                .as_ref()
                .and_then(|loop_summary| loop_summary.fold.as_ref())
            {
                let accumulator = summary_accumulator_label(&fold.accumulator);
                let memory = summary
                    .memory
                    .as_ref()
                    .map(summary_memory_location_label)
                    .unwrap_or_else(|| "summary_input".to_string());
                let length = summary_worker_length(summary)
                    .map(summary_transfer_length_label)
                    .unwrap_or_else(|| "unknown length".to_string());
                if let Some(predicate) = fold.predicate.as_ref() {
                    return Some(format!(
                        "{} count over {} where {} into {} ({})",
                        native_worker_fold_operation_label(fold.operation),
                        memory,
                        native_worker_predicate_label(predicate),
                        accumulator,
                        length
                    ));
                }
                return Some(format!(
                    "{} fold over {} into {} ({})",
                    native_worker_fold_operation_label(fold.operation),
                    memory,
                    accumulator,
                    length
                ));
            }
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

#[cfg(test)]
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

#[cfg(test)]
pub fn detached_semantic_linearization_reason(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<String> {
    planner::detached_semantic_linearization_reason(func_name, blocks, function_facts)
}

#[cfg(test)]
pub fn detached_semantic_route_plan(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<SemanticRoutePlan> {
    planner::detached_semantic_route_plan(func_name, blocks, function_facts)
}

#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
pub fn cfg_guard_reason_from_summary(summary: &r2ssa::CFGRiskSummary) -> Option<String> {
    planner::cfg_guard_reason_from_summary(summary)
}

#[cfg(test)]
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
    append_semantic_summary_return_to_function_if_needed_with_mode(func, function_facts, true);
}

fn append_semantic_summary_return_comment_to_function_if_needed(
    func: &mut CFunction,
    function_facts: &FunctionFacts,
) {
    append_semantic_summary_return_to_function_if_needed_with_mode(func, function_facts, false);
}

fn append_semantic_summary_return_to_function_if_needed_with_mode(
    func: &mut CFunction,
    function_facts: &FunctionFacts,
    allow_executable_return: bool,
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
    if allow_executable_return
        && let Some(expr) = semantic_summary_return_expr(function_facts, semantic_artifact)
    {
        func.body.push(CStmt::Return(Some(expr)));
    } else {
        func.body.push(CStmt::comment(
            "summary return unresolved; value intentionally not reconstructed".to_string(),
        ));
    }
}

fn looped_standard_output_residual_reason(
    func: &CFunction,
    cfg_summary: &r2ssa::CFGRiskSummary,
) -> Option<String> {
    if cfg_summary.loop_count == 0 && cfg_summary.back_edge_count == 0 {
        return None;
    }
    if func.body.iter().any(stmt_has_empty_loop_body) {
        return Some("unproven loop effects: empty loop body rendered".to_string());
    }
    if !func.body.iter().any(stmt_contains_loop_construct) {
        return Some(
            "unproven loop effects: looped CFG rendered without loop structure".to_string(),
        );
    }
    None
}

#[cfg(test)]
fn certifying_render_residual_reason(
    prepared: Option<&r2ssa::SsaArtifact>,
    cfg_summary: &r2ssa::CFGRiskSummary,
    func: &CFunction,
) -> Option<String> {
    certifying_render_residual_reason_with_proofs(prepared, cfg_summary, func, None)
}

fn certifying_render_residual_reason_with_proofs(
    prepared: Option<&r2ssa::SsaArtifact>,
    cfg_summary: &r2ssa::CFGRiskSummary,
    func: &CFunction,
    render_proofs: Option<&[ControlRenderProof]>,
) -> Option<String> {
    let (rendered, render_proof_failures) =
        function_control_render_nodes_with_proofs(func, render_proofs);
    let inventory = prepared.map(control_certificate_inventory);

    structured_control_residual_reason_for_nodes(
        inventory.as_ref(),
        cfg_summary,
        &rendered,
        &render_proof_failures,
    )
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ControlRenderCounts {
    loops: usize,
    switches: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RenderNodeId(Vec<usize>);

impl RenderNodeId {
    fn root_child(index: usize) -> Self {
        Self(vec![index])
    }

    fn child(&self, index: usize) -> Self {
        let mut path = self.0.clone();
        path.push(index);
        Self(path)
    }
}

impl std::fmt::Display for RenderNodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("stmt:")?;
        for (idx, part) in self.0.iter().enumerate() {
            if idx > 0 {
                f.write_str(".")?;
            }
            write!(f, "{part}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ControlRenderNodeKind {
    Loop,
    Switch,
}

impl ControlRenderNodeKind {
    fn label(self) -> &'static str {
        match self {
            Self::Loop => "loop",
            Self::Switch => "switch",
        }
    }

    fn matches_proof_kind(self, proof_kind: ControlRenderProofKind) -> bool {
        matches!(
            (self, proof_kind),
            (Self::Loop, ControlRenderProofKind::Loop)
                | (Self::Switch, ControlRenderProofKind::Switch)
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ControlRenderNode {
    id: RenderNodeId,
    kind: ControlRenderNodeKind,
    proof_anchor: Option<u64>,
    proof_loop_condition: Option<r2ssa::PredicateId>,
    proof_loop_condition_value: Option<r2ssa::ValueId>,
    proof_loop_body_blocks: Vec<u64>,
    proof_loop_latches: Vec<u64>,
    proof_loop_exits: Vec<u64>,
    proof_switch_selector: Option<r2ssa::ValueId>,
    proof_switch_cases: Vec<(u64, u64)>,
    proof_switch_default: Option<u64>,
    loop_has_condition: bool,
    switch_cases: usize,
    switch_case_values: Vec<u64>,
    switch_has_placeholder_selector: bool,
    switch_has_nonliteral_case: bool,
    switch_has_default: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoopCertificateSummary {
    anchor: u64,
    proof_node: String,
    condition: Option<r2ssa::PredicateId>,
    condition_value: Option<r2ssa::ValueId>,
    body: Vec<u64>,
    latches: Vec<u64>,
    exits: Vec<u64>,
    has_condition: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SwitchCertificateSummary {
    anchor: u64,
    proof_node: String,
    selector: Option<r2ssa::ValueId>,
    case_targets: Vec<(u64, u64)>,
    default_target: Option<u64>,
    cases: usize,
    case_values: Vec<u64>,
    has_default: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ControlCertificateInventory {
    loops: Vec<LoopCertificateSummary>,
    switches: Vec<SwitchCertificateSummary>,
}

impl ControlCertificateInventory {
    fn counts(&self) -> ControlRenderCounts {
        ControlRenderCounts {
            loops: self.loops.len(),
            switches: self.switches.len(),
        }
    }
}

fn control_certificate_inventory(prepared: &r2ssa::SsaArtifact) -> ControlCertificateInventory {
    let certificates = prepared.certificates();
    let predicates = prepared.predicates();
    ControlCertificateInventory {
        loops: certificates
            .loops
            .values()
            .map(|cert| LoopCertificateSummary {
                anchor: cert.header,
                proof_node: cert.proof_node.to_string(),
                condition: cert.condition,
                condition_value: cert.condition.and_then(|id| {
                    predicates
                        .predicates
                        .get(&id)
                        .map(|predicate| predicate.condition)
                }),
                body: sorted_u64s(&cert.body),
                latches: sorted_u64s(&cert.latches),
                exits: sorted_u64s(&cert.exits),
                has_condition: cert.condition.is_some(),
            })
            .collect(),
        switches: certificates
            .switches
            .values()
            .map(|cert| SwitchCertificateSummary {
                anchor: cert.block_addr,
                proof_node: cert.proof_node.to_string(),
                selector: cert.selector,
                case_targets: sorted_switch_cases(&cert.cases),
                default_target: cert.default,
                cases: cert.cases.len(),
                case_values: sorted_switch_case_values(&cert.cases),
                has_default: cert.default.is_some(),
            })
            .collect(),
    }
}

fn sorted_u64s(values: &[u64]) -> Vec<u64> {
    let mut values = values.to_vec();
    values.sort_unstable();
    values
}

fn sorted_switch_cases(cases: &[(u64, u64)]) -> Vec<(u64, u64)> {
    let mut cases = cases.to_vec();
    cases.sort_unstable();
    cases
}

fn sorted_switch_case_values(cases: &[(u64, u64)]) -> Vec<u64> {
    let mut values = cases.iter().map(|(value, _)| *value).collect::<Vec<_>>();
    values.sort_unstable();
    values
}

fn structured_control_residual_reason_for_counts(
    certified: Option<ControlRenderCounts>,
    cfg_summary: &r2ssa::CFGRiskSummary,
    rendered: ControlRenderCounts,
) -> Option<String> {
    let cfg_has_loop = cfg_summary.loop_count > 0 || cfg_summary.back_edge_count > 0;
    let cfg_has_switch = cfg_summary.switch_block_count > 0;
    let rendered_has_control = rendered.loops > 0 || rendered.switches > 0;

    if !cfg_has_loop && !cfg_has_switch && !rendered_has_control {
        return None;
    }

    let Some(certified) = certified else {
        return Some("missing prepared SSA certificates for structured control".to_string());
    };

    let mut reasons = Vec::new();
    if rendered.loops > 0 && !cfg_has_loop {
        reasons.push("rendered loop without loop CFG evidence".to_string());
    }
    if rendered.switches > 0 && !cfg_has_switch {
        reasons.push("rendered switch without switch CFG evidence".to_string());
    }
    if cfg_has_loop && certified.loops == 0 {
        reasons.push("loop CFG without LoopCertificate".to_string());
    }
    if cfg_has_switch && certified.switches == 0 {
        reasons.push("switch CFG without SwitchCertificate".to_string());
    }
    if rendered.loops > certified.loops {
        reasons.push(format!(
            "rendered {} loop construct(s) with only {} LoopCertificate(s)",
            rendered.loops, certified.loops
        ));
    }
    if rendered.loops > 0 && rendered.loops < certified.loops {
        reasons.push(format!(
            "rendered only {} of {} LoopCertificate-backed loop construct(s)",
            rendered.loops, certified.loops
        ));
    }
    if rendered.switches > certified.switches {
        reasons.push(format!(
            "rendered {} switch construct(s) with only {} SwitchCertificate(s)",
            rendered.switches, certified.switches
        ));
    }
    if rendered.switches > 0 && rendered.switches < certified.switches {
        reasons.push(format!(
            "rendered only {} of {} SwitchCertificate-backed switch construct(s)",
            rendered.switches, certified.switches
        ));
    }
    if cfg_has_loop && rendered.loops == 0 {
        reasons.push("loop CFG rendered without loop structure".to_string());
    }
    if cfg_has_switch && rendered.switches == 0 {
        reasons.push("switch CFG rendered without switch structure".to_string());
    }

    if reasons.is_empty() {
        None
    } else {
        Some(format!(
            "uncertified structured control: {}",
            reasons.join(", ")
        ))
    }
}

fn structured_control_residual_reason_for_nodes(
    inventory: Option<&ControlCertificateInventory>,
    cfg_summary: &r2ssa::CFGRiskSummary,
    rendered: &[ControlRenderNode],
    render_proof_failures: &[String],
) -> Option<String> {
    let rendered_counts = control_render_counts_from_nodes(rendered);
    let certified_counts = inventory.map(ControlCertificateInventory::counts);
    let mut reasons = structured_control_residual_reason_for_counts(
        certified_counts,
        cfg_summary,
        rendered_counts,
    )
    .map(|reason| vec![reason])
    .unwrap_or_default();
    reasons.extend(render_proof_failures.iter().cloned());

    if let Some(inventory) = inventory {
        reasons.extend(control_node_certificate_shape_failures(inventory, rendered));
        if !reasons.is_empty() {
            reasons.extend(control_certificate_identity_notes(
                inventory,
                cfg_summary,
                rendered_counts,
            ));
        }
    }

    if reasons.is_empty() {
        None
    } else {
        Some(reasons.join("; "))
    }
}

fn control_render_counts_from_nodes(nodes: &[ControlRenderNode]) -> ControlRenderCounts {
    let mut counts = ControlRenderCounts::default();
    for node in nodes {
        match node.kind {
            ControlRenderNodeKind::Loop => counts.loops += 1,
            ControlRenderNodeKind::Switch => counts.switches += 1,
        }
    }
    counts
}

fn control_certificate_identity_notes(
    inventory: &ControlCertificateInventory,
    cfg_summary: &r2ssa::CFGRiskSummary,
    rendered: ControlRenderCounts,
) -> Vec<String> {
    let mut notes = Vec::new();
    let cfg_has_loop = cfg_summary.loop_count > 0 || cfg_summary.back_edge_count > 0;
    let cfg_has_switch = cfg_summary.switch_block_count > 0;

    if cfg_has_loop
        && (rendered.loops == 0 || rendered.loops > inventory.loops.len())
        && !inventory.loops.is_empty()
    {
        notes.push(format!(
            "available LoopCertificate proof node(s): {}",
            inventory
                .loops
                .iter()
                .map(|cert| format!("{} at 0x{:x}", cert.proof_node, cert.anchor))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if cfg_has_switch
        && (rendered.switches == 0 || rendered.switches > inventory.switches.len())
        && !inventory.switches.is_empty()
    {
        notes.push(format!(
            "available SwitchCertificate proof node(s): {}",
            inventory
                .switches
                .iter()
                .map(|cert| format!("{} at 0x{:x}", cert.proof_node, cert.anchor))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    notes
}

fn control_node_certificate_shape_failures(
    inventory: &ControlCertificateInventory,
    rendered: &[ControlRenderNode],
) -> Vec<String> {
    let mut reasons = Vec::new();
    let loops_by_anchor = inventory
        .loops
        .iter()
        .map(|cert| (cert.anchor, cert))
        .collect::<std::collections::BTreeMap<_, _>>();
    let switches_by_anchor = inventory
        .switches
        .iter()
        .map(|cert| (cert.anchor, cert))
        .collect::<std::collections::BTreeMap<_, _>>();

    for node in rendered {
        match node.kind {
            ControlRenderNodeKind::Loop => {
                let Some(anchor) = node.proof_anchor else {
                    reasons.push(format!(
                        "rendered loop node {} lacks LoopCertificate proof identity",
                        node.id
                    ));
                    continue;
                };
                if !loops_by_anchor.contains_key(&anchor) {
                    reasons.push(format!(
                        "rendered loop node {} proof anchor 0x{:x} has no matching LoopCertificate",
                        node.id, anchor
                    ));
                    continue;
                }
                if let Some(cert) = loops_by_anchor.get(&anchor).copied()
                    && node.loop_has_condition != cert.has_condition
                {
                    reasons.push(format!(
                        "rendered loop node {} condition presence ({}) disagrees with LoopCertificate {} at 0x{:x} ({})",
                        node.id,
                        node.loop_has_condition,
                        cert.proof_node,
                        cert.anchor,
                        cert.has_condition
                    ));
                }
                if let Some(cert) = loops_by_anchor.get(&anchor).copied()
                    && node.proof_loop_condition != cert.condition
                {
                    reasons.push(format!(
                        "rendered loop node {} condition proof {:?} disagrees with LoopCertificate {} at 0x{:x} condition {:?}",
                        node.id,
                        node.proof_loop_condition,
                        cert.proof_node,
                        cert.anchor,
                        cert.condition
                    ));
                }
                if let Some(cert) = loops_by_anchor.get(&anchor).copied()
                    && node.proof_loop_condition_value != cert.condition_value
                {
                    reasons.push(format!(
                        "rendered loop node {} condition value proof {:?} disagrees with LoopCertificate {} at 0x{:x} condition value {:?}",
                        node.id,
                        node.proof_loop_condition_value,
                        cert.proof_node,
                        cert.anchor,
                        cert.condition_value
                    ));
                }
                if let Some(cert) = loops_by_anchor.get(&anchor).copied() {
                    if node.proof_loop_body_blocks != cert.body {
                        reasons.push(format!(
                            "rendered loop node {} body blocks {:?} disagree with LoopCertificate {} at 0x{:x} body {:?}",
                            node.id, node.proof_loop_body_blocks, cert.proof_node, cert.anchor, cert.body
                        ));
                    }
                    if node.proof_loop_latches != cert.latches {
                        reasons.push(format!(
                            "rendered loop node {} latch blocks {:?} disagree with LoopCertificate {} at 0x{:x} latches {:?}",
                            node.id, node.proof_loop_latches, cert.proof_node, cert.anchor, cert.latches
                        ));
                    }
                    if node.proof_loop_exits != cert.exits {
                        reasons.push(format!(
                            "rendered loop node {} exit targets {:?} disagree with LoopCertificate {} at 0x{:x} exits {:?}",
                            node.id, node.proof_loop_exits, cert.proof_node, cert.anchor, cert.exits
                        ));
                    }
                }
            }
            ControlRenderNodeKind::Switch => {
                let Some(anchor) = node.proof_anchor else {
                    reasons.push(format!(
                        "rendered switch node {} lacks SwitchCertificate proof identity",
                        node.id
                    ));
                    continue;
                };
                match switches_by_anchor.get(&anchor).copied() {
                    Some(cert) => {
                        if node.switch_cases != cert.cases {
                            reasons.push(format!(
                                "rendered switch node {} has {} case(s), but SwitchCertificate {} at 0x{:x} has {}",
                                node.id, node.switch_cases, cert.proof_node, cert.anchor, cert.cases
                            ));
                        }
                        if cert.selector.is_some() && node.switch_has_placeholder_selector {
                            reasons.push(format!(
                                "rendered switch node {} uses placeholder selector, but SwitchCertificate {} at 0x{:x} has canonical selector evidence",
                                node.id, cert.proof_node, cert.anchor
                            ));
                        }
                        if node.proof_switch_selector != cert.selector {
                            reasons.push(format!(
                                "rendered switch node {} selector proof {:?} disagrees with SwitchCertificate {} at 0x{:x} selector {:?}",
                                node.id, node.proof_switch_selector, cert.proof_node, cert.anchor, cert.selector
                            ));
                        }
                        if node.proof_switch_cases != cert.case_targets {
                            reasons.push(format!(
                                "rendered switch node {} case targets {:?} disagree with SwitchCertificate {} at 0x{:x} case targets {:?}",
                                node.id, node.proof_switch_cases, cert.proof_node, cert.anchor, cert.case_targets
                            ));
                        }
                        if node.proof_switch_default != cert.default_target {
                            reasons.push(format!(
                                "rendered switch node {} default target {:?} disagrees with SwitchCertificate {} at 0x{:x} default {:?}",
                                node.id, node.proof_switch_default, cert.proof_node, cert.anchor, cert.default_target
                            ));
                        }
                        if node.switch_has_nonliteral_case {
                            reasons.push(format!(
                                "rendered switch node {} has non-literal case value(s), but SwitchCertificate {} at 0x{:x} requires exact case values",
                                node.id, cert.proof_node, cert.anchor
                            ));
                        } else if node.switch_case_values != cert.case_values {
                            reasons.push(format!(
                                "rendered switch node {} case values {:?} disagree with SwitchCertificate {} at 0x{:x} values {:?}",
                                node.id, node.switch_case_values, cert.proof_node, cert.anchor, cert.case_values
                            ));
                        }
                        if node.switch_has_default != cert.has_default {
                            reasons.push(format!(
                                "rendered switch node {} default presence ({}) disagrees with SwitchCertificate {} at 0x{:x} ({})",
                                node.id, node.switch_has_default, cert.proof_node, cert.anchor, cert.has_default
                            ));
                        }
                    }
                    None => reasons.push(format!(
                        "rendered switch node {} proof anchor 0x{:x} has no matching SwitchCertificate",
                        node.id, anchor
                    )),
                }
            }
        }
    }

    reasons
}

#[cfg(test)]
fn function_control_render_counts(func: &CFunction) -> ControlRenderCounts {
    control_render_counts_from_nodes(&function_control_render_nodes(func))
}

#[cfg(test)]
fn function_control_render_nodes(func: &CFunction) -> Vec<ControlRenderNode> {
    function_control_render_nodes_with_proofs(func, None).0
}

fn function_control_render_nodes_with_proofs(
    func: &CFunction,
    render_proofs: Option<&[ControlRenderProof]>,
) -> (Vec<ControlRenderNode>, Vec<String>) {
    let mut nodes = Vec::new();
    for (index, stmt) in func.body.iter().enumerate() {
        collect_stmt_control_render_nodes(stmt, RenderNodeId::root_child(index), &mut nodes);
    }
    let failures = if let Some(render_proofs) = render_proofs {
        attach_control_render_proofs(&mut nodes, render_proofs)
    } else {
        Vec::new()
    };
    (nodes, failures)
}

fn attach_control_render_proofs(
    nodes: &mut [ControlRenderNode],
    render_proofs: &[ControlRenderProof],
) -> Vec<String> {
    let mut failures = Vec::new();
    let mut proof_index = 0;

    for node in nodes {
        let Some(proof) = render_proofs.get(proof_index).cloned() else {
            failures.push(format!(
                "rendered {} node {} lacks render proof identity",
                node.kind.label(),
                node.id
            ));
            continue;
        };
        proof_index += 1;
        if !node.kind.matches_proof_kind(proof.kind) {
            failures.push(format!(
                "rendered {} node {} proof kind mismatch: {:?} at 0x{:x}",
                node.kind.label(),
                node.id,
                proof.kind,
                proof.anchor
            ));
            continue;
        }
        node.proof_anchor = Some(proof.anchor);
        node.proof_loop_condition = proof.loop_condition;
        node.proof_loop_condition_value = proof.loop_condition_value;
        node.proof_loop_body_blocks = proof.loop_body_blocks;
        node.proof_loop_latches = proof.loop_latches;
        node.proof_loop_exits = proof.loop_exits;
        node.proof_switch_selector = proof.switch_selector;
        node.proof_switch_cases = proof.switch_cases;
        node.proof_switch_default = proof.switch_default;
    }

    for proof in &render_proofs[proof_index..] {
        failures.push(format!(
            "render proof identity {:?} at 0x{:x} was not rendered",
            proof.kind, proof.anchor
        ));
    }

    failures
}

fn collect_stmt_control_render_nodes(
    stmt: &CStmt,
    id: RenderNodeId,
    nodes: &mut Vec<ControlRenderNode>,
) {
    match stmt {
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            nodes.push(ControlRenderNode {
                id: id.clone(),
                kind: ControlRenderNodeKind::Loop,
                proof_anchor: None,
                proof_loop_condition: None,
                proof_loop_condition_value: None,
                proof_loop_body_blocks: Vec::new(),
                proof_loop_latches: Vec::new(),
                proof_loop_exits: Vec::new(),
                proof_switch_selector: None,
                proof_switch_cases: Vec::new(),
                proof_switch_default: None,
                loop_has_condition: rendered_loop_has_condition(Some(cond)),
                switch_cases: 0,
                switch_case_values: Vec::new(),
                switch_has_placeholder_selector: false,
                switch_has_nonliteral_case: false,
                switch_has_default: false,
            });
            collect_stmt_control_render_nodes(body, id.child(0), nodes);
        }
        CStmt::For {
            init, cond, body, ..
        } => {
            nodes.push(ControlRenderNode {
                id: id.clone(),
                kind: ControlRenderNodeKind::Loop,
                proof_anchor: None,
                proof_loop_condition: None,
                proof_loop_condition_value: None,
                proof_loop_body_blocks: Vec::new(),
                proof_loop_latches: Vec::new(),
                proof_loop_exits: Vec::new(),
                proof_switch_selector: None,
                proof_switch_cases: Vec::new(),
                proof_switch_default: None,
                loop_has_condition: rendered_loop_has_condition(cond.as_ref()),
                switch_cases: 0,
                switch_case_values: Vec::new(),
                switch_has_placeholder_selector: false,
                switch_has_nonliteral_case: false,
                switch_has_default: false,
            });
            if let Some(init) = init.as_deref() {
                collect_stmt_control_render_nodes(init, id.child(0), nodes);
            }
            collect_stmt_control_render_nodes(body, id.child(1), nodes);
        }
        CStmt::Block(stmts) => {
            for (index, stmt) in stmts.iter().enumerate() {
                collect_stmt_control_render_nodes(stmt, id.child(index), nodes);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            collect_stmt_control_render_nodes(then_body, id.child(0), nodes);
            if let Some(else_body) = else_body.as_deref() {
                collect_stmt_control_render_nodes(else_body, id.child(1), nodes);
            }
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            let mut switch_case_values = cases
                .iter()
                .filter_map(|case| switch_case_value_as_u64(&case.value))
                .collect::<Vec<_>>();
            switch_case_values.sort_unstable();
            nodes.push(ControlRenderNode {
                id: id.clone(),
                kind: ControlRenderNodeKind::Switch,
                proof_anchor: None,
                proof_loop_condition: None,
                proof_loop_condition_value: None,
                proof_loop_body_blocks: Vec::new(),
                proof_loop_latches: Vec::new(),
                proof_loop_exits: Vec::new(),
                proof_switch_selector: None,
                proof_switch_cases: Vec::new(),
                proof_switch_default: None,
                loop_has_condition: false,
                switch_cases: cases.len(),
                switch_has_placeholder_selector: is_placeholder_switch_selector(expr),
                switch_has_nonliteral_case: switch_case_values.len() != cases.len(),
                switch_case_values,
                switch_has_default: default.is_some(),
            });
            for (case_index, case) in cases.iter().enumerate() {
                for (stmt_index, stmt) in case.body.iter().enumerate() {
                    collect_stmt_control_render_nodes(
                        stmt,
                        id.child(case_index).child(stmt_index),
                        nodes,
                    );
                }
            }
            if let Some(default) = default {
                let default_index = cases.len();
                for (stmt_index, stmt) in default.iter().enumerate() {
                    collect_stmt_control_render_nodes(
                        stmt,
                        id.child(default_index).child(stmt_index),
                        nodes,
                    );
                }
            }
        }
        _ => {}
    }
}

fn is_placeholder_switch_selector(expr: &CExpr) -> bool {
    match expr {
        CExpr::Var(name) => matches!(name.as_str(), "test" | "switch_expr"),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            is_placeholder_switch_selector(inner)
        }
        _ => false,
    }
}

fn rendered_loop_has_condition(cond: Option<&CExpr>) -> bool {
    cond.is_some_and(|cond| !is_loop_unconditional_literal(cond))
}

fn is_loop_unconditional_literal(cond: &CExpr) -> bool {
    match cond {
        CExpr::IntLit(_) | CExpr::UIntLit(_) => true,
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            is_loop_unconditional_literal(inner)
        }
        _ => false,
    }
}

fn switch_case_value_as_u64(value: &CExpr) -> Option<u64> {
    match value {
        CExpr::UIntLit(value) => Some(*value),
        CExpr::IntLit(value) => u64::try_from(*value).ok(),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => switch_case_value_as_u64(inner),
        _ => None,
    }
}

fn residual_function_for_unproven_loop(mut func: CFunction, reason: String) -> CFunction {
    func.locals.clear();
    func.body = vec![CStmt::comment(format!(
        "r2dec residual: {}; structured C suppressed until canonical facts prove the rendered effects",
        sanitize_comment_text(&reason)
    ))];
    if !matches!(func.ret_type, CType::Void | CType::Unknown) {
        func.body.push(CStmt::comment(
            "summary return unresolved; value intentionally not reconstructed".to_string(),
        ));
    }
    func
}

fn render_permission_refusal_comment(
    func_name: &str,
    permission: Option<&r2sym::RenderPermission>,
) -> Option<String> {
    let permission = permission?;
    (permission.kind == r2sym::RenderPermissionKind::Refuse)
        .then(|| artifact_guard_fallback_comment(func_name, &permission.reason))
}

fn render_permission_residual_reason(
    permission: Option<&r2sym::RenderPermission>,
) -> Option<String> {
    let permission = permission?;
    match permission.kind {
        r2sym::RenderPermissionKind::Residual => Some(format!(
            "engine render permission residual: {}",
            permission.reason
        )),
        r2sym::RenderPermissionKind::Refuse => Some(format!(
            "engine render permission refusal: {}",
            permission.reason
        )),
        r2sym::RenderPermissionKind::CertifiedC | r2sym::RenderPermissionKind::SummaryComment => {
            None
        }
    }
}

#[derive(Debug, Clone, Default)]
struct CertifiedOutputCounts {
    calls: usize,
    expression_roots: usize,
    returns_with_value: usize,
    memory_like_accesses: usize,
    field_accesses: usize,
    array_accesses: usize,
    field_members: Vec<String>,
    call_nodes: Vec<RenderNodeId>,
    expression_nodes: Vec<RenderNodeId>,
    return_nodes: Vec<RenderNodeId>,
    memory_nodes: Vec<RenderNodeId>,
    field_nodes: Vec<(RenderNodeId, String)>,
    array_nodes: Vec<RenderNodeId>,
}

#[derive(Debug, Clone, Default)]
struct CertifiedEffectProofCounts {
    calls: usize,
    expressions: usize,
    memory_reads: usize,
    memory_writes: usize,
    returns: usize,
}

fn certified_effect_proof_counts(
    effect_render_proofs: &[EffectRenderProof],
) -> CertifiedEffectProofCounts {
    let mut call_sites = BTreeSet::new();
    let mut expressions = 0usize;
    let mut memory_reads = BTreeSet::new();
    let mut memory_writes = BTreeSet::new();
    let mut returns = 0;

    for proof in effect_render_proofs {
        match proof.kind {
            EffectRenderProofKind::Call => {
                call_sites.insert((proof.block_addr, proof.op_idx));
            }
            EffectRenderProofKind::Expression => {
                expressions += 1;
            }
            EffectRenderProofKind::MemoryRead => {
                memory_reads.insert((proof.block_addr, proof.op_idx));
            }
            EffectRenderProofKind::MemoryWrite => {
                memory_writes.insert((proof.block_addr, proof.op_idx));
            }
            EffectRenderProofKind::Return => {
                returns += 1;
            }
        }
    }

    CertifiedEffectProofCounts {
        calls: call_sites.len(),
        expressions,
        memory_reads: memory_reads.len(),
        memory_writes: memory_writes.len(),
        returns,
    }
}

#[cfg(test)]
fn certified_standard_output_residual_reason(
    prepared: &r2ssa::SsaArtifact,
    function_facts: &FunctionFacts,
    func: &CFunction,
) -> Option<String> {
    certified_standard_output_residual_reason_with_effect_proofs(
        prepared,
        function_facts,
        func,
        None,
    )
}

fn certified_standard_output_residual_reason_with_effect_proofs(
    prepared: &r2ssa::SsaArtifact,
    function_facts: &FunctionFacts,
    func: &CFunction,
    effect_render_proofs: Option<&[EffectRenderProof]>,
) -> Option<String> {
    let certificates = prepared.certificates();
    let mut reasons = Vec::new();

    if func.body.is_empty() {
        reasons.push("certified standard route produced no body".to_string());
    }
    for local in &func.locals {
        match local.stack_offset {
            Some(offset)
                if certificates
                    .stack_slots
                    .values()
                    .any(|cert| cert.offset == offset) => {}
            Some(offset) => reasons.push(format!(
                "local {} at stack offset {} lacks StackSlotCertificate",
                local.name, offset
            )),
            None => reasons.push(format!(
                "local {} lacks stack/object certificate in certified mode",
                local.name
            )),
        }
    }

    let mut counts = CertifiedOutputCounts::default();
    let mut raw_names = Vec::new();
    for (index, stmt) in func.body.iter().enumerate() {
        collect_certified_stmt_contract(
            stmt,
            RenderNodeId::root_child(index),
            &mut counts,
            &mut raw_names,
        );
    }

    if let Some(effect_render_proofs) = effect_render_proofs {
        for proof in effect_render_proofs
            .iter()
            .filter(|proof| proof.kind == EffectRenderProofKind::Call)
        {
            match prepared.callsite_certificate_for_op(proof.block_addr, proof.op_idx) {
                Some(cert) => {
                    if proof.target != Some(cert.target) {
                        reasons.push(format!(
                            "rendered call proof at 0x{:x}:{} target proof {:?} disagrees with CallsiteCertificate target {:?}",
                            proof.block_addr, proof.op_idx, proof.target, cert.target
                        ));
                    }
                    let expected = cert
                        .argument_values
                        .iter()
                        .take(proof.values.len())
                        .copied()
                        .collect::<Vec<_>>();
                    if proof.values.len() > cert.argument_values.len() || proof.values != expected {
                        reasons.push(format!(
                            "rendered call proof at 0x{:x}:{} argument value proof {:?} disagrees with CallsiteCertificate argument values {:?}",
                            proof.block_addr, proof.op_idx, proof.values, cert.argument_values
                        ));
                    }
                    for value in &proof.values {
                        if !certificates
                            .expressions
                            .get(value)
                            .is_some_and(|cert| cert.renderable)
                        {
                            reasons.push(format!(
                                "rendered call proof at 0x{:x}:{} argument value {:?} lacks renderable ExpressionCertificate",
                                proof.block_addr, proof.op_idx, value
                            ));
                        }
                    }
                }
                None => {
                    reasons.push(format!(
                        "rendered call proof at 0x{:x}:{} has no matching CallsiteCertificate",
                        proof.block_addr, proof.op_idx
                    ));
                }
            }
        }
        for proof in effect_render_proofs
            .iter()
            .filter(|proof| proof.kind == EffectRenderProofKind::Expression)
        {
            match proof.value.and_then(|value| {
                certificates
                    .expressions
                    .get(&value)
                    .map(|cert| (value, cert))
            }) {
                Some((value, cert)) => {
                    if !cert.renderable {
                        reasons.push(format!(
                            "rendered expression proof at 0x{:x}:{} value {:?} lacks renderable ExpressionCertificate",
                            proof.block_addr, proof.op_idx, value
                        ));
                    }
                    let rendered_inst = prepared
                        .graph()
                        .inst_id_for_op_site(proof.block_addr, proof.op_idx);
                    let defined_at_rendered_site = cert
                        .defining_inst
                        .is_some_and(|inst| Some(inst) == rendered_inst);
                    let consumed_at_rendered_site = rendered_inst
                        .and_then(|inst| prepared.graph().inst(inst))
                        .is_some_and(|inst| inst.inputs.contains(&value));
                    if !defined_at_rendered_site
                        && !consumed_at_rendered_site
                        && !expression_proof_is_materialized_phi_copy(prepared, proof, value, cert)
                    {
                        match cert.defining_inst.and_then(|inst| prepared.inst_op_site(inst)) {
                            Some((block_addr, op_idx)) => reasons.push(format!(
                                "rendered expression proof at 0x{:x}:{} value {:?} was neither defined nor consumed at the rendered op site; value was defined at 0x{:x}:{}",
                                proof.block_addr, proof.op_idx, value, block_addr, op_idx
                            )),
                            None => reasons.push(format!(
                                "rendered expression proof at 0x{:x}:{} value {:?} was not consumed at the rendered op site and lacks defining op-site ExpressionCertificate",
                                proof.block_addr, proof.op_idx, value
                            )),
                        }
                    }
                }
                None => reasons.push(format!(
                    "rendered expression proof at 0x{:x}:{} value {:?} has no matching ExpressionCertificate",
                    proof.block_addr, proof.op_idx, proof.value
                )),
            }
        }
        for proof in effect_render_proofs.iter().filter(|proof| {
            matches!(
                proof.kind,
                EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite
            )
        }) {
            let is_write = proof.kind == EffectRenderProofKind::MemoryWrite;
            match prepared.memory_certificate_for_op_site(proof.block_addr, proof.op_idx, is_write)
            {
                Some(cert) => {
                    if proof.address != Some(cert.address) {
                        reasons.push(format!(
                            "rendered memory proof at 0x{:x}:{} address proof {:?} disagrees with MemoryAccessCertificate address {:?}",
                            proof.block_addr, proof.op_idx, proof.address, cert.address
                        ));
                    }
                    if proof.value != cert.value {
                        reasons.push(format!(
                            "rendered memory proof at 0x{:x}:{} value proof {:?} disagrees with MemoryAccessCertificate value {:?}",
                            proof.block_addr, proof.op_idx, proof.value, cert.value
                        ));
                    }
                }
                None => {
                    reasons.push(format!(
                        "rendered memory proof at 0x{:x}:{} has no matching MemoryAccessCertificate",
                        proof.block_addr, proof.op_idx
                    ));
                }
            }
        }
        for proof in effect_render_proofs
            .iter()
            .filter(|proof| proof.kind == EffectRenderProofKind::Return)
        {
            match prepared.return_certificate_for_op(proof.block_addr, proof.op_idx) {
                Some(cert) => {
                    if proof.value != Some(cert.value) {
                        reasons.push(format!(
                            "rendered return proof at 0x{:x}:{} value proof {:?} disagrees with ReturnValueCertificate value {:?}",
                            proof.block_addr, proof.op_idx, proof.value, cert.value
                        ));
                    }
                    match proof.value.and_then(|value| {
                        certificates
                            .expressions
                            .get(&value)
                            .map(|cert| (value, cert))
                    }) {
                        Some((value, expr_cert)) => {
                            if !expr_cert.renderable {
                                let value_name = prepared
                                    .value_var(value)
                                    .map(|var| var.display_name())
                                    .unwrap_or_else(|| "<unknown>".to_string());
                                reasons.push(format!(
                                    "rendered return proof at 0x{:x}:{} value {:?} ({}) lacks renderable ExpressionCertificate",
                                    proof.block_addr, proof.op_idx, value, value_name
                                ));
                            }
                            let rendered_inst = prepared
                                .graph()
                                .inst_id_for_op_site(proof.block_addr, proof.op_idx);
                            let defined_at_rendered_site = expr_cert
                                .defining_inst
                                .is_some_and(|inst| Some(inst) == rendered_inst);
                            let consumed_at_rendered_site = rendered_inst
                                .and_then(|inst| prepared.graph().inst(inst))
                                .is_some_and(|inst| inst.inputs.contains(&value));
                            if !defined_at_rendered_site && !consumed_at_rendered_site {
                                match expr_cert
                                    .defining_inst
                                    .and_then(|inst| prepared.inst_op_site(inst))
                                {
                                    Some((block_addr, op_idx)) => reasons.push(format!(
                                        "rendered return proof at 0x{:x}:{} value {:?} was neither defined nor consumed at the rendered op site; value was defined at 0x{:x}:{}",
                                        proof.block_addr, proof.op_idx, value, block_addr, op_idx
                                    )),
                                    None => reasons.push(format!(
                                        "rendered return proof at 0x{:x}:{} value {:?} was not consumed at the rendered op site and lacks defining op-site ExpressionCertificate",
                                        proof.block_addr, proof.op_idx, value
                                    )),
                                }
                            }
                        }
                        None => reasons.push(format!(
                            "rendered return proof at 0x{:x}:{} value {:?} has no matching ExpressionCertificate",
                            proof.block_addr, proof.op_idx, proof.value
                        )),
                    }
                }
                None => {
                    reasons.push(format!(
                        "rendered return proof at 0x{:x}:{} has no matching ReturnValueCertificate",
                        proof.block_addr, proof.op_idx
                    ));
                }
            }
        }
        let proof_counts = certified_effect_proof_counts(effect_render_proofs);
        if counts.calls > proof_counts.calls {
            let first_missing = counts
                .call_nodes
                .get(proof_counts.calls)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} call(s) with only {} rendered CallsiteCertificate proof(s){}",
                counts.calls, proof_counts.calls, first_missing
            ));
        }
        if counts.expression_roots > proof_counts.expressions {
            let first_missing = counts
                .expression_nodes
                .get(proof_counts.expressions)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} pure expression assignment(s) with only {} rendered ExpressionCertificate proof(s){}",
                counts.expression_roots, proof_counts.expressions, first_missing
            ));
        }
        let return_proofs = if proof_counts.returns > 0 {
            proof_counts.returns.max(certificates.returns.len())
        } else {
            0
        };
        if counts.returns_with_value > return_proofs {
            let first_missing = counts
                .return_nodes
                .get(return_proofs)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} value return(s) with only {} rendered ReturnValueCertificate proof(s){}",
                counts.returns_with_value, return_proofs, first_missing
            ));
        }
        let raw_memory_proofs = proof_counts.memory_reads + proof_counts.memory_writes;
        let memory_proofs = if raw_memory_proofs > 0
            || (proof_counts.returns > 0 && counts.returns_with_value > proof_counts.returns)
        {
            raw_memory_proofs.max(certificates.memory_accesses.len())
        } else {
            0
        };
        if counts.memory_like_accesses > memory_proofs {
            let first_missing = counts
                .memory_nodes
                .get(memory_proofs)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} memory-like access(es) with only {} rendered MemoryAccessCertificate proof(s){}",
                counts.memory_like_accesses, memory_proofs, first_missing
            ));
        }
    } else {
        if counts.calls > certificates.callsites.len() {
            let first_missing = counts
                .call_nodes
                .get(certificates.callsites.len())
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} call(s) with only {} CallsiteCertificate(s){}",
                counts.calls,
                certificates.callsites.len(),
                first_missing
            ));
        }
        if counts.returns_with_value > certificates.returns.len() {
            let first_missing = counts
                .return_nodes
                .get(certificates.returns.len())
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} value return(s) with only {} ReturnValueCertificate(s){}",
                counts.returns_with_value,
                certificates.returns.len(),
                first_missing
            ));
        }
    }
    if effect_render_proofs.is_none()
        && counts.memory_like_accesses > certificates.memory_accesses.len()
    {
        let first_missing = counts
            .memory_nodes
            .get(certificates.memory_accesses.len())
            .map(|id| format!("; first missing node {id}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} memory-like access(es) with only {} MemoryAccessCertificate(s){}",
            counts.memory_like_accesses,
            certificates.memory_accesses.len(),
            first_missing
        ));
    }
    if counts.field_accesses > 0
        && !field_accesses_are_certified(&function_facts.types, &function_facts.proof, &counts)
    {
        let first_node = counts
            .field_nodes
            .first()
            .map(|(id, member)| format!("; first field node {id}.{member}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} field access(es) without type-layout certificates{}",
            counts.field_accesses, first_node
        ));
    }
    if counts.array_accesses > 0
        && !array_accesses_are_certified(&function_facts.types, &function_facts.proof, &counts)
    {
        let certified_arrays = function_facts
            .proof
            .certified_array_indexes
            .max(function_facts.types.array_index_certificates.len());
        let first_missing = counts
            .array_nodes
            .get(certified_arrays)
            .or_else(|| counts.array_nodes.first())
            .map(|id| format!("; first array node {id}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} array access(es) with only {} ArrayIndexCertificate(s){}",
            counts.array_accesses, certified_arrays, first_missing
        ));
    }
    raw_names.sort();
    raw_names.dedup();
    if !raw_names.is_empty() {
        reasons.push(format!(
            "rendered uncertified raw artifact name(s): {}",
            raw_names.join(", ")
        ));
    }

    if reasons.is_empty() {
        None
    } else {
        Some(format!(
            "certified render contract failed: {}",
            reasons.join("; ")
        ))
    }
}

fn expression_proof_is_materialized_phi_copy(
    prepared: &r2ssa::SsaArtifact,
    proof: &EffectRenderProof,
    value: r2ssa::ValueId,
    cert: &r2ssa::semantic::ExpressionCertificate,
) -> bool {
    if !proof.materialized_phi_copy || cert.value != value {
        return false;
    }
    let Some(def_inst) = cert.defining_inst else {
        return false;
    };
    let Some(inst) = prepared.graph().inst(def_inst) else {
        return false;
    };
    if inst.output != Some(value) {
        return false;
    }
    let r2ssa::InstPayload::Phi { predecessors } = &inst.payload else {
        return false;
    };
    predecessors.iter().any(|pred| {
        prepared
            .graph()
            .block(*pred)
            .is_some_and(|block| block.addr == proof.block_addr)
    })
}

fn array_accesses_are_certified(
    type_facts: &FunctionTypeFacts,
    proof: &r2sym::ProofCoverage,
    counts: &CertifiedOutputCounts,
) -> bool {
    let certified_count = proof
        .certified_array_indexes
        .max(type_facts.array_index_certificates.len());
    if certified_count >= counts.array_accesses {
        return true;
    }
    if type_facts.array_index_certificates.is_empty() {
        return false;
    }
    if counts.field_members.is_empty() {
        return certified_count > 0;
    }

    let certified_names = certified_array_field_names(type_facts);
    !certified_names.is_empty()
        && counts
            .field_members
            .iter()
            .all(|member| certified_names.contains(&member.to_ascii_lowercase()))
}

fn certified_array_field_names(type_facts: &FunctionTypeFacts) -> BTreeSet<String> {
    let certified_offsets = type_facts
        .array_index_certificates
        .iter()
        .map(|cert| cert.field_offset)
        .collect::<BTreeSet<_>>();
    let mut names = BTreeSet::new();

    for cert in &type_facts.field_access_certificates {
        if certified_offsets.contains(&cert.field_offset) {
            names.insert(cert.field_name.to_ascii_lowercase());
        }
    }
    for fields in type_facts.slot_field_profiles.values() {
        for offset in fields.keys() {
            if certified_offsets.contains(offset) {
                names.insert(format!("f_{offset:x}"));
            }
        }
    }
    for structure in type_facts.external_type_db.structs.values() {
        for (offset, field) in &structure.fields {
            if certified_offsets.contains(offset) {
                names.insert(field.name.to_ascii_lowercase());
            }
        }
    }
    for union in type_facts.external_type_db.unions.values() {
        for (offset, field) in &union.fields {
            if certified_offsets.contains(offset) {
                names.insert(field.name.to_ascii_lowercase());
            }
        }
    }

    names
}

fn field_accesses_are_certified(
    type_facts: &FunctionTypeFacts,
    proof: &r2sym::ProofCoverage,
    counts: &CertifiedOutputCounts,
) -> bool {
    let certified_count = proof
        .certified_field_accesses
        .max(type_facts.field_access_certificates.len());
    if certified_count >= counts.field_accesses {
        return true;
    }

    let certified_names = certified_layout_field_names(type_facts);
    !counts.field_members.is_empty()
        && counts
            .field_members
            .iter()
            .all(|member| certified_names.contains(&member.to_ascii_lowercase()))
}

fn certified_layout_field_names(type_facts: &FunctionTypeFacts) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for cert in &type_facts.field_access_certificates {
        names.insert(cert.field_name.to_ascii_lowercase());
    }
    for profile in type_facts.slot_field_profiles.values() {
        for name in profile.values() {
            names.insert(name.to_ascii_lowercase());
        }
    }
    for structure in type_facts.external_type_db.structs.values() {
        for field in structure.fields.values() {
            names.insert(field.name.to_ascii_lowercase());
        }
    }
    for union in type_facts.external_type_db.unions.values() {
        for field in union.fields.values() {
            names.insert(field.name.to_ascii_lowercase());
        }
    }
    names
}

fn collect_certified_stmt_contract(
    stmt: &CStmt,
    id: RenderNodeId,
    counts: &mut CertifiedOutputCounts,
    raw_names: &mut Vec<String>,
) {
    match stmt {
        CStmt::Expr(expr) => {
            if assignment_rhs_requires_expression_certificate(expr) {
                counts.expression_roots += 1;
                counts.expression_nodes.push(id.child(0).child(1));
            }
            collect_certified_expr_contract(expr, id.child(0), counts, raw_names);
        }
        CStmt::Decl { name, init, .. } => {
            if is_uncertified_render_var_name(name) {
                raw_names.push(name.clone());
            }
            if let Some(expr) = init {
                collect_certified_expr_contract(expr, id.child(0), counts, raw_names);
            }
        }
        CStmt::Block(stmts) => {
            for (index, stmt) in stmts.iter().enumerate() {
                collect_certified_stmt_contract(stmt, id.child(index), counts, raw_names);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            collect_certified_expr_contract(cond, id.child(0), counts, raw_names);
            collect_certified_stmt_contract(then_body, id.child(1), counts, raw_names);
            if let Some(else_body) = else_body {
                collect_certified_stmt_contract(else_body, id.child(2), counts, raw_names);
            }
        }
        CStmt::While { cond, body } => {
            collect_certified_expr_contract(cond, id.child(0), counts, raw_names);
            collect_certified_stmt_contract(body, id.child(1), counts, raw_names);
        }
        CStmt::DoWhile { body, cond } => {
            collect_certified_stmt_contract(body, id.child(0), counts, raw_names);
            collect_certified_expr_contract(cond, id.child(1), counts, raw_names);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                collect_certified_stmt_contract(init, id.child(0), counts, raw_names);
            }
            if let Some(cond) = cond {
                collect_certified_expr_contract(cond, id.child(1), counts, raw_names);
            }
            if let Some(update) = update {
                collect_certified_expr_contract(update, id.child(2), counts, raw_names);
            }
            collect_certified_stmt_contract(body, id.child(3), counts, raw_names);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            collect_certified_expr_contract(expr, id.child(0), counts, raw_names);
            for (case_index, case) in cases.iter().enumerate() {
                collect_certified_expr_contract(
                    &case.value,
                    id.child(1).child(case_index),
                    counts,
                    raw_names,
                );
                for (stmt_index, stmt) in case.body.iter().enumerate() {
                    collect_certified_stmt_contract(
                        stmt,
                        id.child(2).child(case_index).child(stmt_index),
                        counts,
                        raw_names,
                    );
                }
            }
            if let Some(default) = default {
                for (stmt_index, stmt) in default.iter().enumerate() {
                    collect_certified_stmt_contract(
                        stmt,
                        id.child(3).child(stmt_index),
                        counts,
                        raw_names,
                    );
                }
            }
        }
        CStmt::Return(Some(expr)) => {
            counts.returns_with_value += 1;
            counts.return_nodes.push(id.clone());
            collect_certified_expr_contract(expr, id.child(0), counts, raw_names);
        }
        CStmt::Return(None)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

fn assignment_rhs_requires_expression_certificate(expr: &CExpr) -> bool {
    let CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    } = expr
    else {
        return false;
    };
    matches!(left.as_ref(), CExpr::Var(_))
        && !certified_expr_contains_memory_like_access(right)
        && !certified_expr_contains_call(right)
}

fn certified_expr_contains_memory_like_access(expr: &CExpr) -> bool {
    let mut found = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Deref(_) | CExpr::Subscript { .. }) {
            found = true;
        }
    });
    found
}

fn certified_expr_contains_call(expr: &CExpr) -> bool {
    let mut found = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Call { .. }) {
            found = true;
        }
    });
    found
}

fn collect_certified_expr_contract(
    expr: &CExpr,
    id: RenderNodeId,
    counts: &mut CertifiedOutputCounts,
    raw_names: &mut Vec<String>,
) {
    match expr {
        CExpr::Var(name) => {
            if is_uncertified_render_var_name(name) {
                raw_names.push(name.clone());
            }
        }
        CExpr::Call { func, args } => {
            counts.calls += 1;
            counts.call_nodes.push(id.clone());
            collect_certified_expr_contract(func, id.child(0), counts, raw_names);
            for (index, arg) in args.iter().enumerate() {
                collect_certified_expr_contract(arg, id.child(index + 1), counts, raw_names);
            }
        }
        CExpr::Subscript { base, index } => {
            counts.memory_like_accesses += 1;
            counts.array_accesses += 1;
            counts.memory_nodes.push(id.clone());
            counts.array_nodes.push(id.clone());
            collect_certified_expr_contract(base, id.child(0), counts, raw_names);
            collect_certified_expr_contract(index, id.child(1), counts, raw_names);
        }
        CExpr::Member { base, member } | CExpr::PtrMember { base, member } => {
            counts.field_accesses += 1;
            counts.field_members.push(member.clone());
            counts.field_nodes.push((id.clone(), member.clone()));
            collect_certified_expr_contract(base, id.child(0), counts, raw_names);
        }
        CExpr::Deref(inner) => {
            counts.memory_like_accesses += 1;
            counts.memory_nodes.push(id.clone());
            collect_certified_expr_contract(inner, id.child(0), counts, raw_names);
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Paren(operand) => {
            collect_certified_expr_contract(operand, id.child(0), counts, raw_names)
        }
        CExpr::Binary { left, right, .. } => {
            collect_certified_expr_contract(left, id.child(0), counts, raw_names);
            collect_certified_expr_contract(right, id.child(1), counts, raw_names);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_certified_expr_contract(cond, id.child(0), counts, raw_names);
            collect_certified_expr_contract(then_expr, id.child(1), counts, raw_names);
            collect_certified_expr_contract(else_expr, id.child(2), counts, raw_names);
        }
        CExpr::Comma(items) => {
            for (index, item) in items.iter().enumerate() {
                collect_certified_expr_contract(item, id.child(index), counts, raw_names);
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

fn is_uncertified_render_var_name(name: &str) -> bool {
    let stripped = name.trim_start_matches('&');
    let lower = stripped.to_ascii_lowercase();
    crate::analysis::utils::is_temporary_name(stripped)
        || lower.starts_with("tmp_")
        || lower.starts_with("unique_")
        || lower.starts_with("stack_")
        || lower.starts_with("local_")
        || lower.starts_with("var_")
        || is_ssa_versioned_register_label(stripped)
}

fn stmt_contains_loop_construct(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::While { .. } | CStmt::DoWhile { .. } | CStmt::For { .. } => true,
        CStmt::Block(stmts) => stmts.iter().any(stmt_contains_loop_construct),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            stmt_contains_loop_construct(then_body)
                || else_body
                    .as_deref()
                    .is_some_and(stmt_contains_loop_construct)
        }
        CStmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .any(|case| case.body.iter().any(stmt_contains_loop_construct))
                || default
                    .as_ref()
                    .is_some_and(|body| body.iter().any(stmt_contains_loop_construct))
        }
        _ => false,
    }
}

fn stmt_has_empty_loop_body(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            !stmt_has_loop_body_content(body) || stmt_has_empty_loop_body(body)
        }
        CStmt::For { body, .. } => {
            !stmt_has_loop_body_content(body) || stmt_has_empty_loop_body(body)
        }
        CStmt::Block(stmts) => stmts.iter().any(stmt_has_empty_loop_body),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            stmt_has_empty_loop_body(then_body)
                || else_body.as_deref().is_some_and(stmt_has_empty_loop_body)
        }
        CStmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .any(|case| case.body.iter().any(stmt_has_empty_loop_body))
                || default
                    .as_ref()
                    .is_some_and(|body| body.iter().any(stmt_has_empty_loop_body))
        }
        _ => false,
    }
}

fn stmt_has_loop_body_content(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => false,
        CStmt::Decl { init: None, .. } => false,
        CStmt::Decl { init: Some(_), .. } => true,
        CStmt::Block(stmts) => stmts.iter().any(stmt_has_loop_body_content),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            stmt_has_loop_body_content(then_body)
                || else_body.as_deref().is_some_and(stmt_has_loop_body_content)
        }
        CStmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .any(|case| case.body.iter().any(stmt_has_loop_body_content))
                || default
                    .as_ref()
                    .is_some_and(|body| body.iter().any(stmt_has_loop_body_content))
        }
        _ => true,
    }
}

fn summary_non_void_return_type(
    function_facts: &FunctionFacts,
    _semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<CType> {
    function_facts
        .types
        .render_authorized_signature()
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
        // A summary rollup describes interprocedural effects, but it is not a
        // render-node proof for the returned expression. Keep the relation
        // visible in comments and residualize until a return certificate owns
        // the exact value.
        r2ssa::SummaryReturnRelation::Unknown
        | r2ssa::SummaryReturnRelation::Void
        | r2ssa::SummaryReturnRelation::Arg(_)
        | r2ssa::SummaryReturnRelation::Const(_)
        | r2ssa::SummaryReturnRelation::HeapAlloc
        | r2ssa::SummaryReturnRelation::Global(_) => None,
    }
}

fn rewrite_summary_arg_labels(output: String, type_facts: &FunctionTypeFacts) -> String {
    let mut replacements: Vec<Option<String>> = Vec::new();
    let extra_index_base;
    if let Some(signature) = type_facts.render_authorized_signature() {
        extra_index_base = 0usize;
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
    } else if !type_facts.register_params.is_empty() {
        extra_index_base = 1usize;
        replacements = type_facts
            .register_params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let name = param.name.trim();
                if name.is_empty() || is_generic_arg_name(name) {
                    Some(format!("summary_input{}", idx + 1))
                } else {
                    Some(name.to_string())
                }
            })
            .collect();
    } else {
        return output;
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
                    .or_else(|| Some(format!("summary_input{}", index + extra_index_base)));
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
    /// Engine-selected permission for the selected route. Missing means legacy
    /// direct r2dec callers still use local certifying gates.
    pub render_permission: Option<r2sym::RenderPermission>,
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
            render_permission: None,
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
            render_permission: None,
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

    pub fn with_render_permission(mut self, permission: Option<r2sym::RenderPermission>) -> Self {
        self.render_permission = permission;
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
        if let Some(comment) =
            render_permission_refusal_comment(&func_name, self.context.render_permission.as_ref())
        {
            return comment;
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
        if let Some(comment) =
            render_permission_refusal_comment(&func_name, input.context.render_permission.as_ref())
        {
            return comment;
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
            type_inference.set_external_signature(
                self.context
                    .type_facts()
                    .render_authorized_signature()
                    .cloned(),
            );
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
        merge_runtime_type_hints(
            &mut type_hints,
            seed_runtime_type_hints_from_facts_and_recovery(
                self.context.type_facts(),
                &var_recovery,
            ),
        );
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
        let render_signature = self.context.type_facts().render_authorized_signature();
        let params = merge_params_with_external_signature(
            recovered_param_infos
                .iter()
                .map(|(_, param)| param.clone())
                .collect(),
            render_signature,
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
                render_signature.and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
            })
            .unwrap_or(CType::Unknown);
        let signature_ret_type =
            render_signature.and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype));
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
        let certified_standard_mode = prepared.is_some()
            && self.context.render_permission.is_some()
            && matches!(semantic_route, planner::SemanticRoutePlan::Standard);
        if certified_standard_mode {
            fold_ctx.clear_effect_render_proofs();
        }

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
        let mut control_render_proofs = if certified_standard_mode {
            structurer.control_render_proofs().to_vec()
        } else {
            Vec::new()
        };
        let mut effect_render_proofs = if certified_standard_mode {
            fold_ctx.effect_render_proofs()
        } else {
            Vec::new()
        };

        if !certified_standard_mode
            && matches!(semantic_route, planner::SemanticRoutePlan::Standard)
            && !Self::stmt_has_content(&body_stmt)
        {
            if let Some(semantic_body) = structurer.structure_semantic_worker_islands(6) {
                body_stmt = consumer_structured::semantic_worker_structured_body(
                    "semantic control islands",
                    semantic_body,
                );
                control_render_proofs.clear();
                effect_render_proofs.clear();
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
                    None,
                    || self.linearize_function_body(func, &fold_ctx),
                );
                use_conservative_locals = empty_fallback.use_conservative_locals;
                is_linear_fallback = empty_fallback.is_linear_fallback;
                body_stmt = empty_fallback.body_stmt;
                control_render_proofs.clear();
                effect_render_proofs.clear();
            }
        }

        if !certified_standard_mode
            || matches!(semantic_route, planner::SemanticRoutePlan::Standard)
        {
            body_stmt = fold_ctx.normalize_final_stmt_calls(body_stmt);
            body_stmt = fold_ctx.prune_dead_temp_assignments_in_stmt(body_stmt);
            if !is_linear_fallback {
                body_stmt = ControlFlowStructurer::cleanup(body_stmt);
            }
        }

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
                    ty: choose_more_specific_runtime_type(
                        type_inference
                            .as_ref()
                            .map(|type_inference| {
                                type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                            })
                            .unwrap_or_else(|| v.ty.clone()),
                        runtime_type_hint_for_name(&type_hints, &v.name),
                    ),
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
                    ty: choose_more_specific_runtime_type(
                        type_inference
                            .as_ref()
                            .map(|type_inference| {
                                type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                            })
                            .unwrap_or_else(|| v.ty.clone()),
                        runtime_type_hint_for_name(&type_hints, &v.name),
                    ),
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
            ret_type: render_signature
                .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                .unwrap_or_else(|| inferred_ret_type.clone()),
            params,
            locals,
            body,
        };
        let appended_stack_return = if !matches!(c_function.ret_type, CType::Void | CType::Unknown)
            && !c_function.body.iter().any(summary_stmt_contains_return)
            && let Some(expr) = fold_ctx.unique_scalar_stack_return_expr()
        {
            c_function.body.push(CStmt::Return(Some(expr)));
            true
        } else {
            false
        };
        if appended_stack_return && certified_standard_mode {
            effect_render_proofs = fold_ctx.effect_render_proofs();
        }
        if certified_standard_mode {
            fold_ctx.prune_duplicate_tail_call_statements(&mut c_function.body);
        }
        if certified_standard_mode {
            append_semantic_summary_return_comment_to_function_if_needed(
                &mut c_function,
                &self.context.function_facts,
            );
        } else {
            append_semantic_summary_return_to_function_if_needed(
                &mut c_function,
                &self.context.function_facts,
            );
        }

        // Apply post-structuring suffix cleanup for folded/unfolded paths.
        // Linear fallback intentionally keeps its raw expression-builder output.
        if !certified_standard_mode && !is_linear_fallback {
            let mut known_function_names = HashSet::new();
            for name in self.context.function_names.values() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            for name in self.context.type_facts().known_function_signatures.keys() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            post_rename::rewrite_function_identifiers(&mut c_function, &known_function_names);
        }
        if !certified_standard_mode {
            rewrite_stack_synonym_uses_to_declared_locals(&mut c_function, &fold_ctx);
            prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx);
            prune_unused_pure_locals(&mut c_function);
        } else if matches!(semantic_route, planner::SemanticRoutePlan::Standard) {
            prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx);
            materialize_certified_raw_carrier_locals(&mut c_function, &fold_ctx);
            prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx);
            prune_unused_pure_locals(&mut c_function);
            if !is_linear_fallback {
                let body = CStmt::Block(std::mem::take(&mut c_function.body));
                c_function.body = self.stmt_to_vec(ControlFlowStructurer::cleanup(body));
            }
        }
        if matches!(semantic_route, planner::SemanticRoutePlan::Standard) {
            let residual_reason =
                render_permission_residual_reason(self.context.render_permission.as_ref())
                    .or_else(|| {
                        (prepared.is_some()
                            && matches!(semantic_route, planner::SemanticRoutePlan::Standard))
                        .then(|| {
                            certified_standard_output_residual_reason_with_effect_proofs(
                                prepared.expect("certified mode requires prepared SSA"),
                                &self.context.function_facts,
                                &c_function,
                                certified_standard_mode.then_some(effect_render_proofs.as_slice()),
                            )
                        })?
                    })
                    .or_else(|| {
                        certifying_render_residual_reason_with_proofs(
                            prepared,
                            &func.cfg_risk_summary(),
                            &c_function,
                            certified_standard_mode.then_some(control_render_proofs.as_slice()),
                        )
                    })
                    .or_else(|| {
                        looped_standard_output_residual_reason(
                            &c_function,
                            &func.cfg_risk_summary(),
                        )
                    });

            if let Some(reason) = residual_reason {
                c_function = residual_function_for_unproven_loop(c_function, reason);
            }
        }

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

fn rewrite_stmt_var_aliases(
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
        CStmt::Expr(expr) => rewrite_expr_var_aliases(expr, rename_map, true),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                rewrite_expr_var_aliases(init, rename_map, true);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                rewrite_stmt_var_aliases(stmt, rename_map);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rewrite_expr_var_aliases(cond, rename_map, true);
            rewrite_stmt_var_aliases(then_body, rename_map);
            if let Some(else_body) = else_body {
                rewrite_stmt_var_aliases(else_body, rename_map);
            }
        }
        CStmt::While { cond, body } => {
            rewrite_expr_var_aliases(cond, rename_map, true);
            rewrite_stmt_var_aliases(body, rename_map);
        }
        CStmt::DoWhile { body, cond } => {
            rewrite_stmt_var_aliases(body, rename_map);
            rewrite_expr_var_aliases(cond, rename_map, true);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                rewrite_stmt_var_aliases(init, rename_map);
            }
            if let Some(cond) = cond {
                rewrite_expr_var_aliases(cond, rename_map, true);
            }
            if let Some(update) = update {
                rewrite_expr_var_aliases(update, rename_map, true);
            }
            rewrite_stmt_var_aliases(body, rename_map);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            rewrite_expr_var_aliases(expr, rename_map, true);
            for case in cases {
                rewrite_expr_var_aliases(&mut case.value, rename_map, true);
                for stmt in &mut case.body {
                    rewrite_stmt_var_aliases(stmt, rename_map);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    rewrite_stmt_var_aliases(stmt, rename_map);
                }
            }
        }
        CStmt::Return(expr) => {
            if let Some(expr) = expr {
                rewrite_expr_var_aliases(expr, rename_map, true);
            }
        }
    }
}

fn rewrite_expr_var_aliases(
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
            rewrite_expr_var_aliases(operand, rename_map, allow_plain_var_rewrite);
        }
        CExpr::AddrOf(operand) => {
            rewrite_expr_var_aliases(operand, rename_map, false);
        }
        CExpr::Deref(operand) => {
            rewrite_expr_var_aliases(operand, rename_map, false);
        }
        CExpr::Binary { left, right, .. } => {
            rewrite_expr_var_aliases(left, rename_map, allow_plain_var_rewrite);
            rewrite_expr_var_aliases(right, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            rewrite_expr_var_aliases(cond, rename_map, allow_plain_var_rewrite);
            rewrite_expr_var_aliases(then_expr, rename_map, allow_plain_var_rewrite);
            rewrite_expr_var_aliases(else_expr, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Call { func, args } => {
            rewrite_expr_var_aliases(func, rename_map, allow_plain_var_rewrite);
            for arg in args {
                rewrite_expr_var_aliases(arg, rename_map, allow_plain_var_rewrite);
            }
        }
        CExpr::Subscript { base, index } => {
            rewrite_expr_var_aliases(base, rename_map, allow_plain_var_rewrite);
            rewrite_expr_var_aliases(index, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            rewrite_expr_var_aliases(base, rename_map, allow_plain_var_rewrite);
        }
        CExpr::Comma(items) => {
            for item in items {
                rewrite_expr_var_aliases(item, rename_map, allow_plain_var_rewrite);
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
        rewrite_stmt_var_aliases(stmt, &rename_map);
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

fn materialize_certified_raw_carrier_locals(func: &mut CFunction, fold_ctx: &FoldingContext<'_>) {
    let mut assigned = Vec::new();
    collect_raw_carrier_assignment_names(&func.body, &mut assigned);
    let mut referenced = assigned.clone();
    collect_raw_carrier_read_names(&func.body, &mut referenced);
    if referenced.is_empty() {
        return;
    }

    let mut used_names = collect_stmt_var_names(&func.body);
    used_names.extend(
        func.params
            .iter()
            .map(|param| param.name.to_ascii_lowercase()),
    );
    used_names.extend(
        func.locals
            .iter()
            .map(|local| local.name.to_ascii_lowercase()),
    );

    let mut rename_map = BTreeMap::new();
    let mut carrier_defs = BTreeMap::new();
    let assigned_set = assigned
        .iter()
        .map(|name| name.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    for raw in referenced {
        let lower = raw.to_ascii_lowercase();
        if rename_map.contains_key(&lower) {
            continue;
        }
        if !assigned_set.contains(&lower) {
            let Some(definition) = fold_ctx.certified_raw_carrier_definition(&raw) else {
                continue;
            };
            carrier_defs.insert(lower.clone(), definition);
        }
        let mut index = rename_map.len();
        let clean = loop {
            let candidate = format!("value_{index}");
            if !used_names.contains(&candidate) {
                used_names.insert(candidate.clone());
                break candidate;
            }
            index += 1;
        };
        rename_map.insert(lower, (clean, certified_raw_carrier_type(&raw)));
    }

    let mut declared = HashSet::new();
    rewrite_certified_raw_carrier_stmts(&mut func.body, &rename_map, &carrier_defs, &mut declared);
}

fn collect_raw_carrier_assignment_names(stmts: &[CStmt], out: &mut Vec<String>) {
    for stmt in stmts {
        match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                ..
            }) => {
                if let CExpr::Var(name) = left.as_ref()
                    && is_ssa_versioned_register_label(name)
                {
                    out.push(name.clone());
                }
            }
            CStmt::Decl { name, .. } if is_ssa_versioned_register_label(name) => {
                out.push(name.clone());
            }
            CStmt::Block(stmts) => collect_raw_carrier_assignment_names(stmts, out),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_raw_carrier_assignment_names_from_stmt(then_body, out);
                if let Some(else_body) = else_body {
                    collect_raw_carrier_assignment_names_from_stmt(else_body, out);
                }
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } | CStmt::For { body, .. } => {
                collect_raw_carrier_assignment_names_from_stmt(body, out)
            }
            CStmt::Switch { cases, default, .. } => {
                for case in cases {
                    collect_raw_carrier_assignment_names(&case.body, out);
                }
                if let Some(default) = default {
                    collect_raw_carrier_assignment_names(default, out);
                }
            }
            _ => {}
        }
    }
}

fn collect_raw_carrier_assignment_names_from_stmt(stmt: &CStmt, out: &mut Vec<String>) {
    collect_raw_carrier_assignment_names(std::slice::from_ref(stmt), out);
}

fn collect_raw_carrier_read_names(stmts: &[CStmt], out: &mut Vec<String>) {
    for stmt in stmts {
        match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            }) => {
                collect_raw_carrier_read_names_from_expr(right, out);
                if !matches!(left.as_ref(), CExpr::Var(name) if is_ssa_versioned_register_label(name))
                {
                    collect_raw_carrier_read_names_from_expr(left, out);
                }
            }
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
                collect_raw_carrier_read_names_from_expr(expr, out);
            }
            CStmt::Decl {
                init: Some(expr), ..
            } => collect_raw_carrier_read_names_from_expr(expr, out),
            CStmt::Block(stmts) => collect_raw_carrier_read_names(stmts, out),
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                collect_raw_carrier_read_names_from_expr(cond, out);
                collect_raw_carrier_read_names_from_stmt(then_body, out);
                if let Some(else_body) = else_body {
                    collect_raw_carrier_read_names_from_stmt(else_body, out);
                }
            }
            CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
                collect_raw_carrier_read_names_from_expr(cond, out);
                collect_raw_carrier_read_names_from_stmt(body, out);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    collect_raw_carrier_read_names_from_stmt(init, out);
                }
                if let Some(cond) = cond {
                    collect_raw_carrier_read_names_from_expr(cond, out);
                }
                if let Some(update) = update {
                    collect_raw_carrier_read_names_from_expr(update, out);
                }
                collect_raw_carrier_read_names_from_stmt(body, out);
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                collect_raw_carrier_read_names_from_expr(expr, out);
                for case in cases {
                    collect_raw_carrier_read_names_from_expr(&case.value, out);
                    collect_raw_carrier_read_names(&case.body, out);
                }
                if let Some(default) = default {
                    collect_raw_carrier_read_names(default, out);
                }
            }
            CStmt::Decl { init: None, .. }
            | CStmt::Return(None)
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_)
            | CStmt::Empty => {}
        }
    }
}

fn collect_raw_carrier_read_names_from_stmt(stmt: &CStmt, out: &mut Vec<String>) {
    collect_raw_carrier_read_names(std::slice::from_ref(stmt), out);
}

fn collect_raw_carrier_read_names_from_expr(expr: &CExpr, out: &mut Vec<String>) {
    match expr {
        CExpr::Var(name) if is_ssa_versioned_register_label(name) => out.push(name.clone()),
        CExpr::Deref(inner) | CExpr::AddrOf(inner) | CExpr::Paren(inner) | CExpr::Sizeof(inner) => {
            collect_raw_carrier_read_names_from_expr(inner, out)
        }
        CExpr::Cast { expr, .. } | CExpr::Unary { operand: expr, .. } => {
            collect_raw_carrier_read_names_from_expr(expr, out);
        }
        CExpr::Binary { left, right, .. } => {
            collect_raw_carrier_read_names_from_expr(left, out);
            collect_raw_carrier_read_names_from_expr(right, out);
        }
        CExpr::Subscript { base, index } => {
            collect_raw_carrier_read_names_from_expr(base, out);
            collect_raw_carrier_read_names_from_expr(index, out);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            collect_raw_carrier_read_names_from_expr(base, out);
        }
        CExpr::Call { func, args } => {
            collect_raw_carrier_read_names_from_expr(func, out);
            for arg in args {
                collect_raw_carrier_read_names_from_expr(arg, out);
            }
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_raw_carrier_read_names_from_expr(cond, out);
            collect_raw_carrier_read_names_from_expr(then_expr, out);
            collect_raw_carrier_read_names_from_expr(else_expr, out);
        }
        CExpr::Comma(items) => {
            for item in items {
                collect_raw_carrier_read_names_from_expr(item, out);
            }
        }
        _ => {}
    }
}

fn rewrite_certified_raw_carrier_stmts(
    stmts: &mut Vec<CStmt>,
    rename_map: &BTreeMap<String, (String, CType)>,
    carrier_defs: &BTreeMap<String, CExpr>,
    declared: &mut HashSet<String>,
) {
    let mut rewritten = Vec::with_capacity(stmts.len());
    for mut stmt in std::mem::take(stmts) {
        let mut reads = Vec::new();
        collect_raw_carrier_read_names_from_stmt(&stmt, &mut reads);
        for raw in reads {
            let lower = raw.to_ascii_lowercase();
            if declared.contains(&lower) {
                continue;
            }
            let Some((clean, ty)) = rename_map.get(&lower) else {
                continue;
            };
            let Some(mut init) = carrier_defs.get(&lower).cloned() else {
                continue;
            };
            rewrite_certified_raw_carrier_expr(&mut init, rename_map);
            declared.insert(lower);
            rewritten.push(CStmt::Decl {
                ty: ty.clone(),
                name: clean.clone(),
                init: Some(init),
            });
        }
        rewrite_certified_raw_carrier_stmt(&mut stmt, rename_map, carrier_defs, declared);
        rewritten.push(stmt);
    }
    *stmts = rewritten;
}

fn rewrite_certified_raw_carrier_stmt(
    stmt: &mut CStmt,
    rename_map: &BTreeMap<String, (String, CType)>,
    carrier_defs: &BTreeMap<String, CExpr>,
    declared: &mut HashSet<String>,
) {
    match stmt {
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) => {
            rewrite_certified_raw_carrier_expr(right, rename_map);
            if let CExpr::Var(raw_name) = left.as_ref() {
                let lower = raw_name.to_ascii_lowercase();
                if let Some((clean, ty)) = rename_map.get(&lower) {
                    if declared.insert(lower) {
                        *stmt = CStmt::Decl {
                            ty: ty.clone(),
                            name: clean.clone(),
                            init: Some((**right).clone()),
                        };
                    } else {
                        **left = CExpr::Var(clean.clone());
                    }
                    return;
                }
            }
            rewrite_certified_raw_carrier_expr(left, rename_map);
        }
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            rewrite_certified_raw_carrier_expr(expr, rename_map);
        }
        CStmt::Decl { ty, name, init } => {
            if let Some(init) = init {
                rewrite_certified_raw_carrier_expr(init, rename_map);
            }
            let lower = name.to_ascii_lowercase();
            if let Some((clean, clean_ty)) = rename_map.get(&lower) {
                *name = clean.clone();
                *ty = clean_ty.clone();
                declared.insert(lower);
            }
        }
        CStmt::Block(stmts) => {
            rewrite_certified_raw_carrier_stmts(stmts, rename_map, carrier_defs, declared)
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rewrite_certified_raw_carrier_expr(cond, rename_map);
            rewrite_certified_raw_carrier_stmt(then_body, rename_map, carrier_defs, declared);
            if let Some(else_body) = else_body {
                rewrite_certified_raw_carrier_stmt(else_body, rename_map, carrier_defs, declared);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            rewrite_certified_raw_carrier_expr(cond, rename_map);
            rewrite_certified_raw_carrier_stmt(body, rename_map, carrier_defs, declared);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                rewrite_certified_raw_carrier_stmt(init, rename_map, carrier_defs, declared);
            }
            if let Some(cond) = cond {
                rewrite_certified_raw_carrier_expr(cond, rename_map);
            }
            if let Some(update) = update {
                rewrite_certified_raw_carrier_expr(update, rename_map);
            }
            rewrite_certified_raw_carrier_stmt(body, rename_map, carrier_defs, declared);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            rewrite_certified_raw_carrier_expr(expr, rename_map);
            for case in cases {
                rewrite_certified_raw_carrier_expr(&mut case.value, rename_map);
                rewrite_certified_raw_carrier_stmts(
                    &mut case.body,
                    rename_map,
                    carrier_defs,
                    declared,
                );
            }
            if let Some(default) = default {
                rewrite_certified_raw_carrier_stmts(default, rename_map, carrier_defs, declared);
            }
        }
        CStmt::Return(None)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_)
        | CStmt::Empty => {}
    }
}

fn rewrite_certified_raw_carrier_expr(
    expr: &mut CExpr,
    rename_map: &BTreeMap<String, (String, CType)>,
) {
    match expr {
        CExpr::Var(name) => {
            if let Some((clean, _)) = rename_map.get(&name.to_ascii_lowercase()) {
                *name = clean.clone();
            }
        }
        CExpr::Deref(inner) | CExpr::AddrOf(inner) | CExpr::Paren(inner) | CExpr::Sizeof(inner) => {
            rewrite_certified_raw_carrier_expr(inner, rename_map)
        }
        CExpr::Cast { expr, .. } | CExpr::Unary { operand: expr, .. } => {
            rewrite_certified_raw_carrier_expr(expr, rename_map);
        }
        CExpr::Binary { left, right, .. } => {
            rewrite_certified_raw_carrier_expr(left, rename_map);
            rewrite_certified_raw_carrier_expr(right, rename_map);
        }
        CExpr::Subscript { base, index } => {
            rewrite_certified_raw_carrier_expr(base, rename_map);
            rewrite_certified_raw_carrier_expr(index, rename_map);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            rewrite_certified_raw_carrier_expr(base, rename_map);
        }
        CExpr::Call { func, args } => {
            rewrite_certified_raw_carrier_expr(func, rename_map);
            for arg in args {
                rewrite_certified_raw_carrier_expr(arg, rename_map);
            }
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            rewrite_certified_raw_carrier_expr(cond, rename_map);
            rewrite_certified_raw_carrier_expr(then_expr, rename_map);
            rewrite_certified_raw_carrier_expr(else_expr, rename_map);
        }
        CExpr::Comma(items) => {
            for item in items {
                rewrite_certified_raw_carrier_expr(item, rename_map);
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

fn certified_raw_carrier_type(name: &str) -> CType {
    let base = name
        .rsplit_once('_')
        .map(|(base, _)| base)
        .unwrap_or(name)
        .to_ascii_lowercase();
    match base.as_str() {
        "al" | "ah" | "bl" | "bh" | "cl" | "ch" | "dl" | "dh" => CType::i8(),
        "ax" | "bx" | "cx" | "dx" | "si" | "di" | "bp" | "sp" => CType::i16(),
        base if base.starts_with('e') || base.starts_with('w') => CType::i32(),
        _ => CType::i64(),
    }
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
                role_identity: None,
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
        ArrayIndexBase, ArrayIndexCertificate, ExternalField, ExternalRegisterParamSpec,
        ExternalStruct, FieldAccessCertificate, FunctionFacts, FunctionParamSpec,
        FunctionSignatureSpec, FunctionTypeFacts,
    };
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    fn ssa_from_ops(ops: Vec<R2ILOp>, arch: &ArchSpec) -> SSAFunction {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        SSAFunction::from_blocks_with_arch(&[block], Some(arch))
            .expect("SSA function should build")
            .with_name("stable_demo")
    }

    #[test]
    fn runtime_type_hints_prefer_canonical_typed_pointer_over_inferred_void_pointer() {
        let mut hints = HashMap::from([("buf".to_string(), CType::Pointer(Box::new(CType::Void)))]);
        merge_runtime_type_hints(
            &mut hints,
            HashMap::from([("buf".to_string(), CType::Pointer(Box::new(CType::Int(8))))]),
        );

        assert_eq!(
            hints.get("buf"),
            Some(&CType::Pointer(Box::new(CType::Int(8))))
        );
        assert_eq!(
            choose_more_specific_runtime_type(
                CType::Pointer(Box::new(CType::Void)),
                hints.get("buf")
            ),
            CType::Pointer(Box::new(CType::Int(8)))
        );
    }

    #[test]
    fn runtime_type_hints_preserve_same_width_canonical_signedness() {
        assert_eq!(
            choose_more_specific_runtime_type(CType::Int(8), Some(&CType::UInt(8))),
            CType::UInt(8)
        );
        assert_eq!(
            choose_more_specific_runtime_type(CType::UInt(8), Some(&CType::Int(8))),
            CType::Int(8)
        );
    }

    #[test]
    fn runtime_type_hints_prefer_canonical_narrow_integer_over_carrier_width() {
        assert_eq!(
            choose_more_specific_runtime_type(CType::Int(64), Some(&CType::UInt(8))),
            CType::UInt(8)
        );
        assert_eq!(
            choose_more_specific_runtime_type(CType::UInt(64), Some(&CType::Int(16))),
            CType::Int(16)
        );
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

    fn expression_value_for_op(
        prepared: &r2ssa::SsaArtifact,
        block_addr: u64,
        op_idx: usize,
    ) -> r2ssa::ValueId {
        let inst = prepared
            .graph()
            .inst_id_for_op_site(block_addr, op_idx)
            .expect("prepared op-site should have graph inst");
        prepared
            .certificates()
            .expressions
            .iter()
            .find_map(|(value, cert)| (cert.defining_inst == Some(inst)).then_some(*value))
            .expect("prepared op-site should define expression value")
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

    fn external_signature_certificate(
        signature: &FunctionSignatureSpec,
    ) -> Option<r2types::SignatureCertificate> {
        r2types::SignatureCertificate::from_signature(
            signature,
            [r2types::SignatureCertificateSource::ExternalContext],
        )
    }

    fn loop_cfg_summary() -> r2ssa::CFGRiskSummary {
        r2ssa::CFGRiskSummary {
            block_count: 4,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 0,
            max_switch_cases: 0,
        }
    }

    fn switch_cfg_summary() -> r2ssa::CFGRiskSummary {
        r2ssa::CFGRiskSummary {
            block_count: 4,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 1,
            max_switch_cases: 2,
        }
    }

    #[test]
    fn looped_standard_output_refuses_loop_cfg_without_rendered_loop_structure() {
        let func = CFunction::new("loop_fold", CType::u64()).with_body(vec![CStmt::Return(Some(
            CExpr::UIntLit(0x14650fb0739d0383),
        ))]);

        let reason = looped_standard_output_residual_reason(&func, &loop_cfg_summary())
            .expect("looped CFG without a loop construct must refuse structured output");
        assert!(reason.contains("without loop structure"), "{reason}");

        let residual = residual_function_for_unproven_loop(func, reason);
        assert!(residual.locals.is_empty());
        assert!(residual.body.iter().any(|stmt| matches!(
            stmt,
            CStmt::Comment(text) if text.contains("r2dec residual")
        )));
        assert!(residual.body.iter().any(|stmt| matches!(
            stmt,
            CStmt::Comment(text) if text.contains("summary return unresolved")
        )));
    }

    #[test]
    fn standard_structured_output_requires_prepared_control_certificates() {
        let func = CFunction::new("loop_fold", CType::u64());
        let reason = certifying_render_residual_reason(None, &loop_cfg_summary(), &func)
            .expect("missing certificates should refuse loop rendering");

        assert!(
            reason.contains("missing prepared SSA certificates"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_rendered_loop_without_cfg_evidence() {
        let func =
            CFunction::new("spurious_loop", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let cfg = r2ssa::CFGRiskSummary {
            block_count: 1,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let reason = structured_control_residual_reason_for_counts(
            Some(ControlRenderCounts {
                loops: 1,
                switches: 0,
            }),
            &cfg,
            function_control_render_counts(&func),
        )
        .expect("rendered loop without CFG loop evidence must be residualized");

        assert!(
            reason.contains("rendered loop without loop CFG evidence"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_switch_cfg_without_rendered_switch_structure() {
        let func = CFunction::new("switch_fold", CType::u64())
            .with_body(vec![CStmt::Return(Some(CExpr::uint(0)))]);

        let reason = structured_control_residual_reason_for_counts(
            Some(ControlRenderCounts {
                loops: 0,
                switches: 1,
            }),
            &switch_cfg_summary(),
            function_control_render_counts(&func),
        )
        .expect("switch CFG rendered without switch structure must be residualized");

        assert!(
            reason.contains("switch CFG rendered without switch structure"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_more_switches_than_certificates() {
        let func = CFunction::new("extra_switch", CType::u64()).with_body(vec![
            CStmt::Switch {
                expr: CExpr::var("sel0"),
                cases: vec![ast::SwitchCase {
                    value: CExpr::uint(0),
                    body: vec![CStmt::Break],
                }],
                default: None,
            },
            CStmt::Switch {
                expr: CExpr::var("sel1"),
                cases: vec![ast::SwitchCase {
                    value: CExpr::uint(1),
                    body: vec![CStmt::Break],
                }],
                default: None,
            },
        ]);

        let reason = structured_control_residual_reason_for_counts(
            Some(ControlRenderCounts {
                loops: 0,
                switches: 1,
            }),
            &switch_cfg_summary(),
            function_control_render_counts(&func),
        )
        .expect("rendered switch count must not exceed switch certificates");

        assert!(
            reason.contains("rendered 2 switch construct(s) with only 1 SwitchCertificate(s)"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_switch_shape_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_switch_shape", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![
                    ast::SwitchCase {
                        value: CExpr::uint(0),
                        body: vec![CStmt::Break],
                    },
                    ast::SwitchCase {
                        value: CExpr::uint(1),
                        body: vec![CStmt::Break],
                    },
                ],
                default: Some(vec![CStmt::Break]),
            }]);
        let inventory = ControlCertificateInventory {
            loops: Vec::new(),
            switches: vec![SwitchCertificateSummary {
                anchor: 0x401020,
                proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                selector: None,
                case_targets: Vec::new(),
                default_target: None,
                cases: 1,
                case_values: vec![0],
                has_default: false,
            }],
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof::new(
                ControlRenderProofKind::Switch,
                0x401020,
            )]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &switch_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("switch shape mismatch must be residualized even with one certificate");

        assert!(reason.contains("switch node stmt:0"), "{reason}");
        assert!(reason.contains("r2ssa:switch:0x401020:0"), "{reason}");
        assert!(reason.contains("has 2 case(s)"), "{reason}");
        assert!(reason.contains("default presence"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_switch_case_value_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_switch_values", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![
                    ast::SwitchCase {
                        value: CExpr::uint(0),
                        body: vec![CStmt::Break],
                    },
                    ast::SwitchCase {
                        value: CExpr::uint(2),
                        body: vec![CStmt::Break],
                    },
                ],
                default: None,
            }]);
        let inventory = ControlCertificateInventory {
            loops: Vec::new(),
            switches: vec![SwitchCertificateSummary {
                anchor: 0x401020,
                proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                selector: None,
                case_targets: Vec::new(),
                default_target: None,
                cases: 2,
                case_values: vec![0, 1],
                has_default: false,
            }],
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof::new(
                ControlRenderProofKind::Switch,
                0x401020,
            )]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &switch_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("switch value mismatch must be residualized");

        assert!(reason.contains("switch node stmt:0"), "{reason}");
        assert!(reason.contains("case values [0, 2]"), "{reason}");
        assert!(reason.contains("values [0, 1]"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_switch_case_target_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_switch_targets", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![
                    ast::SwitchCase {
                        value: CExpr::uint(0),
                        body: vec![CStmt::Break],
                    },
                    ast::SwitchCase {
                        value: CExpr::uint(1),
                        body: vec![CStmt::Break],
                    },
                ],
                default: None,
            }]);
        let inventory = ControlCertificateInventory {
            loops: Vec::new(),
            switches: vec![SwitchCertificateSummary {
                anchor: 0x401020,
                proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                selector: None,
                case_targets: vec![(0, 0x401100), (1, 0x401200)],
                default_target: None,
                cases: 2,
                case_values: vec![0, 1],
                has_default: false,
            }],
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Switch,
                anchor: 0x401020,
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: None,
                switch_cases: vec![(0, 0x401100), (1, 0x401208)],
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &switch_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("switch target mismatch must be residualized");

        assert!(reason.contains("switch node stmt:0"), "{reason}");
        assert!(reason.contains("case targets"), "{reason}");
        assert!(reason.contains("4198920"), "{reason}");
        assert!(reason.contains("4198912"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_placeholder_switch_selector_with_selector_certificate() {
        let func =
            CFunction::new("bad_switch_selector", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("test"),
                cases: vec![
                    ast::SwitchCase {
                        value: CExpr::uint(0),
                        body: vec![CStmt::Break],
                    },
                    ast::SwitchCase {
                        value: CExpr::uint(1),
                        body: vec![CStmt::Break],
                    },
                ],
                default: None,
            }]);
        let inventory = ControlCertificateInventory {
            loops: Vec::new(),
            switches: vec![SwitchCertificateSummary {
                anchor: 0x401020,
                proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                selector: Some(r2ssa::ValueId(7)),
                case_targets: Vec::new(),
                default_target: None,
                cases: 2,
                case_values: vec![0, 1],
                has_default: false,
            }],
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof::new(
                ControlRenderProofKind::Switch,
                0x401020,
            )]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &switch_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("placeholder switch selector must be residualized");

        assert!(reason.contains("switch node stmt:0"), "{reason}");
        assert!(reason.contains("placeholder selector"), "{reason}");
        assert!(reason.contains("canonical selector evidence"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_switch_selector_value_mismatch_at_render_node() {
        let func = CFunction::new("bad_switch_selector_value", CType::u64()).with_body(vec![
            CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![
                    ast::SwitchCase {
                        value: CExpr::uint(0),
                        body: vec![CStmt::Break],
                    },
                    ast::SwitchCase {
                        value: CExpr::uint(1),
                        body: vec![CStmt::Break],
                    },
                ],
                default: None,
            },
        ]);
        let inventory = ControlCertificateInventory {
            loops: Vec::new(),
            switches: vec![SwitchCertificateSummary {
                anchor: 0x401020,
                proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                selector: Some(r2ssa::ValueId(7)),
                case_targets: vec![(0, 0x401100), (1, 0x401200)],
                default_target: None,
                cases: 2,
                case_values: vec![0, 1],
                has_default: false,
            }],
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Switch,
                anchor: 0x401020,
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: Some(r2ssa::ValueId(8)),
                switch_cases: vec![(0, 0x401100), (1, 0x401200)],
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &switch_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("switch selector mismatch must be residualized");

        assert!(reason.contains("switch node stmt:0"), "{reason}");
        assert!(
            reason.contains("selector proof Some(ValueId(8))"),
            "{reason}"
        );
        assert!(reason.contains("selector Some(ValueId(7))"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_loop_certificate_anchor_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_loop_anchor", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let inventory = ControlCertificateInventory {
            loops: vec![LoopCertificateSummary {
                anchor: 0x401000,
                proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(0))
                    .to_string(),
                condition: Some(r2ssa::PredicateId(1)),
                condition_value: Some(r2ssa::ValueId(10)),
                body: Vec::new(),
                latches: Vec::new(),
                exits: Vec::new(),
                has_condition: true,
            }],
            switches: Vec::new(),
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof::new(
                ControlRenderProofKind::Loop,
                0x402000,
            )]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("loop proof anchor mismatch must be residualized");

        assert!(reason.contains("loop node stmt:0"), "{reason}");
        assert!(reason.contains("proof anchor 0x402000"), "{reason}");
        assert!(reason.contains("no matching LoopCertificate"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_loop_body_membership_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_loop_body", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let inventory = ControlCertificateInventory {
            loops: vec![LoopCertificateSummary {
                anchor: 0x401000,
                proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(0))
                    .to_string(),
                condition: Some(r2ssa::PredicateId(1)),
                condition_value: Some(r2ssa::ValueId(10)),
                body: vec![0x401000, 0x401010],
                latches: vec![0x401010],
                exits: vec![0x401020],
                has_condition: true,
            }],
            switches: Vec::new(),
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Loop,
                anchor: 0x401000,
                loop_condition: Some(r2ssa::PredicateId(1)),
                loop_condition_value: Some(r2ssa::ValueId(10)),
                loop_body_blocks: vec![0x401000, 0x401018],
                loop_latches: vec![0x401018],
                loop_exits: vec![0x401020],
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("loop body mismatch must be residualized");

        assert!(reason.contains("loop node stmt:0"), "{reason}");
        assert!(reason.contains("body blocks"), "{reason}");
        assert!(reason.contains("4198424"), "{reason}");
        assert!(reason.contains("4198416"), "{reason}");
    }

    #[test]
    fn standard_structured_output_refuses_loop_condition_predicate_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_loop_predicate", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let inventory = ControlCertificateInventory {
            loops: vec![LoopCertificateSummary {
                anchor: 0x401000,
                proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(0))
                    .to_string(),
                condition: Some(r2ssa::PredicateId(1)),
                condition_value: Some(r2ssa::ValueId(10)),
                body: vec![0x401000, 0x401010],
                latches: vec![0x401010],
                exits: vec![0x401020],
                has_condition: true,
            }],
            switches: Vec::new(),
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Loop,
                anchor: 0x401000,
                loop_condition: Some(r2ssa::PredicateId(2)),
                loop_condition_value: Some(r2ssa::ValueId(10)),
                loop_body_blocks: vec![0x401000, 0x401010],
                loop_latches: vec![0x401010],
                loop_exits: vec![0x401020],
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("loop condition predicate mismatch must be residualized");

        assert!(reason.contains("loop node stmt:0"), "{reason}");
        assert!(
            reason.contains("condition proof Some(PredicateId(2))"),
            "{reason}"
        );
        assert!(
            reason.contains("condition Some(PredicateId(1))"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_loop_condition_value_mismatch_at_render_node() {
        let func = CFunction::new("bad_loop_condition_value", CType::u64()).with_body(vec![
            CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            ),
        ]);
        let inventory = ControlCertificateInventory {
            loops: vec![LoopCertificateSummary {
                anchor: 0x401000,
                proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(0))
                    .to_string(),
                condition: Some(r2ssa::PredicateId(1)),
                condition_value: Some(r2ssa::ValueId(10)),
                body: vec![0x401000, 0x401010],
                latches: vec![0x401010],
                exits: vec![0x401020],
                has_condition: true,
            }],
            switches: Vec::new(),
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Loop,
                anchor: 0x401000,
                loop_condition: Some(r2ssa::PredicateId(1)),
                loop_condition_value: Some(r2ssa::ValueId(11)),
                loop_body_blocks: vec![0x401000, 0x401010],
                loop_latches: vec![0x401010],
                loop_exits: vec![0x401020],
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("loop condition value mismatch must be residualized");

        assert!(reason.contains("loop node stmt:0"), "{reason}");
        assert!(
            reason.contains("condition value proof Some(ValueId(11))"),
            "{reason}"
        );
        assert!(
            reason.contains("condition value Some(ValueId(10))"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_loop_condition_presence_mismatch_at_render_node() {
        let func =
            CFunction::new("bad_loop_condition", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::int(1),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let inventory = ControlCertificateInventory {
            loops: vec![LoopCertificateSummary {
                anchor: 0x401000,
                proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(0))
                    .to_string(),
                condition: Some(r2ssa::PredicateId(1)),
                condition_value: Some(r2ssa::ValueId(10)),
                body: Vec::new(),
                latches: Vec::new(),
                exits: Vec::new(),
                has_condition: true,
            }],
            switches: Vec::new(),
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof::new(
                ControlRenderProofKind::Loop,
                0x401000,
            )]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("loop condition mismatch must be residualized");

        assert!(reason.contains("loop node stmt:0"), "{reason}");
        assert!(reason.contains("condition presence (false)"), "{reason}");
        assert!(reason.contains("r2ssa:loop:0x401000:0"), "{reason}");
        assert!(reason.contains("(true)"), "{reason}");
    }

    #[test]
    fn standard_structured_output_requires_render_proof_identity_when_enforced() {
        let func =
            CFunction::new("missing_loop_anchor", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let inventory = ControlCertificateInventory {
            loops: vec![LoopCertificateSummary {
                anchor: 0x401000,
                proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(0))
                    .to_string(),
                condition: Some(r2ssa::PredicateId(1)),
                condition_value: Some(r2ssa::ValueId(10)),
                body: Vec::new(),
                latches: Vec::new(),
                exits: Vec::new(),
                has_condition: true,
            }],
            switches: Vec::new(),
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(&func, Some(&[]));

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("missing exact render proof must be residualized");

        assert!(reason.contains("loop node stmt:0"), "{reason}");
        assert!(reason.contains("lacks render proof identity"), "{reason}");
    }

    #[test]
    fn looped_standard_output_refuses_empty_loop_body() {
        let func =
            CFunction::new("count_bytes", CType::Typedef("size_t".to_string())).with_body(vec![
                CStmt::DoWhile {
                    body: Box::new(CStmt::block(vec![CStmt::comment("dropped loop effects")])),
                    cond: CExpr::var("cond"),
                },
            ]);

        let reason = looped_standard_output_residual_reason(&func, &loop_cfg_summary())
            .expect("empty/comment-only loop body must refuse structured output");
        assert!(reason.contains("empty loop body"), "{reason}");
    }

    #[test]
    fn looped_standard_output_refuses_control_only_loop_body() {
        let func =
            CFunction::new("kernel_lru_scan", CType::i64()).with_body(vec![CStmt::while_loop(
                CExpr::var("pos == head"),
                CStmt::Break,
            )]);

        let reason = looped_standard_output_residual_reason(&func, &loop_cfg_summary())
            .expect("break-only loop body must refuse structured output");
        assert!(reason.contains("empty loop body"), "{reason}");
    }

    #[test]
    fn looped_standard_output_refuses_nested_control_only_loop_body() {
        let func = CFunction::new("guarded_loop", CType::i64()).with_body(vec![CStmt::while_loop(
            CExpr::var("cond"),
            CStmt::if_stmt(CExpr::var("done"), CStmt::Break, None),
        )]);

        let reason = looped_standard_output_residual_reason(&func, &loop_cfg_summary())
            .expect("nested break-only loop body must refuse structured output");
        assert!(reason.contains("empty loop body"), "{reason}");
    }

    #[test]
    fn looped_standard_output_accepts_nonempty_rendered_loop() {
        let func = CFunction::new("count", CType::u64()).with_body(vec![CStmt::while_loop(
            CExpr::var("cond"),
            CStmt::block(vec![CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Add, CExpr::var("acc"), CExpr::uint(1)),
            ))]),
        )]);

        assert_eq!(
            looped_standard_output_residual_reason(&func, &loop_cfg_summary()),
            None
        );
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
        let signature = signature_spec(
            Some(CType::Int(64)),
            vec![
                ("zzz_first", Some(CType::Int(64))),
                ("aaa_second", Some(CType::Int(64))),
            ],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
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
        assert!(typed_text.contains("arg2"), "{typed_text}");
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
    fn decompile_input_honors_engine_render_permission_residual() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let context = DecompilerContext::default()
            .with_semantic_route(Some(SemanticRoutePlan::Standard))
            .with_render_permission(Some(r2sym::RenderPermission::residual(
                r2sym::ProofOwner::R2engine,
                "missing expression proof",
            )));
        let input = DecompilerInput::new(prepared, context);

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert!(output.contains("r2dec residual"), "{output}");
        assert!(
            output.contains("engine render permission residual"),
            "{output}"
        );
        assert!(output.contains("missing expression proof"), "{output}");
    }

    #[test]
    fn certified_standard_output_refuses_raw_temp_names() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let func = CFunction::new("bad_temp", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::var("tmp:_2")))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("raw temp should break certified rendering");

        assert!(
            reason.contains("rendered uncertified raw artifact name"),
            "{reason}"
        );

        let func = CFunction::new("bad_temp_addr", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::var("&TMP:_2")))]);
        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("addressed raw temp should break certified rendering");
        assert!(
            reason.contains("rendered uncertified raw artifact name"),
            "{reason}"
        );
    }

    #[test]
    fn typed_storage_render_filters_cover_summary_and_certified_paths() {
        assert_eq!(summary_accumulator_label("TMP:2c280_2"), "accumulator");
        assert_eq!(summary_accumulator_label("const:1_0"), "accumulator");
        assert_eq!(summary_accumulator_label("ram:401000_0"), "accumulator");
        assert_eq!(summary_accumulator_label("unique:12_0"), "accumulator");
        assert_eq!(summary_accumulator_label("sha_state"), "sha_state");
        assert!(is_uncertified_render_var_name("&TMP:_2"));
        assert!(!is_uncertified_render_var_name("sha_state"));

        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let func = CFunction::new("bad_temp_addr", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::var("&TMP:_2")))]);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("addressed raw temp should break certified rendering");
        assert!(
            reason.contains("rendered uncertified raw artifact name"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_lowercase_ssa_register_names() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let func = CFunction::new("bad_reg", CType::i64()).with_body(vec![CStmt::Return(Some(
            CExpr::binary(BinaryOp::Add, CExpr::var("r10_1"), CExpr::var("r8d_2")),
        ))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("raw SSA register should break certified rendering");

        assert!(
            reason.contains("rendered uncertified raw artifact name")
                && reason.contains("r10_1")
                && reason.contains("r8d_2"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_expression_assignment_without_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::IntAdd {
                dst: Varnode::register(0x00, 8),
                a: Varnode::constant(1, 8),
                b: Varnode::constant(2, 8),
            }],
            &arch,
        );
        let func =
            CFunction::new("bad_expr", CType::Void).with_body(vec![CStmt::expr(CExpr::assign(
                CExpr::var("result"),
                CExpr::binary(BinaryOp::Add, CExpr::uint(1), CExpr::uint(2)),
            ))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("pure expression assignment without proof must break certified rendering");

        assert!(
            reason.contains("pure expression assignment")
                && reason.contains("ExpressionCertificate")
                && reason.contains("stmt:0.0.1"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_accepts_expression_assignment_with_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::IntAdd {
                dst: Varnode::register(0x00, 8),
                a: Varnode::constant(1, 8),
                b: Varnode::constant(2, 8),
            }],
            &arch,
        );
        let value = expression_value_for_op(&prepared, 0x1000, 0);
        let func =
            CFunction::new("expr_ok", CType::Void).with_body(vec![CStmt::expr(CExpr::assign(
                CExpr::var("result"),
                CExpr::binary(BinaryOp::Add, CExpr::uint(1), CExpr::uint(2)),
            ))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Expression,
            block_addr: 0x1000,
            op_idx: 0,
            target: None,
            address: None,
            value: Some(value),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_refuses_expression_assignment_value_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::IntAdd {
                dst: Varnode::register(0x00, 8),
                a: Varnode::constant(1, 8),
                b: Varnode::constant(2, 8),
            }],
            &arch,
        );
        let func = CFunction::new("bad_expr_value", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(
                CExpr::var("result"),
                CExpr::binary(BinaryOp::Add, CExpr::uint(1), CExpr::uint(2)),
            ),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Expression,
            block_addr: 0x1000,
            op_idx: 0,
            target: None,
            address: None,
            value: Some(r2ssa::ValueId(999)),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("expression proof with unknown value must break certified rendering");

        assert!(
            reason.contains("expression proof at 0x1000:0 value Some(ValueId(999))")
                && reason.contains("ExpressionCertificate"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_expression_assignment_op_site_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x10, 8),
                    a: Varnode::constant(1, 8),
                    b: Varnode::constant(2, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x00, 8),
                    a: Varnode::constant(4, 8),
                    b: Varnode::constant(3, 8),
                },
            ],
            &arch,
        );
        let first_value = expression_value_for_op(&prepared, 0x1000, 0);
        let func = CFunction::new("bad_expr_site", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(
                CExpr::var("result"),
                CExpr::binary(BinaryOp::Add, CExpr::var("tmp"), CExpr::uint(3)),
            ),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Expression,
            block_addr: 0x1000,
            op_idx: 1,
            target: None,
            address: None,
            value: Some(first_value),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("expression proof from a different op-site must break certified rendering");

        assert!(
            reason.contains("expression proof at 0x1000:1")
                && reason.contains("neither defined nor consumed")
                && reason.contains("was defined at 0x1000:0"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_uncertified_call_count() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let func = CFunction::new("bad_call", CType::Void).with_body(vec![CStmt::expr(
            CExpr::call(CExpr::var("helper"), vec![CExpr::uint(1)]),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("call without callsite cert should break certified rendering");

        assert!(reason.contains("CallsiteCertificate"), "{reason}");
        assert!(reason.contains("first missing node stmt:0.0"), "{reason}");
    }

    #[test]
    fn certified_standard_output_refuses_call_without_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Call {
                target: Varnode::constant(0x401000, 8),
            }],
            &arch,
        );
        assert_eq!(prepared.certificates().callsites.len(), 1);
        let func = CFunction::new("bad_call", CType::Void)
            .with_body(vec![CStmt::expr(CExpr::call(CExpr::var("helper"), vec![]))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("call without exact emitted proof should break certified rendering");

        assert!(
            reason.contains("rendered 1 call(s) with only 0 rendered CallsiteCertificate proof(s)"),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:0.0"), "{reason}");
    }

    #[test]
    fn certified_standard_output_accepts_call_with_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Call {
                target: Varnode::constant(0x401000, 8),
            }],
            &arch,
        );
        let call = prepared
            .callsite_certificate_for_op(0x1000, 0)
            .expect("callsite certificate");
        let func = CFunction::new("call_ok", CType::Void)
            .with_body(vec![CStmt::expr(CExpr::call(CExpr::var("helper"), vec![]))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 0,
            target: Some(call.target),
            address: None,
            value: None,
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_refuses_call_argument_value_render_proof_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0x10, 8),
                    src: Varnode::constant(7, 8),
                },
                R2ILOp::Call {
                    target: Varnode::constant(0x401000, 8),
                },
            ],
            &arch,
        );
        let call = prepared
            .callsite_certificate_for_op(0x1000, 1)
            .expect("callsite certificate");
        assert_eq!(call.argument_values.len(), 1);
        let func = CFunction::new("bad_call_arg", CType::Void).with_body(vec![CStmt::expr(
            CExpr::call(CExpr::var("helper"), vec![CExpr::uint(7)]),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 1,
            target: Some(call.target),
            address: None,
            value: None,
            values: vec![r2ssa::ValueId(999)],
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("call argument value proof mismatch must break certified rendering");

        assert!(
            reason.contains("call proof at 0x1000:1 argument value proof [ValueId(999)]"),
            "{reason}"
        );
        assert!(
            reason.contains("CallsiteCertificate argument values"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_call_target_render_proof_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Call {
                target: Varnode::constant(0x401000, 8),
            }],
            &arch,
        );
        let func = CFunction::new("bad_call_target", CType::Void)
            .with_body(vec![CStmt::expr(CExpr::call(CExpr::var("helper"), vec![]))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 0,
            target: Some(r2ssa::ValueId(999)),
            address: None,
            value: None,
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("call target proof mismatch must break certified rendering");

        assert!(
            reason.contains("call proof at 0x1000:0 target proof Some(ValueId(999))"),
            "{reason}"
        );
        assert!(reason.contains("CallsiteCertificate target"), "{reason}");
    }

    #[test]
    fn certified_standard_output_refuses_return_without_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        assert_eq!(prepared.certificates().returns.len(), 1);
        let func = CFunction::new("bad_return", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::uint(0)))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("return without exact emitted proof should break certified rendering");

        assert!(
            reason.contains(
                "rendered 1 value return(s) with only 0 rendered ReturnValueCertificate proof(s)"
            ),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:0"), "{reason}");
    }

    #[test]
    fn certified_standard_output_accepts_return_with_exact_value_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let cert = prepared
            .return_certificate_for_op(0x1000, 0)
            .expect("return certificate");
        let func = CFunction::new("return_ok", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::uint(0)))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 0,
            target: None,
            address: None,
            value: Some(cert.value),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_refuses_return_value_without_renderable_expression_certificate() {
        let arch = test_arch_for_decompile();
        let userop_out = Varnode::unique(0x2222, 8);
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::CallOther {
                    output: Some(userop_out.clone()),
                    userop: 99,
                    inputs: vec![Varnode::register(0x10, 8)],
                },
                R2ILOp::Return { target: userop_out },
            ],
            &arch,
        );
        let cert = prepared
            .return_certificate_for_op(0x1000, 1)
            .expect("return certificate");
        assert!(
            prepared
                .certificates()
                .expressions
                .get(&cert.value)
                .is_some_and(|cert| !cert.renderable),
            "opaque userop return should not be renderable"
        );
        let func = CFunction::new("return_bad_expr", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::Var("opaque".to_string())))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 1,
            target: None,
            address: None,
            value: Some(cert.value),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("returning an opaque expression value must break certified rendering");

        assert!(
            reason.contains("return proof at 0x1000:1 value")
                && reason.contains("lacks renderable ExpressionCertificate"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_return_value_render_proof_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let func = CFunction::new("bad_return_value", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::uint(0)))]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 0,
            target: None,
            address: None,
            value: Some(r2ssa::ValueId(999)),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("return value proof mismatch must break certified rendering");

        assert!(
            reason.contains("return proof at 0x1000:0 value proof Some(ValueId(999))"),
            "{reason}"
        );
        assert!(reason.contains("ReturnValueCertificate value"), "{reason}");
    }

    #[test]
    fn certified_standard_output_refuses_memory_without_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Load {
                dst: Varnode::register(0x00, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x10, 8),
            }],
            &arch,
        );
        assert_eq!(prepared.certificates().memory_accesses.len(), 1);
        let func = CFunction::new("bad_memory", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(CExpr::var("x"), CExpr::deref(CExpr::var("p"))),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("memory expression without exact emitted proof should break certified rendering");

        assert!(
            reason.contains(
                "rendered 1 memory-like access(es) with only 0 rendered MemoryAccessCertificate proof(s)"
            ),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:0.0"), "{reason}");
    }

    #[test]
    fn certified_standard_output_accepts_memory_with_exact_render_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Load {
                dst: Varnode::register(0x00, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x10, 8),
            }],
            &arch,
        );
        let func = CFunction::new("memory_ok", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(CExpr::var("x"), CExpr::deref(CExpr::var("p"))),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("memory certificate");
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            target: None,
            address: Some(cert.address),
            value: cert.value,
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_refuses_memory_address_value_render_proof_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Load {
                dst: Varnode::register(0x00, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x10, 8),
            }],
            &arch,
        );
        let cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("memory certificate");
        let func = CFunction::new("bad_memory_value", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(CExpr::var("x"), CExpr::deref(CExpr::var("p"))),
        )]);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            target: None,
            address: Some(r2ssa::ValueId(998)),
            value: cert.value.map(|_| r2ssa::ValueId(999)),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("memory address/value proof mismatch must break certified rendering");

        assert!(
            reason.contains("memory proof at 0x1000:0 address proof Some(ValueId(998))"),
            "{reason}"
        );
        assert!(
            reason.contains("memory proof at 0x1000:0 value proof Some(ValueId(999))"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_accepts_type_layout_certified_member_access() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                field_access_certificates: vec![FieldAccessCertificate {
                    slot: 0,
                    field_offset: 0,
                    field_name: "len".to_string(),
                    field_type: Some("uint64_t".to_string()),
                }],
                ..FunctionTypeFacts::default()
            },
            None,
        );
        let func = CFunction::new("field_ok", CType::i64()).with_body(vec![CStmt::Return(Some(
            CExpr::Member {
                base: Box::new(CExpr::var("arg0")),
                member: "len".to_string(),
            },
        ))]);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func);

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_accepts_repeated_array_member_access_with_layout_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x10, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::unique(0x20, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x00, 8),
                    a: Varnode::unique(0x10, 8),
                    b: Varnode::unique(0x20, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );
        let indexed_len = || CExpr::Member {
            base: Box::new(CExpr::Subscript {
                base: Box::new(CExpr::var("arr")),
                index: Box::new(CExpr::var("idx")),
            }),
            member: "len".to_string(),
        };
        let func = CFunction::new("array_member_ok", CType::i64()).with_body(vec![CStmt::Return(
            Some(CExpr::Binary {
                op: BinaryOp::Add,
                left: Box::new(indexed_len()),
                right: Box::new(indexed_len()),
            }),
        )]);
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                array_index_certificates: vec![ArrayIndexCertificate {
                    slot: 0,
                    base: Some(ArrayIndexBase::Param { index: 0 }),
                    field_offset: 0,
                    element_stride: 8,
                }],
                external_type_db: ExternalTypeDb {
                    structs: [(
                        "node".to_string(),
                        ExternalStruct {
                            name: "node".to_string(),
                            fields: [(
                                0,
                                ExternalField {
                                    name: "len".to_string(),
                                    offset: 0,
                                    ty: Some("int64_t".to_string()),
                                },
                            )]
                            .into_iter()
                            .collect(),
                        },
                    )]
                    .into_iter()
                    .collect(),
                    ..ExternalTypeDb::default()
                },
                ..FunctionTypeFacts::default()
            },
            None,
        );

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func);

        assert_eq!(reason, None);
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
        let signature = signature_spec(
            Some(CType::Int(64)),
            vec![
                ("arg1", Some(CType::ptr(CType::Struct(struct_name)))),
                ("arg2", Some(CType::Int(32))),
                ("arg3", Some(CType::Int(32))),
            ],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
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
        let signature = signature_spec(
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
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
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
        type_inference.set_external_signature(
            decompiler
                .context
                .type_facts()
                .render_authorized_signature()
                .cloned(),
        );
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
            decompiler
                .context
                .type_facts()
                .render_authorized_signature(),
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
            .render_authorized_signature()
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
        let signature = signature_spec(
            Some(CType::Int(64)),
            vec![
                ("arg1", Some(CType::ptr(CType::Struct(struct_name.clone())))),
                ("arg2", Some(CType::Int(32))),
                ("arg3", Some(CType::Int(32))),
            ],
        );
        decompiler.set_type_facts(FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
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
        let signature = signature_spec(Some(CType::Void), vec![("status", Some(CType::Int(32)))]);
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(
            Some(CType::Void),
            vec![
                ("dst", Some(CType::Pointer(Box::new(CType::Void)))),
                ("src", Some(CType::Pointer(Box::new(CType::Void)))),
                ("len", Some(CType::Int(64))),
            ],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
            !output.contains("memcpy("),
            "summary evidence must not synthesize helper calls, got:\n{output}"
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
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(
            Some(CType::Void),
            vec![
                ("dst", Some(CType::Pointer(Box::new(CType::Void)))),
                ("src", Some(CType::Pointer(Box::new(CType::Void)))),
            ],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(
            Some(CType::Void),
            vec![
                ("dst", Some(CType::Pointer(Box::new(CType::Void)))),
                ("src", Some(CType::Pointer(Box::new(CType::Void)))),
            ],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(Some(CType::Bool), Vec::new());
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
    fn semantic_worker_summary_ignores_uncertified_merged_signature_header() {
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
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(Some(CType::Bool), Vec::new())),
                register_params: vec![ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(CTypeLike::Typedef("int64_t".to_string())),
                    reg: "rdi".to_string(),
                }],
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "fcn.00004129",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "named native-worker summary projection".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");
        let header = output.lines().next().unwrap_or_default();

        assert!(
            header.starts_with("/* unknown */ fcn.00004129(int64_t summary_input1)"),
            "uncertified merged signatures must not drive summary headers, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_sanitizes_generic_header_register_params() {
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
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                register_params: vec![
                    ExternalRegisterParamSpec {
                        name: "arg1".to_string(),
                        ty: Some(CTypeLike::Typedef("int64_t".to_string())),
                        reg: "rdi".to_string(),
                    },
                    ExternalRegisterParamSpec {
                        name: "arg2".to_string(),
                        ty: Some(CTypeLike::Typedef("int64_t".to_string())),
                        reg: "rsi".to_string(),
                    },
                ],
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "fcn.00004129",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "named native-worker summary projection".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");
        let header = output.lines().next().unwrap_or_default();

        assert!(
            header.contains("summary_input1") && header.contains("summary_input2"),
            "expected summary header to avoid generic arg labels, got:\n{output}"
        );
        assert!(
            !header.contains(" arg1") && !header.contains(" arg2"),
            "summary-only headers must not leak generic arg labels, got:\n{output}"
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
                evidence: r2sym::SemanticEvidence::exact(),
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
        let signature = signature_spec(
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
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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

        assert!(!output.contains("copy_file_data_summary("));
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
        let signature = signature_spec(
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
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
        assert!(!output.contains("run_program_orchestrator("));
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
                    table_walk: None,
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

        assert!(!output.contains("scan_string_summary("));
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
                    return_predicate: None,
                }),
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401030,
                    exit_target: Some(0x401060),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::Unknown),
                    fold: None,
                    table_walk: None,
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

        assert!(!output.contains("parse_base10_numeric_summary("));
        assert!(!output.contains("_parse_active"));
        assert!(output.contains("worker loop: parse base10 numeric stream from arg0"));
        assert!(output.contains("parser=base10 numeric"));
        assert!(output.contains("cursor=arg0"));
        assert!(output.contains("sign=true"));
    }

    #[test]
    fn semantic_worker_summary_reports_numeric_parser_return_without_synthetic_code() {
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
                    accepts_sign: false,
                    return_predicate: None,
                }),
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401030,
                    exit_target: Some(0x401060),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::Unknown),
                    fold: Some(r2sym::NativeWorkerFold {
                        accumulator: "EAX_13".to_string(),
                        bits: 32,
                        operation: r2sym::NativeWorkerFoldOperation::Add,
                        predicate: None,
                        init: Some(0),
                        multiplier: Some(10),
                        byte_transform: None,
                    }),
                    table_walk: None,
                }),
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::Int(32)),
                    vec![("str", Some(CType::Pointer(Box::new(CType::Int(8)))))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.parse_worker",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(!output.contains("summary projection (not native CFG)"));
        assert!(!output.contains("summary locals are synthetic"));
        assert!(!output.contains("while ("));
        assert!(!output.contains("return summary_value;"));
        assert!(output.contains("worker loop: parse base10 numeric stream from arg0"));
        assert!(output.contains("worker summary: parser"));
    }

    #[test]
    fn semantic_worker_summary_reports_certified_parser_success_without_synthetic_code() {
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
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
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
                    return_predicate: Some(r2sym::NativeParserReturnPredicate {
                        kind:
                            r2sym::NativeParserReturnPredicateKind::NonzeroCursorAndZeroTerminator,
                        cursor_arg: 0,
                    }),
                }),
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401030,
                    exit_target: Some(0x401060),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::Unknown),
                    fold: None,
                    table_walk: None,
                }),
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(
            Some(CType::i32()),
            vec![
                ("s", Some(CType::ptr(CType::i8()))),
                (
                    "out",
                    Some(CType::ptr(CType::Typedef("Result".to_string()))),
                ),
            ],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.out_param_parse",
            &function_facts,
            &SemanticRoutePlan::LinearWorker {
                reason: "guarded structuring unavailable".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(!output.contains("summary projection (not native CFG)"));
        assert!(!output.contains("summary locals are synthetic"));
        assert!(!output.contains("while ("));
        assert!(!output.contains("return i > 0 && s[i] == 0;"), "{output}");
        assert!(output.contains("worker loop: parse base10 numeric stream from s"));
        assert!(output.contains("summary return unresolved"));
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
        let signature = signature_spec(Some(CType::Void), vec![("size", Some(CType::UInt(64)))]);
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
        assert!(!output.contains("probe_file_metadata("));
        assert!(
            output.contains("metadata_probe") || output.contains("native summary"),
            "expected metadata summary evidence to remain visible, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_reports_length_bounded_hash_fold_without_fake_code() {
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
                        predicate: None,
                        init: None,
                        multiplier: None,
                        byte_transform: None,
                    }),
                    table_walk: None,
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

        assert!(!output.contains("rotate_mix_fold_summary"));
        assert!(!output.contains("return md5_state;"));
        assert!(!output.contains("_fold_active"));
        assert!(output.contains("worker loop: rotate_mix fold over arg0[0..0;w=1] into md5_state"));
        assert!(output.contains("len=arg1"));
        assert!(output.contains("fold=rotate_mix/md5_state:32"));
    }

    #[test]
    fn semantic_worker_summary_renders_predicated_byte_count_return() {
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
                kind: r2sym::NativeWorkerSummaryKind::NumericTransform,
                dst: None,
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
                    header: 0x401050,
                    exit_target: Some(0x401090),
                    iterations: None,
                    length_arg: Some(1),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                    fold: Some(r2sym::NativeWorkerFold {
                        accumulator: "match_count".to_string(),
                        bits: 64,
                        operation: r2sym::NativeWorkerFoldOperation::Add,
                        predicate: Some(r2sym::NativeWorkerPredicate::AnyOf(vec![
                            r2sym::NativeWorkerPredicate::ByteEqArg { arg: 2 },
                            r2sym::NativeWorkerPredicate::ByteEqArg { arg: 3 },
                        ])),
                        init: None,
                        multiplier: None,
                        byte_transform: None,
                    }),
                    table_walk: None,
                }),
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(
            Some(CType::Typedef("size_t".to_string())),
            vec![
                ("buf", Some(CType::Pointer(Box::new(CType::UInt(8))))),
                ("n", Some(CType::Typedef("size_t".to_string()))),
                ("a", Some(CType::UInt(8))),
                ("b", Some(CType::UInt(8))),
            ],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "count_bytes",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "named native-worker summary projection".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("predicated byte-count summary should render");

        assert!(!output.contains("summary projection (not native CFG)"));
        assert!(!output.contains("summary locals are synthetic"));
        assert!(!output.contains("size_t summary_count = 0;"));
        assert!(!output.contains("for (size_t summary_i = 0; summary_i < n; summary_i++)"));
        assert!(!output.contains("unsigned char summary_byte = buf[summary_i];"));
        assert!(!output.contains("if (summary_byte == a || summary_byte == b)"));
        assert!(!output.contains("summary_count++;"));
        assert!(!output.contains("return summary_count;"));
        assert!(output.contains("worker loop: add count over"));
        assert!(output.contains("worker summary: numeric_transform"));
        assert!(output.contains("summary return unresolved"));
        assert!(!output.contains("summary-backed count loop"));
        assert!(!output.contains("return match_count;"));
        assert!(!output.contains("match_count++;"));
        assert!(!output.contains("count_matching_bytes_summary"));
        assert!(!output.contains("add_fold_summary"));
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
                    table_walk: None,
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
                    return_predicate: None,
                }),
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401048,
                    exit_target: Some(0x401088),
                    iterations: None,
                    length_arg: Some(2),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                    fold: None,
                    table_walk: None,
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

        assert!(!output.contains("scan_string_summary("));
        assert!(output.contains("scan arg1[0..0;w=1] until length bound"));
        assert!(!output.contains("parse_token_summary("));
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

        assert!(!output.contains("diagnose_summary("));
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

        assert!(!output.contains("fetch_printf_arguments("));
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
                confidence: r2sym::SemanticConfidence::Exact,
                evidence: r2sym::SemanticEvidence::exact(),
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
                    init: None,
                    multiplier: None,
                    byte_transform: None,
                }],
                parser: None,
                residual_reasons: Vec::new(),
                confidence: r2sym::SemanticConfidence::Exact,
                evidence: r2sym::SemanticEvidence::exact(),
            });
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401010,
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
                    header: 0x401010,
                    exit_target: None,
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                    fold: None,
                    table_walk: None,
                }),
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
        assert!(!output.contains("scan_string_summary("));
        assert!(!output.contains("fold_summary("));
        assert!(!output.contains("return accumulator;"));
        assert!(!output.contains("_scan_active"));
        assert!(!output.contains("tmp:"));
        assert!(!output.contains("while ("));
        assert!(!output.contains("for ("));
        assert!(output.contains("summary island: scan arg0 until zero byte"));
        assert!(output.contains("summary island: add fold over arg0 into accumulator"));
        assert!(output.contains("island summary: string_scan"));
        assert!(output.contains("native worker summaries: 1"));
        assert!(output.contains("worker summary: table_walk: mem=arg0"));
    }

    #[test]
    fn semantic_region_summary_reports_hash_fold_without_synthetic_loop() {
        let mut semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401020,
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::HashFold,
                blocks: BTreeSet::from([0x401020, 0x401030]),
                entries: BTreeSet::from([0x401020]),
                exits: BTreeSet::from([0x401040]),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
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
                loop_summary: Some(r2sym::NativeLoopSummary {
                    header: 0x401020,
                    body: BTreeSet::from([0x401020, 0x401030]),
                    entries: BTreeSet::from([0x401020]),
                    exits: BTreeSet::from([0x401040]),
                    iterations: None,
                    length_arg: Some(1),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                }),
                reductions: vec![r2sym::NativeReductionSummary {
                    accumulator: "RAX_2".to_string(),
                    bits: 64,
                    operation: r2sym::NativeWorkerFoldOperation::Xor,
                    source: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: Some(r2ssa::SummaryMemoryRange {
                            offset_lo: 0,
                            offset_hi: 0,
                            width: Some(1),
                        }),
                    }),
                    init: Some(0x14650fb0739d0383),
                    multiplier: Some(1099511628211),
                    byte_transform: Some(r2sym::NativeWorkerByteTransform::AsciiLowercase),
                }],
                parser: None,
                residual_reasons: Vec::new(),
                confidence: r2sym::SemanticConfidence::Exact,
                evidence: r2sym::SemanticEvidence::exact(),
            });
        let signature = signature_spec(
            Some(CType::u64()),
            vec![
                (
                    "buf",
                    Some(CType::Pointer(Box::new(CType::Typedef(
                        "uint8_t".to_string(),
                    )))),
                ),
                ("n", Some(CType::Typedef("size_t".to_string()))),
            ],
        );
        let type_facts = FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            ..FunctionTypeFacts::default()
        };
        let function_facts = FunctionFacts::new(type_facts, Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "fnv_fold",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "large native worker summarized as typed islands".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("hash fold summary should render");

        assert!(!output.contains("summary projection (not native CFG)"));
        assert!(!output.contains("summary locals are synthetic"));
        assert!(!output.contains("uint64_t summary_hash = 0x14650fb0739d0383U;"));
        assert!(!output.contains("for (size_t summary_i = 0; summary_i < n; summary_i++)"));
        assert!(!output.contains("unsigned char summary_byte = buf[summary_i];"));
        assert!(!output.contains("if (summary_byte >= 'A' && summary_byte <= 'Z')"));
        assert!(!output.contains("summary_hash ^= summary_byte;"));
        assert!(!output.contains("summary_hash *= 0x100000001b3U;"));
        assert!(!output.contains("return summary_hash;"));
        assert!(output.contains("summary island: xor fold over"));
        assert!(output.contains("island summary: hash_fold"));
        assert!(output.contains("summary return unresolved"));
        assert!(!output.contains("fold_summary"));
    }

    #[test]
    fn semantic_worker_summary_refuses_bounded_table_walk_projection() {
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
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 24,
                        offset_hi: 24,
                        width: Some(8),
                    }),
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401020,
                    exit_target: Some(0x401080),
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::Unknown),
                    fold: None,
                    table_walk: Some(r2sym::NativeTableWalkSummary {
                        table_arg: 0,
                        needle_arg: Some(1),
                        id_offset: Some(0),
                        len_offset: Some(6),
                        name_offset: Some(24),
                        next_offset: Some(32),
                        count_accumulator: Some("EAX_3".to_string()),
                        match_returns_field_plus_count: true,
                        exhausted_returns_negative_count: true,
                    }),
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let signature = signature_spec(
            Some(CType::i32()),
            vec![
                (
                    "head",
                    Some(CType::Pointer(Box::new(CType::Typedef("Item".to_string())))),
                ),
                ("needle", Some(CType::Pointer(Box::new(CType::i8())))),
            ],
        );
        let mut item_fields = BTreeMap::new();
        for (offset, name, ty) in [
            (0, "id", Some("int32_t")),
            (6, "len", Some("uint16_t")),
            (24, "name", Some("char *")),
            (32, "next", Some("Item *")),
        ] {
            item_fields.insert(
                offset,
                r2types::ExternalField {
                    name: name.to_string(),
                    offset,
                    ty: ty.map(str::to_string),
                },
            );
        }
        let type_facts = FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            external_type_db: ExternalTypeDb {
                structs: std::collections::HashMap::from([(
                    "item".to_string(),
                    ExternalStruct {
                        name: "Item".to_string(),
                        fields: item_fields,
                    },
                )]),
                ..ExternalTypeDb::default()
            },
            ..FunctionTypeFacts::default()
        };
        let function_facts = FunctionFacts::new(type_facts, Some(semantic_artifact));
        let output = render_semantic_worker_summary(
            "table_walk",
            &function_facts,
            &SemanticRoutePlan::SummaryIslands {
                reason: "large native worker summarized as typed islands".to_string(),
            },
            DecompilerConfig::default(),
        )
        .expect("table walk summary should stay comment-only without hard proof");

        assert!(output.contains("worker summary: table_walk"));
        assert!(output.contains("summary return unresolved"));
        assert!(!output.contains("for (Item* it = head; it != NULL; it = it->next)"));
        assert!(!output.contains("it->id + seen"));
        assert!(!output.contains("return -seen;"));
        assert!(!output.contains("table walk fields and returns are certified by r2sym"));
    }

    #[test]
    fn summary_accumulator_label_hides_ssa_register_versions() {
        assert_eq!(summary_accumulator_label("RDX_4"), "accumulator");
        assert_eq!(summary_accumulator_label("tmp:2c280_2"), "accumulator");
        assert_eq!(summary_accumulator_label("TMP:2c280_2"), "accumulator");
        assert_eq!(summary_accumulator_label("const:1_0"), "accumulator");
        assert_eq!(summary_accumulator_label("ram:401000_0"), "accumulator");
        assert_eq!(summary_accumulator_label("unique:12_0"), "accumulator");
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
                    return_predicate: None,
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
                    return_predicate: None,
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
        assert!(!output.contains("parse_token_summary("));
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
                    table_walk: None,
                }),
                evidence: r2sym::SemanticEvidence::heuristic(
                    r2sym::SemanticEvidenceReason::NameHint,
                )
                .with_coverage(r2sym::SemanticEvidenceCoverage::Bounded)
                .with_ambiguity(r2sym::SemanticEvidenceAmbiguity::Ranked)
                .with_budget_limited(true),
            });
        native.summary.role_identity = Some(Box::new(r2sym::NativeWorkerRoleIdentity {
            role_name: "table_walk".to_string(),
            source: r2sym::NativeWorkerRoleSource::NameHint,
            confidence: r2sym::SemanticConfidence::Heuristic,
            source_names: vec!["sym.name_ranked_table".to_string()],
            summary_kinds: BTreeSet::from([r2sym::NativeWorkerSummaryKind::TableWalk]),
            evidence: r2sym::SemanticEvidence::heuristic(r2sym::SemanticEvidenceReason::NameHint)
                .with_coverage(r2sym::SemanticEvidenceCoverage::Bounded),
        }));
        let signature = signature_spec(
            Some(CType::Int(32)),
            vec![("table", Some(CType::Pointer(Box::new(CType::Int(8)))))],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
        assert!(output.contains("summary role hint: table_walk; source=NameHint"));
        assert!(!output.contains("semantic role:"));
        assert!(output.contains("semantic claims:"));
        assert!(output.contains("summary_roles=0"));
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
        let signature = signature_spec(Some(CType::Void), Vec::new());
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
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
        assert!(output.contains("summary_roles=0"));
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
    fn raw_summary_return_rollup_does_not_invent_executable_return() {
        let semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::WholeFunction,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let mut function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::ptr(CType::Int(8))),
                    vec![("buf", Some(CType::ptr(CType::Int(8))))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        function_facts.summary_view.rollup = Some(r2types::SummaryEffectRollup {
            root_return_relation: Some(r2ssa::SummaryReturnRelation::Arg(0)),
            ..r2types::SummaryEffectRollup::default()
        });
        let mut func = CFunction {
            name: "dbg.return_arg_summary".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            locals: Vec::new(),
            body: vec![CStmt::Expr(CExpr::call(
                CExpr::var("summary_worker"),
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
            "raw summary rollups must not invent executable return C, got {func:?}"
        );
    }

    #[test]
    fn certified_standard_summary_return_guard_does_not_invent_executable_return() {
        let semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::WholeFunction,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let mut function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::ptr(CType::Int(8))),
                    vec![("n", Some(CType::Typedef("size_t".to_string())))],
                )),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        function_facts.summary_view.rollup = Some(r2types::SummaryEffectRollup {
            root_return_relation: Some(r2ssa::SummaryReturnRelation::HeapAlloc),
            ..r2types::SummaryEffectRollup::default()
        });
        let mut func = CFunction {
            name: "dbg.alloc_wrapper2".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            locals: Vec::new(),
            body: vec![CStmt::Expr(CExpr::call(
                CExpr::var("sym.imp.malloc"),
                vec![CExpr::var("n")],
            ))],
        };

        append_semantic_summary_return_comment_to_function_if_needed(&mut func, &function_facts);

        assert!(
            matches!(func.body.last(), Some(CStmt::Comment(text)) if text.contains("summary return unresolved"))
        );
        assert!(
            !func
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "certified standard mode must not invent summary returns, got {func:?}"
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
