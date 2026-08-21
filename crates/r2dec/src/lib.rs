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
//! use r2dec::{Decompiler, DecompilerConfig, DecompilerInput};
//!
//! let input: DecompilerInput = /* built by r2engine from source-owned FunctionFacts */;
//! let config = DecompilerConfig::default();
//! let decompiler = Decompiler::new(config);
//! let c_code = decompiler.decompile_input(&input);
//! println!("{}", c_code);
//! ```

pub(crate) mod address;
pub(crate) mod analysis;
pub mod ast;
pub(crate) mod codegen;
#[cfg(test)]
pub(crate) mod consumer_linear;
pub(crate) mod consumer_structured;
pub(crate) mod consumer_summary;
pub(crate) mod consumer_vm;
pub mod control;
pub(crate) mod fold;
pub mod highlight;
pub(crate) mod normalize;
pub(crate) mod planner;
pub(crate) mod post_rename;
pub mod region;
pub(crate) mod registers;
pub(crate) mod single_evaluation;
pub mod structure;
pub mod symbol;
pub(crate) mod unrendered;
pub mod variable;

pub use ast::{BinaryOp, CExpr, CFunction, CStmt, CType, UnaryOp};
pub use codegen::CodeGenConfig;
pub use control::{DecompileExecutionStop, DecompileWorkControl, DecompileWorkPhase};
pub use fold::lower_ssa_ops_to_stmts;
pub use highlight::highlight_c_ansi;
pub use region::{Region, RegionAnalyzer};
pub(crate) use structure::ControlFlowStructurer;
pub use variable::VariableRecovery;

use crate::codegen::CodeGenerator;
use crate::fold::FoldingContext;
use crate::fold::context::{FoldArchConfig, FoldInputs};
use r2ssa::SSAFunction;
use r2ssa::SSAOp;
use r2ssa::cfg::BlockTerminator;
use r2types::{
    CTypeLike, DecompileRouteFacts, DecompileRouteKind, ExternalRegisterParamSpec, FunctionFacts,
    FunctionSignatureSpec, FunctionTypeFacts, StackSlotKey, TypeInference, TypeOracle,
    VisibleBinding, VisibleBindingKind, register_alias_names,
};
#[cfg(test)]
use r2types::{ExternalTypeDb, FunctionType};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
#[cfg(test)]
use std::sync::Arc;

fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
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

pub(crate) fn certified_loop_carrier_name(phi: r2ssa::ValueId) -> String {
    format!("loop_value_{}", phi.0)
}

pub(crate) fn certified_memory_result_name(access: r2ssa::StructuredAccessId) -> String {
    format!("memory_value_{}_{}", access.inst.0, access.ordinal)
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
        r2sym::VmValueExpr::Select {
            cond,
            if_true,
            if_false,
        } => format!(
            "({} ? {} : {})",
            format_vm_value_expr(cond),
            format_vm_value_expr(if_true),
            format_vm_value_expr(if_false)
        ),
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

fn format_semantic_memory_address(address: &r2sym::SemanticMemoryAddress) -> String {
    if address.is_exact_offset() {
        return format!("{:#x}", address.offset_lo());
    }
    if address.terms().is_empty() {
        return format!(
            "bounded({:#x}..{:#x})",
            address.offset_lo(),
            address.offset_hi()
        );
    }
    let terms = address
        .terms()
        .iter()
        .map(|term| format!("v{}*{}", term.value.0, term.coefficient))
        .collect::<Vec<_>>()
        .join(" + ");
    format!("affine({terms}; offset={})", address.offset_lo())
}

fn format_vm_memory_conditions(conditions: &[r2sym::VmMemoryCondition]) -> String {
    if conditions.is_empty() {
        return "[]".to_string();
    }
    let rendered = conditions
        .iter()
        .map(|condition| {
            let region = condition.region.name.clone();
            let address = format_semantic_memory_address(&condition.address);
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
                "{}@[{}]/{}:{}{}{}",
                region, address, condition.size, condition.expr, binding, value,
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{rendered}]")
}

pub(crate) fn sanitize_comment_text(text: &str) -> String {
    let flattened = text.replace("*/", "* /").replace(['\r', '\n'], " ");
    sanitize_comment_raw_tokens(&sanitize_comment_debug_ids(&flattened))
}

fn sanitize_comment_debug_ids(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut index = 0;
    while index < text.len() {
        let rest = &text[index..];
        let replacement = if rest.starts_with("ValueId(") {
            Some("value")
        } else if rest.starts_with("ObjectId(") {
            Some("object")
        } else {
            None
        };
        if let Some(replacement) = replacement {
            out.push_str(replacement);
            if let Some(end) = rest.find(')') {
                index += end + 1;
            } else {
                break;
            }
            continue;
        }
        let ch = rest.chars().next().expect("valid char boundary");
        out.push(ch);
        index += ch.len_utf8();
    }
    out
}

fn sanitize_comment_raw_tokens(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut token = String::new();
    let flush_token = |out: &mut String, token: &mut String| {
        if token.is_empty() {
            return;
        }
        if let Some(replacement) = sanitized_comment_token(token) {
            out.push_str(replacement);
        } else {
            out.push_str(token);
        }
        token.clear();
    };

    for ch in text.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == ':' {
            token.push(ch);
        } else {
            flush_token(&mut out, &mut token);
            out.push(ch);
        }
    }
    flush_token(&mut out, &mut token);
    out
}

fn sanitized_comment_token(token: &str) -> Option<&'static str> {
    let lower = token.to_ascii_lowercase();
    if matches!(lower.as_str(), "fake_stack_slot" | "saved_fp") {
        return Some("stack slot");
    }
    if is_ssa_versioned_register_label(token) {
        return Some("register");
    }
    if lower.starts_with("tmp:") || lower.starts_with("ram:") {
        return Some("temporary");
    }
    for prefix in ["stack_", "slot_", "local_", "arg_", "var_"] {
        if let Some(suffix) = lower.strip_prefix(prefix)
            && raw_stack_suffix_label(suffix)
        {
            return Some("stack slot");
        }
    }
    if let Some(rest) = lower.strip_prefix('t')
        && rest.len() >= 3
        && rest.bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        return Some("temporary");
    }
    None
}

fn raw_stack_suffix_label(suffix: &str) -> bool {
    if suffix.is_empty() {
        return false;
    }
    let suffix = suffix.strip_suffix('h').unwrap_or(suffix);
    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_hexdigit())
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
    r2source::display_names::is_generated_function_name(name)
}

pub(crate) fn semantic_mode_label(artifact: &r2sym::SemanticArtifactReport) -> &'static str {
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

pub fn block_guard_fallback_comment(func_name: &str, blocks: usize, max_blocks: usize) -> String {
    planner::block_guard_fallback_comment(func_name, blocks, max_blocks)
}

pub fn artifact_guard_fallback_comment(func_name: &str, reason: &str) -> String {
    planner::artifact_guard_fallback_comment(func_name, reason)
}

pub fn render_vm_semantic_summary(func_name: &str, input: &DecompilerInput) -> Option<String> {
    let function_facts = input.function_facts();
    let route = function_facts.decompile_route()?;
    if route.kind != r2types::DecompileRouteKind::VmSummary {
        return None;
    }
    consumer_vm::render_vm_semantic_summary(
        func_name,
        function_facts,
        function_facts.semantic_report()?,
    )
}

pub fn render_semantic_worker_summary(
    func_name: &str,
    input: &DecompilerInput,
    config: DecompilerConfig,
) -> Option<String> {
    let function_facts = input.function_facts();
    let route = function_facts.decompile_route()?;
    if !route_is_summary_boundary(route) {
        return None;
    }
    Decompiler::new(config).semantic_worker_summary_output_for_route(
        func_name,
        function_facts,
        route,
    )
}

fn append_summary_return_if_needed(
    body: &mut Vec<CStmt>,
    function_facts: &FunctionFacts,
    semantic_artifact: &r2sym::SemanticArtifactReport,
) {
    if summary_non_void_return_type(function_facts, semantic_artifact).is_none() {
        return;
    }
    if body.iter().any(summary_stmt_contains_return) {
        return;
    }
    if semantic_summary_return_expr(function_facts, semantic_artifact).is_some() {
        body.push(CStmt::comment(
            "summary return value intentionally not reconstructed as executable C".to_string(),
        ));
    } else {
        body.push(CStmt::comment(
            "summary return unresolved; value intentionally not reconstructed".to_string(),
        ));
    }
}

fn append_semantic_summary_return_to_function_if_needed(
    func: &mut CFunction,
    function_facts: &FunctionFacts,
    semantic_report: Option<&r2sym::SemanticArtifactReport>,
) {
    append_semantic_summary_return_comment_to_function_if_needed(
        func,
        function_facts,
        semantic_report,
    );
}

fn append_semantic_summary_return_comment_to_function_if_needed(
    func: &mut CFunction,
    function_facts: &FunctionFacts,
    semantic_report: Option<&r2sym::SemanticArtifactReport>,
) {
    if matches!(func.ret_type, CType::Void | CType::Unknown) {
        return;
    }
    if func.body.iter().any(summary_stmt_contains_return) {
        return;
    }
    let Some(semantic_artifact) = semantic_report else {
        return;
    };
    if semantic_summary_return_expr(function_facts, semantic_artifact).is_some() {
        func.body.push(CStmt::comment(
            "summary return value intentionally not reconstructed as executable C".to_string(),
        ));
    } else {
        func.body.push(CStmt::comment(
            "summary return unresolved; value intentionally not reconstructed".to_string(),
        ));
    }
}

/// Count the residual markers the structurer left in a rendered body.
///
/// The structurer already refuses per construct: an unresolved branch, loop,
/// switch selector or case value becomes a `r2dec residual:` comment where that
/// construct would have been. Counting them is a reading of the body, not a
/// second opinion about what was proven.
fn count_residual_markers(stmts: &[CStmt]) -> usize {
    fn walk(stmts: &[CStmt], found: &mut usize) {
        for stmt in stmts {
            walk_one(stmt, found);
        }
    }
    fn walk_one(stmt: &CStmt, found: &mut usize) {
        match stmt {
            CStmt::Comment(text) => {
                if text.contains("r2dec residual:") {
                    *found += 1;
                }
            }
            CStmt::Block(body) => walk(body, found),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                walk_one(then_body, found);
                if let Some(else_body) = else_body {
                    walk_one(else_body, found);
                }
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => walk_one(body, found),
            CStmt::For { init, body, .. } => {
                if let Some(init) = init {
                    walk_one(init, found);
                }
                walk_one(body, found);
            }
            CStmt::Switch { cases, default, .. } => {
                for case in cases {
                    walk(&case.body, found);
                }
                if let Some(default) = default {
                    walk(default, found);
                }
            }
            _ => {}
        }
    }
    let mut found = 0;
    walk(stmts, &mut found);
    found
}

/// State the proof status of a rendered function in its own body.
///
/// Rendering used to stop at the function boundary whenever the certification
/// kernel had not claimed the route, which meant one unproven construct cost
/// every proven one beside it and left the caller with nothing to read. The
/// function is rendered either way now, so it has to say what it is: the
/// structurer marks the individual constructs it could not prove, and this
/// records whether the kernel certified the function at all.
///
/// A shared empty name table for fixtures that carry no recovered names.
#[cfg(test)]
pub(crate) fn empty_display_names() -> &'static r2types::DisplayNames {
    static EMPTY: std::sync::OnceLock<r2types::DisplayNames> = std::sync::OnceLock::new();
    EMPTY.get_or_init(r2types::DisplayNames::default)
}

/// State what the rendering did and did not show.
///
/// "Nothing was marked" and "everything was shown to be right" are different
/// claims, and only the second earns silence. Nothing here makes the second, so
/// the note is always emitted: it reports how many constructs carry a residual
/// marker, and then reports the ledger, which says what became of every effect
/// the source obliges.
///
/// The ledger's columns sum to its total, so an effect that went missing is a
/// number in the line rather than an absence from it. An unaccounted count is
/// never zero because nothing went wrong; it is zero only when every obligation
/// was reached by a rule that named its fate.
fn note_unproven_constructs(func: &mut CFunction, ledger: Option<&r2ssa::ledger::ObligationLedger>) {
    let rendered_nothing = func.body.is_empty();
    let residuals = count_residual_markers(&func.body);
    let detail = if rendered_nothing {
        "rendering produced no statements".to_string()
    } else {
        match residuals {
            0 => "no individual construct is marked".to_string(),
            1 => "1 construct is marked below".to_string(),
            n => format!("{n} constructs are marked below"),
        }
    };
    let detail = match ledger.map(r2ssa::ledger::ObligationLedger::close) {
        Some(closure) if closure.total > 0 => {
            let mut line = format!(
                "{detail}; {} source obligations: {} rendered, {} elided, {} refused",
                closure.total, closure.rendered, closure.elided, closure.refused
            );
            // The column that used to have no name. Saying nothing here is what let a
            // gutted body report as clean, so it is spelled out whenever it is not zero.
            if closure.unattributed > 0 {
                let _ = write!(&mut line, ", {} unaccounted", closure.unattributed);
            }
            if closure.conflicts > 0 {
                let _ = write!(&mut line, ", {} conflicting", closure.conflicts);
            }
            line
        }
        _ => detail,
    };
    func.body.insert(
        0,
        CStmt::comment(sanitize_comment_text(&format!("r2dec proof: {detail}"))),
    );
}

/// Take back every rendering claim when the body that would carry them is empty.
///
/// Proofs are taken while folding, and a structuring that then emits nothing has
/// discharged none of them. Claiming otherwise is how a function with no output
/// reported most of its obligations owned. This works at whole-function
/// granularity because that is what can be proven without statement provenance;
/// a statement that survives structuring cannot yet name the obligations it carries.
fn reconcile_ledger_with_body(ledger: &mut r2ssa::ledger::ObligationLedger, func: &CFunction) {
    use r2ssa::ledger::{LedgerLayer, Outcome, RefusalReason};
    let rendered_any_statement = func
        .body
        .iter()
        .any(|stmt| !matches!(stmt, CStmt::Comment(_) | CStmt::Empty));
    if rendered_any_statement {
        return;
    }
    let claimed = ledger
        .entries()
        .filter(|(_, outcome)| matches!(outcome, Outcome::Rendered { .. }))
        .map(|(id, _)| *id)
        .collect::<Vec<_>>();
    for id in claimed {
        ledger.overwrite(
            id,
            Outcome::Refused {
                layer: LedgerLayer::Structure,
                reason: RefusalReason::BlockNotRendered,
            },
        );
    }
}

/// What became of every obligation this function's source inventory recorded.
///
/// Ownership used to be inferred at the end by asking whether anything had been
/// proven about each entry, and an entry nothing had an opinion about fell out of
/// every total. Attribution now writes into a ledger that already holds each
/// obligation, so an entry no rule reaches stays visible as undecided instead of
/// disappearing, and the counts sum to the inventory by construction.
fn build_obligation_ledger(
    prepared: &r2ssa::SsaArtifact,
    proofs: &[crate::fold::context::EffectRenderProof],
    folded_blocks: &std::collections::BTreeSet<u64>,
    elided_op_sites: &std::collections::BTreeMap<(u64, usize), &'static str>,
) -> r2ssa::ledger::ObligationLedger {
    use r2ssa::SemanticObligationKind as Kind;
    use r2ssa::ledger::{LedgerLayer, ObligationLedger, Outcome, RefusalReason};

    let obligations = prepared.obligations();
    let graph = prepared.graph();
    let mut ledger = ObligationLedger::open(obligations);

    // InstId is a dense index, so membership is a direct probe rather than a tree
    // walk, and the site an obligation rendered at is read back from the same table.
    let inst_count = graph.insts.len();
    let mut rendered_site = vec![None::<(u64, usize)>; inst_count];
    for proof in proofs {
        if let Some(inst) = graph.inst_id_for_op_site(proof.block_addr, proof.op_idx)
            && let Some(slot) = rendered_site.get_mut(inst.0 as usize)
        {
            *slot = Some((proof.block_addr, proof.op_idx));
        }
    }
    let mut elided_reason = vec![None::<&'static str>; inst_count];
    for ((block_addr, op_idx), reason) in elided_op_sites {
        if let Some(inst) = graph.inst_id_for_op_site(*block_addr, *op_idx)
            && let Some(slot) = elided_reason.get_mut(inst.0 as usize)
        {
            *slot = Some(*reason);
        }
    }

    for id in obligations.obligations().keys() {
        // The admission rule asks these to residualize rather than be owned, which
        // is a refusal with a reason and not an absence.
        if matches!(id.kind, Kind::VolatileOrUnknownEffect | Kind::Trap) {
            ledger.record(
                *id,
                Outcome::Refused {
                    layer: LedgerLayer::Ssa,
                    reason: RefusalReason::UnsupportedEffect,
                },
            );
            continue;
        }
        let block_rendered = folded_blocks.contains(&id.instruction.block_addr);
        // A merge sits at the head of its block rather than at any operation, so no
        // operation site can name it; the block it heads is what expresses it.
        let outcome = match id.instruction.site {
            r2ssa::CanonicalInstructionSite::Phi(_) if block_rendered => Outcome::Rendered {
                block_addr: id.instruction.block_addr,
                op_idx: 0,
            },
            r2ssa::CanonicalInstructionSite::Phi(_) => Outcome::Refused {
                layer: LedgerLayer::Structure,
                reason: RefusalReason::BlockNotRendered,
            },
            _ => {
                let inst = obligations
                    .instructions()
                    .get(&id.instruction)
                    .and_then(|disposition| disposition.source.graph_inst());
                let index = inst.map(|inst| inst.0 as usize);
                let site = index.and_then(|index| rendered_site.get(index).copied().flatten());
                match site {
                    Some((block_addr, op_idx)) => Outcome::Rendered { block_addr, op_idx },
                    None => {
                        match index.and_then(|index| elided_reason.get(index).copied().flatten()) {
                            Some(reason) => Outcome::Elided(elision_reason(reason)),
                            None if !block_rendered => Outcome::Refused {
                                layer: LedgerLayer::Structure,
                                reason: RefusalReason::BlockNotRendered,
                            },
                            // The block rendered and no rule reached this obligation.
                            None => Outcome::Unattributed,
                        }
                    }
                }
            }
        };
        ledger.record(*id, outcome);
    }

    debug_log_ledger(prepared, &ledger);
    ledger
}

/// Read the fold's elision label as the reason it names.
fn elision_reason(reason: &str) -> r2ssa::ledger::ElisionReason {
    use r2ssa::ledger::ElisionReason;
    match reason {
        "stack-frame" => ElisionReason::StackFrame,
        "dead-cpu-flag" => ElisionReason::DeadCpuFlag,
        "dead-flag-only" => ElisionReason::DeadFlagOnly,
        "dead-unused-temp" => ElisionReason::DeadUnusedTemporary,
        "dead-caller-saved" => ElisionReason::DeadCallerSaved,
        "dead-call-arg" => ElisionReason::DeadCallArgument,
        "dead-stack-base" => ElisionReason::DeadStackBase,
        _ => ElisionReason::DeadUnclassified,
    }
}

/// Whether a run was asked to report what the rendering left unaccounted for.
pub(crate) fn unowned_report_requested() -> bool {
    static REQUESTED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *REQUESTED.get_or_init(|| std::env::var_os("R2SLEIGH_DEBUG_UNOWNED").is_some())
}

/// Write the whole ledger out on request, so a count has somewhere to look.
///
/// The rendered note says how many obligations landed in each column, which tells
/// a reader that a function is short without saying short of what. This names the
/// kinds left undecided, the reasons given for eliding, and the layer behind every
/// refusal, which is what turns those numbers into a place to start.
fn debug_log_ledger(prepared: &r2ssa::SsaArtifact, ledger: &r2ssa::ledger::ObligationLedger) {
    if !unowned_report_requested() {
        return;
    }
    let closure = ledger.close();
    // Largest first, and by name where two entries tie, so the report reads the
    // same way twice over the same binary.
    fn ranked<K: std::fmt::Display>(counts: std::collections::BTreeMap<K, usize>) -> String {
        let mut entries = counts.into_iter().collect::<Vec<_>>();
        entries.sort_by(|(left_key, left), (right_key, right)| {
            right
                .cmp(left)
                .then_with(|| left_key.to_string().cmp(&right_key.to_string()))
        });
        entries
            .into_iter()
            .map(|(key, count)| format!("{key}={count}"))
            .collect::<Vec<_>>()
            .join(" ")
    }
    let refusals = ranked(
        ledger
            .refusals_by_layer()
            .into_iter()
            .map(|((layer, reason), count)| (format!("{layer}/{reason}"), count))
            .collect(),
    );
    let message = format!(
        "LEDGER fn={:#x} total={} rendered={} elided={} refused={} unaccounted={} conflicts={} | unaccounted-kinds: {} | elided: {} | refused: {}",
        prepared.function().entry,
        closure.total,
        closure.rendered,
        closure.elided,
        closure.refused,
        closure.unattributed,
        closure.conflicts,
        ranked(ledger.unattributed_by_kind()),
        ranked(ledger.elisions_by_reason()),
        refusals,
    );
    let path = std::env::var("R2SLEIGH_DEBUG_UNOWNED_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_unowned.log".to_string());
    if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        use std::io::Write;
        let _ = writeln!(file, "{message}");
    }
}

/// Why the source obligation inventory cannot account for this function, if it cannot.
fn incomplete_source_obligations_reason(prepared: &r2ssa::SsaArtifact) -> Option<String> {
    let obligations = prepared.obligations();
    if obligations.is_complete() {
        return None;
    }
    let failures = obligations.construction_failures().len();
    let cycles = obligations.unstructured_cycle_blocks().len();
    Some(format!(
        "r2dec residual: the source obligation inventory did not close, so what this function owes was never enumerated ({failures} construction failures, {cycles} unstructured cycle blocks)"
    ))
}

fn residual_function_for_render_boundary(func_name: &str, reason: &str) -> CFunction {
    let mut func = CFunction::new(func_name.to_string(), CType::Unknown).with_unknown_params();
    func.body = vec![CStmt::comment(sanitize_comment_text(reason))];
    func
}

fn route_reason(route: &DecompileRouteFacts) -> &str {
    route
        .reason
        .as_deref()
        .or(route.fallback_comment.as_deref())
        .unwrap_or("non-standard decompile route")
}

fn route_fallback_reason(route: &DecompileRouteFacts) -> Option<&str> {
    (route.kind == DecompileRouteKind::FallbackComment).then(|| {
        route
            .reason
            .as_deref()
            .or(route.fallback_comment.as_deref())
            .unwrap_or("source-owned fallback route")
    })
}

fn route_is_summary_boundary(route: &DecompileRouteFacts) -> bool {
    matches!(
        route.kind,
        DecompileRouteKind::StructuredWorker
            | DecompileRouteKind::SummaryIslands
            | DecompileRouteKind::LinearWorker
            | DecompileRouteKind::VmSummary
    )
}

fn residual_function_for_summary_route_boundary(
    func_name: &str,
    route: &DecompileRouteFacts,
) -> CFunction {
    let (label, reason) = match route.kind {
        DecompileRouteKind::StructuredWorker => ("structured_worker", route_reason(route)),
        DecompileRouteKind::SummaryIslands | DecompileRouteKind::LinearWorker => {
            ("summary_route", route_reason(route))
        }
        DecompileRouteKind::VmSummary => ("vm_summary", route_reason(route)),
        DecompileRouteKind::Standard | DecompileRouteKind::FallbackComment => {
            ("summary_route", "non-standard decompile route")
        }
    };
    let mut func = CFunction::new(func_name.to_string(), CType::Unknown);
    func.body = vec![
        CStmt::comment(format!(
            "r2dec summary: {} for {}",
            label,
            sanitize_comment_text(reason)
        )),
        CStmt::comment(
            "render contract: summary facts only; no executable native C reconstructed".to_string(),
        ),
    ];
    func
}

fn summary_only_semantics_standard_render_residual_reason(
    route: Option<&DecompileRouteFacts>,
    semantics: Option<&r2sym::SemanticArtifactReport>,
) -> Option<String> {
    let route = route?;
    if route.kind != r2types::DecompileRouteKind::Standard {
        return None;
    }
    let semantics = semantics?;
    (semantics.granularity == r2sym::ArtifactGranularity::SummaryOnly).then(|| {
        "r2dec residual: summary-only semantic artifact cannot authorize Standard executable C; route must stay summary/residual until native CFG/control/dataflow facts are certified".to_string()
    })
}

fn missing_decompile_route_residual_comment(func_name: &str) -> String {
    artifact_guard_fallback_comment(
        func_name,
        "missing FunctionFacts::decompile_route; executable C suppressed until r2engine supplies route/refusal evidence",
    )
}

fn summary_non_void_return_type(
    function_facts: &FunctionFacts,
    _semantic_artifact: &r2sym::SemanticArtifactReport,
) -> Option<CType> {
    function_facts
        .type_facts()
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
    _semantic_artifact: &r2sym::SemanticArtifactReport,
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

/// Name a parameter the way the source named it, where it did.
///
/// The renderer's own fallback is `argN`, which says only the position. The
/// source often knows better - debug info called it `password` - and that name
/// travelled with the snapshot all along. It is applied only where a real name
/// exists, and never over one an external signature already supplied, because
/// a parsed signature is the more specific statement.
fn apply_source_parameter_names(params: &mut [ast::CParam], display_names: &r2types::DisplayNames) {
    for (index, param) in params.iter_mut().enumerate() {
        if !is_generic_arg_name(&param.name) {
            continue;
        }
        if let Some(name) = display_names.parameter(index) {
            param.name = name.to_string();
        }
    }
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

    (0..signature.params.len())
        .map(|idx| {
            let fallback_name = format!("arg{idx}");
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

/// The float-argument registers that advance alongside an integer sequence.
///
/// SysV and AAPCS both keep two argument sequences and advance them
/// independently, so walking one positional list assigns the wrong register to
/// every parameter after the first float: in
/// `abi_mixed_params(int a, double b, int c, ...)` a positional walk put `b` in
/// `rsi`, which actually carries `c`, and left the register really holding `b`
/// with no name at all.
fn float_arg_regs_for(abi_arg_regs: &[String]) -> &'static [&'static str] {
    match abi_arg_regs
        .first()
        .map(|reg| reg.to_ascii_lowercase())
        .as_deref()
    {
        Some("rdi") => &["xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7"],
        Some("x0") => &["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7"],
        _ => &[],
    }
}

fn param_takes_float_register(ty: &CType) -> bool {
    match ty {
        CType::Float(_) => true,
        // A recovered prototype spells its types, so a double arrives as the
        // name `double` rather than as a width.
        CType::Typedef(name) => matches!(
            name.trim().to_ascii_lowercase().as_str(),
            "float" | "double" | "long double" | "__float128" | "_float16"
        ),
        _ => false,
    }
}

fn build_param_register_aliases(
    params: &[ast::CParam],
    recovered_params: &[(r2ssa::SSAVar, ast::CParam)],
    register_params: &[ExternalRegisterParamSpec],
    abi_arg_regs: &[String],
    allow_positional_aliases: bool,
) -> std::collections::HashMap<String, String> {
    let mut aliases = std::collections::HashMap::new();

    if allow_positional_aliases {
        let float_regs = float_arg_regs_for(abi_arg_regs);
        let mut integer_index = 0usize;
        let mut float_index = 0usize;
        for param in params {
            let reg_name = if param_takes_float_register(&param.ty) && !float_regs.is_empty() {
                let reg = float_regs.get(float_index).map(|reg| (*reg).to_string());
                float_index += 1;
                reg
            } else {
                let reg = abi_arg_regs.get(integer_index).cloned();
                integer_index += 1;
                reg
            };
            let Some(reg_name) = reg_name else {
                continue;
            };
            for alias in register_alias_names(&reg_name) {
                aliases.insert(alias, param.name.clone());
            }
        }

        for (idx, (ssa_var, _)) in recovered_params.iter().enumerate() {
            if let Some(param) = params.get(idx) {
                aliases.insert(ssa_var.name.to_ascii_lowercase(), param.name.clone());
            }
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
            _ => Self::unrecognized(ptr_bits),
        }
    }

    /// A target whose registers this renderer does not know.
    ///
    /// Falling back to the defaults meant falling back to x86-64: an
    /// unrecognized target was rendered with rsp, rbp and the SysV argument
    /// registers, naming registers it does not have. Naming none of them is
    /// the honest answer, and it leaves the residual machinery to say so.
    fn unrecognized(ptr_bits: u32) -> Self {
        Self {
            ptr_size: ptr_bits,
            sp_name: String::new(),
            fp_name: String::new(),
            arg_regs: Vec::new(),
            ret_regs: Vec::new(),
            caller_saved_regs: Default::default(),
            ..Self::default()
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

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct LocalStructFieldAccess {
    pub arg_index: usize,
    pub field_offset: u64,
    pub access_size: u32,
    pub is_write: bool,
}

#[derive(Debug, Clone, Default)]
struct DecompilerContext {
    #[cfg(test)]
    pub function_names: std::collections::HashMap<u64, String>,
    #[cfg(test)]
    pub strings: std::collections::HashMap<u64, String>,
    #[cfg(test)]
    pub symbols: std::collections::HashMap<u64, String>,
    /// Canonical combined type and semantic facts.
    function_facts: FunctionFacts,
}

impl DecompilerContext {
    fn type_facts(&self) -> &FunctionTypeFacts {
        self.function_facts.type_facts()
    }

    fn semantic_report(&self) -> Option<&r2sym::SemanticArtifactReport> {
        self.function_facts.semantic_report()
    }

    fn from_source_owned(
        function_facts: &r2types::function_facts::SourceOwnedFunctionFacts,
    ) -> Self {
        Self {
            #[cfg(test)]
            function_names: std::collections::HashMap::new(),
            #[cfg(test)]
            strings: std::collections::HashMap::new(),
            #[cfg(test)]
            symbols: std::collections::HashMap::new(),
            function_facts: function_facts.report().clone(),
        }
    }

    fn skip_runtime_type_inference(&self, prepared: &r2ssa::SsaArtifact) -> bool {
        let _ = prepared;
        self.function_facts
            .decompile_route()
            .is_some_and(|route| route.skip_runtime_type_inference)
    }

    fn use_prepared_semantic_view(&self, prepared: &r2ssa::SsaArtifact) -> bool {
        let _ = prepared;
        self.function_facts
            .decompile_route()
            .is_some_and(|route| route.use_prepared_semantic_view)
    }
}

#[derive(Debug, Clone)]
pub struct DecompilerInput {
    source_owned_facts: r2types::function_facts::SourceOwnedFunctionFacts,
}

impl DecompilerInput {
    pub fn new(source_owned_facts: r2types::function_facts::SourceOwnedFunctionFacts) -> Self {
        Self { source_owned_facts }
    }

    pub fn source_owned_facts(&self) -> &r2types::function_facts::SourceOwnedFunctionFacts {
        &self.source_owned_facts
    }

    pub fn prepared_ssa(&self) -> &r2ssa::SsaArtifact {
        self.source_owned_facts.source()
    }

    pub fn function_facts(&self) -> &FunctionFacts {
        self.source_owned_facts.report()
    }

    fn context_projection(&self) -> DecompilerContext {
        DecompilerContext::from_source_owned(&self.source_owned_facts)
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

    fn with_context(mut self, context: DecompilerContext) -> Self {
        self.context = context;
        self
    }

    /// Set external context (function names, strings, symbols).
    /// Set externally recovered known function signatures keyed by name.
    #[cfg(test)]
    pub fn set_known_function_signatures<T>(
        &mut self,
        signatures: std::collections::HashMap<String, T>,
    ) where
        T: Into<FunctionType>,
    {
        let mut type_facts = self.context.type_facts().clone();
        type_facts.known_function_signatures = signatures
            .into_iter()
            .map(|(name, sig)| (name, sig.into()))
            .collect();
        self.context.function_facts.replace_type_facts(type_facts);
    }

    /// Set externally recovered host type database.
    #[cfg(test)]
    pub fn set_external_type_db(&mut self, external_type_db: ExternalTypeDb) {
        let mut type_facts = self.context.type_facts().clone();
        type_facts.external_type_db = external_type_db;
        self.context.function_facts.replace_type_facts(type_facts);
    }

    /// Set externally recovered type facts.
    #[cfg(test)]
    pub fn set_type_facts(&mut self, type_facts: FunctionTypeFacts) {
        self.context.function_facts.replace_type_facts(type_facts);
    }

    fn vm_summary_output_for_route(
        &self,
        func_name: &str,
        function_facts: &FunctionFacts,
        route: &DecompileRouteFacts,
    ) -> Option<String> {
        if route.kind != DecompileRouteKind::VmSummary {
            return None;
        }
        crate::consumer_vm::render_vm_semantic_summary(
            func_name,
            function_facts,
            function_facts.semantic_report()?,
        )
    }

    /// Decompile a prepared function with an explicit typed context payload.
    pub fn decompile_input(&self, input: &DecompilerInput) -> String {
        let control = r2ssa::SsaExecutionControl::default();
        self.decompile_input_with_control(input, &control)
            .expect("default decompiler control never stops")
    }

    /// Decompile with cooperative cancellation/deadline polling.
    pub fn decompile_input_with_control<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<String, DecompileExecutionStop> {
        let work = DecompileWorkControl::new(control, DecompileWorkPhase::Normalization);
        work.poll()?;
        let func = input.prepared_ssa().function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let block_count = func.blocks().count();
        if block_count > self.config.max_blocks {
            return Ok(block_guard_fallback_comment(
                &func_name,
                block_count,
                self.config.max_blocks,
            ));
        }
        let function_facts = input.function_facts();
        let Some(semantic_route) = function_facts.decompile_route() else {
            return Ok(missing_decompile_route_residual_comment(&func_name));
        };
        if let Some(reason) = route_fallback_reason(semantic_route) {
            return Ok(artifact_guard_fallback_comment(&func_name, reason));
        }
        if let Some(reason) = summary_only_semantics_standard_render_residual_reason(
            function_facts.decompile_route(),
            function_facts.semantic_report(),
        ) {
            return Ok(artifact_guard_fallback_comment(&func_name, &reason));
        }
        if let Some(output) =
            self.vm_summary_output_for_route(&func_name, function_facts, semantic_route)
        {
            return Ok(output);
        }
        if let Some(output) = self.semantic_worker_summary_output_for_route(
            &func_name,
            function_facts,
            semantic_route,
        ) {
            return Ok(output);
        }
        let c_func = self.build_function_from_input_with_control(input, control)?;
        let render_work = work.with_phase(DecompileWorkPhase::Rendering);
        render_work.poll()?;
        let mut codegen = CodeGenerator::new(self.config.codegen.clone());
        let output = codegen.generate_function(&c_func);
        render_work.poll()?;
        Ok(output)
    }

    /// Build a C function from a prepared function + typed context payload.
    pub fn build_function_from_input(&self, input: &DecompilerInput) -> CFunction {
        let control = r2ssa::SsaExecutionControl::default();
        self.build_function_from_input_with_control(input, &control)
            .expect("default decompiler control never stops")
    }

    /// Build a C AST with cooperative cancellation/deadline polling.
    pub fn build_function_from_input_with_control<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<CFunction, DecompileExecutionStop> {
        let work = DecompileWorkControl::new(control, DecompileWorkPhase::Normalization);
        work.poll()?;
        let func = input.prepared_ssa().function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let block_count = func.blocks().count();
        if block_count > self.config.max_blocks {
            return Ok(residual_function_for_render_boundary(
                &func_name,
                &block_guard_fallback_comment(&func_name, block_count, self.config.max_blocks),
            ));
        }
        let decompiler = Self::new(self.config.clone()).with_context(input.context_projection());
        let Some(semantic_route) = decompiler.context.function_facts.decompile_route() else {
            return Ok(residual_function_for_render_boundary(
                &func_name,
                &missing_decompile_route_residual_comment(&func_name),
            ));
        };
        if let Some(reason) = route_fallback_reason(semantic_route) {
            return Ok(residual_function_for_render_boundary(&func_name, reason));
        }
        if let Some(reason) = summary_only_semantics_standard_render_residual_reason(
            decompiler.context.function_facts.decompile_route(),
            decompiler.context.function_facts.semantic_report(),
        ) {
            return Ok(residual_function_for_render_boundary(&func_name, &reason));
        }
        if route_is_summary_boundary(semantic_route) {
            return Ok(residual_function_for_summary_route_boundary(
                &func_name,
                semantic_route,
            ));
        }
        decompiler.build_function_internal_with_control(input, semantic_route, work)
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
        let vm_body = self.context.semantic_report()?.vm_body()?;
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
        route: &DecompileRouteFacts,
    ) -> Option<String> {
        consumer_summary::render_for_route(
            func_name,
            function_facts,
            function_facts.semantic_report()?,
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
            } => fold_ctx
                .extract_condition_from_block(block)
                .map(|cond| {
                    CStmt::if_stmt(
                        cond,
                        CStmt::Goto(Self::linear_block_label(*true_target)),
                        Some(CStmt::Goto(Self::linear_block_label(*false_target))),
                    )
                })
                .or_else(|| {
                    Some(CStmt::comment(format!(
                        "conditional branch condition unresolved; true_target={}, false_target={}",
                        Self::linear_block_label(*true_target),
                        Self::linear_block_label(*false_target)
                    )))
                }),
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

    fn build_function_internal_with_control<'a>(
        &self,
        input: &'a DecompilerInput,
        semantic_route: &DecompileRouteFacts,
        work: DecompileWorkControl<'a>,
    ) -> Result<CFunction, DecompileExecutionStop> {
        work.poll()?;
        let prepared = input.prepared_ssa();
        let func = prepared.function();
        let mut normalized_func = if let Some(render_facts) = self.context.function_facts.render() {
            normalize::materialize_certified_loop_carriers_with_control(
                func,
                prepared,
                render_facts,
                work,
            )?
        } else {
            func.clone()
        };
        if let Some(render_facts) = self.context.function_facts.render() {
            normalize::materialize_certified_loop_carrier_initializers_with_control(
                &mut normalized_func,
                prepared,
                render_facts,
                work,
            )?;
        }
        work.poll()?;
        let func = &normalized_func;
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let render_signature = self.context.type_facts().render_authorized_signature();
        // Recover variables
        let mut var_recovery = VariableRecovery::new_with_abi(
            &self.config.sp_name,
            &self.config.fp_name,
            self.config.ptr_size,
            self.config.arg_regs.clone(),
            self.config.ret_regs.clone(),
        );
        var_recovery.recover_input(input);
        let skip_runtime_type_inference = self.context.skip_runtime_type_inference(prepared);
        let type_inference = (!skip_runtime_type_inference).then(|| {
            let mut type_inference = TypeInference::new_with_abi(
                self.config.ptr_size,
                self.config.arg_regs.clone(),
                self.config.ret_regs.clone(),
            );
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
            type_inference.set_prepared_ssa(prepared);
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
        let mut params = merge_params_with_external_signature(
            recovered_param_infos
                .iter()
                .map(|(_, param)| param.clone())
                .collect(),
            render_signature,
        );
        apply_source_parameter_names(&mut params, self.context.function_facts.display_names());
        let param_register_aliases = build_param_register_aliases(
            &params,
            &recovered_param_infos,
            &self.context.type_facts().register_params,
            &self.config.arg_regs,
            true,
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
        let fold_function_return_type = signature_ret_type.as_ref().or(Some(&inferred_ret_type));
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
        let use_prepared_semantic_view = self.context.use_prepared_semantic_view(prepared);
        let prepared_semantic_view = use_prepared_semantic_view.then(|| {
            analysis::PreparedSemanticView::build(analysis::PreparedSemanticViewInputs {
                prepared,
                abi_arg_regs: &self.config.arg_regs,
                stack_slots: &self.context.type_facts().stack_slots,
                visible_bindings: &self.context.type_facts().visible_bindings,
                param_register_aliases: &param_register_aliases,
                function_facts: &self.context.function_facts,
                #[cfg(test)]
                certified_rendering_required: false,
            })
        });
        let fold_inputs = FoldInputs {
            arch: &fold_arch,
            display_names: self.context.function_facts.display_names(),
            #[cfg(test)]
            function_names: &self.context.function_names,
            #[cfg(test)]
            strings: &self.context.strings,
            #[cfg(test)]
            symbols: &self.context.symbols,
            function_facts: &self.context.function_facts,
            #[cfg(test)]
            certified_rendering_required: false,
            stack_slots: &self.context.type_facts().stack_slots,
            field_access_certificates: &self.context.type_facts().field_access_certificates,
            #[cfg(test)]
            external_stack_vars: &self.context.type_facts().external_stack_vars,
            visible_bindings: &self.context.type_facts().visible_bindings,
            external_type_db: &self.context.type_facts().external_type_db,
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle,
            function_return_type: fold_function_return_type,
            prepared_ssa: Some(prepared),
            prepared_semantic_view: prepared_semantic_view.as_ref(),
            prepared_objects: Some(prepared.objects()),
            prepared_memory: Some(prepared.memory()),
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        let structuring_work = work.with_phase(DecompileWorkPhase::Structuring);
        fold_ctx.analyze_blocks_with_control(&fold_blocks, structuring_work)?;
        structuring_work.poll()?;
        fold_ctx.analyze_function_structure(func);
        structuring_work.poll()?;
        // Structure control flow (primary path: folded)
        let mut structurer =
            ControlFlowStructurer::new_with_control(func, &fold_ctx, structuring_work)?;

        // Get set of variables that survive folding before structuring.
        let emitted_vars = structurer.emitted_var_names();
        let routed_body = consumer_structured::primary_body_for_semantic_route(
            semantic_route,
            &mut structurer,
            || self.linearize_function_body(func, &fold_ctx),
        );
        if let Some(stop) = structurer.execution_stop() {
            return Err(stop);
        }
        structuring_work.poll()?;
        let use_conservative_locals = routed_body.use_conservative_locals;
        let is_linear_fallback = routed_body.is_linear_fallback;
        let mut body_stmt = routed_body.body_stmt;

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
                    let not_param_home = !v
                        .stack_offset
                        .is_some_and(|offset| param_home_offsets.contains(&offset));
                    not_param_home
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
        // A slot that owns a call result is declared with what the callee
        // returns; nothing else may know its type on a binary without symbols.
        let owned_call_result_local_types = fold_ctx.owned_call_result_types_by_stack_offset();
        let locals = locals
            .into_iter()
            .map(|local| {
                let hint = local
                    .stack_offset
                    .and_then(|offset| owned_call_result_local_types.get(&offset));
                ast::CLocal {
                    ty: choose_more_specific_runtime_type(local.ty, hint),
                    ..local
                }
            })
            .collect::<Vec<_>>();
        let mut c_function = CFunction {
            name: func_name,
            ret_type: render_signature
                .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                .unwrap_or_else(|| inferred_ret_type.clone()),
            params,
            locals,
            body,
            // Parameters here come from the render signature, so an empty list
            // is a recovered empty list rather than an unknown one.
            params_known: true,
        };
        append_semantic_summary_return_to_function_if_needed(
            &mut c_function,
            &self.context.function_facts,
            self.context.function_facts.semantic_report(),
        );

        let strings = self.context.function_facts.display_names().strings();
        fold_constant_arithmetic_in_function(&mut c_function, strings);
        // Binding a repeated call to one name means finding the call site in
        // the body, and that match is by expression. The body has just been
        // folded -- an adrp/add pair is one address and that address is a
        // string -- while the recorded site is still the unfolded form, so
        // `strcmp(password, "secret123")` matched nothing and was printed once
        // per use. The sites fold the same way before they are matched.
        let mut folded_call_sites = fold_ctx.call_result_exprs_map().clone();
        for expr in folded_call_sites.values_mut() {
            fold_constant_arithmetic_in_expr(expr, strings);
        }
        single_evaluation::bind_each_call_site_once(&mut c_function, &folded_call_sites);
        simplify_identities_in_function(&mut c_function, &fold_ctx);
        propagate_single_use_register_carriers(&mut c_function, &fold_ctx);
        rewrite_stack_synonym_uses_to_declared_locals(&mut c_function, &fold_ctx);
        // Dropping a version suffix loses which value a name meant, so anything
        // that resolves a name to the storage behind it has to run before this.
        // Linear fallback intentionally keeps its raw expression-builder output.
        if !is_linear_fallback {
            let mut known_function_names = HashSet::new();
            for name in self.context.type_facts().known_function_signatures.keys() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            post_rename::rewrite_function_identifiers(&mut c_function, &known_function_names);
        }
        reconstruct_flag_conditions_in_function(&mut c_function, &fold_ctx);
        prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx);
        prune_unused_pure_locals(&mut c_function);
        resolve_undeclared_carriers(&mut c_function, &fold_ctx);
        prune_unreferenced_local_declarations(&mut c_function);
        normalize_redundant_return_carrier_casts(&mut c_function);
        normalize_declared_assignment_literals(&mut c_function);
        normalize_comparison_operand_order(&mut c_function);
        unrendered::prune_unreferenced_labels(&mut c_function);
        unrendered::drop_values_from_void_returns(&mut c_function);
        // Whatever carriers are still on the page after every pass that could
        // resolve one, the body reads and writes, so it declares them.
        unrendered::declare_rendered_carriers(&mut c_function, &type_hints);
        unrendered::mark_undeclared_names(&mut c_function);
        // Executable C is admitted only when the source obligation inventory is
        // complete. The inventory is what says which effects the source has, so a
        // function whose inventory did not close has no account of what the output
        // owes, and rendering it says the effects were all handled when nothing
        // ever enumerated them.
        if let Some(reason) = incomplete_source_obligations_reason(prepared) {
            return Ok(residual_function_for_render_boundary(&c_function.name, &reason));
        }
        let mut ledger = build_obligation_ledger(
            prepared,
            &fold_ctx.effect_render_proofs_since(0),
            &fold_ctx.folded_block_addrs(),
            &fold_ctx.elided_op_sites(),
        );
        reconcile_ledger_with_body(&mut ledger, &c_function);
        note_unproven_constructs(&mut c_function, Some(&ledger));
        work.with_phase(DecompileWorkPhase::Rendering).poll()?;
        Ok(c_function)
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

/// Replace a single-use SSA register carrier with the value it copied.
///
/// The lifter names every version of a machine register, so bookkeeping the
/// source did for itself arrives as `x8_8 = arg_28; return x8_8;`. `x8_8` is
/// not a variable the program has - it is the eighth version of a register -
/// and declaring one asserts a local that never existed. Where such a carrier
/// is assigned once from a pure expression and read once afterwards, the read
/// becomes that expression and the assignment falls to the dead-assignment
/// prune that already runs.
///
/// Propagation is refused when anything between the assignment and the read
/// writes what the expression reads, because moving a computation past a write
/// to its own inputs changes what it computes.
/// Fold a value bound to a name that is read once into the place it is read.
///
/// Apply the identity rules to every expression the function renders.
///
/// The rules used to reach only the value side of an assignment, so `x ^ x` folded
/// where it was stored and stayed where it was tested: a loop kept running
/// `while (len != (i ^ i) + 1)`. A condition is an expression like any other and
/// the same rules decide it.
fn simplify_identities_in_function(func: &mut CFunction, fold_ctx: &FoldingContext<'_>) {
    fn visit(stmt: &mut CStmt, fold_ctx: &FoldingContext<'_>) {
        single_evaluation::for_each_expr_mut(stmt, &mut |expr| {
            let taken = std::mem::replace(expr, CExpr::IntLit(0));
            *expr = fold_ctx.simplify_identities(taken);
        });
        if let CStmt::For { init: Some(init), .. } = stmt {
            visit(init, fold_ctx);
        }
        single_evaluation::for_each_child_block_mut(stmt, &mut |body, _| {
            for stmt in body.iter_mut() {
                visit(stmt, fold_ctx);
            }
        });
    }

    for stmt in &mut func.body {
        visit(stmt, fold_ctx);
    }
}

/// Give a carrier the body writes but the function never declares exactly one
/// disposition: dropped when nothing reads it, declared when something does.
///
/// Propagation runs first and takes the values a single reader consumes. What is
/// left is a value the function genuinely keeps, and printing it as a bare name
/// says the program has a variable it never declared. Naming a value obliges the
/// function to declare it, so the two arms here are what that obligation costs.
/// Fold machine flag arithmetic into the comparison it spells, wherever it
/// appears.
///
/// Branch conditions are reconstructed as they are built, so an `if` shows
/// `a > b`. A comparison that ends up somewhere else keeps the flags showing:
/// a ternary condition in a return read `n - 1 < 0 != tmpOV`, which is the
/// signed `n < 1` written as "the sign of the difference disagrees with the
/// overflow flag", and named an overflow temporary the function never
/// declares. The reconstruction does not care where the expression sits, so
/// run it over the finished body rather than only at the places that build
/// conditions.
fn reconstruct_flag_conditions_in_function(func: &mut CFunction, fold_ctx: &FoldingContext<'_>) {
    fn rewrite(expr: CExpr, ctx: &FoldingContext<'_>) -> CExpr {
        let mut recurse = |child: CExpr| rewrite(child, ctx);
        let expr = expr.map_children(&mut recurse);
        ctx.try_reconstruct_condition(&expr).unwrap_or(expr)
    }

    fn walk(stmts: &mut Vec<CStmt>, ctx: &FoldingContext<'_>) {
        for stmt in stmts.iter_mut() {
            single_evaluation::for_each_expr_mut(stmt, &mut |expr| {
                let taken = std::mem::replace(expr, CExpr::IntLit(0));
                *expr = rewrite(taken, ctx);
            });
            single_evaluation::for_each_child_block_mut(stmt, &mut |body, _| {
                walk(body, ctx);
            });
        }
    }

    walk(&mut func.body, fold_ctx);
}

fn resolve_undeclared_carriers(func: &mut CFunction, fold_ctx: &FoldingContext<'_>) {
    let declared = func
        .params
        .iter()
        .map(|param| param.name.to_ascii_lowercase())
        .chain(func.locals.iter().map(|local| local.name.to_ascii_lowercase()))
        .collect::<HashSet<_>>();

    // Dropping one dead carrier can leave the value it read with no reader, so
    // the pass repeats until a sweep removes nothing.
    // The caller reads the return register, so a carrier that names it is never
    // dead here however the body reads it. Dropping one would delete the value
    // the function answers with and leave nothing saying it was ever computed.
    let returns_value = !matches!(func.ret_type, CType::Void);

    loop {
        let reads = collect_function_local_reads(func);
        let mut removed = false;
        drop_dead_undeclared_carriers(
            &mut func.body,
            &declared,
            &reads,
            fold_ctx,
            returns_value,
            &mut removed,
        );
        if !removed {
            break;
        }
    }

    let mut carriers = Vec::new();
    collect_undeclared_carrier_targets(&mut func.body, &declared, &mut carriers);
    let mut seen = HashSet::new();
    for (name, value) in carriers {
        if !seen.insert(name.to_ascii_lowercase()) {
            continue;
        }
        let ty = fold_ctx.declared_type_for_carrier(&name, &value);
        func.locals.push(ast::CLocal {
            ty,
            name,
            stack_offset: None,
        });
    }
}

/// Remove every assignment to an undeclared name that nothing reads, provided
/// evaluating its value does nothing on its own.
fn drop_dead_undeclared_carriers(
    stmts: &mut Vec<CStmt>,
    declared: &HashSet<String>,
    reads: &HashSet<String>,
    fold_ctx: &FoldingContext<'_>,
    returns_value: bool,
    removed: &mut bool,
) {
    for stmt in stmts.iter_mut() {
        single_evaluation::for_each_expr_mut(stmt, &mut |expr| {
            drop_dead_undeclared_comma_carriers(
                expr,
                declared,
                reads,
                fold_ctx,
                returns_value,
                removed,
            );
        });
        single_evaluation::for_each_child_block_mut(stmt, &mut |body, _| {
            drop_dead_undeclared_carriers(
                body,
                declared,
                reads,
                fold_ctx,
                returns_value,
                removed,
            );
        });
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
        else {
            continue;
        };
        let CExpr::Var(name) = left.as_ref() else {
            continue;
        };
        let lower = name.to_ascii_lowercase();
        if declared.contains(&lower)
            || reads.contains(&lower)
            || !expr_is_pure_for_dead_local_prune(right)
            || (returns_value && fold_ctx.carrier_names_return_register(name))
        {
            continue;
        }
        *stmt = CStmt::Empty;
        *removed = true;
    }
    stmts.retain(|stmt| !matches!(stmt, CStmt::Empty));
}

/// The same rule inside a comma expression, where the lifter parks a store that
/// a condition then evaluates: `while (t3f680 = n, i < n)` tests `i < n` and
/// names storage nobody reads to say so.
fn drop_dead_undeclared_comma_carriers(
    expr: &mut CExpr,
    declared: &HashSet<String>,
    reads: &HashSet<String>,
    fold_ctx: &FoldingContext<'_>,
    returns_value: bool,
    removed: &mut bool,
) {
    for child in single_evaluation::children_mut(expr) {
        drop_dead_undeclared_comma_carriers(child, declared, reads, fold_ctx, returns_value, removed);
    }
    let CExpr::Comma(items) = expr else {
        return;
    };
    // The last item is the value of the comma expression, so it is never a store
    // nothing reads however the name is spelled.
    let last = items.len().saturating_sub(1);
    let mut index = 0;
    items.retain(|item| {
        let keep = index == last
            || !dead_undeclared_carrier_assignment(
                item,
                declared,
                reads,
                fold_ctx,
                returns_value,
            );
        if !keep {
            *removed = true;
        }
        index += 1;
        keep
    });
    if items.len() == 1
        && let Some(only) = items.pop()
    {
        *expr = only;
    }
}

/// Whether this expression stores to a name the function never declares and
/// nothing reads, with a value that does nothing on its own.
fn dead_undeclared_carrier_assignment(
    expr: &CExpr,
    declared: &HashSet<String>,
    reads: &HashSet<String>,
    fold_ctx: &FoldingContext<'_>,
    returns_value: bool,
) -> bool {
    let CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    } = expr
    else {
        return false;
    };
    let CExpr::Var(name) = left.as_ref() else {
        return false;
    };
    let lower = name.to_ascii_lowercase();
    !declared.contains(&lower)
        && !reads.contains(&lower)
        && expr_is_pure_for_dead_local_prune(right)
        && !(returns_value && fold_ctx.carrier_names_return_register(name))
}

/// Every undeclared name the body assigns, paired with the value first stored in
/// it so the declaration can be typed from what it holds.
fn collect_undeclared_carrier_targets(
    stmts: &mut Vec<CStmt>,
    declared: &HashSet<String>,
    out: &mut Vec<(String, CExpr)>,
) {
    for stmt in stmts.iter_mut() {
        if let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
            && let CExpr::Var(name) = left.as_ref()
            && !declared.contains(&name.to_ascii_lowercase())
        {
            out.push((name.clone(), right.as_ref().clone()));
        }
        single_evaluation::for_each_child_block_mut(stmt, &mut |body, _| {
            collect_undeclared_carrier_targets(body, declared, out);
        });
    }
}

/// A name assigned once and read once is not a variable of the program, it is
/// the value itself with a label attached. That is true of the versioned
/// register carriers this started with, and equally of the temporaries the
/// lifter leaves behind: `t3e580 = a - b; *p = t3e580;` says no more than
/// `*p = a - b;` and says it with a name the function never declares.
fn propagate_single_use_register_carriers(func: &mut CFunction, fold_ctx: &FoldingContext<'_>) {
    let declared = func
        .params
        .iter()
        .map(|param| param.name.clone())
        .chain(func.locals.iter().map(|local| local.name.clone()))
        .collect::<std::collections::HashSet<_>>();

    fn visit_block(
        stmts: &mut Vec<CStmt>,
        fold_ctx: &FoldingContext<'_>,
        declared: &std::collections::HashSet<String>,
    ) {
        for stmt in stmts.iter_mut() {
            visit_nested(stmt, fold_ctx, declared);
        }
        let mut index = 0;
        while index < stmts.len() {
            let Some((name, value)) = carrier_assignment(&stmts[index], fold_ctx, declared) else {
                index += 1;
                continue;
            };
            let rest = &stmts[index + 1..];
            if count_var_reads_in_stmts(rest, &name) != 1 {
                index += 1;
                continue;
            }
            let Some(offset) = rest
                .iter()
                .position(|stmt| count_var_reads_in_stmts(std::slice::from_ref(stmt), &name) == 1)
            else {
                index += 1;
                continue;
            };
            let reads = expr_var_names(&value);
            let blocked = rest[..offset].iter().any(|between| {
                let (_, def) = fold_ctx.stmt_reads_and_def_for_render(between);
                def.is_some_and(|def| reads.iter().any(|read| read.eq_ignore_ascii_case(&def)))
            });
            if blocked {
                index += 1;
                continue;
            }
            let target = index + 1 + offset;
            substitute_var_in_stmt(&mut stmts[target], &name, &value);
            stmts.remove(index);
        }
    }

    fn visit_nested(
        stmt: &mut CStmt,
        fold_ctx: &FoldingContext<'_>,
        declared: &std::collections::HashSet<String>,
    ) {
        match stmt {
            CStmt::Block(stmts) => visit_block(stmts, fold_ctx, declared),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                visit_nested(then_body, fold_ctx, declared);
                if let Some(else_body) = else_body {
                    visit_nested(else_body, fold_ctx, declared);
                }
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
                visit_nested(body, fold_ctx, declared)
            }
            CStmt::For { init, body, .. } => {
                if let Some(init) = init {
                    visit_nested(init, fold_ctx, declared);
                }
                visit_nested(body, fold_ctx, declared);
            }
            CStmt::Switch { cases, default, .. } => {
                for case in cases {
                    visit_block(&mut case.body, fold_ctx, declared);
                }
                if let Some(default) = default {
                    visit_block(default, fold_ctx, declared);
                }
            }
            _ => {}
        }
    }

    visit_block(&mut func.body, fold_ctx, &declared);
}

/// The carrier assigned by this statement, when it is one worth propagating.
fn carrier_assignment(
    stmt: &CStmt,
    fold_ctx: &FoldingContext<'_>,
    declared: &std::collections::HashSet<String>,
) -> Option<(String, CExpr)> {
    let CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    }) = stmt
    else {
        return None;
    };
    let CExpr::Var(name) = left.as_ref() else {
        return None;
    };
    // Either a register carrier, which this pass has always folded, or a name
    // the function never declares -- a temporary the lifter left behind. The
    // second only qualifies when evaluating it does nothing, since moving a
    // value to its reader moves whatever computing it does along with it.
    let is_register_carrier =
        fold_ctx.stmt_is_side_effect_free_versioned_register_carrier_for_render(stmt);
    let is_undeclared_temporary =
        !declared.contains(name) && expr_is_pure_for_dead_local_prune(right);
    if !is_register_carrier && !is_undeclared_temporary {
        return None;
    }
    Some((name.clone(), right.as_ref().clone()))
}

/// Every variable an expression reads.
fn expr_var_names(expr: &CExpr) -> Vec<String> {
    let mut names = Vec::new();
    expr.visit(&mut |node| {
        if let CExpr::Var(name) = node {
            names.push(name.clone());
        }
    });
    names
}

/// Fold arithmetic between integer literals, and name the result when it names
/// a string.
///
/// A PIC address arrives as two constants: `adrp` puts a page in a register and
/// `add` puts the offset on top, so the renderer had `0x100002000U + 0xbbc`
/// where the program has one address. The sum is strictly more readable folded,
/// and folding it is also what lets the string table answer: the table is keyed
/// by address, and until the two halves are one number there is no address to
/// look up.
fn fold_constant_arithmetic_in_function(
    func: &mut CFunction,
    strings: &std::collections::BTreeMap<u64, String>,
) {
    for stmt in &mut func.body {
        fold_constant_arithmetic_in_stmt(stmt, strings);
    }
}

fn fold_constant_arithmetic_in_stmt(
    stmt: &mut CStmt,
    strings: &std::collections::BTreeMap<u64, String>,
) {
    let mut fold_expr = |expr: &mut CExpr| fold_constant_arithmetic_in_expr(expr, strings);
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => fold_expr(expr),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                fold_expr(init);
            }
        }
        CStmt::Return(expr) => {
            if let Some(expr) = expr {
                fold_expr(expr);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                fold_constant_arithmetic_in_stmt(stmt, strings);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            fold_expr(cond);
            fold_constant_arithmetic_in_stmt(then_body, strings);
            if let Some(else_body) = else_body {
                fold_constant_arithmetic_in_stmt(else_body, strings);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            fold_expr(cond);
            fold_constant_arithmetic_in_stmt(body, strings);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                fold_constant_arithmetic_in_stmt(init, strings);
            }
            if let Some(cond) = cond {
                fold_expr(cond);
            }
            if let Some(update) = update {
                fold_expr(update);
            }
            fold_constant_arithmetic_in_stmt(body, strings);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            fold_expr(expr);
            for case in cases {
                for stmt in &mut case.body {
                    fold_constant_arithmetic_in_stmt(stmt, strings);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    fold_constant_arithmetic_in_stmt(stmt, strings);
                }
            }
        }
    }
}

/// The unsigned value of an integer literal, ignoring any cast around it.
fn literal_value(expr: &CExpr) -> Option<u64> {
    match expr {
        CExpr::UIntLit(value) => Some(*value),
        CExpr::IntLit(value) => u64::try_from(*value).ok(),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => literal_value(inner),
        _ => None,
    }
}

fn fold_constant_arithmetic_in_expr(
    expr: &mut CExpr,
    strings: &std::collections::BTreeMap<u64, String>,
) {
    match expr {
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => fold_constant_arithmetic_in_expr(operand, strings),
        CExpr::Binary { op, left, right } => {
            fold_constant_arithmetic_in_expr(left, strings);
            fold_constant_arithmetic_in_expr(right, strings);
            if let (Some(lhs), Some(rhs)) = (literal_value(left), literal_value(right)) {
                // Wrapping, because the program's arithmetic wraps; a fold that
                // disagreed with the machine would be worse than no fold.
                let folded = match op {
                    BinaryOp::Add => Some(lhs.wrapping_add(rhs)),
                    BinaryOp::Sub => Some(lhs.wrapping_sub(rhs)),
                    _ => None,
                };
                if let Some(folded) = folded {
                    *expr = CExpr::UIntLit(folded);
                }
            }
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            fold_constant_arithmetic_in_expr(cond, strings);
            fold_constant_arithmetic_in_expr(then_expr, strings);
            fold_constant_arithmetic_in_expr(else_expr, strings);
        }
        CExpr::Call { func, args } => {
            fold_constant_arithmetic_in_expr(func, strings);
            for arg in args {
                fold_constant_arithmetic_in_expr(arg, strings);
            }
        }
        CExpr::Subscript { base, index } => {
            fold_constant_arithmetic_in_expr(base, strings);
            fold_constant_arithmetic_in_expr(index, strings);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            fold_constant_arithmetic_in_expr(base, strings)
        }
        CExpr::Comma(items) => {
            for item in items {
                fold_constant_arithmetic_in_expr(item, strings);
            }
        }
        _ => {}
    }
    // Once the address is one number the string table can answer for it.
    if let Some(value) = literal_value(expr)
        && let Some(text) = strings.get(&value)
    {
        *expr = CExpr::StringLit(text.clone());
    }
}

/// How many times `name` is read across these statements.
fn count_var_reads_in_stmts(stmts: &[CStmt], name: &str) -> usize {
    let mut reads = 0;
    for stmt in stmts {
        count_var_reads_in_stmt(stmt, name, &mut reads);
    }
    reads
}

fn count_var_reads_in_stmt(stmt: &CStmt, name: &str, reads: &mut usize) {
    let mut count_expr = |expr: &CExpr, reads: &mut usize| {
        expr.visit(&mut |node| {
            if matches!(node, CExpr::Var(found) if found.eq_ignore_ascii_case(name)) {
                *reads += 1;
            }
        });
    };
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => count_expr(expr, reads),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                count_expr(init, reads);
            }
        }
        CStmt::Return(expr) => {
            if let Some(expr) = expr {
                count_expr(expr, reads);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                count_var_reads_in_stmt(stmt, name, reads);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            count_expr(cond, reads);
            count_var_reads_in_stmt(then_body, name, reads);
            if let Some(else_body) = else_body {
                count_var_reads_in_stmt(else_body, name, reads);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            count_expr(cond, reads);
            count_var_reads_in_stmt(body, name, reads);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                count_var_reads_in_stmt(init, name, reads);
            }
            if let Some(cond) = cond {
                count_expr(cond, reads);
            }
            if let Some(update) = update {
                count_expr(update, reads);
            }
            count_var_reads_in_stmt(body, name, reads);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            count_expr(expr, reads);
            for case in cases {
                for stmt in &case.body {
                    count_var_reads_in_stmt(stmt, name, reads);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    count_var_reads_in_stmt(stmt, name, reads);
                }
            }
        }
    }
}

/// Put `value` wherever `name` is read in this statement.
fn substitute_var_in_stmt(stmt: &mut CStmt, name: &str, value: &CExpr) {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => substitute_var_in_expr(expr, name, value),
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                substitute_var_in_expr(init, name, value);
            }
        }
        CStmt::Return(expr) => {
            if let Some(expr) = expr {
                substitute_var_in_expr(expr, name, value);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                substitute_var_in_stmt(stmt, name, value);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            substitute_var_in_expr(cond, name, value);
            substitute_var_in_stmt(then_body, name, value);
            if let Some(else_body) = else_body {
                substitute_var_in_stmt(else_body, name, value);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            substitute_var_in_expr(cond, name, value);
            substitute_var_in_stmt(body, name, value);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                substitute_var_in_stmt(init, name, value);
            }
            if let Some(cond) = cond {
                substitute_var_in_expr(cond, name, value);
            }
            if let Some(update) = update {
                substitute_var_in_expr(update, name, value);
            }
            substitute_var_in_stmt(body, name, value);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            substitute_var_in_expr(expr, name, value);
            for case in cases {
                for stmt in &mut case.body {
                    substitute_var_in_stmt(stmt, name, value);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    substitute_var_in_stmt(stmt, name, value);
                }
            }
        }
    }
}

fn substitute_var_in_expr(expr: &mut CExpr, name: &str, value: &CExpr) {
    if matches!(expr, CExpr::Var(found) if found.eq_ignore_ascii_case(name)) {
        *expr = value.clone();
        return;
    }
    match expr {
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => substitute_var_in_expr(operand, name, value),
        CExpr::Binary { op, left, right } => {
            // The left operand of an assignment names storage. Substituting a
            // value there rewrites what the statement writes into what it
            // wrote, which is how a slot the source never named rendered as
            // `1 = 1;`.
            if !op.writes_left_operand() {
                substitute_var_in_expr(left, name, value);
            }
            substitute_var_in_expr(right, name, value);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            substitute_var_in_expr(cond, name, value);
            substitute_var_in_expr(then_expr, name, value);
            substitute_var_in_expr(else_expr, name, value);
        }
        CExpr::Call { func, args } => {
            substitute_var_in_expr(func, name, value);
            for arg in args {
                substitute_var_in_expr(arg, name, value);
            }
        }
        CExpr::Subscript { base, index } => {
            substitute_var_in_expr(base, name, value);
            substitute_var_in_expr(index, name, value);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            substitute_var_in_expr(base, name, value)
        }
        CExpr::Comma(items) => {
            for item in items {
                substitute_var_in_expr(item, name, value);
            }
        }
        _ => {}
    }
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
        } else if let Some(offset) = fold_ctx.loaded_stack_offset_for_visible_name(&name) {
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

fn normalize_redundant_return_carrier_casts(func: &mut CFunction) {
    fn visit(stmt: &mut CStmt, ret_type: &CType, declared_types: &HashMap<String, CType>) {
        match stmt {
            CStmt::Return(Some(expr)) => {
                let CExpr::Cast { expr: inner, .. } = expr else {
                    return;
                };
                let CExpr::Var(name) = inner.as_ref() else {
                    return;
                };
                if declared_types
                    .get(&name.to_ascii_lowercase())
                    .is_some_and(|ty| ty == ret_type)
                {
                    *expr = *inner.clone();
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    visit(stmt, ret_type, declared_types);
                }
            }
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                visit(then_body, ret_type, declared_types);
                if let Some(else_body) = else_body {
                    visit(else_body, ret_type, declared_types);
                }
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
                visit(body, ret_type, declared_types);
            }
            CStmt::For { init, body, .. } => {
                if let Some(init) = init {
                    visit(init, ret_type, declared_types);
                }
                visit(body, ret_type, declared_types);
            }
            CStmt::Switch { cases, default, .. } => {
                for case in cases {
                    for stmt in &mut case.body {
                        visit(stmt, ret_type, declared_types);
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        visit(stmt, ret_type, declared_types);
                    }
                }
            }
            CStmt::Empty
            | CStmt::Expr(_)
            | CStmt::Decl { .. }
            | CStmt::Return(None)
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_) => {}
        }
    }

    let declared_types = func
        .params
        .iter()
        .map(|param| (param.name.to_ascii_lowercase(), param.ty.clone()))
        .chain(
            func.locals
                .iter()
                .map(|local| (local.name.to_ascii_lowercase(), local.ty.clone())),
        )
        .collect::<HashMap<_, _>>();
    for stmt in &mut func.body {
        visit(stmt, &func.ret_type, &declared_types);
    }
}

fn typed_integer_literal_expr(value: u64, is_signed: bool, bits: u32) -> CExpr {
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let truncated = value & mask;
    if is_signed {
        let sign_bit = 1u64 << (bits - 1);
        if truncated & sign_bit != 0 {
            return CExpr::IntLit((truncated | (!mask)) as i64);
        }
        return CExpr::IntLit(truncated as i64);
    }
    if bits == 64 || truncated > 0x7fff_ffff {
        CExpr::UIntLit(truncated)
    } else {
        CExpr::IntLit(truncated as i64)
    }
}

/// Width and signedness of a spelled integer type.
///
/// A type carried by name renders as the source wrote it, which is what a
/// reader wants, but a consumer still has to know how wide it is. Only
/// spellings whose width is fixed by the language are answered here: `long`
/// and `size_t` depend on the target and are left unresolved rather than
/// guessed.
fn spelled_integer_shape(spelling: &str) -> Option<(bool, u32)> {
    let normalized = spelling
        .split_whitespace()
        .filter(|word| !matches!(*word, "const" | "volatile" | "restrict"))
        .collect::<Vec<_>>()
        .join(" ");
    match normalized.as_str() {
        "char" | "signed char" | "int8_t" => Some((true, 8)),
        "unsigned char" | "uint8_t" => Some((false, 8)),
        "short" | "short int" | "signed short" | "int16_t" => Some((true, 16)),
        "unsigned short" | "unsigned short int" | "uint16_t" => Some((false, 16)),
        "int" | "signed" | "signed int" | "int32_t" => Some((true, 32)),
        "unsigned" | "unsigned int" | "uint32_t" => Some((false, 32)),
        "int64_t" | "long long" | "signed long long" => Some((true, 64)),
        "uint64_t" | "unsigned long long" => Some((false, 64)),
        _ => None,
    }
}

fn normalize_literal_for_declared_type(expr: &mut CExpr, ty: &CType) {
    let (is_signed, bits) = match ty {
        CType::Int(bits) => (true, *bits),
        CType::UInt(bits) => (false, *bits),
        CType::Bool => (false, 1),
        CType::Typedef(name) => match spelled_integer_shape(name) {
            Some(shape) => shape,
            None => return,
        },
        _ => return,
    };
    if bits == 0 || bits > 64 {
        return;
    }
    match expr {
        CExpr::UIntLit(value) => {
            *expr = typed_integer_literal_expr(*value, is_signed, bits);
        }
        CExpr::IntLit(value) if *value >= 0 => {
            *expr = typed_integer_literal_expr(*value as u64, is_signed, bits);
        }
        CExpr::Paren(inner) => normalize_literal_for_declared_type(inner, ty),
        _ => {}
    }
}

/// Put the constant on the right of a comparison, the way C is written.
///
/// The lifted form keeps whichever operand the instruction encoded first, so a
/// bound reads as `100 < len` where the source said `len > 100`. Mirroring the
/// operator alongside the operands preserves the meaning exactly.
fn normalize_comparison_operand_order(func: &mut CFunction) {
    fn is_literal(expr: &CExpr) -> bool {
        match expr {
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::CharLit(_) => true,
            CExpr::Paren(inner) => is_literal(inner),
            _ => false,
        }
    }

    fn mirrored(op: BinaryOp) -> Option<BinaryOp> {
        match op {
            BinaryOp::Lt => Some(BinaryOp::Gt),
            BinaryOp::Gt => Some(BinaryOp::Lt),
            BinaryOp::Le => Some(BinaryOp::Ge),
            BinaryOp::Ge => Some(BinaryOp::Le),
            BinaryOp::Eq => Some(BinaryOp::Eq),
            BinaryOp::Ne => Some(BinaryOp::Ne),
            _ => None,
        }
    }

    fn visit(expr: &mut CExpr) {
        for child in single_evaluation::children_mut(expr) {
            visit(child);
        }
        let CExpr::Binary { op, left, right } = expr else {
            return;
        };
        let Some(flipped) = mirrored(*op) else {
            return;
        };
        if !is_literal(left) || is_literal(right) {
            return;
        }
        std::mem::swap(left, right);
        *op = flipped;
    }

    fn visit_stmt(stmt: &mut CStmt) {
        single_evaluation::for_each_expr_mut(stmt, &mut visit);
        single_evaluation::for_each_child_block_mut(stmt, &mut |stmts, _| {
            for stmt in stmts.iter_mut() {
                visit_stmt(stmt);
            }
        });
    }

    for stmt in &mut func.body {
        visit_stmt(stmt);
    }
}

/// Key under which the function's own return type rides in the declared-type
/// map. A local cannot be called this, so it cannot collide with one.
const RETURN_TYPE_KEY: &str = "\u{0}return";

fn normalize_declared_assignment_literals(func: &mut CFunction) {
    fn visit_expr(expr: &mut CExpr, declared_types: &HashMap<String, CType>) {
        match expr {
            CExpr::Unary { operand, .. }
            | CExpr::Cast { expr: operand, .. }
            | CExpr::Sizeof(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Deref(operand)
            | CExpr::Paren(operand) => visit_expr(operand, declared_types),
            CExpr::Binary { left, right, .. } => {
                visit_expr(left, declared_types);
                visit_expr(right, declared_types);
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                visit_expr(cond, declared_types);
                visit_expr(then_expr, declared_types);
                visit_expr(else_expr, declared_types);
            }
            CExpr::Call { func, args } => {
                visit_expr(func, declared_types);
                for arg in args {
                    visit_expr(arg, declared_types);
                }
            }
            CExpr::Subscript { base, index } => {
                visit_expr(base, declared_types);
                visit_expr(index, declared_types);
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                visit_expr(base, declared_types);
            }
            CExpr::Comma(exprs) => {
                for expr in exprs {
                    visit_expr(expr, declared_types);
                }
            }
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::Var(_)
            | CExpr::SizeofType(_) => {}
        }

        let CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } = expr
        else {
            return;
        };
        let CExpr::Var(name) = left.as_ref() else {
            return;
        };
        if let Some(ty) = declared_types.get(&name.to_ascii_lowercase()) {
            normalize_literal_for_declared_type(right, ty);
        }
    }

    fn visit_stmt(stmt: &mut CStmt, declared_types: &HashMap<String, CType>) {
        match stmt {
            CStmt::Expr(expr) => visit_expr(expr, declared_types),
            CStmt::Decl { ty, init, .. } => {
                if let Some(init) = init {
                    visit_expr(init, declared_types);
                    normalize_literal_for_declared_type(init, ty);
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    visit_stmt(stmt, declared_types);
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                visit_expr(cond, declared_types);
                visit_stmt(then_body, declared_types);
                if let Some(else_body) = else_body {
                    visit_stmt(else_body, declared_types);
                }
            }
            CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
                visit_expr(cond, declared_types);
                visit_stmt(body, declared_types);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    visit_stmt(init, declared_types);
                }
                if let Some(cond) = cond {
                    visit_expr(cond, declared_types);
                }
                if let Some(update) = update {
                    visit_expr(update, declared_types);
                }
                visit_stmt(body, declared_types);
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                visit_expr(expr, declared_types);
                for case in cases {
                    visit_expr(&mut case.value, declared_types);
                    for stmt in &mut case.body {
                        visit_stmt(stmt, declared_types);
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        visit_stmt(stmt, declared_types);
                    }
                }
            }
            CStmt::Return(Some(expr)) => {
                visit_expr(expr, declared_types);
                // A returned literal is read as the return type, so an all-ones
                // word coming back from an `int` function is -1, not 0xffffffff.
                if let Some(ty) = declared_types.get(RETURN_TYPE_KEY) {
                    normalize_literal_for_declared_type(expr, ty);
                }
            }
            CStmt::Empty
            | CStmt::Return(None)
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_) => {}
        }
    }

    let mut declared_types = func
        .params
        .iter()
        .map(|param| (param.name.to_ascii_lowercase(), param.ty.clone()))
        .chain(
            func.locals
                .iter()
                .map(|local| (local.name.to_ascii_lowercase(), local.ty.clone())),
        )
        .collect::<HashMap<_, _>>();
    declared_types.insert(RETURN_TYPE_KEY.to_string(), func.ret_type.clone());
    for stmt in &mut func.body {
        visit_stmt(stmt, &declared_types);
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

fn prune_unreferenced_local_declarations(func: &mut CFunction) {
    let referenced = collect_stmt_var_names(&func.body)
        .into_iter()
        .map(|name| name.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    func.locals
        .retain(|local| referenced.contains(&local.name.to_ascii_lowercase()));
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
        // A plain name on the left of an assignment is written, not read, wherever
        // the assignment sits. The statement form already said so; a comma inside
        // a condition holds the same store and has to answer the same way.
        CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } if matches!(left.as_ref(), CExpr::Var(_)) => {
            collect_expr_local_reads(right, reads);
        }
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

#[cfg(test)]
fn infer_local_struct_field_accesses(
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

    let type_hints = std::collections::HashMap::new();
    let function_names = std::collections::HashMap::new();
    let strings = std::collections::HashMap::new();
    let symbols = std::collections::HashMap::new();
    let mut param_register_aliases = std::collections::HashMap::new();
    let mut arg_slot_map = std::collections::HashMap::new();

    for (idx, reg_name) in config.arg_regs.iter().enumerate() {
        let arg_name = format!("arg{idx}");
        for alias in register_alias_names(reg_name) {
            let lower = alias.to_ascii_lowercase();
            param_register_aliases.insert(lower.clone(), arg_name.clone());
            arg_slot_map.insert(lower, idx);
        }
    }

    let env = analysis::PassEnv {
        string_literals: crate::analysis::lower::no_string_literals(),
        ptr_size: config.ptr_size,
        sp_name: &config.sp_name,
        fp_name: &config.fp_name,
        ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
        #[cfg(test)]
        function_names: &function_names,
        #[cfg(test)]
        strings: &strings,
        #[cfg(test)]
        symbols: &symbols,
        callee_facts: analysis::empty_callee_facts(),
        callee_resolution: None,
        summary_view: None,
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
pub(crate) fn test_native_semantic_report(
    stage: r2sym::RefinementStage,
    granularity: r2sym::ArtifactGranularity,
    slice_class: r2sym::SliceClass,
    skipped_large_cfg: bool,
    residual_reasons: Vec<r2sym::ResidualReason>,
    regions: Vec<r2sym::SemanticRegion>,
) -> r2sym::SemanticArtifactReport {
    let regions = regions
        .into_iter()
        .map(|region| (region.key(), region))
        .collect();
    r2sym::SemanticArtifactReport {
        schema_version: r2sym::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
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
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::SSAFunction;
    use r2types::{
        ExternalField, ExternalRegisterParamSpec, ExternalStruct, ExternalTypeDb, FunctionFacts,
        FunctionParamSpec, FunctionSignatureSpec, FunctionTypeFacts, SignatureCertificate,
        SignatureCertificateSource,
    };
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    #[test]
    fn substitution_leaves_an_assignment_target_alone() {
        let mut stmt = CStmt::Expr(CExpr::assign(
            CExpr::Var("local_4".to_string()),
            CExpr::Var("local_4".to_string()),
        ));
        substitute_var_in_stmt(&mut stmt, "local_4", &CExpr::IntLit(1));
        assert_eq!(
            stmt,
            CStmt::Expr(CExpr::assign(
                CExpr::Var("local_4".to_string()),
                CExpr::IntLit(1),
            ))
        );
    }

    #[test]
    fn substitution_leaves_a_compound_assignment_target_alone() {
        let mut stmt = CStmt::Expr(CExpr::binary(
            BinaryOp::AddAssign,
            CExpr::Var("local_4".to_string()),
            CExpr::Var("local_4".to_string()),
        ));
        substitute_var_in_stmt(&mut stmt, "local_4", &CExpr::IntLit(1));
        assert_eq!(
            stmt,
            CStmt::Expr(CExpr::binary(
                BinaryOp::AddAssign,
                CExpr::Var("local_4".to_string()),
                CExpr::IntLit(1),
            ))
        );
    }

    #[test]
    fn semantic_memory_address_format_preserves_identity_kind() {
        assert_eq!(
            format_semantic_memory_address(&r2sym::SemanticMemoryAddress::exact(4)),
            "0x4"
        );
        assert_eq!(
            format_semantic_memory_address(
                &r2sym::SemanticMemoryAddress::bounded(4, 8).expect("bounded address")
            ),
            "bounded(0x4..0x8)"
        );
        assert_eq!(
            format_semantic_memory_address(
                &r2sym::SemanticMemoryAddress::affine(
                    vec![r2ssa::AffineAddressTerm {
                        value: r2ssa::ValueId(7),
                        coefficient: 40,
                    }],
                    4,
                )
                .expect("affine address")
            ),
            "affine(v7*40; offset=4)"
        );
    }

    fn empty_fold_context_for_linearization<'a>() -> FoldingContext<'a> {
        let arch = Box::leak(Box::new(FoldArchConfig {
            ptr_size: 8,
            sp_name: "rsp".to_string(),
            fp_name: "rbp".to_string(),
            ret_reg_name: "rax".to_string(),
            arg_regs: vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ],
            caller_saved_regs: HashSet::new(),
        }));
        FoldingContext::from_inputs(FoldInputs {
            display_names: crate::empty_display_names(),
            arch,
            function_names: Box::leak(Box::new(HashMap::new())),
            strings: Box::leak(Box::new(HashMap::new())),
            symbols: Box::leak(Box::new(HashMap::new())),
            function_facts: crate::fold::context::empty_function_facts(),
            #[cfg(test)]
            certified_rendering_required: false,
            stack_slots: Box::leak(Box::new(BTreeMap::new())),
            field_access_certificates: &[],
            external_stack_vars: Box::leak(Box::new(HashMap::new())),
            visible_bindings: Box::leak(Box::new(Vec::new())),
            external_type_db: Box::leak(Box::new(ExternalTypeDb::default())),
            param_register_aliases: Box::leak(Box::new(HashMap::new())),
            type_hints: Box::leak(Box::new(HashMap::new())),
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
        })
    }

    fn test_decompile_route(
        kind: r2types::DecompileRouteKind,
        reason: &str,
        fallback_comment: Option<String>,
    ) -> r2types::DecompileRouteFacts {
        r2types::DecompileRouteFacts {
            kind,
            reason: Some(reason.to_string()),
            fallback_comment,
            skip_runtime_type_inference: !matches!(kind, r2types::DecompileRouteKind::Standard),
            use_prepared_semantic_view: matches!(kind, r2types::DecompileRouteKind::Standard),
        }
    }

    fn test_summary_decompile_route(
        kind: r2types::DecompileRouteKind,
        reason: &str,
    ) -> r2types::DecompileRouteFacts {
        test_decompile_route(kind, reason, None)
    }

    fn render_semantic_worker_summary(
        func_name: &str,
        function_facts: &FunctionFacts,
        semantic_report: &r2sym::SemanticArtifactReport,
        route: &r2types::DecompileRouteFacts,
        config: DecompilerConfig,
    ) -> Option<String> {
        let function_facts = function_facts.clone().with_decompile_route(route.clone());
        consumer_summary::render_for_route(
            func_name,
            &function_facts,
            semantic_report,
            route,
            config.codegen,
        )
    }

    #[test]
    fn linearized_conditional_branch_without_predicate_is_residual_comment() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: Varnode::constant(0x2000, 8),
                    cond: Varnode::constant(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA function");
        func.get_block_mut(0x1000).expect("entry block").ops.clear();
        let block = func.get_block(0x1000).expect("entry block");
        let fold_ctx = empty_fold_context_for_linearization();

        let stmt = Decompiler::linearized_terminator_stmt(&func, &fold_ctx, block)
            .expect("linearized residual terminator");
        let CStmt::Comment(comment) = stmt else {
            panic!("unresolved conditional branch must not fabricate executable control: {stmt:?}");
        };
        assert!(comment.contains("conditional branch condition unresolved"));
        assert!(comment.contains("true_target=loc_2000"));
        assert!(comment.contains("false_target=loc_1004"));
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
        prepared_from_blocks(&[block], arch)
    }

    fn prepared_from_blocks(blocks: &[R2ILBlock], arch: &ArchSpec) -> r2ssa::SsaArtifact {
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-source-owned-fixture".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .expect("exact test source interface");
        r2ssa::SsaArtifact::for_decompile_with_interface(blocks, Some(arch), interface)
            .expect("prepared SSA should build")
            .with_name("stable_demo")
    }

    fn source_owned_type_analysis(
        prepared: impl Into<Arc<r2ssa::SsaArtifact>>,
    ) -> r2types::TypeWritebackAnalysis {
        let prepared = prepared.into();
        let request = r2types::TypeWritebackAnalysisRequest::new(
            Arc::clone(&prepared),
            r2types::ParsedExternalContext::default(),
        )
        .expect("test source assumptions");
        r2types::build_source_owned_type_writeback_analysis(request)
            .expect("source-owned test analysis")
    }

    fn source_owned_decompiler_input(
        prepared: impl Into<Arc<r2ssa::SsaArtifact>>,
        route: (r2types::DecompileRouteKind, &'static str, Option<String>),
    ) -> DecompilerInput {
        let (kind, reason, fallback_comment) = route;
        let source_owned_facts = source_owned_type_analysis(prepared)
            .finalize_for_decompile(r2types::DecompileFinalization {
                kind,
                reason: reason.to_string(),
                fallback_comment,
            })
            .expect("compatible source-owned decompile finalization");
        DecompilerInput::new(source_owned_facts)
    }

    fn test_arch_for_decompile() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RSI", 0x18, 8));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
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
            true,
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

    fn large_cfg_worker_report(
        stage: r2sym::RefinementStage,
        residual_reasons: Vec<r2sym::ResidualReason>,
        regions: Vec<r2sym::SemanticRegion>,
    ) -> r2sym::SemanticArtifactReport {
        test_native_semantic_report(
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
            params_known: true,
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
    fn generic_external_signature_still_owns_header_arity() {
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
            2,
            "certified signature arity must be the visible header authority even when generic"
        );
        assert!(
            params.iter().all(|param| param.name != "arg3"),
            "local recovery must not append surplus header params beyond FunctionFacts signature"
        );
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
    fn redundant_return_carrier_cast_yields_to_declared_c_type() {
        let mut func = CFunction::new("carrier", CType::Int(32)).with_body(vec![CStmt::if_stmt(
            CExpr::IntLit(1),
            CStmt::Return(Some(CExpr::cast(CType::Int(64), CExpr::var("result")))),
            None,
        )]);
        func.locals.push(ast::CLocal {
            ty: CType::Int(32),
            name: "result".to_string(),
            stack_offset: Some(-4),
        });

        normalize_redundant_return_carrier_casts(&mut func);

        assert!(matches!(
            &func.body[0],
            CStmt::If { then_body, .. }
                if matches!(then_body.as_ref(), CStmt::Return(Some(CExpr::Var(name))) if name == "result")
        ));
    }

    #[test]
    fn declared_assignment_type_normalizes_only_root_integer_literals() {
        let mut func = CFunction::new("typed_assignments", CType::Int(32)).with_body(vec![
            CStmt::Expr(CExpr::binary(
                BinaryOp::Assign,
                CExpr::var("signed_value"),
                CExpr::UIntLit(0xffff_ffff),
            )),
            CStmt::Expr(CExpr::binary(
                BinaryOp::Assign,
                CExpr::var("unsigned_value"),
                CExpr::UIntLit(0xffff_ffff),
            )),
            CStmt::Expr(CExpr::binary(
                BinaryOp::Assign,
                CExpr::var("signed_value"),
                CExpr::binary(BinaryOp::Add, CExpr::UIntLit(0xffff_ffff), CExpr::IntLit(1)),
            )),
        ]);
        func.locals = vec![
            ast::CLocal {
                ty: CType::Int(32),
                name: "signed_value".to_string(),
                stack_offset: Some(-4),
            },
            ast::CLocal {
                ty: CType::UInt(32),
                name: "unsigned_value".to_string(),
                stack_offset: Some(-8),
            },
        ];

        normalize_declared_assignment_literals(&mut func);

        let CStmt::Expr(CExpr::Binary { right, .. }) = &func.body[0] else {
            panic!("expected signed assignment");
        };
        assert_eq!(right.as_ref(), &CExpr::IntLit(-1));
        let CStmt::Expr(CExpr::Binary { right, .. }) = &func.body[1] else {
            panic!("expected unsigned assignment");
        };
        assert_eq!(right.as_ref(), &CExpr::UIntLit(0xffff_ffff));
        let CStmt::Expr(CExpr::Binary { right, .. }) = &func.body[2] else {
            panic!("expected compound rhs assignment");
        };
        assert!(matches!(
            right.as_ref(),
            CExpr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn unreferenced_local_declaration_is_removed_without_touching_live_locals() {
        let mut func = CFunction::new("locals", CType::Int(32))
            .with_body(vec![CStmt::Return(Some(CExpr::var("live")))]);
        func.locals = vec![
            ast::CLocal {
                ty: CType::Int(32),
                name: "dead_return_slot".to_string(),
                stack_offset: Some(-4),
            },
            ast::CLocal {
                ty: CType::Int(32),
                name: "live".to_string(),
                stack_offset: Some(-8),
            },
        ];

        prune_unreferenced_local_declarations(&mut func);

        assert_eq!(func.locals.len(), 1);
        assert_eq!(func.locals[0].name, "live");
    }

    #[test]
    fn decompile_input_enforces_configured_block_budget_before_route_work() {
        let arch = test_arch_for_decompile();
        let mut first = R2ILBlock::new(0x1000, 4);
        first.push(R2ILOp::Branch {
            target: Varnode::ram(0x2000, 8),
        });
        let mut second = R2ILBlock::new(0x2000, 4);
        second.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let prepared = prepared_from_blocks(&[first, second], &arch).with_name("budget_demo");
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::Standard,
                "block budget route",
                None,
            ),
        );
        let mut config = DecompilerConfig::x86_64();
        config.max_blocks = 1;
        let decompiler = Decompiler::new(config);

        let output = decompiler.decompile_input(&input);
        let function = decompiler.build_function_from_input(&input);

        assert_eq!(
            output,
            "/* r2dec budget: skipped decompilation for budget_demo (2 blocks > limit 1). */"
        );
        assert!(
            function.body.iter().any(
                |stmt| matches!(stmt, CStmt::Comment(text) if text.contains("2 blocks > limit 1"))
            ),
            "direct AST construction must enforce the same block budget: {function:?}"
        );
    }

    #[test]
    fn decompile_input_honors_engine_selected_route() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x10, 4),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Return {
                    target: Varnode::unique(0x10, 4),
                },
            ],
            &arch,
        );
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::FallbackComment,
                "engine refusal: tested route",
                Some("/* engine refusal: tested route */".to_string()),
            ),
        );

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert_eq!(
            output,
            "/* r2dec fallback: skipped decompilation for stable_demo (engine refusal: tested route) */"
        );
        assert!(
            !output.contains("/* engine refusal: tested route */"),
            "stored fallback payload must not be replayed verbatim"
        );
    }

    #[test]
    fn function_facts_route_is_the_decompile_route_authority() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::FallbackComment,
                "facts-owned route",
                Some("/* facts-owned refusal */".to_string()),
            ),
        );

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert_eq!(
            output,
            "/* r2dec fallback: skipped decompilation for stable_demo (facts-owned route) */"
        );
        assert!(
            !output.contains("/* facts-owned refusal */"),
            "stored fallback payload must not replace the canonical route reason"
        );
    }

    #[test]
    fn decompiler_input_retains_exact_source_owner_and_foreign_semantics_never_reach_it() {
        let arch = test_arch_for_decompile();
        let ops = vec![R2ILOp::Return {
            target: Varnode::constant(0, 8),
        }];
        let requested = Arc::new(prepared_from_ops(ops.clone(), &arch));
        let foreign = Arc::new(prepared_from_ops(ops, &arch));
        let artifact = r2sym::compile_semantic_artifact_default_with_scope(
            &z3::Context::thread_local(),
            &foreign,
            None,
        );
        let request = r2types::TypeWritebackAnalysisRequest::new(
            Arc::clone(&requested),
            r2types::ParsedExternalContext::default(),
        )
        .expect("source-owned request");
        assert_eq!(
            request
                .with_semantic_artifact(artifact)
                .expect_err("foreign semantics must be rejected before r2dec"),
            r2types::TypeWritebackAnalysisError::ForeignSemanticArtifact
        );
        let input = source_owned_decompiler_input(
            Arc::clone(&requested),
            (
                r2types::DecompileRouteKind::Standard,
                "otherwise renderable",
                None,
            ),
        );

        assert!(input.source_owned_facts().shares_source(&requested));
        assert!(std::ptr::eq(input.prepared_ssa(), requested.as_ref()));
    }

    #[test]
    fn context_projection_preserves_the_exact_sealed_report() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::Standard,
                "sealed projection",
                None,
            ),
        );

        let projected = input.context_projection();

        assert_eq!(projected.type_facts(), input.function_facts().type_facts());
        assert_eq!(
            projected.function_facts.decompile_route(),
            input.function_facts().decompile_route()
        );
    }

    #[test]
    fn foreign_interproc_summary_never_reaches_decompiler_input() {
        let mut arch = test_arch_for_decompile();
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"rebuilt-identical-owner".to_vec(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(0, storage(0x10))],
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .expect("exact source interface");
        let requested = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                std::slice::from_ref(&block),
                Some(&arch),
                interface.clone(),
            )
            .expect("requested prepared SSA"),
        );
        let foreign = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("foreign prepared SSA"),
        );
        let summary = r2ssa::solve_prepared_interproc_summary_set(
            Arc::clone(&foreign),
            &[r2ssa::PreparedInterprocFunctionInput {
                id: r2ssa::InterprocFunctionId(foreign.entry),
                name: None,
                prepared: &foreign,
            }],
            r2ssa::InterprocSolveConfig::default(),
        )
        .expect("foreign prepared summary");
        let request = r2types::TypeWritebackAnalysisRequest::new(
            requested,
            r2types::ParsedExternalContext::default(),
        )
        .expect("source-owned request");

        assert_eq!(
            request
                .with_interproc_summary(summary)
                .expect_err("foreign interprocedural evidence must be rejected before r2dec"),
            r2types::TypeWritebackAnalysisError::ForeignInterprocSummary
        );
    }

    #[test]
    fn advisory_summary_renderer_requires_summary_route_kind() {
        let semantic_artifact = large_cfg_worker_report(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        let non_summary_route = test_decompile_route(
            r2types::DecompileRouteKind::Standard,
            "wrong route kind for summary renderer",
            None,
        );
        assert!(
            render_semantic_worker_summary(
                "sym.worker",
                &function_facts,
                &semantic_artifact,
                &non_summary_route,
                DecompilerConfig::default(),
            )
            .is_none(),
            "advisory formatting must require an explicit summary route kind"
        );

        let summary_route = test_decompile_route(
            r2types::DecompileRouteKind::LinearWorker,
            "engine-selected summary route",
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.worker",
            &function_facts,
            &semantic_artifact,
            &summary_route,
            DecompilerConfig::default(),
        )
        .expect("facts-owned summary route should render");

        assert!(
            output.contains("render contract: residual summary only; no certified native C")
                && !output.contains("return 0;")
                && !output.contains("switch ("),
            "facts-owned summary route must remain comment-only, got:\n{output}"
        );
    }

    #[test]
    fn decompile_finalization_refuses_summary_routes_without_bound_semantics() {
        let arch = test_arch_for_decompile();
        for route in [
            (
                r2types::DecompileRouteKind::StructuredWorker,
                "engine-selected structured summary route",
            ),
            (
                r2types::DecompileRouteKind::LinearWorker,
                "engine-selected linear summary route",
            ),
            (
                r2types::DecompileRouteKind::SummaryIslands,
                "engine-selected island summary route",
            ),
        ] {
            let prepared = prepared_from_ops(
                vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
                &arch,
            );
            let error = source_owned_type_analysis(prepared)
                .finalize_for_decompile(r2types::DecompileFinalization {
                    kind: route.0,
                    reason: route.1.to_string(),
                    fallback_comment: None,
                })
                .expect_err("summary route without bound semantics must fail before r2dec");

            assert_eq!(
                error,
                r2types::TypeWritebackAnalysisError::IncompatibleDecompileRoute,
                "summary route without bound semantics must fail closed for {:?}",
                route.0,
            );
        }
    }

    #[test]
    fn raw_fallback_comments_regenerate_and_sanitize_hostile_text() {
        let assert_one_safe_comment = |output: &str| {
            assert!(
                output.starts_with("/* "),
                "expected one C comment: {output:?}"
            );
            assert!(
                output.ends_with(" */"),
                "expected closed C comment: {output:?}"
            );
            assert_eq!(
                output.matches("*/").count(),
                1,
                "comment payload must not close the comment early: {output:?}"
            );
            assert!(
                !output.contains('\r') && !output.contains('\n'),
                "comment payload must stay on one line: {output:?}"
            );
        };

        let block_comment = block_guard_fallback_comment("bad */\nint injected", 2, 1);
        assert_one_safe_comment(&block_comment);

        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        )
        .with_name("bad */\nint injected");
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::FallbackComment,
                "reason */\nreturn 7;",
                Some("*/ payload must be ignored\nint payload; /*".to_string()),
            ),
        );

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);
        assert_one_safe_comment(&output);
        assert!(
            output.contains("* /"),
            "hostile close must be neutralized: {output}"
        );
        assert!(
            !output.contains("payload must be ignored"),
            "stored fallback payload must not be replayed as raw output: {output}"
        );
    }

    #[test]
    fn build_function_from_input_fallback_route_residualizes_ast() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::FallbackComment,
                "engine-selected fallback route",
                Some("/* engine-selected fallback route */".to_string()),
            ),
        );

        let built = Decompiler::new(DecompilerConfig::x86_64()).build_function_from_input(&input);

        assert!(
            built
                .body
                .iter()
                .all(|stmt| matches!(stmt, CStmt::Comment(_))),
            "fallback route AST must be comment-only, got {:?}",
            built.body
        );
        assert!(
            !built
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "fallback route AST must not contain executable returns: {:?}",
            built.body
        );
    }

    #[test]
    fn report_only_standard_summary_semantics_residualizes() {
        let semantic_report = test_native_semantic_report(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let route = test_decompile_route(
            r2types::DecompileRouteKind::Standard,
            "bad standard route over summary-only semantics",
            None,
        );
        let reason = summary_only_semantics_standard_render_residual_reason(
            Some(&route),
            Some(&semantic_report),
        )
        .expect("summary-only report must reject Standard rendering");

        assert!(
            reason
                .contains("summary-only semantic artifact cannot authorize Standard executable C"),
            "summary-only semantics must reject Standard output, got: {reason}"
        );
    }

    /// A route the certification kernel did not claim used to lose its whole
    /// function: rendering returned a single comment and nothing else, so one
    /// unproven construct cost every proven one beside it. The structurer marks
    /// what it cannot prove, so the function is rendered either way.
    #[test]
    fn a_standard_route_renders_instead_of_refusing_the_whole_function() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::Standard,
                "standard route request",
                None,
            ),
        );

        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let built = decompiler.build_function_from_input(&input);
        assert!(
            built
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "standard route must render its return, got {:?}",
            built.body
        );
        assert!(
            !format!("{:?}", built.body).contains("Standard executable rendering is unavailable"),
            "standard route must not refuse the function wholesale: {:?}",
            built.body
        );

        let output = decompiler.decompile_input(&input);
        assert!(output.contains("return"), "{output}");
    }

    /// Nothing in this function is unproven, so it carries no proof note. A
    /// note on clean output would be noise readers learn to ignore.

    /// The marks the structurer leaves are counted wherever they sit, including
    /// inside a loop or a switch arm, and the function says how many it carries.
    #[test]
    fn unproven_constructs_are_counted_through_nested_bodies() {
        let mut func = CFunction::new("partly_proven".to_string(), CType::Unknown);
        func.body = vec![
            CStmt::comment("r2dec residual: unresolved branch condition at 0x1000"),
            CStmt::While {
                cond: CExpr::IntLit(1),
                body: Box::new(CStmt::Block(vec![CStmt::comment(
                    "r2dec residual: uncertified loop structure at 0x1010",
                )])),
            },
            CStmt::Return(Some(CExpr::IntLit(0))),
        ];
        assert_eq!(count_residual_markers(&func.body), 2);

        note_unproven_constructs(&mut func, None);
        let note = match func.body.first() {
            Some(CStmt::Comment(text)) => text.clone(),
            other => panic!("expected a leading proof note, got {other:?}"),
        };
        assert!(note.contains("r2dec proof:"), "{note}");
        assert!(note.contains("2 constructs are marked below"), "{note}");
        assert!(
            func.body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "the proven return survives beside the marks: {:?}",
            func.body
        );
    }

    /// An uncertified route says so even when the structurer marked nothing,
    /// because "nothing was marked" is not the same claim as "everything was
    /// proven". Without this the near-miss aggregate fixture rendered a bare
    /// `return` with no indication the kernel never claimed it.
    #[test]
    fn a_rendering_says_so_even_with_nothing_marked() {
        let mut func = CFunction::new("unclaimed".to_string(), CType::Unknown);
        func.body = vec![CStmt::Return(Some(CExpr::IntLit(0)))];
        note_unproven_constructs(&mut func, None);
        let note = match func.body.first() {
            Some(CStmt::Comment(text)) => text.clone(),
            other => panic!("expected a leading proof note, got {other:?}"),
        };
        assert!(note.contains("r2dec proof:"), "{note}");
        assert!(note.contains("no individual construct is marked"), "{note}");
    }

    /// Rendering nothing is not the same as proving the function does nothing.
    /// An empty body reads as "this function has no effects", so a render that
    /// produced no statements says that instead of implying it.
    #[test]
    fn a_body_that_rendered_nothing_says_so_rather_than_reading_as_empty() {
        let mut func = CFunction::new("nothing_rendered".to_string(), CType::Unknown);
        func.body = Vec::new();
        note_unproven_constructs(&mut func, None);
        let text = format!("{:?}", func.body);
        assert!(
            text.contains("r2dec proof: rendering produced no statements"),
            "{text}"
        );
        assert_eq!(func.body.len(), 1, "one statement says it, not two: {text}");
    }

    #[test]
    fn summary_storage_render_filter_hides_raw_carriers() {
        assert_eq!(summary_accumulator_label("TMP:2c280_2"), "accumulator");
        assert_eq!(summary_accumulator_label("const:1_0"), "accumulator");
        assert_eq!(summary_accumulator_label("ram:401000_0"), "accumulator");
        assert_eq!(summary_accumulator_label("unique:12_0"), "accumulator");
        assert_eq!(summary_accumulator_label("sha_state"), "sha_state");
    }

    #[test]
    fn normal_residual_comments_hide_debug_ids_and_raw_storage_tokens() {
        let comment = sanitize_comment_text(
            "uncertified expression value ValueId(125) from ObjectId(9) via eax_1 var_8h var_ch fake_stack_slot t6a80 tmp:2c280_2",
        );

        for raw in [
            "ValueId",
            "ObjectId",
            "eax_1",
            "var_8h",
            "var_ch",
            "fake_stack_slot",
            "t6a80",
            "tmp:2c280_2",
        ] {
            assert!(
                !comment.contains(raw),
                "normal comments must hide {raw}, got {comment}"
            );
        }
        assert!(
            comment.contains("uncertified expression value value")
                && comment.contains("object")
                && comment.contains("register")
                && comment.contains("stack slot")
                && comment.contains("temporary"),
            "sanitized comment should preserve actionable categories, got {comment}"
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
            string_literals: crate::analysis::lower::no_string_literals(),
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("x0"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            callee_facts: analysis::empty_callee_facts(),
            callee_resolution: None,
            summary_view: None,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                    space: r2il::SpaceId::Ram,
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
            string_literals: crate::analysis::lower::no_string_literals(),
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            callee_facts: analysis::empty_callee_facts(),
            callee_resolution: None,
            summary_view: None,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:4700", 5, 8),
                },
                SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 6, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: r2ssa::SSAVar::new("EAX", 2, 4),
                    space: r2il::SpaceId::Ram,
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
            string_literals: crate::analysis::lower::no_string_literals(),
            ptr_size: config.ptr_size,
            sp_name: &config.sp_name,
            fp_name: &config.fp_name,
            ret_reg_name: config.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            callee_facts: analysis::empty_callee_facts(),
            callee_resolution: None,
            summary_view: None,
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
    fn report_only_vm_summary_renders_semantic_comment() {
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
                    address: r2sym::SemanticMemoryAddress::exact(0),
                    size: 1,
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
                    address: r2sym::SemanticMemoryAddress::exact(4),
                    size: 1,
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
                    address: r2sym::SemanticMemoryAddress::exact(0),
                    size: 1,
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
                    address: r2sym::SemanticMemoryAddress::exact(4),
                    size: 1,
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
        let semantic_artifact = r2sym::SemanticArtifactReport {
            schema_version: r2sym::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
            stage: r2sym::RefinementStage::Residual,
            granularity: r2sym::ArtifactGranularity::SummaryOnly,
            execution: r2sym::ExecutionModel::Vm,
            body: r2sym::SemanticArtifactBody::Vm(Box::new(r2sym::VmArtifactBody {
                interpreter: None,
                step_summary: Some(vm_step),
                transfer_summary: None,
                native: None,
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
            },
        };
        let signature = signature_spec(
            Some(CType::Int(32)),
            vec![
                ("code", Some(CType::Pointer(Box::new(CType::UInt(8))))),
                ("len", Some(CType::Int(32))),
                ("arg3", Some(CType::Int(64))),
            ],
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            None,
        );

        let output = consumer_vm::render_vm_semantic_summary(
            "stable_demo",
            &function_facts,
            &semantic_artifact,
        )
        .expect("report-only VM summary");
        assert!(
            output.contains("r2dec semantic summary: vm_summary"),
            "expected VM semantic summary output, got:\n{output}"
        );
        assert!(
            !output.contains("residual_") && !output.contains("state_inputs=["),
            "normal VM rendering should not expose debug-scale internals, got:\n{output}"
        );
        assert!(
            output.contains("/* int32_t stable_demo(uint8_t* code, int32_t len) */")
                && !output.contains("arg3")
                && output.contains("/* switch (vm.sel) */")
                && output.contains("/* case 0x1: */")
                && output.contains("/* case 0x2: */")
                && output.contains("/* case 0x3: */")
                && output.contains("/* default: */")
                && output.contains("selector: vm.sel")
                && output.contains("handler 0x1004")
                && output.contains("labels=[0x1, 0x2]")
                && output.contains("transfer exits=1 guards=1 updates=2 reads=1 writes=1")
                && output.contains("selector updated")
                && output.contains(
                    "handler 0x1008: labels=[0x3] default=false blocks=[] */\n    /* no exact handler body recovered */"
                )
                && !output.contains("break;")
                && !output.contains("state = state + 1;")
                && !output.contains("read ram:0x2000"),
            "expected comment-only VM summary rendering, got:\n{output}"
        );
    }

    #[test]
    fn report_only_renderer_uses_bounded_summary_for_native_linear_worker() {
        let semantic_artifact = large_cfg_worker_report(
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
        let signature = signature_spec(Some(CType::Void), vec![("status", Some(CType::Int(32)))]);
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            None,
        );
        let route = test_decompile_route(
            r2types::DecompileRouteKind::LinearWorker,
            "guarded structuring unavailable",
            None,
        );
        let output = render_semantic_worker_summary(
            "stable_demo",
            &function_facts,
            &semantic_artifact,
            &route,
            DecompilerConfig::default(),
        )
        .expect("report-only worker summary");

        assert!(
            output.starts_with("/* summary-only route for stable_demo;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void stable_demo(void)"),
            "summary routes must not present even void C wrappers, got:\n{output}"
        );
        assert!(
            !output.contains("int32_t status"),
            "summary route leaked ABI-looking header params, got:\n{output}"
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
        let mut semantic_artifact = large_cfg_worker_report(
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.copy_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
    fn dense_worker_report_remains_comment_only_without_runtime_owner() {
        let mut semantic_artifact = test_native_semantic_report(
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
            None,
        );
        assert!(function_facts.decompile_plan().is_none());

        let output = render_semantic_worker_summary(
            "sym.dense_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
            DecompilerConfig::default(),
        )
        .expect("dense worker report should render as an advisory comment");

        assert!(output.contains("r2dec summary: semantic worker linear summary"));
        assert!(output.contains("native worker summaries: 8"));
        assert!(!output.contains("return summary_result;"));
    }

    #[test]
    fn semantic_worker_summary_handles_structured_worker_comment_only() {
        let semantic_artifact =
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
        let signature = signature_spec(Some(CType::Int(32)), Vec::new());
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.structured_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::StructuredWorker,
                "engine-selected structured summary route",
            ),
            DecompilerConfig::default(),
        )
        .expect("structured worker summary route should render");

        assert!(output.contains("semantic route: structured_worker_summary"));
        assert!(output.contains("render contract: summary facts only"));
        assert!(
            output.starts_with("/* summary-only route for sym.structured_worker;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void sym.structured_worker(void)"),
            "summary routes must not use non-authoritative C wrappers, got:\n{output}"
        );
        assert!(
            !output.contains("int sym.structured_worker")
                && !output.contains("return 0;")
                && !output.contains("if (")
                && !output.contains("switch ("),
            "structured summary route must not emit executable C, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_does_not_invent_header_params_for_extra_summary_operands() {
        let mut semantic_artifact = large_cfg_worker_report(
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.copy_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.starts_with("/* summary-only route for sym.copy_worker;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void sym.copy_worker(void)"),
            "summary routes must not present canonical signatures as native C headers, got:\n{output}"
        );
        assert!(!output.contains("(void* dst"));
        assert!(!output.contains(", void* src"));
        assert!(!output.contains("=arg2"));
        assert!(output.contains("summary_input2"));
    }

    #[test]
    fn semantic_worker_summary_keeps_unknown_length_transfer_as_residual_comment() {
        let mut semantic_artifact = large_cfg_worker_report(
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.copy_residual_len",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "or",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "named native-worker summary projection",
            ),
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");

        assert!(
            output.starts_with("/* summary-only route for or;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void or(void)"),
            "summary routes must not use non-authoritative C wrappers, got:\n{output}"
        );
        assert!(
            !output.lines().next().unwrap_or_default().contains("arg"),
            "summary-only headers must not expose register params, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_ignores_uncertified_merged_signature_header() {
        let mut semantic_artifact =
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "fcn.00004129",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "named native-worker summary projection",
            ),
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");
        let header = output.lines().next().unwrap_or_default();

        assert!(
            header.starts_with("/* summary-only route for fcn.00004129;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void fcn.00004129(void)"),
            "summary routes must not use uncertified merged signatures for headers, got:\n{output}"
        );
        assert!(
            !header.contains("summary_input") && !header.contains("int64_t"),
            "summary-only headers must not synthesize ABI-looking params, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_sanitizes_generic_header_register_params() {
        let mut semantic_artifact =
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "fcn.00004129",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "named native-worker summary projection",
            ),
            DecompilerConfig::default(),
        )
        .expect("worker summary should render");
        let header = output.lines().next().unwrap_or_default();

        assert!(
            header.starts_with("/* summary-only route for fcn.00004129;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void fcn.00004129(void)"),
            "summary routes must not use non-authoritative C wrappers, got:\n{output}"
        );
        assert!(
            !header.contains("summary_input")
                && !header.contains(" arg1")
                && !header.contains(" arg2"),
            "summary-only headers must not leak generic arg labels, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_renders_file_and_fts_worker_families() {
        let mut semantic_artifact =
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.copy_file_data",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "named file worker summary",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "main",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "named program orchestrator summary",
            ),
            DecompilerConfig::default(),
        )
        .expect("program orchestrator summary should render");

        assert!(
            output.starts_with("/* summary-only route for main;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void main(void)"),
            "summary-only role evidence must not become a native main signature, got:\n{output}"
        );
        assert!(!output.contains("int main(int argc"));
        assert!(output.contains("worker summary: program_orchestrator"));
        assert!(!output.contains("run_program_orchestrator("));
        assert!(output.contains("orchestrate program phases"));
    }

    #[test]
    fn semantic_worker_summary_renders_summary_backed_scan_loop() {
        let mut semantic_artifact = large_cfg_worker_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym.str_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = large_cfg_worker_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym.parse_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.parse_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.out_param_parse",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = large_cfg_worker_report(
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
            None,
        );
        let output = render_semantic_worker_summary(
            "fcn.000068f0",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
            DecompilerConfig::default(),
        )
        .expect("metadata summary should render");

        assert!(
            output.starts_with("/* summary-only route for fcn.000068f0;"),
            "summary routes must start with an explicit refusal comment, got:\n{output}"
        );
        assert!(
            !output.contains("void fcn.000068f0(void)"),
            "summary routes must not present typed params as native C headers, got:\n{output}"
        );
        assert!(!output.contains("uint64_t size"));
        assert!(!output.contains("return metadata_result;"));
        assert!(!output.contains("probe_file_metadata("));
        assert!(
            output.contains("metadata_probe") || output.contains("native summary"),
            "expected metadata summary evidence to remain visible, got:\n{output}"
        );
    }

    #[test]
    fn semantic_worker_summary_reports_length_bounded_hash_fold_without_fake_code() {
        let mut semantic_artifact = large_cfg_worker_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym._md5_process_block",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = large_cfg_worker_report(
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
            None,
        );
        let output = render_semantic_worker_summary(
            "count_bytes",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "named native-worker summary projection",
            ),
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
        let mut semantic_artifact = large_cfg_worker_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym.rpl_mbrtowc",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = large_cfg_worker_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym.diagnose",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = large_cfg_worker_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym.printf_fetchargs",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Residual, Vec::new(), Vec::new());
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "sym.scan",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "large native worker summarized as typed islands",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
        let function_facts = FunctionFacts::new(type_facts, None);
        let output = render_semantic_worker_summary(
            "byte_hash_worker",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "large native worker summarized as typed islands",
            ),
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
            large_cfg_worker_report(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
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
        let function_facts = FunctionFacts::new(type_facts, None);
        let output = render_semantic_worker_summary(
            "table_walk",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "large native worker summarized as typed islands",
            ),
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
        let mut semantic_artifact = test_native_semantic_report(
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
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);
        let output = render_semantic_worker_summary(
            "readlinebuffer_delim",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = test_native_semantic_report(
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
            linkage: r2ssa::FunctionSemanticLinkage::Unknown,
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
            None,
        );
        let output = render_semantic_worker_summary(
            "sym.name_ranked_table",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
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
        let mut semantic_artifact = test_native_semantic_report(
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
            None,
        );
        let output = render_semantic_worker_summary(
            "dbg.print_current_files",
            &function_facts,
            &semantic_artifact,
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::SummaryIslands,
                "named native-worker summary projection",
            ),
            DecompilerConfig::default(),
        )
        .expect("weak format summary should render as bounded summary comments");

        assert!(output.starts_with("/* summary-only route for dbg.print_current_files;"));
        assert!(!output.contains("void dbg.print_current_files(void)"));
        assert!(output.contains("worker summary: format_render"));
        assert!(output.contains("summary_roles=0"));
        assert!(!output.contains("render_formatted_output(summary_input0);"));
        assert!(!output.contains("arg0"));
    }

    #[test]
    fn semantic_summary_return_guard_fills_nonvoid_body_without_return() {
        let mut semantic_artifact = test_native_semantic_report(
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
            None,
        );
        let mut func = CFunction {
            name: "dbg.gettext_quote".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            params_known: true,
            locals: Vec::new(),
            body: vec![CStmt::Expr(CExpr::call(
                CExpr::var("sym.rpl_mbrtoc32"),
                Vec::new(),
            ))],
        };

        append_semantic_summary_return_to_function_if_needed(
            &mut func,
            &function_facts,
            Some(&semantic_artifact),
        );

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
    fn raw_summary_report_does_not_invent_executable_return() {
        let semantic_artifact = test_native_semantic_report(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::WholeFunction,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::ptr(CType::Int(8))),
                    vec![("buf", Some(CType::ptr(CType::Int(8))))],
                )),
                ..FunctionTypeFacts::default()
            },
            None,
        );
        let mut func = CFunction {
            name: "dbg.return_arg_summary".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            params_known: true,
            locals: Vec::new(),
            body: vec![CStmt::Expr(CExpr::call(
                CExpr::var("summary_worker"),
                Vec::new(),
            ))],
        };

        append_semantic_summary_return_to_function_if_needed(
            &mut func,
            &function_facts,
            Some(&semantic_artifact),
        );

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
        let semantic_artifact = test_native_semantic_report(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::WholeFunction,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(signature_spec(
                    Some(CType::ptr(CType::Int(8))),
                    vec![("n", Some(CType::Typedef("size_t".to_string())))],
                )),
                ..FunctionTypeFacts::default()
            },
            None,
        );
        let mut func = CFunction {
            name: "dbg.alloc_wrapper2".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            params_known: true,
            locals: Vec::new(),
            body: vec![CStmt::Expr(CExpr::call(
                CExpr::var("sym.imp.malloc"),
                vec![CExpr::var("n")],
            ))],
        };

        append_semantic_summary_return_comment_to_function_if_needed(
            &mut func,
            &function_facts,
            Some(&semantic_artifact),
        );

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
    fn autogenerated_name_detection_accepts_underscore_hex_labels() {
        assert!(is_autogenerated_function_name("_140010138"));
        assert!(is_autogenerated_function_name("_401000"));
        assert!(!is_autogenerated_function_name("_named_worker"));
    }
}
