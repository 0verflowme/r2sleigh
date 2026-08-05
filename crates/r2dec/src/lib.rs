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
//! let input: DecompilerInput = /* built by r2engine from prepared FunctionFacts */;
//! let config = DecompilerConfig::default();
//! let decompiler = Decompiler::new(config);
//! let c_code = decompiler.decompile_input(&input);
//! println!("{}", c_code);
//! ```

pub(crate) mod address;
pub(crate) mod analysis;
pub mod ast;
pub(crate) mod codegen;
pub(crate) mod consumer_fallback;
#[cfg(test)]
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
pub use codegen::CodeGenConfig;
pub use fold::lower_ssa_ops_to_stmts;
pub use highlight::highlight_c_ansi;
pub use region::{Region, RegionAnalyzer};
pub use structure::{ControlFlowStructurer, ControlRenderProof, ControlRenderProofKind};
pub use variable::VariableRecovery;

use crate::codegen::CodeGenerator;
use crate::fold::FoldingContext;
use crate::fold::context::{EffectRenderProof, EffectRenderProofKind, FoldArchConfig, FoldInputs};
use r2ssa::SSAFunction;
use r2ssa::SSAOp;
use r2ssa::cfg::BlockTerminator;
use r2types::{
    CTypeLike, DecompileRouteFacts, DecompileRouteKind, ExternalRegisterParamSpec,
    ExternalStackSlotRole, FunctionFacts, FunctionSignatureSpec, FunctionTypeFacts,
    ParamSlotResolver, StackSlotKey, TypeInference, TypeOracle, VisibleBinding, VisibleBindingKind,
};
#[cfg(test)]
use r2types::{ExternalTypeDb, FunctionType};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

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

pub fn block_guard_fallback_comment(func_name: &str, blocks: usize, max_blocks: usize) -> String {
    planner::block_guard_fallback_comment(func_name, blocks, max_blocks)
}

pub fn artifact_guard_fallback_comment(func_name: &str, reason: &str) -> String {
    planner::artifact_guard_fallback_comment(func_name, reason)
}

pub fn render_vm_semantic_summary(
    func_name: &str,
    function_facts: &FunctionFacts,
) -> Option<String> {
    let route = function_facts.decompile_route()?;
    if route.kind != r2types::DecompileRouteKind::VmSummary
        || route.render_permission.kind != r2sym::RenderPermissionKind::SummaryComment
    {
        return None;
    }
    consumer_vm::render_vm_semantic_summary(
        func_name,
        function_facts.type_facts(),
        function_facts.semantic_artifact()?,
    )
}

pub fn render_semantic_worker_summary(
    func_name: &str,
    function_facts: &FunctionFacts,
    config: DecompilerConfig,
) -> Option<String> {
    let route = function_facts.decompile_route()?;
    if route.render_permission.kind != r2sym::RenderPermissionKind::SummaryComment {
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
    semantic_artifact: &r2sym::SemanticArtifact,
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
) {
    append_semantic_summary_return_comment_to_function_if_needed(func, function_facts);
}

fn append_semantic_summary_return_comment_to_function_if_needed(
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
    control_facts: Option<&r2types::FunctionControlFacts>,
    cfg_summary: &r2ssa::CFGRiskSummary,
    func: &CFunction,
) -> Option<String> {
    certifying_render_residual_reason_with_proofs(prepared, control_facts, cfg_summary, func, None)
}

fn certifying_render_residual_reason_with_proofs(
    prepared: Option<&r2ssa::SsaArtifact>,
    control_facts: Option<&r2types::FunctionControlFacts>,
    cfg_summary: &r2ssa::CFGRiskSummary,
    func: &CFunction,
    render_proofs: Option<&[ControlRenderProof]>,
) -> Option<String> {
    let (rendered, render_proof_failures) =
        function_control_render_nodes_with_proofs(func, render_proofs);
    let inventory = prepared
        .is_some()
        .then(|| control_certificate_inventory(control_facts));

    let mut reasons = Vec::new();
    if let Some(reason) = structured_control_residual_reason_for_nodes(
        inventory.as_ref(),
        cfg_summary,
        &rendered,
        &render_proof_failures,
    ) {
        reasons.push(reason);
    }
    if render_proofs.is_some()
        && let Some(reason) = certified_control_transfer_residual_reason(func)
    {
        reasons.push(reason);
    }

    if reasons.is_empty() {
        None
    } else {
        Some(reasons.join("; "))
    }
}

fn certified_control_transfer_residual_reason(func: &CFunction) -> Option<String> {
    for (index, stmt) in func.body.iter().enumerate() {
        if let Some(reason) =
            certified_control_transfer_stmt_residual_reason(stmt, RenderNodeId::root_child(index))
        {
            return Some(reason);
        }
    }
    None
}

fn certified_control_transfer_stmt_residual_reason(
    stmt: &CStmt,
    id: RenderNodeId,
) -> Option<String> {
    match stmt {
        CStmt::Break => Some(format!(
            "unproved control transfer break at {id}; exact case/loop exit facts required"
        )),
        CStmt::Continue => Some(format!(
            "unproved control transfer continue at {id}; exact loop iteration facts required"
        )),
        CStmt::Goto(label) => Some(format!(
            "unproved control transfer goto {label} at {id}; exact irreducible-edge facts required"
        )),
        CStmt::Block(stmts) => certified_control_transfer_stmts_residual_reason(stmts, id),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            certified_control_transfer_stmt_residual_reason(then_body, id.child(0)).or_else(|| {
                else_body.as_deref().and_then(|stmt| {
                    certified_control_transfer_stmt_residual_reason(stmt, id.child(1))
                })
            })
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            certified_control_transfer_stmt_residual_reason(body, id.child(0))
        }
        CStmt::For { init, body, .. } => init
            .as_deref()
            .and_then(|stmt| certified_control_transfer_stmt_residual_reason(stmt, id.child(0)))
            .or_else(|| certified_control_transfer_stmt_residual_reason(body, id.child(1))),
        CStmt::Switch { cases, default, .. } => {
            for (case_index, case) in cases.iter().enumerate() {
                let case_id = id.child(case_index);
                if let Some(reason) =
                    certified_control_transfer_stmts_residual_reason(&case.body, case_id.clone())
                {
                    return Some(reason);
                }
                if !certified_stmt_list_is_terminal(&case.body) {
                    return Some(format!(
                        "unproved switch case fallthrough at {case_id}; exact case-exit/fallthrough facts required"
                    ));
                }
            }
            if let Some(default_body) = default {
                let default_id = id.child(cases.len());
                if let Some(reason) = certified_control_transfer_stmts_residual_reason(
                    default_body,
                    default_id.clone(),
                ) {
                    return Some(reason);
                }
                if !certified_stmt_list_is_terminal(default_body) {
                    return Some(format!(
                        "unproved switch default fallthrough at {default_id}; exact case-exit/fallthrough facts required"
                    ));
                }
            }
            None
        }
        CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Empty
        | CStmt::Label(_)
        | CStmt::Comment(_) => None,
    }
}

fn certified_control_transfer_stmts_residual_reason(
    stmts: &[CStmt],
    id: RenderNodeId,
) -> Option<String> {
    for (index, stmt) in stmts.iter().enumerate() {
        if let Some(reason) = certified_control_transfer_stmt_residual_reason(stmt, id.child(index))
        {
            return Some(reason);
        }
    }
    None
}

fn certified_stmt_list_is_terminal(stmts: &[CStmt]) -> bool {
    stmts.last().is_some_and(certified_stmt_is_terminal)
}

fn certified_stmt_is_terminal(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Return(_) => true,
        CStmt::Block(stmts) => certified_stmt_list_is_terminal(stmts),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            certified_stmt_is_terminal(then_body)
                && else_body.as_deref().is_some_and(certified_stmt_is_terminal)
        }
        _ => false,
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ControlRenderCounts {
    branches: usize,
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
    Branch,
    Loop,
    Switch,
}

impl ControlRenderNodeKind {
    fn label(self) -> &'static str {
        match self {
            Self::Branch => "branch",
            Self::Loop => "loop",
            Self::Switch => "switch",
        }
    }

    fn matches_proof_kind(self, proof_kind: ControlRenderProofKind) -> bool {
        matches!(
            (self, proof_kind),
            (Self::Branch, ControlRenderProofKind::Branch)
                | (Self::Loop, ControlRenderProofKind::Loop)
                | (Self::Switch, ControlRenderProofKind::Switch)
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ControlRenderNode {
    id: RenderNodeId,
    kind: ControlRenderNodeKind,
    proof_anchor: Option<u64>,
    proof_branch_condition: Option<r2ssa::PredicateId>,
    proof_branch_condition_value: Option<r2ssa::ValueId>,
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
struct BranchCertificateSummary {
    anchor: u64,
    proof_node: String,
    condition: r2ssa::PredicateId,
    condition_value: r2ssa::ValueId,
    true_target: u64,
    false_target: u64,
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
    branches: Vec<BranchCertificateSummary>,
    loops: Vec<LoopCertificateSummary>,
    switches: Vec<SwitchCertificateSummary>,
}

impl ControlCertificateInventory {
    fn counts(&self) -> ControlRenderCounts {
        ControlRenderCounts {
            branches: self.branches.len(),
            loops: self.loops.len(),
            switches: self.switches.len(),
        }
    }
}

fn control_certificate_inventory(
    control_facts: Option<&r2types::FunctionControlFacts>,
) -> ControlCertificateInventory {
    ControlCertificateInventory {
        branches: control_facts
            .into_iter()
            .flat_map(|facts| facts.branch_predicates.values())
            .map(|fact| BranchCertificateSummary {
                anchor: fact.block_addr,
                proof_node: format!("FunctionFacts.branch_predicate:{:?}", fact.id),
                condition: fact.id,
                condition_value: fact.condition,
                true_target: fact.true_target,
                false_target: fact.false_target,
            })
            .collect(),
        loops: control_facts
            .into_iter()
            .flat_map(|facts| facts.loops.values())
            .map(|fact| LoopCertificateSummary {
                anchor: fact.header,
                proof_node: fact.proof_node.clone(),
                condition: fact.condition,
                condition_value: fact.condition_value,
                body: sorted_u64s(&fact.body),
                latches: sorted_u64s(&fact.latches),
                exits: sorted_u64s(&fact.exits),
                has_condition: fact.condition.is_some(),
            })
            .collect(),
        switches: control_facts
            .into_iter()
            .flat_map(|facts| facts.switches.values())
            .map(|fact| SwitchCertificateSummary {
                anchor: fact.block_addr,
                proof_node: fact.proof_node.clone(),
                selector: fact.selector,
                case_targets: sorted_switch_cases(&fact.cases),
                default_target: fact.default,
                cases: fact.cases.len(),
                case_values: sorted_switch_case_values(&fact.cases),
                has_default: fact.default.is_some(),
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
    let rendered_has_control = rendered.branches > 0 || rendered.loops > 0 || rendered.switches > 0;

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
    if rendered.branches > certified.branches {
        reasons.push(format!(
            "rendered {} branch construct(s) with only {} FunctionFacts branch predicate(s)",
            rendered.branches, certified.branches
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
            ControlRenderNodeKind::Branch => counts.branches += 1,
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
    let branches_by_anchor = inventory
        .branches
        .iter()
        .map(|cert| (cert.anchor, cert))
        .collect::<std::collections::BTreeMap<_, _>>();

    for node in rendered {
        match node.kind {
            ControlRenderNodeKind::Branch => {
                let Some(anchor) = node.proof_anchor else {
                    reasons.push(format!(
                        "rendered branch node {} lacks FunctionFacts branch predicate proof identity",
                        node.id
                    ));
                    continue;
                };
                match branches_by_anchor.get(&anchor).copied() {
                    Some(cert) => {
                        if node.proof_branch_condition != Some(cert.condition) {
                            reasons.push(format!(
                                "rendered branch node {} predicate proof {:?} disagrees with {} at 0x{:x} predicate {:?}",
                                node.id,
                                node.proof_branch_condition,
                                cert.proof_node,
                                cert.anchor,
                                cert.condition
                            ));
                        }
                        if node.proof_branch_condition_value != Some(cert.condition_value) {
                            reasons.push(format!(
                                "rendered branch node {} condition value proof {:?} disagrees with {} at 0x{:x} condition value {:?}",
                                node.id,
                                node.proof_branch_condition_value,
                                cert.proof_node,
                                cert.anchor,
                                cert.condition_value
                            ));
                        }
                    }
                    None => reasons.push(format!(
                        "rendered branch node {} proof anchor 0x{:x} has no matching FunctionFacts branch predicate",
                        node.id, anchor
                    )),
                }
            }
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
                // Condition/condition_value use different ID spaces (r2il vs SSA).
                // The certified_loop_render_proof gate already validated the loop
                // against the canonical certificate before recording the proof.
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
        node.proof_branch_condition = proof.branch_condition;
        node.proof_branch_condition_value = proof.branch_condition_value;
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
                proof_branch_condition: None,
                proof_branch_condition_value: None,
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
                proof_branch_condition: None,
                proof_branch_condition_value: None,
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
            nodes.push(ControlRenderNode {
                id: id.clone(),
                kind: ControlRenderNodeKind::Branch,
                proof_anchor: None,
                proof_branch_condition: None,
                proof_branch_condition_value: None,
                proof_loop_condition: None,
                proof_loop_condition_value: None,
                proof_loop_body_blocks: Vec::new(),
                proof_loop_latches: Vec::new(),
                proof_loop_exits: Vec::new(),
                proof_switch_selector: None,
                proof_switch_cases: Vec::new(),
                proof_switch_default: None,
                loop_has_condition: false,
                switch_cases: 0,
                switch_case_values: Vec::new(),
                switch_has_placeholder_selector: false,
                switch_has_nonliteral_case: false,
                switch_has_default: false,
            });
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
                proof_branch_condition: None,
                proof_branch_condition_value: None,
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

fn residual_function_for_render_boundary(func_name: &str, reason: &str) -> CFunction {
    let mut func = CFunction::new(func_name.to_string(), CType::Unknown);
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

fn route_fallback_comment(route: &DecompileRouteFacts) -> Option<&str> {
    (route.kind == DecompileRouteKind::FallbackComment)
        .then(|| {
            route
                .fallback_comment
                .as_deref()
                .or(route.reason.as_deref())
        })
        .flatten()
}

fn route_is_standard(route: &DecompileRouteFacts) -> bool {
    route.kind == DecompileRouteKind::Standard
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
            "r2dec residual: engine render permission residual: {}",
            permission.reason
        )),
        r2sym::RenderPermissionKind::Refuse => Some(format!(
            "r2dec residual: engine render permission refusal: {}",
            permission.reason
        )),
        r2sym::RenderPermissionKind::SummaryComment => Some(format!(
            "r2dec residual: engine render permission summary-only: {}",
            permission.reason
        )),
        r2sym::RenderPermissionKind::CertifiedC => {
            (permission.owner != r2sym::ProofOwner::R2engine).then(|| {
                format!(
                    "r2dec residual: CertifiedC render permission from non-engine proof owner {:?}: {}",
                    permission.owner, permission.reason
                )
            })
        }
    }
}

fn render_permission_allows_executable_c(permission: Option<&r2sym::RenderPermission>) -> bool {
    permission.is_some_and(|permission| {
        permission.kind == r2sym::RenderPermissionKind::CertifiedC
            && permission.owner == r2sym::ProofOwner::R2engine
    })
}

fn summary_only_semantics_standard_render_residual_reason(
    function_facts: &FunctionFacts,
) -> Option<String> {
    let route = function_facts.decompile_route()?;
    if route.kind != r2types::DecompileRouteKind::Standard {
        return None;
    }
    if route.render_permission.kind != r2sym::RenderPermissionKind::CertifiedC {
        return None;
    }
    let semantics = function_facts.semantic_artifact()?;
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

#[derive(Debug, Clone, Default)]
struct CertifiedOutputCounts {
    calls: usize,
    expression_roots: usize,
    returns_with_value: usize,
    memory_like_accesses: usize,
    field_accesses: usize,
    array_accesses: usize,
    raw_address_call_args: usize,
    raw_pointer_arithmetic_derefs: usize,
    residual_comments: usize,
    field_members: Vec<String>,
    return_field_members: Vec<String>,
    call_nodes: Vec<RenderNodeId>,
    expression_nodes: Vec<RenderNodeId>,
    return_nodes: Vec<RenderNodeId>,
    memory_nodes: Vec<RenderNodeId>,
    field_nodes: Vec<(RenderNodeId, String)>,
    array_nodes: Vec<RenderNodeId>,
    raw_address_call_arg_nodes: Vec<RenderNodeId>,
    raw_pointer_arithmetic_nodes: Vec<RenderNodeId>,
    residual_comment_nodes: Vec<RenderNodeId>,
    residual_comment_texts: Vec<String>,
}

#[derive(Debug, Clone, Default)]
struct CertifiedEffectProofCounts {
    calls: usize,
    expressions: usize,
    returns: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct CertifiedSemanticLedger {
    ids: BTreeMap<r2ssa::SemanticId, usize>,
    unresolved: usize,
}

impl CertifiedSemanticLedger {
    fn from_effect_proofs(function_facts: &FunctionFacts, proofs: &[EffectRenderProof]) -> Self {
        let mut ledger = Self::default();
        for proof in proofs {
            let id = match proof.kind {
                EffectRenderProofKind::Call => function_facts
                    .callsites()
                    .and_then(|facts| {
                        facts.arguments_for_site(r2types::CallsiteKey {
                            block_addr: proof.block_addr,
                            op_index: proof.op_idx,
                        })
                    })
                    .map(|fact| r2ssa::SemanticId::call(fact.call_site_id)),
                EffectRenderProofKind::Expression => proof.value.and_then(|value| {
                    function_facts
                        .render_facts()
                        .certified_expr_for_value(value)
                        .map(|cert| cert.id)
                }),
                EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite => {
                    proof.address.and_then(|address| {
                        function_facts.render_facts().memory_effect_id_for_op(
                            proof.block_addr,
                            proof.op_idx,
                            proof.kind == EffectRenderProofKind::MemoryWrite,
                            address,
                            proof.value,
                        )
                    })
                }
                EffectRenderProofKind::Return => function_facts
                    .render_facts()
                    .return_effect_id_for_op(proof.block_addr, proof.op_idx),
            };
            if let Some(id) = id {
                *ledger.ids.entry(id).or_default() += 1;
            } else {
                ledger.unresolved += 1;
            }
        }
        ledger
    }
}

fn certified_effect_proof_counts(
    effect_render_proofs: &[EffectRenderProof],
) -> CertifiedEffectProofCounts {
    let mut calls = 0usize;
    let mut expressions = 0usize;
    let mut returns = 0;

    for proof in effect_render_proofs {
        match proof.kind {
            EffectRenderProofKind::Call => {
                calls += 1;
            }
            EffectRenderProofKind::Expression => {
                expressions += 1;
            }
            EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite => {}
            EffectRenderProofKind::Return => {
                returns += 1;
            }
        }
    }

    CertifiedEffectProofCounts {
        calls,
        expressions,
        returns,
    }
}

fn certified_memory_effects_requiring_ast_access(
    render_facts: &r2types::FunctionRenderFacts,
    effect_render_proofs: &[EffectRenderProof],
) -> usize {
    let mut accesses = BTreeSet::new();
    for proof in effect_render_proofs.iter().filter(|proof| {
        matches!(
            proof.kind,
            EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite
        )
    }) {
        let is_write = proof.kind == EffectRenderProofKind::MemoryWrite;
        let Some(memory) =
            render_facts.memory_access_for_op(proof.block_addr, proof.op_idx, is_write)
        else {
            continue;
        };
        if proof.address != Some(memory.address) || proof.value != memory.value {
            continue;
        }
        let has_structured_access = render_facts
            .array_accesses_by_op
            .get(&(proof.block_addr, proof.op_idx, is_write))
            .into_iter()
            .flatten()
            .any(|fact| fact.access == memory.access)
            || render_facts
                .member_accesses_by_op
                .get(&(proof.block_addr, proof.op_idx, is_write))
                .into_iter()
                .flatten()
                .any(|fact| fact.access == memory.access);
        if has_structured_access || render_facts.stack_slot(memory.object).is_none() {
            accesses.insert((proof.block_addr, proof.op_idx, is_write, memory.access));
        }
    }
    accesses.len()
}

fn call_render_facts_from_effect_proofs(
    effect_render_proofs: &[EffectRenderProof],
) -> r2types::FunctionCallRenderFacts {
    let by_callsite = effect_render_proofs
        .iter()
        .filter(|proof| proof.kind == EffectRenderProofKind::Call)
        .map(|proof| {
            let callsite = r2types::CallsiteKey {
                block_addr: proof.block_addr,
                op_index: proof.op_idx,
            };
            (
                callsite,
                r2types::CallsiteRenderFact {
                    callsite,
                    target: proof.target,
                    disposition: proof
                        .call_disposition
                        .unwrap_or(r2types::CallsiteRenderDisposition::NestedExpression),
                    proof_values: proof.values.clone(),
                    residual_reason: None,
                },
            )
        })
        .collect();
    r2types::FunctionCallRenderFacts { by_callsite }
}

fn certified_callsite_expected_argument_values(
    function_facts: &FunctionFacts,
    cert: &r2types::CallsiteArgumentFacts,
) -> Vec<r2ssa::ValueId> {
    let mut expected = cert
        .argument_values
        .iter()
        .map(|arg| arg.value)
        .collect::<Vec<_>>();
    if let Some(max_arity) = function_facts
        .callee_resolution()
        .and_then(|resolution| resolution.identity_for_callsite(cert.callsite))
        .and_then(r2types::CalleeIdentity::non_variadic_known_arity)
    {
        expected.truncate(max_arity);
    }
    expected
}

fn return_value_has_certified_call_result_effect(
    call_result_facts: Option<&r2types::FunctionCallResultFacts>,
    effect_render_proofs: &[EffectRenderProof],
    value: r2ssa::ValueId,
) -> bool {
    let Some(call_result) = call_result_facts.and_then(|facts| facts.result_for_value(value))
    else {
        return false;
    };
    effect_render_proofs.iter().any(|proof| {
        proof.kind == EffectRenderProofKind::Call
            && proof.block_addr == call_result.callsite.block_addr
            && proof.op_idx == call_result.callsite.op_index
    })
}

fn certified_stack_local_identity_is_exact(
    function_facts: &FunctionFacts,
    name: &str,
    offset: i64,
) -> bool {
    function_facts
        .authorized_stack_slot_owner_render_by_offset(offset, name)
        .or_else(|| function_facts.authorized_stack_slot_owner_render_by_offset(-offset, name))
        .is_some()
        || function_facts.render().is_some_and(|render| {
            render.stack_slots().any(|(object, _, slot_offset, _)| {
                (slot_offset == offset || slot_offset == -offset)
                    && function_facts
                        .authorized_recovered_stack_slot_owner_render(object, slot_offset, name)
                        .is_some()
            })
        })
}

fn certified_recovered_stack_local_is_exact(
    function_facts: &FunctionFacts,
    emitted_vars: &HashSet<String>,
    body_visible_names: &HashSet<String>,
    name: &str,
    stack_offset: Option<i64>,
) -> bool {
    let Some(offset) = stack_offset else {
        return false;
    };
    (emitted_vars.contains(name) || body_visible_names.contains(name))
        && certified_stack_local_identity_is_exact(function_facts, name, offset)
}

fn certified_stack_local_type_matches(
    type_facts: &FunctionTypeFacts,
    name: &str,
    offset: i64,
    rendered_ty: &CType,
) -> bool {
    typed_stack_local_type_for_name_offset(type_facts, name, offset)
        .is_some_and(|certified_ty| certified_ty == *rendered_ty)
}

fn certified_loop_carrier_local_is_exact(
    function_facts: &FunctionFacts,
    local: &ast::CLocal,
) -> bool {
    if local.stack_offset.is_some() {
        return false;
    }
    function_facts.render().is_some_and(|render| {
        render.loop_carriers().any(|entity| {
            let r2types::CertifiedEntity::LoopCarrier {
                id, phi, width, ty, ..
            } = entity
            else {
                return false;
            };
            let rendered_ty = ty
                .as_ref()
                .map(type_like_to_ctype)
                .or_else(|| (*width > 0).then(|| CType::Int(width.saturating_mul(8))));
            *id == r2ssa::SemanticId::loop_carrier(*phi)
                && local.name == certified_loop_carrier_name(*phi)
                && rendered_ty.is_some_and(|ty| ty == local.ty)
        })
    })
}

fn certified_memory_result_local_is_exact(
    function_facts: &FunctionFacts,
    local: &ast::CLocal,
) -> bool {
    if local.stack_offset.is_some() {
        return false;
    }
    function_facts.render().is_some_and(|render| {
        render.certified_effects.values().any(|effect| {
            let r2types::CertifiedEffect::Memory { id, fact } = effect else {
                return false;
            };
            *id == r2ssa::SemanticId::memory_access(fact.access)
                && !fact.is_write
                && fact.value.is_some()
                && fact.width > 0
                && fact.materialize_result
                && local.name == certified_memory_result_name(fact.access)
                && local.ty == CType::UInt(fact.width.saturating_mul(8))
        })
    })
}

fn typed_stack_local_type_for_name_offset(
    type_facts: &FunctionTypeFacts,
    name: &str,
    offset: i64,
) -> Option<CType> {
    let normalized = name.trim();
    if normalized.is_empty() {
        return None;
    }
    let renderable_type = |ty: &CTypeLike| {
        let ty = type_like_to_ctype(ty);
        (!matches!(ty, CType::Unknown | CType::Void)).then_some(ty)
    };

    type_facts
        .visible_bindings
        .iter()
        .find(|binding| {
            matches!(
                binding.kind,
                VisibleBindingKind::Param
                    | VisibleBindingKind::Local
                    | VisibleBindingKind::StackObject
            ) && binding.name.eq_ignore_ascii_case(normalized)
                && binding
                    .stack_slot
                    .as_ref()
                    .is_some_and(|slot| stack_slot_key_matches_offset(slot, offset))
        })
        .and_then(|binding| binding.ty.as_ref())
        .and_then(renderable_type)
        .or_else(|| {
            type_facts
                .stack_slots
                .iter()
                .find(|(slot_key, slot)| {
                    matches!(
                        slot.role,
                        ExternalStackSlotRole::Local | ExternalStackSlotRole::StackArg
                    ) && slot.name.eq_ignore_ascii_case(normalized)
                        && stack_slot_key_matches_offset(slot_key, offset)
                })
                .and_then(|(_, slot)| slot.ty.as_ref())
                .and_then(renderable_type)
        })
}

fn stack_slot_key_matches_offset(slot: &StackSlotKey, offset: i64) -> bool {
    slot.offset == offset
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

fn definite_assignment_residual_reason(func: &CFunction) -> Option<String> {
    let mut local_names = func
        .locals
        .iter()
        .map(|local| local.name.clone())
        .collect::<BTreeSet<_>>();
    for stmt in &func.body {
        collect_declared_local_names(stmt, &mut local_names);
    }
    let mut assigned = func
        .params
        .iter()
        .map(|param| param.name.clone())
        .collect::<BTreeSet<_>>();
    for (index, stmt) in func.body.iter().enumerate() {
        if let Err(reason) = analyze_definite_assignment_stmt(stmt, &local_names, &mut assigned) {
            return Some(format!(
                "definite-assignment proof failed at statement {index}: {reason}"
            ));
        }
    }
    None
}

fn collect_declared_local_names(stmt: &CStmt, names: &mut BTreeSet<String>) {
    match stmt {
        CStmt::Decl { name, .. } => {
            names.insert(name.clone());
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                collect_declared_local_names(stmt, names);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            collect_declared_local_names(then_body, names);
            if let Some(else_body) = else_body {
                collect_declared_local_names(else_body, names);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            collect_declared_local_names(body, names);
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                collect_declared_local_names(init, names);
            }
            collect_declared_local_names(body, names);
        }
        CStmt::Switch { cases, default, .. } => {
            for stmt in cases.iter().flat_map(|case| &case.body) {
                collect_declared_local_names(stmt, names);
            }
            for stmt in default.iter().flatten() {
                collect_declared_local_names(stmt, names);
            }
        }
        _ => {}
    }
}

fn analyze_definite_assignment_stmt(
    stmt: &CStmt,
    local_names: &BTreeSet<String>,
    assigned: &mut BTreeSet<String>,
) -> Result<(), String> {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => {
            analyze_definite_assignment_expr_stmt(expr, local_names, assigned)?;
        }
        CStmt::Decl { name, init, .. } => {
            if let Some(init) = init {
                validate_expr_local_reads(init, local_names, assigned, false)?;
                assigned.insert(name.clone());
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                analyze_definite_assignment_stmt(stmt, local_names, assigned)?;
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            validate_expr_local_reads(cond, local_names, assigned, false)?;
            let mut then_assigned = assigned.clone();
            analyze_definite_assignment_stmt(then_body, local_names, &mut then_assigned)?;
            let mut else_assigned = assigned.clone();
            if let Some(else_body) = else_body {
                analyze_definite_assignment_stmt(else_body, local_names, &mut else_assigned)?;
            }
            *assigned = then_assigned
                .intersection(&else_assigned)
                .cloned()
                .collect();
        }
        CStmt::While { cond, body } => {
            validate_expr_local_reads(cond, local_names, assigned, false)?;
            let mut body_assigned = assigned.clone();
            analyze_definite_assignment_stmt(body, local_names, &mut body_assigned)?;
        }
        CStmt::DoWhile { body, cond } => {
            let mut body_assigned = assigned.clone();
            analyze_definite_assignment_stmt(body, local_names, &mut body_assigned)?;
            validate_expr_local_reads(cond, local_names, &body_assigned, false)?;
            *assigned = body_assigned;
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                analyze_definite_assignment_stmt(init, local_names, assigned)?;
            }
            if let Some(cond) = cond {
                validate_expr_local_reads(cond, local_names, assigned, false)?;
            }
            let mut body_assigned = assigned.clone();
            analyze_definite_assignment_stmt(body, local_names, &mut body_assigned)?;
            if let Some(update) = update {
                analyze_definite_assignment_expr_stmt(update, local_names, &mut body_assigned)?;
            }
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            validate_expr_local_reads(expr, local_names, assigned, false)?;
            let mut exits = Vec::new();
            for case in cases {
                let mut case_assigned = assigned.clone();
                for stmt in &case.body {
                    analyze_definite_assignment_stmt(stmt, local_names, &mut case_assigned)?;
                }
                exits.push(case_assigned);
            }
            if let Some(default) = default {
                let mut default_assigned = assigned.clone();
                for stmt in default {
                    analyze_definite_assignment_stmt(stmt, local_names, &mut default_assigned)?;
                }
                exits.push(default_assigned);
            } else {
                exits.push(assigned.clone());
            }
            if let Some(first) = exits.first().cloned() {
                *assigned = exits[1..].iter().fold(first, |current, exit| {
                    current.intersection(exit).cloned().collect()
                });
            }
        }
        CStmt::Return(value) => {
            if let Some(value) = value {
                validate_expr_local_reads(value, local_names, assigned, false)?;
            }
        }
    }
    Ok(())
}

fn analyze_definite_assignment_expr_stmt(
    expr: &CExpr,
    local_names: &BTreeSet<String>,
    assigned: &mut BTreeSet<String>,
) -> Result<(), String> {
    if let CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    } = expr
    {
        validate_expr_local_reads(right, local_names, assigned, false)?;
        validate_expr_local_reads(left, local_names, assigned, true)?;
        if let CExpr::Var(name) = left.as_ref()
            && local_names.contains(name)
        {
            assigned.insert(name.clone());
        }
        return Ok(());
    }
    validate_expr_local_reads(expr, local_names, assigned, false)
}

fn validate_expr_local_reads(
    expr: &CExpr,
    local_names: &BTreeSet<String>,
    assigned: &BTreeSet<String>,
    is_assignment_lhs: bool,
) -> Result<(), String> {
    match expr {
        CExpr::Var(name) => {
            if !is_assignment_lhs && local_names.contains(name) && !assigned.contains(name) {
                return Err(format!("local {name} may be read before assignment"));
            }
        }
        CExpr::Unary {
            op: UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
            operand,
        } => {
            validate_expr_local_reads(operand, local_names, assigned, false)?;
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => {
            validate_expr_local_reads(operand, local_names, assigned, false)?;
        }
        CExpr::AddrOf(operand) => {
            if !matches!(operand.as_ref(), CExpr::Var(_)) {
                validate_expr_local_reads(operand, local_names, assigned, false)?;
            }
        }
        CExpr::Binary { op, left, right } => {
            let lhs_is_write = matches!(op, BinaryOp::Assign);
            validate_expr_local_reads(left, local_names, assigned, lhs_is_write)?;
            validate_expr_local_reads(right, local_names, assigned, false)?;
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            validate_expr_local_reads(cond, local_names, assigned, false)?;
            validate_expr_local_reads(then_expr, local_names, assigned, false)?;
            validate_expr_local_reads(else_expr, local_names, assigned, false)?;
        }
        CExpr::Call { func, args } => {
            validate_expr_local_reads(func, local_names, assigned, false)?;
            for arg in args {
                validate_expr_local_reads(arg, local_names, assigned, false)?;
            }
        }
        CExpr::Subscript { base, index } => {
            validate_expr_local_reads(base, local_names, assigned, false)?;
            validate_expr_local_reads(index, local_names, assigned, false)?;
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            validate_expr_local_reads(base, local_names, assigned, false)?;
        }
        CExpr::Comma(items) => {
            for item in items {
                validate_expr_local_reads(item, local_names, assigned, false)?;
            }
        }
        CExpr::Sizeof(_)
        | CExpr::SizeofType(_)
        | CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_) => {}
    }
    Ok(())
}

fn certified_standard_output_residual_reason_with_effect_proofs(
    prepared: &r2ssa::SsaArtifact,
    function_facts: &FunctionFacts,
    func: &CFunction,
    effect_render_proofs: Option<&[EffectRenderProof]>,
) -> Option<String> {
    let empty_callsites = r2types::FunctionCallsiteFacts::default();
    let callsite_facts = function_facts.callsites().unwrap_or(&empty_callsites);
    let empty_call_results = r2types::FunctionCallResultFacts::default();
    let call_result_facts = function_facts.call_results().unwrap_or(&empty_call_results);
    let empty_render = r2types::FunctionRenderFacts::default();
    let render_facts = function_facts.render().unwrap_or(&empty_render);
    let mut reasons = Vec::new();
    for effect in render_facts.certified_effects.values() {
        let domain = effect.control_domain();
        if !domain.complete {
            reasons.push(format!(
                "certified effect {} has incomplete control domain {}",
                effect.id(),
                domain.id.0
            ));
        }
    }

    if func.body.is_empty() {
        reasons.push("certified standard route produced no body".to_string());
    }
    if let Some(reason) = definite_assignment_residual_reason(func) {
        reasons.push(reason);
    }
    for local in &func.locals {
        match local.stack_offset {
            Some(offset)
                if certified_stack_local_identity_is_exact(function_facts, &local.name, offset)
                    && certified_stack_local_type_matches(
                        function_facts.type_facts(),
                        &local.name,
                        offset,
                        &local.ty,
                    ) => {}
            None if certified_loop_carrier_local_is_exact(function_facts, local) => {}
            None if certified_memory_result_local_is_exact(function_facts, local) => {}
            Some(offset) => reasons.push(format!(
                "local {} at stack offset {} lacks exact typed StackSlotCertificate",
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
        let semantic_ledger =
            CertifiedSemanticLedger::from_effect_proofs(function_facts, effect_render_proofs);
        if !render_facts.certified_effects.is_empty() && semantic_ledger.unresolved > 0 {
            reasons.push(format!(
                "{} rendered proof(s) lack stable semantic identity",
                semantic_ledger.unresolved
            ));
        }
        for proof in effect_render_proofs
            .iter()
            .filter(|proof| proof.kind == EffectRenderProofKind::Call)
        {
            match callsite_facts.arguments_for_site(r2types::CallsiteKey {
                block_addr: proof.block_addr,
                op_index: proof.op_idx,
            }) {
                Some(cert) => {
                    if proof.target != Some(cert.target) {
                        reasons.push(format!(
                            "rendered call proof at 0x{:x}:{} target proof {:?} disagrees with FunctionCallsiteFacts target {:?}",
                            proof.block_addr, proof.op_idx, proof.target, cert.target
                        ));
                    }
                    let expected =
                        certified_callsite_expected_argument_values(function_facts, cert);
                    if proof.values != expected {
                        reasons.push(format!(
                            "rendered call proof at 0x{:x}:{} argument value proof {:?} disagrees with FunctionCallsiteFacts argument values {:?}",
                            proof.block_addr, proof.op_idx, proof.values, cert.argument_values
                        ));
                    }
                    for value in &proof.values {
                        if !render_facts.expression_is_renderable(*value) {
                            reasons.push(format!(
                                "rendered call proof at 0x{:x}:{} argument value {:?} lacks renderable FunctionRenderFacts expression",
                                proof.block_addr, proof.op_idx, value
                            ));
                        }
                    }
                }
                None => {
                    reasons.push(format!(
                        "rendered call proof at 0x{:x}:{} has no matching FunctionCallsiteFacts callsite",
                        proof.block_addr, proof.op_idx
                    ));
                }
            }
        }
        for proof in effect_render_proofs
            .iter()
            .filter(|proof| proof.kind == EffectRenderProofKind::Expression)
        {
            match proof
                .value
                .and_then(|value| render_facts.expression_for_value(value).map(|cert| (value, cert)))
            {
                Some((value, cert)) => {
                    if !cert.renderable {
                        reasons.push(format!(
                            "rendered expression proof at 0x{:x}:{} value {:?} lacks renderable FunctionRenderFacts expression",
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
                        && !expression_proof_is_materialized_phi_copy(
                            prepared,
                            render_facts,
                            proof,
                            value,
                            cert,
                        )
                    {
                        match cert.defining_inst.and_then(|inst| prepared.inst_op_site(inst)) {
                            Some((block_addr, op_idx)) => reasons.push(format!(
                                "rendered expression proof at 0x{:x}:{} value {:?} was neither defined nor consumed at the rendered op site; FunctionRenderFacts value was defined at 0x{:x}:{}",
                                proof.block_addr, proof.op_idx, value, block_addr, op_idx
                            )),
                            None => reasons.push(format!(
                                "rendered expression proof at 0x{:x}:{} value {:?} was not consumed at the rendered op site and lacks defining op-site FunctionRenderFacts expression",
                                proof.block_addr, proof.op_idx, value
                            )),
                        }
                    }
                }
                None => reasons.push(format!(
                    "rendered expression proof at 0x{:x}:{} value {:?} has no matching FunctionRenderFacts expression",
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
            match render_facts.memory_access_for_op(proof.block_addr, proof.op_idx, is_write) {
                Some(cert) => {
                    if proof.address != Some(cert.address) {
                        reasons.push(format!(
                            "rendered memory proof at 0x{:x}:{} address proof {:?} disagrees with FunctionRenderFacts memory address {:?}",
                            proof.block_addr, proof.op_idx, proof.address, cert.address
                        ));
                    }
                    if proof.value != cert.value {
                        reasons.push(format!(
                            "rendered memory proof at 0x{:x}:{} value proof {:?} disagrees with FunctionRenderFacts memory value {:?}",
                            proof.block_addr, proof.op_idx, proof.value, cert.value
                        ));
                    }
                }
                None => {
                    reasons.push(format!(
                        "rendered memory proof at 0x{:x}:{} has no matching FunctionRenderFacts memory access",
                        proof.block_addr, proof.op_idx
                    ));
                }
            }
        }
        for proof in effect_render_proofs
            .iter()
            .filter(|proof| proof.kind == EffectRenderProofKind::Return)
        {
            match render_facts.return_for_op(proof.block_addr, proof.op_idx) {
                Some(cert) => {
                    if proof.value != Some(cert.value) {
                        reasons.push(format!(
                            "rendered return proof at 0x{:x}:{} value proof {:?} disagrees with FunctionRenderFacts return value {:?}",
                            proof.block_addr, proof.op_idx, proof.value, cert.value
                        ));
                    }
                    if proof.value.is_some_and(|value| {
                        return_value_has_certified_call_result_effect(
                            Some(call_result_facts),
                            effect_render_proofs,
                            value,
                        )
                    }) {
                        continue;
                    }
                    match proof.value.and_then(|value| {
                        render_facts
                            .expression_for_value(value)
                            .map(|cert| (value, cert))
                    }) {
                        Some((value, expr_cert)) => {
                            if !expr_cert.renderable {
                                let value_name = prepared
                                    .value_var(value)
                                    .map(|var| var.display_name())
                                    .unwrap_or_else(|| "<unknown>".to_string());
                                reasons.push(format!(
                                    "rendered return proof at 0x{:x}:{} value {:?} ({}) lacks renderable FunctionRenderFacts expression",
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
                            let bound_by_return_certificate = proof.value == Some(cert.value);
                            if !defined_at_rendered_site
                                && !consumed_at_rendered_site
                                && !bound_by_return_certificate
                            {
                                match expr_cert
                                    .defining_inst
                                    .and_then(|inst| prepared.inst_op_site(inst))
                                {
                                    Some((block_addr, op_idx)) => reasons.push(format!(
                                        "rendered return proof at 0x{:x}:{} value {:?} was neither defined nor consumed at the rendered op site; FunctionRenderFacts value was defined at 0x{:x}:{}",
                                        proof.block_addr, proof.op_idx, value, block_addr, op_idx
                                    )),
                                    None => reasons.push(format!(
                                        "rendered return proof at 0x{:x}:{} value {:?} was not consumed at the rendered op site and lacks defining op-site FunctionRenderFacts expression",
                                        proof.block_addr, proof.op_idx, value
                                    )),
                                }
                            }
                        }
                        None => reasons.push(format!(
                            "rendered return proof at 0x{:x}:{} value {:?} has no matching FunctionRenderFacts expression",
                            proof.block_addr, proof.op_idx, proof.value
                        )),
                    }
                }
                None => {
                    reasons.push(format!(
                        "rendered return proof at 0x{:x}:{} has no matching FunctionRenderFacts return",
                        proof.block_addr, proof.op_idx
                    ));
                }
            }
        }
        let proof_counts = certified_effect_proof_counts(effect_render_proofs);
        let call_render_facts = call_render_facts_from_effect_proofs(effect_render_proofs);
        let missing_source_callsite = callsite_facts
            .by_callsite
            .keys()
            .find(|callsite| call_render_facts.fact_for_site(**callsite).is_none());
        if let Some(callsite) = missing_source_callsite {
            reasons.push(format!(
                "rendered {} executable call(s) from {} source FunctionCallsiteFacts callsite(s); first missing callsite 0x{:x}:{}; missing callsite effects must residualize instead of disappearing",
                counts.calls,
                callsite_facts.by_callsite.len(),
                callsite.block_addr,
                callsite.op_index
            ));
        }
        if counts.calls > proof_counts.calls {
            let first_missing = counts
                .call_nodes
                .get(proof_counts.calls)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} call(s) with only {} rendered FunctionCallsiteFacts proof(s){}",
                counts.calls, proof_counts.calls, first_missing
            ));
        }
        if proof_counts.calls > counts.calls {
            reasons.push(format!(
                "rendered FunctionCallsiteFacts proof recorded {} call effect(s), but final AST contains only {} executable call(s); dropped callsite effects must residualize instead of disappearing",
                proof_counts.calls, counts.calls
            ));
        }
        if counts.expression_roots > proof_counts.expressions {
            let first_missing = counts
                .expression_nodes
                .get(proof_counts.expressions)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} pure expression assignment(s) with only {} rendered FunctionRenderFacts expression proof(s){}",
                counts.expression_roots, proof_counts.expressions, first_missing
            ));
        }
        let return_proofs = proof_counts.returns;
        if counts.returns_with_value > return_proofs {
            let first_missing = counts
                .return_nodes
                .get(return_proofs)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} value return(s) with only {} rendered FunctionRenderFacts return proof(s){}",
                counts.returns_with_value, return_proofs, first_missing
            ));
        }
        if counts.returns_with_value > 0 && proof_counts.returns == 0 {
            reasons.push(format!(
                "rendered {} value return(s) with no EffectRenderProof coverage; returns require at least one certified proof",
                counts.returns_with_value
            ));
        }
        let memory_proofs =
            certified_memory_effects_requiring_ast_access(render_facts, effect_render_proofs);
        if counts.memory_like_accesses > memory_proofs {
            let first_missing = counts
                .memory_nodes
                .get(memory_proofs)
                .map(|id| format!("; first missing node {id}"))
                .unwrap_or_default();
            reasons.push(format!(
                "rendered {} memory-like access(es) with only {} rendered FunctionRenderFacts memory proof(s){}",
                counts.memory_like_accesses, memory_proofs, first_missing
            ));
        }
        if memory_proofs > counts.memory_like_accesses {
            reasons.push(format!(
				"rendered FunctionRenderFacts proof recorded {} memory effect(s), but final AST contains only {} memory-like access(es); dropped memory effects must residualize instead of disappearing",
				memory_proofs, counts.memory_like_accesses
			));
        }
    } else if counts.calls > 0
        || counts.expression_roots > 0
        || counts.returns_with_value > 0
        || counts.memory_like_accesses > 0
    {
        reasons.push(format!(
            "missing exact FunctionFacts render proof for certified Standard output: rendered calls={}, expression_roots={}, value_returns={}, memory_like_accesses={}",
            counts.calls, counts.expression_roots, counts.returns_with_value, counts.memory_like_accesses
        ));
    }
    let proved_member_counts = effect_render_proofs
        .map(|proofs| proved_member_access_counts(render_facts, proofs))
        .unwrap_or_default();
    if counts.field_accesses > 0 && !field_accesses_are_certified(&proved_member_counts, &counts) {
        let first_node = counts
            .field_nodes
            .first()
            .map(|(id, member)| format!("; first field node {id}.{member}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} field access(es) without FunctionRenderFacts member-access proof{}",
            counts.field_accesses, first_node
        ));
    }
    if !counts.return_field_members.is_empty()
        && !return_field_members_are_authoritatively_certified(&proved_member_counts, &counts)
    {
        let first_member = counts
            .return_field_members
            .first()
            .map(|member| format!("; first returned member {member}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered returned field access(es) without FunctionRenderFacts member-access proof{}",
            first_member
        ));
    }
    let array_accesses_certified = effect_render_proofs
        .is_some_and(|proofs| array_accesses_are_certified(render_facts, proofs, &counts));
    if counts.array_accesses > 0 && !array_accesses_certified {
        let first_missing = counts
            .array_nodes
            .first()
            .map(|id| format!("; first array node {id}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} array access(es) without exact FunctionRenderFacts array-access proof{}",
            counts.array_accesses, first_missing
        ));
    }
    if counts.raw_pointer_arithmetic_derefs > 0 {
        let first_node = counts
            .raw_pointer_arithmetic_nodes
            .first()
            .map(|id| format!("; first raw pointer arithmetic node {id}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} raw pointer-arithmetic dereference(s); typed field/array accesses must render through FunctionFacts certificates{}",
            counts.raw_pointer_arithmetic_derefs, first_node
        ));
    }
    if counts.raw_address_call_args > 0 {
        let first_node = counts
            .raw_address_call_arg_nodes
            .first()
            .map(|id| format!("; first raw address call argument node {id}"))
            .unwrap_or_default();
        reasons.push(format!(
            "rendered {} raw address-like call argument(s); pointer/string call arguments must render through FunctionFacts certificates{}",
            counts.raw_address_call_args, first_node
        ));
    }
    if counts.residual_comments > 0 {
        let first_node = counts
            .residual_comment_nodes
            .first()
            .map(|id| format!("; first residual node {id}"))
            .unwrap_or_default();
        let first_comment = counts
            .residual_comment_texts
            .first()
            .map(|comment| format!("; first residual comment: {comment}"))
            .unwrap_or_default();
        reasons.push(format!(
			"rendered {} residual comment(s) inside certified Standard output; residuals must replace the whole executable body{}{}",
			counts.residual_comments, first_node, first_comment
		));
    }
    raw_names.sort();
    raw_names.dedup();
    raw_names.retain(|name| {
        !func
            .params
            .iter()
            .any(|param| param.name.eq_ignore_ascii_case(name))
            && !func.locals.iter().any(|local| {
                local.name.eq_ignore_ascii_case(name)
                    && (local.stack_offset.is_some_and(|offset| {
                        certified_stack_local_identity_is_exact(function_facts, &local.name, offset)
                            && certified_stack_local_type_matches(
                                function_facts.type_facts(),
                                &local.name,
                                offset,
                                &local.ty,
                            )
                    }) || certified_loop_carrier_local_is_exact(function_facts, local)
                        || certified_memory_result_local_is_exact(function_facts, local))
            })
    });
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
    render_facts: &r2types::FunctionRenderFacts,
    proof: &EffectRenderProof,
    value: r2ssa::ValueId,
    cert: &r2types::ExpressionRenderFact,
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
    let [source] = proof.values.as_slice() else {
        return false;
    };
    let phi_edge_matches = predecessors.iter().zip(&inst.inputs).any(|(pred, input)| {
        *input == *source
            && prepared
                .graph()
                .block(*pred)
                .is_some_and(|block| block.addr == proof.block_addr)
    });
    if phi_edge_matches {
        return true;
    }
    matches!(
        render_facts.loop_carrier_for_value(value),
        Some(r2types::CertifiedEntity::LoopCarrier {
            phi,
            dominating_initializers,
            ..
        }) if *phi == value
            && dominating_initializers.iter().any(|initializer| {
                initializer.predecessor == proof.block_addr && initializer.value == *source
            })
    )
}

fn array_accesses_are_certified(
    render_facts: &r2types::FunctionRenderFacts,
    effect_render_proofs: &[EffectRenderProof],
    counts: &CertifiedOutputCounts,
) -> bool {
    let mut proved = BTreeSet::new();
    for proof in effect_render_proofs.iter().filter(|proof| {
        matches!(
            proof.kind,
            EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite
        )
    }) {
        let is_write = proof.kind == EffectRenderProofKind::MemoryWrite;
        let Some(memory) =
            render_facts.memory_access_for_op(proof.block_addr, proof.op_idx, is_write)
        else {
            continue;
        };
        if proof.address != Some(memory.address) || proof.value != memory.value {
            continue;
        }
        if render_facts
            .array_accesses_by_op
            .get(&(proof.block_addr, proof.op_idx, is_write))
            .into_iter()
            .flatten()
            .any(|array| {
                array.access == memory.access
                    && array.block_addr == memory.block_addr
                    && array.op_index == memory.op_index
                    && array.object == memory.object
                    && array.is_write == memory.is_write
                    && array.access_width == memory.width
                    && array.element_stride > 0
            })
        {
            proved.insert((proof.block_addr, proof.op_idx, is_write, memory.access));
        }
    }

    let mut proved = proved.into_iter();
    counts.array_nodes.iter().all(|_| proved.next().is_some())
}

fn proved_member_access_counts(
    render_facts: &r2types::FunctionRenderFacts,
    effect_render_proofs: &[EffectRenderProof],
) -> BTreeMap<String, usize> {
    let mut proved = BTreeMap::<String, usize>::new();
    for proof in effect_render_proofs.iter().filter(|proof| {
        matches!(
            proof.kind,
            EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite
        )
    }) {
        let is_write = proof.kind == EffectRenderProofKind::MemoryWrite;
        let Some(memory) =
            render_facts.memory_access_for_op(proof.block_addr, proof.op_idx, is_write)
        else {
            continue;
        };
        if proof.address != Some(memory.address) || proof.value != memory.value {
            continue;
        }
        for member in render_facts
            .member_accesses_by_op
            .get(&(proof.block_addr, proof.op_idx, is_write))
            .into_iter()
            .flatten()
            .filter(|member| {
                member.access == memory.access
                    && member.object == memory.object
                    && member.access_width == memory.width
            })
        {
            *proved
                .entry(member.field_name.to_ascii_lowercase())
                .or_default() += 1;
        }
    }
    proved
}

fn field_accesses_are_certified(
    proved_member_counts: &BTreeMap<String, usize>,
    counts: &CertifiedOutputCounts,
) -> bool {
    let mut rendered = BTreeMap::<String, usize>::new();
    for (_, member) in &counts.field_nodes {
        *rendered.entry(member.to_ascii_lowercase()).or_default() += 1;
    }

    rendered
        .into_iter()
        .all(|(field, count)| proved_member_counts.get(&field).copied().unwrap_or(0) >= count)
}

fn return_field_members_are_authoritatively_certified(
    proved_member_counts: &BTreeMap<String, usize>,
    counts: &CertifiedOutputCounts,
) -> bool {
    let mut returned = BTreeMap::<String, usize>::new();
    for member in &counts.return_field_members {
        *returned.entry(member.to_ascii_lowercase()).or_default() += 1;
    }

    returned
        .into_iter()
        .all(|(field, count)| proved_member_counts.get(&field).copied().unwrap_or(0) >= count)
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
            collect_expr_field_members(expr, &mut counts.return_field_members);
            collect_certified_expr_contract(expr, id.child(0), counts, raw_names);
        }
        CStmt::Return(None)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {
            if let CStmt::Comment(text) = stmt
                && (text.contains("r2sleigh residual:") || text.contains("r2dec residual:"))
            {
                counts.residual_comments += 1;
                counts.residual_comment_nodes.push(id);
                counts.residual_comment_texts.push(text.clone());
            }
        }
    }
}

fn collect_expr_field_members(expr: &CExpr, members: &mut Vec<String>) {
    expr.visit(&mut |node| {
        if let CExpr::Member { member, .. } | CExpr::PtrMember { member, .. } = node {
            members.push(member.clone());
        }
    });
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
    collect_certified_expr_contract_inner(expr, id, counts, raw_names, false);
}

fn collect_certified_expr_contract_inner(
    expr: &CExpr,
    id: RenderNodeId,
    counts: &mut CertifiedOutputCounts,
    raw_names: &mut Vec<String>,
    inside_memory_access: bool,
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
            collect_certified_expr_contract_inner(func, id.child(0), counts, raw_names, false);
            for (index, arg) in args.iter().enumerate() {
                let arg_id = id.child(index + 1);
                if certified_expr_is_raw_address_call_arg(arg) {
                    counts.raw_address_call_args += 1;
                    counts.raw_address_call_arg_nodes.push(arg_id.clone());
                }
                collect_certified_expr_contract_inner(arg, arg_id, counts, raw_names, false);
            }
        }
        CExpr::Subscript { base, index } => {
            if !inside_memory_access {
                counts.memory_like_accesses += 1;
                counts.memory_nodes.push(id.clone());
            }
            counts.array_accesses += 1;
            counts.array_nodes.push(id.clone());
            collect_certified_expr_contract_inner(base, id.child(0), counts, raw_names, true);
            collect_certified_expr_contract_inner(index, id.child(1), counts, raw_names, false);
        }
        CExpr::Member { base, member } | CExpr::PtrMember { base, member } => {
            if !inside_memory_access {
                counts.memory_like_accesses += 1;
                counts.memory_nodes.push(id.clone());
            }
            counts.field_accesses += 1;
            counts.field_members.push(member.clone());
            counts.field_nodes.push((id.clone(), member.clone()));
            collect_certified_expr_contract_inner(base, id.child(0), counts, raw_names, true);
        }
        CExpr::Deref(inner) => {
            if !inside_memory_access {
                counts.memory_like_accesses += 1;
                counts.memory_nodes.push(id.clone());
            }
            if certified_expr_is_raw_pointer_arithmetic(inner) {
                counts.raw_pointer_arithmetic_derefs += 1;
                counts.raw_pointer_arithmetic_nodes.push(id.clone());
            }
            collect_certified_expr_contract_inner(inner, id.child(0), counts, raw_names, true);
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Paren(operand) => collect_certified_expr_contract_inner(
            operand,
            id.child(0),
            counts,
            raw_names,
            inside_memory_access,
        ),
        CExpr::Binary { left, right, .. } => {
            collect_certified_expr_contract_inner(left, id.child(0), counts, raw_names, false);
            collect_certified_expr_contract_inner(right, id.child(1), counts, raw_names, false);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_certified_expr_contract_inner(cond, id.child(0), counts, raw_names, false);
            collect_certified_expr_contract_inner(then_expr, id.child(1), counts, raw_names, false);
            collect_certified_expr_contract_inner(else_expr, id.child(2), counts, raw_names, false);
        }
        CExpr::Comma(items) => {
            for (index, item) in items.iter().enumerate() {
                collect_certified_expr_contract_inner(
                    item,
                    id.child(index),
                    counts,
                    raw_names,
                    false,
                );
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

fn certified_expr_is_raw_address_call_arg(expr: &CExpr) -> bool {
    const MIN_ADDRESS_LIKE_LITERAL: u64 = 0x1000;

    match expr {
        CExpr::UIntLit(value) => *value >= MIN_ADDRESS_LIKE_LITERAL,
        CExpr::IntLit(value) => {
            u64::try_from(*value).is_ok_and(|value| value >= MIN_ADDRESS_LIKE_LITERAL)
        }
        CExpr::Cast { expr, .. } | CExpr::Paren(expr) => {
            certified_expr_is_raw_address_call_arg(expr)
        }
        CExpr::Binary { left, right, .. } => {
            certified_expr_is_raw_address_call_arg(left)
                || certified_expr_is_raw_address_call_arg(right)
        }
        CExpr::Unary { operand, .. } => certified_expr_is_raw_address_call_arg(operand),
        _ => false,
    }
}

fn certified_expr_is_raw_pointer_arithmetic(expr: &CExpr) -> bool {
    match expr {
        CExpr::Binary { op, .. } => matches!(
            op,
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Shl | BinaryOp::Shr
        ),
        CExpr::Cast { expr, .. } | CExpr::Paren(expr) => {
            certified_expr_is_raw_pointer_arithmetic(expr)
        }
        _ => false,
    }
}

fn is_uncertified_render_var_name(name: &str) -> bool {
    let stripped = name.trim_start_matches('&');
    let lower = stripped.to_ascii_lowercase();
    let is_generated_arg = lower
        .strip_prefix("arg")
        .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit()));
    crate::analysis::utils::is_temporary_name(stripped)
        || stripped == "__r2dec_unresolved_call_arg"
        || is_generated_arg
        || lower.starts_with("tmp_")
        || lower.starts_with("unique_")
        || lower.starts_with("stack_")
        || lower.starts_with("local_")
        || lower.starts_with("var_")
        || lower.starts_with("value_")
        || is_unversioned_raw_register_label(stripped)
        || is_ssa_versioned_register_label(stripped)
}

fn is_unversioned_raw_register_label(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    matches!(
        lower.as_str(),
        "al" | "ah"
            | "ax"
            | "eax"
            | "rax"
            | "bl"
            | "bh"
            | "bx"
            | "ebx"
            | "rbx"
            | "cl"
            | "ch"
            | "cx"
            | "ecx"
            | "rcx"
            | "dl"
            | "dh"
            | "dx"
            | "edx"
            | "rdx"
            | "si"
            | "esi"
            | "rsi"
            | "di"
            | "edi"
            | "rdi"
            | "sp"
            | "esp"
            | "rsp"
            | "bp"
            | "ebp"
            | "rbp"
            | "x0"
            | "w0"
            | "x1"
            | "w1"
            | "x2"
            | "w2"
            | "x3"
            | "w3"
            | "x8"
            | "w8"
            | "x9"
            | "w9"
            | "x10"
            | "w10"
            | "x20"
            | "w20"
    )
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

fn params_from_authorized_signature(signature: &FunctionSignatureSpec) -> Vec<ast::CParam> {
    signature
        .params
        .iter()
        .enumerate()
        .map(|(idx, param)| ast::CParam {
            ty: param
                .ty
                .as_ref()
                .map(type_like_to_ctype)
                .expect("render-authorized signature parameter types checked before rendering"),
            name: if param.name.trim().is_empty() || is_generic_arg_name(&param.name) {
                format!("arg{idx}")
            } else {
                param.name.clone()
            },
        })
        .collect()
}

fn signature_has_complete_render_param_types(signature: &FunctionSignatureSpec) -> bool {
    signature.params.iter().all(|param| {
        param
            .ty
            .as_ref()
            .is_some_and(|ty| !matches!(type_like_to_ctype(ty), CType::Unknown))
    })
}

fn certified_signature_entity_residual_reason(
    signature: &FunctionSignatureSpec,
    render: &r2types::FunctionRenderFacts,
    ptr_bits: u32,
) -> Option<String> {
    let params = params_from_authorized_signature(signature);
    let mut entities = BTreeMap::<u32, u32>::new();
    for entity in render.certified_entities.values() {
        if let r2types::CertifiedEntity::Parameter {
            slot,
            carrier_width,
            ..
        } = entity
        {
            entities.insert(*slot, *carrier_width);
        }
    }
    if entities.len() != params.len()
        || entities
            .keys()
            .copied()
            .ne((0..params.len()).map(|slot| slot as u32))
    {
        return Some(format!(
            "certified ABI parameter slots {:?} disagree with rendered signature arity {}",
            entities.keys().collect::<Vec<_>>(),
            params.len()
        ));
    }
    for (slot, param) in params.iter().enumerate() {
        let source_type = signature.params[slot]
            .ty
            .as_ref()
            .expect("render-authorized parameter type checked before ABI certification");
        let Some(type_bits) = certified_type_width(source_type, ptr_bits) else {
            return Some(format!(
                "parameter {slot} type {} has no certified width",
                param.ty
            ));
        };
        let carrier_bits = entities
            .get(&(slot as u32))
            .copied()
            .unwrap_or(0)
            .saturating_mul(8);
        let width_matches = if certified_type_is_pointer(source_type) {
            type_bits == carrier_bits
        } else {
            type_bits > 0 && type_bits <= carrier_bits
        };
        if !width_matches {
            return Some(format!(
                "parameter {slot} type width {type_bits} disagrees with ABI carrier width {carrier_bits}"
            ));
        }
    }

    let source_ret_type = signature.ret_type.as_ref()?;
    let ret_type = type_like_to_ctype(source_ret_type);
    let return_widths = render
        .certified_effects
        .values()
        .filter_map(|effect| effect.return_fact().map(|fact| fact.width))
        .collect::<BTreeSet<_>>();
    if matches!(ret_type, CType::Void) {
        if !return_widths.is_empty() {
            return Some(format!(
                "void signature has certified value-return widths {:?}",
                return_widths
            ));
        }
        return None;
    }
    let Some(ret_bits) = certified_type_width(source_ret_type, ptr_bits) else {
        return Some(format!("return type {ret_type} has no certified width"));
    };
    let return_width_matches = !return_widths.is_empty()
        && return_widths.iter().all(|width| {
            let carrier_bits = width.saturating_mul(8);
            if certified_type_is_pointer(source_ret_type) {
                ret_bits == carrier_bits
            } else {
                ret_bits > 0 && ret_bits <= carrier_bits
            }
        });
    if !return_width_matches {
        return Some(format!(
            "signature return width {} bit(s) disagrees with certified carrier widths {:?}",
            ret_bits,
            render
                .certified_effects
                .values()
                .filter_map(|effect| effect.return_fact().map(|fact| fact.width))
                .collect::<BTreeSet<_>>()
        ));
    }
    None
}

fn certified_type_width(ty: &r2types::CTypeLike, ptr_bits: u32) -> Option<u32> {
    match ty {
        r2types::CTypeLike::Bool => Some(1),
        r2types::CTypeLike::Int { bits, .. } | r2types::CTypeLike::Float(bits) => Some(*bits),
        r2types::CTypeLike::Pointer(_) => Some(ptr_bits),
        r2types::CTypeLike::Typedef(name) if r2types::semantic_typedef_is_pointer(name) => {
            Some(ptr_bits)
        }
        r2types::CTypeLike::Typedef(name) => {
            let resolved = r2types::parse_external_type_like_spec(name, ptr_bits)?;
            if &resolved == ty {
                None
            } else {
                certified_type_width(&resolved, ptr_bits)
            }
        }
        _ => None,
    }
}

fn certified_type_is_pointer(ty: &r2types::CTypeLike) -> bool {
    matches!(ty, r2types::CTypeLike::Pointer(_))
        || matches!(ty, r2types::CTypeLike::Typedef(name) if r2types::semantic_typedef_is_pointer(name))
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
    allow_positional_aliases: bool,
) -> std::collections::HashMap<String, String> {
    let mut aliases = std::collections::HashMap::new();

    if allow_positional_aliases {
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
    fn canonicalize_function_facts(mut function_facts: FunctionFacts) -> FunctionFacts {
        function_facts.canonicalize_type_facts();
        function_facts
    }

    pub fn type_facts(&self) -> &FunctionTypeFacts {
        self.function_facts.type_facts()
    }

    #[cfg(test)]
    pub fn type_facts_mut(&mut self) -> &mut FunctionTypeFacts {
        self.function_facts.__test_type_facts_mut()
    }

    pub fn semantic_artifact(&self) -> Option<&r2sym::SemanticArtifact> {
        self.function_facts.semantic_artifact()
    }

    pub fn function_facts(&self) -> &FunctionFacts {
        &self.function_facts
    }

    pub fn from_function_facts(function_facts: FunctionFacts) -> Self {
        let function_facts = Self::canonicalize_function_facts(function_facts);
        Self {
            #[cfg(test)]
            function_names: std::collections::HashMap::new(),
            #[cfg(test)]
            strings: std::collections::HashMap::new(),
            #[cfg(test)]
            symbols: std::collections::HashMap::new(),
            function_facts,
        }
    }

    #[cfg(test)]
    pub fn with_type_facts(mut self, type_facts: FunctionTypeFacts) -> Self {
        self.function_facts.replace_type_facts(type_facts);
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

    fn effective_render_permission(&self) -> Option<&r2sym::RenderPermission> {
        self.function_facts
            .decompile_route()
            .map(|route| &route.render_permission)
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
    pub prepared_ssa: r2ssa::SsaArtifact,
    pub interproc_summary_set: Option<r2ssa::InterprocSummarySet>,
    context: DecompilerContext,
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
        self.context
            .function_facts
            .set_summary_set(interproc_summary_set.clone());
        self.interproc_summary_set = interproc_summary_set;
        self
    }

    pub fn context(&self) -> &DecompilerContext {
        &self.context
    }

    pub fn function_facts(&self) -> &FunctionFacts {
        self.context.function_facts()
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

    /// Set externally recovered known function signatures keyed by name.
    #[cfg(test)]
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
    #[cfg(test)]
    pub fn set_external_type_db(&mut self, external_type_db: ExternalTypeDb) {
        self.context.type_facts_mut().external_type_db = external_type_db;
    }

    /// Set externally recovered type facts.
    #[cfg(test)]
    pub fn set_type_facts(&mut self, type_facts: FunctionTypeFacts) {
        self.context.function_facts.replace_type_facts(type_facts);
    }

    pub fn set_function_facts(&mut self, function_facts: FunctionFacts) {
        self.context = self.context.clone().with_function_facts(function_facts);
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
            function_facts.type_facts(),
            function_facts.semantic_artifact()?,
        )
    }

    /// Decompile a prepared function with an explicit typed context payload.
    pub fn decompile_input(&self, input: &DecompilerInput) -> String {
        let func = input.prepared_ssa.function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let Some(semantic_route) = input.context.function_facts.decompile_route() else {
            return missing_decompile_route_residual_comment(&func_name);
        };
        if let Some(comment) = route_fallback_comment(semantic_route) {
            return comment.to_string();
        }
        if let Some(comment) = render_permission_refusal_comment(
            &func_name,
            input.context.effective_render_permission(),
        ) {
            return comment;
        }
        if let Some(reason) =
            summary_only_semantics_standard_render_residual_reason(&input.context.function_facts)
        {
            return artifact_guard_fallback_comment(&func_name, &reason);
        }
        if let Some(output) = self.vm_summary_output_for_route(
            &func_name,
            &input.context.function_facts,
            semantic_route,
        ) {
            return output;
        }
        if let Some(output) = self.semantic_worker_summary_output_for_route(
            &func_name,
            &input.context.function_facts,
            semantic_route,
        ) {
            return output;
        }
        let c_func = self.build_function_from_input(input);
        let mut codegen = CodeGenerator::new(self.config.codegen.clone());
        codegen.generate_function(&c_func)
    }

    /// Build a C function from a prepared function + typed context payload.
    pub fn build_function_from_input(&self, input: &DecompilerInput) -> CFunction {
        let mut decompiler = Self::new(self.config.clone()).with_context(input.context.clone());
        let param_slots = ParamSlotResolver::from_arg_regs(&decompiler.config.arg_regs);
        decompiler
            .context
            .function_facts
            .normalize_field_certificates_from_external_layout();
        decompiler
            .context
            .function_facts
            .populate_member_access_render_facts_from_field_certificates(
                &input.prepared_ssa,
                &param_slots,
            );
        decompiler
            .context
            .function_facts
            .populate_array_access_render_facts_from_scalar_candidates(
                &input.prepared_ssa,
                &param_slots,
            );
        let func = input.prepared_ssa.function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let Some(semantic_route) = decompiler.context.function_facts.decompile_route() else {
            return residual_function_for_render_boundary(
                &func_name,
                &missing_decompile_route_residual_comment(&func_name),
            );
        };
        if let Some(comment) = route_fallback_comment(semantic_route) {
            return residual_function_for_render_boundary(&func_name, comment);
        }
        if let Some(comment) = render_permission_refusal_comment(
            &func_name,
            decompiler.context.effective_render_permission(),
        ) {
            return residual_function_for_render_boundary(&func_name, &comment);
        }
        if let Some(reason) = summary_only_semantics_standard_render_residual_reason(
            &decompiler.context.function_facts,
        ) {
            return residual_function_for_render_boundary(&func_name, &reason);
        }
        if route_is_summary_boundary(semantic_route) {
            return residual_function_for_summary_route_boundary(&func_name, semantic_route);
        }
        if let Some(reason) =
            render_permission_residual_reason(decompiler.context.effective_render_permission())
        {
            return residual_function_for_render_boundary(&func_name, &reason);
        }
        decompiler.build_function_internal(func, &input.prepared_ssa, semantic_route)
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
        route: &DecompileRouteFacts,
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

    fn build_function_internal(
        &self,
        func: &SSAFunction,
        prepared: &r2ssa::SsaArtifact,
        semantic_route: &DecompileRouteFacts,
    ) -> CFunction {
        // Materialize phis on non-critical edges to reduce SSA artifacts in output.
        let mut normalized_func = normalize::materialize_phis(func);
        if let Some(render_facts) = self.context.function_facts.render() {
            normalize::materialize_certified_loop_carrier_initializers(
                &mut normalized_func,
                prepared,
                render_facts,
            );
        }
        let func = &normalized_func;
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let certified_rendering_required =
            render_permission_allows_executable_c(self.context.effective_render_permission());
        let certified_standard_mode =
            certified_rendering_required && route_is_standard(semantic_route);
        if route_is_standard(semantic_route) && !certified_rendering_required {
            let reason = render_permission_residual_reason(self.context.effective_render_permission())
                .unwrap_or_else(|| {
                    "r2dec residual: Standard executable rendering requires engine-owned CertifiedC permission".to_string()
                });
            return residual_function_for_render_boundary(&func_name, &reason);
        }
        let render_signature = self.context.type_facts().render_authorized_signature();
        if certified_standard_mode {
            let Some(signature) = render_signature else {
                return residual_function_for_render_boundary(
                    &func_name,
                    "r2dec residual: certified Standard header lacks FunctionTypeFacts render-authorized signature",
                );
            };
            if signature.ret_type.is_none() {
                return residual_function_for_render_boundary(
                    &func_name,
                    "r2dec residual: certified Standard header lacks FunctionTypeFacts render-authorized return type",
                );
            }
            if !signature_has_complete_render_param_types(signature) {
                return residual_function_for_render_boundary(
                    &func_name,
                    "r2dec residual: certified Standard header has incomplete FunctionTypeFacts render-authorized parameter types",
                );
            }
            if let Some(reason) = certified_signature_entity_residual_reason(
                signature,
                self.context.function_facts.render_facts(),
                self.config.ptr_size,
            ) {
                return residual_function_for_render_boundary(
                    &func_name,
                    &format!("r2dec residual: {reason}"),
                );
            }
        }
        // Recover variables
        let mut var_recovery = VariableRecovery::new_with_abi(
            &self.config.sp_name,
            &self.config.fp_name,
            self.config.ptr_size,
            self.config.arg_regs.clone(),
            self.config.ret_regs.clone(),
        );
        var_recovery.set_function_facts(&self.context.function_facts);
        var_recovery.recover_prepared(prepared);
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
        let params = if certified_standard_mode {
            params_from_authorized_signature(
                render_signature.expect("certified Standard mode checked render signature"),
            )
        } else {
            merge_params_with_external_signature(
                recovered_param_infos
                    .iter()
                    .map(|(_, param)| param.clone())
                    .collect(),
                render_signature,
            )
        };
        let param_register_aliases = build_param_register_aliases(
            &params,
            &recovered_param_infos,
            &self.context.type_facts().register_params,
            &self.config.arg_regs,
            !certified_standard_mode,
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
        let inferred_ret_type = if certified_standard_mode {
            CType::Unknown
        } else {
            type_inference
                .as_ref()
                .map(|type_inference| self.infer_return_type(func, type_inference))
                .or_else(|| {
                    render_signature.and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                })
                .unwrap_or(CType::Unknown)
        };
        let signature_ret_type =
            render_signature.and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype));
        let fold_function_return_type = if certified_standard_mode {
            signature_ret_type.as_ref()
        } else {
            signature_ret_type.as_ref().or(Some(&inferred_ret_type))
        };
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
                certified_rendering_required,
            })
        });
        let certified_empty_type_hints = HashMap::new();
        let fold_type_hints = if certified_standard_mode {
            &certified_empty_type_hints
        } else {
            &type_hints
        };
        let fold_type_oracle = if certified_standard_mode {
            None
        } else {
            type_oracle
        };
        let fold_inputs = FoldInputs {
            arch: &fold_arch,
            #[cfg(test)]
            function_names: &self.context.function_names,
            #[cfg(test)]
            strings: &self.context.strings,
            #[cfg(test)]
            symbols: &self.context.symbols,
            function_facts: &self.context.function_facts,
            #[cfg(test)]
            certified_rendering_required,
            stack_slots: &self.context.type_facts().stack_slots,
            field_access_certificates: &self.context.type_facts().field_access_certificates,
            #[cfg(test)]
            external_stack_vars: &self.context.type_facts().external_stack_vars,
            visible_bindings: &self.context.type_facts().visible_bindings,
            external_type_db: &self.context.type_facts().external_type_db,
            param_register_aliases: &param_register_aliases,
            type_hints: fold_type_hints,
            type_oracle: fold_type_oracle,
            function_return_type: fold_function_return_type,
            prepared_ssa: Some(prepared),
            prepared_semantic_view: prepared_semantic_view.as_ref(),
            prepared_objects: Some(prepared.objects()),
            prepared_memory: Some(prepared.memory()),
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        fold_ctx.analyze_blocks(&fold_blocks);
        fold_ctx.analyze_function_structure(func);
        if certified_standard_mode {
            fold_ctx.clear_effect_render_proofs();
        }

        // Structure control flow (primary path: folded)
        let mut structurer = ControlFlowStructurer::new(func, &fold_ctx);

        // Get set of variables that survive folding before structuring.
        let emitted_vars = structurer.emitted_var_names();
        let routed_body = if certified_standard_mode && route_is_standard(semantic_route) {
            consumer_structured::RoutedBody {
                body_stmt: structurer.structure_preserving_render_proof_identity(),
                use_conservative_locals: false,
                is_linear_fallback: false,
            }
        } else {
            consumer_structured::primary_body_for_semantic_route(
                semantic_route,
                &mut structurer,
                || self.linearize_function_body(func, &fold_ctx),
            )
        };
        let mut use_conservative_locals = routed_body.use_conservative_locals;
        let mut is_linear_fallback = routed_body.is_linear_fallback;
        let mut body_stmt = routed_body.body_stmt;
        if certified_standard_mode {
            body_stmt = fold_ctx.prune_unproved_register_carriers_in_stmt(body_stmt);
            body_stmt = ControlFlowStructurer::cleanup_preserving_render_proof_identity(body_stmt);
        }
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
        let structuring_proof_failure = certified_standard_mode
            .then(|| structurer.safety_reason().map(str::to_string))
            .flatten();
        if let Some(reason) = structuring_proof_failure.as_deref() {
            body_stmt = CStmt::Comment(format!("r2sleigh residual: {reason}"));
        }

        if !certified_standard_mode
            && route_is_standard(semantic_route)
            && !Self::stmt_has_content(&body_stmt)
        {
            let folded_reason = structurer
                .safety_reason()
                .map(str::to_string)
                .unwrap_or_else(|| "folded structuring produced empty output".to_string());
            let empty_fallback = consumer_fallback::recover_empty_structuring(folded_reason);
            use_conservative_locals = empty_fallback.use_conservative_locals;
            is_linear_fallback = empty_fallback.is_linear_fallback;
            body_stmt = empty_fallback.body_stmt;
            control_render_proofs.clear();
            effect_render_proofs.clear();
        }

        if !certified_standard_mode && route_is_standard(semantic_route) {
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
        let mut locals: Vec<ast::CLocal> = if use_conservative_locals {
            var_recovery
                .locals()
                .iter()
                .filter(|v| {
                    let not_param_home = !v
                        .stack_offset
                        .is_some_and(|offset| param_home_offsets.contains(&offset));
                    if certified_standard_mode {
                        not_param_home
                            && certified_recovered_stack_local_is_exact(
                                &self.context.function_facts,
                                &emitted_vars,
                                &body_visible_names,
                                &v.name,
                                v.stack_offset,
                            )
                    } else {
                        not_param_home
                    }
                })
                .map(|v| ast::CLocal {
                    ty: if certified_standard_mode {
                        v.stack_offset
                            .and_then(|offset| {
                                typed_stack_local_type_for_name_offset(
                                    self.context.type_facts(),
                                    &v.name,
                                    offset,
                                )
                            })
                            .unwrap_or(CType::Unknown)
                    } else {
                        choose_more_specific_runtime_type(
                            type_inference
                                .as_ref()
                                .map(|type_inference| {
                                    type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                                })
                                .unwrap_or_else(|| v.ty.clone()),
                            runtime_type_hint_for_name(&type_hints, &v.name),
                        )
                    },
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
                    if certified_standard_mode {
                        not_param_home
                            && certified_recovered_stack_local_is_exact(
                                &self.context.function_facts,
                                &emitted_vars,
                                &body_visible_names,
                                &v.name,
                                v.stack_offset,
                            )
                    } else {
                        not_param_home
                            && (emitted_vars.contains(&v.name)
                                || body_visible_names.contains(&v.name)
                                || v.stack_offset.is_some_and(|offset| {
                                    body_visible_stack_offsets.contains(&offset)
                                }))
                    }
                })
                .map(|v| ast::CLocal {
                    ty: if certified_standard_mode {
                        v.stack_offset
                            .and_then(|offset| {
                                typed_stack_local_type_for_name_offset(
                                    self.context.type_facts(),
                                    &v.name,
                                    offset,
                                )
                            })
                            .unwrap_or(CType::Unknown)
                    } else {
                        choose_more_specific_runtime_type(
                            type_inference
                                .as_ref()
                                .map(|type_inference| {
                                    type_like_to_ctype(&type_inference.get_type(&v.ssa_var))
                                })
                                .unwrap_or_else(|| v.ty.clone()),
                            runtime_type_hint_for_name(&type_hints, &v.name),
                        )
                    },
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
        if certified_standard_mode && let Some(render_facts) = self.context.function_facts.render()
        {
            let mut existing_names = params
                .iter()
                .map(|param| param.name.to_ascii_lowercase())
                .chain(locals.iter().map(|local| local.name.to_ascii_lowercase()))
                .collect::<BTreeSet<_>>();
            for entity in render_facts.loop_carriers() {
                let r2types::CertifiedEntity::LoopCarrier { phi, width, ty, .. } = entity else {
                    continue;
                };
                let name = certified_loop_carrier_name(*phi);
                if !existing_names.insert(name.to_ascii_lowercase()) {
                    continue;
                }
                locals.push(ast::CLocal {
                    ty: ty
                        .as_ref()
                        .map(type_like_to_ctype)
                        .unwrap_or_else(|| match width {
                            0 => CType::Unknown,
                            width => CType::Int(width.saturating_mul(8)),
                        }),
                    name,
                    stack_offset: None,
                });
            }
            for effect in render_facts.certified_effects.values() {
                let r2types::CertifiedEffect::Memory { fact, .. } = effect else {
                    continue;
                };
                if fact.is_write
                    || fact.value.is_none()
                    || fact.width == 0
                    || !fact.materialize_result
                {
                    continue;
                }
                let name = certified_memory_result_name(fact.access);
                if !existing_names.insert(name.to_ascii_lowercase()) {
                    continue;
                }
                locals.push(ast::CLocal {
                    ty: CType::UInt(fact.width.saturating_mul(8)),
                    name,
                    stack_offset: None,
                });
            }
        }

        let mut c_function = CFunction {
            name: func_name,
            ret_type: if certified_standard_mode {
                signature_ret_type
                    .clone()
                    .expect("certified Standard mode checked render return type")
            } else {
                render_signature
                    .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                    .unwrap_or_else(|| inferred_ret_type.clone())
            },
            params,
            locals,
            body,
        };
        if !certified_standard_mode
            && route_is_standard(semantic_route)
            && !matches!(c_function.ret_type, CType::Void | CType::Unknown)
            && !c_function.body.iter().any(summary_stmt_contains_return)
            && let Some(expr) = fold_ctx.unique_scalar_stack_return_expr()
        {
            c_function.body.push(CStmt::Return(Some(expr)));
        }
        if certified_standard_mode
            && route_is_standard(semantic_route)
            && structuring_proof_failure.is_none()
            && !matches!(c_function.ret_type, CType::Void | CType::Unknown)
            && !c_function.body.iter().any(summary_stmt_contains_return)
        {
            let unique_return_expr = fold_ctx.unique_scalar_stack_return_expr().or_else(|| {
                let mut rendered_returns = self
                    .context
                    .function_facts
                    .render()
                    .into_iter()
                    .flat_map(r2types::FunctionRenderFacts::return_effects)
                    .filter_map(|fact| {
                        fold_ctx
                            .certified_return_expr_for_op(fact.block_addr, fact.op_index)
                            .map(|(expr, value)| {
                                (
                                    normalize_certified_appended_return_expr(
                                        expr,
                                        &c_function.ret_type,
                                        &c_function.locals,
                                    ),
                                    fact.block_addr,
                                    fact.op_index,
                                    value,
                                )
                            })
                    })
                    .collect::<Vec<_>>();
                rendered_returns
                    .sort_by_key(|(_, block_addr, op_idx, value)| (*block_addr, *op_idx, *value));
                let mut groups = Vec::<(CExpr, usize)>::new();
                for (expr, _, _, _) in &rendered_returns {
                    if let Some((_, count)) =
                        groups.iter_mut().find(|(candidate, _)| candidate == expr)
                    {
                        *count += 1;
                    } else {
                        groups.push((expr.clone(), 1));
                    }
                }
                let max_count = groups.iter().map(|(_, count)| *count).max()?;
                let mut winners = groups
                    .into_iter()
                    .filter(|(_, count)| *count == max_count)
                    .collect::<Vec<_>>();
                (winners.len() == 1 && (max_count > 1 || rendered_returns.len() == 1))
                    .then(|| winners.remove(0).0)
            });
            if let Some(expr) = unique_return_expr {
                let mut rendered_returns = self
                    .context
                    .function_facts
                    .render()
                    .into_iter()
                    .flat_map(r2types::FunctionRenderFacts::return_effects)
                    .filter_map(|fact| {
                        fold_ctx
                            .certified_return_expr_for_op(fact.block_addr, fact.op_index)
                            .map(|(rendered, value)| {
                                (
                                    normalize_certified_appended_return_expr(
                                        rendered,
                                        &c_function.ret_type,
                                        &c_function.locals,
                                    ),
                                    fact.block_addr,
                                    fact.op_index,
                                    value,
                                )
                            })
                    })
                    .filter(|(rendered, _, _, _)| rendered == &expr)
                    .collect::<Vec<_>>();
                rendered_returns
                    .sort_by_key(|(_, block_addr, op_idx, value)| (*block_addr, *op_idx, *value));
                if let Some((_, block_addr, op_idx, value)) = rendered_returns.first().cloned() {
                    c_function.body.push(CStmt::Return(Some(expr)));
                    effect_render_proofs.push(EffectRenderProof {
                        kind: EffectRenderProofKind::Return,
                        block_addr,
                        op_idx,
                        call_disposition: None,
                        target: None,
                        address: None,
                        value: Some(value),
                        values: Vec::new(),
                        materialized_phi_copy: false,
                    });
                }
            }
        }
        if !certified_standard_mode && route_is_standard(semantic_route) {
            fold_ctx.prune_duplicate_call_statements_by_source(&mut c_function.body);
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
            for name in self.context.type_facts().known_function_signatures.keys() {
                known_function_names.insert(name.to_ascii_lowercase());
            }
            post_rename::rewrite_function_identifiers(&mut c_function, &known_function_names);
        }
        if !certified_standard_mode {
            rewrite_stack_synonym_uses_to_declared_locals(&mut c_function, &fold_ctx);
            prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx);
        }
        prune_unused_pure_locals(&mut c_function);
        prune_unreferenced_local_declarations(&mut c_function);
        normalize_redundant_return_carrier_casts(&mut c_function);
        normalize_declared_assignment_literals(&mut c_function);
        if route_is_standard(semantic_route) {
            let residual_reason =
                render_permission_residual_reason(self.context.effective_render_permission())
                    .or_else(|| {
                        route_is_standard(semantic_route).then(|| {
                            certified_standard_output_residual_reason_with_effect_proofs(
                                prepared,
                                &self.context.function_facts,
                                &c_function,
                                certified_standard_mode.then_some(effect_render_proofs.as_slice()),
                            )
                        })?
                    })
                    .or_else(|| {
                        certifying_render_residual_reason_with_proofs(
                            Some(prepared),
                            self.context.function_facts.control(),
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

fn normalize_certified_appended_return_expr(
    expr: CExpr,
    ret_type: &CType,
    locals: &[ast::CLocal],
) -> CExpr {
    let CExpr::Cast { ty, expr: inner } = expr else {
        return expr;
    };
    if let CExpr::Var(name) = inner.as_ref()
        && locals
            .iter()
            .any(|local| local.name.eq_ignore_ascii_case(name) && local.ty == *ret_type)
    {
        return *inner;
    }
    CExpr::Cast { ty, expr: inner }
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

fn normalize_literal_for_declared_type(expr: &mut CExpr, ty: &CType) {
    let (is_signed, bits) = match ty {
        CType::Int(bits) => (true, *bits),
        CType::UInt(bits) => (false, *bits),
        CType::Bool => (false, 1),
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
            CStmt::Return(Some(expr)) => visit_expr(expr, declared_types),
            CStmt::Empty
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

    let type_hints = std::collections::HashMap::new();
    #[cfg(test)]
    let function_names = std::collections::HashMap::new();
    #[cfg(test)]
    let strings = std::collections::HashMap::new();
    #[cfg(test)]
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
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::SSAFunction;
    use r2types::{
        ArrayIndexBase, ArrayIndexCertificate, ExternalField, ExternalRegisterParamSpec,
        ExternalStackBase, ExternalStackSlotRole, ExternalStackSlotSpec, ExternalStruct,
        ExternalTypeDb, FieldAccessCertificate, FunctionFacts, FunctionParamSpec,
        FunctionRenderFacts, FunctionSignatureSpec, FunctionTypeFacts, ParamSlotResolver,
        SignatureCertificate, SignatureCertificateSource, Signedness,
    };
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    fn test_stack_render_facts(
        object: r2ssa::ObjectId,
        base: r2ssa::StackAddressBase,
        offset: i64,
    ) -> FunctionRenderFacts {
        let id = r2ssa::SemanticId::stack_slot(object);
        FunctionRenderFacts {
            certified_entities: BTreeMap::from([(
                id,
                r2types::CertifiedEntity::StackSlot {
                    id,
                    object,
                    base,
                    offset,
                    size: None,
                },
            )]),
            ..FunctionRenderFacts::default()
        }
    }

    #[test]
    fn definite_assignment_rejects_partial_branch_initialization() {
        let mut function = CFunction::new("unlock", CType::i32());
        function.locals.push(crate::ast::CLocal {
            ty: CType::i32(),
            name: "result".to_string(),
            stack_offset: Some(-4),
        });
        function.body = vec![
            CStmt::If {
                cond: CExpr::Var("condition".to_string()),
                then_body: Box::new(CStmt::Expr(CExpr::assign(
                    CExpr::Var("result".to_string()),
                    CExpr::IntLit(1),
                ))),
                else_body: None,
            },
            CStmt::Return(Some(CExpr::Var("result".to_string()))),
        ];

        assert!(
            definite_assignment_residual_reason(&function)
                .is_some_and(|reason| reason.contains("result may be read before assignment"))
        );
    }

    #[test]
    fn definite_assignment_accepts_complete_branch_initialization() {
        let mut function = CFunction::new("unlock", CType::i32());
        function.locals.push(crate::ast::CLocal {
            ty: CType::i32(),
            name: "result".to_string(),
            stack_offset: Some(-4),
        });
        let assignment = |value| {
            CStmt::Expr(CExpr::assign(
                CExpr::Var("result".to_string()),
                CExpr::IntLit(value),
            ))
        };
        function.body = vec![
            CStmt::If {
                cond: CExpr::Var("condition".to_string()),
                then_body: Box::new(assignment(1)),
                else_body: Some(Box::new(assignment(0))),
            },
            CStmt::Return(Some(CExpr::Var("result".to_string()))),
        ];

        assert_eq!(definite_assignment_residual_reason(&function), None);
    }

    fn x86_64_param_slot_resolver() -> ParamSlotResolver {
        ParamSlotResolver::from_arg_regs(DecompilerConfig::x86_64().arg_regs)
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

    #[test]
    fn certified_source_aliases_normalize_strength_reduced_array_member_address() {
        let arch = FoldArchConfig {
            ptr_size: 64,
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
        };
        let signature = FunctionSignatureSpec {
            ret_type: Some(ctype_to_type_like(&CType::i32())),
            params: vec![
                FunctionParamSpec {
                    name: "arr".to_string(),
                    ty: Some(ctype_to_type_like(&CType::ptr(CType::Struct(
                        "DemoStruct".to_string(),
                    )))),
                },
                FunctionParamSpec {
                    name: "idx".to_string(),
                    ty: Some(ctype_to_type_like(&CType::i32())),
                },
                FunctionParamSpec {
                    name: "v".to_string(),
                    ty: Some(ctype_to_type_like(&CType::i32())),
                },
            ],
        };
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(signature.clone()),
            register_params: vec![ExternalRegisterParamSpec {
                name: "arr".to_string(),
                ty: Some(ctype_to_type_like(&CType::ptr(CType::Struct(
                    "DemoStruct".to_string(),
                )))),
                reg: "rdi".to_string(),
            }],
            signature_certificate: SignatureCertificate::from_signature(
                &signature,
                [SignatureCertificateSource::ExternalContext],
            ),
            ..Default::default()
        };
        let function_facts =
            FunctionFacts::new(type_facts, None).with_decompile_route(test_decompile_route(
                r2types::DecompileRouteKind::Standard,
                "certified source alias normalization",
                None,
                r2sym::RenderPermission::certified(
                    r2sym::ProofOwner::R2engine,
                    "certified source alias normalization",
                ),
            ));
        let mut param_register_aliases = HashMap::new();
        param_register_aliases.insert("rdi".to_string(), "arr".to_string());
        param_register_aliases.insert("edi".to_string(), "arr".to_string());
        let type_hints = HashMap::new();
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let symbols = HashMap::new();
        let stack_slots = BTreeMap::new();
        let external_stack_vars = HashMap::new();
        let visible_bindings = Vec::new();
        let external_type_db = ExternalTypeDb::default();
        let mut ctx = FoldingContext::from_inputs(FoldInputs {
            arch: &arch,
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            function_facts: &function_facts,
            certified_rendering_required: true,
            stack_slots: &stack_slots,
            field_access_certificates: &[],
            external_stack_vars: &external_stack_vars,
            visible_bindings: &visible_bindings,
            external_type_db: &external_type_db,
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
        });
        ctx.set_type_hints(type_hints.clone());
        let idx_times_56 = CExpr::binary(
            BinaryOp::Shl,
            CExpr::binary(
                BinaryOp::Sub,
                CExpr::binary(BinaryOp::Shl, CExpr::var("idx"), CExpr::int(3)),
                CExpr::var("idx"),
            ),
            CExpr::int(3),
        );
        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::binary(BinaryOp::Add, idx_times_56, CExpr::var("arr")),
            CExpr::int(8),
        );

        assert_eq!(
            ctx.debug_ssa_var_for_visible_name("arr"),
            Some(r2ssa::SSAVar::new("rdi", 0, 64))
        );
        assert_eq!(
            ctx.debug_ssa_var_for_visible_name("idx"),
            Some(r2ssa::SSAVar::new("rsi", 0, 64))
        );
        let canonical = ctx.debug_canonicalize_visible_address_expr(&expr);
        let addr = ctx
            .debug_normalized_addr_from_visible_expr(&canonical)
            .expect("strength-reduced array member address should normalize");

        match addr.base {
            analysis::BaseRef::Value(base) => {
                assert_eq!(base.var, r2ssa::SSAVar::new("rdi", 0, 64));
            }
            other => panic!("expected arr base, got {other:?}"),
        }
        let index = addr.index.expect("array index");
        assert_eq!(index.var, r2ssa::SSAVar::new("rsi", 0, 64));
        assert_eq!(addr.scale_bytes, 56);
        assert_eq!(addr.offset_bytes, 8);
    }

    fn test_decompile_route(
        kind: r2types::DecompileRouteKind,
        reason: &str,
        fallback_comment: Option<String>,
        render_permission: r2sym::RenderPermission,
    ) -> r2types::DecompileRouteFacts {
        r2types::DecompileRouteFacts {
            kind,
            reason: Some(reason.to_string()),
            fallback_comment,
            skip_runtime_type_inference: !matches!(kind, r2types::DecompileRouteKind::Standard),
            use_prepared_semantic_view: matches!(kind, r2types::DecompileRouteKind::Standard),
            proof_coverage: r2sym::ProofCoverage::default(),
            render_permission,
        }
    }

    fn test_summary_decompile_route(
        kind: r2types::DecompileRouteKind,
        reason: &str,
    ) -> r2types::DecompileRouteFacts {
        test_decompile_route(
            kind,
            reason,
            None,
            r2sym::RenderPermission::summary(r2sym::ProofOwner::R2engine, reason),
        )
    }

    fn render_semantic_worker_summary(
        func_name: &str,
        function_facts: &FunctionFacts,
        route: &r2types::DecompileRouteFacts,
        config: DecompilerConfig,
    ) -> Option<String> {
        let function_facts = function_facts.clone().with_decompile_route(route.clone());
        super::render_semantic_worker_summary(func_name, &function_facts, config)
    }

    #[test]
    fn standard_certified_c_requires_r2engine_proof_owner() {
        let arch = test_arch_for_decompile();
        let ops = vec![
            R2ILOp::Copy {
                dst: Varnode::register(0x00, 8),
                src: Varnode::constant(7, 8),
            },
            R2ILOp::Return {
                target: Varnode::register(0x00, 8),
            },
        ];
        let prepared = prepared_from_ops(ops, &arch);
        let route = test_decompile_route(
            r2types::DecompileRouteKind::Standard,
            "non-engine certified fixture",
            None,
            r2sym::RenderPermission::certified(
                r2sym::ProofOwner::R2sym,
                "non-engine certified fixture",
            ),
        );
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), None).with_decompile_route(route);
        let input = DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        );
        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert!(
            output.contains("CertifiedC render permission from non-engine proof owner R2sym"),
            "wrong-owner CertifiedC must residualize before executable Standard rendering, got:\n{output}"
        );
        assert!(
            !output.contains("return 7;"),
            "wrong-owner CertifiedC must not emit executable C, got:\n{output}"
        );
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
        r2ssa::SsaArtifact::for_decompile(&[block], Some(arch))
            .expect("prepared SSA should build")
            .with_name("stable_demo")
    }

    fn prepared_standard_input_with_type_facts(
        prepared: r2ssa::SsaArtifact,
        type_facts: FunctionTypeFacts,
        reason: &str,
    ) -> DecompilerInput {
        let mut function_facts =
            FunctionFacts::new(type_facts, None).with_decompile_route(test_decompile_route(
                r2types::DecompileRouteKind::Standard,
                reason,
                None,
                r2sym::RenderPermission::certified(r2sym::ProofOwner::R2engine, reason),
            ));
        function_facts.attach_prepared_decompile_evidence(&prepared);
        function_facts.normalize_field_certificates_from_external_layout();
        function_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_64_param_slot_resolver(),
        );
        function_facts.populate_array_access_render_facts_from_scalar_candidates(
            &prepared,
            &x86_64_param_slot_resolver(),
        );
        function_facts.populate_certified_parameter_exprs(&prepared, &x86_64_param_slot_resolver());
        DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        )
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

    fn test_function_facts_with_prepared_render(prepared: &r2ssa::SsaArtifact) -> FunctionFacts {
        FunctionFacts::new(FunctionTypeFacts::default(), None)
            .with_callsites(test_callsite_facts(prepared))
            .with_call_results(test_call_result_facts(prepared))
            .with_call_render(test_call_render_facts(prepared))
            .with_render(test_render_facts(prepared))
    }

    fn test_callsite_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionCallsiteFacts {
        let by_callsite = prepared
            .certificates()
            .callsites
            .values()
            .filter_map(|cert| {
                let (block_addr, op_index) = prepared.inst_op_site(cert.at)?;
                let callsite = r2types::CallsiteKey {
                    block_addr,
                    op_index,
                };
                Some((
                    callsite,
                    r2types::CallsiteArgumentFacts {
                        callsite,
                        call_site_id: cert.call_site,
                        at: cert.at,
                        target: cert.target,
                        direct_target: cert.direct_target,
                        argument_values: cert
                            .argument_values
                            .iter()
                            .copied()
                            .enumerate()
                            .map(|(index, value)| r2types::CallArgumentValueFact { index, value })
                            .collect(),
                        register_argument_locations: Vec::new(),
                        stack_argument_locations: Vec::new(),
                    },
                ))
            })
            .collect();
        r2types::FunctionCallsiteFacts { by_callsite }
    }

    fn test_call_result_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionCallResultFacts {
        let mut by_value = BTreeMap::new();
        let mut by_callsite = BTreeMap::<r2types::CallsiteKey, Vec<r2ssa::ValueId>>::new();
        for cert in prepared.certificates().call_results.values() {
            let Some(callsite_cert) = prepared.certificates().callsites.get(&cert.call_site) else {
                continue;
            };
            let callsite = r2types::CallsiteKey {
                block_addr: callsite_cert.block_addr,
                op_index: callsite_cert.op_index,
            };
            by_callsite.entry(callsite).or_default().push(cert.value);
            by_value.insert(
                cert.value,
                r2types::CallResultFact {
                    callsite,
                    call_site_id: cert.call_site,
                    at: cert.at,
                    value: cert.value,
                    width: cert.width,
                    relation: cert.relation,
                    carrier: cert.carrier.clone(),
                    owner: cert.owner.clone(),
                },
            );
        }
        r2types::FunctionCallResultFacts {
            by_value,
            by_callsite,
        }
    }

    fn test_call_render_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionCallRenderFacts {
        let call_results = test_call_result_facts(prepared);
        let by_callsite = prepared
            .certificates()
            .callsites
            .values()
            .map(|cert| {
                let callsite = r2types::CallsiteKey {
                    block_addr: cert.block_addr,
                    op_index: cert.op_index,
                };
                let disposition = if call_results
                    .results_for_site(callsite)
                    .any(|result| matches!(result.owner, Some(r2ssa::ValueOwner::StackSlot { .. })))
                {
                    r2types::CallsiteRenderDisposition::AssignedResult
                } else {
                    r2types::CallsiteRenderDisposition::SideEffectStatement
                };
                (
                    callsite,
                    r2types::CallsiteRenderFact {
                        callsite,
                        target: Some(cert.target),
                        disposition,
                        proof_values: cert.argument_values.clone(),
                        residual_reason: None,
                    },
                )
            })
            .collect();
        r2types::FunctionCallRenderFacts { by_callsite }
    }

    fn test_render_facts(prepared: &r2ssa::SsaArtifact) -> r2types::FunctionRenderFacts {
        r2types::FunctionRenderFacts::from_prepared(prepared)
    }

    struct TestMemberRenderFact<'a> {
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        field_name: &'a str,
        field_offset: u64,
        access_width: u32,
    }

    struct TestArrayRenderFact {
        block_addr: u64,
        op_index: usize,
        is_write: bool,
        field_offset: u64,
        element_stride: u64,
        access_width: u32,
    }

    fn add_member_render_fact(
        function_facts: &mut FunctionFacts,
        prepared: &r2ssa::SsaArtifact,
        fact: TestMemberRenderFact<'_>,
    ) {
        let cert = prepared
            .memory_certificate_for_op_site(fact.block_addr, fact.op_index, fact.is_write)
            .expect("prepared memory certificate for member render fact");
        function_facts
            .__test_render_facts_mut()
            .member_accesses_by_op
            .entry((fact.block_addr, fact.op_index, fact.is_write))
            .or_default()
            .push(r2types::MemberAccessRenderFact {
                access: cert.access,
                block_addr: fact.block_addr,
                op_index: fact.op_index,
                object: cert.object,
                is_write: fact.is_write,
                field_offset: fact.field_offset,
                field_name: fact.field_name.to_string(),
                access_width: fact.access_width,
            });
    }

    fn add_array_render_fact(
        function_facts: &mut FunctionFacts,
        prepared: &r2ssa::SsaArtifact,
        fact: TestArrayRenderFact,
    ) {
        let cert = prepared
            .memory_certificate_for_op_site(fact.block_addr, fact.op_index, fact.is_write)
            .expect("prepared memory certificate for array render fact");
        function_facts
            .__test_render_facts_mut()
            .array_accesses_by_op
            .entry((fact.block_addr, fact.op_index, fact.is_write))
            .or_default()
            .push(r2types::ArrayAccessRenderFact {
                access: cert.access,
                block_addr: fact.block_addr,
                op_index: fact.op_index,
                object: cert.object,
                is_write: fact.is_write,
                field_offset: fact.field_offset,
                element_stride: fact.element_stride,
                access_width: fact.access_width,
            });
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

    fn straightline_cfg_summary() -> r2ssa::CFGRiskSummary {
        r2ssa::CFGRiskSummary {
            block_count: 1,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
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
        let reason = certifying_render_residual_reason(None, None, &loop_cfg_summary(), &func)
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
                branches: 0,
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
                branches: 0,
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
                branches: 0,
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
    fn standard_structured_output_refuses_branch_without_function_facts_predicate() {
        let func = CFunction::new("spurious_if", CType::u64()).with_body(vec![CStmt::if_stmt(
            CExpr::var("cond"),
            CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            None,
        )]);
        let inventory = ControlCertificateInventory {
            branches: Vec::new(),
            loops: Vec::new(),
            switches: Vec::new(),
        };
        let cfg = r2ssa::CFGRiskSummary {
            block_count: 2,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(&func, Some(&[]));

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &cfg,
            &nodes,
            &proof_failures,
        )
        .expect("rendered if without FunctionFacts branch proof must residualize");

        assert!(reason.contains("branch node stmt:0"), "{reason}");
        assert!(reason.contains("lacks render proof identity"), "{reason}");
        assert!(
            reason.contains("with only 0 FunctionFacts branch predicate"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_accepts_exact_function_facts_branch_predicate() {
        let func = CFunction::new("certified_if", CType::u64()).with_body(vec![CStmt::if_stmt(
            CExpr::var("cond"),
            CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            None,
        )]);
        let inventory = ControlCertificateInventory {
            branches: vec![BranchCertificateSummary {
                anchor: 0x401000,
                proof_node: "FunctionFacts.branch_predicate:PredicateId(7)".to_string(),
                condition: r2ssa::PredicateId(7),
                condition_value: r2ssa::ValueId(11),
                true_target: 0x401010,
                false_target: 0x401020,
            }],
            loops: Vec::new(),
            switches: Vec::new(),
        };
        let cfg = r2ssa::CFGRiskSummary {
            block_count: 3,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Branch,
                anchor: 0x401000,
                branch_condition: Some(r2ssa::PredicateId(7)),
                branch_condition_value: Some(r2ssa::ValueId(11)),
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &cfg,
            &nodes,
            &proof_failures,
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn standard_structured_output_refuses_branch_predicate_value_mismatch() {
        let func =
            CFunction::new("bad_if_predicate", CType::u64()).with_body(vec![CStmt::if_stmt(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
                None,
            )]);
        let inventory = ControlCertificateInventory {
            branches: vec![BranchCertificateSummary {
                anchor: 0x401000,
                proof_node: "FunctionFacts.branch_predicate:PredicateId(7)".to_string(),
                condition: r2ssa::PredicateId(7),
                condition_value: r2ssa::ValueId(11),
                true_target: 0x401010,
                false_target: 0x401020,
            }],
            loops: Vec::new(),
            switches: Vec::new(),
        };
        let cfg = r2ssa::CFGRiskSummary {
            block_count: 3,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Branch,
                anchor: 0x401000,
                branch_condition: Some(r2ssa::PredicateId(8)),
                branch_condition_value: Some(r2ssa::ValueId(12)),
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );

        let reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &cfg,
            &nodes,
            &proof_failures,
        )
        .expect("branch predicate mismatch must residualize");

        assert!(reason.contains("branch node stmt:0"), "{reason}");
        assert!(
            reason.contains("predicate proof Some(PredicateId(8))"),
            "{reason}"
        );
        assert!(
            reason.contains("condition value proof Some(ValueId(12))"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_loop_without_function_facts_loop_structure() {
        let prepared = prepared_from_ops(Vec::new(), &test_arch_for_decompile());
        let func =
            CFunction::new("uncertified_loop", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let (nodes, proof_failures) = function_control_render_nodes_with_proofs(
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Loop,
                anchor: 0x401000,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: Some(r2ssa::PredicateId(1)),
                loop_condition_value: Some(r2ssa::ValueId(10)),
                loop_body_blocks: vec![0x401000, 0x401010],
                loop_latches: vec![0x401010],
                loop_exits: vec![0x401020],
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );
        let inventory = control_certificate_inventory(None);

        let direct_reason = structured_control_residual_reason_for_nodes(
            Some(&inventory),
            &loop_cfg_summary(),
            &nodes,
            &proof_failures,
        )
        .expect("rendered loop without FunctionFacts loop proof must residualize");
        let route_reason = certifying_render_residual_reason_with_proofs(
            Some(&prepared),
            None,
            &loop_cfg_summary(),
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Loop,
                anchor: 0x401000,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: Some(r2ssa::PredicateId(1)),
                loop_condition_value: Some(r2ssa::ValueId(10)),
                loop_body_blocks: vec![0x401000, 0x401010],
                loop_latches: vec![0x401010],
                loop_exits: vec![0x401020],
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        )
        .expect("certified route must not recover loop proof from prepared SSA side channels");

        assert!(
            direct_reason.contains("with only 0 LoopCertificate"),
            "{direct_reason}"
        );
        assert!(
            route_reason.contains("with only 0 LoopCertificate"),
            "{route_reason}"
        );
    }

    #[test]
    fn standard_structured_output_accepts_exact_function_facts_loop_structure() {
        let prepared = prepared_from_ops(Vec::new(), &test_arch_for_decompile());
        let func =
            CFunction::new("certified_loop", CType::u64()).with_body(vec![CStmt::while_loop(
                CExpr::var("cond"),
                CStmt::expr(CExpr::assign(CExpr::var("acc"), CExpr::uint(1))),
            )]);
        let control = r2types::FunctionControlFacts {
            loops: BTreeMap::from([(
                r2ssa::LoopId(1),
                r2types::LoopStructureFact {
                    loop_id: r2ssa::LoopId(1),
                    proof_node: r2ssa::ProofNodeId::loop_certificate(0x401000, r2ssa::LoopId(1))
                        .to_string(),
                    header: 0x401000,
                    condition: Some(r2ssa::PredicateId(1)),
                    condition_value: Some(r2ssa::ValueId(10)),
                    body: vec![0x401000, 0x401010],
                    latches: vec![0x401010],
                    exits: vec![0x401020],
                },
            )]),
            ..r2types::FunctionControlFacts::default()
        };

        let reason = certifying_render_residual_reason_with_proofs(
            Some(&prepared),
            Some(&control),
            &loop_cfg_summary(),
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Loop,
                anchor: 0x401000,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: Some(r2ssa::PredicateId(1)),
                loop_condition_value: Some(r2ssa::ValueId(10)),
                loop_body_blocks: vec![0x401000, 0x401010],
                loop_latches: vec![0x401010],
                loop_exits: vec![0x401020],
                switch_selector: None,
                switch_cases: Vec::new(),
                switch_default: None,
            }]),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn standard_structured_output_refuses_switch_without_function_facts_selector() {
        let prepared = prepared_from_ops(Vec::new(), &test_arch_for_decompile());
        let func =
            CFunction::new("uncertified_switch", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![ast::SwitchCase {
                    value: CExpr::uint(0),
                    body: vec![CStmt::Break],
                }],
                default: None,
            }]);

        let reason = certifying_render_residual_reason_with_proofs(
            Some(&prepared),
            None,
            &switch_cfg_summary(),
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Switch,
                anchor: 0x401020,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: Some(r2ssa::ValueId(7)),
                switch_cases: vec![(0, 0x401100)],
                switch_default: None,
            }]),
        )
        .expect("rendered switch without FunctionFacts selector proof must residualize");

        assert!(reason.contains("with only 0 SwitchCertificate"), "{reason}");
    }

    #[test]
    fn standard_structured_output_accepts_exact_function_facts_switch_selector() {
        let prepared = prepared_from_ops(Vec::new(), &test_arch_for_decompile());
        let func =
            CFunction::new("certified_switch", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![ast::SwitchCase {
                    value: CExpr::uint(0),
                    body: vec![CStmt::Return(Some(CExpr::uint(0)))],
                }],
                default: None,
            }]);
        let control = r2types::FunctionControlFacts {
            switches: BTreeMap::from([(
                0x401020,
                r2types::SwitchSelectorFact {
                    proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                    block_addr: 0x401020,
                    selector: Some(r2ssa::ValueId(7)),
                    cases: vec![(0, 0x401100)],
                    default: None,
                },
            )]),
            ..r2types::FunctionControlFacts::default()
        };

        let reason = certifying_render_residual_reason_with_proofs(
            Some(&prepared),
            Some(&control),
            &switch_cfg_summary(),
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Switch,
                anchor: 0x401020,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: Some(r2ssa::ValueId(7)),
                switch_cases: vec![(0, 0x401100)],
                switch_default: None,
            }]),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn standard_structured_output_refuses_unproved_switch_case_break() {
        let prepared = prepared_from_ops(Vec::new(), &test_arch_for_decompile());
        let control = r2types::FunctionControlFacts {
            switches: BTreeMap::from([(
                0x401020,
                r2types::SwitchSelectorFact {
                    proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                    block_addr: 0x401020,
                    selector: Some(r2ssa::ValueId(7)),
                    cases: vec![(0, 0x401100)],
                    default: None,
                },
            )]),
            ..r2types::FunctionControlFacts::default()
        };
        let func = CFunction::new("case_break", CType::u64()).with_body(vec![CStmt::Switch {
            expr: CExpr::var("sel"),
            cases: vec![ast::SwitchCase {
                value: CExpr::uint(0),
                body: vec![CStmt::Break],
            }],
            default: None,
        }]);

        let reason = certifying_render_residual_reason_with_proofs(
            Some(&prepared),
            Some(&control),
            &switch_cfg_summary(),
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Switch,
                anchor: 0x401020,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: Some(r2ssa::ValueId(7)),
                switch_cases: vec![(0, 0x401100)],
                switch_default: None,
            }]),
        )
        .expect("case break without case-exit proof must residualize");

        assert!(
            reason.contains("unproved control transfer break"),
            "{reason}"
        );
    }

    #[test]
    fn standard_structured_output_refuses_unproved_continue_and_goto() {
        for (stmt, expected) in [
            (CStmt::Continue, "unproved control transfer continue"),
            (
                CStmt::Goto("block_401000".to_string()),
                "unproved control transfer goto",
            ),
        ] {
            let func = CFunction::new("unproved_transfer", CType::u64()).with_body(vec![stmt]);

            let reason = certifying_render_residual_reason_with_proofs(
                None,
                None,
                &straightline_cfg_summary(),
                &func,
                Some(&[]),
            )
            .expect("unproved control transfer must residualize");

            assert!(reason.contains(expected), "{reason}");
        }
    }

    #[test]
    fn standard_structured_output_refuses_implicit_switch_case_fallthrough() {
        let prepared = prepared_from_ops(Vec::new(), &test_arch_for_decompile());
        let control = r2types::FunctionControlFacts {
            switches: BTreeMap::from([(
                0x401020,
                r2types::SwitchSelectorFact {
                    proof_node: r2ssa::ProofNodeId::switch_certificate(0x401020).to_string(),
                    block_addr: 0x401020,
                    selector: Some(r2ssa::ValueId(7)),
                    cases: vec![(0, 0x401100)],
                    default: None,
                },
            )]),
            ..r2types::FunctionControlFacts::default()
        };
        let func =
            CFunction::new("case_fallthrough", CType::u64()).with_body(vec![CStmt::Switch {
                expr: CExpr::var("sel"),
                cases: vec![ast::SwitchCase {
                    value: CExpr::uint(0),
                    body: vec![CStmt::expr(CExpr::assign(CExpr::var("x"), CExpr::uint(1)))],
                }],
                default: None,
            }]);

        let reason = certifying_render_residual_reason_with_proofs(
            Some(&prepared),
            Some(&control),
            &switch_cfg_summary(),
            &func,
            Some(&[ControlRenderProof {
                kind: ControlRenderProofKind::Switch,
                anchor: 0x401020,
                branch_condition: None,
                branch_condition_value: None,
                loop_condition: None,
                loop_condition_value: None,
                loop_body_blocks: Vec::new(),
                loop_latches: Vec::new(),
                loop_exits: Vec::new(),
                switch_selector: Some(r2ssa::ValueId(7)),
                switch_cases: vec![(0, 0x401100)],
                switch_default: None,
            }]),
        )
        .expect("implicit switch fallthrough without exact case-exit proof must residualize");

        assert!(
            reason.contains("unproved switch case fallthrough"),
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
            branches: Vec::new(),
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
            branches: Vec::new(),
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
            branches: Vec::new(),
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
                branch_condition: None,
                branch_condition_value: None,
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
            branches: Vec::new(),
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
            branches: Vec::new(),
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
                branch_condition: None,
                branch_condition_value: None,
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
            branches: Vec::new(),
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
            branches: Vec::new(),
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
                branch_condition: None,
                branch_condition_value: None,
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
            branches: Vec::new(),
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
                branch_condition: None,
                branch_condition_value: None,
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
        );
        assert!(
            reason.is_none(),
            "loop condition predicate mismatch should not residualize: {reason:?}"
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
            branches: Vec::new(),
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
                branch_condition: None,
                branch_condition_value: None,
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
        );
        assert!(
            reason.is_none(),
            "loop condition value mismatch should not residualize: {reason:?}"
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
            branches: Vec::new(),
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
            branches: Vec::new(),
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
    fn authorized_signature_canonicalizes_generic_names_by_abi_slot() {
        let signature = signature_spec(
            Some(CType::Int(32)),
            vec![
                ("arg1", Some(CType::Int(32))),
                ("arg2", Some(CType::Int(32))),
            ],
        );
        let params = params_from_authorized_signature(&signature);

        assert_eq!(params[0].name, "arg0");
        assert_eq!(params[1].name, "arg1");
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
    fn decompile_is_stable_with_external_param_names_and_local_order() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
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

        let signature = signature_spec(
            Some(CType::Int(64)),
            vec![
                ("zzz_first", Some(CType::Int(64))),
                ("aaa_second", Some(CType::Int(64))),
            ],
        );
        let input = prepared_standard_input_with_type_facts(
            prepared,
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            "prepared stability test route",
        );
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());

        let built_first = decompiler.build_function_from_input(&input);
        let built_second = decompiler.build_function_from_input(&input);
        let first = decompiler.decompile_input(&input);
        let second = decompiler.decompile_input(&input);

        assert_eq!(first, second, "decompiled text should be byte-stable");
        assert!(
            first.contains("stable_demo(int64_t zzz_first, int64_t aaa_second)"),
            "{first}"
        );
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
    fn certified_standard_output_accepts_auto_populated_prepared_member_access() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x10, 8),
                    a: Varnode::register(0x10, 8),
                    b: Varnode::constant(8, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::register(0x00, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::unique(0x10, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            field_access_certificates: vec![FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        });
        function_facts.populate_member_access_render_facts_from_field_certificates(
            &prepared,
            &x86_64_param_slot_resolver(),
        );
        assert!(
            function_facts.render().is_some_and(|render| render
                .member_access_for_op(0x1000, 1, false, "hash", 8, Some(8))
                .is_some()),
            "prepared field certificate should populate member render fact"
        );
        let func = CFunction::new("field_auto_ok", CType::u64())
            .with_param(CType::ptr(CType::Struct("record".to_string())), "arg0")
            .with_body(vec![CStmt::Return(Some(CExpr::PtrMember {
                base: Box::new(CExpr::var("arg0")),
                member: "hash".to_string(),
            }))]);
        let memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 1, false)
            .expect("memory certificate");
        let return_cert = prepared
            .return_certificate_for_op(0x1000, 2)
            .expect("return certificate");
        let effect_proofs = [
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 1,
                call_disposition: None,
                target: None,
                address: Some(memory_cert.address),
                value: memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::Return,
                block_addr: 0x1000,
                op_idx: 2,
                call_disposition: None,
                target: None,
                address: None,
                value: Some(return_cert.value),
                values: Vec::new(),
                materialized_phi_copy: false,
            },
        ];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    fn prepared_member_return_fixture(arch: &ArchSpec) -> r2ssa::SsaArtifact {
        prepared_from_ops(
            vec![
                R2ILOp::IntAdd {
                    dst: Varnode::unique(0x10, 8),
                    a: Varnode::register(0x10, 8),
                    b: Varnode::constant(8, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::register(0x00, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::unique(0x10, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            arch,
        )
    }

    fn node_hash_type_db() -> ExternalTypeDb {
        ExternalTypeDb {
            structs: [(
                "node".to_string(),
                ExternalStruct {
                    name: "Node".to_string(),
                    fields: [(
                        8,
                        ExternalField {
                            name: "hash".to_string(),
                            offset: 8,
                            ty: Some("uint64_t".to_string()),
                        },
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            ..ExternalTypeDb::default()
        }
    }

    fn node_hash_signature() -> FunctionSignatureSpec {
        signature_spec(
            Some(CType::UInt(64)),
            vec![(
                "node",
                Some(CType::Pointer(Box::new(CType::Struct("Node".to_string())))),
            )],
        )
    }

    #[test]
    fn decompile_renders_certified_member_return_load() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_member_return_fixture(&arch);
        let signature = node_hash_signature();
        let input = prepared_standard_input_with_type_facts(
            prepared,
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                external_type_db: node_hash_type_db(),
                field_access_certificates: vec![FieldAccessCertificate {
                    slot: 0,
                    field_offset: 8,
                    field_name: "hash".to_string(),
                    field_type: Some("uint64_t".to_string()),
                }],
                ..FunctionTypeFacts::default()
            },
            "prepared member return certificate route",
        );
        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert!(
            output.contains("return node->hash;"),
            "certified member load return should render executable C, got:\n{output}"
        );
        assert!(
            !output.contains("summary return unresolved"),
            "certified member load return must not residualize, got:\n{output}"
        );
    }

    #[test]
    fn decompile_residualizes_member_return_load_without_matching_member_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_member_return_fixture(&arch);
        let signature = node_hash_signature();
        let input = prepared_standard_input_with_type_facts(
            prepared,
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                external_type_db: node_hash_type_db(),
                field_access_certificates: vec![FieldAccessCertificate {
                    slot: 0,
                    field_offset: 8,
                    field_name: "hash".to_string(),
                    field_type: Some("uint32_t".to_string()),
                }],
                ..FunctionTypeFacts::default()
            },
            "prepared member return missing proof route",
        );
        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert!(
            output.contains("r2dec residual"),
            "wrong-width member proof must residualize, got:\n{output}"
        );
        assert!(
            !output.contains("return node->hash;"),
            "wrong-width member proof must not render member return, got:\n{output}"
        );
    }

    #[test]
    fn decompile_residual_for_predicate_heavy_return_without_complete_render_proof_is_stable() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
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
        let signature = signature_spec(Some(CType::Int(32)), vec![("value", Some(CType::Int(64)))]);
        let input = prepared_standard_input_with_type_facts(
            prepared,
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            "prepared predicate-heavy builder stability route",
        );
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let built_first = decompiler.build_function_from_input(&input);
        let built_second = decompiler.build_function_from_input(&input);
        let first = decompiler.decompile_input(&input);
        let second = decompiler.decompile_input(&input);

        assert_eq!(first, second, "predicate-heavy text should be byte-stable");
        assert_eq!(
            built_first.body, built_second.body,
            "predicate-heavy AST should be stable across builds"
        );
        assert!(
            built_first
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "renderable predicate chain should emit executable return: {:?}",
            built_first.body
        );
        assert!(
            !format!("{:?}", built_first.body).contains("certified render contract failed"),
            "renderable predicate chain must not residualize, got {:?}",
            built_first.body
        );
    }

    #[test]
    fn certified_signed_return_renders_all_ones_literal_as_negative_one() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0x00, 8),
                    src: Varnode::constant(0xffff_ffff, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );
        let signature = signature_spec(Some(CType::Int(32)), Vec::new());
        let input = prepared_standard_input_with_type_facts(
            prepared,
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            "signed literal return normalization",
        );

        let built = Decompiler::new(DecompilerConfig::x86_64()).build_function_from_input(&input);

        assert!(
            built
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(Some(CExpr::IntLit(-1))))),
            "expected signed literal return, got {:?}",
            built.body
        );
    }

    #[test]
    fn decompile_input_residualizes_uncertified_header_and_return_memory() {
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
        let function_facts =
            FunctionFacts::new(type_facts, None).with_decompile_route(test_decompile_route(
                r2types::DecompileRouteKind::Standard,
                "test-certified standard route",
                None,
                r2sym::RenderPermission::certified(
                    r2sym::ProofOwner::R2engine,
                    "test-certified standard route",
                ),
            ));
        let context = DecompilerContext::default().with_function_facts(function_facts);

        let input = DecompilerInput::new(prepared, context);
        let typed = Decompiler::new(DecompilerConfig::x86_64());

        let typed_fn = typed.build_function_from_input(&input);
        let typed_text = typed.decompile_input(&input);

        assert_eq!(typed_fn.name, "stable_demo");
        assert_eq!(typed_fn.ret_type, CType::Unknown);
        assert!(typed_text.contains("stable_demo"));
        assert!(
            typed_text.contains(
                "certified Standard header lacks FunctionTypeFacts render-authorized signature"
            ),
            "{typed_text}"
        );
        assert!(
            !typed_text.contains("int64_t stable_demo"),
            "certified route must not preserve a header from uncertified merged_signature facts:\n{typed_text}"
        );
        assert!(
            !typed_text.contains("\n    return "),
            "certified route must not render executable return through an uncertified memory load:\n{typed_text}"
        );
        assert!(
            !typed_text.contains("rax_") && !typed_text.contains("rbp"),
            "residualized certified output must not leak raw carriers:\n{typed_text}"
        );
    }

    #[test]
    fn decompile_input_residualizes_signature_without_certified_abi_entities() {
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
        let prepared = prepared_from_ops(ops, &arch);
        let signature = signature_spec(
            Some(CType::Int(64)),
            vec![
                ("left", Some(CType::Int(64))),
                ("right", Some(CType::Int(64))),
            ],
        );
        let type_facts = FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            ..FunctionTypeFacts::default()
        };
        let function_facts =
            FunctionFacts::new(type_facts, None).with_decompile_route(test_decompile_route(
                r2types::DecompileRouteKind::Standard,
                "test-certified standard route",
                None,
                r2sym::RenderPermission::certified(
                    r2sym::ProofOwner::R2engine,
                    "test-certified standard route",
                ),
            ));
        let context = DecompilerContext::default().with_function_facts(function_facts);
        let input = DecompilerInput::new(prepared, context);
        let typed = Decompiler::new(DecompilerConfig::x86_64());

        let typed_fn = typed.build_function_from_input(&input);
        let typed_text = typed.decompile_input(&input);

        assert_eq!(typed_fn.ret_type, CType::Unknown);
        assert!(typed_fn.params.is_empty());
        assert!(
            typed_text.contains(
                "certified ABI parameter slots [] disagree with rendered signature arity 2"
            ),
            "a friendly signature without certified ABI entities must residualize, got:\n{typed_text}"
        );
        assert!(
            !typed_text.contains("\n    return "),
            "certified route must not render executable return through an uncertified memory load:\n{typed_text}"
        );
    }

    #[test]
    fn decompile_input_residualizes_render_authorized_header_with_unknown_param_type() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let signature = signature_spec(
            Some(CType::Int(64)),
            vec![("left", Some(CType::Int(64))), ("right", None)],
        );
        let type_facts = FunctionTypeFacts {
            signature_certificate: external_signature_certificate(&signature),
            merged_signature: Some(signature),
            ..FunctionTypeFacts::default()
        };
        let function_facts =
            FunctionFacts::new(type_facts, None).with_decompile_route(test_decompile_route(
                r2types::DecompileRouteKind::Standard,
                "test-certified standard route",
                None,
                r2sym::RenderPermission::certified(
                    r2sym::ProofOwner::R2engine,
                    "test-certified standard route",
                ),
            ));
        let input = DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        );

        let typed_text = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert!(
            typed_text.contains("certified Standard header has incomplete FunctionTypeFacts render-authorized parameter types"),
            "{typed_text}"
        );
        assert!(
            !typed_text.contains("stable_demo(int64_t left, unknown_t right)"),
            "certified Standard must residualize incomplete render-authorized signatures:\n{typed_text}"
        );
    }

    #[test]
    fn decompile_input_without_route_facts_residualizes() {
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
        let input = DecompilerInput::new(prepared, DecompilerContext::default());

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert!(
            output.contains("missing FunctionFacts::decompile_route"),
            "{output}"
        );
        assert!(
            !output.contains("return 0;"),
            "missing route facts must not render executable C, got:\n{output}"
        );
    }

    #[test]
    fn build_function_from_input_without_route_facts_residualizes_ast() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let input = DecompilerInput::new(prepared, DecompilerContext::default());

        let func = Decompiler::new(DecompilerConfig::x86_64()).build_function_from_input(&input);

        assert!(
            func.body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Comment(text) if text.contains("missing FunctionFacts::decompile_route"))),
            "missing route facts must produce an explicit residual AST, got {func:?}"
        );
        assert!(
            !func.body.iter().any(summary_stmt_contains_return),
            "missing route facts must not render executable return AST, got {func:?}"
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
        let function_facts = FunctionFacts::default().with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::FallbackComment,
            "engine refusal: tested route",
            Some("/* engine refusal: tested route */".to_string()),
            r2sym::RenderPermission::refuse(
                r2sym::ProofOwner::R2engine,
                "engine refusal: tested route",
            ),
        ));
        let context = DecompilerContext::default().with_function_facts(function_facts);
        let input = DecompilerInput::new(prepared, context);

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert_eq!(output, "/* engine refusal: tested route */");
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
        let function_facts = FunctionFacts::default().with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::FallbackComment,
            "facts-owned route",
            Some("/* facts-owned refusal */".to_string()),
            r2sym::RenderPermission::refuse(r2sym::ProofOwner::R2engine, "facts-owned route"),
        ));
        let context = DecompilerContext::default().with_function_facts(function_facts);
        let input = DecompilerInput::new(prepared, context);

        let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

        assert_eq!(output, "/* facts-owned refusal */");
    }

    #[test]
    fn public_summary_renderer_requires_function_facts_route_permission() {
        let semantic_artifact = large_cfg_worker_artifact(
            r2sym::RefinementStage::Residual,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));

        assert!(
            super::render_semantic_worker_summary(
                "sym.worker",
                &function_facts,
                DecompilerConfig::default(),
            )
            .is_none(),
            "summary rendering must not infer route permission from semantics alone"
        );

        let certified_route_facts =
            function_facts
                .clone()
                .with_decompile_route(test_decompile_route(
                    r2types::DecompileRouteKind::LinearWorker,
                    "wrong permission for summary route",
                    None,
                    r2sym::RenderPermission::certified(
                        r2sym::ProofOwner::R2engine,
                        "wrong permission for summary route",
                    ),
                ));
        assert!(
            super::render_semantic_worker_summary(
                "sym.worker",
                &certified_route_facts,
                DecompilerConfig::default(),
            )
            .is_none(),
            "summary rendering must require summary-comment permission, not only a route kind"
        );

        let summary_route_facts = function_facts.with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::LinearWorker,
            "engine-selected summary route",
            None,
            r2sym::RenderPermission::summary(
                r2sym::ProofOwner::R2engine,
                "engine-selected summary route",
            ),
        ));
        let output = super::render_semantic_worker_summary(
            "sym.worker",
            &summary_route_facts,
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
    fn decompiler_context_reads_callee_resolution_from_function_facts() {
        let callsite = r2types::CallsiteKey {
            block_addr: 0x401000,
            op_index: 2,
        };
        let identity_key = r2types::CalleeIdentityKey::Named("sym.helper".to_string());
        let mut callee_resolution = r2types::CalleeResolutionFacts::default();
        callee_resolution.by_key.insert(
            identity_key.clone(),
            r2types::CalleeIdentity::from_name("sym.helper"),
        );
        callee_resolution.by_callsite.insert(callsite, identity_key);
        let function_facts = FunctionFacts::default().with_callee_resolution(callee_resolution);

        let context = DecompilerContext::from_function_facts(function_facts);

        assert!(
            context
                .function_facts
                .callee_resolution()
                .and_then(|resolution| resolution.identity_for_callsite(callsite))
                .is_some(),
            "callee resolution must be retained on FunctionFacts"
        );
    }

    #[test]
    fn decompiler_context_does_not_enrich_type_facts_from_names() {
        let context = DecompilerContext::from_function_facts(FunctionFacts::default());

        assert!(
            context
                .function_facts
                .type_facts()
                .known_function_signatures
                .is_empty(),
            "r2dec must consume FunctionFacts type evidence, not enrich signatures from names locally"
        );
    }

    #[test]
    fn decompile_input_nonstandard_summary_routes_are_comment_only() {
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
            let signature = signature_spec(Some(CType::Int(32)), Vec::new());
            let function_facts = FunctionFacts::new(
                FunctionTypeFacts {
                    signature_certificate: external_signature_certificate(&signature),
                    merged_signature: Some(signature),
                    ..FunctionTypeFacts::default()
                },
                None,
            )
            .with_decompile_route(test_decompile_route(
                route.0,
                route.1,
                None,
                r2sym::RenderPermission::summary(r2sym::ProofOwner::R2engine, route.1),
            ));
            let context = DecompilerContext::default().with_function_facts(function_facts);
            let input = DecompilerInput::new(prepared, context);

            let output = Decompiler::new(DecompilerConfig::x86_64()).decompile_input(&input);

            assert!(
                output.contains(
                    "render contract: summary facts only; no executable native C reconstructed"
                ),
                "summary route builder path must state the render contract for {:?}, got:\n{output}",
                route.0
            );
            assert!(
                !output.contains("return 0;")
                    && !output.contains("switch (")
                    && !output.contains("case 0x"),
                "summary route builder path must not emit executable C for {:?}, got:\n{output}",
                route.0
            );
        }
    }

    #[test]
    fn build_function_from_input_nonstandard_routes_residualize_ast() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let function_facts = FunctionFacts::default().with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::LinearWorker,
            "engine-selected summary route",
            None,
            r2sym::RenderPermission::summary(
                r2sym::ProofOwner::R2engine,
                "engine-selected summary route",
            ),
        ));
        let input = DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        );

        let built = Decompiler::new(DecompilerConfig::x86_64()).build_function_from_input(&input);

        assert!(
            built
                .body
                .iter()
                .all(|stmt| matches!(stmt, CStmt::Comment(_))),
            "summary route AST must be comment-only, got {:?}",
            built.body
        );
        assert!(
            !built
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "summary route AST must not contain executable returns: {:?}",
            built.body
        );
    }

    #[test]
    fn build_function_from_input_standard_summary_permission_residualizes_ast() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let function_facts = FunctionFacts::default().with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::Standard,
            "standard route but summary-only permission",
            None,
            r2sym::RenderPermission::summary(
                r2sym::ProofOwner::R2engine,
                "standard route but summary-only permission",
            ),
        ));
        let input = DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        );

        let built = Decompiler::new(DecompilerConfig::x86_64()).build_function_from_input(&input);

        assert!(
            format!("{:?}", built.body).contains("summary-only"),
            "summary-only permission should explain the residual: {:?}",
            built.body
        );
        assert!(
            !built
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "summary-only permission must not produce executable returns: {:?}",
            built.body
        );
        assert!(
            built.locals.is_empty(),
            "summary-only permission must fail closed before local recovery: {:?}",
            built.locals
        );

        let decompiler =
            Decompiler::new(DecompilerConfig::x86_64()).with_context(input.context.clone());
        let route = decompiler
            .context
            .function_facts
            .decompile_route()
            .expect("test route");
        let direct_built = decompiler.build_function_internal(
            input.prepared_ssa.function(),
            &input.prepared_ssa,
            route,
        );
        assert!(
            direct_built
                .body
                .iter()
                .all(|stmt| matches!(stmt, CStmt::Comment(_))),
            "internal Standard path must fail closed before structuring executable C: {:?}",
            direct_built.body
        );
        assert!(
            direct_built.locals.is_empty(),
            "internal Standard path must fail closed before local recovery: {:?}",
            direct_built.locals
        );
    }

    #[test]
    fn decompile_input_standard_certified_summary_only_semantics_residualizes() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let semantic_artifact = test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::SummaryOnly,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact))
                .with_decompile_route(test_decompile_route(
                    r2types::DecompileRouteKind::Standard,
                    "bad standard route over summary-only semantics",
                    None,
                    r2sym::RenderPermission::certified(
                        r2sym::ProofOwner::R2engine,
                        "bad standard route over summary-only semantics",
                    ),
                ));
        let input = DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        );
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());

        let output = decompiler.decompile_input(&input);
        let built = decompiler.build_function_from_input(&input);

        assert!(
            output
                .contains("summary-only semantic artifact cannot authorize Standard executable C"),
            "summary-only semantics must reject certified Standard output, got:\n{output}"
        );
        assert!(
            !output.contains("return 0;"),
            "summary-only semantics must not render executable returns, got:\n{output}"
        );
        assert!(
            format!("{:?}", built.body)
                .contains("summary-only semantic artifact cannot authorize Standard executable C"),
            "AST boundary should carry the same residual reason, got {:?}",
            built.body
        );
        assert!(
            !built
                .body
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Return(_))),
            "summary-only Standard contradiction must not produce executable returns: {:?}",
            built.body
        );
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
        let function_facts = FunctionFacts::default().with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::Standard,
            "standard route with missing expression proof",
            None,
            r2sym::RenderPermission::residual(
                r2sym::ProofOwner::R2engine,
                "missing expression proof",
            ),
        ));
        let context = DecompilerContext::default().with_function_facts(function_facts);
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

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

        let func = CFunction::new("bad_value_carrier", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::var("value_0")))]);
        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("generated carrier locals should break certified rendering");
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
        assert!(is_uncertified_render_var_name("EAX"));
        assert!(is_uncertified_render_var_name("RAX"));
        assert!(is_uncertified_render_var_name("x0"));
        assert!(is_uncertified_render_var_name("arg0"));
        assert!(is_uncertified_render_var_name("value_0"));
        assert!(is_uncertified_render_var_name("value_3e480"));
        assert!(!is_uncertified_render_var_name("sha_state"));

        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let func = CFunction::new("bad_temp_addr", CType::i64())
            .with_body(vec![CStmt::Return(Some(CExpr::var("&TMP:_2")))]);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("addressed raw temp should break certified rendering");
        assert!(
            reason.contains("rendered uncertified raw artifact name"),
            "{reason}"
        );

        let func = CFunction::new("mismatched_arg", CType::i64())
            .with_param(CType::i64(), "arg1")
            .with_body(vec![CStmt::Return(Some(CExpr::var("arg0")))]);
        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("an undeclared generated argument should break certified rendering");
        assert!(
            reason.contains("rendered uncertified raw artifact name(s): arg0"),
            "{reason}"
        );
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("pure expression assignment without proof must break certified rendering");

        assert!(
            reason.contains("pure expression assignment")
                && reason.contains("FunctionRenderFacts expression")
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Expression,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Expression,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
                && reason.contains("FunctionRenderFacts expression"),
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Expression,
            block_addr: 0x1000,
            op_idx: 1,
            call_disposition: None,
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("call without callsite cert should break certified rendering");

        assert!(
            reason.contains("missing exact FunctionFacts render proof"),
            "{reason}"
        );
        assert!(reason.contains("rendered calls=1"), "{reason}");
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("call without exact emitted proof should break certified rendering");

        assert!(
            reason
                .contains("rendered 1 call(s) with only 0 rendered FunctionCallsiteFacts proof(s)"),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:0.0"), "{reason}");
    }

    #[test]
    fn certified_standard_output_refuses_missing_source_call_effect() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Call {
                target: Varnode::constant(0x401000, 8),
            }],
            &arch,
        );
        assert_eq!(prepared.certificates().callsites.len(), 1);
        let func = CFunction::new("missing_call", CType::Void)
            .with_body(vec![CStmt::comment("no executable call rendered")]);
        let function_facts = test_function_facts_with_prepared_render(&prepared);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("missing source call effect should break certified rendering");

        assert!(
            reason.contains(
                "rendered 0 executable call(s) from 1 source FunctionCallsiteFacts callsite(s)"
            ) && reason.contains("first missing callsite 0x1000:0")
                && reason.contains("missing callsite effects must residualize"),
            "{reason}"
        );
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 1,
            call_disposition: None,
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
            reason.contains("FunctionCallsiteFacts argument values"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_address_arithmetic_call_argument() {
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
        let func =
            CFunction::new("bad_call_arg_address_math", CType::Void).with_body(vec![CStmt::expr(
                CExpr::call(
                    CExpr::var("helper"),
                    vec![CExpr::binary(
                        BinaryOp::Add,
                        CExpr::uint(0x1000_2000),
                        CExpr::uint(658),
                    )],
                ),
            )]);
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        )
        .expect("address arithmetic call argument must residualize without FunctionFacts proof");

        assert!(
            reason.contains("raw address-like call argument")
                && reason.contains("FunctionFacts certificates"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_call_argument_prefix_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Call {
                target: Varnode::constant(0x401000, 8),
            }],
            &arch,
        );
        let callsite = r2types::CallsiteKey {
            block_addr: 0x1000,
            op_index: 0,
        };
        let target = r2ssa::ValueId(7);
        let first_arg = r2ssa::ValueId(11);
        let second_arg = r2ssa::ValueId(12);
        let function_facts = FunctionFacts::default()
            .with_callsites(r2types::FunctionCallsiteFacts {
                by_callsite: BTreeMap::from([(
                    callsite,
                    r2types::CallsiteArgumentFacts {
                        callsite,
                        call_site_id: r2ssa::CallSiteId(0),
                        at: r2ssa::InstId(0),
                        target,
                        direct_target: Some(0x401000),
                        argument_values: vec![
                            r2types::CallArgumentValueFact {
                                index: 0,
                                value: first_arg,
                            },
                            r2types::CallArgumentValueFact {
                                index: 1,
                                value: second_arg,
                            },
                        ],
                        register_argument_locations: Vec::new(),
                        stack_argument_locations: Vec::new(),
                    },
                )]),
            })
            .with_render(r2types::FunctionRenderFacts {
                certified_exprs: BTreeMap::from([(
                    r2ssa::SemanticId::expression(first_arg),
                    r2types::CertifiedExpr {
                        id: r2ssa::SemanticId::expression(first_arg),
                        fact: r2types::ExpressionRenderFact {
                            value: first_arg,
                            defining_inst: None,
                            width: 64,
                            renderable: true,
                        },
                        inputs: Vec::new(),
                        bindings: BTreeSet::new(),
                    },
                )]),
                ..r2types::FunctionRenderFacts::default()
            });
        let func = CFunction::new("bad_call_prefix", CType::Void).with_body(vec![CStmt::expr(
            CExpr::call(CExpr::var("helper"), vec![CExpr::uint(1)]),
        )]);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: callsite.block_addr,
            op_idx: callsite.op_index,
            call_disposition: None,
            target: Some(target),
            address: None,
            value: None,
            values: vec![first_arg],
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("prefix-only call argument proof must break certified rendering");

        assert!(
            reason.contains("argument value proof [ValueId(11)]"),
            "{reason}"
        );
        assert!(reason.contains("ValueId(12)"), "{reason}");
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Call,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        assert!(reason.contains("FunctionCallsiteFacts target"), "{reason}");
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("return without exact emitted proof should break certified rendering");

        assert!(
            reason.contains(
                "rendered 1 value return(s) with only 0 rendered FunctionRenderFacts return proof(s)"
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 1,
            call_disposition: None,
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
                && reason.contains("lacks renderable FunctionRenderFacts expression"),
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        assert!(
            reason.contains("FunctionRenderFacts return value"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_second_return_hidden_by_source_return_fact() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                },
                R2ILOp::Return {
                    target: Varnode::constant(1, 8),
                },
            ],
            &arch,
        );
        assert_eq!(prepared.certificates().returns.len(), 2);
        let first = prepared
            .return_certificate_for_op(0x1000, 0)
            .expect("first return certificate");
        let func = CFunction::new("bad_second_return", CType::i64()).with_body(vec![
            CStmt::Return(Some(CExpr::uint(0))),
            CStmt::Return(Some(CExpr::uint(1))),
        ]);
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        assert_eq!(
            function_facts
                .render()
                .map(|render| render.return_effects().count()),
            Some(2),
            "fixture must expose two source return facts"
        );
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
            target: None,
            address: None,
            value: Some(first.value),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("unproved second return must break certified rendering");

        assert!(
            reason.contains(
                "rendered 2 value return(s) with only 1 rendered FunctionRenderFacts return proof(s)"
            ),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:1"), "{reason}");
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&[]),
        )
        .expect("memory expression without exact emitted proof should break certified rendering");

        assert!(
            reason.contains(
                "rendered 1 memory-like access(es) with only 0 rendered FunctionRenderFacts memory proof(s)"
            ),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:0.0"), "{reason}");
    }

    #[test]
    fn certified_standard_output_refuses_second_memory_access_hidden_by_source_memory_fact() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::register(0x00, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::register(0x08, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x18, 8),
                },
            ],
            &arch,
        );
        assert_eq!(prepared.certificates().memory_accesses.len(), 2);
        let first = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("first memory certificate");
        let func = CFunction::new("bad_second_memory", CType::Void).with_body(vec![
            CStmt::expr(CExpr::assign(
                CExpr::var("x"),
                CExpr::deref(CExpr::var("p")),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var("y"),
                CExpr::deref(CExpr::var("q")),
            )),
        ]);
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        assert_eq!(
            function_facts
                .render()
                .map(|render| render.memory_accesses().count()),
            Some(2),
            "fixture must expose two source memory facts"
        );
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
            target: None,
            address: Some(first.address),
            value: first.value,
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("unproved second memory access must break certified rendering");

        assert!(
            reason.contains(
                "rendered 2 memory-like access(es) with only 1 rendered FunctionRenderFacts memory proof(s)"
            ),
            "{reason}"
        );
        assert!(reason.contains("first missing node stmt:1.0.1"), "{reason}");
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("memory certificate");
        let func = CFunction::new("memory_ok", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(CExpr::var("x"), CExpr::deref(CExpr::var("p"))),
        )]);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
    fn certified_standard_output_refuses_dropped_memory_effect() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Load {
                dst: Varnode::register(0x00, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x10, 8),
            }],
            &arch,
        );
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("memory certificate");
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
            target: None,
            address: Some(cert.address),
            value: cert.value,
            values: Vec::new(),
            materialized_phi_copy: false,
        }];
        let func = CFunction::new("dropped_memory", CType::Void)
            .with_body(vec![CStmt::Comment("no memory effect".to_string())]);

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("dropped memory effect must break certified rendering");

        assert!(
            reason.contains(
                "recorded 1 memory effect(s), but final AST contains only 0 memory-like access(es)"
            ),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_raw_pointer_arithmetic_deref() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Load {
                dst: Varnode::register(0x00, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0x10, 8),
            }],
            &arch,
        );
        let func = CFunction::new("raw_pointer_math", CType::Void).with_body(vec![CStmt::expr(
            CExpr::assign(
                CExpr::var("x"),
                CExpr::deref(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::var("arr"),
                    CExpr::binary(BinaryOp::Mul, CExpr::var("idx"), CExpr::int(56)),
                )),
            ),
        )]);
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("memory certificate");
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
        )
        .expect("raw pointer arithmetic must not replace typed array/member proof");

        assert!(
            reason.contains("raw pointer-arithmetic dereference")
                && reason.contains("FunctionFacts certificates"),
            "{reason}"
        );
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
        let function_facts = test_function_facts_with_prepared_render(&prepared);
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::MemoryRead,
            block_addr: 0x1000,
            op_idx: 0,
            call_disposition: None,
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
    fn certified_standard_output_rejects_stack_local_with_offset_only_evidence() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(Vec::new(), &arch);
        let render = test_stack_render_facts(
            r2ssa::ObjectId(1),
            r2ssa::StackAddressBase::FramePointer,
            -8,
        );
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), None).with_render(render);
        let mut func = CFunction::new("local_offset_only", CType::Void)
            .with_body(vec![CStmt::Comment("body".to_string())]);
        func.locals.push(ast::CLocal {
            ty: CType::Int(32),
            name: "buf".to_string(),
            stack_offset: Some(-8),
        });

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("offset-only stack evidence must not certify a friendly local");

        assert!(
            reason.contains("local buf at stack offset -8 lacks exact typed StackSlotCertificate"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_accepts_exact_typed_stack_local_identity() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(Vec::new(), &arch);
        let render = test_stack_render_facts(
            r2ssa::ObjectId(1),
            r2ssa::StackAddressBase::FramePointer,
            -8,
        );
        let type_facts = FunctionTypeFacts {
            stack_slots: BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -8,
                },
                ExternalStackSlotSpec {
                    name: "buf".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    base: ExternalStackBase::FramePointer,
                    role: ExternalStackSlotRole::Local,
                    ..ExternalStackSlotSpec::default()
                },
            )]),
            ..FunctionTypeFacts::default()
        };
        let function_facts = FunctionFacts::new(type_facts, None).with_render(render);
        let mut func = CFunction::new("local_exact", CType::Void)
            .with_body(vec![CStmt::Comment("body".to_string())]);
        func.locals.push(ast::CLocal {
            ty: CType::Int(32),
            name: "buf".to_string(),
            stack_offset: Some(-8),
        });

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func);

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_rejects_stack_local_type_mismatch() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(Vec::new(), &arch);
        let render = test_stack_render_facts(
            r2ssa::ObjectId(1),
            r2ssa::StackAddressBase::FramePointer,
            -8,
        );
        let type_facts = FunctionTypeFacts {
            stack_slots: BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -8,
                },
                ExternalStackSlotSpec {
                    name: "buf".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    base: ExternalStackBase::FramePointer,
                    role: ExternalStackSlotRole::Local,
                    ..ExternalStackSlotSpec::default()
                },
            )]),
            ..FunctionTypeFacts::default()
        };
        let function_facts = FunctionFacts::new(type_facts, None).with_render(render);
        let mut func = CFunction::new("local_type_mismatch", CType::Void)
            .with_body(vec![CStmt::Comment("body".to_string())]);
        func.locals.push(ast::CLocal {
            ty: CType::UInt(32),
            name: "buf".to_string(),
            stack_offset: Some(-8),
        });

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("renderer-local stack local type must not override FunctionTypeFacts");

        assert!(
            reason.contains("local buf at stack offset -8 lacks exact typed StackSlotCertificate"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_accepts_type_layout_certified_member_access() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::register(0x00, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            field_access_certificates: vec![FieldAccessCertificate {
                slot: 0,
                field_offset: 0,
                field_name: "len".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        });
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 0,
                is_write: false,
                field_name: "len",
                field_offset: 0,
                access_width: 8,
            },
        );
        let func = CFunction::new("field_ok", CType::i64())
            .with_param(CType::Struct("record".to_string()), "arg0")
            .with_body(vec![CStmt::Return(Some(CExpr::Member {
                base: Box::new(CExpr::var("arg0")),
                member: "len".to_string(),
            }))]);
        let memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("memory certificate");
        let return_cert = prepared
            .return_certificate_for_op(0x1000, 1)
            .expect("return certificate");
        let effect_proofs = [
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 0,
                call_disposition: None,
                target: None,
                address: Some(memory_cert.address),
                value: memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::Return,
                block_addr: 0x1000,
                op_idx: 1,
                call_disposition: None,
                target: None,
                address: None,
                value: Some(return_cert.value),
                values: Vec::new(),
                materialized_phi_copy: false,
            },
        ];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_refuses_member_fact_without_rendered_memory_proof() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::register(0x00, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 0,
                is_write: false,
                field_name: "len",
                field_offset: 0,
                access_width: 8,
            },
        );
        let func =
            CFunction::new("field_unproved_memory", CType::i64()).with_body(vec![CStmt::Return(
                Some(CExpr::Member {
                    base: Box::new(CExpr::var("arg0")),
                    member: "len".to_string(),
                }),
            )]);
        let return_cert = prepared
            .return_certificate_for_op(0x1000, 1)
            .expect("return certificate");
        let effect_proofs = [EffectRenderProof {
            kind: EffectRenderProofKind::Return,
            block_addr: 0x1000,
            op_idx: 1,
            call_disposition: None,
            target: None,
            address: None,
            value: Some(return_cert.value),
            values: Vec::new(),
            materialized_phi_copy: false,
        }];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("member fact without emitted memory proof must not certify final member syntax");

        assert!(
            reason.contains(
                "rendered 1 field access(es) without FunctionRenderFacts member-access proof"
            ) && reason.contains("len"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_refuses_member_fact_from_unrendered_op() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::register(0x00, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::register(0x08, 8),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x18, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 8),
                },
            ],
            &arch,
        );
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 1,
                is_write: false,
                field_name: "len",
                field_offset: 0,
                access_width: 8,
            },
        );
        let func = CFunction::new("field_wrong_op", CType::i64()).with_body(vec![CStmt::Return(
            Some(CExpr::Member {
                base: Box::new(CExpr::var("arg0")),
                member: "len".to_string(),
            }),
        )]);
        let memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("first memory certificate");
        let return_cert = prepared
            .return_certificate_for_op(0x1000, 2)
            .expect("return certificate");
        let effect_proofs = [
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 0,
                call_disposition: None,
                target: None,
                address: Some(memory_cert.address),
                value: memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::Return,
                block_addr: 0x1000,
                op_idx: 2,
                call_disposition: None,
                target: None,
                address: None,
                value: Some(return_cert.value),
                values: Vec::new(),
                materialized_phi_copy: false,
            },
        ];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        )
        .expect("member fact from an unrendered op must not certify final member syntax");

        assert!(
            reason.contains(
                "rendered 1 field access(es) without FunctionRenderFacts member-access proof"
            ) && reason.contains("len"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_accepts_multiple_returned_members_with_layout_proofs() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Load {
                    dst: Varnode::unique(0x10, 4),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x10, 8),
                },
                R2ILOp::Load {
                    dst: Varnode::unique(0x20, 4),
                    space: SpaceId::Ram,
                    addr: Varnode::register(0x18, 8),
                },
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x00, 4),
                    a: Varnode::unique(0x10, 4),
                    b: Varnode::unique(0x20, 4),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x00, 4),
                },
            ],
            &arch,
        );
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            field_access_certificates: vec![
                FieldAccessCertificate {
                    slot: 0,
                    field_offset: 0,
                    field_name: "f_0".to_string(),
                    field_type: Some("int32_t".to_string()),
                },
                FieldAccessCertificate {
                    slot: 0,
                    field_offset: 0x30,
                    field_name: "f_30".to_string(),
                    field_type: Some("int32_t".to_string()),
                },
            ],
            ..FunctionTypeFacts::default()
        });
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 0,
                is_write: false,
                field_name: "f_0",
                field_offset: 0,
                access_width: 4,
            },
        );
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 1,
                is_write: false,
                field_name: "f_30",
                field_offset: 0x30,
                access_width: 4,
            },
        );
        let func = CFunction::new("field_pair_ok", CType::i32()).with_body(vec![CStmt::Return(
            Some(CExpr::Binary {
                op: BinaryOp::Add,
                left: Box::new(CExpr::PtrMember {
                    base: Box::new(CExpr::var("obj")),
                    member: "f_0".to_string(),
                }),
                right: Box::new(CExpr::PtrMember {
                    base: Box::new(CExpr::var("obj")),
                    member: "f_30".to_string(),
                }),
            }),
        )]);
        let first_memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("first memory certificate");
        let second_memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 1, false)
            .expect("second memory certificate");
        let return_cert = prepared
            .return_certificate_for_op(0x1000, 3)
            .expect("return certificate");
        let effect_proofs = [
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 0,
                call_disposition: None,
                target: None,
                address: Some(first_memory_cert.address),
                value: first_memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 1,
                call_disposition: None,
                target: None,
                address: Some(second_memory_cert.address),
                value: second_memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::Return,
                block_addr: 0x1000,
                op_idx: 3,
                call_disposition: None,
                target: None,
                address: None,
                value: Some(return_cert.value),
                values: Vec::new(),
                materialized_phi_copy: false,
            },
        ];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn certified_standard_output_rejects_returned_member_missing_layout_proof() {
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
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            field_access_certificates: vec![FieldAccessCertificate {
                slot: 0,
                field_offset: 0,
                field_name: "f_0".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        });
        let func =
            CFunction::new("field_pair_missing", CType::i32()).with_body(vec![CStmt::Return(
                Some(CExpr::Binary {
                    op: BinaryOp::Add,
                    left: Box::new(CExpr::PtrMember {
                        base: Box::new(CExpr::var("obj")),
                        member: "f_0".to_string(),
                    }),
                    right: Box::new(CExpr::PtrMember {
                        base: Box::new(CExpr::var("obj")),
                        member: "f_30".to_string(),
                    }),
                }),
            )]);

        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 0,
                is_write: false,
                field_name: "f_0",
                field_offset: 0,
                access_width: 4,
            },
        );

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("every returned member must have a FunctionRenderFacts member proof");

        assert!(
            reason.contains("FunctionRenderFacts member-access proof"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_rejects_external_layout_member_without_field_certificate() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &arch,
        );
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
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
                                ty: Some("uint64_t".to_string()),
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
        });
        let func =
            CFunction::new("field_external_only", CType::i64()).with_body(vec![CStmt::Return(
                Some(CExpr::Member {
                    base: Box::new(CExpr::var("arg0")),
                    member: "len".to_string(),
                }),
            )]);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("external layout alone must not certify executable member syntax");

        assert!(
            reason.contains(
                "rendered 1 field access(es) without FunctionRenderFacts member-access proof"
            ) && reason.contains("len"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_rejects_member_name_not_in_layout_certificate() {
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
        let func = CFunction::new("field_bad", CType::i64()).with_body(vec![CStmt::Return(Some(
            CExpr::Member {
                base: Box::new(CExpr::var("arg0")),
                member: "capacity".to_string(),
            },
        ))]);

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("mismatched member name must residualize");

        assert!(
            reason.contains(
                "rendered 1 field access(es) without FunctionRenderFacts member-access proof"
            ) && reason.contains("capacity"),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_rejects_repeated_array_member_access_without_array_render_proof() {
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
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            array_index_certificates: vec![ArrayIndexCertificate {
                slot: 0,
                base: Some(ArrayIndexBase::Param { index: 0 }),
                field_offset: 0,
                element_stride: 8,
            }],
            field_access_certificates: vec![FieldAccessCertificate {
                slot: 0,
                field_offset: 0,
                field_name: "len".to_string(),
                field_type: Some("int64_t".to_string()),
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
        });
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 0,
                is_write: false,
                field_name: "len",
                field_offset: 0,
                access_width: 8,
            },
        );
        add_member_render_fact(
            &mut function_facts,
            &prepared,
            TestMemberRenderFact {
                block_addr: 0x1000,
                op_index: 1,
                is_write: false,
                field_name: "len",
                field_offset: 0,
                access_width: 8,
            },
        );

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func)
            .expect("array member syntax must residualize without exact array render proof");

        assert!(
            reason.contains(
                "rendered 2 array access(es) without exact FunctionRenderFacts array-access proof"
            ),
            "{reason}"
        );
    }

    #[test]
    fn certified_standard_output_residualizes_repeated_array_member_access_without_render_node_identity()
     {
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
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            array_index_certificates: vec![ArrayIndexCertificate {
                slot: 0,
                base: Some(ArrayIndexBase::Param { index: 0 }),
                field_offset: 0,
                element_stride: 8,
            }],
            field_access_certificates: vec![FieldAccessCertificate {
                slot: 0,
                field_offset: 0,
                field_name: "len".to_string(),
                field_type: Some("int64_t".to_string()),
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
        });
        for op_index in [0, 1] {
            add_member_render_fact(
                &mut function_facts,
                &prepared,
                TestMemberRenderFact {
                    block_addr: 0x1000,
                    op_index,
                    is_write: false,
                    field_name: "len",
                    field_offset: 0,
                    access_width: 8,
                },
            );
            add_array_render_fact(
                &mut function_facts,
                &prepared,
                TestArrayRenderFact {
                    block_addr: 0x1000,
                    op_index,
                    is_write: false,
                    field_offset: 0,
                    element_stride: 8,
                    access_width: 8,
                },
            );
        }

        let reason = certified_standard_output_residual_reason(&prepared, &function_facts, &func);

        let reason = reason.expect("array syntax without render-node identity must residualize");
        assert!(reason.contains("rendered 2 array access(es) without exact FunctionRenderFacts"));
        assert!(reason.contains("first array node"));
    }

    #[test]
    fn certified_standard_output_accepts_repeated_array_member_access_with_exact_render_proofs() {
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
        let mut function_facts = test_function_facts_with_prepared_render(&prepared);
        function_facts.replace_type_facts(FunctionTypeFacts {
            array_index_certificates: vec![ArrayIndexCertificate {
                slot: 0,
                base: Some(ArrayIndexBase::Param { index: 0 }),
                field_offset: 0,
                element_stride: 8,
            }],
            field_access_certificates: vec![FieldAccessCertificate {
                slot: 0,
                field_offset: 0,
                field_name: "len".to_string(),
                field_type: Some("int64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        });
        for op_index in [0, 1] {
            add_member_render_fact(
                &mut function_facts,
                &prepared,
                TestMemberRenderFact {
                    block_addr: 0x1000,
                    op_index,
                    is_write: false,
                    field_name: "len",
                    field_offset: 0,
                    access_width: 8,
                },
            );
            add_array_render_fact(
                &mut function_facts,
                &prepared,
                TestArrayRenderFact {
                    block_addr: 0x1000,
                    op_index,
                    is_write: false,
                    field_offset: 0,
                    element_stride: 8,
                    access_width: 8,
                },
            );
        }
        let first_memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 0, false)
            .expect("first memory certificate");
        let second_memory_cert = prepared
            .memory_certificate_for_op_site(0x1000, 1, false)
            .expect("second memory certificate");
        let return_cert = prepared
            .return_certificate_for_op(0x1000, 3)
            .expect("return certificate");
        let effect_proofs = [
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 0,
                call_disposition: None,
                target: None,
                address: Some(first_memory_cert.address),
                value: first_memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::MemoryRead,
                block_addr: 0x1000,
                op_idx: 1,
                call_disposition: None,
                target: None,
                address: Some(second_memory_cert.address),
                value: second_memory_cert.value,
                values: Vec::new(),
                materialized_phi_copy: false,
            },
            EffectRenderProof {
                kind: EffectRenderProofKind::Return,
                block_addr: 0x1000,
                op_idx: 3,
                call_disposition: None,
                target: None,
                address: None,
                value: Some(return_cert.value),
                values: Vec::new(),
                materialized_phi_copy: false,
            },
        ];

        let reason = certified_standard_output_residual_reason_with_effect_proofs(
            &prepared,
            &function_facts,
            &func,
            Some(&effect_proofs),
        );

        assert_eq!(reason, None);
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
        let type_facts = decompiler.context.type_facts().clone();
        let mut route = test_decompile_route(
            r2types::DecompileRouteKind::Standard,
            "x86 struct-array pipeline test route",
            None,
            r2sym::RenderPermission::certified(
                r2sym::ProofOwner::R2engine,
                "x86 struct-array pipeline test route",
            ),
        );
        route.use_prepared_semantic_view = false;
        decompiler
            .set_function_facts(FunctionFacts::new(type_facts, None).with_decompile_route(route));

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
            function_facts: &decompiler.context.function_facts,
            certified_rendering_required: render_permission_allows_executable_c(
                decompiler.context.effective_render_permission(),
            ),
            stack_slots: &decompiler.context.type_facts().stack_slots,
            field_access_certificates: &decompiler.context.type_facts().field_access_certificates,
            #[cfg(test)]
            external_stack_vars: &decompiler.context.type_facts().external_stack_vars,
            visible_bindings: &decompiler.context.type_facts().visible_bindings,
            external_type_db: &decompiler.context.type_facts().external_type_db,
            param_register_aliases: &param_register_aliases,
            type_hints: &type_hints,
            type_oracle: combined_type_oracle
                .as_ref()
                .map(|oracle| oracle as &dyn TypeOracle),
            function_return_type: signature_ret_type.as_ref().or(Some(&inferred_ret_type)),
            prepared_ssa: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        fold_ctx.analyze_blocks(&fold_blocks);
        fold_ctx.analyze_function_structure(func);

        let eax2 = fold_ctx.get_expr(&r2ssa::SSAVar::new("EAX", 2, 4));
        let ecx1 = fold_ctx.get_expr(&r2ssa::SSAVar::new("ECX", 1, 4));
        let stmts = fold_ctx.fold_block(&fold_blocks[0], fold_blocks[0].addr);
        let mut structurer = ControlFlowStructurer::new(func, &fold_ctx);
        let body_stmt = structurer.structure();
        let normalized_body_stmt = fold_ctx.normalize_final_stmt_calls(body_stmt.clone());

        assert!(
            !matches!(eax2, CExpr::Member { .. } | CExpr::PtrMember { .. })
                && !matches!(ecx1, CExpr::Member { .. } | CExpr::PtrMember { .. }),
            "uncertified internal pipeline must not invent member loads without render certificates, eax2={eax2:?}, ecx1={ecx1:?}; params={params:?}; param_aliases={param_register_aliases:?}; type_hints={type_hints:?}"
        );
        assert!(
            stmts.iter().all(|stmt| !matches!(stmt, CStmt::Return(_)))
                && format!("{stmts:?}").contains("uncertified memory store")
                && format!("{stmts:?}").contains("missing certified value return"),
            "incomplete FunctionFacts must residualize this block instead of fabricating a return, got {stmts:?}"
        );
        assert!(
            !format!("{body_stmt:?}").contains("f_34")
                && !format!("{body_stmt:?}").contains("f_8")
                && !format!("{normalized_body_stmt:?}").contains("f_34")
                && !format!("{normalized_body_stmt:?}").contains("f_8"),
            "uncertified structuring must not preserve fake member loads, body={body_stmt:?}; normalized={normalized_body_stmt:?}"
        );
    }

    #[test]
    fn decompiler_prepends_vm_summary_semantic_comment() {
        let prepared = prepared_from_ops(
            vec![R2ILOp::Return {
                target: Varnode::constant(0, 8),
            }],
            &test_arch_for_decompile(),
        );

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
            Some(semantic_artifact),
        )
        .with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::VmSummary,
            "test-selected vm summary",
            None,
            r2sym::RenderPermission::summary(
                r2sym::ProofOwner::R2engine,
                "test-selected vm summary",
            ),
        ));
        let input = DecompilerInput::new(
            prepared,
            DecompilerContext::default().with_function_facts(function_facts),
        );

        let output = Decompiler::new(DecompilerConfig::default()).decompile_input(&input);
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
        .with_summary_set(Some(summary_set))
        .with_decompile_route(test_decompile_route(
            r2types::DecompileRouteKind::LinearWorker,
            "guarded structuring unavailable",
            None,
            r2sym::RenderPermission::summary(
                r2sym::ProofOwner::R2engine,
                "guarded structuring unavailable",
            ),
        ));
        assert!(function_facts.has_summary_conflicts());
        let context = DecompilerContext::from_function_facts(function_facts);
        let input = DecompilerInput::new(prepared, context);
        assert!(input.context.function_facts.has_summary_conflicts());
        let output = Decompiler::new(DecompilerConfig::default()).decompile_input(&input);

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
            &test_summary_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                "guarded structuring unavailable",
            ),
            DecompilerConfig::default(),
        )
        .expect("dense native-linear worker summary should render");

        assert!(output.contains("r2dec summary: semantic worker linear summary"));
        assert!(output.contains("native worker summaries: 8"));
        assert!(!output.contains("return summary_result;"));
    }

    #[test]
    fn semantic_worker_summary_handles_structured_worker_comment_only() {
        let semantic_artifact =
            large_cfg_worker_artifact(r2sym::RefinementStage::Compiled, Vec::new(), Vec::new());
        let signature = signature_spec(Some(CType::Int(32)), Vec::new());
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: external_signature_certificate(&signature),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            Some(semantic_artifact),
        );
        let output = render_semantic_worker_summary(
            "sym.structured_worker",
            &function_facts,
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
        function_facts.__test_set_summary_rollup(r2types::SummaryEffectRollup {
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
        function_facts.__test_set_summary_rollup(r2types::SummaryEffectRollup {
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
    fn autogenerated_name_detection_accepts_underscore_hex_labels() {
        assert!(is_autogenerated_function_name("_140010138"));
        assert!(is_autogenerated_function_name("_401000"));
        assert!(!is_autogenerated_function_name("_named_worker"));
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
