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
//! 6. **Binding Planning** (`binding_plan`): Project exact SSA identities into C bindings
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

pub(crate) mod analysis;
pub mod ast;
mod binding_plan;
pub(crate) mod codegen;
#[cfg(test)]
pub(crate) mod consumer_linear;
pub(crate) mod consumer_structured;
pub(crate) mod consumer_summary;
pub(crate) mod consumer_vm;
pub mod control;
mod effect_ledger;
pub(crate) mod fold;
pub mod highlight;
pub(crate) mod naming;
pub(crate) mod normalize;
mod observation_journal;
mod placement;
pub(crate) mod planner;
pub mod region;
mod shadow_report;
pub(crate) mod single_evaluation;
pub mod structure;
mod structured_region;
pub mod symbol;
pub(crate) mod unrendered;
mod variable;

use crate::codegen::{CodeGenerator, EmissionReadyFunction, prepare_function_for_emission};
use crate::fold::FoldingContext;
use crate::fold::context::{FoldArchConfig, FoldInputs};
use crate::observation_journal::{
    LegacyObservationCoverage, LegacyObservationJournal, MarkedNativeDraft, SealedNativeFunction,
};
pub use ast::{BinaryOp, CExpr, CFunction, CStmt, CType, UnaryOp};
pub use codegen::CodeGenConfig;
pub use control::{DecompileExecutionStop, DecompileWorkControl, DecompileWorkPhase};
pub use fold::lower_ssa_ops_to_stmts;
pub use highlight::highlight_c_ansi;
use r2ssa::SSAFunction;
#[cfg(test)]
use r2ssa::SSAOp;
use r2ssa::cfg::BlockTerminator;
use r2types::{
    CTypeLike, DecompileRouteFacts, DecompileRouteKind, FunctionFacts, FunctionTypeFacts,
    SourceEvidenceTypeOracle, TypeOracle,
};
#[cfg(test)]
use r2types::{ExternalTypeDb, FunctionType};
pub use region::{Region, RegionAnalyzer};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::rc::Rc;
#[cfg(test)]
use std::sync::Arc;
pub(crate) use structure::ControlFlowStructurer;

fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

#[cfg(test)]
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
        CType::BitVector(bits) => CTypeLike::Int {
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
            r2types::Signedness::Unsigned if *bits > 128 => CType::BitVector(*bits),
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

#[cfg(test)]
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
        match stmt.unobserved() {
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
fn note_unproven_constructs(
    func: &mut CFunction,
    ledger: Option<&r2ssa::ledger::ObligationLedger>,
) {
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
            let _ = write!(
                &mut line,
                "; {} statements rendered",
                count_body_statements(&func.body)
            );
            line
        }
        _ => detail,
    };
    func.body.insert(
        0,
        CStmt::comment(sanitize_comment_text(&format!("r2dec proof: {detail}"))),
    );
}

/// Statements the body holds, counting the ones nested inside control flow.
fn count_body_statements(stmts: &[CStmt]) -> usize {
    fn visit(stmt: &CStmt) -> usize {
        match stmt.unobserved() {
            CStmt::Comment(_) | CStmt::Empty => 0,
            CStmt::Block(inner) => inner.iter().map(visit).sum(),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => 1 + visit(then_body) + else_body.as_deref().map(visit).unwrap_or(0),
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => 1 + visit(body),
            CStmt::For { init, body, .. } => {
                1 + init.as_deref().map(visit).unwrap_or(0) + visit(body)
            }
            CStmt::Switch { cases, default, .. } => {
                1 + cases
                    .iter()
                    .map(|case| case.body.iter().map(visit).sum::<usize>())
                    .sum::<usize>()
                    + default
                        .as_ref()
                        .map(|body| body.iter().map(visit).sum::<usize>())
                        .unwrap_or(0)
            }
            _ => 1,
        }
    }
    stmts.iter().map(visit).sum()
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
        "r2dec refusal: the source obligation inventory did not close, so what this function owes was never enumerated ({failures} construction failures, {cycles} unstructured cycle blocks)"
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
    match stmt.unobserved() {
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

#[derive(Debug)]
enum BindingShadowFailure {
    Pairing,
    Report,
    IncompleteObservations {
        ledger: crate::shadow_report::ShadowLedger,
        coverage: LegacyObservationCoverage,
    },
    NonQuality {
        ledger: crate::shadow_report::ShadowLedger,
        coverage: LegacyObservationCoverage,
    },
}

#[derive(Debug)]
struct BindingShadow {
    ledger: crate::shadow_report::ShadowLedger,
    coverage: LegacyObservationCoverage,
}

#[derive(Debug)]
enum BindingShadowOutcome {
    Complete(BindingShadow),
    Failed(BindingShadowFailure),
}

impl BindingShadowOutcome {
    fn build(
        plan: &crate::binding_plan::BindingPlan,
        source: &r2types::function_facts::SourceOwnedFunctionFacts,
        legacy: &crate::shadow_report::LegacyAnalysisSnapshot,
        coverage: LegacyObservationCoverage,
    ) -> Self {
        if crate::fold::op_lower::PlannedLoweringInput::try_new(source, plan).is_err() {
            return Self::Failed(BindingShadowFailure::Pairing);
        }
        let report = match crate::shadow_report::ShadowReport::build(plan, source, legacy) {
            Ok(report) => report,
            Err(_) => return Self::Failed(BindingShadowFailure::Report),
        };
        if report.validate_against(plan, source, legacy).is_err() {
            return Self::Failed(BindingShadowFailure::Report);
        }
        let ledger = report.ledger(source);
        if !coverage.is_complete() {
            return Self::Failed(BindingShadowFailure::IncompleteObservations { ledger, coverage });
        }
        if !ledger.passes_quality() || !coverage.passes_quality() {
            return Self::Failed(BindingShadowFailure::NonQuality { ledger, coverage });
        }
        Self::Complete(BindingShadow { ledger, coverage })
    }
}

/// Public, renderer-independent counts for one binding-shadow domain.
///
/// These are audit results, not rendering inputs. Keeping the complete ledger
/// visible prevents a refusal or an unclassified cell from being counted as a
/// successful shadow run merely because no C was emitted for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindingShadowDomainAudit {
    pub total: usize,
    pub observed: usize,
    pub agree_correct: usize,
    pub old_wrong: usize,
    pub shadow_wrong: usize,
    pub both_wrong_equal: usize,
    pub both_wrong_different: usize,
    pub unclassified: usize,
    pub refused: usize,
}

impl BindingShadowDomainAudit {
    pub const fn equations_hold(self) -> bool {
        let Some(both_wrong) = self.both_wrong_equal.checked_add(self.both_wrong_different) else {
            return false;
        };
        let Some(classified) = self.agree_correct.checked_add(self.old_wrong) else {
            return false;
        };
        let Some(classified) = classified.checked_add(self.shadow_wrong) else {
            return false;
        };
        let Some(classified) = classified.checked_add(both_wrong) else {
            return false;
        };
        let Some(accounted) = classified.checked_add(self.unclassified) else {
            return false;
        };
        self.total == self.observed && self.observed == accounted
    }

    pub const fn passes_quality(self) -> bool {
        self.equations_hold()
            && self.shadow_wrong == 0
            && self.both_wrong_equal == 0
            && self.both_wrong_different == 0
            && self.unclassified == 0
            && self.refused == 0
    }
}

impl From<crate::shadow_report::DomainLedger> for BindingShadowDomainAudit {
    fn from(ledger: crate::shadow_report::DomainLedger) -> Self {
        Self {
            total: ledger.total,
            observed: ledger.observed,
            agree_correct: ledger.agree_correct,
            old_wrong: ledger.old_wrong,
            shadow_wrong: ledger.shadow_wrong,
            both_wrong_equal: ledger.both_wrong_equal,
            both_wrong_different: ledger.both_wrong_different,
            unclassified: ledger.unclassified,
            refused: ledger.refused,
        }
    }
}

/// Public count of exact legacy-render observations for one source domain.
///
/// This is deliberately separate from the shadow classification ledger. A
/// dense shadow report can classify `LegacyAbsent` as an old-renderer defect;
/// only this equation proves that the renderer actually accounted for every
/// source value, use, and write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindingObservationDomainAudit {
    pub total: usize,
    pub rendered: usize,
    pub justified_elision: usize,
    pub refused: usize,
    pub unaccounted: usize,
}

impl BindingObservationDomainAudit {
    pub const fn equations_hold(self) -> bool {
        let Some(accounted) = self.rendered.checked_add(self.justified_elision) else {
            return false;
        };
        let Some(accounted) = accounted.checked_add(self.refused) else {
            return false;
        };
        let Some(accounted) = accounted.checked_add(self.unaccounted) else {
            return false;
        };
        accounted == self.total
    }

    pub const fn is_complete(self) -> bool {
        self.equations_hold() && self.unaccounted == 0
    }

    pub const fn passes_quality(self) -> bool {
        self.is_complete() && self.refused == 0
    }
}

impl From<crate::observation_journal::LegacyObservationDomainCoverage>
    for BindingObservationDomainAudit
{
    fn from(coverage: crate::observation_journal::LegacyObservationDomainCoverage) -> Self {
        Self {
            total: coverage.total,
            rendered: coverage.rendered,
            justified_elision: coverage.justified_elision,
            refused: coverage.refused,
            unaccounted: coverage.unaccounted,
        }
    }
}

/// Exact V/U/W observation coverage, independent of shadow correctness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindingObservationAudit {
    pub values: BindingObservationDomainAudit,
    pub uses: BindingObservationDomainAudit,
    pub writes: BindingObservationDomainAudit,
}

impl BindingObservationAudit {
    pub const fn equations_hold(self) -> bool {
        self.values.equations_hold() && self.uses.equations_hold() && self.writes.equations_hold()
    }

    pub const fn is_complete(self) -> bool {
        self.values.is_complete() && self.uses.is_complete() && self.writes.is_complete()
    }

    pub const fn passes_quality(self) -> bool {
        self.values.passes_quality() && self.uses.passes_quality() && self.writes.passes_quality()
    }
}

impl From<LegacyObservationCoverage> for BindingObservationAudit {
    fn from(coverage: LegacyObservationCoverage) -> Self {
        Self {
            values: coverage.values.into(),
            uses: coverage.uses.into(),
            writes: coverage.writes.into(),
        }
    }
}

/// Observable Stage 4 ledger, kept separate from all renderer inputs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindingShadowAuditLedger {
    pub values: BindingShadowDomainAudit,
    pub uses: BindingShadowDomainAudit,
    pub writes: BindingShadowDomainAudit,
}

impl BindingShadowAuditLedger {
    pub const fn equations_hold(self) -> bool {
        self.values.equations_hold() && self.uses.equations_hold() && self.writes.equations_hold()
    }

    pub const fn passes_quality(self) -> bool {
        self.values.passes_quality() && self.uses.passes_quality() && self.writes.passes_quality()
    }
}

impl From<crate::shadow_report::ShadowLedger> for BindingShadowAuditLedger {
    fn from(ledger: crate::shadow_report::ShadowLedger) -> Self {
        Self {
            values: ledger.values.into(),
            uses: ledger.uses.into(),
            writes: ledger.writes.into(),
        }
    }
}

/// Stable public cause retained when the observation journal cannot be built or sealed.
///
/// The journal's implementation error type remains private because it also
/// carries renderer-only contracts.  This projection preserves every error
/// category and the canonical IDs or counts that are safe to expose across the
/// `r2dec`/`r2engine` boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingMachineProjectionFailure {
    UntrustedArtifactProvenance,
    IncompleteObligationInventory,
    MissingGraphValue {
        value: r2ssa::ValueId,
    },
    MissingGraphBlock {
        block: r2ssa::BlockId,
    },
    DuplicateBlockAddress {
        address: u64,
    },
    TopologyMismatch,
    MachineContextMismatch,
    MissingInstruction {
        inst: r2ssa::InstId,
    },
    MissingInstructionDisposition {
        inst: r2ssa::InstId,
    },
    MissingUseDisposition {
        site: r2ssa::UseSite,
    },
    MissingWriteDisposition {
        inst: r2ssa::InstId,
    },
    MissingOutput {
        inst: r2ssa::InstId,
    },
    InvalidValueWidth {
        value: r2ssa::ValueId,
        size_bytes: u32,
    },
    ConstantTooWide {
        value: r2ssa::ValueId,
        width_bits: u32,
    },
    WrongOperandCount {
        inst: r2ssa::InstId,
        expected: usize,
        actual: usize,
    },
    WidthMismatch {
        inst: r2ssa::InstId,
        expected_bits: u32,
        actual_bits: u32,
    },
    InvalidCastWidth {
        inst: r2ssa::InstId,
        kind: r2ssa::MachineCastKind,
        from_bits: u32,
        to_bits: u32,
    },
    InvalidSubpiece {
        inst: r2ssa::InstId,
        source_bits: u32,
        result_bits: u32,
        lsb_bits: u32,
    },
    InvalidChild {
        expr_index: usize,
        child_index: usize,
    },
    InvalidExpressionType {
        expr_index: usize,
    },
    DuplicateEntity {
        value: r2ssa::ValueId,
    },
    EntityMismatch {
        inst: r2ssa::InstId,
    },
    ObligationMismatch {
        inst: r2ssa::InstId,
    },
    UseDispositionMismatch {
        site: r2ssa::UseSite,
    },
    WriteDispositionMismatch {
        inst: r2ssa::InstId,
    },
    ObligationSourceMismatch {
        instruction: r2ssa::CanonicalInstructionId,
    },
    UnsupportedOperation {
        inst: r2ssa::InstId,
    },
}

impl BindingMachineProjectionFailure {
    pub const fn kind(self) -> &'static str {
        match self {
            Self::UntrustedArtifactProvenance => {
                "binding_plan_machine_untrusted_artifact_provenance"
            }
            Self::IncompleteObligationInventory => {
                "binding_plan_machine_incomplete_obligation_inventory"
            }
            Self::MissingGraphValue { .. } => "binding_plan_machine_missing_graph_value",
            Self::MissingGraphBlock { .. } => "binding_plan_machine_missing_graph_block",
            Self::DuplicateBlockAddress { .. } => "binding_plan_machine_duplicate_block_address",
            Self::TopologyMismatch => "binding_plan_machine_topology_mismatch",
            Self::MachineContextMismatch => "binding_plan_machine_context_mismatch",
            Self::MissingInstruction { .. } => "binding_plan_machine_missing_instruction",
            Self::MissingInstructionDisposition { .. } => {
                "binding_plan_machine_missing_instruction_disposition"
            }
            Self::MissingUseDisposition { .. } => "binding_plan_machine_missing_use_disposition",
            Self::MissingWriteDisposition { .. } => {
                "binding_plan_machine_missing_write_disposition"
            }
            Self::MissingOutput { .. } => "binding_plan_machine_missing_output",
            Self::InvalidValueWidth { .. } => "binding_plan_machine_invalid_value_width",
            Self::ConstantTooWide { .. } => "binding_plan_machine_constant_too_wide",
            Self::WrongOperandCount { .. } => "binding_plan_machine_wrong_operand_count",
            Self::WidthMismatch { .. } => "binding_plan_machine_width_mismatch",
            Self::InvalidCastWidth { kind, .. } => match kind {
                r2ssa::MachineCastKind::ZeroExtend => {
                    "binding_plan_machine_invalid_zero_extend_width"
                }
                r2ssa::MachineCastKind::SignExtend => {
                    "binding_plan_machine_invalid_sign_extend_width"
                }
                r2ssa::MachineCastKind::Truncate => "binding_plan_machine_invalid_truncate_width",
                r2ssa::MachineCastKind::BitReinterpret => {
                    "binding_plan_machine_invalid_bit_reinterpret_width"
                }
                r2ssa::MachineCastKind::IntegerToAddress => {
                    "binding_plan_machine_invalid_integer_to_address_width"
                }
                r2ssa::MachineCastKind::AddressToInteger => {
                    "binding_plan_machine_invalid_address_to_integer_width"
                }
            },
            Self::InvalidSubpiece { .. } => "binding_plan_machine_invalid_subpiece",
            Self::InvalidChild { .. } => "binding_plan_machine_invalid_child",
            Self::InvalidExpressionType { .. } => "binding_plan_machine_invalid_expression_type",
            Self::DuplicateEntity { .. } => "binding_plan_machine_duplicate_entity",
            Self::EntityMismatch { .. } => "binding_plan_machine_entity_mismatch",
            Self::ObligationMismatch { .. } => "binding_plan_machine_obligation_mismatch",
            Self::UseDispositionMismatch { .. } => "binding_plan_machine_use_disposition_mismatch",
            Self::WriteDispositionMismatch { .. } => {
                "binding_plan_machine_write_disposition_mismatch"
            }
            Self::ObligationSourceMismatch { instruction } => match instruction.site {
                r2ssa::CanonicalInstructionSite::Phi(storage) => match storage.space {
                    r2ssa::CanonicalStorageSpace::Ram => {
                        "binding_plan_machine_obligation_source_mismatch_phi_ram"
                    }
                    r2ssa::CanonicalStorageSpace::Register => {
                        "binding_plan_machine_obligation_source_mismatch_phi_register"
                    }
                    r2ssa::CanonicalStorageSpace::Unique => {
                        "binding_plan_machine_obligation_source_mismatch_phi_unique"
                    }
                    r2ssa::CanonicalStorageSpace::Constant => {
                        "binding_plan_machine_obligation_source_mismatch_phi_constant"
                    }
                    r2ssa::CanonicalStorageSpace::Custom(_) => {
                        "binding_plan_machine_obligation_source_mismatch_phi_custom"
                    }
                    r2ssa::CanonicalStorageSpace::Unknown => {
                        "binding_plan_machine_obligation_source_mismatch_phi_unknown"
                    }
                },
                r2ssa::CanonicalInstructionSite::Op(_) => {
                    "binding_plan_machine_obligation_source_mismatch_op"
                }
                r2ssa::CanonicalInstructionSite::NativeSpan { .. } => {
                    "binding_plan_machine_obligation_source_mismatch_native_span"
                }
            },
            Self::UnsupportedOperation { .. } => "binding_plan_machine_unsupported_operation",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingObservationJournalFailure {
    SourceAuthority,
    BindingPlanAuthority,
    BindingPlanMachineProjection(BindingMachineProjectionFailure),
    BindingPlanValueTopology {
        index: usize,
        value: r2ssa::ValueId,
    },
    BindingPlanDispositionCount {
        expected: usize,
        actual: usize,
    },
    BindingPlanBindingCount {
        expected: usize,
        actual: usize,
    },
    BindingPlanInvalidBindingReference {
        value: r2ssa::ValueId,
        binding_index: usize,
    },
    BindingPlanCertificateMembership {
        binding_index: usize,
    },
    BindingPlanDeclarationWidth {
        binding_index: usize,
    },
    BindingPlanInvalidLiteralInline {
        value: r2ssa::ValueId,
    },
    BindingPlanInvalidElisionProof {
        value: r2ssa::ValueId,
    },
    BindingPlanUnexpectedValueDisposition {
        value: r2ssa::ValueId,
    },
    BindingPlanStackObjectCount {
        expected: usize,
        actual: usize,
    },
    BindingPlanUnexpectedStackObjectDisposition {
        object: r2ssa::ObjectId,
    },
    BindingPlanStackObjectCertificate {
        object: r2ssa::ObjectId,
        binding_index: usize,
    },
    BindingPlanStackObjectDeclarationWidth {
        object: r2ssa::ObjectId,
        binding_index: usize,
    },
    BindingPlanParameterCount {
        expected: usize,
        actual: usize,
    },
    BindingPlanUnexpectedParameterDisposition {
        slot: u32,
    },
    BindingPlanParameterCertificate {
        slot: u32,
        binding_index: usize,
    },
    BindingPlanParameterDeclarationWidth {
        slot: u32,
        binding_index: usize,
    },
    NormalizationSourceAuthority,
    NormalizationBlockTopology,
    NormalizationRowCount {
        block_address: u64,
    },
    NormalizationOriginalInstruction {
        block_address: u64,
        op_idx: usize,
    },
    NormalizationOriginalCoverage,
    NormalizationPhiEdge {
        block_address: u64,
        op_idx: usize,
    },
    NormalizationRelocatedInitializer {
        block_address: u64,
        op_idx: usize,
    },
    NormalizationRemovedPhi,
    NormalizationRemovedPhiEdge,
    NormalizationInvalidCarrierCertificates,
    TooManyObservations,
    InvalidValue {
        value: r2ssa::ValueId,
    },
    InvalidCertifiedValueRead {
        value: r2ssa::ValueId,
        at: r2ssa::InstId,
    },
    InvalidUse {
        site: r2ssa::UseSite,
    },
    InvalidWrite {
        inst: r2ssa::InstId,
    },
    InvalidEffectObligation {
        obligation: r2ssa::SemanticObligationId,
    },
    OutputlessWrite {
        inst: r2ssa::InstId,
    },
    InvalidNormalizedSite {
        block: r2ssa::BlockId,
        op_idx: usize,
    },
    MissingNormalizedBlock {
        address: u64,
    },
    MissingNormalizedSiteContext,
    InvalidNormalizedInput {
        block: r2ssa::BlockId,
        op_idx: usize,
        input_idx: usize,
    },
    MissingNormalizedOutput {
        block: r2ssa::BlockId,
        op_idx: usize,
    },
    RefusedRenderedUse {
        site: r2ssa::UseSite,
    },
    RefusedRenderedWrite {
        inst: r2ssa::InstId,
    },
    RenderedValueRequired {
        value: r2ssa::ValueId,
    },
    PlannedElidedValueRendered {
        value: r2ssa::ValueId,
    },
    PlannedRefusedValueRendered {
        value: r2ssa::ValueId,
    },
    MissingPlannedValue {
        value: r2ssa::ValueId,
    },
    InvalidPlannedInline {
        value: r2ssa::ValueId,
        expr_index: usize,
    },
    ExactUseRequiresRenderedOccurrence {
        site: r2ssa::UseSite,
    },
    ExactWriteRequiresRenderedOccurrence {
        inst: r2ssa::InstId,
    },
    SymbolTableMismatch,
    UnownedBindingSymbol {
        value: r2ssa::ValueId,
        symbol_index: usize,
    },
    ConflictingValue {
        value: r2ssa::ValueId,
    },
    ConflictingUse {
        site: r2ssa::UseSite,
    },
    ConflictingWrite {
        inst: r2ssa::InstId,
    },
    ObservationDomainTooLarge {
        expected_count: usize,
    },
    ObservationCapacityUnavailable {
        expected_count: usize,
    },
    ObservationOutOfRange {
        observation_id: u32,
        expected_count: usize,
    },
    DuplicateObservation {
        observation_id: u32,
    },
}

impl BindingObservationJournalFailure {
    /// Stable machine-readable category used by the plugin JSON boundary.
    pub const fn kind(self) -> &'static str {
        match self {
            Self::SourceAuthority => "source_authority",
            Self::BindingPlanAuthority => "binding_plan_authority",
            Self::BindingPlanMachineProjection(failure) => failure.kind(),
            Self::BindingPlanValueTopology { .. } => "binding_plan_value_topology",
            Self::BindingPlanDispositionCount { .. } => "binding_plan_disposition_count",
            Self::BindingPlanBindingCount { .. } => "binding_plan_binding_count",
            Self::BindingPlanInvalidBindingReference { .. } => {
                "binding_plan_invalid_binding_reference"
            }
            Self::BindingPlanCertificateMembership { .. } => "binding_plan_certificate_membership",
            Self::BindingPlanDeclarationWidth { .. } => "binding_plan_declaration_width",
            Self::BindingPlanInvalidLiteralInline { .. } => "binding_plan_invalid_literal_inline",
            Self::BindingPlanInvalidElisionProof { .. } => "binding_plan_invalid_elision_proof",
            Self::BindingPlanUnexpectedValueDisposition { .. } => {
                "binding_plan_unexpected_value_disposition"
            }
            Self::BindingPlanStackObjectCount { .. } => "binding_plan_stack_object_count",
            Self::BindingPlanUnexpectedStackObjectDisposition { .. } => {
                "binding_plan_unexpected_stack_object_disposition"
            }
            Self::BindingPlanStackObjectCertificate { .. } => {
                "binding_plan_stack_object_certificate"
            }
            Self::BindingPlanStackObjectDeclarationWidth { .. } => {
                "binding_plan_stack_object_declaration_width"
            }
            Self::BindingPlanParameterCount { .. } => "binding_plan_parameter_count",
            Self::BindingPlanUnexpectedParameterDisposition { .. } => {
                "binding_plan_unexpected_parameter_disposition"
            }
            Self::BindingPlanParameterCertificate { .. } => "binding_plan_parameter_certificate",
            Self::BindingPlanParameterDeclarationWidth { .. } => {
                "binding_plan_parameter_declaration_width"
            }
            Self::NormalizationSourceAuthority => "normalization_source_authority",
            Self::NormalizationBlockTopology => "normalization_block_topology",
            Self::NormalizationRowCount { .. } => "normalization_row_count",
            Self::NormalizationOriginalInstruction { .. } => "normalization_original_instruction",
            Self::NormalizationOriginalCoverage => "normalization_original_coverage",
            Self::NormalizationPhiEdge { .. } => "normalization_phi_edge",
            Self::NormalizationRelocatedInitializer { .. } => "normalization_relocated_initializer",
            Self::NormalizationRemovedPhi => "normalization_removed_phi",
            Self::NormalizationRemovedPhiEdge => "normalization_removed_phi_edge",
            Self::NormalizationInvalidCarrierCertificates => {
                "normalization_invalid_carrier_certificates"
            }
            Self::TooManyObservations => "too_many_observations",
            Self::InvalidValue { .. } => "invalid_value",
            Self::InvalidCertifiedValueRead { .. } => "invalid_certified_value_read",
            Self::InvalidUse { .. } => "invalid_use",
            Self::InvalidWrite { .. } => "invalid_write",
            Self::InvalidEffectObligation { .. } => "invalid_effect_obligation",
            Self::OutputlessWrite { .. } => "outputless_write",
            Self::InvalidNormalizedSite { .. } => "invalid_normalized_site",
            Self::MissingNormalizedBlock { .. } => "missing_normalized_block",
            Self::MissingNormalizedSiteContext => "missing_normalized_site_context",
            Self::InvalidNormalizedInput { .. } => "invalid_normalized_input",
            Self::MissingNormalizedOutput { .. } => "missing_normalized_output",
            Self::RefusedRenderedUse { .. } => "refused_rendered_use",
            Self::RefusedRenderedWrite { .. } => "refused_rendered_write",
            Self::RenderedValueRequired { .. } => "rendered_value_required",
            Self::PlannedElidedValueRendered { .. } => "planned_elided_value_rendered",
            Self::PlannedRefusedValueRendered { .. } => "planned_refused_value_rendered",
            Self::MissingPlannedValue { .. } => "missing_planned_value",
            Self::InvalidPlannedInline { .. } => "invalid_planned_inline",
            Self::ExactUseRequiresRenderedOccurrence { .. } => {
                "exact_use_requires_rendered_occurrence"
            }
            Self::ExactWriteRequiresRenderedOccurrence { .. } => {
                "exact_write_requires_rendered_occurrence"
            }
            Self::SymbolTableMismatch => "symbol_table_mismatch",
            Self::UnownedBindingSymbol { .. } => "unowned_binding_symbol",
            Self::ConflictingValue { .. } => "conflicting_value",
            Self::ConflictingUse { .. } => "conflicting_use",
            Self::ConflictingWrite { .. } => "conflicting_write",
            Self::ObservationDomainTooLarge { .. } => "observation_domain_too_large",
            Self::ObservationCapacityUnavailable { .. } => "observation_capacity_unavailable",
            Self::ObservationOutOfRange { .. } => "observation_out_of_range",
            Self::DuplicateObservation { .. } => "duplicate_observation",
        }
    }
}

/// Typed reason a production binding-shadow audit did not complete cleanly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingShadowAuditFailure {
    PlanBuild,
    SourcePairing,
    JournalConstruction(BindingObservationJournalFailure),
    JournalRecording(BindingObservationJournalFailure),
    JournalSeal(BindingObservationJournalFailure),
    Placement(PlacementAuditRefusal),
    NonQualityObservations {
        observations: BindingObservationAudit,
    },
    Report,
    IncompleteObservations {
        ledger: BindingShadowAuditLedger,
        observations: BindingObservationAudit,
    },
    NonQuality {
        ledger: BindingShadowAuditLedger,
        observations: BindingObservationAudit,
    },
}

/// Non-consuming binding audit exposed to corpus and integration tooling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingShadowAuditOutcome {
    Complete {
        ledger: BindingShadowAuditLedger,
        observations: BindingObservationAudit,
    },
    Failed(BindingShadowAuditFailure),
    /// The selected route never entered the native Standard renderer.
    NotRun,
}

impl BindingShadowAuditOutcome {
    fn from_internal(outcome: &BindingShadowOutcome) -> Self {
        match outcome {
            BindingShadowOutcome::Complete(shadow) => Self::Complete {
                ledger: shadow.ledger.into(),
                observations: shadow.coverage.into(),
            },
            BindingShadowOutcome::Failed(BindingShadowFailure::Pairing) => {
                Self::Failed(BindingShadowAuditFailure::SourcePairing)
            }
            BindingShadowOutcome::Failed(BindingShadowFailure::Report) => {
                Self::Failed(BindingShadowAuditFailure::Report)
            }
            BindingShadowOutcome::Failed(BindingShadowFailure::IncompleteObservations {
                ledger,
                coverage,
            }) => Self::Failed(BindingShadowAuditFailure::IncompleteObservations {
                ledger: (*ledger).into(),
                observations: (*coverage).into(),
            }),
            BindingShadowOutcome::Failed(BindingShadowFailure::NonQuality { ledger, coverage }) => {
                Self::Failed(BindingShadowAuditFailure::NonQuality {
                    ledger: (*ledger).into(),
                    observations: (*coverage).into(),
                })
            }
        }
    }
}

/// Whether the final emission tree satisfied the source effect inventory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectObligationDisposition {
    Admitted,
    Refused,
    /// The selected route never entered the native Standard renderer.
    NotRun,
}

/// Stable source-effect tuple exposed independently of binding quality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EffectObligationAudit {
    pub disposition: EffectObligationDisposition,
    pub total: usize,
    pub rendered: usize,
    pub justified_elision: usize,
    pub refused: usize,
    pub unaccounted: usize,
    pub conflicts: usize,
}

impl EffectObligationAudit {
    pub const NOT_RUN: Self = Self {
        disposition: EffectObligationDisposition::NotRun,
        total: 0,
        rendered: 0,
        justified_elision: 0,
        refused: 0,
        unaccounted: 0,
        conflicts: 0,
    };

    fn from_ledger(ledger: &r2ssa::ledger::ObligationLedger) -> Self {
        let closure = ledger.close();
        let admitted = closure.refused == 0
            && closure.unattributed == 0
            && closure.conflicts == 0
            && closure.is_closed();
        Self {
            disposition: if admitted {
                EffectObligationDisposition::Admitted
            } else {
                EffectObligationDisposition::Refused
            },
            total: closure.total,
            rendered: closure.rendered,
            justified_elision: closure.elided,
            refused: closure.refused,
            unaccounted: closure.unattributed,
            conflicts: closure.conflicts,
        }
    }

    pub const fn is_admitted(self) -> bool {
        matches!(self.disposition, EffectObligationDisposition::Admitted)
    }
}

/// Stable reason the final native declaration-placement pass refused C.
///
/// Payloads contain only deterministic dense identities and counts. Private
/// renderer errors are projected into this type before crossing the r2dec API
/// boundary; their debug representations are never part of the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlacementAuditRefusal {
    MissingStructuredRegionArtifact,
    ObservationJournalUnavailable,
    SourceAuthorityMismatch,
    BindingOutsidePlan {
        binding_index: usize,
    },
    RegionOutsideArtifact {
        region_index: usize,
    },
    BlockOutsideFunction {
        block_address: u64,
    },
    RegionDoesNotDominateOccurrence {
        region_index: usize,
        block_address: u64,
    },
    ExternalBindingOutsidePlan {
        binding_index: usize,
    },
    RegionMarkerUnsealed,
    RegionMarkerForeign {
        anchor_index: usize,
    },
    RegionMarkerDuplicate {
        region_index: usize,
    },
    RegionMarkerMissing {
        region_index: usize,
    },
    RegionMarkerParentMismatch {
        region_index: usize,
    },
    RegionMarkerOutOfOrder {
        region_index: usize,
        expected_region_index: usize,
    },
    ObservationDomainTooLarge {
        expected_count: usize,
    },
    ObservationCapacityUnavailable {
        expected_count: usize,
    },
    ObservationOutOfRange {
        observation_id: u32,
        expected_count: usize,
    },
    DuplicateObservation {
        observation_id: u32,
    },
    MissingObservationTarget {
        observation_id: u32,
    },
    InvalidUse {
        instruction_id: u32,
        input_index: usize,
    },
    InvalidWrite {
        instruction_id: u32,
    },
    InvalidCertifiedValueRead {
        value_id: u32,
        instruction_id: u32,
    },
    MissingPlannedValue {
        value_id: u32,
    },
    RefusedPlannedValue {
        value_id: u32,
    },
    UnscopedObservation {
        observation_id: u32,
    },
    UnauthorizedProgramVariable {
        symbol_index: usize,
    },
    UnobservedBindingRead {
        binding_index: usize,
    },
    UnobservedBindingWrite {
        binding_index: usize,
    },
    NoDominatingRegion {
        binding_index: usize,
    },
    MissingDefinition {
        binding_index: usize,
    },
    ReadBeforeAssignment {
        binding_index: usize,
        instruction_id: u32,
        input_index: usize,
    },
    CertifiedValueReadBeforeAssignment {
        binding_index: usize,
        value_id: u32,
        instruction_id: u32,
    },
    UnprovableExecutionOrder {
        binding_index: usize,
    },
    AmbiguousObservationExecutionOrder {
        observation_id: u32,
    },
    MissingBinding {
        binding_index: usize,
    },
    MissingBindingSymbol {
        binding_index: usize,
    },
    ExternalBindingMissingParameter {
        binding_index: usize,
    },
    MissingRegion {
        region_index: usize,
    },
    DuplicateRegion {
        region_index: usize,
    },
    MissingInlineWrite {
        instruction_id: u32,
    },
    DuplicateInlineWrite {
        instruction_id: u32,
    },
    MissingBindingRole {
        binding_index: usize,
    },
    UndeclaredNames {
        count: usize,
    },
}

impl PlacementAuditRefusal {
    /// Stable machine-readable category used by engine and plugin boundaries.
    pub const fn kind(self) -> &'static str {
        match self {
            Self::MissingStructuredRegionArtifact => "missing_structured_region_artifact",
            Self::ObservationJournalUnavailable => "observation_journal_unavailable",
            Self::SourceAuthorityMismatch => "source_authority_mismatch",
            Self::BindingOutsidePlan { .. } => "binding_outside_plan",
            Self::RegionOutsideArtifact { .. } => "region_outside_artifact",
            Self::BlockOutsideFunction { .. } => "block_outside_function",
            Self::RegionDoesNotDominateOccurrence { .. } => "region_does_not_dominate_occurrence",
            Self::ExternalBindingOutsidePlan { .. } => "external_binding_outside_plan",
            Self::RegionMarkerUnsealed => "region_marker_unsealed",
            Self::RegionMarkerForeign { .. } => "region_marker_foreign",
            Self::RegionMarkerDuplicate { .. } => "region_marker_duplicate",
            Self::RegionMarkerMissing { .. } => "region_marker_missing",
            Self::RegionMarkerParentMismatch { .. } => "region_marker_parent_mismatch",
            Self::RegionMarkerOutOfOrder { .. } => "region_marker_out_of_order",
            Self::ObservationDomainTooLarge { .. } => "observation_domain_too_large",
            Self::ObservationCapacityUnavailable { .. } => "observation_capacity_unavailable",
            Self::ObservationOutOfRange { .. } => "observation_out_of_range",
            Self::DuplicateObservation { .. } => "duplicate_observation",
            Self::MissingObservationTarget { .. } => "missing_observation_target",
            Self::InvalidUse { .. } => "invalid_use",
            Self::InvalidWrite { .. } => "invalid_write",
            Self::InvalidCertifiedValueRead { .. } => "invalid_certified_value_read",
            Self::MissingPlannedValue { .. } => "missing_planned_value",
            Self::RefusedPlannedValue { .. } => "refused_planned_value",
            Self::UnscopedObservation { .. } => "unscoped_observation",
            Self::UnauthorizedProgramVariable { .. } => "unauthorized_program_variable",
            Self::UnobservedBindingRead { .. } => "unobserved_binding_read",
            Self::UnobservedBindingWrite { .. } => "unobserved_binding_write",
            Self::NoDominatingRegion { .. } => "no_dominating_region",
            Self::MissingDefinition { .. } => "missing_definition",
            Self::ReadBeforeAssignment { .. } => "read_before_assignment",
            Self::CertifiedValueReadBeforeAssignment { .. } => {
                "certified_value_read_before_assignment"
            }
            Self::UnprovableExecutionOrder { .. } => "unprovable_execution_order",
            Self::AmbiguousObservationExecutionOrder { .. } => {
                "ambiguous_observation_execution_order"
            }
            Self::MissingBinding { .. } => "missing_binding",
            Self::MissingBindingSymbol { .. } => "missing_binding_symbol",
            Self::ExternalBindingMissingParameter { .. } => "external_binding_missing_parameter",
            Self::MissingRegion { .. } => "missing_region",
            Self::DuplicateRegion { .. } => "duplicate_region",
            Self::MissingInlineWrite { .. } => "missing_inline_write",
            Self::DuplicateInlineWrite { .. } => "duplicate_inline_write",
            Self::MissingBindingRole { .. } => "missing_binding_role",
            Self::UndeclaredNames { .. } => "undeclared_names",
        }
    }
}

/// Independent final-tree declaration-placement audit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlacementAudit {
    Applied,
    Refused(PlacementAuditRefusal),
    /// The selected route never entered native declaration placement.
    NotRun,
}

impl PlacementAudit {
    pub const fn is_applied(self) -> bool {
        matches!(self, Self::Applied)
    }
}

/// Rendered C paired with the non-consuming Stage 4 binding audit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecompileRenderRefusal {
    MissingMachineProjectionAuthorization,
    MissingProgramVariableAuthorization,
    DeclarationPlacement(PlacementAuditRefusal),
    RefusedBindingDisposition {
        observations: BindingObservationAudit,
    },
    NormalizationOriginUnavailable,
    UnrepresentableControlFlow,
    IncompleteEffectInventory,
    UnrepresentableOperation,
}

impl DecompileRenderRefusal {
    /// Stable machine-readable category used by engine and corpus boundaries.
    pub const fn kind(self) -> &'static str {
        match self {
            Self::MissingMachineProjectionAuthorization => {
                "missing_machine_projection_authorization"
            }
            Self::MissingProgramVariableAuthorization => "missing_program_variable_authorization",
            Self::DeclarationPlacement(refusal) => refusal.kind(),
            Self::RefusedBindingDisposition { .. } => "refused_binding_disposition",
            Self::NormalizationOriginUnavailable => "normalization_origin_unavailable",
            Self::UnrepresentableControlFlow => "unrepresentable_control_flow",
            Self::IncompleteEffectInventory => "incomplete_effect_inventory",
            Self::UnrepresentableOperation => "unrepresentable_operation",
        }
    }
}

fn validate_sealed_region_occurrence_counts(
    occurrences: usize,
    region_nodes: usize,
) -> Result<(), DecompileRenderRefusal> {
    if occurrences == region_nodes {
        Ok(())
    } else {
        Err(DecompileRenderRefusal::UnrepresentableControlFlow)
    }
}

fn validate_sealed_region_occurrence_coverage(
    body: &crate::structured_region::SealedStructuredBody,
) -> Result<(), DecompileRenderRefusal> {
    let mut occurrences = 0usize;
    body.visit_occurrences(|_| occurrences += 1);
    validate_sealed_region_occurrence_counts(occurrences, body.regions().nodes().len())
}

impl From<BindingShadowAuditFailure> for DecompileRenderRefusal {
    fn from(failure: BindingShadowAuditFailure) -> Self {
        match failure {
            BindingShadowAuditFailure::Placement(refusal) => Self::DeclarationPlacement(refusal),
            BindingShadowAuditFailure::NonQualityObservations { observations } => {
                Self::RefusedBindingDisposition { observations }
            }
            BindingShadowAuditFailure::PlanBuild
            | BindingShadowAuditFailure::SourcePairing
            | BindingShadowAuditFailure::JournalConstruction(_)
            | BindingShadowAuditFailure::JournalRecording(_)
            | BindingShadowAuditFailure::JournalSeal(_)
            | BindingShadowAuditFailure::Report
            | BindingShadowAuditFailure::IncompleteObservations { .. }
            | BindingShadowAuditFailure::NonQuality { .. } => {
                Self::MissingMachineProjectionAuthorization
            }
        }
    }
}

impl From<crate::fold::op_lower::OpLoweringRefusal> for DecompileRenderRefusal {
    fn from(refusal: crate::fold::op_lower::OpLoweringRefusal) -> Self {
        match refusal {
            crate::fold::op_lower::OpLoweringRefusal::MissingMachineProjectionAuthorization => {
                Self::MissingMachineProjectionAuthorization
            }
            crate::fold::op_lower::OpLoweringRefusal::MissingProgramVariableAuthorization => {
                Self::MissingProgramVariableAuthorization
            }
            crate::fold::op_lower::OpLoweringRefusal::UnrepresentableOperation => {
                Self::UnrepresentableOperation
            }
        }
    }
}

fn rendered_identity_refusal_category(
    refusal: crate::binding_plan::RenderedIdentityRefusal,
) -> DecompileRenderRefusal {
    use crate::binding_plan::{RenderedIdentityRefusal, ValueRefusal};

    match refusal {
        RenderedIdentityRefusal::MachineUse { .. }
        | RenderedIdentityRefusal::MachineWrite { .. }
        | RenderedIdentityRefusal::MissingUseDisposition { .. }
        | RenderedIdentityRefusal::MissingWriteDisposition { .. }
        | RenderedIdentityRefusal::Value {
            reason:
                ValueRefusal::MissingLiteralProjection { .. }
                | ValueRefusal::IncoherentUseProjection { .. }
                | ValueRefusal::IncoherentWriteProjection { .. },
            ..
        } => DecompileRenderRefusal::MissingMachineProjectionAuthorization,
        RenderedIdentityRefusal::Value {
            reason:
                ValueRefusal::MissingBindingCertificate { .. }
                | ValueRefusal::UnsupportedDeclarationWidth { .. },
            ..
        }
        | RenderedIdentityRefusal::Parameter { .. }
        | RenderedIdentityRefusal::StackObject { .. }
        | RenderedIdentityRefusal::MissingBinding { .. }
        | RenderedIdentityRefusal::MissingValueDisposition { .. }
        | RenderedIdentityRefusal::MissingParameterDisposition { .. }
        | RenderedIdentityRefusal::MissingStackDisposition { .. } => {
            DecompileRenderRefusal::MissingProgramVariableAuthorization
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecompileBindingAudit {
    output: String,
    binding_shadow: BindingShadowAuditOutcome,
    effect_obligations: EffectObligationAudit,
    placement_audit: PlacementAudit,
    render_refusal: Option<DecompileRenderRefusal>,
}

impl DecompileBindingAudit {
    fn not_run(output: String) -> Self {
        Self {
            output,
            binding_shadow: BindingShadowAuditOutcome::NotRun,
            effect_obligations: EffectObligationAudit::NOT_RUN,
            placement_audit: PlacementAudit::NotRun,
            render_refusal: None,
        }
    }

    pub fn output(&self) -> &str {
        &self.output
    }

    pub fn into_output(self) -> String {
        self.output
    }

    pub const fn binding_shadow(&self) -> BindingShadowAuditOutcome {
        self.binding_shadow
    }

    pub const fn effect_obligations(&self) -> EffectObligationAudit {
        self.effect_obligations
    }

    pub const fn placement_audit(&self) -> PlacementAudit {
        self.placement_audit
    }

    pub const fn render_refusal(&self) -> Option<DecompileRenderRefusal> {
        self.render_refusal
    }
}

/// Rendered C whose same-run binding classification is deliberately deferred.
///
/// The engine uses this boundary to make every production cancellation and
/// deadline decision before the diagnostic shadow comparison runs. Finalizing
/// consumes the exact rendered product; dropping it emits the same C without
/// paying for or consulting the audit.
pub struct PendingDecompileBindingAudit {
    output: String,
    product: Option<(
        InternalBuildProduct,
        r2types::function_facts::SourceOwnedFunctionFacts,
    )>,
    ready: BindingShadowAuditOutcome,
    ready_effects: EffectObligationAudit,
    ready_placement: PlacementAudit,
    ready_refusal: Option<DecompileRenderRefusal>,
}

impl PendingDecompileBindingAudit {
    fn from_audit(audit: DecompileBindingAudit) -> Self {
        Self {
            output: audit.output,
            product: None,
            ready: audit.binding_shadow,
            ready_effects: audit.effect_obligations,
            ready_placement: audit.placement_audit,
            ready_refusal: audit.render_refusal,
        }
    }

    fn from_product(
        output: String,
        product: InternalBuildProduct,
        source: r2types::function_facts::SourceOwnedFunctionFacts,
    ) -> Self {
        Self {
            output,
            product: Some((product, source)),
            ready: BindingShadowAuditOutcome::NotRun,
            ready_effects: EffectObligationAudit::NOT_RUN,
            ready_placement: PlacementAudit::NotRun,
            ready_refusal: None,
        }
    }

    pub fn output(&self) -> &str {
        &self.output
    }

    pub fn into_output(self) -> String {
        self.output
    }

    pub fn finalize(self) -> DecompileBindingAudit {
        let (binding_shadow, effect_obligations, placement_audit, render_refusal) =
            self.product.map_or(
                (
                    self.ready,
                    self.ready_effects,
                    self.ready_placement,
                    self.ready_refusal,
                ),
                |(product, source)| {
                    (
                        product.binding_shadow(&source),
                        product.effect_obligations(),
                        product.placement_audit(),
                        product.render_refusal(),
                    )
                },
            );
        DecompileBindingAudit {
            output: self.output,
            binding_shadow,
            effect_obligations,
            placement_audit,
            render_refusal,
        }
    }
}

/// Private result of one source-authority-bound native build.
///
/// Native output retains the exact binding plan and final-AST observations.
/// Residual output is marker-free and carries no pretend native audit.
enum InternalBuildProduct {
    Native(SealedNativeFunction),
    Residual(EmissionReadyFunction),
    Refused {
        emission: EmissionReadyFunction,
        refusal: DecompileRenderRefusal,
        binding_shadow: BindingShadowAuditOutcome,
        placement_audit: PlacementAudit,
    },
}

enum PreparedDecompile {
    Immediate(DecompileBindingAudit),
    NativeOrResidual(InternalBuildProduct),
}

impl InternalBuildProduct {
    fn residual(function: CFunction) -> Self {
        Self::Residual(prepare_function_for_emission(&function))
    }

    fn refused(function: CFunction, refusal: DecompileRenderRefusal) -> Self {
        Self::Refused {
            emission: prepare_function_for_emission(&function),
            refusal: refusal.into(),
            binding_shadow: BindingShadowAuditOutcome::NotRun,
            placement_audit: PlacementAudit::NotRun,
        }
    }

    fn refused_after_native_admission(
        function: CFunction,
        failure: BindingShadowAuditFailure,
    ) -> Self {
        let refusal = DecompileRenderRefusal::from(failure);
        let placement_audit = match failure {
            BindingShadowAuditFailure::Placement(refusal) => PlacementAudit::Refused(refusal),
            BindingShadowAuditFailure::NonQualityObservations { .. } => PlacementAudit::Applied,
            _ => PlacementAudit::NotRun,
        };
        Self::Refused {
            emission: prepare_function_for_emission(&function),
            refusal,
            binding_shadow: BindingShadowAuditOutcome::Failed(failure),
            placement_audit,
        }
    }

    fn emission(&self) -> &EmissionReadyFunction {
        match self {
            Self::Native(native) => native.emission(),
            Self::Residual(ready) => ready,
            Self::Refused { emission, .. } => emission,
        }
    }

    fn into_function(self) -> CFunction {
        match self {
            Self::Native(native) => native.into_function(),
            Self::Residual(ready) => ready.into_function(),
            Self::Refused { emission, .. } => emission.into_function(),
        }
    }

    fn binding_shadow(
        &self,
        source: &r2types::SourceOwnedFunctionFacts,
    ) -> BindingShadowAuditOutcome {
        let native = match self {
            Self::Native(native) => native,
            Self::Refused { binding_shadow, .. } => return *binding_shadow,
            Self::Residual(_) => return BindingShadowAuditOutcome::NotRun,
        };
        let (observations, coverage) = match native.audit_observations() {
            Ok(observations) => observations,
            Err(failure) => return BindingShadowAuditOutcome::Failed(failure),
        };
        let outcome = BindingShadowOutcome::build(native.plan(), source, observations, coverage);
        BindingShadowAuditOutcome::from_internal(&outcome)
    }

    fn effect_obligations(&self) -> EffectObligationAudit {
        match self {
            Self::Native(native) => native.effect_obligation_audit(),
            Self::Residual(_) | Self::Refused { .. } => EffectObligationAudit::NOT_RUN,
        }
    }

    fn placement_audit(&self) -> PlacementAudit {
        match self {
            Self::Native(native) => native.placement_audit(),
            Self::Refused {
                placement_audit, ..
            } => *placement_audit,
            Self::Residual(_) => PlacementAudit::NotRun,
        }
    }

    fn render_refusal(&self) -> Option<DecompileRenderRefusal> {
        match self {
            Self::Refused { refusal, .. } => Some(*refusal),
            Self::Native(_) | Self::Residual(_) => None,
        }
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
        self.decompile_input_with_binding_audit_and_control(input, control)
            .map(DecompileBindingAudit::into_output)
    }

    /// Decompile and expose the non-consuming binding-shadow audit.
    ///
    /// The audit is constructed only after the final production poll. Its
    /// outcome therefore cannot change the C output or a cancellation/deadline
    /// decision made by the rendering path.
    pub fn decompile_input_with_binding_audit(
        &self,
        input: &DecompilerInput,
    ) -> DecompileBindingAudit {
        let control = r2ssa::SsaExecutionControl::default();
        self.decompile_input_with_binding_audit_and_control(input, &control)
            .expect("default decompiler control never stops")
    }

    fn prepare_decompile_with_control<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<PreparedDecompile, DecompileExecutionStop> {
        let work = DecompileWorkControl::new(control, DecompileWorkPhase::Normalization);
        work.poll()?;
        let func = input.prepared_ssa().function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let block_count = func.blocks().count();
        if block_count > self.config.max_blocks {
            return Ok(PreparedDecompile::Immediate(
                DecompileBindingAudit::not_run(block_guard_fallback_comment(
                    &func_name,
                    block_count,
                    self.config.max_blocks,
                )),
            ));
        }
        let function_facts = input.function_facts();
        let Some(semantic_route) = function_facts.decompile_route() else {
            return Ok(PreparedDecompile::Immediate(
                DecompileBindingAudit::not_run(missing_decompile_route_residual_comment(
                    &func_name,
                )),
            ));
        };
        if let Some(reason) = route_fallback_reason(semantic_route) {
            return Ok(PreparedDecompile::Immediate(
                DecompileBindingAudit::not_run(artifact_guard_fallback_comment(&func_name, reason)),
            ));
        }
        if let Some(reason) = summary_only_semantics_standard_render_residual_reason(
            function_facts.decompile_route(),
            function_facts.semantic_report(),
        ) {
            return Ok(PreparedDecompile::Immediate(
                DecompileBindingAudit::not_run(artifact_guard_fallback_comment(
                    &func_name, &reason,
                )),
            ));
        }
        if let Some(output) =
            self.vm_summary_output_for_route(&func_name, function_facts, semantic_route)
        {
            return Ok(PreparedDecompile::Immediate(
                DecompileBindingAudit::not_run(output),
            ));
        }
        if let Some(output) = self.semantic_worker_summary_output_for_route(
            &func_name,
            function_facts,
            semantic_route,
        ) {
            return Ok(PreparedDecompile::Immediate(
                DecompileBindingAudit::not_run(output),
            ));
        }
        self.build_product_from_input_with_control(input, control)
            .map(PreparedDecompile::NativeOrResidual)
    }

    /// Controlled form of [`Self::decompile_input_with_binding_audit`].
    pub fn decompile_input_with_binding_audit_and_control<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<DecompileBindingAudit, DecompileExecutionStop> {
        let product = match self.prepare_decompile_with_control(input, control)? {
            PreparedDecompile::Immediate(audit) => return Ok(audit),
            PreparedDecompile::NativeOrResidual(product) => product,
        };
        let render_work = DecompileWorkControl::new(control, DecompileWorkPhase::Rendering);
        render_work.poll()?;
        let output =
            CodeGenerator::new(self.config.codegen.clone()).generate_function(product.emission());
        // This is deliberately the last production work-control decision.
        // Everything below classifies the already sealed observation journal.
        render_work.poll()?;
        let binding_shadow = product.binding_shadow(input.source_owned_facts());
        let effect_obligations = product.effect_obligations();
        let placement_audit = product.placement_audit();
        Ok(DecompileBindingAudit {
            output,
            binding_shadow,
            effect_obligations,
            placement_audit,
            render_refusal: product.render_refusal(),
        })
    }

    /// Render, keeping whatever was produced when a phase stopped.
    ///
    /// `decompile_input_with_control` returns only the stop, so a caller has to
    /// discard the rendering to report that a budget ran out. That is why
    /// `RefusalReason::BudgetExhausted` has never been constructed: the ledger
    /// that would record it lives in the rendering being thrown away, and a
    /// function that ran out of time reports as one that produced nothing.
    ///
    /// A stop while building the C function has no partial to keep. A stop
    /// during rendering does -- the function is built by then, and generating it
    /// is what the caller wanted.
    pub fn decompile_input_keeping_partial<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<String, (DecompileExecutionStop, Option<String>)> {
        self.decompile_input_keeping_partial_with_pending_binding_audit(input, control)
            .map(PendingDecompileBindingAudit::into_output)
            .map_err(|(stop, partial)| {
                (stop, partial.map(PendingDecompileBindingAudit::into_output))
            })
    }

    /// Render with a same-run binding audit, retaining both after a rendering stop.
    ///
    /// A product-bound partial is classified from the exact product that was
    /// rendered. The audit is never rebuilt, and its construction performs no
    /// work-control poll. Stops before a product exists therefore retain no
    /// partial; either rendering poll retains the already sealed product's C and
    /// audit together.
    pub fn decompile_input_keeping_partial_with_binding_audit<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<DecompileBindingAudit, (DecompileExecutionStop, Option<DecompileBindingAudit>)>
    {
        self.decompile_input_keeping_partial_with_pending_binding_audit(input, control)
            .map(PendingDecompileBindingAudit::finalize)
            .map_err(|(stop, partial)| (stop, partial.map(PendingDecompileBindingAudit::finalize)))
    }

    /// Render while deferring non-consuming binding classification until the
    /// caller has made every production control decision.
    pub fn decompile_input_keeping_partial_with_pending_binding_audit<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<
        PendingDecompileBindingAudit,
        (DecompileExecutionStop, Option<PendingDecompileBindingAudit>),
    > {
        let product = match self.prepare_decompile_with_control(input, control) {
            Ok(PreparedDecompile::Immediate(audit)) => {
                return Ok(PendingDecompileBindingAudit::from_audit(audit));
            }
            Ok(PreparedDecompile::NativeOrResidual(product)) => product,
            Err(stop) => return Err((stop, None)),
        };
        let render_work = DecompileWorkControl::new(control, DecompileWorkPhase::Rendering);
        if let Err(stop) = render_work.poll() {
            let output = CodeGenerator::new(self.config.codegen.clone())
                .generate_function(product.emission());
            return Err((
                stop,
                Some(PendingDecompileBindingAudit::from_product(
                    output,
                    product,
                    input.source_owned_facts().clone(),
                )),
            ));
        }
        let output =
            CodeGenerator::new(self.config.codegen.clone()).generate_function(product.emission());
        if let Err(stop) = render_work.poll() {
            return Err((
                stop,
                Some(PendingDecompileBindingAudit::from_product(
                    output,
                    product,
                    input.source_owned_facts().clone(),
                )),
            ));
        }
        Ok(PendingDecompileBindingAudit::from_product(
            output,
            product,
            input.source_owned_facts().clone(),
        ))
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
        self.build_product_from_input_with_control(input, control)
            .map(InternalBuildProduct::into_function)
    }

    fn build_product_from_input_with_control<'a>(
        &self,
        input: &'a DecompilerInput,
        control: &'a dyn r2ssa::SsaWorkControl,
    ) -> Result<InternalBuildProduct, DecompileExecutionStop> {
        let work = DecompileWorkControl::new(control, DecompileWorkPhase::Normalization);
        work.poll()?;
        let func = input.prepared_ssa().function();
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let block_count = func.blocks().count();
        if block_count > self.config.max_blocks {
            return Ok(InternalBuildProduct::residual(
                residual_function_for_render_boundary(
                    &func_name,
                    &block_guard_fallback_comment(&func_name, block_count, self.config.max_blocks),
                ),
            ));
        }
        let decompiler = Self::new(self.config.clone()).with_context(input.context_projection());
        let Some(semantic_route) = decompiler.context.function_facts.decompile_route() else {
            return Ok(InternalBuildProduct::residual(
                residual_function_for_render_boundary(
                    &func_name,
                    &missing_decompile_route_residual_comment(&func_name),
                ),
            ));
        };
        if let Some(reason) = route_fallback_reason(semantic_route) {
            return Ok(InternalBuildProduct::residual(
                residual_function_for_render_boundary(&func_name, reason),
            ));
        }
        if let Some(reason) = summary_only_semantics_standard_render_residual_reason(
            decompiler.context.function_facts.decompile_route(),
            decompiler.context.function_facts.semantic_report(),
        ) {
            return Ok(InternalBuildProduct::residual(
                residual_function_for_render_boundary(&func_name, &reason),
            ));
        }
        if route_is_summary_boundary(semantic_route) {
            return Ok(InternalBuildProduct::residual(
                residual_function_for_summary_route_boundary(&func_name, semantic_route),
            ));
        }
        decompiler.build_function_internal_with_control(input, semantic_route, work)
    }

    pub(crate) fn prepend_comment(stmt: CStmt, text: String) -> CStmt {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        let comment = CStmt::comment(text);
        match semantic {
            CStmt::Empty => CStmt::Block(vec![comment]),
            CStmt::Block(mut stmts) => {
                // Inserting a new sibling splits the observed block position;
                // no existing child is an exact owner for its outer markers.
                // Nested child observations remain intact.
                stmts.insert(0, comment);
                CStmt::Block(stmts)
            }
            other => CStmt::Block(vec![comment, observations.reapply(other)]),
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
    ) -> structure::ControlFlowStructureResult<Vec<CStmt>> {
        let blocks: Vec<_> = func.blocks().cloned().collect();
        let mut stmts = Vec::new();

        for block in &blocks {
            stmts.push(CStmt::Label(Self::linear_block_label(block.addr)));
            for stmt in fold_ctx.fold_block(block, block.addr)? {
                if !matches!(stmt, CStmt::Empty) {
                    stmts.push(stmt);
                }
            }
            if let Some(terminator_stmt) = Self::linearized_terminator_stmt(func, fold_ctx, block) {
                stmts.push(terminator_stmt);
            }
        }

        Ok(stmts)
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
    ) -> Result<InternalBuildProduct, DecompileExecutionStop> {
        // The names this rendering declares, from the first pass that mints one.
        let symbol_table =
            std::rc::Rc::new(std::cell::RefCell::new(crate::symbol::SymbolTable::new()));
        let symbols = &*symbol_table;

        work.poll()?;
        let prepared = input.prepared_ssa();
        let func = prepared.function();
        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
            let graph = prepared.graph();
            let live = prepared.live_out();
            let dead = r2ssa::deadphi::DeadPhis::find(func, graph, &live);
            let total: usize = func.blocks().map(|b| b.phis.len()).sum();
            eprintln!(
                "MERGES fn={:#x} phis={} unobserved={} live_out={} unresolved={}",
                func.entry,
                total,
                dead.len(),
                live.len(),
                live.unresolved_blocks().count()
            );
            // Which merges the carrier gate admits, and which it turns away. The
            // gate is one question asked per phi, so printing its answer beside the
            // merge names the value that is lost rather than the layer that lost it.
            let render_facts = self.context.function_facts.render();
            for block in func.blocks() {
                for phi in &block.phis {
                    let value = graph.value_id_for_var(&phi.dst);
                    let carrier = value.is_some_and(|value| {
                        render_facts
                            .is_some_and(|facts| facts.loop_carrier_for_value(value).is_some())
                    });
                    eprintln!(
                        "MERGEPHI block={:#x} dst={} size={} value={:?} carrier={}",
                        block.addr,
                        phi.dst.display_name(),
                        phi.dst.size,
                        value,
                        carrier
                    );
                }
            }
            // What each carrier member is spelled as, so a member that some other
            // table also answers for shows up as a name the body never uses.
            if let Some(facts) = render_facts {
                // A carrier the alias map drops is spelled by whatever else answers
                // for its name, so the two filters that drop one are printed by name.
                let mirrored = prepared.memory_mirrored_carriers();
                let reused = prepared.carriers_spanning_a_reuse();
                let spans = prepared.storage_spans();
                for carrier in facts.loop_carriers() {
                    if let r2types::CertifiedEntity::LoopCarrier {
                        id,
                        phi,
                        identity_values,
                        entries,
                        updates,
                        ..
                    } = carrier
                    {
                        eprintln!(
                            "CARRIERFILTER id={:?} phi={:?} var={} mirrored={} reused={}",
                            id,
                            phi,
                            graph
                                .value(*phi)
                                .map(|value| value.var.display_name())
                                .unwrap_or_default(),
                            mirrored.contains(id),
                            reused.contains(id)
                        );
                        // A member in a second span is what makes a carrier span a
                        // reuse, so each member prints with the span it landed in.
                        let members = identity_values
                            .iter()
                            .copied()
                            .chain(entries.iter().map(|edge| edge.value))
                            .chain(updates.iter().flat_map(|update| {
                                std::iter::once(update.value)
                                    .chain(update.identity_values.iter().copied())
                            }))
                            .collect::<std::collections::BTreeSet<_>>();
                        for member in members {
                            eprintln!(
                                "  MEMBER value={:?} var={} storage={:?} span={:?}",
                                member,
                                graph
                                    .value(member)
                                    .map(|value| value.var.display_name())
                                    .unwrap_or_default(),
                                graph
                                    .value(member)
                                    .and_then(|value| value.canonical_storage),
                                spans.span_of(member)
                            );
                        }
                    }
                }
            }
        }
        let normalization_refusal = |error: normalize::NormalizationOriginError| {
            let func_name = func
                .name
                .clone()
                .unwrap_or_else(|| format!("sub_{:x}", func.entry));
            residual_function_for_render_boundary(
                &func_name,
                &format!("normalization origin refusal: {error}"),
            )
        };
        let (mut normalized_func, mut normalization_origins) =
            if let Some(render_facts) = self.context.function_facts.render() {
                match normalize::materialize_certified_loop_carriers_with_control(
                    func,
                    prepared,
                    render_facts,
                    work,
                ) {
                    Ok(result) => result,
                    Err(normalize::NormalizationFailure::Execution(error)) => return Err(error),
                    Err(normalize::NormalizationFailure::Origins(error)) => {
                        return Ok(InternalBuildProduct::refused(
                            normalization_refusal(error),
                            DecompileRenderRefusal::NormalizationOriginUnavailable,
                        ));
                    }
                }
            } else {
                (
                    func.clone(),
                    normalize::NormalizationOrigins::for_unchanged(func, prepared),
                )
            };
        if let Some(render_facts) = self.context.function_facts.render() {
            if let Err(error) =
                normalize::materialize_certified_loop_carrier_initializers_with_control(
                    &mut normalized_func,
                    &mut normalization_origins,
                    prepared,
                    render_facts,
                    work,
                )
            {
                match error {
                    normalize::NormalizationFailure::Execution(error) => return Err(error),
                    normalize::NormalizationFailure::Origins(error) => {
                        return Ok(InternalBuildProduct::refused(
                            normalization_refusal(error),
                            DecompileRenderRefusal::NormalizationOriginUnavailable,
                        ));
                    }
                }
            }
        }
        if let Err(error) = normalization_origins.validate(
            &normalized_func,
            prepared,
            self.context.function_facts.render(),
        ) {
            let func_name = func
                .name
                .clone()
                .unwrap_or_else(|| format!("sub_{:x}", func.entry));
            return Ok(InternalBuildProduct::refused(
                residual_function_for_render_boundary(
                    &func_name,
                    &format!("normalization origin refusal: {error:?}"),
                ),
                DecompileRenderRefusal::NormalizationOriginUnavailable,
            ));
        }
        let binding_plan =
            match crate::binding_plan::BindingPlan::build_shadow(input.source_owned_facts()) {
                Ok(plan) => std::rc::Rc::new(plan),
                Err(error) => {
                    let refusal = match error {
                        crate::binding_plan::BindingPlanBuildError::MachineProjection(_)
                        | crate::binding_plan::BindingPlanBuildError::Seal(
                            crate::binding_plan::BindingPlanSourceMismatch::MachineProjection(_),
                        ) => DecompileRenderRefusal::MissingMachineProjectionAuthorization,
                        _ => DecompileRenderRefusal::MissingProgramVariableAuthorization,
                    };
                    return Ok(InternalBuildProduct::refused(
                        residual_function_for_render_boundary(
                            &func
                                .name
                                .clone()
                                .unwrap_or_else(|| format!("sub_{:x}", func.entry)),
                            &format!("native render refusal: {}", refusal.kind()),
                        ),
                        refusal,
                    ));
                }
            };
        if let Err(error) = crate::fold::op_lower::PlannedLoweringInput::try_new(
            input.source_owned_facts(),
            &binding_plan,
        ) {
            let refusal = match error {
                crate::binding_plan::BindingPlanSourceMismatch::MachineProjection(_) => {
                    DecompileRenderRefusal::MissingMachineProjectionAuthorization
                }
                _ => DecompileRenderRefusal::MissingProgramVariableAuthorization,
            };
            return Ok(InternalBuildProduct::refused(
                residual_function_for_render_boundary(
                    &func
                        .name
                        .clone()
                        .unwrap_or_else(|| format!("sub_{:x}", func.entry)),
                    &format!("native render refusal: {}", refusal.kind()),
                ),
                refusal,
            ));
        }
        let binding_names = match crate::binding_plan::BindingNameResolution::build(
            input.source_owned_facts(),
            std::rc::Rc::clone(&binding_plan),
            std::rc::Rc::clone(&symbol_table),
        ) {
            Ok(names) => std::rc::Rc::new(names),
            Err(error) => {
                let refusal = match error {
                    crate::binding_plan::BindingNameResolutionError::Source(
                        crate::binding_plan::BindingPlanSourceMismatch::MachineProjection(_),
                    ) => DecompileRenderRefusal::MissingMachineProjectionAuthorization,
                    crate::binding_plan::BindingNameResolutionError::Source(_)
                    | crate::binding_plan::BindingNameResolutionError::ConflictingCertifiedRoles(
                        _,
                    ) => DecompileRenderRefusal::MissingProgramVariableAuthorization,
                };
                return Ok(InternalBuildProduct::refused(
                    residual_function_for_render_boundary(
                        &func
                            .name
                            .clone()
                            .unwrap_or_else(|| format!("sub_{:x}", func.entry)),
                        &format!("native render refusal: {}", refusal.kind()),
                    ),
                    refusal,
                ));
            }
        };
        let func = &normalized_func;
        let func_name = func
            .name
            .clone()
            .unwrap_or_else(|| format!("sub_{:x}", func.entry));
        let observation_journal = match LegacyObservationJournal::new(
            input.source_owned_facts(),
            &normalized_func,
            &normalization_origins,
            Rc::clone(&binding_plan),
            Rc::clone(&symbol_table),
        ) {
            Ok(journal) => std::cell::RefCell::new(journal),
            Err(_) => {
                let refusal = DecompileRenderRefusal::MissingMachineProjectionAuthorization;
                return Ok(InternalBuildProduct::refused(
                    residual_function_for_render_boundary(
                        &func_name,
                        &format!("native render refusal: {}", refusal.kind()),
                    ),
                    refusal,
                ));
            }
        };
        work.poll()?;
        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
            // What materialisation left behind, so a carrier update that renders
            // more than once shows which ops the fold was handed.
            for block in normalized_func.blocks() {
                for (index, op) in block.ops.iter().enumerate() {
                    let op: &r2ssa::SSAOp = op;
                    let kind = format!("{op:?}");
                    let kind = kind
                        .split(|c: char| c == ' ' || c == '{')
                        .next()
                        .unwrap_or("?");
                    eprintln!(
                        "NORMOP block={:#x} idx={index} kind={kind} dst={:?} srcs={:?}",
                        block.addr,
                        op.dst().map(|var| var.display_name()),
                        op.sources()
                            .iter()
                            .map(|var| var.display_name())
                            .collect::<Vec<_>>()
                    );
                }
            }
        }
        let render_signature = self.context.type_facts().render_authorized_signature();
        let evidence_type_oracle = SourceEvidenceTypeOracle::new(
            prepared,
            input.source_owned_facts().evidence_types(),
            &self.context.type_facts().external_type_db,
        );
        let type_oracle = Some(&evidence_type_oracle as &dyn TypeOracle);
        let params = match binding_names
            .parameters()
            .map(|resolved| {
                let resolved = resolved?;
                let ty = usize::try_from(resolved.slot)
                    .ok()
                    .and_then(|slot| {
                        render_signature.and_then(|signature| signature.params.get(slot))
                    })
                    .and_then(|parameter| parameter.ty.as_ref())
                    .map(type_like_to_ctype)
                    .unwrap_or(resolved.declaration_type);
                Ok(ast::CParam {
                    ty,
                    name: resolved.symbol,
                })
            })
            .collect::<Result<Vec<_>, crate::binding_plan::RenderedIdentityRefusal>>()
        {
            Ok(params) => params,
            Err(error) => {
                let refusal = rendered_identity_refusal_category(error);
                return Ok(InternalBuildProduct::refused(
                    residual_function_for_render_boundary(
                        &func_name,
                        &format!("native render refusal: {}", refusal.kind()),
                    ),
                    refusal,
                ));
            }
        };
        let inferred_ret_type =
            evidence_return_type(prepared, input.source_owned_facts().evidence_types());
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
            flag_regs: prepared
                .machine_context()
                .flag_register_names()
                .into_iter()
                .collect(),
        };
        let prepared_semantic_view = match analysis::PreparedSemanticView::build_with_bindings(
            symbols,
            analysis::PreparedSemanticViewInputs {
                prepared,
                #[cfg(test)]
                stack_slots: &self.context.type_facts().stack_slots,
                #[cfg(test)]
                visible_bindings: &self.context.type_facts().visible_bindings,
                #[cfg(test)]
                param_register_aliases: &HashMap::new(),
                function_facts: &self.context.function_facts,
                #[cfg(test)]
                certified_rendering_required: false,
            },
            Rc::clone(&binding_names),
        ) {
            Ok(view) => view,
            Err(error) => {
                let refusal = match error {
                    analysis::prepared_semantic::PreparedSemanticViewBuildError::RenderedIdentity(
                        refusal,
                    ) => {
                        rendered_identity_refusal_category(refusal)
                    }
                    analysis::prepared_semantic::PreparedSemanticViewBuildError::SourceAuthorityMismatch
                    | analysis::prepared_semantic::PreparedSemanticViewBuildError::SymbolTableMismatch => {
                        DecompileRenderRefusal::MissingProgramVariableAuthorization
                    }
                };
                return Ok(InternalBuildProduct::refused(
                    residual_function_for_render_boundary(
                        &func
                            .name
                            .clone()
                            .unwrap_or_else(|| format!("sub_{:x}", func.entry)),
                        &format!("native render refusal: {}", refusal.kind()),
                    ),
                    refusal,
                ));
            }
        };
        let fold_inputs = FoldInputs {
            normalization_origins: Some(&normalization_origins),
            observation_journal: Some(&observation_journal),
            arch: &fold_arch,
            display_names: self.context.function_facts.display_names(),
            #[cfg(test)]
            function_names: &self.context.function_names,
            #[cfg(test)]
            strings: &self.context.strings,
            #[cfg(test)]
            binary_symbols: &self.context.symbols,
            function_facts: &self.context.function_facts,
            #[cfg(test)]
            stack_slots: &self.context.type_facts().stack_slots,
            #[cfg(test)]
            visible_bindings: &self.context.type_facts().visible_bindings,
            type_oracle,
            function_return_type: fold_function_return_type,
            prepared_ssa: Some(prepared),
            binding_names: Some(&binding_names),
            prepared_semantic_view: Some(&prepared_semantic_view),
        };
        let mut fold_ctx = FoldingContext::from_inputs(fold_inputs);
        // One rendered function has one table, and this is the one the passes
        // before now declared into.
        fold_ctx.symbols = std::rc::Rc::clone(&symbol_table);
        let fold_blocks: Vec<_> = func.blocks().cloned().collect();
        let structuring_work = work.with_phase(DecompileWorkPhase::Structuring);
        if let Err(error) = fold_ctx.analyze_blocks_with_control(&fold_blocks, structuring_work) {
            match error {
                analysis::PreparedRuntimeFactsError::ExecutionStop(stop) => return Err(stop),
                analysis::PreparedRuntimeFactsError::Lowering(refusal) => {
                    return Ok(InternalBuildProduct::refused(
                        residual_function_for_render_boundary(
                            &func_name,
                            &format!("operation lowering refusal: {refusal:?}"),
                        ),
                        refusal.into(),
                    ));
                }
            }
        }
        structuring_work.poll()?;
        // Structure control flow (primary path: folded)
        let mut structurer =
            ControlFlowStructurer::new_with_control(func, &fold_ctx, structuring_work)?;

        let routed_body = match consumer_structured::primary_body_for_semantic_route(
            semantic_route,
            &mut structurer,
            || self.linearize_function_body(func, &fold_ctx),
        ) {
            Ok(body) => body,
            Err(structure::ControlFlowStructureError::Lowering(refusal)) => {
                let function = residual_function_for_render_boundary(
                    &func
                        .name
                        .clone()
                        .unwrap_or_else(|| format!("sub_{:x}", func.entry)),
                    &format!("operation lowering refusal: {refusal:?}"),
                );
                return Ok(InternalBuildProduct::refused(function, refusal.into()));
            }
            Err(structure::ControlFlowStructureError::StructuredRegion(error)) => {
                return Ok(InternalBuildProduct::refused(
                    residual_function_for_render_boundary(
                        &func
                            .name
                            .clone()
                            .unwrap_or_else(|| format!("sub_{:x}", func.entry)),
                        &format!("structured-region refusal: {error:?}"),
                    ),
                    DecompileRenderRefusal::UnrepresentableControlFlow,
                ));
            }
        };
        if let Some(stop) = structurer.execution_stop() {
            return Err(stop);
        }
        structuring_work.poll()?;
        if let Some(structured_body) = routed_body.structured_body()
            && let Err(refusal) = validate_sealed_region_occurrence_coverage(structured_body)
        {
            return Ok(InternalBuildProduct::refused(
                residual_function_for_render_boundary(
                    &func_name,
                    "structured-region occurrence coverage mismatch",
                ),
                refusal,
            ));
        }
        let (mut body_stmt, structured_regions) = routed_body.into_marked_body();

        if let Some(comment) = self.semantic_vm_summary_comment() {
            body_stmt = Self::prepend_comment(body_stmt, comment);
        }

        // Build the C function
        // Convert body to statements
        let body = self.stmt_to_vec(body_stmt);
        let mut c_function = CFunction {
            symbols: std::rc::Rc::clone(&symbol_table),
            name: func_name.clone(),
            ret_type: render_signature
                .and_then(|sig| sig.ret_type.as_ref().map(type_like_to_ctype))
                .unwrap_or_else(|| inferred_ret_type.clone()),
            params,
            // Program locals are introduced only by the final placement pass
            // from surviving, observed BindingId occurrences.
            locals: Vec::new(),
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
        if single_evaluation::bind_each_call_site_once(&mut c_function, &binding_names).is_err() {
            let refusal = DecompileRenderRefusal::MissingProgramVariableAuthorization;
            return Ok(InternalBuildProduct::refused(
                residual_function_for_render_boundary(
                    &c_function.name,
                    &format!("native render refusal: {}", refusal.kind()),
                ),
                refusal,
            ));
        }
        simplify_identities_in_function(&mut c_function, &fold_ctx);
        debug_assigned_locals(&c_function, "simplify_identities_in_function");
        reconstruct_flag_conditions_in_function(&mut c_function, &fold_ctx);
        debug_assigned_locals(&c_function, "reconstruct_flag_conditions_in_function");
        normalize_redundant_return_carrier_casts(&mut c_function);
        normalize_declared_assignment_literals(&mut c_function);
        normalize_comparison_operand_order(&mut c_function);
        debug_assigned_locals(&c_function, "normalize_comparison_operand_order");
        unrendered::prune_unreferenced_labels(&mut c_function);
        if void_function_has_value_return(&c_function) {
            let refusal = DecompileRenderRefusal::UnrepresentableOperation;
            return Ok(InternalBuildProduct::refused(
                residual_function_for_render_boundary(
                    &c_function.name,
                    "native render refusal: value-bearing return in void function",
                ),
                refusal,
            ));
        }
        // The refusal gate above proves this is a no-op. Do not discard a
        // value-bearing return here: its expression may carry source effects.
        unrendered::drop_values_from_void_returns(&mut c_function);
        // Executable C is admitted only when the source obligation inventory is
        // complete. The inventory is what says which effects the source has, so a
        // function whose inventory did not close has no account of what the output
        // owes, and rendering it says the effects were all handled when nothing
        // ever enumerated them.
        if let Some(reason) = incomplete_source_obligations_reason(prepared) {
            return Ok(InternalBuildProduct::refused(
                residual_function_for_render_boundary(&c_function.name, &reason),
                DecompileRenderRefusal::IncompleteEffectInventory,
            ));
        }
        let observation_error = fold_ctx.observation_error.borrow().clone();
        drop(fold_ctx);
        let mut native = match MarkedNativeDraft::new_with_placement(
            c_function,
            observation_journal.into_inner(),
            structured_regions,
            Rc::clone(&binding_names),
        )
        .finish_enforcing(input.source_owned_facts(), observation_error)
        {
            Ok(native) => native,
            Err(failure) => {
                let refusal = DecompileRenderRefusal::from(failure);
                return Ok(InternalBuildProduct::refused_after_native_admission(
                    residual_function_for_render_boundary(
                        &func_name,
                        &format!("native render refusal: {}", refusal.kind()),
                    ),
                    failure,
                ));
            }
        };
        let ledger = effect_ledger::build_obligation_ledger(
            prepared,
            &normalization_origins,
            native.effect_observations(),
        );
        debug_log_ledger(prepared, &ledger);
        native.finalize_effect_ledger(&ledger);
        Ok(InternalBuildProduct::Native(native))
    }

    /// Convert a CStmt to a Vec<CStmt>.
    fn stmt_to_vec(&self, stmt: CStmt) -> Vec<CStmt> {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        match semantic {
            CStmt::Block(mut stmts) => {
                observations.reapply_to_unique(&mut stmts);
                stmts
            }
            CStmt::Empty => vec![],
            other => vec![observations.reapply(other)],
        }
    }
}

fn evidence_return_type(source: &r2ssa::SsaArtifact, evidence: &r2types::EvidenceTypes) -> CType {
    let mut candidate: Option<CType> = None;
    let mut saw_return = false;
    for certificate in &source.certificates().returns {
        saw_return = true;
        let Some(ty) = evidence.value_type(certificate.value) else {
            return CType::Unknown;
        };
        let ty = type_like_to_ctype(ty);
        match &candidate {
            None => candidate = Some(ty),
            Some(existing) if existing == &ty => {}
            Some(_) => return CType::Unknown,
        }
    }
    candidate.unwrap_or(if saw_return {
        CType::Unknown
    } else {
        CType::Void
    })
}

fn void_function_has_value_return(func: &CFunction) -> bool {
    if !matches!(func.ret_type, CType::Void) {
        return false;
    }

    fn stmt_has_value_return(stmt: &CStmt) -> bool {
        match stmt {
            CStmt::StructuredRegion { stmt, .. } | CStmt::Observed { stmt, .. } => {
                stmt_has_value_return(stmt)
            }
            CStmt::Return(Some(_)) => true,
            CStmt::Block(stmts) => stmts.iter().any(stmt_has_value_return),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                stmt_has_value_return(then_body)
                    || else_body.as_deref().is_some_and(stmt_has_value_return)
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => stmt_has_value_return(body),
            CStmt::For { init, body, .. } => {
                init.as_deref().is_some_and(stmt_has_value_return) || stmt_has_value_return(body)
            }
            CStmt::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|case| case.body.iter().any(stmt_has_value_return))
                    || default
                        .as_ref()
                        .is_some_and(|stmts| stmts.iter().any(stmt_has_value_return))
            }
            CStmt::Empty
            | CStmt::Expr(_)
            | CStmt::Decl { .. }
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Return(None)
            | CStmt::Comment(_) => false,
        }
    }

    func.body.iter().any(stmt_has_value_return)
}

fn collect_expr_var_names(expr: &CExpr, out: &mut HashSet<crate::symbol::SymbolId>) {
    match expr {
        CExpr::Observed { expr, .. } => collect_expr_var_names(expr, out),
        CExpr::Var(name) => {
            out.insert(*name);
        }
        // Not a name this function declares, so not one it has to.
        CExpr::External { .. } => {}
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
        CExpr::Call { func, args, .. } => {
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

/// Names a statement introduces, wherever it sits in the body.
pub(crate) fn declarations_in_stmts(stmts: &[CStmt]) -> Vec<crate::symbol::SymbolId> {
    fn visit(stmt: &CStmt, out: &mut Vec<crate::symbol::SymbolId>) {
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => visit(stmt, out),
            CStmt::Observed { stmt, .. } => visit(stmt, out),
            CStmt::Decl { name, .. } => out.push(*name),
            CStmt::Block(body) => body.iter().for_each(|s| visit(s, out)),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                visit(then_body, out);
                if let Some(body) = else_body {
                    visit(body, out);
                }
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => visit(body, out),
            CStmt::For { init, body, .. } => {
                if let Some(init) = init {
                    visit(init, out);
                }
                visit(body, out);
            }
            CStmt::Switch { cases, default, .. } => {
                for case in cases {
                    case.body.iter().for_each(|s| visit(s, out));
                }
                if let Some(body) = default {
                    body.iter().for_each(|s| visit(s, out));
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    for stmt in stmts {
        visit(stmt, &mut out);
    }
    out
}

pub(crate) fn collect_stmt_var_names(stmts: &[CStmt]) -> HashSet<crate::symbol::SymbolId> {
    fn visit_stmt(stmt: &CStmt, out: &mut HashSet<crate::symbol::SymbolId>) {
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => visit_stmt(stmt, out),
            CStmt::Observed { stmt, .. } => visit_stmt(stmt, out),
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

/// Which locals the body still assigns, printed between passes.
///
/// A statement the fold built and the page does not show was removed by one of
/// the passes that run after structuring, and there are a dozen of them. Naming
/// the pass is a bisect, and a bisect needs one print per step rather than one
/// build per step.
fn debug_assigned_locals(func: &CFunction, after: &str) {
    if std::env::var_os("R2SLEIGH_DEBUG_PASSES").is_none() {
        return;
    }
    fn walk(stmts: &[CStmt], out: &mut Vec<crate::symbol::SymbolId>) {
        for stmt in stmts {
            if let CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                ..
            }) = stmt
                && let CExpr::Var(id) = left.as_ref()
            {
                out.push(*id);
            }
            match stmt {
                CStmt::Block(inner) => walk(inner, out),
                CStmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    walk(std::slice::from_ref(then_body), out);
                    if let Some(body) = else_body {
                        walk(std::slice::from_ref(body), out);
                    }
                }
                CStmt::While { body, .. }
                | CStmt::DoWhile { body, .. }
                | CStmt::For { body, .. } => walk(std::slice::from_ref(body), out),
                _ => {}
            }
        }
    }
    let mut ids = Vec::new();
    walk(&func.body, &mut ids);
    let table = func.symbols.borrow();
    let mut counts: std::collections::BTreeMap<String, usize> = Default::default();
    for id in ids {
        *counts.entry(table.name(id).to_string()).or_default() += 1;
    }
    let names = counts
        .into_iter()
        .map(|(name, count)| format!("{name}x{count}"))
        .collect::<Vec<_>>();
    fn count_returns(stmts: &[CStmt]) -> usize {
        let mut n = 0;
        for stmt in stmts {
            if matches!(stmt, CStmt::Return(_)) {
                n += 1;
            }
            match stmt {
                CStmt::Block(inner) => n += count_returns(inner),
                CStmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    n += count_returns(std::slice::from_ref(then_body));
                    if let Some(body) = else_body {
                        n += count_returns(std::slice::from_ref(body));
                    }
                }
                CStmt::While { body, .. }
                | CStmt::DoWhile { body, .. }
                | CStmt::For { body, .. } => n += count_returns(std::slice::from_ref(body)),
                _ => {}
            }
        }
        n
    }
    eprintln!(
        "PASS after={after} returns={} assigns={names:?}",
        count_returns(&func.body)
    );
}

fn simplify_identities_in_function(func: &mut CFunction, fold_ctx: &FoldingContext<'_>) {
    fn visit(stmt: &mut CStmt, fold_ctx: &FoldingContext<'_>) {
        single_evaluation::for_each_expr_mut(stmt, &mut |expr| {
            let taken = std::mem::replace(expr, CExpr::IntLit(0));
            *expr = fold_ctx.simplify_identities(taken);
        });
        if let CStmt::For {
            init: Some(init), ..
        } = stmt.unobserved_mut()
        {
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
    let fold_expr = |expr: &mut CExpr| fold_constant_arithmetic_in_expr(expr, strings);
    match stmt {
        CStmt::StructuredRegion { stmt, .. } => fold_constant_arithmetic_in_stmt(stmt, strings),
        CStmt::Observed { stmt, .. } => fold_constant_arithmetic_in_stmt(stmt, strings),
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
        CExpr::Observed { expr, .. } => literal_value(expr),
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
    if let CExpr::Observed { expr, .. } = expr {
        fold_constant_arithmetic_in_expr(expr, strings);
        return;
    }
    let mut replacement = None;
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
                    replacement = Some(CExpr::UIntLit(folded));
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
        CExpr::Call { func, args, .. } => {
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
    if let Some(replacement) = replacement {
        let source = std::mem::replace(expr, CExpr::IntLit(0));
        *expr = crate::ast::carry_outer_expr_observations(&source, replacement);
    }
    // Once the address is one number the string table can answer for it.
    if let Some(value) = literal_value(expr)
        && let Some(text) = strings.get(&value)
    {
        let source = std::mem::replace(expr, CExpr::IntLit(0));
        *expr = crate::ast::carry_outer_expr_observations(&source, CExpr::StringLit(text.clone()));
    }
}

fn normalize_redundant_return_carrier_casts(func: &mut CFunction) {
    fn visit(
        stmt: &mut CStmt,
        ret_type: &CType,
        declared_types: &HashMap<crate::symbol::SymbolId, CType>,
    ) {
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => visit(stmt, ret_type, declared_types),
            CStmt::Observed { stmt, .. } => visit(stmt, ret_type, declared_types),
            CStmt::Return(Some(expr)) => {
                let mut target = expr;
                while let CExpr::Observed { expr: inner, .. } = target {
                    target = inner;
                }
                let CExpr::Cast { expr: inner, .. } = target else {
                    return;
                };
                let CExpr::Var(name) = inner.unobserved() else {
                    return;
                };
                if declared_types.get(name).is_some_and(|ty| ty == ret_type) {
                    *target = *inner.clone();
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
        .map(|param| (param.name, param.ty.clone()))
        .chain(
            func.locals
                .iter()
                .map(|local| (local.name, local.ty.clone())),
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
        CExpr::Observed { expr, .. } => normalize_literal_for_declared_type(expr, ty),
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
        match expr.unobserved() {
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
        if let CExpr::Observed { expr, .. } = expr {
            visit(expr);
            return;
        }
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

fn normalize_declared_assignment_literals(func: &mut CFunction) {
    fn visit_expr(expr: &mut CExpr, declared_types: &HashMap<crate::symbol::SymbolId, CType>) {
        match expr {
            CExpr::Observed { expr, .. } => visit_expr(expr, declared_types),
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
            CExpr::Call { func, args, .. } => {
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
            | CExpr::External { .. }
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
        let CExpr::Var(name) = left.unobserved() else {
            return;
        };
        if let Some(ty) = declared_types.get(name) {
            normalize_literal_for_declared_type(right, ty);
        }
    }

    fn visit_stmt(
        stmt: &mut CStmt,
        declared_types: &HashMap<crate::symbol::SymbolId, CType>,
        ret_type: &CType,
    ) {
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => visit_stmt(stmt, declared_types, ret_type),
            CStmt::Observed { stmt, .. } => visit_stmt(stmt, declared_types, ret_type),
            CStmt::Expr(expr) => visit_expr(expr, declared_types),
            CStmt::Decl { ty, init, .. } => {
                if let Some(init) = init {
                    visit_expr(init, declared_types);
                    normalize_literal_for_declared_type(init, ty);
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    visit_stmt(stmt, declared_types, ret_type);
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                visit_expr(cond, declared_types);
                visit_stmt(then_body, declared_types, ret_type);
                if let Some(else_body) = else_body {
                    visit_stmt(else_body, declared_types, ret_type);
                }
            }
            CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
                visit_expr(cond, declared_types);
                visit_stmt(body, declared_types, ret_type);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    visit_stmt(init, declared_types, ret_type);
                }
                if let Some(cond) = cond {
                    visit_expr(cond, declared_types);
                }
                if let Some(update) = update {
                    visit_expr(update, declared_types);
                }
                visit_stmt(body, declared_types, ret_type);
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
                        visit_stmt(stmt, declared_types, ret_type);
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        visit_stmt(stmt, declared_types, ret_type);
                    }
                }
            }
            CStmt::Return(Some(expr)) => {
                visit_expr(expr, declared_types);
                // A returned literal is read as the return type, so an all-ones
                // word coming back from an `int` function is -1, not 0xffffffff.
                normalize_literal_for_declared_type(expr, ret_type);
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

    let declared_types = func
        .params
        .iter()
        .map(|param| (param.name, param.ty.clone()))
        .chain(
            func.locals
                .iter()
                .map(|local| (local.name, local.ty.clone())),
        )
        .collect::<HashMap<_, _>>();
    for stmt in &mut func.body {
        visit_stmt(stmt, &declared_types, &func.ret_type);
    }
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
    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
        RegisterProjectionDisposition, RegisterStorage, SpaceId, Varnode,
    };
    use r2ssa::SSAFunction;
    use r2types::{
        ExternalRegisterParamSpec, ExternalStruct, ExternalTypeDb, FunctionFacts,
        FunctionParamSpec, FunctionSignatureSpec, FunctionTypeFacts,
    };
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
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
            flag_regs: crate::fold::arch::X86_FLAG_REGISTERS
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
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
            normalization_origins: None,
            observation_journal: None,
            display_names: crate::empty_display_names(),
            arch,
            function_names: Box::leak(Box::new(HashMap::new())),
            strings: Box::leak(Box::new(HashMap::new())),
            binary_symbols: Box::leak(Box::new(HashMap::new())),
            function_facts: crate::fold::context::empty_function_facts(),
            stack_slots: Box::leak(Box::new(BTreeMap::new())),
            visible_bindings: Box::leak(Box::new(Vec::new())),
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            binding_names: None,
            prepared_semantic_view: None,
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
        let registers = [
            (
                "RAX",
                RegisterStorage {
                    offset: 0x00,
                    size: 8,
                },
            ),
            (
                "RDI",
                RegisterStorage {
                    offset: 0x10,
                    size: 8,
                },
            ),
            (
                "RSI",
                RegisterStorage {
                    offset: 0x18,
                    size: 8,
                },
            ),
            (
                "RBP",
                RegisterStorage {
                    offset: 0x20,
                    size: 8,
                },
            ),
            (
                "RSP",
                RegisterStorage {
                    offset: 0x28,
                    size: 8,
                },
            ),
            (
                "RIP",
                RegisterStorage {
                    offset: 0x30,
                    size: 8,
                },
            ),
        ];
        for (name, storage) in registers {
            arch.add_register(RegisterDef::new(name, storage.offset, storage.size));
            arch.register_projections.push(RegisterProjection {
                written: storage,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: storage,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: u64::from(storage.size) * 8,
                    },
                },
            });
        }
        arch
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
    fn redundant_return_carrier_cast_yields_to_declared_c_type() {
        let symbols = test_table();
        let mut func = CFunction::new("carrier", CType::Int(32)).with_body(vec![CStmt::if_stmt(
            CExpr::IntLit(1),
            CStmt::Return(Some(CExpr::cast(
                CType::Int(64),
                CExpr::var(crate::symbol::declare(&symbols, "result")),
            ))),
            None,
        )]);
        func.locals.push(ast::CLocal {
            ty: CType::Int(32),
            name: crate::symbol::declare(&symbols, "result"),
            stack_offset: None,
        });
        func.symbols = std::rc::Rc::new(symbols);

        normalize_redundant_return_carrier_casts(&mut func);

        assert!(matches!(
            &func.body[0],
            CStmt::If { then_body, .. }
                if matches!(then_body.as_ref(), CStmt::Return(Some(CExpr::Var(name))) if &*crate::symbol::spelling(&func.symbols, *name) == "result")
        ));
    }

    #[test]
    fn declared_assignment_type_normalizes_only_root_integer_literals() {
        let symbols = test_table();
        let mut func = CFunction::new("typed_assignments", CType::Int(32)).with_body(vec![
            CStmt::Expr(CExpr::binary(
                BinaryOp::Assign,
                CExpr::var(crate::symbol::declare(&symbols, "signed_value")),
                CExpr::UIntLit(0xffff_ffff),
            )),
            CStmt::Expr(CExpr::binary(
                BinaryOp::Assign,
                CExpr::var(crate::symbol::declare(&symbols, "unsigned_value")),
                CExpr::UIntLit(0xffff_ffff),
            )),
            CStmt::Expr(CExpr::binary(
                BinaryOp::Assign,
                CExpr::var(crate::symbol::declare(&symbols, "signed_value")),
                CExpr::binary(BinaryOp::Add, CExpr::UIntLit(0xffff_ffff), CExpr::IntLit(1)),
            )),
        ]);
        func.locals = vec![
            ast::CLocal {
                ty: CType::Int(32),
                name: crate::symbol::declare(&symbols, "signed_value"),
                stack_offset: Some(-4),
            },
            ast::CLocal {
                ty: CType::UInt(32),
                name: crate::symbol::declare(&symbols, "unsigned_value"),
                stack_offset: Some(-8),
            },
        ];
        func.symbols = std::rc::Rc::new(symbols);

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
    fn folded_constant_keeps_only_the_rewritten_root_observation() {
        let mut observations = crate::ast::RenderObservationOwner::new();
        let (left_id, left) = observations
            .observe_expr(CExpr::UIntLit(0x1000))
            .expect("left operand observation");
        let (right_id, right) = observations
            .observe_expr(CExpr::UIntLit(4))
            .expect("right operand observation");
        let (root_id, mut expr) = observations
            .observe_expr(CExpr::binary(BinaryOp::Add, left, right))
            .expect("root observation");
        let strings = BTreeMap::from([(0x1004, "text".to_string())]);

        fold_constant_arithmetic_in_expr(&mut expr, &strings);
        let mut function = CFunction::new("folded", CType::Pointer(Box::new(CType::Int(8))))
            .with_body(vec![CStmt::Return(Some(expr))]);
        let reachable =
            crate::ast::strip_render_observations(&mut function, observations.expected_count())
                .expect("constant folding preserves a valid marker domain");

        assert!(reachable.contains(root_id));
        assert!(!reachable.contains(left_id));
        assert!(!reachable.contains(right_id));
        assert_eq!(
            function.body,
            vec![CStmt::Return(Some(CExpr::StringLit("text".to_string())))]
        );
    }

    #[test]
    fn prepended_comment_keeps_only_the_exact_original_statement_observation() {
        let mut observations = crate::ast::RenderObservationOwner::new();
        let (stmt_id, stmt) = observations
            .observe_stmt(CStmt::Return(Some(CExpr::IntLit(7))))
            .expect("return observation");
        let commented = Decompiler::prepend_comment(stmt, "summary".to_string());
        assert_eq!(
            commented,
            CStmt::Block(vec![
                CStmt::comment("summary"),
                CStmt::observed(stmt_id, CStmt::Return(Some(CExpr::IntLit(7)))),
            ])
        );

        let mut function = CFunction::new("commented", CType::Int(32)).with_body(vec![commented]);
        let reachable =
            crate::ast::strip_render_observations(&mut function, observations.expected_count())
                .expect("comment insertion preserves a valid marker domain");
        assert!(reachable.contains(stmt_id));
    }

    #[test]
    fn prepended_comment_does_not_move_a_split_block_observation() {
        let mut observations = crate::ast::RenderObservationOwner::new();
        let (child_id, child) = observations
            .observe_stmt(CStmt::Return(Some(CExpr::IntLit(1))))
            .expect("child observation");
        let (block_id, block) = observations
            .observe_stmt(CStmt::Block(vec![
                child,
                CStmt::Return(Some(CExpr::IntLit(2))),
            ]))
            .expect("block observation");
        let commented = Decompiler::prepend_comment(block, "summary".to_string());
        let mut function =
            CFunction::new("commented_block", CType::Int(32)).with_body(vec![commented]);

        let reachable =
            crate::ast::strip_render_observations(&mut function, observations.expected_count())
                .expect("comment insertion preserves a valid marker domain");
        assert!(reachable.contains(child_id));
        assert!(
            !reachable.contains(block_id),
            "a new comment sibling leaves no exact owner for the old block marker"
        );
        assert_eq!(
            function.body,
            vec![CStmt::Block(vec![
                CStmt::comment("summary"),
                CStmt::Return(Some(CExpr::IntLit(1))),
                CStmt::Return(Some(CExpr::IntLit(2))),
            ])]
        );
    }

    #[test]
    fn split_block_observation_is_not_assigned_to_its_first_child() {
        let mut observations = crate::ast::RenderObservationOwner::new();
        let (first_id, first) = observations
            .observe_stmt(CStmt::Return(Some(CExpr::IntLit(1))))
            .expect("first statement observation");
        let (block_id, block) = observations
            .observe_stmt(CStmt::Block(vec![
                first,
                CStmt::Return(Some(CExpr::IntLit(2))),
            ]))
            .expect("block observation");
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let body = decompiler.stmt_to_vec(block);
        let mut function = CFunction::new("split", CType::Int(32)).with_body(body);

        let reachable =
            crate::ast::strip_render_observations(&mut function, observations.expected_count())
                .expect("block decomposition preserves a valid marker domain");
        assert!(reachable.contains(first_id));
        assert!(
            !reachable.contains(block_id),
            "a multi-statement block has no exact first-child projection"
        );
        assert_eq!(
            function.body,
            vec![
                CStmt::Return(Some(CExpr::IntLit(1))),
                CStmt::Return(Some(CExpr::IntLit(2))),
            ]
        );
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
        let arch = test_arch_for_decompile();
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

    /// A malformed source return boundary is refused before the effect ledger
    /// can classify any native C as surviving.
    #[test]
    fn malformed_return_boundary_refuses_before_effect_audit() {
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
        let audited = decompiler.decompile_input_with_binding_audit(&input);
        assert_eq!(
            audited.render_refusal(),
            Some(DecompileRenderRefusal::MissingMachineProjectionAuthorization)
        );
        assert_eq!(audited.effect_obligations(), EffectObligationAudit::NOT_RUN);
        assert!(!audited.output().contains("return"), "{}", audited.output());
    }

    #[test]
    fn native_standard_path_builds_a_sound_non_consuming_binding_shadow() {
        let arch = test_arch_for_decompile();
        let prepared = prepared_from_ops(
            vec![
                R2ILOp::Copy {
                    dst: Varnode::register(0, 8),
                    src: Varnode::constant(0, 8),
                },
                R2ILOp::Return {
                    target: Varnode::register(0x30, 8),
                },
            ],
            &arch,
        );
        let block = prepared.function().get_block(0x1000).expect("entry block");
        let copy_source = block
            .ops
            .iter()
            .find_map(|op| match op {
                SSAOp::Copy { src, .. } => Some(src),
                _ => None,
            })
            .expect("copy source");
        let copy_source_value = prepared
            .graph()
            .value_id_for_var(copy_source)
            .expect("copy source must retain exact ValueId");
        let return_op = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Return { .. }))
            .expect("return op");
        let return_certificate = prepared
            .return_certificate_for_op(0x1000, return_op)
            .expect("scalar audit fixture must retain an exact return certificate");
        assert_eq!(return_certificate.block_addr, 0x1000);
        assert_eq!(return_certificate.op_index, return_op);
        let return_value = return_certificate.value;
        let input = source_owned_decompiler_input(
            prepared,
            (
                r2types::DecompileRouteKind::Standard,
                "binding shadow production path",
                None,
            ),
        );
        let plan = crate::binding_plan::BindingPlan::build_shadow(input.source_owned_facts())
            .expect("scalar audit fixture binding plan");
        assert!(matches!(
            plan.disposition(return_value),
            Some(crate::binding_plan::ValueDisposition::Bound { .. })
        ));
        assert!(matches!(
            plan.disposition(copy_source_value),
            Some(crate::binding_plan::ValueDisposition::Inline { .. })
        ));
        assert_eq!(
            input
                .function_facts()
                .render()
                .and_then(|render| render.return_for_op(0x1000, return_op))
                .map(|fact| fact.value),
            Some(return_value)
        );
        let config = DecompilerConfig::x86_64();
        let public_decompiler = Decompiler::new(config.clone());
        let internal_decompiler =
            Decompiler::new(config.clone()).with_context(input.context_projection());
        let semantic_route = input
            .function_facts()
            .decompile_route()
            .expect("sealed standard route");
        let execution = r2ssa::SsaExecutionControl::default();
        let work = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
        let built = internal_decompiler
            .build_function_internal_with_control(&input, semantic_route, work)
            .expect("native production build");

        let internal_output =
            CodeGenerator::new(config.codegen).generate_function(built.emission());
        let public_output = public_decompiler.decompile_input(&input);
        assert_eq!(internal_output, public_output);
        let audited = public_decompiler.decompile_input_with_binding_audit(&input);
        assert_eq!(audited.output(), public_output);
        let BindingShadowAuditOutcome::Complete {
            ledger,
            observations,
        } = audited.binding_shadow()
        else {
            panic!("public native path did not expose its complete shadow audit");
        };
        assert!(ledger.equations_hold());
        assert!(ledger.passes_quality());
        assert!(observations.equations_hold());
        assert!(observations.passes_quality());
        let mut corrupted_public_ledger = ledger;
        corrupted_public_ledger.values.observed =
            corrupted_public_ledger.values.observed.saturating_sub(1);
        assert!(!corrupted_public_ledger.equations_hold());
        assert!(!corrupted_public_ledger.passes_quality());
    }

    #[test]
    fn shuffled_block_schedule_keeps_spans_bindings_placement_and_bytes_identical() {
        fn exact_diamond_input(
            blocks: &[R2ILBlock],
        ) -> (r2ssa::span::StorageSpans, DecompilerInput) {
            let arch = test_arch_for_decompile();
            let storage = |offset| r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset,
                size: 8,
            };
            let logical_u64 = r2ssa::SourceLogicalValue::new(
                0,
                r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64),
            );
            let type_graph = r2ssa::SourceTypeGraph::new(
                [r2ssa::SourceType::new(
                    0,
                    r2ssa::SourceTypeKind::UnsignedInteger,
                    64,
                    64,
                )],
                [],
            )
            .expect("exact diamond type graph");
            let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
                b"r2dec-shuffled-diamond".to_vec(),
                "sysv64",
                [r2ssa::SourceAbiParameterSpec::new(0, storage(0x10))],
                r2ssa::SourceFunctionReturn::Register {
                    storage: storage(0),
                },
                [],
                [logical_u64],
                Some(logical_u64),
                Some(type_graph),
            )
            .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
            .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
            .expect("exact diamond interface");
            let prepared = Arc::new(
                r2ssa::SsaArtifact::for_decompile_with_interface(blocks, Some(&arch), interface)
                    .expect("prepared shuffled diamond")
                    .with_name("stable_diamond"),
            );
            let spans = prepared.storage_spans().clone();
            let signature = signature_spec(
                Some(CType::UInt(64)),
                vec![("condition", Some(CType::UInt(64)))],
            );
            let parsed_context = r2types::ParsedExternalContext {
                current_signature: Some(signature.clone()),
                merged_signature: Some(signature),
                ..r2types::ParsedExternalContext::default()
            };
            let request = r2types::TypeWritebackAnalysisRequest::new(prepared, parsed_context)
                .expect("source-owned shuffled diamond request");
            let source_owned_facts = r2types::build_source_owned_type_writeback_analysis(request)
                .expect("source-owned shuffled diamond analysis")
                .finalize_for_decompile(r2types::DecompileFinalization {
                    kind: r2types::DecompileRouteKind::Standard,
                    reason: "shuffled determinism proof".to_string(),
                    fallback_comment: None,
                })
                .expect("source-owned shuffled diamond finalization");
            let input = DecompilerInput::new(source_owned_facts);
            (spans, input)
        }

        fn binding_signature(input: &DecompilerInput) -> (Vec<String>, Vec<String>) {
            let plan = crate::binding_plan::BindingPlan::build_shadow(input.source_owned_facts())
                .expect("sealed deterministic plan");
            let bindings = plan
                .bindings()
                .map(|(id, binding)| {
                    format!(
                        "{}:{:?}:{:?}:{:?}",
                        id.index(),
                        binding.declaration_type(),
                        binding.presentation_name_hint(),
                        plan.binding_role(id)
                    )
                })
                .collect();
            let dispositions = (0..input.prepared_ssa().graph().values.len())
                .map(|index| {
                    let value = r2ssa::ValueId(index as u32);
                    match plan
                        .disposition(value)
                        .expect("one disposition per dense value")
                    {
                        crate::binding_plan::ValueDisposition::Bound { binding } => {
                            format!("bound:{}", binding.index())
                        }
                        crate::binding_plan::ValueDisposition::Inline { expr, .. } => {
                            format!("inline:{}", expr.index())
                        }
                        crate::binding_plan::ValueDisposition::Elided { reason, .. } => {
                            format!("elided:{reason:?}")
                        }
                        crate::binding_plan::ValueDisposition::Refused { reason } => {
                            format!("refused:{reason:?}")
                        }
                    }
                })
                .collect();
            (bindings, dispositions)
        }

        let mut entry = R2ILBlock::new(0x1000, 0x10);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::register(0x10, 8),
        });
        let mut false_arm = R2ILBlock::new(0x1010, 0x10);
        false_arm.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(1, 8),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });
        let mut true_arm = R2ILBlock::new(0x1020, 0x10);
        true_arm.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(2, 8),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });
        let mut merge = R2ILBlock::new(0x1030, 4);
        merge.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });

        let peers = [false_arm, true_arm, merge];
        let baseline_blocks = vec![
            entry.clone(),
            peers[0].clone(),
            peers[1].clone(),
            peers[2].clone(),
        ];
        let (baseline_spans, baseline_input) = exact_diamond_input(&baseline_blocks);
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let baseline = decompiler.decompile_input_with_binding_audit(&baseline_input);
        let baseline_binding_signature = binding_signature(&baseline_input);
        let baseline_values = baseline_input
            .prepared_ssa()
            .graph()
            .values
            .iter()
            .map(|value| {
                format!(
                    "{:?}:{}:{:?}",
                    value.id,
                    value.var.display_name(),
                    value.canonical_storage
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            baseline.placement_audit(),
            PlacementAudit::Applied,
            "baseline must reach placement: output={} refusal={:?} binding={:?} effects={:?} signature={baseline_binding_signature:?} values={baseline_values:?} type_facts={:?}",
            baseline.output(),
            baseline.render_refusal(),
            baseline.binding_shadow(),
            baseline.effect_obligations(),
            baseline_input.function_facts().type_facts(),
        );

        // Exhaust the complete schedule domain of the non-entry blocks. Entry
        // identity is semantic input; node/edge insertion order is not.
        for schedule in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut shuffled_blocks = vec![entry.clone()];
            shuffled_blocks.extend(schedule.map(|index| peers[index].clone()));
            let (shuffled_spans, shuffled_input) = exact_diamond_input(&shuffled_blocks);
            let shuffled = decompiler.decompile_input_with_binding_audit(&shuffled_input);

            assert_eq!(baseline_spans, shuffled_spans, "schedule={schedule:?}");
            assert_eq!(
                baseline_binding_signature,
                binding_signature(&shuffled_input),
                "schedule={schedule:?}"
            );
            assert_eq!(
                baseline.placement_audit(),
                shuffled.placement_audit(),
                "schedule={schedule:?}"
            );
            assert_eq!(
                baseline.binding_shadow(),
                shuffled.binding_shadow(),
                "schedule={schedule:?}"
            );
            assert_eq!(
                baseline.effect_obligations(),
                shuffled.effect_obligations(),
                "schedule={schedule:?}"
            );
            assert_eq!(
                baseline.render_refusal(),
                shuffled.render_refusal(),
                "schedule={schedule:?}"
            );
            assert_eq!(
                baseline.output().as_bytes(),
                shuffled.output().as_bytes(),
                "schedule={schedule:?}"
            );
        }
    }

    #[test]
    fn binding_shadow_adds_no_post_render_work_control_decision() {
        struct CountingControl {
            polls: std::cell::Cell<usize>,
            stop_at: Option<usize>,
        }

        impl r2ssa::SsaWorkControl for CountingControl {
            fn poll(&self) -> Result<(), r2ssa::SsaExecutionStopReason> {
                let poll = self.polls.get() + 1;
                self.polls.set(poll);
                if self.stop_at == Some(poll) {
                    Err(r2ssa::SsaExecutionStopReason::Cancelled)
                } else {
                    Ok(())
                }
            }
        }

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
                "binding shadow work-control path",
                None,
            ),
        );
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());
        let baseline = CountingControl {
            polls: std::cell::Cell::new(0),
            stop_at: None,
        };
        decompiler
            .decompile_input_with_binding_audit_and_control(&input, &baseline)
            .expect("unbounded audit");
        let final_production_poll = baseline.polls.get();

        let stop_at_final = CountingControl {
            polls: std::cell::Cell::new(0),
            stop_at: Some(final_production_poll),
        };
        let stop = decompiler
            .decompile_input_with_binding_audit_and_control(&input, &stop_at_final)
            .expect_err("the final production poll must remain observable");
        assert_eq!(stop.phase(), DecompileWorkPhase::Rendering);
        assert_eq!(stop.reason(), r2ssa::SsaExecutionStopReason::Cancelled);

        let no_later_poll = CountingControl {
            polls: std::cell::Cell::new(0),
            stop_at: Some(final_production_poll + 1),
        };
        decompiler
            .decompile_input_with_binding_audit_and_control(&input, &no_later_poll)
            .expect("shadow capture and classification must not poll work control");
        assert_eq!(no_later_poll.polls.get(), final_production_poll);
    }

    #[test]
    fn audited_partial_retains_the_same_product_without_extra_polls() {
        struct CountingControl {
            polls: std::cell::Cell<usize>,
            stop_at: Option<usize>,
        }

        impl r2ssa::SsaWorkControl for CountingControl {
            fn poll(&self) -> Result<(), r2ssa::SsaExecutionStopReason> {
                let poll = self.polls.get() + 1;
                self.polls.set(poll);
                if self.stop_at == Some(poll) {
                    Err(r2ssa::SsaExecutionStopReason::Cancelled)
                } else {
                    Ok(())
                }
            }
        }

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
                "same-run audited partial",
                None,
            ),
        );
        let decompiler = Decompiler::new(DecompilerConfig::x86_64());

        let baseline_control = CountingControl {
            polls: std::cell::Cell::new(0),
            stop_at: None,
        };
        let baseline = decompiler
            .decompile_input_keeping_partial_with_binding_audit(&input, &baseline_control)
            .expect("unbounded audited rendering");
        let final_poll = baseline_control.polls.get();
        let first_render_poll = final_poll
            .checked_sub(1)
            .expect("successful product rendering has two rendering polls");

        for stop_at in [first_render_poll, final_poll] {
            let stopped_control = CountingControl {
                polls: std::cell::Cell::new(0),
                stop_at: Some(stop_at),
            };
            let (stop, partial) = decompiler
                .decompile_input_keeping_partial_with_binding_audit(&input, &stopped_control)
                .expect_err("selected rendering poll must stop");
            assert_eq!(stop.phase(), DecompileWorkPhase::Rendering);
            assert_eq!(stop.reason(), r2ssa::SsaExecutionStopReason::Cancelled);
            assert_eq!(
                stopped_control.polls.get(),
                stop_at,
                "retaining output and audit must neither rebuild nor poll again"
            );
            assert_eq!(
                partial.as_ref(),
                Some(&baseline),
                "the partial must classify the exact retained product"
            );
        }

        let pre_product_control = CountingControl {
            polls: std::cell::Cell::new(0),
            stop_at: Some(1),
        };
        let (stop, partial) = decompiler
            .decompile_input_keeping_partial_with_binding_audit(&input, &pre_product_control)
            .expect_err("initial preparation poll must stop");
        assert_eq!(stop.phase(), DecompileWorkPhase::Normalization);
        assert_eq!(partial, None);
        assert_eq!(pre_product_control.polls.get(), 1);

        let compatibility_control = CountingControl {
            polls: std::cell::Cell::new(0),
            stop_at: None,
        };
        let compatibility_output = decompiler
            .decompile_input_keeping_partial(&input, &compatibility_control)
            .expect("compatibility rendering");
        assert_eq!(compatibility_output, baseline.output());
        assert_eq!(
            compatibility_control.polls.get(),
            final_poll,
            "the string compatibility mapper must add no work-control decision"
        );
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
        let symbols = test_table();
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
                CExpr::var(crate::symbol::declare(&symbols, "sym.rpl_mbrtoc32")),
                Vec::new(),
            ))],
            symbols: std::rc::Rc::new(symbols),
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
        let symbols = test_table();
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
                CExpr::var(crate::symbol::declare(&symbols, "summary_worker")),
                Vec::new(),
            ))],
            symbols: std::rc::Rc::new(symbols),
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
        let symbols = test_table();
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
        let body = vec![CStmt::Expr(CExpr::call(
            crate::symbol::var_ref(&symbols, "sym.imp.malloc"),
            vec![crate::symbol::var_ref(&symbols, "n")],
        ))];
        let mut func = CFunction {
            name: "dbg.alloc_wrapper2".to_string(),
            ret_type: CType::ptr(CType::Int(8)),
            params: Vec::new(),
            params_known: true,
            locals: Vec::new(),
            body,
            symbols: std::rc::Rc::new(symbols),
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

    #[test]
    fn sealed_region_occurrence_mismatch_is_a_render_refusal() {
        assert_eq!(validate_sealed_region_occurrence_counts(3, 3), Ok(()));
        assert_eq!(
            validate_sealed_region_occurrence_counts(2, 3),
            Err(DecompileRenderRefusal::UnrepresentableControlFlow),
            "release builds must not admit a partially represented region domain"
        );
    }
}
