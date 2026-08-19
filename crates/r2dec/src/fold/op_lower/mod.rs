//! Expression folding for decompilation.
//!
//! This module performs expression folding to combine SSA operations into
//! compound C expressions, eliminating unnecessary temporaries and improving
//! readability.
//!
//! ## Key Transformations
//!
//! 1. **Single-use inlining**: If a variable is only used once, inline its
//!    definition at the use site.
//!    ```text
//!    t1 = a + b;
//!    t2 = t1 * c;
//!    // becomes:
//!    t2 = (a + b) * c;
//!    ```
//!
//! 2. **Dead code elimination**: Remove definitions of variables that are
//!    never used (especially CPU flags).
//!
//! 3. **Constant folding**: Replace `const:xxx` with actual numeric values.

use std::collections::{BTreeSet, HashMap, HashSet};

use r2ssa::{
    DecompilePrepFacts, MemoryDefFact, MemoryLocation, ObjectKind, ObjectModel,
    PreparedFunctionFacts, SSAFunction, SSAOp, SSAVar, SSAVarNameKind, SsaArtifact, ValueId,
};
#[cfg(test)]
use r2types::StackSlotKey;
#[cfg(test)]
use r2types::TypeOracle;
#[cfg(test)]
use r2types::normalize_callee_name;
use r2types::{
    CTypeLike, CalleeIdentity, ExternalField, ExternalStackBase, ExternalStackSlotRole,
    ExternalStruct, ExternalUnion, FunctionRenderFacts, ReturnValueRenderFact,
    normalize_external_type_name, parse_type_like_spec,
};

use crate::address::parse_address_from_var_name;
use crate::analysis;
use crate::ast::{BinaryOp, CExpr, CStmt, CType, UnaryOp};
use crate::registers::register_family_name;

use super::SSABlock;
use super::context::{
    EffectRenderProofKind, FoldingContext, PhiEdgeRenderKind, PhiEdgeRenderProof,
};
use super::context::{ResolutionGuardKey, ResolutionPhase};
use super::flags::is_cpu_flag;
use super::{
    MAX_ALIAS_REWRITE_DEPTH, MAX_PREDICATE_OPERAND_DEPTH, MAX_RETURN_EXPR_DEPTH,
    MAX_RETURN_INLINE_CANDIDATE_DEPTH, MAX_RETURN_INLINE_DEPTH, MAX_SIMPLE_EXPR_DEPTH,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CallExprSourceProof {
    Exact((u64, usize)),
    ContradictedOrAmbiguous,
    None,
}

fn certified_compare_truth_relation(
    target: (r2ssa::CompareKind, r2ssa::SemanticId, r2ssa::SemanticId),
    predicate: (r2ssa::CompareKind, r2ssa::SemanticId, r2ssa::SemanticId),
) -> Option<bool> {
    let equality_family = |kind| {
        matches!(
            kind,
            r2ssa::CompareKind::Equal | r2ssa::CompareKind::NotEqual
        )
    };
    let operands_match = target.1 == predicate.1 && target.2 == predicate.2
        || equality_family(target.0)
            && equality_family(predicate.0)
            && target.1 == predicate.2
            && target.2 == predicate.1;
    if !operands_match {
        return None;
    }
    if target.0 == predicate.0 {
        Some(true)
    } else if equality_family(target.0) && equality_family(predicate.0) {
        Some(false)
    } else {
        None
    }
}

#[cfg(test)]
#[test]
fn certified_compare_truth_relation_handles_complement_and_swapped_equality() {
    let lhs = r2ssa::SemanticId::expression(ValueId(1));
    let rhs = r2ssa::SemanticId::expression(ValueId(2));
    assert_eq!(
        certified_compare_truth_relation(
            (r2ssa::CompareKind::Equal, lhs, rhs),
            (r2ssa::CompareKind::NotEqual, rhs, lhs),
        ),
        Some(false)
    );
    assert_eq!(
        certified_compare_truth_relation(
            (r2ssa::CompareKind::Less, lhs, rhs),
            (r2ssa::CompareKind::LessEqual, lhs, rhs),
        ),
        None
    );
}

fn is_visible_external_stack_name_role(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::Local
            | ExternalStackSlotRole::StackArg
            | ExternalStackSlotRole::Unknown
    )
}

fn external_struct_field_name_for_offset(
    st: &ExternalStruct,
    offset: u64,
    access_size: Option<u32>,
    ptr_bits: u32,
) -> Option<String> {
    st.fields
        .range(..=offset)
        .next_back()
        .and_then(|(_, field)| external_field_name_for_offset(field, offset, access_size, ptr_bits))
}

fn external_union_field_name_for_offset(
    un: &ExternalUnion,
    offset: u64,
    access_size: Option<u32>,
    ptr_bits: u32,
) -> Option<String> {
    if offset != 0 {
        return None;
    }
    un.fields
        .values()
        .find_map(|field| external_field_name_for_offset(field, offset, access_size, ptr_bits))
}

fn external_field_name_for_offset(
    field: &ExternalField,
    offset: u64,
    access_size: Option<u32>,
    ptr_bits: u32,
) -> Option<String> {
    if offset < field.offset {
        return None;
    }
    let rel = offset - field.offset;
    if let Some(CTypeLike::Array(inner, len)) = field
        .ty
        .as_deref()
        .and_then(|ty| parse_type_like_spec(ty, ptr_bits))
    {
        let elem_size = c_type_like_size_bytes(&inner, ptr_bits)?;
        if elem_size == 0 || !rel.is_multiple_of(elem_size) {
            return None;
        }
        if let Some(access_size) = access_size
            && u64::from(access_size) > elem_size
        {
            return (rel == 0).then(|| field.name.clone());
        }
        let index = rel / elem_size;
        if len.is_some_and(|count| index >= count as u64) {
            return None;
        }
        return Some(format!("{}[{index}]", field.name));
    }
    (rel == 0).then(|| field.name.clone())
}

fn exact_external_field_name_for_offset(
    field: &ExternalField,
    offset: u64,
    access_size: u32,
    ptr_bits: u32,
) -> Option<String> {
    if offset != field.offset {
        return None;
    }
    let field_size = field
        .ty
        .as_deref()
        .and_then(|ty| parse_type_like_spec(ty, ptr_bits))
        .and_then(|ty| c_type_like_size_bytes(&ty, ptr_bits))?;
    (field_size == u64::from(access_size)).then(|| field.name.clone())
}

fn external_field_type_is_pointer(field: &ExternalField, ptr_bits: u32) -> bool {
    field
        .ty
        .as_deref()
        .and_then(|ty| parse_type_like_spec(ty, ptr_bits))
        .is_some_and(|ty| matches!(ty, CTypeLike::Pointer(_)))
}

fn exact_external_struct_field_name_for_offset(
    st: &ExternalStruct,
    offset: u64,
    access_size: u32,
    ptr_bits: u32,
) -> Option<String> {
    st.fields.get(&offset).and_then(|field| {
        exact_external_field_name_for_offset(field, offset, access_size, ptr_bits)
    })
}

fn exact_external_union_field_name_for_offset(
    un: &ExternalUnion,
    offset: u64,
    access_size: u32,
    ptr_bits: u32,
) -> Option<String> {
    if offset != 0 {
        return None;
    }
    let mut matches = un
        .fields
        .values()
        .filter_map(|field| {
            exact_external_field_name_for_offset(field, offset, access_size, ptr_bits)
        })
        .collect::<Vec<_>>();
    matches.sort();
    matches.dedup();
    (matches.len() == 1).then(|| matches.remove(0))
}

fn c_type_like_size_bytes(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Void | CTypeLike::Unknown | CTypeLike::Function => None,
        CTypeLike::Bool => Some(1),
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        CTypeLike::Pointer(_) => Some((ptr_bits / 8).max(1) as u64),
        CTypeLike::Array(inner, Some(count)) => {
            c_type_like_size_bytes(inner, ptr_bits).map(|size| size.saturating_mul(*count as u64))
        }
        CTypeLike::Array(inner, None) => c_type_like_size_bytes(inner, ptr_bits),
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) | CTypeLike::Typedef(_) => {
            None
        }
    }
}

fn c_type_size_bytes(ty: &CType, ptr_size: u32) -> Option<u64> {
    match ty {
        CType::Void | CType::Unknown | CType::Function { .. } => None,
        CType::Bool => Some(1),
        CType::Int(bits) | CType::UInt(bits) | CType::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        CType::Pointer(_) => Some(u64::from(ptr_size.max(1))),
        CType::Array(inner, Some(count)) => {
            c_type_size_bytes(inner, ptr_size).map(|size| size.saturating_mul(*count as u64))
        }
        CType::Array(inner, None) => c_type_size_bytes(inner, ptr_size),
        CType::Typedef(name) => match name.as_str() {
            "size_t" | "ssize_t" | "uintptr_t" | "intptr_t" | "ptrdiff_t" => {
                Some(u64::from(ptr_size.max(1)))
            }
            "uint8_t" | "int8_t" | "char" | "unsigned char" | "signed char" => Some(1),
            "uint16_t" | "int16_t" => Some(2),
            "uint32_t" | "int32_t" => Some(4),
            "uint64_t" | "int64_t" => Some(8),
            _ => None,
        },
        CType::Struct(_) | CType::Union(_) | CType::Enum(_) => None,
    }
}

mod aliases;
mod calls;
mod lowering;
mod memory_renderer;
mod return_resolver;

#[derive(Debug, Clone, PartialEq)]
enum LoweredOp {
    Assign { lhs: CExpr, rhs: CExpr },
    Expr(CExpr),
    Return(Option<CExpr>),
    None,
    Comment(String),
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CertifiedCallExpr {
    pub(super) expr: CExpr,
    pub(super) target: ValueId,
    pub(super) values: Vec<ValueId>,
}

fn expr_contains_memory_like_access(expr: &CExpr) -> bool {
    let mut found = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Deref(_) | CExpr::Subscript { .. }) {
            found = true;
        }
    });
    found
}

fn expr_contains_call(expr: &CExpr) -> bool {
    let mut found = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Call { .. }) {
            found = true;
        }
    });
    found
}

fn assignment_rhs_requires_expression_render_proof(expr: &CExpr) -> bool {
    let CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    } = expr
    else {
        return false;
    };
    matches!(left.as_ref(), CExpr::Var(_))
        && !expr_contains_memory_like_access(right)
        && !expr_contains_call(right)
}

fn stmt_requires_expression_render_proof(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Expr(expr) => assignment_rhs_requires_expression_render_proof(expr),
        _ => false,
    }
}

fn expr_is_side_effect_free_for_carrier_gate(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::SizeofType(_) => true,
        CExpr::Paren(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Sizeof(inner) => expr_is_side_effect_free_for_carrier_gate(inner),
        CExpr::Unary { op, operand } => {
            !matches!(
                op,
                UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
            ) && expr_is_side_effect_free_for_carrier_gate(operand)
        }
        CExpr::Binary { op, left, right } => {
            !matches!(
                op,
                BinaryOp::Assign
                    | BinaryOp::AddAssign
                    | BinaryOp::SubAssign
                    | BinaryOp::MulAssign
                    | BinaryOp::DivAssign
                    | BinaryOp::ModAssign
                    | BinaryOp::BitAndAssign
                    | BinaryOp::BitOrAssign
                    | BinaryOp::BitXorAssign
                    | BinaryOp::ShlAssign
                    | BinaryOp::ShrAssign
            ) && expr_is_side_effect_free_for_carrier_gate(left)
                && expr_is_side_effect_free_for_carrier_gate(right)
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_is_side_effect_free_for_carrier_gate(cond)
                && expr_is_side_effect_free_for_carrier_gate(then_expr)
                && expr_is_side_effect_free_for_carrier_gate(else_expr)
        }
        CExpr::Subscript { base, index } => {
            expr_is_side_effect_free_for_carrier_gate(base)
                && expr_is_side_effect_free_for_carrier_gate(index)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            expr_is_side_effect_free_for_carrier_gate(base)
        }
        CExpr::Comma(values) => values.iter().all(expr_is_side_effect_free_for_carrier_gate),
        CExpr::Call { .. } => false,
    }
}

fn is_generated_carrier_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("value_")
        || lower.contains(':')
        || (lower.starts_with('t') && lower[1..].chars().all(|ch| ch.is_ascii_digit()))
}

fn is_static_jump_table_base_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if matches!(
        SSAVarNameKind::classify(&lower),
        SSAVarNameKind::Symbol | SSAVarNameKind::Object
    ) {
        return true;
    }
    lower
        .strip_prefix("0x")
        .is_some_and(|hex| !hex.is_empty() && u64::from_str_radix(hex, 16).is_ok())
}

fn side_effect_free_assignment_name(stmt: &CStmt) -> Option<&str> {
    let (name, rhs) = match stmt {
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) => {
            let CExpr::Var(name) = left.as_ref() else {
                return None;
            };
            (name.as_str(), right.as_ref())
        }
        CStmt::Decl {
            name,
            init: Some(init),
            ..
        } => (name.as_str(), init),
        _ => return None,
    };
    expr_is_side_effect_free_for_carrier_gate(rhs).then_some(name)
}

fn stmt_is_side_effect_free_generated_carrier(stmt: &CStmt) -> bool {
    side_effect_free_assignment_name(stmt).is_some_and(is_generated_carrier_name)
}

fn stmt_contains_memory_like_access(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => expr_contains_memory_like_access(expr),
        CStmt::Decl { init, .. } => init.as_ref().is_some_and(expr_contains_memory_like_access),
        CStmt::Block(stmts) => stmts.iter().any(stmt_contains_memory_like_access),
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            expr_contains_memory_like_access(cond)
                || stmt_contains_memory_like_access(then_body)
                || else_body
                    .as_ref()
                    .is_some_and(|stmt| stmt_contains_memory_like_access(stmt))
        }
        CStmt::While { cond, body } => {
            expr_contains_memory_like_access(cond) || stmt_contains_memory_like_access(body)
        }
        CStmt::DoWhile { body, cond } => {
            stmt_contains_memory_like_access(body) || expr_contains_memory_like_access(cond)
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            init.as_ref()
                .is_some_and(|stmt| stmt_contains_memory_like_access(stmt))
                || cond.as_ref().is_some_and(expr_contains_memory_like_access)
                || update
                    .as_ref()
                    .is_some_and(expr_contains_memory_like_access)
                || stmt_contains_memory_like_access(body)
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            expr_contains_memory_like_access(expr)
                || cases.iter().any(|case| {
                    expr_contains_memory_like_access(&case.value)
                        || case.body.iter().any(stmt_contains_memory_like_access)
                })
                || default
                    .as_ref()
                    .is_some_and(|stmts| stmts.iter().any(stmt_contains_memory_like_access))
        }
        CStmt::Return(None)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => false,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LowerMode {
    Expr,
    Stmt,
}

#[derive(Debug, Clone, Copy)]
struct LowerFrame {
    mode: LowerMode,
    block_addr: u64,
    op_idx: usize,
    with_call_args: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisibleExprContext {
    Generic,
    ScalarPredicate,
    ScalarReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FinalExprNormalizeContext {
    Generic,
    DefinitionRoot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FinalExprNormalizeScope {
    context: FinalExprNormalizeContext,
    source_call: Option<(u64, usize)>,
}

impl FinalExprNormalizeScope {
    fn new(context: FinalExprNormalizeContext) -> Self {
        Self {
            context,
            source_call: None,
        }
    }

    fn for_source_call(context: FinalExprNormalizeContext, source_call: (u64, usize)) -> Self {
        Self {
            context,
            source_call: Some(source_call),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PublicExprSanitizeMode {
    Generic,
    CallArg,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
struct VisibleExprQuality {
    scalar_signal: i32,
    predicate_signal: i32,
    semantic_shapes: i32,
    semantic_names: i32,
    stable_pointer_shapes: i32,
    generic_stack_penalty: i32,
    transient_reg_penalty: i32,
    temp_penalty: i32,
    zero_offset_penalty: i32,
    address_shape_penalty: i32,
    stack_home_penalty: i32,
    node_penalty: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum RenderCandidateSource {
    ExactNameDefinition,
    ValueDefinition,
    SemanticValue,
    ForwardedValue,
    AliasDefinition,
    RawDefinition,
}

#[derive(Debug, Clone, PartialEq)]
struct RenderCandidate {
    expr: CExpr,
    source: RenderCandidateSource,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CertifiedRenderPlan<'a> {
    function_facts: &'a r2types::FunctionFacts,
    prepared_view: &'a analysis::PreparedSemanticView,
    proof: CertifiedRenderContext<'a>,
}

impl<'a> CertifiedRenderPlan<'a> {
    fn new(
        function_facts: &'a r2types::FunctionFacts,
        prepared_view: &'a analysis::PreparedSemanticView,
        proof: CertifiedRenderContext<'a>,
    ) -> Self {
        Self {
            function_facts,
            prepared_view,
            proof,
        }
    }

    fn call_arg_expr<F>(
        &self,
        site: (u64, usize),
        value: r2ssa::ValueId,
        contains_raw_storage_name: F,
    ) -> Option<CExpr>
    where
        F: FnOnce(&CExpr) -> bool,
    {
        if !self.proof.expression_is_renderable(value) {
            return None;
        }
        let call_view = self.prepared_view.call_view_for_site(site)?;
        let render_fact = call_view.render_fact.as_ref()?;
        if render_fact.callsite.block_addr != site.0
            || render_fact.callsite.op_index != site.1
            || matches!(
                render_fact.disposition,
                r2types::CallsiteRenderDisposition::Suppressed
                    | r2types::CallsiteRenderDisposition::Residualized
            )
        {
            return None;
        }
        let index = call_view
            .authoritative_arg_values
            .iter()
            .position(|candidate| *candidate == value)?;
        if render_fact.proof_values.get(index).copied() != Some(value) {
            return None;
        }
        let expr = self
            .prepared_view
            .authoritative_call_arg_expr_for_value(site, value)?;
        if contains_raw_storage_name(&expr) {
            return None;
        }
        Some(expr)
    }

    fn stack_param_expr_for_memory_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
    ) -> Option<CExpr> {
        if fact.is_write || fact.width == 0 {
            return None;
        }
        let offset = self.proof.render_facts.stack_slot_offset(fact.object)?;
        let authorization = self
            .function_facts
            .authorized_stack_param_owner_render(fact.object, offset)?;
        Some(CExpr::Var(authorization.name))
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CertifiedRenderContext<'a> {
    prepared: &'a SsaArtifact,
    render_facts: &'a FunctionRenderFacts,
}

impl<'a> CertifiedRenderContext<'a> {
    fn new(prepared: &'a SsaArtifact, render_facts: &'a FunctionRenderFacts) -> Self {
        Self {
            prepared,
            render_facts,
        }
    }

    fn expression_is_renderable(&self, value: r2ssa::ValueId) -> bool {
        self.render_facts.expression_is_renderable(value)
    }

    fn memory_access_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
        is_write: bool,
    ) -> Option<&'a r2types::MemoryAccessRenderFact> {
        let block = self.prepared.function().get_block(block_addr)?;
        let space = block.ops.get(op_idx)?.memory_space()?;
        self.render_facts
            .memory_access_for_op(block_addr, op_idx, is_write, space)
    }

    fn exact_memory_read_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&'a r2types::MemoryAccessRenderFact> {
        let inst = self.prepared.graph().def_inst(value)?;
        if !matches!(
            self.prepared.graph().inst(inst)?.payload,
            r2ssa::InstPayload::Op(SSAOp::Load { .. })
        ) {
            return None;
        }
        let (block_addr, op_idx) = self.prepared.inst_op_site(inst)?;
        let fact = self.memory_access_for_op(block_addr, op_idx, false)?;
        (fact.value == Some(value) && !fact.is_write && fact.materialize_result).then_some(fact)
    }

    fn memory_read_for_value_dependency(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&'a r2types::MemoryAccessRenderFact> {
        let mut visited = BTreeSet::new();
        let mut stack = vec![(value, 0usize)];
        while let Some((current, depth)) = stack.pop() {
            if depth > 8 || !visited.insert(current) {
                continue;
            }
            if let Some(cert) = self
                .prepared
                .certificates()
                .memory_accesses
                .values()
                .find(|cert| !cert.is_write && cert.width > 0 && cert.value == Some(current))
            {
                let fact = self.render_facts.memory_access_for_op(
                    cert.block_addr,
                    cert.op_index,
                    false,
                    cert.space,
                )?;
                if fact.access == cert.access
                    && fact.space == cert.space
                    && fact.address == cert.address
                    && fact.value == cert.value
                    && fact.width == cert.width
                {
                    return Some(fact);
                }
                return None;
            }
            let Some(inst_id) = self.prepared.graph().def_inst(current) else {
                continue;
            };
            let Some(inst) = self.prepared.graph().inst(inst_id) else {
                continue;
            };
            stack.extend(inst.inputs.iter().map(|input| (*input, depth + 1)));
        }
        None
    }

    fn return_for_op(&self, block_addr: u64, op_idx: usize) -> Option<&'a ReturnValueRenderFact> {
        self.render_facts.return_for_op(block_addr, op_idx)
    }
}

impl LowerFrame {
    fn for_expr() -> Self {
        Self {
            mode: LowerMode::Expr,
            block_addr: 0,
            op_idx: 0,
            with_call_args: false,
        }
    }

    fn for_stmt(block_addr: u64, op_idx: usize, with_call_args: bool) -> Self {
        Self {
            mode: LowerMode::Stmt,
            block_addr,
            op_idx,
            with_call_args,
        }
    }
}

impl<'a> FoldingContext<'a> {
    fn certified_parameter_expr_for_value(&self, value: r2ssa::ValueId) -> Option<CExpr> {
        let slot = self
            .certified_render_context()?
            .render_facts
            .exact_parameter_slot_for_value(value)?;
        let signature = self
            .inputs
            .function_facts
            .type_facts()
            .render_authorized_signature()?;
        let parameter = signature.params.get(slot)?;
        (!parameter.name.trim().is_empty()).then(|| CExpr::Var(parameter.name.clone()))
    }

    fn stable_semantic_ids_are_required(&self) -> bool {
        self.certified_render_context()
            .is_some_and(|proof| !proof.render_facts.certified_exprs.is_empty())
    }

    fn certified_const_expr(&self, var: &SSAVar) -> Option<CExpr> {
        let value = parse_const_value(&var.name)?;
        Some(if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        })
    }

    const MAX_SEMANTIC_RENDER_DEPTH: u32 = 16;

    fn use_info(&self) -> &analysis::UseInfo {
        self.state.analysis_ctx.semantic()
    }

    fn flag_info(&self) -> &analysis::FlagInfo {
        self.state.analysis_ctx.flags()
    }

    fn stack_info(&self) -> &analysis::StackInfo {
        self.state.analysis_ctx.stack()
    }

    fn ownership(&self) -> &analysis::SemanticOwnershipFacts {
        self.state.analysis_ctx.ownership()
    }

    fn prepared_ssa(&self) -> Option<&SsaArtifact> {
        self.inputs.prepared_ssa
    }

    pub(crate) fn certified_render_context(&self) -> Option<CertifiedRenderContext<'_>> {
        Some(CertifiedRenderContext::new(
            self.prepared_ssa()?,
            self.inputs.render_facts()?,
        ))
    }

    pub(crate) fn certified_render_plan<'b>(
        &'b self,
        proof: CertifiedRenderContext<'b>,
    ) -> Option<CertifiedRenderPlan<'b>> {
        Some(CertifiedRenderPlan::new(
            self.inputs.function_facts,
            self.prepared_semantic_view()?,
            proof,
        ))
    }

    pub(crate) fn requires_certified_rendering(&self) -> bool {
        false
    }

    pub(crate) fn stable_stack_value_for_offset(
        &self,
        offset: i64,
    ) -> Option<&analysis::SemanticValue> {
        self.use_info().stable_stack_values.get(&offset)
    }

    pub(super) fn certified_phi_edge_render_proof(
        &self,
        op: &SSAOp,
        stmt: &CStmt,
        predecessor: u64,
    ) -> Option<PhiEdgeRenderProof> {
        let (dst, src, guarded) = match op {
            SSAOp::Copy { dst, src } => (dst, src, None),
            SSAOp::Select {
                dst,
                cond,
                if_true,
                if_false,
            } if if_false == dst && if_true != dst => (dst, if_true, Some((cond, true))),
            SSAOp::Select {
                dst,
                cond,
                if_true,
                if_false,
            } if if_true == dst && if_false != dst => (dst, if_false, Some((cond, false))),
            _ => return None,
        };
        let (target, _) = Self::assignment_target_and_rhs(stmt)?;
        if !target.eq_ignore_ascii_case(&self.var_name(dst))
            && !target.eq_ignore_ascii_case(&dst.display_name())
            && !self
                .prepared_value_id_for_var(dst)
                .and_then(|value| self.certified_loop_carrier_name_for_value(value))
                .is_some_and(|name| target.eq_ignore_ascii_case(&name))
        {
            return None;
        }
        let prepared = self.prepared_ssa()?;
        let dst_id = prepared.graph().value_id_for_var(dst)?;
        let src_id = prepared.graph().value_id_for_var(src)?;
        let def_inst = prepared.graph().def_inst(dst_id)?;
        let inst = prepared.graph().inst(def_inst)?;
        let r2ssa::InstPayload::Phi { predecessors } = &inst.payload else {
            return None;
        };
        let exact_phi_edge = predecessors.iter().zip(&inst.inputs).any(|(pred, input)| {
            *input == src_id
                && prepared
                    .graph()
                    .block(*pred)
                    .is_some_and(|block| block.addr == predecessor)
        });
        if !inst.inputs.contains(&src_id) {
            return None;
        }
        let phi_block = prepared.graph().block(inst.block)?.addr;
        let kind = match guarded {
            None if exact_phi_edge
                && prepared.successors(predecessor).as_slice() == [phi_block] =>
            {
                PhiEdgeRenderKind::Direct
            }
            None if exact_phi_edge
                && prepared.successors(predecessor).contains(&phi_block)
                && prepared.function().dominates(phi_block, predecessor) =>
            {
                PhiEdgeRenderKind::UnconditionalDeadOnOtherEdges
            }
            None if matches!(
                self.certified_render_context()
                    .and_then(|render| render.render_facts.loop_carrier_for_value(dst_id)),
                Some(r2types::CertifiedEntity::LoopCarrier {
                    dominating_initializers,
                    ..
                }) if dominating_initializers.iter().any(|initializer| {
                    initializer.predecessor == predecessor
                        && initializer.value == src_id
                })
            ) =>
            {
                PhiEdgeRenderKind::Direct
            }
            None => return None,
            Some((cond, truth)) => {
                if !exact_phi_edge {
                    return None;
                }
                let condition = prepared.graph().value_id_for_var(cond)?;
                let edge_truth = match prepared.function().edge_type(predecessor, phi_block) {
                    Some(r2ssa::CFGEdge::True) => true,
                    Some(r2ssa::CFGEdge::False) => false,
                    _ => return None,
                };
                if !prepared.function().dominates(phi_block, predecessor)
                    || edge_truth != truth
                    || !prepared
                        .get_block(predecessor)
                        .and_then(|block| block.ops.last())
                        .is_some_and(|op| {
                            matches!(op, SSAOp::CBranch { cond, .. }
                                if prepared.graph().value_id_for_var(cond) == Some(condition))
                        })
                {
                    return None;
                }
                PhiEdgeRenderKind::Guarded { condition, truth }
            }
        };
        Some(PhiEdgeRenderProof {
            source: src_id,
            kind,
        })
    }

    fn is_certified_loop_carrier_phi_copy(&self, dst: &SSAVar, src: &SSAVar) -> bool {
        let Some(dst_id) = self.prepared_value_id_for_var(dst) else {
            return false;
        };
        if self.certified_loop_carrier_name_for_value(dst_id).is_none() {
            return false;
        }
        let Some(prepared) = self.prepared_ssa() else {
            return false;
        };
        let Some(src_id) = prepared.graph().value_id_for_var(src) else {
            return false;
        };
        prepared
            .graph()
            .def_inst(dst_id)
            .and_then(|inst| prepared.graph().inst(inst))
            .is_some_and(|inst| {
                matches!(&inst.payload, r2ssa::InstPayload::Phi { .. })
                    && inst.inputs.contains(&src_id)
            })
    }

    pub(crate) fn certified_residual_comment(&self, reason: impl Into<String>) -> CStmt {
        CStmt::Comment(format!("r2sleigh residual: {}", reason.into()))
    }

    pub(super) fn certified_loop_carrier_name_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<String> {
        let r2types::CertifiedEntity::LoopCarrier { phi, .. } = self
            .certified_render_context()?
            .render_facts
            .loop_carrier_for_value(value)?
        else {
            return None;
        };
        Some(crate::certified_loop_carrier_name(*phi))
    }

    pub(super) fn certified_memory_result_name_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<String> {
        let fact = self
            .certified_render_context()?
            .exact_memory_read_for_value(value)?;
        Some(crate::certified_memory_result_name(fact.access))
    }

    pub(crate) fn certified_loop_carrier_update_name_for_value_at_latch(
        &self,
        value: r2ssa::ValueId,
        latch: u64,
    ) -> Option<String> {
        let r2types::CertifiedEntity::LoopCarrier { phi, .. } = self
            .certified_render_context()?
            .render_facts
            .loop_carrier_update_for_value_at_latch(value, latch)?
        else {
            return None;
        };
        Some(crate::certified_loop_carrier_name(*phi))
    }

    pub(crate) fn certified_callsite_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&r2types::CallsiteArgumentFacts> {
        self.inputs
            .callsite_facts()?
            .arguments_for_site(r2types::CallsiteKey {
                block_addr,
                op_index: op_idx,
            })
    }

    pub(crate) fn certified_call_render_fact_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&r2types::CallsiteRenderFact> {
        self.inputs
            .call_render_facts()?
            .fact_for_site(r2types::CallsiteKey {
                block_addr,
                op_index: op_idx,
            })
    }

    pub(crate) fn certified_memory_access_for_current_op(
        &self,
        is_write: bool,
    ) -> Option<&r2types::MemoryAccessRenderFact> {
        let block_addr = self.current_block_addr.get()?;
        let op_idx = self.current_op_idx.get()?;
        self.certified_render_context()?
            .memory_access_for_op(block_addr, op_idx, is_write)
    }

    pub(crate) fn certified_memory_read_for_value_dependency(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&r2types::MemoryAccessRenderFact> {
        self.certified_render_context()?
            .memory_read_for_value_dependency(value)
    }

    pub(super) fn record_certified_call_arg_memory_render_proofs(&self, values: &[r2ssa::ValueId]) {
        return;

        let mut seen = BTreeSet::new();
        for value in values {
            let Some(cert) = self.certified_memory_read_for_value_dependency(*value) else {
                continue;
            };
            let key = (cert.block_addr, cert.op_index, cert.address, cert.value);
            if seen.insert(key) {
                self.record_effect_render_proof_for_memory(
                    EffectRenderProofKind::MemoryRead,
                    cert.block_addr,
                    cert.op_index,
                    cert.space,
                    cert.address,
                    cert.value,
                );
            }
        }
    }

    pub(crate) fn certified_return_for_current_op(&self) -> Option<&ReturnValueRenderFact> {
        let block_addr = self.current_block_addr.get()?;
        let op_idx = self.current_op_idx.get()?;
        self.certified_return_for_op(block_addr, op_idx)
    }

    pub(crate) fn certified_return_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&ReturnValueRenderFact> {
        self.certified_render_context()?
            .return_for_op(block_addr, op_idx)
    }

    pub(crate) fn current_return_target_is_certified(&self, target: &SSAVar) -> bool {
        return true;

        let Some(cert) = self.certified_return_for_current_op() else {
            return false;
        };
        let Some(value) = self.prepared_value_id_for_var(target) else {
            return false;
        };
        cert.value == value
            && self
                .certified_render_context()
                .is_some_and(|proof| proof.expression_is_renderable(value))
    }

    fn certified_return_expr_for_value(&self, value: r2ssa::ValueId) -> Option<CExpr> {
        let prepared = self.prepared_ssa()?;
        if prepared
            .call_result_certificate_for_value(value)
            .is_some_and(|result| result.relation.is_identity())
        {
            return self.certified_call_result_expr_for_value(value);
        }

        if let Some(expr) = self.certified_structural_expr_for_value(value, 0, &mut BTreeSet::new())
        {
            return Some(expr);
        }
        if prepared.graph().def_inst(value).is_some() {
            return None;
        }

        let var = prepared.value_var(value)?;
        if var.is_const() {
            return self.certified_const_expr(var);
        }
        self.render_certified_value_expr_for_var(var)
    }

    fn certified_expr_for_prepared_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if var.is_const() {
            return self.certified_const_expr(var);
        }
        let value = self.prepared_value_id_for_var(var)?;
        self.certified_structural_expr_for_value(value, depth + 1, visited)
    }

    fn certified_structural_expr_for_value(
        &self,
        value: r2ssa::ValueId,
        depth: u32,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        if let Some(name) = self.certified_loop_carrier_name_for_value(value) {
            return Some(CExpr::Var(name));
        }
        if let Some(name) = self.certified_memory_result_name_for_value(value) {
            return Some(CExpr::Var(name));
        }
        if !visited.insert(value) {
            return None;
        }

        let result = (|| {
            let prepared = self.prepared_ssa()?;
            let var = prepared.value_var(value)?;
            if var.is_const() {
                return self.certified_const_expr(var);
            }
            if prepared
                .call_result_certificate_for_value(value)
                .is_some_and(|result| result.relation.is_identity())
            {
                return self.certified_call_result_expr_for_value(value);
            }
            let expression_renderable = self
                .certified_render_context()
                .is_some_and(|proof| proof.expression_is_renderable(value));
            if var.version == 0 && var.is_register() {
                if !expression_renderable {
                    return None;
                }
                if let Some(expr) = self.certified_parameter_expr_for_value(value) {
                    return Some(expr);
                }
                if self.stable_semantic_ids_are_required() {
                    return None;
                }
                let rendered = self.var_name(var);
                return Some(
                    self.arg_alias_for_rendered_name(&rendered)
                        .or_else(|| self.certified_signature_arg_alias_for_register(&rendered))
                        .map(CExpr::Var)
                        .unwrap_or_else(|| CExpr::Var(rendered)),
                );
            }

            let inst_id = prepared.graph().def_inst(value)?;
            let inst = prepared.graph().inst(inst_id)?;
            let transparent_value_forward = matches!(
                &inst.payload,
                r2ssa::InstPayload::Op(
                    SSAOp::Copy { .. }
                        | SSAOp::New { .. }
                        | SSAOp::Cast { .. }
                        | SSAOp::Subpiece { .. }
                        | SSAOp::IntZExt { .. }
                        | SSAOp::IntSExt { .. }
                        | SSAOp::Trunc { .. }
                )
            );
            let is_memory_load =
                matches!(&inst.payload, r2ssa::InstPayload::Op(SSAOp::Load { .. }));
            if !expression_renderable && !is_memory_load && !transparent_value_forward {
                return None;
            }
            match &inst.payload {
                r2ssa::InstPayload::Phi { predecessors } => {
                    if let Some(guarded) = self
                        .certified_render_context()
                        .and_then(|render| render.render_facts.guarded_phi_for_value(value))
                    {
                        let expected_sources = inst
                            .inputs
                            .iter()
                            .copied()
                            .map(r2ssa::SemanticId::expression)
                            .collect::<BTreeSet<_>>();
                        let rendered_sources = guarded
                            .when_true
                            .sources
                            .iter()
                            .chain(&guarded.when_false.sources)
                            .copied()
                            .collect::<BTreeSet<_>>();
                        let r2ssa::SemanticId::Predicate(predicate) = guarded.predicate else {
                            return None;
                        };
                        let r2ssa::SemanticId::Expression(when_true) = guarded.when_true.rendered
                        else {
                            return None;
                        };
                        let r2ssa::SemanticId::Expression(when_false) = guarded.when_false.rendered
                        else {
                            return None;
                        };
                        if expected_sources != rendered_sources
                            || guarded.when_true.sources.is_empty()
                            || guarded.when_false.sources.is_empty()
                        {
                            return None;
                        }
                        return Some(CExpr::Ternary {
                            cond: Box::new(self.certified_predicate_expr_for_id(predicate)?),
                            then_expr: Box::new(self.certified_structural_expr_for_value(
                                when_true,
                                depth + 1,
                                visited,
                            )?),
                            else_expr: Box::new(self.certified_structural_expr_for_value(
                                when_false,
                                depth + 1,
                                visited,
                            )?),
                        });
                    }
                    let compute_latch = |pred_addr: u64| {
                        self.control_facts().and_then(|facts| {
                            facts
                                .loops
                                .values()
                                .find_map(|fact| fact.latches.contains(&pred_addr).then_some(true))
                        })
                    };
                    // First pass: try non-raw inputs only
                    let mut rendered: Vec<(Option<bool>, CExpr)> = Vec::new();
                    for (i, input) in inst.inputs.iter().enumerate() {
                        let Some(expr) =
                            self.certified_structural_expr_for_value(*input, depth + 1, visited)
                        else {
                            continue;
                        };
                        if self.certified_return_expr_contains_raw_storage_name(&expr) {
                            continue;
                        }
                        let is_latch = predecessors
                            .get(i)
                            .and_then(|pred_id| prepared.graph().block(*pred_id))
                            .map(|block| block.addr)
                            .and_then(compute_latch)
                            .unwrap_or(false);
                        rendered.push((Some(is_latch), expr));
                    }
                    // Second pass: if empty and structurally backed, accept raw inputs
                    let has_raw_fallback = rendered.is_empty()
                        && self.control_facts().is_some_and(|facts| {
                            !facts.loops.is_empty() || !facts.switches.is_empty()
                        });
                    if has_raw_fallback {
                        for (i, input) in inst.inputs.iter().enumerate() {
                            let Some(expr) = self.certified_structural_expr_for_value(
                                *input,
                                depth + 1,
                                visited,
                            ) else {
                                continue;
                            };
                            let is_latch = predecessors
                                .get(i)
                                .and_then(|pred_id| prepared.graph().block(*pred_id))
                                .map(|block| block.addr)
                                .and_then(compute_latch)
                                .unwrap_or(false);
                            rendered.push((Some(is_latch), expr));
                        }
                    }
                    let latch_exprs: Vec<_> = rendered
                        .iter()
                        .filter(|(is_latch, _)| is_latch.unwrap_or(false))
                        .map(|(_, expr)| expr)
                        .collect();
                    let unique_exprs: Vec<_> = rendered.iter().map(|(_, expr)| expr).fold(
                        Vec::<&CExpr>::new(),
                        |mut acc, expr| {
                            if !acc.contains(&expr) {
                                acc.push(expr);
                            }
                            acc
                        },
                    );
                    if latch_exprs.len() == 1 {
                        Some(latch_exprs[0].clone())
                    } else if unique_exprs.len() == 1 {
                        Some(unique_exprs[0].clone())
                    } else if !rendered.is_empty() && has_raw_fallback {
                        rendered.into_iter().next().map(|(_, expr)| expr)
                    } else {
                        None
                    }
                }
                r2ssa::InstPayload::Op(op) => match op {
                    SSAOp::Copy { src, .. } => {
                        self.certified_expr_for_prepared_var(src, depth + 1, visited)
                    }
                    SSAOp::Load { addr: _, .. } => {
                        let (block_addr, op_idx) = prepared.inst_op_site(inst_id)?;
                        let fact = self
                            .certified_render_context()?
                            .memory_access_for_op(block_addr, op_idx, false)?;
                        if fact.value != Some(value) {
                            return None;
                        }
                        let rendered = self.render_certified_memory_expr_for_fact(
                            fact,
                            type_from_size(fact.width),
                        )?;
                        if self.expr_contains_raw_stack_base_arithmetic(&rendered)
                            || self.certified_return_expr_contains_raw_storage_name(&rendered)
                        {
                            return None;
                        }
                        self.record_effect_render_proof_for_memory(
                            EffectRenderProofKind::MemoryRead,
                            block_addr,
                            op_idx,
                            fact.space,
                            fact.address,
                            fact.value,
                        );
                        Some(rendered)
                    }
                    SSAOp::IntAdd { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Add, a, b, depth, visited)
                    }
                    SSAOp::IntSub { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Sub, a, b, depth, visited)
                    }
                    SSAOp::IntMult { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Mul, a, b, depth, visited)
                    }
                    SSAOp::IntDiv { a, b, .. } | SSAOp::IntSDiv { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Div, a, b, depth, visited)
                    }
                    SSAOp::IntRem { a, b, .. } | SSAOp::IntSRem { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Mod, a, b, depth, visited)
                    }
                    SSAOp::IntAnd { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitAnd, a, b, depth, visited)
                    }
                    SSAOp::IntOr { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitOr, a, b, depth, visited)
                    }
                    SSAOp::IntXor { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitXor, a, b, depth, visited)
                    }
                    SSAOp::IntLeft { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Shl, a, b, depth, visited)
                    }
                    SSAOp::IntRight { a, b, .. } | SSAOp::IntSRight { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Shr, a, b, depth, visited)
                    }
                    SSAOp::IntEqual { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Eq, a, b, depth, visited)
                    }
                    SSAOp::IntNotEqual { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Ne, a, b, depth, visited)
                    }
                    SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Lt, a, b, depth, visited)
                    }
                    SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Le, a, b, depth, visited)
                    }
                    SSAOp::BoolAnd { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::And, a, b, depth, visited)
                    }
                    SSAOp::BoolOr { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::Or, a, b, depth, visited)
                    }
                    SSAOp::BoolXor { a, b, .. } => {
                        self.certified_binary_return_expr(BinaryOp::BitXor, a, b, depth, visited)
                    }
                    SSAOp::IntNegate { src, .. } => self
                        .certified_expr_for_prepared_var(src, depth + 1, visited)
                        .map(|expr| CExpr::unary(UnaryOp::Neg, expr)),
                    SSAOp::IntNot { src, .. } => self
                        .certified_expr_for_prepared_var(src, depth + 1, visited)
                        .map(|expr| CExpr::unary(UnaryOp::BitNot, expr)),
                    SSAOp::BoolNot { src, .. } => self
                        .certified_expr_for_prepared_var(src, depth + 1, visited)
                        .map(|expr| CExpr::unary(UnaryOp::Not, expr)),
                    SSAOp::Select {
                        cond,
                        if_true,
                        if_false,
                        ..
                    } => {
                        let cond_value = self.prepared_value_id_for_var(cond)?;
                        if let Some(truth) =
                            self.certified_value_truth_in_current_control_domain(cond_value)
                        {
                            return self.certified_expr_for_prepared_var(
                                if truth { if_true } else { if_false },
                                depth + 1,
                                visited,
                            );
                        }
                        Some(CExpr::Ternary {
                            cond: Box::new(self.certified_expr_for_prepared_var(
                                cond,
                                depth + 1,
                                visited,
                            )?),
                            then_expr: Box::new(self.certified_expr_for_prepared_var(
                                if_true,
                                depth + 1,
                                visited,
                            )?),
                            else_expr: Box::new(self.certified_expr_for_prepared_var(
                                if_false,
                                depth + 1,
                                visited,
                            )?),
                        })
                    }
                    SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src }
                    | SSAOp::Cast { dst, src } => {
                        let expr = self.certified_expr_for_prepared_var(src, depth + 1, visited)?;
                        let source_already_matches_return = depth == 0
                            && dst.size > src.size
                            && self.inputs.function_return_type.and_then(CType::bits)
                                == Some(src.size.saturating_mul(8));
                        Some(if source_already_matches_return {
                            expr
                        } else {
                            CExpr::cast(type_from_size(dst.size), expr)
                        })
                    }
                    SSAOp::Subpiece { dst, src, offset } => {
                        let expr = self.certified_expr_for_prepared_var(src, depth + 1, visited)?;
                        if *offset == 0 {
                            Some(CExpr::cast(uint_type_from_size(dst.size), expr))
                        } else {
                            let shift_bits = offset.saturating_mul(8);
                            let shifted = CExpr::binary(
                                BinaryOp::Shr,
                                CExpr::cast(uint_type_from_size(src.size), expr),
                                CExpr::IntLit(shift_bits as i64),
                            );
                            Some(CExpr::cast(uint_type_from_size(dst.size), shifted))
                        }
                    }
                    _ => None,
                },
            }
        })();

        visited.remove(&value);
        result
    }

    fn certified_value_truth_in_current_control_domain(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<bool> {
        let block_addr = self.current_block_addr.get()?;
        let facts = self.control_facts()?;
        if !facts
            .control_domain_for_block(block_addr)
            .is_some_and(|domain| domain.complete)
        {
            return None;
        }
        let target_compare = self.certified_compare_for_value(value);
        let mut proven = None;
        for assumption in facts.assumptions_for_block(block_addr) {
            let Some(predicate) = facts
                .branch_predicates
                .values()
                .find(|predicate| predicate.id == assumption.predicate)
            else {
                continue;
            };
            let implied = if predicate.condition == value {
                Some(assumption.truth)
            } else {
                let Some(target_compare) = target_compare else {
                    continue;
                };
                let Some(comparison) = predicate.comparison.as_ref() else {
                    continue;
                };
                let Some(predicate_compare) = self.certified_canonical_compare(
                    comparison.kind,
                    comparison.lhs,
                    comparison.rhs,
                ) else {
                    continue;
                };
                certified_compare_truth_relation(target_compare, predicate_compare)
                    .map(|same_truth| assumption.truth == same_truth)
            };
            let Some(implied) = implied else {
                continue;
            };
            if proven.is_some_and(|existing| existing != implied) {
                return None;
            }
            proven = Some(implied);
        }
        proven
    }

    fn certified_compare_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<(r2ssa::CompareKind, r2ssa::SemanticId, r2ssa::SemanticId)> {
        let prepared = self.prepared_ssa()?;
        let inst = prepared.graph().inst(prepared.graph().def_inst(value)?)?;
        let r2ssa::InstPayload::Op(op) = &inst.payload else {
            return None;
        };
        let (kind, lhs, rhs) = match op {
            SSAOp::IntEqual { a, b, .. } => (r2ssa::CompareKind::Equal, a, b),
            SSAOp::IntNotEqual { a, b, .. } => (r2ssa::CompareKind::NotEqual, a, b),
            SSAOp::IntLess { a, b, .. } => (r2ssa::CompareKind::Less, a, b),
            SSAOp::IntSLess { a, b, .. } => (r2ssa::CompareKind::SignedLess, a, b),
            SSAOp::IntLessEqual { a, b, .. } => (r2ssa::CompareKind::LessEqual, a, b),
            SSAOp::IntSLessEqual { a, b, .. } => (r2ssa::CompareKind::SignedLessEqual, a, b),
            _ => return None,
        };
        Some((
            kind,
            self.certified_canonical_value(lhs)?,
            self.certified_canonical_value(rhs)?,
        ))
    }

    fn certified_canonical_compare(
        &self,
        kind: r2ssa::CompareKind,
        lhs: r2ssa::ValueId,
        rhs: r2ssa::ValueId,
    ) -> Option<(r2ssa::CompareKind, r2ssa::SemanticId, r2ssa::SemanticId)> {
        let prepared = self.prepared_ssa()?;
        Some((
            kind,
            self.certified_canonical_value(prepared.value_var(lhs)?)?,
            self.certified_canonical_value(prepared.value_var(rhs)?)?,
        ))
    }

    fn certified_canonical_value(&self, var: &SSAVar) -> Option<r2ssa::SemanticId> {
        let prepared = self.prepared_ssa()?;
        let mut value = self.prepared_value_id_for_var(var)?;
        let mut visited = BTreeSet::new();
        for _ in 0..32 {
            if !visited.insert(value) {
                return None;
            }
            if let Some(reload) = prepared.stack_reload_certificate_for_value(value)
                && reload.canonical_source != value
            {
                value = reload.canonical_source;
                continue;
            }
            let current = prepared.value_var(value)?;
            if current.version == 0 && current.is_register() {
                let certified = self
                    .certified_render_context()?
                    .render_facts
                    .certified_expr_for_value(value)?;
                let mut parameters = certified
                    .bindings
                    .iter()
                    .filter(|binding| matches!(binding, r2ssa::SemanticId::Parameter(_)));
                let parameter = *parameters.next()?;
                if parameters.next().is_none() {
                    return Some(parameter);
                }
                return None;
            }
            if let Some(object) = prepared.object_for_var(current, r2il::SpaceId::Ram) {
                let identity = r2ssa::SemanticId::stack_slot(object);
                if self
                    .certified_render_context()?
                    .render_facts
                    .certified_entities
                    .contains_key(&identity)
                {
                    return Some(identity);
                }
            }
            let Some(root) = self.prepared_canonical_value_root(current) else {
                return Some(r2ssa::SemanticId::expression(value));
            };
            let Some(root_value) = self.prepared_value_id_for_var(&root) else {
                return Some(r2ssa::SemanticId::expression(value));
            };
            if root_value == value {
                return Some(r2ssa::SemanticId::expression(value));
            }
            value = root_value;
        }
        None
    }

    fn certified_return_expr_contains_raw_storage_name(&self, expr: &CExpr) -> bool {
        let mut contains_raw = false;
        expr.visit(&mut |node| {
            if contains_raw {
                return;
            }
            if let CExpr::Var(name) = node {
                let lower = name.to_ascii_lowercase();
                contains_raw = self.is_raw_register_public_call_arg_name(name)
                    || self.inputs.arch.is_stack_base_name(&lower)
                    || self.inputs.arch.is_return_register_name(&lower)
                    || self.is_transient_visible_name(name)
                    || self.is_low_signal_visible_name(name);
            }
        });
        contains_raw
    }

    fn certified_binary_return_expr(
        &self,
        op: BinaryOp,
        a: &SSAVar,
        b: &SSAVar,
        depth: u32,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> Option<CExpr> {
        Some(CExpr::binary(
            op,
            self.certified_expr_for_prepared_var(a, depth + 1, visited)?,
            self.certified_expr_for_prepared_var(b, depth + 1, visited)?,
        ))
    }

    pub(crate) fn certified_return_expr_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<(CExpr, r2ssa::ValueId)> {
        let cert = self.certified_return_for_op(block_addr, op_idx)?;
        let expr = self.rewrite_typed_return_literal_expr(
            self.certified_return_expr_for_value(cert.value)?,
            self.current_return_context(),
        );
        if self.certified_return_expr_contains_raw_storage_name(&expr)
            && self
                .control_facts()
                .is_none_or(|facts| facts.loops.is_empty() && facts.switches.is_empty())
        {
            return None;
        }
        Some((expr, cert.value))
    }

    fn certified_call_result_fact_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<&r2types::CallResultFact> {
        let fact = self.inputs.call_result_facts()?.result_for_value(value)?;
        (fact.value == value).then_some(fact)
    }

    pub(crate) fn certified_call_result_expr_for_value(
        &self,
        value: r2ssa::ValueId,
    ) -> Option<CExpr> {
        let prepared = self.prepared_ssa()?;
        let prepared_result = prepared.call_result_certificate_for_value(value)?;
        let fact = self.certified_call_result_fact_for_value(value)?;
        if fact.call_site_id != prepared_result.call_site
            || fact.relation != prepared_result.relation
            || !fact.relation.is_identity()
        {
            return None;
        }
        let binding = r2ssa::SemanticId::call(fact.call_site_id);
        let certified = self
            .certified_render_context()?
            .render_facts
            .certified_expr_for_value(value)?;
        if !certified.fact.renderable || !certified.bindings.contains(&binding) {
            return None;
        }
        let source_call = (fact.callsite.block_addr, fact.callsite.op_index);
        if let Some(owner) = self.certified_assigned_call_result_owner_expr_for_source(source_call)
        {
            return Some(owner);
        }
        if let r2ssa::ReturnCarrier::StackSlot { object, offset, .. } = &fact.carrier {
            let stack_binding = r2ssa::SemanticId::stack_slot(*object);
            if !certified.bindings.contains(&stack_binding) {
                return None;
            }
            return self
                .certified_stack_var_name_for_object_offset(*object, *offset)
                .map(CExpr::Var);
        }
        self.synthesized_call_expr_for_source_call(source_call)
    }

    fn certified_return_members_have_external_layout(&self, expr: &CExpr) -> bool {
        let mut members = BTreeSet::new();
        expr.visit(&mut |node| {
            if let CExpr::Member { member, .. } | CExpr::PtrMember { member, .. } = node {
                members.insert(member.to_ascii_lowercase());
            }
        });
        if members.is_empty() {
            return true;
        }

        let mut external_names = BTreeSet::new();
        for structure in self.inputs.external_type_db.structs.values() {
            external_names.extend(
                structure
                    .fields
                    .values()
                    .map(|field| field.name.to_ascii_lowercase()),
            );
        }
        for union in self.inputs.external_type_db.unions.values() {
            external_names.extend(
                union
                    .fields
                    .values()
                    .map(|field| field.name.to_ascii_lowercase()),
            );
        }

        !external_names.is_empty() && members.iter().all(|member| external_names.contains(member))
    }

    pub(crate) fn summary_view(&self) -> Option<&r2types::InterprocSummaryView> {
        self.inputs.summary_view()
    }

    pub(crate) fn prepared_semantic_view(&self) -> Option<&analysis::PreparedSemanticView> {
        if let Some(view) = self.inputs.prepared_semantic_view {
            return Some(view);
        }

        let prepared = self.inputs.prepared_ssa?;
        if self.prepared_semantic_view_building.get() {
            return None;
        }

        self.prepared_semantic_view_building.set(true);
        let view = self.prepared_semantic_view_cache.get_or_init(|| {
            analysis::PreparedSemanticView::build(analysis::PreparedSemanticViewInputs {
                prepared,
                abi_arg_regs: &self.inputs.arch.arg_regs,
                stack_slots: self.inputs.stack_slots,
                visible_bindings: self.inputs.visible_bindings,
                param_register_aliases: self.inputs.param_register_aliases,
                function_facts: self.inputs.function_facts,
                #[cfg(test)]
                certified_rendering_required: self.requires_certified_rendering(),
            })
        });
        self.prepared_semantic_view_building.set(false);
        Some(view)
    }

    fn prepared_facts(&self) -> Option<&PreparedFunctionFacts> {
        self.prepared_ssa().map(SsaArtifact::facts)
    }

    pub(crate) fn prepared_objects(&self) -> Option<&ObjectModel> {
        self.prepared_facts()
            .map(|facts| &facts.objects)
            .or(self.inputs.prepared_objects)
    }

    pub(crate) fn control_facts(&self) -> Option<&r2types::FunctionControlFacts> {
        self.inputs.control_facts()
    }

    pub(crate) fn prepared_decompile_prep_facts(&self) -> Option<&DecompilePrepFacts> {
        self.prepared_ssa()
            .and_then(|prepared| prepared.function().decompile_prep_facts())
    }

    fn enter_resolution_guard(&self, phase: ResolutionPhase, name: &str) -> bool {
        self.resolution_guard
            .borrow_mut()
            .insert(ResolutionGuardKey {
                phase,
                name: name.to_string(),
            })
    }

    fn leave_resolution_guard(&self, phase: ResolutionPhase, name: &str) {
        self.resolution_guard
            .borrow_mut()
            .remove(&ResolutionGuardKey {
                phase,
                name: name.to_string(),
            });
    }

    fn resolution_cycle_fallback(&self, name: &str) -> Option<CExpr> {
        self.direct_definition_expr(name)
            .or_else(|| self.stable_owned_call_result_expr_for_name(name, true))
            .or_else(|| Some(self.expr_for_ssa_fallback_name(name)))
    }

    pub(crate) fn prepared_call_view_for_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&analysis::PreparedCallView> {
        self.prepared_semantic_view()
            .and_then(|view| view.call_view_for_site((block_addr, op_idx)))
    }

    pub(crate) fn prepared_memory_defs_for_current_op(&self) -> Option<&[MemoryDefFact]> {
        let prepared = self.inputs.prepared_ssa?;
        let block_addr = self.current_block_addr.get()?;
        let op_idx = self.current_op_idx.get()?;
        prepared.memory_defs_for_op_site(block_addr, op_idx)
    }

    pub(crate) fn prepared_var_for_value_id(&self, value_id: r2ssa::ValueId) -> Option<&SSAVar> {
        self.inputs.prepared_ssa?.value_var(value_id)
    }

    pub(crate) fn prepared_value_id_for_var(&self, var: &SSAVar) -> Option<r2ssa::ValueId> {
        self.inputs.prepared_ssa?.graph().value_id_for_var(var)
    }

    pub(crate) fn prepared_canonical_value_root(&self, var: &SSAVar) -> Option<SSAVar> {
        let facts = self.prepared_decompile_prep_facts()?;
        let mut current = var.clone();
        for _ in 0..32 {
            let Some(next) = facts.canonical_root_of(&current) else {
                break;
            };
            if next == &current {
                break;
            }
            current = next.clone();
        }
        Some(current)
    }

    pub(crate) fn use_counts_map(&self) -> &HashMap<String, usize> {
        &self.use_info().use_counts
    }
    pub(crate) fn definitions_map(&self) -> &HashMap<String, CExpr> {
        &self.use_info().definitions
    }
    pub(crate) fn frame_slot_merges_map(
        &self,
    ) -> &HashMap<String, analysis::FrameSlotMergeSummary> {
        &self.use_info().frame_slot_merges
    }
    pub(crate) fn phi_sources_map(&self) -> &HashMap<String, Vec<SSAVar>> {
        &self.use_info().phi_sources
    }
    pub(crate) fn formatted_defs_map(&self) -> &HashMap<String, CExpr> {
        &self.use_info().formatted_defs
    }
    pub(crate) fn copy_sources_map(&self) -> &HashMap<String, String> {
        &self.use_info().copy_sources
    }
    pub(crate) fn ptr_members_map(&self) -> &HashMap<String, (SSAVar, i64)> {
        &self.use_info().ptr_members
    }
    pub(crate) fn definition_for_value_id(&self, value_id: r2ssa::ValueId) -> Option<&CExpr> {
        self.use_info().definition_for_value(value_id)
    }
    pub(crate) fn value_id_for_name(&self, name: &str) -> Option<r2ssa::ValueId> {
        self.use_info().value_id_for_name(name)
    }
    pub(crate) fn definition_for_name(&self, name: &str) -> Option<&CExpr> {
        self.use_info().render_definition_for_name(name)
    }
    pub(crate) fn semantic_value_for_value_id(
        &self,
        value_id: r2ssa::ValueId,
    ) -> Option<&analysis::SemanticValue> {
        self.use_info().semantic_value_for_value(value_id)
    }
    pub(crate) fn semantic_value_for_name(&self, name: &str) -> Option<&analysis::SemanticValue> {
        self.use_info().render_semantic_value_for_name(name)
    }
    pub(crate) fn forwarded_value_for_value_id(
        &self,
        value_id: r2ssa::ValueId,
    ) -> Option<&analysis::ValueProvenance> {
        self.use_info().forwarded_value_for_value(value_id)
    }
    pub(crate) fn forwarded_value_for_name(
        &self,
        name: &str,
    ) -> Option<&analysis::ValueProvenance> {
        self.use_info().render_forwarded_value_for_name(name)
    }

    pub(crate) fn render_copy_source_for_name(&self, name: &str) -> Option<String> {
        self.use_info().render_copy_source_for_name(name)
    }
    pub(crate) fn has_renderable_named_fact(&self, name: &str) -> bool {
        self.use_info().has_renderable_named_fact(name)
    }
    pub(crate) fn known_named_values(&self) -> Vec<String> {
        self.use_info().known_named_values()
    }
    pub(crate) fn stack_slots(&self) -> impl Iterator<Item = analysis::StackSlotProvenance> + '_ {
        self.use_info().stack_slots()
    }
    pub(crate) fn condition_vars_set(&self) -> &HashSet<String> {
        &self.use_info().condition_vars
    }
    pub(crate) fn pinned_set(&self) -> &HashSet<String> {
        &self.use_info().pinned
    }
    pub(crate) fn call_args_map(&self) -> &HashMap<(u64, usize), Vec<analysis::CallArgBinding>> {
        &self.use_info().call_args
    }
    pub(crate) fn callee_identity_for_direct_target(&self, addr: u64) -> CalleeIdentity {
        self.inputs
            .callee_resolution()
            .and_then(|facts| facts.identity_for_direct_addr(addr))
            .cloned()
            .unwrap_or_else(|| CalleeIdentity::from_name(&format!("const:{addr:x}")))
    }
    pub(crate) fn callee_identity_for_name(&self, name: &str) -> CalleeIdentity {
        if let Some(addr) = parse_address_from_var_name(name) {
            return self.callee_identity_for_direct_target(addr);
        }
        if let Some(identity) = self
            .inputs
            .callee_resolution()
            .and_then(|facts| facts.identity_for_name(name))
        {
            return identity.clone();
        }
        CalleeIdentity::from_name(name)
    }
    pub(crate) fn callee_identity_for_expr(&self, expr: &CExpr) -> Option<CalleeIdentity> {
        call_arg_callee_name(expr).map(|name| self.callee_identity_for_name(name))
    }

    #[cfg(test)]
    pub(crate) fn direct_target_addr_from_callee_expr(&self, expr: &CExpr) -> Option<u64> {
        match expr {
            CExpr::Var(name) => parse_address_from_var_name(name),
            CExpr::Paren(inner) | CExpr::AddrOf(inner) | CExpr::Deref(inner) => {
                self.direct_target_addr_from_callee_expr(inner)
            }
            CExpr::Cast { expr: inner, .. } => self.direct_target_addr_from_callee_expr(inner),
            _ => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn callee_target_policy_for_identity(
        &self,
        identity: &CalleeIdentity,
    ) -> r2types::CalleeTargetPolicyDecision {
        identity.target_policy_decision(self.inputs.callee_resolution(), self.inputs.callee_facts())
    }
    pub(crate) fn call_result_aliases_map(
        &self,
    ) -> &std::collections::BTreeMap<(u64, usize), std::collections::BTreeSet<String>> {
        &self.use_info().call_result_aliases
    }
    pub(crate) fn call_result_exprs_map(&self) -> &std::collections::BTreeMap<(u64, usize), CExpr> {
        &self.use_info().call_result_exprs
    }
    pub(crate) fn direct_call_result_aliases_set(&self) -> &HashSet<String> {
        &self.use_info().direct_call_result_aliases
    }
    pub(crate) fn switch_selector_roots_map(
        &self,
    ) -> &std::collections::BTreeMap<u64, analysis::SemanticValue> {
        &self.use_info().switch_selector_roots
    }
    pub(crate) fn consumed_by_call_set(&self) -> &HashSet<String> {
        &self.use_info().consumed_by_call
    }
    pub(crate) fn var_aliases_map(&self) -> &HashMap<String, String> {
        &self.use_info().var_aliases
    }
    pub(crate) fn type_hints_map(&self) -> &HashMap<String, CType> {
        &self.use_info().type_hints
    }
    pub(crate) fn flag_origins_map(&self) -> &HashMap<String, (String, String)> {
        &self.flag_info().flag_origins
    }
    pub(crate) fn flag_only_values_set(&self) -> &HashSet<String> {
        &self.flag_info().flag_only_values
    }
    pub(crate) fn stack_vars_map(&self) -> &HashMap<i64, String> {
        &self.stack_info().stack_vars
    }
    pub(crate) fn stack_arg_aliases_map(&self) -> &HashMap<i64, String> {
        &self.stack_info().stack_arg_aliases
    }
    pub(crate) fn to_pass_env(&self) -> analysis::PassEnv<'_> {
        analysis::PassEnv {
            string_literals: self.inputs.display_names.strings(),
            ptr_size: self.inputs.arch.ptr_size,
            sp_name: &self.inputs.arch.sp_name,
            fp_name: &self.inputs.arch.fp_name,
            ret_reg_name: &self.inputs.arch.ret_reg_name,
            #[cfg(test)]
            function_names: self.inputs.function_names,
            #[cfg(test)]
            strings: self.inputs.strings,
            #[cfg(test)]
            symbols: self.inputs.symbols,
            callee_facts: self.inputs.callee_facts(),
            callee_resolution: self.inputs.callee_resolution(),
            summary_view: self.inputs.summary_view(),
            arg_regs: &self.inputs.arch.arg_regs,
            param_register_aliases: self.inputs.param_register_aliases,
            caller_saved_regs: &self.inputs.arch.caller_saved_regs,
            type_hints: &self.use_info().type_hints,
            type_oracle: self.inputs.type_oracle,
        }
    }

    #[cfg(test)]
    pub fn set_function_names(&mut self, names: HashMap<u64, String>) {
        self.inputs.function_names = Box::leak(Box::new(names));
    }

    #[cfg(test)]
    pub fn set_known_function_signatures<T>(&mut self, signatures: HashMap<String, T>)
    where
        T: Into<r2types::FunctionType>,
    {
        let normalized = signatures
            .into_iter()
            .map(|(name, sig)| (normalize_callee_name(&name), sig.into()))
            .collect::<HashMap<_, _>>();
        let ctx = r2types::CalleeIdentityContext {
            #[cfg(test)]
            function_names: self.inputs.function_names,
            #[cfg(test)]
            symbols: self.inputs.symbols,
            callee_facts: self.inputs.callee_facts(),
            known_function_signatures: &normalized,
        };
        let mut resolution = self.inputs.callee_resolution().cloned().unwrap_or_default();
        resolution.index_context(&ctx);
        let mut function_facts = self.inputs.function_facts.clone();
        function_facts.set_callee_resolution(resolution);
        self.inputs.function_facts = Box::leak(Box::new(function_facts));
    }

    #[cfg(test)]
    pub fn set_type_hints(&mut self, hints: HashMap<String, CType>) {
        self.inputs.type_hints = Box::leak(Box::new(hints.clone()));
        self.state.analysis_ctx.semantic_mut().type_hints = hints;
    }

    #[cfg(test)]
    pub fn set_external_stack_vars(
        &mut self,
        stack_vars: HashMap<i64, r2types::ExternalStackVarSpec>,
    ) {
        self.inputs.external_stack_vars = Box::leak(Box::new(stack_vars));
        let stack_slots = self
            .inputs
            .external_stack_vars
            .iter()
            .map(|(offset, slot)| {
                (
                    StackSlotKey {
                        base: slot.base.clone(),
                        offset: *offset,
                    },
                    slot.clone(),
                )
            })
            .collect();
        self.inputs.stack_slots = Box::leak(Box::new(stack_slots));
    }

    #[cfg(test)]
    pub fn set_type_oracle(&mut self, type_oracle: Option<&'a dyn TypeOracle>) {
        self.inputs.type_oracle = type_oracle;
    }

    /// Collect the set of variable names that survive folding (not inlined, not dead,
    /// not consumed by call args). Used to filter local variable declarations.
    pub fn emitted_var_names(&self, blocks: &[SSABlock]) -> HashSet<String> {
        let mut names = HashSet::new();
        for block in blocks {
            for (op_idx, op) in block.ops.iter().enumerate() {
                if self.is_stack_frame_op(op) {
                    continue;
                }
                if let Some(dst) = op.dst() {
                    if self.is_dead(dst) {
                        continue;
                    }
                    let key = dst.display_name();
                    if self.should_inline(dst) {
                        continue;
                    }
                    if self.consumed_by_call_set().contains(&key) {
                        continue;
                    }
                }
                // For Call/CallInd, check if op_to_stmt_with_args would emit it
                let is_call = matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. });
                if is_call {
                    // Calls don't produce named variables, skip
                    continue;
                }
                // This op would be emitted - collect any variable name it defines
                if let Some(dst) = op.dst() {
                    let var_name = self.var_name(dst);
                    names.insert(var_name);
                }
                // Also collect variable names used in the right-hand side
                // (These appear as Var references in the output)
                for src in op.sources() {
                    if src.is_const() || src.is_memory() {
                        continue;
                    }
                    let _ = op_idx; // suppress unused warning
                    let var_name = self.var_name(src);
                    names.insert(var_name);
                }
            }
        }
        names
    }

    /// Analyze function structure to detect return patterns.
    /// This finds the exit block and blocks that branch to it.
    pub(crate) fn analyze_function_structure(&mut self, func: &SSAFunction) {
        self.state.return_blocks.clear();
        self.state.return_stack_slots.clear();
        self.state
            .analysis_ctx
            .semantic_mut()
            .frame_slot_merges
            .clear();
        // Find exit block (the block containing SSAOp::Return)
        for block in func.blocks() {
            for op in &block.ops {
                if matches!(op, SSAOp::Return { .. }) {
                    self.state.exit_block = Some(block.addr);
                    break;
                }
            }
            if self.state.exit_block.is_some() {
                break;
            }
        }

        // Find blocks that branch directly to the exit block
        if let Some(exit_addr) = self.state.exit_block {
            let pure_control_exit = func
                .get_block(exit_addr)
                .is_some_and(|block| self.exit_block_is_control_only_epilogue(block));

            // Treat the exit block itself as a return context.
            self.state.return_blocks.insert(exit_addr);
            self.detect_return_stack_slots(func, exit_addr);

            // Predecessors are only return contexts when they materially carry
            // the returned value into the exit block. Marking every predecessor
            // as a return block causes non-return body blocks to sprout
            // synthesized returns.
            for pred in func.predecessors(exit_addr) {
                if pred != exit_addr
                    && self.block_is_exit_return_context(
                        func,
                        pred,
                        exit_addr,
                        pure_control_exit,
                        true,
                    )
                {
                    self.state.return_blocks.insert(pred);
                }
            }

            for block in func.blocks() {
                // Skip the exit block itself
                if block.addr == exit_addr {
                    continue;
                }

                for op in &block.ops {
                    if let SSAOp::Branch { target } = op {
                        // Extract address from the target variable (e.g., "ram:401256_0")
                        if let Some(addr) = self.extract_branch_target_address(target)
                            && addr == exit_addr
                            && self.block_is_exit_return_context(
                                func,
                                block.addr,
                                exit_addr,
                                pure_control_exit,
                                false,
                            )
                        {
                            self.state.return_blocks.insert(block.addr);
                        }
                    }
                }
            }

            // Phi metadata can preserve predecessor edges even when CFG recovery
            // is sparse, but only keep them when the source block really carries
            // the eventual return value.
            if let Some(exit_blk) = func.get_block(exit_addr) {
                for phi in &exit_blk.phis {
                    for (src_addr, _) in &phi.sources {
                        // src_addr is already u64
                        if *src_addr != exit_addr
                            && self.block_is_exit_return_context(
                                func,
                                *src_addr,
                                exit_addr,
                                pure_control_exit,
                                false,
                            )
                        {
                            self.state.return_blocks.insert(*src_addr);
                        }
                    }
                }
            }
        }
        let type_hints = self.state.analysis_ctx.semantic().type_hints.clone();
        let env = analysis::PassEnv {
            string_literals: self.inputs.display_names.strings(),
            ptr_size: self.inputs.arch.ptr_size,
            sp_name: &self.inputs.arch.sp_name,
            fp_name: &self.inputs.arch.fp_name,
            ret_reg_name: &self.inputs.arch.ret_reg_name,
            #[cfg(test)]
            function_names: self.inputs.function_names,
            #[cfg(test)]
            strings: self.inputs.strings,
            #[cfg(test)]
            symbols: self.inputs.symbols,
            callee_facts: self.inputs.callee_facts(),
            callee_resolution: self.inputs.callee_resolution(),
            summary_view: self.inputs.summary_view(),
            arg_regs: &self.inputs.arch.arg_regs,
            param_register_aliases: self.inputs.param_register_aliases,
            caller_saved_regs: &self.inputs.arch.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: self.inputs.type_oracle,
        };
        analysis::use_info::populate_frame_slot_merges(
            self.state.analysis_ctx.semantic_mut(),
            func,
            &env,
            self.inputs.prepared_ssa,
        );
        if self.inputs.prepared_ssa.is_none() {
            analysis::use_info::populate_switch_selector_roots(
                self.state.analysis_ctx.semantic_mut(),
                func,
                &env,
            );
        } else {
            self.state
                .analysis_ctx
                .semantic_mut()
                .switch_selector_roots
                .clear();
        }
        analysis::use_info::annotate_stack_slot_semantics(
            self.state.analysis_ctx.semantic_mut(),
            func,
            &self.state.return_stack_slots,
            &env,
        );
        let filtered_return_stack_slots = self
            .state
            .return_stack_slots
            .iter()
            .copied()
            .filter(|offset| {
                !matches!(
                    self.resolve_stack_var(*offset).as_deref(),
                    Some("stack") | Some("saved_fp")
                )
            })
            .collect();
        self.state.return_stack_slots = filtered_return_stack_slots;
    }

    fn block_is_exit_return_context(
        &self,
        func: &SSAFunction,
        block_addr: u64,
        exit_addr: u64,
        pure_control_exit: bool,
        edge_known: bool,
    ) -> bool {
        let Some(block) = func.get_block(block_addr) else {
            return false;
        };

        if !edge_known && !self.block_can_reach_exit_via_terminator(block, exit_addr) {
            return false;
        }

        if self.block_has_non_exit_successor(func, block_addr, exit_addr) {
            return false;
        }

        if !self.state.return_stack_slots.is_empty()
            && self
                .return_stack_slot_written_before_exit(block, exit_addr, edge_known)
                .is_some_and(|slot| self.state.return_stack_slots.contains(&slot))
        {
            return true;
        }

        pure_control_exit
            && self.block_writes_return_register_before_exit(block, exit_addr, edge_known)
    }

    fn block_has_non_exit_successor(
        &self,
        func: &SSAFunction,
        block_addr: u64,
        exit_addr: u64,
    ) -> bool {
        func.successors(block_addr)
            .iter()
            .any(|succ| *succ != exit_addr)
    }

    fn block_can_reach_exit_via_terminator(&self, block: &SSABlock, exit_addr: u64) -> bool {
        block.ops.iter().rev().any(|op| match op {
            SSAOp::Branch { target } | SSAOp::CBranch { target, .. } => {
                self.extract_branch_target_address(target) == Some(exit_addr)
            }
            _ => false,
        })
    }

    fn block_writes_return_register_before_exit(
        &self,
        block: &SSABlock,
        exit_addr: u64,
        edge_known: bool,
    ) -> bool {
        let mut reaches_exit = edge_known;
        for op in block.ops.iter().rev() {
            match op {
                SSAOp::Branch { target } | SSAOp::CBranch { target, .. } => {
                    if self.extract_branch_target_address(target) == Some(exit_addr) {
                        reaches_exit = true;
                    }
                }
                _ if reaches_exit => {
                    if let Some(dst) = op.dst()
                        && self
                            .inputs
                            .arch
                            .is_return_register_name(&dst.name.to_ascii_lowercase())
                    {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn detect_return_stack_slots(&mut self, func: &SSAFunction, exit_addr: u64) {
        let Some(exit_block) = func.get_block(exit_addr) else {
            return;
        };
        let pure_control_exit = self.exit_block_is_control_only_epilogue(exit_block);
        let exit_loaded_slot = if pure_control_exit {
            None
        } else {
            self.return_stack_slot_loaded_before_control_return(exit_block)
        };
        if !pure_control_exit && exit_loaded_slot.is_none() {
            return;
        }

        if let Some(exit_slot) = exit_loaded_slot {
            self.state.return_stack_slots.insert(exit_slot);
        }

        let preds = func.predecessors(exit_addr);
        if preds.is_empty() {
            return;
        }

        let mut common_slot: Option<i64> = None;
        for pred_addr in preds {
            let Some(pred_block) = func.get_block(pred_addr) else {
                return;
            };
            let Some(slot) =
                self.return_stack_slot_written_before_exit(pred_block, exit_addr, true)
            else {
                return;
            };
            match common_slot {
                Some(existing) if existing != slot => return,
                None => common_slot = Some(slot),
                Some(_) => {}
            }
        }

        if let Some(exit_slot) = exit_loaded_slot
            && common_slot != Some(exit_slot)
        {
            return;
        }

        if let Some(slot) = common_slot.or(exit_loaded_slot) {
            self.state.return_stack_slots.insert(slot);
        }
    }

    fn exit_block_is_control_only_epilogue(&self, block: &SSABlock) -> bool {
        block.ops.iter().enumerate().all(|(op_idx, op)| match op {
            SSAOp::Return { target } => self.is_control_return_target(target),
            SSAOp::Load {
                dst,
                space: r2il::SpaceId::Ram,
                ..
            } => {
                self.is_control_return_target(dst)
                    || self
                        .inputs
                        .arch
                        .is_stack_pointer_name(&dst.name.to_ascii_lowercase())
                    || self
                        .inputs
                        .arch
                        .is_frame_pointer_name(&dst.name.to_ascii_lowercase())
                    || self.load_is_control_epilogue_artifact(block, op_idx, dst)
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src } => {
                let dst_lower = dst.name.to_ascii_lowercase();
                let src_lower = src.name.to_ascii_lowercase();
                self.is_control_return_target(dst)
                    || dst.name.eq_ignore_ascii_case(&self.inputs.arch.sp_name)
                    || self.inputs.arch.is_frame_pointer_name(&dst_lower)
                        && (self.inputs.arch.is_stack_pointer_name(&src_lower)
                            || matches!(
                                block.ops.iter().enumerate().take(op_idx).find_map(
                                    |(idx, prior)| match prior {
                                        SSAOp::Load {
                                            dst: load_dst,
                                            space: r2il::SpaceId::Ram,
                                            ..
                                        } if load_dst == src => {
                                            Some(self.load_is_control_epilogue_artifact(
                                                block, idx, load_dst,
                                            ))
                                        }
                                        _ => None,
                                    }
                                ),
                                Some(true)
                            ))
                    || matches!(op, SSAOp::Copy { .. })
                        && src.is_const()
                        && self
                            .seed_copy_is_overwritten_by_control_epilogue_load(block, op_idx, dst)
            }
            SSAOp::IntAdd { dst, .. } | SSAOp::IntSub { dst, .. } => {
                dst.name.eq_ignore_ascii_case(&self.inputs.arch.sp_name)
            }
            _ => false,
        })
    }

    fn return_stack_slot_written_before_exit(
        &self,
        block: &SSABlock,
        exit_addr: u64,
        edge_known: bool,
    ) -> Option<i64> {
        let mut branches_to_exit = edge_known;
        for op in block.ops.iter().rev() {
            match op {
                SSAOp::Branch { target } => {
                    if self.extract_branch_target_address(target) == Some(exit_addr) {
                        branches_to_exit = true;
                    }
                }
                SSAOp::CBranch { target, .. } => {
                    if self.extract_branch_target_address(target) == Some(exit_addr) {
                        branches_to_exit = true;
                    }
                }
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr,
                    ..
                } => {
                    if branches_to_exit || self.is_current_return_context_candidate(block.addr) {
                        let offset = self.stack_slot_offset_for_var(addr);
                        if offset.is_some() {
                            return offset;
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn seed_copy_is_overwritten_by_control_epilogue_load(
        &self,
        block: &SSABlock,
        op_idx: usize,
        dst: &SSAVar,
    ) -> bool {
        let same_storage =
            |lhs: &SSAVar, rhs: &SSAVar| lhs.name == rhs.name && lhs.size == rhs.size;
        for (later_idx, later_op) in block.ops.iter().enumerate().skip(op_idx + 1) {
            if later_op.sources().iter().any(|src| same_storage(src, dst)) {
                return false;
            }
            let Some(later_dst) = later_op.dst() else {
                continue;
            };
            if !same_storage(later_dst, dst) {
                continue;
            }
            return matches!(
                later_op,
                SSAOp::Load {
                    dst: load_dst,
                    space: r2il::SpaceId::Ram,
                    ..
                }
                    if self.load_is_control_epilogue_artifact(block, later_idx, load_dst)
            );
        }
        false
    }

    fn return_stack_slot_loaded_before_control_return(&self, block: &SSABlock) -> Option<i64> {
        let mut loaded_slots = HashSet::new();
        let mut saw_control_return = false;

        for (op_idx, op) in block.ops.iter().enumerate() {
            match op {
                SSAOp::Load {
                    dst,
                    space: r2il::SpaceId::Ram,
                    addr,
                } => {
                    if self.is_control_return_target(dst)
                        || self.load_is_control_epilogue_artifact(block, op_idx, dst)
                    {
                        continue;
                    }
                    if let Some(offset) = self.stack_slot_offset_for_var(addr) {
                        loaded_slots.insert(offset);
                    }
                }
                SSAOp::Return { target } => {
                    if !self.is_control_return_target(target) {
                        return None;
                    }
                    saw_control_return = true;
                }
                SSAOp::Copy { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::IntSExt { .. }
                | SSAOp::Trunc { .. }
                | SSAOp::Cast { .. }
                | SSAOp::IntAdd { .. }
                | SSAOp::IntCarry { .. }
                | SSAOp::IntSCarry { .. }
                | SSAOp::IntSLess { .. }
                | SSAOp::IntEqual { .. } => {}
                _ => return None,
            }
        }

        if !saw_control_return || loaded_slots.len() != 1 {
            return None;
        }

        loaded_slots.into_iter().next()
    }

    fn load_is_control_epilogue_artifact(
        &self,
        block: &SSABlock,
        load_idx: usize,
        loaded_dst: &SSAVar,
    ) -> bool {
        let mut saw_use = false;
        for op in block.ops.iter().skip(load_idx + 1) {
            let uses_dst = op.sources().contains(&loaded_dst);
            if !uses_dst {
                continue;
            }
            saw_use = true;
            match op {
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Trunc { dst, src }
                | SSAOp::Cast { dst, src }
                    if src == loaded_dst =>
                {
                    let lower = dst.name.to_ascii_lowercase();
                    if self.is_control_return_target(dst)
                        || self.inputs.arch.is_stack_pointer_name(&lower)
                        || self.inputs.arch.is_frame_pointer_name(&lower)
                    {
                        continue;
                    }
                    return false;
                }
                _ => return false,
            }
        }

        saw_use
    }

    fn stack_slot_offset_for_var(&self, var: &SSAVar) -> Option<i64> {
        self.stack_slot_provenance_for_var(var)
            .map(|slot| slot.offset)
            .or_else(|| self.prepared_stack_offset_for_var(var))
            .or_else(|| {
                analysis::utils::extract_stack_offset_from_var(
                    var,
                    self.definitions_map(),
                    &self.inputs.arch.fp_name,
                    &self.inputs.arch.sp_name,
                )
            })
    }

    fn resolve_copy_root_name_in_fold(&self, name: &str) -> String {
        let mut current = name.to_string();
        let mut seen = HashSet::new();
        while seen.insert(current.clone()) {
            let Some(next) = self.render_copy_source_for_name(&current) else {
                break;
            };
            current = next;
        }
        current
    }

    fn register_family_name_for_ssa(&self, var: &SSAVar) -> Option<String> {
        register_family_name(&var.name).or_else(|| {
            let root = self.resolve_copy_root_name_in_fold(&var.display_name());
            (root != var.display_name())
                .then_some(root)
                .and_then(|root| register_family_name(&root))
        })
    }

    fn same_storage_value(&self, a: &SSAVar, b: &SSAVar) -> bool {
        a == b
            || (a.version == b.version
                && self
                    .register_family_name_for_ssa(a)
                    .zip(self.register_family_name_for_ssa(b))
                    .is_some_and(|(lhs, rhs)| lhs == rhs))
    }

    fn recent_same_family_return_expr_before(
        &self,
        block: &SSABlock,
        op_idx: usize,
        var: &SSAVar,
    ) -> Option<CExpr> {
        let family = self.register_family_name_for_ssa(var)?;

        for op in block.ops[..op_idx].iter().rev() {
            match op {
                SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::CallOther { .. } => break,
                _ => {}
            }

            let Some(dst) = op.dst() else {
                continue;
            };
            let Some(dst_family) = self.register_family_name_for_ssa(dst) else {
                continue;
            };
            if dst_family != family {
                continue;
            }

            let candidate = match op {
                SSAOp::Copy { src, .. } => self.get_return_expr(src),
                SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Trunc { dst, src }
                | SSAOp::Cast { dst, src } => {
                    self.tracked_return_cast_expr(dst, src, self.get_return_expr(src))
                }
                _ => {
                    let mut visited = HashSet::new();
                    let raw = self.op_to_expr(op);
                    let expanded = self.expand_return_expr(&raw, 0, &mut visited);
                    let mut semantic_visited = HashSet::new();
                    let semanticized =
                        self.semanticize_visible_expr(&expanded, 0, &mut semantic_visited);
                    if self.is_predicate_like_expr(&semanticized) {
                        self.simplify_condition_expr(semanticized)
                    } else {
                        semanticized
                    }
                }
            };

            if self.is_low_level_return_artifact(&candidate)
                || self.is_uninitialized_return_reg(&candidate)
                || self.expr_is_transient_return_artifact(&candidate)
            {
                continue;
            }

            return Some(self.resolve_return_candidate(&candidate));
        }

        None
    }

    fn expr_is_generic_entry_arg_like(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                name.eq_ignore_ascii_case("argc")
                    || name.eq_ignore_ascii_case("argv")
                    || name.eq_ignore_ascii_case("envp")
                    || is_generic_arg_name(name)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.expr_is_generic_entry_arg_like(inner)
            }
            _ => false,
        }
    }

    fn should_prefer_recent_same_family_return_expr(&self, recent: &CExpr, direct: &CExpr) -> bool {
        self.expr_is_generic_entry_arg_like(direct)
            && !self.expr_is_generic_entry_arg_like(recent)
            && (self.is_direct_constish_visible_expr(recent, 0)
                || !self.is_direct_constish_visible_expr(direct, 0))
    }

    fn is_current_return_context_candidate(&self, addr: u64) -> bool {
        self.state.return_blocks.contains(&addr)
    }

    /// Extract address from a branch target variable.
    fn extract_branch_target_address(&self, target: &SSAVar) -> Option<u64> {
        crate::address::parse_address_from_var_name(&target.name)
    }

    /// Check if the current block is a return block.
    fn is_current_return_block(&self) -> bool {
        if let Some(addr) = self.current_block_addr.get() {
            return self.state.return_blocks.contains(&addr);
        }
        false
    }

    /// Analyze a block to collect use counts and definitions.
    #[cfg(test)]
    pub(crate) fn analyze_block(&mut self, block: &SSABlock) {
        self.analyze_blocks(std::slice::from_ref(block));
    }

    /// Analyze multiple blocks (for function-level folding).
    #[cfg(test)]
    pub(crate) fn analyze_blocks(&mut self, blocks: &[SSABlock]) {
        let execution = r2ssa::SsaExecutionControl::default();
        let control =
            crate::DecompileWorkControl::new(&execution, crate::DecompileWorkPhase::Structuring);
        self.analyze_blocks_with_control(blocks, control)
            .expect("default decompiler work control cannot stop");
    }

    pub(crate) fn analyze_blocks_with_control(
        &mut self,
        blocks: &[SSABlock],
        control: crate::DecompileWorkControl<'_>,
    ) -> Result<(), crate::DecompileExecutionStop> {
        control.poll()?;
        if let Some(prepared) = self.inputs.prepared_ssa {
            self.state.analysis_ctx.semantic_mut().type_hints = self.inputs.type_hints.clone();
            let env = self.to_pass_env();
            let prepared_view = self.prepared_semantic_view().cloned().unwrap_or_else(|| {
                analysis::PreparedSemanticView::build(analysis::PreparedSemanticViewInputs {
                    prepared,
                    abi_arg_regs: &self.inputs.arch.arg_regs,
                    stack_slots: self.inputs.stack_slots,
                    visible_bindings: self.inputs.visible_bindings,
                    param_register_aliases: self.inputs.param_register_aliases,
                    function_facts: self.inputs.function_facts,
                    #[cfg(test)]
                    certified_rendering_required: self.requires_certified_rendering(),
                })
            });
            self.state.analysis_ctx = analysis::build_prepared_runtime_facts_with_control(
                blocks,
                &env,
                prepared,
                &prepared_view,
                control,
            )?;
            self.state.analysis_ctx.ownership = self.build_semantic_ownership_facts();
            self.clear_semantic_ownership_caches();
            return Ok(());
        }

        // Explicit pass order:
        // 1) UseInfo
        // 2) FlagInfo + StackInfo
        // 3) Predicate simplification/statement emit consume analysis state
        self.state.analysis_ctx.semantic_mut().type_hints = self.inputs.type_hints.clone();
        let env = self.to_pass_env();
        let mut use_info = analysis::UseInfo::analyze_with_control(blocks, &env, control)?;
        let authoritative_use_info = use_info.clone();
        let mut stack_info = analysis::StackInfo::analyze(blocks, &use_info, &env);
        let initial_stack_info = stack_info.clone();

        for (slot_key, ext_var) in self.inputs.stack_slots {
            if ext_var.name.is_empty() || !is_visible_external_stack_name_role(ext_var.role) {
                continue;
            }
            if self.is_reserved_param_alias_name(&ext_var.name) {
                continue;
            }
            for candidate_offset in [slot_key.offset, -slot_key.offset] {
                if candidate_offset != slot_key.offset
                    && !matches!(slot_key.base, ExternalStackBase::FramePointer)
                {
                    continue;
                }
                let should_replace = match stack_info.stack_vars.get(&candidate_offset) {
                    None => true,
                    Some(existing) => {
                        existing.starts_with("local_")
                            || existing.starts_with("stack_")
                            || existing.starts_with("arg_")
                            || existing == "saved_fp"
                            || is_generic_arg_name(existing)
                    }
                };
                if should_replace {
                    stack_info
                        .stack_vars
                        .insert(candidate_offset, ext_var.name.clone());
                }
            }
        }

        if !stack_info.definition_overrides.is_empty() {
            use_info = analysis::UseInfo::analyze_with_definition_overrides_with_control(
                blocks,
                &env,
                &stack_info.definition_overrides,
                control,
            )?;
            use_info.preserve_authoritative_facts_from(&authoritative_use_info);
            stack_info = analysis::StackInfo::analyze(blocks, &use_info, &env);
            for (offset, alias) in &initial_stack_info.stack_arg_aliases {
                stack_info.stack_arg_aliases.insert(*offset, alias.clone());
                let should_replace = match stack_info.stack_vars.get(offset) {
                    None => true,
                    Some(existing) => should_replace_preserved_stack_alias(existing),
                };
                if should_replace && !self.is_reserved_param_alias_name(alias) {
                    stack_info.stack_vars.insert(*offset, alias.clone());
                }
            }
            for (key, expr) in &initial_stack_info.definition_overrides {
                let should_replace = match stack_info.definition_overrides.get(key) {
                    None => true,
                    Some(existing) => should_replace_preserved_stack_expr(existing, expr),
                };
                if should_replace {
                    stack_info
                        .definition_overrides
                        .insert(key.clone(), expr.clone());
                }
            }
            normalize_stack_definition_overrides(&mut stack_info);
            for (slot_key, ext_var) in self.inputs.stack_slots {
                if ext_var.name.is_empty() || !is_visible_external_stack_name_role(ext_var.role) {
                    continue;
                }
                if self.is_reserved_param_alias_name(&ext_var.name) {
                    continue;
                }
                for candidate_offset in [slot_key.offset, -slot_key.offset] {
                    if candidate_offset != slot_key.offset
                        && !matches!(slot_key.base, ExternalStackBase::FramePointer)
                    {
                        continue;
                    }
                    let should_replace = match stack_info.stack_vars.get(&candidate_offset) {
                        None => true,
                        Some(existing) => {
                            existing.starts_with("local_")
                                || existing.starts_with("stack_")
                                || existing.starts_with("arg_")
                                || existing == "saved_fp"
                                || is_generic_arg_name(existing)
                        }
                    };
                    if should_replace {
                        stack_info
                            .stack_vars
                            .insert(candidate_offset, ext_var.name.clone());
                    }
                }
            }
            use_info = analysis::UseInfo::analyze_with_definition_overrides_with_control(
                blocks,
                &env,
                &stack_info.definition_overrides,
                control,
            )?;
            use_info.preserve_authoritative_facts_from(&authoritative_use_info);
        }
        let flag_info = analysis::FlagInfo::analyze(blocks, &use_info, &env);
        self.state.analysis_ctx = analysis::DecompilerFacts {
            use_info,
            ownership: analysis::SemanticOwnershipFacts::default(),
            flag_info,
            stack_info,
        };
        self.state.analysis_ctx.ownership = self.build_semantic_ownership_facts();
        self.clear_semantic_ownership_caches();
        control.poll()?;
        Ok(())
    }

    fn clear_semantic_ownership_caches(&self) {
        self.call_result_owner_name_cache.borrow_mut().clear();
        *self.owned_call_visible_names_cache.borrow_mut() = None;
    }

    fn build_semantic_ownership_facts(&self) -> analysis::SemanticOwnershipFacts {
        let mut facts = analysis::SemanticOwnershipFacts::default();
        let call_sources = self
            .call_result_aliases_map()
            .iter()
            .map(|(source_call, aliases)| (*source_call, aliases.clone()))
            .collect::<Vec<_>>();

        for (source_call, aliases) in call_sources {
            let source_id = analysis::CallSiteId::from(source_call);
            let mut direct_aliases = BTreeSet::new();

            for alias in &aliases {
                facts.alias_sources.insert(alias.clone(), source_id);
                facts
                    .alias_sources
                    .insert(alias.to_ascii_lowercase(), source_id);
                if self.direct_call_result_aliases_set().contains(alias) {
                    direct_aliases.insert(alias.clone());
                }
            }

            let prepared_owner = self
                .prepared_semantic_view()
                .and_then(|view| view.call_view_for_site(source_call))
                .and_then(|view| view.result_owner.as_ref())
                .and_then(Self::prepared_owned_result_name)
                .filter(|name| {
                    !is_generic_arg_name(name) && !self.inputs.arch.is_return_register_name(name)
                });
            let dynamic_owner = self
                .derive_stable_owned_call_result_name_for_source(aliases.iter())
                .filter(|name| !self.call_result_owner_candidate_is_stack_storage(name));
            let owner = prepared_owner.or(dynamic_owner).map(|visible_name| {
                let kind = self.classify_call_owner_kind(&visible_name);
                facts
                    .visible_owner_sources
                    .insert(visible_name.clone(), source_id);
                facts
                    .visible_owner_sources
                    .insert(visible_name.to_ascii_lowercase(), source_id);
                facts
                    .visible_owned_names
                    .insert(visible_name.to_ascii_lowercase());
                analysis::CallOwner { visible_name, kind }
            });

            facts.call_ownership.insert(
                source_id,
                analysis::CallOwnershipFact {
                    source: source_id,
                    owner,
                    aliases,
                    direct_aliases,
                },
            );
        }

        facts
    }

    fn classify_call_owner_kind(&self, visible_name: &str) -> analysis::CallOwnerKind {
        if self.is_generic_stack_local_owner_name(visible_name)
            || self
                .stack_offset_for_visible_storage_name(visible_name)
                .is_some_and(|offset| offset < 0)
        {
            analysis::CallOwnerKind::StableStackLocal
        } else if self
            .inputs
            .param_register_aliases
            .values()
            .any(|alias| alias.eq_ignore_ascii_case(visible_name))
            || self
                .stack_arg_aliases_map()
                .values()
                .any(|alias| alias.eq_ignore_ascii_case(visible_name))
        {
            analysis::CallOwnerKind::Parameter
        } else {
            analysis::CallOwnerKind::StableLocal
        }
    }

    fn recovered_owned_call_result_definition_rhs_for_visible_name(
        &self,
        visible_name: &str,
    ) -> Option<CExpr> {
        let source_call = self.source_call_for_visible_owner_name(visible_name)?;

        self.call_result_exprs_map()
            .get(&source_call)
            .cloned()
            .map(|expr| {
                self.normalize_call_expr_for_source_call(
                    source_call,
                    expr,
                    FinalExprNormalizeContext::DefinitionRoot,
                )
            })
            .or_else(|| {
                self.call_result_aliases_map()
                    .get(&source_call)
                    .into_iter()
                    .flat_map(|aliases| aliases.iter())
                    .find_map(|alias| {
                        self.direct_definition_expr(alias)
                            .or_else(|| self.lookup_definition_raw(alias))
                            .filter(|expr| matches!(expr, CExpr::Call { .. }))
                            .map(|expr| {
                                self.normalize_call_expr_for_source_call(
                                    source_call,
                                    expr,
                                    FinalExprNormalizeContext::DefinitionRoot,
                                )
                            })
                    })
            })
            .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
    }

    fn source_call_for_visible_owner_name(&self, visible_name: &str) -> Option<(u64, usize)> {
        self.ownership()
            .source_for_visible_owner_name(visible_name)
            .map(Into::into)
            .or_else(|| {
                self.ownership().call_ownership.values().find_map(|fact| {
                    fact.owner
                        .as_ref()
                        .is_some_and(|owner| owner.visible_name.eq_ignore_ascii_case(visible_name))
                        .then_some(fact.source.into())
                })
            })
            .or_else(|| {
                self.stack_offset_for_visible_storage_name(visible_name)
                    .and_then(|wanted_offset| {
                        self.ownership()
                            .call_ownership
                            .values()
                            .find_map(|fact| {
                                let owner = fact.owner.as_ref()?;
                                self.visible_names_share_stack_slot(
                                    &owner.visible_name,
                                    visible_name,
                                )
                                .then_some((wanted_offset, fact.source))
                            })
                            .map(|(_, source)| source.into())
                    })
            })
    }

    pub(super) fn synthesized_call_expr_for_source_call(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        self.certified_synthesized_call_expr_for_source_call(source_call)
            .map(|call| call.expr)
    }

    pub(super) fn certified_synthesized_call_expr_for_source_call(
        &self,
        source_call: (u64, usize),
    ) -> Option<CertifiedCallExpr> {
        let (block_addr, op_idx) = source_call;
        let cert = self.certified_callsite_for_op(block_addr, op_idx)?;
        let render_fact = self.certified_call_render_fact_for_op(block_addr, op_idx)?;
        if matches!(
            render_fact.disposition,
            r2types::CallsiteRenderDisposition::Suppressed
                | r2types::CallsiteRenderDisposition::Residualized
        ) {
            return None;
        }
        let proof = self.certified_render_context()?;
        let target_is_certified =
            proof.expression_is_renderable(cert.target) || cert.direct_target.is_some();
        if !target_is_certified {
            return None;
        }
        let func = self.resolve_call_target_for_site(
            block_addr,
            op_idx,
            self.prepared_var_for_value_id(cert.target)?,
        );
        let raw_args = self
            .call_args_map()
            .get(&source_call)
            .cloned()
            .unwrap_or_default();
        let certified_args =
            self.certified_call_args_for_site(block_addr, op_idx, &func, raw_args)?;
        let func = self
            .resolved_callee_identity_expr_for_site(block_addr, op_idx)
            .unwrap_or(func);
        let expr = CExpr::call(func, certified_args.args);
        Some(CertifiedCallExpr {
            expr,
            target: cert.target,
            values: certified_args.values,
        })
    }

    pub(crate) fn record_certified_call_render_proofs_for_stmt(&self, stmt: &CStmt) -> Option<()> {
        self.record_certified_call_render_proofs_for_stmt_with_current(stmt, None)
    }

    pub(super) fn record_certified_call_render_proofs_for_stmt_with_current(
        &self,
        stmt: &CStmt,
        current_source_call: Option<(u64, usize)>,
    ) -> Option<()> {
        return Some(());

        let mut sources = BTreeSet::new();
        self.collect_certified_rendered_call_sources_for_stmt(
            stmt,
            current_source_call,
            &mut sources,
        )?;
        let proofs = sources
            .into_iter()
            .map(|source_call| {
                self.certified_synthesized_call_expr_for_source_call(source_call)
                    .map(|call| (source_call, call.target, call.values))
            })
            .collect::<Option<Vec<_>>>()?;

        for ((block_addr, op_idx), target, values) in proofs {
            self.record_call_effect_render_proof(
                block_addr,
                op_idx,
                Some(target),
                values.clone(),
                r2types::CallsiteRenderDisposition::NestedExpression,
            );
            self.record_certified_call_arg_memory_render_proofs(&values);
        }
        Some(())
    }

    #[cfg(test)]
    pub(super) fn record_certified_call_render_proof_for_source_call(
        &self,
        source_call: (u64, usize),
    ) -> Option<()> {
        return Some(());

        let call = self.certified_synthesized_call_expr_for_source_call(source_call)?;
        self.record_call_effect_render_proof(
            source_call.0,
            source_call.1,
            Some(call.target),
            call.values.clone(),
            r2types::CallsiteRenderDisposition::NestedExpression,
        );
        self.record_certified_call_arg_memory_render_proofs(&call.values);
        Some(())
    }

    fn collect_certified_rendered_call_sources_for_stmt(
        &self,
        stmt: &CStmt,
        current_source_call: Option<(u64, usize)>,
        out: &mut BTreeSet<(u64, usize)>,
    ) -> Option<()> {
        match stmt {
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => self
                .collect_certified_rendered_call_sources_for_expr(expr, current_source_call, out),
            CStmt::While { cond, body } => {
                self.collect_certified_rendered_call_sources_for_expr(
                    cond,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_stmt(
                    body,
                    current_source_call,
                    out,
                )
            }
            CStmt::DoWhile { body, cond } => {
                self.collect_certified_rendered_call_sources_for_stmt(
                    body,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_expr(
                    cond,
                    current_source_call,
                    out,
                )
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    self.collect_certified_rendered_call_sources_for_stmt(
                        stmt,
                        current_source_call,
                        out,
                    )?;
                }
                Some(())
            }
            CStmt::Decl {
                init: Some(expr), ..
            } => self.collect_certified_rendered_call_sources_for_expr(
                expr,
                current_source_call,
                out,
            ),
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.collect_certified_rendered_call_sources_for_expr(
                    cond,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_stmt(
                    then_body,
                    current_source_call,
                    out,
                )?;
                if let Some(else_body) = else_body {
                    self.collect_certified_rendered_call_sources_for_stmt(
                        else_body,
                        current_source_call,
                        out,
                    )?;
                }
                Some(())
            }
            CStmt::For {
                cond: Some(expr),
                update: Some(update),
                body,
                ..
            } => {
                self.collect_certified_rendered_call_sources_for_expr(
                    expr,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_expr(
                    update,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_stmt(
                    body,
                    current_source_call,
                    out,
                )
            }
            CStmt::For {
                cond: Some(expr),
                body,
                update: None,
                ..
            } => {
                self.collect_certified_rendered_call_sources_for_expr(
                    expr,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_stmt(
                    body,
                    current_source_call,
                    out,
                )
            }
            CStmt::For {
                cond: None,
                update: Some(expr),
                body,
                ..
            } => {
                self.collect_certified_rendered_call_sources_for_expr(
                    expr,
                    current_source_call,
                    out,
                )?;
                self.collect_certified_rendered_call_sources_for_stmt(
                    body,
                    current_source_call,
                    out,
                )
            }
            CStmt::For {
                cond: None,
                update: None,
                body,
                ..
            } => self.collect_certified_rendered_call_sources_for_stmt(
                body,
                current_source_call,
                out,
            ),
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                self.collect_certified_rendered_call_sources_for_expr(
                    expr,
                    current_source_call,
                    out,
                )?;
                for case in cases {
                    self.collect_certified_rendered_call_sources_for_expr(
                        &case.value,
                        current_source_call,
                        out,
                    )?;
                    for stmt in &case.body {
                        self.collect_certified_rendered_call_sources_for_stmt(
                            stmt,
                            current_source_call,
                            out,
                        )?;
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        self.collect_certified_rendered_call_sources_for_stmt(
                            stmt,
                            current_source_call,
                            out,
                        )?;
                    }
                }
                Some(())
            }
            CStmt::Return(None)
            | CStmt::Decl { init: None, .. }
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_)
            | CStmt::Empty => Some(()),
        }
    }

    fn collect_certified_rendered_call_sources_for_expr(
        &self,
        expr: &CExpr,
        current_source_call: Option<(u64, usize)>,
        out: &mut BTreeSet<(u64, usize)>,
    ) -> Option<()> {
        if matches!(expr, CExpr::Call { .. }) {
            let source_call =
                self.certified_source_for_rendered_call_expr(expr, current_source_call)?;
            out.insert(source_call);
        }
        let mut certified = true;
        expr.visit(&mut |node| {
            if let CExpr::Call { .. } = node {
                if let Some(source_call) =
                    self.certified_source_for_rendered_call_expr(node, current_source_call)
                {
                    out.insert(source_call);
                } else {
                    certified = false;
                }
            }
        });
        certified.then_some(())
    }

    fn should_inline(&self, var: &SSAVar) -> bool {
        let var_name = var.display_name();
        let use_count = self.use_counts_map().get(&var_name).copied().unwrap_or(0);

        if use_count == 0 || use_count > 3 {
            return false;
        }

        if self
            .call_result_source_for_ssa_name(&var_name)
            .or_else(|| self.local_post_call_source_for_ssa_name(&var_name))
            .or_else(|| self.source_call_for_visible_owner_name(&self.var_name(var)))
            .and_then(|source| self.stable_owned_call_result_name_for_source(source))
            .is_some()
        {
            return false;
        }

        if self.pinned_set().contains(&var_name) {
            return false;
        }

        if self.condition_vars_set().contains(&var_name)
            && !self.is_condition_inline_candidate(&var_name)
        {
            return false;
        }

        // Values that only feed flag computation should always disappear.
        if self.flag_only_values_set().contains(&var_name) {
            return true;
        }

        // After the zero/>3 guard above, any non-1 count is multi-use.
        if use_count != 1 && !self.is_simple_inline_candidate(&var_name) {
            return false;
        }

        // Inline single-use or trivially small values after preserving
        // structural return/stack registers.
        {
            let base_lower = var.name.to_lowercase();
            // Don't inline return register assignments in return blocks
            if self.inputs.arch.is_return_register_name(&base_lower)
                && self.is_current_return_block()
            {
                return false;
            }
            // Don't inline stack/frame pointer versions - they're structural
            if self.inputs.arch.is_stack_base_name(&base_lower) {
                return false;
            }
            // Inline calling-convention argument registers (consumed by call args)
            if self.inputs.arch.is_caller_saved_name(&base_lower) {
                return true;
            }
            // Inline any register with a definition when it is single-use
            // or the definition is trivially small.
            if use_count == 1 || self.is_simple_inline_candidate(&var_name) {
                return true;
            }
        }

        false
    }

    fn is_condition_inline_candidate(&self, var_name: &str) -> bool {
        if self.flag_only_values_set().contains(var_name) {
            return true;
        }

        if is_cpu_flag(&var_name.to_lowercase()) {
            return true;
        }

        self.is_simple_inline_candidate(var_name)
    }

    fn is_simple_inline_candidate(&self, var_name: &str) -> bool {
        self.definition_for_name(var_name)
            .map(|expr| self.is_simple_expr(expr, 0))
            .unwrap_or(false)
    }

    fn is_simple_expr(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > MAX_SIMPLE_EXPR_DEPTH {
            return false;
        }

        match expr {
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_) => true,
            CExpr::Var(name) => {
                if is_cpu_flag(&name.to_lowercase()) {
                    return true;
                }
                self.definition_for_name(name)
                    .map(|inner| self.is_simple_expr(inner, depth + 1))
                    .unwrap_or(true)
            }
            CExpr::Cast { expr, .. } | CExpr::Paren(expr) => self.is_simple_expr(expr, depth + 1),
            CExpr::Unary { operand, .. } => self.is_simple_expr(operand, depth + 1),
            CExpr::Binary { op, left, right } => {
                matches!(
                    op,
                    BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::BitAnd
                        | BinaryOp::BitOr
                        | BinaryOp::BitXor
                        | BinaryOp::And
                        | BinaryOp::Or
                ) && self.is_simple_expr(left, depth + 1)
                    && self.is_simple_expr(right, depth + 1)
            }
            _ => false,
        }
    }

    /// Check if a variable is dead (never used).
    pub fn is_dead(&self, var: &SSAVar) -> bool {
        let key = var.display_name();
        let use_count = self.use_counts_map().get(&key).copied().unwrap_or(0);
        let lower = var.name.to_lowercase();

        // Flag registers are rendering artifacts; keep them out of emitted code.
        if is_cpu_flag(&lower) {
            return true;
        }

        // Helpers used only to feed flags are also dead in final output.
        if self.flag_only_values_set().contains(&key) {
            return true;
        }

        if self.pinned_set().contains(&key) || self.pinned_set().contains(&key.to_ascii_lowercase())
        {
            return false;
        }

        if use_count > 0 {
            return false;
        }

        // Temporaries and reg: prefixed vars are always dead if unused
        if var.is_temp()
            || var.is_const()
            || matches!(var.name_kind(), SSAVarNameKind::RegisterAlias)
        {
            return true;
        }

        // Caller-saved / calling-convention registers are dead if unused
        // (their values don't survive across calls anyway)
        if self.inputs.arch.is_caller_saved_name(&lower) {
            return true;
        }

        if lower.starts_with('q') && lower.chars().nth(1).is_some_and(|ch| ch.is_ascii_digit()) {
            return true;
        }

        // Variables consumed by call argument collection are dead
        if self.consumed_by_call_set().contains(&key) {
            return true;
        }

        // Stack/frame pointer intermediate versions are dead if unused
        if self.inputs.arch.is_stack_base_name(&lower) {
            return true;
        }

        // Eliminate explicit zeroing idioms when the value is never used
        // beyond setup/flag chains (e.g., eax = eax ^ eax).
        if let Some(expr) = self.definition_for_name(&key)
            && self.is_zeroing_expr(expr)
        {
            return true;
        }

        // Keep other named registers alive (e.g., callee-saved like rbx, r12-r15)
        // as they might be meaningful outputs
        false
    }

    /// Get the expression for a variable, potentially inlining its definition.
    pub fn get_expr(&self, var: &SSAVar) -> CExpr {
        let key = var.display_name();

        // Always inline constants
        if var.is_const() {
            return self.const_to_expr(var);
        }

        let fallback = CExpr::Var(self.var_name(var));
        if let Some(expr) = self.signed_divrem_expr_for_value(var) {
            return expr;
        }
        let producer_load_expr = self.use_info().producers.get(&key).and_then(|op| match op {
            SSAOp::Load {
                dst,
                space: r2il::SpaceId::Ram,
                addr,
            } if dst.size < addr.size => {
                let elem_ty = self
                    .type_hint_for_var(dst)
                    .unwrap_or_else(|| type_from_size(dst.size));
                let expr = self.render_canonical_load_expr(dst, addr, elem_ty);
                (Self::expr_is_scalar_memory_candidate(&expr)
                    || Self::expr_is_structured_memory_candidate(&expr))
                .then_some(expr)
            }
            _ => None,
        });
        if let Some(load_expr) = producer_load_expr {
            return load_expr;
        }
        let raw_memory_expr = self.lookup_definition_raw(&key).and_then(|raw| {
            let mut raw_semantic_visited = HashSet::new();
            let semanticized = self.semanticize_visible_expr(&raw, 0, &mut raw_semantic_visited);
            (Self::expr_is_scalar_memory_candidate(&semanticized)
                || Self::expr_is_structured_memory_candidate(&semanticized))
            .then_some(semanticized)
        });
        if let Some(offset) = self
            .forwarded_value_for_name(&key)
            .and_then(|prov| prov.stack_slot)
            && let Some(alias) = self.stack_arg_aliases_map().get(&offset)
            && !alias.trim().is_empty()
        {
            return CExpr::Var(alias.clone());
        }
        if let Some(slot) = self.stack_slot_provenance_for_name(&key)
            && slot.offset < 0
            && let Some(name) = self.resolve_stack_var(slot.offset)
            && !is_generic_stack_placeholder_alias(&name)
            && !self.is_transient_visible_name(&name)
            && !self.is_low_signal_visible_name(&name)
        {
            return CExpr::Var(name);
        }
        if let Some(owner) = self.stable_owned_call_result_expr_for_name(&key, true) {
            return owner;
        }
        if let Some(owner) = self.preserved_owned_call_result_var_for_name(&key) {
            return owner;
        }
        if (self.is_low_signal_visible_name(&self.var_name(var))
            || self.is_transient_visible_name(&self.var_name(var)))
            && let Some(candidate) = self.lookup_definition_with_depth(&key, 0, &mut HashSet::new())
        {
            let candidate = self.rewrite_stack_expr(candidate);
            if self.prefers_visible_expr(&fallback, &candidate) {
                return candidate;
            }
        }
        if matches!(
            self.lookup_semantic_value(&key),
            Some(analysis::SemanticValue::Address(_))
        ) && let Some(candidate) =
            self.lookup_definition_with_depth(&key, 0, &mut HashSet::new())
        {
            let candidate = self.rewrite_stack_expr(candidate);
            if !matches!(candidate, CExpr::AddrOf(_))
                && self.prefers_visible_expr(&fallback, &candidate)
            {
                return candidate;
            }
        }
        let mut semantic_visited = HashSet::new();
        if let Some(semantic) = self.render_semantic_value_by_name(&key, 0, &mut semantic_visited) {
            if let Some(raw_memory) = raw_memory_expr.clone()
                && !Self::expr_is_scalar_memory_candidate(&semantic)
                && !Self::expr_is_structured_memory_candidate(&semantic)
            {
                return raw_memory;
            }
            if self.prefers_visible_expr(&fallback, &semantic) {
                return semantic;
            }
        }
        if let Some(raw_memory) = raw_memory_expr {
            return raw_memory;
        }

        // Try to inline if appropriate
        if self.should_inline(var)
            && let Some(expr) = self.definition_for_name(&key)
        {
            return expr.clone();
        }

        // Otherwise return a variable reference
        fallback
    }

    fn certified_expr_depends_on_semantic_array(
        &self,
        value: r2ssa::ValueId,
        visited: &mut BTreeSet<r2ssa::ValueId>,
    ) -> bool {
        if !visited.insert(value) {
            return false;
        }
        let Some(render) = self.inputs.render_facts() else {
            return false;
        };
        let has_exact_array_load = render
            .memory_accesses()
            .filter(|memory| !memory.is_write && memory.value == Some(value))
            .any(|memory| {
                render
                    .array_accesses_by_op
                    .get(&(memory.block_addr, memory.op_index, false))
                    .into_iter()
                    .flatten()
                    .any(|array| {
                        array.access == memory.access
                            && array.object == memory.object
                            && array.access_width == memory.width
                            && array.base.is_some()
                            && array.index.is_some()
                    })
            });
        if has_exact_array_load {
            return true;
        }
        render.certified_expr_for_value(value).is_some_and(|expr| {
            expr.inputs.iter().any(|input| match input {
                r2ssa::SemanticId::Expression(input) => {
                    self.certified_expr_depends_on_semantic_array(*input, visited)
                }
                _ => false,
            })
        })
    }

    fn op_to_expr_impl(&self, op: &SSAOp) -> CExpr {
        if let SSAOp::Copy { src, .. } = op {
            return self.get_expr(src);
        }

        if let Some(stmt) = self.op_to_stmt_impl(op) {
            return match Self::lowered_from_stmt(stmt) {
                LoweredOp::Assign { rhs, .. } => rhs,
                LoweredOp::Expr(expr) => expr,
                LoweredOp::Return(Some(expr)) => expr,
                LoweredOp::Return(None) => CExpr::Var("return".to_string()),
                LoweredOp::Comment(_) | LoweredOp::None => {
                    if let Some(dst) = op.dst() {
                        CExpr::Var(self.var_name(dst))
                    } else {
                        CExpr::Var("__unhandled_op__".to_string())
                    }
                }
            };
        }

        match op {
            // These ops do not lower to statements but still need expression form.
            SSAOp::CBranch { cond, .. } => self.get_condition_expr(cond),
            SSAOp::Return { target } => self.get_return_expr(target),
            _ => {
                if let Some(dst) = op.dst() {
                    CExpr::Var(self.var_name(dst))
                } else {
                    CExpr::Var("__unhandled_op__".to_string())
                }
            }
        }
    }

    /// Create a binary expression.
    #[allow(dead_code)]
    fn binary_expr(&self, op: BinaryOp, a: &SSAVar, b: &SSAVar) -> CExpr {
        let width_bytes = if a.size > 0 && a.size == b.size {
            Some(a.size)
        } else {
            None
        };
        self.identity_simplify_binary(op, self.get_expr(a), self.get_expr(b), width_bytes)
    }

    fn is_literal_zero_expr(&self, expr: &CExpr) -> bool {
        matches!(expr, CExpr::IntLit(0) | CExpr::UIntLit(0))
    }

    fn is_one_expr(&self, expr: &CExpr) -> bool {
        matches!(expr, CExpr::IntLit(1) | CExpr::UIntLit(1))
    }

    fn is_all_ones_mask_expr(&self, expr: &CExpr, width_bytes: u32) -> bool {
        if width_bytes == 0 || width_bytes > 8 {
            return false;
        }
        let bits = width_bytes.saturating_mul(8);
        let mask = if bits == 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };

        match expr {
            CExpr::UIntLit(v) => *v == mask,
            CExpr::IntLit(v) => *v == -1 || u64::try_from(*v).map(|n| n == mask).unwrap_or(false),
            CExpr::Paren(inner) => self.is_all_ones_mask_expr(inner, width_bytes),
            CExpr::Cast { expr: inner, .. } => self.is_all_ones_mask_expr(inner, width_bytes),
            _ => false,
        }
    }

    fn identity_simplify_binary(
        &self,
        op: BinaryOp,
        left: CExpr,
        right: CExpr,
        width_bytes: Option<u32>,
    ) -> CExpr {
        if let Some(value) = self.literal_binary_value(op, &left, &right) {
            return CExpr::IntLit(value);
        }
        match op {
            BinaryOp::Sub if self.is_literal_zero_expr(&right) => left,
            BinaryOp::Sub => {
                if let Some(expr) = self.simplify_linear_subtraction(&left, &right) {
                    expr
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Add => {
                if self.is_literal_zero_expr(&right) {
                    left
                } else if self.is_literal_zero_expr(&left) {
                    right
                } else if let Some(expr) = self.simplify_linear_addition(&left, &right) {
                    expr
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::BitOr | BinaryOp::BitXor => {
                if op == BinaryOp::BitXor && left == right {
                    CExpr::IntLit(0)
                } else if self.is_literal_zero_expr(&right) {
                    left
                } else if self.is_literal_zero_expr(&left) {
                    right
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Mul => {
                if self.is_one_expr(&right) {
                    left
                } else if self.is_one_expr(&left) {
                    right
                } else if let Some(coeff) = self.literal_to_i64(&right)
                    && let Some(expr) = self.simplify_linear_scale(&left, coeff)
                {
                    expr
                } else if let Some(coeff) = self.literal_to_i64(&left)
                    && let Some(expr) = self.simplify_linear_scale(&right, coeff)
                {
                    expr
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Div => {
                if self.is_one_expr(&right) {
                    left
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::BitAnd => {
                if let Some(width) = width_bytes {
                    if self.is_all_ones_mask_expr(&right, width) {
                        return left;
                    }
                    if self.is_all_ones_mask_expr(&left, width) {
                        return right;
                    }
                }
                CExpr::binary(op, left, right)
            }
            BinaryOp::Shl => {
                if self.is_literal_zero_expr(&right) {
                    left
                } else if let Some(shift) = self.literal_to_i64(&right)
                    && (0..=62).contains(&shift)
                    && let Some(expr) = self.simplify_linear_scale(&left, 1i64 << shift)
                {
                    expr
                } else {
                    CExpr::binary(op, left, right)
                }
            }
            BinaryOp::Shr if self.is_literal_zero_expr(&right) => left,
            _ => CExpr::binary(op, left, right),
        }
    }

    fn literal_binary_value(&self, op: BinaryOp, left: &CExpr, right: &CExpr) -> Option<i64> {
        let left = self.literal_to_i64(left)?;
        let right = self.literal_to_i64(right)?;
        match op {
            BinaryOp::Add => left.checked_add(right),
            BinaryOp::Sub => left.checked_sub(right),
            BinaryOp::Mul => left.checked_mul(right),
            BinaryOp::Div => (right != 0).then(|| left.checked_div(right)).flatten(),
            BinaryOp::Mod => (right != 0).then(|| left.checked_rem(right)).flatten(),
            BinaryOp::BitAnd => Some(left & right),
            BinaryOp::BitOr => Some(left | right),
            BinaryOp::BitXor => Some(left ^ right),
            BinaryOp::Shl => {
                if !(0..=62).contains(&right) {
                    return None;
                }
                left.checked_mul(1i64 << right)
            }
            BinaryOp::Shr => {
                if !(0..=62).contains(&right) {
                    return None;
                }
                Some(left >> right)
            }
            _ => None,
        }
    }

    fn simplify_linear_subtraction(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let mut terms = Vec::new();
        let mut constant = 0i64;
        self.collect_linear_add_terms(left, 1, &mut terms, &mut constant)?;
        self.collect_linear_add_terms(right, -1, &mut terms, &mut constant)?;
        self.linear_expr_from_terms(terms, constant)
    }

    fn simplify_linear_scale(&self, expr: &CExpr, scale: i64) -> Option<CExpr> {
        let mut terms = Vec::new();
        let mut constant = 0i64;
        self.collect_linear_add_terms(expr, scale, &mut terms, &mut constant)?;
        self.linear_expr_from_terms(terms, constant)
    }

    fn simplify_linear_addition(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let mut terms = Vec::new();
        let mut constant = 0i64;
        self.collect_linear_add_terms(left, 1, &mut terms, &mut constant)?;
        self.collect_linear_add_terms(right, 1, &mut terms, &mut constant)?;
        self.linear_expr_from_terms(terms, constant)
    }

    fn linear_expr_from_terms(&self, mut terms: Vec<(CExpr, i64)>, constant: i64) -> Option<CExpr> {
        terms.retain(|(_, coeff)| *coeff != 0);
        terms.sort_by_key(|(term, _)| self.linear_term_order_key(term));

        let mut pieces: Vec<CExpr> = terms
            .into_iter()
            .map(|(term, coeff)| linear_coeff_expr(term, coeff))
            .collect::<Option<Vec<_>>>()?;
        if constant != 0 {
            pieces.push(CExpr::IntLit(constant));
        }

        let mut iter = pieces.into_iter();
        let first = iter.next().unwrap_or(CExpr::IntLit(0));
        Some(iter.fold(first, |acc, expr| CExpr::binary(BinaryOp::Add, acc, expr)))
    }

    fn collect_linear_add_terms(
        &self,
        expr: &CExpr,
        scale: i64,
        terms: &mut Vec<(CExpr, i64)>,
        constant: &mut i64,
    ) -> Option<()> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                self.collect_linear_add_terms(left, scale, terms, constant)?;
                self.collect_linear_add_terms(right, scale, terms, constant)
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                self.collect_linear_add_terms(left, scale, terms, constant)?;
                self.collect_linear_add_terms(right, scale.checked_neg()?, terms, constant)
            }
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if let Some(coeff) = self.literal_to_i64(right)
                    && let Some(term) = self.linear_atom_expr(left)
                {
                    return push_linear_term(terms, term, scale.checked_mul(coeff)?);
                }
                if let Some(coeff) = self.literal_to_i64(left)
                    && let Some(term) = self.linear_atom_expr(right)
                {
                    return push_linear_term(terms, term, scale.checked_mul(coeff)?);
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Shl,
                left,
                right,
            } => {
                let shift = self.literal_to_i64(right)?;
                if !(0..=62).contains(&shift) {
                    return None;
                }
                self.collect_linear_add_terms(
                    left,
                    scale.checked_mul(1i64 << shift)?,
                    terms,
                    constant,
                )
            }
            CExpr::IntLit(value) => {
                *constant = constant.checked_add(scale.checked_mul(*value)?)?;
                Some(())
            }
            CExpr::UIntLit(value) => {
                let value = i64::try_from(*value).ok()?;
                *constant = constant.checked_add(scale.checked_mul(value)?)?;
                Some(())
            }
            CExpr::Paren(inner) => self.collect_linear_add_terms(inner, scale, terms, constant),
            _ => {
                let term = self.linear_atom_expr(expr)?;
                push_linear_term(terms, term, scale)
            }
        }
    }

    fn linear_atom_expr(&self, expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::Var(name) if self.linear_var_is_integer_scalar(name) => Some(expr.clone()),
            CExpr::Paren(inner) => self.linear_atom_expr(inner),
            CExpr::Cast { ty, expr: inner }
                if ty.is_integer() && self.linear_atom_expr(inner).is_some() =>
            {
                Some(expr.clone())
            }
            _ => None,
        }
    }

    fn linear_var_is_integer_scalar(&self, name: &str) -> bool {
        if self.expr_mentions_stack_or_ip(&CExpr::Var(name.to_string())) {
            return false;
        }
        self.lookup_type_hint(name).is_some_and(CType::is_integer)
    }

    fn linear_term_order_key(&self, expr: &CExpr) -> (u8, usize, String) {
        match expr {
            CExpr::Var(name) => (
                0,
                self.param_rank_for_visible_name(name).unwrap_or(usize::MAX),
                name.clone(),
            ),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.linear_term_order_key(inner)
            }
            _ => (1, usize::MAX, format!("{expr:?}")),
        }
    }

    fn param_rank_for_visible_name(&self, name: &str) -> Option<usize> {
        let lower = name.to_ascii_lowercase();
        self.inputs
            .arch
            .arg_regs
            .iter()
            .enumerate()
            .find_map(|(idx, reg)| {
                let reg_lower = reg.to_ascii_lowercase();
                if lower == reg_lower {
                    return Some(idx);
                }
                self.inputs
                    .param_register_aliases
                    .get(&reg_lower)
                    .filter(|alias| alias.eq_ignore_ascii_case(name))
                    .map(|_| idx)
            })
    }

    fn identity_simplify_expr(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::Binary { op, left, right } => {
                self.identity_simplify_binary(op, *left, *right, None)
            }
            other => other,
        }
    }

    fn assign_stmt(&self, lhs: CExpr, rhs: CExpr) -> Option<CStmt> {
        let lhs = self.rewrite_stack_expr(lhs);
        let rhs = self.identity_simplify_expr(rhs);
        let rhs = {
            let mut semantic_visited = HashSet::new();
            self.semanticize_visible_expr(&rhs, 0, &mut semantic_visited)
        };
        let rhs = self.rewrite_stack_expr(rhs);
        let mut rhs = if let CExpr::Var(lhs_name) = &lhs
            && self
                .stack_offset_for_visible_storage_name(lhs_name)
                .is_some()
            && self.expr_is_address_artifact_in_scalar_context(&rhs)
        {
            self.scalar_context_root_candidate_for_name(
                lhs_name,
                VisibleExprContext::ScalarPredicate,
            )
            .unwrap_or(rhs)
        } else {
            rhs
        };
        if let CExpr::Var(lhs_name) = &lhs
            && is_generic_arg_name(lhs_name)
            && let Some(rhs_alias) = self.arg_alias_for_expr(&rhs)
            && lhs_name.eq_ignore_ascii_case(&rhs_alias)
        {
            return None;
        }
        if let CExpr::Var(lhs_name) = &lhs
            && is_generic_arg_name(lhs_name)
            && self
                .lookup_type_hint(lhs_name)
                .is_some_and(|ty| matches!(ty, CType::Pointer(_)))
            && !self.looks_like_pointer(&rhs)
            && self.expr_mentions_rendered_name(&rhs, lhs_name)
        {
            return None;
        }
        if let CExpr::Var(lhs_name) = &lhs
            && let CExpr::Cast { expr, .. } = &rhs
            && matches!(expr.as_ref(), CExpr::Var(rhs_name) if rhs_name.eq_ignore_ascii_case(lhs_name))
        {
            return None;
        }
        if let CExpr::Var(lhs_name) = &lhs
            && let CExpr::Var(rhs_name) = &rhs
            && lhs_name.eq_ignore_ascii_case(rhs_name)
            && let Some(recovered) =
                self.recovered_owned_call_result_definition_rhs_for_visible_name(lhs_name)
        {
            rhs = recovered;
        }
        if lhs == rhs {
            return None;
        }
        Some(CStmt::Expr(CExpr::assign(lhs, rhs)))
    }

    fn assignment_lhs_expr(&self, dst: &SSAVar) -> CExpr {
        let rendered = self.var_name(dst);
        if dst.version > 0 && is_generic_arg_name(&rendered) {
            if let Some(alias) = self.var_aliases_map().get(&dst.display_name())
                && !is_generic_arg_name(alias)
            {
                return CExpr::Var(
                    self.canonicalize_stack_name(alias)
                        .unwrap_or_else(|| alias.clone()),
                );
            }

            let base = match dst.name_kind() {
                SSAVarNameKind::RegisterAlias => {
                    let reg = dst.name.trim_start_matches("reg:");
                    if is_hex_name(reg) {
                        format!("r{}", reg)
                    } else {
                        reg.to_ascii_lowercase()
                    }
                }
                SSAVarNameKind::Temporary => "t".to_string(),
                _ => dst.name.to_ascii_lowercase().replace([':', '.'], "_"),
            };

            return if base == "t" {
                CExpr::Var(format!("t{}", dst.version))
            } else {
                CExpr::Var(format!("{}_{}", base, dst.version))
            };
        }
        CExpr::Var(rendered)
    }

    fn expr_mentions_rendered_name(&self, expr: &CExpr, name: &str) -> bool {
        let mut found = false;
        expr.visit(&mut |node| {
            if let CExpr::Var(candidate) = node
                && candidate.eq_ignore_ascii_case(name)
            {
                found = true;
            }
        });
        found
    }

    fn ptr_arith_expr(
        &self,
        base: &SSAVar,
        index: &SSAVar,
        element_size: u32,
        is_sub: bool,
    ) -> CExpr {
        let base_expr = self.get_expr(base);
        let index_expr = self.get_expr(index);
        let scaled = if element_size <= 1 {
            index_expr
        } else {
            CExpr::binary(
                BinaryOp::Mul,
                index_expr,
                CExpr::IntLit(element_size as i64),
            )
        };
        let op = if is_sub { BinaryOp::Sub } else { BinaryOp::Add };
        CExpr::binary(op, base_expr, scaled)
    }

    fn lookup_semantic_value(&self, name: &str) -> Option<&analysis::SemanticValue> {
        self.semantic_value_for_name(name)
    }

    fn resolution_name_key(&self, prefix: &str, name: &str) -> String {
        self.use_info()
            .value_id_for_name(name)
            .map(|value_id| format!("{prefix}:value:{}", value_id.0))
            .unwrap_or_else(|| format!("{prefix}:name:{name}"))
    }

    fn phi_sources_for_name(&self, name: &str) -> Option<&Vec<SSAVar>> {
        self.phi_sources_map()
            .get(name)
            .or_else(|| self.phi_sources_map().get(&name.to_ascii_lowercase()))
            .or_else(|| {
                name.rsplit_once('_').and_then(|(base, version)| {
                    self.phi_sources_map()
                        .get(&format!("{}_{}", base.to_lowercase(), version))
                        .or_else(|| {
                            self.phi_sources_map().get(&format!(
                                "{}_{}",
                                base.to_uppercase(),
                                version
                            ))
                        })
                })
            })
    }

    fn resolve_expr_from_phi_sources(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
        imported: bool,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        let visit_key = self.resolution_name_key("phi-expr", name);
        if !visited.insert(visit_key.clone()) {
            return None;
        }

        let mut best = None;
        let sources = self.phi_sources_for_name(name).cloned();
        if let Some(sources) = sources {
            for src in sources {
                let src_name = src.display_name();
                let candidate = self
                    .render_semantic_value_by_name(&src_name, depth + 1, visited)
                    .or_else(|| {
                        self.lookup_definition_raw_with_depth(&src_name, depth + 1, visited)
                            .map(|expr| self.semanticize_visible_expr(&expr, depth + 1, visited))
                    })
                    .or_else(|| {
                        self.render_value_ref(
                            &analysis::ValueRef::from(src.clone()),
                            depth + 1,
                            visited,
                        )
                    })
                    .or_else(|| self.lookup_definition_with_depth(&src_name, depth + 1, visited))
                    .or_else(|| {
                        self.best_visible_definition_with_depth(&src_name, depth + 1, visited)
                    });
                let candidate = if imported {
                    candidate
                        .map(|expr| self.resolve_imported_call_arg_expr(&expr, depth + 1, visited))
                } else {
                    candidate
                };

                best = if imported {
                    self.choose_preferred_call_arg_expr(best, candidate, true)
                } else {
                    self.choose_preferred_visible_expr(best, candidate)
                };
            }
        }

        visited.remove(&visit_key);
        best
    }

    fn render_semantic_value_by_name(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Semantic, name) {
            return self.resolution_cycle_fallback(name);
        }
        let visit_key = self.resolution_name_key("sem", name);
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH || !visited.insert(visit_key.clone()) {
            self.leave_resolution_guard(ResolutionPhase::Semantic, name);
            return None;
        }
        let in_progress_key = self.resolution_name_key("sem-progress", name);
        {
            let mut in_progress = self.semantic_render_in_progress.borrow_mut();
            if !in_progress.insert(in_progress_key.clone()) {
                visited.remove(&visit_key);
                self.leave_resolution_guard(ResolutionPhase::Semantic, name);
                return None;
            }
        }
        let rendered = self
            .lookup_semantic_value(name)
            .and_then(|value| self.render_semantic_value(value, depth + 1, visited))
            .or_else(|| {
                self.find_ssa_name_for_rendered_alias(name)
                    .and_then(|ssa_name| {
                        (ssa_name != name)
                            .then_some(ssa_name)
                            .and_then(|ssa_name| self.lookup_semantic_value(&ssa_name))
                            .and_then(|value| self.render_semantic_value(value, depth + 1, visited))
                    })
            })
            .or_else(|| self.resolve_expr_from_phi_sources(name, depth + 1, visited, false));
        self.semantic_render_in_progress
            .borrow_mut()
            .remove(&in_progress_key);
        self.leave_resolution_guard(ResolutionPhase::Semantic, name);
        visited.remove(&visit_key);
        rendered
    }

    pub(crate) fn resolve_switch_expr_for_block_with_selector(
        &self,
        block_addr: u64,
    ) -> Option<(CExpr, Option<ValueId>)> {
        if let Some(selector) = self.resolve_switch_expr_from_control_facts(block_addr) {
            return Some(selector);
        }

        if let Some(expr) = self
            .prepared_semantic_view()
            .and_then(|view| view.switch_selector_expr_for_block(block_addr).cloned())
        {
            return Some((self.refine_switch_selector_expr(expr), None));
        }
        let value = self.switch_selector_roots_map().get(&block_addr)?;
        let mut visited = HashSet::new();
        let rendered = self
            .render_semantic_value(value, 0, &mut visited)
            .unwrap_or_else(|| self.expr_for_semantic_call_arg_fallback(value));
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&rendered, 0, &mut semantic_visited);
        self.choose_preferred_visible_expr(Some(rendered), Some(semanticized))
            .map(|expr| (self.refine_switch_selector_expr(expr), None))
    }

    fn resolve_switch_expr_from_control_facts(
        &self,
        block_addr: u64,
    ) -> Option<(CExpr, Option<ValueId>)> {
        if let Some((selector_id, selector)) = self
            .control_facts()
            .and_then(|facts| facts.switches.get(&block_addr))
            .and_then(|switch| switch.selector)
            .and_then(|selector| {
                self.prepared_var_for_value_id(selector)
                    .map(|var| (selector, var))
            })
        {
            let rooted = self
                .prepared_canonical_value_root(selector)
                .unwrap_or_else(|| selector.clone());
            let rendered = if rooted.is_const() {
                self.const_to_expr(&rooted)
            } else {
                self.resolve_predicate_operand(
                    &self.origin_name_to_expr(&rooted.display_name()),
                    0,
                    &mut HashSet::new(),
                )
            };
            let mut semantic_visited = HashSet::new();
            let semanticized = self.semanticize_visible_expr(&rendered, 0, &mut semantic_visited);
            return self
                .choose_preferred_visible_expr(Some(rendered), Some(semanticized))
                .map(|expr| (self.refine_switch_selector_expr(expr), Some(selector_id)));
        }
        None
    }

    fn refine_switch_selector_expr(&self, expr: CExpr) -> CExpr {
        let refined = self.simplify_switch_selector_expr(self.rewrite_stack_expr(expr));
        let fallback = match &refined {
            CExpr::Var(name)
                if self.is_low_signal_visible_name(name)
                    || self.is_transient_visible_name(name)
                    || is_generic_stack_placeholder_alias(name) =>
            {
                self.call_result_source_for_ssa_name(name)
                    .or_else(|| self.local_post_call_source_for_ssa_name(name))
                    .and_then(|source| self.stable_owned_call_result_expr_for_source(source))
                    .or_else(|| self.stable_owned_call_result_expr_for_name(name, true))
                    .or_else(|| self.best_visible_definition(name))
                    .map(|candidate| {
                        self.simplify_switch_selector_expr(self.rewrite_stack_expr(candidate))
                    })
            }
            _ => None,
        };
        self.choose_preferred_visible_expr(Some(refined.clone()), fallback)
            .unwrap_or(refined)
    }

    fn simplify_switch_selector_expr(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::Paren(inner) => self.simplify_switch_selector_expr(*inner),
            CExpr::Cast { expr: inner, .. } => self.simplify_switch_selector_expr(*inner),
            CExpr::Subscript { base, index } => {
                if self.is_jump_table_base_expr(base.as_ref())
                    && self.is_switch_selector_index_expr(index.as_ref())
                {
                    self.simplify_switch_selector_expr(*index)
                } else {
                    CExpr::Subscript { base, index }
                }
            }
            other => other,
        }
    }

    fn is_jump_table_base_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::UIntLit(_) | CExpr::IntLit(_) | CExpr::StringLit(_) => true,
            CExpr::Var(name) => is_static_jump_table_base_name(name),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_jump_table_base_expr(inner)
            }
            _ => false,
        }
    }

    fn is_switch_selector_index_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                !self.is_low_signal_visible_name(name)
                    && !self.is_transient_visible_name(name)
                    && !is_generic_stack_placeholder_alias(name)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_switch_selector_index_expr(inner)
            }
            CExpr::Binary { left, right, .. } => {
                self.is_switch_selector_index_expr(left)
                    || self.is_switch_selector_index_expr(right)
            }
            _ => false,
        }
    }

    pub(crate) fn render_semantic_value(
        &self,
        value: &analysis::SemanticValue,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        match value {
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => {
                Some(expr.clone())
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(value)) => {
                self.render_value_ref(value, depth, visited)
            }
            analysis::SemanticValue::Address(shape) => {
                self.render_address_expr_from_addr(shape, depth, visited)
            }
            analysis::SemanticValue::Load { space, addr, size } => {
                self.render_semantic_load(*space, addr, *size, depth, visited)
            }
            analysis::SemanticValue::Unknown => None,
        }
    }

    fn render_value_ref(
        &self,
        value: &analysis::ValueRef,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        let name = value.display_name();
        let visit_key = format!("val:{name}");
        if !visited.insert(visit_key.clone()) {
            return None;
        }
        {
            let mut in_progress = self.value_render_in_progress.borrow_mut();
            if !in_progress.insert(name.clone()) {
                visited.remove(&visit_key);
                return None;
            }
        }

        if let Some(owner) = self.stable_owned_call_result_expr_for_name(&name, true) {
            self.value_render_in_progress.borrow_mut().remove(&name);
            visited.remove(&visit_key);
            return Some(owner);
        }

        let forwarded = value
            .value_id()
            .and_then(|value_id| self.forwarded_value_for_value_id(value_id))
            .and_then(|prov| {
                prov.source_var.clone().map(|source| {
                    self.render_value_ref(&analysis::ValueRef::from(source), depth + 1, visited)
                })
            })
            .flatten()
            .or_else(|| {
                self.forwarded_source_var(&name).and_then(|source| {
                    self.render_value_ref(&analysis::ValueRef::from(source), depth + 1, visited)
                })
            });
        let fallback = if value.var.is_const() {
            Some(self.const_to_expr(&value.var))
        } else {
            let rendered = self.var_name(&value.var);
            Some(
                self.arg_alias_for_rendered_name(&rendered)
                    .or_else(|| self.certified_signature_arg_alias_for_register(&rendered))
                    .map(CExpr::Var)
                    .unwrap_or_else(|| CExpr::Var(rendered)),
            )
        };
        let rendered = match self.lookup_semantic_value(&name).or_else(|| {
            value
                .value_id()
                .and_then(|value_id| self.semantic_value_for_value_id(value_id))
        }) {
            Some(analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr))) => {
                self.render_scalar_value_ref(value, expr.clone(), fallback.clone())
            }
            Some(analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(root))) => {
                self.render_value_ref(root, depth + 1, visited)
            }
            Some(analysis::SemanticValue::Address(shape)) => {
                self.render_address_expr_from_addr(shape, depth + 1, visited)
            }
            Some(analysis::SemanticValue::Load { space, addr, size }) => {
                self.render_semantic_load(*space, addr, *size, depth + 1, visited)
            }
            Some(analysis::SemanticValue::Unknown) | None => self
                .resolve_expr_from_phi_sources(&name, depth + 1, visited, false)
                .or_else(|| {
                    self.lookup_definition_raw_with_depth(&name, depth + 1, visited)
                        .or_else(|| {
                            value.value_id().and_then(|value_id| {
                                self.definition_for_value_id(value_id).cloned()
                            })
                        })
                        .map(|expr| {
                            let semanticized =
                                self.semanticize_visible_expr(&expr, depth + 1, visited);
                            if self.prefers_visible_expr(&expr, &semanticized) {
                                semanticized
                            } else {
                                expr
                            }
                        })
                        .and_then(|expr| {
                            self.render_scalar_value_ref(value, expr, fallback.clone())
                        })
                })
                .or_else(|| {
                    self.lookup_definition_with_depth(&name, depth + 1, visited)
                        .and_then(|expr| {
                            self.render_semantic_load_from_definition_expr(
                                &expr,
                                depth + 1,
                                visited,
                            )
                        })
                })
                .or_else(|| {
                    self.definition_for_name(&name).and_then(|expr| {
                        self.render_semantic_load_from_definition_expr(expr, depth + 1, visited)
                    })
                }),
        }
        .or(fallback);
        let rendered = self.choose_preferred_visible_expr(rendered, forwarded);

        self.value_render_in_progress.borrow_mut().remove(&name);
        visited.remove(&visit_key);
        rendered
    }

    fn render_semantic_load_from_definition_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        match expr {
            CExpr::Deref(inner) => {
                let addr = self.normalized_addr_from_visible_expr(inner, depth + 1)?;
                self.render_load_from_addr(&addr, 0, depth + 1, visited)
            }
            CExpr::Cast { expr: inner, .. } | CExpr::Paren(inner) => {
                self.render_semantic_load_from_definition_expr(inner, depth + 1, visited)
            }
            _ => None,
        }
    }

    fn forwarded_source_var(&self, name: &str) -> Option<SSAVar> {
        if let Some(cached) = self.forwarded_source_cache.borrow().get(name).cloned() {
            return cached;
        }

        let resolved = self
            .forwarded_value_for_name(name)
            .and_then(|prov| prov.source_var.clone())
            .filter(|src| src.display_name() != name);
        self.forwarded_source_cache
            .borrow_mut()
            .insert(name.to_string(), resolved.clone());
        resolved
    }

    fn render_base_ref_expr(
        &self,
        base: &analysis::BaseRef,
        as_address: bool,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        match base {
            analysis::BaseRef::Value(value) => self.render_value_ref(value, depth + 1, visited),
            analysis::BaseRef::StackSlot(offset) => {
                self.resolve_stack_var(*offset).map(CExpr::Var).map(|expr| {
                    if as_address {
                        CExpr::AddrOf(Box::new(expr))
                    } else {
                        expr
                    }
                })
            }
            analysis::BaseRef::Raw(expr) => {
                if let Some(owner) = self.stable_owned_call_result_expr_for_raw_call(expr) {
                    return Some(owner);
                }
                let normalized = self.normalize_final_call_expr_in_context(
                    expr.clone(),
                    FinalExprNormalizeContext::Generic,
                );
                if normalized != *expr {
                    Some(normalized)
                } else {
                    Some(expr.clone())
                }
            }
        }
    }

    fn stable_owned_call_result_expr_for_raw_call(&self, expr: &CExpr) -> Option<CExpr> {
        match self.source_proof_for_call_expr(expr) {
            CallExprSourceProof::Exact(source_call) => {
                self.stable_owned_call_result_expr_for_source(source_call)
            }
            CallExprSourceProof::ContradictedOrAmbiguous | CallExprSourceProof::None => None,
        }
    }

    fn prepared_named_expr_for_memory_location(&self, location: &MemoryLocation) -> Option<CExpr> {
        let object = self.prepared_objects()?.object(location.object)?;
        match &object.kind {
            ObjectKind::Global { .. } => None,
            ObjectKind::StackSlot { offset, .. } | ObjectKind::FrameObject { offset, .. }
                if location.address.exact_offset() == Some(0) =>
            {
                self.resolve_stack_var(*offset).map(CExpr::Var)
            }
            _ => None,
        }
    }

    fn prepared_named_memory_expr_for_value(&self, var: &SSAVar) -> Option<CExpr> {
        let prepared = self.inputs.prepared_ssa?;
        let value = prepared.graph().value_id_for_var(var)?;
        let inst = prepared.graph().def_inst(value)?;
        let (block_addr, op_idx) = prepared.inst_op_site(inst)?;
        let uses = prepared.memory_uses_for_op_site(block_addr, op_idx)?;
        (uses.len() == 1)
            .then_some(&uses[0])
            .and_then(|fact| self.prepared_named_expr_for_memory_location(&fact.location))
    }

    fn prepared_named_memory_def_expr_for_current_op(&self) -> Option<CExpr> {
        let defs = self.prepared_memory_defs_for_current_op()?;
        (defs.len() == 1)
            .then_some(&defs[0])
            .and_then(|fact| self.prepared_named_expr_for_memory_location(&fact.location))
    }

    fn prepared_named_object_expr_for_addr(
        &self,
        addr: &analysis::NormalizedAddr,
    ) -> Option<CExpr> {
        if addr.index.is_some() {
            return None;
        }

        match &addr.base {
            analysis::BaseRef::Value(base_ref) if addr.offset_bytes == 0 => {
                let prepared = self.inputs.prepared_ssa?;
                let object = prepared
                    .object_for_var(&base_ref.var, r2il::SpaceId::Ram)
                    .or_else(|| {
                        self.prepared_canonical_value_root(&base_ref.var)
                            .and_then(|root| prepared.object_for_var(&root, r2il::SpaceId::Ram))
                    })?;
                self.prepared_named_expr_for_memory_location(&MemoryLocation {
                    space: r2il::SpaceId::Ram,
                    object,
                    address: r2ssa::RelativeMemoryAddress::Exact(0),
                    size: 0,
                })
            }
            _ => None,
        }
    }

    fn allow_exact_named_object_expr_for_load_addr(&self, addr: &analysis::NormalizedAddr) -> bool {
        let analysis::BaseRef::Value(base_ref) = &addr.base else {
            return true;
        };
        if addr.index.is_some() || addr.offset_bytes != 0 {
            return true;
        }

        let mut visited = HashSet::new();
        let root = self
            .semantic_root_var(&base_ref.var, 0, &mut visited)
            .unwrap_or_else(|| base_ref.var.clone());
        !matches!(
            self.type_hint_for_var(&root)
                .or_else(|| self.type_hint_for_var(&base_ref.var)),
            Some(CType::Pointer(_)) | Some(CType::Array(_, _))
        )
    }

    fn exact_named_object_expr_for_addr(&self, addr: &analysis::NormalizedAddr) -> Option<CExpr> {
        self.prepared_named_object_expr_for_addr(addr)
    }

    fn render_scalar_value_ref(
        &self,
        value: &analysis::ValueRef,
        semantic: CExpr,
        fallback: Option<CExpr>,
    ) -> Option<CExpr> {
        if !value.var.is_const()
            && (matches!(semantic, CExpr::IntLit(0) | CExpr::UIntLit(0))
                || self.expr_contains_synthetic_stack_placeholder(&semantic)
                || self.is_uninitialized_return_reg(&semantic))
        {
            fallback
        } else {
            Some(semantic)
        }
    }

    fn expr_contains_synthetic_stack_placeholder(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = name.to_ascii_lowercase();
                lower == "stack" || lower == "saved_fp" || lower.starts_with("stack_")
            }
            CExpr::Paren(inner) | CExpr::AddrOf(inner) | CExpr::Deref(inner) => {
                self.expr_contains_synthetic_stack_placeholder(inner)
            }
            CExpr::Cast { expr: inner, .. } | CExpr::Unary { operand: inner, .. } => {
                self.expr_contains_synthetic_stack_placeholder(inner)
            }
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_synthetic_stack_placeholder(left)
                    || self.expr_contains_synthetic_stack_placeholder(right)
            }
            CExpr::Subscript { base, index } => {
                self.expr_contains_synthetic_stack_placeholder(base)
                    || self.expr_contains_synthetic_stack_placeholder(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_synthetic_stack_placeholder(base)
            }
            CExpr::Call { func, args } => {
                self.expr_contains_synthetic_stack_placeholder(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_contains_synthetic_stack_placeholder(arg))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_contains_synthetic_stack_placeholder(cond)
                    || self.expr_contains_synthetic_stack_placeholder(then_expr)
                    || self.expr_contains_synthetic_stack_placeholder(else_expr)
            }
            CExpr::Comma(exprs) => exprs
                .iter()
                .any(|inner| self.expr_contains_synthetic_stack_placeholder(inner)),
            CExpr::Sizeof(inner) => self.expr_contains_synthetic_stack_placeholder(inner),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn stack_offset_for_normalized_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<i64> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        if addr.index.is_none()
            && let analysis::BaseRef::StackSlot(base) = addr.base
        {
            return base.checked_add(addr.offset_bytes);
        }

        let base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
        if addr.index.is_none()
            && let Some(base_offset) = self.extract_offset_from_expr(&base_expr)
        {
            return base_offset.checked_add(addr.offset_bytes);
        }

        if let Some(index) = &addr.index
            && addr.scale_bytes == 1
        {
            let index_expr = self.render_value_ref(index, depth + 1, visited)?;
            if self.is_stack_base_expr(&index_expr) {
                let base_offset = self.expr_to_offset(&base_expr)?;
                return base_offset.checked_add(addr.offset_bytes);
            }
        }

        let mut full_expr = base_expr;
        if let Some(index) = &addr.index {
            let index_expr = self.render_value_ref(index, depth + 1, visited)?;
            let scaled = if addr.scale_bytes.unsigned_abs() <= 1 {
                index_expr
            } else {
                CExpr::binary(
                    BinaryOp::Mul,
                    index_expr,
                    CExpr::IntLit(addr.scale_bytes.unsigned_abs() as i64),
                )
            };
            full_expr = CExpr::binary(
                if addr.scale_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                full_expr,
                scaled,
            );
        }
        if addr.offset_bytes != 0 {
            full_expr = CExpr::binary(
                if addr.offset_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                full_expr,
                CExpr::IntLit(addr.offset_bytes.unsigned_abs() as i64),
            );
        }

        self.extract_offset_from_expr(&full_expr).or_else(|| {
            let canonical = self.canonicalize_visible_address_expr(&full_expr, depth + 1);
            self.extract_offset_from_expr(&canonical)
        })
    }

    fn render_address_expr_from_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        let stack_slot_addr_alias = |ctx: &FoldingContext<'_>, offset: i64| {
            ctx.resolve_stack_var(offset).and_then(|name| {
                (!is_generic_stack_placeholder_alias(&name)
                    && !ctx.is_low_signal_visible_name(&name)
                    && !ctx.is_transient_visible_name(&name))
                .then(|| CExpr::AddrOf(Box::new(CExpr::Var(name))))
            })
        };

        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_addr_alias(self, full_offset)
        {
            return Some(alias);
        }

        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
            && Self::expr_supports_addr_of(&rendered)
        {
            return Some(CExpr::AddrOf(Box::new(rendered)));
        }

        let raw_base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
        let recovered_stack_slot = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|_| addr.index.is_some() && self.expr_to_offset(&raw_base_expr).is_some())
            .map(|offset| analysis::NormalizedAddr {
                base: analysis::BaseRef::StackSlot(offset),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            });
        let effective_addr = if let Some(stack_slot) = recovered_stack_slot {
            stack_slot
        } else if matches!(addr.base, analysis::BaseRef::StackSlot(_)) {
            addr.clone()
        } else if addr.index.is_none() {
            self.normalized_addr_from_visible_expr(&raw_base_expr, depth + 1)
                .and_then(|mut normalized| {
                    normalized.offset_bytes =
                        normalized.offset_bytes.checked_add(addr.offset_bytes)?;
                    Some(normalized)
                })
                .filter(|normalized| matches!(normalized.base, analysis::BaseRef::StackSlot(_)))
                .unwrap_or_else(|| addr.clone())
        } else {
            addr.clone()
        };
        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_addr_alias(self, full_offset)
        {
            return Some(alias);
        }
        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
            && Self::expr_supports_addr_of(&rendered)
        {
            return Some(CExpr::AddrOf(Box::new(rendered)));
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(alias) = stack_slot_addr_alias(self, full_offset)
        {
            return Some(alias);
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
            && Self::expr_supports_addr_of(&rendered)
        {
            return Some(CExpr::AddrOf(Box::new(rendered)));
        }

        let mut expr = self.render_base_ref_expr(&effective_addr.base, true, depth + 1, visited)?;
        if let Some(index) = &effective_addr.index {
            let index_expr = self.render_value_ref(index, depth + 1, visited)?;
            let scaled = if effective_addr.scale_bytes.unsigned_abs() <= 1 {
                index_expr
            } else {
                CExpr::binary(
                    BinaryOp::Mul,
                    index_expr,
                    CExpr::IntLit(effective_addr.scale_bytes.unsigned_abs() as i64),
                )
            };
            expr = CExpr::binary(
                if effective_addr.scale_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                expr,
                scaled,
            );
        }
        if effective_addr.offset_bytes != 0 {
            expr = CExpr::binary(
                if effective_addr.offset_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                expr,
                CExpr::IntLit(effective_addr.offset_bytes.unsigned_abs() as i64),
            );
        }
        Some(expr)
    }

    fn expr_supports_addr_of(expr: &CExpr) -> bool {
        matches!(
            expr,
            CExpr::Var(_)
                | CExpr::Subscript { .. }
                | CExpr::Member { .. }
                | CExpr::PtrMember { .. }
        )
    }

    fn oracle_field_name_for_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        access_size: Option<u32>,
    ) -> Option<String> {
        if addr.offset_bytes < 0 {
            return None;
        }
        let offset = addr.offset_bytes as u64;

        match &addr.base {
            analysis::BaseRef::Value(base_ref) => {
                let mut visited = HashSet::new();
                if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited)
                    && let Some(field) = self
                        .field_name_from_type_hint_for_var(&root, offset, access_size)
                        .or_else(|| {
                            self.field_name_from_type_hint_for_var(
                                &base_ref.var,
                                offset,
                                access_size,
                            )
                        })
                {
                    return Some(field);
                }

                if let Some(field) =
                    self.field_name_from_type_hint_for_var(&base_ref.var, offset, access_size)
                {
                    return Some(field);
                }

                if let Some(oracle) = self.inputs.type_oracle
                    && let Some(field) = oracle
                        .field_name(oracle.type_of(&base_ref.var), offset)
                        .map(|field| field.to_string())
                {
                    return Some(field);
                }

                let mut visited = HashSet::new();
                if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited)
                    && let Some(oracle) = self.inputs.type_oracle
                    && let Some(field) = oracle
                        .field_name(oracle.type_of(&root), offset)
                        .map(|field| field.to_string())
                {
                    return Some(field);
                }
            }
            analysis::BaseRef::Raw(CExpr::Var(name)) => {
                if let Some(hint) = self.lookup_type_hint(name)
                    && let Some(field) = self.field_name_from_type_hint(hint, offset, access_size)
                {
                    return Some(field);
                }
                if let Some(ssa_name) = self.preferred_entry_arg_ssa_name(name)
                    && let Some(var) = self.guess_ssa_var_from_name(&ssa_name)
                {
                    if let Some(oracle) = self.inputs.type_oracle
                        && let Some(field) = oracle
                            .field_name(oracle.type_of(&var), offset)
                            .map(|field| field.to_string())
                    {
                        return Some(field);
                    }
                    if let Some(field) =
                        self.field_name_from_type_hint_for_var(&var, offset, access_size)
                    {
                        return Some(field);
                    }
                }
                if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
                    && let Some(var) = self.guess_ssa_var_from_name(&ssa_name)
                {
                    if let Some(oracle) = self.inputs.type_oracle
                        && let Some(field) = oracle
                            .field_name(oracle.type_of(&var), offset)
                            .map(|field| field.to_string())
                    {
                        return Some(field);
                    }
                    if let Some(field) =
                        self.field_name_from_type_hint_for_var(&var, offset, access_size)
                    {
                        return Some(field);
                    }
                }
                if let Some(var) = self.guess_ssa_var_from_name(name) {
                    if let Some(oracle) = self.inputs.type_oracle
                        && let Some(field) = oracle
                            .field_name(oracle.type_of(&var), offset)
                            .map(|field| field.to_string())
                    {
                        return Some(field);
                    }
                    if let Some(field) =
                        self.field_name_from_type_hint_for_var(&var, offset, access_size)
                    {
                        return Some(field);
                    }
                }
            }
            analysis::BaseRef::StackSlot(_) | analysis::BaseRef::Raw(_) => {}
        }

        None
    }

    fn exact_oracle_field_name_for_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        offset: u64,
    ) -> Option<String> {
        let oracle = self.inputs.type_oracle?;
        match &addr.base {
            analysis::BaseRef::Value(base_ref) => {
                if let Some(field) = oracle
                    .field_layout(oracle.type_of(&base_ref.var), offset)
                    .map(|layout| layout.field_name)
                {
                    return Some(field);
                }
                let mut visited = HashSet::new();
                if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited)
                    && let Some(field) = oracle
                        .field_layout(oracle.type_of(&root), offset)
                        .map(|layout| layout.field_name)
                {
                    return Some(field);
                }
            }
            analysis::BaseRef::Raw(CExpr::Var(name)) => {
                let mut vars = Vec::new();
                if let Some(ssa_name) = self.preferred_entry_arg_ssa_name(name)
                    && let Some(var) = self.guess_ssa_var_from_name(&ssa_name)
                {
                    vars.push(var);
                }
                if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
                    && let Some(var) = self.guess_ssa_var_from_name(&ssa_name)
                {
                    vars.push(var);
                }
                if let Some(var) = self.guess_ssa_var_from_name(name) {
                    vars.push(var);
                }
                vars.sort_by_key(SSAVar::display_name);
                vars.dedup_by_key(|var| var.display_name());
                for var in vars {
                    if let Some(field) = oracle
                        .field_layout(oracle.type_of(&var), offset)
                        .map(|layout| layout.field_name)
                    {
                        return Some(field);
                    }
                }
            }
            analysis::BaseRef::StackSlot(_) | analysis::BaseRef::Raw(_) => {}
        }
        None
    }

    fn field_name_from_type_hint_for_var(
        &self,
        var: &SSAVar,
        offset: u64,
        access_size: Option<u32>,
    ) -> Option<String> {
        let hint = self.type_hint_for_var(var)?;
        self.field_name_from_type_hint(&hint, offset, access_size)
    }

    fn field_name_from_type_hint(
        &self,
        ty: &CType,
        offset: u64,
        access_size: Option<u32>,
    ) -> Option<String> {
        match ty {
            CType::Pointer(inner) | CType::Array(inner, _) => {
                self.field_name_from_type_hint(inner, offset, access_size)
            }
            CType::Struct(name) | CType::Union(name) | CType::Typedef(name) => {
                self.lookup_external_field_name(name, offset, access_size)
            }
            _ => None,
        }
    }

    fn certified_field_name_for_offset(
        &self,
        field_name: String,
        offset: i64,
        access_size: Option<u32>,
        is_write: bool,
    ) -> Option<String> {
        return Some(field_name);

        let offset = u64::try_from(offset).ok()?;
        let has_layout_certificate = self.inputs.field_access_certificates.iter().any(|cert| {
            cert.field_offset == offset
                && cert.field_name.eq_ignore_ascii_case(&field_name)
                && access_size.is_none_or(|size| {
                    cert.field_type
                        .as_deref()
                        .and_then(|ty| parse_type_like_spec(ty, self.inputs.arch.ptr_size))
                        .and_then(|ty| c_type_like_size_bytes(&ty, self.inputs.arch.ptr_size))
                        .is_none_or(|bytes| bytes == u64::from(size))
                })
        });
        if !has_layout_certificate {
            return None;
        }
        let render_facts = self.inputs.render_facts()?;
        let block_addr = self.current_block_addr.get()?;
        let op_idx = self.current_op_idx.get()?;
        render_facts
            .member_access_for_op(
                block_addr,
                op_idx,
                is_write,
                &field_name,
                offset,
                access_size,
            )
            .is_some()
            .then_some(field_name)
    }

    pub(super) fn certified_member_field_name_for_current_op_offset(
        &self,
        offset: i64,
        access_size: Option<u32>,
        is_write: bool,
    ) -> Option<String> {
        return None;

        let offset = u64::try_from(offset).ok()?;
        let render_facts = self.inputs.render_facts()?;
        let block_addr = self.current_block_addr.get()?;
        let op_idx = self.current_op_idx.get()?;
        let mut names = render_facts
            .member_accesses_by_op
            .get(&(block_addr, op_idx, is_write))?
            .iter()
            .filter_map(|fact| {
                let memory = render_facts.memory_access(fact.access)?;
                (memory.block_addr == block_addr
                    && memory.op_index == op_idx
                    && memory.is_write == is_write
                    && memory.object == fact.object
                    && memory.width == fact.access_width
                    && fact.field_offset == offset
                    && access_size.is_none_or(|width| fact.access_width == width))
                .then(|| fact.field_name.clone())
            })
            .collect::<Vec<_>>();
        names.sort_by_key(|name| name.to_ascii_lowercase());
        names.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
        let [field_name] = names.as_slice() else {
            return None;
        };
        self.certified_field_name_for_offset(
            field_name.clone(),
            offset as i64,
            access_size,
            is_write,
        )
    }

    fn certified_array_access_for_current_op(
        &self,
        field_offset: i64,
        element_stride: u64,
        access_size: Option<u32>,
        is_write: bool,
    ) -> bool {
        return true;

        let Ok(field_offset) = u64::try_from(field_offset) else {
            return false;
        };
        if element_stride == 0 {
            return false;
        }
        let Some(render_facts) = self.inputs.render_facts() else {
            return false;
        };
        let Some(block_addr) = self.current_block_addr.get() else {
            return false;
        };
        let Some(op_idx) = self.current_op_idx.get() else {
            return false;
        };
        render_facts
            .array_access_for_op(
                block_addr,
                op_idx,
                is_write,
                field_offset,
                element_stride,
                access_size,
            )
            .is_some()
    }

    fn exact_field_name_from_type_hint(
        &self,
        ty: &CType,
        offset: u64,
        access_size: u32,
    ) -> Option<String> {
        match ty {
            CType::Pointer(inner) | CType::Array(inner, _) => {
                self.exact_field_name_from_type_hint(inner, offset, access_size)
            }
            CType::Struct(name) => {
                self.lookup_exact_external_struct_field_name(name, offset, access_size)
            }
            CType::Union(name) => {
                self.lookup_exact_external_union_field_name(name, offset, access_size)
            }
            CType::Typedef(name) => self
                .lookup_exact_external_struct_field_name(name, offset, access_size)
                .or_else(|| self.lookup_exact_external_union_field_name(name, offset, access_size)),
            _ => None,
        }
    }

    fn exact_field_offset_is_pointer(&self, ty: &CType, offset: u64) -> bool {
        match ty {
            CType::Pointer(inner) | CType::Array(inner, _) => {
                self.exact_field_offset_is_pointer(inner, offset)
            }
            CType::Struct(name) => self.exact_external_field_offset_is_pointer(name, offset, true),
            CType::Union(name) => self.exact_external_field_offset_is_pointer(name, offset, false),
            CType::Typedef(name) => {
                self.exact_external_field_offset_is_pointer(name, offset, true)
                    || self.exact_external_field_offset_is_pointer(name, offset, false)
            }
            _ => false,
        }
    }

    fn exact_external_field_offset_is_pointer(
        &self,
        type_name: &str,
        offset: u64,
        is_struct: bool,
    ) -> bool {
        let key = type_name.trim().to_ascii_lowercase();
        let normalized = normalize_external_type_name(type_name)
            .trim()
            .to_ascii_lowercase();
        let mut keys = vec![key.clone()];
        if normalized != key {
            keys.push(normalized);
        }
        keys.into_iter().any(|key| {
            if is_struct {
                self.inputs
                    .external_type_db
                    .structs
                    .get(&key)
                    .and_then(|st| st.fields.get(&offset))
                    .is_some_and(|field| {
                        external_field_type_is_pointer(field, self.inputs.arch.ptr_size)
                    })
            } else {
                offset == 0
                    && self
                        .inputs
                        .external_type_db
                        .unions
                        .get(&key)
                        .is_some_and(|un| {
                            un.fields.values().any(|field| {
                                external_field_type_is_pointer(field, self.inputs.arch.ptr_size)
                            })
                        })
            }
        })
    }

    fn lookup_external_field_name(
        &self,
        type_name: &str,
        offset: u64,
        access_size: Option<u32>,
    ) -> Option<String> {
        let key = type_name.trim().to_ascii_lowercase();
        if let Some(st) = self.inputs.external_type_db.structs.get(&key)
            && let Some(field) = external_struct_field_name_for_offset(
                st,
                offset,
                access_size,
                self.inputs.arch.ptr_size,
            )
        {
            return Some(field);
        }
        if let Some(un) = self.inputs.external_type_db.unions.get(&key)
            && let Some(field) = external_union_field_name_for_offset(
                un,
                offset,
                access_size,
                self.inputs.arch.ptr_size,
            )
        {
            return Some(field);
        }
        let normalized = normalize_external_type_name(type_name);
        if normalized != key {
            let normalized_key = normalized.trim().to_ascii_lowercase();
            if let Some(st) = self.inputs.external_type_db.structs.get(&normalized_key)
                && let Some(field) = external_struct_field_name_for_offset(
                    st,
                    offset,
                    access_size,
                    self.inputs.arch.ptr_size,
                )
            {
                return Some(field);
            }
            if let Some(un) = self.inputs.external_type_db.unions.get(&normalized_key)
                && let Some(field) = external_union_field_name_for_offset(
                    un,
                    offset,
                    access_size,
                    self.inputs.arch.ptr_size,
                )
            {
                return Some(field);
            }
        }
        None
    }

    fn lookup_exact_external_struct_field_name(
        &self,
        type_name: &str,
        offset: u64,
        access_size: u32,
    ) -> Option<String> {
        let key = type_name.trim().to_ascii_lowercase();
        if let Some(st) = self.inputs.external_type_db.structs.get(&key)
            && let Some(field) = exact_external_struct_field_name_for_offset(
                st,
                offset,
                access_size,
                self.inputs.arch.ptr_size,
            )
        {
            return Some(field);
        }
        let normalized = normalize_external_type_name(type_name);
        if normalized != key {
            let normalized_key = normalized.trim().to_ascii_lowercase();
            if let Some(st) = self.inputs.external_type_db.structs.get(&normalized_key)
                && let Some(field) = exact_external_struct_field_name_for_offset(
                    st,
                    offset,
                    access_size,
                    self.inputs.arch.ptr_size,
                )
            {
                return Some(field);
            }
        }
        None
    }

    fn lookup_exact_external_union_field_name(
        &self,
        type_name: &str,
        offset: u64,
        access_size: u32,
    ) -> Option<String> {
        let key = type_name.trim().to_ascii_lowercase();
        if let Some(un) = self.inputs.external_type_db.unions.get(&key)
            && let Some(field) = exact_external_union_field_name_for_offset(
                un,
                offset,
                access_size,
                self.inputs.arch.ptr_size,
            )
        {
            return Some(field);
        }
        let normalized = normalize_external_type_name(type_name);
        if normalized != key {
            let normalized_key = normalized.trim().to_ascii_lowercase();
            if let Some(un) = self.inputs.external_type_db.unions.get(&normalized_key)
                && let Some(field) = exact_external_union_field_name_for_offset(
                    un,
                    offset,
                    access_size,
                    self.inputs.arch.ptr_size,
                )
            {
                return Some(field);
            }
        }
        None
    }

    fn semantic_root_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<SSAVar> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        let name = var.display_name();
        if !visited.insert(name.clone()) {
            return None;
        }

        let resolved = self
            .forwarded_source_var(&name)
            .and_then(|source| {
                self.semantic_root_var(&source, depth + 1, visited)
                    .or(Some(source))
            })
            .or_else(|| match self.lookup_semantic_value(&name) {
                Some(analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(root))) => self
                    .semantic_root_var(&root.var, depth + 1, visited)
                    .or_else(|| Some(root.var.clone())),
                Some(analysis::SemanticValue::Address(analysis::NormalizedAddr {
                    base: analysis::BaseRef::Value(root),
                    ..
                })) => self
                    .semantic_root_var(&root.var, depth + 1, visited)
                    .or_else(|| Some(root.var.clone())),
                _ => {
                    let copy_root = self.resolve_copy_root_name_in_fold(&name);
                    (copy_root != name)
                        .then_some(copy_root)
                        .and_then(|root_name| {
                            self.guess_ssa_var_from_name(&root_name)
                                .and_then(|root_var| {
                                    self.semantic_root_var(&root_var, depth + 1, visited)
                                        .or(Some(root_var))
                                })
                        })
                }
            });

        visited.remove(&name);
        resolved
    }

    fn render_access_expr_from_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        elem_size: u32,
        is_write: bool,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let stack_slot_access_alias = |ctx: &FoldingContext<'_>, offset: i64| {
            ctx.resolve_stack_var(offset).and_then(|name| {
                (!is_generic_stack_placeholder_alias(&name)
                    && !ctx.is_low_signal_visible_name(&name)
                    && !ctx.is_transient_visible_name(&name))
                .then_some(CExpr::Var(name))
            })
        };

        if let Some(exact) = self.exact_named_object_expr_for_addr(addr) {
            if !matches!(addr.base, analysis::BaseRef::StackSlot(_))
                && addr.index.is_none()
                && let Some(field) = self
                    .oracle_field_name_for_addr(addr, Some(elem_size))
                    .or_else(|| self.oracle_member_name(None, &exact, addr.offset_bytes))
                    .and_then(|field| {
                        self.certified_field_name_for_offset(
                            field,
                            addr.offset_bytes,
                            Some(elem_size),
                            is_write,
                        )
                    })
            {
                return Some(self.member_access_expr(exact, field));
            }
            return Some(exact);
        }

        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }

        if let Some(full_offset) = self.stack_offset_for_normalized_addr(addr, depth + 1, visited)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }

        if addr.index.is_none()
            && let Some(full_offset) = match addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }
        if addr.index.is_none()
            && let Some(full_offset) = match addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(addr.offset_bytes),
                _ => None,
            }
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }

        let raw_base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
        let recovered_stack_slot = self
            .stack_offset_for_normalized_addr(addr, depth + 1, visited)
            .filter(|_| addr.index.is_some() && self.expr_to_offset(&raw_base_expr).is_some())
            .map(|offset| analysis::NormalizedAddr {
                base: analysis::BaseRef::StackSlot(offset),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            });
        let effective_addr = if let Some(stack_slot) = recovered_stack_slot {
            stack_slot
        } else if matches!(addr.base, analysis::BaseRef::StackSlot(_)) {
            addr.clone()
        } else if addr.index.is_none() {
            self.normalized_addr_from_visible_expr(&raw_base_expr, depth + 1)
                .and_then(|mut normalized| {
                    normalized.offset_bytes =
                        normalized.offset_bytes.checked_add(addr.offset_bytes)?;
                    Some(normalized)
                })
                .filter(|normalized| {
                    matches!(normalized.base, analysis::BaseRef::StackSlot(_))
                        || normalized.index.is_some()
                        || self
                            .oracle_field_name_for_addr(normalized, Some(elem_size))
                            .is_some()
                })
                .unwrap_or_else(|| addr.clone())
        } else {
            addr.clone()
        };
        if let Some(full_offset) = self
            .stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            .filter(|offset| *offset < 0)
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }
        if let Some(full_offset) =
            self.stack_offset_for_normalized_addr(&effective_addr, depth + 1, visited)
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && full_offset < 0
            && let Some(alias) = stack_slot_access_alias(self, full_offset)
        {
            return Some(alias);
        }
        if effective_addr.index.is_none()
            && let Some(full_offset) = match effective_addr.base {
                analysis::BaseRef::StackSlot(base) => base.checked_add(effective_addr.offset_bytes),
                _ => None,
            }
            && let Some(value) = self.stable_stack_value_for_offset(full_offset)
            && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
        {
            return Some(rendered);
        }
        let base_expr = if effective_addr != *addr {
            self.render_base_ref_expr(&effective_addr.base, false, depth + 1, visited)
                .unwrap_or_else(|| raw_base_expr.clone())
        } else {
            raw_base_expr
        };
        let field_name = if matches!(effective_addr.base, analysis::BaseRef::StackSlot(_)) {
            None
        } else {
            self.oracle_field_name_for_addr(&effective_addr, Some(elem_size))
                .or_else(|| {
                    let mut normalized =
                        self.normalized_addr_from_visible_expr(&base_expr, depth + 1)?;
                    normalized.offset_bytes = normalized
                        .offset_bytes
                        .checked_add(effective_addr.offset_bytes)?;
                    self.oracle_field_name_for_addr(&normalized, Some(elem_size))
                })
                .or_else(|| {
                    self.expr_type_hint(&base_expr).and_then(|ty| {
                        self.field_name_from_type_hint(
                            &ty,
                            effective_addr.offset_bytes as u64,
                            Some(elem_size),
                        )
                    })
                })
                .or_else(|| {
                    self.certified_member_field_name_for_current_op_offset(
                        effective_addr.offset_bytes,
                        Some(elem_size),
                        is_write,
                    )
                })
                .or_else(|| self.oracle_member_name(None, &base_expr, effective_addr.offset_bytes))
                .and_then(|field| {
                    self.certified_field_name_for_offset(
                        field,
                        effective_addr.offset_bytes,
                        Some(elem_size),
                        is_write,
                    )
                })
        };

        if let Some(index) = &effective_addr.index {
            let scale = effective_addr.scale_bytes.unsigned_abs() as u32;
            let element_stride = u64::from(scale.max(elem_size).max(1));

            let mut index_expr = self.render_value_ref(index, depth + 1, visited)?;
            index_expr = self
                .normalize_index_expr(&index_expr, 0)
                .unwrap_or(index_expr);
            let mut elem_ty =
                self.infer_elem_type_from_base_ref(&effective_addr.base, scale.max(elem_size));
            let mut normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
            if effective_addr.scale_bytes >= 0
                && self.should_swap_indexed_access_base(&normalized_base, &index_expr)
            {
                std::mem::swap(&mut normalized_base, &mut index_expr);
                if let Some(swapped_ty) =
                    self.expr_type_hint(&normalized_base)
                        .and_then(|ty| match ty {
                            CType::Pointer(inner) | CType::Array(inner, _) => Some(*inner),
                            _ => None,
                        })
                {
                    elem_ty = swapped_ty;
                }
            }
            let base_source_ty = self.expr_type_hint(&normalized_base);
            let base_cast = self.cast_expr_if_needed(
                normalized_base,
                CType::ptr(elem_ty),
                base_source_ty.as_ref(),
            );
            let index_final = if effective_addr.scale_bytes < 0 {
                CExpr::unary(UnaryOp::Neg, index_expr)
            } else {
                index_expr
            };
            let indexed = CExpr::Subscript {
                base: Box::new(base_cast),
                index: Box::new(index_final),
            };
            if let Some(field) = field_name {
                return Some(self.member_access_expr(indexed, field));
            }
            if effective_addr.offset_bytes == 0 {
                return Some(indexed);
            }
        }

        if effective_addr.index.is_none()
            && effective_addr.offset_bytes != 0
            && field_name.is_none()
            && !matches!(effective_addr.base, analysis::BaseRef::StackSlot(_))
            && Self::expr_is_simple_constant_offset_base(&base_expr)
        {
            let elem_ty = self.infer_elem_type_from_base_ref(&effective_addr.base, elem_size);
            let elem_bytes = elem_ty
                .bits()
                .map(|bits| bits.div_ceil(8).max(1))
                .unwrap_or(elem_size.max(1));
            if self.can_render_constant_offset_as_subscript(&elem_ty)
                && elem_bytes > 0
                && effective_addr.offset_bytes % i64::from(elem_bytes) == 0
                && self.certified_array_access_for_current_op(
                    0,
                    u64::from(elem_bytes),
                    Some(elem_size),
                    is_write,
                )
            {
                let normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
                let base_source_ty = self.expr_type_hint(&normalized_base);
                let base_cast = self.cast_expr_if_needed(
                    normalized_base,
                    CType::ptr(elem_ty),
                    base_source_ty.as_ref(),
                );
                let index = effective_addr.offset_bytes / i64::from(elem_bytes);
                let index_expr = if index < 0 {
                    CExpr::unary(UnaryOp::Neg, CExpr::IntLit(index.unsigned_abs() as i64))
                } else {
                    CExpr::IntLit(index)
                };
                return Some(CExpr::Subscript {
                    base: Box::new(base_cast),
                    index: Box::new(index_expr),
                });
            }
        }

        if let Some(field) = field_name {
            return Some(self.member_access_expr(base_expr, field));
        }

        if matches!(effective_addr.base, analysis::BaseRef::StackSlot(_))
            && effective_addr.index.is_none()
            && effective_addr.offset_bytes == 0
        {
            return Some(base_expr);
        }

        None
    }

    fn expr_is_simple_constant_offset_base(expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(_) => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_simple_constant_offset_base(inner)
            }
            _ => false,
        }
    }

    fn rewrite_pointer_arithmetic_subscript(&self, expr: CExpr) -> CExpr {
        let CExpr::Subscript { base, index } = expr else {
            return expr;
        };
        if self.literal_to_i64(&index).is_some()
            && Self::expr_is_composite_pointer_arithmetic_base(&base)
        {
            let addr = self.identity_simplify_binary(BinaryOp::Add, *base, *index, None);
            return CExpr::Deref(Box::new(addr));
        }
        CExpr::Subscript { base, index }
    }

    fn expr_is_composite_pointer_arithmetic_base(expr: &CExpr) -> bool {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                ..
            } => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_composite_pointer_arithmetic_base(inner)
            }
            _ => false,
        }
    }

    fn can_render_constant_offset_as_subscript(&self, elem_ty: &CType) -> bool {
        match elem_ty {
            CType::Unknown | CType::Void => false,
            CType::Struct(_) | CType::Union(_) => false,
            CType::Pointer(_) | CType::Array(_, _) => true,
            _ => true,
        }
    }

    fn should_render_zero_offset_load_as_subscript(
        &self,
        base_expr: &CExpr,
        elem_ty: &CType,
    ) -> bool {
        let has_subscriptable_base = match self.expr_type_hint(base_expr) {
            Some(CType::Array(_, _)) => true,
            Some(CType::Pointer(inner)) => {
                matches!(inner.as_ref(), CType::Pointer(_) | CType::Array(_, _))
            }
            _ => false,
        };
        has_subscriptable_base && self.can_render_constant_offset_as_subscript(elem_ty)
    }

    fn render_semantic_load(
        &self,
        space: r2il::SpaceId,
        addr: &analysis::NormalizedAddr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if space == r2il::SpaceId::Ram {
            return self.render_load_from_addr(addr, elem_size, depth, visited);
        }
        let address = self
            .render_address_expr_from_addr(addr, depth + 1, visited)
            .unwrap_or_else(|| CExpr::Var("r2s_unresolved_memory_address".to_string()));
        Some(CExpr::call(
            CExpr::Var("r2s_unsupported_space_load".to_string()),
            vec![
                CExpr::StringLit(space.to_string()),
                address,
                CExpr::UIntLit(u64::from(elem_size)),
            ],
        ))
    }

    fn render_load_from_addr(
        &self,
        addr: &analysis::NormalizedAddr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if let Some(index) = &addr.index
            && addr.offset_bytes >= 0
            && !matches!(addr.base, analysis::BaseRef::StackSlot(_))
            && self.certified_array_access_for_current_op(
                addr.offset_bytes,
                addr.scale_bytes
                    .unsigned_abs()
                    .max(u64::from(elem_size).max(1)),
                Some(elem_size),
                false,
            )
            && let Some(field) = self
                .oracle_field_name_for_addr(addr, Some(elem_size))
                .and_then(|field| {
                    self.certified_field_name_for_offset(
                        field,
                        addr.offset_bytes,
                        Some(elem_size),
                        false,
                    )
                })
        {
            let base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
            let mut index_expr = self.render_value_ref(index, depth + 1, visited)?;
            index_expr = self
                .normalize_index_expr(&index_expr, 0)
                .unwrap_or(index_expr);
            let elem_ty = self.infer_elem_type_from_base_ref(
                &addr.base,
                (addr.scale_bytes.unsigned_abs() as u32).max(elem_size),
            );
            let normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
            let base_source_ty = self.expr_type_hint(&normalized_base);
            let base_cast = self.cast_expr_if_needed(
                normalized_base,
                CType::ptr(elem_ty),
                base_source_ty.as_ref(),
            );
            let index_final = if addr.scale_bytes < 0 {
                CExpr::unary(UnaryOp::Neg, index_expr)
            } else {
                index_expr
            };
            let indexed = CExpr::Subscript {
                base: Box::new(base_cast),
                index: Box::new(index_final),
            };
            return Some(self.member_access_expr(indexed, field));
        }

        let direct_access = if self.allow_exact_named_object_expr_for_load_addr(addr) {
            self.render_access_expr_from_addr(addr, elem_size, false, depth, visited)
        } else if let Some(probe) = self.exact_named_object_expr_for_addr(addr) {
            let probe_base = self.render_base_ref_expr(&addr.base, false, depth + 1, visited);
            (probe_base.as_ref() != Some(&probe))
                .then(|| self.render_access_expr_from_addr(addr, elem_size, false, depth, visited))
                .flatten()
        } else {
            self.render_access_expr_from_addr(addr, elem_size, false, depth, visited)
        };

        direct_access
            .or_else(|| {
                if addr.index.is_some()
                    || addr.offset_bytes != 0
                    || matches!(addr.base, analysis::BaseRef::StackSlot(_))
                {
                    return None;
                }

                let base_expr = self.render_base_ref_expr(&addr.base, false, depth + 1, visited)?;
                let normalized_base = self.normalize_pointer_base_expr(&base_expr, 0);
                let elem_ty = self.infer_elem_type_from_base_ref(&addr.base, elem_size.max(1));
                let elem_bytes = elem_ty
                    .bits()
                    .map(|bits| bits.div_ceil(8).max(1))
                    .unwrap_or(elem_size.max(1));
                if !self.certified_array_access_for_current_op(
                    0,
                    u64::from(elem_bytes),
                    Some(elem_size),
                    false,
                ) {
                    return None;
                }
                if !self.should_render_zero_offset_load_as_subscript(&normalized_base, &elem_ty) {
                    return None;
                }
                let base_source_ty = self.expr_type_hint(&normalized_base);
                let base_cast = self.cast_expr_if_needed(
                    normalized_base,
                    CType::ptr(elem_ty),
                    base_source_ty.as_ref(),
                );
                Some(CExpr::Subscript {
                    base: Box::new(base_cast),
                    index: Box::new(CExpr::IntLit(0)),
                })
            })
            .or_else(|| {
                self.render_address_expr_from_addr(addr, depth + 1, visited)
                    .map(|expr| CExpr::Deref(Box::new(expr)))
            })
    }

    fn value_ref_from_visible_expr(&self, expr: &CExpr) -> Option<analysis::ValueRef> {
        match expr {
            CExpr::Var(name) => {
                if let Some(value_ref) = self.certified_stack_owner_value_ref_for_name(name) {
                    return Some(value_ref);
                }
                if let Some(value_ref) =
                    self.certified_current_array_index_stack_load_value_ref(name)
                {
                    return Some(value_ref);
                }
                let prefer_direct_root = Self::is_semantic_binding_name(name)
                    || self.arg_alias_for_rendered_name(name).is_some()
                    || self.lookup_type_hint(name).is_some()
                    || self
                        .certified_signature_arg_register_for_param_name(name)
                        .is_some();
                if !prefer_direct_root && self.stack_offset_for_visible_storage_name(name).is_some()
                {
                    return None;
                }
                self.ssa_var_for_visible_name(name)
                    .map(analysis::ValueRef::from)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.value_ref_from_visible_expr(inner)
            }
            _ => None,
        }
    }

    fn certified_current_array_index_stack_load_value_ref(
        &self,
        name: &str,
    ) -> Option<analysis::ValueRef> {
        return None;

        let block_addr = self.current_block_addr.get()?;
        let op_index = self.current_op_idx.get()?;
        let render_facts = self.inputs.render_facts()?;
        let has_array_proof = [false, true].into_iter().any(|is_write| {
            render_facts
                .array_accesses_by_op
                .get(&(block_addr, op_index, is_write))
                .is_some_and(|facts| !facts.is_empty())
        });
        if !has_array_proof {
            return None;
        }
        let offset = self
            .certified_stack_offset_for_visible_storage_name(name)
            .or_else(|| Self::autogenerated_stack_home_offset(name))?;
        let mut objects = render_facts
            .stack_slots()
            .filter_map(|(object, _, candidate_offset, _)| {
                (candidate_offset == offset).then_some(object)
            })
            .collect::<Vec<_>>();
        objects.sort();
        objects.dedup();
        let [object] = objects.as_slice() else {
            return None;
        };

        let latest_op_index = render_facts
            .memory_accesses()
            .filter(|fact| {
                fact.block_addr == block_addr
                    && fact.op_index < op_index
                    && !fact.is_write
                    && fact.object == *object
                    && fact.value.is_some()
            })
            .map(|fact| fact.op_index)
            .max()?;
        let mut values = render_facts
            .memory_accesses()
            .filter_map(|fact| {
                (fact.block_addr == block_addr
                    && fact.op_index == latest_op_index
                    && !fact.is_write
                    && fact.object == *object)
                    .then_some(fact.value)
                    .flatten()
            })
            .collect::<Vec<_>>();
        values.sort();
        values.dedup();
        let [value] = values.as_slice() else {
            return None;
        };
        let proof = self.certified_render_context()?;
        if !proof.expression_is_renderable(*value) {
            return None;
        }
        let var = self.prepared_ssa()?.value_var(*value)?.clone();
        Some(analysis::ValueRef::with_value_id(*value, var))
    }

    fn certified_stack_owner_value_ref_for_name(&self, name: &str) -> Option<analysis::ValueRef> {
        return None;

        let render_facts = self.inputs.render_facts()?;
        let mut objects = render_facts
            .stack_slots()
            .filter_map(|(object, _, slot_offset, _)| {
                self.certified_stack_var_name_for_object_offset(object, slot_offset)
                    .is_some_and(|owner| owner.eq_ignore_ascii_case(name))
                    .then_some(object)
            })
            .collect::<Vec<_>>();
        objects.sort();
        objects.dedup();
        let [object] = objects.as_slice() else {
            return None;
        };
        let width = render_facts
            .memory_accesses()
            .filter(|fact| fact.object == *object && !fact.is_write && fact.width > 0)
            .map(|fact| fact.width)
            .min()?;
        Some(analysis::ValueRef::new(SSAVar::new(
            name.to_string(),
            0,
            width,
        )))
    }

    fn extract_visible_scaled_index(
        &self,
        expr: &CExpr,
        depth: u32,
    ) -> Option<(analysis::ValueRef, i64)> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        match expr {
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                let (left_index, left_scale) =
                    self.extract_visible_scaled_index(left, depth + 1)?;
                let (right_index, right_scale) =
                    self.extract_visible_scaled_index(right, depth + 1)?;
                if left_index != right_index {
                    return None;
                }
                left_scale
                    .checked_add(right_scale)
                    .map(|scale| (left_index, scale))
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } if self.expr_resolves_to_visible_zero(left, depth + 1) => self
                .extract_visible_scaled_index(right, depth + 1)
                .and_then(|(index, scale)| scale.checked_neg().map(|neg| (index, neg))),
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                let (left_index, left_scale) =
                    self.extract_visible_scaled_index(left, depth + 1)?;
                let (right_index, right_scale) =
                    self.extract_visible_scaled_index(right, depth + 1)?;
                if left_index != right_index {
                    return None;
                }
                left_scale
                    .checked_sub(right_scale)
                    .map(|scale| (left_index, scale))
            }
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if let Some(scale) = self.literal_to_i64(right) {
                    return self.extract_visible_scaled_index(left, depth + 1).and_then(
                        |(index, inner_scale)| {
                            inner_scale.checked_mul(scale).map(|scaled| (index, scaled))
                        },
                    );
                }
                if let Some(scale) = self.literal_to_i64(left) {
                    return self
                        .extract_visible_scaled_index(right, depth + 1)
                        .and_then(|(index, inner_scale)| {
                            inner_scale.checked_mul(scale).map(|scaled| (index, scaled))
                        });
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Shl,
                left,
                right,
            } => {
                let shift = self.literal_to_i64(right)?;
                if !(0..=62).contains(&shift) {
                    return None;
                }
                self.extract_visible_scaled_index(left, depth + 1).and_then(
                    |(index, inner_scale)| {
                        inner_scale
                            .checked_mul(1i64 << shift)
                            .map(|scaled| (index, scaled))
                    },
                )
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.extract_visible_scaled_index(inner, depth + 1)
            }
            _ => self
                .value_ref_from_visible_expr(expr)
                .map(|index| (index, 1)),
        }
    }

    fn expr_resolves_to_visible_zero(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }

        match expr {
            CExpr::IntLit(0) | CExpr::UIntLit(0) => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.expr_resolves_to_visible_zero(inner, depth + 1)
            }
            CExpr::Binary {
                op: BinaryOp::BitXor,
                left,
                right,
            } if left == right => true,
            CExpr::Var(name) => {
                if let Some(def) = self.lookup_definition_raw(name)
                    && !matches!(&def, CExpr::Var(inner) if inner == name)
                    && self.expr_resolves_to_visible_zero(&def, depth + 1)
                {
                    return true;
                }
                if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
                    && ssa_name != *name
                    && let Some(def) = self.lookup_definition_raw(&ssa_name)
                    && self.expr_resolves_to_visible_zero(&def, depth + 1)
                {
                    return true;
                }
                false
            }
            _ => false,
        }
    }

    fn extract_visible_scaled_index_with_offset(
        &self,
        expr: &CExpr,
        depth: u32,
    ) -> Option<(analysis::ValueRef, i64, i64)> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        match expr {
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                if let Some(delta) = self.literal_to_i64(right)
                    && let Some((index, scale, offset)) =
                        self.extract_visible_scaled_index_with_offset(left, depth + 1)
                {
                    return offset
                        .checked_add(delta)
                        .map(|combined| (index, scale, combined));
                }
                if let Some(delta) = self.literal_to_i64(left)
                    && let Some((index, scale, offset)) =
                        self.extract_visible_scaled_index_with_offset(right, depth + 1)
                {
                    return offset
                        .checked_add(delta)
                        .map(|combined| (index, scale, combined));
                }
                self.extract_visible_scaled_index(expr, depth + 1)
                    .map(|(index, scale)| (index, scale, 0))
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                if let Some(delta) = self.literal_to_i64(right)
                    && let Some((index, scale, offset)) =
                        self.extract_visible_scaled_index_with_offset(left, depth + 1)
                {
                    return offset
                        .checked_sub(delta)
                        .map(|combined| (index, scale, combined));
                }
                self.extract_visible_scaled_index(expr, depth + 1)
                    .map(|(index, scale)| (index, scale, 0))
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.extract_visible_scaled_index_with_offset(inner, depth + 1)
            }
            _ => self
                .extract_visible_scaled_index(expr, depth + 1)
                .map(|(index, scale)| (index, scale, 0)),
        }
    }

    fn normalized_addr_from_visible_expr(
        &self,
        expr: &CExpr,
        depth: u32,
    ) -> Option<analysis::NormalizedAddr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.normalized_addr_from_visible_expr(inner, depth + 1)
            }
            CExpr::Deref(_) => {
                if let CExpr::Deref(inner) = expr
                    && let Some(access) = self.render_memory_access_from_visible_expr(
                        inner,
                        self.inputs.arch.ptr_size.max(1),
                        depth + 1,
                        &mut HashSet::new(),
                    )
                    && access != *expr
                    && let Some(addr) = self.normalized_addr_from_visible_expr(&access, depth + 1)
                {
                    return Some(addr);
                }
                let mut semantic_visited = HashSet::new();
                let semantic =
                    self.semanticize_visible_expr(expr, depth + 1, &mut semantic_visited);
                if semantic != *expr {
                    return self.normalized_addr_from_visible_expr(&semantic, depth + 1);
                }
                None
            }
            CExpr::Var(name) => {
                let prefer_direct_root = Self::is_semantic_binding_name(name)
                    || self.arg_alias_for_rendered_name(name).is_some()
                    || self.lookup_type_hint(name).is_some_and(|ty| {
                        matches!(
                            ty,
                            CType::Pointer(_)
                                | CType::Array(_, _)
                                | CType::Struct(_)
                                | CType::Union(_)
                        )
                    })
                    || self
                        .certified_signature_arg_register_for_param_name(name)
                        .is_some();
                if prefer_direct_root && let Some(var) = self.ssa_var_for_visible_name(name) {
                    return Some(analysis::NormalizedAddr {
                        base: analysis::BaseRef::Value(analysis::ValueRef::from(var)),
                        index: None,
                        scale_bytes: 0,
                        offset_bytes: 0,
                    });
                }
                let mut semantic_visited = HashSet::new();
                if let Some(semantic) =
                    self.render_semantic_value_by_name(name, depth + 1, &mut semantic_visited)
                    && !matches!(&semantic, CExpr::Var(inner) if inner == name)
                    && let Some(addr) = self.normalized_addr_from_visible_expr(&semantic, depth + 1)
                {
                    return Some(addr);
                }
                if let Some(def) = self
                    .lookup_definition(name)
                    .or_else(|| self.definition_for_name(name).cloned())
                    && !matches!(&def, CExpr::Var(inner) if inner == name)
                    && let Some(addr) = self.normalized_addr_from_visible_expr(&def, depth + 1)
                {
                    return Some(addr);
                }
                if self.is_named_scalar_local(name)
                    || (!self.is_low_signal_visible_name(name)
                        && !self.is_transient_visible_name(name)
                        && !is_generic_stack_placeholder_alias(name)
                        && self.stack_offset_for_visible_storage_name(name).is_some())
                {
                    return None;
                }
                if let Some(offset) = self.stack_offset_for_visible_storage_name(name) {
                    return Some(analysis::NormalizedAddr {
                        base: analysis::BaseRef::StackSlot(offset),
                        index: None,
                        scale_bytes: 0,
                        offset_bytes: 0,
                    });
                }
                if let Some(var) = self.ssa_var_for_visible_name(name) {
                    return Some(analysis::NormalizedAddr {
                        base: analysis::BaseRef::Value(analysis::ValueRef::from(var)),
                        index: None,
                        scale_bytes: 0,
                        offset_bytes: 0,
                    });
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                if let Some(delta) = self.literal_to_i64(right)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(left, depth + 1)
                {
                    addr.offset_bytes = addr.offset_bytes.saturating_add(delta);
                    return Some(addr);
                }
                if let Some(delta) = self.literal_to_i64(left)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(right, depth + 1)
                {
                    addr.offset_bytes = addr.offset_bytes.saturating_add(delta);
                    return Some(addr);
                }
                if let Some((index, scale)) = self.extract_visible_scaled_index(right, depth + 1)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(left, depth + 1)
                    && addr.index.is_none()
                {
                    addr.index = Some(index);
                    addr.scale_bytes = scale;
                    return Some(addr);
                }
                if let Some((index, scale, offset)) =
                    self.extract_visible_scaled_index_with_offset(right, depth + 1)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(left, depth + 1)
                    && addr.index.is_none()
                {
                    addr.index = Some(index);
                    addr.scale_bytes = scale;
                    addr.offset_bytes = addr.offset_bytes.saturating_add(offset);
                    return Some(addr);
                }
                if let Some((index, scale)) = self.extract_visible_scaled_index(left, depth + 1)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(right, depth + 1)
                    && addr.index.is_none()
                {
                    addr.index = Some(index);
                    addr.scale_bytes = scale;
                    return Some(addr);
                }
                if let Some((index, scale, offset)) =
                    self.extract_visible_scaled_index_with_offset(left, depth + 1)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(right, depth + 1)
                    && addr.index.is_none()
                {
                    addr.index = Some(index);
                    addr.scale_bytes = scale;
                    addr.offset_bytes = addr.offset_bytes.saturating_add(offset);
                    return Some(addr);
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                if let Some(delta) = self.literal_to_i64(right)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(left, depth + 1)
                {
                    addr.offset_bytes = addr.offset_bytes.saturating_sub(delta);
                    return Some(addr);
                }
                if let Some((index, scale)) = self.extract_visible_scaled_index(right, depth + 1)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(left, depth + 1)
                    && addr.index.is_none()
                {
                    addr.index = Some(index);
                    addr.scale_bytes = scale.saturating_neg();
                    return Some(addr);
                }
                if let Some((index, scale, offset)) =
                    self.extract_visible_scaled_index_with_offset(right, depth + 1)
                    && let Some(mut addr) = self.normalized_addr_from_visible_expr(left, depth + 1)
                    && addr.index.is_none()
                {
                    addr.index = Some(index);
                    addr.scale_bytes = scale.saturating_neg();
                    addr.offset_bytes = addr.offset_bytes.saturating_sub(offset);
                    return Some(addr);
                }
                None
            }
            _ => None,
        }
    }

    fn render_memory_access_by_name(
        &self,
        name: &str,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let value = self.lookup_semantic_value(name)?;
        match value {
            analysis::SemanticValue::Load { space, addr, size } => {
                self.render_semantic_load(*space, addr, *size, depth, visited)
            }
            analysis::SemanticValue::Address(shape) => {
                self.render_load_from_addr(shape, elem_size, depth, visited)
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Expr(expr)) => {
                Some(expr.clone())
            }
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(value_ref)) => {
                self.render_value_ref(value_ref, depth, visited)
            }
            analysis::SemanticValue::Unknown => None,
        }
    }

    fn render_exact_member_from_raw_subscript(
        &self,
        base: &CExpr,
        index: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        let subscript_index = self.literal_to_i64(index)?;
        if subscript_index <= 0 {
            return None;
        }
        let mut addr = self.normalized_addr_from_visible_expr(base, depth + 1)?;
        if addr.offset_bytes < 0 {
            return None;
        }

        let aggregate_ty =
            self.infer_elem_type_from_base_ref(&addr.base, addr.scale_bytes.unsigned_abs() as u32);
        let base_offset = u64::try_from(addr.offset_bytes).ok()?;
        let index = u64::try_from(subscript_index).ok()?;
        let mut widths = BTreeSet::from([1_u32, 2, 4, 8, 16]);
        widths.insert(self.inputs.arch.ptr_size.max(1));
        let mut candidates = widths
            .into_iter()
            .filter_map(|width| {
                let field_offset = base_offset.checked_add(index.checked_mul(u64::from(width))?)?;
                if self.exact_field_offset_is_pointer(&aggregate_ty, field_offset) {
                    return None;
                }
                let field = self
                    .exact_field_name_from_type_hint(&aggregate_ty, field_offset, width)
                    .or_else(|| {
                        let mut field_addr = addr.clone();
                        field_addr.offset_bytes = i64::try_from(field_offset).ok()?;
                        self.exact_oracle_field_name_for_addr(&field_addr, field_offset)
                    })?;
                Some((field_offset, width, field))
            })
            .collect::<Vec<_>>();
        candidates.sort();
        candidates.dedup();
        let [(field_offset, access_size, _)] = candidates.as_slice() else {
            return None;
        };
        addr.offset_bytes = i64::try_from(*field_offset).ok()?;
        self.render_access_expr_from_addr(&addr, *access_size, false, depth + 1, visited)
            .filter(Self::expr_is_structured_memory_candidate)
    }

    fn infer_elem_type_from_base_ref(&self, base: &analysis::BaseRef, element_size: u32) -> CType {
        match base {
            analysis::BaseRef::Value(base_ref) => {
                if let Some(CType::Pointer(inner) | CType::Array(inner, _)) =
                    self.type_hint_for_var(&base_ref.var)
                {
                    return *inner;
                }
                if let Some(oracle) = self.inputs.type_oracle {
                    let mut visited = HashSet::new();
                    if let Some(root) = self.semantic_root_var(&base_ref.var, 0, &mut visited) {
                        if let Some(CType::Pointer(inner) | CType::Array(inner, _)) =
                            self.type_hint_for_var(&root)
                        {
                            return *inner;
                        }
                        let ty = oracle.type_of(&root);
                        if (oracle.is_array(ty) || oracle.is_pointer(ty))
                            && let Some(CType::Pointer(inner) | CType::Array(inner, _)) =
                                self.type_hint_for_var(&root)
                        {
                            return *inner;
                        }
                    }
                }
                self.infer_subscript_elem_type(&base_ref.var, element_size)
            }
            analysis::BaseRef::Raw(CExpr::Var(name)) => self
                .lookup_type_hint(name)
                .and_then(|ty| match ty {
                    CType::Pointer(inner) | CType::Array(inner, _) => Some((**inner).clone()),
                    _ => None,
                })
                .unwrap_or_else(|| uint_type_from_size(element_size)),
            analysis::BaseRef::StackSlot(_) | analysis::BaseRef::Raw(_) => {
                uint_type_from_size(element_size)
            }
        }
    }

    fn guess_ssa_var_from_name(&self, name: &str) -> Option<SSAVar> {
        if self.stack_offset_for_visible_storage_name(name).is_some() {
            return None;
        }
        let (base, version) = name.rsplit_once('_')?;
        let version = version.parse::<u32>().ok()?;
        let base = base.to_ascii_lowercase();
        let size = self
            .lookup_type_hint(name)
            .and_then(|ty| ty.bits())
            .map(|bits| bits.div_ceil(8))
            .filter(|bytes| *bytes > 0)
            .unwrap_or(self.inputs.arch.ptr_size);
        Some(SSAVar::new(base, version, size))
    }

    fn ssa_var_for_visible_name(&self, name: &str) -> Option<SSAVar> {
        let prefer_direct_root = Self::is_semantic_binding_name(name)
            || self.arg_alias_for_rendered_name(name).is_some()
            || self.lookup_type_hint(name).is_some()
            || self
                .certified_signature_arg_register_for_param_name(name)
                .is_some();
        if !prefer_direct_root && self.stack_offset_for_visible_storage_name(name).is_some() {
            return None;
        }

        let infer_reg_size = |reg_name: &str| -> u32 {
            let lower = reg_name.to_ascii_lowercase();
            if let Some(ty) = self.lookup_type_hint(name)
                && let Some(bits) = ty.bits()
            {
                return bits.div_ceil(8).max(1);
            }
            if matches!(
                lower.as_str(),
                "eax" | "ebx" | "ecx" | "edx" | "esi" | "edi" | "ebp" | "esp" | "eip"
            ) || (lower.starts_with('w') && lower[1..].chars().all(|ch| ch.is_ascii_digit()))
            {
                return 4;
            }
            self.inputs.arch.ptr_size
        };

        let semantic_var = |value: &analysis::SemanticValue| match value {
            analysis::SemanticValue::Scalar(analysis::ScalarValue::Root(root)) => {
                Some(root.var.clone())
            }
            analysis::SemanticValue::Address(analysis::NormalizedAddr {
                base: analysis::BaseRef::Value(root),
                index: None,
                scale_bytes,
                offset_bytes,
            }) if *scale_bytes == 0 && *offset_bytes == 0 => Some(root.var.clone()),
            analysis::SemanticValue::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            } => match &addr.base {
                analysis::BaseRef::Value(root) => Some(root.var.clone()),
                _ => None,
            },
            _ => None,
        };

        for (reg_name, alias) in self.inputs.param_register_aliases {
            if alias.eq_ignore_ascii_case(name) {
                let reg_name = self.canonical_arg_register_name_for_alias(reg_name);
                return Some(SSAVar::new(reg_name.clone(), 0, infer_reg_size(&reg_name)));
            }
        }

        if let Some(reg_name) = self.certified_signature_arg_register_for_param_name(name) {
            return Some(SSAVar::new(reg_name, 0, infer_reg_size(reg_name)));
        }

        if let Some(rest) = name.strip_prefix("arg")
            && let Ok(idx) = rest.parse::<usize>()
            && idx > 0
            && let Some(reg_name) = self.inputs.arch.arg_regs.get(idx - 1)
        {
            return Some(SSAVar::new(reg_name, 0, infer_reg_size(reg_name)));
        }

        if let Some(value) = self.lookup_semantic_value(name)
            && let Some(var) = semantic_var(value)
        {
            return Some(var);
        }

        if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name) {
            if let Some(value) = self.lookup_semantic_value(&ssa_name)
                && let Some(var) = semantic_var(value)
            {
                return Some(var);
            }
            if let Some(prov) = self.forwarded_value_for_name(&ssa_name)
                && let Some(var) = &prov.source_var
            {
                return Some(var.clone());
            }
            if let Some(var) = self.guess_ssa_var_from_name(&ssa_name) {
                return Some(var);
            }
        }

        if let Some(prov) = self.forwarded_value_for_name(name)
            && let Some(var) = &prov.source_var
        {
            return Some(var.clone());
        }
        self.guess_ssa_var_from_name(name)
    }

    pub(super) fn canonical_arg_register_name_for_alias(&self, reg_name: &str) -> String {
        self.inputs
            .arch
            .arg_regs
            .iter()
            .find(|arg_reg| {
                arg_reg.eq_ignore_ascii_case(reg_name)
                    || crate::register_alias_names(arg_reg)
                        .into_iter()
                        .any(|alias| alias.eq_ignore_ascii_case(reg_name))
            })
            .cloned()
            .unwrap_or_else(|| reg_name.to_string())
    }

    fn certified_signature_arg_register_for_param_name(&self, name: &str) -> Option<&str> {
        return None;

        let signature = self
            .inputs
            .function_facts
            .type_facts()
            .render_authorized_signature()?;
        let (idx, _) = signature
            .params
            .iter()
            .enumerate()
            .find(|(_, param)| param.name.eq_ignore_ascii_case(name))?;
        self.inputs.arch.arg_regs.get(idx).map(String::as_str)
    }

    fn infer_subscript_elem_type(&self, base: &SSAVar, element_size: u32) -> CType {
        if let Some(oracle) = self.inputs.type_oracle {
            let base_ty = oracle.type_of(base);
            if (oracle.is_array(base_ty) || oracle.is_pointer(base_ty))
                && let Some(hint) = self.type_hint_for_var(base)
            {
                match hint {
                    CType::Pointer(inner) | CType::Array(inner, _) => return *inner,
                    _ => {}
                }
            }
        }
        uint_type_from_size(element_size)
    }

    fn oracle_member_name(
        &self,
        addr: Option<&SSAVar>,
        base_expr: &CExpr,
        offset: i64,
    ) -> Option<String> {
        if offset < 0 {
            return None;
        }
        let offset = offset as u64;

        if let Some(name) = self.visible_pointer_root_field_name(base_expr, offset, None, 0) {
            return Some(name);
        }

        // Best-effort: prefer base pointer identities captured during analysis.
        if let Some(addr) = addr
            && let Some((base, mapped_offset)) = self.ptr_members_map().get(&addr.display_name())
            && *mapped_offset == offset as i64
        {
            if let Some(oracle) = self.inputs.type_oracle {
                let base_ty = oracle.type_of(base);
                if let Some(name) = oracle.field_name(base_ty, offset) {
                    return Some(name.to_string());
                }
            }
            if let Some(name) = self.field_name_from_type_hint_for_var(base, offset, None) {
                return Some(name);
            }
        }

        if let Some(addr) = addr
            && offset == 0
            && let Some(name) = self
                .inputs
                .type_oracle
                .and_then(|oracle| oracle.field_name(oracle.type_of(addr), offset))
        {
            return Some(name.to_string());
        }

        if let CExpr::Var(base_name) = base_expr
            && self
                .stack_offset_for_visible_storage_name(base_name)
                .is_none()
            && let Some((reg_name, _)) = self
                .inputs
                .param_register_aliases
                .iter()
                .find(|(_, alias)| alias.eq_ignore_ascii_case(base_name))
        {
            let base_var = SSAVar::new(reg_name, 0, self.inputs.arch.ptr_size);
            if let Some(name) = self
                .inputs
                .type_oracle
                .and_then(|oracle| oracle.field_name(oracle.type_of(&base_var), offset))
            {
                return Some(name.to_string());
            }
            if let Some(name) = self.field_name_from_type_hint_for_var(&base_var, offset, None) {
                return Some(name);
            }
        }

        if let CExpr::Var(base_name) = base_expr
            && self
                .stack_offset_for_visible_storage_name(base_name)
                .is_none()
            && let Some(base_var) = self.ssa_var_for_visible_name(base_name)
        {
            if let Some(name) = self
                .inputs
                .type_oracle
                .and_then(|oracle| oracle.field_name(oracle.type_of(&base_var), offset))
            {
                return Some(name.to_string());
            }
            if let Some(name) = self.field_name_from_type_hint_for_var(&base_var, offset, None) {
                return Some(name);
            }
        }

        if let CExpr::Var(base_name) = base_expr {
            for (base, mapped_offset) in self.ptr_members_map().values() {
                if *mapped_offset != offset as i64 {
                    continue;
                }
                if self.var_name(base) != *base_name {
                    continue;
                }
                if let Some(oracle) = self.inputs.type_oracle {
                    let base_ty = oracle.type_of(base);
                    if let Some(name) = oracle.field_name(base_ty, offset) {
                        return Some(name.to_string());
                    }
                }
                if let Some(name) = self.field_name_from_type_hint_for_var(base, offset, None) {
                    return Some(name);
                }
            }
        }

        None
    }

    fn visible_pointer_root_field_name(
        &self,
        expr: &CExpr,
        offset: u64,
        access_size: Option<u32>,
        depth: u32,
    ) -> Option<String> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        match expr {
            CExpr::Var(name) if self.stack_offset_for_visible_storage_name(name).is_none() => {
                if let Some(hint) = self.lookup_type_hint(name)
                    && matches!(hint, CType::Pointer(_) | CType::Array(_, _))
                    && let Some(field) = self.field_name_from_type_hint(hint, offset, access_size)
                {
                    return Some(field);
                }
                if let Some((reg_name, _)) = self
                    .inputs
                    .param_register_aliases
                    .iter()
                    .find(|(_, alias)| alias.eq_ignore_ascii_case(name))
                {
                    let base_var = SSAVar::new(reg_name, 0, self.inputs.arch.ptr_size);
                    if let Some(field) =
                        self.field_name_from_type_hint_for_var(&base_var, offset, access_size)
                    {
                        return Some(field);
                    }
                    if let Some(field) = self
                        .inputs
                        .type_oracle
                        .and_then(|oracle| oracle.field_name(oracle.type_of(&base_var), offset))
                    {
                        return Some(field.to_string());
                    }
                }
                if let Some(base_var) = self.ssa_var_for_visible_name(name) {
                    if let Some(field) =
                        self.field_name_from_type_hint_for_var(&base_var, offset, access_size)
                    {
                        return Some(field);
                    }
                    if let Some(field) = self
                        .inputs
                        .type_oracle
                        .and_then(|oracle| oracle.field_name(oracle.type_of(&base_var), offset))
                    {
                        return Some(field.to_string());
                    }
                }

                if let Some(def) = self
                    .lookup_definition(name)
                    .or_else(|| self.definition_for_name(name).cloned())
                    .or_else(|| self.best_visible_definition(name))
                    && !matches!(&def, CExpr::Var(inner) if inner.eq_ignore_ascii_case(name))
                    && let Some(field) =
                        self.visible_pointer_root_field_name(&def, offset, access_size, depth + 1)
                {
                    return Some(field);
                }

                let root_name = self.resolve_copy_root_name_in_fold(name);
                if !root_name.eq_ignore_ascii_case(name)
                    && let Some(field) = self.visible_pointer_root_field_name(
                        &CExpr::Var(root_name),
                        offset,
                        access_size,
                        depth + 1,
                    )
                {
                    return Some(field);
                }
                None
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.visible_pointer_root_field_name(inner, offset, access_size, depth + 1)
            }
            CExpr::Binary { left, right, .. } => self
                .visible_pointer_root_field_name(left, offset, access_size, depth + 1)
                .or_else(|| {
                    self.visible_pointer_root_field_name(right, offset, access_size, depth + 1)
                }),
            CExpr::Subscript { base, .. }
            | CExpr::Member { base, .. }
            | CExpr::PtrMember { base, .. } => {
                self.visible_pointer_root_field_name(base, offset, access_size, depth + 1)
            }
            CExpr::Deref(inner) | CExpr::AddrOf(inner) | CExpr::Sizeof(inner) => {
                self.visible_pointer_root_field_name(inner, offset, access_size, depth + 1)
            }
            CExpr::Unary { operand, .. } => {
                self.visible_pointer_root_field_name(operand, offset, access_size, depth + 1)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => self
                .visible_pointer_root_field_name(cond, offset, access_size, depth + 1)
                .or_else(|| {
                    self.visible_pointer_root_field_name(then_expr, offset, access_size, depth + 1)
                })
                .or_else(|| {
                    self.visible_pointer_root_field_name(else_expr, offset, access_size, depth + 1)
                }),
            CExpr::Comma(items) => items.iter().find_map(|item| {
                self.visible_pointer_root_field_name(item, offset, access_size, depth + 1)
            }),
            _ => None,
        }
    }

    pub(crate) fn stack_offset_for_visible_storage_name(&self, name: &str) -> Option<i64> {
        let lower = name.to_ascii_lowercase();
        if lower == "stack" {
            return Some(0);
        }
        if lower == "saved_fp" {
            return Some(0);
        }
        if let Some(rest) = lower.strip_prefix("stack_")
            && let Ok(offset) = i64::from_str_radix(rest, 16)
        {
            return Some(offset);
        }
        if let Some(rest) = lower.strip_prefix("local_")
            && let Ok(offset) = i64::from_str_radix(rest, 16)
        {
            return Some(-offset);
        }
        if let Some(rest) = lower.strip_prefix("arg_")
            && let Ok(offset) = i64::from_str_radix(rest, 16)
        {
            return Some(-offset);
        }
        if let Some((offset, _)) = self
            .stack_vars_map()
            .iter()
            .find(|(_, candidate)| candidate.eq_ignore_ascii_case(name))
        {
            return Some(*offset);
        }
        self.canonical_stack_offset_for_visible_storage_name(name)
    }

    fn certified_stack_offset_for_visible_storage_name(&self, name: &str) -> Option<i64> {
        let offset = self.canonical_stack_offset_for_visible_storage_name(name)?;
        self.inputs
            .function_facts
            .authorized_stack_slot_owner_render_by_offset(offset, name)
            .map(|authorization| authorization.offset)
    }

    fn canonical_stack_offset_for_visible_storage_name(&self, name: &str) -> Option<i64> {
        if let Some(offset) = self
            .inputs
            .visible_bindings
            .iter()
            .find(|binding| binding.name.eq_ignore_ascii_case(name))
            .and_then(|binding| binding.stack_slot.as_ref())
            .map(|slot| match slot.base {
                ExternalStackBase::FramePointer => -slot.offset,
                _ => slot.offset,
            })
        {
            return Some(offset);
        }
        if let Some(offset) = self
            .inputs
            .stack_slots
            .iter()
            .find(|(_, var)| var.name.eq_ignore_ascii_case(name))
            .map(|(slot_key, _)| match slot_key.base {
                ExternalStackBase::FramePointer => -slot_key.offset,
                _ => slot_key.offset,
            })
        {
            return Some(offset);
        }
        None
    }

    fn stack_offsets_for_visible_storage_name(&self, name: &str) -> Vec<i64> {
        let mut offsets = Vec::new();
        if let Some(offset) = self.stack_offset_for_visible_storage_name(name) {
            offsets.push(offset);
        }

        if let Some(offset) = self.canonical_stack_offset_for_visible_storage_name(name)
            && !offsets.contains(&offset)
        {
            offsets.push(offset);
        }
        offsets
    }

    fn looks_like_pointer(&self, expr: &CExpr) -> bool {
        if self.expr_type_hint(expr).is_some_and(|ty| {
            matches!(
                ty,
                CType::Pointer(_) | CType::Array(_, _) | CType::Struct(_) | CType::Union(_)
            )
        }) {
            return true;
        }

        match expr {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_) => true,
            CExpr::Subscript { .. } | CExpr::Member { .. } | CExpr::PtrMember { .. } => true,
            CExpr::Var(name) => {
                if name.starts_with("arg") || name.contains("ptr") {
                    return true;
                }
                if let Some(ty) = self.lookup_type_hint(name) {
                    return matches!(ty, CType::Pointer(_) | CType::Struct(_));
                }
                false
            }
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => self.looks_like_pointer(left) || self.looks_like_pointer(right),
            _ => false,
        }
    }

    fn normalize_pointer_base_expr(&self, expr: &CExpr, depth: u32) -> CExpr {
        if depth > 4 {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => self
                .lookup_definition(name)
                .map(|inner| self.normalize_pointer_base_expr(&inner, depth + 1))
                .filter(|inner| self.looks_like_pointer(inner))
                .unwrap_or_else(|| expr.clone()),
            CExpr::Paren(inner) => {
                CExpr::Paren(Box::new(self.normalize_pointer_base_expr(inner, depth + 1)))
            }
            CExpr::Cast { ty, expr: inner } => CExpr::Cast {
                ty: ty.clone(),
                expr: Box::new(self.normalize_pointer_base_expr(inner, depth + 1)),
            },
            _ => expr.clone(),
        }
    }

    fn should_swap_indexed_access_base(&self, base_expr: &CExpr, index_expr: &CExpr) -> bool {
        let base_pointer =
            self.looks_like_pointer(base_expr) || self.is_non_index_pointer_expr(base_expr);
        let index_pointer =
            self.looks_like_pointer(index_expr) || self.is_non_index_pointer_expr(index_expr);
        !base_pointer && index_pointer
    }

    fn normalize_index_expr(&self, expr: &CExpr, depth: u32) -> Option<CExpr> {
        if depth > 4 {
            return self.is_semantic_index_expr(expr).then_some(expr.clone());
        }

        match expr {
            CExpr::Var(name) => {
                let resolved_definition = self
                    .lookup_definition(name)
                    .or_else(|| self.best_visible_definition(name))
                    .or_else(|| {
                        self.find_ssa_name_for_rendered_alias(name)
                            .and_then(|ssa_name| {
                                self.lookup_definition(&ssa_name)
                                    .or_else(|| self.best_visible_definition(&ssa_name))
                            })
                    });
                if !self.is_low_signal_visible_name(name)
                    && !self.is_transient_visible_name(name)
                    && !self.is_non_index_pointer_expr(expr)
                    && self.is_semantic_index_expr(expr)
                {
                    return Some(expr.clone());
                }
                if let Some(inner) = resolved_definition
                    && let Some(normalized) = self.normalize_index_expr(&inner, depth + 1)
                    && !self.is_non_index_pointer_expr(&normalized)
                {
                    return Some(normalized);
                }
                if self.lookup_definition(name).is_some()
                    || self.best_visible_definition(name).is_some()
                    || self.find_ssa_name_for_rendered_alias(name).is_some()
                {
                    return None;
                }
                if self.is_non_index_pointer_expr(expr) {
                    None
                } else {
                    self.is_semantic_index_expr(expr).then_some(expr.clone())
                }
            }
            CExpr::Paren(inner) => self
                .normalize_index_expr(inner, depth + 1)
                .map(|normalized| CExpr::Paren(Box::new(normalized))),
            CExpr::Cast { ty, expr: inner } => self
                .normalize_index_expr(inner, depth + 1)
                .map(|normalized| CExpr::cast(ty.clone(), normalized)),
            CExpr::Unary { op, operand } => self
                .normalize_index_expr(operand, depth + 1)
                .map(|normalized| CExpr::unary(*op, normalized)),
            _ => self.is_semantic_index_expr(expr).then_some(expr.clone()),
        }
    }

    fn is_semantic_index_expr(&self, expr: &CExpr) -> bool {
        self.is_semantic_index_expr_with_depth(expr, 0, &mut HashSet::new())
    }

    fn is_semantic_index_expr_with_depth(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> bool {
        if depth > MAX_SIMPLE_EXPR_DEPTH {
            return false;
        }
        match expr {
            CExpr::Var(name) => {
                let visit_key = format!("index:{}", name.to_ascii_lowercase());
                if !visited.insert(visit_key.clone()) {
                    return false;
                }
                if let Some(inner) = self.direct_definition_expr(name)
                    && inner != *expr
                    && self.is_semantic_index_expr_with_depth(&inner, depth + 1, visited)
                {
                    visited.remove(&visit_key);
                    return true;
                }
                let lower = name.to_ascii_lowercase();
                let name_kind = SSAVarNameKind::classify(name);
                let stack_placeholder =
                    lower == "stack" || lower == "saved_fp" || lower.starts_with("stack_");
                let result = !name_kind.is_constant()
                    && !name_kind.is_memory()
                    && !stack_placeholder
                    && (self.is_static_param_home_alias_name(name)
                        || self.stack_slot_provenance_for_name(name).is_none()
                        || lower.starts_with("local_")
                        || lower.starts_with("arg"));
                visited.remove(&visit_key);
                result
            }
            CExpr::Unary { operand, .. } => {
                self.is_semantic_index_expr_with_depth(operand, depth + 1, visited)
            }
            CExpr::Binary { left, right, .. } => {
                self.is_semantic_index_expr_with_depth(left, depth + 1, visited)
                    || self.is_semantic_index_expr_with_depth(right, depth + 1, visited)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_semantic_index_expr_with_depth(inner, depth + 1, visited)
            }
            _ => false,
        }
    }

    fn is_non_index_pointer_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_) | CExpr::Subscript { .. } | CExpr::PtrMember { .. } => true,
            CExpr::Var(name) => {
                let lower = name.to_ascii_lowercase();
                lower.contains("ptr")
                    || lower.contains("addr")
                    || self
                        .stack_slot_provenance_for_name(name)
                        .is_some_and(analysis::StackSlotProvenance::is_address_like)
                    || self
                        .lookup_type_hint(name)
                        .map(|ty| matches!(ty, CType::Pointer(_) | CType::Struct(_)))
                        .unwrap_or(false)
            }
            CExpr::Paren(inner) => self.is_non_index_pointer_expr(inner),
            CExpr::Unary { operand, .. } => self.is_non_index_pointer_expr(operand),
            _ => false,
        }
    }

    fn member_access_expr(&self, base_expr: CExpr, member: String) -> CExpr {
        let base_expr = self.canonical_member_base_expr(base_expr);
        match base_expr {
            CExpr::Subscript { .. } | CExpr::Member { .. } => CExpr::Member {
                base: Box::new(base_expr),
                member,
            },
            _ => CExpr::PtrMember {
                base: Box::new(base_expr),
                member,
            },
        }
    }

    fn canonical_member_base_expr(&self, base_expr: CExpr) -> CExpr {
        match base_expr {
            CExpr::Var(name) => {
                let (base, version) = Self::ssa_name_parts(&name);
                if version > 0
                    && !base.is_empty()
                    && let Some(base_ty) = self.lookup_type_hint(base)
                    && matches!(
                        base_ty,
                        CType::Pointer(_) | CType::Array(_, _) | CType::Struct(_) | CType::Union(_)
                    )
                    && self
                        .expr_type_hint(&CExpr::Var(name.clone()))
                        .is_some_and(|ty| {
                            matches!(
                                ty,
                                CType::Pointer(_)
                                    | CType::Array(_, _)
                                    | CType::Struct(_)
                                    | CType::Union(_)
                            )
                        })
                {
                    return CExpr::Var(base.to_string());
                }
                CExpr::Var(name)
            }
            other => other,
        }
    }

    fn lookup_type_hint(&self, name: &str) -> Option<&CType> {
        if let Some(ty) = self.type_hints_map().get(name) {
            return Some(ty);
        }
        let lower = name.to_lowercase();
        self.type_hints_map().get(&lower)
    }

    fn type_hint_for_var(&self, var: &SSAVar) -> Option<CType> {
        let display = var.display_name();
        if let Some(ty) = self.lookup_type_hint(&display) {
            return Some(ty.clone());
        }

        if var.version > 0
            && let Some(ty) = self.lookup_type_hint(&var.name)
        {
            return Some(ty.clone());
        }

        if let Some(alias) = self
            .inputs
            .param_register_aliases
            .get(&var.name.to_ascii_lowercase())
            && let Some(ty) = self.lookup_type_hint(alias)
        {
            return Some(ty.clone());
        }

        let rendered = self.var_name(var);
        self.lookup_type_hint(&rendered).cloned()
    }

    pub(super) fn stack_slot_provenance_for_name(
        &self,
        name: &str,
    ) -> Option<analysis::StackSlotProvenance> {
        let provenance = self
            .use_info()
            .render_stack_slot_for_name(name)
            .or_else(|| {
                self.find_ssa_name_for_rendered_alias(name)
                    .and_then(|ssa_name| self.use_info().render_stack_slot_for_name(&ssa_name))
            })?;

        Some(provenance)
    }

    pub(super) fn stack_slot_provenance_for_var(
        &self,
        var: &SSAVar,
    ) -> Option<analysis::StackSlotProvenance> {
        self.stack_slot_provenance_for_name(&var.display_name())
    }

    fn scalar_context_root_candidate_for_name(
        &self,
        name: &str,
        context: VisibleExprContext,
    ) -> Option<CExpr> {
        if !matches!(
            context,
            VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
        ) {
            return None;
        }

        let stack_offset_for_name = |ctx: &FoldingContext<'_>, name: &str| {
            ctx.forwarded_value_for_name(name)
                .and_then(|prov| prov.stack_slot)
                .or_else(|| {
                    ctx.stack_slot_provenance_for_name(name)
                        .map(|slot| slot.offset)
                })
                .or_else(|| ctx.stack_offset_for_visible_storage_name(name))
        };

        let stable_scalar_expr_for_offset = |ctx: &FoldingContext<'_>, offset: i64| {
            (offset < 0)
                .then(|| ctx.stable_stack_value_for_offset(offset))
                .flatten()
                .filter(|value| matches!(value, analysis::SemanticValue::Scalar(_)))
                .and_then(|value| ctx.render_semantic_value(value, 0, &mut HashSet::new()))
        };

        let scalar_stack_expr_for_offset = |ctx: &FoldingContext<'_>, offset: i64| {
            let stable = stable_scalar_expr_for_offset(ctx, offset)
                .filter(|candidate| !ctx.expr_is_address_artifact_in_scalar_context(candidate));
            if stable
                .as_ref()
                .is_some_and(|expr| !ctx.expr_is_autogenerated_stack_home_expr(expr))
            {
                return stable;
            }
            ctx.param_home_alias_for_stack_offset(offset)
                .map(CExpr::Var)
                .or(stable)
        };

        if let Some(offset) = stack_offset_for_name(self, name)
            && let Some(candidate) = scalar_stack_expr_for_offset(self, offset)
        {
            return Some(candidate);
        }

        let root_name = self.resolve_copy_root_name_in_fold(name);
        if root_name == name {
            return None;
        }

        if let Some(offset) = stack_offset_for_name(self, &root_name)
            && let Some(candidate) = scalar_stack_expr_for_offset(self, offset)
        {
            return Some(candidate);
        }

        let unresolved_root = self
            .guess_ssa_var_from_name(&root_name)
            .map(|var| CExpr::Var(self.var_name(&var)))
            .or_else(|| Some(self.expr_for_ssa_fallback_name(&root_name)));
        let semantic_root = self
            .render_semantic_value_by_name(&root_name, 0, &mut HashSet::new())
            .filter(|candidate| !self.expr_is_address_artifact_in_scalar_context(candidate));
        self.choose_preferred_visible_expr_in_context(unresolved_root, semantic_root, context)
            .filter(|candidate| !self.expr_is_address_artifact_in_scalar_context(candidate))
    }

    fn is_autogenerated_stack_home_name(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        let has_hexish_suffix = |prefix: &str| {
            lower.strip_prefix(prefix).is_some_and(|suffix| {
                !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_hexdigit() || ch == 'h')
            })
        };
        lower == "saved_fp"
            || lower.starts_with("stack_")
            || has_hexish_suffix("local_")
            || has_hexish_suffix("var_")
    }

    fn is_static_param_home_alias_name(&self, name: &str) -> bool {
        let normalized = name.trim();
        !normalized.is_empty()
            && self.inputs.stack_slots.iter().any(|(_, slot)| {
                matches!(slot.role, ExternalStackSlotRole::ParamHome)
                    && (slot
                        .param_name
                        .as_deref()
                        .map(str::trim)
                        .is_some_and(|param_name| param_name.eq_ignore_ascii_case(normalized))
                        || slot
                            .source_reg
                            .as_deref()
                            .and_then(|reg| self.arg_alias_for_register_name(reg))
                            .is_some_and(|alias| alias.eq_ignore_ascii_case(normalized)))
            })
    }

    fn autogenerated_stack_home_offset(name: &str) -> Option<i64> {
        let lower = name.to_ascii_lowercase();
        if lower == "saved_fp" {
            return Some(0);
        }
        let parse_hex = |raw: &str| {
            let suffix = raw.strip_suffix('h').unwrap_or(raw);
            (!suffix.is_empty())
                .then(|| i64::from_str_radix(suffix, 16).ok())
                .flatten()
        };
        if let Some(suffix) = lower.strip_prefix("local_") {
            return parse_hex(suffix).map(|offset| -offset);
        }
        if let Some(suffix) = lower.strip_prefix("var_") {
            return parse_hex(suffix).map(|offset| -offset);
        }
        if let Some(suffix) = lower.strip_prefix("arg_") {
            return parse_hex(suffix).map(|offset| -offset);
        }
        if let Some(suffix) = lower.strip_prefix("stack_") {
            return parse_hex(suffix);
        }
        None
    }

    fn certified_autogenerated_stack_storage_offset(&self, name: &str) -> Option<i64> {
        return None;

        let offset = Self::autogenerated_stack_home_offset(name)?;
        let render_facts = self.inputs.render_facts()?;
        let mut objects = render_facts
            .stack_slots()
            .filter_map(|(object, _, candidate_offset, _)| {
                (candidate_offset == offset).then_some(object)
            })
            .collect::<Vec<_>>();
        objects.sort();
        objects.dedup();
        let [object] = objects.as_slice() else {
            return None;
        };
        render_facts
            .memory_accesses()
            .any(|fact| fact.object == *object)
            .then_some(offset)
    }

    fn expr_is_autogenerated_stack_home_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => self.is_autogenerated_stack_home_name(name),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.expr_is_autogenerated_stack_home_expr(inner)
            }
            _ => false,
        }
    }

    fn is_named_scalar_local(&self, name: &str) -> bool {
        (self.stack_slot_provenance_for_name(name).is_some()
            || self
                .stack_offset_for_visible_storage_name(name)
                .is_some_and(|offset| offset < 0))
            && !self.is_autogenerated_stack_home_name(name)
            && !self.is_low_signal_visible_name(name)
            && !self.is_transient_visible_name(name)
    }

    pub(super) fn is_generic_stack_local_owner_name(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        (self
            .stack_slot_provenance_for_name(name)
            .is_some_and(|slot| slot.offset < 0)
            || self
                .stack_offset_for_visible_storage_name(name)
                .is_some_and(|offset| offset < 0))
            && !self.is_transient_visible_name(name)
            && !is_generic_stack_placeholder_alias(name)
            && lower != "saved_fp"
            && !lower.starts_with("stack_")
    }

    fn rendered_visible_name_for_ssa_name(&self, ssa_name: &str) -> String {
        self.var_aliases_map()
            .get(ssa_name)
            .and_then(|alias| {
                self.canonicalize_stack_name(alias)
                    .or_else(|| Some(alias.clone()))
            })
            .or_else(|| self.canonicalize_stack_name(ssa_name))
            .unwrap_or_else(|| ssa_name.to_string())
    }

    fn derive_stable_owned_call_result_name_for_alias(&self, alias: &str) -> Option<String> {
        let mut candidates = Vec::new();
        let alias_base = alias
            .split('_')
            .next()
            .map(|base| base.to_ascii_lowercase())
            .unwrap_or_else(|| alias.to_ascii_lowercase());
        let alias_is_register_like = self.inputs.arch.is_register_like_base_name(&alias_base);

        if !alias_is_register_like {
            if let Some(name) = Self::meaningful_tmp_call_owner_name(alias) {
                candidates.push(name);
            }
            if let Some(raw_alias) = self.var_aliases_map().get(alias)
                && !self.call_result_owner_candidate_is_stack_storage(raw_alias)
            {
                candidates.push(raw_alias.clone());
            }
            if !self.call_result_alias_is_stack_derived(alias) {
                candidates.push(self.rendered_visible_name_for_ssa_name(alias));
            }
        }

        for candidate in candidates {
            if candidate.is_empty() {
                continue;
            }
            if self.call_result_owner_candidate_is_stack_storage(&candidate) {
                continue;
            }
            if !self.is_low_signal_visible_name(&candidate)
                && !self.is_transient_visible_name(&candidate)
                && !is_generic_stack_placeholder_alias(&candidate)
                && (!self.is_autogenerated_stack_home_name(&candidate)
                    || self.is_named_scalar_local(&candidate))
            {
                return Some(candidate);
            }
        }

        None
    }

    fn call_result_owner_candidate_is_stack_storage(&self, name: &str) -> bool {
        self.stack_slot_provenance_for_name(name).is_some()
            || self.stack_offset_for_visible_storage_name(name).is_some()
            || self.canonicalize_stack_name(name).is_some()
            || self.is_generic_stack_local_owner_name(name)
    }

    fn call_result_alias_is_stack_derived(&self, alias: &str) -> bool {
        self.call_result_owner_candidate_is_stack_storage(alias)
            || self.var_aliases_map().get(alias).is_some_and(|raw_alias| {
                self.call_result_owner_candidate_is_stack_storage(raw_alias)
            })
    }

    fn meaningful_tmp_call_owner_name(alias: &str) -> Option<String> {
        let lower = alias.to_ascii_lowercase();
        let raw = SSAVarNameKind::strip_temporary_prefix(&lower)?;
        let stem = raw
            .rsplit_once('_')
            .filter(|(_, suffix)| suffix.chars().all(|ch| ch.is_ascii_digit()))
            .map(|(base, _)| base)
            .unwrap_or(raw);
        (!stem.is_empty()
            && stem.chars().any(|ch| ch.is_ascii_alphabetic())
            && !stem.chars().all(|ch| ch.is_ascii_hexdigit())
            && stem
                .chars()
                .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'))
        .then(|| stem.to_string())
    }

    fn derive_stable_owned_call_result_name_for_source<'b>(
        &self,
        aliases: impl IntoIterator<Item = &'b String>,
    ) -> Option<String> {
        let mut best_name: Option<String> = None;
        let mut best_expr: Option<CExpr> = None;

        for alias in aliases {
            let rendered = match self.derive_stable_owned_call_result_name_for_alias(alias) {
                Some(rendered) => rendered,
                None => continue,
            };

            let candidate_expr = CExpr::Var(rendered.clone());
            let replace = match &best_expr {
                None => true,
                Some(current) => self.prefers_visible_expr(current, &candidate_expr),
            };
            if replace {
                best_name = Some(rendered);
                best_expr = Some(candidate_expr);
            }
        }

        best_name
    }

    pub(crate) fn should_materialize_call_result_at_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        let owner_name = self.stable_owned_call_result_name_for_source(source_call)?;
        if self.should_skip_unused_transient_call_result_owner(source_call, &owner_name) {
            return None;
        }
        let observable_owner = {
            let candidate_names = self.call_result_candidate_names(source_call, &owner_name);
            self.call_result_candidate_names_have_observable_use(&candidate_names)
        };
        let named_stack_owner = self.stack_slot_provenance_for_name(&owner_name).is_some()
            || self
                .stack_offset_for_visible_storage_name(&owner_name)
                .is_some();
        (observable_owner || named_stack_owner).then_some(CExpr::Var(owner_name))
    }

    pub(crate) fn materializable_call_result_expr_for_call_expr(
        &self,
        source_call: (u64, usize),
        _call: &CExpr,
    ) -> Option<CExpr> {
        if let Some(owner) = self.should_materialize_call_result_at_source(source_call) {
            return Some(owner);
        }
        None
    }

    fn should_skip_unused_transient_call_result_owner(
        &self,
        source_call: (u64, usize),
        owner_name: &str,
    ) -> bool {
        if !self.is_low_signal_visible_name(owner_name)
            && !self.is_transient_visible_name(owner_name)
        {
            return false;
        }

        if self.call_result_source_has_result_binding(source_call) {
            return false;
        }

        let candidate_names = self.call_result_candidate_names(source_call, owner_name);
        !self.call_result_candidate_names_have_observable_use(&candidate_names)
    }

    fn call_result_source_has_result_binding(&self, source_call: (u64, usize)) -> bool {
        self.call_args_map().values().any(|args| {
            args.iter().any(|binding| {
                binding.role == analysis::CallArgRole::Result
                    && binding.source_call == Some(source_call)
            })
        })
    }

    fn call_result_candidate_names(
        &self,
        source_call: (u64, usize),
        owner_name: &str,
    ) -> BTreeSet<String> {
        let mut candidate_names = BTreeSet::new();
        candidate_names.insert(owner_name.to_string());
        candidate_names.insert(owner_name.to_ascii_lowercase());
        candidate_names.insert(owner_name.to_ascii_uppercase());
        if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(owner_name) {
            candidate_names.insert(ssa_name.to_ascii_lowercase());
            candidate_names.insert(ssa_name.to_ascii_uppercase());
            candidate_names.insert(ssa_name);
        }
        if let Some(aliases) = self.call_result_aliases_map().get(&source_call) {
            candidate_names.extend(aliases.iter().cloned());
            for alias in aliases {
                candidate_names.insert(alias.to_ascii_lowercase());
                candidate_names.insert(alias.to_ascii_uppercase());
                let rendered = self.rendered_visible_name_for_ssa_name(alias);
                candidate_names.insert(rendered.to_ascii_lowercase());
                candidate_names.insert(rendered.to_ascii_uppercase());
                candidate_names.insert(rendered);
            }
        }

        candidate_names
    }

    fn call_result_candidate_names_have_observable_use(
        &self,
        candidate_names: &BTreeSet<String>,
    ) -> bool {
        let Some(prepared) = self.inputs.prepared_ssa else {
            return candidate_names
                .iter()
                .any(|name| self.use_counts_map().get(name).copied().unwrap_or(0) > 0);
        };

        let graph = prepared.graph();
        let mut stack = candidate_names
            .iter()
            .filter_map(|name| self.value_id_for_name(name))
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();

        while let Some(value_id) = stack.pop() {
            if !visited.insert(value_id) {
                continue;
            }

            for site in graph.use_sites(value_id) {
                let Some(inst) = graph.inst(site.inst) else {
                    continue;
                };
                match &inst.payload {
                    r2ssa::InstPayload::Phi { .. } => {
                        if let Some(output) = inst.output {
                            stack.push(output);
                        }
                    }
                    r2ssa::InstPayload::Op(op) => {
                        if Self::call_result_use_is_passthrough_or_call_plumbing(op) {
                            if let Some(output) = inst.output {
                                stack.push(output);
                            }
                            continue;
                        }
                        return true;
                    }
                }
            }
        }

        false
    }

    fn call_result_use_is_passthrough_or_call_plumbing(op: &SSAOp) -> bool {
        matches!(
            op,
            SSAOp::Copy { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::IntSExt { .. }
                | SSAOp::Trunc { .. }
                | SSAOp::Subpiece { .. }
                | SSAOp::Cast { .. }
                | SSAOp::Store { .. }
                | SSAOp::Call { .. }
                | SSAOp::CallInd { .. }
                | SSAOp::CallDefine { .. }
        )
    }

    #[cfg(test)]
    fn source_call_allows_return_register_owner(&self, source_call: (u64, usize)) -> bool {
        let Some(CExpr::Call { .. }) = self.call_result_exprs_map().get(&source_call) else {
            return false;
        };
        let Some(identity) = self.callee_identity_for_callsite(source_call.0, source_call.1) else {
            return false;
        };
        if identity.is_raw_storage_target() {
            return false;
        }
        if identity.has_known_signature() {
            return false;
        }

        identity.is_internal_name_hint()
    }

    fn fallback_owned_call_result_return_name_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<String> {
        let _ = source_call;
        None
    }

    fn prepared_owned_result_name(expr: &CExpr) -> Option<String> {
        match expr {
            CExpr::Var(name) => Some(name.clone()),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::prepared_owned_result_name(inner)
            }
            _ => None,
        }
    }

    pub(crate) fn stable_owned_call_result_name_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<String> {
        let prepared_name = self
            .prepared_result_owner_name_for_source(source_call)
            .filter(|name| {
                !is_generic_arg_name(name) && !self.inputs.arch.is_return_register_name(name)
            })
            .filter(|_| self.has_certified_call_result_owner_fact_for_source(source_call));
        let ownership_name = self
            .ownership()
            .ownership_for_source(analysis::CallSiteId::from(source_call))
            .and_then(|fact| fact.owner.as_ref())
            .map(|owner| owner.visible_name.clone());
        let dynamic_name = self
            .call_result_aliases_map()
            .get(&source_call)
            .and_then(|aliases| self.derive_stable_owned_call_result_name_for_source(aliases));
        let fallback_name = self.fallback_owned_call_result_return_name_for_source(source_call);

        let mut best = ownership_name;
        for candidate in [prepared_name, dynamic_name, fallback_name]
            .into_iter()
            .flatten()
        {
            best = match best {
                None => Some(candidate),
                Some(current) => {
                    if self.prefers_visible_expr(
                        &CExpr::Var(current.clone()),
                        &CExpr::Var(candidate.clone()),
                    ) {
                        Some(candidate)
                    } else {
                        Some(current)
                    }
                }
            };
        }

        best
    }

    fn prepared_result_owner_name_for_source(&self, source_call: (u64, usize)) -> Option<String> {
        self.prepared_semantic_view()
            .and_then(|view| view.call_view_for_site(source_call))
            .and_then(|view| view.result_owner.as_ref())
            .and_then(Self::prepared_owned_result_name)
    }

    fn has_certified_call_result_owner_fact_for_source(&self, source_call: (u64, usize)) -> bool {
        self.certified_call_result_owner_for_source(source_call)
            .is_some()
    }

    fn certified_call_result_owner_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<&r2ssa::ValueOwner> {
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        self.inputs.call_result_facts()?.owner_for_site(callsite)
    }

    fn certified_call_result_owner_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        match self.certified_call_result_owner_for_source(source_call)? {
            r2ssa::ValueOwner::StackSlot { object, offset } => self
                .certified_stack_var_name_for_object_offset(*object, *offset)
                .map(CExpr::Var),
            r2ssa::ValueOwner::Value(value) => {
                let prepared = self.inputs.prepared_ssa?;
                let var = prepared.value_var(*value)?;
                (!var.is_register()).then(|| CExpr::Var(var.display_name()))
            }
        }
    }

    fn certified_assigned_call_result_owner_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        let render_fact = self.inputs.call_render_facts()?.fact_for_site(callsite)?;
        (render_fact.disposition == r2types::CallsiteRenderDisposition::AssignedResult)
            .then(|| self.certified_call_result_owner_expr_for_source(source_call))?
    }

    fn certified_call_result_owner_name_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<String> {
        match self.certified_call_result_owner_expr_for_source(source_call)? {
            CExpr::Var(name)
                if !is_generic_arg_name(&name)
                    && !self.inputs.arch.is_return_register_name(&name) =>
            {
                Some(name)
            }
            _ => None,
        }
    }

    fn prepared_source_call_for_visible_owner_name(
        &self,
        visible_name: &str,
    ) -> Option<(u64, usize)> {
        self.prepared_semantic_view()?
            .call_view_by_site
            .iter()
            .find_map(|(source_call, view)| {
                view.result_owner
                    .as_ref()
                    .and_then(Self::prepared_owned_result_name)
                    .is_some_and(|owner| owner.eq_ignore_ascii_case(visible_name))
                    .then_some(*source_call)
            })
    }

    pub(super) fn stable_owned_call_result_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        let prepared_owner = self
            .prepared_semantic_view()
            .and_then(|view| view.call_view_for_site(source_call))
            .and_then(|view| view.result_owner.clone())
            .filter(|expr| {
                Self::prepared_owned_result_name(expr).is_none_or(|name| {
                    !is_generic_arg_name(&name) && !self.inputs.arch.is_return_register_name(&name)
                })
            });
        let owned_name = self
            .stable_owned_call_result_name_for_source(source_call)
            .map(CExpr::Var);

        let selected = self
            .choose_preferred_visible_expr(prepared_owner.clone(), owned_name.clone())
            .or(prepared_owner)
            .or(owned_name)?;

        if let CExpr::Var(name) = &selected
            && self.should_skip_unused_transient_call_result_owner(source_call, name)
            && !self
                .fallback_owned_call_result_return_name_for_source(source_call)
                .is_some_and(|return_name| return_name.eq_ignore_ascii_case(name))
        {
            return None;
        }

        Some(selected)
    }

    fn raw_call_exprs_match_for_source_owner_definition(
        &self,
        candidate_source_call: Option<(u64, usize)>,
        candidate: &CExpr,
        expr: &CExpr,
    ) -> bool {
        match (candidate, expr) {
            (
                CExpr::Call {
                    func: candidate_func,
                    args: candidate_args,
                },
                CExpr::Call { func, args },
            ) => {
                let candidate_identity = candidate_source_call
                    .and_then(|(block_addr, op_idx)| {
                        self.callee_identity_for_callsite(block_addr, op_idx)
                    })
                    .map(|identity| identity.primary_key())
                    .or_else(|| self.call_target_identity(candidate_func.as_ref()));
                let expr_identity = self.call_target_identity(func.as_ref());
                let target_matches = match (candidate_identity, expr_identity) {
                    (Some(candidate), Some(observed)) => candidate == observed,
                    (None, None) => candidate_func == func,
                    _ => false,
                };
                target_matches
                    && candidate_args.len() == args.len()
                    && candidate_args
                        .iter()
                        .zip(args.iter())
                        .all(|(left, right)| self.call_owner_definition_args_match(left, right))
            }
            _ => candidate == expr,
        }
    }

    fn source_proof_for_call_expr(&self, expr: &CExpr) -> CallExprSourceProof {
        let (matches, contradicted) = self.source_matches_for_call_expr(expr);
        let mut matches = matches.into_iter();
        let Some(source_call) = matches.next() else {
            return if contradicted {
                CallExprSourceProof::ContradictedOrAmbiguous
            } else {
                CallExprSourceProof::None
            };
        };
        if matches.next().is_some() || contradicted {
            CallExprSourceProof::ContradictedOrAmbiguous
        } else {
            CallExprSourceProof::Exact(source_call)
        }
    }

    fn source_matches_for_call_expr(&self, expr: &CExpr) -> (BTreeSet<(u64, usize)>, bool) {
        if !matches!(expr, CExpr::Call { .. }) {
            return (BTreeSet::new(), false);
        }
        let mut matches = BTreeSet::new();
        let mut contradicted = false;
        for (source_call, source_expr) in self.call_result_exprs_map() {
            if self.raw_call_exprs_match_for_source_owner_definition(
                Some(*source_call),
                source_expr,
                expr,
            ) {
                matches.insert(*source_call);
                continue;
            }
            if self.raw_call_exprs_match_for_source_owner_definition(None, source_expr, expr) {
                contradicted = true;
            }
        }
        (matches, contradicted)
    }

    fn certified_source_for_rendered_call_expr(
        &self,
        expr: &CExpr,
        current_source_call: Option<(u64, usize)>,
    ) -> Option<(u64, usize)> {
        return None;

        if let Some(source_call) = current_source_call
            && let Some(certified) =
                self.certified_synthesized_call_expr_for_source_call(source_call)
            && self.raw_call_exprs_match_for_source_owner_definition(
                Some(source_call),
                &certified.expr,
                expr,
            )
        {
            return Some(source_call);
        }
        let CallExprSourceProof::Exact(source_call) = self.source_proof_for_call_expr(expr) else {
            return None;
        };
        let certified = self.certified_synthesized_call_expr_for_source_call(source_call)?;
        self.raw_call_exprs_match_for_source_owner_definition(
            Some(source_call),
            &certified.expr,
            expr,
        )
        .then_some(source_call)
    }

    fn call_owner_definition_args_match(&self, left: &CExpr, right: &CExpr) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (CExpr::StringLit(_), _) | (_, CExpr::StringLit(_)) => false,
            (CExpr::Var(left), CExpr::Var(right)) => {
                if self.visible_names_share_stack_slot(left, right) {
                    return true;
                }
                self.normalized_call_owner_definition_var_arg(left)
                    == self.normalized_call_owner_definition_var_arg(right)
            }
            (
                CExpr::Binary {
                    op: left_op,
                    left: left_lhs,
                    right: left_rhs,
                },
                CExpr::Binary {
                    op: right_op,
                    left: right_lhs,
                    right: right_rhs,
                },
            ) => {
                left_op == right_op
                    && self.call_owner_definition_args_match(left_lhs, right_lhs)
                    && self.call_owner_definition_args_match(left_rhs, right_rhs)
            }
            (CExpr::Cast { expr: left, .. }, other) | (other, CExpr::Cast { expr: left, .. }) => {
                self.call_owner_definition_args_match(left, other)
            }
            (CExpr::Paren(left), other) | (other, CExpr::Paren(left)) => {
                self.call_owner_definition_args_match(left, other)
            }
            _ => false,
        }
    }

    fn normalized_call_owner_definition_var_arg(&self, name: &str) -> String {
        let mut normalized = if Self::is_opaque_public_call_arg_name(name) {
            Self::opaque_public_call_arg_display_name(name)
        } else {
            name.to_ascii_lowercase()
        };
        if (normalized.starts_with("unk_") || normalized.starts_with("value_"))
            && let Some((base, suffix)) = normalized.rsplit_once('_')
            && !base.is_empty()
            && !suffix.is_empty()
            && suffix.chars().all(|ch| ch.is_ascii_digit())
        {
            normalized = base.to_string();
        }
        normalized
    }

    fn canonicalize_call_expr_for_source_call(
        &self,
        source_call: (u64, usize),
        expr: CExpr,
    ) -> CExpr {
        let CExpr::Call { func, args } = expr else {
            return expr;
        };
        let func = self
            .resolved_callee_identity_expr_for_site(source_call.0, source_call.1)
            .unwrap_or(*func);
        CExpr::call(func, args)
    }

    fn normalize_call_expr_for_source_call(
        &self,
        source_call: (u64, usize),
        expr: CExpr,
        context: FinalExprNormalizeContext,
    ) -> CExpr {
        self.normalize_final_call_expr_in_scope(
            self.canonicalize_call_expr_for_source_call(source_call, expr),
            FinalExprNormalizeScope::for_source_call(context, source_call),
        )
    }

    fn call_target_identity(&self, expr: &CExpr) -> Option<String> {
        match expr {
            CExpr::Var(name) => Some(self.callee_identity_for_name(name).primary_key()),
            CExpr::Paren(inner) | CExpr::AddrOf(inner) | CExpr::Deref(inner) => {
                self.call_target_identity(inner)
            }
            CExpr::Cast { expr: inner, .. } => self.call_target_identity(inner),
            _ => None,
        }
    }

    fn recovered_owned_call_result_definition_rhs(
        &self,
        lhs_name: &str,
        original_rhs: &CExpr,
    ) -> Option<CExpr> {
        let source_call = match original_rhs {
            CExpr::Var(name) => self
                .call_result_source_for_ssa_name(name)
                .or_else(|| self.local_post_call_source_for_ssa_name(name))?,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                return self.recovered_owned_call_result_definition_rhs(lhs_name, inner);
            }
            CExpr::Call { .. } => {
                let source_call = self
                    .call_result_source_for_ssa_name(lhs_name)
                    .or_else(|| self.local_post_call_source_for_ssa_name(lhs_name))
                    .or_else(|| self.source_call_for_visible_owner_name(lhs_name))?;
                let owner = self.stable_owned_call_result_expr_for_source(source_call)?;
                match owner {
                    CExpr::Var(owner_name) if owner_name.eq_ignore_ascii_case(lhs_name) => {
                        return Some(self.normalize_call_expr_for_source_call(
                            source_call,
                            original_rhs.clone(),
                            FinalExprNormalizeContext::DefinitionRoot,
                        ));
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };

        let owner_name = self.stable_owned_call_result_name_for_source(source_call)?;
        if !owner_name.eq_ignore_ascii_case(lhs_name) {
            return None;
        }

        if let Some(expr) = self.call_result_exprs_map().get(&source_call) {
            return Some(self.normalize_call_expr_for_source_call(
                source_call,
                expr.clone(),
                FinalExprNormalizeContext::DefinitionRoot,
            ));
        }

        self.call_result_aliases_map()
            .get(&source_call)
            .into_iter()
            .flat_map(|aliases| aliases.iter())
            .find_map(|alias| {
                let definition = self
                    .direct_definition_expr(alias)
                    .or_else(|| self.lookup_definition_raw(alias))
                    .or_else(|| self.lookup_definition(alias))?;
                matches!(definition, CExpr::Call { .. }).then_some(
                    self.normalize_call_expr_for_source_call(
                        source_call,
                        definition,
                        FinalExprNormalizeContext::DefinitionRoot,
                    ),
                )
            })
            .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
    }

    pub(super) fn should_preserve_owned_call_result_visible_name(&self, name: &str) -> bool {
        self.ownership().has_visible_owner_name(name)
            || self
                .call_result_source_for_ssa_name(name)
                .and_then(|source| self.stable_owned_call_result_name_for_source(source))
                .is_some_and(|owner| owner.eq_ignore_ascii_case(name))
            || self
                .find_ssa_name_for_rendered_alias(name)
                .and_then(|ssa_name| self.call_result_source_for_ssa_name(&ssa_name))
                .and_then(|source| self.stable_owned_call_result_name_for_source(source))
                .is_some_and(|owner| owner.eq_ignore_ascii_case(name))
    }

    pub(super) fn materialized_call_result_source_for_visible_name(
        &self,
        name: &str,
    ) -> Option<(u64, usize)> {
        let resolved_name = self
            .find_ssa_name_for_rendered_alias(name)
            .unwrap_or_else(|| name.to_string());
        self.ownership()
            .source_for_visible_owner_name(name)
            .map(Into::into)
            .or_else(|| self.call_result_source_for_ssa_name(name))
            .or_else(|| {
                (!resolved_name.eq_ignore_ascii_case(name))
                    .then(|| self.call_result_source_for_ssa_name(&resolved_name))?
            })
            .filter(|source| {
                self.should_materialize_call_result_at_source(*source)
                    .and_then(|expr| match expr {
                        CExpr::Var(owner) => Some(owner),
                        _ => None,
                    })
                    .is_some_and(|owner| {
                        owner.eq_ignore_ascii_case(name)
                            || owner.eq_ignore_ascii_case(&resolved_name)
                    })
            })
    }

    fn certified_materialized_call_result_source_for_visible_name(
        &self,
        name: &str,
    ) -> Option<(u64, usize)> {
        let resolved_name = self
            .find_ssa_name_for_rendered_alias(name)
            .unwrap_or_else(|| name.to_string());
        let facts = self.inputs.call_result_facts()?;
        facts.by_callsite.keys().find_map(|callsite| {
            let source_call = (callsite.block_addr, callsite.op_index);
            let owner_name =
                match self.certified_assigned_call_result_owner_expr_for_source(source_call)? {
                    CExpr::Var(owner) => owner,
                    _ => return None,
                };
            (owner_name.eq_ignore_ascii_case(name)
                || owner_name.eq_ignore_ascii_case(&resolved_name))
            .then_some(source_call)
        })
    }

    pub(crate) fn call_result_source_for_ssa_name(&self, ssa_name: &str) -> Option<(u64, usize)> {
        let source_call = self
            .ownership()
            .source_for_alias(ssa_name)
            .map(Into::into)
            .or_else(|| self.use_info().call_result_source_for_name(ssa_name))
            .or_else(|| {
                self.prepared_semantic_view()
                    .and_then(|view| view.call_result_source_for_name(ssa_name))
            })
            .or_else(|| {
                self.find_ssa_name_for_rendered_alias(ssa_name)
                    .filter(|resolved| resolved != ssa_name)
                    .and_then(|resolved| self.call_result_source_for_ssa_name(&resolved))
            })?;
        Some(source_call)
    }

    fn certified_call_result_source_for_ssa_name(&self, ssa_name: &str) -> Option<(u64, usize)> {
        let fact = self.certified_call_result_fact_for_name(ssa_name)?;
        Some((fact.callsite.block_addr, fact.callsite.op_index))
    }

    pub(super) fn local_post_call_source_for_ssa_name(
        &self,
        ssa_name: &str,
    ) -> Option<(u64, usize)> {
        let block_addr = self.current_block_addr.get()?;
        let func = self
            .inputs
            .prepared_ssa
            .map(|prepared| prepared.function())?;
        let block = func.get_block(block_addr)?;
        self.local_post_call_source_for_ssa_name_in_block(block, ssa_name, 0)
    }

    pub(super) fn local_post_call_source_for_ssa_name_in_block(
        &self,
        block: &SSABlock,
        ssa_name: &str,
        depth: u32,
    ) -> Option<(u64, usize)> {
        self.raw_local_post_call_source_for_ssa_name_in_block(block, ssa_name, depth)
    }

    fn raw_local_post_call_source_for_ssa_name_in_block(
        &self,
        block: &SSABlock,
        ssa_name: &str,
        depth: u32,
    ) -> Option<(u64, usize)> {
        if depth > 16 {
            return None;
        }

        let (producer_idx, producer_op) = block.ops.iter().enumerate().rev().find(|(_, op)| {
            op.dst()
                .is_some_and(|dst| dst.display_name().eq_ignore_ascii_case(ssa_name))
        })?;

        match producer_op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. } => self.raw_local_post_call_source_for_ssa_name_in_block(
                block,
                &src.display_name(),
                depth + 1,
            ),
            SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            } => {
                let load_offset = self.extract_stack_offset_from_var(addr)?;
                block
                    .ops
                    .iter()
                    .enumerate()
                    .take(producer_idx)
                    .rev()
                    .find_map(|(_, op)| match op {
                        SSAOp::Store {
                            space: r2il::SpaceId::Ram,
                            addr: store_addr,
                            val,
                            ..
                        } if self.extract_stack_offset_from_var(store_addr)
                            == Some(load_offset) =>
                        {
                            self.call_result_source_for_ssa_name(&val.display_name())
                                .or_else(|| {
                                    self.raw_local_post_call_source_for_ssa_name_in_block(
                                        block,
                                        &val.display_name(),
                                        depth + 1,
                                    )
                                })
                        }
                        _ => None,
                    })
            }
            SSAOp::CallDefine { .. } => block
                .ops
                .iter()
                .enumerate()
                .take(producer_idx)
                .rev()
                .find_map(|(idx, op)| match op {
                    SSAOp::Call { .. } | SSAOp::CallInd { .. } => Some((block.addr, idx)),
                    _ => None,
                }),
            _ => None,
        }
    }

    pub(super) fn stable_owned_call_result_expr_for_name(
        &self,
        name: &str,
        include_direct_aliases: bool,
    ) -> Option<CExpr> {
        let resolved_name = self
            .find_ssa_name_for_rendered_alias(name)
            .unwrap_or_else(|| name.to_string());
        let source_call = self
            .call_result_source_for_ssa_name(name)
            .or_else(|| self.local_post_call_source_for_ssa_name(name))
            .or_else(|| self.certified_call_result_source_for_stack_owner_alias(name))
            .or_else(|| {
                (!resolved_name.eq_ignore_ascii_case(name)).then(|| {
                    self.call_result_source_for_ssa_name(&resolved_name)
                        .or_else(|| self.local_post_call_source_for_ssa_name(&resolved_name))
                        .or_else(|| {
                            self.certified_call_result_source_for_stack_owner_alias(&resolved_name)
                        })
                })?
            })?;
        let owner = self.stable_owned_call_result_expr_for_source(source_call)?;
        let owner_name = match &owner {
            CExpr::Var(name) => name,
            _ => return Some(owner),
        };
        let is_direct_alias = self.direct_call_result_aliases_set().contains(name)
            || self
                .direct_call_result_aliases_set()
                .contains(&resolved_name);
        let has_stack_owner_provenance = self.call_result_alias_has_stack_owner_provenance(name)
            || self.call_result_alias_has_stack_owner_provenance(&resolved_name);
        let owner_has_named_stack_provenance =
            self.stack_slot_provenance_for_name(owner_name).is_some()
                || self
                    .stack_offset_for_visible_storage_name(owner_name)
                    .is_some();
        if !is_direct_alias && !has_stack_owner_provenance && !owner_has_named_stack_provenance {
            return None;
        }
        if owner_name.eq_ignore_ascii_case(name) || owner_name.eq_ignore_ascii_case(&resolved_name)
        {
            return None;
        }
        if !include_direct_aliases && is_direct_alias {
            return None;
        }
        Some(owner)
    }

    fn certified_stable_owned_call_result_expr_for_name(
        &self,
        name: &str,
        include_direct_aliases: bool,
    ) -> Option<CExpr> {
        if !include_direct_aliases {
            return None;
        }
        let fact = self.certified_call_result_fact_for_name(name)?;
        let source_call = (fact.callsite.block_addr, fact.callsite.op_index);
        let owner = self.certified_call_result_owner_expr_for_source(source_call)?;
        let owner_name = match &owner {
            CExpr::Var(owner_name) => owner_name,
            _ => return Some(owner),
        };
        if owner_name.eq_ignore_ascii_case(name) {
            return None;
        }
        Some(owner)
    }

    fn certified_call_result_fact_for_name(
        &self,
        ssa_name: &str,
    ) -> Option<&r2types::CallResultFact> {
        let prepared = self.inputs.prepared_ssa?;
        let var = prepared
            .function()
            .blocks()
            .flat_map(|block| block.ops.iter())
            .filter_map(SSAOp::dst)
            .find(|dst| dst.display_name().eq_ignore_ascii_case(ssa_name))?;
        let value = prepared.graph().value_id_for_var(var)?;
        self.certified_call_result_fact_for_value(value)
    }

    fn certified_call_result_source_for_stack_owner_alias(
        &self,
        name: &str,
    ) -> Option<(u64, usize)> {
        return None;

        let source_call = self
            .use_info()
            .call_result_source_for_name(name)
            .or_else(|| {
                self.prepared_semantic_view()
                    .and_then(|view| view.call_result_source_for_name(name))
            })?;
        self.has_certified_call_result_owner_fact_for_source(source_call)
            .then_some(source_call)
    }

    fn call_result_alias_has_stack_owner_provenance(&self, name: &str) -> bool {
        self.stack_slot_provenance_for_name(name).is_some()
            || self.semantic_stack_owner_name_for_alias(name).is_some()
            || self
                .forwarded_value_for_name(name)
                .and_then(|prov| prov.stack_slot)
                .is_some()
    }

    fn preserved_owned_call_result_var_for_name(&self, name: &str) -> Option<CExpr> {
        let rendered_name = self.rendered_visible_name_for_ssa_name(name);
        let source_call = self
            .call_result_source_for_ssa_name(name)
            .or_else(|| self.local_post_call_source_for_ssa_name(name))
            .or_else(|| self.source_call_for_visible_owner_name(name))
            .or_else(|| self.source_call_for_visible_owner_name(&rendered_name))?;
        let owner_name = self.stable_owned_call_result_name_for_source(source_call)?;
        (owner_name.eq_ignore_ascii_case(name) || owner_name.eq_ignore_ascii_case(&rendered_name))
            .then_some(CExpr::Var(owner_name))
    }

    pub(super) fn predicate_owned_call_result_expr_for_source(
        &self,
        source_call: (u64, usize),
    ) -> Option<CExpr> {
        let owner = self
            .stable_owned_call_result_name_for_source(source_call)
            .map(CExpr::Var)
            .or_else(|| self.stable_owned_call_result_expr_for_source(source_call))?;
        let CExpr::Var(owner_name) = owner else {
            return None;
        };
        (!is_generic_arg_name(&owner_name)
            && !self.inputs.arch.is_return_register_name(&owner_name)
            && !self.is_low_signal_visible_name(&owner_name)
            && !self.is_transient_visible_name(&owner_name)
            && !owner_name.ends_with("_home")
            && !owner_name.starts_with("var_")
            && !owner_name.starts_with("local_")
            && !owner_name.starts_with("stack_")
            && !owner_name.starts_with("arg_"))
        .then_some(CExpr::Var(owner_name))
    }

    pub(super) fn predicate_owned_call_result_expr_for_name(&self, name: &str) -> Option<CExpr> {
        self.call_result_source_for_ssa_name(name)
            .or_else(|| self.local_post_call_source_for_ssa_name(name))
            .and_then(|source| self.predicate_owned_call_result_expr_for_source(source))
    }

    fn semantic_stack_owner_name_for_alias(&self, alias: &str) -> Option<String> {
        match self.semantic_value_for_name(alias) {
            Some(analysis::SemanticValue::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            }) => self.stack_owner_name_for_addr(addr),
            Some(analysis::SemanticValue::Address(addr)) => self.stack_owner_name_for_addr(addr),
            _ => None,
        }
    }

    fn stack_owner_name_for_addr(&self, addr: &analysis::NormalizedAddr) -> Option<String> {
        (addr.index.is_none() && addr.scale_bytes == 0 && addr.offset_bytes == 0)
            .then_some(())
            .and_then(|_| match addr.base {
                analysis::BaseRef::StackSlot(offset) => self.resolve_stack_var(offset),
                _ => None,
            })
    }

    fn visible_names_share_stack_slot(&self, lhs: &str, rhs: &str) -> bool {
        self.stack_offset_for_visible_storage_name(lhs).is_some()
            && self.stack_offset_for_visible_storage_name(lhs)
                == self.stack_offset_for_visible_storage_name(rhs)
    }

    fn should_suppress_shadow_call_result_assignment(&self, dst: &SSAVar) -> bool {
        let source_call = match self.call_result_source_for_ssa_name(&dst.display_name()) {
            Some(source_call) => source_call,
            None => return false,
        };
        let rendered = self.var_name(dst);
        let owner_name = self.stable_owned_call_result_name_for_source(source_call);
        let Some(owner_name) = owner_name else {
            return self
                .direct_call_result_aliases_set()
                .contains(&dst.display_name())
                && self.call_result_exprs_map().contains_key(&source_call)
                && (self.is_low_signal_visible_name(&rendered)
                    || self.is_transient_visible_name(&rendered));
        };
        if owner_name.eq_ignore_ascii_case(&rendered)
            && self
                .should_materialize_call_result_at_source(source_call)
                .is_some()
        {
            return true;
        }
        owner_name != rendered
            && (self.is_low_signal_visible_name(&rendered)
                || self.is_transient_visible_name(&rendered))
    }

    fn expr_is_stack_base_like(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = name.to_ascii_lowercase();
                self.inputs.arch.is_stack_base_name(&lower)
                    || self.inputs.arch.is_frame_pointer_name(&lower)
                    || lower == "stack"
                    || lower == "saved_fp"
                    || is_generic_stack_placeholder_alias(name)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.expr_is_stack_base_like(inner)
            }
            CExpr::Unary { operand, .. } => self.expr_is_stack_base_like(operand),
            _ => false,
        }
    }

    fn expr_contains_raw_stack_base_arithmetic(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => {
                self.expr_is_stack_base_like(left)
                    || self.expr_is_stack_base_like(right)
                    || self.expr_contains_raw_stack_base_arithmetic(left)
                    || self.expr_contains_raw_stack_base_arithmetic(right)
            }
            CExpr::Paren(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Deref(inner)
            | CExpr::Cast { expr: inner, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(inner)
            }
            CExpr::Unary { operand, .. } => self.expr_contains_raw_stack_base_arithmetic(operand),
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(left)
                    || self.expr_contains_raw_stack_base_arithmetic(right)
            }
            CExpr::Subscript { base, index } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
                    || self.expr_contains_raw_stack_base_arithmetic(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
            }
            CExpr::Call { func, args } => {
                self.expr_contains_raw_stack_base_arithmetic(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_contains_raw_stack_base_arithmetic(arg))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_contains_raw_stack_base_arithmetic(cond)
                    || self.expr_contains_raw_stack_base_arithmetic(then_expr)
                    || self.expr_contains_raw_stack_base_arithmetic(else_expr)
            }
            CExpr::Comma(exprs) => exprs
                .iter()
                .any(|inner| self.expr_contains_raw_stack_base_arithmetic(inner)),
            CExpr::Sizeof(inner) => self.expr_contains_raw_stack_base_arithmetic(inner),
            _ => false,
        }
    }

    pub(super) fn expr_is_address_artifact_in_scalar_context(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::AddrOf(_) => true,
            CExpr::Deref(inner) => self.expr_contains_raw_stack_base_arithmetic(inner),
            CExpr::Subscript { base, index } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
                    || self.expr_contains_raw_stack_base_arithmetic(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(base)
            }
            CExpr::Var(name) => {
                self.is_non_index_pointer_expr(expr)
                    && !matches!(
                        self.stack_slot_provenance_for_name(name),
                        Some(slot) if slot.is_scalar_predicate_carrier() || slot.is_scalar_return_carrier()
                    )
            }
            CExpr::Cast { ty, expr: inner } => {
                matches!(ty, CType::Pointer(_))
                    || self.expr_is_address_artifact_in_scalar_context(inner)
            }
            CExpr::Paren(inner) => self.expr_is_address_artifact_in_scalar_context(inner),
            CExpr::Unary { operand, .. } => {
                self.expr_is_address_artifact_in_scalar_context(operand)
            }
            CExpr::Binary { left, right, .. } => {
                self.expr_contains_raw_stack_base_arithmetic(expr)
                    || self.expr_is_address_artifact_in_scalar_context(left)
                    || self.expr_is_address_artifact_in_scalar_context(right)
            }
            CExpr::Call { func, args } => {
                self.expr_is_address_artifact_in_scalar_context(func)
                    || args
                        .iter()
                        .any(|arg| self.expr_is_address_artifact_in_scalar_context(arg))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expr_is_address_artifact_in_scalar_context(cond)
                    || self.expr_is_address_artifact_in_scalar_context(then_expr)
                    || self.expr_is_address_artifact_in_scalar_context(else_expr)
            }
            CExpr::Comma(exprs) => exprs
                .iter()
                .any(|inner| self.expr_is_address_artifact_in_scalar_context(inner)),
            CExpr::Sizeof(inner) => self.expr_is_address_artifact_in_scalar_context(inner),
            _ => false,
        }
    }

    pub(crate) fn prefers_visible_expr(&self, current: &CExpr, candidate: &CExpr) -> bool {
        self.prefers_visible_expr_in_context(current, candidate, VisibleExprContext::Generic)
    }

    fn prefers_visible_expr_in_context(
        &self,
        current: &CExpr,
        candidate: &CExpr,
        context: VisibleExprContext,
    ) -> bool {
        self.visible_expr_quality_in_context(candidate, context)
            > self.visible_expr_quality_in_context(current, context)
    }

    pub(super) fn choose_preferred_visible_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            current,
            candidate,
            VisibleExprContext::Generic,
        )
    }

    pub(super) fn choose_preferred_scalar_predicate_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            current,
            candidate,
            VisibleExprContext::ScalarPredicate,
        )
    }

    fn choose_preferred_visible_expr_in_context(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        context: VisibleExprContext,
    ) -> Option<CExpr> {
        match (current, candidate) {
            (None, other) => other,
            (some @ Some(_), None) => some,
            (Some(current_expr), Some(candidate_expr)) => {
                if self.prefers_visible_expr_in_context(&current_expr, &candidate_expr, context) {
                    Some(candidate_expr)
                } else {
                    Some(current_expr)
                }
            }
        }
    }

    fn should_preserve_address_like_visible_name(&self, name: &str) -> bool {
        let Some(stripped) = name.strip_prefix('&') else {
            return false;
        };
        !stripped.is_empty()
            && !self.is_low_signal_visible_name(stripped)
            && !self.is_transient_visible_name(stripped)
            && !is_generic_stack_placeholder_alias(stripped)
    }

    pub(super) fn best_visible_definition(&self, name: &str) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Visible, name) {
            return self.resolution_cycle_fallback(name);
        }
        let result = self.best_visible_definition_in_context(name, VisibleExprContext::Generic);
        self.leave_resolution_guard(ResolutionPhase::Visible, name);
        result
    }

    fn best_visible_definition_in_context(
        &self,
        name: &str,
        context: VisibleExprContext,
    ) -> Option<CExpr> {
        self.best_visible_definition_in_context_with_depth(name, context, 0, &mut HashSet::new())
    }

    fn best_visible_definition_with_depth(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        self.best_visible_definition_in_context_with_depth(
            name,
            VisibleExprContext::Generic,
            depth,
            visited,
        )
    }

    fn best_visible_definition_in_context_with_depth(
        &self,
        name: &str,
        context: VisibleExprContext,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            self.lookup_definition_with_depth(name, depth, visited),
            self.formatted_defs_map().get(name).cloned(),
            context,
        )
    }

    fn visible_expr_quality(&self, expr: &CExpr) -> VisibleExprQuality {
        self.visible_expr_quality_in_context(expr, VisibleExprContext::Generic)
    }

    fn visible_expr_quality_in_context(
        &self,
        expr: &CExpr,
        context: VisibleExprContext,
    ) -> VisibleExprQuality {
        let mut quality = VisibleExprQuality::default();
        self.accumulate_visible_expr_quality(expr, &mut quality, 0, context);
        if matches!(context, VisibleExprContext::ScalarPredicate)
            && self.is_predicate_like_expr(expr)
        {
            quality.predicate_signal += 12;
            quality.scalar_signal += 4;
        }
        if matches!(
            context,
            VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
        ) && self.expr_contains_raw_stack_base_arithmetic(expr)
        {
            quality.address_shape_penalty -= 24;
        }
        quality
    }

    fn accumulate_visible_expr_quality(
        &self,
        expr: &CExpr,
        quality: &mut VisibleExprQuality,
        depth: u32,
        context: VisibleExprContext,
    ) {
        if depth > MAX_SIMPLE_EXPR_DEPTH {
            return;
        }

        quality.node_penalty -= 1;
        match expr {
            CExpr::Var(name) => {
                if is_generic_stack_placeholder_alias(name) {
                    quality.generic_stack_penalty -= 8;
                } else if self.is_transient_visible_name(name) {
                    quality.transient_reg_penalty -= 6;
                } else if self.is_low_signal_visible_name(name) {
                    quality.temp_penalty -= 4;
                } else {
                    quality.semantic_names += 3;
                }
                if matches!(
                    context,
                    VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                ) {
                    if self.arg_alias_for_rendered_name(name).is_some() || is_generic_arg_name(name)
                    {
                        quality.scalar_signal += 12;
                    }
                    if self.lookup_predicate_expr(name).is_some()
                        || self.condition_vars_set().contains(name)
                    {
                        quality.predicate_signal += 8;
                        quality.scalar_signal += 4;
                    }
                    if self.is_named_scalar_local(name) {
                        quality.scalar_signal += 6;
                    }
                    if self.is_autogenerated_stack_home_name(name)
                        && self.stack_slot_provenance_for_name(name).is_some()
                        && !self.is_generic_stack_local_owner_name(name)
                    {
                        quality.stack_home_penalty -= 18;
                    }
                    if self.is_generic_stack_local_owner_name(name) {
                        quality.generic_stack_penalty -= 8;
                    }
                    if self
                        .ownership()
                        .source_for_visible_owner_name(name)
                        .and_then(|source| {
                            self.should_materialize_call_result_at_source(source.into())
                        })
                        .is_some()
                    {
                        quality.scalar_signal += 18;
                        quality.semantic_names += 4;
                    }
                    if matches!(
                        self.stack_slot_provenance_for_name(name),
                        Some(slot)
                            if slot.is_scalar_predicate_carrier()
                                || slot.is_scalar_return_carrier()
                    ) {
                        if self.is_named_scalar_local(name) {
                            quality.scalar_signal += 4;
                        } else {
                            quality.generic_stack_penalty -= 4;
                        }
                    }
                    if self.is_non_index_pointer_expr(expr)
                        && !matches!(
                            self.stack_slot_provenance_for_name(name),
                            Some(slot)
                                if slot.is_scalar_predicate_carrier()
                                    || slot.is_scalar_return_carrier()
                        )
                    {
                        quality.address_shape_penalty -= 20;
                    }
                }
            }
            CExpr::Subscript { base, index } => {
                quality.semantic_shapes += 6;
                quality.stable_pointer_shapes += 2;
                if self.is_non_index_pointer_expr(index) {
                    quality.transient_reg_penalty -= 10;
                }
                if matches!(
                    context,
                    VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                ) {
                    quality.scalar_signal += 8;
                }
                self.accumulate_visible_expr_quality(base, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(index, quality, depth + 1, context);
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                quality.semantic_shapes += 7;
                quality.stable_pointer_shapes += 2;
                if matches!(
                    context,
                    VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                ) {
                    quality.scalar_signal += 8;
                }
                self.accumulate_visible_expr_quality(base, quality, depth + 1, context);
            }
            CExpr::Deref(inner) | CExpr::AddrOf(inner) => {
                quality.stable_pointer_shapes += 1;
                if matches!(expr, CExpr::AddrOf(_))
                    && matches!(
                        context,
                        VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                    )
                {
                    quality.address_shape_penalty -= 30;
                } else if matches!(
                    context,
                    VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                ) {
                    quality.scalar_signal += 4;
                }
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
            }
            CExpr::Cast { ty, expr: inner } => {
                if matches!(
                    context,
                    VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                ) && matches!(ty, CType::Pointer(_))
                {
                    quality.address_shape_penalty -= 24;
                }
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
            }
            CExpr::Paren(inner) | CExpr::Unary { operand: inner, .. } => {
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
            }
            CExpr::Binary { op, left, right } => {
                if matches!(op, BinaryOp::Add | BinaryOp::Sub)
                    && (self.literal_to_i64(left).is_some_and(|lit| lit == 0)
                        || self.literal_to_i64(right).is_some_and(|lit| lit == 0))
                {
                    quality.zero_offset_penalty -= 10;
                }
                if matches!(
                    context,
                    VisibleExprContext::ScalarPredicate | VisibleExprContext::ScalarReturn
                ) && self.expr_contains_raw_stack_base_arithmetic(expr)
                {
                    quality.address_shape_penalty -= 18;
                }
                self.accumulate_visible_expr_quality(left, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(right, quality, depth + 1, context);
            }
            CExpr::Call { func, args } => {
                self.accumulate_visible_expr_quality(func, quality, depth + 1, context);
                for arg in args {
                    self.accumulate_visible_expr_quality(arg, quality, depth + 1, context);
                }
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.accumulate_visible_expr_quality(cond, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(then_expr, quality, depth + 1, context);
                self.accumulate_visible_expr_quality(else_expr, quality, depth + 1, context);
            }
            CExpr::Comma(exprs) => {
                for inner in exprs {
                    self.accumulate_visible_expr_quality(inner, quality, depth + 1, context);
                }
            }
            CExpr::Sizeof(inner) => {
                self.accumulate_visible_expr_quality(inner, quality, depth + 1, context)
            }
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => {}
        }
    }

    pub(super) fn is_low_signal_visible_name(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        let storage_kind = SSAVarNameKind::classify(&lower);
        let is_temp_family = |prefix: char| {
            lower
                .strip_prefix(prefix)
                .and_then(|rest| {
                    let (head, tail) = rest.split_once('_').unwrap_or((rest, ""));
                    head.chars()
                        .all(|ch| ch.is_ascii_hexdigit())
                        .then_some(tail)
                })
                .is_some_and(|tail| tail.is_empty() || tail.chars().all(|ch| ch.is_ascii_digit()))
        };
        matches!(
            storage_kind,
            SSAVarNameKind::Temporary | SSAVarNameKind::Constant | SSAVarNameKind::Memory
        ) || lower.starts_with("tmp")
            || is_temp_family('t')
            || is_temp_family('v')
    }

    pub(super) fn is_transient_visible_name(&self, name: &str) -> bool {
        if self.is_low_signal_visible_name(name) {
            return false;
        }

        let lower = name.to_ascii_lowercase();
        if is_cpu_flag(&lower) {
            return true;
        }

        let base = lower.split('_').next().unwrap_or(lower.as_str());
        self.inputs.arch.is_register_like_base_name(base)
            && !Self::is_semantic_binding_name(base)
            && self.arg_alias_for_rendered_name(name).is_none()
    }

    fn should_force_imported_call_resolution_name(&self, name: &str) -> bool {
        self.is_transient_visible_name(name)
            || self.is_low_signal_visible_name(name)
            || Self::is_low_quality_imported_call_arg_name(name)
    }

    fn is_low_quality_imported_call_arg_name(name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        lower.starts_with("var_")
            || lower.starts_with("local_")
            || lower.starts_with("arg_")
            || lower.starts_with("slot_")
            || lower == "slot"
            || Self::is_opaque_public_call_arg_name(&lower)
            || lower.starts_with("value_")
            || lower == "saved_fp"
            || lower.starts_with("stack_")
            || lower.ends_with("_home")
    }

    fn expr_type_hint(&self, expr: &CExpr) -> Option<CType> {
        match expr {
            CExpr::Var(name) => self.lookup_type_hint(name).cloned().or_else(|| {
                self.find_ssa_name_for_rendered_alias(name)
                    .and_then(|ssa_name| self.guess_ssa_var_from_name(&ssa_name))
                    .and_then(|var| self.type_hint_for_var(&var))
            }),
            CExpr::Call { func, .. } => self
                .known_signature_for_callee_expr(func)
                .map(|sig| crate::variable::type_like_to_ctype(&sig.return_type)),
            CExpr::Cast { ty, .. } => Some(ty.clone()),
            CExpr::Paren(inner) => self.expr_type_hint(inner),
            _ => None,
        }
    }

    fn expr_type_hint_for_source_call(
        &self,
        source_call: (u64, usize),
        expr: &CExpr,
    ) -> Option<CType> {
        match expr {
            CExpr::Call { .. } => self
                .known_signature_for_site(source_call.0, source_call.1)
                .map(|sig| crate::variable::type_like_to_ctype(&sig.return_type)),
            CExpr::Cast { ty, .. } => Some(ty.clone()),
            CExpr::Paren(inner) => self.expr_type_hint_for_source_call(source_call, inner),
            _ => self.expr_type_hint(expr),
        }
    }

    fn root_visible_name_in_expr<'b>(&self, expr: &'b CExpr) -> Option<&'b str> {
        match expr {
            CExpr::Var(name) => Some(name.as_str()),
            CExpr::Cast { expr: inner, .. } | CExpr::Paren(inner) => {
                self.root_visible_name_in_expr(inner)
            }
            _ => None,
        }
    }

    fn should_preserve_indirect_local_deref(&self, expr: &CExpr) -> bool {
        let is_pointer_like_owner = |ctx: &FoldingContext<'_>, name: &str, expr: &CExpr| {
            ctx.is_named_scalar_local(name)
                && matches!(
                    ctx.lookup_type_hint(name)
                        .cloned()
                        .or_else(|| ctx.expr_type_hint(expr)),
                    Some(CType::Pointer(_)) | Some(CType::Array(_, _))
                )
        };

        let Some(name) = self.root_visible_name_in_expr(expr) else {
            return false;
        };
        if is_pointer_like_owner(self, name, expr) {
            return true;
        }

        let root = self.resolve_copy_root_name_in_fold(name);
        if root != name {
            let rendered = self.rendered_visible_name_for_ssa_name(&root);
            if is_pointer_like_owner(self, &rendered, expr) {
                return true;
            }
        }

        false
    }

    fn typed_deref_expr(&self, addr: &SSAVar, addr_expr: CExpr, elem_ty: CType) -> CExpr {
        let elem_size = elem_ty.bits().map(|bits| bits.div_ceil(8)).unwrap_or(0);
        if let Some(shape) = self.normalized_addr_from_visible_expr(&addr_expr, 0) {
            let mut visited = HashSet::new();
            if let Some(access) =
                self.render_access_expr_from_addr(&shape, elem_size, false, 0, &mut visited)
            {
                return access;
            }
        }
        if let Some(indexed) = self.indexed_pointer_add_expr(&addr_expr, &elem_ty) {
            return indexed;
        }
        let ptr_ty = CType::ptr(elem_ty);
        let casted = self.cast_addr_expr_to_ptr_if_needed(addr, addr_expr, &ptr_ty);
        CExpr::Deref(Box::new(casted))
    }

    fn cast_addr_expr_to_ptr_if_needed(
        &self,
        addr: &SSAVar,
        addr_expr: CExpr,
        target_ptr_ty: &CType,
    ) -> CExpr {
        if let CExpr::Cast { ty, .. } = &addr_expr
            && ty == target_ptr_ty
        {
            return addr_expr;
        }

        let source_ty = self
            .expr_type_hint(&addr_expr)
            .or_else(|| self.type_hint_for_var(addr));
        if let Some(source_ty) = source_ty.as_ref() {
            return self.cast_expr_if_needed(addr_expr, target_ptr_ty.clone(), Some(source_ty));
        }

        if self.looks_like_pointer(&addr_expr) {
            return addr_expr;
        }

        CExpr::cast(target_ptr_ty.clone(), addr_expr)
    }

    fn int_meta(&self, ty: &CType) -> Option<(bool, u32)> {
        match ty {
            CType::Int(bits) => Some((true, *bits)),
            CType::UInt(bits) => Some((false, *bits)),
            CType::Bool => Some((false, 1)),
            CType::Typedef(name) => self.typedef_int_meta(name),
            _ => None,
        }
    }

    fn typedef_int_meta(&self, name: &str) -> Option<(bool, u32)> {
        let normalized = name
            .to_ascii_lowercase()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        match normalized.as_str() {
            "signed char" | "int8_t" => Some((true, 8)),
            "unsigned char" | "uint8_t" => Some((false, 8)),
            "short" | "short int" | "signed short" | "signed short int" | "int16_t" => {
                Some((true, 16))
            }
            "unsigned short" | "unsigned short int" | "uint16_t" => Some((false, 16)),
            "int" | "signed" | "signed int" | "int32_t" => Some((true, 32)),
            "unsigned" | "unsigned int" | "uint32_t" => Some((false, 32)),
            "long long"
            | "long long int"
            | "signed long long"
            | "signed long long int"
            | "int64_t"
            | "intmax_t" => Some((true, 64)),
            "unsigned long long" | "unsigned long long int" | "uint64_t" | "uintmax_t" => {
                Some((false, 64))
            }
            "long" | "long int" | "signed long" | "signed long int" => {
                Some((true, self.inputs.arch.ptr_size.saturating_mul(8)))
            }
            "unsigned long" | "unsigned long int" | "size_t" | "uintptr_t" => {
                Some((false, self.inputs.arch.ptr_size.saturating_mul(8)))
            }
            "ssize_t" | "intptr_t" | "ptrdiff_t" => {
                Some((true, self.inputs.arch.ptr_size.saturating_mul(8)))
            }
            _ => None,
        }
    }

    fn function_return_int_meta(&self) -> Option<(bool, u32)> {
        self.inputs
            .function_return_type
            .and_then(|ty| self.int_meta(ty))
    }

    fn function_return_int_bits(&self) -> Option<u32> {
        self.function_return_int_meta().map(|(_, bits)| bits)
    }

    fn should_preserve_narrow_return_expr(&self, src: &SSAVar) -> bool {
        self.function_return_int_bits()
            .is_some_and(|bits| bits <= src.size.saturating_mul(8))
    }

    fn tracked_return_cast_expr(&self, dst: &SSAVar, src: &SSAVar, src_expr: CExpr) -> CExpr {
        if self.should_preserve_narrow_return_expr(src) {
            src_expr
        } else {
            CExpr::cast(type_from_size(dst.size), src_expr)
        }
    }

    fn tracked_return_source_expr(&self, src: &SSAVar) -> CExpr {
        let direct = self.get_expr(src);
        if Self::expr_is_scalar_memory_candidate(&direct)
            && !self.expr_is_address_artifact_in_scalar_context(&direct)
        {
            self.resolve_return_candidate(&direct)
        } else if self
            .function_return_int_bits()
            .is_some_and(|bits| bits > src.size.saturating_mul(8))
        {
            self.get_return_expr(src)
        } else {
            direct
        }
    }

    fn cast_needed(&self, target: &CType, source: Option<&CType>) -> bool {
        let Some(source) = source else {
            return false;
        };

        if target == source {
            return false;
        }

        if let (Some((dst_signed, dst_bits)), Some((src_signed, src_bits))) =
            (self.int_meta(target), self.int_meta(source))
        {
            return dst_signed != src_signed || dst_bits != src_bits;
        }

        matches!(
            (target, source),
            (
                CType::Pointer(_),
                CType::Int(_) | CType::UInt(_) | CType::Bool
            ) | (CType::Int(_) | CType::UInt(_), CType::Pointer(_))
        )
    }

    fn cast_expr_if_needed(&self, expr: CExpr, target: CType, source: Option<&CType>) -> CExpr {
        if let CExpr::Cast { ty, .. } = &expr
            && *ty == target
        {
            return expr;
        }
        if self.cast_needed(&target, source) {
            CExpr::cast(target, expr)
        } else {
            expr
        }
    }

    fn assignment_rhs_with_type_policy(
        &self,
        dst: &SSAVar,
        src: Option<&SSAVar>,
        rhs: CExpr,
    ) -> CExpr {
        let Some(dst_ty) = self.type_hint_for_var(dst) else {
            return rhs;
        };

        let src_ty = src.and_then(|var| self.type_hint_for_var(var));
        let rhs = self.cast_expr_if_needed(rhs, dst_ty.clone(), src_ty.as_ref());
        self.rewrite_typed_assignment_literal_expr(rhs, &dst_ty)
    }

    fn rewrite_typed_assignment_literal_expr(&self, expr: CExpr, dst_ty: &CType) -> CExpr {
        let Some((is_signed, bits)) = self.int_meta(dst_ty) else {
            return expr;
        };
        if bits == 0 || bits > 64 {
            return expr;
        }
        match expr {
            CExpr::UIntLit(value) => crate::typed_integer_literal_expr(value, is_signed, bits),
            CExpr::IntLit(value) if value >= 0 => {
                crate::typed_integer_literal_expr(value as u64, is_signed, bits)
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(
                self.rewrite_typed_assignment_literal_expr(*inner, dst_ty),
            )),
            other => other,
        }
    }

    fn collapse_scalar_stack_addr_artifact(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::AddrOf(inner) => {
                if let CExpr::Var(name) = inner.as_ref()
                    && !is_generic_stack_placeholder_alias(name)
                    && self.stack_offset_for_visible_storage_name(name).is_some()
                {
                    return CExpr::Var(name.clone());
                }
                let candidate = CExpr::AddrOf(inner.clone());
                if let Some(alias) = self.resolve_stack_alias_from_addr_expr(&candidate, 0)
                    && !is_generic_stack_placeholder_alias(&alias)
                {
                    return CExpr::Var(alias);
                }
                CExpr::AddrOf(Box::new(self.collapse_scalar_stack_addr_artifact(*inner)))
            }
            CExpr::Paren(inner) => {
                CExpr::Paren(Box::new(self.collapse_scalar_stack_addr_artifact(*inner)))
            }
            CExpr::Cast { ty, expr: inner } => {
                CExpr::cast(ty, self.collapse_scalar_stack_addr_artifact(*inner))
            }
            other => {
                other.map_children(&mut |child| self.collapse_scalar_stack_addr_artifact(child))
            }
        }
    }

    fn scalar_stack_placeholder_offset_expr(&self, expr: &CExpr) -> Option<i64> {
        match expr {
            CExpr::Var(name) if should_replace_preserved_stack_alias(name) => {
                self.stack_offset_for_visible_storage_name(name)
            }
            CExpr::AddrOf(inner) | CExpr::Paren(inner) => {
                self.scalar_stack_placeholder_offset_expr(inner)
            }
            CExpr::Cast { expr: inner, .. } => self.scalar_stack_placeholder_offset_expr(inner),
            _ => None,
        }
    }

    fn rewrite_scalar_stack_placeholder_rhs(&self, lhs: &CExpr, rhs: CExpr) -> CExpr {
        let CExpr::Var(lhs_name) = lhs else {
            return rhs;
        };
        if is_generic_stack_placeholder_alias(lhs_name) {
            return rhs;
        }
        let Some(lhs_offset) = self.stack_offset_for_visible_storage_name(lhs_name) else {
            return rhs;
        };
        let Some(rhs_offset) = self.scalar_stack_placeholder_offset_expr(&rhs) else {
            return rhs;
        };

        let delta = rhs_offset - lhs_offset;
        if delta == 0 {
            return CExpr::Var(lhs_name.clone());
        }
        rhs
    }

    fn producer_for_value(&self, value: &SSAVar) -> Option<&SSAOp> {
        if let Some(op) = self.current_block_producer_for_value(value) {
            return Some(op);
        }
        self.use_info().producers.get(&value.display_name())
    }

    fn current_block_producer_for_value(&self, value: &SSAVar) -> Option<&SSAOp> {
        let block_addr = self.current_block_addr.get()?;
        let current_op_idx = self.current_op_idx.get()?;
        let block = self.prepared_ssa()?.function().get_block(block_addr)?;
        block
            .ops
            .iter()
            .take(current_op_idx)
            .rev()
            .find(|op| op.dst() == Some(value))
    }

    fn stack_slot_load_offset_for_value(&self, value: &SSAVar, depth: usize) -> Option<i64> {
        if depth > 8 {
            return None;
        }
        match self.producer_for_value(value)? {
            SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            } => self.stack_slot_offset_for_var(addr),
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. } => self.stack_slot_load_offset_for_value(src, depth + 1),
            _ => None,
        }
    }

    fn value_loads_from_store_addr(
        &self,
        value: &SSAVar,
        store_addr: &SSAVar,
        depth: usize,
    ) -> bool {
        if depth > 8 {
            return false;
        }
        match self.producer_for_value(value) {
            Some(SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            }) => {
                addr == store_addr
                    || self.stack_slot_offset_for_var(addr).is_some()
                        && self.stack_slot_offset_for_var(addr)
                            == self.stack_slot_offset_for_var(store_addr)
            }
            Some(
                SSAOp::Copy { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. }
                | SSAOp::Trunc { src, .. }
                | SSAOp::Cast { src, .. }
                | SSAOp::Subpiece { src, .. },
            ) => self.value_loads_from_store_addr(src, store_addr, depth + 1),
            _ => false,
        }
    }

    fn small_const_delta(value: &SSAVar) -> Option<i64> {
        let raw = parse_const_value(&value.name)?;
        (raw <= 0x1000).then_some(raw as i64)
    }

    fn stack_rmw_rhs_operand_expr(&self, value: &SSAVar) -> Option<CExpr> {
        if let Some(delta) = Self::small_const_delta(value) {
            return Some(CExpr::IntLit(delta));
        }

        let candidate = match self.producer_for_value(value) {
            Some(SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            }) => {
                let elem_ty = self
                    .type_hint_for_var(value)
                    .unwrap_or_else(|| type_from_size(value.size));
                self.render_canonical_load_expr(value, addr, elem_ty)
            }
            _ => {
                let name = value.display_name();
                let mut visited = HashSet::new();
                self.render_semantic_value_by_name(&name, 0, &mut visited)
                    .or_else(|| self.best_visible_definition(&name))
                    .unwrap_or_else(|| self.get_expr(value))
            }
        };
        let elem_ty = self
            .type_hint_for_var(value)
            .unwrap_or_else(|| type_from_size(value.size));
        let candidate = self
            .indexed_pointer_add_expr(&candidate, &elem_ty)
            .or_else(|| {
                (!FoldingContext::expr_is_scalar_memory_candidate(&candidate)
                    && !matches!(elem_ty, CType::Pointer(_) | CType::Array(_, _))
                    && self
                        .normalized_addr_from_visible_expr(&candidate, 0)
                        .is_some())
                .then(|| self.typed_deref_expr(value, candidate.clone(), elem_ty.clone()))
            })
            .unwrap_or(candidate);
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&candidate, 0, &mut semantic_visited);
        let candidate = self
            .choose_preferred_visible_expr(Some(candidate), Some(semanticized))
            .unwrap_or_else(|| self.get_expr(value));
        (!expr_contains_call(&candidate)).then_some(candidate)
    }

    fn stack_read_modify_write_rhs(
        &self,
        lhs: &CExpr,
        store_addr: &SSAVar,
        val: &SSAVar,
    ) -> Option<CExpr> {
        let CExpr::Var(lhs_name) = lhs else {
            return None;
        };
        let producer = self.producer_for_value(val)?;
        match producer {
            SSAOp::IntAdd { a, b, .. } => {
                if self.value_loads_from_store_addr(a, store_addr, 0) {
                    let rhs = self.stack_rmw_rhs_operand_expr(b)?;
                    if rhs != CExpr::IntLit(0) {
                        return Some(CExpr::binary(
                            BinaryOp::Add,
                            CExpr::Var(lhs_name.to_string()),
                            rhs,
                        ));
                    }
                } else if self.value_loads_from_store_addr(b, store_addr, 0) {
                    let rhs = self.stack_rmw_rhs_operand_expr(a)?;
                    if rhs != CExpr::IntLit(0) {
                        return Some(CExpr::binary(
                            BinaryOp::Add,
                            CExpr::Var(lhs_name.to_string()),
                            rhs,
                        ));
                    }
                }
            }
            SSAOp::IntSub { a, b, .. } if self.value_loads_from_store_addr(a, store_addr, 0) => {
                let delta = Self::small_const_delta(b)?;
                if delta != 0 {
                    return Some(CExpr::binary(
                        BinaryOp::Sub,
                        CExpr::Var(lhs_name.to_string()),
                        CExpr::IntLit(delta),
                    ));
                }
            }
            _ => {}
        }

        for lhs_offset in self.stack_offsets_for_visible_storage_name(lhs_name) {
            let (base, delta, is_sub) = match producer {
                SSAOp::IntAdd { a, b, .. } => {
                    if self.stack_slot_load_offset_for_value(a, 0) == Some(lhs_offset) {
                        (a, Self::small_const_delta(b)?, false)
                    } else if self.stack_slot_load_offset_for_value(b, 0) == Some(lhs_offset) {
                        (b, Self::small_const_delta(a)?, false)
                    } else {
                        continue;
                    }
                }
                SSAOp::IntSub { a, b, .. } => {
                    if self.stack_slot_load_offset_for_value(a, 0) == Some(lhs_offset) {
                        (a, Self::small_const_delta(b)?, true)
                    } else {
                        continue;
                    }
                }
                _ => return None,
            };
            if delta == 0 || self.stack_slot_load_offset_for_value(base, 0) != Some(lhs_offset) {
                continue;
            }
            let max_delta = self
                .lookup_type_hint(lhs_name)
                .and_then(|ty| c_type_size_bytes(ty, self.inputs.arch.ptr_size))
                .unwrap_or(1)
                .max(1);
            if delta.unsigned_abs() > max_delta {
                continue;
            }
            return Some(CExpr::binary(
                if is_sub { BinaryOp::Sub } else { BinaryOp::Add },
                CExpr::Var(lhs_name.to_string()),
                CExpr::IntLit(delta),
            ));
        }
        None
    }

    fn is_pointer_typed_var(&self, var: &SSAVar) -> bool {
        self.type_hint_for_var(var)
            .is_some_and(|ty| matches!(ty, CType::Pointer(_)))
    }

    fn literal_to_i64(&self, expr: &CExpr) -> Option<i64> {
        match expr {
            CExpr::IntLit(v) => Some(*v),
            CExpr::UIntLit(v) => i64::try_from(*v).ok(),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => self.literal_to_i64(inner),
            CExpr::Binary { op, left, right } => {
                let left = self.literal_to_i64(left)?;
                let right = self.literal_to_i64(right)?;
                match op {
                    BinaryOp::Add => left.checked_add(right),
                    BinaryOp::Sub => left.checked_sub(right),
                    BinaryOp::Mul => left.checked_mul(right),
                    BinaryOp::BitAnd => Some(left & right),
                    BinaryOp::BitOr => Some(left | right),
                    BinaryOp::BitXor => Some(left ^ right),
                    BinaryOp::Shl => {
                        if !(0..=62).contains(&right) {
                            return None;
                        }
                        left.checked_mul(1i64 << right)
                    }
                    BinaryOp::Shr => {
                        if !(0..=62).contains(&right) {
                            return None;
                        }
                        Some(left >> right)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn expr_mentions_stack_or_ip(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = name.to_lowercase();
                self.inputs.arch.is_stack_pointer_name(&lower)
                    || self.inputs.arch.is_frame_pointer_name(&lower)
                    || lower == "pc"
                    || lower.starts_with("pc_")
                    || lower == "lr"
                    || lower.starts_with("lr_")
                    || lower == "ra"
                    || lower.starts_with("ra_")
                    || lower == "x30"
                    || lower.starts_with("x30_")
                    || lower.contains("rip")
                    || lower.contains("eip")
            }
            CExpr::Unary { operand, .. } => self.expr_mentions_stack_or_ip(operand),
            CExpr::Binary { left, right, .. } => {
                self.expr_mentions_stack_or_ip(left) || self.expr_mentions_stack_or_ip(right)
            }
            CExpr::Paren(inner) => self.expr_mentions_stack_or_ip(inner),
            CExpr::Cast { expr: inner, .. } => self.expr_mentions_stack_or_ip(inner),
            CExpr::Deref(inner) => self.expr_mentions_stack_or_ip(inner),
            _ => false,
        }
    }

    fn is_low_level_return_artifact(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Deref(inner) => self.expr_mentions_stack_or_ip(inner),
            CExpr::Var(_) => self.expr_mentions_stack_or_ip(expr),
            CExpr::Paren(inner) => self.is_low_level_return_artifact(inner),
            CExpr::Cast { expr: inner, .. } => self.is_low_level_return_artifact(inner),
            _ => false,
        }
    }

    /// Check if `expr` is a version-0 return register (e.g. `RAX_0`, `EAX_0`,
    /// `XMM0_0`).  These appear in exit blocks when phi nodes merge uninitialized
    /// entry values and should be replaced by the last meaningful computed value.
    pub(crate) fn is_uninitialized_return_reg(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = name.to_lowercase();
                lower.ends_with("_0")
                    && self
                        .inputs
                        .arch
                        .is_return_register_name(lower.trim_end_matches("_0"))
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_uninitialized_return_reg(inner)
            }
            _ => false,
        }
    }

    fn is_uninitialized_return_register_var(&self, var: &SSAVar) -> bool {
        var.version == 0
            && self
                .inputs
                .arch
                .is_return_register_name(&var.name.to_ascii_lowercase())
    }

    fn is_return_register_var(&self, var: &SSAVar) -> bool {
        self.inputs
            .arch
            .is_return_register_name(&var.name.to_ascii_lowercase())
    }

    fn is_uninitialized_return_register_copy(&self, dst: &SSAVar, src: &SSAVar) -> bool {
        self.is_return_register_var(dst)
            && self.is_uninitialized_return_register_var(src)
            && !self.is_certified_loop_carrier_phi_copy(dst, src)
    }

    fn resolve_return_expr_from_defs(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return None;
        }

        match expr {
            CExpr::Paren(inner) => self.resolve_return_expr_from_defs(inner, depth + 1, visited),
            CExpr::Cast { ty, expr: inner } => self
                .resolve_return_expr_from_defs(inner, depth + 1, visited)
                .map(|resolved| CExpr::cast(ty.clone(), resolved)),
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return None;
                }

                let resolved = self.best_visible_definition(name).and_then(|def| {
                    if def == CExpr::Var(name.clone()) {
                        return None;
                    }
                    self.resolve_return_expr_from_defs(&def, depth + 1, visited)
                        .or(Some(def))
                });

                visited.remove(name);
                resolved
            }
            _ => None,
        }
    }

    fn resolve_return_target_expr(
        &self,
        target_expr: CExpr,
        last_ret_value: Option<CExpr>,
    ) -> CExpr {
        let mut best = Some(target_expr.clone());
        let mut visited = HashSet::new();
        if let Some(resolved) = self.resolve_return_expr_from_defs(&target_expr, 0, &mut visited)
            && resolved != target_expr
        {
            best = self.preferred_return_candidate(best, Some(resolved));
        }

        if let Some(last) = last_ret_value {
            let last = self.resolve_return_candidate(&last);
            best = self.preferred_return_candidate(best, Some(last));
        }

        best.unwrap_or(target_expr)
    }

    fn normalize_final_return_candidate(&self, expr: CExpr) -> CExpr {
        if self.is_certified_rendered_call_expr(&expr) {
            return self
                .stable_owner_for_certified_rendered_call_expr(&expr)
                .unwrap_or(expr);
        }
        let rewritten = self.rewrite_stack_expr(expr);
        if self.is_certified_rendered_call_expr(&rewritten) {
            return self
                .stable_owner_for_certified_rendered_call_expr(&rewritten)
                .unwrap_or(rewritten);
        }
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&rewritten, 0, &mut semantic_visited);
        if self.is_predicate_like_expr(&semanticized) {
            self.simplify_condition_expr(semanticized)
        } else {
            semanticized
        }
    }

    fn is_certified_rendered_call_expr(&self, expr: &CExpr) -> bool {
        self.certified_source_for_rendered_call_expr(expr, None)
            .is_some()
    }

    pub(super) fn stable_owner_for_certified_rendered_call_expr(
        &self,
        expr: &CExpr,
    ) -> Option<CExpr> {
        let source = self.certified_source_for_rendered_call_expr(expr, None)?;
        let owner = self.stable_owned_call_result_expr_for_source(source)?;
        match &owner {
            CExpr::Var(name)
                if !self
                    .inputs
                    .arch
                    .is_return_register_name(&name.to_ascii_lowercase())
                    && !self.is_transient_visible_name(name)
                    && !self.is_low_signal_visible_name(name)
                    && !is_generic_stack_placeholder_alias(name) =>
            {
                Some(owner)
            }
            CExpr::Var(_) => None,
            _ => Some(owner),
        }
    }

    fn should_emit_return_slot_assignment(&self, offset: i64, value: &CExpr) -> bool {
        let is_scalar_return_slot = self
            .use_info()
            .stack_slots()
            .any(|slot| slot.offset == offset && slot.is_scalar_return_carrier());
        let is_return_slot =
            is_scalar_return_slot || self.state.return_stack_slots.contains(&offset);
        if !is_return_slot {
            return true;
        }

        match value {
            CExpr::Var(name) => {
                !(self.arg_alias_for_rendered_name(name).is_some()
                    || is_generic_arg_name(name)
                    || self.is_named_scalar_local(name))
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.should_emit_return_slot_assignment(offset, inner)
            }
            _ => true,
        }
    }

    fn is_control_return_target(&self, target: &SSAVar) -> bool {
        let lower = target.name.to_ascii_lowercase();
        lower == "pc"
            || lower == "lr"
            || lower == "ra"
            || lower == "x30"
            || lower.starts_with("pc_")
            || lower.starts_with("lr_")
            || lower.starts_with("ra_")
            || lower.starts_with("x30_")
            || lower == "rip"
            || lower == "eip"
            || lower.starts_with("rip_")
            || lower.starts_with("eip_")
    }

    pub(super) fn lookup_definition(&self, name: &str) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::Definition, name) {
            return self.resolution_cycle_fallback(name);
        }
        let result = self.lookup_definition_with_depth(name, 0, &mut HashSet::new());
        self.leave_resolution_guard(ResolutionPhase::Definition, name);
        result
    }

    fn render_candidate_rank(source: RenderCandidateSource) -> usize {
        match source {
            RenderCandidateSource::ExactNameDefinition => 0,
            RenderCandidateSource::SemanticValue => 1,
            RenderCandidateSource::ForwardedValue => 2,
            RenderCandidateSource::ValueDefinition => 3,
            RenderCandidateSource::AliasDefinition => 4,
            RenderCandidateSource::RawDefinition => 5,
        }
    }

    fn choose_preferred_render_candidate(
        &self,
        current: Option<RenderCandidate>,
        candidate: Option<RenderCandidate>,
        context: VisibleExprContext,
    ) -> Option<RenderCandidate> {
        match (current, candidate) {
            (None, None) => None,
            (Some(current), None) => Some(current),
            (None, Some(candidate)) => Some(candidate),
            (Some(current), Some(candidate)) => {
                let chosen = self.choose_preferred_visible_expr_in_context(
                    Some(current.expr.clone()),
                    Some(candidate.expr.clone()),
                    context,
                );
                match chosen {
                    Some(expr) if expr == current.expr && expr != candidate.expr => Some(current),
                    Some(expr) if expr == candidate.expr && expr != current.expr => Some(candidate),
                    Some(_) => {
                        if Self::render_candidate_rank(candidate.source)
                            < Self::render_candidate_rank(current.source)
                        {
                            Some(candidate)
                        } else {
                            Some(current)
                        }
                    }
                    None => None,
                }
            }
        }
    }

    fn render_candidate_for_value_id_with_depth(
        &self,
        value_id: r2ssa::ValueId,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<RenderCandidate> {
        let mut best =
            self.definition_for_value_id(value_id)
                .cloned()
                .map(|expr| RenderCandidate {
                    expr,
                    source: RenderCandidateSource::ValueDefinition,
                });

        let mut semantic_visited = visited.clone();
        let semantic = self
            .semantic_value_for_value_id(value_id)
            .and_then(|value| self.render_semantic_value(value, depth, &mut semantic_visited))
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::SemanticValue,
            });
        best = self.choose_preferred_render_candidate(best, semantic, VisibleExprContext::Generic);

        let forwarded = self
            .forwarded_value_for_value_id(value_id)
            .and_then(|prov| {
                self.lookup_definition_with_depth(&prov.source, depth + 1, visited)
                    .or_else(|| Some(self.expr_for_ssa_fallback_name(&prov.source)))
            })
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::ForwardedValue,
            });
        self.choose_preferred_render_candidate(best, forwarded, VisibleExprContext::Generic)
    }

    fn direct_definition_expr(&self, name: &str) -> Option<CExpr> {
        self.use_info().render_definition_for_name(name).cloned()
    }

    fn lookup_definition_with_depth(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let visit_key = self.resolution_name_key("def", name);
        if depth > MAX_SIMPLE_EXPR_DEPTH || !visited.insert(visit_key.clone()) {
            return None;
        }
        let in_progress_key = self.resolution_name_key("def-progress", name);
        {
            let mut in_progress = self.definition_lookup_in_progress.borrow_mut();
            if !in_progress.insert(in_progress_key.clone()) {
                visited.remove(&visit_key);
                return self.direct_definition_expr(name);
            }
        }

        if let Some(owner) = self.preserved_owned_call_result_var_for_name(name) {
            visited.remove(&visit_key);
            self.definition_lookup_in_progress
                .borrow_mut()
                .remove(&in_progress_key);
            return Some(owner);
        }

        let mut best = self.value_id_for_name(name).and_then(|value_id| {
            self.render_candidate_for_value_id_with_depth(value_id, depth, visited)
        });

        let exact = self
            .direct_definition_expr(name)
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::ExactNameDefinition,
            });
        best = self.choose_preferred_render_candidate(best, exact, VisibleExprContext::Generic);

        let semantic = self
            .render_semantic_value_by_name(name, depth, visited)
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::SemanticValue,
            });
        best = self.choose_preferred_render_candidate(best, semantic, VisibleExprContext::Generic);

        let raw = self
            .lookup_definition_raw_with_depth(name, depth + 1, visited)
            .map(|expr| {
                let expr = if matches!(&expr, CExpr::Var(raw_name) if self.should_preserve_address_like_visible_name(raw_name))
                    || matches!(&expr, CExpr::AddrOf(inner) if matches!(inner.as_ref(), CExpr::Var(raw_name) if !self.is_low_signal_visible_name(raw_name) && !self.is_transient_visible_name(raw_name)))
                {
                    expr
                } else {
                    let semanticized = self.semanticize_visible_expr(&expr, depth + 1, visited);
                    if (Self::expr_is_scalar_memory_candidate(&expr)
                        || Self::expr_is_structured_memory_candidate(&expr))
                        && !Self::expr_is_scalar_memory_candidate(&semanticized)
                        && !Self::expr_is_structured_memory_candidate(&semanticized)
                    {
                        expr
                    } else if self.prefers_visible_expr(&expr, &semanticized) {
                        semanticized
                    } else {
                        expr
                    }
                };
                RenderCandidate {
                    expr,
                    source: RenderCandidateSource::RawDefinition,
                }
            });
        best = self.choose_preferred_render_candidate(best, raw, VisibleExprContext::Generic);

        if let Some(prov) = self.forwarded_value_for_name(name) {
            let resolved = self
                .lookup_definition_with_depth(&prov.source, depth + 1, visited)
                .or_else(|| Some(self.expr_for_ssa_fallback_name(&prov.source)));
            best = self.choose_preferred_render_candidate(
                best,
                resolved.map(|expr| RenderCandidate {
                    expr,
                    source: RenderCandidateSource::ForwardedValue,
                }),
                VisibleExprContext::Generic,
            );
        }

        let rendered = self
            .find_ssa_name_for_rendered_alias(name)
            .and_then(|ssa_name| self.lookup_definition_with_depth(&ssa_name, depth + 1, visited))
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::AliasDefinition,
            });
        best = self.choose_preferred_render_candidate(best, rendered, VisibleExprContext::Generic);
        self.definition_lookup_in_progress
            .borrow_mut()
            .remove(&in_progress_key);
        visited.remove(&visit_key);
        best.map(|candidate| candidate.expr)
    }

    pub(super) fn lookup_definition_raw(&self, name: &str) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::DefinitionRaw, name) {
            return self.resolution_cycle_fallback(name);
        }
        let result = self.lookup_definition_raw_with_depth(name, 0, &mut HashSet::new());
        self.leave_resolution_guard(ResolutionPhase::DefinitionRaw, name);
        result
    }

    fn lookup_definition_raw_with_depth(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let visit_key = self.resolution_name_key("defraw", name);
        if depth > MAX_ALIAS_REWRITE_DEPTH || !visited.insert(visit_key.clone()) {
            return None;
        }
        let in_progress_key = self.resolution_name_key("defraw-progress", name);
        {
            let mut in_progress = self.definition_raw_in_progress.borrow_mut();
            if !in_progress.insert(in_progress_key.clone()) {
                visited.remove(&visit_key);
                return self.direct_definition_expr(name);
            }
        }

        let mut best = self
            .direct_definition_expr(name)
            .map(|expr| RenderCandidate {
                expr,
                source: RenderCandidateSource::ExactNameDefinition,
            });
        if let Some(value_id) = self.value_id_for_name(name) {
            best = self.choose_preferred_render_candidate(
                best,
                self.definition_for_value_id(value_id)
                    .cloned()
                    .map(|expr| RenderCandidate {
                        expr,
                        source: RenderCandidateSource::ValueDefinition,
                    }),
                VisibleExprContext::Generic,
            );
        }
        if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
            && ssa_name != name
        {
            best = self.choose_preferred_render_candidate(
                best,
                self.lookup_definition_raw_with_depth(&ssa_name, depth + 1, visited)
                    .map(|expr| RenderCandidate {
                        expr,
                        source: RenderCandidateSource::AliasDefinition,
                    }),
                VisibleExprContext::Generic,
            );
        }
        self.definition_raw_in_progress
            .borrow_mut()
            .remove(&in_progress_key);
        visited.remove(&visit_key);
        best.map(|candidate| candidate.expr)
    }

    pub(super) fn find_ssa_name_for_rendered_alias(&self, name: &str) -> Option<String> {
        if let Some(cached) = self.rendered_alias_lookup_cache.borrow().get(name).cloned() {
            return cached;
        }
        self.rendered_alias_lookup_cache
            .borrow_mut()
            .insert(name.to_string(), None);

        let mut temp_matches = self.ssa_names_for_lowered_temp_alias(name);
        let resolved = if !temp_matches.is_empty() {
            temp_matches.sort_by(|a, b| {
                let a_key = self.ssa_alias_preference_key(a);
                let b_key = self.ssa_alias_preference_key(b);
                let (a_base, a_version) = Self::ssa_name_parts(a);
                let (b_base, b_version) = Self::ssa_name_parts(b);
                b_key
                    .cmp(&a_key)
                    .then_with(|| b_version.cmp(&a_version))
                    .then_with(|| a_base.cmp(b_base))
                    .then_with(|| a.cmp(b))
            });
            temp_matches.into_iter().next()
        } else if let Some(preferred) = self.preferred_entry_arg_ssa_name(name)
            && (self.has_renderable_named_fact(&preferred)
                || self.var_aliases_map().contains_key(&preferred))
        {
            Some(preferred)
        } else {
            let mut matches = self
                .var_aliases_map()
                .iter()
                .filter(|(_, alias)| alias.eq_ignore_ascii_case(name))
                .map(|(ssa_name, _)| ssa_name.clone())
                .collect::<Vec<_>>();
            matches.sort_by(|a, b| {
                let a_key = self.ssa_alias_preference_key(a);
                let b_key = self.ssa_alias_preference_key(b);
                let (a_base, a_version) = Self::ssa_name_parts(a);
                let (b_base, b_version) = Self::ssa_name_parts(b);
                b_key
                    .cmp(&a_key)
                    .then_with(|| b_version.cmp(&a_version))
                    .then_with(|| a_base.cmp(b_base))
                    .then_with(|| a.cmp(b))
            });
            matches.into_iter().next()
        };

        self.rendered_alias_lookup_cache
            .borrow_mut()
            .insert(name.to_string(), resolved.clone());
        resolved
    }

    fn ssa_alias_preference_key(&self, ssa_name: &str) -> (bool, bool, VisibleExprQuality) {
        let candidate = self
            .semantic_value_for_name(ssa_name)
            .and_then(|value| self.render_semantic_value(value, 0, &mut HashSet::new()))
            .or_else(|| self.definition_for_name(ssa_name).cloned());
        match candidate {
            Some(expr) => (
                self.is_direct_constish_visible_expr(&expr, 0),
                matches!(expr, CExpr::StringLit(_)),
                self.visible_expr_quality(&expr),
            ),
            None => (false, false, VisibleExprQuality::default()),
        }
    }

    fn is_direct_constish_visible_expr(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }
        match expr {
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::StringLit(_) => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_direct_constish_visible_expr(inner, depth + 1)
            }
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => {
                self.is_direct_constish_visible_expr(left, depth + 1)
                    && self.is_direct_constish_visible_expr(right, depth + 1)
            }
            _ => false,
        }
    }

    fn ssa_names_for_lowered_temp_alias(&self, name: &str) -> Vec<String> {
        let Some((is_temp_alias, alias_base, alias_version)) = Self::parse_lowered_temp_alias(name)
        else {
            return Vec::new();
        };

        let mut matches = self
            .known_named_values()
            .into_iter()
            .filter(|ssa_name| {
                let (base, ssa_version) = Self::ssa_name_parts(ssa_name);
                let base_matches = if is_temp_alias {
                    base.to_ascii_lowercase()
                        .strip_prefix("tmp:")
                        .is_some_and(|temp_base| {
                            alias_base.is_empty() || temp_base.eq_ignore_ascii_case(alias_base)
                        })
                } else {
                    !SSAVarNameKind::classify(base).is_temporary()
                };

                if alias_version != ssa_version || !base_matches {
                    return false;
                }

                if is_temp_alias {
                    true
                } else {
                    name.starts_with('v')
                }
            })
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();
        matches
    }

    fn parse_lowered_temp_alias(name: &str) -> Option<(bool, &str, u32)> {
        if let Some(rest) = name.strip_prefix('t') {
            if let Some((alias_base, alias_version)) = rest.rsplit_once('_') {
                let alias_version = alias_version.parse::<u32>().ok()?;
                return Some((true, alias_base, alias_version));
            }
            let version = rest
                .chars()
                .all(|ch| ch.is_ascii_digit())
                .then(|| rest.parse::<u32>().ok())
                .flatten()?;
            return Some((true, "", version));
        }

        let version = name
            .strip_prefix('v')
            .filter(|suffix| !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit()))
            .and_then(|suffix| suffix.parse::<u32>().ok())?;
        Some((false, "", version))
    }

    fn ssa_name_parts(name: &str) -> (&str, u32) {
        match name.rsplit_once('_') {
            Some((base, version)) if version.chars().all(|ch| ch.is_ascii_digit()) => {
                (base, version.parse::<u32>().unwrap_or(0))
            }
            _ => (name, 0),
        }
    }

    fn preferred_entry_arg_ssa_name(&self, name: &str) -> Option<String> {
        if let Some(cached) = self
            .preferred_entry_arg_lookup_cache
            .borrow()
            .get(name)
            .cloned()
        {
            return cached;
        }

        let resolved = if is_generic_arg_name(name) {
            self.var_aliases_map()
                .iter()
                .filter(|(ssa_name, alias)| {
                    alias.eq_ignore_ascii_case(name) && Self::ssa_name_parts(ssa_name).1 == 0
                })
                .map(|(ssa_name, _)| ssa_name.clone())
                .min()
        } else {
            let base = name
                .rsplit_once('_')
                .map(|(root, _)| root)
                .unwrap_or(name)
                .to_ascii_lowercase();
            if self.arg_alias_for_register_name(&base).is_none() {
                None
            } else {
                self.var_aliases_map()
                    .keys()
                    .filter(|ssa_name| {
                        let (ssa_base, version) = Self::ssa_name_parts(ssa_name);
                        version == 0 && ssa_base.eq_ignore_ascii_case(&base)
                    })
                    .cloned()
                    .min()
            }
        };

        self.preferred_entry_arg_lookup_cache
            .borrow_mut()
            .insert(name.to_string(), resolved.clone());
        resolved
    }

    fn expr_for_ssa_fallback_name(&self, ssa_name: &str) -> CExpr {
        if parse_const_value(ssa_name).is_some() {
            return CExpr::Var(ssa_name.to_string());
        }
        if let Some(alias) = self.var_aliases_map().get(ssa_name) {
            return CExpr::Var(alias.clone());
        }
        CExpr::Var(ssa_name.to_string())
    }

    fn semanticize_visible_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => {
                if self.should_preserve_address_like_visible_name(name) {
                    return expr.clone();
                }
                if self.should_preserve_owned_call_result_visible_name(name) {
                    return expr.clone();
                }
                if let Some(owner) = self.stable_owned_call_result_expr_for_name(name, true)
                    && !matches!(&owner, CExpr::Var(owner_name) if owner_name.eq_ignore_ascii_case(name))
                {
                    return owner;
                }
                if let Some(semantic) = self
                    .render_semantic_value_by_name(name, depth + 1, visited)
                    .map(|candidate| {
                        if self.is_low_signal_visible_name(name)
                            && matches!(candidate, CExpr::Var(_))
                            && let Some(deref) = self.semantic_deref_candidate_for_name(name)
                            && deref != candidate
                        {
                            deref
                        } else {
                            candidate
                        }
                    })
                    .filter(|candidate| {
                        !self.requires_certified_rendering()
                            || !Self::expr_contains_structured_memory_syntax(candidate)
                    })
                    && (self.prefers_visible_expr(expr, &semantic)
                        || (self.is_low_signal_visible_name(name)
                            && matches!(
                                semantic,
                                CExpr::Subscript { .. }
                                    | CExpr::Member { .. }
                                    | CExpr::PtrMember { .. }
                                    | CExpr::Deref(_)
                            )))
                {
                    return semantic;
                }
                if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
                    && ssa_name != *name
                {
                    if let Some(semantic) = self
                        .render_semantic_value_by_name(&ssa_name, depth + 1, visited)
                        .map(|candidate| {
                            if self.is_low_signal_visible_name(name)
                                && matches!(candidate, CExpr::Var(_))
                                && let Some(deref) = self.semantic_deref_candidate_for_name(name)
                                && deref != candidate
                            {
                                deref
                            } else {
                                candidate
                            }
                        })
                        .filter(|candidate| {
                            !self.requires_certified_rendering()
                                || !Self::expr_contains_structured_memory_syntax(candidate)
                        })
                        && (self.prefers_visible_expr(expr, &semantic)
                            || (self.is_low_signal_visible_name(name)
                                && matches!(
                                    semantic,
                                    CExpr::Subscript { .. }
                                        | CExpr::Member { .. }
                                        | CExpr::PtrMember { .. }
                                        | CExpr::Deref(_)
                                )))
                    {
                        return semantic;
                    }
                    if let Some(def) =
                        self.lookup_definition_raw_with_depth(&ssa_name, depth + 1, visited)
                        && !matches!(&def, CExpr::Var(inner) if inner.eq_ignore_ascii_case(name))
                    {
                        let semanticized = self.semanticize_visible_expr(&def, depth + 1, visited);
                        let best = self
                            .choose_preferred_visible_expr(Some(def.clone()), Some(semanticized))
                            .unwrap_or(def);
                        if self.prefers_visible_expr(expr, &best) {
                            return best;
                        }
                    }
                }
                let visit_key = format!("vis:{name}");
                if visited.insert(visit_key.clone()) {
                    if let Some(def) =
                        self.lookup_definition_raw_with_depth(name, depth + 1, visited)
                        && !matches!(&def, CExpr::Var(inner) if inner == name)
                    {
                        let semanticized = self.semanticize_visible_expr(&def, depth + 1, visited);
                        let best = self
                            .choose_preferred_visible_expr(Some(def.clone()), Some(semanticized))
                            .unwrap_or(def);
                        if self.prefers_visible_expr(expr, &best) {
                            visited.remove(&visit_key);
                            return best;
                        }
                    }
                    visited.remove(&visit_key);
                }
                expr.clone()
            }
            CExpr::Deref(inner) => {
                if let CExpr::Var(name) = inner.as_ref()
                    && let Some(candidate) = self.semantic_deref_candidate_for_name(name)
                {
                    return candidate;
                }

                let semantic_inner = self.semanticize_visible_expr(inner, depth + 1, visited);
                if self.should_preserve_indirect_local_deref(&semantic_inner) {
                    return CExpr::Deref(Box::new(semantic_inner));
                }
                if let Some(access) = self.render_memory_access_from_visible_expr(
                    &semantic_inner,
                    0,
                    depth + 1,
                    visited,
                ) {
                    return access;
                }
                CExpr::Deref(Box::new(semantic_inner))
            }
            CExpr::Cast { ty, expr: inner } => CExpr::cast(
                ty.clone(),
                self.semanticize_visible_expr(inner, depth + 1, visited),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.semanticize_visible_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Unary { op, operand } => CExpr::unary(
                *op,
                self.semanticize_visible_expr(operand, depth + 1, visited),
            ),
            CExpr::Binary { op, left, right } => {
                if matches!(op, BinaryOp::BitAnd | BinaryOp::BitOr)
                    && let (Some(left_source), Some(right_source)) = (
                        self.call_result_source_for_idempotent_operand(left),
                        self.call_result_source_for_idempotent_operand(right),
                    )
                    && left_source == right_source
                    && let Some(call_expr) = self
                        .call_result_exprs_map()
                        .get(&left_source)
                        .cloned()
                        .map(|expr| {
                            self.normalize_call_expr_for_source_call(
                                left_source,
                                expr,
                                FinalExprNormalizeContext::Generic,
                            )
                        })
                        .or_else(|| self.synthesized_call_expr_for_source_call(left_source))
                {
                    return call_expr;
                }
                CExpr::binary(
                    *op,
                    self.semanticize_visible_expr(left, depth + 1, visited),
                    self.semanticize_visible_expr(right, depth + 1, visited),
                )
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(self.semanticize_visible_expr(cond, depth + 1, visited)),
                then_expr: Box::new(self.semanticize_visible_expr(then_expr, depth + 1, visited)),
                else_expr: Box::new(self.semanticize_visible_expr(else_expr, depth + 1, visited)),
            },
            CExpr::Call { func, args } => CExpr::Call {
                func: Box::new(self.semanticize_visible_expr(func, depth + 1, visited)),
                args: args
                    .iter()
                    .map(|arg| self.semanticize_visible_expr(arg, depth + 1, visited))
                    .collect(),
            },
            CExpr::Subscript { base, index } => {
                let semantic_base = self.semanticize_visible_expr(base, depth + 1, visited);
                let semantic_index = self.semanticize_visible_expr(index, depth + 1, visited);
                let rebuilt = CExpr::Subscript {
                    base: Box::new(semantic_base.clone()),
                    index: Box::new(semantic_index.clone()),
                };
                let access = self.render_exact_member_from_raw_subscript(
                    &semantic_base,
                    &semantic_index,
                    depth + 1,
                    visited,
                );
                if let Some(access) = access
                    && self.prefers_visible_expr(&rebuilt, &access)
                {
                    return access;
                }
                rebuilt
            }
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(self.semanticize_visible_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(self.semanticize_visible_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::Sizeof(inner) => CExpr::Sizeof(Box::new(self.semanticize_visible_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::AddrOf(inner) => {
                if matches!(
                    inner.as_ref(),
                    CExpr::Var(name)
                        if !self.is_low_signal_visible_name(name)
                            && !self.is_transient_visible_name(name)
                            && !is_generic_stack_placeholder_alias(name)
                ) {
                    return expr.clone();
                }
                CExpr::AddrOf(Box::new(self.semanticize_visible_expr(
                    inner,
                    depth + 1,
                    visited,
                )))
            }
            CExpr::Comma(items) => CExpr::Comma(
                items
                    .iter()
                    .map(|item| self.semanticize_visible_expr(item, depth + 1, visited))
                    .collect(),
            ),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => expr.clone(),
        }
    }

    fn certified_semanticize_visible_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => self
                .certified_semanticized_var_expr(name, depth, visited)
                .unwrap_or_else(|| expr.clone()),
            CExpr::Deref(inner) => CExpr::Deref(Box::new(self.certified_semanticize_visible_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Cast { ty, expr: inner } => CExpr::cast(
                ty.clone(),
                self.certified_semanticize_visible_expr(inner, depth + 1, visited),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.certified_semanticize_visible_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Unary { op, operand } => CExpr::unary(
                *op,
                self.certified_semanticize_visible_expr(operand, depth + 1, visited),
            ),
            CExpr::Binary { op, left, right } => CExpr::binary(
                *op,
                self.certified_semanticize_visible_expr(left, depth + 1, visited),
                self.certified_semanticize_visible_expr(right, depth + 1, visited),
            ),
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(self.certified_semanticize_visible_expr(cond, depth + 1, visited)),
                then_expr: Box::new(self.certified_semanticize_visible_expr(
                    then_expr,
                    depth + 1,
                    visited,
                )),
                else_expr: Box::new(self.certified_semanticize_visible_expr(
                    else_expr,
                    depth + 1,
                    visited,
                )),
            },
            CExpr::Call { func, args } => CExpr::Call {
                func: Box::new(self.certified_semanticize_visible_expr(func, depth + 1, visited)),
                args: args
                    .iter()
                    .map(|arg| self.certified_semanticize_visible_expr(arg, depth + 1, visited))
                    .collect(),
            },
            CExpr::Subscript { base, index } => CExpr::Subscript {
                base: Box::new(self.certified_semanticize_visible_expr(base, depth + 1, visited)),
                index: Box::new(self.certified_semanticize_visible_expr(index, depth + 1, visited)),
            },
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(self.certified_semanticize_visible_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(self.certified_semanticize_visible_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::Sizeof(inner) => CExpr::Sizeof(Box::new(
                self.certified_semanticize_visible_expr(inner, depth + 1, visited),
            )),
            CExpr::AddrOf(inner) => CExpr::AddrOf(Box::new(
                self.certified_semanticize_visible_expr(inner, depth + 1, visited),
            )),
            CExpr::Comma(items) => CExpr::Comma(
                items
                    .iter()
                    .map(|item| self.certified_semanticize_visible_expr(item, depth + 1, visited))
                    .collect(),
            ),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => expr.clone(),
        }
    }

    fn certified_semanticized_var_expr(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        if self.should_preserve_address_like_visible_name(name)
            || self.should_preserve_owned_call_result_visible_name(name)
        {
            return None;
        }
        if let Some(owner) = self.stable_owned_call_result_expr_for_name(name, true)
            && !matches!(&owner, CExpr::Var(owner_name) if owner_name.eq_ignore_ascii_case(name))
        {
            return Some(owner);
        }

        let visit_key = format!("cert-sem:{name}");
        if !visited.insert(visit_key.clone()) {
            return None;
        }
        let rendered = self
            .certified_prepared_var_for_visible_name(name)
            .and_then(|var| self.render_certified_value_expr_for_var(var))
            .filter(|candidate| {
                self.prefers_visible_expr(&CExpr::Var(name.to_string()), candidate)
            });
        visited.remove(&visit_key);
        rendered
    }

    fn certified_prepared_var_for_visible_name(&self, name: &str) -> Option<&SSAVar> {
        let prepared = self.inputs.prepared_ssa?;
        prepared
            .function()
            .blocks()
            .flat_map(|block| block.ops.iter())
            .filter_map(SSAOp::dst)
            .find(|var| var.display_name().eq_ignore_ascii_case(name))
    }

    fn canonicalize_visible_address_expr(&self, expr: &CExpr, depth: u32) -> CExpr {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Paren(inner) => CExpr::Paren(Box::new(
                self.canonicalize_visible_address_expr(inner, depth + 1),
            )),
            CExpr::Cast { ty, expr: inner } => CExpr::cast(
                ty.clone(),
                self.canonicalize_visible_address_expr(inner, depth + 1),
            ),
            CExpr::Unary { op, operand } => CExpr::unary(
                *op,
                self.canonicalize_visible_address_expr(operand, depth + 1),
            ),
            CExpr::Binary { op, left, right } => {
                let left = self.canonicalize_visible_address_expr(left, depth + 1);
                let right = self.canonicalize_visible_address_expr(right, depth + 1);
                if matches!(op, BinaryOp::BitXor) && left == right {
                    return CExpr::IntLit(0);
                }
                self.identity_simplify_binary(*op, left, right, None)
            }
            _ => expr.clone(),
        }
    }

    #[cfg(test)]
    pub(crate) fn debug_semanticize_visible_expr(&self, expr: &CExpr) -> CExpr {
        let mut visited = HashSet::new();
        self.semanticize_visible_expr(expr, 0, &mut visited)
    }

    fn call_result_source_for_idempotent_operand(&self, expr: &CExpr) -> Option<(u64, usize)> {
        match expr {
            CExpr::Var(name) => self
                .call_result_source_for_ssa_name(name)
                .or_else(|| self.local_post_call_source_for_ssa_name(name)),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.call_result_source_for_idempotent_operand(inner)
            }
            _ => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn debug_choose_generic_visible_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            current,
            candidate,
            VisibleExprContext::Generic,
        )
    }

    #[cfg(test)]
    pub(crate) fn debug_choose_scalar_predicate_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            current,
            candidate,
            VisibleExprContext::ScalarPredicate,
        )
    }

    #[cfg(test)]
    pub(crate) fn debug_choose_scalar_return_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
    ) -> Option<CExpr> {
        self.choose_preferred_visible_expr_in_context(
            current,
            candidate,
            VisibleExprContext::ScalarReturn,
        )
    }

    #[cfg(test)]
    pub(crate) fn debug_resolve_prepared_predicate_operand(&self, var: &SSAVar) -> CExpr {
        self.resolve_prepared_predicate_operand(var)
    }

    #[cfg(test)]
    pub(crate) fn debug_stack_slot_provenance(
        &self,
        name: &str,
    ) -> Option<analysis::StackSlotProvenance> {
        self.stack_slot_provenance_for_name(name)
    }

    #[cfg(test)]
    pub(crate) fn debug_render_memory_access_from_visible_expr(
        &self,
        expr: &CExpr,
        elem_size: u32,
    ) -> Option<CExpr> {
        let mut visited = HashSet::new();
        self.render_memory_access_from_visible_expr(expr, elem_size, 0, &mut visited)
    }

    #[cfg(test)]
    pub(crate) fn debug_normalized_addr_from_visible_expr(
        &self,
        expr: &CExpr,
    ) -> Option<analysis::NormalizedAddr> {
        self.normalized_addr_from_visible_expr(expr, 0)
    }

    #[cfg(test)]
    pub(crate) fn debug_ssa_var_for_visible_name(&self, name: &str) -> Option<SSAVar> {
        self.ssa_var_for_visible_name(name)
    }

    #[cfg(test)]
    pub(crate) fn debug_canonicalize_visible_address_expr(&self, expr: &CExpr) -> CExpr {
        self.canonicalize_visible_address_expr(expr, 0)
    }

    #[cfg(test)]
    pub(crate) fn debug_extract_visible_scaled_index(
        &self,
        expr: &CExpr,
    ) -> Option<(analysis::ValueRef, i64)> {
        self.extract_visible_scaled_index(expr, 0)
    }

    fn evaluate_constish_call_arg_expr(&self, expr: &CExpr, depth: u32) -> Option<u64> {
        let mut visited = HashSet::new();
        self.evaluate_constish_call_arg_expr_with_visited(expr, depth, &mut visited)
    }

    fn evaluate_constish_call_arg_expr_with_visited(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<u64> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        match expr {
            CExpr::IntLit(value) => (*value >= 0).then_some(*value as u64),
            CExpr::UIntLit(value) => Some(*value),
            CExpr::Var(name) => {
                if let Some(value) = parse_const_value(name) {
                    return Some(value);
                }
                if let Some(addr) = parse_address_from_var_name(name) {
                    return Some(addr);
                }
                let visit_key = format!("constish:{name}");
                if !visited.insert(visit_key.clone()) {
                    return None;
                }
                let resolved = self
                    .render_semantic_value_by_name(name, depth + 1, visited)
                    .and_then(|expr| {
                        self.evaluate_constish_call_arg_expr_with_visited(&expr, depth + 1, visited)
                    })
                    .or_else(|| {
                        self.find_ssa_name_for_rendered_alias(name)
                            .filter(|ssa_name| ssa_name != name)
                            .and_then(|ssa_name| {
                                self.render_semantic_value_by_name(&ssa_name, depth + 1, visited)
                                    .and_then(|expr| {
                                        self.evaluate_constish_call_arg_expr_with_visited(
                                            &expr,
                                            depth + 1,
                                            visited,
                                        )
                                    })
                                    .or_else(|| {
                                        self.lookup_definition_raw(&ssa_name).and_then(|expr| {
                                            self.evaluate_constish_call_arg_expr_with_visited(
                                                &expr,
                                                depth + 1,
                                                visited,
                                            )
                                        })
                                    })
                            })
                    })
                    .or_else(|| {
                        self.resolve_expr_from_phi_sources(name, depth + 1, visited, true)
                            .and_then(|expr| {
                                self.evaluate_constish_call_arg_expr_with_visited(
                                    &expr,
                                    depth + 1,
                                    visited,
                                )
                            })
                    })
                    .or_else(|| {
                        self.lookup_definition_raw(name).and_then(|expr| {
                            self.evaluate_constish_call_arg_expr_with_visited(
                                &expr,
                                depth + 1,
                                visited,
                            )
                        })
                    })
                    .or_else(|| {
                        self.best_visible_definition(name).and_then(|expr| {
                            self.evaluate_constish_call_arg_expr_with_visited(
                                &expr,
                                depth + 1,
                                visited,
                            )
                        })
                    });
                visited.remove(&visit_key);
                resolved
            }
            CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
                self.evaluate_constish_call_arg_expr_with_visited(inner, depth + 1, visited)
            }
            CExpr::Cast { expr: inner, .. } => {
                self.evaluate_constish_call_arg_expr_with_visited(inner, depth + 1, visited)
            }
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => self
                .evaluate_constish_call_arg_expr_with_visited(left, depth + 1, visited)?
                .checked_add(self.evaluate_constish_call_arg_expr_with_visited(
                    right,
                    depth + 1,
                    visited,
                )?),
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => self
                .evaluate_constish_call_arg_expr_with_visited(left, depth + 1, visited)?
                .checked_sub(self.evaluate_constish_call_arg_expr_with_visited(
                    right,
                    depth + 1,
                    visited,
                )?),
            _ => None,
        }
    }

    fn resolve_literalish_call_arg_expr(&self, expr: &CExpr) -> Option<CExpr> {
        let mut visited = HashSet::new();
        self.resolve_literalish_call_arg_expr_with_visited(expr, &mut visited)
    }

    fn resolve_literalish_call_arg_expr_with_visited(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if let CExpr::Var(name) = expr {
            let visit_key = format!("rendered:{}", name.to_ascii_lowercase());
            if !visited.insert(visit_key.clone()) {
                return None;
            }

            if let Some(resolved) =
                self.resolve_literalish_rendered_alias_expr_with_visited(name, visited)
            {
                visited.remove(&visit_key);
                return Some(resolved);
            }

            if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
                && ssa_name != *name
            {
                let ssa_key = format!("ssa:{}", ssa_name.to_ascii_lowercase());
                if visited.insert(ssa_key.clone()) {
                    let resolved = if let Some(def) = self
                        .lookup_definition_raw(&ssa_name)
                        .or_else(|| self.best_visible_definition(&ssa_name))
                        && def != *expr
                    {
                        self.resolve_literalish_call_arg_expr_with_visited(&def, visited)
                    } else {
                        None
                    };
                    visited.remove(&ssa_key);
                    if let Some(resolved) = resolved {
                        visited.remove(&visit_key);
                        return Some(resolved);
                    }
                }
            }

            if let Some(def) = self
                .lookup_definition_raw(name)
                .or_else(|| self.best_visible_definition(name))
                && def != *expr
                && let Some(resolved) =
                    self.resolve_literalish_call_arg_expr_with_visited(&def, visited)
            {
                visited.remove(&visit_key);
                return Some(resolved);
            }
            visited.remove(&visit_key);
        }

        let direct_addr = self.evaluate_constish_call_arg_expr(expr, 0);
        let direct = direct_addr.and_then(|addr| self.literalish_call_arg_expr_for_addr(addr));
        if direct.is_some() {
            return direct;
        }

        let alt_addr = self.evaluate_hex_digit_offset_call_arg_expr(expr, 0)?;
        self.literalish_call_arg_expr_for_addr(alt_addr)
    }

    fn resolve_literalish_rendered_alias_expr_with_visited(
        &self,
        name: &str,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let alias_key = format!("alias:{}", name.to_ascii_lowercase());
        if !visited.insert(alias_key.clone()) {
            return None;
        }

        let mut matches = self
            .var_aliases_map()
            .iter()
            .filter(|(_, alias)| alias.eq_ignore_ascii_case(name))
            .map(|(ssa_name, _)| ssa_name.clone())
            .collect::<Vec<_>>();
        matches.sort_by(|a, b| {
            let a_key = self.ssa_alias_preference_key(a);
            let b_key = self.ssa_alias_preference_key(b);
            let (a_base, a_version) = Self::ssa_name_parts(a);
            let (b_base, b_version) = Self::ssa_name_parts(b);
            b_key
                .cmp(&a_key)
                .then_with(|| b_version.cmp(&a_version))
                .then_with(|| a_base.cmp(b_base))
                .then_with(|| a.cmp(b))
        });
        matches.dedup();

        for ssa_name in matches {
            let ssa_key = format!("ssa:{}", ssa_name.to_ascii_lowercase());
            if !visited.insert(ssa_key.clone()) {
                continue;
            }
            let resolved = if let Some(def) = self
                .lookup_definition_raw(&ssa_name)
                .or_else(|| self.best_visible_definition(&ssa_name))
            {
                self.resolve_literalish_call_arg_expr_with_visited(&def, visited)
            } else {
                None
            };
            visited.remove(&ssa_key);
            if resolved.is_some() {
                visited.remove(&alias_key);
                return resolved;
            }
        }

        visited.remove(&alias_key);
        None
    }

    fn literalish_call_arg_expr_for_addr(&self, addr: u64) -> Option<CExpr> {
        let _ = addr;
        None
    }

    fn evaluate_hex_digit_offset_call_arg_expr(&self, expr: &CExpr, depth: u32) -> Option<u64> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        match expr {
            CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
                self.evaluate_hex_digit_offset_call_arg_expr(inner, depth + 1)
            }
            CExpr::Cast { expr: inner, .. } => {
                self.evaluate_hex_digit_offset_call_arg_expr(inner, depth + 1)
            }
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                let base = self.evaluate_constish_call_arg_expr(left, depth + 1)?;
                let delta = self.hex_digit_literal_value(right, depth + 1)?;
                base.checked_add(delta)
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                let base = self.evaluate_constish_call_arg_expr(left, depth + 1)?;
                let delta = self.hex_digit_literal_value(right, depth + 1)?;
                base.checked_sub(delta)
            }
            _ => None,
        }
    }

    fn hex_digit_literal_value(&self, expr: &CExpr, depth: u32) -> Option<u64> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }

        match expr {
            CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
                self.hex_digit_literal_value(inner, depth + 1)
            }
            CExpr::Cast { expr: inner, .. } => self.hex_digit_literal_value(inner, depth + 1),
            CExpr::IntLit(value) if *value >= 0 => {
                self.reinterpret_decimal_digits_as_hex(*value as u64)
            }
            CExpr::UIntLit(value) => self.reinterpret_decimal_digits_as_hex(*value),
            _ => None,
        }
    }

    fn reinterpret_decimal_digits_as_hex(&self, value: u64) -> Option<u64> {
        let digits = value.to_string();
        if digits.is_empty() || digits.len() > 4 || !digits.chars().all(|ch| ch.is_ascii_digit()) {
            return None;
        }
        u64::from_str_radix(&digits, 16).ok()
    }

    fn promote_constant_indexed_call_arg(&self, addr_expr: &CExpr) -> Option<CExpr> {
        let canonical = self.canonicalize_visible_address_expr(addr_expr, 0);
        let addr = self.normalized_addr_from_visible_expr(&canonical, 0)?;
        if addr.index.is_some() || addr.offset_bytes == 0 {
            return None;
        }
        if matches!(addr.base, analysis::BaseRef::StackSlot(_)) {
            return None;
        }
        if self.oracle_field_name_for_addr(&addr, None).is_some() {
            return None;
        }

        let elem_size = i64::from(self.inputs.arch.ptr_size.max(1));
        if addr.offset_bytes % elem_size != 0 {
            return None;
        }

        let raw_base = self.render_base_ref_expr(&addr.base, false, 0, &mut HashSet::new())?;
        let normalized_base = self.normalize_pointer_base_expr(&raw_base, 0);
        let elem_ty = self.infer_elem_type_from_base_ref(&addr.base, elem_size as u32);
        let base_source_ty = self.expr_type_hint(&normalized_base);
        let base = self.cast_expr_if_needed(
            normalized_base,
            CType::ptr(elem_ty),
            base_source_ty.as_ref(),
        );

        let index = addr.offset_bytes / elem_size;
        let index_expr = if index < 0 {
            CExpr::unary(UnaryOp::Neg, CExpr::IntLit(index.unsigned_abs() as i64))
        } else {
            CExpr::IntLit(index)
        };

        Some(CExpr::Subscript {
            base: Box::new(base),
            index: Box::new(index_expr),
        })
    }

    fn expand_call_arg_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => {
                if let Some(value) = parse_const_value(name) {
                    return if value > 0x7fffffff {
                        CExpr::UIntLit(value)
                    } else {
                        CExpr::IntLit(value as i64)
                    };
                }

                let mut semantic_visited = HashSet::new();
                if let Some(semantic) =
                    self.render_semantic_value_by_name(name, depth + 1, &mut semantic_visited)
                    && self.prefers_visible_expr(expr, &semantic)
                {
                    let visit_key = format!("call-sem:{name}");
                    if visited.insert(visit_key.clone()) {
                        let resolved = self.expand_call_arg_expr(&semantic, depth + 1, visited);
                        visited.remove(&visit_key);
                        return resolved;
                    }
                    return semantic;
                }

                let candidate = self
                    .choose_preferred_visible_expr(
                        self.lookup_definition_raw(name),
                        self.lookup_definition(name),
                    )
                    .or_else(|| self.resolve_expr_from_phi_sources(name, depth + 1, visited, true))
                    .or_else(|| self.best_visible_definition(name));
                if let Some(candidate) = candidate
                    && !matches!(&candidate, CExpr::Var(inner) if inner == name)
                {
                    let visit_key = format!("call-def:{name}");
                    if visited.insert(visit_key.clone()) {
                        let resolved = self.expand_call_arg_expr(&candidate, depth + 1, visited);
                        visited.remove(&visit_key);
                        return resolved;
                    }
                }

                expr.clone()
            }
            CExpr::Deref(inner) => CExpr::Deref(Box::new(self.expand_call_arg_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Cast { ty, expr: inner } => CExpr::cast(
                ty.clone(),
                self.expand_call_arg_expr(inner, depth + 1, visited),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.expand_call_arg_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Unary { op, operand } => {
                CExpr::unary(*op, self.expand_call_arg_expr(operand, depth + 1, visited))
            }
            CExpr::Binary { op, left, right } => CExpr::binary(
                *op,
                self.expand_call_arg_expr(left, depth + 1, visited),
                self.expand_call_arg_expr(right, depth + 1, visited),
            ),
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(self.expand_call_arg_expr(cond, depth + 1, visited)),
                then_expr: Box::new(self.expand_call_arg_expr(then_expr, depth + 1, visited)),
                else_expr: Box::new(self.expand_call_arg_expr(else_expr, depth + 1, visited)),
            },
            CExpr::Call { func, args } => CExpr::Call {
                func: Box::new(self.expand_call_arg_expr(func, depth + 1, visited)),
                args: args
                    .iter()
                    .map(|arg| self.expand_call_arg_expr(arg, depth + 1, visited))
                    .collect(),
            },
            CExpr::Subscript { base, index } => CExpr::Subscript {
                base: Box::new(self.expand_call_arg_expr(base, depth + 1, visited)),
                index: Box::new(self.expand_call_arg_expr(index, depth + 1, visited)),
            },
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(self.expand_call_arg_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(self.expand_call_arg_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::Sizeof(inner) => CExpr::Sizeof(Box::new(self.expand_call_arg_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::AddrOf(inner) => CExpr::AddrOf(Box::new(self.expand_call_arg_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Comma(items) => CExpr::Comma(
                items
                    .iter()
                    .map(|item| self.expand_call_arg_expr(item, depth + 1, visited))
                    .collect(),
            ),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => expr.clone(),
        }
    }

    #[cfg(test)]
    fn is_imported_call_target(&self, callee: &CExpr) -> bool {
        self.resolved_callee_target_for_optional_site(None, callee)
            .is_some_and(|target| target.policy.imported)
    }

    #[cfg(test)]
    fn is_imported_call_target_for_site(&self, block_addr: u64, op_idx: usize) -> bool {
        self.resolved_callee_target_for_site(block_addr, op_idx)
            .is_some_and(|target| target.policy.imported)
    }

    fn call_arg_contains_stack_placeholder(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }

        match expr {
            CExpr::Var(name) => is_generic_stack_placeholder_alias(name),
            CExpr::Deref(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Paren(inner)
            | CExpr::Cast { expr: inner, .. }
            | CExpr::Unary { operand: inner, .. }
            | CExpr::Sizeof(inner) => self.call_arg_contains_stack_placeholder(inner, depth + 1),
            CExpr::Binary { left, right, .. } => {
                self.call_arg_contains_stack_placeholder(left, depth + 1)
                    || self.call_arg_contains_stack_placeholder(right, depth + 1)
            }
            CExpr::Subscript { base, index } => {
                self.call_arg_contains_stack_placeholder(base, depth + 1)
                    || self.call_arg_contains_stack_placeholder(index, depth + 1)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.call_arg_contains_stack_placeholder(base, depth + 1)
            }
            CExpr::Call { func, args } => {
                self.call_arg_contains_stack_placeholder(func, depth + 1)
                    || args
                        .iter()
                        .any(|arg| self.call_arg_contains_stack_placeholder(arg, depth + 1))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.call_arg_contains_stack_placeholder(cond, depth + 1)
                    || self.call_arg_contains_stack_placeholder(then_expr, depth + 1)
                    || self.call_arg_contains_stack_placeholder(else_expr, depth + 1)
            }
            CExpr::Comma(items) => items
                .iter()
                .any(|item| self.call_arg_contains_stack_placeholder(item, depth + 1)),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn call_arg_contains_transient_name(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }

        match expr {
            CExpr::Var(name) => self.is_transient_visible_name(name),
            CExpr::Deref(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Paren(inner)
            | CExpr::Cast { expr: inner, .. }
            | CExpr::Unary { operand: inner, .. }
            | CExpr::Sizeof(inner) => self.call_arg_contains_transient_name(inner, depth + 1),
            CExpr::Binary { left, right, .. } => {
                self.call_arg_contains_transient_name(left, depth + 1)
                    || self.call_arg_contains_transient_name(right, depth + 1)
            }
            CExpr::Subscript { base, index } => {
                self.call_arg_contains_transient_name(base, depth + 1)
                    || self.call_arg_contains_transient_name(index, depth + 1)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.call_arg_contains_transient_name(base, depth + 1)
            }
            CExpr::Call { func, args } => {
                self.call_arg_contains_transient_name(func, depth + 1)
                    || args
                        .iter()
                        .any(|arg| self.call_arg_contains_transient_name(arg, depth + 1))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.call_arg_contains_transient_name(cond, depth + 1)
                    || self.call_arg_contains_transient_name(then_expr, depth + 1)
                    || self.call_arg_contains_transient_name(else_expr, depth + 1)
            }
            CExpr::Comma(items) => items
                .iter()
                .any(|item| self.call_arg_contains_transient_name(item, depth + 1)),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn call_arg_contains_low_quality_name(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }

        match expr {
            CExpr::Var(name) => Self::is_low_quality_imported_call_arg_name(name),
            CExpr::Deref(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Paren(inner)
            | CExpr::Cast { expr: inner, .. }
            | CExpr::Unary { operand: inner, .. }
            | CExpr::Sizeof(inner) => self.call_arg_contains_low_quality_name(inner, depth + 1),
            CExpr::Binary { left, right, .. } => {
                self.call_arg_contains_low_quality_name(left, depth + 1)
                    || self.call_arg_contains_low_quality_name(right, depth + 1)
            }
            CExpr::Subscript { base, index } => {
                self.call_arg_contains_low_quality_name(base, depth + 1)
                    || self.call_arg_contains_low_quality_name(index, depth + 1)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.call_arg_contains_low_quality_name(base, depth + 1)
            }
            CExpr::Call { func, args } => {
                self.call_arg_contains_low_quality_name(func, depth + 1)
                    || args
                        .iter()
                        .any(|arg| self.call_arg_contains_low_quality_name(arg, depth + 1))
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.call_arg_contains_low_quality_name(cond, depth + 1)
                    || self.call_arg_contains_low_quality_name(then_expr, depth + 1)
                    || self.call_arg_contains_low_quality_name(else_expr, depth + 1)
            }
            CExpr::Comma(items) => items
                .iter()
                .any(|item| self.call_arg_contains_low_quality_name(item, depth + 1)),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn call_arg_contains_call(&self, expr: &CExpr, depth: u32) -> bool {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return false;
        }

        match expr {
            CExpr::Call { .. } => true,
            CExpr::Deref(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Paren(inner)
            | CExpr::Cast { expr: inner, .. }
            | CExpr::Unary { operand: inner, .. }
            | CExpr::Sizeof(inner) => self.call_arg_contains_call(inner, depth + 1),
            CExpr::Binary { left, right, .. } => {
                self.call_arg_contains_call(left, depth + 1)
                    || self.call_arg_contains_call(right, depth + 1)
            }
            CExpr::Subscript { base, index } => {
                self.call_arg_contains_call(base, depth + 1)
                    || self.call_arg_contains_call(index, depth + 1)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.call_arg_contains_call(base, depth + 1)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.call_arg_contains_call(cond, depth + 1)
                    || self.call_arg_contains_call(then_expr, depth + 1)
                    || self.call_arg_contains_call(else_expr, depth + 1)
            }
            CExpr::Comma(items) => items
                .iter()
                .any(|item| self.call_arg_contains_call(item, depth + 1)),
            CExpr::Var(_)
            | CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => false,
        }
    }

    fn choose_preferred_call_arg_expr(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        imported: bool,
    ) -> Option<CExpr> {
        self.choose_preferred_call_arg_expr_with_slot_policy(current, candidate, imported, false)
    }

    fn choose_preferred_call_arg_expr_with_slot_policy(
        &self,
        current: Option<CExpr>,
        candidate: Option<CExpr>,
        imported: bool,
        preserve_stable_input_slot: bool,
    ) -> Option<CExpr> {
        match (current, candidate) {
            (None, other) => other,
            (some @ Some(_), None) => some,
            (Some(current_expr), Some(candidate_expr)) => {
                if imported {
                    if preserve_stable_input_slot
                        && self.is_preserved_imported_input_expr(&current_expr)
                        && matches!(candidate_expr, CExpr::Call { .. })
                    {
                        return Some(current_expr);
                    }
                    match (&current_expr, &candidate_expr) {
                        (CExpr::Var(current_name), CExpr::IntLit(_) | CExpr::UIntLit(_))
                            if self
                                .find_ssa_name_for_rendered_alias(current_name)
                                .is_some() =>
                        {
                            return Some(current_expr);
                        }
                        (CExpr::IntLit(_) | CExpr::UIntLit(_), CExpr::Var(candidate_name))
                            if self
                                .find_ssa_name_for_rendered_alias(candidate_name)
                                .is_some() =>
                        {
                            return Some(candidate_expr);
                        }
                        (current, candidate)
                            if self.is_preservable_named_stack_slot_expr(current)
                                && self.is_direct_constish_visible_expr(candidate, 0) =>
                        {
                            return Some(current_expr);
                        }
                        (current, candidate)
                            if self.is_preservable_named_stack_slot_expr(candidate)
                                && self.is_direct_constish_visible_expr(current, 0) =>
                        {
                            return Some(candidate_expr);
                        }
                        (CExpr::Var(current_name), candidate)
                            if self.should_force_imported_call_resolution_name(current_name)
                                && !matches!(
                                    candidate,
                                    CExpr::Var(candidate_name)
                                        if candidate_name.eq_ignore_ascii_case(current_name)
                                ) =>
                        {
                            return Some(candidate_expr);
                        }
                        (candidate, CExpr::Var(candidate_name))
                            if self.should_force_imported_call_resolution_name(candidate_name)
                                && !matches!(
                                    candidate,
                                    CExpr::Var(current_name)
                                        if current_name.eq_ignore_ascii_case(candidate_name)
                                ) =>
                        {
                            return Some(current_expr);
                        }
                        _ => {}
                    }
                    let current_stacky = self.call_arg_contains_stack_placeholder(&current_expr, 0);
                    let candidate_stacky =
                        self.call_arg_contains_stack_placeholder(&candidate_expr, 0);
                    match (current_stacky, candidate_stacky) {
                        (true, false) => return Some(candidate_expr),
                        (false, true) => return Some(current_expr),
                        _ => {}
                    }
                    let current_low_quality =
                        self.call_arg_contains_low_quality_name(&current_expr, 0);
                    let candidate_low_quality =
                        self.call_arg_contains_low_quality_name(&candidate_expr, 0);
                    match (current_low_quality, candidate_low_quality) {
                        (true, false) => return Some(candidate_expr),
                        (false, true) => return Some(current_expr),
                        _ => {}
                    }
                    let current_has_call = self.call_arg_contains_call(&current_expr, 0);
                    let candidate_has_call = self.call_arg_contains_call(&candidate_expr, 0);
                    match (current_has_call, candidate_has_call) {
                        (true, false) => return Some(candidate_expr),
                        (false, true) => return Some(current_expr),
                        _ => {}
                    }
                    match (&current_expr, &candidate_expr) {
                        (CExpr::StringLit(_), CExpr::StringLit(_)) => {}
                        (_, CExpr::StringLit(_)) => return Some(candidate_expr),
                        (CExpr::StringLit(_), _) => return Some(current_expr),
                        _ => {}
                    }
                    let current_literalish = self.resolve_literalish_call_arg_expr(&current_expr);
                    let candidate_literalish =
                        self.resolve_literalish_call_arg_expr(&candidate_expr);
                    match (current_literalish, candidate_literalish) {
                        (None, Some(candidate)) => return Some(candidate),
                        (Some(current), None) => return Some(current),
                        (Some(current), Some(candidate)) => {
                            return self
                                .choose_preferred_visible_expr(Some(current), Some(candidate));
                        }
                        (None, None) => {}
                    }
                }

                self.choose_preferred_visible_expr(Some(current_expr), Some(candidate_expr))
            }
        }
    }

    fn is_preservable_named_stack_slot_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                (self.stack_offset_for_visible_storage_name(name).is_some()
                    || self
                        .inputs
                        .param_register_aliases
                        .values()
                        .any(|alias| alias.eq_ignore_ascii_case(name)))
                    && !is_generic_stack_placeholder_alias(name)
                    && !self.is_transient_visible_name(name)
                    && !self.is_low_signal_visible_name(name)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_preservable_named_stack_slot_expr(inner)
            }
            _ => false,
        }
    }

    fn is_preserved_imported_input_expr(&self, expr: &CExpr) -> bool {
        !self.call_arg_contains_stack_placeholder(expr, 0)
            && !self.call_arg_contains_transient_name(expr, 0)
            && !self.call_arg_contains_low_quality_name(expr, 0)
            && !matches!(expr, CExpr::Call { .. })
    }

    #[allow(dead_code)]
    fn resolve_imported_call_arg_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if let CExpr::Var(name) = expr
            && !self.enter_resolution_guard(ResolutionPhase::ImportedArg, name)
        {
            return self
                .resolution_cycle_fallback(name)
                .unwrap_or_else(|| expr.clone());
        }
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            if let CExpr::Var(name) = expr {
                self.leave_resolution_guard(ResolutionPhase::ImportedArg, name);
            }
            return expr.clone();
        }

        let resolved = match expr {
            CExpr::Var(name) => {
                if let Some(source_call) = self
                    .prepared_semantic_view()
                    .and_then(|view| view.call_result_source_for_name(name))
                    .or_else(|| {
                        self.find_ssa_name_for_rendered_alias(name)
                            .and_then(|ssa_name| {
                                self.prepared_semantic_view()
                                    .and_then(|view| view.call_result_source_for_name(&ssa_name))
                            })
                    })
                    && let Some(expr) = self
                        .stable_owned_call_result_expr_for_source(source_call)
                        .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
                {
                    return self.resolve_imported_call_arg_expr(&expr, depth + 1, visited);
                }
                let transient = self.is_transient_visible_name(name);
                if let Some(offset) = self.stack_offset_for_visible_storage_name(name)
                    && let Some(value) = self.stable_stack_value_for_offset(offset)
                    && let Some(rendered) = self.render_semantic_value(value, depth + 1, visited)
                    && let Some(preferred) = if transient {
                        Some(rendered.clone())
                    } else {
                        self.choose_preferred_call_arg_expr(
                            Some(expr.clone()),
                            Some(rendered.clone()),
                            true,
                        )
                    }
                    && preferred != *expr
                {
                    return self.resolve_imported_call_arg_expr(&preferred, depth + 1, visited);
                }
                if let Some(semantic) = self.render_semantic_value_by_name(name, depth + 1, visited)
                    && let Some(preferred) = if transient {
                        Some(semantic.clone())
                    } else {
                        self.choose_preferred_call_arg_expr(
                            Some(expr.clone()),
                            Some(semantic.clone()),
                            true,
                        )
                    }
                    && preferred != *expr
                {
                    return self.resolve_imported_call_arg_expr(&preferred, depth + 1, visited);
                }
                if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
                    && ssa_name != *name
                {
                    if let Some(semantic) =
                        self.render_semantic_value_by_name(&ssa_name, depth + 1, visited)
                        && let Some(preferred) = if transient {
                            Some(semantic.clone())
                        } else {
                            self.choose_preferred_call_arg_expr(
                                Some(expr.clone()),
                                Some(semantic.clone()),
                                true,
                            )
                        }
                        && preferred != *expr
                    {
                        return self.resolve_imported_call_arg_expr(&preferred, depth + 1, visited);
                    }
                    if let Some(best) = self.lookup_definition(&ssa_name)
                        && !matches!(&best, CExpr::Var(inner) if inner.eq_ignore_ascii_case(name))
                    {
                        return self.resolve_imported_call_arg_expr(&best, depth + 1, visited);
                    }
                }
                if let Some(best) =
                    self.resolve_expr_from_phi_sources(name, depth + 1, visited, true)
                    && !matches!(&best, CExpr::Var(inner) if inner.eq_ignore_ascii_case(name))
                {
                    return best;
                }
                if let Some(best) = self.lookup_definition_raw(name)
                    && !matches!(&best, CExpr::Var(inner) if inner.eq_ignore_ascii_case(name))
                {
                    let resolved = self.resolve_imported_call_arg_expr(&best, depth + 1, visited);
                    let semanticized = self.semanticize_visible_expr(&resolved, depth + 1, visited);
                    return self
                        .choose_preferred_visible_expr(Some(resolved), Some(semanticized))
                        .unwrap_or(best);
                }
                if let Some(best) = self.lookup_definition(name)
                    && !matches!(&best, CExpr::Var(inner) if inner == name)
                {
                    return self.resolve_imported_call_arg_expr(&best, depth + 1, visited);
                }
                if let Some(best) = self.best_visible_definition(name)
                    && !matches!(&best, CExpr::Var(inner) if inner == name)
                {
                    return self.resolve_imported_call_arg_expr(&best, depth + 1, visited);
                }
                expr.clone()
            }
            CExpr::Deref(inner) => {
                let resolved_inner = self.resolve_imported_call_arg_expr(inner, depth + 1, visited);
                let mut memory_visited = HashSet::new();
                if let Some(access) = self.render_memory_access_from_visible_expr(
                    &resolved_inner,
                    self.inputs.arch.ptr_size.max(1),
                    depth + 1,
                    &mut memory_visited,
                ) {
                    return self.resolve_imported_call_arg_expr(&access, depth + 1, visited);
                }
                CExpr::Deref(Box::new(resolved_inner))
            }
            CExpr::Cast { ty, expr: inner } => CExpr::cast(
                ty.clone(),
                self.resolve_imported_call_arg_expr(inner, depth + 1, visited),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.resolve_imported_call_arg_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Unary { op, operand } => CExpr::unary(
                *op,
                self.resolve_imported_call_arg_expr(operand, depth + 1, visited),
            ),
            CExpr::Binary { op, left, right } => CExpr::binary(
                *op,
                self.resolve_imported_call_arg_expr(left, depth + 1, visited),
                self.resolve_imported_call_arg_expr(right, depth + 1, visited),
            ),
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(self.resolve_imported_call_arg_expr(cond, depth + 1, visited)),
                then_expr: Box::new(self.resolve_imported_call_arg_expr(
                    then_expr,
                    depth + 1,
                    visited,
                )),
                else_expr: Box::new(self.resolve_imported_call_arg_expr(
                    else_expr,
                    depth + 1,
                    visited,
                )),
            },
            CExpr::Call { func, args } => {
                let resolved_func = self.resolve_imported_call_arg_expr(func, depth + 1, visited);
                let resolved_args = args
                    .iter()
                    .map(|arg| self.resolve_imported_call_arg_expr(arg, depth + 1, visited))
                    .collect::<Vec<_>>();
                CExpr::Call {
                    func: Box::new(resolved_func),
                    args: resolved_args,
                }
            }
            CExpr::Subscript { base, index } => CExpr::Subscript {
                base: Box::new(self.resolve_imported_call_arg_expr(base, depth + 1, visited)),
                index: Box::new(self.resolve_imported_call_arg_expr(index, depth + 1, visited)),
            },
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(self.resolve_imported_call_arg_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(self.resolve_imported_call_arg_expr(base, depth + 1, visited)),
                member: member.clone(),
            },
            CExpr::Sizeof(inner) => CExpr::Sizeof(Box::new(self.resolve_imported_call_arg_expr(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::AddrOf(inner) => {
                if let CExpr::Var(name) = inner.as_ref()
                    && self
                        .stack_offset_for_visible_storage_name(name)
                        .is_some_and(|offset| offset >= 0)
                {
                    return expr.clone();
                }
                CExpr::AddrOf(Box::new(self.resolve_imported_call_arg_expr(
                    inner,
                    depth + 1,
                    visited,
                )))
            }
            CExpr::Comma(items) => CExpr::Comma(
                items
                    .iter()
                    .map(|item| self.resolve_imported_call_arg_expr(item, depth + 1, visited))
                    .collect(),
            ),
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => expr.clone(),
        };
        if let CExpr::Var(name) = expr {
            self.leave_resolution_guard(ResolutionPhase::ImportedArg, name);
        }
        resolved
    }

    #[allow(dead_code)]
    fn resolve_string_like_imported_call_arg_expr(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            return None;
        }
        if let Some(literalish) = self.resolve_literalish_call_arg_expr(expr) {
            return Some(literalish);
        }
        match expr {
            CExpr::StringLit(_) => Some(expr.clone()),
            CExpr::Var(name) => {
                let visit_key = format!("callstr:{name}");
                if !visited.insert(visit_key.clone()) {
                    return None;
                }
                let resolved = self
                    .render_semantic_value_by_name(name, depth + 1, visited)
                    .and_then(|candidate| {
                        self.resolve_string_like_imported_call_arg_expr(
                            &candidate,
                            depth + 1,
                            visited,
                        )
                    })
                    .or_else(|| {
                        self.resolve_expr_from_phi_sources(name, depth + 1, visited, true)
                            .and_then(|candidate| {
                                self.resolve_string_like_imported_call_arg_expr(
                                    &candidate,
                                    depth + 1,
                                    visited,
                                )
                            })
                    })
                    .or_else(|| {
                        self.lookup_definition_raw(name).and_then(|candidate| {
                            self.resolve_string_like_imported_call_arg_expr(
                                &candidate,
                                depth + 1,
                                visited,
                            )
                        })
                    })
                    .or_else(|| {
                        self.find_ssa_name_for_rendered_alias(name)
                            .filter(|ssa_name| ssa_name != name)
                            .and_then(|ssa_name| {
                                self.render_semantic_value_by_name(&ssa_name, depth + 1, visited)
                                    .and_then(|candidate| {
                                        self.resolve_string_like_imported_call_arg_expr(
                                            &candidate,
                                            depth + 1,
                                            visited,
                                        )
                                    })
                                    .or_else(|| {
                                        self.lookup_definition(&ssa_name).and_then(|candidate| {
                                            self.resolve_string_like_imported_call_arg_expr(
                                                &candidate,
                                                depth + 1,
                                                visited,
                                            )
                                        })
                                    })
                            })
                    })
                    .or_else(|| {
                        self.best_visible_definition(name).and_then(|candidate| {
                            self.resolve_string_like_imported_call_arg_expr(
                                &candidate,
                                depth + 1,
                                visited,
                            )
                        })
                    });
                visited.remove(&visit_key);
                resolved
            }
            CExpr::AddrOf(inner) | CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.resolve_string_like_imported_call_arg_expr(inner, depth + 1, visited)
            }
            CExpr::Deref(inner) => {
                let resolved_inner = self.resolve_imported_call_arg_expr(inner, depth + 1, visited);
                let mut memory_visited = HashSet::new();
                self.render_memory_access_from_visible_expr(
                    &resolved_inner,
                    self.inputs.arch.ptr_size.max(1),
                    depth + 1,
                    &mut memory_visited,
                )
                .and_then(|access| {
                    self.resolve_string_like_imported_call_arg_expr(&access, depth + 1, visited)
                })
            }
            _ => None,
        }
    }

    fn normalize_forced_imported_call_arg_candidate(
        &self,
        original_name: &str,
        candidate: CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if matches!(&candidate, CExpr::Var(inner) if inner.eq_ignore_ascii_case(original_name)) {
            return None;
        }

        let expanded = self.expand_call_arg_expr(&candidate, depth + 1, visited);
        let mut semantic_visited = HashSet::new();
        let semanticized =
            self.semanticize_visible_expr(&expanded, depth + 1, &mut semantic_visited);
        let mut imported_visited = HashSet::new();
        let imported_resolved =
            self.resolve_imported_call_arg_expr(&semanticized, depth + 1, &mut imported_visited);
        let memoryized = match &imported_resolved {
            CExpr::Deref(inner) => {
                let mut memory_visited = HashSet::new();
                self.render_memory_access_from_visible_expr(
                    inner,
                    self.inputs.arch.ptr_size.max(1),
                    depth + 1,
                    &mut memory_visited,
                )
                .or_else(|| self.promote_constant_indexed_call_arg(inner))
                .unwrap_or_else(|| imported_resolved.clone())
            }
            _ => imported_resolved.clone(),
        };
        let literalized = self
            .resolve_literalish_call_arg_expr(&memoryized)
            .unwrap_or(memoryized);
        let mut string_visited = HashSet::new();
        Some(
            self.resolve_string_like_imported_call_arg_expr(
                &literalized,
                depth + 1,
                &mut string_visited,
            )
            .unwrap_or(literalized),
        )
    }

    #[allow(dead_code)]
    fn force_resolve_imported_call_arg_var(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if !self.enter_resolution_guard(ResolutionPhase::ImportedArg, name) {
            return self.resolution_cycle_fallback(name);
        }
        if depth > Self::MAX_SEMANTIC_RENDER_DEPTH {
            self.leave_resolution_guard(ResolutionPhase::ImportedArg, name);
            return None;
        }

        let visit_key = format!("force-call:{name}");
        if !visited.insert(visit_key.clone()) {
            self.leave_resolution_guard(ResolutionPhase::ImportedArg, name);
            return None;
        }

        let mut best = None;
        if let Some(candidate) = self
            .render_semantic_value_by_name(name, depth + 1, visited)
            .and_then(|candidate| {
                self.normalize_forced_imported_call_arg_candidate(name, candidate, depth, visited)
            })
        {
            best = self.choose_preferred_call_arg_expr(best, Some(candidate), true);
        }
        if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
            && ssa_name != name
            && let Some(candidate) = self
                .render_semantic_value_by_name(&ssa_name, depth + 1, visited)
                .or_else(|| self.lookup_definition_raw(&ssa_name))
                .or_else(|| self.lookup_definition(&ssa_name))
                .and_then(|candidate| {
                    self.normalize_forced_imported_call_arg_candidate(
                        name, candidate, depth, visited,
                    )
                })
        {
            best = self.choose_preferred_call_arg_expr(best, Some(candidate), true);
        }
        if let Some(candidate) = self
            .resolve_expr_from_phi_sources(name, depth + 1, visited, true)
            .and_then(|candidate| {
                self.normalize_forced_imported_call_arg_candidate(name, candidate, depth, visited)
            })
        {
            best = self.choose_preferred_call_arg_expr(best, Some(candidate), true);
        }
        if let Some(candidate) = self.lookup_definition_raw(name).and_then(|candidate| {
            self.normalize_forced_imported_call_arg_candidate(name, candidate, depth, visited)
        }) {
            best = self.choose_preferred_call_arg_expr(best, Some(candidate), true);
        }
        if let Some(candidate) = self.lookup_definition(name).and_then(|candidate| {
            self.normalize_forced_imported_call_arg_candidate(name, candidate, depth, visited)
        }) {
            best = self.choose_preferred_call_arg_expr(best, Some(candidate), true);
        }
        if let Some(candidate) = self.best_visible_definition(name).and_then(|candidate| {
            self.normalize_forced_imported_call_arg_candidate(name, candidate, depth, visited)
        }) {
            best = self.choose_preferred_call_arg_expr(best, Some(candidate), true);
        }

        visited.remove(&visit_key);
        self.leave_resolution_guard(ResolutionPhase::ImportedArg, name);
        best
    }

    #[cfg(test)]
    pub(super) fn normalize_call_arg_expr_for_callee(&self, callee: &CExpr, expr: CExpr) -> CExpr {
        let imported = self.is_imported_call_target(callee);
        self.normalize_call_arg_expr_with_import_policy(expr, imported)
    }

    pub(super) fn normalize_call_arg_expr_with_import_policy(
        &self,
        expr: CExpr,
        imported: bool,
    ) -> CExpr {
        let raw = expr.clone();
        let rewritten = self.rewrite_stack_expr(expr);
        let initial = if imported {
            raw.clone()
        } else {
            rewritten.clone()
        };
        let mut best = Some(initial.clone());
        if imported {
            best = self.choose_preferred_call_arg_expr(best, Some(rewritten.clone()), true);
        }
        let mut expanded_visited = HashSet::new();
        let expanded = self.expand_call_arg_expr(&initial, 0, &mut expanded_visited);
        best = self.choose_preferred_call_arg_expr(best, Some(expanded.clone()), imported);
        let mut semantic_visited = HashSet::new();
        let semanticized = self.semanticize_visible_expr(&expanded, 0, &mut semantic_visited);
        best = self.choose_preferred_call_arg_expr(best, Some(semanticized.clone()), imported);
        let call_normalized = self.normalize_final_call_expr(semanticized.clone());
        best = self.choose_preferred_call_arg_expr(best, Some(call_normalized.clone()), imported);
        let should_try_general_resolution = imported
            || self.call_arg_contains_transient_name(&call_normalized, 0)
            || self.call_arg_contains_stack_placeholder(&call_normalized, 0)
            || self.expr_is_generic_entry_arg_like(&call_normalized);
        let imported_resolved = if should_try_general_resolution {
            let mut imported_visited = HashSet::new();
            self.resolve_imported_call_arg_expr(&call_normalized, 0, &mut imported_visited)
        } else {
            call_normalized.clone()
        };
        best = self.choose_preferred_call_arg_expr(best, Some(imported_resolved.clone()), imported);
        let memoryized = match &imported_resolved {
            CExpr::Deref(inner) => {
                let mut memory_visited = HashSet::new();
                self.render_memory_access_from_visible_expr(
                    inner,
                    self.inputs.arch.ptr_size.max(1),
                    0,
                    &mut memory_visited,
                )
                .or_else(|| self.promote_constant_indexed_call_arg(inner))
                .unwrap_or_else(|| imported_resolved.clone())
            }
            _ => imported_resolved.clone(),
        };
        best = self.choose_preferred_call_arg_expr(best, Some(memoryized.clone()), imported);
        let literalized = self
            .resolve_literalish_call_arg_expr(&memoryized)
            .unwrap_or(memoryized);
        best = self.choose_preferred_call_arg_expr(best, Some(literalized.clone()), imported);
        if imported {
            let mut string_visited = HashSet::new();
            if let Some(string_like) = self.resolve_string_like_imported_call_arg_expr(
                &literalized,
                0,
                &mut string_visited,
            ) {
                best = self.choose_preferred_call_arg_expr(best, Some(string_like), true);
            }
        }
        let best = best.unwrap_or(rewritten);
        let rewritten_best = self.rewrite_stack_expr(best.clone());
        let normalized = if imported {
            self.choose_preferred_call_arg_expr(
                Some(best.clone()),
                Some(rewritten_best.clone()),
                true,
            )
            .unwrap_or(best)
        } else {
            rewritten_best
        };
        self.sanitize_public_call_arg_expr(normalized)
    }

    fn sanitize_public_call_arg_expr(&self, expr: CExpr) -> CExpr {
        self.sanitize_public_expr(expr, PublicExprSanitizeMode::CallArg)
    }

    fn proven_source_for_public_call_arg_call(&self, expr: &CExpr) -> Option<(u64, usize)> {
        self.requires_certified_rendering()
            .then(|| self.certified_source_for_rendered_call_expr(expr, None))
            .flatten()
    }

    fn sanitize_public_call_arg_call_expr(&self, expr: CExpr) -> CExpr {
        let Some(source_call) = self.proven_source_for_public_call_arg_call(&expr) else {
            return Self::unresolved_call_arg_expr();
        };
        let normalized = self.normalize_call_expr_for_source_call(
            source_call,
            expr,
            FinalExprNormalizeContext::DefinitionRoot,
        );
        let CExpr::Call { func, args } = normalized else {
            return self.sanitize_public_expr(normalized, PublicExprSanitizeMode::CallArg);
        };
        CExpr::Call {
            func: Box::new(self.sanitize_public_expr(*func, PublicExprSanitizeMode::Generic)),
            args: args
                .into_iter()
                .map(|arg| self.sanitize_public_expr(arg, PublicExprSanitizeMode::CallArg))
                .collect(),
        }
    }

    fn sanitize_public_expr(&self, expr: CExpr, mode: PublicExprSanitizeMode) -> CExpr {
        match expr {
            CExpr::Var(name) if Self::is_opaque_public_call_arg_name(&name) => {
                CExpr::Var(Self::opaque_public_call_arg_display_name(&name))
            }
            CExpr::Var(name) if matches!(mode, PublicExprSanitizeMode::CallArg) => self
                .canonical_stack_owner_display_name(&name)
                .map(CExpr::Var)
                .unwrap_or_else(|| {
                    if self.is_raw_register_public_call_arg_name(&name)
                        || self.is_transient_visible_name(&name)
                    {
                        Self::unresolved_call_arg_expr()
                    } else {
                        CExpr::Var(name)
                    }
                }),
            CExpr::Deref(inner) => CExpr::Deref(Box::new(self.sanitize_public_expr(*inner, mode))),
            CExpr::AddrOf(inner) => {
                CExpr::AddrOf(Box::new(self.sanitize_public_expr(*inner, mode)))
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.sanitize_public_expr(*inner, mode))),
            CExpr::Cast { ty, expr } => CExpr::Cast {
                ty,
                expr: Box::new(self.sanitize_public_expr(*expr, mode)),
            },
            CExpr::Unary { op, operand } => CExpr::Unary {
                op,
                operand: Box::new(self.sanitize_public_expr(*operand, mode)),
            },
            CExpr::Sizeof(inner) => {
                CExpr::Sizeof(Box::new(self.sanitize_public_expr(*inner, mode)))
            }
            CExpr::Binary { op, left, right } => {
                let left = self.sanitize_public_expr(*left, mode);
                let right = self.sanitize_public_expr(*right, mode);
                self.identity_simplify_binary(op, left, right, None)
            }
            CExpr::Subscript { base, index } => {
                let base = self.sanitize_public_expr(*base, mode);
                let index = self.sanitize_public_expr(*index, mode);
                self.rewrite_pointer_arithmetic_subscript(CExpr::Subscript {
                    base: Box::new(base),
                    index: Box::new(index),
                })
            }
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(self.sanitize_public_expr(*base, mode)),
                member,
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(self.sanitize_public_expr(*base, mode)),
                member,
            },
            CExpr::Call { func, args } if matches!(mode, PublicExprSanitizeMode::CallArg) => {
                self.sanitize_public_call_arg_call_expr(CExpr::Call { func, args })
            }
            CExpr::Call { func, args } => CExpr::Call {
                func: Box::new(self.sanitize_public_expr(*func, PublicExprSanitizeMode::Generic)),
                args: args
                    .into_iter()
                    .map(|arg| self.sanitize_public_expr(arg, PublicExprSanitizeMode::CallArg))
                    .collect(),
            },
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(self.sanitize_public_expr(*cond, mode)),
                then_expr: Box::new(self.sanitize_public_expr(*then_expr, mode)),
                else_expr: Box::new(self.sanitize_public_expr(*else_expr, mode)),
            },
            CExpr::Comma(items) => CExpr::Comma(
                items
                    .into_iter()
                    .map(|item| self.sanitize_public_expr(item, mode))
                    .collect(),
            ),
            other => other,
        }
    }

    fn is_opaque_public_call_arg_name(name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        SSAVarNameKind::classify(&lower).is_temporary()
    }

    fn is_raw_register_public_call_arg_name(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        let base = lower
            .rsplit_once('_')
            .filter(|(_, version)| version.chars().all(|ch| ch.is_ascii_digit()))
            .map(|(base, _)| base)
            .unwrap_or(lower.as_str());
        self.inputs.arch.is_register_like_base_name(base) && !Self::is_semantic_binding_name(base)
    }

    fn opaque_public_call_arg_display_name(name: &str) -> String {
        let lower = name.to_ascii_lowercase();
        let raw = SSAVarNameKind::strip_temporary_prefix(&lower).unwrap_or(lower.as_str());
        let mut suffix = raw
            .chars()
            .map(|ch| {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    ch
                } else {
                    '_'
                }
            })
            .collect::<String>();
        if suffix.is_empty() {
            suffix.push_str("value");
        }
        format!("value_{suffix}")
    }

    fn canonical_stack_owner_display_name(&self, name: &str) -> Option<String> {
        if !name.eq_ignore_ascii_case("slot") {
            return None;
        }
        let offset = self.stack_offset_for_visible_storage_name(name)?;
        self.stack_vars_map()
            .get(&offset)
            .filter(|candidate| !candidate.eq_ignore_ascii_case(name))
            .cloned()
    }

    fn normalize_final_call_expr(&self, expr: CExpr) -> CExpr {
        self.normalize_final_call_expr_in_context(expr, FinalExprNormalizeContext::Generic)
    }

    fn normalize_final_call_expr_in_context(
        &self,
        expr: CExpr,
        context: FinalExprNormalizeContext,
    ) -> CExpr {
        self.normalize_final_call_expr_in_scope(expr, FinalExprNormalizeScope::new(context))
    }

    fn final_child_normalize_scope(
        &self,
        _expr: &CExpr,
        context: FinalExprNormalizeContext,
    ) -> FinalExprNormalizeScope {
        FinalExprNormalizeScope {
            context,
            source_call: None,
        }
    }

    fn normalize_final_call_expr_in_scope(
        &self,
        expr: CExpr,
        scope: FinalExprNormalizeScope,
    ) -> CExpr {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            } => {
                let left = *left;
                let left_scope =
                    self.final_child_normalize_scope(&left, FinalExprNormalizeContext::Generic);
                let right = *right;
                let right_scope = self
                    .final_child_normalize_scope(&right, FinalExprNormalizeContext::DefinitionRoot);
                CExpr::assign(
                    self.normalize_final_call_expr_in_scope(left, left_scope),
                    self.normalize_final_call_expr_in_scope(right, right_scope),
                )
            }
            CExpr::Call { func, args } => {
                let func = scope
                    .source_call
                    .and_then(|(block_addr, op_idx)| {
                        self.resolved_callee_identity_expr_for_site(block_addr, op_idx)
                    })
                    .unwrap_or(*func);
                let func_scope =
                    self.final_child_normalize_scope(&func, FinalExprNormalizeContext::Generic);
                let func = self.normalize_final_call_expr_in_scope(func, func_scope);
                let imported_or_modeled =
                    self.imported_or_modeled_call_target_for_optional_site(scope.source_call);
                let mut args: Vec<CExpr> = if imported_or_modeled {
                    args.into_iter()
                        .map(|arg| {
                            let original_param_home = match &arg {
                                CExpr::Var(name) if self.is_static_param_home_alias_name(name) => {
                                    Some(name.clone())
                                }
                                _ => None,
                            };
                            let arg_scope = self.final_child_normalize_scope(
                                &arg,
                                FinalExprNormalizeContext::Generic,
                            );
                            let normalized =
                                self.normalize_final_call_expr_in_scope(arg, arg_scope);
                            let normalized =
                                self.normalize_imported_call_arg_expr(normalized, true, true, true);
                            if let Some(name) = original_param_home
                                && matches!(&normalized, CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(inner_name) if inner_name.eq_ignore_ascii_case(&name)))
                            {
                                return CExpr::Var(name);
                            }
                            normalized
                        })
                        .collect()
                } else {
                    args.into_iter()
                        .map(|arg| {
                            let original_param_home = match &arg {
                                CExpr::Var(name) if self.is_static_param_home_alias_name(name) => {
                                    Some(name.clone())
                                }
                                _ => None,
                            };
                            let arg_scope = self.final_child_normalize_scope(
                                &arg,
                                FinalExprNormalizeContext::Generic,
                            );
                            let normalized =
                                self.normalize_final_call_expr_in_scope(arg, arg_scope);
                            let normalized =
                                self.normalize_call_arg_expr_with_import_policy(normalized, false);
                            if let Some(name) = original_param_home
                                && matches!(&normalized, CExpr::Deref(inner) if matches!(inner.as_ref(), CExpr::Var(inner_name) if inner_name.eq_ignore_ascii_case(&name)))
                            {
                                return CExpr::Var(name);
                            }
                            normalized
                        })
                        .collect()
                };
                if let Some(max_arity) =
                    self.non_variadic_call_arity_for_optional_site(scope.source_call)
                {
                    args.truncate(max_arity);
                }
                let call = CExpr::Call {
                    func: Box::new(func),
                    args,
                };
                if !matches!(scope.context, FinalExprNormalizeContext::DefinitionRoot)
                    && let Some(owner) = scope.source_call.and_then(|source_call| {
                        self.stable_owned_call_result_expr_for_source(source_call)
                    })
                {
                    return owner;
                }
                call
            }
            CExpr::Deref(inner) => {
                let inner = *inner;
                let inner_scope =
                    self.final_child_normalize_scope(&inner, FinalExprNormalizeContext::Generic);
                let inner = self.normalize_final_call_expr_in_scope(inner, inner_scope);
                if let Some(addr) = self.normalized_addr_from_visible_expr(&inner, 0)
                    && let Some(access) =
                        self.render_access_expr_from_addr(&addr, 0, false, 0, &mut HashSet::new())
                {
                    return access;
                }
                CExpr::Deref(Box::new(inner))
            }
            CExpr::Subscript { base, index } => {
                let base = *base;
                let base_scope =
                    self.final_child_normalize_scope(&base, FinalExprNormalizeContext::Generic);
                let mut base = self.normalize_final_call_expr_in_scope(base, base_scope);
                let index = *index;
                let index_scope =
                    self.final_child_normalize_scope(&index, FinalExprNormalizeContext::Generic);
                let mut index = self.normalize_final_call_expr_in_scope(index, index_scope);
                if self.should_swap_indexed_access_base(&base, &index) {
                    std::mem::swap(&mut base, &mut index);
                }
                self.rewrite_pointer_arithmetic_subscript(CExpr::Subscript {
                    base: Box::new(base),
                    index: Box::new(index),
                })
            }
            CExpr::Cast { ty, expr: inner } => {
                let inner = *inner;
                let inner_scope = FinalExprNormalizeScope {
                    context: scope.context,
                    source_call: scope.source_call,
                };
                CExpr::cast(
                    ty,
                    self.normalize_final_call_expr_in_scope(inner, inner_scope),
                )
            }
            CExpr::Paren(inner) => {
                let inner = *inner;
                let inner_scope = FinalExprNormalizeScope {
                    context: scope.context,
                    source_call: scope.source_call,
                };
                CExpr::Paren(Box::new(
                    self.normalize_final_call_expr_in_scope(inner, inner_scope),
                ))
            }
            CExpr::Binary { op, left, right } => {
                let left = *left;
                let left_scope =
                    self.final_child_normalize_scope(&left, FinalExprNormalizeContext::Generic);
                let right = *right;
                let right_scope =
                    self.final_child_normalize_scope(&right, FinalExprNormalizeContext::Generic);
                self.identity_simplify_binary(
                    op,
                    self.normalize_final_call_expr_in_scope(left, left_scope),
                    self.normalize_final_call_expr_in_scope(right, right_scope),
                    None,
                )
            }
            other => other.map_children(&mut |child| {
                let child_scope =
                    self.final_child_normalize_scope(&child, FinalExprNormalizeContext::Generic);
                self.normalize_final_call_expr_in_scope(child, child_scope)
            }),
        }
    }

    /// Convert a block to folded C statements.
    pub(crate) fn fold_block(&self, block: &SSABlock, current_block_addr: u64) -> Vec<CStmt> {
        self.current_block_addr.set(Some(current_block_addr));
        self.current_op_idx.set(None);
        let mut stmts = Vec::new();
        let mut last_ret_value: Option<CExpr> = None;
        let mut last_ret_value_op_idx: Option<usize> = None;
        let track_return_value = self.is_current_return_block()
            || block
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Return { .. }));

        for (op_idx, op) in block.ops.iter().enumerate() {
            self.current_op_idx.set(Some(op_idx));
            // Skip stack frame setup/teardown if enabled
            if self.is_stack_frame_op(op) {
                continue;
            }

            if self.is_inlined_single_use_call_result(block, op_idx, op) {
                continue;
            }

            if self.is_consumed_immediate_call_home_store(block, op_idx, op) {
                continue;
            }

            if let SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr,
                val,
            } = op
                && self.is_current_return_block()
                && let Some(offset) = self.stack_slot_offset_for_var(addr)
                && self.state.return_stack_slots.contains(&offset)
            {
                let direct_value = self.get_return_expr(val);
                let local_value =
                    match self.recent_same_family_return_expr_before(block, op_idx, val) {
                        Some(recent)
                            if self.should_prefer_recent_same_family_return_expr(
                                &recent,
                                &direct_value,
                            ) =>
                        {
                            Some(recent)
                        }
                        Some(recent) => {
                            self.preferred_return_candidate(Some(recent), Some(direct_value))
                        }
                        None => Some(direct_value),
                    };
                last_ret_value = self.preferred_return_candidate(
                    local_value,
                    self.merged_return_candidate_for_block_slot(block.addr, offset),
                );
                last_ret_value_op_idx = self
                    .certified_return_for_op(block.addr, op_idx)
                    .map(|_| op_idx);
                if let Some(local_name) = self
                    .resolve_stack_var(offset)
                    .filter(|name| !is_generic_stack_placeholder_alias(name))
                    && let Some(value) = last_ret_value.clone()
                    && value != CExpr::Var(local_name.clone())
                    && self.should_emit_return_slot_assignment(offset, &value)
                    && let Some(assign) = self.assign_stmt(CExpr::Var(local_name), value)
                {
                    stmts.push(assign);
                }
                continue;
            }

            if let SSAOp::Load {
                space: r2il::SpaceId::Ram,
                addr,
                ..
            } = op
                && block.addr == self.state.exit_block.unwrap_or(0)
                && self.is_current_return_block()
                && let Some(offset) = self.stack_slot_offset_for_var(addr)
                && self.state.return_stack_slots.contains(&offset)
            {
                continue;
            }

            if track_return_value {
                match op {
                    SSAOp::Copy { dst, src }
                        if self
                            .inputs
                            .arch
                            .is_return_register_name(&dst.name.to_lowercase()) =>
                    {
                        if self.is_control_return_target(dst) {
                            continue;
                        }
                        let src_expr = if self
                            .inputs
                            .arch
                            .is_return_register_name(&src.name.to_lowercase())
                        {
                            last_ret_value.clone().unwrap_or_else(|| {
                                self.lookup_definition(&src.display_name())
                                    .unwrap_or_else(|| self.get_expr(src))
                            })
                        } else {
                            self.tracked_return_source_expr(src)
                        };
                        last_ret_value = Some(src_expr);
                        last_ret_value_op_idx = self
                            .certified_return_for_op(block.addr, op_idx)
                            .map(|_| op_idx);
                    }
                    SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src }
                    | SSAOp::Cast { dst, src }
                        if self
                            .inputs
                            .arch
                            .is_return_register_name(&dst.name.to_lowercase()) =>
                    {
                        if self.is_control_return_target(dst) {
                            continue;
                        }
                        let src_expr = if self
                            .inputs
                            .arch
                            .is_return_register_name(&src.name.to_lowercase())
                        {
                            last_ret_value.clone().unwrap_or_else(|| {
                                self.lookup_definition(&src.display_name())
                                    .unwrap_or_else(|| self.get_expr(src))
                            })
                        } else {
                            self.tracked_return_source_expr(src)
                        };
                        last_ret_value = Some(self.tracked_return_cast_expr(dst, src, src_expr));
                        last_ret_value_op_idx = self
                            .certified_return_for_op(block.addr, op_idx)
                            .map(|_| op_idx);
                    }
                    _ => {
                        if let Some(dst) = op.dst()
                            && self
                                .inputs
                                .arch
                                .is_return_register_name(&dst.name.to_lowercase())
                            && !self.is_control_return_target(dst)
                        {
                            let mut visited = HashSet::new();
                            let raw = self.op_to_expr(op);
                            let expanded = self.expand_return_expr(&raw, 0, &mut visited);
                            let final_expr = if self.is_certified_rendered_call_expr(&expanded) {
                                expanded.clone()
                            } else {
                                let mut semantic_visited = HashSet::new();
                                let semanticized = self.semanticize_visible_expr(
                                    &expanded,
                                    0,
                                    &mut semantic_visited,
                                );
                                if self.is_predicate_like_expr(&semanticized) {
                                    self.simplify_condition_expr(semanticized)
                                } else {
                                    semanticized
                                }
                            };
                            last_ret_value = Some(final_expr);
                            last_ret_value_op_idx = self
                                .certified_return_for_op(block.addr, op_idx)
                                .map(|_| op_idx);
                        }
                    }
                }
            }

            if let SSAOp::Return { target } = op {
                if block.addr == self.state.exit_block.unwrap_or(0)
                    && self.is_control_return_target(target)
                    && !self.state.return_stack_slots.is_empty()
                    && last_ret_value.is_none()
                {
                    break;
                }
                let return_op_idx = if self.is_control_return_target(target) {
                    match last_ret_value_op_idx {
                        Some(op_idx) => op_idx,
                        None if self.requires_certified_rendering()
                            && self
                                .certified_return_expr_for_op(block.addr, op_idx)
                                .is_some() =>
                        {
                            op_idx
                        }
                        None if self.requires_certified_rendering() => {
                            stmts.push(self.certified_residual_comment(format!(
                                "missing certified value return for control-only exit at 0x{:x}:{}",
                                block.addr, op_idx
                            )));
                            break;
                        }
                        None => op_idx,
                    }
                } else {
                    op_idx
                };
                let certified_return_expr = None;

                if !self.current_return_target_is_certified(target) {
                    stmts.push(self.certified_residual_comment(format!(
                        "uncertified return value at 0x{:x}:{}",
                        block.addr, op_idx
                    )));
                    break;
                }

                let (expr, certified_value) = if let Some((expr, value)) = certified_return_expr {
                    (expr, Some(value))
                } else {
                    let unresolved = self.get_return_expr(target);
                    let mut visited = HashSet::new();
                    let target_expr = self
                        .choose_preferred_visible_expr(
                            self.render_semantic_value_by_name(
                                &target.display_name(),
                                0,
                                &mut visited,
                            ),
                            Some(unresolved.clone()),
                        )
                        .and_then(|expr| {
                            self.choose_preferred_visible_expr(
                                Some(expr),
                                self.best_visible_definition(&target.display_name()),
                            )
                        })
                        .unwrap_or(unresolved);
                    let expr = if self.is_control_return_target(target) {
                        let control_return_value = last_ret_value.clone().or_else(|| {
                            self.current_block_addr.get().and_then(|block_addr| {
                                self.merged_return_register_candidate_for_block(block_addr)
                            })
                        });
                        if let Some(last) = control_return_value {
                            self.resolve_return_target_expr(last, None)
                        } else {
                            self.resolve_return_target_expr(target_expr, None)
                        }
                    } else {
                        self.resolve_return_target_expr(target_expr, last_ret_value.clone())
                    };
                    let value = self
                        .certified_return_for_op(block.addr, return_op_idx)
                        .map(|cert| cert.value);
                    (expr, value)
                };
                let final_expr = {
                    let normalized = self.normalize_final_return_candidate(expr.clone());
                    self.sanitize_final_return_expr(normalized, expr)
                };
                if !self.certified_return_members_have_external_layout(&final_expr) {
                    stmts.push(self.certified_residual_comment(format!(
                        "uncertified return expression at 0x{:x}:{}",
                        block.addr, return_op_idx
                    )));
                    break;
                }
                let return_stmt = CStmt::Return(Some(final_expr));
                self.record_effect_render_proof_for_value(
                    EffectRenderProofKind::Return,
                    block.addr,
                    return_op_idx,
                    certified_value,
                );
                stmts.push(return_stmt);

                break;
            }

            // In return-context blocks, keep return-register writes as tracking-only.
            // Emit a single high-level return at the SSA Return terminator.
            if track_return_value
                && let Some(dst) = op.dst()
                && self
                    .inputs
                    .arch
                    .is_return_register_name(&dst.name.to_lowercase())
            {
                continue;
            }

            if let Some(dst) = op.dst()
                && self.should_suppress_shadow_call_result_assignment(dst)
            {
                continue;
            }

            // Skip operations that produce dead values
            if let Some(dst) = op.dst() {
                if self.is_dead(dst) {
                    continue;
                }

                // Skip if this will be inlined
                let key = dst.display_name();
                if self.should_inline(dst) {
                    continue;
                }

                // Skip if this op's destination was consumed by call argument collection
                if self.consumed_by_call_set().contains(&key) {
                    continue;
                }
            }

            if let Some(stmt) = self.op_to_stmt_with_args(op, block.addr, op_idx) {
                let is_return = matches!(stmt, CStmt::Return(_));
                stmts.push(stmt);
                if is_return {
                    break;
                }
            }
        }

        if self.is_current_return_block()
            && !stmts.iter().any(|stmt| matches!(stmt, CStmt::Return(_)))
            && let Some(expr) = last_ret_value
        {
            let return_expr = Some((expr, None));

            if let Some((expr, certified_value)) = return_expr {
                let final_expr = {
                    let normalized = self.normalize_final_return_candidate(expr.clone());
                    self.sanitize_final_return_expr(normalized, expr)
                };
                if !self.certified_return_members_have_external_layout(&final_expr) {
                    stmts.push(self.certified_residual_comment(format!(
                        "uncertified return expression at 0x{:x}:{}",
                        block.addr,
                        last_ret_value_op_idx.unwrap_or(0)
                    )));
                } else {
                    let return_stmt = CStmt::Return(Some(final_expr));
                    if let Some(op_idx) = last_ret_value_op_idx {
                        let value = certified_value.or_else(|| {
                            self.certified_return_for_op(block.addr, op_idx)
                                .map(|cert| cert.value)
                        });
                        self.record_effect_render_proof_for_value(
                            EffectRenderProofKind::Return,
                            block.addr,
                            op_idx,
                            value,
                        );
                        stmts.push(return_stmt);
                    } else {
                        stmts.push(return_stmt);
                    }
                };
            }
        }

        let stmts = self.propagate_ephemeral_copies(stmts);
        let out = self.prune_redundant_return_slot_assignments(
            self.prune_dead_temp_assignments_before_structuring(stmts),
        );
        self.current_block_addr.set(None);
        self.current_op_idx.set(None);
        out
    }

    fn prune_redundant_return_slot_assignments(&self, stmts: Vec<CStmt>) -> Vec<CStmt> {
        if stmts.len() < 2 {
            return stmts;
        }

        let mut out = Vec::with_capacity(stmts.len());
        let mut idx = 0;
        while idx < stmts.len() {
            let skip_assignment = if let Some(CStmt::Return(Some(ret_expr))) = stmts.get(idx + 1) {
                match &stmts[idx] {
                    CStmt::Expr(CExpr::Binary {
                        op: BinaryOp::Assign,
                        left,
                        right,
                    }) => match left.as_ref() {
                        CExpr::Var(name) => {
                            match self.stack_offset_for_visible_storage_name(name) {
                                Some(offset) => {
                                    let rhs = self.resolve_return_candidate(right);
                                    let ret = self.resolve_return_candidate(ret_expr);
                                    rhs == ret
                                        && self.state.return_stack_slots.contains(&offset)
                                        && !self.should_emit_return_slot_assignment(offset, &rhs)
                                }
                                None => false,
                            }
                        }
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            };

            if skip_assignment {
                idx += 1;
                continue;
            }

            out.push(stmts[idx].clone());
            idx += 1;
        }

        out
    }

    fn is_inlined_single_use_call_result(
        &self,
        block: &SSABlock,
        op_idx: usize,
        op: &SSAOp,
    ) -> bool {
        if !matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
            return false;
        }

        false
    }

    fn certified_call_result_flows_to_return(&self, source_call: (u64, usize)) -> bool {
        let callsite = r2types::CallsiteKey {
            block_addr: source_call.0,
            op_index: source_call.1,
        };
        let Some(call_result_facts) = self.inputs.call_result_facts() else {
            return false;
        };
        let Some(render_facts) = self.inputs.render_facts() else {
            return false;
        };
        render_facts.return_effects().any(|return_fact| {
            call_result_facts
                .result_for_value(return_fact.value)
                .is_some_and(|result| result.callsite == callsite)
        })
    }

    fn is_consumed_immediate_call_home_store(
        &self,
        block: &SSABlock,
        op_idx: usize,
        op: &SSAOp,
    ) -> bool {
        let SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr,
            val,
        } = op
        else {
            return false;
        };

        let addr_key = addr.display_name();
        let val_key = val.display_name();
        if !self.consumed_by_call_set().contains(&addr_key)
            && !self.consumed_by_call_set().contains(&val_key)
        {
            return false;
        }

        if let Some(offset) = self.stack_slot_offset_for_var(addr)
            && offset < 0
            && let Some(name) = self.resolve_stack_var(offset)
            && !is_generic_stack_placeholder_alias(&name)
            && !self.is_autogenerated_stack_home_name(&name)
            && !name.ends_with("_home")
        {
            return false;
        }

        for next_idx in (op_idx + 1)..block.ops.len() {
            match &block.ops[next_idx] {
                SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                    return self.call_args_map().contains_key(&(block.addr, next_idx));
                }
                SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. } => {
                    return false;
                }
                _ => {}
            }
        }

        false
    }

    fn is_materialized_call_result_stack_home_store(&self, addr: &SSAVar, val: &SSAVar) -> bool {
        let Some(offset) = self
            .stack_slot_offset_for_var(addr)
            .or_else(|| self.extract_stack_offset_from_var(addr))
        else {
            return false;
        };
        if offset >= 0 {
            return false;
        }
        let val_name = val.display_name();
        let Some(source_call) = self
            .call_result_source_for_ssa_name(&val_name)
            .or_else(|| self.local_post_call_source_for_ssa_name(&val_name))
            .or_else(|| {
                return None;

                let block_addr = self.current_block_addr.get()?;
                let prepared = self.inputs.prepared_ssa?;
                let block = prepared.function().get_block(block_addr)?;
                self.raw_local_post_call_source_for_ssa_name_in_block(block, &val_name, 0)
                    .filter(|source| self.has_certified_call_result_owner_fact_for_source(*source))
            })
        else {
            return false;
        };
        let Some(CExpr::Var(owner_name)) =
            self.should_materialize_call_result_at_source(source_call)
        else {
            return false;
        };
        if self
            .stack_offset_for_visible_storage_name(&owner_name)
            .is_some_and(|owner_offset| owner_offset == offset)
        {
            return true;
        }
        self.resolve_stack_var(offset).is_some_and(|slot_name| {
            owner_name.eq_ignore_ascii_case(&slot_name)
                || self.visible_names_share_stack_slot(&owner_name, &slot_name)
        })
    }

    fn is_certified_materialized_call_result_stack_home_store(
        &self,
        addr: &SSAVar,
        val: &SSAVar,
    ) -> bool {
        let Some(offset) = self
            .stack_slot_offset_for_var(addr)
            .or_else(|| self.extract_stack_offset_from_var(addr))
        else {
            return false;
        };
        if offset >= 0 {
            return false;
        }

        let Some(value) = self.prepared_value_id_for_var(val) else {
            return false;
        };
        let Some(fact) = self.certified_call_result_fact_for_value(value) else {
            return false;
        };
        let Some(call_result_facts) = self.inputs.call_result_facts() else {
            return false;
        };
        let Some(r2ssa::ValueOwner::StackSlot {
            offset: owner_offset,
            ..
        }) = call_result_facts.owner_for_value(value)
        else {
            return false;
        };
        if *owner_offset != offset {
            return false;
        }

        let source_call = (fact.callsite.block_addr, fact.callsite.op_index);
        let Some(CExpr::Var(owner_name)) =
            self.certified_assigned_call_result_owner_expr_for_source(source_call)
        else {
            return false;
        };
        self.stack_offset_for_visible_storage_name(&owner_name)
            .is_some_and(|materialized_offset| materialized_offset == offset)
            || self.resolve_stack_var(offset).is_some_and(|slot_name| {
                owner_name.eq_ignore_ascii_case(&slot_name)
                    || self.visible_names_share_stack_slot(&owner_name, &slot_name)
            })
    }

    fn op_to_stmt_impl(&self, op: &SSAOp) -> Option<CStmt> {
        match op {
            SSAOp::Copy { dst, src } => {
                if self.is_entry_arg_alias_copy(dst, src) {
                    return None;
                }
                if self.is_uninitialized_return_register_copy(dst, src) {
                    return None;
                }
                let lhs = self.assignment_lhs_expr(dst);
                let certified_rhs = self
                    .requires_certified_rendering()
                    .then(|| self.render_certified_value_expr_for_var(src))
                    .flatten();
                let rhs_base = if let Some(certified) = certified_rhs {
                    certified
                } else if dst.is_memory() {
                    let raw = self.lookup_definition_raw(&src.display_name());
                    let direct = self.direct_definition_expr(&src.display_name());
                    let preferred = if raw
                        .as_ref()
                        .is_some_and(|expr| self.expr_is_address_artifact_in_scalar_context(expr))
                    {
                        self.choose_preferred_visible_expr(
                            raw.clone(),
                            direct.filter(|expr| {
                                !self.expr_is_address_artifact_in_scalar_context(expr)
                            }),
                        )
                    } else {
                        self.choose_preferred_visible_expr(raw.clone(), direct)
                    };
                    preferred.unwrap_or_else(|| self.get_expr(src))
                } else {
                    let raw = self.get_expr(src);
                    if matches!(
                        &raw,
                        CExpr::Var(name)
                            if self.should_force_imported_call_resolution_name(name)
                                || is_generic_stack_placeholder_alias(name)
                    ) {
                        let mut semantic_visited = HashSet::new();
                        let semantic = self.render_semantic_value_by_name(
                            &src.display_name(),
                            0,
                            &mut semantic_visited,
                        );
                        let visible = self.best_visible_definition(&src.display_name());
                        let direct = self
                            .direct_definition_expr(&src.display_name())
                            .or_else(|| self.lookup_definition_raw(&src.display_name()));
                        self.choose_preferred_visible_expr(
                            self.choose_preferred_visible_expr(semantic, visible),
                            direct,
                        )
                        .filter(|expr| {
                            !matches!(
                                expr,
                                CExpr::Var(name)
                                    if name.eq_ignore_ascii_case(&src.display_name())
                            )
                        })
                        .unwrap_or(raw)
                    } else {
                        raw
                    }
                };
                let rhs = self.resolve_predicate_rhs_for_var(src, rhs_base);
                let rhs = if !self.is_pointer_typed_var(src) && !self.is_pointer_typed_var(dst) {
                    self.collapse_scalar_stack_addr_artifact(rhs)
                } else {
                    rhs
                };
                let rhs = self.assignment_rhs_with_type_policy(dst, Some(src), rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Load { dst, addr, space } => {
                if *space != r2il::SpaceId::Ram {
                    return Some(self.certified_residual_comment(format!(
                        "unsupported exact memory load space {} at 0x{:x}:{}",
                        space,
                        self.current_block_addr.get().unwrap_or_default(),
                        self.current_op_idx.get().unwrap_or_default()
                    )));
                }
                let lhs = self.assignment_lhs_expr(dst);
                let elem_ty = self
                    .type_hint_for_var(dst)
                    .unwrap_or_else(|| type_from_size(dst.size));
                let rhs = self.render_canonical_load_expr(dst, addr, elem_ty.clone());
                let rhs = if let CExpr::Var(lhs_name) = &lhs
                    && !self.requires_certified_rendering()
                    && let Some(source_call) = self
                        .call_result_source_for_ssa_name(&dst.display_name())
                        .or_else(|| self.local_post_call_source_for_ssa_name(&dst.display_name()))
                    && (self
                        .stable_owned_call_result_name_for_source(source_call)
                        .is_some_and(|owner| {
                            owner.eq_ignore_ascii_case(lhs_name)
                                || self.visible_names_share_stack_slot(&owner, lhs_name)
                        })
                        || self
                            .stack_offset_for_visible_storage_name(lhs_name)
                            .is_some_and(|offset| {
                                offset < 0
                                    && !self.is_autogenerated_stack_home_name(lhs_name)
                                    && !lhs_name.ends_with("_home")
                            }))
                {
                    self.recovered_owned_call_result_definition_rhs_for_visible_name(lhs_name)
                        .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
                        .unwrap_or(rhs.clone())
                } else {
                    rhs
                };
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Store { addr, val, space } => {
                if *space != r2il::SpaceId::Ram {
                    return Some(self.certified_residual_comment(format!(
                        "unsupported exact memory store space {} at 0x{:x}:{}",
                        space,
                        self.current_block_addr.get().unwrap_or_default(),
                        self.current_op_idx.get().unwrap_or_default()
                    )));
                }
                if self.is_entry_arg_alias_store(addr, val) {
                    return None;
                }
                if self.is_materialized_call_result_stack_home_store(addr, val) {
                    return None;
                }
                let elem_ty = self
                    .type_hint_for_var(val)
                    .unwrap_or_else(|| type_from_size(val.size));
                let mut certified_store_fact = None;
                let lhs = self.render_canonical_store_target_expr(addr, val.size, elem_ty.clone());
                let mut rhs = if let CExpr::Var(lhs_name) = &lhs
                    && let Some(source_call) = self
                        .call_result_source_for_ssa_name(&val.display_name())
                        .or_else(|| self.local_post_call_source_for_ssa_name(&val.display_name()))
                    && (self
                        .stable_owned_call_result_name_for_source(source_call)
                        .is_some_and(|owner| {
                            owner.eq_ignore_ascii_case(lhs_name)
                                || self.visible_names_share_stack_slot(&owner, lhs_name)
                        })
                        || self
                            .stack_offset_for_visible_storage_name(lhs_name)
                            .is_some_and(|offset| {
                                offset < 0
                                    && !self.is_autogenerated_stack_home_name(lhs_name)
                                    && !lhs_name.ends_with("_home")
                            })) {
                    self.call_result_exprs_map()
                        .get(&source_call)
                        .cloned()
                        .map(|expr| {
                            self.normalize_call_expr_for_source_call(
                                source_call,
                                expr,
                                FinalExprNormalizeContext::DefinitionRoot,
                            )
                        })
                        .or_else(|| {
                            self.call_result_aliases_map()
                                .get(&source_call)
                                .into_iter()
                                .flat_map(|aliases| aliases.iter())
                                .find_map(|alias| {
                                    self.direct_definition_expr(alias)
                                        .or_else(|| self.lookup_definition_raw(alias))
                                        .filter(|expr| matches!(expr, CExpr::Call { .. }))
                                        .map(|expr| {
                                            self.normalize_call_expr_for_source_call(
                                                source_call,
                                                expr,
                                                FinalExprNormalizeContext::DefinitionRoot,
                                            )
                                        })
                                })
                        })
                        .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
                        .or_else(|| {
                            self.recovered_owned_call_result_definition_rhs(
                                lhs_name,
                                &CExpr::Var(val.display_name()),
                            )
                        })
                        .or_else(|| {
                            self.recovered_owned_call_result_definition_rhs(
                                lhs_name,
                                &self.get_expr(val),
                            )
                        })
                        .or_else(|| {
                            self.direct_definition_expr(&val.display_name())
                                .or_else(|| self.lookup_definition_raw(&val.display_name()))
                                .filter(|expr| matches!(expr, CExpr::Call { .. }))
                                .map(|expr| {
                                    self.normalize_call_expr_for_source_call(
                                        source_call,
                                        expr,
                                        FinalExprNormalizeContext::DefinitionRoot,
                                    )
                                })
                        })
                        .unwrap_or_else(|| self.get_expr(val))
                } else {
                    self.get_expr(val)
                };
                let lhs_is_pointer_typed = matches!(
                    &lhs,
                    CExpr::Var(name) if matches!(self.lookup_type_hint(name), Some(CType::Pointer(_)))
                );
                if let Some(rmw_rhs) = self.stack_read_modify_write_rhs(&lhs, addr, val) {
                    rhs = rmw_rhs;
                } else {
                    if !self.is_pointer_typed_var(val) || !lhs_is_pointer_typed {
                        rhs = self.collapse_scalar_stack_addr_artifact(rhs);
                    }
                    if !lhs_is_pointer_typed {
                        rhs = self.rewrite_scalar_stack_placeholder_rhs(&lhs, rhs);
                    }
                }

                if let Some(val_ty) = self.type_hint_for_var(val)
                    && matches!(val_ty, CType::Pointer(_))
                    && !self.looks_like_pointer(&rhs)
                {
                    rhs = CExpr::cast(val_ty, rhs);
                }
                if let Some((block_addr, op_idx, space, address, value)) = certified_store_fact {
                    self.record_effect_render_proof_for_memory(
                        EffectRenderProofKind::MemoryWrite,
                        block_addr,
                        op_idx,
                        space,
                        address,
                        value,
                    );
                }
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Fence { ordering } => Some(CStmt::Expr(CExpr::call(
                CExpr::Var("memory_fence".to_string()),
                vec![CExpr::StringLit(memory_ordering_name(ordering).to_string())],
            ))),
            SSAOp::LoadLinked {
                dst,
                space,
                addr,
                ordering,
            } => {
                let lhs = self.assignment_lhs_expr(dst);
                let call = CExpr::call(
                    CExpr::Var("load_linked".to_string()),
                    vec![
                        CExpr::StringLit(space.to_string()),
                        self.get_expr(addr),
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::StoreConditional {
                result,
                space,
                addr,
                val,
                ordering,
            } => {
                let call = CExpr::call(
                    CExpr::Var("store_conditional".to_string()),
                    vec![
                        CExpr::StringLit(space.to_string()),
                        self.get_expr(addr),
                        self.get_expr(val),
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                if let Some(dst) = result {
                    let lhs = self.assignment_lhs_expr(dst);
                    Some(CStmt::Expr(CExpr::assign(lhs, call)))
                } else {
                    Some(CStmt::Expr(call))
                }
            }
            SSAOp::AtomicCAS {
                dst,
                space,
                addr,
                expected,
                replacement,
                ordering,
            } => {
                let lhs = self.assignment_lhs_expr(dst);
                let call = CExpr::call(
                    CExpr::Var("atomic_cas".to_string()),
                    vec![
                        CExpr::StringLit(space.to_string()),
                        self.get_expr(addr),
                        self.get_expr(expected),
                        self.get_expr(replacement),
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::LoadGuarded {
                dst,
                space,
                addr,
                guard,
                ordering,
            } => {
                let lhs = self.assignment_lhs_expr(dst);
                let call = CExpr::call(
                    CExpr::Var("load_guarded".to_string()),
                    vec![
                        CExpr::StringLit(space.to_string()),
                        self.get_expr(addr),
                        self.get_expr(guard),
                        CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                    ],
                );
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::StoreGuarded {
                space,
                addr,
                val,
                guard,
                ordering,
            } => Some(CStmt::Expr(CExpr::call(
                CExpr::Var("store_guarded".to_string()),
                vec![
                    CExpr::StringLit(space.to_string()),
                    self.get_expr(addr),
                    self.get_expr(val),
                    self.get_expr(guard),
                    CExpr::StringLit(memory_ordering_name(ordering).to_string()),
                ],
            ))),
            SSAOp::IntAdd { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Add),
            SSAOp::IntSub { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Sub),
            SSAOp::IntMult { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Mul),
            SSAOp::IntDiv { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Div,
                Some(uint_type_from_size(dst.size)),
            ),
            SSAOp::IntSDiv { dst, a, b } => self.signed_divrem_stmt(dst, a, b, BinaryOp::Div),
            SSAOp::IntRem { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Mod,
                Some(uint_type_from_size(dst.size)),
            ),
            SSAOp::IntSRem { dst, a, b } => self.signed_divrem_stmt(dst, a, b, BinaryOp::Mod),
            SSAOp::IntAnd { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::BitAnd),
            SSAOp::IntOr { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::BitOr),
            SSAOp::IntXor { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::BitXor),
            SSAOp::IntLeft { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Shl),
            SSAOp::IntRight { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Shr,
                Some(uint_type_from_size(dst.size)),
            ),
            SSAOp::IntSRight { dst, a, b } => {
                self.binary_stmt_typed(dst, a, b, BinaryOp::Shr, Some(type_from_size(dst.size)))
            }
            SSAOp::IntLess { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Lt,
                Some(uint_type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntSLess { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Lt,
                Some(type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntLessEqual { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Le,
                Some(uint_type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntSLessEqual { dst, a, b } => self.binary_stmt_typed(
                dst,
                a,
                b,
                BinaryOp::Le,
                Some(type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntEqual { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Eq),
            SSAOp::IntNotEqual { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Ne),
            SSAOp::IntNegate { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::unary(UnaryOp::Neg, self.get_expr(src));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::IntNot { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::unary(UnaryOp::BitNot, self.get_expr(src));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::BoolAnd { dst, a, b } => self.boolean_stmt(dst, BinaryOp::And, a, b),
            SSAOp::BoolOr { dst, a, b } => self.boolean_stmt(dst, BinaryOp::Or, a, b),
            SSAOp::BoolXor { dst, a, b } => self.boolean_stmt(dst, BinaryOp::BitXor, a, b),
            SSAOp::BoolNot { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = self.resolve_predicate_rhs_for_var(
                    dst,
                    CExpr::unary(UnaryOp::Not, self.get_expr(src)),
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let ty = type_from_size(dst.size);
                let rhs =
                    self.resolve_predicate_rhs_for_var(dst, CExpr::cast(ty, self.get_expr(src)));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Trunc { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let ty = type_from_size(dst.size);
                let rhs =
                    self.resolve_predicate_rhs_for_var(dst, CExpr::cast(ty, self.get_expr(src)));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Piece { dst, hi, lo } => {
                let lhs = self.assignment_lhs_expr(dst);
                let shift_bits = lo.size.saturating_mul(8);
                let dst_ty = uint_type_from_size(dst.size);
                let hi_cast = CExpr::cast(dst_ty.clone(), self.get_expr(hi));
                let lo_cast = CExpr::cast(dst_ty.clone(), self.get_expr(lo));
                let shifted = if shift_bits == 0 {
                    hi_cast
                } else {
                    CExpr::binary(BinaryOp::Shl, hi_cast, CExpr::IntLit(shift_bits as i64))
                };
                let rhs = CExpr::binary(BinaryOp::BitOr, shifted, lo_cast);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Subpiece { dst, src, offset } => {
                let lhs = self.assignment_lhs_expr(dst);
                let src_expr = self
                    .requires_certified_rendering()
                    .then(|| self.render_certified_value_expr_for_var(src))
                    .flatten()
                    .unwrap_or_else(|| self.get_expr(src));
                let rhs = if *offset == 0 && dst.size == src.size {
                    src_expr
                } else if *offset == 0
                    && let Some(expr) = self.signed_divrem_expr_for_value(src)
                {
                    expr
                } else if *offset == 0 {
                    CExpr::cast(uint_type_from_size(dst.size), src_expr)
                } else {
                    let shift_bits = offset.saturating_mul(8);
                    let src_cast = CExpr::cast(uint_type_from_size(src.size), src_expr);
                    let shifted =
                        CExpr::binary(BinaryOp::Shr, src_cast, CExpr::IntLit(shift_bits as i64));
                    CExpr::cast(uint_type_from_size(dst.size), shifted)
                };
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatAdd { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Add),
            SSAOp::FloatSub { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Sub),
            SSAOp::FloatMult { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Mul),
            SSAOp::FloatDiv { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Div),
            SSAOp::FloatNeg { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::unary(UnaryOp::Neg, self.get_expr(src));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatAbs { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::call(CExpr::Var("fabs".to_string()), vec![self.get_expr(src)]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatSqrt { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::call(CExpr::Var("sqrt".to_string()), vec![self.get_expr(src)]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatCeil { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::call(CExpr::Var("ceil".to_string()), vec![self.get_expr(src)]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatFloor { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::call(CExpr::Var("floor".to_string()), vec![self.get_expr(src)]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatRound { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::call(CExpr::Var("round".to_string()), vec![self.get_expr(src)]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatNaN { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::call(CExpr::Var("isnan".to_string()), vec![self.get_expr(src)]);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatLess { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Lt),
            SSAOp::FloatLessEqual { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Le),
            SSAOp::FloatEqual { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Eq),
            SSAOp::FloatNotEqual { dst, a, b } => self.binary_stmt(dst, a, b, BinaryOp::Ne),
            SSAOp::Int2Float { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::cast(CType::Float(dst.size), self.get_expr(src));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Float2Int { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::cast(type_from_size(dst.size), self.get_expr(src));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::FloatFloat { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = CExpr::cast(CType::Float(dst.size), self.get_expr(src));
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Call { target } => {
                // Note: Call arguments are handled by op_to_stmt_with_args().

                let func_expr = match (self.current_block_addr.get(), self.current_op_idx.get()) {
                    (Some(block_addr), Some(op_idx)) => {
                        self.resolve_call_target_for_site(block_addr, op_idx, target)
                    }
                    _ => self.resolve_call_target(target),
                };
                let call = CExpr::call(func_expr, vec![]);
                Some(CStmt::Expr(call))
            }
            SSAOp::CallInd { target } => {
                // Note: Call arguments are handled by op_to_stmt_with_args().

                let func_expr = match (self.current_block_addr.get(), self.current_op_idx.get()) {
                    (Some(block_addr), Some(op_idx)) => self
                        .resolved_callee_identity_expr_for_site(block_addr, op_idx)
                        .unwrap_or_else(|| CExpr::Deref(Box::new(self.get_expr(target)))),
                    _ => CExpr::Deref(Box::new(self.get_expr(target))),
                };
                let call = CExpr::call(func_expr, vec![]);
                Some(CStmt::Expr(call))
            }
            SSAOp::CallOther {
                output,
                userop,
                inputs,
            } => {
                let mut args = Vec::with_capacity(inputs.len() + 1);
                args.push(CExpr::StringLit(format!("userop_{}", userop)));
                for input in inputs {
                    args.push(self.get_expr(input));
                }
                let call = CExpr::call(CExpr::Var("callother".to_string()), args);
                if let Some(dst) = output {
                    let lhs = self.assignment_lhs_expr(dst);
                    Some(CStmt::Expr(CExpr::assign(lhs, call)))
                } else {
                    Some(CStmt::Expr(call))
                }
            }
            SSAOp::CpuId { dst } => {
                let call = CExpr::call(
                    CExpr::Var("callother".to_string()),
                    vec![CExpr::StringLit("cpuid".to_string())],
                );
                let lhs = self.assignment_lhs_expr(dst);
                Some(CStmt::Expr(CExpr::assign(lhs, call)))
            }
            SSAOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = self.ptr_arith_expr(base, index, *element_size, false);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = self.ptr_arith_expr(base, index, *element_size, true);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Cast { dst, src } => {
                let lhs = self.assignment_lhs_expr(dst);
                let rhs = self.resolve_predicate_rhs_for_var(
                    dst,
                    CExpr::cast(type_from_size(dst.size), self.get_expr(src)),
                );
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Select {
                dst,
                cond,
                if_true,
                if_false,
            } => {
                let lhs = self.assignment_lhs_expr(dst);
                let certified = |var: &SSAVar| {
                    self.requires_certified_rendering()
                        .then(|| self.certified_expr_for_prepared_var(var, 0, &mut BTreeSet::new()))
                        .flatten()
                };
                let rhs = CExpr::Ternary {
                    cond: Box::new(certified(cond).unwrap_or_else(|| self.get_expr(cond))),
                    then_expr: Box::new(
                        certified(if_true).unwrap_or_else(|| self.get_expr(if_true)),
                    ),
                    else_expr: Box::new(
                        certified(if_false).unwrap_or_else(|| self.get_expr(if_false)),
                    ),
                };
                let rhs = self.assignment_rhs_with_type_policy(dst, None, rhs);
                self.assign_stmt(lhs, rhs)
            }
            SSAOp::Return { target } => Some(CStmt::Return(Some(
                self.rewrite_stack_expr(self.get_return_expr(target)),
            ))),
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } => {
                // Handled by control flow structuring
                None
            }
            SSAOp::Phi { .. } => {
                // Phi nodes handled separately
                None
            }
            SSAOp::Nop => None,
            SSAOp::Unimplemented => Some(CStmt::comment("Unimplemented operation")),
            _ => None,
        }
    }

    fn prepared_stack_address_is_expression_plumbing(&self, value: &SSAVar) -> bool {
        let Some(prepared) = self.inputs.prepared_ssa else {
            return false;
        };
        let Some(stack_roots) = prepared.function().decompile_prep_facts() else {
            return false;
        };
        if stack_roots.stack_address_root_of(value).is_none() {
            return false;
        }
        let Some(value_id) = prepared.graph().value_id_for_var(value) else {
            return false;
        };
        self.prepared_value_is_stack_address_plumbing(prepared, value_id, &mut HashSet::new())
    }

    fn prepared_value_is_stack_address_plumbing(
        &self,
        prepared: &SsaArtifact,
        value: ValueId,
        visited: &mut HashSet<ValueId>,
    ) -> bool {
        if !visited.insert(value) {
            return true;
        }
        let Some(value_var) = prepared.value_var(value) else {
            return false;
        };
        for use_site in prepared.graph().use_sites(value) {
            let Some(inst) = prepared.graph().inst(use_site.inst) else {
                return false;
            };
            match &inst.payload {
                r2ssa::InstPayload::Phi { .. } => {
                    let Some(output) = inst.output else {
                        return false;
                    };
                    if !self.prepared_value_is_stack_address_plumbing(prepared, output, visited) {
                        return false;
                    }
                }
                r2ssa::InstPayload::Op(op) => {
                    let used_as_memory_address = matches!(
                        op,
                        SSAOp::Load { addr, .. }
                            | SSAOp::Store { addr, .. }
                            | SSAOp::LoadLinked { addr, .. }
                            | SSAOp::StoreConditional { addr, .. }
                            | SSAOp::AtomicCAS { addr, .. }
                            | SSAOp::LoadGuarded { addr, .. }
                            | SSAOp::StoreGuarded { addr, .. }
                            if addr == value_var
                    );
                    if used_as_memory_address {
                        continue;
                    }
                    let address_derivation = matches!(
                        op,
                        SSAOp::Copy { .. }
                            | SSAOp::Cast { .. }
                            | SSAOp::New { .. }
                            | SSAOp::IntAdd { .. }
                            | SSAOp::IntSub { .. }
                            | SSAOp::PtrAdd { .. }
                            | SSAOp::PtrSub { .. }
                    );
                    let Some(output) = address_derivation.then_some(inst.output).flatten() else {
                        return false;
                    };
                    if !self.prepared_value_is_stack_address_plumbing(prepared, output, visited) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Create a binary operation statement.
    fn binary_stmt(&self, dst: &SSAVar, a: &SSAVar, b: &SSAVar, op: BinaryOp) -> Option<CStmt> {
        self.binary_stmt_typed(dst, a, b, op, None)
    }

    fn binary_stmt_typed(
        &self,
        dst: &SSAVar,
        a: &SSAVar,
        b: &SSAVar,
        op: BinaryOp,
        operand_ty: Option<CType>,
    ) -> Option<CStmt> {
        let lhs = self.assignment_lhs_expr(dst);
        if matches!(op, BinaryOp::BitAnd | BinaryOp::BitOr)
            && let (Some(left_source), Some(right_source)) = (
                self.call_result_source_for_ssa_name(&a.display_name())
                    .or_else(|| self.local_post_call_source_for_ssa_name(&a.display_name())),
                self.call_result_source_for_ssa_name(&b.display_name())
                    .or_else(|| self.local_post_call_source_for_ssa_name(&b.display_name())),
            )
            && left_source == right_source
            && let Some(call_expr) = self
                .call_result_exprs_map()
                .get(&left_source)
                .cloned()
                .map(|expr| {
                    self.normalize_call_expr_for_source_call(
                        left_source,
                        expr,
                        FinalExprNormalizeContext::DefinitionRoot,
                    )
                })
                .or_else(|| self.synthesized_call_expr_for_source_call(left_source))
        {
            let rhs = self.assignment_rhs_with_type_policy(dst, None, call_expr);
            return self.assign_stmt(lhs, rhs);
        }
        let mut lhs_expr = self.get_expr(a);
        let mut rhs_expr = self.get_expr(b);
        if let Some(ty) = operand_ty {
            let a_hint = self.type_hint_for_var(a);
            let b_hint = self.type_hint_for_var(b);
            lhs_expr = self.cast_expr_if_needed(lhs_expr, ty.clone(), a_hint.as_ref());
            rhs_expr = self.cast_expr_if_needed(rhs_expr, ty, b_hint.as_ref());
        }
        if dst.size <= 4 && !self.is_pointer_typed_var(dst) {
            lhs_expr = self.collapse_scalar_stack_addr_artifact(lhs_expr);
            rhs_expr = self.collapse_scalar_stack_addr_artifact(rhs_expr);
        }
        let rhs_raw = self.identity_simplify_binary(
            op,
            lhs_expr,
            rhs_expr,
            (dst.size > 0).then_some(dst.size),
        );
        let rhs = if matches!(
            op,
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
        ) {
            self.resolve_predicate_rhs_for_var(dst, rhs_raw)
        } else {
            rhs_raw
        };
        let rhs = self.assignment_rhs_with_type_policy(dst, None, rhs);
        self.assign_stmt(lhs, rhs)
    }

    fn signed_divrem_stmt(
        &self,
        dst: &SSAVar,
        dividend: &SSAVar,
        divisor: &SSAVar,
        op: BinaryOp,
    ) -> Option<CStmt> {
        let lhs = self.assignment_lhs_expr(dst);
        let Some(rhs) = self.signed_divrem_expr(dividend, divisor, op) else {
            return self.binary_stmt_typed(
                dst,
                dividend,
                divisor,
                op,
                Some(type_from_size(dst.size)),
            );
        };
        let rhs = self.assignment_rhs_with_type_policy(dst, None, rhs);
        self.assign_stmt(lhs, rhs)
    }

    fn signed_divrem_expr_for_value(&self, value: &SSAVar) -> Option<CExpr> {
        match self.use_info().producers.get(&value.display_name())? {
            SSAOp::IntSDiv { a, b, .. } => self.signed_divrem_expr(a, b, BinaryOp::Div),
            SSAOp::IntSRem { a, b, .. } => self.signed_divrem_expr(a, b, BinaryOp::Mod),
            _ => None,
        }
    }

    fn signed_divrem_expr(
        &self,
        dividend: &SSAVar,
        divisor: &SSAVar,
        op: BinaryOp,
    ) -> Option<CExpr> {
        let dividend_root = self.signed_extended_dividend_low_root(dividend)?;
        let divisor_root = self
            .sign_extension_root(divisor)
            .unwrap_or_else(|| divisor.clone());
        let width = dividend_root.size.max(divisor_root.size);
        Some(self.identity_simplify_binary(
            op,
            self.get_expr(&dividend_root),
            self.get_expr(&divisor_root),
            (width > 0).then_some(width),
        ))
    }

    fn sign_extension_root(&self, value: &SSAVar) -> Option<SSAVar> {
        match self.use_info().producers.get(&value.display_name())? {
            SSAOp::IntSExt { src, .. } => Some(src.clone()),
            _ => None,
        }
    }

    fn signed_extended_dividend_low_root(&self, value: &SSAVar) -> Option<SSAVar> {
        let SSAOp::IntOr {
            a: high_part,
            b: low_part,
            ..
        } = self.use_info().producers.get(&value.display_name())?
        else {
            return None;
        };
        self.sign_extended_pair_low_root(high_part, low_part)
            .or_else(|| self.sign_extended_pair_low_root(low_part, high_part))
    }

    fn sign_extended_pair_low_root(
        &self,
        shifted_high: &SSAVar,
        low_zext: &SSAVar,
    ) -> Option<SSAVar> {
        let SSAOp::IntLeft {
            a: high_zext,
            b: shift,
            ..
        } = self
            .use_info()
            .producers
            .get(&shifted_high.display_name())?
        else {
            return None;
        };
        let SSAOp::IntZExt { src: high, .. } =
            self.use_info().producers.get(&high_zext.display_name())?
        else {
            return None;
        };
        let low_root = self.signed_high_limb_low_root(high)?;
        let SSAOp::IntZExt { src: low, .. } =
            self.use_info().producers.get(&low_zext.display_name())?
        else {
            return None;
        };
        if self.same_storage_value(low, low_root)
            && shift_matches_signed_concat_width(&shift.name, high, low, low_root)
        {
            Some(low_root.clone())
        } else {
            None
        }
    }

    fn signed_high_limb_low_root<'b>(&'b self, high: &'b SSAVar) -> Option<&'b SSAVar> {
        match self.use_info().producers.get(&high.display_name())? {
            SSAOp::Subpiece { src: sext, .. } => {
                match self.use_info().producers.get(&sext.display_name())? {
                    SSAOp::IntSExt { src, .. } => Some(src),
                    _ => None,
                }
            }
            SSAOp::IntSExt { src, .. } => Some(src),
            _ => None,
        }
    }

    fn boolean_stmt(&self, dst: &SSAVar, op: BinaryOp, a: &SSAVar, b: &SSAVar) -> Option<CStmt> {
        let lhs = self.assignment_lhs_expr(dst);
        let rhs = self.resolve_predicate_rhs_for_var(
            dst,
            CExpr::binary(op, self.get_expr(a), self.get_expr(b)),
        );
        self.assign_stmt(lhs, rhs)
    }
}

/// Parse a constant value from a name like "const:0x42" or "const:42".
pub(crate) fn parse_const_value(name: &str) -> Option<u64> {
    analysis::utils::parse_const_value(name)
}

fn const_value_may_equal(name: &str, expected: u64) -> bool {
    if parse_const_value(name) == Some(expected) {
        return true;
    }
    parse_address_from_var_name(name) == Some(expected)
}

fn push_linear_term(terms: &mut Vec<(CExpr, i64)>, term: CExpr, coeff: i64) -> Option<()> {
    if coeff == 0 {
        return Some(());
    }
    if let Some((_, existing)) = terms.iter_mut().find(|(existing, _)| *existing == term) {
        *existing = existing.checked_add(coeff)?;
    } else {
        terms.push((term, coeff));
    }
    Some(())
}

fn linear_coeff_expr(term: CExpr, coeff: i64) -> Option<CExpr> {
    match coeff {
        0 => Some(CExpr::IntLit(0)),
        1 => Some(term),
        _ => Some(CExpr::binary(BinaryOp::Mul, term, CExpr::IntLit(coeff))),
    }
}

fn shift_matches_signed_concat_width(
    shift_name: &str,
    high: &SSAVar,
    low: &SSAVar,
    low_root: &SSAVar,
) -> bool {
    [low.size, low_root.size, high.size]
        .into_iter()
        .filter(|size| *size > 0)
        .any(|size| const_value_may_equal(shift_name, u64::from(size.saturating_mul(8))))
}

pub(super) fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

pub(crate) fn should_replace_preserved_stack_alias(existing: &str) -> bool {
    let normalized = existing.trim_start_matches('&');
    normalized == "stack"
        || normalized.starts_with("local_")
        || normalized.starts_with("stack_")
        || normalized == "saved_fp"
}

pub(crate) fn is_generic_stack_placeholder_alias(existing: &str) -> bool {
    analysis::utils::is_generic_stack_placeholder_alias(existing)
}

fn should_replace_preserved_stack_expr(existing: &CExpr, preserved: &CExpr) -> bool {
    match (existing, preserved) {
        (CExpr::Var(existing_name), CExpr::Var(preserved_name)) => {
            should_replace_preserved_stack_alias(existing_name)
                && !should_replace_preserved_stack_alias(preserved_name)
        }
        _ => false,
    }
}

fn normalize_stack_definition_overrides(stack_info: &mut analysis::StackInfo) {
    let replacements: Vec<(String, CExpr)> = stack_info
        .definition_overrides
        .iter()
        .filter_map(|(key, expr)| {
            let CExpr::Var(name) = expr else {
                return None;
            };
            let offset = if let Some(rest) = name.strip_prefix("local_") {
                i64::from_str_radix(rest, 16).ok().map(|v| -v)
            } else if let Some(rest) = name.strip_prefix("stack_") {
                i64::from_str_radix(rest, 16).ok()
            } else {
                None
            }?;
            let preferred = stack_info.stack_vars.get(&offset)?;
            if should_replace_preserved_stack_alias(name)
                && !should_replace_preserved_stack_alias(preferred)
            {
                Some((key.clone(), CExpr::Var(preferred.clone())))
            } else {
                None
            }
        })
        .collect();
    for (key, expr) in replacements {
        stack_info.definition_overrides.insert(key, expr);
    }
}

fn call_arg_callee_name(expr: &CExpr) -> Option<&str> {
    match expr {
        CExpr::Var(name) => Some(name.as_str()),
        CExpr::Deref(inner) | CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
            call_arg_callee_name(inner)
        }
        CExpr::Cast { expr: inner, .. } => call_arg_callee_name(inner),
        _ => None,
    }
}

/// Check if a string looks like a hex number.
fn is_hex_name(value: &str) -> bool {
    !value.is_empty() && value.chars().all(|c| c.is_ascii_hexdigit())
}

/// Get a C type from a bit size.
fn type_from_size(size: u32) -> CType {
    match size {
        0 => CType::Unknown,
        1 => CType::Int(8),
        2 => CType::Int(16),
        4 => CType::Int(32),
        8 => CType::Int(64),
        _ => CType::Int(size.saturating_mul(8)),
    }
}

fn uint_type_from_size(size: u32) -> CType {
    match size {
        0 => CType::Unknown,
        1 => CType::UInt(8),
        2 => CType::UInt(16),
        4 => CType::UInt(32),
        8 => CType::UInt(64),
        _ => CType::UInt(size.saturating_mul(8)),
    }
}

fn memory_ordering_name(ordering: &r2il::MemoryOrdering) -> &'static str {
    match ordering {
        r2il::MemoryOrdering::Relaxed => "relaxed",
        r2il::MemoryOrdering::Acquire => "acquire",
        r2il::MemoryOrdering::Release => "release",
        r2il::MemoryOrdering::AcqRel => "acq_rel",
        r2il::MemoryOrdering::SeqCst => "seq_cst",
        r2il::MemoryOrdering::Unknown => "unknown",
    }
}

#[cfg(test)]
#[test]
fn callother_ids_share_effect_and_result_lowering() {
    let ctx = FoldingContext::new(64);
    let input = SSAVar::new("X30", 0, 8);
    let output = SSAVar::new("X30", 1, 8);

    for userop in [7, 0x7fff_ffff, 0x8000_0000, u32::MAX] {
        let stmt = ctx.op_to_stmt_impl(&SSAOp::CallOther {
            output: Some(output.clone()),
            userop,
            inputs: vec![input.clone()],
        });
        assert_eq!(
            stmt,
            Some(CStmt::Expr(CExpr::assign(
                CExpr::Var("x30_1".to_string()),
                CExpr::call(
                    CExpr::Var("callother".to_string()),
                    vec![
                        CExpr::StringLit(format!("userop_{userop}")),
                        CExpr::Var("x30".to_string()),
                    ],
                ),
            ))),
            "numeric userop must retain its explicit result assignment"
        );
    }

    let effect_userop = u32::MAX;
    let stmt = ctx.op_to_stmt_impl(&SSAOp::CallOther {
        output: None,
        userop: effect_userop,
        inputs: vec![input],
    });
    assert_eq!(
        stmt,
        Some(CStmt::Expr(CExpr::call(
            CExpr::Var("callother".to_string()),
            vec![
                CExpr::StringLit(format!("userop_{effect_userop}")),
                CExpr::Var("x30".to_string()),
            ],
        ))),
        "outputless CallOther must retain its explicit effect"
    );
}

#[cfg(test)]
#[path = "../tests/lowering.rs"]
mod lowering_tests;

include!("../tests/pipeline.rs");
