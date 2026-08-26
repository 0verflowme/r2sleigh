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
    DecompilePrepFacts, MemoryLocation, ObjectKind, ObjectModel, PreparedFunctionFacts,
    SSAFunction, SSAOp, SSAVar, SSAVarNameKind, SsaArtifact, ValueId,
};
#[cfg(test)]
use r2ssa::MemoryDefFact;
#[cfg(test)]
use r2types::StackSlotKey;
#[cfg(test)]
use r2types::TypeOracle;
#[cfg(test)]
use r2types::normalize_callee_name;
use r2types::{
    CTypeLike, CalleeIdentity, ExternalField, ExternalStackBase, ExternalStackSlotRole,
    ExternalStruct, ExternalUnion, FunctionRenderFacts, ReturnValueRenderFact,
    SourceOwnedFunctionFacts, normalize_external_type_name, parse_type_like_spec,
};

use crate::address::parse_address_from_var_name;
use crate::analysis;
pub(crate) use crate::analysis::lower::OpLoweringRefusal;
use crate::ast::{BinaryOp, CExpr, CStmt, CType, UnaryOp};
use crate::binding_plan::{BindingPlan, BindingPlanSourceMismatch};
use crate::registers::register_family_name;

use super::SSABlock;
use super::context::{EffectOccurrenceKind, FoldingContext};
use super::context::{ResolutionGuardKey, ResolutionPhase};
use super::{
    MAX_ALIAS_REWRITE_DEPTH, MAX_PREDICATE_OPERAND_DEPTH, MAX_RETURN_EXPR_DEPTH,
    MAX_SIMPLE_EXPR_DEPTH,
};

/// Stage-3 lowering seam. Construction checks that the plan, its machine
/// projection, and the source-owned report all refer to the exact same SSA
/// artifact before a lowering path can observe the pair.
#[allow(
    dead_code,
    reason = "Stage 1 API seam; Stage 3 moves existing lowering behind it"
)]
pub(crate) struct PlannedLoweringInput<'a> {
    source: &'a SourceOwnedFunctionFacts,
    plan: &'a BindingPlan,
}

#[allow(
    dead_code,
    reason = "Stage 1 API seam; Stage 3 moves existing lowering behind it"
)]
impl<'a> PlannedLoweringInput<'a> {
    pub(crate) fn try_new(
        source: &'a SourceOwnedFunctionFacts,
        plan: &'a BindingPlan,
    ) -> Result<Self, BindingPlanSourceMismatch> {
        plan.validate_source(source.source())?;
        Ok(Self { source, plan })
    }

    pub(crate) const fn source(&self) -> &'a SourceOwnedFunctionFacts {
        self.source
    }

    pub(crate) const fn plan(&self) -> &'a BindingPlan {
        self.plan
    }
}

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
        CType::Int(bits) | CType::UInt(bits) | CType::BitVector(bits) | CType::Float(bits) => {
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
mod projection;
mod return_resolver;

#[derive(Debug, Clone, PartialEq)]
enum LoweredOp {
    Assign { lhs: CExpr, rhs: CExpr },
    FinalizedStmt(CStmt),
    Expr(CExpr),
    None,
    Comment(String),
}

pub(crate) type OpLoweringResult<T> = Result<T, OpLoweringRefusal>;

/// The authoritative result of lowering one operation for expression use.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum LoweredExprAt {
    Rendered(CExpr),
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

pub(crate) fn expr_is_side_effect_free(expr: &CExpr) -> bool {
    match expr {
        CExpr::Observed { expr, .. } => expr_is_side_effect_free(expr),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => true,
        CExpr::Paren(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Sizeof(inner) => expr_is_side_effect_free(inner),
        CExpr::Unary { op, operand } => {
            !matches!(
                op,
                UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
            ) && expr_is_side_effect_free(operand)
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
            ) && expr_is_side_effect_free(left)
                && expr_is_side_effect_free(right)
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_is_side_effect_free(cond)
                && expr_is_side_effect_free(then_expr)
                && expr_is_side_effect_free(else_expr)
        }
        CExpr::Subscript { base, index } => {
            expr_is_side_effect_free(base) && expr_is_side_effect_free(index)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            expr_is_side_effect_free(base)
        }
        CExpr::Comma(values) => values.iter().all(expr_is_side_effect_free),
        CExpr::Call { .. } => false,
    }
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

fn stmt_contains_memory_like_access(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::StructuredRegion { stmt, .. } => stmt_contains_memory_like_access(stmt),
        CStmt::Observed { stmt, .. } => stmt_contains_memory_like_access(stmt),
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
    /// Whether ordinary operand lowering owns occurrence markers.
    /// Marker-free expression lowering decorates its completed answer instead.
    observe_inputs: bool,
    /// Exact normalized operation used only for render-observation identity.
    normalized_site: Option<crate::normalize::NormalizedOpSite>,
    /// Original source operation used only for callsite/type/render facts.
    source_call_site: Option<(u64, usize)>,
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
        names: &crate::binding_plan::BindingNameResolution,
    ) -> Option<CExpr> {
        if fact.is_write || fact.width == 0 {
            return None;
        }
        let offset = self.proof.render_facts.stack_slot_offset(fact.object)?;
        self
            .function_facts
            .authorized_stack_param_owner_render(fact.object, offset)?;
        let mut matching_slots = self
            .function_facts
            .type_facts()
            .stack_slots
            .iter()
            .filter(|(key, slot)| {
                key.offset == offset
                    && matches!(
                        slot.role,
                        ExternalStackSlotRole::StackArg | ExternalStackSlotRole::ParamHome
                    )
            });
        let (_, slot) = matching_slots.next()?;
        if matching_slots.next().is_some() {
            return None;
        }
        let slot = u32::try_from(slot.param_index?).ok()?;
        match names.require_parameter_slot(slot).ok()? {
            crate::binding_plan::PlannedParameterSymbol::Bound { symbol, .. } => {
                Some(CExpr::Var(symbol))
            }
            crate::binding_plan::PlannedParameterSymbol::Refused(_)
            | crate::binding_plan::PlannedParameterSymbol::Absent => {
                unreachable!("require_parameter_slot cannot return absent or refused")
            }
        }
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
    #[cfg(test)]
    fn for_expr() -> Self {
        Self {
            mode: LowerMode::Expr,
            observe_inputs: false,
            normalized_site: None,
            source_call_site: None,
            with_call_args: false,
        }
    }

    /// Expression lowering whose operands retain their exact AST positions.
    fn for_observed_expr(normalized_site: Option<crate::normalize::NormalizedOpSite>) -> Self {
        Self {
            mode: LowerMode::Expr,
            observe_inputs: true,
            normalized_site,
            source_call_site: None,
            with_call_args: false,
        }
    }

    fn for_stmt(
        normalized_site: Option<crate::normalize::NormalizedOpSite>,
        source_call_site: Option<(u64, usize)>,
        with_call_args: bool,
    ) -> Self {
        Self {
            mode: LowerMode::Stmt,
            observe_inputs: true,
            normalized_site,
            source_call_site,
            with_call_args,
        }
    }
}

include!("implementation.rs");

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

fn call_arg_callee_name(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    expr: &CExpr,
) -> Option<std::rc::Rc<str>> {
    match expr {
        CExpr::Observed { expr, .. } => call_arg_callee_name(symbols, expr),
        // A local binding may hold a function pointer, but its spelling is not
        // the identity of the external function it may point at.
        CExpr::Var(_) => None,
        // A call names something outside the function, so the callee is an
        // external. Matching only variables here lost the signature for every
        // call the moment callees started saying what they are.
        CExpr::External { name, .. } => Some(std::rc::Rc::from(name.as_str())),
        CExpr::Deref(inner) | CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
            call_arg_callee_name(symbols, inner)
        }
        CExpr::Cast { expr: inner, .. } => call_arg_callee_name(symbols, inner),
        _ => None,
    }
}

/// Get a C type from a bit size.
fn type_from_size(size: u32) -> CType {
    match size {
        0 => CType::Unknown,
        1 => CType::Int(8),
        2 => CType::Int(16),
        4 => CType::Int(32),
        8 => CType::Int(64),
        16 => CType::Int(128),
        _ => CType::BitVector(size.saturating_mul(8)),
    }
}

fn uint_type_from_size(size: u32) -> CType {
    match size {
        0 => CType::Unknown,
        1 => CType::UInt(8),
        2 => CType::UInt(16),
        4 => CType::UInt(32),
        8 => CType::UInt(64),
        16 => CType::UInt(128),
        _ => CType::BitVector(size.saturating_mul(8)),
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
