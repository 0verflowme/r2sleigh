//! Certified SSA-to-C operation lowering.
//!
//! This module renders the binding dispositions, per-use projections, and
//! effect decisions sealed by upstream analysis. Inlining and elision happen
//! only when those plans authorize them; lowering itself does not infer either
//! policy from use counts, names, or expression shape.

use std::collections::BTreeSet;
#[cfg(test)]
use std::collections::HashMap;

use r2ssa::{DecompilePrepFacts, SSAOp, SSAVar, SsaArtifact, ValueId};
#[cfg(test)]
use r2types::normalize_callee_name;
use r2types::{
    CalleeIdentity, FunctionRenderFacts, ReturnValueRenderFact, SourceOwnedFunctionFacts,
};

use crate::analysis;
pub(crate) use crate::analysis::lower::OpLoweringRefusal;
use crate::ast::{BinaryOp, CExpr, CStmt, CType, UnaryOp};
use crate::binding_plan::{BindingPlan, BindingPlanSourceMismatch};

use super::SSABlock;
use super::context::{EffectOccurrenceKind, FoldingContext};

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

mod aliases;
mod calls;
mod lowering;
mod memory_renderer;
mod projection;

#[derive(Debug, Clone, PartialEq)]
enum LoweredOp {
    Assign { lhs: CExpr, rhs: CExpr },
    FinalizedStmt(CStmt),
    Expr(CExpr),
    None,
}

pub(crate) type OpLoweringResult<T> = Result<T, OpLoweringRefusal>;

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CertifiedCallExpr {
    pub(super) expr: CExpr,
    pub(super) target: ValueId,
    pub(super) values: Vec<ValueId>,
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

    fn call_arg_expr(
        &self,
        site: (u64, usize),
        index: usize,
        value: r2ssa::ValueId,
    ) -> Option<CExpr> {
        if !self.proof.expression_is_renderable(value) {
            return None;
        }
        let call_view = self.prepared_view.call_view_for_site(site)?;
        let callsite = r2types::CallsiteKey {
            block_addr: site.0,
            op_index: site.1,
        };
        let render_fact = self.function_facts.call_render()?.fact_for_site(callsite)?;
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
        if render_fact.proof_values.get(index).copied() != Some(value)
            || call_view.authoritative_arg_values.get(index).copied() != Some(value)
            || call_view.render_fact.as_ref() != Some(render_fact)
        {
            return None;
        }
        call_view.authoritative_args.get(index).cloned()
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

/// Parse a constant value from a name like "const:0x42" or "const:42".
#[cfg(test)]
pub(crate) fn parse_const_value(name: &str) -> Option<u64> {
    analysis::utils::parse_const_value(name)
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

include!("implementation.rs");
