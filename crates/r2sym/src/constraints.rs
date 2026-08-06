//! Canonical constraint graph derived from semantic evidence.
//!
//! This module deliberately records what is known and how it was derived. A
//! constraint graph can feed tactics, but verification remains responsible for
//! deciding whether a produced candidate is a proven solve.

use std::collections::{BTreeMap, HashSet};

use r2ssa::SSAOp;
use r2ssa::{AssumptionSubject, AssumptionValue, CompareKind, SSAVar, SsaArtifact};

use crate::loops::{
    ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, LoopFoldOperation, LoopMemoryTermKind,
    exact_fold_evidence_from_recurrences,
};
use crate::path::PathResult;
use crate::solver::SymModel;
use crate::{SymState, SymValue};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FinalConstraintPrecision {
    Exact,
    ModelConditioned,
    Residual,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FinalConstraintSource {
    TerminalCompareExact,
    ExactRecurrenceAggregateModel,
    MemoryWindowAssumption,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecurrenceAggregateConstraint {
    pub recurrence: ExactLoopRecurrenceEvidence,
    pub target: u64,
    pub bits: u32,
    pub source: FinalConstraintSource,
    pub precision: FinalConstraintPrecision,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecurrenceAggregateRangeConstraint {
    pub recurrence: ExactLoopRecurrenceEvidence,
    pub min: u64,
    pub max: u64,
    pub bits: u32,
    pub source: FinalConstraintSource,
    pub precision: FinalConstraintPrecision,
    pub reasons: Vec<String>,
}

pub type FoldAggregateConstraint = RecurrenceAggregateConstraint;
pub type FoldAggregateRangeConstraint = RecurrenceAggregateRangeConstraint;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputByteConstraint {
    pub addr: u64,
    pub allowed: Vec<u8>,
    pub precision: FinalConstraintPrecision,
    pub source: FinalConstraintSource,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputLengthConstraint {
    pub base_addr: u64,
    pub len: u32,
    pub precision: FinalConstraintPrecision,
    pub source: FinalConstraintSource,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalConstraint {
    RecurrenceEquals(RecurrenceAggregateConstraint),
    RecurrenceRange(RecurrenceAggregateRangeConstraint),
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FinalConstraintGraph {
    pub constraints: Vec<FinalConstraint>,
    pub input_byte_constraints: Vec<InputByteConstraint>,
    pub input_length_constraints: Vec<InputLengthConstraint>,
    pub refusals: Vec<String>,
}

impl FinalConstraintGraph {
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    pub fn recurrence_aggregate_constraints(
        &self,
    ) -> impl Iterator<Item = &RecurrenceAggregateConstraint> {
        self.constraints
            .iter()
            .filter_map(|constraint| match constraint {
                FinalConstraint::RecurrenceEquals(constraint) => Some(constraint),
                FinalConstraint::RecurrenceRange(_) => None,
            })
    }

    pub fn recurrence_aggregate_range_constraints(
        &self,
    ) -> impl Iterator<Item = &RecurrenceAggregateRangeConstraint> {
        self.constraints
            .iter()
            .filter_map(|constraint| match constraint {
                FinalConstraint::RecurrenceEquals(_) => None,
                FinalConstraint::RecurrenceRange(constraint) => Some(constraint),
            })
    }

    pub fn constraints_iter(&self) -> impl Iterator<Item = &FinalConstraint> {
        self.constraints.iter()
    }

    pub fn exact_constraint_count(&self) -> usize {
        self.constraints_iter()
            .filter(|constraint| {
                constraint_precision(constraint) == FinalConstraintPrecision::Exact
            })
            .count()
    }

    pub fn model_conditioned_constraint_count(&self) -> usize {
        self.constraints_iter()
            .filter(|constraint| {
                constraint_precision(constraint) == FinalConstraintPrecision::ModelConditioned
            })
            .count()
    }

    pub fn strongest_precision(&self) -> FinalConstraintPrecision {
        if self.exact_constraint_count() > 0 {
            FinalConstraintPrecision::Exact
        } else if self.model_conditioned_constraint_count() > 0 {
            FinalConstraintPrecision::ModelConditioned
        } else if self.constraints_iter().any(|constraint| {
            constraint_precision(constraint) == FinalConstraintPrecision::Residual
        }) {
            FinalConstraintPrecision::Residual
        } else {
            FinalConstraintPrecision::Unknown
        }
    }

    pub fn has_exact_constraints(&self) -> bool {
        self.exact_constraint_count() > 0
    }

    pub fn merge(&mut self, other: Self) {
        self.constraints.extend(other.constraints);
        self.input_byte_constraints
            .extend(other.input_byte_constraints);
        self.input_length_constraints
            .extend(other.input_length_constraints);
        for reason in other.refusals {
            push_unique(&mut self.refusals, reason);
        }
        self.constraints
            .sort_by(|lhs, rhs| constraint_sort_key(lhs).cmp(&constraint_sort_key(rhs)));
        self.input_byte_constraints
            .sort_by(|lhs, rhs| lhs.addr.cmp(&rhs.addr));
        self.input_byte_constraints.dedup_by(|lhs, rhs| {
            lhs.addr == rhs.addr
                && lhs.allowed == rhs.allowed
                && lhs.precision == rhs.precision
                && lhs.source == rhs.source
        });
        self.input_length_constraints
            .sort_by(|lhs, rhs| lhs.base_addr.cmp(&rhs.base_addr));
        self.input_length_constraints.dedup_by(|lhs, rhs| {
            lhs.base_addr == rhs.base_addr
                && lhs.len == rhs.len
                && lhs.precision == rhs.precision
                && lhs.source == rhs.source
        });
    }
}

fn constraint_precision(constraint: &FinalConstraint) -> FinalConstraintPrecision {
    match constraint {
        FinalConstraint::RecurrenceEquals(constraint) => constraint.precision,
        FinalConstraint::RecurrenceRange(constraint) => constraint.precision,
    }
}

fn constraint_sort_key(constraint: &FinalConstraint) -> (u64, u64, &str, u64, u64, u8) {
    match constraint {
        FinalConstraint::RecurrenceEquals(constraint) => (
            constraint.recurrence.header,
            constraint.recurrence.exit_target,
            constraint.recurrence.accumulator.as_str(),
            constraint.target,
            constraint.target,
            0,
        ),
        FinalConstraint::RecurrenceRange(constraint) => (
            constraint.recurrence.header,
            constraint.recurrence.exit_target,
            constraint.recurrence.accumulator.as_str(),
            constraint.min,
            constraint.max,
            1,
        ),
    }
}

pub fn exact_fold_model_bytes<'ctx>(
    state: &SymState<'ctx>,
    fold: &ExactLoopFoldEvidence,
    model: &SymModel<'ctx>,
) -> Option<Vec<u8>> {
    if fold.term.bytes != 1 {
        return None;
    }
    let (Some(base), Some(stride)) = (fold.term.base, fold.term.stride) else {
        return None;
    };
    let mut bytes = Vec::with_capacity(fold.iterations as usize);
    for iteration in 0..fold.iterations {
        let offset = iteration.checked_mul(stride)?;
        let addr = base.checked_add(offset)?;
        let value = state.mem_read(&SymValue::concrete(addr, 64), 1);
        bytes.push(model.eval(&value)? as u8);
    }
    Some(bytes)
}

pub fn aggregate_exact_fold_bytes(fold: &ExactLoopFoldEvidence, bytes: &[u8]) -> Option<u64> {
    if fold.term.bytes != 1 || bytes.len() != fold.iterations as usize {
        return None;
    }
    let aggregate = match fold.operation {
        LoopFoldOperation::Xor => bytes.iter().fold(0u64, |acc, byte| acc ^ (*byte as u64)),
        LoopFoldOperation::Add => {
            let sum = bytes
                .iter()
                .fold(0u128, |acc, byte| acc.saturating_add(*byte as u128));
            if fold.bits >= 64 {
                sum as u64
            } else {
                (sum % (1u128 << fold.bits.max(1))) as u64
            }
        }
    };
    Some(mask_to_bits(aggregate, fold.bits))
}

pub fn build_model_conditioned_recurrence_constraint_graph<'ctx>(
    state: &SymState<'ctx>,
    recurrences: &[ExactLoopRecurrenceEvidence],
    model: &SymModel<'ctx>,
) -> FinalConstraintGraph {
    let mut graph = FinalConstraintGraph::default();
    for recurrence in recurrences {
        let Some(fold) = recurrence.as_fold() else {
            push_unique(
                &mut graph.refusals,
                format!(
                    "non_fold_model_conditioned_recurrence:{}",
                    recurrence.accumulator
                ),
            );
            continue;
        };
        if fold.term.kind != LoopMemoryTermKind::InputRead {
            push_unique(
                &mut graph.refusals,
                format!("non_input_recurrence_constraint:{}", recurrence.accumulator),
            );
            continue;
        }
        if fold.term.bytes != 1 {
            push_unique(
                &mut graph.refusals,
                format!("unsupported_recurrence_read_width:{}", fold.term.bytes),
            );
            continue;
        }
        let Some(bytes) = exact_fold_model_bytes(state, &fold, model) else {
            push_unique(
                &mut graph.refusals,
                format!(
                    "recurrence_model_bytes_unavailable:{}",
                    recurrence.accumulator
                ),
            );
            continue;
        };
        let Some(target) = aggregate_exact_fold_bytes(&fold, &bytes) else {
            push_unique(
                &mut graph.refusals,
                format!(
                    "recurrence_aggregate_unavailable:{}",
                    recurrence.accumulator
                ),
            );
            continue;
        };
        graph.constraints.push(FinalConstraint::RecurrenceEquals(
            RecurrenceAggregateConstraint {
                recurrence: recurrence.clone(),
                target,
                bits: recurrence.bits,
                source: FinalConstraintSource::ExactRecurrenceAggregateModel,
                precision: FinalConstraintPrecision::ModelConditioned,
                reasons: vec![
                    "target derived from selected-path exact recurrence model".to_string(),
                ],
            },
        ));
    }
    graph
        .constraints
        .sort_by(|lhs, rhs| constraint_sort_key(lhs).cmp(&constraint_sort_key(rhs)));
    graph
}

pub fn build_exact_fold_constraint_graph<'ctx>(
    state: &SymState<'ctx>,
    folds: &[ExactLoopFoldEvidence],
    model: &SymModel<'ctx>,
) -> FinalConstraintGraph {
    let recurrences = folds
        .iter()
        .cloned()
        .map(ExactLoopRecurrenceEvidence::from)
        .collect::<Vec<_>>();
    build_model_conditioned_recurrence_constraint_graph(state, &recurrences, model)
}

pub fn build_final_constraint_graph_for_path<'ctx>(
    func: &SsaArtifact,
    path: &PathResult<'ctx>,
    recurrences: &[ExactLoopRecurrenceEvidence],
    target_addr: u64,
    model: Option<&SymModel<'ctx>>,
) -> FinalConstraintGraph {
    let folds = exact_fold_evidence_from_recurrences(recurrences);
    let mut graph = extract_terminal_recurrence_constraints(func, path, recurrences, target_addr);
    graph.merge(extract_input_constraints_for_path(func, path, &folds));
    if graph.constraints.is_empty()
        && let Some(model) = model
    {
        graph.merge(build_model_conditioned_recurrence_constraint_graph(
            &path.state,
            recurrences,
            model,
        ));
    }
    graph
}

fn extract_terminal_recurrence_constraints<'ctx>(
    func: &SsaArtifact,
    path: &PathResult<'ctx>,
    recurrences: &[ExactLoopRecurrenceEvidence],
    target_addr: u64,
) -> FinalConstraintGraph {
    let mut graph = FinalConstraintGraph::default();
    let def_index = build_ssa_def_index(func);
    let Some(predecessor) = path.state.prev_pc() else {
        push_unique(&mut graph.refusals, "final_constraint_missing_predecessor");
        return graph;
    };

    let predicates = func
        .predicates()
        .predicates
        .values()
        .filter(|predicate| {
            predicate.block_addr == predecessor
                && (predicate.true_target == target_addr || predicate.false_target == target_addr)
        })
        .collect::<Vec<_>>();

    if predicates.is_empty() {
        push_unique(
            &mut graph.refusals,
            format!("final_constraint_missing_terminal_predicate:0x{predecessor:x}"),
        );
        return graph;
    }
    if predicates.len() > 1 {
        push_unique(
            &mut graph.refusals,
            format!("final_constraint_ambiguous_terminal_predicate:0x{predecessor:x}"),
        );
        return graph;
    }

    let predicate = predicates[0];
    let Some(comparison) = &predicate.comparison else {
        push_unique(
            &mut graph.refusals,
            format!("final_constraint_missing_compare:0x{predecessor:x}"),
        );
        return graph;
    };
    let branch_truth = predicate.true_target == target_addr;
    let Some(lhs) = func.value_var(comparison.lhs) else {
        push_unique(&mut graph.refusals, "final_constraint_missing_lhs");
        return graph;
    };
    let Some(rhs) = func.value_var(comparison.rhs) else {
        push_unique(&mut graph.refusals, "final_constraint_missing_rhs");
        return graph;
    };

    let lhs_const = parse_literal_var(lhs);
    let rhs_const = parse_literal_var(rhs);
    for recurrence in recurrences {
        let linked = if let Some(expr) =
            invertible_expr_for_recurrence_operand(func, &def_index, lhs, recurrence)
        {
            rhs_const.map(|target| TerminalCompareLink {
                target,
                const_name: rhs.display_name(),
                recurrence_is_lhs: true,
                expr,
            })
        } else if let Some(expr) =
            invertible_expr_for_recurrence_operand(func, &def_index, rhs, recurrence)
        {
            lhs_const.map(|target| TerminalCompareLink {
                target,
                const_name: lhs.display_name(),
                recurrence_is_lhs: false,
                expr,
            })
        } else {
            None
        };
        let Some(link) = linked else {
            continue;
        };
        let Some(constraint) = terminal_constraint_for_compare(
            predecessor,
            comparison.kind,
            branch_truth,
            recurrence,
            &link,
        ) else {
            continue;
        };
        graph.constraints.push(constraint);
    }

    if graph.constraints.is_empty() {
        push_unique(
            &mut graph.refusals,
            format!("final_constraint_compare_not_linked_to_exact_recurrence:0x{predecessor:x}"),
        );
    }
    graph
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FoldTransform {
    AddConst(u64),
    XorConst(u64),
    Scale(u64),
    RotateLeft(u32),
    RotateRight(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct InvertibleFoldExpr {
    bits: u32,
    transforms: Vec<FoldTransform>,
}

#[derive(Debug, Clone)]
struct TerminalCompareLink {
    target: u64,
    const_name: String,
    recurrence_is_lhs: bool,
    expr: InvertibleFoldExpr,
}

struct InvertibleRecurrenceParseContext<'a> {
    func: &'a SsaArtifact,
    def_index: BTreeMap<String, &'a SSAOp>,
    recurrence: &'a ExactLoopRecurrenceEvidence,
    visited: HashSet<String>,
}

fn terminal_constraint_for_compare(
    predecessor: u64,
    kind: CompareKind,
    branch_truth: bool,
    recurrence: &ExactLoopRecurrenceEvidence,
    link: &TerminalCompareLink,
) -> Option<FinalConstraint> {
    let exact_reason = || {
        if invertible_expr_is_direct_identity(&link.expr, recurrence.bits, link.target) {
            vec![format!(
                "exact terminal compare links {} to {} at 0x{predecessor:x}",
                recurrence.accumulator, link.const_name
            )]
        } else {
            vec![format!(
                "exact terminal compare links {} to {} at 0x{predecessor:x} via {}",
                recurrence.accumulator,
                link.const_name,
                describe_invertible_expr(&link.expr)
            )]
        }
    };
    match (kind, branch_truth) {
        (CompareKind::Equal, true) | (CompareKind::NotEqual, false) => Some(
            FinalConstraint::RecurrenceEquals(RecurrenceAggregateConstraint {
                recurrence: recurrence.clone(),
                target: invert_invertible_recurrence_equality(
                    &link.expr,
                    link.target,
                    recurrence.bits,
                )?,
                bits: recurrence.bits,
                source: FinalConstraintSource::TerminalCompareExact,
                precision: FinalConstraintPrecision::Exact,
                reasons: exact_reason(),
            }),
        ),
        (CompareKind::Less, truth)
            if invertible_expr_is_direct_identity(&link.expr, recurrence.bits, link.target) =>
        {
            recurrence_range_constraint(
                recurrence,
                if link.recurrence_is_lhs {
                    if truth {
                        FoldRangeRelation::Le(mask_to_bits(
                            link.target.wrapping_sub(1),
                            recurrence.bits,
                        ))
                    } else {
                        FoldRangeRelation::Ge(mask_to_bits(link.target, recurrence.bits))
                    }
                } else if truth {
                    FoldRangeRelation::Ge(mask_to_bits(
                        link.target.saturating_add(1),
                        recurrence.bits,
                    ))
                } else {
                    FoldRangeRelation::Le(mask_to_bits(link.target, recurrence.bits))
                },
                exact_reason(),
            )
        }
        (CompareKind::LessEqual, truth)
            if invertible_expr_is_direct_identity(&link.expr, recurrence.bits, link.target) =>
        {
            recurrence_range_constraint(
                recurrence,
                if link.recurrence_is_lhs {
                    if truth {
                        FoldRangeRelation::Le(mask_to_bits(link.target, recurrence.bits))
                    } else {
                        FoldRangeRelation::Ge(mask_to_bits(
                            link.target.saturating_add(1),
                            recurrence.bits,
                        ))
                    }
                } else if truth {
                    FoldRangeRelation::Ge(mask_to_bits(link.target, recurrence.bits))
                } else {
                    FoldRangeRelation::Le(mask_to_bits(
                        link.target.wrapping_sub(1),
                        recurrence.bits,
                    ))
                },
                exact_reason(),
            )
        }
        _ => None,
    }
}

fn invertible_expr_for_recurrence_operand(
    func: &SsaArtifact,
    def_index: &BTreeMap<String, &SSAOp>,
    var: &SSAVar,
    recurrence: &ExactLoopRecurrenceEvidence,
) -> Option<InvertibleFoldExpr> {
    let bits = var.size.saturating_mul(8).max(1);
    let mut ctx = InvertibleRecurrenceParseContext {
        func,
        def_index: def_index.clone(),
        recurrence,
        visited: HashSet::new(),
    };
    parse_invertible_expr_for_recurrence_operand(&mut ctx, var, bits, 8)
}

fn parse_invertible_expr_for_recurrence_operand(
    ctx: &mut InvertibleRecurrenceParseContext<'_>,
    var: &SSAVar,
    _bits: u32,
    depth: u8,
) -> Option<InvertibleFoldExpr> {
    if depth == 0 {
        return None;
    }
    if var.display_name() == ctx.recurrence.accumulator {
        return Some(InvertibleFoldExpr {
            bits: ctx.recurrence.bits.max(1),
            transforms: Vec::new(),
        });
    }
    let name = var.display_name();
    let op = *ctx.def_index.get(&name)?;
    if !ctx.visited.insert(name.clone()) {
        return None;
    }
    let result = match op {
        SSAOp::Copy { src, dst } | SSAOp::IntZExt { src, dst } => {
            parse_invertible_expr_for_recurrence_operand(
                ctx,
                src,
                dst.size.saturating_mul(8).max(1),
                depth - 1,
            )
        }
        SSAOp::IntAdd { dst, a, b } => {
            parse_invertible_add_like_expr(ctx, a, b, dst.size, depth - 1)
        }
        SSAOp::IntSub { dst, a, b } => {
            parse_invertible_sub_like_expr(ctx, a, b, dst.size, depth - 1)
        }
        SSAOp::IntMult { dst, a, b } => {
            let bits = dst.size.saturating_mul(8).max(1);
            if let Some(scale) = parse_literal_var(a) {
                let inner = parse_invertible_expr_for_recurrence_operand(ctx, b, bits, depth - 1)?;
                Some(push_fold_transform(
                    inner,
                    FoldTransform::Scale(scale),
                    bits,
                ))
            } else if let Some(scale) = parse_literal_var(b) {
                let inner = parse_invertible_expr_for_recurrence_operand(ctx, a, bits, depth - 1)?;
                Some(push_fold_transform(
                    inner,
                    FoldTransform::Scale(scale),
                    bits,
                ))
            } else {
                None
            }
        }
        SSAOp::IntXor { dst, a, b } => {
            parse_invertible_xor_like_expr(ctx, a, b, dst.size, depth - 1)
        }
        SSAOp::IntOr { dst, a, b } => parse_rotate_or_expr(ctx, a, b, dst.size, depth - 1),
        _ => None,
    }
    .or_else(|| {
        ctx.func
            .function()
            .decompile_prep_facts()
            .and_then(|facts| facts.canonical_root_of(var))
            .filter(|root| root.display_name() == ctx.recurrence.accumulator)
            .map(|_| InvertibleFoldExpr {
                bits: ctx.recurrence.bits.max(1),
                transforms: Vec::new(),
            })
    });
    ctx.visited.remove(&name);
    result
}

fn parse_invertible_add_like_expr(
    ctx: &mut InvertibleRecurrenceParseContext<'_>,
    a: &SSAVar,
    b: &SSAVar,
    dst_size: u32,
    depth: u8,
) -> Option<InvertibleFoldExpr> {
    if let Some(constant) = parse_literal_var(a) {
        let inner = parse_invertible_expr_for_recurrence_operand(
            ctx,
            b,
            dst_size.saturating_mul(8).max(1),
            depth,
        )?;
        let bits = inner.bits;
        return Some(push_fold_transform(
            inner,
            FoldTransform::AddConst(constant),
            bits,
        ));
    }
    if let Some(constant) = parse_literal_var(b) {
        let inner = parse_invertible_expr_for_recurrence_operand(
            ctx,
            a,
            dst_size.saturating_mul(8).max(1),
            depth,
        )?;
        let bits = inner.bits;
        return Some(push_fold_transform(
            inner,
            FoldTransform::AddConst(constant),
            bits,
        ));
    }
    None
}

fn parse_invertible_sub_like_expr(
    ctx: &mut InvertibleRecurrenceParseContext<'_>,
    a: &SSAVar,
    b: &SSAVar,
    dst_size: u32,
    depth: u8,
) -> Option<InvertibleFoldExpr> {
    if let Some(constant) = parse_literal_var(b) {
        let inner = parse_invertible_expr_for_recurrence_operand(
            ctx,
            a,
            dst_size.saturating_mul(8).max(1),
            depth,
        )?;
        let bits = inner.bits;
        return Some(push_fold_transform(
            inner,
            FoldTransform::AddConst(mask_to_bits(constant.wrapping_neg(), bits)),
            bits,
        ));
    }
    if let Some(constant) = parse_literal_var(a) {
        let inner = parse_invertible_expr_for_recurrence_operand(
            ctx,
            b,
            dst_size.saturating_mul(8).max(1),
            depth,
        )?;
        let bits = inner.bits;
        let inner = push_fold_transform(
            inner,
            FoldTransform::Scale(mask_to_bits(u64::MAX, bits)),
            bits,
        );
        return Some(push_fold_transform(
            inner,
            FoldTransform::AddConst(constant),
            bits,
        ));
    }
    None
}

fn parse_invertible_xor_like_expr(
    ctx: &mut InvertibleRecurrenceParseContext<'_>,
    a: &SSAVar,
    b: &SSAVar,
    dst_size: u32,
    depth: u8,
) -> Option<InvertibleFoldExpr> {
    if let Some(constant) = parse_literal_var(a) {
        let inner = parse_invertible_expr_for_recurrence_operand(
            ctx,
            b,
            dst_size.saturating_mul(8).max(1),
            depth,
        )?;
        let bits = inner.bits;
        return Some(push_fold_transform(
            inner,
            FoldTransform::XorConst(constant),
            bits,
        ));
    }
    if let Some(constant) = parse_literal_var(b) {
        let inner = parse_invertible_expr_for_recurrence_operand(
            ctx,
            a,
            dst_size.saturating_mul(8).max(1),
            depth,
        )?;
        let bits = inner.bits;
        return Some(push_fold_transform(
            inner,
            FoldTransform::XorConst(constant),
            bits,
        ));
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RotateDirection {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RotateShiftTerm {
    inner: InvertibleFoldExpr,
    direction: RotateDirection,
    shift: u32,
    bits: u32,
}

fn parse_rotate_or_expr(
    ctx: &mut InvertibleRecurrenceParseContext<'_>,
    a: &SSAVar,
    b: &SSAVar,
    dst_size: u32,
    depth: u8,
) -> Option<InvertibleFoldExpr> {
    let lhs = parse_rotate_shift_term(ctx, a, dst_size.saturating_mul(8).max(1), depth)?;
    let rhs = parse_rotate_shift_term(ctx, b, dst_size.saturating_mul(8).max(1), depth)?;
    if lhs.inner != rhs.inner || lhs.bits != rhs.bits {
        return None;
    }
    let bits = lhs.inner.bits;
    if lhs.shift == 0 || rhs.shift == 0 || lhs.shift.saturating_add(rhs.shift) != bits {
        return None;
    }
    if lhs.direction == RotateDirection::Left && rhs.direction == RotateDirection::Right {
        return Some(push_fold_transform(
            lhs.inner,
            FoldTransform::RotateLeft(lhs.shift),
            bits,
        ));
    }
    if lhs.direction == RotateDirection::Right && rhs.direction == RotateDirection::Left {
        return Some(push_fold_transform(
            lhs.inner,
            FoldTransform::RotateRight(lhs.shift),
            bits,
        ));
    }
    None
}

fn parse_rotate_shift_term(
    ctx: &mut InvertibleRecurrenceParseContext<'_>,
    var: &SSAVar,
    bits: u32,
    depth: u8,
) -> Option<RotateShiftTerm> {
    if depth == 0 {
        return None;
    }
    let op = *ctx.def_index.get(&var.display_name())?;
    match op {
        SSAOp::IntLeft { dst, a, b } => Some(RotateShiftTerm {
            inner: parse_invertible_expr_for_recurrence_operand(
                ctx,
                a,
                dst.size.saturating_mul(8).max(1),
                depth - 1,
            )?,
            direction: RotateDirection::Left,
            shift: normalize_rotate_amount(parse_literal_var(b)? as u32, bits),
            bits: dst.size.saturating_mul(8).max(1),
        }),
        SSAOp::IntRight { dst, a, b } => Some(RotateShiftTerm {
            inner: parse_invertible_expr_for_recurrence_operand(
                ctx,
                a,
                dst.size.saturating_mul(8).max(1),
                depth - 1,
            )?,
            direction: RotateDirection::Right,
            shift: normalize_rotate_amount(parse_literal_var(b)? as u32, bits),
            bits: dst.size.saturating_mul(8).max(1),
        }),
        _ => None,
    }
}

fn build_ssa_def_index(func: &SsaArtifact) -> BTreeMap<String, &SSAOp> {
    let mut index = BTreeMap::new();
    for block in func.function().blocks() {
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                index.insert(dst.display_name(), op);
            }
        }
    }
    index
}

fn push_fold_transform(
    mut expr: InvertibleFoldExpr,
    transform: FoldTransform,
    bits: u32,
) -> InvertibleFoldExpr {
    let normalized = match transform {
        FoldTransform::AddConst(value) => FoldTransform::AddConst(mask_to_bits(value, bits)),
        FoldTransform::XorConst(value) => FoldTransform::XorConst(mask_to_bits(value, bits)),
        FoldTransform::Scale(value) => FoldTransform::Scale(mask_to_bits(value, bits)),
        FoldTransform::RotateLeft(value) => {
            FoldTransform::RotateLeft(normalize_rotate_amount(value, bits))
        }
        FoldTransform::RotateRight(value) => {
            FoldTransform::RotateRight(normalize_rotate_amount(value, bits))
        }
    };
    expr.bits = bits;
    expr.transforms.push(normalized);
    expr
}

fn normalize_rotate_amount(amount: u32, bits: u32) -> u32 {
    if bits == 0 { 0 } else { amount % bits.min(64) }
}

fn invertible_expr_is_direct_identity(
    expr: &InvertibleFoldExpr,
    recurrence_bits: u32,
    target: u64,
) -> bool {
    expr.transforms.is_empty()
        && target <= max_value_for_bits(recurrence_bits)
        && expr.bits >= recurrence_bits
}

fn invert_invertible_recurrence_equality(
    expr: &InvertibleFoldExpr,
    target: u64,
    recurrence_bits: u32,
) -> Option<u64> {
    let mut solved = mask_to_bits(target, expr.bits);
    for transform in expr.transforms.iter().rev() {
        solved = match transform {
            FoldTransform::AddConst(value) => mask_to_bits(solved.wrapping_sub(*value), expr.bits),
            FoldTransform::XorConst(value) => mask_to_bits(solved ^ *value, expr.bits),
            FoldTransform::Scale(value) => {
                let inverse = modular_inverse_pow2(*value, expr.bits)?;
                mask_to_bits(solved.wrapping_mul(inverse), expr.bits)
            }
            FoldTransform::RotateLeft(amount) => rotate_right_bits(solved, *amount, expr.bits),
            FoldTransform::RotateRight(amount) => rotate_left_bits(solved, *amount, expr.bits),
        };
    }
    (solved <= max_value_for_bits(recurrence_bits)).then_some(mask_to_bits(solved, recurrence_bits))
}

fn describe_invertible_expr(expr: &InvertibleFoldExpr) -> String {
    if expr.transforms.is_empty() {
        return format!("identity(bits={})", expr.bits);
    }
    let parts = expr
        .transforms
        .iter()
        .map(|transform| match transform {
            FoldTransform::AddConst(value) => format!("add_const(0x{value:x})"),
            FoldTransform::XorConst(value) => format!("xor_const(0x{value:x})"),
            FoldTransform::Scale(value) => format!("scale(0x{value:x})"),
            FoldTransform::RotateLeft(amount) => format!("rol({amount})"),
            FoldTransform::RotateRight(amount) => format!("ror({amount})"),
        })
        .collect::<Vec<_>>();
    format!("{}; bits={}", parts.join(" -> "), expr.bits)
}

fn rotate_left_bits(value: u64, amount: u32, bits: u32) -> u64 {
    rotate_bits(value, amount, bits, true)
}

fn rotate_right_bits(value: u64, amount: u32, bits: u32) -> u64 {
    rotate_bits(value, amount, bits, false)
}

fn rotate_bits(value: u64, amount: u32, bits: u32, left: bool) -> u64 {
    let bits = bits.min(64);
    if bits == 0 {
        return 0;
    }
    let value = mask_to_bits(value, bits);
    let amount = normalize_rotate_amount(amount, bits);
    if amount == 0 {
        return value;
    }
    if bits == 64 {
        if left {
            value.rotate_left(amount)
        } else {
            value.rotate_right(amount)
        }
    } else {
        let lhs = if left {
            value.wrapping_shl(amount)
        } else {
            value >> amount
        };
        let rhs = if left {
            value >> (bits - amount)
        } else {
            value.wrapping_shl(bits - amount)
        };
        mask_to_bits(lhs | rhs, bits)
    }
}

fn modular_inverse_pow2(value: u64, bits: u32) -> Option<u64> {
    if bits == 0 {
        return None;
    }
    if value & 1 == 0 {
        return None;
    }
    let modulus = 1i128.checked_shl(bits.min(64))?;
    let value = (mask_to_bits(value, bits)) as i128;
    let (gcd, x, _) = extended_gcd_i128(value, modulus);
    if gcd != 1 {
        return None;
    }
    let inverse = ((x % modulus) + modulus) % modulus;
    Some(mask_to_bits(inverse as u64, bits))
}

fn extended_gcd_i128(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (gcd, x, y) = extended_gcd_i128(b, a.rem_euclid(b));
        (gcd, y, x - (a / b) * y)
    }
}

#[derive(Clone, Copy)]
enum FoldRangeRelation {
    Ge(u64),
    Le(u64),
}

fn recurrence_range_constraint(
    recurrence: &ExactLoopRecurrenceEvidence,
    relation: FoldRangeRelation,
    reasons: Vec<String>,
) -> Option<FinalConstraint> {
    let max_value = max_value_for_bits(recurrence.bits);
    let (min, max) = match relation {
        FoldRangeRelation::Ge(min) if min <= max_value => (min, max_value),
        FoldRangeRelation::Le(max) => (0, max.min(max_value)),
        _ => return None,
    };
    if min > max {
        return None;
    }
    Some(FinalConstraint::RecurrenceRange(
        RecurrenceAggregateRangeConstraint {
            recurrence: recurrence.clone(),
            min,
            max,
            bits: recurrence.bits,
            source: FinalConstraintSource::TerminalCompareExact,
            precision: FinalConstraintPrecision::Exact,
            reasons,
        },
    ))
}

fn extract_input_constraints_for_path<'ctx>(
    func: &SsaArtifact,
    path: &PathResult<'ctx>,
    folds: &[ExactLoopFoldEvidence],
) -> FinalConstraintGraph {
    let mut graph = FinalConstraintGraph::default();
    let interesting_ranges = folds
        .iter()
        .filter_map(|fold| {
            let (Some(base), Some(stride)) = (fold.term.base, fold.term.stride) else {
                return None;
            };
            Some((
                base,
                fold.iterations,
                stride,
                fold.term.region.as_deref(),
                fold.term.region_base,
            ))
        })
        .collect::<Vec<_>>();

    for assumption in func.facts().assumptions.iter() {
        let AssumptionSubject::MemoryWindow { addr, size } = assumption.subject else {
            continue;
        };
        if !interesting_ranges
            .iter()
            .any(|(base, iterations, stride, region, region_base)| {
                memory_window_overlaps_fold(
                    addr,
                    size,
                    *base,
                    *iterations,
                    *stride,
                    *region,
                    *region_base,
                )
            })
        {
            continue;
        }
        let Some(region) = path
            .state
            .symbolic_memory()
            .iter()
            .find(|region| memory_window_within_region(addr, size, region.addr, region.size))
        else {
            push_unique(
                &mut graph.refusals,
                format!("input_assumption_missing_region:0x{addr:x}/{size}"),
            );
            continue;
        };
        graph.merge(memory_window_constraints_from_assumption(
            addr,
            size,
            region.addr,
            region.size,
            &assumption.value,
        ));
    }

    for region in path.state.symbolic_memory() {
        graph.input_length_constraints.push(InputLengthConstraint {
            base_addr: region.addr,
            len: region.size,
            precision: FinalConstraintPrecision::Exact,
            source: FinalConstraintSource::MemoryWindowAssumption,
            reasons: vec![format!(
                "symbolic input region length {} @ 0x{:x}",
                region.size, region.addr
            )],
        });
    }

    graph
}

fn memory_window_constraints_from_assumption(
    addr: u64,
    size: u32,
    region_addr: u64,
    region_size: u32,
    value: &AssumptionValue,
) -> FinalConstraintGraph {
    let mut graph = FinalConstraintGraph::default();
    match value {
        AssumptionValue::Constant { value } if size <= 8 => {
            for index in 0..size {
                let byte = ((value >> (index * 8)) & 0xff) as u8;
                graph.input_byte_constraints.push(InputByteConstraint {
                    addr: addr + index as u64,
                    allowed: vec![byte],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: vec![format!(
                        "memory-window constant assumption at 0x{:x}",
                        addr + index as u64
                    )],
                });
            }
        }
        AssumptionValue::Range { min, max } if size == 1 && *min <= 0xff && *max <= 0xff => {
            graph.input_byte_constraints.push(InputByteConstraint {
                addr,
                allowed: (*min as u8..=*max as u8).collect(),
                precision: FinalConstraintPrecision::Exact,
                source: FinalConstraintSource::MemoryWindowAssumption,
                reasons: vec![format!("memory-window range assumption at 0x{addr:x}")],
            });
        }
        AssumptionValue::FiniteSet { values } if size == 1 => {
            let allowed = values
                .iter()
                .copied()
                .filter(|value| *value <= 0xff)
                .map(|value| value as u8)
                .collect::<Vec<_>>();
            if !allowed.is_empty() {
                graph.input_byte_constraints.push(InputByteConstraint {
                    addr,
                    allowed,
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: vec![format!("memory-window finite-set assumption at 0x{addr:x}")],
                });
            }
        }
        AssumptionValue::EnumDomain { values, .. } if size == 1 => {
            let allowed = values
                .iter()
                .copied()
                .filter(|value| *value >= 0 && *value <= 0xff)
                .map(|value| value as u8)
                .collect::<Vec<_>>();
            if !allowed.is_empty() {
                graph.input_byte_constraints.push(InputByteConstraint {
                    addr,
                    allowed,
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: vec![format!("memory-window enum assumption at 0x{addr:x}")],
                });
            }
        }
        _ => {
            push_unique(
                &mut graph.refusals,
                format!("input_assumption_unsupported:0x{addr:x}/{size}"),
            );
        }
    }
    if memory_window_within_region(addr, size, region_addr, region_size) {
        graph.input_length_constraints.push(InputLengthConstraint {
            base_addr: region_addr,
            len: region_size,
            precision: FinalConstraintPrecision::Exact,
            source: FinalConstraintSource::MemoryWindowAssumption,
            reasons: vec![format!(
                "memory-window assumption applies within region @ 0x{region_addr:x}"
            )],
        });
    }
    graph
}

fn memory_window_overlaps_fold(
    addr: u64,
    size: u32,
    base: u64,
    iterations: u64,
    stride: u64,
    region: Option<&str>,
    region_base: Option<u64>,
) -> bool {
    if stride == 0 {
        return false;
    }
    let Some(end) = addr.checked_add(size as u64) else {
        return false;
    };
    let Some(fold_end) = base.checked_add(iterations.saturating_mul(stride)) else {
        return false;
    };
    if addr < fold_end && end > base {
        return true;
    }
    region.is_some() && region_base == Some(base)
}

fn memory_window_within_region(addr: u64, size: u32, region_addr: u64, region_size: u32) -> bool {
    let Some(region_end) = region_addr.checked_add(region_size as u64) else {
        return false;
    };
    let Some(end) = addr.checked_add(size as u64) else {
        return false;
    };
    addr >= region_addr && end <= region_end
}

fn parse_literal_var(var: &SSAVar) -> Option<u64> {
    parse_literal_value_name(&var.name)
}

fn parse_literal_value_name(name: &str) -> Option<u64> {
    let value_str = if let Some(value) = name.strip_prefix("const:") {
        value
    } else if let Some(value) = name.strip_prefix("ram:") {
        value
    } else {
        return None;
    };
    let value_str = value_str.split('_').next().unwrap_or(value_str);
    if let Some(dec) = value_str
        .strip_prefix("0d")
        .or_else(|| value_str.strip_prefix("0D"))
    {
        return dec.parse().ok();
    }
    if let Some(hex) = value_str
        .strip_prefix("0x")
        .or_else(|| value_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }
    u64::from_str_radix(value_str, 16)
        .ok()
        .or_else(|| value_str.parse().ok())
}

fn mask_to_bits(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else if bits == 0 {
        0
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn max_value_for_bits(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else if bits == 0 {
        0
    } else {
        (1u64 << bits) - 1
    }
}

fn push_unique(reasons: &mut Vec<String>, reason: impl Into<String>) {
    let reason = reason.into();
    if !reasons.iter().any(|existing| existing == &reason) {
        reasons.push(reason);
    }
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        AnalysisAssumption, AssumptionScope, AssumptionSet, AssumptionSubject, AssumptionValue,
        SsaArtifact,
    };
    use z3::Context;

    use super::{
        FinalConstraint, FinalConstraintSource, InputByteConstraint, aggregate_exact_fold_bytes,
        build_exact_fold_constraint_graph, build_final_constraint_graph_for_path,
    };
    use crate::{
        ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, ExactLoopRecurrenceKind,
        LoopFoldOperation, LoopMemoryTerm, LoopMemoryTermKind, LoopRotateDirection, PathResult,
        SymSolver, SymState, SymValue,
    };

    const RAX: u64 = 0;
    const RCX: u64 = 16;
    const RDX: u64 = 24;
    const RSI: u64 = 32;

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(val: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size,
            meta: None,
        }
    }

    fn make_x86_64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", RAX, 8));
        arch.add_register(RegisterDef::new("RCX", RCX, 8));
        arch.add_register(RegisterDef::new("RDX", RDX, 8));
        arch.add_register(RegisterDef::new("RSI", RSI, 8));
        arch
    }

    fn input_fold(
        operation: LoopFoldOperation,
        bits: u32,
        iterations: u64,
    ) -> ExactLoopFoldEvidence {
        ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations,
            accumulator: "ACC_2".to_string(),
            bits,
            operation,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "PTR_1".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(iterations),
            },
        }
    }

    #[test]
    fn aggregate_exact_fold_bytes_masks_to_width() {
        let fold = input_fold(LoopFoldOperation::Add, 8, 3);
        assert_eq!(aggregate_exact_fold_bytes(&fold, &[200, 100, 10]), Some(54));

        let fold = input_fold(LoopFoldOperation::Xor, 8, 3);
        assert_eq!(
            aggregate_exact_fold_bytes(&fold, &[0xaa, 0x55, 0xff]),
            Some(0)
        );
    }

    #[test]
    fn constraint_graph_derives_input_fold_target_from_selected_model() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic_memory(0x7000, 3, "argv1");
        let fold = input_fold(LoopFoldOperation::Add, 16, 3);
        for (offset, byte) in [10u64, 20, 30].into_iter().enumerate() {
            let value = state.mem_read(&crate::SymValue::concrete(0x7000 + offset as u64, 64), 1);
            state.constrain_eq(&value, byte);
        }
        let solver = SymSolver::new(&ctx);
        let model = solver.solve(&state).expect("model");
        let graph = build_exact_fold_constraint_graph(&state, &[fold], &model);
        assert!(graph.refusals.is_empty());
        assert_eq!(graph.constraints.len(), 1);
        match &graph.constraints[0] {
            FinalConstraint::RecurrenceEquals(constraint) => {
                assert_eq!(constraint.target, 60);
                assert_eq!(constraint.bits, 16);
            }
            FinalConstraint::RecurrenceRange(_) => panic!("unexpected range constraint"),
        }
    }

    #[test]
    fn final_constraint_graph_extracts_exact_terminal_compare_for_fold_accumulator() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::IntEqual {
                        dst: make_reg(RCX, 1),
                        a: make_reg(RAX, 8),
                        b: make_const(0x55, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(RCX, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("function");
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x1010,
            iterations: 1,
            accumulator: "RAX_0".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_0".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(1),
            },
        };

        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        state.set_register("RAX_0", SymValue::concrete(0x55, 64));
        let path = PathResult::new(state, true);
        let recurrences = vec![ExactLoopRecurrenceEvidence::from(fold)];
        let graph = build_final_constraint_graph_for_path(&func, &path, &recurrences, 0x1010, None);
        assert!(graph.refusals.is_empty(), "{:?}", graph.refusals);
        assert_eq!(graph.exact_constraint_count(), 1);
        match &graph.constraints[0] {
            FinalConstraint::RecurrenceEquals(constraint) => {
                assert_eq!(constraint.target, 0x55);
                assert_eq!(
                    constraint.source,
                    FinalConstraintSource::TerminalCompareExact
                );
                assert_eq!(constraint.precision, super::FinalConstraintPrecision::Exact);
            }
            FinalConstraint::RecurrenceRange(_) => panic!("unexpected range constraint"),
        }
    }

    #[test]
    fn final_constraint_graph_extracts_terminal_range_compare_for_fold_accumulator() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::IntLess {
                        dst: make_reg(RCX, 1),
                        a: make_reg(RAX, 8),
                        b: make_const(0x40, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(RCX, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("function");
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x1010,
            iterations: 1,
            accumulator: "RAX_0".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_0".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(1),
            },
        };

        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        let path = PathResult::new(state, true);
        let recurrences = vec![ExactLoopRecurrenceEvidence::from(fold)];
        let graph = build_final_constraint_graph_for_path(&func, &path, &recurrences, 0x1010, None);
        assert!(graph.refusals.is_empty(), "{:?}", graph.refusals);
        assert_eq!(graph.exact_constraint_count(), 1);
        match &graph.constraints[0] {
            FinalConstraint::RecurrenceRange(constraint) => {
                assert_eq!(constraint.min, 0);
                assert_eq!(constraint.max, 0x3f);
            }
            FinalConstraint::RecurrenceEquals(_) => panic!("unexpected equality constraint"),
        }
    }

    #[test]
    fn final_constraint_graph_inverts_affine_terminal_compare_for_fold_accumulator() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::IntMult {
                        dst: make_reg(RCX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(3, 8),
                    },
                    R2ILOp::IntAdd {
                        dst: make_reg(RCX, 8),
                        a: make_reg(RCX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::IntEqual {
                        dst: make_reg(RCX, 1),
                        a: make_reg(RCX, 8),
                        b: make_const(0x10, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(RCX, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("function");
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x1010,
            iterations: 1,
            accumulator: "RAX_0".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_0".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(1),
            },
        };

        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        let path = PathResult::new(state, true);
        let recurrences = vec![ExactLoopRecurrenceEvidence::from(fold)];
        let graph = build_final_constraint_graph_for_path(&func, &path, &recurrences, 0x1010, None);
        assert!(graph.refusals.is_empty(), "{:?}", graph.refusals);
        assert_eq!(graph.exact_constraint_count(), 1);
        match &graph.constraints[0] {
            FinalConstraint::RecurrenceEquals(constraint) => {
                assert_eq!(constraint.target, 5);
                assert_eq!(
                    constraint.source,
                    FinalConstraintSource::TerminalCompareExact
                );
                assert_eq!(constraint.precision, super::FinalConstraintPrecision::Exact);
            }
            FinalConstraint::RecurrenceRange(_) => panic!("unexpected range constraint"),
        }
    }

    #[test]
    fn final_constraint_graph_inverts_rotate_xor_terminal_compare_for_fold_accumulator() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 6,
                ops: vec![
                    R2ILOp::IntLeft {
                        dst: make_reg(RDX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(3, 8),
                    },
                    R2ILOp::IntRight {
                        dst: make_reg(RSI, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(5, 8),
                    },
                    R2ILOp::IntOr {
                        dst: make_reg(RCX, 8),
                        a: make_reg(RDX, 8),
                        b: make_reg(RSI, 8),
                    },
                    R2ILOp::IntXor {
                        dst: make_reg(RCX, 8),
                        a: make_reg(RCX, 8),
                        b: make_const(0x55, 8),
                    },
                    R2ILOp::IntEqual {
                        dst: make_reg(RDX, 1),
                        a: make_reg(RCX, 8),
                        b: make_const(0x78, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(RDX, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("function");
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x1010,
            iterations: 1,
            accumulator: "RAX_0".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_0".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(1),
            },
        };

        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        let path = PathResult::new(state, true);
        let recurrences = vec![ExactLoopRecurrenceEvidence::from(fold)];
        let graph = build_final_constraint_graph_for_path(&func, &path, &recurrences, 0x1010, None);
        assert!(graph.refusals.is_empty(), "{:?}", graph.refusals);
        assert_eq!(graph.exact_constraint_count(), 1);
        match &graph.constraints[0] {
            FinalConstraint::RecurrenceEquals(constraint) => {
                assert_eq!(constraint.target, 0xa5);
                assert_eq!(constraint.precision, super::FinalConstraintPrecision::Exact);
            }
            FinalConstraint::RecurrenceRange(_) => panic!("unexpected range constraint"),
        }
    }

    #[test]
    fn final_constraint_graph_links_direct_terminal_compare_to_exact_rotate_recurrence() {
        let ctx = Context::thread_local();
        let arch = make_x86_64_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 2,
                ops: vec![
                    R2ILOp::IntEqual {
                        dst: make_reg(RCX, 1),
                        a: make_reg(RAX, 8),
                        b: make_const(0x42, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(RCX, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("function");
        let recurrence = ExactLoopRecurrenceEvidence {
            header: 0x1000,
            exit_target: 0x1010,
            iterations: 4,
            accumulator: "RAX_0".to_string(),
            initial: "RAX_1".to_string(),
            bits: 8,
            kind: ExactLoopRecurrenceKind::RotateMix {
                direction: LoopRotateDirection::Left,
                amount: 3,
                operation: LoopFoldOperation::Xor,
                term: LoopMemoryTerm {
                    kind: LoopMemoryTermKind::InputRead,
                    addr: "RDI_0".to_string(),
                    bytes: 1,
                    base: Some(0x7000),
                    stride: Some(1),
                    region: Some("argv1".to_string()),
                    region_base: Some(0x7000),
                    region_size: Some(4),
                },
            },
        };

        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        let path = PathResult::new(state, true);
        let graph = build_final_constraint_graph_for_path(
            &func,
            &path,
            std::slice::from_ref(&recurrence),
            0x1010,
            None,
        );
        assert!(graph.refusals.is_empty(), "{:?}", graph.refusals);
        assert_eq!(graph.exact_constraint_count(), 1);
        match &graph.constraints[0] {
            FinalConstraint::RecurrenceEquals(constraint) => {
                assert_eq!(constraint.target, 0x42);
                assert_eq!(constraint.recurrence, recurrence);
                assert_eq!(constraint.precision, super::FinalConstraintPrecision::Exact);
            }
            FinalConstraint::RecurrenceRange(_) => panic!("unexpected range constraint"),
        }
    }

    #[test]
    fn final_constraint_graph_extracts_memory_window_byte_constraints() {
        let ctx = Context::thread_local();
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, None)
            .expect("function")
            .with_assumptions(&AssumptionSet::new(vec![AnalysisAssumption {
                id: Some("argv-byte".to_string()),
                subject: AssumptionSubject::MemoryWindow {
                    addr: 0x7001,
                    size: 1,
                },
                value: AssumptionValue::FiniteSet {
                    values: vec![b'A' as u64, b'B' as u64],
                },
                scope: AssumptionScope::Query,
                provenance: Default::default(),
            }]));
        let fold = input_fold(LoopFoldOperation::Xor, 8, 3);
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic_memory(0x7000, 3, "argv1");
        let path = PathResult::new(state, true);
        let recurrences = vec![ExactLoopRecurrenceEvidence::from(fold)];
        let graph = build_final_constraint_graph_for_path(&func, &path, &recurrences, 0x1000, None);
        assert!(graph.constraints.is_empty());
        assert!(
            graph
                .input_length_constraints
                .iter()
                .any(|constraint| constraint.base_addr == 0x7000 && constraint.len == 3)
        );
        assert!(
            graph
                .input_byte_constraints
                .iter()
                .any(|constraint: &InputByteConstraint| {
                    constraint.addr == 0x7001 && constraint.allowed == vec![b'A', b'B']
                })
        );
    }
}
