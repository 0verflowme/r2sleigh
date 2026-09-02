//! Group G: the affine lemmas.
//!
//! The affine normal form itself is a normaliser (`canon::affine_normalize`):
//! over a maximal tree of additions, subtractions, negations and
//! multiplications by a literal at one width it collects `sum k_i * t_i + c`
//! modulo `2^w`, merges like terms, drops zero coefficients, and emits the
//! terms in id order with the literal last, subtracting rather than adding a
//! coefficient whose signed reading is negative. It never distributes a
//! literal over a sum, so it never adds a node, and re-collecting its own
//! output emits the same output, so it is idempotent. Its equivalence is
//! checked on a family of shapes in the proof harness.
//!
//! The rules here are the lemmas the normal form rests on that also strictly
//! shrink a term on their own, so they stand as rules with proofs of their
//! own and fire wherever the normaliser has not already taken the shape.

use r2ssa::MachineArithmeticOp;

use super::literal::{lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup, literal_like, literal_of};
use crate::eval::mask;
use crate::term::{TermArena, TermId, TermKind};

macro_rules! affine_rule {
    ($name:ident, $id:literal, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Affine,
            decreases: Measure::NonLeafNodes,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

fn arith(arena: &mut TermArena, op: MachineArithmeticOp, left: TermId, right: TermId) -> TermId {
    let ty = arena.term(left).ty;
    arena.intern(ty, TermKind::Arithmetic { op, left, right })
}

/// `op(op(x, c1), c2)` with literal `c1`, `c2`, combined by `combine` at the
/// term's width.
fn nested_literal(
    arena: &mut TermArena,
    id: TermId,
    op: MachineArithmeticOp,
    combine: fn(u64, u64) -> u64,
) -> Option<TermId> {
    let TermKind::Arithmetic {
        op: outer,
        left,
        right,
    } = arena.term(id).kind
    else {
        return None;
    };
    if outer != op {
        return None;
    }
    let c2 = literal_of(arena, right)?;
    let TermKind::Arithmetic {
        op: inner,
        left: x,
        right: inner_right,
    } = arena.term(left).kind
    else {
        return None;
    };
    if inner != op {
        return None;
    }
    let c1 = literal_of(arena, inner_right)?;
    let width = arena.term(id).width_bits();
    let combined = combine(c1, c2) & (mask(width) as u64);
    let literal = literal_like(arena, id, combined);
    let ty = arena.term(id).ty;
    Some(arena.intern(
        ty,
        TermKind::Arithmetic {
            op,
            left: x,
            right: literal,
        },
    ))
}

fn nested_template(op: MachineArithmeticOp) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, w, l| {
        let c1 = lit(arena, w, 3);
        let c2 = lit(arena, w, 5);
        let _ = unsigned(w);
        let inner = arith(arena, op, l[0], c1);
        arith(arena, op, inner, c2)
    }
}

affine_rule!(
    ADD_ADD_LITERAL,
    "affine.add_add_literal",
    |arena, id| nested_literal(arena, id, MachineArithmeticOp::Add, u64::wrapping_add),
    &[|a, w, l| nested_template(MachineArithmeticOp::Add)(a, w, l)]
);
affine_rule!(
    SUB_SUB_LITERAL,
    "affine.sub_sub_literal",
    |arena, id| nested_literal(arena, id, MachineArithmeticOp::Subtract, u64::wrapping_add),
    &[|a, w, l| nested_template(MachineArithmeticOp::Subtract)(a, w, l)]
);
affine_rule!(
    MUL_MUL_LITERAL,
    "affine.mul_mul_literal",
    |arena, id| nested_literal(arena, id, MachineArithmeticOp::Multiply, u64::wrapping_mul),
    &[|a, w, l| nested_template(MachineArithmeticOp::Multiply)(a, w, l)]
);

affine_rule!(
    ADD_NEG,
    "affine.add_neg",
    |arena, id| match arena.term(id).kind {
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Add,
            left,
            right,
        } => match arena.term(right).kind {
            TermKind::Negate(y) => Some(arith(arena, MachineArithmeticOp::Subtract, left, y)),
            _ => match arena.term(left).kind {
                TermKind::Negate(y) => Some(arith(arena, MachineArithmeticOp::Subtract, right, y)),
                _ => None,
            },
        },
        _ => None,
    },
    &[|arena, w, l| {
        let neg = arena.intern(unsigned(w), TermKind::Negate(l[1]));
        arith(arena, MachineArithmeticOp::Add, l[0], neg)
    }]
);
affine_rule!(
    SUB_NEG,
    "affine.sub_neg",
    |arena, id| match arena.term(id).kind {
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Subtract,
            left,
            right,
        } => match arena.term(right).kind {
            TermKind::Negate(y) => Some(arith(arena, MachineArithmeticOp::Add, left, y)),
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let neg = arena.intern(unsigned(w), TermKind::Negate(l[1]));
        arith(arena, MachineArithmeticOp::Subtract, l[0], neg)
    }]
);
affine_rule!(
    NEG_SUB,
    "affine.neg_sub",
    |arena, id| match arena.term(id).kind {
        TermKind::Negate(inner) => match arena.term(inner).kind {
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Subtract,
                left,
                right,
            } if arena.term(inner).width_bits() == arena.term(id).width_bits() => {
                Some(arith(arena, MachineArithmeticOp::Subtract, right, left))
            }
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let diff = arith(arena, MachineArithmeticOp::Subtract, l[0], l[1]);
        arena.intern(unsigned(w), TermKind::Negate(diff))
    }]
);
