//! Group E: flag arithmetic to comparison.
//!
//! A conditional branch on x86 or arm64 reads condition codes that the
//! lifter spells as their definitions: with `d = a - b`, the sign flag is
//! `d <s 0`, the overflow flag is `sborrow(a, b)`, the zero flag is
//! `d == 0`, and `jl` tests `SF != OF`. These rules state on structure what
//! `crates/r2dec/src/fold/flags.rs` matched on rendered text. Two of them
//! match through a leaf's definition: `d` usually has two readers, the sign
//! flag and the zero flag, so it is read by name rather than expanded, and
//! the rule asks the arena what `d` stands for. The rewritten term then reads
//! `a` and `b` and no longer reads `d`, which is why the measure counts
//! defined leaves.
//!
//! The two remaining shapes are lemmas over comparisons and hold for either
//! signedness: `x <= y && x != y` is `x < y`, and `x == y || x < y` is
//! `x <= y`. The boolean normal form of group D delivers the flag shapes for
//! `jg`, `jle`, `ja`, `jbe`, `b.hi` and `b.ls` into exactly those two.

use r2ssa::{
    MachineArithmeticFlagOp, MachineArithmeticOp, MachineBooleanOp, MachineComparisonOp,
    MachineSignedness,
};

use super::literal::{boolean, lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup};
use crate::term::{TermArena, TermId, TermKind};

macro_rules! flag_rule {
    ($name:ident, $id:literal, $decreases:expr, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Flag,
            decreases: $decreases,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

fn compare(
    arena: &mut TermArena,
    op: MachineComparisonOp,
    interpretation: MachineSignedness,
    left: TermId,
    right: TermId,
) -> TermId {
    arena.intern(
        boolean(8),
        TermKind::Compare {
            op,
            interpretation,
            left,
            right,
        },
    )
}

fn both_bool(arena: &TermArena, p: TermId, q: TermId) -> bool {
    arena.term(p).is_bool() && arena.term(q).is_bool()
}

flag_rule!(
    BOOL_NE_IS_XOR,
    "flag.bool_ne_is_xor",
    Measure::Selections,
    |arena, id| match arena.term(id).kind {
        TermKind::Compare {
            op: MachineComparisonOp::NotEqual,
            left,
            right,
            ..
        } if both_bool(arena, left, right)
            && arena.term(left).width_bits() == arena.term(id).width_bits() =>
        {
            let ty = arena.term(id).ty;
            Some(arena.intern(
                ty,
                TermKind::Boolean {
                    op: MachineBooleanOp::Xor,
                    left,
                    right,
                },
            ))
        }
        _ => None,
    },
    &[|arena, _, l| {
        let p = compare(
            arena,
            MachineComparisonOp::Equal,
            MachineSignedness::Unsigned,
            l[0],
            l[1],
        );
        let q = compare(
            arena,
            MachineComparisonOp::LessThan,
            MachineSignedness::Signed,
            l[0],
            l[2],
        );
        compare(
            arena,
            MachineComparisonOp::NotEqual,
            MachineSignedness::Unsigned,
            p,
            q,
        )
    }]
);

flag_rule!(
    NOT_XOR_IS_EQ,
    "flag.not_xor_is_eq",
    Measure::NonLeafNodes,
    |arena, id| match arena.term(id).kind {
        TermKind::BooleanNot(inner) => match arena.term(inner).kind {
            TermKind::Boolean {
                op: MachineBooleanOp::Xor,
                left,
                right,
            } if both_bool(arena, left, right)
                && arena.term(inner).width_bits() == arena.term(id).width_bits() =>
            {
                let ty = arena.term(id).ty;
                Some(arena.intern(
                    ty,
                    TermKind::Compare {
                        op: MachineComparisonOp::Equal,
                        interpretation: MachineSignedness::Unsigned,
                        left,
                        right,
                    },
                ))
            }
            _ => None,
        },
        _ => None,
    },
    &[|arena, _, l| {
        let p = compare(
            arena,
            MachineComparisonOp::Equal,
            MachineSignedness::Unsigned,
            l[0],
            l[1],
        );
        let q = compare(
            arena,
            MachineComparisonOp::LessThan,
            MachineSignedness::Signed,
            l[0],
            l[2],
        );
        let x = arena.intern(
            boolean(8),
            TermKind::Boolean {
                op: MachineBooleanOp::Xor,
                left: p,
                right: q,
            },
        );
        arena.intern(boolean(8), TermKind::BooleanNot(x))
    }]
);

/// The `(a, b)` of a sign flag `s` and an overflow flag `o` that describe one
/// subtraction: `o` is `sborrow(a, b)` and `s` is `(a - b) <s 0`, where the
/// difference is either written out or a leaf that stands for it.
fn subtraction_flags(arena: &TermArena, s: TermId, o: TermId) -> Option<(TermId, TermId)> {
    let TermKind::Flag {
        op: MachineArithmeticFlagOp::SignedBorrow,
        left: a,
        right: b,
    } = arena.term(o).kind
    else {
        return None;
    };
    let TermKind::Compare {
        op: MachineComparisonOp::LessThan,
        interpretation: MachineSignedness::Signed,
        left: d,
        right: zero,
    } = arena.term(s).kind
    else {
        return None;
    };
    if crate::canon::literal_bits(arena, zero) != Some(0) {
        return None;
    }
    let TermKind::Arithmetic {
        op: MachineArithmeticOp::Subtract,
        left: da,
        right: db,
    } = arena.term(arena.unfold(d)).kind
    else {
        return None;
    };
    (da == a && db == b).then_some((a, b))
}

fn sign_and_overflow(arena: &TermArena, left: TermId, right: TermId) -> Option<(TermId, TermId)> {
    subtraction_flags(arena, left, right).or_else(|| subtraction_flags(arena, right, left))
}

/// Templates for the flag shapes: the difference written out, and the
/// difference as a leaf that stands for it.
fn sign_flag(arena: &mut TermArena, w: u32, a: TermId, b: TermId, through_leaf: bool) -> TermId {
    let difference = arena.intern(
        unsigned(w),
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Subtract,
            left: a,
            right: b,
        },
    );
    let d = if through_leaf {
        let leaf = arena.intern(unsigned(w), TermKind::Variable(9));
        arena.define(leaf, difference);
        leaf
    } else {
        difference
    };
    let zero = lit(arena, w, 0);
    compare(
        arena,
        MachineComparisonOp::LessThan,
        MachineSignedness::Signed,
        d,
        zero,
    )
}

fn overflow_flag(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.intern(
        boolean(8),
        TermKind::Flag {
            op: MachineArithmeticFlagOp::SignedBorrow,
            left: a,
            right: b,
        },
    )
}

flag_rule!(
    SIGNED_LT_FROM_BORROW,
    "flag.signed_lt_from_borrow",
    Measure::NonLeafNodes,
    |arena, id| match arena.term(id).kind {
        TermKind::Boolean {
            op: MachineBooleanOp::Xor,
            left,
            right,
        } => {
            let (a, b) = sign_and_overflow(arena, left, right)?;
            let ty = arena.term(id).ty;
            Some(arena.intern(
                ty,
                TermKind::Compare {
                    op: MachineComparisonOp::LessThan,
                    interpretation: MachineSignedness::Signed,
                    left: a,
                    right: b,
                },
            ))
        }
        _ => None,
    },
    &[
        |arena, w, l| {
            let s = sign_flag(arena, w, l[0], l[1], false);
            let o = overflow_flag(arena, l[0], l[1]);
            arena.intern(
                boolean(8),
                TermKind::Boolean {
                    op: MachineBooleanOp::Xor,
                    left: s,
                    right: o,
                },
            )
        },
        |arena, w, l| {
            let s = sign_flag(arena, w, l[0], l[1], true);
            let o = overflow_flag(arena, l[0], l[1]);
            arena.intern(
                boolean(8),
                TermKind::Boolean {
                    op: MachineBooleanOp::Xor,
                    left: o,
                    right: s,
                },
            )
        },
    ]
);

flag_rule!(
    SIGNED_GE_FROM_BORROW,
    "flag.signed_ge_from_borrow",
    Measure::NonLeafNodes,
    |arena, id| match arena.term(id).kind {
        TermKind::Compare {
            op: MachineComparisonOp::Equal,
            left,
            right,
            ..
        } => {
            let (a, b) = sign_and_overflow(arena, left, right)?;
            let ty = arena.term(id).ty;
            Some(arena.intern(
                ty,
                TermKind::Compare {
                    op: MachineComparisonOp::LessThanOrEqual,
                    interpretation: MachineSignedness::Signed,
                    left: b,
                    right: a,
                },
            ))
        }
        _ => None,
    },
    &[
        |arena, w, l| {
            let s = sign_flag(arena, w, l[0], l[1], false);
            let o = overflow_flag(arena, l[0], l[1]);
            compare(
                arena,
                MachineComparisonOp::Equal,
                MachineSignedness::Unsigned,
                s,
                o,
            )
        },
        |arena, w, l| {
            let s = sign_flag(arena, w, l[0], l[1], true);
            let o = overflow_flag(arena, l[0], l[1]);
            compare(
                arena,
                MachineComparisonOp::Equal,
                MachineSignedness::Unsigned,
                o,
                s,
            )
        },
    ]
);

/// An ordering `x OP y` and an equality over the same two operands in
/// either order, from the two children of a boolean node.
fn ordering_and_equality(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    ordering: MachineComparisonOp,
    equality: MachineComparisonOp,
) -> Option<(MachineSignedness, TermId, TermId)> {
    let pick = |ordered: TermId, equal: TermId| -> Option<(MachineSignedness, TermId, TermId)> {
        let TermKind::Compare {
            op: o,
            interpretation,
            left: x,
            right: y,
        } = arena.term(ordered).kind
        else {
            return None;
        };
        let TermKind::Compare {
            op: e,
            left: p,
            right: q,
            ..
        } = arena.term(equal).kind
        else {
            return None;
        };
        if o != ordering || e != equality {
            return None;
        }
        ((p == x && q == y) || (p == y && q == x)).then_some((interpretation, x, y))
    };
    pick(left, right).or_else(|| pick(right, left))
}

fn lemma_template(
    op: MachineBooleanOp,
    ordering: MachineComparisonOp,
    equality: MachineComparisonOp,
    interpretation: MachineSignedness,
    swap: bool,
) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, _, l| {
        let ordered = compare(arena, ordering, interpretation, l[0], l[1]);
        let equal = if swap {
            compare(arena, equality, MachineSignedness::Unsigned, l[1], l[0])
        } else {
            compare(arena, equality, MachineSignedness::Unsigned, l[0], l[1])
        };
        arena.intern(
            boolean(8),
            TermKind::Boolean {
                op,
                left: ordered,
                right: equal,
            },
        )
    }
}

flag_rule!(
    LE_AND_NE_IS_LT,
    "flag.le_and_ne_is_lt",
    Measure::NonLeafNodes,
    |arena, id| match arena.term(id).kind {
        TermKind::Boolean {
            op: MachineBooleanOp::And,
            left,
            right,
        } => {
            let (interpretation, x, y) = ordering_and_equality(
                arena,
                left,
                right,
                MachineComparisonOp::LessThanOrEqual,
                MachineComparisonOp::NotEqual,
            )?;
            let ty = arena.term(id).ty;
            Some(arena.intern(
                ty,
                TermKind::Compare {
                    op: MachineComparisonOp::LessThan,
                    interpretation,
                    left: x,
                    right: y,
                },
            ))
        }
        _ => None,
    },
    &[
        |a, w, l| lemma_template(
            MachineBooleanOp::And,
            MachineComparisonOp::LessThanOrEqual,
            MachineComparisonOp::NotEqual,
            MachineSignedness::Signed,
            false
        )(a, w, l),
        |a, w, l| lemma_template(
            MachineBooleanOp::And,
            MachineComparisonOp::LessThanOrEqual,
            MachineComparisonOp::NotEqual,
            MachineSignedness::Unsigned,
            true
        )(a, w, l),
    ]
);

flag_rule!(
    EQ_OR_LT_IS_LE,
    "flag.eq_or_lt_is_le",
    Measure::NonLeafNodes,
    |arena, id| match arena.term(id).kind {
        TermKind::Boolean {
            op: MachineBooleanOp::Or,
            left,
            right,
        } => {
            let (interpretation, x, y) = ordering_and_equality(
                arena,
                left,
                right,
                MachineComparisonOp::LessThan,
                MachineComparisonOp::Equal,
            )?;
            let ty = arena.term(id).ty;
            Some(arena.intern(
                ty,
                TermKind::Compare {
                    op: MachineComparisonOp::LessThanOrEqual,
                    interpretation,
                    left: x,
                    right: y,
                },
            ))
        }
        _ => None,
    },
    &[
        |a, w, l| lemma_template(
            MachineBooleanOp::Or,
            MachineComparisonOp::LessThan,
            MachineComparisonOp::Equal,
            MachineSignedness::Signed,
            true
        )(a, w, l),
        |a, w, l| lemma_template(
            MachineBooleanOp::Or,
            MachineComparisonOp::LessThan,
            MachineComparisonOp::Equal,
            MachineSignedness::Unsigned,
            false
        )(a, w, l),
    ]
);
