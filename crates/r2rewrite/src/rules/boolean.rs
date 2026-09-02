//! Group D: boolean and comparison normal form.
//!
//! Negations move into the comparison, a comparison of a difference against
//! zero becomes a comparison of its operands, a Bool-typed value compared to
//! a literal is the value or its negation, and a select of the two boolean
//! literals is a widening of its condition.

use r2ssa::{
    MachineArithmeticOp, MachineBitwiseOp, MachineCastKind, MachineComparisonOp, MachineSignedness,
};

use super::identity::bool_term;
use super::literal::{boolean, lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup, literal_like, literal_of};
use crate::term::{TermArena, TermId, TermKind};

macro_rules! boolean_rule {
    ($name:ident, $id:literal, $decreases:expr, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Boolean,
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

fn not_of_compare(
    arena: &TermArena,
    id: TermId,
    op: MachineComparisonOp,
) -> Option<(MachineSignedness, TermId, TermId)> {
    match arena.term(id).kind {
        TermKind::BooleanNot(inner) => match arena.term(inner).kind {
            TermKind::Compare {
                op: actual,
                interpretation,
                left,
                right,
            } if actual == op && arena.term(inner).width_bits() == arena.term(id).width_bits() => {
                Some((interpretation, left, right))
            }
            _ => None,
        },
        _ => None,
    }
}

fn negated(
    arena: &mut TermArena,
    id: TermId,
    op: MachineComparisonOp,
    negated: MachineComparisonOp,
    swap: bool,
) -> Option<TermId> {
    let (interpretation, left, right) = not_of_compare(arena, id, op)?;
    let ty = arena.term(id).ty;
    let (left, right) = if swap { (right, left) } else { (left, right) };
    Some(arena.intern(
        ty,
        TermKind::Compare {
            op: negated,
            interpretation,
            left,
            right,
        },
    ))
}

fn not_template(
    op: MachineComparisonOp,
    interpretation: MachineSignedness,
) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, _, l| {
        let inner = compare(arena, op, interpretation, l[0], l[1]);
        arena.intern(boolean(8), TermKind::BooleanNot(inner))
    }
}

boolean_rule!(
    NOT_EQ,
    "boolean.not_eq",
    Measure::NonLeafNodes,
    |arena, id| negated(
        arena,
        id,
        MachineComparisonOp::Equal,
        MachineComparisonOp::NotEqual,
        false
    ),
    &[|a, w, l| not_template(MachineComparisonOp::Equal, MachineSignedness::Unsigned)(a, w, l)]
);
boolean_rule!(
    NOT_NE,
    "boolean.not_ne",
    Measure::NonLeafNodes,
    |arena, id| negated(
        arena,
        id,
        MachineComparisonOp::NotEqual,
        MachineComparisonOp::Equal,
        false
    ),
    &[|a, w, l| not_template(MachineComparisonOp::NotEqual, MachineSignedness::Unsigned)(a, w, l)]
);
boolean_rule!(
    NOT_LT,
    "boolean.not_lt",
    Measure::NonLeafNodes,
    |arena, id| negated(
        arena,
        id,
        MachineComparisonOp::LessThan,
        MachineComparisonOp::LessThanOrEqual,
        true
    ),
    &[
        |a, w, l| not_template(MachineComparisonOp::LessThan, MachineSignedness::Unsigned)(a, w, l),
        |a, w, l| not_template(MachineComparisonOp::LessThan, MachineSignedness::Signed)(a, w, l),
    ]
);
boolean_rule!(
    NOT_LE,
    "boolean.not_le",
    Measure::NonLeafNodes,
    |arena, id| negated(
        arena,
        id,
        MachineComparisonOp::LessThanOrEqual,
        MachineComparisonOp::LessThan,
        true
    ),
    &[
        |a, w, l| not_template(
            MachineComparisonOp::LessThanOrEqual,
            MachineSignedness::Unsigned
        )(a, w, l),
        |a, w, l| not_template(
            MachineComparisonOp::LessThanOrEqual,
            MachineSignedness::Signed
        )(a, w, l),
    ]
);

fn compare_self(arena: &TermArena, id: TermId, op: MachineComparisonOp) -> bool {
    matches!(arena.term(id).kind, TermKind::Compare { op: actual, left, right, .. } if actual == op && left == right)
}

boolean_rule!(
    EQ_SELF,
    "boolean.eq_self",
    Measure::NonLeafNodes,
    |arena, id| compare_self(arena, id, MachineComparisonOp::Equal)
        .then(|| literal_like(arena, id, 1)),
    &[|arena, _, l| compare(
        arena,
        MachineComparisonOp::Equal,
        MachineSignedness::Unsigned,
        l[0],
        l[0]
    )]
);
boolean_rule!(
    LT_SELF,
    "boolean.lt_self",
    Measure::NonLeafNodes,
    |arena, id| compare_self(arena, id, MachineComparisonOp::LessThan)
        .then(|| literal_like(arena, id, 0)),
    &[
        |arena, _, l| compare(
            arena,
            MachineComparisonOp::LessThan,
            MachineSignedness::Unsigned,
            l[0],
            l[0]
        ),
        |arena, _, l| compare(
            arena,
            MachineComparisonOp::LessThan,
            MachineSignedness::Signed,
            l[0],
            l[0]
        ),
    ]
);
boolean_rule!(
    LE_SELF,
    "boolean.le_self",
    Measure::NonLeafNodes,
    |arena, id| compare_self(arena, id, MachineComparisonOp::LessThanOrEqual)
        .then(|| literal_like(arena, id, 1)),
    &[
        |arena, _, l| compare(
            arena,
            MachineComparisonOp::LessThanOrEqual,
            MachineSignedness::Unsigned,
            l[0],
            l[0]
        ),
        |arena, _, l| compare(
            arena,
            MachineComparisonOp::LessThanOrEqual,
            MachineSignedness::Signed,
            l[0],
            l[0]
        ),
    ]
);

/// `Compare(op, X, 0)` where `X` is `left OP right` for the given operator.
fn difference_against_zero(
    arena: &TermArena,
    id: TermId,
    op: MachineComparisonOp,
    arithmetic: bool,
) -> Option<(TermId, TermId)> {
    match arena.term(id).kind {
        TermKind::Compare {
            op: actual,
            left,
            right,
            ..
        } if actual == op && literal_of(arena, right) == Some(0) => match arena.term(left).kind {
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Subtract,
                left: a,
                right: b,
            } if arithmetic => Some((a, b)),
            TermKind::Bitwise {
                op: MachineBitwiseOp::Xor,
                left: a,
                right: b,
            } if !arithmetic => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

fn zero_compare_template(
    op: MachineComparisonOp,
    arithmetic: bool,
) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, w, l| {
        let inner = if arithmetic {
            arena.intern(
                unsigned(w),
                TermKind::Arithmetic {
                    op: MachineArithmeticOp::Subtract,
                    left: l[0],
                    right: l[1],
                },
            )
        } else {
            arena.intern(
                unsigned(w),
                TermKind::Bitwise {
                    op: MachineBitwiseOp::Xor,
                    left: l[0],
                    right: l[1],
                },
            )
        };
        let zero = lit(arena, w, 0);
        compare(arena, op, MachineSignedness::Unsigned, inner, zero)
    }
}

boolean_rule!(
    SUB_EQ_ZERO,
    "boolean.sub_eq_zero",
    Measure::NonLeafNodes,
    |arena, id| {
        let (a, b) = difference_against_zero(arena, id, MachineComparisonOp::Equal, true)?;
        let ty = arena.term(id).ty;
        Some(arena.intern(
            ty,
            TermKind::Compare {
                op: MachineComparisonOp::Equal,
                interpretation: MachineSignedness::Unsigned,
                left: a,
                right: b,
            },
        ))
    },
    &[|a, w, l| zero_compare_template(MachineComparisonOp::Equal, true)(a, w, l)]
);
boolean_rule!(
    SUB_NE_ZERO,
    "boolean.sub_ne_zero",
    Measure::NonLeafNodes,
    |arena, id| {
        let (a, b) = difference_against_zero(arena, id, MachineComparisonOp::NotEqual, true)?;
        let ty = arena.term(id).ty;
        Some(arena.intern(
            ty,
            TermKind::Compare {
                op: MachineComparisonOp::NotEqual,
                interpretation: MachineSignedness::Unsigned,
                left: a,
                right: b,
            },
        ))
    },
    &[|a, w, l| zero_compare_template(MachineComparisonOp::NotEqual, true)(a, w, l)]
);
boolean_rule!(
    XOR_EQ_ZERO,
    "boolean.xor_eq_zero",
    Measure::NonLeafNodes,
    |arena, id| {
        let (a, b) = difference_against_zero(arena, id, MachineComparisonOp::Equal, false)?;
        let ty = arena.term(id).ty;
        Some(arena.intern(
            ty,
            TermKind::Compare {
                op: MachineComparisonOp::Equal,
                interpretation: MachineSignedness::Unsigned,
                left: a,
                right: b,
            },
        ))
    },
    &[|a, w, l| zero_compare_template(MachineComparisonOp::Equal, false)(a, w, l)]
);

/// `Compare(op, b, literal)` where `b` is Bool-typed.
fn bool_against_literal(
    arena: &TermArena,
    id: TermId,
    op: MachineComparisonOp,
    value: u64,
) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Compare {
            op: actual,
            left,
            right,
            ..
        } if actual == op
            && literal_of(arena, right) == Some(value)
            && arena.term(left).is_bool() =>
        {
            Some(left)
        }
        _ => None,
    }
}

fn bool_literal_template(
    op: MachineComparisonOp,
    value: u64,
) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, _, l| {
        let b = bool_term(arena, l);
        let literal = lit(arena, 8, value);
        compare(arena, op, MachineSignedness::Unsigned, b, literal)
    }
}

/// A term with the same bits as `b` at the type of `like`: `b` itself when
/// the widths agree, which they do for every producer the machine has.
fn retyped(arena: &mut TermArena, like: TermId, b: TermId) -> Option<TermId> {
    (arena.term(like).width_bits() == arena.term(b).width_bits()).then_some(b)
}

boolean_rule!(
    BOOL_EQ_ZERO,
    "boolean.bool_eq_zero",
    Measure::Selections,
    |arena, id| {
        let b = bool_against_literal(arena, id, MachineComparisonOp::Equal, 0)?;
        let ty = arena.term(id).ty;
        (arena.term(id).width_bits() == arena.term(b).width_bits())
            .then(|| arena.intern(ty, TermKind::BooleanNot(b)))
    },
    &[|a, w, l| bool_literal_template(MachineComparisonOp::Equal, 0)(a, w, l)]
);
boolean_rule!(
    BOOL_NE_ZERO,
    "boolean.bool_ne_zero",
    Measure::NonLeafNodes,
    |arena, id| {
        let b = bool_against_literal(arena, id, MachineComparisonOp::NotEqual, 0)?;
        retyped(arena, id, b)
    },
    &[|a, w, l| bool_literal_template(MachineComparisonOp::NotEqual, 0)(a, w, l)]
);
boolean_rule!(
    BOOL_EQ_ONE,
    "boolean.bool_eq_one",
    Measure::NonLeafNodes,
    |arena, id| {
        let b = bool_against_literal(arena, id, MachineComparisonOp::Equal, 1)?;
        retyped(arena, id, b)
    },
    &[|a, w, l| bool_literal_template(MachineComparisonOp::Equal, 1)(a, w, l)]
);
boolean_rule!(
    BOOL_NE_ONE,
    "boolean.bool_ne_one",
    Measure::Selections,
    |arena, id| {
        let b = bool_against_literal(arena, id, MachineComparisonOp::NotEqual, 1)?;
        let ty = arena.term(id).ty;
        (arena.term(id).width_bits() == arena.term(b).width_bits())
            .then(|| arena.intern(ty, TermKind::BooleanNot(b)))
    },
    &[|a, w, l| bool_literal_template(MachineComparisonOp::NotEqual, 1)(a, w, l)]
);

boolean_rule!(
    SELECT_SAME,
    "boolean.select_same",
    Measure::NonLeafNodes,
    |arena, id| match arena.term(id).kind {
        TermKind::Select {
            if_true, if_false, ..
        } if if_true == if_false => Some(if_true),
        _ => None,
    },
    &[|arena, w, l| {
        let c = bool_term(arena, &l[1..]);
        arena.intern(
            unsigned(w),
            TermKind::Select {
                condition: c,
                if_true: l[0],
                if_false: l[0],
            },
        )
    }]
);

fn select_of_literals(
    arena: &TermArena,
    id: TermId,
    if_true: u64,
    if_false: u64,
) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Select {
            condition,
            if_true: t,
            if_false: f,
        } if literal_of(arena, t) == Some(if_true)
            && literal_of(arena, f) == Some(if_false)
            && arena.term(condition).is_bool() =>
        {
            Some(condition)
        }
        _ => None,
    }
}

fn select_template(
    if_true: u64,
    if_false: u64,
) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, w, l| {
        let c = bool_term(arena, l);
        let t = lit(arena, w, if_true);
        let f = lit(arena, w, if_false);
        arena.intern(
            unsigned(w),
            TermKind::Select {
                condition: c,
                if_true: t,
                if_false: f,
            },
        )
    }
}

boolean_rule!(
    SELECT_TRUE_FALSE,
    "boolean.select_true_false",
    Measure::Selections,
    |arena, id| {
        let c = select_of_literals(arena, id, 1, 0)?;
        let ty = arena.term(id).ty;
        let (to, from) = (arena.term(id).width_bits(), arena.term(c).width_bits());
        if to == from {
            Some(c)
        } else if to > from {
            Some(arena.intern(
                ty,
                TermKind::Cast {
                    kind: MachineCastKind::ZeroExtend,
                    input: c,
                },
            ))
        } else {
            None
        }
    },
    &[|a, w, l| select_template(1, 0)(a, w, l)]
);
boolean_rule!(
    SELECT_FALSE_TRUE,
    "boolean.select_false_true",
    Measure::Selections,
    |arena, id| {
        let c = select_of_literals(arena, id, 0, 1)?;
        let ty = arena.term(id).ty;
        (arena.term(id).width_bits() == arena.term(c).width_bits())
            .then(|| arena.intern(ty, TermKind::BooleanNot(c)))
    },
    &[|arena, _, l| {
        let c = bool_term(arena, l);
        let t = lit(arena, 8, 0);
        let f = lit(arena, 8, 1);
        arena.intern(
            unsigned(8),
            TermKind::Select {
                condition: c,
                if_true: t,
                if_false: f,
            },
        )
    }]
);
