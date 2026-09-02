//! Group B: identities and absorption.
//!
//! Each rule recognises one shape over a literal or a shared operand and
//! answers the operand or the absorbing constant. The normaliser puts a
//! literal operand on the right, so each rule looks only there.

use r2ssa::{
    MachineArithmeticOp, MachineBitVector, MachineBitwiseOp, MachineBooleanOp, MachineShiftKind,
};

use super::literal::{boolean, lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup};
use crate::canon::literal_bits;
use crate::eval::mask;
use crate::term::{TermArena, TermId, TermKind};

fn is_literal(arena: &TermArena, id: TermId, value: u64) -> bool {
    literal_bits(arena, id) == Some(value)
}

fn all_ones(width: u32) -> u64 {
    mask(width) as u64
}

fn literal_of(arena: &mut TermArena, like: TermId, value: u64) -> TermId {
    let term = arena.term(like);
    let bits = MachineBitVector::new(term.width_bits(), value).expect("term width fits a literal");
    arena.intern(term.ty, TermKind::Literal(bits))
}

macro_rules! identity_rule {
    ($name:ident, $id:literal, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Identity,
            decreases: Measure::NonLeafNodes,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

fn arith_right_literal(
    arena: &TermArena,
    id: TermId,
    op: MachineArithmeticOp,
    value: u64,
) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Arithmetic {
            op: actual,
            left,
            right,
        } if actual == op && is_literal(arena, right, value) => Some(left),
        _ => None,
    }
}

fn bitwise_right_literal(
    arena: &TermArena,
    id: TermId,
    op: MachineBitwiseOp,
    value: u64,
) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Bitwise {
            op: actual,
            left,
            right,
        } if actual == op && is_literal(arena, right, value) => Some(left),
        _ => None,
    }
}

fn same_operands(arena: &TermArena, id: TermId) -> Option<(TermKind, TermId)> {
    let kind = arena.term(id).kind;
    let mut children = kind.children();
    let (Some(left), Some(right)) = (children.next(), children.next()) else {
        return None;
    };
    (left == right).then_some((kind, left))
}

identity_rule!(
    ADD_ZERO,
    "identity.add_zero",
    |arena, id| arith_right_literal(arena, id, MachineArithmeticOp::Add, 0),
    &[|arena, w, l| {
        let z = lit(arena, w, 0);
        arena.intern(
            unsigned(w),
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Add,
                left: l[0],
                right: z,
            },
        )
    }]
);
identity_rule!(
    SUB_ZERO,
    "identity.sub_zero",
    |arena, id| arith_right_literal(arena, id, MachineArithmeticOp::Subtract, 0),
    &[|arena, w, l| {
        let z = lit(arena, w, 0);
        arena.intern(
            unsigned(w),
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Subtract,
                left: l[0],
                right: z,
            },
        )
    }]
);
identity_rule!(
    SUB_SELF,
    "identity.sub_self",
    |arena, id| match same_operands(arena, id)? {
        (
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Subtract,
                ..
            },
            _,
        ) => Some(literal_of(arena, id, 0)),
        _ => None,
    },
    &[|arena, w, l| arena.intern(
        unsigned(w),
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Subtract,
            left: l[0],
            right: l[0]
        }
    )]
);
identity_rule!(
    MUL_ONE,
    "identity.mul_one",
    |arena, id| arith_right_literal(arena, id, MachineArithmeticOp::Multiply, 1),
    &[|arena, w, l| {
        let one = lit(arena, w, 1);
        arena.intern(
            unsigned(w),
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Multiply,
                left: l[0],
                right: one,
            },
        )
    }]
);
identity_rule!(
    MUL_ZERO,
    "identity.mul_zero",
    |arena, id| arith_right_literal(arena, id, MachineArithmeticOp::Multiply, 0)
        .map(|_| literal_of(arena, id, 0)),
    &[|arena, w, l| {
        let z = lit(arena, w, 0);
        arena.intern(
            unsigned(w),
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Multiply,
                left: l[0],
                right: z,
            },
        )
    }]
);
identity_rule!(
    AND_ZERO,
    "identity.and_zero",
    |arena, id| bitwise_right_literal(arena, id, MachineBitwiseOp::And, 0)
        .map(|_| literal_of(arena, id, 0)),
    &[|arena, w, l| {
        let z = lit(arena, w, 0);
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::And,
                left: l[0],
                right: z,
            },
        )
    }]
);
identity_rule!(
    AND_ONES,
    "identity.and_ones",
    |arena, id| {
        let width = arena.term(id).width_bits();
        bitwise_right_literal(arena, id, MachineBitwiseOp::And, all_ones(width))
    },
    &[|arena, w, l| {
        let ones = lit(arena, w, all_ones(w));
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::And,
                left: l[0],
                right: ones,
            },
        )
    }]
);
identity_rule!(
    AND_SELF,
    "identity.and_self",
    |arena, id| match same_operands(arena, id)? {
        (
            TermKind::Bitwise {
                op: MachineBitwiseOp::And,
                ..
            },
            x,
        ) => Some(x),
        _ => None,
    },
    &[|arena, w, l| arena.intern(
        unsigned(w),
        TermKind::Bitwise {
            op: MachineBitwiseOp::And,
            left: l[0],
            right: l[0]
        }
    )]
);
identity_rule!(
    OR_ZERO,
    "identity.or_zero",
    |arena, id| bitwise_right_literal(arena, id, MachineBitwiseOp::Or, 0),
    &[|arena, w, l| {
        let z = lit(arena, w, 0);
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::Or,
                left: l[0],
                right: z,
            },
        )
    }]
);
identity_rule!(
    OR_SELF,
    "identity.or_self",
    |arena, id| match same_operands(arena, id)? {
        (
            TermKind::Bitwise {
                op: MachineBitwiseOp::Or,
                ..
            },
            x,
        ) => Some(x),
        _ => None,
    },
    &[|arena, w, l| arena.intern(
        unsigned(w),
        TermKind::Bitwise {
            op: MachineBitwiseOp::Or,
            left: l[0],
            right: l[0]
        }
    )]
);
identity_rule!(
    OR_ONES,
    "identity.or_ones",
    |arena, id| {
        let width = arena.term(id).width_bits();
        bitwise_right_literal(arena, id, MachineBitwiseOp::Or, all_ones(width))
            .map(|_| literal_of(arena, id, all_ones(width)))
    },
    &[|arena, w, l| {
        let ones = lit(arena, w, all_ones(w));
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::Or,
                left: l[0],
                right: ones,
            },
        )
    }]
);
identity_rule!(
    XOR_ZERO,
    "identity.xor_zero",
    |arena, id| bitwise_right_literal(arena, id, MachineBitwiseOp::Xor, 0),
    &[|arena, w, l| {
        let z = lit(arena, w, 0);
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::Xor,
                left: l[0],
                right: z,
            },
        )
    }]
);
identity_rule!(
    XOR_SELF,
    "identity.xor_self",
    |arena, id| match same_operands(arena, id)? {
        (
            TermKind::Bitwise {
                op: MachineBitwiseOp::Xor,
                ..
            },
            _,
        ) => Some(literal_of(arena, id, 0)),
        _ => None,
    },
    &[|arena, w, l| arena.intern(
        unsigned(w),
        TermKind::Bitwise {
            op: MachineBitwiseOp::Xor,
            left: l[0],
            right: l[0]
        }
    )]
);
identity_rule!(
    NOT_NOT,
    "identity.not_not",
    |arena, id| match arena.term(id).kind {
        TermKind::BitwiseNot(inner) => match arena.term(inner).kind {
            TermKind::BitwiseNot(x)
                if arena.term(x).width_bits() == arena.term(id).width_bits() =>
                Some(x),
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let inner = arena.intern(unsigned(w), TermKind::BitwiseNot(l[0]));
        arena.intern(unsigned(w), TermKind::BitwiseNot(inner))
    }]
);
identity_rule!(
    NEG_NEG,
    "identity.neg_neg",
    |arena, id| match arena.term(id).kind {
        TermKind::Negate(inner) => match arena.term(inner).kind {
            TermKind::Negate(x) if arena.term(x).width_bits() == arena.term(id).width_bits() =>
                Some(x),
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let inner = arena.intern(unsigned(w), TermKind::Negate(l[0]));
        arena.intern(unsigned(w), TermKind::Negate(inner))
    }]
);

fn shift_by_zero(arena: &TermArena, id: TermId, kind: MachineShiftKind) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Shift {
            kind: actual,
            value,
            count,
            ..
        } if actual == kind && is_literal(arena, count, 0) => Some(value),
        _ => None,
    }
}

fn shift_template(kind: MachineShiftKind) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, w, l| {
        let z = lit(arena, 8, 0);
        let overshift = match kind {
            MachineShiftKind::ArithmeticRight => r2ssa::MachineOvershiftBehavior::SignFill,
            _ => r2ssa::MachineOvershiftBehavior::Zero,
        };
        arena.intern(
            unsigned(w),
            TermKind::Shift {
                kind,
                overshift,
                value: l[0],
                count: z,
            },
        )
    }
}

identity_rule!(
    SHL_ZERO,
    "identity.shl_zero",
    |arena, id| shift_by_zero(arena, id, MachineShiftKind::Left),
    &[|a, w, l| shift_template(MachineShiftKind::Left)(a, w, l)]
);
identity_rule!(
    LSHR_ZERO,
    "identity.lshr_zero",
    |arena, id| shift_by_zero(arena, id, MachineShiftKind::LogicalRight),
    &[|a, w, l| shift_template(MachineShiftKind::LogicalRight)(a, w, l)]
);
identity_rule!(
    ASHR_ZERO,
    "identity.ashr_zero",
    |arena, id| shift_by_zero(arena, id, MachineShiftKind::ArithmeticRight),
    &[|a, w, l| shift_template(MachineShiftKind::ArithmeticRight)(a, w, l)]
);

/// A Bool-typed operand: one whose value is 0 or 1 by construction.
fn is_boolean(arena: &TermArena, id: TermId) -> bool {
    arena.term(id).is_bool()
}

/// A Bool-typed term for templates: the comparison of two leaves.
pub(super) fn bool_term(arena: &mut TermArena, l: &[TermId]) -> TermId {
    arena.intern(
        boolean(8),
        TermKind::Compare {
            op: r2ssa::MachineComparisonOp::Equal,
            interpretation: r2ssa::MachineSignedness::Unsigned,
            left: l[0],
            right: l[1],
        },
    )
}

identity_rule!(
    BOOLNOT_BOOLNOT,
    "identity.boolnot_boolnot",
    |arena, id| match arena.term(id).kind {
        TermKind::BooleanNot(inner) => match arena.term(inner).kind {
            TermKind::BooleanNot(b)
                if is_boolean(arena, b)
                    && arena.term(b).width_bits() == arena.term(id).width_bits() =>
                Some(b),
            _ => None,
        },
        _ => None,
    },
    &[|arena, _, l| {
        let b = bool_term(arena, l);
        let inner = arena.intern(boolean(8), TermKind::BooleanNot(b));
        arena.intern(boolean(8), TermKind::BooleanNot(inner))
    }]
);

fn boolean_same(arena: &TermArena, id: TermId, op: MachineBooleanOp) -> Option<TermId> {
    match same_operands(arena, id)? {
        (TermKind::Boolean { op: actual, .. }, b) if actual == op && is_boolean(arena, b) => {
            Some(b)
        }
        _ => None,
    }
}

fn boolean_right_literal(
    arena: &TermArena,
    id: TermId,
    op: MachineBooleanOp,
    value: u64,
) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Boolean {
            op: actual,
            left,
            right,
        } if actual == op && is_literal(arena, right, value) && is_boolean(arena, left) => {
            Some(left)
        }
        _ => None,
    }
}

fn bool_literal(arena: &mut TermArena, value: bool) -> TermId {
    arena.intern(
        boolean(8),
        TermKind::Literal(MachineBitVector::new(8, u64::from(value)).expect("bool literal")),
    )
}

identity_rule!(
    BOOLAND_SELF,
    "identity.booland_self",
    |arena, id| boolean_same(arena, id, MachineBooleanOp::And),
    &[|arena, _, l| {
        let b = bool_term(arena, l);
        arena.intern(
            boolean(8),
            TermKind::Boolean {
                op: MachineBooleanOp::And,
                left: b,
                right: b,
            },
        )
    }]
);
identity_rule!(
    BOOLOR_SELF,
    "identity.boolor_self",
    |arena, id| boolean_same(arena, id, MachineBooleanOp::Or),
    &[|arena, _, l| {
        let b = bool_term(arena, l);
        arena.intern(
            boolean(8),
            TermKind::Boolean {
                op: MachineBooleanOp::Or,
                left: b,
                right: b,
            },
        )
    }]
);
identity_rule!(
    BOOLAND_TRUE,
    "identity.booland_true",
    |arena, id| boolean_right_literal(arena, id, MachineBooleanOp::And, 1),
    &[|arena, _, l| {
        let b = bool_term(arena, l);
        let t = bool_literal(arena, true);
        arena.intern(
            boolean(8),
            TermKind::Boolean {
                op: MachineBooleanOp::And,
                left: b,
                right: t,
            },
        )
    }]
);
identity_rule!(
    BOOLOR_FALSE,
    "identity.boolor_false",
    |arena, id| boolean_right_literal(arena, id, MachineBooleanOp::Or, 0),
    &[|arena, _, l| {
        let b = bool_term(arena, l);
        let f = bool_literal(arena, false);
        arena.intern(
            boolean(8),
            TermKind::Boolean {
                op: MachineBooleanOp::Or,
                left: b,
                right: f,
            },
        )
    }]
);

pub static GROUP: &[&Rule] = &[
    &ADD_ZERO,
    &SUB_ZERO,
    &SUB_SELF,
    &MUL_ONE,
    &MUL_ZERO,
    &AND_ZERO,
    &AND_ONES,
    &AND_SELF,
    &OR_ZERO,
    &OR_SELF,
    &OR_ONES,
    &XOR_ZERO,
    &XOR_SELF,
    &NOT_NOT,
    &NEG_NEG,
    &SHL_ZERO,
    &LSHR_ZERO,
    &ASHR_ZERO,
    &BOOLNOT_BOOLNOT,
    &BOOLAND_SELF,
    &BOOLOR_SELF,
    &BOOLAND_TRUE,
    &BOOLOR_FALSE,
];
