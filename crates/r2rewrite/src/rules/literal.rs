//! Group A: folding over literals.
//!
//! One rewrite serves every operation: when every child of a term is a
//! literal, the term is the literal the evaluator computes, at the term's own
//! type and width. The proof harness proves the evaluator against the Z3
//! encoding for each shape, so each operation has its own rule id and its own
//! templates even though they share one body.

use r2ssa::{
    MachineArithmeticFlagOp, MachineArithmeticOp, MachineBitVector, MachineBitwiseOp,
    MachineBooleanOp, MachineCastKind, MachineComparisonOp, MachineOvershiftBehavior,
    MachineShiftKind, MachineSignedness,
};

use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup, Template};
use crate::eval::eval;
use crate::term::{TermArena, TermId, TermKind};

/// The literal a term over literal children denotes, at the term's type.
pub fn fold_literal(arena: &mut TermArena, id: TermId) -> Option<TermId> {
    let term = arena.term(id);
    if term.kind.is_nullary() {
        return None;
    }
    let all_literal = term
        .kind
        .children()
        .all(|child| matches!(arena.term(child).kind, TermKind::Literal(_)));
    if !all_literal {
        return None;
    }
    let value = eval(arena, id, &mut |_, _| {
        unreachable!("every child is a literal")
    });
    let bits = MachineBitVector::new(term.width_bits(), value as u64)?;
    Some(arena.intern(term.ty, TermKind::Literal(bits)))
}

fn fold_if(arena: &mut TermArena, id: TermId, shape: fn(&TermKind) -> bool) -> Option<TermId> {
    if !shape(&arena.term(id).kind) {
        return None;
    }
    fold_literal(arena, id)
}

macro_rules! literal_rule {
    ($name:ident, $id:literal, $shape:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Literal,
            decreases: Measure::NonLeafNodes,
            apply: |arena, id| fold_if(arena, id, $shape),
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

pub(super) fn lit(arena: &mut TermArena, width: u32, bits: u64) -> TermId {
    let ty = r2ssa::MachineType::Integer {
        width_bits: width,
        signedness: MachineSignedness::Unsigned,
    };
    arena.intern(
        ty,
        TermKind::Literal(MachineBitVector::new(width, bits).expect("proof width fits")),
    )
}

pub(super) fn unsigned(width: u32) -> r2ssa::MachineType {
    r2ssa::MachineType::Integer {
        width_bits: width,
        signedness: MachineSignedness::Unsigned,
    }
}

pub(super) fn boolean(width: u32) -> r2ssa::MachineType {
    r2ssa::MachineType::Bool {
        storage_bits: width,
    }
}

/// Two literals that exercise the wrap: one near the top of the range, one
/// small.
fn two_literals(arena: &mut TermArena, width: u32) -> (TermId, TermId) {
    let top = if width >= 64 {
        u64::MAX - 5
    } else {
        (1u64 << width) - 6
    };
    (lit(arena, width, top), lit(arena, width, 9))
}

fn arith(op: MachineArithmeticOp) -> Template {
    match op {
        MachineArithmeticOp::Add => |arena, w, _| {
            let (l, r) = two_literals(arena, w);
            arena.intern(
                unsigned(w),
                TermKind::Arithmetic {
                    op: MachineArithmeticOp::Add,
                    left: l,
                    right: r,
                },
            )
        },
        MachineArithmeticOp::Subtract => |arena, w, _| {
            let (l, r) = two_literals(arena, w);
            arena.intern(
                unsigned(w),
                TermKind::Arithmetic {
                    op: MachineArithmeticOp::Subtract,
                    left: r,
                    right: l,
                },
            )
        },
        MachineArithmeticOp::Multiply => |arena, w, _| {
            let (l, r) = two_literals(arena, w);
            arena.intern(
                unsigned(w),
                TermKind::Arithmetic {
                    op: MachineArithmeticOp::Multiply,
                    left: l,
                    right: r,
                },
            )
        },
    }
}

literal_rule!(
    ADD,
    "literal.add",
    |k| matches!(
        k,
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Add,
            ..
        }
    ),
    &[|a, w, l| arith(MachineArithmeticOp::Add)(a, w, l)]
);
literal_rule!(
    SUB,
    "literal.sub",
    |k| matches!(
        k,
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Subtract,
            ..
        }
    ),
    &[|a, w, l| arith(MachineArithmeticOp::Subtract)(a, w, l)]
);
literal_rule!(
    MUL,
    "literal.mul",
    |k| matches!(
        k,
        TermKind::Arithmetic {
            op: MachineArithmeticOp::Multiply,
            ..
        }
    ),
    &[|a, w, l| arith(MachineArithmeticOp::Multiply)(a, w, l)]
);
literal_rule!(
    NEG,
    "literal.neg",
    |k| matches!(k, TermKind::Negate(_)),
    &[|arena, w, _| {
        let x = lit(arena, w, 9);
        arena.intern(unsigned(w), TermKind::Negate(x))
    }]
);
literal_rule!(
    AND,
    "literal.and",
    |k| matches!(
        k,
        TermKind::Bitwise {
            op: MachineBitwiseOp::And,
            ..
        }
    ),
    &[|arena, w, _| {
        let (l, r) = two_literals(arena, w);
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::And,
                left: l,
                right: r,
            },
        )
    }]
);
literal_rule!(
    OR,
    "literal.or",
    |k| matches!(
        k,
        TermKind::Bitwise {
            op: MachineBitwiseOp::Or,
            ..
        }
    ),
    &[|arena, w, _| {
        let (l, r) = two_literals(arena, w);
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::Or,
                left: l,
                right: r,
            },
        )
    }]
);
literal_rule!(
    XOR,
    "literal.xor",
    |k| matches!(
        k,
        TermKind::Bitwise {
            op: MachineBitwiseOp::Xor,
            ..
        }
    ),
    &[|arena, w, _| {
        let (l, r) = two_literals(arena, w);
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::Xor,
                left: l,
                right: r,
            },
        )
    }]
);
literal_rule!(
    NOT,
    "literal.not",
    |k| matches!(k, TermKind::BitwiseNot(_)),
    &[|arena, w, _| {
        let x = lit(arena, w, 9);
        arena.intern(unsigned(w), TermKind::BitwiseNot(x))
    }]
);
literal_rule!(
    SHIFT,
    "literal.shift",
    |k| matches!(k, TermKind::Shift { .. }),
    &[
        |arena, w, _| {
            let v = lit(arena, w, 0x5b);
            let c = lit(arena, 8, 3);
            arena.intern(
                unsigned(w),
                TermKind::Shift {
                    kind: MachineShiftKind::Left,
                    overshift: MachineOvershiftBehavior::Zero,
                    value: v,
                    count: c,
                },
            )
        },
        |arena, w, _| {
            let v = lit(arena, w, 0x5b);
            let c = lit(arena, 8, 3);
            arena.intern(
                unsigned(w),
                TermKind::Shift {
                    kind: MachineShiftKind::LogicalRight,
                    overshift: MachineOvershiftBehavior::Zero,
                    value: v,
                    count: c,
                },
            )
        },
        |arena, w, _| {
            let (top, _) = two_literals(arena, w);
            let c = lit(arena, 8, 3);
            arena.intern(
                unsigned(w),
                TermKind::Shift {
                    kind: MachineShiftKind::ArithmeticRight,
                    overshift: MachineOvershiftBehavior::SignFill,
                    value: top,
                    count: c,
                },
            )
        },
        // An over-wide count: the literal count exceeds the width.
        |arena, w, _| {
            let v = lit(arena, w, 0x5b);
            let c = lit(arena, 8, 200);
            arena.intern(
                unsigned(w),
                TermKind::Shift {
                    kind: MachineShiftKind::Left,
                    overshift: MachineOvershiftBehavior::Zero,
                    value: v,
                    count: c,
                },
            )
        },
        |arena, w, _| {
            let (top, _) = two_literals(arena, w);
            let c = lit(arena, 8, 200);
            arena.intern(
                unsigned(w),
                TermKind::Shift {
                    kind: MachineShiftKind::ArithmeticRight,
                    overshift: MachineOvershiftBehavior::SignFill,
                    value: top,
                    count: c,
                },
            )
        },
    ]
);

fn compare(
    op: MachineComparisonOp,
    interpretation: MachineSignedness,
) -> impl Fn(&mut TermArena, u32) -> TermId {
    move |arena, w| {
        let (l, r) = two_literals(arena, w);
        arena.intern(
            boolean(8),
            TermKind::Compare {
                op,
                interpretation,
                left: l,
                right: r,
            },
        )
    }
}

literal_rule!(
    COMPARE,
    "literal.compare",
    |k| matches!(k, TermKind::Compare { .. }),
    &[
        |a, w, _| compare(MachineComparisonOp::Equal, MachineSignedness::Unsigned)(a, w),
        |a, w, _| compare(MachineComparisonOp::NotEqual, MachineSignedness::Unsigned)(a, w),
        |a, w, _| compare(MachineComparisonOp::LessThan, MachineSignedness::Unsigned)(a, w),
        |a, w, _| compare(MachineComparisonOp::LessThan, MachineSignedness::Signed)(a, w),
        |a, w, _| compare(
            MachineComparisonOp::LessThanOrEqual,
            MachineSignedness::Unsigned
        )(a, w),
        |a, w, _| compare(
            MachineComparisonOp::LessThanOrEqual,
            MachineSignedness::Signed
        )(a, w),
    ]
);

fn flag(op: MachineArithmeticFlagOp) -> impl Fn(&mut TermArena, u32) -> TermId {
    move |arena, w| {
        let (l, r) = two_literals(arena, w);
        arena.intern(
            boolean(8),
            TermKind::Flag {
                op,
                left: l,
                right: r,
            },
        )
    }
}

literal_rule!(
    FLAG,
    "literal.flag",
    |k| matches!(k, TermKind::Flag { .. }),
    &[
        |a, w, _| flag(MachineArithmeticFlagOp::UnsignedCarry)(a, w),
        |a, w, _| flag(MachineArithmeticFlagOp::SignedCarry)(a, w),
        |a, w, _| flag(MachineArithmeticFlagOp::SignedBorrow)(a, w),
    ]
);

fn bool_lit(arena: &mut TermArena, value: bool) -> TermId {
    arena.intern(
        boolean(8),
        TermKind::Literal(MachineBitVector::new(8, u64::from(value)).expect("bool literal")),
    )
}

literal_rule!(
    BOOL,
    "literal.bool",
    |k| matches!(k, TermKind::Boolean { .. }),
    &[
        |arena, _, _| {
            let (l, r) = (bool_lit(arena, true), bool_lit(arena, false));
            arena.intern(
                boolean(8),
                TermKind::Boolean {
                    op: MachineBooleanOp::And,
                    left: l,
                    right: r,
                },
            )
        },
        |arena, _, _| {
            let (l, r) = (bool_lit(arena, true), bool_lit(arena, false));
            arena.intern(
                boolean(8),
                TermKind::Boolean {
                    op: MachineBooleanOp::Or,
                    left: l,
                    right: r,
                },
            )
        },
        |arena, _, _| {
            let (l, r) = (bool_lit(arena, true), bool_lit(arena, false));
            arena.intern(
                boolean(8),
                TermKind::Boolean {
                    op: MachineBooleanOp::Xor,
                    left: l,
                    right: r,
                },
            )
        },
    ]
);
literal_rule!(
    BOOL_NOT,
    "literal.boolnot",
    |k| matches!(k, TermKind::BooleanNot(_)),
    &[|arena, _, _| {
        let b = bool_lit(arena, false);
        arena.intern(boolean(8), TermKind::BooleanNot(b))
    }]
);
literal_rule!(
    CAST,
    "literal.cast",
    |k| matches!(k, TermKind::Cast { .. }),
    &[
        |arena, w, _| {
            let x = lit(arena, 8, 0x85);
            arena.intern(
                unsigned(w.max(16)),
                TermKind::Cast {
                    kind: MachineCastKind::ZeroExtend,
                    input: x,
                },
            )
        },
        |arena, w, _| {
            let x = lit(arena, 8, 0x85);
            arena.intern(
                unsigned(w.max(16)),
                TermKind::Cast {
                    kind: MachineCastKind::SignExtend,
                    input: x,
                },
            )
        },
        |arena, w, _| {
            let x = lit(arena, 64, 0x1234_5678_9abc_def0);
            arena.intern(
                unsigned(w.min(32)),
                TermKind::Cast {
                    kind: MachineCastKind::Truncate,
                    input: x,
                },
            )
        },
        |arena, w, _| {
            let x = lit(arena, w, 0x85);
            arena.intern(
                unsigned(w),
                TermKind::Cast {
                    kind: MachineCastKind::BitReinterpret,
                    input: x,
                },
            )
        },
    ]
);
literal_rule!(
    EXTRACT,
    "literal.extract",
    |k| matches!(k, TermKind::Extract { .. }),
    &[|arena, w, _| {
        let x = lit(arena, 64, 0x1234_5678_9abc_def0);
        arena.intern(
            unsigned(w.min(32)),
            TermKind::Extract {
                input: x,
                lsb_bits: 8,
            },
        )
    }]
);
literal_rule!(
    CONCAT,
    "literal.concat",
    |k| matches!(k, TermKind::Concat { .. }),
    &[|arena, w, _| {
        let half = (w / 2).max(4);
        let (h, l) = (lit(arena, half, 0x9), lit(arena, half, 0x5));
        arena.intern(unsigned(half * 2), TermKind::Concat { high: h, low: l })
    }]
);
literal_rule!(
    SELECT,
    "literal.select",
    |k| matches!(k, TermKind::Select { .. }),
    &[|arena, w, _| {
        let c = bool_lit(arena, true);
        let (t, f) = two_literals(arena, w);
        arena.intern(
            unsigned(w),
            TermKind::Select {
                condition: c,
                if_true: t,
                if_false: f,
            },
        )
    }]
);

pub static GROUP: &[&Rule] = &[
    &ADD, &SUB, &MUL, &NEG, &AND, &OR, &XOR, &NOT, &SHIFT, &COMPARE, &FLAG, &BOOL, &BOOL_NOT,
    &CAST, &EXTRACT, &CONCAT, &SELECT,
];
