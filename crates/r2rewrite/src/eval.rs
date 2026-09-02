//! Concrete interpreter for terms, the twin of the Z3 encoding in the proof
//! harness. Widths are at most 64 bits; arithmetic is done in `u128` and
//! masked to the term's width.

use r2ssa::{
    MachineArithmeticFlagOp, MachineArithmeticOp, MachineBitwiseOp, MachineBooleanOp,
    MachineCastKind, MachineComparisonOp, MachineExprId, MachineOvershiftBehavior,
    MachineShiftKind, MachineSignedness, MachineType,
};

use crate::term::{TermArena, TermId, TermKind};

pub fn mask(width_bits: u32) -> u128 {
    if width_bits >= 128 {
        u128::MAX
    } else {
        (1u128 << width_bits) - 1
    }
}

/// Interpret `bits` of `width_bits` as a signed value.
pub fn signed(bits: u128, width_bits: u32) -> i128 {
    let shift = 128 - width_bits;
    ((bits << shift) as i128) >> shift
}

/// What a term reads from outside itself: a base-arena node, or a free
/// variable of a proof template.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LeafRef {
    Expr(MachineExprId),
    Variable(u32),
}

/// Evaluate `root`, asking `leaf` for the value of every base-arena node or
/// variable it reads. A Bool-typed leaf must be answered with 0 or 1.
pub fn eval(
    arena: &TermArena,
    root: TermId,
    leaf: &mut dyn FnMut(LeafRef, &MachineType) -> u128,
) -> u128 {
    let term = arena.term(root);
    let width = term.width_bits();
    let m = mask(width);
    let value = match term.kind {
        TermKind::Leaf(expr) | TermKind::Opaque(expr) => leaf(LeafRef::Expr(expr), &term.ty),
        TermKind::Variable(index) => leaf(LeafRef::Variable(index), &term.ty),
        TermKind::Literal(bits) => u128::from(bits.bits()),
        TermKind::Arithmetic { op, left, right } => {
            let l = eval(arena, left, leaf);
            let r = eval(arena, right, leaf);
            match op {
                MachineArithmeticOp::Add => l.wrapping_add(r),
                MachineArithmeticOp::Subtract => l.wrapping_sub(r),
                MachineArithmeticOp::Multiply => l.wrapping_mul(r),
            }
        }
        TermKind::Negate(input) => 0u128.wrapping_sub(eval(arena, input, leaf)),
        TermKind::Bitwise { op, left, right } => {
            let l = eval(arena, left, leaf);
            let r = eval(arena, right, leaf);
            match op {
                MachineBitwiseOp::And => l & r,
                MachineBitwiseOp::Or => l | r,
                MachineBitwiseOp::Xor => l ^ r,
            }
        }
        TermKind::BitwiseNot(input) => !eval(arena, input, leaf),
        TermKind::Boolean { op, left, right } => {
            let l = eval(arena, left, leaf) != 0;
            let r = eval(arena, right, leaf) != 0;
            u128::from(match op {
                MachineBooleanOp::And => l && r,
                MachineBooleanOp::Or => l || r,
                MachineBooleanOp::Xor => l ^ r,
            })
        }
        TermKind::BooleanNot(input) => u128::from(eval(arena, input, leaf) == 0),
        TermKind::Shift {
            kind,
            overshift,
            value,
            count,
        } => {
            let v = eval(arena, value, leaf);
            let c = eval(arena, count, leaf);
            let w = u128::from(width);
            let c = match overshift {
                MachineOvershiftBehavior::MaskCount => c & (w - 1),
                _ => c,
            };
            let sign = (v >> (width - 1)) & 1 == 1;
            match kind {
                MachineShiftKind::Left => {
                    if c >= w {
                        0
                    } else {
                        v << c
                    }
                }
                MachineShiftKind::LogicalRight => {
                    if c >= w {
                        0
                    } else {
                        v >> c
                    }
                }
                MachineShiftKind::ArithmeticRight => {
                    if c >= w {
                        match overshift {
                            MachineOvershiftBehavior::Zero => 0,
                            _ => {
                                if sign {
                                    m
                                } else {
                                    0
                                }
                            }
                        }
                    } else {
                        (signed(v, width) >> c) as u128
                    }
                }
            }
        }
        TermKind::Compare {
            op,
            interpretation,
            left,
            right,
        } => {
            let l = eval(arena, left, leaf);
            let r = eval(arena, right, leaf);
            let lw = arena.term(left).width_bits();
            let result = match (op, interpretation) {
                (MachineComparisonOp::Equal, _) => l == r,
                (MachineComparisonOp::NotEqual, _) => l != r,
                (MachineComparisonOp::LessThan, MachineSignedness::Unsigned) => l < r,
                (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Unsigned) => l <= r,
                (MachineComparisonOp::LessThan, MachineSignedness::Signed) => {
                    signed(l, lw) < signed(r, lw)
                }
                (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Signed) => {
                    signed(l, lw) <= signed(r, lw)
                }
            };
            u128::from(result)
        }
        TermKind::Flag { op, left, right } => {
            let l = eval(arena, left, leaf);
            let r = eval(arena, right, leaf);
            let lw = arena.term(left).width_bits();
            let lm = mask(lw);
            let result = match op {
                MachineArithmeticFlagOp::UnsignedCarry => l + r > lm,
                MachineArithmeticFlagOp::SignedCarry => {
                    let sum = signed(l, lw) + signed(r, lw);
                    sum != signed((sum as u128) & lm, lw)
                }
                MachineArithmeticFlagOp::SignedBorrow => {
                    let diff = signed(l, lw) - signed(r, lw);
                    diff != signed((diff as u128) & lm, lw)
                }
            };
            u128::from(result)
        }
        TermKind::Cast { kind, input } => {
            let x = eval(arena, input, leaf);
            let from = arena.term(input).width_bits();
            match kind {
                MachineCastKind::SignExtend => signed(x, from) as u128,
                MachineCastKind::ZeroExtend
                | MachineCastKind::Truncate
                | MachineCastKind::BitReinterpret
                | MachineCastKind::IntegerToAddress
                | MachineCastKind::AddressToInteger => x,
            }
        }
        TermKind::Extract { input, lsb_bits } => eval(arena, input, leaf) >> lsb_bits,
        TermKind::Concat { high, low } => {
            let low_width = arena.term(low).width_bits();
            (eval(arena, high, leaf) << low_width) | eval(arena, low, leaf)
        }
        TermKind::Select {
            condition,
            if_true,
            if_false,
        } => {
            if eval(arena, condition, leaf) != 0 {
                eval(arena, if_true, leaf)
            } else {
                eval(arena, if_false, leaf)
            }
        }
    };
    value & m
}
