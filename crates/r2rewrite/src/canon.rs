//! Normalisers: idempotent, measure-non-increasing rewrites the driver applies
//! to every canonical node. Unlike a rule, a normaliser never fires "again";
//! applying it to its own output returns the same term, and it never adds a
//! node, so the driver's termination argument does not depend on it.

use r2ssa::{MachineArithmeticOp, MachineBitwiseOp, MachineBooleanOp, MachineComparisonOp};

use crate::term::{TermArena, TermId, TermKind};

/// Whether swapping the two operands of this term leaves its value unchanged.
pub fn is_commutative(kind: &TermKind) -> bool {
    match kind {
        TermKind::Arithmetic { op, .. } => {
            matches!(op, MachineArithmeticOp::Add | MachineArithmeticOp::Multiply)
        }
        TermKind::Bitwise { op, .. } => matches!(
            op,
            MachineBitwiseOp::And | MachineBitwiseOp::Or | MachineBitwiseOp::Xor
        ),
        TermKind::Boolean { op, .. } => matches!(
            op,
            MachineBooleanOp::And | MachineBooleanOp::Or | MachineBooleanOp::Xor
        ),
        TermKind::Compare { op, .. } => matches!(
            op,
            MachineComparisonOp::Equal | MachineComparisonOp::NotEqual
        ),
        _ => false,
    }
}

/// Operand order for a commutative term: a literal goes right; two literals
/// order by value; two non-literals order by id. Total, so the result is one
/// term for every operand pair, and idempotent.
pub fn order_operands(arena: &mut TermArena, id: TermId) -> TermId {
    let term = arena.term(id);
    if !is_commutative(&term.kind) {
        return id;
    }
    let mut children = term.kind.children();
    let (Some(left), Some(right)) = (children.next(), children.next()) else {
        return id;
    };
    let left_literal = literal_bits(arena, left);
    let right_literal = literal_bits(arena, right);
    let swap = match (left_literal, right_literal) {
        (Some(_), None) => true,
        (None, Some(_)) => false,
        (Some(l), Some(r)) => l > r,
        (None, None) => left > right,
    };
    if !swap {
        return id;
    }
    arena.intern(term.ty, term.kind.with_children(&[right, left]))
}

pub fn literal_bits(arena: &TermArena, id: TermId) -> Option<u64> {
    match arena.term(id).kind {
        TermKind::Literal(bits) => Some(bits.bits()),
        _ => None,
    }
}

/// A truncation is the extraction of the low bits, and the extract rules
/// compose where two spellings of one operation would not. Same node count,
/// same width, idempotent.
pub fn truncate_as_extract(arena: &mut TermArena, id: TermId) -> TermId {
    let term = arena.term(id);
    match term.kind {
        TermKind::Cast {
            kind: r2ssa::MachineCastKind::Truncate,
            input,
        } => arena.intern(term.ty, TermKind::Extract { input, lsb_bits: 0 }),
        _ => id,
    }
}

/// An arithmetic right shift that sign-fills on overshift shifts by at most
/// width minus one: a literal count beyond that is the same operation with
/// the count clamped. Same node count, idempotent.
pub fn clamp_arithmetic_shift_count(arena: &mut TermArena, id: TermId) -> TermId {
    let term = arena.term(id);
    let TermKind::Shift {
        kind: r2ssa::MachineShiftKind::ArithmeticRight,
        overshift: r2ssa::MachineOvershiftBehavior::SignFill,
        value,
        count,
    } = term.kind
    else {
        return id;
    };
    let width = u64::from(term.width_bits());
    let Some(bits) = literal_bits(arena, count) else {
        return id;
    };
    if bits < width {
        return id;
    }
    let count_term = arena.term(count);
    let clamped = r2ssa::MachineBitVector::new(count_term.width_bits(), width - 1)
        .expect("count width fits a literal");
    let count = arena.intern(count_term.ty, TermKind::Literal(clamped));
    arena.intern(
        term.ty,
        TermKind::Shift {
            kind: r2ssa::MachineShiftKind::ArithmeticRight,
            overshift: r2ssa::MachineOvershiftBehavior::SignFill,
            value,
            count,
        },
    )
}

/// Every normaliser, in the order the driver applies them.
pub fn normalize(arena: &mut TermArena, id: TermId) -> TermId {
    let id = truncate_as_extract(arena, id);
    let id = clamp_arithmetic_shift_count(arena, id);
    order_operands(arena, id)
}
