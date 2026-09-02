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

/// Every normaliser, in the order the driver applies them.
pub fn normalize(arena: &mut TermArena, id: TermId) -> TermId {
    order_operands(arena, id)
}
