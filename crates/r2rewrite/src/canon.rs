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

/// The affine normal form of a tree of additions, subtractions, negations
/// and multiplications by a literal at one integer width.
///
/// Collects `sum k_i * t_i + c` modulo `2^w` over the maximal such tree,
/// merging like terms and dropping zero coefficients, and emits the terms in
/// id order with the constant last; a coefficient or constant whose signed
/// reading is negative is subtracted rather than added. A multiplication by a
/// literal counts the multiplied term as one atom -- nothing is distributed
/// over a sum -- so the output never has more nodes than the input, and
/// re-collecting the output yields the same sum, so the form is idempotent.
/// Applied only where it changes the term.
pub fn affine_normalize(arena: &mut TermArena, id: TermId) -> TermId {
    let term = arena.term(id);
    if !matches!(term.ty, r2ssa::MachineType::Integer { .. }) {
        return id;
    }
    if !matches!(
        term.kind,
        TermKind::Arithmetic {
            op: r2ssa::MachineArithmeticOp::Add | r2ssa::MachineArithmeticOp::Subtract,
            ..
        } | TermKind::Negate(_)
    ) {
        return id;
    }
    let width = term.width_bits();
    let modulus = crate::eval::mask(width) as u64;
    let mut coefficients: std::collections::BTreeMap<TermId, u64> =
        std::collections::BTreeMap::new();
    let mut constant = 0u64;
    let mut atoms = 0usize;
    collect_affine(
        arena,
        id,
        1,
        width,
        &mut coefficients,
        &mut constant,
        &mut atoms,
    );
    let emitted = emit_affine(arena, term.ty, width, modulus, &coefficients, constant);
    if arena.tree_measure(emitted) > arena.tree_measure(id) {
        // Cannot happen by construction; refuse rather than grow.
        return id;
    }
    emitted
}

pub(crate) fn collect_affine(
    arena: &TermArena,
    id: TermId,
    scale: u64,
    width: u32,
    coefficients: &mut std::collections::BTreeMap<TermId, u64>,
    constant: &mut u64,
    atoms: &mut usize,
) {
    let modulus = crate::eval::mask(width) as u64;
    let term = arena.term(id);
    if term.width_bits() != width {
        *coefficients.entry(id).or_insert(0) = coefficients[&id].wrapping_add(scale) & modulus;
        *atoms += 1;
        return;
    }
    match term.kind {
        TermKind::Literal(bits) => {
            *constant = constant.wrapping_add(scale.wrapping_mul(bits.bits())) & modulus;
        }
        TermKind::Arithmetic {
            op: r2ssa::MachineArithmeticOp::Add,
            left,
            right,
        } => {
            collect_affine(arena, left, scale, width, coefficients, constant, atoms);
            collect_affine(arena, right, scale, width, coefficients, constant, atoms);
        }
        TermKind::Arithmetic {
            op: r2ssa::MachineArithmeticOp::Subtract,
            left,
            right,
        } => {
            collect_affine(arena, left, scale, width, coefficients, constant, atoms);
            let negated = 0u64.wrapping_sub(scale) & modulus;
            collect_affine(arena, right, negated, width, coefficients, constant, atoms);
        }
        TermKind::Negate(input) => {
            let negated = 0u64.wrapping_sub(scale) & modulus;
            collect_affine(arena, input, negated, width, coefficients, constant, atoms);
        }
        TermKind::Arithmetic {
            op: r2ssa::MachineArithmeticOp::Multiply,
            left,
            right,
        } if literal_bits(arena, right).is_some() => {
            let k = literal_bits(arena, right).expect("checked");
            let entry = coefficients.entry(left).or_insert(0);
            *entry = entry.wrapping_add(scale.wrapping_mul(k)) & modulus;
            *atoms += 1;
        }
        _ => {
            let entry = coefficients.entry(id).or_insert(0);
            *entry = entry.wrapping_add(scale) & modulus;
            *atoms += 1;
        }
    }
}

/// Whether a coefficient reads as negative at `width`.
pub(crate) fn is_negative(k: u64, width: u32) -> bool {
    width < 64 && k >> (width - 1) == 1 || width == 64 && k >> 63 == 1
}

pub(crate) fn emit_affine(
    arena: &mut TermArena,
    ty: r2ssa::MachineType,
    width: u32,
    modulus: u64,
    coefficients: &std::collections::BTreeMap<TermId, u64>,
    constant: u64,
) -> TermId {
    use r2ssa::MachineArithmeticOp::{Add, Multiply, Subtract};
    let literal = |arena: &mut TermArena, value: u64| {
        let bits = r2ssa::MachineBitVector::new(width, value & modulus).expect("term width fits");
        arena.intern(ty, TermKind::Literal(bits))
    };
    let piece = |arena: &mut TermArena, t: TermId, k: u64| -> TermId {
        if k == 1 {
            t
        } else {
            let k = literal(arena, k);
            arena.intern(
                ty,
                TermKind::Arithmetic {
                    op: Multiply,
                    left: t,
                    right: k,
                },
            )
        }
    };
    let mut acc: Option<TermId> = None;
    for (&t, &k) in coefficients {
        if k == 0 || is_negative(k, width) {
            continue;
        }
        let p = piece(arena, t, k);
        acc = Some(match acc {
            None => p,
            Some(a) => arena.intern(
                ty,
                TermKind::Arithmetic {
                    op: Add,
                    left: a,
                    right: p,
                },
            ),
        });
    }
    for (&t, &k) in coefficients {
        if k == 0 || !is_negative(k, width) {
            continue;
        }
        let magnitude = 0u64.wrapping_sub(k) & modulus;
        let p = piece(arena, t, magnitude);
        acc = Some(match acc {
            None => arena.intern(ty, TermKind::Negate(p)),
            Some(a) => arena.intern(
                ty,
                TermKind::Arithmetic {
                    op: Subtract,
                    left: a,
                    right: p,
                },
            ),
        });
    }
    match acc {
        None => literal(arena, constant),
        Some(a) if constant == 0 => a,
        Some(a) if is_negative(constant, width) => {
            let c = literal(arena, 0u64.wrapping_sub(constant) & modulus);
            arena.intern(
                ty,
                TermKind::Arithmetic {
                    op: Subtract,
                    left: a,
                    right: c,
                },
            )
        }
        Some(a) => {
            let c = literal(arena, constant);
            arena.intern(
                ty,
                TermKind::Arithmetic {
                    op: Add,
                    left: a,
                    right: c,
                },
            )
        }
    }
}

/// Every normaliser, in the order the driver applies them.
pub fn normalize(arena: &mut TermArena, id: TermId) -> TermId {
    let id = truncate_as_extract(arena, id);
    let id = clamp_arithmetic_shift_count(arena, id);
    let id = affine_normalize(arena, id);
    order_operands(arena, id)
}
