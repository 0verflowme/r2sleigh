//! Group F: shifts by literal counts.

use r2ssa::{MachineBitVector, MachineOvershiftBehavior, MachineShiftKind};

use super::literal::{lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup, literal_like, literal_of};
use crate::term::{TermArena, TermId, TermKind};

macro_rules! shift_rule {
    ($name:ident, $id:literal, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Shift,
            decreases: Measure::NonLeafNodes,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

/// `Shift(kind, Shift(kind, x, a), b)` with literal counts.
fn nested(
    arena: &TermArena,
    id: TermId,
    kind: MachineShiftKind,
) -> Option<(TermId, u64, u64, TermId)> {
    match arena.term(id).kind {
        TermKind::Shift {
            kind: outer,
            value,
            count,
            ..
        } if outer == kind => {
            let b = literal_of(arena, count)?;
            match arena.term(value).kind {
                TermKind::Shift {
                    kind: inner,
                    value: x,
                    count: inner_count,
                    ..
                } if inner == kind => {
                    let a = literal_of(arena, inner_count)?;
                    Some((x, a, b, count))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn shift(arena: &mut TermArena, kind: MachineShiftKind, value: TermId, count: TermId) -> TermId {
    let ty = arena.term(value).ty;
    let overshift = match kind {
        MachineShiftKind::ArithmeticRight => MachineOvershiftBehavior::SignFill,
        _ => MachineOvershiftBehavior::Zero,
    };
    arena.intern(
        ty,
        TermKind::Shift {
            kind,
            overshift,
            value,
            count,
        },
    )
}

fn literal_count(arena: &mut TermArena, like: TermId, value: u64) -> TermId {
    let ty = arena.term(like).ty;
    let bits = MachineBitVector::new(ty.width_bits(), value).expect("count width fits a literal");
    arena.intern(ty, TermKind::Literal(bits))
}

fn compose(arena: &mut TermArena, id: TermId, kind: MachineShiftKind) -> Option<TermId> {
    let (x, a, b, count) = nested(arena, id, kind)?;
    let width = u64::from(arena.term(id).width_bits());
    let total = a.checked_add(b)?;
    let total = match kind {
        MachineShiftKind::ArithmeticRight => total.min(width - 1),
        _ => {
            if total >= width {
                return None;
            }
            total
        }
    };
    if total >= (1u64 << arena.term(count).width_bits().min(63)) {
        return None;
    }
    let count = literal_count(arena, count, total);
    Some(shift(arena, kind, x, count))
}

fn nested_template(kind: MachineShiftKind) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, _, l| {
        let a = lit(arena, 8, 3);
        let b = lit(arena, 8, 2);
        let inner = shift(arena, kind, l[0], a);
        shift(arena, kind, inner, b)
    }
}

shift_rule!(
    SHL_SHL,
    "shift.shl_shl",
    |arena, id| compose(arena, id, MachineShiftKind::Left),
    &[|a, w, l| nested_template(MachineShiftKind::Left)(a, w, l)]
);
shift_rule!(
    LSHR_LSHR,
    "shift.lshr_lshr",
    |arena, id| compose(arena, id, MachineShiftKind::LogicalRight),
    &[|a, w, l| nested_template(MachineShiftKind::LogicalRight)(a, w, l)]
);
shift_rule!(
    ASHR_ASHR,
    "shift.ashr_ashr",
    |arena, id| compose(arena, id, MachineShiftKind::ArithmeticRight),
    &[
        |a, w, l| nested_template(MachineShiftKind::ArithmeticRight)(a, w, l),
        // Counts that sum past the width clamp to width minus one.
        |arena, _, l| {
            let a = lit(arena, 8, 60);
            let b = lit(arena, 8, 60);
            let inner = shift(arena, MachineShiftKind::ArithmeticRight, l[0], a);
            shift(arena, MachineShiftKind::ArithmeticRight, inner, b)
        },
    ]
);

fn overwidth(arena: &mut TermArena, id: TermId, kind: MachineShiftKind) -> Option<TermId> {
    match arena.term(id).kind {
        TermKind::Shift {
            kind: actual,
            overshift: MachineOvershiftBehavior::Zero,
            count,
            ..
        } if actual == kind
            && literal_of(arena, count)? >= u64::from(arena.term(id).width_bits()) =>
        {
            Some(literal_like(arena, id, 0))
        }
        _ => None,
    }
}

fn overwidth_template(kind: MachineShiftKind) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, w, l| {
        let count = lit(arena, 8, u64::from(w));
        let _ = unsigned(w);
        shift(arena, kind, l[0], count)
    }
}

shift_rule!(
    SHL_OVERWIDTH,
    "shift.shl_overwidth",
    |arena, id| overwidth(arena, id, MachineShiftKind::Left),
    &[|a, w, l| overwidth_template(MachineShiftKind::Left)(a, w, l)]
);
shift_rule!(
    LSHR_OVERWIDTH,
    "shift.lshr_overwidth",
    |arena, id| overwidth(arena, id, MachineShiftKind::LogicalRight),
    &[|a, w, l| overwidth_template(MachineShiftKind::LogicalRight)(a, w, l)]
);
