//! Group H: masks.

use r2ssa::{MachineBitwiseOp, MachineCastKind};

use super::literal::{lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup, literal_like, literal_of};
use crate::eval::mask;
use crate::term::{TermArena, TermId, TermKind};

macro_rules! mask_rule {
    ($name:ident, $id:literal, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Mask,
            decreases: Measure::NonLeafNodes,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

/// `op(op(x, c1), c2)` with literals on the right, combined by `combine`.
fn nested_literal(
    arena: &mut TermArena,
    id: TermId,
    op: MachineBitwiseOp,
    combine: fn(u64, u64) -> u64,
) -> Option<TermId> {
    let TermKind::Bitwise {
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
    let TermKind::Bitwise {
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
    let ty = arena.term(id).ty;
    let combined = literal_like(arena, id, combine(c1, c2));
    Some(arena.intern(
        ty,
        TermKind::Bitwise {
            op,
            left: x,
            right: combined,
        },
    ))
}

fn nested_template(op: MachineBitwiseOp) -> impl Fn(&mut TermArena, u32, &[TermId]) -> TermId {
    move |arena, w, l| {
        let c1 = lit(arena, w, 0x3c);
        let c2 = lit(arena, w, 0x66);
        let inner = arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op,
                left: l[0],
                right: c1,
            },
        );
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op,
                left: inner,
                right: c2,
            },
        )
    }
}

mask_rule!(
    AND_AND,
    "mask.and_and",
    |arena, id| nested_literal(arena, id, MachineBitwiseOp::And, |a, b| a & b),
    &[|a, w, l| nested_template(MachineBitwiseOp::And)(a, w, l)]
);
mask_rule!(
    OR_OR,
    "mask.or_or",
    |arena, id| nested_literal(arena, id, MachineBitwiseOp::Or, |a, b| a | b),
    &[|a, w, l| nested_template(MachineBitwiseOp::Or)(a, w, l)]
);
mask_rule!(
    XOR_XOR,
    "mask.xor_xor",
    |arena, id| nested_literal(arena, id, MachineBitwiseOp::Xor, |a, b| a ^ b),
    &[|a, w, l| nested_template(MachineBitwiseOp::Xor)(a, w, l)]
);

// `and(zext(x), m)` where `m` keeps every bit of `x`: the mask does nothing.
mask_rule!(
    AND_OF_ZEXT,
    "mask.and_of_zext",
    |arena, id| {
        let TermKind::Bitwise {
            op: MachineBitwiseOp::And,
            left,
            right,
        } = arena.term(id).kind
        else {
            return None;
        };
        let m = literal_of(arena, right)?;
        let TermKind::Cast {
            kind: MachineCastKind::ZeroExtend,
            input: x,
        } = arena.term(left).kind
        else {
            return None;
        };
        let keep = mask(arena.term(x).width_bits()) as u64;
        (m & keep == keep).then_some(left)
    },
    &[|arena, w, _| {
        let narrow = (w / 2).max(4);
        let x = arena.intern(unsigned(narrow), TermKind::Variable(100));
        let ext = arena.intern(
            unsigned(w),
            TermKind::Cast {
                kind: MachineCastKind::ZeroExtend,
                input: x,
            },
        );
        let m = lit(arena, w, mask(narrow) as u64 | (1u64 << (w - 1)));
        arena.intern(
            unsigned(w),
            TermKind::Bitwise {
                op: MachineBitwiseOp::And,
                left: ext,
                right: m,
            },
        )
    }]
);
