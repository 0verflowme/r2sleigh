//! Group C: casts and slices.
//!
//! A truncation normalises to an extract at offset zero before any rule
//! looks, so one family of extract rules covers `trunc(trunc(x))`,
//! `trunc(zext(x))` and the subpiece shapes alike.

use r2ssa::{MachineCastKind, MachineType};

use super::literal::unsigned;
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup, literal_like};
use crate::term::{TermArena, TermId, TermKind};

macro_rules! cast_rule {
    ($name:ident, $id:literal, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Cast,
            decreases: Measure::NonLeafNodes,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

fn width(arena: &TermArena, id: TermId) -> u32 {
    arena.term(id).width_bits()
}

/// A variable narrower than `width`, for templates that need one.
fn narrow_variable(arena: &mut TermArena, width: u32, index: u32) -> TermId {
    let narrow = (width / 2).max(4);
    arena.intern(unsigned(narrow), TermKind::Variable(100 + index))
}

/// A variable wider than `width`, for templates that need one.
fn wide_variable(arena: &mut TermArena, width: u32, index: u32) -> TermId {
    let wide = (width * 2).min(64).max(width + 4);
    arena.intern(unsigned(wide), TermKind::Variable(200 + index))
}

fn extend(arena: &mut TermArena, kind: MachineCastKind, input: TermId, to: u32) -> TermId {
    let ty = match kind {
        MachineCastKind::SignExtend => MachineType::Integer {
            width_bits: to,
            signedness: r2ssa::MachineSignedness::Signed,
        },
        _ => unsigned(to),
    };
    arena.intern(ty, TermKind::Cast { kind, input })
}

fn extract(arena: &mut TermArena, input: TermId, lsb_bits: u32, to: u32) -> TermId {
    arena.intern(unsigned(to), TermKind::Extract { input, lsb_bits })
}

fn nested_extend(arena: &TermArena, id: TermId, kind: MachineCastKind) -> Option<(TermId, TermId)> {
    match arena.term(id).kind {
        TermKind::Cast {
            kind: outer,
            input: inner,
        } if outer == kind => match arena.term(inner).kind {
            TermKind::Cast {
                kind: inner_kind,
                input: x,
            } if inner_kind == kind => Some((inner, x)),
            _ => None,
        },
        _ => None,
    }
}

cast_rule!(
    ZEXT_ZEXT,
    "cast.zext_zext",
    |arena, id| {
        let (_, x) = nested_extend(arena, id, MachineCastKind::ZeroExtend)?;
        let ty = arena.term(id).ty;
        Some(arena.intern(
            ty,
            TermKind::Cast {
                kind: MachineCastKind::ZeroExtend,
                input: x,
            },
        ))
    },
    &[|arena, w, _| {
        let x = narrow_variable(arena, w, 0);
        let mid = (width(arena, x) + w) / 2;
        let inner = extend(
            arena,
            MachineCastKind::ZeroExtend,
            x,
            mid.max(width(arena, x) + 1),
        );
        extend(
            arena,
            MachineCastKind::ZeroExtend,
            inner,
            w.max(width(arena, inner) + 1),
        )
    }]
);
cast_rule!(
    SEXT_SEXT,
    "cast.sext_sext",
    |arena, id| {
        let (_, x) = nested_extend(arena, id, MachineCastKind::SignExtend)?;
        let ty = arena.term(id).ty;
        Some(arena.intern(
            ty,
            TermKind::Cast {
                kind: MachineCastKind::SignExtend,
                input: x,
            },
        ))
    },
    &[|arena, w, _| {
        let x = narrow_variable(arena, w, 0);
        let mid = (width(arena, x) + w) / 2;
        let inner = extend(
            arena,
            MachineCastKind::SignExtend,
            x,
            mid.max(width(arena, x) + 1),
        );
        extend(
            arena,
            MachineCastKind::SignExtend,
            inner,
            w.max(width(arena, inner) + 1),
        )
    }]
);
// An extension to the width its input already has extends nothing. The
// importer never builds one -- a zero or sign extension is admitted only from
// a narrower input -- so this fires on terms a rule produced, and it is what
// makes an extension nested in an identical one, `zext_W(zext_W(x))`, collapse
// through `cast.zext_zext` to the one extension that remains.
cast_rule!(
    EXTEND_IDENTITY,
    "cast.extend_identity",
    |arena, id| match arena.term(id).kind {
        TermKind::Cast {
            kind: MachineCastKind::ZeroExtend | MachineCastKind::SignExtend,
            input,
        } if width(arena, input) == width(arena, id) => Some(input),
        _ => None,
    },
    &[
        |arena, w, l| extend(arena, MachineCastKind::ZeroExtend, l[0], w),
        |arena, w, l| extend(arena, MachineCastKind::SignExtend, l[0], w),
    ]
);
cast_rule!(
    EXTRACT_EXTRACT,
    "cast.extract_extract",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract {
            input,
            lsb_bits: outer,
        } => match arena.term(input).kind {
            TermKind::Extract {
                input: x,
                lsb_bits: inner,
            } => {
                let ty = arena.term(id).ty;
                Some(arena.intern(
                    ty,
                    TermKind::Extract {
                        input: x,
                        lsb_bits: inner + outer,
                    },
                ))
            }
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, _| {
        let x = wide_variable(arena, w, 0);
        let xw = width(arena, x);
        let mid = extract(arena, x, 2, xw - 2);
        extract(arena, mid, 1, w.min(xw - 3))
    }]
);
cast_rule!(
    EXTRACT_FULL,
    "cast.extract_full",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract { input, lsb_bits: 0 } if width(arena, input) == width(arena, id) =>
            Some(input),
        _ => None,
    },
    &[|arena, w, l| extract(arena, l[0], 0, w)]
);
cast_rule!(
    EXTRACT_OF_EXTEND_WHOLE,
    "cast.extract_of_extend_whole",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract { input, lsb_bits: 0 } => match arena.term(input).kind {
            TermKind::Cast {
                kind: MachineCastKind::ZeroExtend | MachineCastKind::SignExtend,
                input: x,
            } if width(arena, x) == width(arena, id) => Some(x),
            _ => None,
        },
        _ => None,
    },
    &[
        |arena, w, l| {
            let ext = extend(
                arena,
                MachineCastKind::ZeroExtend,
                l[0],
                (w * 2).min(64).max(w + 4),
            );
            extract(arena, ext, 0, w)
        },
        |arena, w, l| {
            let ext = extend(
                arena,
                MachineCastKind::SignExtend,
                l[0],
                (w * 2).min(64).max(w + 4),
            );
            extract(arena, ext, 0, w)
        },
    ]
);
cast_rule!(
    EXTRACT_OF_EXTEND_WITHIN,
    "cast.extract_of_extend_within",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract { input, lsb_bits } => match arena.term(input).kind {
            TermKind::Cast {
                kind: MachineCastKind::ZeroExtend | MachineCastKind::SignExtend,
                input: x,
            } if lsb_bits + width(arena, id) <= width(arena, x)
                && !(lsb_bits == 0 && width(arena, id) == width(arena, x)) =>
            {
                let ty = arena.term(id).ty;
                Some(arena.intern(ty, TermKind::Extract { input: x, lsb_bits }))
            }
            _ => None,
        },
        _ => None,
    },
    &[
        |arena, w, l| {
            let ext = extend(
                arena,
                MachineCastKind::ZeroExtend,
                l[0],
                (w * 2).min(64).max(w + 4),
            );
            extract(arena, ext, 1, w - 2)
        },
        |arena, w, l| {
            let ext = extend(
                arena,
                MachineCastKind::SignExtend,
                l[0],
                (w * 2).min(64).max(w + 4),
            );
            extract(arena, ext, 0, w - 1)
        },
    ]
);
cast_rule!(
    EXTRACT_OF_ZEXT_ABOVE,
    "cast.extract_of_zext_above",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract { input, lsb_bits } => match arena.term(input).kind {
            TermKind::Cast {
                kind: MachineCastKind::ZeroExtend,
                input: x,
            } if lsb_bits >= width(arena, x) => Some(literal_like(arena, id, 0)),
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let ext = extend(
            arena,
            MachineCastKind::ZeroExtend,
            l[0],
            (w * 2).min(64).max(w + 4),
        );
        let ew = width(arena, ext);
        extract(arena, ext, w, ew - w)
    }]
);
cast_rule!(
    REINTERPRET_SAME_WIDTH,
    "cast.reinterpret_same_width",
    |arena, id| match arena.term(id).kind {
        TermKind::Cast {
            kind: MachineCastKind::BitReinterpret,
            input,
        } if width(arena, input) == width(arena, id) => Some(input),
        _ => None,
    },
    &[|arena, w, l| arena.intern(
        unsigned(w),
        TermKind::Cast {
            kind: MachineCastKind::BitReinterpret,
            input: l[0]
        }
    )]
);
cast_rule!(
    EXTRACT_LOW_OF_CONCAT,
    "cast.extract_low_of_concat",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract { input, lsb_bits: 0 } => match arena.term(input).kind {
            TermKind::Concat { low, .. } if width(arena, low) == width(arena, id) => Some(low),
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let high = narrow_variable(arena, w, 1);
        let cat = arena.intern(
            unsigned(w + width(arena, high)),
            TermKind::Concat { high, low: l[0] },
        );
        extract(arena, cat, 0, w)
    }]
);
cast_rule!(
    EXTRACT_HIGH_OF_CONCAT,
    "cast.extract_high_of_concat",
    |arena, id| match arena.term(id).kind {
        TermKind::Extract { input, lsb_bits } => match arena.term(input).kind {
            TermKind::Concat { high, low }
                if lsb_bits == width(arena, low) && width(arena, high) == width(arena, id) =>
            {
                Some(high)
            }
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let low = narrow_variable(arena, w, 1);
        let lw = width(arena, low);
        let cat = arena.intern(unsigned(w + lw), TermKind::Concat { high: l[0], low });
        extract(arena, cat, lw, w)
    }]
);
cast_rule!(
    CONCAT_OF_EXTRACTS,
    "cast.concat_of_extracts",
    |arena, id| match arena.term(id).kind {
        TermKind::Concat { high, low } => match (arena.term(high).kind, arena.term(low).kind) {
            (
                TermKind::Extract {
                    input: hx,
                    lsb_bits: hl,
                },
                TermKind::Extract {
                    input: lx,
                    lsb_bits: 0,
                },
            ) if hx == lx
                && hl == width(arena, low)
                && width(arena, high) + width(arena, low) == width(arena, hx) =>
            {
                Some(hx)
            }
            _ => None,
        },
        _ => None,
    },
    &[|arena, w, l| {
        let low_w = w / 2;
        let high = extract(arena, l[0], low_w, w - low_w);
        let low = extract(arena, l[0], 0, low_w);
        arena.intern(unsigned(w), TermKind::Concat { high, low })
    }]
);
