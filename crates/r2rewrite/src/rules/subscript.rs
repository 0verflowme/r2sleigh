//! Group H: memory accesses as array elements.
//!
//! A load whose address is a base plus an index scaled by the width it reads
//! is an element of an array of that width at that base, and C spells it
//! `base[index]`. The sum itself is integer arithmetic and says nothing about
//! which operand is the base; the certificates the arena carries do, and the
//! three rules here recognise the three ways a base is known:
//!
//! - `constant_stride`: one operand is a leaf the certificates type as a
//!   pointer. The equivalence needs no certificate -- `Mem[p + i*k]` is
//!   `Mem[p + i*k]` whichever operand is called the base -- so the
//!   certificate only chooses the spelling.
//! - `stack_element[stack_slot]`: the load reaches a stack slot the
//!   certificates place at a frame position, and one operand holds a frame
//!   position. The slot's own address stands as the base, and the
//!   equivalence rests on the two positions, which the rule id names.
//! - `pointer_walk[induction]`: one operand is a pointer carried round a
//!   loop, and the induction facts prove it is the loop's entry pointer plus
//!   the loop's counter times the stride. The rule id names the certificate.
//!
//! Every rule turns one `Load` into one `Subscript`, which is the `Loads`
//! measure, and never adds a node: the base leaves the sum and the index is
//! what remains, divided by the stride. A plain dereference stays a load,
//! because `*p` is not `p[0]`.

use std::collections::BTreeMap;

use r2ssa::{MachineArithmeticOp, MachineType, ObjectId, StackAddressBase, StackAddressRoot};

use super::literal::{lit, unsigned};
use super::{DEFAULT_PROOF_WIDTHS, Measure, Rule, RuleGroup};
use crate::canon::{collect_affine, emit_affine};
use crate::eval::{mask, signed};
use crate::term::{ObjectPlacement, PointerWalk, Term, TermArena, TermId, TermKind};

macro_rules! subscript_rule {
    ($name:ident, $id:literal, $apply:expr, $templates:expr) => {
        pub static $name: Rule = Rule {
            id: $id,
            group: RuleGroup::Subscript,
            decreases: Measure::Loads,
            apply: $apply,
            templates: $templates,
            proof_widths: DEFAULT_PROOF_WIDTHS,
            proof_note: None,
        };
    };
}

/// An address as `sum k_i * t_i + c` at its own width.
struct Affine {
    coefficients: BTreeMap<TermId, u64>,
    constant: u64,
    width: u32,
    ty: MachineType,
}

/// The affine form of an address. An address the arena types as an address
/// rather than an integer -- a leaf that was never expanded -- is one atom.
fn affine_of(arena: &TermArena, address: TermId) -> Option<Affine> {
    let term = arena.term(address);
    let width = term.width_bits();
    if width == 0 || width > 64 {
        return None;
    }
    let mut coefficients = BTreeMap::new();
    let mut constant = 0u64;
    match term.ty {
        MachineType::Integer { .. } => {
            let mut atoms = 0usize;
            collect_affine(
                arena,
                address,
                1,
                width,
                &mut coefficients,
                &mut constant,
                &mut atoms,
            );
        }
        MachineType::Address { .. } => {
            coefficients.insert(address, 1);
        }
        MachineType::Bool { .. } => return None,
    }
    coefficients.retain(|_, k| *k != 0);
    Some(Affine {
        coefficients,
        constant,
        width,
        ty: term.ty,
    })
}

/// The bytes one element of this load occupies.
fn stride_of(term: Term) -> Option<u64> {
    let width = term.width_bits();
    (width > 0 && width.is_multiple_of(8)).then(|| u64::from(width / 8))
}

/// The one atom with a unit coefficient that `is_base` accepts, if exactly
/// one does.
fn unique_base(
    arena: &TermArena,
    affine: &Affine,
    is_base: impl Fn(&TermArena, TermId) -> bool,
) -> Option<TermId> {
    let mut bases = affine
        .coefficients
        .iter()
        .filter(|(term, k)| **k == 1 && is_base(arena, **term))
        .map(|(term, _)| *term);
    let base = bases.next()?;
    bases.next().is_none().then_some(base)
}

/// The index the remaining terms and constant spell, in elements of
/// `stride` bytes.
///
/// Every coefficient and the constant must be a multiple of the stride when
/// read as signed at the address width, so that scaling the index back by
/// the stride returns exactly the address it came from. Something must
/// remain, because a plain dereference is not an element.
fn element_index(arena: &mut TermArena, affine: &Affine, stride: u64) -> Option<TermId> {
    let modulus = mask(affine.width) as u64;
    let divide = |k: u64| -> Option<u64> {
        let stride = i128::from(stride);
        let k = signed(u128::from(k), affine.width);
        (k % stride == 0).then(|| ((k / stride) as u64) & modulus)
    };
    let mut scaled = BTreeMap::new();
    for (&term, &k) in &affine.coefficients {
        scaled.insert(term, divide(k)?);
    }
    let constant = divide(affine.constant)?;
    if scaled.is_empty() && constant == 0 {
        return None;
    }
    Some(emit_affine(
        arena,
        affine.ty,
        affine.width,
        modulus,
        &scaled,
        constant,
    ))
}

fn constant_stride(arena: &mut TermArena, id: TermId) -> Option<TermId> {
    let term = arena.term(id);
    let TermKind::Load { object, address } = term.kind else {
        return None;
    };
    // An object the certificates place has its own address to stand as the
    // base; that is the element rule's business, not this one's.
    if arena.placement(object).is_some() {
        return None;
    }
    let stride = stride_of(term)?;
    let mut affine = affine_of(arena, address)?;
    let base = unique_base(arena, &affine, TermArena::is_pointer)?;
    affine.coefficients.remove(&base);
    let index = element_index(arena, &affine, stride)?;
    Some(arena.intern(term.ty, TermKind::Subscript { base, index }))
}

fn pointer_walk(arena: &mut TermArena, id: TermId) -> Option<TermId> {
    let term = arena.term(id);
    let TermKind::Load { address, .. } = term.kind else {
        return None;
    };
    let stride = stride_of(term)?;
    let mut affine = affine_of(arena, address)?;
    let walked = unique_base(arena, &affine, |arena, term| arena.walk(term).is_some())?;
    let walk = arena.walk(walked)?;
    if walk.stride != stride {
        return None;
    }
    affine.coefficients.remove(&walked);
    // Whatever else the address adds is measured in elements from the
    // counter.
    let index = if affine.coefficients.is_empty() && affine.constant == 0 {
        walk.counter
    } else {
        let rest = element_index(arena, &affine, stride)?;
        let ty = arena.term(walk.counter).ty;
        arena.intern(
            ty,
            TermKind::Arithmetic {
                op: MachineArithmeticOp::Add,
                left: walk.counter,
                right: rest,
            },
        )
    };
    Some(arena.intern(
        term.ty,
        TermKind::Subscript {
            base: walk.init,
            index,
        },
    ))
}

fn stack_element(arena: &mut TermArena, id: TermId) -> Option<TermId> {
    let term = arena.term(id);
    let TermKind::Load { object, address } = term.kind else {
        return None;
    };
    let Some(ObjectPlacement::Stack(slot)) = arena.placement(object) else {
        return None;
    };
    let stride = stride_of(term)?;
    let mut affine = affine_of(arena, address)?;
    let frame = unique_base(arena, &affine, |arena, term| {
        arena
            .stack_root(term)
            .is_some_and(|held| held.base == slot.base)
    })?;
    let held = arena.stack_root(frame)?;
    affine.coefficients.remove(&frame);
    // The operand holds `base + held.offset` and the slot sits at
    // `base + slot.offset`, so the address is the slot's plus the
    // difference plus whatever the constant already added.
    let modulus = mask(affine.width) as u64;
    affine.constant = affine
        .constant
        .wrapping_add(held.offset as u64)
        .wrapping_sub(slot.offset as u64)
        & modulus;
    let index = element_index(arena, &affine, stride)?;
    let base = arena.intern(affine.ty, TermKind::ObjectAddress(object));
    Some(arena.intern(term.ty, TermKind::Subscript { base, index }))
}

/// The object the templates load from.
const OBJECT: ObjectId = ObjectId(7);

fn arith(arena: &mut TermArena, op: MachineArithmeticOp, left: TermId, right: TermId) -> TermId {
    let ty = arena.term(left).ty;
    arena.intern(ty, TermKind::Arithmetic { op, left, right })
}

fn load(arena: &mut TermArena, width_bits: u32, address: TermId) -> TermId {
    arena.intern(
        unsigned(width_bits),
        TermKind::Load {
            object: OBJECT,
            address,
        },
    )
}

/// `-0x20` at width `w`.
fn minus_thirty_two(arena: &mut TermArena, w: u32) -> TermId {
    lit(arena, w, 0u64.wrapping_sub(0x20) & (mask(w) as u64))
}

subscript_rule!(
    CONSTANT_STRIDE,
    "subscript.constant_stride",
    constant_stride,
    &[
        // p + i*4, read at four bytes: p[i].
        |a, w, l| {
            a.declare_pointer(l[0]);
            let four = lit(a, w, 4);
            let scaled = arith(a, MachineArithmeticOp::Multiply, l[1], four);
            let address = arith(a, MachineArithmeticOp::Add, l[0], scaled);
            load(a, 32, address)
        },
        // p + 8, read at four bytes: p[2].
        |a, w, l| {
            a.declare_pointer(l[0]);
            let eight = lit(a, w, 8);
            let address = arith(a, MachineArithmeticOp::Add, l[0], eight);
            load(a, 32, address)
        },
        // p + i + 3, read at one byte: p[i + 3].
        |a, w, l| {
            a.declare_pointer(l[0]);
            let three = lit(a, w, 3);
            let sum = arith(a, MachineArithmeticOp::Add, l[0], l[1]);
            let address = arith(a, MachineArithmeticOp::Add, sum, three);
            load(a, 8, address)
        },
        // p + i*8 - 4, read at four bytes: p[i*2 - 1].
        |a, w, l| {
            a.declare_pointer(l[0]);
            let eight = lit(a, w, 8);
            let four = lit(a, w, 4);
            let scaled = arith(a, MachineArithmeticOp::Multiply, l[1], eight);
            let sum = arith(a, MachineArithmeticOp::Add, l[0], scaled);
            let address = arith(a, MachineArithmeticOp::Subtract, sum, four);
            load(a, 32, address)
        },
    ]
);

subscript_rule!(
    POINTER_WALK,
    "subscript.pointer_walk[induction]",
    pointer_walk,
    &[
        // A pointer walked by four each trip, read at four bytes: init[counter].
        |a, _w, l| {
            a.declare_walk(
                l[0],
                PointerWalk {
                    init: l[1],
                    counter: l[2],
                    stride: 4,
                },
            );
            load(a, 32, l[0])
        },
        // The same pointer plus eight: init[counter + 2].
        |a, w, l| {
            a.declare_walk(
                l[0],
                PointerWalk {
                    init: l[1],
                    counter: l[2],
                    stride: 4,
                },
            );
            let eight = lit(a, w, 8);
            let address = arith(a, MachineArithmeticOp::Add, l[0], eight);
            load(a, 32, address)
        },
    ]
);

subscript_rule!(
    STACK_ELEMENT,
    "subscript.stack_element[stack_slot]",
    stack_element,
    &[
        // A frame pointer, a slot thirty-two below it, a byte at fp - 0x20 + i:
        // slot[i].
        |a, w, l| {
            a.declare_stack_root(
                l[0],
                StackAddressRoot {
                    base: StackAddressBase::FramePointer,
                    offset: 0,
                },
            );
            a.place_object(
                OBJECT,
                ObjectPlacement::Stack(StackAddressRoot {
                    base: StackAddressBase::FramePointer,
                    offset: -0x20,
                }),
            );
            let displacement = minus_thirty_two(a, w);
            let slot = arith(a, MachineArithmeticOp::Add, l[0], displacement);
            let address = arith(a, MachineArithmeticOp::Add, slot, l[1]);
            load(a, 8, address)
        },
        // Four bytes at fp - 0x20 + i*4 + 4: slot[i + 1].
        |a, w, l| {
            a.declare_stack_root(
                l[0],
                StackAddressRoot {
                    base: StackAddressBase::FramePointer,
                    offset: 0,
                },
            );
            a.place_object(
                OBJECT,
                ObjectPlacement::Stack(StackAddressRoot {
                    base: StackAddressBase::FramePointer,
                    offset: -0x20,
                }),
            );
            let displacement = minus_thirty_two(a, w);
            let four = lit(a, w, 4);
            let scaled = arith(a, MachineArithmeticOp::Multiply, l[1], four);
            let slot = arith(a, MachineArithmeticOp::Add, l[0], displacement);
            let element = arith(a, MachineArithmeticOp::Add, slot, scaled);
            let address = arith(a, MachineArithmeticOp::Add, element, four);
            load(a, 32, address)
        },
        // The operand holds a position below the base -- a frame pointer
        // established eight under the entry stack pointer -- and the slot is
        // placed from that base: the difference is part of the displacement.
        |a, w, l| {
            a.declare_stack_root(
                l[0],
                StackAddressRoot {
                    base: StackAddressBase::StackPointer,
                    offset: -8,
                },
            );
            a.place_object(
                OBJECT,
                ObjectPlacement::Stack(StackAddressRoot {
                    base: StackAddressBase::StackPointer,
                    offset: -0x28,
                }),
            );
            let displacement = minus_thirty_two(a, w);
            let slot = arith(a, MachineArithmeticOp::Add, l[0], displacement);
            let address = arith(a, MachineArithmeticOp::Add, slot, l[1]);
            load(a, 8, address)
        },
    ]
);
