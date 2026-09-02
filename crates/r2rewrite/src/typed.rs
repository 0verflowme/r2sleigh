//! The C type at every boundary of the base arena.
//!
//! A cast in the rendered C is a statement that one type becomes another.
//! The renderer used to make that statement at each site from the text it
//! had just produced -- a name looked like a pointer, a cast was already
//! there -- and seven sites each spelled their own, so a value declared
//! `uint64_t` was converted to `uint64_t` three thousand times over the
//! corpus. This module states the types once, from the arena and the plan,
//! and the renderer converts exactly where two of them meet and differ.
//!
//! Two questions are answered for every node. What the rendering of the node
//! *has* -- [`TypedBoundaries::produced`] -- follows from the operator and
//! the machine type: an unsigned integer for wrapping arithmetic, the
//! promoted `int` where the operands are narrower than `int`, `_Bool` for a
//! comparison, the signed integer of a sign extension. What the node
//! *requires* of each operand -- [`TypedBoundaries::required`] -- is the
//! operator's operand rule: the signedness a comparison, a shift or a
//! division states, the unsigned width every other integer operator works
//! in, the pointee for an address. A leaf's rendering has the type the plan
//! declared the object with, or, for a value rendered in place, the type of
//! the expression that stands for it.
//!
//! Signedness is never re-derived from the C operator that will be spelled.
//! It comes from the `interpretation` at a `Compare`, the `kind` at a
//! `Shift`, and the node kind at a division, which is where the machine
//! states it.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    MachineCastKind, MachineExprId, MachineExprKind, MachineProjection, MachineShiftKind,
    MachineSignedness, MachineType, ValueId,
};
use r2types::{CTypeLike, Signedness};

/// What the renderer's plan says about a value, as far as typing needs it.
///
/// The binding plan lives in the renderer; this is the two answers of it that
/// decide a C type. A bound value renders as a name with a declaration; an
/// inlined value renders as the expression of the arena node that defines it.
pub trait RenderTypes {
    /// The declared type of the object a bound value renders as.
    fn declaration_type(&self, value: ValueId) -> Option<CTypeLike>;

    /// The arena node an inlined value renders as, at each of its readers.
    fn inline_root(&self, value: ValueId) -> Option<MachineExprId>;
}

/// The C type a rendered expression has.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CValue {
    /// An integer constant.
    ///
    /// C types a constant by its value and converts it implicitly, and
    /// exactly, to any integer type it fits. So a constant is not converted
    /// to the type that reads it; it is spelled in that type.
    Constant,
    /// An expression of this type.
    Typed(CTypeLike),
}

impl CValue {
    /// The type, where the expression has one rather than being a constant.
    pub const fn as_type(&self) -> Option<&CTypeLike> {
        match self {
            Self::Constant => None,
            Self::Typed(ty) => Some(ty),
        }
    }
}

/// The C spelling of a machine type: the unsigned integer of an address or
/// an unsigned integer, the signed integer of a signed one, `_Bool` for a
/// boolean, and the limb-backed bitvector for a width C has no scalar for.
pub fn c_type_of(ty: &MachineType) -> CTypeLike {
    match ty {
        MachineType::Bool { .. } => CTypeLike::Bool,
        MachineType::Integer {
            width_bits,
            signedness,
        } => integer(*width_bits, *signedness),
        MachineType::Address { width_bits, .. } => {
            integer(*width_bits, MachineSignedness::Unsigned)
        }
    }
}

fn integer(width_bits: u32, signedness: MachineSignedness) -> CTypeLike {
    match width_bits {
        8 | 16 | 32 | 64 | 128 => CTypeLike::Int {
            bits: width_bits,
            signedness: match signedness {
                MachineSignedness::Unsigned => Signedness::Unsigned,
                MachineSignedness::Signed => Signedness::Signed,
            },
        },
        _ => CTypeLike::BitVector(width_bits),
    }
}

fn unsigned(width_bits: u32) -> CTypeLike {
    integer(width_bits, MachineSignedness::Unsigned)
}

fn signed(width_bits: u32) -> CTypeLike {
    integer(width_bits, MachineSignedness::Signed)
}

/// What C computes an integer operand in.
///
/// Anything narrower than `int` is promoted to `int` before any arithmetic,
/// bitwise, shift or comparison operator sees it, and the result of such an
/// operator has the promoted type, not the operand's. This is the one place
/// a width has to be spelled again -- the narrowing back to the operand's
/// width -- and it is spelled by the boundary that reads the result, from
/// this type, rather than by the operator that produced it.
pub fn promoted(ty: &CTypeLike) -> CTypeLike {
    match ty {
        CTypeLike::Int { bits, .. } if *bits < 32 => CTypeLike::int(32),
        CTypeLike::Bool => CTypeLike::int(32),
        other => other.clone(),
    }
}

/// The C type at every boundary of one function's arena.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypedBoundaries {
    /// What a read of each value renders as, before any use projection.
    values: BTreeMap<ValueId, CValue>,
    /// What the expression each node renders as has.
    produced: BTreeMap<MachineExprId, CValue>,
    /// What each node requires of the operand at each position.
    ///
    /// Keyed by the edge rather than by the operand node: the arena interns
    /// one `Source` leaf per value and type, so one leaf is read by every
    /// operator that wants the value at that type, and a signed comparison
    /// and an unsigned addition of the same value share it while requiring
    /// different things of it.
    required: BTreeMap<(MachineExprId, usize), CTypeLike>,
}

impl TypedBoundaries {
    /// What a read of `value` renders as: the declared type of the object it
    /// is bound to, the type of the expression it is inlined as, or the C
    /// spelling of its machine type where the plan says neither.
    pub fn value_type(&self, value: ValueId) -> Option<&CValue> {
        self.values.get(&value)
    }

    /// What the expression `node` renders as has.
    pub fn produced(&self, node: MachineExprId) -> Option<&CValue> {
        self.produced.get(&node)
    }

    /// What `parent` requires of its operand at `operand`, in the order of
    /// [`MachineExprKind::children`].
    pub fn required(&self, parent: MachineExprId, operand: usize) -> Option<&CTypeLike> {
        self.required.get(&(parent, operand))
    }
}

/// State the C type at every boundary of `projection` under `plan`.
pub fn typed_boundaries(projection: &MachineProjection, plan: &dyn RenderTypes) -> TypedBoundaries {
    let mut builder = Builder {
        projection,
        plan,
        out: TypedBoundaries::default(),
        in_progress: BTreeSet::new(),
    };
    for (id, _) in projection.arena().iter() {
        builder.produced(id);
    }
    for entity in projection.entities() {
        let value = entity.output().value();
        let ty = projection
            .expr(entity.root())
            .map(|expr| *expr.ty())
            .unwrap_or(MachineType::Integer {
                width_bits: entity.output().width_bits(),
                signedness: MachineSignedness::Unsigned,
            });
        builder.value_type(value, &ty);
    }
    builder.out
}

struct Builder<'a> {
    projection: &'a MachineProjection,
    plan: &'a dyn RenderTypes,
    out: TypedBoundaries,
    /// Nodes whose type is being derived, so a value read inside its own
    /// definition -- a call that reads the location it defines -- takes its
    /// machine type instead of recursing forever.
    in_progress: BTreeSet<MachineExprId>,
}

impl Builder<'_> {
    fn width(&self, id: MachineExprId) -> u32 {
        self.projection
            .expr(id)
            .map(|expr| expr.ty().width_bits())
            .unwrap_or(0)
    }

    fn require(&mut self, parent: MachineExprId, operand: usize, ty: CTypeLike) {
        self.out.required.insert((parent, operand), ty);
    }

    fn value_type(&mut self, value: ValueId, fallback: &MachineType) -> CValue {
        if let Some(known) = self.out.values.get(&value) {
            return known.clone();
        }
        let ty = if let Some(declared) = self.plan.declaration_type(value) {
            CValue::Typed(declared)
        } else if let Some(root) = self.plan.inline_root(value) {
            if self.in_progress.contains(&root) {
                CValue::Typed(c_type_of(fallback))
            } else {
                self.produced(root)
            }
        } else {
            CValue::Typed(c_type_of(fallback))
        };
        self.out.values.insert(value, ty.clone());
        ty
    }

    fn produced(&mut self, id: MachineExprId) -> CValue {
        if let Some(known) = self.out.produced.get(&id) {
            return known.clone();
        }
        let Some(expr) = self.projection.expr(id) else {
            return CValue::Typed(CTypeLike::Unknown);
        };
        if !self.in_progress.insert(id) {
            return CValue::Typed(c_type_of(expr.ty()));
        }
        let ty = *expr.ty();
        let kind = expr.kind().clone();
        let produced = self.boundary(id, &ty, &kind);
        self.in_progress.remove(&id);
        self.out.produced.insert(id, produced.clone());
        produced
    }

    /// The operator's operand rule and what it produces, in one place.
    fn boundary(&mut self, id: MachineExprId, ty: &MachineType, kind: &MachineExprKind) -> CValue {
        let own = c_type_of(ty);
        match kind {
            MachineExprKind::Source { binding, .. } => self.value_type(binding.value(), ty),
            MachineExprKind::Constant { .. } => CValue::Constant,
            // A copy converts nothing. Whatever it reads is what it has, and
            // the assignment that writes the copy's object is where the
            // declared type is met.
            MachineExprKind::Copy { input } => {
                let input_type = self.produced(*input);
                let required = input_type.as_type().cloned().unwrap_or(own);
                self.require(id, 0, required);
                input_type
            }
            // Wrapping arithmetic is unsigned arithmetic at the width, and
            // C performs it in the promoted type.
            MachineExprKind::Arithmetic { left, right, .. }
            | MachineExprKind::Bitwise { left, right, .. }
            | MachineExprKind::UnsignedDivide {
                dividend: left,
                divisor: right,
                ..
            }
            | MachineExprKind::UnsignedRemainder {
                dividend: left,
                divisor: right,
                ..
            } => {
                self.produced(*left);
                self.produced(*right);
                self.require(id, 0, own.clone());
                self.require(id, 1, own.clone());
                CValue::Typed(promoted(&own))
            }
            MachineExprKind::Negate { input, .. } | MachineExprKind::BitwiseNot { input } => {
                self.produced(*input);
                self.require(id, 0, own.clone());
                CValue::Typed(promoted(&own))
            }
            // The signedness of a shift is the kind of the shift: an
            // arithmetic right shift is `>>` on a signed operand and nothing
            // else. The count is any integer C accepts, at its own width.
            MachineExprKind::Shift {
                kind, value, count, ..
            } => {
                self.produced(*value);
                self.produced(*count);
                let shifted = match kind {
                    MachineShiftKind::ArithmeticRight => signed(ty.width_bits()),
                    MachineShiftKind::Left | MachineShiftKind::LogicalRight => own,
                };
                self.require(id, 0, shifted.clone());
                let count_width = self.width(*count);
                self.require(id, 1, unsigned(count_width));
                CValue::Typed(promoted(&shifted))
            }
            // The signedness of a comparison is its interpretation, stated
            // at the node; the operands are compared at their own width.
            MachineExprKind::Compare {
                interpretation,
                left,
                right,
                ..
            } => {
                self.produced(*left);
                self.produced(*right);
                let operand = integer(self.width(*left), *interpretation);
                self.require(id, 0, operand.clone());
                self.require(id, 1, operand);
                CValue::Typed(CTypeLike::Bool)
            }
            // A flag is computed by a prelude helper over the unsigned
            // operands, and the helper returns `uint8_t`.
            MachineExprKind::ArithmeticFlag { left, right, .. } => {
                self.produced(*left);
                self.produced(*right);
                let operand = unsigned(self.width(*left));
                self.require(id, 0, operand.clone());
                self.require(id, 1, operand);
                CValue::Typed(CTypeLike::u8())
            }
            // A boolean operator accepts any scalar and yields a truth
            // value.
            MachineExprKind::Boolean { left, right, .. } => {
                self.produced(*left);
                self.produced(*right);
                self.require(id, 0, CTypeLike::Bool);
                self.require(id, 1, CTypeLike::Bool);
                CValue::Typed(CTypeLike::Bool)
            }
            MachineExprKind::BooleanNot { input } => {
                self.produced(*input);
                self.require(id, 0, CTypeLike::Bool);
                CValue::Typed(CTypeLike::Bool)
            }
            // A cast is the conversion. Its operand must have the
            // signedness the conversion extends by -- `(uint64_t)(int32_t)x`
            // sign-extends and `(uint64_t)(uint32_t)x` does not -- and what
            // it produces is its own type.
            MachineExprKind::Cast { kind, input } => {
                self.produced(*input);
                let from = self.width(*input);
                let operand = match kind {
                    MachineCastKind::SignExtend => signed(from),
                    MachineCastKind::ZeroExtend
                    | MachineCastKind::Truncate
                    | MachineCastKind::BitReinterpret
                    | MachineCastKind::IntegerToAddress
                    | MachineCastKind::AddressToInteger => unsigned(from),
                };
                self.require(id, 0, operand);
                CValue::Typed(own)
            }
            MachineExprKind::Extract { input, .. } => {
                self.produced(*input);
                let from = self.width(*input);
                self.require(id, 0, unsigned(from));
                CValue::Typed(own)
            }
            // A concatenation is spelled as a shift and an or over both
            // pieces converted to the whole width, so C promotes it like any
            // other integer operator.
            MachineExprKind::Concat { high, low } => {
                self.produced(*high);
                self.produced(*low);
                let high_width = self.width(*high);
                let low_width = self.width(*low);
                self.require(id, 0, unsigned(high_width));
                self.require(id, 1, unsigned(low_width));
                CValue::Typed(promoted(&own))
            }
            // Both arms of a selection are brought to the machine type, so
            // the selection has it whichever arm is taken.
            MachineExprKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                self.produced(*condition);
                self.produced(*if_true);
                self.produced(*if_false);
                self.require(id, 0, CTypeLike::Bool);
                self.require(id, 1, own.clone());
                self.require(id, 2, own.clone());
                CValue::Typed(own)
            }
            // The address of a read is a pointer to what is read.
            MachineExprKind::MemoryRead { address, .. } => {
                self.produced(*address);
                self.require(id, 0, CTypeLike::ptr(own.clone()));
                CValue::Typed(own)
            }
            // `__builtin_popcountll` takes an unsigned long long and returns
            // an `int`.
            MachineExprKind::PopulationCount { input } => {
                self.produced(*input);
                self.require(id, 0, CTypeLike::u64());
                CValue::Typed(CTypeLike::int(32))
            }
            // A merge is not an expression; each of its edges is a copy,
            // typed as one.
            MachineExprKind::Phi { inputs } => {
                for input in inputs.iter() {
                    self.produced(*input);
                }
                CValue::Typed(own)
            }
        }
    }
}
