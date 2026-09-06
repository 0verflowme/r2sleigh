//! Ordering and combination of types, over *regular trees*.
//!
//! A source type graph is cyclic in ordinary C: zlib declares
//! `z_stream.state : internal_state *` and `inflate_state.strm : z_streamp`, so
//! the two refer to each other. Read as finite trees those types have no finite
//! representation, and the structural recursion this file used to do had no
//! reason to stop -- `join(Ptr a, Ptr b) = Ptr(join a b)` on a cyclic pair walks
//! forever, interning one fresh node per step. The ascending chain
//!
//! ```text
//! Ptr(Bottom) < Ptr(Struct{.. Ptr(Bottom) ..}) < Ptr(Struct{.. Ptr(Struct{..}) ..}) < ..
//! ```
//!
//! is strictly increasing and infinite, so the lattice does not satisfy the
//! ascending chain condition and the solver's Kleene iteration cannot converge.
//! Measured: one 126-byte, 11-block zlib function -- the one that walks
//! `strm->state->strm` -- did not finish in ten minutes, and the arena grew
//! until the kernel killed the process.
//!
//! So a type here is a regular tree: an infinite unfolding with finitely many
//! distinct subtrees, held as a finite graph that may contain back edges. Two
//! consequences, and they are what makes this terminate.
//!
//! `is_subtype` is coinductive. It carries the set of pairs it has already
//! assumed related and answers `true` on meeting one again, which is the
//! greatest-fixpoint reading of the rule rather than the least. Termination is
//! immediate: the assumption set only grows and is bounded by the square of the
//! carrier, so the recursion is O(n^2). This is the Amadio-Cardelli algorithm.
//!
//! `join` and `meet` are product constructions. A state of the result is a
//! *pair* of input states, each pair is built once and memoised, and the id is
//! reserved before its children are computed so a back edge has something to
//! point at. The result therefore has at most |A|x|B| nodes, again by
//! construction rather than by any depth parameter.
//!
//! One thing the construction cannot do is invent recursion: a cycle in a
//! product exists only where both components return to a state they have
//! already visited, so every cycle in the result is a cycle in an operand. The
//! check that says so is kept anyway, and refuses that one value rather than
//! asserting a recursive type no declaration backs.

use std::collections::{BTreeMap, BTreeSet};

use crate::model::{Signedness, StructField, StructShape, Type, TypeArena, TypeId};

#[derive(Debug, Default, Clone, Copy)]
pub struct TypeLattice;

impl TypeLattice {
    fn meet_integer_shape(
        a_bits: u32,
        a_sign: Signedness,
        b_bits: u32,
        b_sign: Signedness,
    ) -> Option<(u32, Signedness)> {
        let bits = a_bits.min(b_bits);
        (a_sign == b_sign).then_some((bits, a_sign))
    }

    pub fn is_subtype(arena: &TypeArena, sub: TypeId, sup: TypeId) -> bool {
        let mut assumed = BTreeSet::new();
        Self::is_subtype_coinductive(arena, sub, sup, &mut assumed)
    }

    /// `sub <= sup` read as a greatest fixpoint.
    ///
    /// `assumed` holds the pairs this derivation has already taken as related.
    /// Meeting one again means the obligation has come back to itself, which
    /// under the coinductive reading is discharged rather than infinite -- and
    /// it is what stops a cyclic type from being walked forever. The set only
    /// grows and is bounded by the carrier squared, so this is O(n^2).
    fn is_subtype_coinductive(
        arena: &TypeArena,
        sub: TypeId,
        sup: TypeId,
        assumed: &mut BTreeSet<(TypeId, TypeId)>,
    ) -> bool {
        if sub == sup {
            return true;
        }
        if !assumed.insert((sub, sup)) {
            return true;
        }

        match (arena.get(sub), arena.get(sup)) {
            (_, Type::Top) => true,
            (Type::Bottom, _) => true,
            (Type::Bool, Type::Int { bits, .. }) => *bits >= 1,
            (
                Type::Int {
                    bits: a_bits,
                    signedness: a_sign,
                },
                Type::Int {
                    bits: b_bits,
                    signedness: b_sign,
                },
            ) => {
                a_bits <= b_bits
                    && matches!(
                        (a_sign, b_sign),
                        (Signedness::Signed, Signedness::Signed)
                            | (Signedness::Unsigned, Signedness::Unsigned)
                            | (_, Signedness::Unknown)
                    )
            }
            (Type::Float { bits: a_bits }, Type::Float { bits: b_bits }) => a_bits <= b_bits,
            (Type::Ptr(a_inner), Type::Ptr(b_inner)) => {
                Self::is_subtype_coinductive(arena, *a_inner, *b_inner, assumed)
            }
            (
                Type::Array {
                    elem: a_elem,
                    len: a_len,
                    ..
                },
                Type::Array {
                    elem: b_elem,
                    len: b_len,
                    ..
                },
            ) => {
                let len_ok = match (a_len, b_len) {
                    (_, None) => true,
                    (Some(x), Some(y)) => x == y,
                    (None, Some(_)) => false,
                };
                len_ok && Self::is_subtype_coinductive(arena, *a_elem, *b_elem, assumed)
            }
            (Type::Struct(a), Type::Struct(b)) => b.fields.iter().all(|(off, b_field)| {
                a.fields.get(off).is_some_and(|a_field| {
                    Self::is_subtype_coinductive(arena, a_field.ty, b_field.ty, assumed)
                })
            }),
            _ => false,
        }
    }

    /// The least upper bound, or `Top` where the construction refuses.
    pub fn join(arena: &mut TypeArena, a: TypeId, b: TypeId) -> TypeId {
        Self::try_join(arena, a, b).unwrap_or_else(|| arena.top())
    }

    /// The least upper bound, refusing rather than asserting invented recursion.
    ///
    /// `None` says the result would have contained a cycle that neither operand
    /// contains. A product cycle needs both components to return to a state
    /// they have already visited, so this cannot happen by construction; the
    /// check states the invariant and keeps the refusal per value if it is ever
    /// wrong, instead of emitting a recursive type no declaration backs.
    pub fn try_join(arena: &mut TypeArena, a: TypeId, b: TypeId) -> Option<TypeId> {
        let mut state = ProductState::default();
        let id = Self::join_pair(arena, a, b, &mut state);
        state.settle(arena).then_some(id)
    }

    fn join_pair(arena: &mut TypeArena, a: TypeId, b: TypeId, state: &mut ProductState) -> TypeId {
        if Self::is_subtype(arena, a, b) {
            return b;
        }
        if Self::is_subtype(arena, b, a) {
            return a;
        }
        if let Some(existing) = state.pairs.get(&(a, b)).copied() {
            // The derivation has come back to a pair it is still building, so
            // this edge is the cycle. Pointing at the reserved id closes it.
            state.closed.insert(existing);
            return existing;
        }

        match (arena.get(a).clone(), arena.get(b).clone()) {
            (Type::Bottom, other) | (other, Type::Bottom) => arena.intern(other),
            (Type::Top, _) | (_, Type::Top) => arena.top(),
            (Type::Bool, Type::Bool) => arena.bool_ty(),
            (
                Type::Int {
                    bits: a_bits,
                    signedness: a_sign,
                },
                Type::Int {
                    bits: b_bits,
                    signedness: b_sign,
                },
            ) => {
                let bits = a_bits.max(b_bits);
                let signedness = if a_sign == b_sign {
                    a_sign
                } else {
                    Signedness::Unknown
                };
                arena.int(bits, signedness)
            }
            (Type::Bool, Type::Int { bits, signedness })
            | (Type::Int { bits, signedness }, Type::Bool) => arena.int(bits.max(1), signedness),
            (Type::Float { bits: a_bits }, Type::Float { bits: b_bits }) => {
                arena.float(a_bits.max(b_bits))
            }
            (Type::Ptr(a_inner), Type::Ptr(b_inner)) => {
                let slot = state.open(arena, a, b);
                let inner = Self::join_pair(arena, a_inner, b_inner, state);
                state.close(arena, slot, Type::Ptr(inner), a, b)
            }
            (Type::Ptr(inner), Type::Int { .. }) | (Type::Int { .. }, Type::Ptr(inner)) => {
                let top = arena.top();
                let slot = state.open(arena, a, b);
                let merged = Self::join_pair(arena, inner, top, state);
                state.close(arena, slot, Type::Ptr(merged), a, b)
            }
            (
                Type::Array {
                    elem: a_elem,
                    len: a_len,
                    stride: a_stride,
                },
                Type::Array {
                    elem: b_elem,
                    len: b_len,
                    stride: b_stride,
                },
            ) => {
                let slot = state.open(arena, a, b);
                let elem = Self::join_pair(arena, a_elem, b_elem, state);
                let len = if a_len == b_len { a_len } else { None };
                let stride = if a_stride == b_stride { a_stride } else { None };
                state.close(arena, slot, Type::Array { elem, len, stride }, a, b)
            }
            (Type::Struct(a_shape), Type::Struct(b_shape)) => {
                let slot = state.open(arena, a, b);
                let mut merged = StructShape {
                    name: a_shape.name.clone().or_else(|| b_shape.name.clone()),
                    fields: BTreeMap::new(),
                };
                for (off, a_field) in &a_shape.fields {
                    if let Some(b_field) = b_shape.fields.get(off) {
                        let ty = Self::join_pair(arena, a_field.ty, b_field.ty, state);
                        let name = a_field.name.clone().or_else(|| b_field.name.clone());
                        merged.fields.insert(*off, StructField { name, ty });
                    } else {
                        merged.fields.insert(*off, a_field.clone());
                    }
                }
                for (off, b_field) in &b_shape.fields {
                    merged.fields.entry(*off).or_insert_with(|| b_field.clone());
                }
                state.close(arena, slot, Type::Struct(merged), a, b)
            }
            (
                Type::Function {
                    params: a_params,
                    ret: a_ret,
                    variadic: a_var,
                },
                Type::Function {
                    params: b_params,
                    ret: b_ret,
                    variadic: b_var,
                },
            ) if a_params.len() == b_params.len() => {
                let slot = state.open(arena, a, b);
                let params = a_params
                    .iter()
                    .zip(b_params.iter())
                    .map(|(a_param, b_param)| Self::meet_pair(arena, *a_param, *b_param, state))
                    .collect();
                let ret = Self::join_pair(arena, a_ret, b_ret, state);
                state.close(
                    arena,
                    slot,
                    Type::Function {
                        params,
                        ret,
                        variadic: a_var || b_var,
                    },
                    a,
                    b,
                )
            }
            (Type::UnknownAlias(a_name), Type::UnknownAlias(b_name)) if a_name == b_name => {
                arena.unknown_alias(&a_name)
            }
            _ => arena.top(),
        }
    }

    /// The greatest lower bound, or `Bottom` where the construction refuses.
    pub fn meet(arena: &mut TypeArena, a: TypeId, b: TypeId) -> TypeId {
        Self::try_meet(arena, a, b).unwrap_or_else(|| arena.bottom())
    }

    /// The greatest lower bound, refusing rather than inventing recursion.
    pub fn try_meet(arena: &mut TypeArena, a: TypeId, b: TypeId) -> Option<TypeId> {
        let mut state = ProductState::default();
        let id = Self::meet_pair(arena, a, b, &mut state);
        state.settle(arena).then_some(id)
    }

    /// Whether the graph rooted at `id` reaches itself.
    ///
    /// Asked only when a product actually closed a cycle, which is rare, so the
    /// walk is paid for by the case that needs it rather than by every join.
    fn is_cyclic(arena: &TypeArena, id: TypeId) -> bool {
        fn walk(
            arena: &TypeArena,
            id: TypeId,
            path: &mut BTreeSet<TypeId>,
            done: &mut BTreeSet<TypeId>,
        ) -> bool {
            if path.contains(&id) {
                return true;
            }
            if !done.insert(id) {
                return false;
            }
            path.insert(id);
            let children: Vec<TypeId> = match arena.get(id) {
                Type::Ptr(inner) => vec![*inner],
                Type::Array { elem, .. } => vec![*elem],
                Type::Struct(shape) => shape.fields.values().map(|field| field.ty).collect(),
                Type::Function { params, ret, .. } => params
                    .iter()
                    .copied()
                    .chain(std::iter::once(*ret))
                    .collect(),
                _ => Vec::new(),
            };
            let cyclic = children
                .into_iter()
                .any(|child| walk(arena, child, path, done));
            path.remove(&id);
            cyclic
        }
        let mut path = BTreeSet::new();
        let mut done = BTreeSet::new();
        walk(arena, id, &mut path, &mut done)
    }

    fn meet_pair(arena: &mut TypeArena, a: TypeId, b: TypeId, state: &mut ProductState) -> TypeId {
        if Self::is_subtype(arena, a, b) {
            return a;
        }
        if Self::is_subtype(arena, b, a) {
            return b;
        }
        if let Some(existing) = state.pairs.get(&(a, b)).copied() {
            state.closed.insert(existing);
            return existing;
        }

        match (arena.get(a).clone(), arena.get(b).clone()) {
            (Type::Top, other) | (other, Type::Top) => arena.intern(other),
            (Type::Bottom, _) | (_, Type::Bottom) => arena.bottom(),
            (
                Type::Int {
                    bits: a_bits,
                    signedness: a_sign,
                },
                Type::Int {
                    bits: b_bits,
                    signedness: b_sign,
                },
            ) => {
                if let Some((bits, signedness)) =
                    Self::meet_integer_shape(a_bits, a_sign, b_bits, b_sign)
                {
                    arena.int(bits, signedness)
                } else {
                    arena.bottom()
                }
            }
            (Type::Ptr(a_inner), Type::Ptr(b_inner)) => {
                let slot = state.open(arena, a, b);
                let inner = Self::meet_pair(arena, a_inner, b_inner, state);
                state.close(arena, slot, Type::Ptr(inner), a, b)
            }
            (Type::Float { bits: a_bits }, Type::Float { bits: b_bits }) => {
                arena.float(a_bits.min(b_bits))
            }
            _ => arena.bottom(),
        }
    }
}

/// The pair table a product construction is built from.
///
/// `pairs` maps a pair of input states to the id standing for it, so each pair
/// is built once and the whole construction is bounded by |A|x|B|. `open`
/// reserves that id before the children are known, which is what gives a back
/// edge something to point at; `closed` records the ids something actually
/// pointed back at, so the ones nothing did can be interned normally and keep
/// the id-equality that the rest of the solver relies on for acyclic types.
#[derive(Debug, Default)]
struct ProductState {
    pairs: BTreeMap<(TypeId, TypeId), TypeId>,
    slots: BTreeMap<TypeId, (TypeId, TypeId)>,
    closed: BTreeSet<TypeId>,
}

impl ProductState {
    /// Reserve the id for a pair before its children are known.
    fn open(&mut self, arena: &mut TypeArena, a: TypeId, b: TypeId) -> TypeId {
        let slot = arena.reserve();
        self.pairs.insert((a, b), slot);
        self.slots.insert(slot, (a, b));
        slot
    }

    /// Give a reserved id its shape, or intern the shape if nothing pointed back.
    ///
    /// Only a node some descendant actually closed onto has to keep its
    /// reserved identity; every other node is acyclic and is interned, so two
    /// equal acyclic types keep one id and the reserved slot is left as an
    /// unreferenced hole. Without this every join would mint fresh ids for
    /// ordinary types and the identity the rest of the solver compares on would
    /// stop meaning anything.
    fn close(
        &mut self,
        arena: &mut TypeArena,
        slot: TypeId,
        ty: Type,
        a: TypeId,
        b: TypeId,
    ) -> TypeId {
        if self.closed.contains(&slot) {
            arena.define(slot, ty);
            return slot;
        }
        self.slots.remove(&slot);
        let id = arena.intern(ty);
        self.pairs.insert((a, b), id);
        id
    }

    /// Whether every cycle this construction created was already in an operand.
    fn settle(&self, arena: &TypeArena) -> bool {
        self.closed.iter().all(|slot| {
            self.slots.get(slot).is_none_or(|(a, b)| {
                TypeLattice::is_cyclic(arena, *a) || TypeLattice::is_cyclic(arena, *b)
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_signed_unsigned_becomes_unknown() {
        let mut arena = TypeArena::default();
        let signed = arena.int(32, Signedness::Signed);
        let unsigned = arena.int(32, Signedness::Unsigned);
        let joined = TypeLattice::join(&mut arena, signed, unsigned);
        assert_eq!(
            arena.get(joined),
            &Type::Int {
                bits: 32,
                signedness: Signedness::Unknown
            }
        );
    }

    #[test]
    fn meet_signed_unsigned_is_bottom() {
        let mut arena = TypeArena::default();
        let signed = arena.int(32, Signedness::Signed);
        let unsigned = arena.int(32, Signedness::Unsigned);
        let meet = TypeLattice::meet(&mut arena, signed, unsigned);
        assert_eq!(meet, arena.bottom());
    }

    #[test]
    fn struct_join_merges_fields() {
        let mut arena = TypeArena::default();
        let i32_ty = arena.int(32, Signedness::Signed);
        let u64_ty = arena.int(64, Signedness::Unsigned);

        let s1_base = arena.struct_anon();
        let s2_base = arena.struct_anon();
        let s1 = arena.struct_with_field(s1_base, 0, Some("a".to_string()), i32_ty);
        let s2 = arena.struct_with_field(s2_base, 8, Some("b".to_string()), u64_ty);

        let joined = TypeLattice::join(&mut arena, s1, s2);
        let Type::Struct(shape) = arena.get(joined) else {
            panic!("joined type should be a struct");
        };
        assert_eq!(shape.fields.len(), 2);
    }

    #[test]
    fn meet_signed_unsigned_with_different_widths_is_bottom() {
        let mut arena = TypeArena::default();
        let a = arena.int(64, Signedness::Signed);
        let b = arena.int(32, Signedness::Unsigned);
        let met = TypeLattice::meet(&mut arena, a, b);
        assert_eq!(met, arena.bottom());
    }

    #[test]
    fn meet_pointer_meets_inner_types() {
        let mut arena = TypeArena::default();
        let i64_ty = arena.int(64, Signedness::Signed);
        let i32_ty = arena.int(32, Signedness::Signed);
        let p1 = arena.ptr(i64_ty);
        let p2 = arena.ptr(i32_ty);
        let met = TypeLattice::meet(&mut arena, p1, p2);
        let Type::Ptr(inner) = arena.get(met) else {
            panic!("meet should return pointer");
        };
        assert_eq!(
            arena.get(*inner),
            &Type::Int {
                bits: 32,
                signedness: Signedness::Signed
            }
        );
    }

    #[test]
    fn meet_incompatible_types_goes_bottom() {
        let mut arena = TypeArena::default();
        let i32_ty = arena.int(32, Signedness::Signed);
        let f64_ty = arena.float(64);
        let met = TypeLattice::meet(&mut arena, i32_ty, f64_ty);
        assert_eq!(arena.get(met), &Type::Bottom);
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    fn pick_signedness(tag: u8) -> Signedness {
        match tag % 3 {
            0 => Signedness::Signed,
            1 => Signedness::Unsigned,
            _ => Signedness::Unknown,
        }
    }

    #[kani::proof]
    fn integer_meet_shape_is_sound() {
        let a_bits: u32 = kani::any();
        let b_bits: u32 = kani::any();
        let a_sign = pick_signedness(kani::any());
        let b_sign = pick_signedness(kani::any());

        let result = TypeLattice::meet_integer_shape(a_bits, a_sign, b_bits, b_sign);

        if a_sign == b_sign {
            match result {
                Some((bits, signedness)) => {
                    assert_eq!(bits, a_bits.min(b_bits));
                    assert_eq!(signedness, a_sign);
                    assert_eq!(signedness, b_sign);
                }
                None => unreachable!("equal signedness must produce an integer meet"),
            }
        } else {
            assert!(result.is_none());
        }
    }
}
