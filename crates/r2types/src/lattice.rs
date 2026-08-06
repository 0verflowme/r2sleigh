use std::collections::BTreeMap;

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
        if sub == sup {
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
            (Type::Ptr(a_inner), Type::Ptr(b_inner)) => Self::is_subtype(arena, *a_inner, *b_inner),
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
                len_ok && Self::is_subtype(arena, *a_elem, *b_elem)
            }
            (Type::Struct(a), Type::Struct(b)) => b.fields.iter().all(|(off, b_field)| {
                a.fields
                    .get(off)
                    .is_some_and(|a_field| Self::is_subtype(arena, a_field.ty, b_field.ty))
            }),
            _ => false,
        }
    }

    pub fn join(arena: &mut TypeArena, a: TypeId, b: TypeId) -> TypeId {
        if Self::is_subtype(arena, a, b) {
            return b;
        }
        if Self::is_subtype(arena, b, a) {
            return a;
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
                let inner = Self::join(arena, a_inner, b_inner);
                arena.ptr(inner)
            }
            (Type::Ptr(inner), Type::Int { .. }) | (Type::Int { .. }, Type::Ptr(inner)) => {
                let top = arena.top();
                let merged = Self::join(arena, inner, top);
                arena.ptr(merged)
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
                let elem = Self::join(arena, a_elem, b_elem);
                let len = if a_len == b_len { a_len } else { None };
                let stride = if a_stride == b_stride { a_stride } else { None };
                arena.array(elem, len, stride)
            }
            (Type::Struct(a_shape), Type::Struct(b_shape)) => {
                let mut merged = StructShape {
                    name: a_shape.name.or(b_shape.name),
                    fields: BTreeMap::new(),
                };

                for (off, a_field) in &a_shape.fields {
                    if let Some(b_field) = b_shape.fields.get(off) {
                        let ty = Self::join(arena, a_field.ty, b_field.ty);
                        let name = a_field.name.clone().or_else(|| b_field.name.clone());
                        merged.fields.insert(*off, StructField { name, ty });
                    } else {
                        merged.fields.insert(*off, a_field.clone());
                    }
                }

                for (off, b_field) in &b_shape.fields {
                    merged.fields.entry(*off).or_insert_with(|| b_field.clone());
                }

                arena.intern(Type::Struct(merged))
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
                let params = a_params
                    .iter()
                    .zip(b_params.iter())
                    .map(|(a_param, b_param)| Self::meet(arena, *a_param, *b_param))
                    .collect();
                let ret = Self::join(arena, a_ret, b_ret);
                arena.function(params, ret, a_var || b_var)
            }
            (Type::UnknownAlias(a_name), Type::UnknownAlias(b_name)) if a_name == b_name => {
                arena.unknown_alias(a_name)
            }
            _ => arena.top(),
        }
    }

    pub fn meet(arena: &mut TypeArena, a: TypeId, b: TypeId) -> TypeId {
        if Self::is_subtype(arena, a, b) {
            return a;
        }
        if Self::is_subtype(arena, b, a) {
            return b;
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
                let inner = Self::meet(arena, a_inner, b_inner);
                arena.ptr(inner)
            }
            (Type::Float { bits: a_bits }, Type::Float { bits: b_bits }) => {
                arena.float(a_bits.min(b_bits))
            }
            _ => arena.bottom(),
        }
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
