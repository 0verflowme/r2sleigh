use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub type TypeId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Signedness {
    Signed,
    Unsigned,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct StructField {
    pub name: Option<String>,
    pub ty: TypeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct StructShape {
    pub name: Option<String>,
    pub fields: BTreeMap<u64, StructField>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Type {
    Top,
    Bottom,
    Bool,
    Int {
        bits: u32,
        signedness: Signedness,
    },
    Float {
        bits: u32,
    },
    Ptr(TypeId),
    Array {
        elem: TypeId,
        len: Option<usize>,
        stride: Option<u32>,
    },
    Struct(StructShape),
    Function {
        params: Vec<TypeId>,
        ret: TypeId,
        variadic: bool,
    },
    UnknownAlias(String),
}

#[derive(Debug, Clone)]
pub struct TypeArena {
    types: Vec<Type>,
    intern_index: BTreeMap<Type, TypeId>,
    top: TypeId,
    bottom: TypeId,
    bool_ty: TypeId,
}

impl Default for TypeArena {
    fn default() -> Self {
        let mut arena = Self {
            types: Vec::new(),
            intern_index: BTreeMap::new(),
            top: 0,
            bottom: 0,
            bool_ty: 0,
        };
        arena.top = arena.intern(Type::Top);
        arena.bottom = arena.intern(Type::Bottom);
        arena.bool_ty = arena.intern(Type::Bool);
        arena
    }
}

impl TypeArena {
    pub fn top(&self) -> TypeId {
        self.top
    }

    pub fn bottom(&self) -> TypeId {
        self.bottom
    }

    pub fn bool_ty(&self) -> TypeId {
        self.bool_ty
    }

    pub fn intern(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.intern_index.get(&ty).copied() {
            return idx;
        }
        let idx = self.types.len();
        self.types.push(ty.clone());
        self.intern_index.insert(ty, idx);
        idx
    }

    pub fn int(&mut self, bits: u32, signedness: Signedness) -> TypeId {
        self.intern(Type::Int { bits, signedness })
    }

    pub fn float(&mut self, bits: u32) -> TypeId {
        self.intern(Type::Float { bits })
    }

    pub fn ptr(&mut self, inner: TypeId) -> TypeId {
        self.intern(Type::Ptr(inner))
    }

    pub fn array(&mut self, elem: TypeId, len: Option<usize>, stride: Option<u32>) -> TypeId {
        self.intern(Type::Array { elem, len, stride })
    }

    pub fn function(&mut self, params: Vec<TypeId>, ret: TypeId, variadic: bool) -> TypeId {
        self.intern(Type::Function {
            params,
            ret,
            variadic,
        })
    }

    pub fn unknown_alias(&mut self, name: impl Into<String>) -> TypeId {
        self.intern(Type::UnknownAlias(name.into()))
    }

    pub fn struct_named(&mut self, name: impl Into<String>) -> TypeId {
        self.intern(Type::Struct(StructShape {
            name: Some(name.into()),
            fields: BTreeMap::new(),
        }))
    }

    pub fn struct_named_or_existing(&mut self, name: impl Into<String>) -> TypeId {
        let name = name.into();
        let mut best: Option<(usize, usize)> = None;
        for (idx, ty) in self.types.iter().enumerate() {
            let Type::Struct(shape) = ty else {
                continue;
            };
            if shape.name.as_deref() != Some(name.as_str()) {
                continue;
            }
            let field_count = shape.fields.len();
            match best {
                None => best = Some((idx, field_count)),
                Some((_, best_fields)) if field_count > best_fields => {
                    best = Some((idx, field_count))
                }
                _ => {}
            }
        }

        if let Some((idx, _)) = best {
            idx
        } else {
            self.struct_named(name)
        }
    }

    pub fn struct_anon(&mut self) -> TypeId {
        self.intern(Type::Struct(StructShape::default()))
    }

    pub fn struct_with_field(
        &mut self,
        base: TypeId,
        offset: u64,
        field_name: Option<String>,
        field_ty: TypeId,
    ) -> TypeId {
        let mut shape = match self.get(base) {
            Type::Struct(s) => s.clone(),
            _ => StructShape::default(),
        };

        let entry = shape.fields.entry(offset).or_insert(StructField {
            name: field_name.clone(),
            ty: field_ty,
        });

        if entry.name.is_none() {
            entry.name = field_name;
        }
        entry.ty = field_ty;

        self.intern(Type::Struct(shape))
    }

    pub fn get(&self, id: TypeId) -> &Type {
        self.types.get(id).unwrap_or(&Type::Top)
    }

    pub fn iter(&self) -> impl Iterator<Item = (TypeId, &Type)> {
        self.types.iter().enumerate()
    }

    pub fn bits_of(&self, id: TypeId) -> Option<u32> {
        match self.get(id) {
            Type::Bool => Some(1),
            Type::Int { bits, .. } | Type::Float { bits } => Some(*bits),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_reuses_existing_ids() {
        let mut arena = TypeArena::default();
        let i1 = arena.int(32, Signedness::Signed);
        let i2 = arena.int(32, Signedness::Signed);
        assert_eq!(i1, i2);

        let p1 = arena.ptr(i1);
        let p2 = arena.ptr(i2);
        assert_eq!(p1, p2);

        let a1 = arena.array(i1, Some(4), Some(32));
        let a2 = arena.array(i2, Some(4), Some(32));
        assert_eq!(a1, a2);
    }

    #[test]
    fn struct_with_field_reuses_identical_shapes() {
        let mut arena = TypeArena::default();
        let base = arena.struct_named("Reuse");
        let i32_ty = arena.int(32, Signedness::Signed);
        let s1 = arena.struct_with_field(base, 0, Some("first".to_string()), i32_ty);
        let s2 = arena.struct_with_field(base, 0, Some("first".to_string()), i32_ty);
        assert_eq!(s1, s2);
    }

    #[test]
    fn struct_named_or_existing_prefers_existing_richer_shape() {
        let mut arena = TypeArena::default();
        let named = arena.struct_named("Demo");
        let i32_ty = arena.int(32, Signedness::Signed);
        let with_field = arena.struct_with_field(named, 0, Some("first".to_string()), i32_ty);
        let selected = arena.struct_named_or_existing("Demo");
        assert_eq!(selected, with_field);
    }
}
