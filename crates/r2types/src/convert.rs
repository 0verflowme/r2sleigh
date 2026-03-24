use crate::model::{Signedness, Type, TypeArena, TypeId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CTypeLike {
    Void,
    Bool,
    Int { bits: u32, signedness: Signedness },
    Float(u32),
    Pointer(Box<CTypeLike>),
    Array(Box<CTypeLike>, Option<usize>),
    Struct(String),
    Union(String),
    Enum(String),
    Function,
    Unknown,
}

pub fn to_c_type_like(arena: &TypeArena, ty: TypeId) -> CTypeLike {
    match arena.get(ty) {
        Type::Top | Type::Bottom => CTypeLike::Unknown,
        Type::Bool => CTypeLike::Bool,
        Type::Int { bits, signedness } => CTypeLike::Int {
            bits: *bits,
            signedness: *signedness,
        },
        Type::Float { bits } => CTypeLike::Float(*bits),
        Type::Ptr(inner) => CTypeLike::Pointer(Box::new(to_c_type_like(arena, *inner))),
        Type::Array { elem, len, .. } => {
            CTypeLike::Array(Box::new(to_c_type_like(arena, *elem)), *len)
        }
        Type::Struct(shape) => {
            CTypeLike::Struct(shape.name.clone().unwrap_or_else(|| "anon".to_string()))
        }
        Type::Function { .. } => CTypeLike::Function,
        Type::UnknownAlias(name) if name == "void" => CTypeLike::Void,
        Type::UnknownAlias(name) if name.starts_with("struct ") => {
            CTypeLike::Struct(name.trim_start_matches("struct ").to_string())
        }
        Type::UnknownAlias(name) if name.starts_with("union ") => {
            CTypeLike::Union(name.trim_start_matches("union ").to_string())
        }
        Type::UnknownAlias(name) if name.starts_with("enum ") => {
            CTypeLike::Enum(name.trim_start_matches("enum ").to_string())
        }
        Type::UnknownAlias(_) => CTypeLike::Unknown,
    }
}
