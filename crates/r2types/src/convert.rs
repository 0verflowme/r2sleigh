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
    Typedef(String),
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
        Type::UnknownAlias(name) => CTypeLike::Typedef(name.clone()),
    }
}

pub fn render_c_type_like(ty: &CTypeLike) -> String {
    match ty {
        CTypeLike::Void => "void".to_string(),
        CTypeLike::Bool => "bool".to_string(),
        CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Signed,
        } => "int8_t".to_string(),
        CTypeLike::Int {
            bits: 16,
            signedness: Signedness::Signed,
        } => "int16_t".to_string(),
        CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Signed,
        } => "int32_t".to_string(),
        CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Signed,
        } => "int64_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Signed | Signedness::Unknown,
        } => format!("int{bits}_t"),
        CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Unsigned,
        } => "uint8_t".to_string(),
        CTypeLike::Int {
            bits: 16,
            signedness: Signedness::Unsigned,
        } => "uint16_t".to_string(),
        CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Unsigned,
        } => "uint32_t".to_string(),
        CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Unsigned,
        } => "uint64_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        } => format!("uint{bits}_t"),
        CTypeLike::Float(32) => "float".to_string(),
        CTypeLike::Float(64) => "double".to_string(),
        CTypeLike::Float(bits) => format!("float{bits}"),
        CTypeLike::Pointer(inner) => format!("{}*", render_c_type_like(inner)),
        CTypeLike::Array(inner, Some(size)) => format!("{}[{}]", render_c_type_like(inner), size),
        CTypeLike::Array(inner, None) => format!("{}[]", render_c_type_like(inner)),
        CTypeLike::Struct(name) => format!("struct {name}"),
        CTypeLike::Union(name) => format!("union {name}"),
        CTypeLike::Enum(name) => format!("enum {name}"),
        CTypeLike::Typedef(name) => name.clone(),
        CTypeLike::Function => "void (*)()".to_string(),
        CTypeLike::Unknown => "/* unknown */".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_c_type_like_preserves_unknown_without_materializing() {
        assert_eq!(render_c_type_like(&CTypeLike::Unknown), "/* unknown */");
        assert_eq!(
            render_c_type_like(&CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
            "/* unknown */*"
        );
    }

    #[test]
    fn render_c_type_like_formats_named_and_integer_types() {
        assert_eq!(
            render_c_type_like(&CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed
            }),
            "int32_t"
        );
        assert_eq!(
            render_c_type_like(&CTypeLike::Struct("Demo".to_string())),
            "struct Demo"
        );
    }
}
