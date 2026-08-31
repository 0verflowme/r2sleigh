use crate::model::{Signedness, Type, TypeArena, TypeId};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum CTypeLike {
    Void,
    Bool,
    Int {
        bits: u32,
        signedness: Signedness,
    },
    Float(u32),
    /// An exact machine bitvector wider than, or not expressible in, C's native
    /// integer domain.
    ///
    /// Distinct from `Int` on purpose: the external C prelude owns the limb
    /// representation, and keeping it apart is what stops ordinary C arithmetic
    /// and casts being emitted for a value the language has no scalar for.
    BitVector(u32),
    Pointer(Box<CTypeLike>),
    Array(Box<CTypeLike>, Option<usize>),
    Struct(String),
    Union(String),
    Enum(String),
    Typedef(String),
    /// A function type, with the signature it was recovered with.
    ///
    /// This carried no signature until the two type models were folded
    /// together: `r2dec`'s `CType::Function` had a return type and parameters,
    /// and every trip through here erased them.
    Function {
        ret: Box<CTypeLike>,
        params: Vec<CTypeLike>,
    },
    Unknown,
}

impl std::fmt::Display for CTypeLike {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&render_c_type_like(self))
    }
}

impl CTypeLike {
    /// A signed integer of the given width.
    pub const fn int(bits: u32) -> Self {
        CTypeLike::Int {
            bits,
            signedness: Signedness::Signed,
        }
    }

    /// An unsigned integer of the given width.
    pub const fn uint(bits: u32) -> Self {
        CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        }
    }

    /// A signed 8-bit integer.
    pub const fn i8() -> Self {
        Self::int(8)
    }

    /// A signed 16-bit integer.
    pub const fn i16() -> Self {
        Self::int(16)
    }

    /// A signed 32-bit integer.
    pub const fn i32() -> Self {
        Self::int(32)
    }

    /// A signed 64-bit integer.
    pub const fn i64() -> Self {
        Self::int(64)
    }

    /// A unsigned 8-bit integer.
    pub const fn u8() -> Self {
        Self::uint(8)
    }

    /// A unsigned 16-bit integer.
    pub const fn u16() -> Self {
        Self::uint(16)
    }

    /// A unsigned 32-bit integer.
    pub const fn u32() -> Self {
        Self::uint(32)
    }

    /// A unsigned 64-bit integer.
    pub const fn u64() -> Self {
        Self::uint(64)
    }

    /// Exact unsigned machine storage of the given width.
    ///
    /// C has scalar integer spellings through 128 bits in the supported
    /// compiler contract. Wider or unaligned carriers use the limb-backed
    /// external prelude instead of inventing names such as `uint256_t`.
    pub const fn machine_bits(bits: u32) -> Self {
        match bits {
            8 | 16 | 32 | 64 | 128 => Self::uint(bits),
            _ => CTypeLike::BitVector(bits),
        }
    }

    /// A pointer to the given type.
    pub fn ptr(inner: CTypeLike) -> Self {
        CTypeLike::Pointer(Box::new(inner))
    }

    /// A pointer to void.
    pub fn void_ptr() -> Self {
        Self::ptr(CTypeLike::Void)
    }

    /// The width in bits, where the type has one.
    pub fn bits(&self, ptr_bits: u32) -> Option<u32> {
        match self {
            CTypeLike::Bool => Some(1),
            CTypeLike::Int { bits, .. } | CTypeLike::BitVector(bits) | CTypeLike::Float(bits) => {
                Some(*bits)
            }
            CTypeLike::Pointer(_) => Some(ptr_bits),
            _ => None,
        }
    }

    /// Whether this is a signed integer.
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            CTypeLike::Int {
                signedness: Signedness::Signed,
                ..
            }
        )
    }

    /// Whether this is an integer, boolean included.
    pub fn is_integer(&self) -> bool {
        matches!(self, CTypeLike::Int { .. } | CTypeLike::Bool)
    }

    /// Whether this is a pointer to anything.
    pub fn is_pointer(&self) -> bool {
        matches!(self, CTypeLike::Pointer(_))
    }

    /// Whether this is `void *`.
    pub fn is_void_pointer(&self) -> bool {
        matches!(self, CTypeLike::Pointer(inner) if matches!(**inner, CTypeLike::Void))
    }
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
        Type::Function { params, ret, .. } => CTypeLike::Function {
            ret: Box::new(to_c_type_like(arena, *ret)),
            params: params
                .iter()
                .map(|param| to_c_type_like(arena, *param))
                .collect(),
        },
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
            bits: 128,
            signedness: Signedness::Signed | Signedness::Unknown,
        } => "__int128_t".to_string(),
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
        // A 128-bit integer has exactly one spelling a C compiler accepts, and
        // `uint128_t` is not it. `r2dec` already knew this for the C it emits;
        // this renderer feeds radare2's type database, which had been getting a
        // type name no compiler would take.
        CTypeLike::Int {
            bits: 128,
            signedness: Signedness::Unsigned,
        } => "__uint128_t".to_string(),
        CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        } => format!("uint{bits}_t"),
        CTypeLike::Float(32) => "float".to_string(),
        CTypeLike::Float(64) => "double".to_string(),
        CTypeLike::Float(bits) => format!("float{bits}"),
        CTypeLike::BitVector(bits) => format!("struct r2sleigh_bits_{bits}"),
        CTypeLike::Pointer(inner) => format!("{}*", render_c_type_like(inner)),
        CTypeLike::Array(inner, Some(size)) => format!("{}[{}]", render_c_type_like(inner), size),
        CTypeLike::Array(inner, None) => format!("{}[]", render_c_type_like(inner)),
        CTypeLike::Struct(name) => format!("struct {name}"),
        CTypeLike::Union(name) => format!("union {name}"),
        CTypeLike::Enum(name) => format!("enum {name}"),
        CTypeLike::Typedef(name) => name.clone(),
        CTypeLike::Function { ret, params } => {
            let params = if params.is_empty() {
                String::new()
            } else {
                params
                    .iter()
                    .map(render_c_type_like)
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            format!("{}(*)({params})", render_c_type_like(ret))
        }
        CTypeLike::Unknown => "/* unknown */".to_string(),
    }
}

/// Parse a C type spelling into the model.
///
/// This is the inverse of `render_c_type_like`, and it exists because the tree
/// had no canonical one: six separate parsers had grown at the seams where a
/// type had been stored as a rendered string, and they did not agree with each
/// other. A spelling is data arriving from radare2's type database, from DWARF,
/// or from our own renderer, so the parser has to accept more spellings than
/// the renderer emits -- `unsigned int` as well as `uint32_t`, `char *` as well
/// as `char*`.
///
/// `ptr_bits` is a parameter rather than an assumption because the width of
/// `long` and `size_t` is a property of the target, and guessing it is how two
/// of the previous parsers came to disagree.
pub fn parse_c_type_like(spelling: &str, ptr_bits: u32) -> CTypeLike {
    let normalized = crate::external::normalize_type_spelling(spelling);
    parse_normalized(normalized.trim(), ptr_bits)
}

fn parse_normalized(spelling: &str, ptr_bits: u32) -> CTypeLike {
    let spelling = spelling.trim();
    if spelling.is_empty() || spelling == "/* unknown */" {
        return CTypeLike::Unknown;
    }
    if let Some(inner) = spelling.strip_suffix('*') {
        return CTypeLike::Pointer(Box::new(parse_normalized(inner, ptr_bits)));
    }
    if let Some(open) = spelling.rfind('[')
        && spelling.ends_with(']')
    {
        let len = spelling[open + 1..spelling.len() - 1].trim();
        let len = if len.is_empty() {
            None
        } else {
            len.parse::<usize>().ok()
        };
        return CTypeLike::Array(Box::new(parse_normalized(&spelling[..open], ptr_bits)), len);
    }
    if let Some(bits) = spelling
        .strip_prefix("struct r2sleigh_bits_")
        .and_then(|bits| bits.parse::<u32>().ok())
    {
        return CTypeLike::BitVector(bits);
    }
    for (keyword, build) in [
        ("struct ", CTypeLike::Struct as fn(String) -> CTypeLike),
        ("union ", CTypeLike::Union as fn(String) -> CTypeLike),
        ("enum ", CTypeLike::Enum as fn(String) -> CTypeLike),
    ] {
        if let Some(name) = spelling.strip_prefix(keyword) {
            return build(name.trim().to_string());
        }
    }
    if spelling.contains("(*)") {
        // A spelling reached here only says it is a function pointer; the
        // signature it was written with is not recovered from the text.
        return CTypeLike::Function {
            ret: Box::new(CTypeLike::Unknown),
            params: Vec::new(),
        };
    }

    let collapsed = spelling.split_whitespace().collect::<Vec<_>>().join(" ");
    if let Some(width) = fixed_width_integer(&collapsed) {
        return width;
    }
    match collapsed.as_str() {
        "void" => CTypeLike::Void,
        "bool" | "_Bool" => CTypeLike::Bool,
        "float" => CTypeLike::Float(32),
        "double" | "long double" => CTypeLike::Float(64),
        _ => match named_integer_bits(&collapsed, ptr_bits) {
            Some((bits, signedness)) => CTypeLike::Int { bits, signedness },
            None => CTypeLike::Typedef(collapsed),
        },
    }
}

/// The `intN_t` family, including the `__int128_t` spelling that is the only
/// one a C compiler accepts for that width.
fn fixed_width_integer(spelling: &str) -> Option<CTypeLike> {
    let (rest, signedness) = match spelling
        .strip_prefix("__")
        .unwrap_or(spelling)
        .strip_prefix('u')
    {
        Some(rest) => (rest, Signedness::Unsigned),
        None => (
            spelling.strip_prefix("__").unwrap_or(spelling),
            Signedness::Signed,
        ),
    };
    let bits = rest.strip_prefix("int")?.strip_suffix("_t")?;
    Some(CTypeLike::Int {
        bits: bits.parse::<u32>().ok()?,
        signedness,
    })
}

/// The spellings whose width depends on the target, plus the plain C keywords.
fn named_integer_bits(spelling: &str, ptr_bits: u32) -> Option<(u32, Signedness)> {
    let (base, signedness) = match spelling.strip_prefix("unsigned") {
        Some(rest) => (rest.trim(), Signedness::Unsigned),
        None => match spelling.strip_prefix("signed") {
            Some(rest) => (rest.trim(), Signedness::Signed),
            None => (spelling, Signedness::Signed),
        },
    };
    let base = if base.is_empty() { "int" } else { base };
    let bits = match base {
        "char" => 8,
        "short" | "short int" => 16,
        "int" => 32,
        "long" | "long int" | "size_t" | "ssize_t" | "uintptr_t" | "intptr_t" | "ptrdiff_t" => {
            ptr_bits
        }
        "long long" | "long long int" => 64,
        _ => return None,
    };
    let signedness = match base {
        "size_t" | "uintptr_t" => Signedness::Unsigned,
        "ssize_t" | "intptr_t" | "ptrdiff_t" => Signedness::Signed,
        _ => signedness,
    };
    Some((bits, signedness))
}

#[cfg(test)]
mod tests {
    use super::*;
    /// radare2's own spellings, which arrive dotted and unspaced.
    ///
    /// These are what `canonicalize_writeback_apply_type_name` was rewriting by
    /// hand, searching a rendered string for the first `*` and inserting a
    /// space in front of it. Parsing reaches the same type from every spelling,
    /// so the normalisation belongs at the point the spelling arrives rather
    /// than at each point one is consumed.
    #[test]
    fn radare_dotted_spellings_reach_the_same_type() {
        let foo = CTypeLike::Pointer(Box::new(CTypeLike::Struct("Foo".to_string())));
        for spelling in ["struct.Foo*", "struct.Foo *", "struct Foo*", "struct Foo *"] {
            assert_eq!(parse_c_type_like(spelling, 64), foo, "{spelling}");
        }
        assert_eq!(
            parse_c_type_like("union.Bar*", 64),
            CTypeLike::Pointer(Box::new(CTypeLike::Union("Bar".to_string())))
        );
        assert_eq!(
            parse_c_type_like("type.Foo", 64),
            CTypeLike::Typedef("Foo".to_string())
        );
    }

    /// Every type the renderer can emit, rendered and parsed back.
    ///
    /// This is the property the seam depends on: a type that survives a trip
    /// through its own spelling is one that can safely be stored as a spelling
    /// at a boundary that needs one. Any case that fails is a place where a
    /// string is lossy and the type must be carried instead.
    #[test]
    fn every_rendered_type_parses_back_to_itself() {
        let mut cases = vec![
            CTypeLike::Void,
            CTypeLike::Bool,
            CTypeLike::Float(32),
            CTypeLike::Float(64),
            CTypeLike::Struct("Demo".to_string()),
            CTypeLike::Union("Demo".to_string()),
            CTypeLike::Enum("Demo".to_string()),
            CTypeLike::Typedef("demo_t".to_string()),
            CTypeLike::Unknown,
            CTypeLike::Function {
                ret: Box::new(CTypeLike::Unknown),
                params: Vec::new(),
            },
        ];
        for bits in [8u32, 16, 32, 64, 128] {
            for signedness in [Signedness::Signed, Signedness::Unsigned] {
                cases.push(CTypeLike::Int { bits, signedness });
            }
        }
        let scalars = cases.clone();
        for scalar in scalars {
            cases.push(CTypeLike::Pointer(Box::new(scalar.clone())));
            cases.push(CTypeLike::Array(Box::new(scalar), Some(4)));
        }

        let mut lossy = Vec::new();
        for case in &cases {
            let rendered = render_c_type_like(case);
            let parsed = parse_c_type_like(&rendered, 64);
            if parsed != *case {
                lossy.push(format!("{case:?} rendered {rendered:?} parsed {parsed:?}"));
            }
        }
        assert!(
            lossy.is_empty(),
            "types lost through their spelling:\n{}",
            lossy.join("\n")
        );
    }

    /// The spellings that arrive from radare2 and DWARF rather than from us.
    #[test]
    fn external_spellings_parse_to_the_same_types_our_own_do() {
        let ptr_bits = 64;
        for (spelling, expected) in [
            (
                "unsigned int",
                CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Unsigned,
                },
            ),
            (
                "int",
                CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                },
            ),
            (
                "unsigned char",
                CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Unsigned,
                },
            ),
            (
                "long",
                CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Signed,
                },
            ),
            (
                "size_t",
                CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                },
            ),
            (
                "char *",
                CTypeLike::Pointer(Box::new(CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Signed,
                })),
            ),
            (
                "const char *",
                CTypeLike::Pointer(Box::new(CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Signed,
                })),
            ),
            (
                "struct Demo *",
                CTypeLike::Pointer(Box::new(CTypeLike::Struct("Demo".to_string()))),
            ),
            (
                "__uint128_t",
                CTypeLike::Int {
                    bits: 128,
                    signedness: Signedness::Unsigned,
                },
            ),
            (
                "uint64_t",
                CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                },
            ),
        ] {
            assert_eq!(
                parse_c_type_like(spelling, ptr_bits),
                expected,
                "{spelling}"
            );
        }
    }

    /// A width whose signedness is unknown cannot survive a spelling.
    ///
    /// C has no way to write "thirty-two bits, signedness not established", so
    /// the renderer has to pick one and picks signed. That is not a bug in the
    /// renderer -- it is the reason a type must be carried as a type across the
    /// writeback boundary rather than as the string it renders to, because the
    /// boundary is exactly where the distinction is still live.
    #[test]
    fn unknown_signedness_is_the_one_thing_a_spelling_cannot_carry() {
        let unknown = CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Unknown,
        };
        assert_eq!(render_c_type_like(&unknown), "int32_t");
        assert_eq!(
            parse_c_type_like("int32_t", 64),
            CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }
        );
    }

    /// `long` is target-width, so the caller supplies the width.
    #[test]
    fn target_width_spellings_follow_the_pointer_width_given() {
        assert_eq!(
            parse_c_type_like("long", 32),
            CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed
            }
        );
        assert_eq!(
            parse_c_type_like("long", 64),
            CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed
            }
        );
    }

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
