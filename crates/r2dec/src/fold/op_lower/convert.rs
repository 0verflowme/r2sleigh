//! The one place a conversion is spelled.
//!
//! A cast is a statement that one type becomes another, and the renderer
//! makes it from exactly two facts: what the expression has, stated by the
//! site that built it or by the typed boundaries of the arena, and what the
//! boundary it is about to cross requires. Neither is read off the rendered
//! text. Where the two are one type nothing is spelled, and a truth value
//! crosses into any integer unspelled; everywhere else the conversion is
//! written down, and at most twice: the address-width step a pointer takes on
//! its way to or from an integer of another width, and the target.

use r2rewrite::CValue;
use r2types::Signedness;

use crate::ast::{CExpr, CType};

/// Whether a type is an integer C would convert, as `(signed, bits)`.
///
/// A boolean is a one-bit unsigned integer here: a comparison's value is
/// exactly zero or one, and every integer type holds it. An enumeration is
/// an `int`. A typedef is resolved to the integer it names, at the pointer
/// width for the types whose width the target decides.
fn integer_meta(ty: &CType, pointer_bits: u32) -> Option<(bool, u32)> {
    match ty {
        CType::Int { bits, signedness } => Some((*signedness == Signedness::Signed, *bits)),
        CType::Bool => Some((false, 1)),
        CType::Enum(_) => Some((true, 32)),
        CType::Typedef(name) => typedef_integer_meta(name, pointer_bits),
        _ => None,
    }
}

fn typedef_integer_meta(name: &str, pointer_bits: u32) -> Option<(bool, u32)> {
    let normalized = name
        .to_ascii_lowercase()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    match normalized.as_str() {
        "signed char" | "int8_t" => Some((true, 8)),
        "unsigned char" | "uint8_t" => Some((false, 8)),
        "short" | "short int" | "signed short" | "signed short int" | "int16_t" => Some((true, 16)),
        "unsigned short" | "unsigned short int" | "uint16_t" => Some((false, 16)),
        "int" | "signed" | "signed int" | "int32_t" => Some((true, 32)),
        "unsigned" | "unsigned int" | "uint32_t" => Some((false, 32)),
        "long long"
        | "long long int"
        | "signed long long"
        | "signed long long int"
        | "int64_t"
        | "intmax_t" => Some((true, 64)),
        "unsigned long long" | "unsigned long long int" | "uint64_t" | "uintmax_t" => {
            Some((false, 64))
        }
        "long" | "long int" | "signed long" | "signed long int" => Some((true, pointer_bits)),
        "unsigned long" | "unsigned long int" | "size_t" | "uintptr_t" => {
            Some((false, pointer_bits))
        }
        "ssize_t" | "intptr_t" | "ptrdiff_t" => Some((true, pointer_bits)),
        _ => None,
    }
}

/// Whether a value of this type is an address: a pointer, or an array or
/// function, which decay to one wherever a value is wanted.
fn is_address(ty: &CType) -> bool {
    matches!(
        ty,
        CType::Pointer(_) | CType::Array(_, _) | CType::Function { .. }
    )
}

/// Whether two types are one type to the compiler.
fn same_type(from: &CType, to: &CType, pointer_bits: u32) -> bool {
    if from == to {
        return true;
    }
    if let (Some(from), Some(to)) = (
        integer_meta(from, pointer_bits),
        integer_meta(to, pointer_bits),
    ) {
        return from == to;
    }
    match (from, to) {
        // An array decays to a pointer to its element.
        (CType::Array(element, _), CType::Pointer(pointee)) => element == pointee,
        _ => false,
    }
}

/// Whether `from` may cross into `to` with nothing spelled.
///
/// Only a truth value may. A comparison's value is zero or one, every
/// integer type holds it, and C reads it as one wherever it is read.
///
/// No other widening is left implicit, exact though C would make it. The
/// type stated for an expression has to be the type the expression has,
/// because the operators that read it compute in that type: two `uint32_t`
/// operands claimed as `uint64_t` and left unconverted are multiplied in
/// thirty-two bits, and two `uint16_t` claimed as `uint32_t` are promoted to
/// `int` and multiplied there, which overflows. So `(uint64_t)x` is spelled
/// where `x` is narrower, and it is not spelled where `x` is already a
/// `uint64_t`, which is the whole of the rule.
fn implicit_is_exact(from: (bool, u32), _to: (bool, u32)) -> bool {
    from == (false, 1)
}

/// Spell a constant in the integer type that reads it.
///
/// C types a constant by its value and converts it exactly to any integer
/// type it fits, so the constant is respelled -- signed where the reader is
/// signed, at the reader's width -- rather than cast. A constant read as a
/// pointer is a conversion the program performs and is spelled as one.
///
/// A constant whose spelling cannot carry its type is the exception, and it
/// is cast. A mask the renderer prints as `-0x4` because that is how a
/// reader wants to see it is an `int` to the compiler whatever value it
/// stands for, and `x &= -0x4` on a `uint64_t` is then a signedness-changing
/// conversion that `-Wsign-conversion` rejects. Spelling the value out
/// instead -- `0xfffffffffffffffc` -- needs a width suffix to mean the same
/// thing, and the literal does not carry a width, so the type is stated the
/// one way that is always available.
fn spell_constant(expr: CExpr, to: &CType, pointer_bits: u32) -> CExpr {
    if matches!(to, CType::Pointer(_)) {
        return CExpr::cast(to.clone(), expr);
    }
    let Some((signed, bits)) = integer_meta(to, pointer_bits) else {
        return expr;
    };
    if !(8..=64).contains(&bits) {
        return expr;
    }
    let respelled = respell_literal(expr, signed, bits);
    if !signed && renders_as_signed(&respelled) {
        return CExpr::cast(to.clone(), respelled);
    }
    respelled
}

/// Whether the rendered form of this literal is a signed constant.
///
/// `codegen` prints a high unsigned value as the negative it stands for,
/// which is what a mask should look like and is an `int` to the compiler.
fn renders_as_signed(expr: &CExpr) -> bool {
    match expr {
        CExpr::Observed { expr, .. } | CExpr::Paren(expr) => renders_as_signed(expr),
        CExpr::IntLit(value) => *value < 0,
        CExpr::UIntLit(value) => *value > crate::codegen::LIKELY_NEGATIVE_THRESHOLD,
        _ => false,
    }
}

fn respell_literal(expr: CExpr, signed: bool, bits: u32) -> CExpr {
    match expr {
        CExpr::Observed { id, expr } => CExpr::observed(id, respell_literal(*expr, signed, bits)),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(respell_literal(*inner, signed, bits))),
        CExpr::UIntLit(value) => crate::typed_integer_literal_expr(value, signed, bits),
        CExpr::IntLit(value) => crate::typed_integer_literal_expr(value as u64, signed, bits),
        other => other,
    }
}

/// Convert `expr`, which has `from`, to `to`.
pub(crate) fn convert(expr: CExpr, from: &CValue, to: &CType, pointer_bits: u32) -> CExpr {
    match from {
        CValue::Constant => spell_constant(expr, to, pointer_bits),
        CValue::Typed(from) => convert_typed(expr, from, to, pointer_bits),
    }
}

fn convert_typed(expr: CExpr, from: &CType, to: &CType, pointer_bits: u32) -> CExpr {
    if same_type(from, to, pointer_bits) {
        return expr;
    }
    // Anything scalar is a condition.
    if matches!(to, CType::Bool) {
        return expr;
    }
    // Nothing is known about one side, or it has no C conversion at all:
    // a limb-backed bitvector is converted by the prelude's helpers, and a
    // structure or union by the access that names a member.
    if matches!(
        from,
        CType::Unknown | CType::Void | CType::BitVector(_) | CType::Struct(_) | CType::Union(_)
    ) || matches!(
        to,
        CType::Unknown
            | CType::Void
            | CType::BitVector(_)
            | CType::Struct(_)
            | CType::Union(_)
            | CType::Array(_, _)
            | CType::Function { .. }
    ) {
        return expr;
    }
    // A floating-point conversion is a value conversion, and it is what the
    // operation asked for.
    if matches!(from, CType::Float(_)) || matches!(to, CType::Float(_)) {
        return CExpr::cast(to.clone(), expr);
    }
    let from_integer = integer_meta(from, pointer_bits);
    let to_integer = integer_meta(to, pointer_bits);
    match (from_integer, to_integer) {
        (Some(from), Some(to_meta)) => {
            if implicit_is_exact(from, to_meta) {
                expr
            } else {
                CExpr::cast(to.clone(), expr)
            }
        }
        // A pointer converts to an integer of its own width in one step,
        // and that step is recorded as the address-width step so a round
        // trip back to the pointer can collapse. Narrower is
        // `-Wpointer-to-int-cast`, because address bits are lost and the
        // compiler will not let that be implicit, so the full-width step is
        // spelled first and the narrowing is the program's own statement.
        (None, Some((_, to_bits))) if is_address(from) => {
            if to_bits == pointer_bits {
                CExpr::pointer_width_cast(to.clone(), expr)
            } else if to_bits < pointer_bits {
                CExpr::cast(
                    to.clone(),
                    CExpr::pointer_width_cast(CType::uint(pointer_bits), expr),
                )
            } else {
                CExpr::cast(to.clone(), expr)
            }
        }
        // The other direction. An integer narrower than an address is
        // widened to the address width first, so that the pointer is made
        // from a whole address and not from whatever the compiler extends
        // the narrow value to.
        (Some((_, from_bits)), None) if matches!(to, CType::Pointer(_)) => {
            if from_bits == pointer_bits {
                CExpr::cast(to.clone(), expr)
            } else if from_bits < pointer_bits {
                CExpr::cast(
                    to.clone(),
                    CExpr::pointer_width_cast(CType::uint(pointer_bits), expr),
                )
            } else {
                CExpr::cast(to.clone(), CExpr::cast(CType::uint(pointer_bits), expr))
            }
        }
        (None, None) if is_address(from) && matches!(to, CType::Pointer(_)) => {
            CExpr::cast(to.clone(), expr)
        }
        _ => expr,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::CastRole;
    use crate::symbol::{SymbolRole, SymbolTable};

    fn name(ty: CType) -> CExpr {
        let mut symbols = SymbolTable::new();
        CExpr::Var(symbols.reserve_binding("value".to_string(), ty, SymbolRole::Carrier))
    }

    fn typed(ty: CType) -> CValue {
        CValue::Typed(ty)
    }

    fn cast_of(expr: &CExpr) -> Option<(CType, CExpr, CastRole)> {
        match expr {
            CExpr::Cast { ty, expr, role } => Some((ty.clone(), (**expr).clone(), *role)),
            _ => None,
        }
    }

    #[test]
    fn a_value_of_the_required_type_is_not_converted() {
        let value = name(CType::u64());
        let converted = convert(value.clone(), &typed(CType::u64()), &CType::u64(), 64);
        assert_eq!(converted, value);
        let pointer = name(CType::ptr(CType::u8()));
        let converted = convert(
            pointer.clone(),
            &typed(CType::ptr(CType::u8())),
            &CType::ptr(CType::u8()),
            64,
        );
        assert_eq!(converted, pointer);
    }

    #[test]
    fn a_typedef_naming_the_required_integer_is_that_integer() {
        let value = name(CType::u64());
        let converted = convert(
            value.clone(),
            &typed(CType::Typedef("size_t".to_string())),
            &CType::u64(),
            64,
        );
        assert_eq!(converted, value);
        let converted = convert(
            value.clone(),
            &typed(CType::Typedef("size_t".to_string())),
            &CType::u64(),
            32,
        );
        assert!(
            cast_of(&converted).is_some(),
            "size_t is 32 bits on a 32-bit target"
        );
    }

    #[test]
    fn a_truth_value_needs_no_conversion_and_a_widening_is_spelled() {
        let truth = name(CType::Bool);
        assert_eq!(
            convert(truth.clone(), &typed(CType::Bool), &CType::u8(), 64),
            truth
        );
        assert_eq!(
            convert(truth.clone(), &typed(CType::Bool), &CType::i64(), 64),
            truth
        );
        // Exact, and still spelled: the operator that reads the value
        // computes in the type the value has, not in the one it fits.
        let byte = name(CType::u8());
        let (ty, _, _) = cast_of(&convert(
            byte.clone(),
            &typed(CType::u8()),
            &CType::u64(),
            64,
        ))
        .expect("a widening is spelled");
        assert_eq!(ty, CType::u64());
        let half = name(CType::u32());
        assert!(cast_of(&convert(half, &typed(CType::u32()), &CType::u64(), 64)).is_some());
    }

    #[test]
    fn a_narrowing_or_a_change_of_signedness_is_spelled() {
        let word = name(CType::u64());
        let (ty, _, role) = cast_of(&convert(
            word.clone(),
            &typed(CType::u64()),
            &CType::u32(),
            64,
        ))
        .expect("narrowing is spelled");
        assert_eq!((ty, role), (CType::u32(), CastRole::Conversion));
        let (ty, _, _) = cast_of(&convert(
            word.clone(),
            &typed(CType::u64()),
            &CType::i64(),
            64,
        ))
        .expect("a change of signedness is spelled");
        assert_eq!(ty, CType::i64());
        let signed = name(CType::i32());
        assert!(
            cast_of(&convert(signed, &typed(CType::i32()), &CType::u64(), 64)).is_some(),
            "a signed value into an unsigned type changes negative values"
        );
    }

    #[test]
    fn a_pointer_takes_the_address_width_step_once() {
        let pointer = name(CType::ptr(CType::u8()));
        let (ty, _, role) = cast_of(&convert(
            pointer.clone(),
            &typed(CType::ptr(CType::u8())),
            &CType::u64(),
            64,
        ))
        .expect("pointer to its own integer");
        assert_eq!((ty, role), (CType::u64(), CastRole::PointerWidthStep));
        let narrowed = convert(
            pointer.clone(),
            &typed(CType::ptr(CType::u8())),
            &CType::u32(),
            64,
        );
        let (outer, inner, outer_role) = cast_of(&narrowed).expect("narrowing");
        assert_eq!((outer, outer_role), (CType::u32(), CastRole::Conversion));
        let (step, _, step_role) = cast_of(&inner).expect("the step beneath it");
        assert_eq!(
            (step, step_role),
            (CType::u64(), CastRole::PointerWidthStep)
        );
    }

    #[test]
    fn an_integer_becomes_a_pointer_through_the_address_width() {
        let word = name(CType::u64());
        let (ty, inner, _) = cast_of(&convert(
            word.clone(),
            &typed(CType::u64()),
            &CType::ptr(CType::u8()),
            64,
        ))
        .expect("integer to pointer");
        assert_eq!(ty, CType::ptr(CType::u8()));
        assert_eq!(inner, word);
        let half = name(CType::u32());
        let converted = convert(half, &typed(CType::u32()), &CType::ptr(CType::u8()), 64);
        let (_, inner, _) = cast_of(&converted).expect("pointer outside");
        let (step, _, role) = cast_of(&inner).expect("the step inside");
        assert_eq!((step, role), (CType::u64(), CastRole::PointerWidthStep));
    }

    #[test]
    fn a_constant_is_spelled_in_the_type_that_reads_it() {
        assert_eq!(
            convert(CExpr::IntLit(5), &CValue::Constant, &CType::u32(), 64),
            CExpr::IntLit(5)
        );
        assert_eq!(
            convert(
                CExpr::UIntLit(0xffff_ffff),
                &CValue::Constant,
                &CType::i32(),
                64
            ),
            CExpr::IntLit(-1)
        );
        // A negative literal read as an unsigned type keeps the spelling a
        // reader wants and states the type, because `-1` alone is an `int`.
        let negative = convert(CExpr::IntLit(-1), &CValue::Constant, &CType::u64(), 64);
        let (ty, inner, _) = cast_of(&negative).expect("the type is stated");
        assert_eq!(ty, CType::u64());
        assert!(renders_as_signed(&inner), "got {inner:?}");
        let (ty, inner, _) = cast_of(&convert(
            CExpr::IntLit(16),
            &CValue::Constant,
            &CType::ptr(CType::u8()),
            64,
        ))
        .expect("a constant address is a conversion");
        assert_eq!((ty, inner), (CType::ptr(CType::u8()), CExpr::IntLit(16)));
    }

    #[test]
    fn a_condition_accepts_any_scalar() {
        let word = name(CType::u64());
        assert_eq!(
            convert(word.clone(), &typed(CType::u64()), &CType::Bool, 64),
            word
        );
        let pointer = name(CType::ptr(CType::u8()));
        assert_eq!(
            convert(
                pointer.clone(),
                &typed(CType::ptr(CType::u8())),
                &CType::Bool,
                64
            ),
            pointer
        );
    }

    #[test]
    fn a_type_c_cannot_convert_is_left_alone() {
        let wide = name(CType::BitVector(256));
        assert_eq!(
            convert(
                wide.clone(),
                &typed(CType::BitVector(256)),
                &CType::u64(),
                64
            ),
            wide
        );
        let unknown = name(CType::u64());
        assert_eq!(
            convert(unknown.clone(), &typed(CType::Unknown), &CType::u64(), 64),
            unknown
        );
    }
}
