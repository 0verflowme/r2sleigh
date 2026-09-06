//! Pure lowering of source-owned per-use machine projections.
//!
//! This module does not decide which bits a use reads. It only translates the
//! exact [`r2ssa::MachineUseSlice`] selected upstream into a C expression.

use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};
use r2rewrite::CValue;
use r2ssa::{MachineCastKind, MachineUseSlice, MachineWriteProjection};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MachineUseProjectionError {
    UnsupportedIntegerWidth(u32),
    IntegerToAddressRequiresType(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MachineWriteProjectionError {
    UnsupportedIntegerWidth(u32),
    InvalidSlice {
        bit_offset: u32,
        width_bits: u32,
        carrier_width_bits: u32,
    },
}

const fn c_integer_width_is_spellable(width_bits: u32) -> bool {
    matches!(width_bits, 8 | 16 | 32 | 64 | 128)
}

const fn c_bitvector_width_is_supported(width_bits: u32) -> bool {
    matches!(width_bits, 256 | 512)
}

fn bitvector_helper(name: String, args: Vec<CExpr>) -> CExpr {
    CExpr::call(
        CExpr::External {
            name,
            kind: crate::symbol::ExternalKind::Intrinsic,
        },
        args,
    )
}

fn checked_uint_type(width_bits: u32) -> Result<CType, MachineUseProjectionError> {
    c_integer_width_is_spellable(width_bits)
        .then_some(CType::Int {
            bits: width_bits,
            signedness: r2types::Signedness::Unsigned,
        })
        .ok_or(MachineUseProjectionError::UnsupportedIntegerWidth(
            width_bits,
        ))
}

fn checked_int_type(width_bits: u32) -> Result<CType, MachineUseProjectionError> {
    c_integer_width_is_spellable(width_bits)
        .then_some(CType::Int {
            bits: width_bits,
            signedness: r2types::Signedness::Signed,
        })
        .ok_or(MachineUseProjectionError::UnsupportedIntegerWidth(
            width_bits,
        ))
}

/// Translate one exact upstream slice, given what the base is spelled as.
///
/// A slice selects bits of the carrier: the base is brought to the carrier's
/// unsigned integer, so the shift is logical and a pointer takes its
/// address-width step, then shifted, then narrowed to the selected width;
/// and only then is the source-owned conversion applied. Every step says its
/// conversion through the one emitter, so a base already spelled at the
/// carrier is not converted to it, and reading the whole of a value is not a
/// projection at all: it is the base, with the type the base has.
///
/// The result carries its type, which is what the boundary reading the
/// operand converts from. Deriving it a second time from the text was how
/// the assignment conversion was spelled on top of the projection's own.
pub(super) fn project_machine_use_of(
    base: CExpr,
    base_type: Option<&CValue>,
    slice: MachineUseSlice,
    pointer_bits: u32,
) -> Result<(CExpr, CValue), MachineUseProjectionError> {
    let convert = |expr: CExpr, from: Option<&CValue>, to: &CType| match from {
        Some(from) => super::convert::convert(expr, from, to, pointer_bits),
        None if matches!(to, CType::Pointer(_)) => CExpr::cast(to.clone(), expr),
        None => expr,
    };
    let whole = slice.bit_offset() == 0 && slice.width_bits() == slice.carrier_width_bits();
    let (projected, projected_type) = if whole {
        let ty = base_type
            .cloned()
            .unwrap_or_else(|| CValue::Typed(CType::machine_bits(slice.carrier_width_bits())));
        (base, ty)
    } else if c_integer_width_is_spellable(slice.carrier_width_bits()) {
        let carrier_type = checked_uint_type(slice.carrier_width_bits())?;
        let selected_type = checked_uint_type(slice.width_bits())?;
        let mut projected = convert(base, base_type, &carrier_type);
        if slice.bit_offset() != 0 {
            projected = CExpr::binary(
                BinaryOp::Shr,
                projected,
                CExpr::UIntLit(u64::from(slice.bit_offset())),
            );
        }
        // The selection is a narrowing, and it is the operation: spelled
        // whatever the shifted carrier is, because the shift produces the
        // carrier's type and the slice is narrower than it.
        let projected = CExpr::cast(selected_type.clone(), projected);
        (projected, CValue::Typed(selected_type))
    } else if c_bitvector_width_is_supported(slice.carrier_width_bits()) {
        if c_integer_width_is_spellable(slice.width_bits()) {
            let selected_type = checked_uint_type(slice.width_bits())?;
            (
                bitvector_helper(
                    format!(
                        "r2sleigh_bits_extract_{}_{}",
                        slice.carrier_width_bits(),
                        slice.width_bits()
                    ),
                    vec![base, CExpr::UIntLit(u64::from(slice.bit_offset()))],
                ),
                CValue::Typed(selected_type),
            )
        } else {
            return Err(MachineUseProjectionError::UnsupportedIntegerWidth(
                slice.width_bits(),
            ));
        }
    } else {
        return Err(MachineUseProjectionError::UnsupportedIntegerWidth(
            slice.carrier_width_bits(),
        ));
    };

    let Some(conversion) = slice.conversion() else {
        return Ok((projected, projected_type));
    };
    let target_width = conversion.to_width_bits();
    let source_width = slice.width_bits();
    if c_bitvector_width_is_supported(source_width) || c_bitvector_width_is_supported(target_width)
    {
        // A width-changing wide conversion needs its own source-owned semantic
        // contract (especially for signed extension). The prelude currently
        // certifies only exact extraction/insertion and zero-extending writes.
        return Err(MachineUseProjectionError::UnsupportedIntegerWidth(
            target_width.max(source_width),
        ));
    }
    // The conversion is the use's own operation, and its operand has to be
    // the unsigned integer of the selected width -- an address takes its
    // step here, a signed spelling loses its sign -- so that a zero
    // extension zero-fills and a truncation keeps the low bits.
    let operand_type = checked_uint_type(source_width)?;
    let projected = convert(projected, Some(&projected_type), &operand_type);
    match conversion.kind() {
        MachineCastKind::ZeroExtend | MachineCastKind::Truncate => {
            let target = checked_uint_type(target_width)?;
            Ok((
                CExpr::cast(target.clone(), projected),
                CValue::Typed(target),
            ))
        }
        MachineCastKind::BitReinterpret | MachineCastKind::AddressToInteger => {
            let target = checked_uint_type(target_width)?;
            let converted = convert(projected, Some(&CValue::Typed(operand_type)), &target);
            Ok((converted, CValue::Typed(target)))
        }
        MachineCastKind::SignExtend => {
            let narrow = checked_int_type(source_width)?;
            let target = checked_int_type(target_width)?;
            Ok((
                CExpr::cast(target.clone(), CExpr::cast(narrow, projected)),
                CValue::Typed(target),
            ))
        }
        MachineCastKind::IntegerToAddress => Err(
            MachineUseProjectionError::IntegerToAddressRequiresType(target_width),
        ),
    }
}

fn checked_write_uint_type(width_bits: u32) -> Result<CType, MachineWriteProjectionError> {
    c_integer_width_is_spellable(width_bits)
        .then_some(CType::Int {
            bits: width_bits,
            signedness: r2types::Signedness::Unsigned,
        })
        .ok_or(MachineWriteProjectionError::UnsupportedIntegerWidth(
            width_bits,
        ))
}

/// Apply one exact source-owned carrier write to an assignment.
///
/// `lhs` is both the assignment target and, for an inserted slice, the source
/// of the bits that the machine definition preserves. No rendered occurrence
/// is attached to that preservation read: it is part of the write projection,
/// not an SSA `UseSite`.
///
/// `rhs_type` is what the right-hand side has. The projection converts it to
/// the width the machine writes -- a lane, or the narrow half of a zero
/// extension -- through the one emitter, so a value already at that width is
/// not converted to it, and the result carries the type the carrier is
/// written at, which the assignment to the declared object converts from.
pub(super) fn project_machine_write(
    lhs: CExpr,
    rhs: CExpr,
    rhs_type: Option<&CValue>,
    projection: MachineWriteProjection,
    pointer_bits: u32,
) -> Result<(CExpr, CExpr, Option<CValue>), MachineWriteProjectionError> {
    let convert = |expr: CExpr, from: Option<&CValue>, to: &CType| match from {
        Some(from) => super::convert::convert(expr, from, to, pointer_bits),
        None if matches!(to, CType::Pointer(_)) => CExpr::cast(to.clone(), expr),
        None => expr,
    };
    match projection {
        MachineWriteProjection::Full => Ok((lhs, rhs, rhs_type.cloned())),
        // The lane is assigned and the carrier's other bits are not mentioned,
        // which is the whole difference from `Insert`: there is no read of the
        // target here, because there is nothing to preserve.
        MachineWriteProjection::Lane { width_bits, .. } => {
            let lane = checked_write_uint_type(width_bits)?;
            let rhs = convert(rhs, rhs_type, &lane);
            Ok((lhs, rhs, Some(CValue::Typed(lane))))
        }
        MachineWriteProjection::ZeroExtend {
            from_width_bits,
            to_width_bits,
        } => {
            if c_bitvector_width_is_supported(to_width_bits) {
                if !c_integer_width_is_spellable(from_width_bits) {
                    return Err(MachineWriteProjectionError::UnsupportedIntegerWidth(
                        from_width_bits,
                    ));
                }
                return Ok((
                    lhs,
                    bitvector_helper(
                        format!("r2sleigh_bits_zero_extend_{from_width_bits}_{to_width_bits}"),
                        vec![rhs],
                    ),
                    Some(CValue::Typed(CType::BitVector(to_width_bits))),
                ));
            }
            let from = checked_write_uint_type(from_width_bits)?;
            let to = checked_write_uint_type(to_width_bits)?;
            // The extension is the write's own operation, spelled whatever
            // the narrow value is; its operand is brought to the unsigned
            // narrow width so that it zero-fills.
            let rhs = convert(rhs, rhs_type, &from);
            Ok((lhs, CExpr::cast(to.clone(), rhs), Some(CValue::Typed(to))))
        }
        MachineWriteProjection::Insert {
            bit_offset,
            width_bits,
            carrier_width_bits,
        } => {
            let Some(end) = bit_offset.checked_add(width_bits) else {
                return Err(MachineWriteProjectionError::InvalidSlice {
                    bit_offset,
                    width_bits,
                    carrier_width_bits,
                });
            };
            if width_bits == 0 || end > carrier_width_bits {
                return Err(MachineWriteProjectionError::InvalidSlice {
                    bit_offset,
                    width_bits,
                    carrier_width_bits,
                });
            }

            if c_bitvector_width_is_supported(carrier_width_bits) {
                if !c_integer_width_is_spellable(width_bits) {
                    return Err(MachineWriteProjectionError::UnsupportedIntegerWidth(
                        width_bits,
                    ));
                }
                let preserved = lhs.clone_without_render_observations();
                return Ok((
                    lhs,
                    bitvector_helper(
                        format!("r2sleigh_bits_insert_{carrier_width_bits}_{width_bits}"),
                        vec![preserved, rhs, CExpr::UIntLit(u64::from(bit_offset))],
                    ),
                    Some(CValue::Typed(CType::BitVector(carrier_width_bits))),
                ));
            }

            let carrier = checked_write_uint_type(carrier_width_bits)?;
            let field = checked_write_uint_type(width_bits)?;
            let all_ones = CExpr::unary(
                UnaryOp::BitNot,
                CExpr::cast(carrier.clone(), CExpr::UIntLit(0)),
            );
            let field_mask = if width_bits == carrier_width_bits {
                all_ones
            } else {
                CExpr::binary(
                    BinaryOp::Shr,
                    all_ones,
                    CExpr::UIntLit(u64::from(carrier_width_bits - width_bits)),
                )
            };
            let shifted_mask = if bit_offset == 0 {
                field_mask.clone()
            } else {
                CExpr::binary(
                    BinaryOp::Shl,
                    field_mask.clone(),
                    CExpr::UIntLit(u64::from(bit_offset)),
                )
            };
            let preserved = CExpr::binary(
                BinaryOp::BitAnd,
                CExpr::cast(carrier.clone(), lhs.clone_without_render_observations()),
                CExpr::unary(UnaryOp::BitNot, shifted_mask),
            );
            let inserted = CExpr::binary(
                BinaryOp::BitAnd,
                CExpr::cast(carrier.clone(), convert(rhs, rhs_type, &field)),
                field_mask,
            );
            let inserted = if bit_offset == 0 {
                inserted
            } else {
                CExpr::binary(
                    BinaryOp::Shl,
                    inserted,
                    CExpr::UIntLit(u64::from(bit_offset)),
                )
            };
            Ok((
                lhs,
                CExpr::cast(
                    carrier.clone(),
                    CExpr::binary(BinaryOp::BitOr, preserved, inserted),
                ),
                Some(CValue::Typed(carrier)),
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::{SymbolRole, SymbolTable};

    fn binding_expr() -> CExpr {
        let mut symbols = SymbolTable::new();
        CExpr::Var(symbols.reserve_binding(
            "carrier".to_string(),
            CType::Int {
                bits: 64,
                signedness: r2types::Signedness::Unsigned,
            },
            SymbolRole::Carrier,
        ))
    }

    #[test]
    fn full_write_does_not_invent_a_conversion() {
        let lhs = binding_expr();
        let rhs = CExpr::UIntLit(7);
        let projected = project_machine_write(
            lhs.clone(),
            rhs.clone(),
            Some(&CValue::Constant),
            MachineWriteProjection::Full,
            64,
        )
        .expect("full write");
        assert!(projected.0.transparently_eq(&lhs));
        assert!(projected.1.transparently_eq(&rhs));
        assert_eq!(projected.2, Some(CValue::Constant));
    }

    #[test]
    fn zero_extending_write_uses_both_source_owned_widths() {
        let (_, rhs, ty) = project_machine_write(
            binding_expr(),
            CExpr::UIntLit(7),
            Some(&CValue::Typed(CType::u64())),
            MachineWriteProjection::ZeroExtend {
                from_width_bits: 32,
                to_width_bits: 64,
            },
            64,
        )
        .expect("zero-extending write");
        assert!(matches!(
            rhs,
            CExpr::Cast {
                ty: CType::Int { bits: 64, signedness: r2types::Signedness::Unsigned },
                expr,
                ..
            } if matches!(*expr, CExpr::Cast { ty: CType::Int { bits: 32, signedness: r2types::Signedness::Unsigned }, .. })
        ));
        assert_eq!(ty, Some(CValue::Typed(CType::u64())));
    }

    #[test]
    fn inserted_write_preserves_the_unwritten_carrier_bits() {
        let lhs = binding_expr();
        let (_, rhs, _) = project_machine_write(
            lhs.clone(),
            CExpr::UIntLit(0xaa),
            Some(&CValue::Constant),
            MachineWriteProjection::Insert {
                bit_offset: 8,
                width_bits: 8,
                carrier_width_bits: 64,
            },
            64,
        )
        .expect("inserted write");
        let CExpr::Cast {
            ty:
                CType::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Unsigned,
                },
            expr: combined,
            ..
        } = rhs
        else {
            panic!("insert must return the carrier type");
        };
        let CExpr::Binary {
            op: BinaryOp::BitOr,
            left: preserved,
            ..
        } = *combined
        else {
            panic!("insert must combine preserved and replaced bits");
        };
        let CExpr::Binary {
            op: BinaryOp::BitAnd,
            left: preserved_carrier,
            ..
        } = *preserved
        else {
            panic!("insert must mask the old carrier");
        };
        let CExpr::Cast {
            expr: old_value, ..
        } = *preserved_carrier
        else {
            panic!("insert must read the old carrier at carrier width");
        };
        assert!(old_value.transparently_eq(&lhs));
    }

    #[test]
    fn wide_insert_uses_the_exact_external_bitvector_contract() {
        let lhs = binding_expr();
        let (_, rhs, _) = project_machine_write(
            lhs.clone(),
            CExpr::UIntLit(0xa5),
            Some(&CValue::Constant),
            MachineWriteProjection::Insert {
                bit_offset: 127,
                width_bits: 8,
                carrier_width_bits: 256,
            },
            64,
        )
        .expect("wide inserted write");

        let CExpr::Call { func, args, .. } = rhs else {
            panic!("wide insertion must lower through the certified prelude helper");
        };
        assert!(matches!(
            func.as_ref(),
            CExpr::External { name, .. } if name == "r2sleigh_bits_insert_256_8"
        ));
        assert_eq!(args.len(), 3);
        assert!(args[0].transparently_eq(&lhs));
        assert_eq!(args[2], CExpr::UIntLit(127));
    }

    fn slice(offset: u32, width: u32, carrier: u32) -> MachineUseSlice {
        MachineUseSlice::for_test(offset, width, carrier, None)
    }

    #[test]
    fn reading_the_whole_of_a_value_is_the_value_with_its_own_type() {
        let base = binding_expr();
        let declared = CValue::Typed(CType::ptr(CType::u8()));
        let (projected, ty) =
            project_machine_use_of(base.clone(), Some(&declared), slice(0, 64, 64), 64)
                .expect("whole read");
        assert!(projected.transparently_eq(&base));
        assert_eq!(ty, declared);
    }

    #[test]
    fn a_slice_of_the_carrier_is_one_narrowing_of_a_base_already_at_the_carrier() {
        let base = binding_expr();
        let (projected, ty) = project_machine_use_of(
            base.clone(),
            Some(&CValue::Typed(CType::u64())),
            slice(0, 32, 64),
            64,
        )
        .expect("low half");
        let CExpr::Cast {
            ty: cast_ty, expr, ..
        } = projected
        else {
            panic!("a slice is a narrowing, got {projected:?}");
        };
        assert_eq!(cast_ty, CType::u32());
        assert!(
            expr.transparently_eq(&base),
            "no conversion to the carrier the base already is"
        );
        assert_eq!(ty, CValue::Typed(CType::u32()));
    }

    #[test]
    fn a_slice_of_a_pointer_takes_the_address_width_step_first() {
        let base = binding_expr();
        let (projected, _) = project_machine_use_of(
            base.clone(),
            Some(&CValue::Typed(CType::ptr(CType::u8()))),
            slice(0, 32, 64),
            64,
        )
        .expect("low half of a pointer");
        let CExpr::Cast { ty, expr, .. } = projected else {
            panic!("expected the narrowing");
        };
        assert_eq!(ty, CType::u32());
        assert!(matches!(
            *expr,
            CExpr::Cast {
                ty: CType::Int { bits: 64, .. },
                role: crate::ast::CastRole::PointerWidthStep,
                ..
            }
        ));
    }

    #[test]
    fn wide_machine_type_is_not_an_invented_integer_typedef() {
        assert_eq!(
            CType::machine_bits(256).to_string(),
            "struct r2sleigh_bits_256"
        );
        assert_eq!(
            CType::machine_bits(128),
            CType::Int {
                bits: 128,
                signedness: r2types::Signedness::Unsigned
            }
        );
    }
}
