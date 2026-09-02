//! Pure lowering of source-owned per-use machine projections.
//!
//! This module does not decide which bits a use reads. It only translates the
//! exact [`r2ssa::MachineUseSlice`] selected upstream into a C expression.

use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};
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

/// Translate one exact upstream slice. The unsigned carrier cast makes the
/// shift logical; the selected-width cast removes every bit outside the use;
/// and only then is the source-owned conversion applied.
/// Project a use, saying whether the object being read is a pointer.
///
/// A pointer cannot be sliced: `(uint32_t)p` narrows an address and the
/// compiler says so (`-Wpointer-to-int-cast`), and casting it to the carrier's
/// unsigned integer is the step that makes the slice meaningful. Reading the
/// whole of a pointer is not a projection at all, and spelling it at the
/// pointer's own type keeps the value a pointer for whatever reads it.
pub(super) fn project_machine_use_of(
    base: CExpr,
    slice: MachineUseSlice,
    base_is_pointer: bool,
) -> Result<CExpr, MachineUseProjectionError> {
    // A pointer cannot be sliced, and the conversion to the carrier's own
    // unsigned integer is the address-width step, not an ordinary widening.
    //
    // The caller's flag reports the object's declared type, which is not the
    // only way the base arrives as a pointer: an expression already converted
    // to one is a pointer here whatever the declaration said, and the
    // conversion above it is the same step for the same reason. Sixty of the
    // corpus's casts were spelled unmarked through that gap, and an unmarked
    // step is one a round trip back to the pointer cannot collapse.
    let base_is_pointer = base_is_pointer
        || matches!(
            base.unobserved(),
            CExpr::Cast {
                ty: CType::Pointer(_),
                ..
            }
        );
    let base = if base_is_pointer && c_integer_width_is_spellable(slice.carrier_width_bits()) {
        CExpr::pointer_width_cast(checked_uint_type(slice.carrier_width_bits())?, base)
    } else {
        base
    };
    let projected = if c_integer_width_is_spellable(slice.carrier_width_bits()) {
        let carrier_type = checked_uint_type(slice.carrier_width_bits())?;
        let selected_type = checked_uint_type(slice.width_bits())?;
        let mut projected = CExpr::cast(carrier_type, base);
        if slice.bit_offset() != 0 {
            projected = CExpr::binary(
                BinaryOp::Shr,
                projected,
                CExpr::UIntLit(u64::from(slice.bit_offset())),
            );
        }
        if slice.bit_offset() != 0 || slice.width_bits() != slice.carrier_width_bits() {
            projected = CExpr::cast(selected_type, projected);
        }
        projected
    } else if c_bitvector_width_is_supported(slice.carrier_width_bits()) {
        if slice.bit_offset() == 0 && slice.width_bits() == slice.carrier_width_bits() {
            base
        } else if c_integer_width_is_spellable(slice.width_bits()) {
            bitvector_helper(
                format!(
                    "r2sleigh_bits_extract_{}_{}",
                    slice.carrier_width_bits(),
                    slice.width_bits()
                ),
                vec![base, CExpr::UIntLit(u64::from(slice.bit_offset()))],
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
        return Ok(projected);
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
    match conversion.kind() {
        MachineCastKind::ZeroExtend
        | MachineCastKind::Truncate
        | MachineCastKind::BitReinterpret
        | MachineCastKind::AddressToInteger => {
            Ok(CExpr::cast(checked_uint_type(target_width)?, projected))
        }
        MachineCastKind::SignExtend => Ok(CExpr::cast(
            checked_int_type(target_width)?,
            CExpr::cast(checked_int_type(slice.width_bits())?, projected),
        )),
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
pub(super) fn project_machine_write(
    lhs: CExpr,
    rhs: CExpr,
    projection: MachineWriteProjection,
) -> Result<(CExpr, CExpr), MachineWriteProjectionError> {
    match projection {
        MachineWriteProjection::Full => Ok((lhs, rhs)),
        // The lane is assigned and the carrier's other bits are not mentioned,
        // which is the whole difference from `Insert`: there is no read of the
        // target here, because there is nothing to preserve.
        MachineWriteProjection::Lane { width_bits, .. } => {
            let lane = checked_write_uint_type(width_bits)?;
            Ok((lhs, CExpr::cast(lane, rhs)))
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
                ));
            }
            let from = checked_write_uint_type(from_width_bits)?;
            let to = checked_write_uint_type(to_width_bits)?;
            Ok((lhs, CExpr::cast(to, CExpr::cast(from, rhs))))
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
                CExpr::cast(carrier.clone(), CExpr::cast(field, rhs)),
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
                CExpr::cast(carrier, CExpr::binary(BinaryOp::BitOr, preserved, inserted)),
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
        let projected =
            project_machine_write(lhs.clone(), rhs.clone(), MachineWriteProjection::Full)
                .expect("full write");
        assert!(projected.0.transparently_eq(&lhs));
        assert!(projected.1.transparently_eq(&rhs));
    }

    #[test]
    fn zero_extending_write_uses_both_source_owned_widths() {
        let (_, rhs) = project_machine_write(
            binding_expr(),
            CExpr::UIntLit(7),
            MachineWriteProjection::ZeroExtend {
                from_width_bits: 32,
                to_width_bits: 64,
            },
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
    }

    #[test]
    fn inserted_write_preserves_the_unwritten_carrier_bits() {
        let lhs = binding_expr();
        let (_, rhs) = project_machine_write(
            lhs.clone(),
            CExpr::UIntLit(0xaa),
            MachineWriteProjection::Insert {
                bit_offset: 8,
                width_bits: 8,
                carrier_width_bits: 64,
            },
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
        let (_, rhs) = project_machine_write(
            lhs.clone(),
            CExpr::UIntLit(0xa5),
            MachineWriteProjection::Insert {
                bit_offset: 127,
                width_bits: 8,
                carrier_width_bits: 256,
            },
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
