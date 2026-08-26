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

fn checked_uint_type(width_bits: u32) -> Result<CType, MachineUseProjectionError> {
    c_integer_width_is_spellable(width_bits)
        .then_some(CType::UInt(width_bits))
        .ok_or(MachineUseProjectionError::UnsupportedIntegerWidth(
            width_bits,
        ))
}

fn checked_int_type(width_bits: u32) -> Result<CType, MachineUseProjectionError> {
    c_integer_width_is_spellable(width_bits)
        .then_some(CType::Int(width_bits))
        .ok_or(MachineUseProjectionError::UnsupportedIntegerWidth(
            width_bits,
        ))
}

/// Translate one exact upstream slice. The unsigned carrier cast makes the
/// shift logical; the selected-width cast removes every bit outside the use;
/// and only then is the source-owned conversion applied.
pub(super) fn project_machine_use(
    base: CExpr,
    slice: MachineUseSlice,
) -> Result<CExpr, MachineUseProjectionError> {
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

    let Some(conversion) = slice.conversion() else {
        return Ok(projected);
    };
    let target_width = conversion.to_width_bits();
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
        .then_some(CType::UInt(width_bits))
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
        MachineWriteProjection::ZeroExtend {
            from_width_bits,
            to_width_bits,
        } => {
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
                CExpr::cast(
                    carrier,
                    CExpr::binary(BinaryOp::BitOr, preserved, inserted),
                ),
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
            CType::UInt(64),
            SymbolRole::Carrier,
        ))
    }

    #[test]
    fn full_write_does_not_invent_a_conversion() {
        let lhs = binding_expr();
        let rhs = CExpr::UIntLit(7);
        let projected = project_machine_write(lhs.clone(), rhs.clone(), MachineWriteProjection::Full)
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
                ty: CType::UInt(64),
                expr
            } if matches!(*expr, CExpr::Cast { ty: CType::UInt(32), .. })
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
            ty: CType::UInt(64),
            expr: combined,
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
        let CExpr::Cast { expr: old_value, .. } = *preserved_carrier else {
            panic!("insert must read the old carrier at carrier width");
        };
        assert!(old_value.transparently_eq(&lhs));
    }
}
