//! Pure lowering of source-owned per-use machine projections.
//!
//! This module does not decide which bits a use reads. It only translates the
//! exact [`r2ssa::MachineUseSlice`] selected upstream into a C expression.

use crate::ast::{BinaryOp, CExpr, CType};
use r2ssa::{MachineCastKind, MachineUseSlice};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MachineUseProjectionError {
    UnsupportedIntegerWidth(u32),
    IntegerToAddressRequiresType(u32),
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
