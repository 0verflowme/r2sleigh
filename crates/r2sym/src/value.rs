//! Symbolic values for symbolic execution.
//!
//! A `SymValue` can be:
//! - `Concrete`: A known constant value
//! - `Symbolic`: A Z3 bitvector expression
//! - `Unknown`: An uninitialized or undefined value

use std::fmt;

use std::marker::PhantomData;
use z3::Context;
use z3::DeclKind;
use z3::ast::{Ast, BV, Dynamic};

/// A symbolic value that can be concrete, symbolic, or unknown.
///
/// Each value carries an optional taint mask for tracking data flow.
#[derive(Clone)]
pub enum SymValue<'ctx> {
    /// A concrete (known) value.
    Concrete {
        /// The value.
        value: u64,
        /// Size in bits.
        bits: u32,
        /// Taint mask (bitfield for multiple taint sources).
        taint: u64,
    },
    /// A symbolic value represented as a Z3 bitvector.
    Symbolic {
        /// The Z3 bitvector AST.
        ast: BV,
        /// Size in bits.
        bits: u32,
        /// Taint mask (bitfield for multiple taint sources).
        taint: u64,
        /// Marker for lifetime
        _marker: PhantomData<&'ctx ()>,
    },
    /// An unknown/uninitialized value.
    Unknown {
        /// Size in bits.
        bits: u32,
        /// Taint mask (bitfield for multiple taint sources).
        taint: u64,
    },
}

impl<'ctx> SymValue<'ctx> {
    #[inline]
    fn normalize_bv_bits(bits: u32) -> u32 {
        bits.max(1)
    }

    /// Create a concrete value (untainted).
    pub fn concrete(value: u64, bits: u32) -> Self {
        Self::Concrete {
            value,
            bits: Self::normalize_bv_bits(bits),
            taint: 0,
        }
    }

    /// Create a concrete value with taint.
    pub fn concrete_tainted(value: u64, bits: u32, taint: u64) -> Self {
        Self::Concrete {
            value,
            bits: Self::normalize_bv_bits(bits),
            taint,
        }
    }

    /// Create a symbolic value from a Z3 bitvector (untainted).
    pub fn symbolic(ast: BV, bits: u32) -> Self {
        Self::Symbolic {
            ast,
            bits: Self::normalize_bv_bits(bits),
            taint: 0,
            _marker: PhantomData,
        }
    }

    /// Create a symbolic value with taint.
    pub fn symbolic_tainted(ast: BV, bits: u32, taint: u64) -> Self {
        Self::Symbolic {
            ast,
            bits: Self::normalize_bv_bits(bits),
            taint,
            _marker: PhantomData,
        }
    }

    /// Create an unknown value (untainted).
    pub fn unknown(bits: u32) -> Self {
        Self::Unknown {
            bits: Self::normalize_bv_bits(bits),
            taint: 0,
        }
    }

    /// Create an unknown value with taint.
    pub fn unknown_tainted(bits: u32, taint: u64) -> Self {
        Self::Unknown {
            bits: Self::normalize_bv_bits(bits),
            taint,
        }
    }

    /// Get the taint mask of this value.
    pub fn get_taint(&self) -> u64 {
        match self {
            Self::Concrete { taint, .. } => *taint,
            Self::Symbolic { taint, .. } => *taint,
            Self::Unknown { taint, .. } => *taint,
        }
    }

    /// Create a copy of this value with additional taint.
    pub fn with_taint(&self, new_taint: u64) -> Self {
        match self {
            Self::Concrete { value, bits, taint } => Self::Concrete {
                value: *value,
                bits: *bits,
                taint: *taint | new_taint,
            },
            Self::Symbolic {
                ast, bits, taint, ..
            } => Self::Symbolic {
                ast: ast.clone(),
                bits: *bits,
                taint: *taint | new_taint,
                _marker: PhantomData,
            },
            Self::Unknown { bits, taint } => Self::Unknown {
                bits: *bits,
                taint: *taint | new_taint,
            },
        }
    }

    /// Check if this value is tainted.
    pub fn is_tainted(&self) -> bool {
        self.get_taint() != 0
    }

    /// Check if this value has a specific taint.
    pub fn has_taint(&self, taint_bit: u64) -> bool {
        self.get_taint() & taint_bit != 0
    }

    /// Create a new symbolic variable (untainted).
    pub fn new_symbolic(_ctx: &'ctx Context, name: &str, bits: u32) -> Self {
        let bits = Self::normalize_bv_bits(bits);
        let ast = BV::new_const(name, bits);
        Self::Symbolic {
            ast,
            bits,
            taint: 0,
            _marker: PhantomData,
        }
    }

    /// Create a new symbolic variable with taint.
    pub fn new_symbolic_tainted(_ctx: &'ctx Context, name: &str, bits: u32, taint: u64) -> Self {
        let bits = Self::normalize_bv_bits(bits);
        let ast = BV::new_const(name, bits);
        Self::Symbolic {
            ast,
            bits,
            taint,
            _marker: PhantomData,
        }
    }

    /// Create a concrete value from a Z3 context.
    pub fn from_u64(_ctx: &'ctx Context, value: u64, bits: u32) -> Self {
        Self::Concrete {
            value,
            bits: Self::normalize_bv_bits(bits),
            taint: 0,
        }
    }

    /// Get the bit width of this value.
    pub fn bits(&self) -> u32 {
        match self {
            Self::Concrete { bits, .. } => *bits,
            Self::Symbolic { bits, .. } => *bits,
            Self::Unknown { bits, .. } => *bits,
        }
    }

    /// Normalize two values to the same bit width for binary operations.
    /// Returns (self_normalized, other_normalized, result_bits).
    /// Uses zero-extension to match the larger width.
    fn normalize_widths<'a>(&'a self, ctx: &'ctx Context, other: &'a Self) -> (BV, BV, u32) {
        let self_bits = self.bits();
        let other_bits = other.bits();

        if self_bits == other_bits {
            (self.to_bv(ctx), other.to_bv(ctx), self_bits)
        } else if self_bits > other_bits {
            let self_bv = self.to_bv(ctx);
            let other_bv = other.to_bv(ctx).zero_ext(self_bits - other_bits);
            (self_bv, other_bv, self_bits)
        } else {
            let self_bv = self.to_bv(ctx).zero_ext(other_bits - self_bits);
            let other_bv = other.to_bv(ctx);
            (self_bv, other_bv, other_bits)
        }
    }

    /// Normalize two values to the same bit width for signed operations.
    /// Returns (self_normalized, other_normalized, result_bits).
    /// Uses sign-extension to match the larger width.
    fn normalize_widths_signed<'a>(&'a self, ctx: &'ctx Context, other: &'a Self) -> (BV, BV, u32) {
        let self_bits = self.bits();
        let other_bits = other.bits();

        if self_bits == other_bits {
            (self.to_bv(ctx), other.to_bv(ctx), self_bits)
        } else if self_bits > other_bits {
            let self_bv = self.to_bv(ctx);
            let other_bv = other.to_bv(ctx).sign_ext(self_bits - other_bits);
            (self_bv, other_bv, self_bits)
        } else {
            let self_bv = self.to_bv(ctx).sign_ext(other_bits - self_bits);
            let other_bv = other.to_bv(ctx);
            (self_bv, other_bv, other_bits)
        }
    }

    /// Normalize shift amount to match value width.
    /// Shift amounts are often smaller (e.g., 8-bit) than the value being shifted.
    fn normalize_shift_amount(&self, ctx: &'ctx Context, amount: &Self) -> BV {
        let value_bits = self.bits();
        let amount_bits = amount.bits();

        if amount_bits == value_bits {
            amount.to_bv(ctx)
        } else if amount_bits < value_bits {
            amount.to_bv(ctx).zero_ext(value_bits - amount_bits)
        } else {
            // Truncate if shift amount is larger (unusual but handle it)
            amount.to_bv(ctx).extract(value_bits - 1, 0)
        }
    }

    /// Check if this value is concrete.
    pub fn is_concrete(&self) -> bool {
        matches!(self, Self::Concrete { .. })
    }

    /// Check if this value is symbolic.
    pub fn is_symbolic(&self) -> bool {
        matches!(self, Self::Symbolic { .. })
    }

    /// Check if this value is unknown.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown { .. })
    }

    /// Get the concrete value if available.
    pub fn as_concrete(&self) -> Option<u64> {
        match self {
            Self::Concrete { value, .. } => Some(*value),
            _ => None,
        }
    }

    /// Get the Z3 AST if this is symbolic.
    pub fn as_ast(&self) -> Option<&BV> {
        match self {
            Self::Symbolic { ast, .. } => Some(ast),
            _ => None,
        }
    }

    pub(crate) fn symbolic_key(&self) -> Option<String> {
        match self {
            Self::Symbolic { ast, bits, .. } => Some(format!("{bits}:{}", ast)),
            _ => None,
        }
    }

    fn is_concrete_value(&self, expected: u64) -> bool {
        matches!(self, Self::Concrete { value, .. } if *value == expected)
    }

    fn mask_for_bits(bits: u32) -> u64 {
        if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        }
    }

    fn concrete_logical_shift_left(value: u64, bits: u32, amount: u64) -> u64 {
        if bits == 0 || amount >= u64::from(bits) {
            return 0;
        }
        value.wrapping_shl(amount as u32) & Self::mask_for_bits(bits)
    }

    fn concrete_logical_shift_right(value: u64, bits: u32, amount: u64) -> u64 {
        if bits == 0 || amount >= u64::from(bits) {
            return 0;
        }
        value >> (amount as u32)
    }

    fn is_all_ones_for(&self, bits: u32) -> bool {
        match self {
            Self::Concrete {
                value,
                bits: value_bits,
                ..
            } => *value_bits == bits && *value == Self::mask_for_bits(bits),
            _ => false,
        }
    }

    fn same_symbolic_ast(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Symbolic { ast: a, .. }, Self::Symbolic { ast: b, .. }) => a.ast_eq(b),
            _ => false,
        }
    }

    /// Convert to a Z3 bitvector (concretizing if needed).
    pub fn to_bv(&self, _ctx: &'ctx Context) -> BV {
        match self {
            Self::Concrete { value, bits, .. } => {
                BV::from_u64(*value, Self::normalize_bv_bits(*bits))
            }
            Self::Symbolic { ast, .. } => ast.clone(),
            Self::Unknown { bits, .. } => {
                // Create a fresh symbolic variable for unknown values
                BV::fresh_const("unknown", Self::normalize_bv_bits(*bits))
            }
        }
    }

    /// Zero-extend to a larger size.
    pub fn zero_extend(&self, _ctx: &'ctx Context, new_bits: u32) -> Self {
        if new_bits <= self.bits() {
            return self.clone();
        }
        let extend_by = new_bits - self.bits();
        let taint = self.get_taint();
        match self {
            Self::Concrete { value, .. } => Self::Concrete {
                value: *value,
                bits: new_bits,
                taint,
            },
            Self::Symbolic {
                ast,
                bits: _,
                taint,
                ..
            } => {
                let new_ast = {
                    let dyn_ast = Dynamic::from_ast(ast);
                    if matches!(
                        dyn_ast.safe_decl().map(|decl| decl.kind()),
                        Ok(DeclKind::ZERO_EXT)
                    ) {
                        if let Some(child) =
                            dyn_ast.children().first().and_then(|child| child.as_bv())
                        {
                            child.zero_ext(new_bits - child.get_size())
                        } else {
                            ast.zero_ext(extend_by)
                        }
                    } else {
                        ast.zero_ext(extend_by)
                    }
                };
                Self::Symbolic {
                    ast: new_ast,
                    bits: new_bits,
                    taint: *taint,
                    _marker: PhantomData,
                }
            }
            Self::Unknown { .. } => Self::Unknown {
                bits: new_bits,
                taint,
            },
        }
    }

    /// Sign-extend to a larger size.
    pub fn sign_extend(&self, _ctx: &'ctx Context, new_bits: u32) -> Self {
        if new_bits <= self.bits() {
            return self.clone();
        }
        let extend_by = new_bits - self.bits();
        let taint = self.get_taint();
        match self {
            Self::Concrete { value, bits, .. } => {
                let src_bits = *bits;
                let mut new_value = *value;
                let low_mask = if src_bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << src_bits) - 1
                };
                new_value &= low_mask;
                if src_bits > 0 && ((new_value >> (src_bits - 1)) & 1) == 1 {
                    let extend_mask = if new_bits >= 64 {
                        if src_bits >= 64 { 0 } else { !low_mask }
                    } else {
                        let new_mask = (1u64 << new_bits) - 1;
                        new_mask & !low_mask
                    };
                    new_value |= extend_mask;
                }
                Self::Concrete {
                    value: new_value,
                    bits: new_bits,
                    taint,
                }
            }
            Self::Symbolic { ast, .. } => {
                let new_ast = {
                    let dyn_ast = Dynamic::from_ast(ast);
                    if matches!(
                        dyn_ast.safe_decl().map(|decl| decl.kind()),
                        Ok(DeclKind::SIGN_EXT)
                    ) {
                        if let Some(child) =
                            dyn_ast.children().first().and_then(|child| child.as_bv())
                        {
                            child.sign_ext(new_bits - child.get_size())
                        } else {
                            ast.sign_ext(extend_by)
                        }
                    } else {
                        ast.sign_ext(extend_by)
                    }
                };
                Self::Symbolic {
                    ast: new_ast,
                    bits: new_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
            Self::Unknown { .. } => Self::Unknown {
                bits: new_bits,
                taint,
            },
        }
    }

    /// Extract bits [high:low] from this value.
    pub fn extract(&self, _ctx: &'ctx Context, high: u32, low: u32) -> Self {
        let taint = self.get_taint();
        let src_bits = self.bits().max(1);
        if high < low || low >= src_bits {
            return Self::Unknown { bits: 1, taint };
        }
        let clamped_high = high.min(src_bits - 1);
        if clamped_high < low {
            return Self::Unknown { bits: 1, taint };
        }
        let new_bits = clamped_high - low + 1;
        if low == 0 && clamped_high + 1 == src_bits {
            return self.clone();
        }
        match self {
            Self::Concrete { value, .. } => {
                if new_bits > 64 || clamped_high >= 64 {
                    let new_ast = self.to_bv(_ctx).extract(clamped_high, low);
                    return Self::symbolic_tainted(new_ast, new_bits, taint);
                }
                let mask = if new_bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << new_bits) - 1
                };
                let new_value = (*value >> low) & mask;
                Self::Concrete {
                    value: new_value,
                    bits: new_bits,
                    taint,
                }
            }
            Self::Symbolic { ast, .. } => {
                if low == 0 {
                    let dyn_ast = Dynamic::from_ast(ast);
                    if matches!(
                        dyn_ast.safe_decl().map(|decl| decl.kind()),
                        Ok(DeclKind::ZERO_EXT | DeclKind::SIGN_EXT)
                    ) {
                        let children = dyn_ast.children();
                        if let Some(child) = children.first().and_then(|child| child.as_bv())
                            && child.get_size() == new_bits
                        {
                            return Self::symbolic_tainted(child, new_bits, taint);
                        }
                    }
                }
                let new_ast = ast.extract(clamped_high, low);
                Self::Symbolic {
                    ast: new_ast,
                    bits: new_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
            Self::Unknown { .. } => Self::Unknown {
                bits: new_bits,
                taint,
            },
        }
    }

    /// Concatenate two values (self is high bits, other is low bits).
    pub fn concat(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let new_bits = self.bits() + other.bits();
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: hi, .. },
                Self::Concrete {
                    value: lo,
                    bits: lo_bits,
                    ..
                },
            ) => {
                if new_bits <= 64 {
                    let new_value = (*hi << *lo_bits) | *lo;
                    Self::Concrete {
                        value: new_value,
                        bits: new_bits,
                        taint,
                    }
                } else {
                    let hi_bv = self.to_bv(ctx);
                    let lo_bv = other.to_bv(ctx);
                    let new_ast = hi_bv.concat(&lo_bv);
                    Self::symbolic_tainted(new_ast, new_bits, taint)
                }
            }
            _ => {
                let hi_bv = self.to_bv(ctx);
                let lo_bv = other.to_bv(ctx);
                let new_ast = hi_bv.concat(&lo_bv);
                Self::symbolic_tainted(new_ast, new_bits, taint)
            }
        }
    }

    // ==================== Arithmetic Operations ====================

    /// Add two values (taint is propagated via OR).
    pub fn add(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => {
                let result_bits = (*bits).max(*b_bits);
                let mask = if result_bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << result_bits) - 1
                };
                Self::Concrete {
                    value: a.wrapping_add(*b) & mask,
                    bits: result_bits,
                    taint,
                }
            }
            (_, rhs) if rhs.is_zero() => self.clone().with_taint(taint),
            (lhs, _) if lhs.is_zero() => other.clone().with_taint(taint),
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvadd(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Subtract two values.
    pub fn sub(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => {
                let result_bits = (*bits).max(*b_bits);
                let mask = if result_bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << result_bits) - 1
                };
                Self::Concrete {
                    value: a.wrapping_sub(*b) & mask,
                    bits: result_bits,
                    taint,
                }
            }
            (_, rhs) if rhs.is_zero() => self.clone().with_taint(taint),
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvsub(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Multiply two values.
    pub fn mul(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => {
                let result_bits = (*bits).max(*b_bits);
                let mask = if result_bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << result_bits) - 1
                };
                Self::Concrete {
                    value: a.wrapping_mul(*b) & mask,
                    bits: result_bits,
                    taint,
                }
            }
            (_, rhs) if rhs.is_zero() => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            (lhs, _) if lhs.is_zero() => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            (_, rhs) if rhs.is_concrete_value(1) => self.clone().with_taint(taint),
            (lhs, _) if lhs.is_concrete_value(1) => other.clone().with_taint(taint),
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvmul(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Unsigned division.
    pub fn udiv(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => {
                let result_bits = (*bits).max(*b_bits);
                if *b == 0 {
                    Self::Unknown {
                        bits: result_bits,
                        taint,
                    }
                } else {
                    Self::Concrete {
                        value: *a / *b,
                        bits: result_bits,
                        taint,
                    }
                }
            }
            (_, rhs) if rhs.is_concrete_value(1) => self.clone().with_taint(taint),
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvudiv(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Signed division.
    pub fn sdiv(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        if other.is_concrete_value(1) {
            return self.clone().with_taint(taint);
        }
        let (a_bv, b_bv, result_bits) = self.normalize_widths_signed(ctx, other);
        Self::Symbolic {
            ast: a_bv.bvsdiv(&b_bv),
            bits: result_bits,
            taint,
            _marker: PhantomData,
        }
    }

    /// Unsigned remainder.
    pub fn urem(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => {
                let result_bits = (*bits).max(*b_bits);
                if *b == 0 {
                    Self::Unknown {
                        bits: result_bits,
                        taint,
                    }
                } else {
                    Self::Concrete {
                        value: *a % *b,
                        bits: result_bits,
                        taint,
                    }
                }
            }
            (_, rhs) if rhs.is_concrete_value(1) => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvurem(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Signed remainder.
    pub fn srem(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        if other.is_concrete_value(1) {
            return Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            };
        }
        let (a_bv, b_bv, result_bits) = self.normalize_widths_signed(ctx, other);
        Self::Symbolic {
            ast: a_bv.bvsrem(&b_bv),
            bits: result_bits,
            taint,
            _marker: PhantomData,
        }
    }

    /// Two's complement negation.
    pub fn neg(&self, ctx: &'ctx Context) -> Self {
        let taint = self.get_taint();
        match self {
            Self::Concrete { value, bits, .. } => {
                let mask = if *bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << *bits) - 1
                };
                Self::Concrete {
                    value: (!*value).wrapping_add(1) & mask,
                    bits: *bits,
                    taint,
                }
            }
            _ => {
                let bv = self.to_bv(ctx);
                Self::Symbolic {
                    ast: bv.bvneg(),
                    bits: self.bits(),
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    // ==================== Bitwise Operations ====================

    /// Bitwise AND.
    pub fn and(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        let result_bits = self.bits().max(other.bits());
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => Self::Concrete {
                value: *a & *b,
                bits: (*bits).max(*b_bits),
                taint,
            },
            (_, rhs) if rhs.is_zero() => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            (lhs, _) if lhs.is_zero() => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            (_, rhs) if rhs.is_all_ones_for(result_bits) => self.clone().with_taint(taint),
            (lhs, _) if lhs.is_all_ones_for(result_bits) => other.clone().with_taint(taint),
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => self.clone().with_taint(taint),
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvand(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Bitwise OR.
    pub fn or(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        let result_bits = self.bits().max(other.bits());
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => Self::Concrete {
                value: *a | *b,
                bits: (*bits).max(*b_bits),
                taint,
            },
            (_, rhs) if rhs.is_zero() => self.clone().with_taint(taint),
            (lhs, _) if lhs.is_zero() => other.clone().with_taint(taint),
            (_, rhs) if rhs.is_all_ones_for(result_bits) => Self::Concrete {
                value: Self::mask_for_bits(result_bits),
                bits: result_bits,
                taint,
            },
            (lhs, _) if lhs.is_all_ones_for(result_bits) => Self::Concrete {
                value: Self::mask_for_bits(result_bits),
                bits: result_bits,
                taint,
            },
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => self.clone().with_taint(taint),
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvor(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Bitwise XOR.
    pub fn xor(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (
                Self::Concrete { value: a, bits, .. },
                Self::Concrete {
                    value: b,
                    bits: b_bits,
                    ..
                },
            ) => Self::Concrete {
                value: *a ^ *b,
                bits: (*bits).max(*b_bits),
                taint,
            },
            (_, rhs) if rhs.is_zero() => self.clone().with_taint(taint),
            (lhs, _) if lhs.is_zero() => other.clone().with_taint(taint),
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => Self::Concrete {
                value: 0,
                bits: self.bits().max(other.bits()),
                taint,
            },
            _ => {
                let (a_bv, b_bv, result_bits) = self.normalize_widths(ctx, other);
                Self::Symbolic {
                    ast: a_bv.bvxor(&b_bv),
                    bits: result_bits,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Bitwise NOT.
    pub fn not(&self, ctx: &'ctx Context) -> Self {
        let taint = self.get_taint();
        match self {
            Self::Concrete { value, bits, .. } => {
                let mask = if *bits >= 64 {
                    u64::MAX
                } else {
                    (1u64 << *bits) - 1
                };
                Self::Concrete {
                    value: !*value & mask,
                    bits: *bits,
                    taint,
                }
            }
            _ => {
                let bv = self.to_bv(ctx);
                Self::Symbolic {
                    ast: bv.bvnot(),
                    bits: self.bits(),
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    // ==================== Shift Operations ====================

    /// Logical left shift.
    pub fn shl(&self, ctx: &'ctx Context, amount: &Self) -> Self {
        let taint = self.get_taint() | amount.get_taint();
        match (self, amount) {
            (_, amt) if amt.is_zero() => self.clone().with_taint(taint),
            (Self::Concrete { value, bits, .. }, Self::Concrete { value: amt, .. }) => {
                Self::Concrete {
                    value: Self::concrete_logical_shift_left(*value, *bits, *amt),
                    bits: *bits,
                    taint,
                }
            }
            _ => {
                let a_bv = self.to_bv(ctx);
                let b_bv = self.normalize_shift_amount(ctx, amount);
                Self::Symbolic {
                    ast: a_bv.bvshl(&b_bv),
                    bits: self.bits(),
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Logical right shift.
    pub fn lshr(&self, ctx: &'ctx Context, amount: &Self) -> Self {
        let taint = self.get_taint() | amount.get_taint();
        match (self, amount) {
            (_, amt) if amt.is_zero() => self.clone().with_taint(taint),
            (Self::Concrete { value, bits, .. }, Self::Concrete { value: amt, .. }) => {
                Self::Concrete {
                    value: Self::concrete_logical_shift_right(*value, *bits, *amt),
                    bits: *bits,
                    taint,
                }
            }
            _ => {
                let a_bv = self.to_bv(ctx);
                let b_bv = self.normalize_shift_amount(ctx, amount);
                Self::Symbolic {
                    ast: a_bv.bvlshr(&b_bv),
                    bits: self.bits(),
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Arithmetic right shift.
    pub fn ashr(&self, ctx: &'ctx Context, amount: &Self) -> Self {
        let taint = self.get_taint() | amount.get_taint();
        if amount.is_zero() {
            return self.clone().with_taint(taint);
        }
        let a_bv = self.to_bv(ctx);
        let b_bv = self.normalize_shift_amount(ctx, amount);
        Self::Symbolic {
            ast: a_bv.bvashr(&b_bv),
            bits: self.bits(),
            taint,
            _marker: PhantomData,
        }
    }

    // ==================== Comparison Operations ====================

    /// Equality comparison (returns 1-bit result).
    pub fn eq(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (Self::Concrete { value: a, .. }, Self::Concrete { value: b, .. }) => Self::Concrete {
                value: if *a == *b { 1 } else { 0 },
                bits: 1,
                taint,
            },
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => Self::Concrete {
                value: 1,
                bits: 1,
                taint,
            },
            _ => {
                let (a_bv, b_bv, _) = self.normalize_widths(ctx, other);
                let cond = a_bv.eq(&b_bv);
                let one = BV::from_i64(1, 1);
                let zero = BV::from_i64(0, 1);
                Self::Symbolic {
                    ast: cond.ite(&one, &zero),
                    bits: 1,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Unsigned less than comparison.
    pub fn ult(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (Self::Concrete { value: a, .. }, Self::Concrete { value: b, .. }) => Self::Concrete {
                value: if *a < *b { 1 } else { 0 },
                bits: 1,
                taint,
            },
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => Self::Concrete {
                value: 0,
                bits: 1,
                taint,
            },
            _ => {
                let (a_bv, b_bv, _) = self.normalize_widths(ctx, other);
                let cond = a_bv.bvult(&b_bv);
                let one = BV::from_i64(1, 1);
                let zero = BV::from_i64(0, 1);
                Self::Symbolic {
                    ast: cond.ite(&one, &zero),
                    bits: 1,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Unsigned less than or equal comparison.
    pub fn ule(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        match (self, other) {
            (Self::Concrete { value: a, .. }, Self::Concrete { value: b, .. }) => Self::Concrete {
                value: if *a <= *b { 1 } else { 0 },
                bits: 1,
                taint,
            },
            (lhs, rhs) if lhs.same_symbolic_ast(rhs) => Self::Concrete {
                value: 1,
                bits: 1,
                taint,
            },
            _ => {
                let (a_bv, b_bv, _) = self.normalize_widths(ctx, other);
                let cond = a_bv.bvule(&b_bv);
                let one = BV::from_i64(1, 1);
                let zero = BV::from_i64(0, 1);
                Self::Symbolic {
                    ast: cond.ite(&one, &zero),
                    bits: 1,
                    taint,
                    _marker: PhantomData,
                }
            }
        }
    }

    /// Signed less than comparison.
    pub fn slt(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        if self.same_symbolic_ast(other) {
            return Self::Concrete {
                value: 0,
                bits: 1,
                taint,
            };
        }
        let (a_bv, b_bv, _) = self.normalize_widths_signed(ctx, other);
        let cond = a_bv.bvslt(&b_bv);
        let one = BV::from_i64(1, 1);
        let zero = BV::from_i64(0, 1);
        Self::Symbolic {
            ast: cond.ite(&one, &zero),
            bits: 1,
            taint,
            _marker: PhantomData,
        }
    }

    /// Signed less than or equal comparison.
    pub fn sle(&self, ctx: &'ctx Context, other: &Self) -> Self {
        let taint = self.get_taint() | other.get_taint();
        if self.same_symbolic_ast(other) {
            return Self::Concrete {
                value: 1,
                bits: 1,
                taint,
            };
        }
        let (a_bv, b_bv, _) = self.normalize_widths_signed(ctx, other);
        let cond = a_bv.bvsle(&b_bv);
        let one = BV::from_i64(1, 1);
        let zero = BV::from_i64(0, 1);
        Self::Symbolic {
            ast: cond.ite(&one, &zero),
            bits: 1,
            taint,
            _marker: PhantomData,
        }
    }

    /// Check if value is zero (returns boolean).
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Concrete { value, .. } => *value == 0,
            _ => false,
        }
    }

    /// Check if value is non-zero (returns boolean).
    pub fn is_nonzero(&self) -> bool {
        match self {
            Self::Concrete { value, .. } => *value != 0,
            _ => false,
        }
    }
}

impl<'ctx> fmt::Debug for SymValue<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Concrete { value, bits, taint } => {
                if *taint != 0 {
                    write!(f, "Concrete(0x{:x}, {}, T:0x{:x})", value, bits, taint)
                } else {
                    write!(f, "Concrete(0x{:x}, {})", value, bits)
                }
            }
            Self::Symbolic { bits, taint, .. } => {
                if *taint != 0 {
                    write!(f, "Symbolic({}, T:0x{:x})", bits, taint)
                } else {
                    write!(f, "Symbolic({})", bits)
                }
            }
            Self::Unknown { bits, taint } => {
                if *taint != 0 {
                    write!(f, "Unknown({}, T:0x{:x})", bits, taint)
                } else {
                    write!(f, "Unknown({})", bits)
                }
            }
        }
    }
}

impl<'ctx> fmt::Display for SymValue<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let taint = self.get_taint();
        let taint_suffix = if taint != 0 {
            format!(" T:0x{:x}", taint)
        } else {
            String::new()
        };
        match self {
            Self::Concrete { value, bits, .. } => {
                write!(f, "0x{:x}:{}{}", value, bits, taint_suffix)
            }
            Self::Symbolic { bits, .. } => write!(f, "<sym:{}>{}", bits, taint_suffix),
            Self::Unknown { bits, .. } => write!(f, "<unk:{}>{}", bits, taint_suffix),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concrete_ops() {
        let ctx = Context::thread_local();

        let a = SymValue::concrete(10, 32);
        let b = SymValue::concrete(3, 32);

        let sum = a.add(&ctx, &b);
        assert_eq!(sum.as_concrete(), Some(13));

        let diff = a.sub(&ctx, &b);
        assert_eq!(diff.as_concrete(), Some(7));

        let prod = a.mul(&ctx, &b);
        assert_eq!(prod.as_concrete(), Some(30));

        let quot = a.udiv(&ctx, &b);
        assert_eq!(quot.as_concrete(), Some(3));

        let rem = a.urem(&ctx, &b);
        assert_eq!(rem.as_concrete(), Some(1));
    }

    #[test]
    fn test_bitwise_ops() {
        let ctx = Context::thread_local();

        let a = SymValue::concrete(0b1100, 8);
        let b = SymValue::concrete(0b1010, 8);

        assert_eq!(a.and(&ctx, &b).as_concrete(), Some(0b1000));
        assert_eq!(a.or(&ctx, &b).as_concrete(), Some(0b1110));
        assert_eq!(a.xor(&ctx, &b).as_concrete(), Some(0b0110));
        assert_eq!(a.not(&ctx).as_concrete(), Some(0b11110011));
    }

    #[test]
    fn test_shift_ops() {
        let ctx = Context::thread_local();

        let a = SymValue::concrete(0b1100, 8);
        let amt = SymValue::concrete(2, 8);

        assert_eq!(a.shl(&ctx, &amt).as_concrete(), Some(0b110000));
        assert_eq!(a.lshr(&ctx, &amt).as_concrete(), Some(0b0011));
    }

    #[test]
    fn test_comparison_ops() {
        let ctx = Context::thread_local();

        let a = SymValue::concrete(10, 32);
        let b = SymValue::concrete(20, 32);

        assert_eq!(a.eq(&ctx, &a).as_concrete(), Some(1));
        assert_eq!(a.eq(&ctx, &b).as_concrete(), Some(0));
        assert_eq!(a.ult(&ctx, &b).as_concrete(), Some(1));
        assert_eq!(b.ult(&ctx, &a).as_concrete(), Some(0));
    }

    #[test]
    fn test_symbolic_creation() {
        let ctx = Context::thread_local();

        let sym = SymValue::new_symbolic(&ctx, "x", 64);
        assert!(sym.is_symbolic());
        assert_eq!(sym.bits(), 64);
    }

    #[test]
    fn test_symbolic_identity_fast_paths() {
        let ctx = Context::thread_local();

        let sym = SymValue::new_symbolic(&ctx, "x", 64);
        let zero = SymValue::concrete(0, 64);
        let one = SymValue::concrete(1, 64);

        let add = sym.add(&ctx, &zero);
        let sub = sym.sub(&ctx, &zero);
        let mul = sym.mul(&ctx, &one);
        let and = sym.and(&ctx, &SymValue::concrete(u64::MAX, 64));
        let or = sym.or(&ctx, &zero);
        let xor = sym.xor(&ctx, &zero);
        let shl = sym.shl(&ctx, &zero);
        let lshr = sym.lshr(&ctx, &zero);
        let ashr = sym.ashr(&ctx, &zero);

        assert!(add.same_symbolic_ast(&sym));
        assert!(sub.same_symbolic_ast(&sym));
        assert!(mul.same_symbolic_ast(&sym));
        assert!(and.same_symbolic_ast(&sym));
        assert!(or.same_symbolic_ast(&sym));
        assert!(xor.same_symbolic_ast(&sym));
        assert!(shl.same_symbolic_ast(&sym));
        assert!(lshr.same_symbolic_ast(&sym));
        assert!(ashr.same_symbolic_ast(&sym));
    }

    #[test]
    fn test_symbolic_division_remainder_fast_paths() {
        let ctx = Context::thread_local();

        let sym = SymValue::new_symbolic(&ctx, "x", 64);
        let one = SymValue::concrete(1, 64);

        let udiv = sym.udiv(&ctx, &one);
        let sdiv = sym.sdiv(&ctx, &one);
        let urem = sym.urem(&ctx, &one);
        let srem = sym.srem(&ctx, &one);

        assert!(udiv.same_symbolic_ast(&sym));
        assert!(sdiv.same_symbolic_ast(&sym));
        assert_eq!(urem.as_concrete(), Some(0));
        assert_eq!(srem.as_concrete(), Some(0));
    }

    #[test]
    fn test_symbolic_self_rules() {
        let ctx = Context::thread_local();

        let sym = SymValue::new_symbolic(&ctx, "x", 64);

        assert_eq!(sym.sub(&ctx, &sym).as_concrete(), Some(0));
        assert_eq!(sym.xor(&ctx, &sym).as_concrete(), Some(0));
        assert_eq!(sym.eq(&ctx, &sym).as_concrete(), Some(1));
        assert_eq!(sym.ult(&ctx, &sym).as_concrete(), Some(0));
        assert_eq!(sym.ule(&ctx, &sym).as_concrete(), Some(1));
        assert_eq!(sym.slt(&ctx, &sym).as_concrete(), Some(0));
        assert_eq!(sym.sle(&ctx, &sym).as_concrete(), Some(1));
    }

    #[test]
    fn test_all_ones_fast_paths_require_full_result_width() {
        let ctx = Context::thread_local();

        let sym = SymValue::new_symbolic(&ctx, "x", 64);
        let byte_ones = SymValue::concrete(0xff, 8);

        let and = sym.and(&ctx, &byte_ones);
        let or = sym.or(&ctx, &byte_ones);

        assert!(and.is_symbolic());
        assert!(or.is_symbolic());
        assert!(!and.same_symbolic_ast(&sym));
        assert!(!or.same_symbolic_ast(&sym));
    }

    #[test]
    fn test_extension() {
        let ctx = Context::thread_local();

        let a = SymValue::concrete(0xFF, 8);

        let zext = a.zero_extend(&ctx, 16);
        assert_eq!(zext.as_concrete(), Some(0xFF));
        assert_eq!(zext.bits(), 16);

        let sext = a.sign_extend(&ctx, 16);
        assert_eq!(sext.bits(), 16);
        // 0xFF sign-extended = 0xFFFF
        assert_eq!(sext.as_concrete(), Some(0xFFFF));
    }

    #[test]
    fn test_extract() {
        let ctx = Context::thread_local();

        let a = SymValue::concrete(0xABCD, 16);
        let low = a.extract(&ctx, 7, 0);
        assert_eq!(low.as_concrete(), Some(0xCD));
        assert_eq!(low.bits(), 8);

        let high = a.extract(&ctx, 15, 8);
        assert_eq!(high.as_concrete(), Some(0xAB));
    }

    #[test]
    fn test_extract_full_width_returns_same_symbolic_ast() {
        let ctx = Context::thread_local();
        let sym = SymValue::new_symbolic(&ctx, "x", 32);
        let extracted = sym.extract(&ctx, 31, 0);
        assert!(extracted.same_symbolic_ast(&sym));
    }

    #[test]
    fn test_extract_zero_extend_low_bits_returns_original_ast() {
        let ctx = Context::thread_local();
        let sym = SymValue::new_symbolic(&ctx, "x", 32);
        let widened = sym.zero_extend(&ctx, 64);
        let extracted = widened.extract(&ctx, 31, 0);
        assert!(extracted.same_symbolic_ast(&sym));
    }

    #[test]
    fn test_extract_sign_extend_low_bits_returns_original_ast() {
        let ctx = Context::thread_local();
        let sym = SymValue::new_symbolic(&ctx, "x", 32);
        let widened = sym.sign_extend(&ctx, 64);
        let extracted = widened.extract(&ctx, 31, 0);
        assert!(extracted.same_symbolic_ast(&sym));
    }

    #[test]
    fn test_zero_extend_flattens_nested_extensions() {
        let ctx = Context::thread_local();
        let sym = SymValue::new_symbolic(&ctx, "x", 16);
        let widened = sym.zero_extend(&ctx, 32).zero_extend(&ctx, 64);
        let direct = sym.zero_extend(&ctx, 64);
        assert!(widened.same_symbolic_ast(&direct));
    }

    #[test]
    fn test_sign_extend_flattens_nested_extensions() {
        let ctx = Context::thread_local();
        let sym = SymValue::new_symbolic(&ctx, "x", 16);
        let widened = sym.sign_extend(&ctx, 32).sign_extend(&ctx, 64);
        let direct = sym.sign_extend(&ctx, 64);
        assert!(widened.same_symbolic_ast(&direct));
    }
}

#[cfg(test)]
mod bitwidth_tests {
    use super::*;

    #[test]
    fn test_add_different_bitwidths_concrete() {
        let ctx = Context::thread_local();

        // Create values of different widths
        let val8 = SymValue::concrete(5, 8);
        let val64 = SymValue::concrete(10, 64);

        // This should handle the mismatch gracefully
        let result = val8.add(&ctx, &val64);
        assert_eq!(result.as_concrete(), Some(15));
        assert_eq!(result.bits(), 64); // Result should use larger width
    }

    #[test]
    fn test_shl_different_bitwidths_concrete() {
        let ctx = Context::thread_local();

        // Create values of different widths - this is common in real code
        // where shift amount might be 8-bit but value is 64-bit
        let val64 = SymValue::concrete(5, 64);
        let shift8 = SymValue::concrete(2, 8);

        // This should handle the mismatch gracefully
        let result = val64.shl(&ctx, &shift8);
        assert_eq!(result.as_concrete(), Some(20)); // 5 << 2 = 20
        assert_eq!(result.bits(), 64); // Result keeps value's width
    }

    #[test]
    fn test_concrete_shifts_past_bitwidth_zero_fill_instead_of_panicking() {
        let ctx = Context::thread_local();

        let val64 = SymValue::concrete(0x1234_5678_9abc_def0, 64);
        let shift64 = SymValue::concrete(64, 64);
        let shift65 = SymValue::concrete(65, 8);

        assert_eq!(val64.shl(&ctx, &shift64).as_concrete(), Some(0));
        assert_eq!(val64.lshr(&ctx, &shift64).as_concrete(), Some(0));
        assert_eq!(val64.shl(&ctx, &shift65).as_concrete(), Some(0));
        assert_eq!(val64.lshr(&ctx, &shift65).as_concrete(), Some(0));

        let val8 = SymValue::concrete(0b1111_0000, 8);
        let shift8 = SymValue::concrete(8, 8);
        assert_eq!(val8.shl(&ctx, &shift8).as_concrete(), Some(0));
        assert_eq!(val8.lshr(&ctx, &shift8).as_concrete(), Some(0));
    }

    #[test]
    fn test_symbolic_different_bitwidths() {
        let ctx = Context::thread_local();

        // Create symbolic values of different widths
        let sym8 = SymValue::new_symbolic(&ctx, "x", 8);
        let sym64 = SymValue::new_symbolic(&ctx, "y", 64);

        // This should NOT crash with Z3 assertion anymore!
        let result = sym8.add(&ctx, &sym64);
        assert!(result.is_symbolic());
        assert_eq!(result.bits(), 64); // Result should use larger width
    }

    #[test]
    fn test_symbolic_shift_different_bitwidths() {
        let ctx = Context::thread_local();

        // Symbolic value with smaller shift amount
        let sym64 = SymValue::new_symbolic(&ctx, "val", 64);
        let shift8 = SymValue::new_symbolic(&ctx, "shift", 8);

        // This should NOT crash with Z3 assertion anymore!
        let result = sym64.shl(&ctx, &shift8);
        assert!(result.is_symbolic());
        assert_eq!(result.bits(), 64); // Shift preserves value width
    }

    #[test]
    fn test_comparison_different_bitwidths() {
        let ctx = Context::thread_local();

        // Create symbolic values of different widths
        let sym8 = SymValue::new_symbolic(&ctx, "x", 8);
        let sym64 = SymValue::new_symbolic(&ctx, "y", 64);

        // Comparison should NOT crash
        let result = sym8.ult(&ctx, &sym64);
        assert!(result.is_symbolic());
        assert_eq!(result.bits(), 1); // Comparison returns 1-bit
    }

    #[test]
    fn test_bitwise_different_bitwidths() {
        let ctx = Context::thread_local();

        let sym8 = SymValue::new_symbolic(&ctx, "x", 8);
        let sym32 = SymValue::new_symbolic(&ctx, "y", 32);

        // AND, OR, XOR should NOT crash
        let and_result = sym8.and(&ctx, &sym32);
        assert!(and_result.is_symbolic());
        assert_eq!(and_result.bits(), 32);

        let or_result = sym8.or(&ctx, &sym32);
        assert!(or_result.is_symbolic());
        assert_eq!(or_result.bits(), 32);

        let xor_result = sym8.xor(&ctx, &sym32);
        assert!(xor_result.is_symbolic());
        assert_eq!(xor_result.bits(), 32);
    }

    #[test]
    fn test_taint_propagation() {
        let ctx = Context::thread_local();

        // Create tainted and untainted values
        const TAINT_USER_INPUT: u64 = 0x1;
        const TAINT_NETWORK: u64 = 0x2;

        let tainted = SymValue::concrete_tainted(42, 32, TAINT_USER_INPUT);
        let untainted = SymValue::concrete(10, 32);

        // Taint should propagate through operations
        let sum = tainted.add(&ctx, &untainted);
        assert!(sum.is_tainted());
        assert!(sum.has_taint(TAINT_USER_INPUT));
        assert!(!sum.has_taint(TAINT_NETWORK));

        // Multiple taints should merge via OR
        let network_tainted = SymValue::concrete_tainted(5, 32, TAINT_NETWORK);
        let combined = tainted.add(&ctx, &network_tainted);
        assert!(combined.has_taint(TAINT_USER_INPUT));
        assert!(combined.has_taint(TAINT_NETWORK));
        assert_eq!(combined.get_taint(), TAINT_USER_INPUT | TAINT_NETWORK);

        // Untainted operations stay untainted
        let clean = untainted.add(&ctx, &SymValue::concrete(1, 32));
        assert!(!clean.is_tainted());
    }

    #[test]
    fn test_taint_with_symbolic_values() {
        let ctx = Context::thread_local();

        const TAINT_STDIN: u64 = 0x4;

        // Create a tainted symbolic value (e.g., user input)
        let sym_input = SymValue::new_symbolic_tainted(&ctx, "stdin", 64, TAINT_STDIN);
        assert!(sym_input.is_tainted());
        assert!(sym_input.has_taint(TAINT_STDIN));

        // Operations with tainted symbolic values propagate taint
        let constant = SymValue::concrete(0x100, 64);
        let result = sym_input.add(&ctx, &constant);
        assert!(result.is_tainted());
        assert!(result.has_taint(TAINT_STDIN));

        // Shift by tainted amount propagates taint
        let shift_amt = SymValue::concrete_tainted(4, 32, TAINT_STDIN);
        let shifted = constant.shl(&ctx, &shift_amt);
        assert!(shifted.is_tainted());
    }

    #[test]
    fn test_zero_width_values_are_normalized() {
        let ctx = Context::thread_local();
        let v = SymValue::concrete(0, 0);
        assert_eq!(v.bits(), 1);
        let bv = v.to_bv(&ctx);
        assert_eq!(bv.get_size(), 1);

        let u = SymValue::unknown(0);
        assert_eq!(u.bits(), 1);
        assert_eq!(u.to_bv(&ctx).get_size(), 1);
    }

    #[test]
    fn test_extract_out_of_range_returns_safe_unknown() {
        let ctx = Context::thread_local();
        let v = SymValue::concrete(0x41, 8);
        let out = v.extract(&ctx, 15, 16);
        assert_eq!(out.bits(), 1);
        assert!(out.is_unknown());
    }

    #[test]
    fn test_symbolic_identity_normalization() {
        let ctx = Context::thread_local();
        let x = SymValue::new_symbolic(&ctx, "x", 32);
        let zero = SymValue::concrete(0, 32);
        let one = SymValue::concrete(1, 32);

        let add = x.add(&ctx, &zero);
        assert!(add.is_symbolic());
        assert!(add.as_ast().unwrap().ast_eq(x.as_ast().unwrap()));

        let mul = x.mul(&ctx, &one);
        assert!(mul.is_symbolic());
        assert!(mul.as_ast().unwrap().ast_eq(x.as_ast().unwrap()));

        let shl = x.shl(&ctx, &zero);
        assert!(shl.is_symbolic());
        assert!(shl.as_ast().unwrap().ast_eq(x.as_ast().unwrap()));
    }

    #[test]
    fn test_symbolic_self_rewrite_rules() {
        let ctx = Context::thread_local();
        let x = SymValue::new_symbolic(&ctx, "x", 32);

        assert_eq!(x.sub(&ctx, &x).as_concrete(), Some(0));
        assert_eq!(x.xor(&ctx, &x).as_concrete(), Some(0));
        assert_eq!(x.eq(&ctx, &x).as_concrete(), Some(1));
        assert_eq!(x.ult(&ctx, &x).as_concrete(), Some(0));
        assert_eq!(x.ule(&ctx, &x).as_concrete(), Some(1));
    }

    #[test]
    fn test_all_ones_normalization_is_width_sensitive() {
        let ctx = Context::thread_local();
        let x = SymValue::new_symbolic(&ctx, "x", 32);
        let mask8 = SymValue::concrete(0xff, 8);
        let mask32 = SymValue::concrete(u32::MAX as u64, 32);

        let narrowed = x.and(&ctx, &mask8);
        assert!(narrowed.is_symbolic());
        assert!(!narrowed.as_ast().unwrap().ast_eq(x.as_ast().unwrap()));

        let widened = x.and(&ctx, &mask32);
        assert!(widened.is_symbolic());
        assert!(widened.as_ast().unwrap().ast_eq(x.as_ast().unwrap()));
    }
}
