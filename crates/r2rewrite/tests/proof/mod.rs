//! The Z3 encoding of terms, the twin of `r2rewrite::eval`.
//!
//! A term of width `w` is a bit-vector of `w` bits. A Bool-typed term is a
//! bit-vector of its storage width holding 0 or 1; a Bool-typed variable is
//! `ite(b, 1, 0)` over a fresh Boolean, which is the invariant every boolean
//! producer in the machine maintains. Every rule's equivalence is checked by
//! asserting `before != after` and requiring Unsat.

#![allow(dead_code)]

use std::collections::HashMap;

use r2rewrite::{TermArena, TermId, TermKind};
use r2ssa::{
    MachineArithmeticFlagOp, MachineArithmeticOp, MachineBitwiseOp, MachineBooleanOp,
    MachineCastKind, MachineComparisonOp, MachineOvershiftBehavior, MachineShiftKind,
    MachineSignedness, MachineType,
};
use z3::ast::{BV, Bool};

pub struct Encoder<'a> {
    arena: &'a TermArena,
    variables: HashMap<(u32, MachineType), BV>,
    memo: HashMap<TermId, BV>,
    /// `leaf == definition` for every defined leaf the encoding met: the
    /// hypotheses under which a definition-aware rule is an equivalence, to
    /// be asserted beside the negated equation.
    hypotheses: Vec<Bool>,
}

fn zero(width: u32) -> BV {
    BV::from_u64(0, width)
}

fn one(width: u32) -> BV {
    BV::from_u64(1, width)
}

fn resize(bv: &BV, width: u32) -> BV {
    let have = bv.get_size();
    if have < width {
        bv.zero_ext(width - have)
    } else if have > width {
        bv.extract(width - 1, 0)
    } else {
        bv.clone()
    }
}

fn as_bool(bv: &BV) -> Bool {
    bv.eq(zero(bv.get_size())).not()
}

fn from_bool(b: &Bool, width: u32) -> BV {
    b.ite(&one(width), &zero(width))
}

impl<'a> Encoder<'a> {
    pub fn new(arena: &'a TermArena) -> Self {
        Self {
            arena,
            variables: HashMap::new(),
            memo: HashMap::new(),
            hypotheses: Vec::new(),
        }
    }

    pub fn hypotheses(&self) -> &[Bool] {
        &self.hypotheses
    }

    pub fn variables(&self) -> &HashMap<(u32, MachineType), BV> {
        &self.variables
    }

    fn variable(&mut self, index: u32, ty: MachineType) -> BV {
        if let Some(bv) = self.variables.get(&(index, ty)) {
            return bv.clone();
        }
        let width = ty.width_bits();
        let bv = match ty {
            MachineType::Bool { .. } => {
                let b = Bool::new_const(format!("b{index}_{width}"));
                from_bool(&b, width)
            }
            _ => BV::new_const(format!("v{index}_{width}"), width),
        };
        self.variables.insert((index, ty), bv.clone());
        bv
    }

    pub fn encode(&mut self, id: TermId) -> BV {
        if let Some(bv) = self.memo.get(&id) {
            return bv.clone();
        }
        let term = self.arena.term(id);
        let width = term.width_bits();
        let bv = match term.kind {
            TermKind::Variable(index) => {
                let bv = self.variable(index, term.ty);
                if let Some(definition) = self.arena.definition(id) {
                    let defined = self.encode(definition);
                    self.hypotheses.push(bv.eq(defined));
                }
                bv
            }
            TermKind::Leaf(expr) | TermKind::Opaque(expr) => {
                // A base node in a proof term is a free variable keyed by
                // its id; templates do not build these, but nothing forbids
                // a fixture from encoding a real term.
                self.variable(0x8000_0000 | expr.index() as u32, term.ty)
            }
            TermKind::Literal(bits) => BV::from_u64(bits.bits(), width),
            TermKind::Arithmetic { op, left, right } => {
                let l = self.encode(left);
                let r = self.encode(right);
                match op {
                    MachineArithmeticOp::Add => l.bvadd(r),
                    MachineArithmeticOp::Subtract => l.bvsub(r),
                    MachineArithmeticOp::Multiply => l.bvmul(r),
                }
            }
            TermKind::Negate(input) => self.encode(input).bvneg(),
            TermKind::Bitwise { op, left, right } => {
                let l = self.encode(left);
                let r = self.encode(right);
                match op {
                    MachineBitwiseOp::And => l.bvand(r),
                    MachineBitwiseOp::Or => l.bvor(r),
                    MachineBitwiseOp::Xor => l.bvxor(r),
                }
            }
            TermKind::BitwiseNot(input) => self.encode(input).bvnot(),
            TermKind::Boolean { op, left, right } => {
                let l = as_bool(&self.encode(left));
                let r = as_bool(&self.encode(right));
                let result = match op {
                    MachineBooleanOp::And => Bool::and(&[l, r]),
                    MachineBooleanOp::Or => Bool::or(&[l, r]),
                    MachineBooleanOp::Xor => l.eq(r).not(),
                };
                from_bool(&result, width)
            }
            TermKind::BooleanNot(input) => {
                let x = self.encode(input);
                from_bool(&as_bool(&x).not(), width)
            }
            TermKind::Shift {
                kind,
                overshift,
                value,
                count,
            } => {
                let v = self.encode(value);
                let c = self.encode(count);
                let count_width = c.get_size();
                let c_wide = if count_width < 64 {
                    c.zero_ext(64 - count_width)
                } else {
                    c.clone()
                };
                let c_wide = match overshift {
                    MachineOvershiftBehavior::MaskCount => {
                        c_wide.bvand(BV::from_u64(u64::from(width) - 1, 64))
                    }
                    _ => c_wide,
                };
                let over = c_wide.bvuge(BV::from_u64(u64::from(width), 64));
                let amount = resize(&c_wide, width);
                let sign_fill = v.bvashr(BV::from_u64(u64::from(width) - 1, width));
                match kind {
                    MachineShiftKind::Left => over.ite(&zero(width), &v.bvshl(amount)),
                    MachineShiftKind::LogicalRight => over.ite(&zero(width), &v.bvlshr(amount)),
                    MachineShiftKind::ArithmeticRight => {
                        let overflowed = match overshift {
                            MachineOvershiftBehavior::Zero => zero(width),
                            _ => sign_fill,
                        };
                        over.ite(&overflowed, &v.bvashr(amount))
                    }
                }
            }
            TermKind::Compare {
                op,
                interpretation,
                left,
                right,
            } => {
                let l = self.encode(left);
                let r = self.encode(right);
                let result = match (op, interpretation) {
                    (MachineComparisonOp::Equal, _) => l.eq(r),
                    (MachineComparisonOp::NotEqual, _) => l.eq(r).not(),
                    (MachineComparisonOp::LessThan, MachineSignedness::Unsigned) => l.bvult(r),
                    (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Unsigned) => {
                        l.bvule(r)
                    }
                    (MachineComparisonOp::LessThan, MachineSignedness::Signed) => l.bvslt(r),
                    (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Signed) => l.bvsle(r),
                };
                from_bool(&result, width)
            }
            TermKind::Flag { op, left, right } => {
                let l = self.encode(left);
                let r = self.encode(right);
                let lw = l.get_size();
                let result = match op {
                    MachineArithmeticFlagOp::UnsignedCarry => {
                        let sum = l.zero_ext(1).bvadd(r.zero_ext(1));
                        sum.extract(lw, lw).eq(one(1))
                    }
                    MachineArithmeticFlagOp::SignedCarry => {
                        let exact = l.sign_ext(1).bvadd(r.sign_ext(1));
                        let wrapped = l.bvadd(r.clone()).sign_ext(1);
                        exact.eq(wrapped).not()
                    }
                    MachineArithmeticFlagOp::SignedBorrow => {
                        let exact = l.sign_ext(1).bvsub(r.sign_ext(1));
                        let wrapped = l.bvsub(r.clone()).sign_ext(1);
                        exact.eq(wrapped).not()
                    }
                };
                from_bool(&result, width)
            }
            TermKind::Cast { kind, input } => {
                let x = self.encode(input);
                let from = x.get_size();
                match kind {
                    MachineCastKind::ZeroExtend => x.zero_ext(width - from),
                    MachineCastKind::SignExtend => x.sign_ext(width - from),
                    MachineCastKind::Truncate => x.extract(width - 1, 0),
                    MachineCastKind::BitReinterpret
                    | MachineCastKind::IntegerToAddress
                    | MachineCastKind::AddressToInteger => x,
                }
            }
            TermKind::Extract { input, lsb_bits } => {
                self.encode(input).extract(lsb_bits + width - 1, lsb_bits)
            }
            TermKind::Concat { high, low } => {
                let h = self.encode(high);
                let l = self.encode(low);
                h.concat(l)
            }
            TermKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                let c = as_bool(&self.encode(condition));
                let t = self.encode(if_true);
                let f = self.encode(if_false);
                c.ite(&t, &f)
            }
        };
        assert_eq!(
            bv.get_size(),
            width,
            "encoding of {:?} has the wrong width",
            term
        );
        self.memo.insert(id, bv.clone());
        bv
    }
}
