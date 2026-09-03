//! The C type at every boundary, stated from the arena and the plan.

mod fixture;

use std::collections::BTreeMap;

use fixture::{RAX, RDI, artifact, konst, projection, reg, tmp, value_named};
use r2il::R2ILOp;
use r2rewrite::{CValue, RenderTypes, c_type_of, promoted, typed_boundaries};
use r2ssa::{MachineExprId, MachineExprKind, MachineSignedness, MachineType, ValueId};
use r2types::CTypeLike;

/// A plan that declares some values and inlines others.
#[derive(Default)]
struct Plan {
    declared: BTreeMap<ValueId, CTypeLike>,
    inlined: BTreeMap<ValueId, MachineExprId>,
}

impl RenderTypes for Plan {
    fn declaration_type(&self, value: ValueId) -> Option<CTypeLike> {
        self.declared.get(&value).cloned()
    }

    fn inline_root(&self, value: ValueId) -> Option<MachineExprId> {
        self.inlined.get(&value).copied()
    }
}

fn ret() -> R2ILOp {
    R2ILOp::Return {
        target: konst(0, 8),
    }
}

fn root_of(projection: &r2ssa::MachineProjection, value: ValueId) -> MachineExprId {
    projection
        .entity_for_output(value)
        .expect("value has an entity")
        .root()
}

#[test]
fn a_signed_comparison_requires_signed_operands_and_produces_a_truth_value() {
    let artifact = artifact(vec![
        R2ILOp::IntSLess {
            dst: tmp(0x100, 1),
            a: reg(RDI, 8),
            b: konst(5, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: konst(0, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let rdi = value_named(&artifact, "RDI_0");
    let less = value_named(&artifact, "tmp:100_1");
    let mut plan = Plan::default();
    plan.declared.insert(rdi, CTypeLike::u64());
    let typed = typed_boundaries(&projection, &plan);

    let root = root_of(&projection, less);
    assert_eq!(typed.required(root, 0), Some(&CTypeLike::i64()));
    assert_eq!(typed.required(root, 1), Some(&CTypeLike::i64()));
    assert_eq!(typed.produced(root), Some(&CValue::Typed(CTypeLike::Bool)));
    // The declaration is what a read of the value has; the comparison's
    // requirement differs from it, which is exactly where a cast belongs.
    assert_eq!(
        typed.value_type(rdi),
        Some(&CValue::Typed(CTypeLike::u64()))
    );
    // The constant is spelled in whatever reads it.
    let children = projection.expr(root).expect("root").kind().children();
    assert_eq!(typed.produced(children[1]), Some(&CValue::Constant));
}

#[test]
fn narrow_arithmetic_is_computed_in_int_and_read_back_at_its_width() {
    let artifact = artifact(vec![
        R2ILOp::Trunc {
            dst: tmp(0x100, 1),
            src: reg(RDI, 8),
        },
        R2ILOp::IntAdd {
            dst: tmp(0x200, 1),
            a: tmp(0x100, 1),
            b: tmp(0x100, 1),
        },
        R2ILOp::IntZExt {
            dst: reg(RAX, 8),
            src: tmp(0x200, 1),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let byte = value_named(&artifact, "tmp:100_1");
    let sum = value_named(&artifact, "tmp:200_1");
    let rax = value_named(&artifact, "RAX_1");
    let mut plan = Plan::default();
    plan.declared
        .insert(value_named(&artifact, "RDI_0"), CTypeLike::u64());
    plan.declared.insert(byte, CTypeLike::u8());
    plan.inlined.insert(sum, root_of(&projection, sum));
    let typed = typed_boundaries(&projection, &plan);

    let trunc = root_of(&projection, byte);
    assert_eq!(typed.required(trunc, 0), Some(&CTypeLike::u64()));
    assert_eq!(typed.produced(trunc), Some(&CValue::Typed(CTypeLike::u8())));

    let add = root_of(&projection, sum);
    assert_eq!(typed.required(add, 0), Some(&CTypeLike::u8()));
    assert_eq!(typed.required(add, 1), Some(&CTypeLike::u8()));
    // `uint8_t + uint8_t` is an `int`, and the sum is inlined, so a read of
    // it has that type: the reader narrows it, once, where it reads it.
    assert_eq!(typed.produced(add), Some(&CValue::Typed(CTypeLike::i32())));
    assert_eq!(
        typed.value_type(sum),
        Some(&CValue::Typed(CTypeLike::i32()))
    );

    // A zero extension requires the unsigned narrow operand, so that the
    // widening zero-fills, and produces its own width.
    let zext = root_of(&projection, rax);
    assert_eq!(typed.required(zext, 0), Some(&CTypeLike::u8()));
    assert_eq!(typed.produced(zext), Some(&CValue::Typed(CTypeLike::u64())));
}

#[test]
fn signedness_comes_from_the_node_not_the_operator() {
    let artifact = artifact(vec![
        R2ILOp::IntSRight {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: konst(3, 8),
        },
        R2ILOp::IntRight {
            dst: tmp(0x200, 8),
            a: reg(RDI, 8),
            b: konst(3, 8),
        },
        R2ILOp::IntSExt {
            dst: tmp(0x300, 8),
            src: tmp(0x400, 4),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x300, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let plan = Plan::default();
    let typed = typed_boundaries(&projection, &plan);

    let arithmetic = root_of(&projection, value_named(&artifact, "tmp:100_1"));
    assert_eq!(typed.required(arithmetic, 0), Some(&CTypeLike::i64()));
    assert_eq!(typed.required(arithmetic, 1), Some(&CTypeLike::u64()));
    assert_eq!(
        typed.produced(arithmetic),
        Some(&CValue::Typed(CTypeLike::i64()))
    );

    let logical = root_of(&projection, value_named(&artifact, "tmp:200_1"));
    assert_eq!(typed.required(logical, 0), Some(&CTypeLike::u64()));
    assert_eq!(
        typed.produced(logical),
        Some(&CValue::Typed(CTypeLike::u64()))
    );

    let sext = root_of(&projection, value_named(&artifact, "tmp:300_1"));
    assert_eq!(typed.required(sext, 0), Some(&CTypeLike::i32()));
    assert_eq!(typed.produced(sext), Some(&CValue::Typed(CTypeLike::i64())));

    // A value the plan neither declares nor inlines reads at its machine
    // type, which for an undeclared entry register is the unsigned word.
    assert_eq!(
        typed.value_type(value_named(&artifact, "RDI_0")),
        Some(&CValue::Typed(CTypeLike::u64()))
    );
}

#[test]
fn a_copy_converts_nothing() {
    let artifact = artifact(vec![
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: reg(RDI, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let rdi = value_named(&artifact, "RDI_0");
    let rax = value_named(&artifact, "RAX_1");
    let mut plan = Plan::default();
    plan.declared.insert(rdi, CTypeLike::ptr(CTypeLike::u8()));
    plan.declared.insert(rax, CTypeLike::u64());
    let typed = typed_boundaries(&projection, &plan);

    let copy = root_of(&projection, rax);
    let kind = projection.expr(copy).expect("root").kind().clone();
    assert!(matches!(kind, MachineExprKind::Copy { .. }));
    // The copy's rendering is the pointer it reads; the assignment to the
    // integer object is where the conversion is met, from these two types.
    assert_eq!(
        typed.produced(copy),
        Some(&CValue::Typed(CTypeLike::ptr(CTypeLike::u8())))
    );
    assert_eq!(
        typed.required(copy, 0),
        Some(&CTypeLike::ptr(CTypeLike::u8()))
    );
    assert_eq!(
        typed.value_type(rax),
        Some(&CValue::Typed(CTypeLike::u64()))
    );
}

#[test]
fn machine_types_spell_as_their_c_integers() {
    let word = MachineType::Integer {
        width_bits: 64,
        signedness: MachineSignedness::Unsigned,
    };
    assert_eq!(c_type_of(&word), CTypeLike::u64());
    let signed_half = MachineType::Integer {
        width_bits: 16,
        signedness: MachineSignedness::Signed,
    };
    assert_eq!(c_type_of(&signed_half), CTypeLike::i16());
    assert_eq!(promoted(&CTypeLike::u16()), CTypeLike::i32());
    assert_eq!(promoted(&CTypeLike::Bool), CTypeLike::i32());
    assert_eq!(promoted(&CTypeLike::u32()), CTypeLike::u32());
    assert_eq!(promoted(&CTypeLike::i64()), CTypeLike::i64());
    let odd = MachineType::Integer {
        width_bits: 24,
        signedness: MachineSignedness::Unsigned,
    };
    assert_eq!(c_type_of(&odd), CTypeLike::BitVector(24));
}
