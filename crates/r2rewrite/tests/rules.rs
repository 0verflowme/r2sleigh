//! Rules end to end: through import, the driver and the accounting fields.

mod fixture;

use fixture::{RAX, RDI, RSI, artifact, konst, projection, reg, tmp, value_named};
use r2il::R2ILOp;
use r2rewrite::{Multiplicity, TermKind, canonicalize};

fn ret() -> R2ILOp {
    R2ILOp::Return {
        target: konst(0, 8),
    }
}

#[test]
fn and_of_one_value_is_that_value() {
    let artifact = artifact(vec![
        R2ILOp::IntAnd {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: reg(RDI, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x100, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let and = roots
        .value(value_named(&artifact, "tmp:100_1"))
        .expect("and");
    assert!(matches!(
        roots.arena().term(and.canonical).kind,
        TermKind::Leaf(_)
    ));
    assert_eq!(and.trace.len(), 1);
    assert_eq!(and.trace[0].rule, "identity.and_self");
    assert!(roots.budget_failures().is_empty());
    assert_eq!(
        roots.rewrite_counts()["identity.and_self"],
        2,
        "the and, and the copy that absorbed it"
    );
}

#[test]
fn a_constant_chain_across_instructions_is_one_literal() {
    // movz/movk: each step reads the previous one once.
    let artifact = artifact(vec![
        R2ILOp::IntAnd {
            dst: tmp(0x100, 8),
            a: konst(0x2325, 8),
            b: konst(0xffff_ffff_0000_ffff, 8),
        },
        R2ILOp::IntOr {
            dst: tmp(0x200, 8),
            a: tmp(0x100, 8),
            b: konst(0x8422_0000, 8),
        },
        R2ILOp::IntAnd {
            dst: tmp(0x300, 8),
            a: tmp(0x200, 8),
            b: konst(0xffff_0000_ffff_ffff, 8),
        },
        R2ILOp::IntOr {
            dst: tmp(0x400, 8),
            a: tmp(0x300, 8),
            b: konst(0x9ce4_0000_0000, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x400, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let last = roots
        .value(value_named(&artifact, "tmp:400_1"))
        .expect("last");
    let TermKind::Literal(bits) = roots.arena().term(last.canonical).kind else {
        panic!(
            "expected a literal, got {:?}",
            roots.arena().term(last.canonical)
        );
    };
    assert_eq!(bits.bits(), 0x0000_9ce4_8422_2325);
    assert_eq!(last.multiplicity, Multiplicity::Any);
    assert_eq!(
        last.discharges.len(),
        3,
        "the three earlier steps render here"
    );
    let rax = roots.value(value_named(&artifact, "RAX_1")).expect("rax");
    assert_eq!(rax.canonical, last.canonical);
    assert_eq!(rax.discharges.len(), 4);
}

#[test]
fn identities_compose_through_a_single_use_chain() {
    // Shapes the SSA constructor's own combiner leaves alone: it folds `x + 0`
    // and `x * 1` into copies before the arena exists, so those never reach
    // a rule here; `x | x` and `-(-x)` do.
    let artifact = artifact(vec![
        R2ILOp::IntOr {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: reg(RDI, 8),
        },
        R2ILOp::IntNegate {
            dst: tmp(0x200, 8),
            src: tmp(0x100, 8),
        },
        R2ILOp::IntNegate {
            dst: tmp(0x300, 8),
            src: tmp(0x200, 8),
        },
        R2ILOp::IntXor {
            dst: tmp(0x400, 8),
            a: tmp(0x300, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x400, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let xor = roots
        .value(value_named(&artifact, "tmp:400_1"))
        .expect("xor");
    let TermKind::Bitwise { left, right, .. } = roots.arena().term(xor.canonical).kind else {
        panic!("expected xor, got {:?}", roots.arena().term(xor.canonical));
    };
    assert!(matches!(roots.arena().term(left).kind, TermKind::Leaf(_)));
    assert!(matches!(roots.arena().term(right).kind, TermKind::Leaf(_)));
    let rules: Vec<&str> = xor.trace.iter().map(|r| r.rule).collect();
    assert!(rules.contains(&"identity.or_self"), "{rules:?}");
    // The double negation is gone too, taken by the affine normal form
    // before the rule could see it; the rule still proves on its own shape.
    assert_eq!(
        xor.discharges.len(),
        3,
        "the or and both negations render here"
    );
    assert!(roots.budget_failures().is_empty());
}

#[test]
fn a_difference_compared_with_zero_compares_its_operands() {
    // `ZF = (a - b) == 0; if (!ZF)` is the flag shape; the rules take it to
    // `a != b` with the difference discharged.
    let artifact = artifact(vec![
        R2ILOp::IntSub {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::IntEqual {
            dst: tmp(0x200, 1),
            a: tmp(0x100, 8),
            b: konst(0, 8),
        },
        R2ILOp::BoolNot {
            dst: tmp(0x300, 1),
            src: tmp(0x200, 1),
        },
        R2ILOp::IntZExt {
            dst: reg(RAX, 8),
            src: tmp(0x300, 1),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let not = roots
        .value(value_named(&artifact, "tmp:300_1"))
        .expect("the negation");
    let TermKind::Compare {
        op, left, right, ..
    } = roots.arena().term(not.canonical).kind
    else {
        panic!(
            "expected a comparison, got {:?}",
            roots.arena().term(not.canonical)
        );
    };
    assert_eq!(op, r2ssa::MachineComparisonOp::NotEqual);
    assert!(matches!(roots.arena().term(left).kind, TermKind::Leaf(_)));
    assert!(matches!(roots.arena().term(right).kind, TermKind::Leaf(_)));
    let rules: Vec<&str> = not.trace.iter().map(|r| r.rule).collect();
    assert!(rules.contains(&"boolean.sub_eq_zero"), "{rules:?}");
    assert!(rules.contains(&"boolean.not_eq"), "{rules:?}");
    assert_eq!(
        not.discharges.len(),
        2,
        "the subtraction and the equality render here"
    );
    assert!(roots.budget_failures().is_empty());
}

#[test]
fn a_negated_ordering_flips_and_a_zero_extension_of_a_truncation_extracts() {
    let artifact = artifact(vec![
        R2ILOp::IntSLess {
            dst: tmp(0x100, 1),
            a: reg(RDI, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::BoolNot {
            dst: tmp(0x200, 1),
            src: tmp(0x100, 1),
        },
        R2ILOp::Trunc {
            dst: tmp(0x300, 4),
            src: reg(RDI, 8),
        },
        R2ILOp::Trunc {
            dst: tmp(0x400, 2),
            src: tmp(0x300, 4),
        },
        R2ILOp::IntZExt {
            dst: tmp(0x500, 8),
            src: tmp(0x400, 2),
        },
        R2ILOp::IntZExt {
            dst: tmp(0x600, 8),
            src: tmp(0x200, 1),
        },
        R2ILOp::IntAdd {
            dst: reg(RAX, 8),
            a: tmp(0x500, 8),
            b: tmp(0x600, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let flipped = roots
        .value(value_named(&artifact, "tmp:200_1"))
        .expect("negated ordering");
    let TermKind::Compare {
        op, interpretation, ..
    } = roots.arena().term(flipped.canonical).kind
    else {
        panic!(
            "expected a comparison, got {:?}",
            roots.arena().term(flipped.canonical)
        );
    };
    assert_eq!(op, r2ssa::MachineComparisonOp::LessThanOrEqual);
    assert_eq!(interpretation, r2ssa::MachineSignedness::Signed);
    let narrowed = roots
        .value(value_named(&artifact, "tmp:400_1"))
        .expect("double truncation");
    let TermKind::Extract { input, lsb_bits } = roots.arena().term(narrowed.canonical).kind else {
        panic!(
            "expected one extract, got {:?}",
            roots.arena().term(narrowed.canonical)
        );
    };
    assert_eq!(lsb_bits, 0);
    assert!(matches!(roots.arena().term(input).kind, TermKind::Leaf(_)));
    let rules: Vec<&str> = narrowed.trace.iter().map(|r| r.rule).collect();
    assert!(rules.contains(&"cast.extract_extract"), "{rules:?}");
}

#[test]
fn a_signed_branch_on_flags_becomes_a_comparison_through_the_difference_by_name() {
    // `cmp a, b; jl`: the difference feeds both the sign flag and the zero
    // flag, so it is read by name; the rule sees through the name.
    let artifact = artifact(vec![
        R2ILOp::IntSub {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::IntSLess {
            dst: tmp(0x200, 1),
            a: tmp(0x100, 8),
            b: konst(0, 8),
        },
        R2ILOp::IntEqual {
            dst: tmp(0x300, 1),
            a: tmp(0x100, 8),
            b: konst(0, 8),
        },
        R2ILOp::IntSBorrow {
            dst: tmp(0x400, 1),
            a: reg(RDI, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::IntNotEqual {
            dst: tmp(0x500, 1),
            a: tmp(0x200, 1),
            b: tmp(0x400, 1),
        },
        R2ILOp::IntZExt {
            dst: tmp(0x600, 8),
            src: tmp(0x500, 1),
        },
        R2ILOp::IntZExt {
            dst: tmp(0x700, 8),
            src: tmp(0x300, 1),
        },
        R2ILOp::IntAdd {
            dst: reg(RAX, 8),
            a: tmp(0x600, 8),
            b: tmp(0x700, 8),
        },
        // RDI is written later, so the difference over it is not duplicable
        // and its two readers keep reading it by name.
        R2ILOp::Copy {
            dst: reg(RDI, 8),
            src: reg(RAX, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let difference = roots
        .value(value_named(&artifact, "tmp:100_1"))
        .expect("difference");
    assert_eq!(difference.multiplicity, Multiplicity::Once);
    let branch = roots
        .value(value_named(&artifact, "tmp:500_1"))
        .expect("the flag comparison");
    let TermKind::Compare {
        op,
        interpretation,
        left,
        right,
    } = roots.arena().term(branch.canonical).kind
    else {
        panic!(
            "expected a comparison, got {:?}",
            roots.arena().term(branch.canonical)
        );
    };
    assert_eq!(op, r2ssa::MachineComparisonOp::LessThan);
    assert_eq!(interpretation, r2ssa::MachineSignedness::Signed);
    assert!(matches!(roots.arena().term(left).kind, TermKind::Leaf(_)));
    assert!(matches!(roots.arena().term(right).kind, TermKind::Leaf(_)));
    let rules: Vec<&str> = branch.trace.iter().map(|r| r.rule).collect();
    assert!(rules.contains(&"flag.signed_lt_from_borrow"), "{rules:?}");
    // The difference was read by name and is not discharged here; the sign
    // flag and the borrow flag were expanded and are.
    assert_eq!(branch.discharges.len(), 2, "{:?}", branch.discharges);
    let zero_flag = roots
        .value(value_named(&artifact, "tmp:300_1"))
        .expect("zero flag");
    assert!(matches!(
        roots.arena().term(zero_flag.canonical).kind,
        TermKind::Compare {
            op: r2ssa::MachineComparisonOp::Equal,
            ..
        }
    ));
}

#[test]
fn an_address_sum_reaches_its_affine_normal_form() {
    // `(1 + p) + i` then `+ 3`: one sum, terms in id order, literal last.
    let artifact = artifact(vec![
        R2ILOp::IntAdd {
            dst: tmp(0x100, 8),
            a: konst(1, 8),
            b: reg(RDI, 8),
        },
        R2ILOp::IntAdd {
            dst: tmp(0x200, 8),
            a: tmp(0x100, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::IntAdd {
            dst: tmp(0x300, 8),
            a: tmp(0x200, 8),
            b: konst(3, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x300, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let sum = roots
        .value(value_named(&artifact, "tmp:300_1"))
        .expect("sum");
    let TermKind::Arithmetic {
        op: r2ssa::MachineArithmeticOp::Add,
        left,
        right,
    } = roots.arena().term(sum.canonical).kind
    else {
        panic!(
            "expected a sum, got {:?}",
            roots.arena().term(sum.canonical)
        );
    };
    let TermKind::Literal(bits) = roots.arena().term(right).kind else {
        panic!(
            "expected the literal last, got {:?}",
            roots.arena().term(right)
        );
    };
    assert_eq!(bits.bits(), 4);
    let TermKind::Arithmetic {
        op: r2ssa::MachineArithmeticOp::Add,
        left: p,
        right: i,
    } = roots.arena().term(left).kind
    else {
        panic!("expected p + i, got {:?}", roots.arena().term(left));
    };
    assert!(matches!(roots.arena().term(p).kind, TermKind::Leaf(_)));
    assert!(matches!(roots.arena().term(i).kind, TermKind::Leaf(_)));
    assert!(roots.budget_failures().is_empty());
}

/// `(uint64_t)(uint32_t)(uint64_t)(uint32_t)x` in the C is, in the arena,
/// `zext(trunc(zext(trunc(x))))`, and no rule is needed for the sandwich as
/// such: the driver canonicalises children first, `cast.extract_of_extend_whole`
/// removes the inner truncation of an extension of the same width, and what
/// remains is the one extension of the one truncation.
#[test]
fn an_extension_sandwiched_in_its_own_truncation_is_one_extension() {
    let artifact = artifact(vec![
        R2ILOp::Trunc {
            dst: tmp(0x100, 4),
            src: reg(RDI, 8),
        },
        R2ILOp::IntZExt {
            dst: tmp(0x200, 8),
            src: tmp(0x100, 4),
        },
        R2ILOp::Trunc {
            dst: tmp(0x300, 4),
            src: tmp(0x200, 8),
        },
        R2ILOp::IntZExt {
            dst: tmp(0x400, 8),
            src: tmp(0x300, 4),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x400, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let once = roots
        .value(value_named(&artifact, "tmp:200_1"))
        .expect("the first extension");
    let twice = roots
        .value(value_named(&artifact, "tmp:400_1"))
        .expect("the second extension");
    assert_eq!(
        twice.canonical, once.canonical,
        "the sandwich must canonicalise to the first extension"
    );
    let arena = roots.arena();
    let TermKind::Cast {
        kind: r2ssa::MachineCastKind::ZeroExtend,
        input,
    } = arena.term(twice.canonical).kind
    else {
        panic!(
            "expected one zero extension, got {:?}",
            arena.term(twice.canonical)
        );
    };
    assert!(
        matches!(
            arena.term(input).kind,
            TermKind::Extract { lsb_bits: 0, .. }
        ),
        "expected the extension of one truncation, got {:?}",
        arena.term(input)
    );
    assert!(
        twice
            .trace
            .iter()
            .any(|rewrite| rewrite.rule == "cast.extract_of_extend_whole"),
        "the inner truncation of the extension is what the existing rule removes: {:?}",
        twice.trace
    );
    assert!(roots.budget_failures().is_empty());
}
