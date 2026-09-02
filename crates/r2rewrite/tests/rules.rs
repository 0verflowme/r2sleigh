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
    assert!(rules.contains(&"identity.neg_neg"), "{rules:?}");
    assert_eq!(
        xor.discharges.len(),
        3,
        "the or and both negations render here"
    );
    assert!(roots.budget_failures().is_empty());
}
