//! Import and the identity canonicalisation: what a term looks like before any
//! rule exists, and what the accounting fields say about it.

mod fixture;

use fixture::{RAX, RDI, RSI, artifact, konst, projection, reg, tmp, value_named};
use r2il::R2ILOp;
use r2rewrite::{COPY_ELIDE, Multiplicity, TermKind, canonicalize, renders_inline};

fn ret() -> R2ILOp {
    R2ILOp::Return {
        target: konst(0, 8),
    }
}

#[test]
fn and_of_one_value_reads_one_leaf_twice() {
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
        .expect("the and has a term");
    let TermKind::Bitwise { left, right, .. } = roots.arena().term(and.canonical).kind else {
        panic!(
            "expected a bitwise term, got {:?}",
            roots.arena().term(and.canonical)
        );
    };
    assert_eq!(left, right, "one value read twice is one leaf");
    assert!(matches!(roots.arena().term(left).kind, TermKind::Leaf(_)));
    assert!(and.trace.is_empty(), "no rule exists yet");
    assert!(and.discharges.is_empty());
    assert_eq!(
        and.multiplicity,
        Multiplicity::Any,
        "RDI is an entry value nothing redefines"
    );
    assert!(renders_inline(roots.arena(), and.canonical));
}

#[test]
fn copy_is_elided_and_its_single_use_source_expanded() {
    let artifact = artifact(vec![
        R2ILOp::IntAnd {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x100, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let and_value = value_named(&artifact, "tmp:100_1");
    let and = roots.value(and_value).expect("and");
    let rax = roots.value(value_named(&artifact, "RAX_1")).expect("rax");
    assert_eq!(
        rax.canonical, and.canonical,
        "the copy's term is the copied term"
    );
    assert_eq!(rax.trace.len(), 1);
    assert_eq!(rax.trace[0].rule, COPY_ELIDE);
    assert_eq!(rax.trace[0].to, and.canonical);
    let and_producer = projection
        .entity_for_output(and_value)
        .expect("entity")
        .producer();
    assert_eq!(
        rax.discharges.iter().copied().collect::<Vec<_>>(),
        vec![and_producer],
        "rendering the copy's term renders the and"
    );
}

#[test]
fn a_value_read_twice_stays_a_leaf_unless_duplicable() {
    let artifact = artifact(vec![
        R2ILOp::IntAdd {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::IntMult {
            dst: tmp(0x200, 8),
            a: tmp(0x100, 8),
            b: tmp(0x100, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x200, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let sum = roots
        .value(value_named(&artifact, "tmp:100_1"))
        .expect("sum");
    let product = roots
        .value(value_named(&artifact, "tmp:200_1"))
        .expect("product");
    let TermKind::Arithmetic { left, right, .. } = roots.arena().term(product.canonical).kind
    else {
        panic!("expected arithmetic");
    };
    assert_eq!(left, right);
    // RDI + RSI reads only entry values nothing redefines, so the sum is
    // duplicable and both reads of it expand.
    assert_eq!(left, sum.canonical);
    assert_eq!(sum.multiplicity, Multiplicity::Any);
    let sum_producer = projection
        .entity_for_output(value_named(&artifact, "tmp:100_1"))
        .expect("entity")
        .producer();
    assert!(product.discharges.contains(&sum_producer));
}

#[test]
fn a_constant_operand_is_a_literal_and_a_division_is_opaque() {
    let artifact = artifact(vec![
        R2ILOp::IntAdd {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: konst(5, 8),
        },
        R2ILOp::IntDiv {
            dst: tmp(0x200, 8),
            a: tmp(0x100, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x200, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let sum = roots
        .value(value_named(&artifact, "tmp:100_1"))
        .expect("sum");
    let TermKind::Arithmetic { right, .. } = roots.arena().term(sum.canonical).kind else {
        panic!("expected arithmetic");
    };
    let TermKind::Literal(bits) = roots.arena().term(right).kind else {
        panic!("expected a literal");
    };
    assert_eq!(bits.bits(), 5);
    assert_eq!(bits.width_bits(), 64);
    let quotient = roots
        .value(value_named(&artifact, "tmp:200_1"))
        .expect("quotient");
    assert!(matches!(
        roots.arena().term(quotient.canonical).kind,
        TermKind::Opaque(_)
    ));
    assert!(!renders_inline(roots.arena(), quotient.canonical));
    assert_eq!(quotient.multiplicity, Multiplicity::Once);
    // The copy of an opaque value keeps reading it by name.
    let rax = roots.value(value_named(&artifact, "RAX_1")).expect("rax");
    assert!(matches!(
        roots.arena().term(rax.canonical).kind,
        TermKind::Leaf(_)
    ));
    assert!(rax.discharges.is_empty());
}

#[test]
fn canonicalisation_is_deterministic() {
    let artifact = artifact(vec![
        R2ILOp::IntAdd {
            dst: tmp(0x100, 8),
            a: reg(RDI, 8),
            b: konst(5, 8),
        },
        R2ILOp::IntMult {
            dst: tmp(0x200, 8),
            a: tmp(0x100, 8),
            b: reg(RSI, 8),
        },
        R2ILOp::Copy {
            dst: reg(RAX, 8),
            src: tmp(0x200, 8),
        },
        ret(),
    ]);
    let projection = projection(&artifact);
    let first = canonicalize(&artifact, &projection).expect("first");
    let second = canonicalize(&artifact, &projection).expect("second");
    let first_terms: Vec<_> = first.arena().iter().collect();
    let second_terms: Vec<_> = second.arena().iter().collect();
    assert_eq!(first_terms, second_terms);
    let first_values: Vec<_> = first.values().cloned().collect();
    let second_values: Vec<_> = second.values().cloned().collect();
    assert_eq!(first_values, second_values);
}
