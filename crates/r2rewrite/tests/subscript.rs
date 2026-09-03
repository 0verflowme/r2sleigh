//! The subscript rules end to end: a load and a store through a parameter
//! plus a scaled index import as cells, canonicalise to elements, and account
//! for the address arithmetic they absorbed; and a load never moves into its
//! reader.

mod fixture;

use fixture::{RAX, RDI, RSI, artifact_with_parameters, konst, projection, reg, tmp, value_named};
use r2il::{R2ILOp, SpaceId};
use r2rewrite::{TermKind, canonicalize};
use r2ssa::StructuredAccessId;

fn ret() -> R2ILOp {
    R2ILOp::Return {
        target: konst(0, 8),
    }
}

/// `rdi + rsi * 4` as a unique, with `rdi` the first parameter.
fn scaled_address() -> Vec<R2ILOp> {
    vec![
        R2ILOp::IntMult {
            dst: tmp(0x100, 8),
            a: reg(RSI, 8),
            b: konst(4, 8),
        },
        R2ILOp::IntAdd {
            dst: tmp(0x200, 8),
            a: reg(RDI, 8),
            b: tmp(0x100, 8),
        },
    ]
}

#[test]
fn a_load_through_a_parameter_plus_a_scaled_index_is_an_element() {
    let mut ops = scaled_address();
    ops.push(R2ILOp::Load {
        dst: tmp(0x300, 4),
        space: SpaceId::Ram,
        addr: tmp(0x200, 8),
    });
    ops.push(R2ILOp::IntZExt {
        dst: reg(RAX, 8),
        src: tmp(0x300, 4),
    });
    ops.push(ret());
    let artifact = artifact_with_parameters(ops, &[RDI, RSI]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let loaded = value_named(&artifact, "tmp:300_1");
    let load = roots.value(loaded).expect("the load has a term");
    let arena = roots.arena();
    let TermKind::Subscript { base, index } = arena.term(load.canonical).kind else {
        panic!("expected a subscript, got {:?}", arena.term(load.canonical));
    };
    assert!(
        arena.is_pointer(base),
        "the base is the leaf the parameter provenance typed as a pointer"
    );
    assert!(
        matches!(arena.term(index).kind, TermKind::Leaf(_)),
        "the index is the unscaled counter, {:?}",
        arena.term(index)
    );
    assert_eq!(
        load.trace
            .iter()
            .map(|rewrite| rewrite.rule)
            .collect::<Vec<_>>(),
        vec!["subscript.constant_stride"]
    );
    // The multiply and the add were absorbed into the load's term, so
    // rendering the subscript renders them: both are discharged.
    assert_eq!(load.discharges.len(), 2, "{:?}", load.discharges);
    let inst = artifact.graph().def_inst(loaded).expect("load instruction");
    let access = roots
        .access(StructuredAccessId { inst, ordinal: 0 })
        .expect("the load's access has a term");
    assert_eq!(access.canonical, load.canonical);
    assert!(roots.budget_failures().is_empty());
}

#[test]
fn a_store_through_the_same_address_writes_the_same_element() {
    let mut ops = scaled_address();
    ops.push(R2ILOp::Store {
        space: SpaceId::Ram,
        addr: tmp(0x200, 8),
        val: reg(RAX, 4),
    });
    ops.push(ret());
    let artifact = artifact_with_parameters(ops, &[RDI, RSI]);
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let store = artifact
        .structured()
        .memory_accesses
        .values()
        .find(|fact| fact.is_write)
        .expect("the store is a structured access");
    assert!(
        projection.store_address(store.id).is_some(),
        "the projection interns the store's address"
    );
    let cell = roots.access(store.id).expect("the store's cell has a term");
    let arena = roots.arena();
    assert!(
        matches!(arena.term(cell.canonical).kind, TermKind::Subscript { .. }),
        "{:?}",
        arena.term(cell.canonical)
    );
    assert_eq!(
        cell.trace
            .iter()
            .map(|rewrite| rewrite.rule)
            .collect::<Vec<_>>(),
        vec!["subscript.constant_stride"]
    );
    assert_eq!(cell.discharges.len(), 2, "{:?}", cell.discharges);
}

#[test]
fn a_dereference_stays_a_load_and_a_load_stays_out_of_its_reader() {
    let artifact = artifact_with_parameters(
        vec![
            R2ILOp::Load {
                dst: tmp(0x300, 8),
                space: SpaceId::Ram,
                addr: reg(RDI, 8),
            },
            R2ILOp::IntAdd {
                dst: reg(RAX, 8),
                a: tmp(0x300, 8),
                b: konst(1, 8),
            },
            ret(),
        ],
        &[RDI],
    );
    let projection = projection(&artifact);
    let roots = canonicalize(&artifact, &projection).expect("canonical roots");
    let arena = roots.arena();
    let load = roots
        .value(value_named(&artifact, "tmp:300_1"))
        .expect("load");
    assert!(
        matches!(arena.term(load.canonical).kind, TermKind::Load { .. }),
        "a plain dereference is not an element: {:?}",
        arena.term(load.canonical)
    );
    let sum = roots.value(value_named(&artifact, "RAX_1")).expect("sum");
    let TermKind::Arithmetic { left, .. } = arena.term(sum.canonical).kind else {
        panic!("expected the add, got {:?}", arena.term(sum.canonical));
    };
    assert!(
        matches!(arena.term(left).kind, TermKind::Leaf(_)),
        "the reader names the loaded value rather than absorbing the read: {:?}",
        arena.term(left)
    );
    assert!(sum.discharges.is_empty());
}
