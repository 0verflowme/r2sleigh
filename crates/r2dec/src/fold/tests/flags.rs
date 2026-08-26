use super::*;
use crate::fold::FoldingContext;

#[test]
fn expr_contains_opaque_temp_uses_visit_over_nested_nodes() {
    let ctx = FoldingContext::new(64);

    let nested = CExpr::binary(
        BinaryOp::And,
        ctx.name_ref("zf_1"),
        CExpr::Paren(Box::new(ctx.name_ref("var_12"))),
    );
    assert!(ctx.expr_contains_opaque_temp(&nested));

    let sleigh_tmp = ctx.name_ref("tmp_ldxn_1");
    assert!(ctx.expr_contains_opaque_temp(&sleigh_tmp));

    let raw_tmp = ctx.name_ref("tmp:2a000");
    assert!(ctx.expr_contains_opaque_temp(&raw_tmp));

    let upper_raw_tmp = ctx.name_ref("TMP:2a000");
    assert!(ctx.expr_contains_opaque_temp(&upper_raw_tmp));

    let clean = CExpr::binary(
        BinaryOp::Eq,
        ctx.name_ref("eax_1"),
        CExpr::IntLit(0),
    );
    assert!(!ctx.expr_contains_opaque_temp(&clean));
}

#[test]
fn expr_contains_unresolved_memory_uses_visit_over_nested_nodes() {
    let ctx = FoldingContext::new(64);

    let deref_nested = CExpr::binary(
        BinaryOp::Or,
        ctx.name_ref("zf_1"),
        CExpr::Paren(Box::new(CExpr::Deref(Box::new(CExpr::Var(
            { let CExpr::Var(id) = ctx.name_ref("tmp:20_1") else { unreachable!() }; id },
        ))))),
    );
    assert!(ctx.expr_contains_unresolved_memory(&deref_nested));

    let no_deref = CExpr::binary(
        BinaryOp::Ne,
        ctx.name_ref("x_1"),
        ctx.name_ref("y_1"),
    );
    assert!(!ctx.expr_contains_unresolved_memory(&no_deref));
}
