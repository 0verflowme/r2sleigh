use super::*;
use std::collections::HashSet;

#[test]
fn collect_expr_reads_visits_nested_children() {
    let ctx = FoldingContext::new(64);
    let expr = CExpr::binary(
        BinaryOp::Add,
        ctx.name_ref("a_1"),
        CExpr::call(
            ctx.name_ref("callee_0"),
            vec![
                CExpr::Deref(Box::new(ctx.name_ref("b_2"))),
                CExpr::Paren(Box::new(CExpr::cast(
                    CType::Int(32),
                    ctx.name_ref("c_3"),
                ))),
            ],
        ),
    );

    let mut reads = HashSet::new();
    ctx.collect_expr_reads(&expr, &mut reads);

    assert!(reads.contains("a_1"));
    assert!(reads.contains("callee_0"));
    assert!(reads.contains("b_2"));
    assert!(reads.contains("c_3"));
}

#[test]
fn expr_is_pure_detects_side_effect_nodes() {
    let ctx = FoldingContext::new(64);
    let pure_expr = CExpr::binary(
        BinaryOp::Mul,
        ctx.name_ref("x_1"),
        CExpr::IntLit(4),
    );
    assert!(ctx.expr_is_pure(&pure_expr));

    let call_expr = CExpr::call(
        ctx.name_ref("foo"),
        vec![ctx.name_ref("x_1")],
    );
    assert!(!ctx.expr_is_pure(&call_expr));

    let assign_expr = CExpr::assign(ctx.name_ref("x_1"), CExpr::IntLit(7));
    assert!(!ctx.expr_is_pure(&assign_expr));
}
