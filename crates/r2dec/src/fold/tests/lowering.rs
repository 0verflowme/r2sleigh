use super::*;
use std::collections::HashSet;

#[test]
fn collect_expr_reads_visits_nested_children() {
    let ctx = FoldingContext::new(64);
    let CExpr::Var(a) = ctx.name_ref("a_1") else {
        unreachable!("fixture name reference")
    };
    let CExpr::Var(callee) = ctx.name_ref("callee_0") else {
        unreachable!("fixture name reference")
    };
    let CExpr::Var(b) = ctx.name_ref("b_2") else {
        unreachable!("fixture name reference")
    };
    let CExpr::Var(c) = ctx.name_ref("c_3") else {
        unreachable!("fixture name reference")
    };
    let expr = CExpr::binary(
        BinaryOp::Add,
        CExpr::Var(a),
        CExpr::call(
            CExpr::Var(callee),
            vec![
                CExpr::Deref(Box::new(CExpr::Var(b))),
                CExpr::Paren(Box::new(CExpr::cast(
                    CType::Int(32),
                    CExpr::Var(c),
                ))),
            ],
        ),
    );

    let mut reads = HashSet::new();
    ctx.collect_expr_reads(&expr, &mut reads);

    assert!(reads.contains(&a));
    assert!(reads.contains(&callee));
    assert!(reads.contains(&b));
    assert!(reads.contains(&c));
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
