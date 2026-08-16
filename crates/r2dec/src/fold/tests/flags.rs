use super::*;
use crate::fold::FoldingContext;
use std::collections::BTreeSet;

fn install_call_owner(
    ctx: &mut FoldingContext<'_>,
    source_call: (u64, usize),
    owner_name: &str,
    alias: &str,
) {
    let source_id = analysis::CallSiteId::from(source_call);
    ctx.state.analysis_ctx.ownership.call_ownership.insert(
        source_id,
        analysis::CallOwnershipFact {
            source: source_id,
            owner: Some(analysis::CallOwner {
                visible_name: owner_name.to_string(),
                kind: analysis::CallOwnerKind::StableLocal,
            }),
            aliases: BTreeSet::from([alias.to_string()]),
            direct_aliases: BTreeSet::from([alias.to_string()]),
        },
    );
    ctx.state
        .analysis_ctx
        .ownership
        .alias_sources
        .insert(alias.to_string(), source_id);
    ctx.state
        .analysis_ctx
        .use_info
        .call_result_source_by_alias
        .insert(alias.to_string(), source_call);
}

fn wrap_parens(mut expr: CExpr, count: usize) -> CExpr {
    for _ in 0..count {
        expr = CExpr::Paren(Box::new(expr));
    }
    expr
}

#[test]
fn expr_contains_opaque_temp_uses_visit_over_nested_nodes() {
    let ctx = FoldingContext::new(64);

    let nested = CExpr::binary(
        BinaryOp::And,
        CExpr::Var("zf_1".to_string()),
        CExpr::Paren(Box::new(CExpr::Var("var_12".to_string()))),
    );
    assert!(ctx.expr_contains_opaque_temp(&nested));

    let sleigh_tmp = CExpr::Var("tmp_ldxn_1".to_string());
    assert!(ctx.expr_contains_opaque_temp(&sleigh_tmp));

    let raw_tmp = CExpr::Var("tmp:2a000".to_string());
    assert!(ctx.expr_contains_opaque_temp(&raw_tmp));

    let upper_raw_tmp = CExpr::Var("TMP:2a000".to_string());
    assert!(ctx.expr_contains_opaque_temp(&upper_raw_tmp));

    let clean = CExpr::binary(
        BinaryOp::Eq,
        CExpr::Var("eax_1".to_string()),
        CExpr::IntLit(0),
    );
    assert!(!ctx.expr_contains_opaque_temp(&clean));
}

#[test]
fn call_result_predicate_owner_rewrite_depth_guard_is_inclusive() {
    let mut ctx = FoldingContext::new(64);
    install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");

    let at_max = wrap_parens(
        CExpr::Var("rax_1".to_string()),
        MAX_PREDICATE_OPERAND_DEPTH as usize,
    );
    assert_eq!(
        ctx.rewrite_call_result_predicate_owners(at_max, 0),
        wrap_parens(
            CExpr::Var("loc".to_string()),
            MAX_PREDICATE_OPERAND_DEPTH as usize,
        ),
        "owner aliases at exactly MAX_PREDICATE_OPERAND_DEPTH must still rewrite"
    );

    let beyond_max = wrap_parens(
        CExpr::Var("rax_1".to_string()),
        MAX_PREDICATE_OPERAND_DEPTH as usize + 1,
    );
    assert_eq!(
        ctx.rewrite_call_result_predicate_owners(beyond_max.clone(), 0),
        beyond_max,
        "owner aliases beyond MAX_PREDICATE_OPERAND_DEPTH must be left untouched"
    );
}

#[test]
fn expr_contains_unresolved_memory_uses_visit_over_nested_nodes() {
    let ctx = FoldingContext::new(64);

    let deref_nested = CExpr::binary(
        BinaryOp::Or,
        CExpr::Var("zf_1".to_string()),
        CExpr::Paren(Box::new(CExpr::Deref(Box::new(CExpr::Var(
            "tmp:20_1".to_string(),
        ))))),
    );
    assert!(ctx.expr_contains_unresolved_memory(&deref_nested));

    let no_deref = CExpr::binary(
        BinaryOp::Ne,
        CExpr::Var("x_1".to_string()),
        CExpr::Var("y_1".to_string()),
    );
    assert!(!ctx.expr_contains_unresolved_memory(&no_deref));
}

#[test]
fn tmp_flag_aliases_reconstruct_signed_ge_condition() {
    let mut ctx = FoldingContext::new(64);
    ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
        "tmpng_1".to_string(),
        analysis::FlagCompareProvenance {
            lhs: "argc".to_string(),
            rhs: "2".to_string(),
            kind: analysis::FlagCompareKind::SignedNegative,
        },
    );
    ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
        "tmpov_1".to_string(),
        analysis::FlagCompareProvenance {
            lhs: "argc".to_string(),
            rhs: "2".to_string(),
            kind: analysis::FlagCompareKind::Overflow,
        },
    );

    let expr = CExpr::binary(
        BinaryOp::Eq,
        CExpr::Var("tmpng_1".to_string()),
        CExpr::Var("tmpov_1".to_string()),
    );

    assert_eq!(
        ctx.simplify_condition_expr(expr),
        CExpr::binary(
            BinaryOp::Ge,
            CExpr::Var("argc".to_string()),
            CExpr::IntLit(2),
        )
    );
}
