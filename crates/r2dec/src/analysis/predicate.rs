use std::collections::HashSet;

use crate::ast::CExpr;
use crate::fold::FoldingContext;
use crate::normalize::{NormalizeMode, normalize_expr};

pub(crate) struct PredicateSimplifier<'a, 'o> {
    ctx: &'a FoldingContext<'o>,
}

impl<'a, 'o> PredicateSimplifier<'a, 'o> {
    pub(crate) fn new(ctx: &'a FoldingContext<'o>) -> Self {
        Self { ctx }
    }

    pub(crate) fn simplify_condition_expr(&self, expr: CExpr) -> CExpr {
        const MAX_SIMPLIFY_PASSES: usize = 4;

        let mut current = expr;
        for _ in 0..MAX_SIMPLIFY_PASSES {
            let next = self.simplify_condition_pass(current.clone());
            if next == current {
                return next;
            }
            current = next;
        }

        current
    }

    fn simplify_condition_pass(&self, expr: CExpr) -> CExpr {
        let mut visited = HashSet::new();
        let expanded = self.ctx.expand_predicate_vars(&expr, 0, &mut visited);
        let reconstructed = self.reconstruct_condition_tree(expanded);
        normalize_expr(self.ctx, reconstructed, NormalizeMode::Predicate)
    }

    fn reconstruct_condition_tree(&self, expr: CExpr) -> CExpr {
        let mut recurse = |child: CExpr| self.reconstruct_condition_tree(child);
        let rewritten = expr.map_children(&mut recurse);

        self.ctx
            .try_reconstruct_condition(&rewritten)
            .unwrap_or(rewritten)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};

    #[test]
    fn simplify_condition_expr_reaches_stable_fixed_point() {
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(BinaryOp::Eq, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
        );

        let once = simplifier.simplify_condition_expr(expr);
        let twice = simplifier.simplify_condition_expr(once.clone());
        assert_eq!(
            once,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0))
        );
        assert_eq!(once, twice);
    }

    #[test]
    fn simplify_condition_expr_reconstructs_nested_signed_predicate_scaffold() {
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::And,
                CExpr::binary(BinaryOp::Ne, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
                CExpr::binary(
                    BinaryOp::Eq,
                    CExpr::Var("of_1".to_string()),
                    CExpr::binary(BinaryOp::Lt, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
                ),
            ),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        let expected = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
            CExpr::binary(BinaryOp::Gt, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
        );
        assert_eq!(simplified, expected);
    }

    #[test]
    fn simplify_condition_expr_reconstructs_nested_cast_paren_signed_predicate_scaffold() {
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
            CExpr::Paren(Box::new(CExpr::binary(
                BinaryOp::And,
                CExpr::binary(BinaryOp::Ne, CExpr::Var("a".to_string()), CExpr::IntLit(0)),
                CExpr::binary(
                    BinaryOp::Eq,
                    CExpr::Var("of_1".to_string()),
                    CExpr::Paren(Box::new(CExpr::binary(
                        BinaryOp::Lt,
                        CExpr::cast(CType::Int(32), CExpr::Var("a".to_string())),
                        CExpr::cast(CType::Int(32), CExpr::IntLit(0)),
                    ))),
                ),
            ))),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        let expected = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
            CExpr::Paren(Box::new(CExpr::binary(
                BinaryOp::Gt,
                CExpr::Var("a".to_string()),
                CExpr::IntLit(0),
            ))),
        );
        assert_eq!(simplified, expected);
    }

    #[test]
    fn simplify_condition_expr_collapses_nested_unsigned_truthy_scaffold() {
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Le,
                CExpr::cast(CType::u64(), CExpr::IntLit(1)),
                CExpr::cast(
                    CType::u64(),
                    CExpr::unary(
                        UnaryOp::Not,
                        CExpr::binary(
                            BinaryOp::Le,
                            CExpr::cast(CType::u64(), CExpr::IntLit(1)),
                            CExpr::cast(CType::u64(), CExpr::Var("t1".to_string())),
                        ),
                    ),
                ),
            ),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("t1".to_string()), CExpr::IntLit(0))
        );
    }

    #[test]
    fn simplify_condition_expr_collapses_boolean_zero_comparison() {
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(BinaryOp::Ne, CExpr::Var("t1".to_string()), CExpr::IntLit(0)),
            CExpr::IntLit(0),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Eq, CExpr::Var("t1".to_string()), CExpr::IntLit(0))
        );
    }

    #[test]
    fn simplify_condition_expr_collapses_boolean_one_comparison_and_shift_zero() {
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::binary(
                    BinaryOp::BitAnd,
                    CExpr::binary(
                        BinaryOp::Shr,
                        CExpr::Var("x0_3".to_string()),
                        CExpr::IntLit(0),
                    ),
                    CExpr::IntLit(1),
                ),
                CExpr::IntLit(0),
            ),
            CExpr::IntLit(1),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::binary(
                    BinaryOp::BitAnd,
                    CExpr::Var("x0_3".to_string()),
                    CExpr::IntLit(1),
                ),
                CExpr::IntLit(0),
            )
        );
    }
}
