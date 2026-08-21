use std::collections::HashSet;

use crate::ast::CExpr;
use crate::normalize::{NormalizeMode, normalize_expr};

pub(crate) trait PredicateAnalysisView {
    fn expand_predicate_vars(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr;

    fn try_reconstruct_condition(&self, expr: &CExpr) -> Option<CExpr>;

    fn simplify_predicate_expr(&self, expr: CExpr) -> CExpr;
}

pub(crate) struct PredicateSimplifier<'a, V: ?Sized> {
    view: &'a V,
}

impl<'a, V: PredicateAnalysisView + ?Sized> PredicateSimplifier<'a, V> {
    pub(crate) fn new(view: &'a V) -> Self {
        Self { view }
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
        let expanded = self.view.expand_predicate_vars(&expr, 0, &mut visited);
        let reconstructed = self.reconstruct_condition_tree(expanded);
        normalize_expr(self.view, reconstructed, NormalizeMode::Predicate)
    }

    fn reconstruct_condition_tree(&self, expr: CExpr) -> CExpr {
        let mut recurse = |child: CExpr| self.reconstruct_condition_tree(child);
        let rewritten = expr.map_children(&mut recurse);

        self.view
            .try_reconstruct_condition(&rewritten)
            .unwrap_or(rewritten)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};
    use crate::fold::FoldingContext;
    use std::collections::HashSet;

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    struct ChainedPredicateView;

    impl PredicateAnalysisView for ChainedPredicateView {
        fn expand_predicate_vars(
            &self,
            expr: &CExpr,
            _depth: u32,
            _visited: &mut HashSet<String>,
        ) -> CExpr {
            let symbols = test_table();
            match expr {
                CExpr::Var(name) if &*crate::symbol::spelling(&symbols, *name) == "stage0" => crate::symbol::var_ref(&&self.symbols, "stage1"),
                CExpr::Var(name) if &*crate::symbol::spelling(&symbols, *name) == "stage1" => crate::symbol::var_ref(&&self.symbols, "done"),
                other => other.clone(),
            }
        }

        fn try_reconstruct_condition(&self, _expr: &CExpr) -> Option<CExpr> {
            None
        }

        fn simplify_predicate_expr(&self, expr: CExpr) -> CExpr {
            expr
        }
    }

    #[test]
    fn simplify_condition_expr_reaches_stable_fixed_point() {
        let symbols = test_table();
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(BinaryOp::Eq, crate::symbol::var_ref(&symbols, "x"), CExpr::IntLit(0)),
        );

        let once = simplifier.simplify_condition_expr(expr);
        let twice = simplifier.simplify_condition_expr(once.clone());
        assert_eq!(
            once,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "x"), CExpr::IntLit(0))
        );
        assert_eq!(once, twice);
    }

    #[test]
    fn simplify_condition_expr_requires_multiple_passes_to_fixed_point() {
        let symbols = test_table();
        let view = ChainedPredicateView;
        let simplifier = PredicateSimplifier::new(&view);

        let simplified = simplifier.simplify_condition_expr(crate::symbol::var_ref(&symbols, "stage0"));
        assert_eq!(simplified, crate::symbol::var_ref(&symbols, "done"));
    }

    #[test]
    fn simplify_condition_expr_reconstructs_nested_signed_predicate_scaffold() {
        let symbols = test_table();
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "x"), CExpr::IntLit(0)),
            CExpr::binary(
                BinaryOp::And,
                CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "a"), CExpr::IntLit(0)),
                CExpr::binary(
                    BinaryOp::Eq,
                    crate::symbol::var_ref(&symbols, "of_1"),
                    CExpr::binary(BinaryOp::Lt, crate::symbol::var_ref(&symbols, "a"), CExpr::IntLit(0)),
                ),
            ),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        let expected = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "x"), CExpr::IntLit(0)),
            CExpr::binary(BinaryOp::Gt, crate::symbol::var_ref(&symbols, "a"), CExpr::IntLit(0)),
        );
        assert_eq!(simplified, expected);
    }

    #[test]
    fn simplify_condition_expr_reconstructs_nested_cast_paren_signed_predicate_scaffold() {
        let symbols = test_table();
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "x"), CExpr::IntLit(0)),
            CExpr::Paren(Box::new(CExpr::binary(
                BinaryOp::And,
                CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "a"), CExpr::IntLit(0)),
                CExpr::binary(
                    BinaryOp::Eq,
                    crate::symbol::var_ref(&symbols, "of_1"),
                    CExpr::Paren(Box::new(CExpr::binary(
                        BinaryOp::Lt,
                        CExpr::cast(CType::Int(32), crate::symbol::var_ref(&symbols, "a")),
                        CExpr::cast(CType::Int(32), CExpr::IntLit(0)),
                    ))),
                ),
            ))),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        let expected = CExpr::binary(
            BinaryOp::BitXor,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "x"), CExpr::IntLit(0)),
            CExpr::Paren(Box::new(CExpr::binary(
                BinaryOp::Gt,
                crate::symbol::var_ref(&symbols, "a"),
                CExpr::IntLit(0),
            ))),
        );
        assert_eq!(simplified, expected);
    }

    #[test]
    fn simplify_condition_expr_collapses_nested_unsigned_truthy_scaffold() {
        let symbols = test_table();
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
                            CExpr::cast(CType::u64(), crate::symbol::var_ref(&symbols, "t1")),
                        ),
                    ),
                ),
            ),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "t1"), CExpr::IntLit(0))
        );
    }

    #[test]
    fn simplify_condition_expr_collapses_boolean_zero_comparison() {
        let symbols = test_table();
        let ctx = FoldingContext::new(64);
        let simplifier = PredicateSimplifier::new(&ctx);

        let expr = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(BinaryOp::Ne, crate::symbol::var_ref(&symbols, "t1"), CExpr::IntLit(0)),
            CExpr::IntLit(0),
        );

        let simplified = simplifier.simplify_condition_expr(expr);
        assert_eq!(
            simplified,
            CExpr::binary(BinaryOp::Eq, crate::symbol::var_ref(&symbols, "t1"), CExpr::IntLit(0))
        );
    }

    #[test]
    fn simplify_condition_expr_collapses_boolean_one_comparison_and_shift_zero() {
        let symbols = test_table();
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
                        crate::symbol::var_ref(&symbols, "x0_3"),
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
                    crate::symbol::var_ref(&symbols, "x0_3"),
                    CExpr::IntLit(1),
                ),
                CExpr::IntLit(0),
            )
        );
    }
}
