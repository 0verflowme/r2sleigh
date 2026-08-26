#[cfg(test)]
use super::*;

#[cfg(test)]
impl<'a> FoldingContext<'a> {
    pub(super) fn source_call_expr_returns_void(
        &self,
        source_call: (u64, usize),
        expr: &CExpr,
    ) -> bool {
        let semantic_expr = expr.unobserved();
        let CExpr::Call { .. } = semantic_expr else {
            return false;
        };
        self.expr_type_hint_for_source_call(source_call, semantic_expr)
            .is_some_and(|ty| matches!(ty, CType::Void))
    }
}
