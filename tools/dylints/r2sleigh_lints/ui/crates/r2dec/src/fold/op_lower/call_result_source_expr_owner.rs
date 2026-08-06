struct CExpr;

struct Context;

impl Context {
    fn raw_call_exprs_match_for_source_owner_definition(&self, _: &CExpr, _: &CExpr) -> bool {
        true
    }

    fn fallback_owned_call_result_register_name_from_matching_source_call(
        &self,
        source_expr: &CExpr,
        definition_expr: &CExpr,
    ) -> Option<String> {
        if self.raw_call_exprs_match_for_source_owner_definition(source_expr, definition_expr) {
            return Some("x20_1".to_string());
        }
        None
    }

    fn fallback_owned_call_result_register_name_from_matching_definition(
        &self,
        source_expr: &CExpr,
        definition_expr: &CExpr,
    ) -> Option<String> {
        self.fallback_owned_call_result_register_name_from_matching_source_call(
            source_expr,
            definition_expr,
        )
    }

    fn materializable_call_result_expr_for_call_expr(
        &self,
        source_expr: &CExpr,
        definition_expr: &CExpr,
    ) -> bool {
        self.raw_call_exprs_match_for_source_owner_definition(source_expr, definition_expr)
    }
}

fn main() {
    let ctx = Context;
    let source_expr = CExpr;
    let definition_expr = CExpr;
    let _ = ctx.fallback_owned_call_result_register_name_from_matching_definition(
        &source_expr,
        &definition_expr,
    );
}
