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
        // What the callee is recorded to return, from the site's identity.
        // The rendered callee's name is not evidence about the signature:
        // a poisoned name resolved to a different function's prototype.
        self.known_signature_for_site(source_call.0, source_call.1)
            .is_some_and(|signature| matches!(signature.return_type, CType::Void))
    }
}
