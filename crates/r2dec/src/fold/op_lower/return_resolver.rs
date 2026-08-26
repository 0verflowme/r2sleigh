use super::*;

impl<'a> FoldingContext<'a> {
    pub(super) fn expr_is_structured_memory_candidate(expr: &CExpr) -> bool {
        match expr {
            CExpr::Member { .. } | CExpr::PtrMember { .. } | CExpr::Subscript { .. } => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_structured_memory_candidate(inner)
            }
            _ => false,
        }
    }

    pub(super) fn expr_is_scalar_memory_candidate(expr: &CExpr) -> bool {
        match expr {
            CExpr::Deref(_)
            | CExpr::Subscript { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. } => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_is_scalar_memory_candidate(inner)
            }
            _ => false,
        }
    }

    /// Convert an SSA variable to a C variable name.
    pub fn var_name(&self, var: &SSAVar) -> OpLoweringResult<String> {
        match self.get_expr(var)? {
            CExpr::Var(symbol) => Ok(self.spelling(symbol).to_string()),
            _ => Err(OpLoweringRefusal::MissingProgramVariableAuthorization),
        }
    }

    /// Convert a constant variable to a C expression.
    pub(crate) fn const_to_expr(&self, var: &SSAVar) -> OpLoweringResult<CExpr> {
        let val = var
            .constant_bits()
            .ok_or(OpLoweringRefusal::MissingProgramVariableAuthorization)?;
        if val > 0x7fffffff {
            Ok(CExpr::UIntLit(val))
        } else {
            Ok(CExpr::IntLit(val as i64))
        }
    }
}
