use crate::ast::CStmt;

pub(crate) struct RoutedBody {
    pub(crate) body_stmt: CStmt,
    pub(crate) use_conservative_locals: bool,
    pub(crate) is_linear_fallback: bool,
}

pub(crate) fn primary_body_for_semantic_route<'a, 'o, F>(
    route: &crate::SemanticRoutePlan,
    structurer: &mut crate::ControlFlowStructurer<'a, 'o>,
    mut linearize: F,
) -> RoutedBody
where
    F: FnMut() -> Vec<CStmt>,
{
    match route {
        crate::SemanticRoutePlan::StructuredWorker { reason } => {
            match structurer.structure_semantic_worker_islands(6) {
                Some(structured) => RoutedBody {
                    body_stmt: semantic_worker_structured_body(reason, structured),
                    use_conservative_locals: true,
                    is_linear_fallback: false,
                },
                None => RoutedBody {
                    body_stmt: semantic_worker_linear_body(reason, linearize()),
                    use_conservative_locals: true,
                    is_linear_fallback: true,
                },
            }
        }
        crate::SemanticRoutePlan::LinearWorker { reason }
        | crate::SemanticRoutePlan::SummaryIslands { reason } => RoutedBody {
            body_stmt: semantic_worker_linear_body(reason, linearize()),
            use_conservative_locals: true,
            is_linear_fallback: true,
        },
        crate::SemanticRoutePlan::VmSummary { .. }
        | crate::SemanticRoutePlan::FallbackComment { .. }
        | crate::SemanticRoutePlan::Standard => RoutedBody {
            body_stmt: structurer.structure(),
            use_conservative_locals: false,
            is_linear_fallback: false,
        },
    }
}

pub(crate) fn semantic_worker_structured_body(reason: &str, structured: CStmt) -> CStmt {
    CStmt::Block(vec![
        CStmt::comment(format!("r2dec semantic worker structuring for {}", reason)),
        structured,
    ])
}

pub(crate) fn semantic_worker_linear_body(reason: &str, mut linear_stmts: Vec<CStmt>) -> CStmt {
    if linear_stmts.is_empty() {
        return CStmt::Block(vec![CStmt::comment(format!(
            "r2dec fallback: semantic worker linearization for {} -> no statements recovered",
            reason
        ))]);
    }
    linear_stmts.insert(
        0,
        CStmt::comment(format!(
            "r2dec residual: semantic worker linearization for {}",
            reason
        )),
    );
    CStmt::Block(linear_stmts)
}
