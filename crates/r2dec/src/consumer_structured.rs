use crate::ast::CStmt;

pub(crate) struct RoutedBody {
    pub(crate) body_stmt: CStmt,
    pub(crate) use_conservative_locals: bool,
    pub(crate) is_linear_fallback: bool,
}

pub(crate) fn primary_body_for_semantic_route<'a, 'o, F>(
    route: &r2types::DecompileRouteFacts,
    structurer: &mut crate::ControlFlowStructurer<'a, 'o>,
    _linearize: F,
) -> RoutedBody
where
    F: FnMut() -> Vec<CStmt>,
{
    match route.kind {
        r2types::DecompileRouteKind::StructuredWorker => RoutedBody {
            body_stmt: semantic_worker_comment_only_body(
                "structured_worker",
                crate::route_reason(route),
            ),
            use_conservative_locals: true,
            is_linear_fallback: false,
        },
        r2types::DecompileRouteKind::LinearWorker | r2types::DecompileRouteKind::SummaryIslands => {
            RoutedBody {
                body_stmt: semantic_worker_comment_only_body(
                    "summary_route",
                    crate::route_reason(route),
                ),
                use_conservative_locals: true,
                is_linear_fallback: false,
            }
        }
        r2types::DecompileRouteKind::VmSummary
        | r2types::DecompileRouteKind::FallbackComment
        | r2types::DecompileRouteKind::Standard => RoutedBody {
            body_stmt: structurer.structure(),
            use_conservative_locals: false,
            is_linear_fallback: false,
        },
    }
}

pub(crate) fn semantic_worker_comment_only_body(route: &str, reason: &str) -> CStmt {
    CStmt::Block(vec![
        CStmt::comment(format!(
            "r2dec summary: {} for {}",
            route,
            crate::sanitize_comment_text(reason)
        )),
        CStmt::comment(
            "render contract: summary facts only; no executable native C reconstructed".to_string(),
        ),
    ])
}
