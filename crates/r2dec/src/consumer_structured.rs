use crate::ast::CStmt;

pub(crate) struct RoutedBody {
    pub(crate) body_stmt: CStmt,
    pub(crate) use_conservative_locals: bool,
    pub(crate) is_linear_fallback: bool,
}

pub(crate) fn primary_body_for_semantic_route<'a, 'o, F>(
    route: &r2types::DecompileRouteFacts,
    structurer: &mut crate::ControlFlowStructurer<'a, 'o>,
    mut linearize: F,
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
        | r2types::DecompileRouteKind::Standard => {
            let structured = structurer.structure();
            // Structuring refuses as a whole when one edge will not lower, so a
            // function whose loop exits reach blocks the region never covered
            // rendered nothing at all: no statements, and none of its
            // obligations owned, while the rest of the body was understood.
            // Say what could not be structured and render the body without
            // structure, rather than withhold all of it.
            match structurer.safety_reason() {
                Some(reason) => {
                    let mut stmts = vec![CStmt::comment(format!(
                        "r2dec residual: {}; body rendered without structure",
                        crate::sanitize_comment_text(reason)
                    ))];
                    stmts.extend(linearize());
                    RoutedBody {
                        body_stmt: CStmt::Block(stmts),
                        use_conservative_locals: true,
                        is_linear_fallback: true,
                    }
                }
                None => RoutedBody {
                    body_stmt: structured,
                    use_conservative_locals: false,
                    is_linear_fallback: false,
                },
            }
        }
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
