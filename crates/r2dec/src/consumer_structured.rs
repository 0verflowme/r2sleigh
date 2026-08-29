use crate::ast::CStmt;
use crate::structure::{ControlFlowStructureError, ControlFlowStructureResult};
use crate::structured_region::SealedStructuredBody;

pub(crate) struct RoutedBody {
    body_stmt: Option<CStmt>,
    structured_body: Option<SealedStructuredBody>,
}

impl RoutedBody {
    pub(crate) fn structured_body(&self) -> Option<&SealedStructuredBody> {
        self.structured_body.as_ref()
    }

    /// Transfer the final statement and its exact lexical authority together.
    /// Unstructured routes have no region proof and therefore cannot silently
    /// participate in declaration placement.
    pub(crate) fn into_marked_body(
        self,
    ) -> (
        CStmt,
        Option<crate::structured_region::SealedStructuredRegionArtifact>,
    ) {
        match (self.structured_body, self.body_stmt) {
            (Some(body), None) => {
                let (stmt, regions) = body.into_marked_parts();
                (stmt, Some(regions))
            }
            (None, Some(stmt)) => (stmt, None),
            _ => unreachable!("a routed body has exactly one statement owner"),
        }
    }
}

pub(crate) fn primary_body_for_semantic_route<'a, 'o, F, R>(
    route: &r2types::DecompileRouteFacts,
    structurer: &mut crate::ControlFlowStructurer<'a, 'o>,
    mut linearize: F,
    mut rollback_tentative_structure: R,
) -> ControlFlowStructureResult<RoutedBody>
where
    F: FnMut() -> ControlFlowStructureResult<Vec<CStmt>>,
    R: FnMut(),
{
    match route.kind {
        r2types::DecompileRouteKind::StructuredWorker => Ok(RoutedBody {
            body_stmt: Some(semantic_worker_comment_only_body(
                "structured_worker",
                crate::route_reason(route),
            )),
            structured_body: None,
        }),
        r2types::DecompileRouteKind::LinearWorker | r2types::DecompileRouteKind::SummaryIslands => {
            Ok(RoutedBody {
                body_stmt: Some(semantic_worker_comment_only_body(
                    "summary_route",
                    crate::route_reason(route),
                )),
                structured_body: None,
            })
        }
        r2types::DecompileRouteKind::VmSummary
        | r2types::DecompileRouteKind::FallbackComment
        | r2types::DecompileRouteKind::Standard => {
            let structured = structurer.structure_with_regions();
            if let Err(ControlFlowStructureError::Lowering(error)) = &structured {
                return Err(ControlFlowStructureError::Lowering(*error));
            }
            // Structuring refuses as a whole when one edge will not lower, so a
            // function whose loop exits reach blocks the region never covered
            // rendered nothing at all: no statements, and none of its
            // obligations owned, while the rest of the body was understood.
            // Say what could not be structured and render the body without
            // structure, rather than withhold all of it.
            match structurer.safety_reason() {
                Some(reason) => {
                    let reason = reason.to_string();
                    rollback_tentative_structure();
                    let mut stmts = vec![CStmt::comment(format!(
                        "r2dec residual: {}; body rendered without structure",
                        crate::sanitize_comment_text(&reason)
                    ))];
                    stmts.extend(linearize()?);
                    let structured_body = structurer.seal_linearized_body(CStmt::Block(stmts))?;
                    Ok(RoutedBody {
                        body_stmt: None,
                        structured_body: Some(structured_body),
                    })
                }
                None => match structured {
                    Ok(structured_body) => Ok(RoutedBody {
                        body_stmt: None,
                        structured_body: Some(structured_body),
                    }),
                    Err(ControlFlowStructureError::StructuredRegion(error)) => {
                        Err(ControlFlowStructureError::StructuredRegion(error))
                    }
                    Err(ControlFlowStructureError::Lowering(_)) => {
                        unreachable!("lowering refusal returned before route fallback")
                    }
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
