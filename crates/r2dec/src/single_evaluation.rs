//! One call site, one evaluation.
//!
//! A call is an event the program performs, not a value that can be recomputed
//! on demand. Folding reaches a call site through every value that carries its
//! result, so the same site can be reconstructed at each of those values and
//! printed several times over. That is not a cosmetic repetition: three
//! renderings of `malloc(n)` say the program allocates three times when it
//! allocates once, and a reader who counts allocations against frees is then
//! reading a program that does not exist.
//!
//! This pass is deliberately a verifier, not a repair pass. A repeated call
//! site needs an upstream certificate proving that no execution can reach two
//! occurrences. Structured rendering carries exactly that certificate in its
//! sealed lexical-region artifact; repeated occurrences are admitted only when
//! every pair lies in mutually exclusive selection arms. Moving the first
//! textual occurrence, adopting a nearby assignment, or retargeting later
//! occurrences would reconstruct execution and dominance facts in the
//! renderer.

use std::collections::BTreeMap;

use crate::ast::{CExpr, CFunction, CStmt};
use crate::binding_plan::BindingNameResolution;
use crate::structured_region::{RegionId, SealedStructuredRegionArtifact};

/// A call site, identified by the address of the call and its index there.
pub(crate) type CallSite = (u64, usize);

/// A repeated call site lacks an upstream one-evaluation certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SingleEvaluationError {
    RepeatedCallRequiresCertifiedBinding { site: CallSite, occurrences: usize },
}

fn source_of(expr: &CExpr) -> Option<CallSite> {
    match expr.unobserved() {
        CExpr::Call {
            site: Some(site), ..
        } => Some(*site),
        _ => None,
    }
}

/// Give every call site in `func` exactly one evaluation.
pub(crate) fn bind_each_call_site_once(
    func: &mut CFunction,
    _names: &BindingNameResolution,
    regions: Option<&SealedStructuredRegionArtifact>,
) -> Result<(), SingleEvaluationError> {
    verify_call_sites_are_single_per_execution(func, regions)
}

fn verify_call_sites_are_single_per_execution(
    func: &CFunction,
    regions: Option<&SealedStructuredRegionArtifact>,
) -> Result<(), SingleEvaluationError> {
    let mut occurrences: BTreeMap<CallSite, Vec<Option<RegionId>>> = BTreeMap::new();
    for stmt in &func.body {
        collect_in_stmt(stmt, regions, None, &mut occurrences);
    }
    for (site, occurrence_regions) in occurrences {
        if occurrence_regions.len() < 2 {
            continue;
        }
        let pairwise_exclusive = regions.is_some_and(|regions| {
            occurrence_regions.iter().enumerate().all(|(index, left)| {
                occurrence_regions[index + 1..].iter().all(|right| {
                    left.zip(*right)
                        .is_some_and(|(left, right)| regions.regions_are_exclusive(left, right))
                })
            })
        });
        if !pairwise_exclusive {
            return Err(
                SingleEvaluationError::RepeatedCallRequiresCertifiedBinding {
                    site,
                    occurrences: occurrence_regions.len(),
                },
            );
        }
    }
    Ok(())
}

fn collect_in_stmt(
    stmt: &CStmt,
    regions: Option<&SealedStructuredRegionArtifact>,
    current_region: Option<RegionId>,
    occurrences: &mut BTreeMap<CallSite, Vec<Option<RegionId>>>,
) {
    match stmt {
        CStmt::StructuredRegion { marker, stmt } => {
            let region = regions
                .and_then(|regions| regions.node_for_marker(marker).map(|(region, _)| region));
            collect_in_stmt(stmt, regions, region, occurrences);
            return;
        }
        CStmt::Observed { stmt, .. } => {
            collect_in_stmt(stmt, regions, current_region, occurrences);
            return;
        }
        _ => {}
    }

    for_each_expr(stmt, &mut |expr| {
        collect_in_expr(expr, current_region, occurrences)
    });
    for_each_child_block(stmt, &mut |stmts| {
        for inner in stmts {
            collect_in_stmt(inner, regions, current_region, occurrences);
        }
    });
}

fn collect_in_expr(
    expr: &CExpr,
    current_region: Option<RegionId>,
    occurrences: &mut BTreeMap<CallSite, Vec<Option<RegionId>>>,
) {
    expr.visit(&mut |node| {
        if let Some(source) = source_of(node) {
            occurrences.entry(source).or_default().push(current_region);
        }
    });
}

fn for_each_expr(stmt: &CStmt, f: &mut impl FnMut(&CExpr)) {
    match stmt {
        CStmt::StructuredRegion { stmt, .. } | CStmt::Observed { stmt, .. } => {
            for_each_expr(stmt, f)
        }
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => f(expr),
        CStmt::Decl {
            init: Some(expr), ..
        } => f(expr),
        CStmt::If { cond, .. } => f(cond),
        CStmt::While { cond, .. } | CStmt::DoWhile { cond, .. } => f(cond),
        CStmt::For { cond, update, .. } => {
            if let Some(cond) = cond {
                f(cond);
            }
            if let Some(update) = update {
                f(update);
            }
        }
        CStmt::Switch { expr, .. } => f(expr),
        _ => {}
    }
}

pub(crate) fn for_each_child_block(stmt: &CStmt, f: &mut impl FnMut(&[CStmt])) {
    match stmt {
        CStmt::StructuredRegion { .. } | CStmt::Observed { .. } => {
            unreachable!("leading wrappers are handled by collect_in_stmt")
        }
        CStmt::Block(stmts) => f(stmts),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            f(std::slice::from_ref(then_body.as_ref()));
            if let Some(body) = else_body {
                f(std::slice::from_ref(body.as_ref()));
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            f(std::slice::from_ref(body.as_ref()))
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                f(std::slice::from_ref(init.as_ref()));
            }
            f(std::slice::from_ref(body.as_ref()));
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                f(&case.body);
            }
            if let Some(default) = default {
                f(default);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{CLocal, CParam, CType};
    use crate::structured_region::{
        StructuredRegionKind, StructuredRegionMarker, seal_structured_body_for_test,
    };

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    fn call(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        name: &str,
        site: CallSite,
    ) -> CExpr {
        CExpr::Call {
            func: Box::new(CExpr::Var(crate::symbol::declare(symbols, name))),
            args: vec![CExpr::IntLit(16)],
            site: Some(site),
        }
    }

    /// A function that owns the table its body declared into. Cloning keeps the
    /// table's identity, so the identifiers in the body still resolve.
    fn function_from(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        body: Vec<CStmt>,
    ) -> CFunction {
        CFunction {
            externs: Vec::new(),
            extern_objects: Vec::new(),
            name: "f".to_string(),
            ret_type: CType::Int {
                bits: 32,
                signedness: r2types::Signedness::Signed,
            },
            params: Vec::<CParam>::new(),
            locals: Vec::<CLocal>::new(),
            body,
            params_known: true,
            symbols: std::rc::Rc::new(std::cell::RefCell::new(symbols.borrow().clone())),
        }
    }

    #[test]
    fn repeated_site_is_refused_without_mutating_the_function() {
        let symbols = test_table();
        let func = function_from(
            &symbols,
            vec![
                CStmt::Expr(call(&symbols, "fcn.1000", (0x1000, 0))),
                CStmt::Return(Some(call(&symbols, "fcn.1000", (0x1000, 0)))),
            ],
        );
        let before = func.body.clone();

        assert_eq!(
            verify_call_sites_are_single_per_execution(&func, None),
            Err(
                SingleEvaluationError::RepeatedCallRequiresCertifiedBinding {
                    site: (0x1000, 0),
                    occurrences: 2,
                }
            )
        );
        assert_eq!(func.body, before);
    }

    #[test]
    fn distinct_single_occurrences_are_accepted_without_mutation() {
        let symbols = test_table();
        let func = function_from(
            &symbols,
            vec![
                CStmt::Expr(call(&symbols, "fcn.1000", (0x1000, 0))),
                CStmt::Return(Some(call(&symbols, "fcn.1000", (0x2000, 0)))),
            ],
        );
        let before = func.body.clone();

        assert_eq!(
            verify_call_sites_are_single_per_execution(&func, None),
            Ok(())
        );
        assert_eq!(func.body, before);
    }

    #[test]
    fn repeated_site_in_exclusive_regions_is_one_evaluation_per_execution() {
        let symbols = test_table();
        let marked = CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::IfThenElse),
                CStmt::If {
                    cond: CExpr::IntLit(1),
                    then_body: Box::new(CStmt::structured_region(
                        StructuredRegionMarker::unsealed(0x1020, StructuredRegionKind::Block),
                        CStmt::Expr(call(&symbols, "fcn.1000", (0x1000, 0))),
                    )),
                    else_body: Some(Box::new(CStmt::structured_region(
                        StructuredRegionMarker::unsealed(0x1030, StructuredRegionKind::Block),
                        CStmt::Expr(call(&symbols, "fcn.1000", (0x1000, 0))),
                    ))),
                },
            ),
        );
        let sealed = seal_structured_body_for_test(marked).expect("sealed structured body");
        let (stmt, regions) = sealed.into_marked_parts();
        let func = function_from(&symbols, vec![stmt]);

        assert_eq!(
            verify_call_sites_are_single_per_execution(&func, Some(&regions)),
            Ok(())
        );
    }
}
