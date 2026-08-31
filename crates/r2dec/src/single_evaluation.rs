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
//! site needs an upstream certificate that identifies its one result binding
//! and proves where the evaluation occurs. The rendered AST does not currently
//! carry that certificate, so repetition is refused. Moving the first textual
//! occurrence, adopting a nearby assignment, or retargeting later occurrences
//! would reconstruct execution and dominance facts in the renderer.

use std::collections::BTreeMap;

use crate::ast::{CExpr, CFunction, CStmt};
use crate::binding_plan::BindingNameResolution;

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
) -> Result<(), SingleEvaluationError> {
    verify_call_sites_are_single(func)
}

fn verify_call_sites_are_single(func: &CFunction) -> Result<(), SingleEvaluationError> {
    let mut counts: BTreeMap<CallSite, usize> = BTreeMap::new();
    for stmt in &func.body {
        count_in_stmt(stmt, &mut counts);
    }
    match counts.into_iter().find(|(_, occurrences)| *occurrences > 1) {
        Some((site, occurrences)) => {
            Err(SingleEvaluationError::RepeatedCallRequiresCertifiedBinding { site, occurrences })
        }
        None => Ok(()),
    }
}

fn count_in_stmt(stmt: &CStmt, counts: &mut BTreeMap<CallSite, usize>) {
    for_each_expr(stmt, &mut |expr| count_in_expr(expr, counts));
    for_each_child_block(stmt, &mut |stmts| {
        for inner in stmts {
            count_in_stmt(inner, counts);
        }
    });
}

fn count_in_expr(expr: &CExpr, counts: &mut BTreeMap<CallSite, usize>) {
    expr.visit(&mut |node| {
        if let Some(source) = source_of(node) {
            *counts.entry(source).or_insert(0) += 1;
        }
    });
}

pub(crate) fn children_mut(expr: &mut CExpr) -> Vec<&mut CExpr> {
    match expr {
        CExpr::Observed { expr, .. } => vec![expr.as_mut()],
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => Vec::new(),
        CExpr::Unary { operand, .. } => vec![operand.as_mut()],
        CExpr::Binary { left, right, .. } => vec![left.as_mut(), right.as_mut()],
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => vec![cond.as_mut(), then_expr.as_mut(), else_expr.as_mut()],
        CExpr::Cast { expr, .. } => vec![expr.as_mut()],
        CExpr::Call { func, args, .. } => {
            let mut out = vec![func.as_mut()];
            out.extend(args.iter_mut());
            out
        }
        CExpr::Subscript { base, index } => vec![base.as_mut(), index.as_mut()],
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => vec![base.as_mut()],
        CExpr::Sizeof(inner) | CExpr::AddrOf(inner) | CExpr::Deref(inner) | CExpr::Paren(inner) => {
            vec![inner.as_mut()]
        }
        CExpr::Comma(items) => items.iter_mut().collect(),
    }
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

pub(crate) fn for_each_expr_mut(stmt: &mut CStmt, f: &mut impl FnMut(&mut CExpr)) {
    match stmt {
        CStmt::StructuredRegion { stmt, .. } | CStmt::Observed { stmt, .. } => {
            for_each_expr_mut(stmt, f)
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
        CStmt::StructuredRegion { stmt, .. } | CStmt::Observed { stmt, .. } => {
            for_each_child_block(stmt, f)
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

/// Visit each nested statement list, saying whether it shares the enclosing
/// scope's bindings on exit. A plain block always runs, so what it binds still
/// holds afterwards; a branch arm or a loop body does not.
pub(crate) fn for_each_child_block_mut(
    stmt: &mut CStmt,
    f: &mut impl FnMut(&mut Vec<CStmt>, bool),
) {
    fn as_block(body: &mut Box<CStmt>, f: &mut impl FnMut(&mut Vec<CStmt>, bool), shares: bool) {
        match body.as_mut() {
            CStmt::StructuredRegion { stmt, .. } | CStmt::Observed { stmt, .. } => {
                as_block(stmt, f, shares)
            }
            CStmt::Block(stmts) => f(stmts, shares),
            other => {
                let mut stmts = vec![std::mem::replace(other, CStmt::Empty)];
                f(&mut stmts, shares);
                *other = if stmts.len() == 1 {
                    stmts.pop().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(stmts)
                };
            }
        }
    }

    match stmt {
        CStmt::StructuredRegion { stmt, .. } | CStmt::Observed { stmt, .. } => {
            for_each_child_block_mut(stmt, f)
        }
        CStmt::Block(stmts) => f(stmts, true),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            as_block(then_body, f, false);
            if let Some(body) = else_body {
                as_block(body, f, false);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => as_block(body, f, false),
        CStmt::For { body, .. } => as_block(body, f, false),
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                let taken = std::mem::take(&mut case.body);
                let mut stmts = taken;
                f(&mut stmts, false);
                case.body = stmts;
            }
            if let Some(default) = default {
                f(default, false);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{CLocal, CParam, CType};

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
            verify_call_sites_are_single(&func),
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

        assert_eq!(verify_call_sites_are_single(&func), Ok(()));
        assert_eq!(func.body, before);
    }
}
