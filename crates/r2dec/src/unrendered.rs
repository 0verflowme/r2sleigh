//! Names in the output that the function does not declare.
//!
//! A rendering that is incomplete is a smaller failure than one that is wrong,
//! and a rendering that is wrong is far worse when nothing distinguishes it
//! from one that is right. The renderer sometimes emits an identifier that
//! names nothing: a Sleigh temporary such as `tmpOV`, a raw register such as
//! `x8`, or a frame slot such as `local_10` reaching the page as though it
//! were a variable of the program. `(a > 0)` has been printed as
//! `(!(a == 0) && a < 0 == tmpOV)`, and a parameter has been assigned the
//! address of its own home slot, `x = local_10 + 8`.
//!
//! Those are not program text. They were printed with exactly the confidence
//! of the lines around them and carried no marker, so the proof note called
//! the function unremarkable while part of it said nothing true.
//!
//! The test is the one the language already makes: an identifier a function
//! neither takes as a parameter nor declares as a local refers to nothing.
//! Names carrying a namespace -- `sym.imp.malloc`, `dbg.process_string` -- are
//! radare2's spelling for something outside the function and are left alone.
//!
//! The marker names what it found in the terms the comment sanitizer allows --
//! a stack slot, a register, a temporary -- rather than the raw token. The
//! token itself is printed by the statement on the next line, so nothing is
//! withheld by saying it that way.

use std::collections::BTreeSet;

use crate::ast::{CExpr, CFunction, CStmt, CType, SwitchCase};

/// Drop the value from every `return` in a function that returns nothing.
///
/// A `void` function has no value to give back, but the renderer resolved a
/// return carrier anyway and printed it, so `void list_free(Node *head)` ended
/// `return rip;`: a function that returns nothing handing back the program
/// counter. The carrier is not program text and the statement is not C, and
/// the marker beside it reported the symptom rather than the statement being
/// wrong to emit at all.
pub(crate) fn drop_values_from_void_returns(func: &mut CFunction) {
    if !matches!(func.ret_type, CType::Void) {
        return;
    }
    let body = std::mem::take(&mut func.body);
    func.body = body.into_iter().map(drop_void_return_value).collect();
}

fn drop_void_return_value(stmt: CStmt) -> CStmt {
    match stmt {
        CStmt::Return(Some(_)) => CStmt::Return(None),
        CStmt::Block(body) => {
            CStmt::Block(body.into_iter().map(drop_void_return_value).collect())
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => CStmt::If {
            cond,
            then_body: Box::new(drop_void_return_value(*then_body)),
            else_body: else_body.map(|body| Box::new(drop_void_return_value(*body))),
        },
        CStmt::While { cond, body } => CStmt::While {
            cond,
            body: Box::new(drop_void_return_value(*body)),
        },
        CStmt::DoWhile { body, cond } => CStmt::DoWhile {
            body: Box::new(drop_void_return_value(*body)),
            cond,
        },
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => CStmt::For {
            init,
            cond,
            update,
            body: Box::new(drop_void_return_value(*body)),
        },
        CStmt::Switch {
            expr,
            cases,
            default,
        } => CStmt::Switch {
            expr,
            cases: cases
                .into_iter()
                .map(|case| SwitchCase {
                    body: case.body.into_iter().map(drop_void_return_value).collect(),
                    ..case
                })
                .collect(),
            default: default
                .map(|body| body.into_iter().map(drop_void_return_value).collect()),
        },
        other => other,
    }
}

/// Mark every construct that mentions a name this function does not declare.
pub(crate) fn mark_undeclared_names(func: &mut CFunction) {
    let mut declared = BTreeSet::new();
    for param in &func.params {
        declared.insert(param.name.clone());
    }
    for local in &func.locals {
        declared.insert(local.name.clone());
    }
    let body = std::mem::take(&mut func.body);
    func.body = mark_block(body, &declared);
}

fn mark_block(stmts: Vec<CStmt>, declared: &BTreeSet<String>) -> Vec<CStmt> {
    let mut out = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        let stmt = mark_nested(stmt, declared);
        let mut undeclared = BTreeSet::new();
        for expr in statement_exprs(&stmt) {
            collect_undeclared(expr, declared, &mut undeclared);
        }
        if !undeclared.is_empty() {
            let names = undeclared.into_iter().collect::<Vec<_>>().join(", ");
            out.push(CStmt::comment(format!(
                "r2dec residual: mentions {names}, which this function does not declare"
            )));
        }
        out.push(stmt);
    }
    out
}

fn mark_nested(stmt: CStmt, declared: &BTreeSet<String>) -> CStmt {
    match stmt {
        CStmt::Block(body) => CStmt::Block(mark_block(body, declared)),
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => CStmt::If {
            cond,
            then_body: Box::new(mark_nested(*then_body, declared)),
            else_body: else_body.map(|body| Box::new(mark_nested(*body, declared))),
        },
        CStmt::While { cond, body } => CStmt::While {
            cond,
            body: Box::new(mark_nested(*body, declared)),
        },
        CStmt::DoWhile { body, cond } => CStmt::DoWhile {
            body: Box::new(mark_nested(*body, declared)),
            cond,
        },
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => CStmt::For {
            init,
            cond,
            update,
            body: Box::new(mark_nested(*body, declared)),
        },
        CStmt::Switch {
            expr,
            cases,
            default,
        } => CStmt::Switch {
            expr,
            cases: cases
                .into_iter()
                .map(|case| SwitchCase {
                    body: mark_block(case.body, declared),
                    ..case
                })
                .collect(),
            default: default.map(|body| mark_block(body, declared)),
        },
        other => other,
    }
}

/// The expressions a statement evaluates in its own right. Nested bodies are
/// visited separately so a marker lands beside the statement that carries the
/// name rather than at the top of the construct enclosing it.
fn statement_exprs(stmt: &CStmt) -> Vec<&CExpr> {
    match stmt {
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => vec![expr],
        CStmt::Decl {
            init: Some(expr), ..
        } => vec![expr],
        CStmt::If { cond, .. }
        | CStmt::While { cond, .. }
        | CStmt::DoWhile { cond, .. }
        | CStmt::Switch { expr: cond, .. } => vec![cond],
        CStmt::For { cond, update, .. } => cond.iter().chain(update.iter()).collect(),
        _ => Vec::new(),
    }
}

fn collect_undeclared(expr: &CExpr, declared: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    // A name in call position is what is being called, not a carrier the
    // function reads. No C function declares the functions it calls, so
    // `isnan(x)` was reported as mentioning an undeclared `isnan` and the
    // statement was marked for naming the callee it invokes.
    let mut called = BTreeSet::new();
    expr.visit(&mut |node| {
        if let CExpr::Call { func, .. } = node
            && let CExpr::Var(name) = func.as_ref()
        {
            called.insert(name.clone());
        }
    });
    expr.visit(&mut |node| {
        if let CExpr::Var(name) = node
            && !declared.contains(name)
            && !names_something_outside_the_function(name)
            && !called.contains(name)
        {
            out.insert(name.clone());
        }
    });
}

/// Whether the name refers to something the function does not own: a symbol,
/// an import, another function, or a literal address radare2 spells with a
/// namespace. Those are references, not undeclared variables.
fn names_something_outside_the_function(name: &str) -> bool {
    name.contains('.') || name.parse::<i64>().is_ok() || name.starts_with("0x")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, CLocal, CParam, CType};

    fn function(params: Vec<&str>, locals: Vec<&str>, body: Vec<CStmt>) -> CFunction {
        CFunction {
            name: "f".to_string(),
            ret_type: CType::Int(32),
            params: params
                .into_iter()
                .map(|name| CParam {
                    ty: CType::Int(32),
                    name: name.to_string(),
                })
                .collect(),
            locals: locals
                .into_iter()
                .map(|name| CLocal {
                    ty: CType::Int(32),
                    name: name.to_string(),
                    stack_offset: None,
                })
                .collect(),
            body,
            params_known: true,
        }
    }

    fn markers(func: &CFunction) -> Vec<String> {
        fn walk(stmts: &[CStmt], out: &mut Vec<String>) {
            for stmt in stmts {
                match stmt {
                    CStmt::Comment(text) => out.push(text.clone()),
                    CStmt::Block(body) => walk(body, out),
                    CStmt::If {
                        then_body,
                        else_body,
                        ..
                    } => {
                        walk(std::slice::from_ref(then_body), out);
                        if let Some(body) = else_body {
                            walk(std::slice::from_ref(body), out);
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut out = Vec::new();
        walk(&func.body, &mut out);
        out
    }

    #[test]
    fn a_name_the_function_declares_is_left_alone() {
        let mut func = function(
            vec!["x"],
            vec!["total"],
            vec![CStmt::Return(Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("x".to_string()),
                CExpr::Var("total".to_string()),
            )))],
        );

        mark_undeclared_names(&mut func);

        assert!(markers(&func).is_empty());
    }

    #[test]
    fn a_leaked_machine_name_is_marked_where_it_appears() {
        let mut func = function(
            vec!["a"],
            Vec::new(),
            vec![CStmt::Return(Some(CExpr::binary(
                BinaryOp::BitXor,
                CExpr::Var("a".to_string()),
                CExpr::Var("tmpOV".to_string()),
            )))],
        );

        mark_undeclared_names(&mut func);

        let markers = markers(&func);
        assert_eq!(markers.len(), 1, "{markers:?}");
        assert!(markers[0].contains("tmpOV"), "{markers:?}");
    }

    #[test]
    fn a_namespaced_reference_is_not_an_undeclared_variable() {
        let mut func = function(
            Vec::new(),
            Vec::new(),
            vec![CStmt::Expr(CExpr::call(
                CExpr::Var("sym.imp.malloc".to_string()),
                vec![CExpr::IntLit(8)],
            ))],
        );

        mark_undeclared_names(&mut func);

        assert!(markers(&func).is_empty());
    }

    #[test]
    fn a_marker_lands_inside_the_branch_that_carries_the_name() {
        let mut func = function(
            vec!["x"],
            Vec::new(),
            vec![CStmt::If {
                cond: CExpr::Var("x".to_string()),
                then_body: Box::new(CStmt::Block(vec![CStmt::Expr(CExpr::binary(
                    BinaryOp::Assign,
                    CExpr::Var("x".to_string()),
                    CExpr::Var("local_10".to_string()),
                ))])),
                else_body: None,
            }],
        );

        mark_undeclared_names(&mut func);

        // The marker is inside the branch, not hoisted to the top of the body.
        assert!(matches!(func.body.first(), Some(CStmt::If { .. })));
        let markers = markers(&func);
        assert_eq!(markers.len(), 1, "{markers:?}");
        assert!(markers[0].contains("local_10"), "{markers:?}");
    }
}
