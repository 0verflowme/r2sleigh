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

use crate::ast::{CFunction, CStmt, CType, SwitchCase};

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
        CStmt::Observed { id, stmt } => CStmt::observed(id, drop_void_return_value(*stmt)),
        CStmt::Return(Some(_)) => CStmt::Return(None),
        CStmt::Block(body) => CStmt::Block(body.into_iter().map(drop_void_return_value).collect()),
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
            default: default.map(|body| body.into_iter().map(drop_void_return_value).collect()),
        },
        other => other,
    }
}
/// Drop a label nothing jumps to.
///
/// A label can only be attached to a block while it is being written, so a
/// block that turns out to need one after the fact can never be given it. The
/// answer is to spell one for every block and take back the ones no jump
/// names, which leaves the same labels a body would have had and lets any
/// block be a destination.
pub(crate) fn prune_unreferenced_labels(func: &mut CFunction) {
    let mut targeted = std::collections::BTreeSet::new();
    for stmt in &func.body {
        collect_goto_targets(stmt, &mut targeted);
    }
    let body = std::mem::take(&mut func.body);
    func.body = body
        .into_iter()
        .filter_map(|stmt| drop_labels_outside(stmt, &targeted))
        .collect();
}

fn collect_goto_targets(stmt: &CStmt, out: &mut std::collections::BTreeSet<String>) {
    match stmt {
        CStmt::Observed { stmt, .. } => collect_goto_targets(stmt, out),
        CStmt::Goto(label) => {
            out.insert(label.clone());
        }
        CStmt::Block(body) => {
            for inner in body {
                collect_goto_targets(inner, out);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            collect_goto_targets(then_body, out);
            if let Some(body) = else_body {
                collect_goto_targets(body, out);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } | CStmt::For { body, .. } => {
            collect_goto_targets(body, out)
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                for inner in &case.body {
                    collect_goto_targets(inner, out);
                }
            }
            if let Some(body) = default {
                for inner in body {
                    collect_goto_targets(inner, out);
                }
            }
        }
        _ => {}
    }
}

fn drop_labels_outside(
    stmt: CStmt,
    targeted: &std::collections::BTreeSet<String>,
) -> Option<CStmt> {
    match stmt {
        CStmt::Observed { id, stmt } => {
            drop_labels_outside(*stmt, targeted).map(|stmt| CStmt::observed(id, stmt))
        }
        CStmt::Label(name) if !targeted.contains(&name) => None,
        CStmt::Block(body) => Some(CStmt::Block(
            body.into_iter()
                .filter_map(|inner| drop_labels_outside(inner, targeted))
                .collect(),
        )),
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => Some(CStmt::If {
            cond,
            then_body: Box::new(drop_labels_outside(*then_body, targeted).unwrap_or(CStmt::Empty)),
            else_body: else_body
                .map(|body| Box::new(drop_labels_outside(*body, targeted).unwrap_or(CStmt::Empty))),
        }),
        CStmt::While { cond, body } => Some(CStmt::While {
            cond,
            body: Box::new(drop_labels_outside(*body, targeted).unwrap_or(CStmt::Empty)),
        }),
        CStmt::DoWhile { body, cond } => Some(CStmt::DoWhile {
            body: Box::new(drop_labels_outside(*body, targeted).unwrap_or(CStmt::Empty)),
            cond,
        }),
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => Some(CStmt::For {
            init,
            cond,
            update,
            body: Box::new(drop_labels_outside(*body, targeted).unwrap_or(CStmt::Empty)),
        }),
        CStmt::Switch {
            expr,
            cases,
            default,
        } => Some(CStmt::Switch {
            expr,
            cases: cases
                .into_iter()
                .map(|case| SwitchCase {
                    body: case
                        .body
                        .into_iter()
                        .filter_map(|inner| drop_labels_outside(inner, targeted))
                        .collect(),
                    ..case
                })
                .collect(),
            default: default.map(|body| {
                body.into_iter()
                    .filter_map(|inner| drop_labels_outside(inner, targeted))
                    .collect()
            }),
        }),
        other => Some(other),
    }
}

/// Every name the body mentions that the function never declares.
///
/// A reference carries an identifier the table issued, so this cannot find a
/// word that resolves to nothing -- that was the old failure and the table
/// removed it. What it finds is a name the reader has no declaration for: the
/// table knows it, the C does not. A value with more than one reader is
/// supposed to become a typed local, and this is the check that it did.
/// Names the function mentions that no enclosing scope declares.
///
/// The property being checked is that every emitted identifier is declared
/// once, in a scope that dominates every surviving read of it. This used to be
/// approximated by collecting every declaration anywhere in the function and
/// every mention anywhere, then subtracting -- which answers the much weaker
/// question of whether the name is declared *somewhere*.
///
/// The two differ wherever C's scopes do not follow the nesting of the tree.
/// A `do { ... } while (cond)` is the case that matters here: the condition is
/// written inside the loop but evaluated in the scope that encloses it, so a
/// temporary the body declares is not in scope for the test that reads it. The
/// flat check saw the declaration and the mention and was satisfied; the
/// compiler saw one name undeclared at the condition and another unused inside
/// the body, and rejected the function.
///
/// Reporting that is the point. A name resolved by a scope that does not
/// dominate its read is not a rendering that happens to be untidy, it is C
/// that does not compile, and the caller refuses the function rather than
/// emitting it.
pub(crate) fn names_mentioned_without_a_declaration(
    func: &CFunction,
) -> Vec<crate::symbol::SymbolId> {
    let outermost = func
        .params
        .iter()
        .map(|param| param.name)
        .chain(func.locals.iter().map(|local| local.name))
        .collect::<std::collections::HashSet<_>>();
    let mut scopes = vec![outermost];
    let mut undeclared = std::collections::HashSet::new();
    check_scope(&func.body, &mut scopes, &mut undeclared);
    let mut undeclared = undeclared.into_iter().collect::<Vec<_>>();
    undeclared.sort_unstable();
    undeclared
}

/// Whether any open scope declares this name.
fn in_scope(
    scopes: &[std::collections::HashSet<crate::symbol::SymbolId>],
    name: crate::symbol::SymbolId,
) -> bool {
    scopes.iter().any(|scope| scope.contains(&name))
}

fn check_expr(
    expr: &crate::ast::CExpr,
    scopes: &[std::collections::HashSet<crate::symbol::SymbolId>],
    undeclared: &mut std::collections::HashSet<crate::symbol::SymbolId>,
) {
    let mut mentioned = std::collections::HashSet::new();
    crate::collect_expr_var_names(expr, &mut mentioned);
    for name in mentioned {
        if !in_scope(scopes, name) {
            undeclared.insert(name);
        }
    }
}

/// Check one statement list as a nested scope.
fn check_nested(
    statements: &[CStmt],
    scopes: &mut Vec<std::collections::HashSet<crate::symbol::SymbolId>>,
    undeclared: &mut std::collections::HashSet<crate::symbol::SymbolId>,
) {
    scopes.push(std::collections::HashSet::new());
    check_scope(statements, scopes, undeclared);
    scopes.pop();
}

fn check_nested_stmt(
    statement: &CStmt,
    scopes: &mut Vec<std::collections::HashSet<crate::symbol::SymbolId>>,
    undeclared: &mut std::collections::HashSet<crate::symbol::SymbolId>,
) {
    check_nested(std::slice::from_ref(statement), scopes, undeclared);
}

/// Check statements in order within the innermost open scope.
///
/// Order matters: a declaration is in scope for what follows it, not for what
/// precedes it, and its own initializer is checked before the name it binds
/// becomes visible.
fn check_scope(
    statements: &[CStmt],
    scopes: &mut Vec<std::collections::HashSet<crate::symbol::SymbolId>>,
    undeclared: &mut std::collections::HashSet<crate::symbol::SymbolId>,
) {
    for statement in statements {
        match statement {
            // Neither wrapper is a C scope; both are transparent here.
            CStmt::Observed { stmt, .. } | CStmt::StructuredRegion { stmt, .. } => {
                check_scope(std::slice::from_ref(stmt), scopes, undeclared);
            }
            CStmt::Block(inner) => check_nested(inner, scopes, undeclared),
            CStmt::Decl { name, init, .. } => {
                if let Some(init) = init {
                    check_expr(init, scopes, undeclared);
                }
                if let Some(scope) = scopes.last_mut() {
                    scope.insert(*name);
                }
            }
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
                check_expr(expr, scopes, undeclared);
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                check_expr(cond, scopes, undeclared);
                check_nested_stmt(then_body, scopes, undeclared);
                if let Some(else_body) = else_body {
                    check_nested_stmt(else_body, scopes, undeclared);
                }
            }
            CStmt::While { cond, body } => {
                check_expr(cond, scopes, undeclared);
                check_nested_stmt(body, scopes, undeclared);
            }
            // The body is a scope of its own and the condition is not inside
            // it, however the source is laid out.
            CStmt::DoWhile { body, cond } => {
                check_nested_stmt(body, scopes, undeclared);
                check_expr(cond, scopes, undeclared);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                // The initializer's declarations are in scope for the condition,
                // the update and the body, and nowhere after the loop.
                scopes.push(std::collections::HashSet::new());
                if let Some(init) = init {
                    check_scope(std::slice::from_ref(init), scopes, undeclared);
                }
                if let Some(cond) = cond {
                    check_expr(cond, scopes, undeclared);
                }
                if let Some(update) = update {
                    check_expr(update, scopes, undeclared);
                }
                check_nested_stmt(body, scopes, undeclared);
                scopes.pop();
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                check_expr(expr, scopes, undeclared);
                for case in cases {
                    check_nested(&case.body, scopes, undeclared);
                }
                if let Some(default) = default {
                    check_nested(default, scopes, undeclared);
                }
            }
            CStmt::Empty
            | CStmt::Return(None)
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_) => {}
        }
    }
}
