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
pub(crate) fn names_mentioned_without_a_declaration(
    func: &CFunction,
) -> Vec<crate::symbol::SymbolId> {
    let mut declared = func
        .params
        .iter()
        .map(|param| param.name)
        .chain(func.locals.iter().map(|local| local.name))
        .collect::<std::collections::HashSet<_>>();
    declared.extend(crate::declarations_in_stmts(&func.body));
    let mut undeclared = crate::collect_stmt_var_names(&func.body)
        .into_iter()
        .filter(|name| !declared.contains(name))
        .collect::<Vec<_>>();
    undeclared.sort_unstable();
    undeclared
}
