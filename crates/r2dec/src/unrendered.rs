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
/// Spell a carrier's name the way C spells an identifier.
///
/// SLEIGH names its scratch by space and offset, `tmp:11f80`, which is exact
/// and is not an identifier. Keep what it says and drop what C cannot read.
fn spell_as_identifier(name: &str, taken: &mut BTreeSet<String>) -> String {
    let mut spelled = name
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect::<String>();
    if spelled.starts_with(|ch: char| ch.is_ascii_digit()) {
        spelled.insert(0, '_');
    }
    if spelled.is_empty() {
        spelled.push('_');
    }
    let base = spelled.clone();
    let mut suffix = 2usize;
    while !taken.insert(spelled.clone()) {
        spelled = format!("{base}_{suffix}");
        suffix += 1;
    }
    spelled
}

/// Spell every name this function declares the way C spells an identifier.
///
/// Lane projections and lifted temporaries are named by the machine, and those
/// names are not identifiers: `tregalias:1000007c0:2d:0` does not compile. The
/// question is not whether a name is declared -- every name is, now that a
/// reference is one -- but whether it can be written down.
///
/// It asks the table rather than the body, because the table is where names
/// live and a reference follows whatever the table says.
pub(crate) fn spell_every_name_as_c(func: &mut CFunction) {
    let unspellable = func
        .symbols
        .borrow()
        .iter()
        .filter(|(_, symbol)| !is_c_identifier(&symbol.name))
        .map(|(_, symbol)| symbol.name.to_string())
        .collect::<Vec<_>>();
    if unspellable.is_empty() {
        return;
    }
    // A readable name keeps its spelling and its claim on it, so spelling one
    // can never collide with another.
    let mut taken = func
        .symbols
        .borrow()
        .iter()
        .filter(|(_, symbol)| is_c_identifier(&symbol.name))
        .map(|(_, symbol)| symbol.name.to_string())
        .collect::<BTreeSet<_>>();
    let mut renames = std::collections::HashMap::new();
    for name in unspellable {
        let spelled = spell_as_identifier(&name, &mut taken);
        renames.insert(name, spelled);
    }
    func.symbols.borrow_mut().follow_renames(&renames);
}

/// Whether C could read this name as an identifier.
fn is_c_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, CLocal, CParam, CType};

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    fn function(params: Vec<&str>, locals: Vec<&str>, body: Vec<CStmt>) -> CFunction {
        let symbols = test_table();
        CFunction {
            name: "f".to_string(),
            ret_type: CType::Int(32),
            params: params
                .into_iter()
                .map(|name| CParam {
                    ty: CType::Int(32),
                    name: crate::symbol::declare(&symbols, &name.to_string()),
                })
                .collect(),
            locals: locals
                .into_iter()
                .map(|name| CLocal {
                    ty: CType::Int(32),
                    name: crate::symbol::declare(&symbols, &name.to_string()),
                    stack_offset: None,
                })
                .collect(),
            body,
            params_known: true,
            symbols: std::rc::Rc::new(symbols),
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
    fn a_name_a_statement_declares_for_itself_is_still_spelled_as_c() {
        let symbols = test_table();
        // A lane projection declares itself in the body, so nothing else had
        // reason to ask whether C could read the name it chose.
        let mut func = function(
            Vec::new(),
            Vec::new(),
            vec![
                CStmt::Decl {
                    ty: CType::UInt(32),
                    name: crate::symbol::declare(&symbols, "tmp:regalias:7c0:2d:0"),
                    init: Some(CExpr::IntLit(0)),
                },
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "tmp:regalias:7c0:2d:0"))),
            ],
        );

        spell_every_name_as_c(&mut func);

        // Every name the function can write down is one the table issued, so
        // asking the table is asking about every mention at once.
        let table = func.symbols.borrow();
        let unreadable = table
            .iter()
            .map(|(_, symbol)| symbol.name.to_string())
            .filter(|name| !is_c_identifier(name))
            .collect::<Vec<_>>();
        assert!(
            unreadable.is_empty(),
            "no name may reach the page that C cannot read: {unreadable:?}"
        );
    }

    #[test]
    fn a_readable_name_keeps_its_spelling_and_its_claim_on_it() {
        let symbols = test_table();
        let mut func = function(
            vec!["total"],
            Vec::new(),
            vec![
                CStmt::Decl {
                    ty: CType::UInt(32),
                    name: crate::symbol::declare(&symbols, "tmp:total"),
                    init: Some(CExpr::IntLit(0)),
                },
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "total"))),
            ],
        );

        spell_every_name_as_c(&mut func);

        // The readable name keeps its spelling, so the one that had to be
        // respelled cannot have taken it.
        let table = func.symbols.borrow();
        assert_eq!(table.name(func.params[0].name), "total");
        let claims = table
            .iter()
            .filter(|(_, symbol)| &*symbol.name == "total")
            .count();
        assert_eq!(claims, 1, "spelling one name must not collide with another");
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
        CStmt::While { body, .. }
        | CStmt::DoWhile { body, .. }
        | CStmt::For { body, .. } => collect_goto_targets(body, out),
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
            then_body: Box::new(
                drop_labels_outside(*then_body, targeted).unwrap_or(CStmt::Empty),
            ),
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

/// Declare a name the body assigns and nothing else declares.
///
/// Structuring rewrites loops after the pass that declares carriers has run, so
/// an assignment it introduces -- a for's init, or one folded into its
/// condition -- names something when nothing is left to notice. C requires a
/// declaration, and the slot may be read after the loop, so it is hoisted to
/// the function rather than folded into the statement.
///
/// Only names the body *assigns* are declared. A name that is only ever read
/// has no definition, and declaring it would turn a dangling reference into
/// valid C that reads uninitialised memory, hiding the defect instead of
/// reporting it.
pub(crate) fn declare_assigned_names_without_a_declaration(func: &mut CFunction) {
    let declared = func
        .params
        .iter()
        .map(|param| param.name)
        .chain(func.locals.iter().map(|local| local.name))
        .chain(crate::declarations_in_stmts(&func.body))
        .collect::<std::collections::HashSet<_>>();
    let mut hoisted: Vec<(crate::symbol::SymbolId, crate::ast::CType)> = Vec::new();
    collect_assigned_undeclared(&func.body, &declared, &mut hoisted);
    for (name, ty) in hoisted {
        func.locals.push(crate::ast::CLocal {
            ty,
            name,
            stack_offset: None,
        });
    }
}

/// Every undeclared name an assignment anywhere in these statements writes to.
fn collect_assigned_undeclared(
    stmts: &[CStmt],
    declared: &std::collections::HashSet<crate::symbol::SymbolId>,
    out: &mut Vec<(crate::symbol::SymbolId, crate::ast::CType)>,
) {
    for stmt in stmts {
        let mut inspect = |expr: &CExpr| {
            expr.visit(&mut |node| {
                if let CExpr::Binary {
                    op: crate::ast::BinaryOp::Assign,
                    left,
                    right,
                } = node
                    && let CExpr::Var(name) = left.as_ref()
                    && !declared.contains(name)
                    && !out.iter().any(|(seen, _)| seen == name)
                {
                    out.push((*name, width_of_initial_value(right)));
                }
            });
        };
        match stmt {
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => inspect(expr),
            CStmt::If { cond, .. } | CStmt::While { cond, .. } | CStmt::DoWhile { cond, .. } => {
                inspect(cond)
            }
            CStmt::For {
                init, cond, update, ..
            } => {
                if let Some(CStmt::Expr(expr)) = init.as_deref() {
                    inspect(expr);
                }
                if let Some(cond) = cond {
                    inspect(cond);
                }
                if let Some(update) = update {
                    inspect(update);
                }
            }
            CStmt::Switch { expr, .. } => inspect(expr),
            _ => {}
        }
        crate::single_evaluation::for_each_child_block(stmt, &mut |body| {
            collect_assigned_undeclared(body, declared, out);
        });
    }
}


/// The type to declare an induction variable with, taken from what it starts as.
fn width_of_initial_value(value: &CExpr) -> crate::ast::CType {
    match value {
        CExpr::Cast { ty, .. } => ty.clone(),
        CExpr::UIntLit(_) => crate::ast::CType::UInt(64),
        _ => crate::ast::CType::Int(64),
    }
}
