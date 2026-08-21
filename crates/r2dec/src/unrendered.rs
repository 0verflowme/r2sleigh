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

use crate::ast::{CExpr, CFunction, CLocal, CStmt, CType, SwitchCase};

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

/// Give the carriers the body renders a declaration and a name C can spell.
///
/// A body that names something it never declares does not compile, and some of
/// what it names -- `tmp:11f80` -- is not an identifier at all. Both are the
/// same omission: the rendering put a carrier on the page and said nothing
/// about it. Say it. The value is real, it is read where it is written, and a
/// declaration is what lets a reader follow it from one to the other.
///
/// This does not make a carrier mean anything it did not already mean. What it
/// removes is a body that cannot be compiled or quoted, and a note on every
/// line saying so.
pub(crate) fn declare_rendered_carriers(
    func: &mut CFunction,
    type_hints: &std::collections::HashMap<String, CType>,
) {
    let mut declared = BTreeSet::new();
    for param in &func.params {
        declared.insert(param.name.clone());
    }
    for local in &func.locals {
        declared.insert(local.name.clone());
    }
    let mut undeclared = BTreeSet::new();
    collect_block_undeclared(&func.body, &declared, &mut undeclared);
    if undeclared.is_empty() {
        return;
    }
    // A spelled name has to stay distinct from the other names in the body, or
    // two carriers would become one. A name already spellable keeps itself.
    let mut taken = declared.clone();
    taken.extend(collect_block_names(&func.body));
    let mut renames = std::collections::HashMap::new();
    let mut declarations = Vec::new();
    for name in undeclared {
        taken.remove(&name);
        let spelled = spell_as_identifier(&name, &mut taken);
        let ty = type_hints
            .get(&name)
            .or_else(|| type_hints.get(&spelled))
            .cloned()
            .filter(|ty| !matches!(ty, CType::Unknown))
            // Nothing said what it holds, and a declaration has to say
            // something. Its width is what the machine gave it, and unsigned is
            // what a carrier is until something reads it as a number.
            .unwrap_or(CType::UInt(64));
        if spelled != name {
            renames.insert(name, spelled.clone());
        }
        declarations.push(CLocal {
            ty,
            name: spelled,
            stack_offset: None,
        });
    }
    if !renames.is_empty() {
        crate::post_rename::rewrite_function_names(func, &renames);
    }
    func.locals.extend(declarations);
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

fn walk_stmts(stmts: &[CStmt], visit: &mut impl FnMut(&CExpr)) {
    for stmt in stmts {
        walk_stmt(stmt, visit);
    }
}

fn walk_stmt(stmt: &CStmt, visit: &mut impl FnMut(&CExpr)) {
    for expr in statement_exprs(stmt) {
        visit(expr);
    }
    match stmt {
        CStmt::Block(body) => walk_stmts(body, visit),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            walk_stmt(then_body, visit);
            if let Some(else_body) = else_body {
                walk_stmt(else_body, visit);
            }
        }
        CStmt::While { body, .. }
        | CStmt::DoWhile { body, .. }
        | CStmt::For { body, .. } => walk_stmt(body, visit),
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                walk_stmts(&case.body, visit);
            }
            if let Some(default) = default {
                walk_stmts(default, visit);
            }
        }
        _ => {}
    }
}

fn collect_block_undeclared(
    stmts: &[CStmt],
    declared: &BTreeSet<String>,
    out: &mut BTreeSet<String>,
) {
    walk_stmts(stmts, &mut |expr| collect_undeclared(expr, declared, out));
}

fn collect_block_names(stmts: &[CStmt]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    walk_stmts(stmts, &mut |expr| {
        expr.visit(&mut |node| {
            if let CExpr::Var(name) = node {
                names.insert(name.clone());
            }
        });
    });
    names
}

/// Spell every name in the rendered function the way C spells an identifier.
///
/// `declare_rendered_carriers` spells the names it declares, but only those: a
/// name a statement declares for itself was already accounted for and so was
/// never asked whether C could read it. Lane projections arrive that way and
/// reach the page as `tregalias:1000007c0:2d:0`, which is not an identifier and
/// not compilable.
///
/// Whether a name is declared and whether it can be written down are different
/// questions, so this asks the second one about every name in the function.
pub(crate) fn spell_every_name_as_c(func: &mut CFunction) {
    let mut names = collect_block_names(&func.body);
    collect_block_declared(&func.body, &mut names);
    for param in &func.params {
        names.insert(param.name.clone());
    }
    for local in &func.locals {
        names.insert(local.name.clone());
    }
    let unspellable = names
        .iter()
        .filter(|name| !is_c_identifier(name) && !names_something_outside_the_function(name))
        .cloned()
        .collect::<Vec<_>>();
    if unspellable.is_empty() {
        return;
    }
    // Everything already readable keeps its spelling and its claim on it, so
    // spelling one name can never collide with another.
    let mut taken = names
        .iter()
        .filter(|name| is_c_identifier(name))
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut renames = std::collections::HashMap::new();
    for name in unspellable {
        let spelled = spell_as_identifier(&name, &mut taken);
        renames.insert(name, spelled);
    }
    for local in &mut func.locals {
        if let Some(spelled) = renames.get(&local.name) {
            local.name = spelled.clone();
        }
    }
    for param in &mut func.params {
        if let Some(spelled) = renames.get(&param.name) {
            param.name = spelled.clone();
        }
    }
    crate::post_rename::rewrite_function_names(func, &renames);
}

/// Whether C could read this name as an identifier.
fn is_c_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

/// Names a statement declares for itself, which nothing else records.
fn collect_block_declared(stmts: &[CStmt], names: &mut BTreeSet<String>) {
    for stmt in stmts {
        match stmt {
            CStmt::Decl { name, .. } => {
                names.insert(name.clone());
            }
            CStmt::Block(body) => collect_block_declared(body, names),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_block_declared(std::slice::from_ref(then_body), names);
                if let Some(body) = else_body {
                    collect_block_declared(std::slice::from_ref(body), names);
                }
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
                collect_block_declared(std::slice::from_ref(body), names);
            }
            CStmt::For { init, body, .. } => {
                if let Some(init) = init {
                    collect_block_declared(std::slice::from_ref(init), names);
                }
                collect_block_declared(std::slice::from_ref(body), names);
            }
            CStmt::Switch { cases, default, .. } => {
                for case in cases {
                    collect_block_declared(&case.body, names);
                }
                if let Some(body) = default {
                    collect_block_declared(body, names);
                }
            }
            _ => {}
        }
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
    fn a_name_a_statement_declares_for_itself_is_still_spelled_as_c() {
        // A lane projection declares itself in the body, so nothing else had
        // reason to ask whether C could read the name it chose.
        let mut func = function(
            Vec::new(),
            Vec::new(),
            vec![
                CStmt::Decl {
                    ty: CType::UInt(32),
                    name: "tmp:regalias:7c0:2d:0".to_string(),
                    init: Some(CExpr::IntLit(0)),
                },
                CStmt::Return(Some(CExpr::Var("tmp:regalias:7c0:2d:0".to_string()))),
            ],
        );

        spell_every_name_as_c(&mut func);

        let names = collect_block_names(&func.body);
        assert!(
            names.iter().all(|name| is_c_identifier(name)),
            "no name may reach the page that C cannot read: {names:?}"
        );
        let mut declared = BTreeSet::new();
        collect_block_declared(&func.body, &mut declared);
        assert!(declared.iter().all(|name| is_c_identifier(name)));
        // The reference and the declaration must still be the same name.
        assert_eq!(declared, names);
    }

    #[test]
    fn a_readable_name_keeps_its_spelling_and_its_claim_on_it() {
        let mut func = function(
            vec!["total"],
            Vec::new(),
            vec![
                CStmt::Decl {
                    ty: CType::UInt(32),
                    name: "tmp:total".to_string(),
                    init: Some(CExpr::IntLit(0)),
                },
                CStmt::Return(Some(CExpr::Var("total".to_string()))),
            ],
        );

        spell_every_name_as_c(&mut func);

        assert_eq!(func.params[0].name, "total", "a readable name is untouched");
        let mut declared = BTreeSet::new();
        collect_block_declared(&func.body, &mut declared);
        assert!(
            !declared.contains("total"),
            "spelling one name must not collide with another: {declared:?}"
        );
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
