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
//! This pass restores the invariant on the rendered function. Within a scope,
//! the first occurrence of a multiply-rendered call site is assigned to the
//! program variable already authorized for that site, and every later
//! occurrence becomes a mention of that binding. Sites that appear once are
//! left exactly as they are. A repeated site without such a target is refused;
//! this pass never invents a local or its type.
//!
//! Sibling branches do not share bindings. A name bound in one arm of an `if`
//! is neither in scope nor in effect in the other, so each arm starts from the
//! set of bindings that reached the branch, and a loop body starts afresh on
//! the same reasoning: what the previous iteration bound is not what this
//! iteration computes.

use std::collections::BTreeMap;

use crate::ast::{BinaryOp, CExpr, CFunction, CStmt};
use crate::binding_plan::BindingNameResolution;

/// A call site, identified by the address of the call and its index there.
pub(crate) type CallSite = (u64, usize);

/// A repeated call site has no binding-plan-authorized assignment target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SingleEvaluationError {
    MissingAssignmentTarget { site: CallSite },
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
    names: &BindingNameResolution,
) -> Result<(), SingleEvaluationError> {
    bind_each_call_site_once_with(func, |symbol| {
        names.authorizes_program_variable(symbol)
    })
}

fn bind_each_call_site_once_with(
    func: &mut CFunction,
    target_is_authorized: impl Fn(crate::symbol::SymbolId) -> bool,
) -> Result<(), SingleEvaluationError> {
    let mut counts: BTreeMap<CallSite, usize> = BTreeMap::new();
    for stmt in &func.body {
        count_in_stmt(stmt, &mut counts);
    }
    let repeated: Vec<CallSite> = counts
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(source, _)| source)
        .collect();
    if repeated.is_empty() {
        return Ok(());
    }

    // A site that is already assigned to a variable somewhere in the body has
    // a name the rest of the function already uses; binding to that same name
    // keeps the two consistent instead of introducing a synonym.
    let mut preferred: BTreeMap<CallSite, crate::symbol::SymbolId> = BTreeMap::new();
    for stmt in &func.body {
        collect_assignment_names(
            stmt,
            &repeated,
            &target_is_authorized,
            &mut preferred,
        );
    }
    if let Some(site) = repeated
        .iter()
        .copied()
        .find(|site| !preferred.contains_key(site))
    {
        return Err(SingleEvaluationError::MissingAssignmentTarget { site });
    }

    let mut bound: BTreeMap<CallSite, crate::symbol::SymbolId> = BTreeMap::new();
    let body = std::mem::take(&mut func.body);
    func.body = rewrite_block(
        body,
        &repeated,
        &preferred,
        &target_is_authorized,
        &mut bound,
    );

    // Binding a site evaluates it at the binding, so a bare statement for the
    // same site evaluates it twice. The fold emits one because at that point
    // nothing owned the result, which is what this pass has just changed.
    drop_bare_statements_for_bound_sites(&mut func.body, &bound);
    Ok(())
}

/// Remove a bare evaluation of a call site this pass has bound to a name.
fn drop_bare_statements_for_bound_sites(
    body: &mut Vec<CStmt>,
    bound: &BTreeMap<CallSite, crate::symbol::SymbolId>,
) {
    body.retain(|stmt| match stmt.unobserved() {
        CStmt::Expr(expr) => source_of(expr).is_none_or(|source| !bound.contains_key(&source)),
        _ => true,
    });
    for stmt in body.iter_mut() {
        for_each_child_block_mut(stmt, &mut |inner, _| {
            drop_bare_statements_for_bound_sites(inner, bound);
        });
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

fn collect_assignment_names(
    stmt: &CStmt,
    repeated: &[CallSite],
    target_is_authorized: &impl Fn(crate::symbol::SymbolId) -> bool,
    out: &mut BTreeMap<CallSite, crate::symbol::SymbolId>,
) {
    if let Some((left, right)) = assignment_parts(stmt)
        && let CExpr::Var(name) = left.unobserved()
        && target_is_authorized(*name)
        && let Some(source) = source_of(right)
        && repeated.contains(&source)
    {
        out.entry(source).or_insert(*name);
    }
    for_each_child_block(stmt, &mut |stmts| {
        for inner in stmts {
            collect_assignment_names(inner, repeated, target_is_authorized, out);
        }
    });
}

fn assignment_parts(stmt: &CStmt) -> Option<(&CExpr, &CExpr)> {
    let CStmt::Expr(expr) = stmt.unobserved() else {
        return None;
    };
    let CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    } = expr.unobserved()
    else {
        return None;
    };
    Some((left, right))
}

fn rewrite_block(
    stmts: Vec<CStmt>,
    repeated: &[CallSite],
    preferred: &BTreeMap<CallSite, crate::symbol::SymbolId>,
    target_is_authorized: &impl Fn(crate::symbol::SymbolId) -> bool,
    bound: &mut BTreeMap<CallSite, crate::symbol::SymbolId>,
) -> Vec<CStmt> {
    let mut out: Vec<CStmt> = Vec::with_capacity(stmts.len());
    for mut stmt in stmts {
        // An assignment whose right-hand side is the site itself is already the
        // binding this pass would otherwise have to invent, so it is adopted
        // rather than duplicated -- unless the site is bound already, in which
        // case the assignment is a second evaluation and becomes a copy.
        if let Some((left, right)) = assignment_parts(&stmt)
            && let CExpr::Var(name) = left.unobserved()
            && let Some(source) = source_of(right)
            && repeated.contains(&source)
            && target_is_authorized(*name)
            && !bound.contains_key(&source)
        {
            bound.insert(source, *name);
            out.push(stmt);
            continue;
        }

        // A second assignment of an already-bound site is a second evaluation
        // of it. Rewriting turns the right-hand side into the bound name, and
        // what is left says only that the variable still holds what it holds.
        let reassigns_bound_site = assignment_parts(&stmt).is_some_and(|(_, right)| {
            source_of(right).is_some_and(|source| bound.contains_key(&source))
        });

        let mut hoists: Vec<CStmt> = Vec::new();
        for_each_expr_mut(&mut stmt, &mut |expr| {
            rewrite_expr(expr, repeated, preferred, bound, &mut hoists)
        });
        out.extend(hoists);

        // The same reasoning covers a bare call whose site is already bound:
        // what is left mentions a value without using it, and says nothing.
        if reassigns_bound_site && is_self_assignment(&stmt) {
            continue;
        }
        if matches!(stmt.unobserved(), CStmt::Expr(expr) if matches!(expr.unobserved(), CExpr::Var(_)))
        {
            continue;
        }

        for_each_child_block_mut(&mut stmt, &mut |stmts, shares_scope| {
            let taken = std::mem::take(stmts);
            if shares_scope {
                *stmts = rewrite_block(
                    taken,
                    repeated,
                    preferred,
                    target_is_authorized,
                    bound,
                );
            } else {
                let mut nested = bound.clone();
                *stmts = rewrite_block(
                    taken,
                    repeated,
                    preferred,
                    target_is_authorized,
                    &mut nested,
                );
            }
        });

        out.push(stmt);
    }
    out
}

fn is_self_assignment(stmt: &CStmt) -> bool {
    let Some((left, right)) = assignment_parts(stmt) else {
        return false;
    };
    matches!(
        (left.unobserved(), right.unobserved()),
        (CExpr::Var(target), CExpr::Var(value)) if target == value
    )
}

fn rewrite_expr(
    expr: &mut CExpr,
    repeated: &[CallSite],
    preferred: &BTreeMap<CallSite, crate::symbol::SymbolId>,
    bound: &mut BTreeMap<CallSite, crate::symbol::SymbolId>,
    hoists: &mut Vec<CStmt>,
) {
    // Children first: a call nested in another call's arguments is evaluated
    // before the call that consumes it, and hoisting in that order keeps the
    // statements in the order the program runs them.
    for child in children_mut(expr) {
        rewrite_expr(child, repeated, preferred, bound, hoists);
    }

    let Some(source) = source_of(expr) else {
        return;
    };
    if !repeated.contains(&source) {
        return;
    }

    if let Some(name) = bound.get(&source) {
        *expr = crate::ast::carry_outer_expr_observations(expr, CExpr::Var(*name));
        return;
    }

    let name = preferred
        .get(&source)
        .copied()
        .expect("single-evaluation preflight requires an authorized assignment target");
    let call = std::mem::replace(expr, CExpr::Var(name));
    hoists.push(CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left: Box::new(CExpr::Var(name)),
        right: Box::new(call),
    }));
    bound.insert(source, name);
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
        CStmt::Observed { stmt, .. } => for_each_expr(stmt, f),
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
        CStmt::Observed { stmt, .. } => for_each_expr_mut(stmt, f),
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
        CStmt::Observed { stmt, .. } => for_each_child_block(stmt, f),
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
            CStmt::Observed { stmt, .. } => as_block(stmt, f, shares),
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
        CStmt::Observed { stmt, .. } => for_each_child_block_mut(stmt, f),
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
    use crate::ast::{
        CLocal, CParam, CType, RenderObservationOwner, strip_render_observations,
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
            func: Box::new(CExpr::Var(crate::symbol::declare(&symbols, &name.to_string()))),
            args: vec![CExpr::IntLit(16)],
            site: Some(site),
        }
    }

    fn assign(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, target: &str, value: CExpr) -> CStmt {
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left: Box::new(CExpr::Var(crate::symbol::declare(&symbols, &target.to_string()))),
            right: Box::new(value),
        })
    }

    /// A function that owns the table its body declared into. Cloning keeps the
    /// table's identity, so the identifiers in the body still resolve.
    fn function_from(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        body: Vec<CStmt>,
    ) -> CFunction {
        CFunction {
            name: "f".to_string(),
            ret_type: CType::Int(32),
            params: Vec::<CParam>::new(),
            locals: Vec::<CLocal>::new(),
            body,
            params_known: true,
            symbols: std::rc::Rc::new(std::cell::RefCell::new(symbols.borrow().clone())),
        }
    }

    fn bind_with_targets(
        func: &mut CFunction,
        target_names: &[&str],
    ) -> Result<(), SingleEvaluationError> {
        let targets = {
            let symbols = func.symbols.borrow();
            target_names
                .iter()
                .map(|name| symbols.by_name(name).expect("authorized test target"))
                .collect::<Vec<_>>()
        };
        bind_each_call_site_once_with(func, |symbol| targets.contains(&symbol))
    }

    #[test]
    fn a_second_assignment_of_the_same_site_becomes_a_copy() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "x0_3", call(&symbols, "fcn.1000", (0x1000, 0))),
            assign(&symbols, "x0_4", call(&symbols, "fcn.1000", (0x1000, 0))),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "x0_3"))),
        ]);

        bind_with_targets(&mut func, &["x0_3", "x0_4"]).expect("authorized targets");

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "x0_3", call(&symbols, "fcn.1000", (0x1000, 0))),
                assign(&symbols, "x0_4", crate::symbol::var_ref(&symbols, "x0_3")),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "x0_3"))),
            ]
        );
    }

    #[test]
    fn reassigning_the_same_target_leaves_nothing_to_say() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "owned", call(&symbols, "fcn.1000", (0x1000, 0))),
            assign(&symbols, "owned", call(&symbols, "fcn.1000", (0x1000, 0))),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
        ]);

        bind_with_targets(&mut func, &["owned"]).expect("authorized target");

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "owned", call(&symbols, "fcn.1000", (0x1000, 0))),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
            ]
        );
    }

    #[test]
    fn a_site_nested_in_an_argument_is_bound_before_the_statement() {
        let symbols = test_table();
        let outer = CExpr::Call {
            func: Box::new(crate::symbol::var_ref(&symbols, "use")),
            args: vec![call(&symbols, "fcn.1000", (0x1000, 0))],
            site: Some((0x2000, 0)),
        };
        let mut func = function_from(&symbols, vec![
            CStmt::Expr(outer),
            assign(&symbols, "owned", call(&symbols, "fcn.1000", (0x1000, 0))),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
        ]);

        bind_with_targets(&mut func, &["owned"]).expect("authorized target");

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "owned", call(&symbols, "fcn.1000", (0x1000, 0))),
                CStmt::Expr(CExpr::Call {
                    func: Box::new(crate::symbol::var_ref(&symbols, "use")),
                    args: vec![crate::symbol::var_ref(&symbols, "owned")],
                    site: Some((0x2000, 0)),
                }),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
            ]
        );
    }

    #[test]
    fn a_repeated_site_without_an_authorized_target_is_refused_transactionally() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            CStmt::Expr(call(&symbols, "fcn.1000", (0x1000, 0))),
            CStmt::Return(Some(call(&symbols, "fcn.1000", (0x1000, 0)))),
        ]);
        let before = func.body.clone();

        let refusal = bind_with_targets(&mut func, &[]);

        assert_eq!(
            refusal,
            Err(SingleEvaluationError::MissingAssignmentTarget {
                site: (0x1000, 0)
            })
        );
        assert_eq!(func.body, before);
        assert!(func.locals.is_empty(), "the pass must never mint a local");
    }

    #[test]
    fn sibling_branches_do_not_share_a_binding() {
        let symbols = test_table();
        let arm = |target: &str| {
            Box::new(CStmt::Block(vec![
                assign(
                    &symbols,
                    target,
                    call(&symbols, "fcn.1000", (0x1000, 0)),
                ),
                CStmt::Return(Some(CExpr::Var(crate::symbol::declare(&symbols, &target.to_string())))),
            ]))
        };
        let mut func = function_from(&symbols, vec![CStmt::If {
            cond: crate::symbol::var_ref(&symbols, "c"),
            then_body: arm("a"),
            else_body: Some(arm("b")),
        }]);
        let before = func.body.clone();

        bind_with_targets(&mut func, &["a", "b"]).expect("authorized branch targets");

        assert_eq!(func.body, before);
    }

    #[test]
    fn two_sites_that_render_alike_are_left_alone() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "a", call(&symbols, "fcn.1000", (0x1000, 0))),
            assign(&symbols, "b", call(&symbols, "fcn.1000", (0x2000, 0))),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "b"))),
        ]);
        let before = func.body.clone();

        bind_with_targets(&mut func, &["a", "b"]).expect("authorized targets");

        assert_eq!(func.body, before);
    }

    #[test]
    fn a_site_rendered_once_is_untouched() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "a", call(&symbols, "fcn.1000", (0x1000, 0))),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "a"))),
        ]);
        let before = func.body.clone();

        bind_with_targets(&mut func, &["a"]).expect("authorized target");

        assert_eq!(func.body, before);
        assert!(func.locals.is_empty());
    }

    #[test]
    fn observations_follow_rewritten_occurrences_and_deleted_ones_disappear() {
        let symbols = test_table();
        let mut observations = RenderObservationOwner::new();
        let (dropped, dropped_stmt) = observations
            .observe_stmt(CStmt::Expr(call(&symbols, "fcn.1000", (0x1000, 0))))
            .unwrap();
        let (surviving, surviving_expr) = observations
            .observe_expr(call(&symbols, "fcn.1000", (0x1000, 0)))
            .unwrap();
        let mut func = function_from(
            &symbols,
            vec![
                dropped_stmt,
                CStmt::Return(Some(surviving_expr)),
                assign(&symbols, "owned", call(&symbols, "fcn.1000", (0x1000, 0))),
            ],
        );

        bind_with_targets(&mut func, &["owned"]).expect("authorized target");
        let reachable = strip_render_observations(&mut func, observations.expected_count())
            .expect("single-evaluation rewriting must preserve unique observation IDs");

        assert_eq!(reachable.ids().collect::<Vec<_>>(), vec![surviving]);
        assert!(!reachable.contains(dropped));
    }
}
