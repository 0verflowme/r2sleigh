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
//! the first occurrence of a multiply-rendered call site becomes its binding
//! and every later occurrence becomes a mention of the bound name. Sites that
//! appear once are left exactly as they are.
//!
//! Sibling branches do not share bindings. A name bound in one arm of an `if`
//! is neither in scope nor in effect in the other, so each arm starts from the
//! set of bindings that reached the branch, and a loop body starts afresh on
//! the same reasoning: what the previous iteration bound is not what this
//! iteration computes.

use std::collections::BTreeMap;

use crate::ast::{BinaryOp, CExpr, CFunction, CStmt, CType};

/// A call site, identified by the address of the call and its index there.
type Source = (u64, usize);

/// Resolves a rendered call expression back to the site it came from.
///
/// Two distinct sites can render identically -- a program may well call
/// `malloc(len + 1)` twice -- and in that case the rendering carries no
/// evidence of which site it is. Such expressions are reported as unresolved
/// rather than guessed at, because merging two real calls into one would
/// delete an event the program performs.
struct CallIndex<'a> {
    entries: Vec<(&'a CExpr, Source)>,
}

impl<'a> CallIndex<'a> {
    fn new(call_exprs: &'a BTreeMap<Source, CExpr>) -> Self {
        Self {
            entries: call_exprs
                .iter()
                .filter(|(_, expr)| matches!(expr.unobserved(), CExpr::Call { .. }))
                .map(|(source, expr)| (expr, *source))
                .collect(),
        }
    }

    fn source_of(&self, expr: &CExpr) -> Option<Source> {
        let semantic_expr = expr.unobserved();
        // A call that knows its site says which site it is. Comparing shapes
        // only works while every layer builds the same expression for a call,
        // and they do not: the analysis layer and the fold each build their own.
        if let CExpr::Call {
            site: Some(site), ..
        } = semantic_expr
        {
            return Some(*site);
        }
        if !matches!(semantic_expr, CExpr::Call { .. }) {
            return None;
        }
        let mut found = None;
        for (candidate, source) in &self.entries {
            if candidate.transparently_eq(expr) {
                if found.is_some() {
                    return None;
                }
                found = Some(*source);
            }
        }
        found
    }
}

/// Give every call site in `func` exactly one evaluation.
pub(crate) fn bind_each_call_site_once(func: &mut CFunction, call_exprs: &BTreeMap<Source, CExpr>) {
    let index = CallIndex::new(call_exprs);
    if index.entries.is_empty() {
        return;
    }

    let mut counts: BTreeMap<Source, usize> = BTreeMap::new();
    for stmt in &func.body {
        count_in_stmt(stmt, &index, &mut counts);
    }
    let repeated: Vec<Source> = counts
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(source, _)| source)
        .collect();
    if repeated.is_empty() {
        return;
    }

    // A site that is already assigned to a variable somewhere in the body has
    // a name the rest of the function already uses; binding to that same name
    // keeps the two consistent instead of introducing a synonym.
    let mut preferred: BTreeMap<Source, crate::symbol::SymbolId> = BTreeMap::new();
    for stmt in &func.body {
        collect_assignment_names(stmt, &index, &repeated, &mut preferred);
    }

    let mut introduced: Vec<crate::symbol::SymbolId> = Vec::new();
    let mut bound: BTreeMap<Source, crate::symbol::SymbolId> = BTreeMap::new();
    let body = std::mem::take(&mut func.body);
    let mut symbols = func.symbols.borrow_mut();
    func.body = rewrite_block(
        body,
        &index,
        &repeated,
        &preferred,
        &mut bound,
        &mut introduced,
        &mut symbols,
    );
    drop(symbols);

    // Binding a site evaluates it at the binding, so a bare statement for the
    // same site evaluates it twice. The fold emits one because at that point
    // nothing owned the result, which is what this pass has just changed.
    drop_bare_statements_for_bound_sites(&mut func.body, &index, &bound);

    for name in introduced {
        if !func.locals.iter().any(|local| local.name == name)
            && !func.params.iter().any(|param| param.name == name)
        {
            func.locals.push(crate::ast::CLocal {
                ty: CType::UInt(64),
                name,
                stack_offset: None,
            });
        }
    }
}

/// Remove a bare evaluation of a call site this pass has bound to a name.
fn drop_bare_statements_for_bound_sites(
    body: &mut Vec<CStmt>,
    index: &CallIndex<'_>,
    bound: &BTreeMap<Source, crate::symbol::SymbolId>,
) {
    body.retain(|stmt| match stmt.unobserved() {
        CStmt::Expr(expr) => index
            .source_of(expr)
            .is_none_or(|source| !bound.contains_key(&source)),
        _ => true,
    });
    for stmt in body.iter_mut() {
        for_each_child_block_mut(stmt, &mut |inner, _| {
            drop_bare_statements_for_bound_sites(inner, index, bound);
        });
    }
}

fn count_in_stmt(stmt: &CStmt, index: &CallIndex<'_>, counts: &mut BTreeMap<Source, usize>) {
    for_each_expr(stmt, &mut |expr| count_in_expr(expr, index, counts));
    for_each_child_block(stmt, &mut |stmts| {
        for inner in stmts {
            count_in_stmt(inner, index, counts);
        }
    });
}

fn count_in_expr(expr: &CExpr, index: &CallIndex<'_>, counts: &mut BTreeMap<Source, usize>) {
    expr.visit(&mut |node| {
        if let Some(source) = index.source_of(node) {
            *counts.entry(source).or_insert(0) += 1;
        }
    });
}

fn collect_assignment_names(
    stmt: &CStmt,
    index: &CallIndex<'_>,
    repeated: &[Source],
    out: &mut BTreeMap<Source, crate::symbol::SymbolId>,
) {
    if let Some((left, right)) = assignment_parts(stmt)
        && let CExpr::Var(name) = left.unobserved()
        && let Some(source) = index.source_of(right)
        && repeated.contains(&source)
    {
        out.entry(source).or_insert(*name);
    }
    for_each_child_block(stmt, &mut |stmts| {
        for inner in stmts {
            collect_assignment_names(inner, index, repeated, out);
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
    index: &CallIndex<'_>,
    repeated: &[Source],
    preferred: &BTreeMap<Source, crate::symbol::SymbolId>,
    bound: &mut BTreeMap<Source, crate::symbol::SymbolId>,
    introduced: &mut Vec<crate::symbol::SymbolId>,
    symbols: &mut crate::symbol::SymbolTable,
) -> Vec<CStmt> {
    let mut out: Vec<CStmt> = Vec::with_capacity(stmts.len());
    for mut stmt in stmts {
        // An assignment whose right-hand side is the site itself is already the
        // binding this pass would otherwise have to invent, so it is adopted
        // rather than duplicated -- unless the site is bound already, in which
        // case the assignment is a second evaluation and becomes a copy.
        if let Some((left, right)) = assignment_parts(&stmt)
            && let CExpr::Var(name) = left.unobserved()
            && let Some(source) = index.source_of(right)
            && repeated.contains(&source)
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
            index
                .source_of(right)
                .is_some_and(|source| bound.contains_key(&source))
        });

        let mut hoists: Vec<CStmt> = Vec::new();
        for_each_expr_mut(&mut stmt, &mut |expr| {
            rewrite_expr(
                expr,
                index,
                repeated,
                preferred,
                bound,
                introduced,
                symbols,
                &mut hoists,
            )
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
                *stmts = rewrite_block(taken, index, repeated, preferred, bound, introduced, symbols);
            } else {
                let mut nested = bound.clone();
                *stmts =
                    rewrite_block(taken, index, repeated, preferred, &mut nested, introduced, symbols);
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
    index: &CallIndex<'_>,
    repeated: &[Source],
    preferred: &BTreeMap<Source, crate::symbol::SymbolId>,
    bound: &mut BTreeMap<Source, crate::symbol::SymbolId>,
    introduced: &mut Vec<crate::symbol::SymbolId>,
    symbols: &mut crate::symbol::SymbolTable,
    hoists: &mut Vec<CStmt>,
) {
    // Children first: a call nested in another call's arguments is evaluated
    // before the call that consumes it, and hoisting in that order keeps the
    // statements in the order the program runs them.
    for child in children_mut(expr) {
        rewrite_expr(child, index, repeated, preferred, bound, introduced, symbols, hoists);
    }

    let Some(source) = index.source_of(expr) else {
        return;
    };
    if !repeated.contains(&source) {
        return;
    }

    if let Some(name) = bound.get(&source) {
        *expr = crate::ast::carry_outer_expr_observations(expr, CExpr::Var(*name));
        return;
    }

    let name = preferred.get(&source).copied().unwrap_or_else(|| {
        let spelling = introduced_name_for(expr, introduced, symbols);
        let name = symbols.declare_or_reuse(&spelling);
        introduced.push(name);
        name
    });
    let call = std::mem::replace(expr, CExpr::Var(name.clone()));
    hoists.push(CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left: Box::new(CExpr::Var(name.clone())),
        right: Box::new(call),
    }));
    bound.insert(source, name);
}

/// A name for a site the body never assigned anywhere, derived from the callee
/// so the binding still says what it holds.
fn introduced_name_for(
    expr: &CExpr,
    introduced: &[crate::symbol::SymbolId],
    symbols: &crate::symbol::SymbolTable,
) -> String {
    let callee = match expr.unobserved() {
        CExpr::Call { func, .. } => match func.unobserved() {
            CExpr::Var(id) => {
                let name = symbols.name(*id);
                let tail = name.rsplit('.').next().unwrap_or(name);
                if tail.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') {
                    tail.to_string()
                } else {
                    name.replace(|c: char| !c.is_ascii_alphanumeric(), "_")
                }
            }
            _ => "call".to_string(),
        },
        _ => "call".to_string(),
    };
    // The table settles collisions when the name is declared, so this only has
    // to avoid re-proposing one this pass has already introduced.
    let base = format!("{callee}_result");
    let taken = |candidate: &str| {
        introduced
            .iter()
            .any(|name| symbols.name(*name) == candidate)
    };
    if !taken(&base) {
        return base;
    }
    let mut suffix = 2;
    loop {
        let candidate = format!("{base}_{suffix}");
        if !taken(&candidate) {
            return candidate;
        }
        suffix += 1;
    }
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

    fn call(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, name: &str) -> CExpr {
        CExpr::Call {
            func: Box::new(CExpr::Var(crate::symbol::declare(&symbols, &name.to_string()))),
            args: vec![CExpr::IntLit(16)],
            site: None,
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

    fn one_site(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>) -> BTreeMap<Source, CExpr> {
        BTreeMap::from([((0x1000, 0), call(symbols, "fcn.1000"))])
    }

    #[test]
    fn a_second_assignment_of_the_same_site_becomes_a_copy() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "x0_3", call(&symbols, "fcn.1000")),
            assign(&symbols, "x0_4", call(&symbols, "fcn.1000")),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "x0_3"))),
        ]);

        bind_each_call_site_once(&mut func, &one_site(&symbols));

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "x0_3", call(&symbols, "fcn.1000")),
                assign(&symbols, "x0_4", crate::symbol::var_ref(&symbols, "x0_3")),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "x0_3"))),
            ]
        );
    }

    #[test]
    fn reassigning_the_same_target_leaves_nothing_to_say() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "owned", call(&symbols, "fcn.1000")),
            assign(&symbols, "owned", call(&symbols, "fcn.1000")),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
        ]);

        bind_each_call_site_once(&mut func, &one_site(&symbols));

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "owned", call(&symbols, "fcn.1000")),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
            ]
        );
    }

    #[test]
    fn a_site_nested_in_an_argument_is_bound_before_the_statement() {
        let symbols = test_table();
        let outer = CExpr::Call {
            func: Box::new(crate::symbol::var_ref(&symbols, "use")),
            args: vec![call(&symbols, "fcn.1000")],
            site: None,
        };
        let mut func = function_from(&symbols, vec![
            CStmt::Expr(outer),
            assign(&symbols, "owned", call(&symbols, "fcn.1000")),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
        ]);

        bind_each_call_site_once(&mut func, &one_site(&symbols));

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "owned", call(&symbols, "fcn.1000")),
                CStmt::Expr(CExpr::Call {
                    func: Box::new(crate::symbol::var_ref(&symbols, "use")),
                    args: vec![crate::symbol::var_ref(&symbols, "owned")],
                    site: None,
                }),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "owned"))),
            ]
        );
    }

    #[test]
    fn a_site_the_body_never_names_gets_a_declared_binding() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            CStmt::Expr(call(&symbols, "fcn.1000")),
            CStmt::Return(Some(call(&symbols, "fcn.1000"))),
        ]);

        bind_each_call_site_once(&mut func, &one_site(&symbols));

        assert_eq!(
            func.body,
            vec![
                assign(&symbols, "fcn_1000_result", call(&symbols, "fcn.1000")),
                CStmt::Return(Some(crate::symbol::var_ref(&symbols, "fcn_1000_result"))),
            ]
        );
        assert_eq!(func.locals.len(), 1);
        assert_eq!(func.locals[0].name, crate::symbol::declare(&symbols, "fcn_1000_result"));
    }

    #[test]
    fn sibling_branches_do_not_share_a_binding() {
        let symbols = test_table();
        let arm = |target: &str| {
            Box::new(CStmt::Block(vec![
                assign(&symbols, target, call(&symbols, "fcn.1000")),
                CStmt::Return(Some(CExpr::Var(crate::symbol::declare(&symbols, &target.to_string())))),
            ]))
        };
        let mut func = function_from(&symbols, vec![CStmt::If {
            cond: crate::symbol::var_ref(&symbols, "c"),
            then_body: arm("a"),
            else_body: Some(arm("b")),
        }]);
        let before = func.body.clone();

        bind_each_call_site_once(&mut func, &one_site(&symbols));

        assert_eq!(func.body, before);
    }

    #[test]
    fn two_sites_that_render_alike_are_left_alone() {
        let symbols = test_table();
        let sites = BTreeMap::from([
            ((0x1000, 0), call(&symbols, "fcn.1000")),
            ((0x2000, 0), call(&symbols, "fcn.1000")),
        ]);
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "a", call(&symbols, "fcn.1000")),
            assign(&symbols, "b", call(&symbols, "fcn.1000")),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "b"))),
        ]);
        let before = func.body.clone();

        bind_each_call_site_once(&mut func, &sites);

        assert_eq!(func.body, before);
    }

    #[test]
    fn a_site_rendered_once_is_untouched() {
        let symbols = test_table();
        let mut func = function_from(&symbols, vec![
            assign(&symbols, "a", call(&symbols, "fcn.1000")),
            CStmt::Return(Some(crate::symbol::var_ref(&symbols, "a"))),
        ]);
        let before = func.body.clone();

        bind_each_call_site_once(&mut func, &one_site(&symbols));

        assert_eq!(func.body, before);
        assert!(func.locals.is_empty());
    }

    #[test]
    fn observations_follow_rewritten_occurrences_and_deleted_ones_disappear() {
        let symbols = test_table();
        let mut observations = RenderObservationOwner::new();
        let (dropped, dropped_stmt) = observations
            .observe_stmt(CStmt::Expr(call(&symbols, "fcn.1000")))
            .unwrap();
        let (surviving, surviving_expr) = observations
            .observe_expr(call(&symbols, "fcn.1000"))
            .unwrap();
        let mut func = function_from(
            &symbols,
            vec![
                dropped_stmt,
                CStmt::Return(Some(surviving_expr)),
            ],
        );

        bind_each_call_site_once(&mut func, &one_site(&symbols));
        let reachable = strip_render_observations(&mut func, observations.expected_count())
            .expect("single-evaluation rewriting must preserve unique observation IDs");

        assert_eq!(reachable.ids().collect::<Vec<_>>(), vec![surviving]);
        assert!(!reachable.contains(dropped));
    }
}
