use std::collections::{HashMap, HashSet};

use crate::ast::{CExpr, CFunction, CStmt};

/// Rewrite ambiguous SSA-style suffixes after structuring/folding.
///
/// This pass runs over the complete rendered function (params, locals, body),
/// so declarations and references stay consistent.
pub(crate) fn rewrite_function_identifiers(
    func: &mut CFunction,
    known_function_names: &HashSet<String>,
) {
    let mut collector = NameCollector::new(known_function_names);
    collector.collect_function(func);

    let rename_map = collector.build_rename_map();
    if rename_map.is_empty() {
        return;
    }

    rewrite_function(func, &rename_map);
}

/// Rewrite an explicit set of names, for a caller that already knows the map.
pub(crate) fn rewrite_function_names(func: &mut CFunction, rename_map: &HashMap<String, String>) {
    if rename_map.is_empty() {
        return;
    }
    rewrite_function(func, rename_map);
}

struct NameCollector<'a> {
    known_function_names: &'a HashSet<String>,
    unsuffixed_bases: HashSet<String>,
    versions_by_base: HashMap<String, HashSet<String>>,
    names_by_base: HashMap<String, HashSet<String>>,
}

impl<'a> NameCollector<'a> {
    fn new(known_function_names: &'a HashSet<String>) -> Self {
        Self {
            known_function_names,
            unsuffixed_bases: HashSet::new(),
            versions_by_base: HashMap::new(),
            names_by_base: HashMap::new(),
        }
    }

    fn collect_function(&mut self, func: &CFunction) {
        for param in &func.params {
            self.collect_name(&param.name);
        }
        for local in &func.locals {
            self.collect_name(&local.name);
        }
        for stmt in &func.body {
            self.collect_stmt(stmt);
        }
    }

    fn collect_stmt(&mut self, stmt: &CStmt) {
        match stmt {
            CStmt::Empty
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_) => {}
            CStmt::Expr(expr) => self.collect_expr(expr),
            CStmt::Decl { name, init, .. } => {
                self.collect_name(name);
                if let Some(init_expr) = init {
                    self.collect_expr(init_expr);
                }
            }
            CStmt::Block(stmts) => {
                for s in stmts {
                    self.collect_stmt(s);
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.collect_expr(cond);
                self.collect_stmt(then_body);
                if let Some(other) = else_body {
                    self.collect_stmt(other);
                }
            }
            CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
                self.collect_expr(cond);
                self.collect_stmt(body);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init_stmt) = init {
                    self.collect_stmt(init_stmt);
                }
                if let Some(cond_expr) = cond {
                    self.collect_expr(cond_expr);
                }
                if let Some(update_expr) = update {
                    self.collect_expr(update_expr);
                }
                self.collect_stmt(body);
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                self.collect_expr(expr);
                for case in cases {
                    self.collect_expr(&case.value);
                    for stmt in &case.body {
                        self.collect_stmt(stmt);
                    }
                }
                if let Some(default_stmts) = default {
                    for stmt in default_stmts {
                        self.collect_stmt(stmt);
                    }
                }
            }
            CStmt::Return(Some(expr)) => self.collect_expr(expr),
            CStmt::Return(None) => {}
        }
    }

    fn collect_expr(&mut self, expr: &CExpr) {
        match expr {
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::External { .. }
            | CExpr::SizeofType(_) => {}
            CExpr::Var(name) => self.collect_name(name),
            CExpr::Unary { operand, .. }
            | CExpr::Cast { expr: operand, .. }
            | CExpr::Paren(operand)
            | CExpr::Deref(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Sizeof(operand) => self.collect_expr(operand),
            CExpr::Binary { left, right, .. } => {
                self.collect_expr(left);
                self.collect_expr(right);
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.collect_expr(cond);
                self.collect_expr(then_expr);
                self.collect_expr(else_expr);
            }
            CExpr::Call { func, args } => {
                self.collect_expr(func);
                for arg in args {
                    self.collect_expr(arg);
                }
            }
            CExpr::Subscript { base, index } => {
                self.collect_expr(base);
                self.collect_expr(index);
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                self.collect_expr(base);
            }
            CExpr::Comma(items) => {
                for item in items {
                    self.collect_expr(item);
                }
            }
        }
    }

    fn collect_name(&mut self, name: &str) {
        if should_exclude_name(name, self.known_function_names) {
            return;
        }

        if let Some((base, suffix)) = split_ssa_suffix(name) {
            let base_norm = base.to_ascii_lowercase();
            self.names_by_base
                .entry(base_norm.clone())
                .or_default()
                .insert(name.to_string());
            self.versions_by_base
                .entry(base_norm)
                .or_default()
                .insert(suffix.to_string());
            return;
        }

        self.unsuffixed_bases.insert(name.to_ascii_lowercase());
    }

    fn build_rename_map(self) -> HashMap<String, String> {
        let mut rename_map = HashMap::new();

        for (base_norm, names) in self.names_by_base {
            let version_count = self
                .versions_by_base
                .get(&base_norm)
                .map_or(0, HashSet::len);
            let has_unsuffixed = self.unsuffixed_bases.contains(&base_norm);

            if version_count + usize::from(has_unsuffixed) != 1 {
                continue;
            }

            for full_name in names {
                if let Some((base, _)) = split_ssa_suffix(&full_name) {
                    rename_map.insert(full_name.clone(), base.to_string());
                }
            }
        }

        rename_map
    }
}

fn should_exclude_name(name: &str, known_function_names: &HashSet<String>) -> bool {
    let lower = name.to_ascii_lowercase();

    if known_function_names.contains(&lower) {
        return true;
    }

    // Semantic names should not be treated as SSA suffix candidates.
    if lower.starts_with("local_")
        || lower.starts_with("arg")
        || lower.starts_with("field_")
        || lower.starts_with("var_")
        || lower.starts_with("sub_")
        || lower.starts_with("str.")
        || lower.starts_with("0x")
        || lower.contains('.')
    {
        return true;
    }

    false
}

fn split_ssa_suffix(name: &str) -> Option<(&str, &str)> {
    let (base, suffix) = name.rsplit_once('_')?;
    if base.is_empty() || suffix.is_empty() {
        return None;
    }
    if suffix.chars().all(|ch| ch.is_ascii_digit()) {
        Some((base, suffix))
    } else {
        None
    }
}

fn rewrite_function(func: &mut CFunction, rename_map: &HashMap<String, String>) {
    for param in &mut func.params {
        rewrite_name(&mut param.name, rename_map);
    }
    for local in &mut func.locals {
        rewrite_name(&mut local.name, rename_map);
    }
    for stmt in &mut func.body {
        rewrite_stmt(stmt, rename_map);
    }
}

fn rewrite_stmt(stmt: &mut CStmt, rename_map: &HashMap<String, String>) {
    match stmt {
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
        CStmt::Expr(expr) => rewrite_expr(expr, rename_map),
        CStmt::Decl { name, init, .. } => {
            rewrite_name(name, rename_map);
            if let Some(init_expr) = init {
                rewrite_expr(init_expr, rename_map);
            }
        }
        CStmt::Block(stmts) => {
            for s in stmts {
                rewrite_stmt(s, rename_map);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rewrite_expr(cond, rename_map);
            rewrite_stmt(then_body, rename_map);
            if let Some(other) = else_body {
                rewrite_stmt(other, rename_map);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            rewrite_expr(cond, rename_map);
            rewrite_stmt(body, rename_map);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init_stmt) = init {
                rewrite_stmt(init_stmt, rename_map);
            }
            if let Some(cond_expr) = cond {
                rewrite_expr(cond_expr, rename_map);
            }
            if let Some(update_expr) = update {
                rewrite_expr(update_expr, rename_map);
            }
            rewrite_stmt(body, rename_map);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            rewrite_expr(expr, rename_map);
            for case in cases {
                rewrite_expr(&mut case.value, rename_map);
                for stmt in &mut case.body {
                    rewrite_stmt(stmt, rename_map);
                }
            }
            if let Some(default_stmts) = default {
                for stmt in default_stmts {
                    rewrite_stmt(stmt, rename_map);
                }
            }
        }
        CStmt::Return(Some(expr)) => rewrite_expr(expr, rename_map),
        CStmt::Return(None) => {}
    }
}

fn rewrite_expr(expr: &mut CExpr, rename_map: &HashMap<String, String>) {
    match expr {
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
        CExpr::Var(name) => rewrite_name(name, rename_map),
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Paren(operand)
        | CExpr::Deref(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Sizeof(operand) => rewrite_expr(operand, rename_map),
        CExpr::Binary { left, right, .. } => {
            rewrite_expr(left, rename_map);
            rewrite_expr(right, rename_map);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            rewrite_expr(cond, rename_map);
            rewrite_expr(then_expr, rename_map);
            rewrite_expr(else_expr, rename_map);
        }
        CExpr::Call { func, args } => {
            rewrite_expr(func, rename_map);
            for arg in args {
                rewrite_expr(arg, rename_map);
            }
        }
        CExpr::Subscript { base, index } => {
            rewrite_expr(base, rename_map);
            rewrite_expr(index, rename_map);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            rewrite_expr(base, rename_map);
        }
        CExpr::Comma(items) => {
            for item in items {
                rewrite_expr(item, rename_map);
            }
        }
    }
}

fn rewrite_name(name: &mut String, rename_map: &HashMap<String, String>) {
    if let Some(new_name) = rename_map.get(name) {
        *name = new_name.clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, CLocal, CParam, CType, SwitchCase};

    fn mk_assign(lhs: &str, rhs: CExpr) -> CStmt {
        CStmt::Expr(CExpr::assign(CExpr::Var(lhs.to_string()), rhs))
    }

    fn mk_func(body: Vec<CStmt>) -> CFunction {
        CFunction {
            name: "demo".to_string(),
            ret_type: CType::Int(32),
            params: Vec::new(),
            locals: Vec::new(),
            body,
            params_known: true,
        }
    }

    fn rewrite(func: &mut CFunction) {
        rewrite_function_identifiers(func, &HashSet::new());
    }

    #[test]
    fn removes_singleton_suffix() {
        let mut func = mk_func(vec![
            mk_assign("eax_3", CExpr::IntLit(1)),
            CStmt::Return(Some(CExpr::Var("eax_3".to_string()))),
        ]);
        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("eax"));
        assert!(!rendered.contains("eax_3"));
    }

    #[test]
    fn keeps_conflicting_versions() {
        let mut func = mk_func(vec![
            mk_assign("eax_1", CExpr::IntLit(1)),
            mk_assign(
                "eax_2",
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("eax_1".to_string()),
                    CExpr::IntLit(1),
                ),
            ),
            CStmt::Return(Some(CExpr::Var("eax_2".to_string()))),
        ]);
        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("eax_1"));
        assert!(rendered.contains("eax_2"));
    }

    #[test]
    fn keeps_suffix_with_unsuffixed_conflict() {
        let mut func = mk_func(vec![
            mk_assign("eax", CExpr::IntLit(0)),
            mk_assign("eax_3", CExpr::IntLit(1)),
            CStmt::Return(Some(CExpr::Var("eax_3".to_string()))),
        ]);
        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("eax_3"));
    }

    #[test]
    fn conflict_is_case_insensitive() {
        let mut func = mk_func(vec![
            mk_assign("RAX_0", CExpr::IntLit(0)),
            mk_assign("rax_2", CExpr::IntLit(1)),
        ]);
        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("RAX_0"));
        assert!(rendered.contains("rax_2"));
    }

    #[test]
    fn rewrites_decl_params_locals_consistently() {
        let mut func = mk_func(vec![
            CStmt::Decl {
                ty: CType::Int(32),
                name: "tmp_5".to_string(),
                init: Some(CExpr::Var("tmp_5".to_string())),
            },
            mk_assign("state_2", CExpr::Var("input_1".to_string())),
            CStmt::Return(Some(CExpr::Var("input_1".to_string()))),
        ]);
        func.params.push(CParam {
            ty: CType::Int(32),
            name: "input_1".to_string(),
        });
        func.locals.push(CLocal {
            ty: CType::Int(32),
            name: "state_2".to_string(),
            stack_offset: None,
        });

        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert_eq!(func.params[0].name, "input");
        assert_eq!(func.locals[0].name, "state");
        assert!(rendered.contains("tmp"));
        assert!(!rendered.contains("tmp_5"));
        assert!(!rendered.contains("state_2"));
        assert!(!rendered.contains("input_1"));
    }

    #[test]
    fn excludes_function_like_dotted_names() {
        let mut func = mk_func(vec![
            mk_assign("fcn.00401234_2", CExpr::IntLit(1)),
            CStmt::Return(Some(CExpr::Var("fcn.00401234_2".to_string()))),
        ]);
        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("fcn.00401234_2"));
    }

    #[test]
    fn traverses_switch_values_and_bodies() {
        let mut func = mk_func(vec![CStmt::Switch {
            expr: CExpr::Var("eax_3".to_string()),
            cases: vec![SwitchCase {
                value: CExpr::Var("eax_3".to_string()),
                body: vec![
                    mk_assign("eax_3", CExpr::IntLit(1)),
                    CStmt::Return(Some(CExpr::Var("eax_3".to_string()))),
                ],
            }],
            default: None,
        }]);
        rewrite(&mut func);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("eax"));
        assert!(!rendered.contains("eax_3"));
    }

    #[test]
    fn does_not_rewrite_comments() {
        let mut func = mk_func(vec![
            CStmt::Comment("eax_3 should stay in comment".to_string()),
            mk_assign("eax_3", CExpr::IntLit(1)),
        ]);
        rewrite(&mut func);
        match &func.body[0] {
            CStmt::Comment(text) => assert_eq!(text, "eax_3 should stay in comment"),
            _ => panic!("expected comment"),
        }
        let rendered = format!("{:?}", func.body[1]);
        assert!(rendered.contains("eax"));
        assert!(!rendered.contains("eax_3"));
    }

    #[test]
    fn excludes_known_function_names() {
        let mut func = mk_func(vec![
            mk_assign("helper_2", CExpr::IntLit(1)),
            CStmt::Return(Some(CExpr::Var("helper_2".to_string()))),
        ]);
        let mut known = HashSet::new();
        known.insert("helper_2".to_string());
        rewrite_function_identifiers(&mut func, &known);
        let rendered = format!("{:?}", func.body);
        assert!(rendered.contains("helper_2"));
    }
}
