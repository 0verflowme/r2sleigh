use std::collections::{HashMap, HashSet};

use crate::ast::CFunction;

/// Drop an SSA version suffix from any name that turned out not to need one.
///
/// This used to rewrite the whole rendered function -- parameters, locals, and
/// every mention in the body -- and its risk was that the three could fall out
/// of step. A reference is an identifier now, so there is one place a name is
/// written down and renaming is done there; every mention follows because every
/// mention was already pointing at it.
pub(crate) fn rewrite_function_identifiers(
    func: &mut CFunction,
    known_function_names: &HashSet<String>,
) {
    let mut collector = NameCollector::new(known_function_names);
    collector.collect_function(func);
    let rename_map = collector.build_rename_map();
    func.symbols.borrow_mut().follow_renames(&rename_map);
}

/// Apply a rename a caller already worked out.
pub(crate) struct NameCollector<'a> {
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

    /// Every name the function declares, read from the table that holds them.
    ///
    /// Walking the body for names is no longer necessary: a reference is an
    /// identifier now, so every name a body can mention is one the table already
    /// has, and the table is the shorter and more certain place to look.
    fn collect_function(&mut self, func: &CFunction) {
        for (_, symbol) in func.symbols.borrow().iter() {
            self.collect_name(&symbol.name);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, CLocal, CParam, CType, SwitchCase};

    fn mk_assign(lhs: &str, rhs: CExpr) -> CStmt {
        CStmt::Expr(CExpr::assign(CExpr::Var(lhs.to_string()), rhs))
    }

    fn mk_func(body: Vec<CStmt>) -> CFunction {
        CFunction {
            symbols: crate::symbol::SymbolTable::new(),
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
