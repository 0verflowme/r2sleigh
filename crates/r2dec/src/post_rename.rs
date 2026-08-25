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

            // The group is keyed by the normalised base, so the target has to be
            // that base and not each name's own. Two spellings of one value
            // differing only in case sit in one group, and renaming each to its
            // own base produced two different version-less names: `x10_2` became
            // `x10` and `X10_2` became `X10`. The definition followed the first,
            // so the second named nothing. `follow_renames` then declines the
            // second rather than merging two symbols, which is what keeps its
            // version and keeps it matched to whatever defines it.
            for full_name in names {
                if split_ssa_suffix(&full_name).is_some() {
                    rename_map.insert(full_name.clone(), base_norm.clone());
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

    // A raw SSA name is not a rendered identifier, and dropping its version
    // turns a value into a storage: `tmp:4700_7` becomes `tmp:4700`, which names
    // the temporary rather than the seventh value in it, and is later sanitised
    // to `tmp_4700`. The same value's other symbol keeps `t4700_7`, so the two
    // spellings diverge and the condition names something no statement assigns.
    // This pass exists to make rendered names readable; a name it cannot spell
    // is not one of them.
    if name.contains(':') {
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
    use crate::ast::{
        BinaryOp, CExpr, CLocal, CParam, CStmt, CType, RenderObservationOwner, SwitchCase,
        strip_render_observations,
    };
    use crate::symbol::{SymbolTable, var_ref};
    use std::cell::RefCell;

    /// The names one rendered function declares.
    fn table() -> RefCell<SymbolTable> {
        RefCell::new(SymbolTable::new())
    }

    fn mk_assign(symbols: &RefCell<SymbolTable>, lhs: &str, rhs: CExpr) -> CStmt {
        CStmt::Expr(CExpr::assign(var_ref(symbols, lhs), rhs))
    }

    fn mk_func(symbols: RefCell<SymbolTable>, body: Vec<CStmt>) -> CFunction {
        CFunction {
            symbols: std::rc::Rc::new(symbols),
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

    /// Renaming moves a spelling in the table, so that is where it is checked.
    fn spells(func: &CFunction, name: &str) -> bool {
        func.symbols.borrow().by_name(name).is_some()
    }

    #[test]
    fn removes_singleton_suffix() {
        let symbols = table();
        let body = vec![
            mk_assign(&symbols, "eax_3", CExpr::IntLit(1)),
            CStmt::Return(Some(var_ref(&symbols, "eax_3"))),
        ];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        assert!(spells(&func, "eax"));
        assert!(!spells(&func, "eax_3"));
    }

    #[test]
    fn renaming_keeps_observation_wrapped_occurrences_reachable() {
        let symbols = table();
        let mut observations = RenderObservationOwner::new();
        let mut func = mk_func(symbols, Vec::new());
        let value = func.symbols.borrow_mut().declare_or_reuse("eax_3");
        let (expr_id, expr) = observations.observe_expr(CExpr::Var(value)).unwrap();
        let (stmt_id, stmt) = observations
            .observe_stmt(CStmt::Return(Some(expr)))
            .unwrap();
        func.body = vec![stmt];

        rewrite(&mut func);
        let reachable = strip_render_observations(&mut func, observations.expected_count())
            .expect("renaming must preserve unique observation IDs");

        assert_eq!(reachable.ids().collect::<Vec<_>>(), vec![expr_id, stmt_id]);
        assert!(spells(&func, "eax"));
    }

    #[test]
    fn keeps_conflicting_versions() {
        let symbols = table();
        let body = vec![
            mk_assign(&symbols, "eax_1", CExpr::IntLit(1)),
            mk_assign(
                &symbols,
                "eax_2",
                CExpr::binary(BinaryOp::Add, var_ref(&symbols, "eax_1"), CExpr::IntLit(1)),
            ),
            CStmt::Return(Some(var_ref(&symbols, "eax_2"))),
        ];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        assert!(spells(&func, "eax_1"));
        assert!(spells(&func, "eax_2"));
    }

    #[test]
    fn keeps_suffix_with_unsuffixed_conflict() {
        let symbols = table();
        let body = vec![
            mk_assign(&symbols, "eax", CExpr::IntLit(1)),
            mk_assign(&symbols, "eax_3", CExpr::IntLit(2)),
        ];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        assert!(spells(&func, "eax_3"));
    }

    #[test]
    fn conflict_is_case_insensitive() {
        let symbols = table();
        let body = vec![
            mk_assign(&symbols, "RAX_0", CExpr::IntLit(1)),
            mk_assign(&symbols, "rax_2", CExpr::IntLit(2)),
        ];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        assert!(spells(&func, "RAX_0"));
        assert!(spells(&func, "rax_2"));
    }

    #[test]
    fn rewrites_decl_params_locals_consistently() {
        let symbols = table();
        let input = var_ref(&symbols, "input_1");
        let state = var_ref(&symbols, "state_2");
        let CExpr::Var(input_id) = input else {
            unreachable!()
        };
        let CExpr::Var(state_id) = state else {
            unreachable!()
        };
        let body = vec![
            CStmt::Decl {
                ty: CType::Int(32),
                name: {
                    let CExpr::Var(id) = var_ref(&symbols, "tmp_5") else {
                        unreachable!()
                    };
                    id
                },
                init: Some(CExpr::IntLit(0)),
            },
            mk_assign(&symbols, "tmp_5", CExpr::IntLit(1)),
        ];
        let mut func = mk_func(symbols, body);
        func.params.push(CParam {
            ty: CType::Int(32),
            name: input_id,
        });
        func.locals.push(CLocal {
            ty: CType::Int(32),
            name: state_id,
            stack_offset: None,
        });
        rewrite(&mut func);
        // A parameter and a local are references too, so one rename moves both.
        assert_eq!(func.symbols.borrow().name(func.params[0].name), "input");
        assert_eq!(func.symbols.borrow().name(func.locals[0].name), "state");
        assert!(spells(&func, "tmp"));
        assert!(!spells(&func, "tmp_5"));
        assert!(!spells(&func, "state_2"));
        assert!(!spells(&func, "input_1"));
    }

    #[test]
    fn excludes_function_like_dotted_names() {
        let symbols = table();
        let body = vec![mk_assign(&symbols, "fcn.00401234_2", CExpr::IntLit(1))];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        assert!(spells(&func, "fcn.00401234_2"));
    }

    #[test]
    fn traverses_switch_values_and_bodies() {
        let symbols = table();
        let body = vec![CStmt::Switch {
            expr: var_ref(&symbols, "eax_3"),
            cases: vec![SwitchCase {
                value: CExpr::IntLit(0),
                body: vec![mk_assign(&symbols, "eax_3", CExpr::IntLit(1))],
            }],
            default: None,
        }];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        assert!(spells(&func, "eax"));
        assert!(!spells(&func, "eax_3"));
    }

    #[test]
    fn does_not_rewrite_comments() {
        let symbols = table();
        let body = vec![CStmt::Comment("eax_3 should stay in comment".to_string())];
        let mut func = mk_func(symbols, body);
        rewrite(&mut func);
        match &func.body[0] {
            CStmt::Comment(text) => assert_eq!(text, "eax_3 should stay in comment"),
            other => panic!("expected comment, got {other:?}"),
        }
    }
}
