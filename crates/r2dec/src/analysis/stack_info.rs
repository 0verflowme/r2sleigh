use std::collections::{HashMap, HashSet};

use r2ssa::SSAOp;

use super::{PassEnv, StackInfo, UseInfo, lower::LowerCtx, utils};
use crate::ast::CExpr;
use crate::fold::SSABlock;

#[derive(Debug, Default)]
pub(crate) struct StackScratch {
    pub(crate) info: StackInfo,
}

pub(crate) fn analyze(blocks: &[SSABlock], use_info: &UseInfo, env: &PassEnv<'_>) -> StackInfo {
    let mut scratch = StackScratch::default();

    analyze_stack_vars(&mut scratch, blocks, use_info, env);

    scratch.info
}

fn analyze_stack_vars(
    scratch: &mut StackScratch,
    blocks: &[SSABlock],
    use_info: &UseInfo,
    env: &PassEnv<'_>,
) {
    for block in blocks {
        for op in &block.ops {
            match op {
                SSAOp::Load { addr, .. } => {
                    if let Some(offset) = utils::extract_stack_offset_from_var(
                        addr,
                        &use_info.definitions,
                        env.fp_name,
                        env.sp_name,
                    ) {
                        get_or_create_stack_var(scratch, offset, env);
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    if let Some(offset) = utils::extract_stack_offset_from_var(
                        addr,
                        &use_info.definitions,
                        env.fp_name,
                        env.sp_name,
                    ) {
                        if let Some(arg_alias) = utils::arg_alias_for_store_source(
                            val,
                            &use_info.copy_sources,
                            &use_info.var_aliases,
                            env.param_register_aliases,
                        ) {
                            set_stack_arg_alias(scratch, offset, arg_alias, env);
                        }
                        get_or_create_stack_var(scratch, offset, env);
                    }
                }
                SSAOp::IntAdd { a, b, .. } => {
                    let a_lower = a.name.to_lowercase();
                    if (a_lower.contains(env.fp_name) || a_lower.contains(env.sp_name))
                        && let Some(offset) = utils::parse_const_offset(b)
                    {
                        get_or_create_stack_var(scratch, offset, env);
                    }
                }
                _ => {}
            }
        }
    }

    let mut merged_defs = use_info.definitions.clone();

    for block in blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } => {
                    let a_lower = a.name.to_lowercase();
                    if !(a_lower.contains(env.fp_name) || a_lower.contains(env.sp_name)) {
                        continue;
                    }
                    if let Some(offset) = utils::parse_const_offset(b)
                        && let Some(stack_var_name) = scratch.info.stack_vars.get(&offset).cloned()
                    {
                        let expr = CExpr::Var(format!("&{}", stack_var_name));
                        scratch
                            .info
                            .definition_overrides
                            .insert(dst.display_name(), expr.clone());
                        merged_defs.insert(dst.display_name(), expr);
                    }
                }
                SSAOp::Load { dst, addr, .. } => {
                    let preserve_indirect_load_shape = matches!(
                        use_info.semantic_values.get(&dst.display_name()),
                        Some(super::SemanticValue::Scalar(super::ScalarValue::Root(root)))
                            if root.var.size > dst.size
                    );
                    if preserve_indirect_load_shape {
                        continue;
                    }
                    let stack_var_name = stack_var_for_addr_var(
                        addr,
                        StackVarLookupInputs {
                            definitions: &merged_defs,
                            stack_vars: &scratch.info.stack_vars,
                            stack_arg_aliases: &scratch.info.stack_arg_aliases,
                            var_aliases: &use_info.var_aliases,
                            stack_slots: &use_info.stack_slots,
                            copy_sources: &use_info.copy_sources,
                            forwarded_values: &use_info.forwarded_values,
                            env,
                        },
                    );
                    let stack_slot = stack_slot_for_addr_var(
                        addr,
                        &merged_defs,
                        &use_info.stack_slots,
                        &use_info.copy_sources,
                        &use_info.forwarded_values,
                        env,
                    );
                    if let Some(expr) = forwarded_expr_for_value(
                        dst.display_name().as_str(),
                        &merged_defs,
                        use_info,
                        env,
                    ) {
                        let expr = normalize_scalar_stack_load_expr(
                            expr,
                            stack_var_name.as_deref(),
                            stack_slot,
                        );
                        scratch
                            .info
                            .definition_overrides
                            .insert(dst.display_name(), expr.clone());
                        merged_defs.insert(dst.display_name(), expr);
                    } else if let Some(stack_var_name) = stack_var_name {
                        let expr = CExpr::Var(stack_var_name);
                        scratch
                            .info
                            .definition_overrides
                            .insert(dst.display_name(), expr.clone());
                        merged_defs.insert(dst.display_name(), expr);
                    }
                }
                _ => {}
            }
        }
    }
}

fn is_reserved_param_alias_name(name: &str, env: &PassEnv<'_>) -> bool {
    env.param_register_aliases
        .values()
        .any(|alias| alias.eq_ignore_ascii_case(name))
}

fn generic_stack_var_name(offset: i64) -> String {
    if offset < 0 {
        format!("local_{:x}", (-offset) as u64)
    } else {
        format!("stack_{:x}", offset as u64)
    }
}

fn set_stack_arg_alias(scratch: &mut StackScratch, offset: i64, alias: String, env: &PassEnv<'_>) {
    scratch
        .info
        .stack_arg_aliases
        .entry(offset)
        .or_insert_with(|| alias.clone());

    let should_replace = match scratch.info.stack_vars.get(&offset) {
        None => true,
        Some(existing) => {
            existing.starts_with("local_")
                || existing.starts_with("stack_")
                || existing == "saved_fp"
        }
    };

    if should_replace {
        if !is_reserved_param_alias_name(&alias, env) {
            scratch.info.stack_vars.insert(offset, alias);
        } else {
            scratch
                .info
                .stack_vars
                .entry(offset)
                .or_insert_with(|| generic_stack_var_name(offset));
        }
    }
}

fn get_or_create_stack_var(scratch: &mut StackScratch, offset: i64, env: &PassEnv<'_>) -> String {
    if let Some(alias) = scratch.info.stack_arg_aliases.get(&offset)
        && !is_reserved_param_alias_name(alias, env)
    {
        return alias.clone();
    }
    if let Some(name) = scratch.info.stack_vars.get(&offset) {
        return name.clone();
    }

    let name = generic_stack_var_name(offset);
    scratch.info.stack_vars.insert(offset, name.clone());
    name
}

struct StackVarLookupInputs<'a, 'b> {
    definitions: &'a HashMap<String, CExpr>,
    stack_vars: &'a HashMap<i64, String>,
    stack_arg_aliases: &'a HashMap<i64, String>,
    var_aliases: &'a HashMap<String, String>,
    stack_slots: &'a HashMap<String, super::StackSlotProvenance>,
    copy_sources: &'a HashMap<String, String>,
    forwarded_values: &'a HashMap<String, super::ValueProvenance>,
    env: &'a PassEnv<'b>,
}

fn stack_var_for_addr_var(
    addr: &r2ssa::SSAVar,
    inputs: StackVarLookupInputs<'_, '_>,
) -> Option<String> {
    if addr_is_stack_reloaded_value(addr, inputs.copy_sources, inputs.forwarded_values) {
        return None;
    }
    let addr_key = addr.display_name();
    let offset_backed = inputs
        .stack_slots
        .get(&addr_key)
        .map(|slot| slot.offset)
        .or_else(|| {
            utils::extract_stack_offset_from_var(
                addr,
                inputs.definitions,
                inputs.env.fp_name,
                inputs.env.sp_name,
            )
        })
        .map(|offset| {
            let preferred = inputs
                .stack_arg_aliases
                .get(&offset)
                .cloned()
                .or_else(|| inputs.stack_vars.get(&offset).cloned())
                .unwrap_or_else(|| generic_stack_var_name(offset));
            (offset, preferred)
        });
    if let Some(alias) = resolve_stack_alias_from_addr_expr(
        &CExpr::Var(addr_key.clone()),
        inputs.definitions,
        inputs.stack_vars,
        inputs.env,
        0,
        &mut HashSet::new(),
    ) {
        if let Some(preferred) =
            preferred_stack_alias(&alias, offset_backed.clone(), inputs.stack_vars)
        {
            return Some(preferred);
        }
        return Some(alias);
    }

    let empty_counts: HashMap<String, usize> = HashMap::new();
    let empty_names: HashSet<String> = HashSet::new();
    let empty_ptrs: HashMap<String, crate::fold::PtrArith> = HashMap::new();
    let empty_semantic_values: HashMap<String, crate::analysis::SemanticValue> = HashMap::new();
    let lower = LowerCtx {
        definitions: inputs.definitions,
        semantic_values: &empty_semantic_values,
        use_counts: &empty_counts,
        condition_vars: &empty_names,
        pinned: &empty_names,
        var_aliases: inputs.var_aliases,
        param_register_aliases: inputs.env.param_register_aliases,
        type_hints: inputs.env.type_hints,
        ptr_arith: &empty_ptrs,
        stack_slots: inputs.stack_slots,
        forwarded_values: &HashMap::new(),
        function_names: inputs.env.function_names,
        strings: inputs.env.strings,
        symbols: inputs.env.symbols,
        type_oracle: inputs.env.type_oracle,
    };
    let rendered = lower.var_name(addr);
    if let Some(alias) = resolve_stack_alias_from_addr_expr(
        &CExpr::Var(rendered),
        inputs.definitions,
        inputs.stack_vars,
        inputs.env,
        0,
        &mut HashSet::new(),
    ) {
        if let Some(preferred) =
            preferred_stack_alias(&alias, offset_backed.clone(), inputs.stack_vars)
        {
            return Some(preferred);
        }
        return Some(alias);
    }

    offset_backed.map(|(_, name)| name)
}

fn stack_slot_for_addr_var(
    addr: &r2ssa::SSAVar,
    definitions: &HashMap<String, CExpr>,
    stack_slots: &HashMap<String, super::StackSlotProvenance>,
    copy_sources: &HashMap<String, String>,
    forwarded_values: &HashMap<String, super::ValueProvenance>,
    env: &PassEnv<'_>,
) -> Option<super::StackSlotProvenance> {
    if addr_is_stack_reloaded_value(addr, copy_sources, forwarded_values) {
        return None;
    }
    stack_slots.get(&addr.display_name()).copied().or_else(|| {
        utils::extract_stack_offset_from_var(addr, definitions, env.fp_name, env.sp_name).and_then(
            |offset| {
                stack_slots
                    .values()
                    .copied()
                    .find(|slot| slot.offset == offset)
            },
        )
    })
}

fn addr_is_stack_reloaded_value(
    addr: &r2ssa::SSAVar,
    copy_sources: &HashMap<String, String>,
    forwarded_values: &HashMap<String, super::ValueProvenance>,
) -> bool {
    let mut current = addr.display_name();
    let mut seen = HashSet::new();
    while seen.insert(current.clone()) {
        if forwarded_values
            .get(&current)
            .is_some_and(|prov| prov.stack_slot.is_some())
        {
            return true;
        }
        let Some(next) = copy_sources.get(&current).cloned() else {
            break;
        };
        current = next;
    }
    false
}

fn is_generic_stack_name(name: &str) -> bool {
    name.starts_with("local_") || name.starts_with("stack_") || name == "saved_fp"
}

fn normalize_scalar_stack_load_expr(
    expr: CExpr,
    stack_var_name: Option<&str>,
    stack_slot: Option<super::StackSlotProvenance>,
) -> CExpr {
    let Some(stack_var_name) = stack_var_name else {
        return expr;
    };
    if !is_generic_stack_name(stack_var_name) && expr_is_addr_of_expr(&expr) {
        return CExpr::Var(stack_var_name.to_string());
    }
    if expr_is_addr_of_named_var(&expr, stack_var_name) {
        return CExpr::Var(stack_var_name.to_string());
    }

    let Some(stack_slot) = stack_slot else {
        return expr;
    };
    if !stack_slot.is_scalar() {
        return expr;
    }
    if expr_is_literalish(&expr) {
        return CExpr::Var(stack_var_name.to_string());
    }

    expr
}

fn expr_is_literalish(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_) => true,
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => expr_is_literalish(inner),
        _ => false,
    }
}

fn expr_is_addr_of_named_var(expr: &CExpr, name: &str) -> bool {
    match expr {
        CExpr::AddrOf(inner) => expr_is_named_var(inner, name),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            expr_is_addr_of_named_var(inner, name)
        }
        _ => false,
    }
}

fn expr_is_addr_of_expr(expr: &CExpr) -> bool {
    match expr {
        CExpr::AddrOf(_) => true,
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => expr_is_addr_of_expr(inner),
        _ => false,
    }
}

fn expr_is_named_var(expr: &CExpr, name: &str) -> bool {
    match expr {
        CExpr::Var(inner) => inner.eq_ignore_ascii_case(name),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => expr_is_named_var(inner, name),
        _ => false,
    }
}

fn preferred_stack_alias(
    alias: &str,
    offset_backed: Option<(i64, String)>,
    stack_vars: &HashMap<i64, String>,
) -> Option<String> {
    if !is_generic_stack_name(alias) {
        return None;
    }
    let offset = parse_generic_stack_name_offset(alias)?;
    if let Some((preferred_offset, preferred)) = offset_backed
        && preferred_offset == offset
        && !is_generic_stack_name(&preferred)
    {
        return Some(preferred);
    }
    let preferred = stack_vars.get(&offset)?.clone();
    if is_generic_stack_name(&preferred) {
        return None;
    }
    Some(preferred)
}

fn parse_generic_stack_name_offset(name: &str) -> Option<i64> {
    if name == "saved_fp" {
        return Some(0);
    }
    if let Some(rest) = name.strip_prefix("local_") {
        return i64::from_str_radix(rest, 16).ok().map(|v| -v);
    }
    if let Some(rest) = name.strip_prefix("stack_") {
        return i64::from_str_radix(rest, 16).ok();
    }
    None
}

fn forwarded_expr_for_value(
    value_key: &str,
    definitions: &HashMap<String, CExpr>,
    use_info: &UseInfo,
    env: &PassEnv<'_>,
) -> Option<CExpr> {
    let prov = use_info.forwarded_values.get(value_key)?;
    let empty_counts: HashMap<String, usize> = HashMap::new();
    let empty_names: HashSet<String> = HashSet::new();
    let empty_ptrs: HashMap<String, crate::fold::PtrArith> = HashMap::new();
    let lower = LowerCtx {
        definitions,
        semantic_values: &use_info.semantic_values,
        use_counts: &empty_counts,
        condition_vars: &empty_names,
        pinned: &empty_names,
        var_aliases: &use_info.var_aliases,
        param_register_aliases: env.param_register_aliases,
        type_hints: &use_info.type_hints,
        ptr_arith: &empty_ptrs,
        stack_slots: &use_info.stack_slots,
        forwarded_values: &use_info.forwarded_values,
        function_names: env.function_names,
        strings: env.strings,
        symbols: env.symbols,
        type_oracle: env.type_oracle,
    };
    Some(lower.expr_for_ssa_name(&prov.source))
}

fn resolve_stack_alias_from_addr_expr(
    expr: &CExpr,
    definitions: &HashMap<String, CExpr>,
    stack_vars: &HashMap<i64, String>,
    env: &PassEnv<'_>,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<String> {
    if depth > 8 {
        return None;
    }

    if let Some(alias) = utils::simplify_stack_access(expr, stack_vars, env.fp_name, env.sp_name) {
        return Some(alias);
    }

    match expr {
        CExpr::Var(name) => {
            if let Some(stripped) = name.strip_prefix('&') {
                return Some(stripped.to_string());
            }
            if !visited.insert(name.clone()) {
                return None;
            }
            definitions.get(name).and_then(|inner| {
                resolve_stack_alias_from_addr_expr(
                    inner,
                    definitions,
                    stack_vars,
                    env,
                    depth + 1,
                    visited,
                )
            })
        }
        CExpr::Paren(inner) => resolve_stack_alias_from_addr_expr(
            inner,
            definitions,
            stack_vars,
            env,
            depth + 1,
            visited,
        ),
        CExpr::Cast { expr: inner, .. } => resolve_stack_alias_from_addr_expr(
            inner,
            definitions,
            stack_vars,
            env,
            depth + 1,
            visited,
        ),
        CExpr::AddrOf(inner) => resolve_stack_alias_from_addr_expr(
            inner,
            definitions,
            stack_vars,
            env,
            depth + 1,
            visited,
        ),
        CExpr::Deref(inner) => resolve_stack_alias_from_addr_expr(
            inner,
            definitions,
            stack_vars,
            env,
            depth + 1,
            visited,
        ),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        generic_stack_var_name, is_reserved_param_alias_name, normalize_scalar_stack_load_expr,
        preferred_stack_alias,
    };
    use crate::DecompilerConfig;
    use crate::analysis::PassEnv;
    use crate::analysis::{StackSlotProvenance, StackSlotValueKind};
    use crate::ast::CExpr;
    use crate::ast::CType;
    use std::collections::HashMap;

    #[test]
    fn preferred_stack_alias_requires_offset_match_for_non_generic_override() {
        let stack_vars = HashMap::from([
            (-0x10, "var_10h".to_string()),
            (-0x14, "var_14h".to_string()),
            (-0x4, "var_4h".to_string()),
        ]);

        assert_eq!(
            preferred_stack_alias("local_10", Some((-0x4, "var_4h".to_string())), &stack_vars),
            Some("var_10h".to_string())
        );
        assert_eq!(
            preferred_stack_alias("local_14", Some((-0x4, "var_4h".to_string())), &stack_vars),
            Some("var_14h".to_string())
        );
    }

    #[test]
    fn normalize_scalar_stack_load_expr_keeps_named_slot_over_address_alias() {
        let slot = StackSlotProvenance {
            offset: -0x14,
            predicate_carrier: false,
            return_carrier: false,
            value_kind: StackSlotValueKind::Scalar,
        };
        let expr = CExpr::AddrOf(Box::new(CExpr::Var("a".to_string())));

        assert_eq!(
            normalize_scalar_stack_load_expr(expr, Some("a"), Some(slot)),
            CExpr::Var("a".to_string())
        );
    }

    #[test]
    fn normalize_scalar_stack_load_expr_keeps_named_slot_over_literal_seed() {
        let slot = StackSlotProvenance {
            offset: -0x2c,
            predicate_carrier: false,
            return_carrier: false,
            value_kind: StackSlotValueKind::Scalar,
        };

        assert_eq!(
            normalize_scalar_stack_load_expr(CExpr::IntLit(1), Some("local_2c"), Some(slot)),
            CExpr::Var("local_2c".to_string())
        );
    }

    #[test]
    fn reserved_param_alias_name_detects_visible_param_names() {
        let arch = DecompilerConfig::x86_64();
        let param_aliases = HashMap::from([
            ("rdi".to_string(), "a".to_string()),
            ("rsi".to_string(), "b".to_string()),
        ]);
        let type_hints = HashMap::from([
            ("a".to_string(), CType::Int(32)),
            ("b".to_string(), CType::Int(32)),
        ]);
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let symbols = HashMap::new();
        let env = PassEnv {
            ptr_size: arch.ptr_size,
            sp_name: &arch.sp_name,
            fp_name: &arch.fp_name,
            ret_reg_name: arch.ret_regs.first().map(String::as_str).unwrap_or("rax"),
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            arg_regs: &arch.arg_regs,
            param_register_aliases: &param_aliases,
            caller_saved_regs: &arch.caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };

        assert!(is_reserved_param_alias_name("a", &env));
        assert!(is_reserved_param_alias_name("B", &env));
        assert!(!is_reserved_param_alias_name("sum", &env));
    }

    #[test]
    fn generic_stack_var_name_uses_local_prefix_for_negative_offsets() {
        assert_eq!(generic_stack_var_name(-0x14), "local_14");
        assert_eq!(generic_stack_var_name(0x20), "stack_20");
    }
}
