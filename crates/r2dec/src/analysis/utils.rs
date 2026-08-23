use std::collections::{HashMap, HashSet};

use r2ssa::{SSAVar, SSAVarNameKind};

use crate::ast::{BinaryOp, CExpr};

/// Threshold for detecting 64-bit negative values stored as unsigned.
const LIKELY_NEGATIVE_THRESHOLD: u64 = 0xffffffffffff0000;

/// The spelling under which a flag is recorded, with prefix and version removed.
pub(crate) fn flag_base_name(name: &str) -> String {
    let lower = name.to_ascii_lowercase();
    let base = lower.strip_prefix("reg:").unwrap_or(&lower);
    match base.rsplit_once('_') {
        Some((head, tail)) if !tail.is_empty() && tail.bytes().all(|b| b.is_ascii_digit()) => {
            head.to_string()
        }
        _ => base.to_string(),
    }
}

pub(crate) fn is_cpu_flag(name: &str) -> bool {
    if matches!(
        name,
        "cf" | "pf"
            | "af"
            | "zf"
            | "sf"
            | "of"
            | "cy"
            | "zr"
            | "ng"
            | "ov"
            | "nf"
            | "vf"
            | "df"
            | "tf"
            | "if"
            | "iopl"
            | "nt"
            | "rf"
            | "vm"
            | "ac"
            | "vif"
            | "vip"
            | "id"
            | "tmpcy"
            | "tmpzr"
            | "tmpng"
            | "tmpov"
    ) {
        return true;
    }

    name.starts_with("cf_")
        || name.starts_with("pf_")
        || name.starts_with("af_")
        || name.starts_with("zf_")
        || name.starts_with("sf_")
        || name.starts_with("of_")
        || name.starts_with("cy_")
        || name.starts_with("zr_")
        || name.starts_with("ng_")
        || name.starts_with("ov_")
        || name.starts_with("nf_")
        || name.starts_with("vf_")
        || name.starts_with("tmpcy_")
        || name.starts_with("tmpzr_")
        || name.starts_with("tmpng_")
        || name.starts_with("tmpov_")
}

pub(crate) fn parse_const_value(name: &str) -> Option<u64> {
    let val_str = name.strip_prefix("const:")?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);

    if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).ok()
    } else if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        dec.parse().ok()
    } else if val_str.chars().all(|c| c.is_ascii_hexdigit()) {
        u64::from_str_radix(val_str, 16).ok()
    } else {
        val_str.parse().ok()
    }
}

pub(crate) fn is_generic_stack_placeholder_alias(existing: &str) -> bool {

    let normalized = existing.trim_start_matches('&');
    normalized == "stack"
        || normalized.starts_with("stack_")
        || normalized == "slot"
        || normalized.starts_with("slot_")
        || normalized == "saved_fp"
}

pub(crate) fn parse_compare_const_value_with_width(
    var: &SSAVar,
    _compare_width: u32,
) -> Option<u64> {
    let raw = var.name.strip_prefix("const:")?;
    let raw = raw.split('_').next().unwrap_or(raw);

    if let Some(dec) = raw.strip_prefix("0d").or_else(|| raw.strip_prefix("0D")) {
        return dec.parse().ok();
    }

    parse_const_value(&var.name)
}

#[cfg(test)]
pub(crate) fn parse_compare_const_value(var: &SSAVar) -> Option<u64> {
    parse_compare_const_value_with_width(var, var.size)
}

pub(crate) fn compare_const_to_expr_with_width(var: &SSAVar, compare_width: u32) -> CExpr {
    let val = parse_compare_const_value_with_width(var, compare_width).unwrap_or(0);
    if val > 0x7fffffff {
        CExpr::UIntLit(val)
    } else {
        CExpr::IntLit(val as i64)
    }
}

pub(crate) fn compare_const_to_expr(var: &SSAVar) -> CExpr {
    compare_const_to_expr_with_width(var, var.size)
}

pub(crate) fn parse_const_offset(var: &SSAVar) -> Option<i64> {
    if !var.is_const() {
        return None;
    }
    // Offsets in SSA const varnames are interpreted as hex by default to stay
    // consistent with type inference / field recovery paths.
    let val = {
        let val_str = var
            .name
            .strip_prefix("const:")?
            .split('_')
            .next()
            .unwrap_or_default();
        if let Some(hex) = val_str
            .strip_prefix("0x")
            .or_else(|| val_str.strip_prefix("0X"))
        {
            u64::from_str_radix(hex, 16).ok()?
        } else if let Some(dec) = val_str
            .strip_prefix("0d")
            .or_else(|| val_str.strip_prefix("0D"))
        {
            dec.parse().ok()?
        } else {
            u64::from_str_radix(val_str, 16).ok()?
        }
    };
    if val > LIKELY_NEGATIVE_THRESHOLD {
        let neg = (!val).wrapping_add(1);
        Some(-(neg as i64))
    } else {
        Some(val as i64)
    }
}

pub(crate) fn uf_find(parent: &mut HashMap<String, String>, x: &str) -> String {
    let p = parent.get(x).cloned().unwrap_or_else(|| x.to_string());
    if p == x {
        return x.to_string();
    }
    let root = uf_find(parent, &p);
    parent.insert(x.to_string(), root.clone());
    root
}

/// How a value keyed only by its display name is spelled.
///
/// A rendered identifier is spelled by `spell_var`, which works from an
/// `SSAVar`. Code that holds only the display name used to spell it separately,
/// and the two disagreed: `spell_var` gave `tmp:25400_2` the name `t25400_2`
/// while this gave the raw key back, so the statement defining the value and the
/// expression using it were two different identifiers and the use read as
/// undefined. Worse, every version-zero temporary was spelled `t0` whatever its
/// name, so distinct values shared one identifier -- the collision the symbol
/// table exists to make impossible, happening one layer above it.
///
/// So this reconstructs the variable and asks the same question `spell_var`
/// asks. There is one spelling of a value, and this is not a second one.
pub(crate) fn format_traced_name(key: &str, var_aliases: &HashMap<String, String>) -> String {
    if let Some(alias) = var_aliases.get(key) {
        return alias.clone();
    }
    let (base, version) = split_display_name(key);
    // Size plays no part in how a name is spelled, so any value serves here.
    let var = SSAVar::new(base, version, 0);
    let rendered = ssa_render_base_name(&var);
    if version > 0 {
        format!("{rendered}_{version}")
    } else {
        rendered
    }
}

/// A display name split back into the variable and version it was made from.
///
/// `display_name` joins them with an underscore, and a machine name may contain
/// underscores of its own, so only a numeric tail is a version.
pub(crate) fn split_display_name(key: &str) -> (&str, u32) {
    match key.rsplit_once('_') {
        Some((base, tail)) => match tail.parse::<u32>() {
            Ok(version) => (base, version),
            Err(_) => (key, 0),
        },
        None => (key, 0),
    }
}

pub(crate) fn ssa_name_kind(name: &str) -> SSAVarNameKind {
    let lower = name.to_ascii_lowercase();
    SSAVarNameKind::classify(&lower)
}

pub(crate) fn is_temporary_name(name: &str) -> bool {

    ssa_name_kind(name).is_temporary()
}

pub(crate) fn is_temporary_or_constant_name(name: &str) -> bool {
    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Temporary | SSAVarNameKind::Constant
    )
}

pub(crate) fn is_temporary_or_memory_name(name: &str) -> bool {

    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Temporary | SSAVarNameKind::Memory
    )
}

pub(crate) fn is_temporary_constant_or_memory_name(name: &str) -> bool {
    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Temporary | SSAVarNameKind::Constant | SSAVarNameKind::Memory
    )
}

pub(crate) fn is_constant_or_memory_name(name: &str) -> bool {

    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Constant | SSAVarNameKind::Memory | SSAVarNameKind::AddressSpace
    )
}

pub(crate) fn is_low_signal_ssa_storage_name(name: &str) -> bool {

    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Temporary
            | SSAVarNameKind::Constant
            | SSAVarNameKind::Memory
            | SSAVarNameKind::AddressSpace
    )
}

pub(crate) fn ssa_render_base_name(var: &SSAVar) -> String {
    match var.name_kind() {
        SSAVarNameKind::RegisterAlias => {
            let reg = var.name.strip_prefix("reg:").unwrap_or(&var.name);
            if is_hex_name(reg) {
                format!("r{}", reg)
            } else {
                reg.to_string()
            }
        }
        SSAVarNameKind::Temporary => {
            let tmp = SSAVarNameKind::strip_temporary_prefix(&var.name).unwrap_or(&var.name);
            format!("t{}", tmp)
        }
        _ => var.name.to_lowercase(),
    }
}

pub(crate) fn trace_ssa_var_to_source(
    var: &SSAVar,
    copy_sources: &HashMap<String, String>,
    var_aliases: &HashMap<String, String>,
) -> String {
    let mut current_key = var.display_name();
    let mut visited = HashSet::new();

    for _ in 0..20 {
        if !visited.insert(current_key.clone()) {
            break;
        }

        if let Some(src_key) = copy_sources.get(&current_key) {
            if src_key.starts_with('*') {
                return format!("var_{}", current_key.split('_').next_back().unwrap_or("0"));
            }
            current_key = src_key.clone();
            continue;
        }
        break;
    }

    format_traced_name(&current_key, var_aliases)
}

pub(crate) fn expr_to_offset(expr: &CExpr) -> Option<i64> {
    match expr {
        CExpr::IntLit(v) => Some(*v),
        CExpr::UIntLit(v) => {
            if *v > LIKELY_NEGATIVE_THRESHOLD {
                let neg = (!*v).wrapping_add(1);
                Some(-(neg as i64))
            } else {
                Some(*v as i64)
            }
        }
        _ => None,
    }
}

pub(crate) fn extract_offset_from_expr(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, expr: &CExpr, fp_name: &str, sp_name: &str) -> Option<i64> {
    match expr {
        CExpr::Paren(inner) => extract_offset_from_expr(symbols, inner, fp_name, sp_name),
        CExpr::Cast { expr: inner, .. } => extract_offset_from_expr(symbols, inner, fp_name, sp_name),
        CExpr::AddrOf(inner) => extract_offset_from_expr(symbols, inner, fp_name, sp_name),
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => {
            if let CExpr::Var(name) = left.as_ref() {
                let name_lower = crate::symbol::spelling(symbols, *name).to_lowercase();
                if name_lower.contains(fp_name) || name_lower.contains(sp_name) {
                    return expr_to_offset(right);
                }
            }
            if let CExpr::Var(name) = right.as_ref() {
                let name_lower = crate::symbol::spelling(symbols, *name).to_lowercase();
                if name_lower.contains(fp_name) || name_lower.contains(sp_name) {
                    return expr_to_offset(left);
                }
            }
            None
        }
        CExpr::Binary {
            op: BinaryOp::Sub,
            left,
            right,
        } => {
            if let CExpr::Var(name) = left.as_ref() {
                let name_lower = crate::symbol::spelling(symbols, *name).to_lowercase();
                if name_lower.contains(fp_name) || name_lower.contains(sp_name) {
                    return expr_to_offset(right).map(|off| -off);
                }
            }
            None
        }
        CExpr::Var(name) => {
            let name_lower = crate::symbol::spelling(symbols, *name).to_lowercase();
            if name_lower.contains(fp_name) || name_lower.contains(sp_name) {
                return Some(0);
            }
            parse_canonical_stack_name_offset(&name_lower)
        }
        _ => None,
    }
}

fn parse_canonical_stack_name_offset(name: &str) -> Option<i64> {
    let stripped = name.strip_prefix('&').unwrap_or(name);
    if stripped == "saved_fp" {
        return Some(0);
    }
    if let Some(rest) = stripped.strip_prefix("local_") {
        return i64::from_str_radix(rest, 16).ok().map(|v| -v);
    }
    if let Some(rest) = stripped.strip_prefix("stack_") {
        return i64::from_str_radix(rest, 16).ok();
    }
    None
}

pub(crate) fn extract_stack_offset_from_var(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
    var: &SSAVar,
    definitions: &HashMap<String, CExpr>,
    fp_name: &str,
    sp_name: &str,
) -> Option<i64> {
    let name_lower = var.name.to_lowercase();
    if name_lower.contains(fp_name) || name_lower.contains(sp_name) {
        return Some(0);
    }

    let key = var.display_name();
    let mut visited = HashSet::new();
    definitions.get(&key).and_then(|expr| {
        extract_offset_from_expr_with_defs(symbols, expr, definitions, fp_name, sp_name, 0, &mut visited)
    })
}

fn extract_offset_from_expr_with_defs(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
    expr: &CExpr,
    definitions: &HashMap<String, CExpr>,
    fp_name: &str,
    sp_name: &str,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 10 {
        return None;
    }

    if let Some(offset) = extract_offset_from_expr(symbols, expr, fp_name, sp_name) {
        return Some(offset);
    }

    match expr {
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => {
            if let Some(offset) = expr_to_offset(left)
                && let Some(base) = extract_offset_from_expr_with_defs(symbols, 
                    right,
                    definitions,
                    fp_name,
                    sp_name,
                    depth + 1,
                    visited,
                )
            {
                return Some(base.saturating_add(offset));
            }
            if let Some(offset) = expr_to_offset(right)
                && let Some(base) = extract_offset_from_expr_with_defs(symbols, 
                    left,
                    definitions,
                    fp_name,
                    sp_name,
                    depth + 1,
                    visited,
                )
            {
                return Some(base.saturating_add(offset));
            }
            None
        }
        CExpr::Binary {
            op: BinaryOp::Sub,
            left,
            right,
        } => {
            if let Some(offset) = expr_to_offset(right)
                && let Some(base) = extract_offset_from_expr_with_defs(symbols, 
                    left,
                    definitions,
                    fp_name,
                    sp_name,
                    depth + 1,
                    visited,
                )
            {
                return Some(base.saturating_sub(offset));
            }
            None
        }
        CExpr::Var(name) => {
            if !visited.insert(crate::symbol::spelling(symbols, *name).to_string()) {
                return None;
            }
            definitions.get(&*crate::symbol::spelling(symbols, *name)).and_then(|inner| {
                extract_offset_from_expr_with_defs(symbols, 
                    inner,
                    definitions,
                    fp_name,
                    sp_name,
                    depth + 1,
                    visited,
                )
            })
        }
        CExpr::Paren(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Deref(inner)
        | CExpr::Unary { operand: inner, .. } => extract_offset_from_expr_with_defs(symbols, 
            inner,
            definitions,
            fp_name,
            sp_name,
            depth + 1,
            visited,
        ),
        _ => None,
    }
}

#[allow(dead_code)]
pub(crate) fn normalize_stack_address(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
    addr: &SSAVar,
    definitions: &HashMap<String, CExpr>,
    fp_name: &str,
    sp_name: &str,
) -> String {
    let addr_key = addr.display_name();
    if let Some(expr) = definitions.get(&addr_key)
        && let Some(offset) = extract_offset_from_expr(symbols, expr, fp_name, sp_name)
    {
        return format!("stack:{}", offset);
    }
    addr_key
}

pub(crate) fn arg_alias_for_register_name(reg_name: &str) -> Option<String> {
    let reg = reg_name.to_lowercase();
    if reg.contains("rdi") || reg.contains("edi") {
        return Some("arg0".to_string());
    }
    if reg.contains("rsi") || reg.contains("esi") {
        return Some("arg1".to_string());
    }
    if reg.contains("rdx") || reg.contains("edx") {
        return Some("arg2".to_string());
    }
    if reg.contains("rcx") || reg.contains("ecx") {
        return Some("arg3".to_string());
    }
    if reg.contains("r8") {
        return Some("arg4".to_string());
    }
    if reg.contains("r9") {
        return Some("arg5".to_string());
    }
    None
}

pub(crate) fn arg_alias_for_ssa_name(ssa_name: &str) -> Option<String> {
    let (base, version) = ssa_name.rsplit_once('_')?;
    if version != "0" {
        return None;
    }
    arg_alias_for_register_name(base)
}

pub(crate) fn param_register_alias_for_ssa_name(
    ssa_name: &str,
    param_register_aliases: &HashMap<String, String>,
) -> Option<String> {
    let lower = ssa_name.to_ascii_lowercase();
    param_register_aliases.get(&lower).cloned().or_else(|| {
        // Only the entry value of the carrier is the parameter. A later version
        // of the same register is whatever was computed into it since, and
        // reading the alias off the base name called a call result an argument.
        lower
            .rsplit_once('_')
            .filter(|(_, version)| *version == "0")
            .and_then(|(base, _)| param_register_aliases.get(base).cloned())
    })
}

pub(crate) fn arg_alias_for_store_source(
    src: &SSAVar,
    copy_sources: &HashMap<String, String>,
    var_aliases: &HashMap<String, String>,
    param_register_aliases: &HashMap<String, String>,
) -> Option<String> {
    let mut key = src.display_name();
    let mut visited = HashSet::new();

    for _ in 0..8 {
        if !visited.insert(key.clone()) {
            break;
        }
        if let Some(alias) = param_register_alias_for_ssa_name(&key, param_register_aliases) {
            return Some(alias);
        }
        if let Some(alias) = arg_alias_for_ssa_name(&key) {
            return Some(alias);
        }
        let Some(next) = copy_sources.get(&key) else {
            break;
        };
        key = next.clone();
    }

    let traced = trace_ssa_var_to_source(src, copy_sources, var_aliases);
    param_register_aliases
        .get(&traced.to_ascii_lowercase())
        .cloned()
        .or_else(|| arg_alias_for_register_name(&traced))
}

fn is_hex_name(value: &str) -> bool {
    !value.is_empty() && value.chars().all(|c| c.is_ascii_hexdigit())
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2ssa::SSAVar;

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[test]
    fn parse_const_value_uses_ssa_hex_payload_by_default() {
        assert_eq!(parse_const_value("const:100"), Some(0x100));
        assert_eq!(parse_const_value("const:0x100"), Some(0x100));
        assert_eq!(parse_const_value("const:0d100"), Some(100));
    }

    #[test]
    fn generic_stack_placeholder_alias_covers_all_generic_forms() {
        for name in ["stack", "stack_10", "slot", "slot_20", "saved_fp"] {
            assert!(
                is_generic_stack_placeholder_alias(name),
                "{name} should be classified as a generic stack placeholder"
            );
            let addr_name = format!("&{name}");
            assert!(
                is_generic_stack_placeholder_alias(&addr_name),
                "{addr_name} should be classified after address-of trimming"
            );
        }

        for name in ["local_10", "arg0", "real_slot_name", "saved_lr"] {
            assert!(
                !is_generic_stack_placeholder_alias(name),
                "{name} should not be treated as a generic stack placeholder"
            );
        }
    }

    #[test]
    fn parse_compare_const_value_keeps_lifted_hex_immediates_and_explicit_decimal_tests() {
        let wide = SSAVar::new("const:64", 0, 8);
        let narrow = SSAVar::new("const:64", 0, 4);
        let explicit_decimal = SSAVar::new("const:0d64", 0, 8);

        assert_eq!(parse_compare_const_value(&wide), Some(0x64));
        assert_eq!(parse_compare_const_value(&narrow), Some(0x64));
        assert_eq!(parse_compare_const_value(&explicit_decimal), Some(64));
    }

    #[test]
    fn parse_compare_const_value_with_width_prefers_hex_for_wide_comparisons() {
        let narrow = SSAVar::new("const:64", 0, 4);
        let decimal = SSAVar::new("const:0d100", 0, 4);

        assert_eq!(parse_compare_const_value_with_width(&narrow, 8), Some(0x64));
        assert_eq!(parse_compare_const_value_with_width(&decimal, 4), Some(100));
    }

    #[test]
    fn parse_const_offset_handles_negative_wrapped_values() {
        let wrapped = SSAVar::new("const:ffffffffffffffb8", 0, 8);
        assert_eq!(parse_const_offset(&wrapped), Some(-72));
    }

    #[test]
    fn parse_const_offset_prefers_hex_for_plain_offsets() {
        let plain = SSAVar::new("const:100", 0, 8);
        assert_eq!(parse_const_offset(&plain), Some(0x100));
        let explicit_dec = SSAVar::new("const:0d100", 0, 8);
        assert_eq!(parse_const_offset(&explicit_dec), Some(100));
    }

    #[test]
    fn param_register_alias_only_answers_for_the_entry_value() {
        let aliases = HashMap::from([("x0".to_string(), "s".to_string())]);
        assert_eq!(
            param_register_alias_for_ssa_name("X0_0", &aliases),
            Some("s".to_string())
        );
        assert_eq!(param_register_alias_for_ssa_name("X0_2", &aliases), None);
    }

    #[test]
    fn arg_alias_for_store_source_uses_arch_param_aliases() {
        let src = SSAVar::new("X1", 0, 8);
        let copy_sources = HashMap::new();
        let var_aliases = HashMap::new();
        let param_register_aliases = HashMap::from([(String::from("x1"), String::from("arg2"))]);

        assert_eq!(
            arg_alias_for_store_source(&src, &copy_sources, &var_aliases, &param_register_aliases),
            Some(String::from("arg2"))
        );
    }

    #[test]
    fn extract_stack_offset_from_var_handles_nested_temp_plus_const() {
        let symbols = test_table();
        let mut definitions = HashMap::new();
        definitions.insert(
            String::from("tmp:11f80_2"),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var(crate::symbol::declare(&symbols, "sp_2")),
                CExpr::IntLit(0x3e0),
            ),
        );
        definitions.insert(
            String::from("x8_1"),
            CExpr::Var(crate::symbol::declare(&symbols, "tmp:11f80_2")),
        );
        definitions.insert(
            String::from("tmp:6500_2"),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var(crate::symbol::declare(&symbols, "x8_1")),
                CExpr::IntLit(0x160),
            ),
        );

        let addr = SSAVar::new("tmp:6500", 2, 8);
        assert_eq!(
            extract_stack_offset_from_var(&symbols, &addr, &definitions, "fp", "sp"),
            Some(0x540)
        );
    }

    #[test]
    fn format_traced_name_keeps_temp_base_identity() {
        // Version zero is still this temporary, not a name shared with every
        // other version-zero temporary in the function.
        assert_eq!(format_traced_name("tmp:11f80_0", &HashMap::new()), "t11f80");
        assert_eq!(format_traced_name("tmp:25400_0", &HashMap::new()), "t25400");
        assert_eq!(
            format_traced_name("tmp:11f80_19", &HashMap::new()),
            "t11f80_19"
        );
        assert_eq!(format_traced_name("tmp:foo_2", &HashMap::new()), "tfoo_2");
        assert_eq!(
            format_traced_name("unique:11f80_19", &HashMap::new()),
            "t11f80_19"
        );
    }

    #[test]
    fn format_traced_name_uses_typed_name_kinds_for_visibility() {
        assert_eq!(format_traced_name("RAX_0", &HashMap::new()), "rax");
        assert_eq!(format_traced_name("RAX_2", &HashMap::new()), "rax_2");
        // A constant and a memory cell are not variables, and neither spelling
        // here is a legal C identifier. What this pins is that the answer matches
        // `spell_var`'s, so a value has one spelling; that either of these reaches
        // a name at all is a separate defect, recorded rather than papered over.
        assert_eq!(format_traced_name("const:2a_0", &HashMap::new()), "const:2a");
        assert_eq!(
            format_traced_name("ram:401000_0", &HashMap::new()),
            "ram:401000"
        );

        let aliases = HashMap::from([(String::from("tmp:11f80_19"), String::from("idx"))]);
        assert_eq!(format_traced_name("tmp:11f80_19", &aliases), "idx");
    }

    #[test]
    fn ssa_render_base_name_uses_typed_name_kinds() {
        assert_eq!(ssa_render_base_name(&SSAVar::new("reg:10", 0, 8)), "r10");
        assert_eq!(ssa_render_base_name(&SSAVar::new("reg:zf", 0, 1)), "zf");
        assert_eq!(
            ssa_render_base_name(&SSAVar::new("tmp:11f80", 2, 8)),
            "t11f80"
        );
        assert_eq!(
            ssa_render_base_name(&SSAVar::new("unique:11f80", 2, 8)),
            "t11f80"
        );
        assert_eq!(ssa_render_base_name(&SSAVar::new("RAX", 1, 8)), "rax");
    }

    #[test]
    fn ssa_name_kind_helpers_classify_prefixed_storage_names() {
        for name in ["tmp:1", "TMP:1", "unique:1", "UNIQUE:1"] {
            assert!(is_temporary_name(name));
            assert!(is_temporary_or_constant_name(name));
            assert!(is_temporary_or_memory_name(name));
            assert!(is_temporary_constant_or_memory_name(name));
            assert!(!is_constant_or_memory_name(name));
            assert!(is_low_signal_ssa_storage_name(name));
        }
        for name in ["const:1", "CONST:1"] {
            assert!(!is_temporary_name(name));
            assert!(is_temporary_or_constant_name(name));
            assert!(!is_temporary_or_memory_name(name));
            assert!(is_temporary_constant_or_memory_name(name));
            assert!(is_constant_or_memory_name(name));
            assert!(is_low_signal_ssa_storage_name(name));
        }
        for name in ["ram:401000", "RAM:401000"] {
            assert!(!is_temporary_or_constant_name(name));
            assert!(is_temporary_or_memory_name(name));
            assert!(is_temporary_constant_or_memory_name(name));
            assert!(is_constant_or_memory_name(name));
            assert!(is_low_signal_ssa_storage_name(name));
        }
        assert!(!is_temporary_or_constant_name("space1:20"));
        assert!(!is_temporary_or_memory_name("space1:20"));
        assert!(!is_temporary_constant_or_memory_name("space1:20"));
        assert!(is_constant_or_memory_name("space1:20"));
        assert!(is_low_signal_ssa_storage_name("space1:20"));

        assert!(!is_temporary_or_memory_name("rax"));
        assert!(!is_temporary_constant_or_memory_name("rax"));
        assert!(!is_constant_or_memory_name("rax"));
        assert!(!is_low_signal_ssa_storage_name("rax"));
    }
}
