#[cfg(test)]
use std::collections::HashMap;

#[cfg(test)]
use r2ssa::SSAVar;
use r2ssa::SSAVarNameKind;

#[cfg(test)]
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
#[cfg(test)]
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
#[cfg(test)]
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

#[cfg(test)]
pub(crate) fn is_temporary_name(name: &str) -> bool {
    ssa_name_kind(name).is_temporary()
}

#[cfg(test)]
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

#[cfg(test)]
pub(crate) fn is_constant_or_memory_name(name: &str) -> bool {
    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Constant | SSAVarNameKind::Memory | SSAVarNameKind::AddressSpace
    )
}

#[cfg(test)]
pub(crate) fn is_low_signal_ssa_storage_name(name: &str) -> bool {
    matches!(
        ssa_name_kind(name),
        SSAVarNameKind::Temporary
            | SSAVarNameKind::Constant
            | SSAVarNameKind::Memory
            | SSAVarNameKind::AddressSpace
    )
}

#[cfg(test)]
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

#[cfg(test)]
fn is_hex_name(value: &str) -> bool {
    !value.is_empty() && value.chars().all(|c| c.is_ascii_hexdigit())
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2ssa::SSAVar;

    #[test]
    fn parse_const_value_uses_ssa_hex_payload_by_default() {
        assert_eq!(parse_const_value("const:100"), Some(0x100));
        assert_eq!(parse_const_value("const:0x100"), Some(0x100));
        assert_eq!(parse_const_value("const:0d100"), Some(100));
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
        assert_eq!(
            format_traced_name("const:2a_0", &HashMap::new()),
            "const:2a"
        );
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
            assert!(is_temporary_or_memory_name(name));
            assert!(is_temporary_constant_or_memory_name(name));
            assert!(!is_constant_or_memory_name(name));
            assert!(is_low_signal_ssa_storage_name(name));
        }
        for name in ["const:1", "CONST:1"] {
            assert!(!is_temporary_name(name));
            assert!(!is_temporary_or_memory_name(name));
            assert!(is_temporary_constant_or_memory_name(name));
            assert!(is_constant_or_memory_name(name));
            assert!(is_low_signal_ssa_storage_name(name));
        }
        for name in ["ram:401000", "RAM:401000"] {
            assert!(is_temporary_or_memory_name(name));
            assert!(is_temporary_constant_or_memory_name(name));
            assert!(is_constant_or_memory_name(name));
            assert!(is_low_signal_ssa_storage_name(name));
        }
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
