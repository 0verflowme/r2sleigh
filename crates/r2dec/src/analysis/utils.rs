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
