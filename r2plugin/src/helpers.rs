use crate::ArchSpec;
use std::collections::HashMap;
use std::ffi::CStr;
use std::os::raw::c_char;

pub(crate) fn resolve_function_name(fcn_addr: u64, fcn_name: *const c_char) -> String {
    let raw_name = if fcn_name.is_null() {
        if fcn_addr == 0 {
            "func".to_string()
        } else {
            format!("fcn_{fcn_addr:x}")
        }
    } else {
        unsafe { CStr::from_ptr(fcn_name).to_string_lossy().to_string() }
    };

    if raw_name.trim().is_empty() {
        if fcn_addr == 0 {
            "func".to_string()
        } else {
            format!("fcn_{fcn_addr:x}")
        }
    } else {
        raw_name
    }
}

pub(crate) fn cstr_or_default(ptr: *const c_char, default: &str) -> String {
    if ptr.is_null() {
        return default.to_string();
    }
    unsafe { CStr::from_ptr(ptr).to_string_lossy().to_string() }
}

fn strip_display_name_prefixes(name: &str) -> &str {
    let mut normalized = name.trim();
    for prefix in ["sym.imp.", "sym.", "imp.", "reloc.", "dbg.", "fcn."] {
        while let Some(rest) = normalized.strip_prefix(prefix) {
            normalized = rest;
        }
    }
    normalized
}

fn sanitize_c_identifier(name: &str) -> Option<String> {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return None;
    }

    let mut out = String::new();
    for (idx, ch) in trimmed.chars().enumerate() {
        let normalized = if ch.is_ascii_alphanumeric() || ch == '_' {
            ch
        } else {
            '_'
        };
        if idx == 0 && normalized.is_ascii_digit() {
            out.push('_');
        }
        out.push(normalized);
    }

    if out.chars().all(|c| c == '_') {
        None
    } else {
        Some(out)
    }
}

pub(crate) fn resolve_decompiler_display_name(
    fcn_addr: u64,
    raw_name: &str,
    function_names: &HashMap<u64, String>,
    symbols: &HashMap<u64, String>,
) -> String {
    for candidate in [
        symbols.get(&fcn_addr).map(String::as_str),
        function_names.get(&fcn_addr).map(String::as_str),
        Some(raw_name),
    ] {
        let Some(candidate) = candidate else {
            continue;
        };
        let stripped = strip_display_name_prefixes(candidate);
        if let Some(clean) = sanitize_c_identifier(stripped) {
            return clean;
        }
    }

    if fcn_addr == 0 {
        "func".to_string()
    } else {
        format!("sub_{fcn_addr:x}")
    }
}

pub(crate) fn effective_addr_size_bytes(arch: &ArchSpec) -> u32 {
    if arch.addr_size > 1 {
        return arch.addr_size;
    }

    if let Some(pc_size) = arch
        .registers
        .iter()
        .find(|reg| {
            matches!(
                reg.name.to_ascii_lowercase().as_str(),
                "pc" | "ip" | "eip" | "rip"
            )
        })
        .map(|reg| reg.size)
        .filter(|size| *size > 1)
    {
        return pc_size;
    }

    if let Some(default_size) = arch
        .spaces
        .iter()
        .find(|space| space.is_default && space.addr_size > 1)
        .map(|space| space.addr_size)
    {
        return default_size;
    }

    arch.spaces
        .iter()
        .map(|space| space.addr_size)
        .max()
        .filter(|size| *size > 1)
        .unwrap_or(arch.addr_size.max(1))
}

pub(crate) fn effective_ptr_bits(arch: &ArchSpec) -> u32 {
    effective_addr_size_bytes(arch).saturating_mul(8)
}

#[cfg(test)]
mod tests {
    use super::resolve_decompiler_display_name;
    use std::collections::HashMap;

    #[test]
    fn decompiler_display_name_prefers_symbol_name() {
        let function_names = HashMap::from([(0x401617, "dbg.test_symbolic_xor_guard".to_string())]);
        let symbols = HashMap::from([(0x401617, "test_symbolic_xor_guard".to_string())]);

        let display = resolve_decompiler_display_name(
            0x401617,
            "dbg.test_symbolic_xor_guard",
            &function_names,
            &symbols,
        );

        assert_eq!(display, "test_symbolic_xor_guard");
    }

    #[test]
    fn decompiler_display_name_strips_debug_prefix_without_symbol_hint() {
        let display = resolve_decompiler_display_name(
            0x401617,
            "dbg.test_symbolic_xor_guard",
            &HashMap::new(),
            &HashMap::new(),
        );

        assert_eq!(display, "test_symbolic_xor_guard");
    }
}
