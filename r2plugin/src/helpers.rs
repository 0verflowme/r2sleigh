use crate::ArchSpec;
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

pub(crate) fn normalize_sim_name(name: &str) -> Option<&'static str> {
    let normalized_owned = name.trim().to_ascii_lowercase();
    let mut normalized = normalized_owned.as_str();

    for prefix in ["sym.imp.", "sym.", "imp.", "reloc.", "dbg."] {
        while let Some(rest) = normalized.strip_prefix(prefix) {
            normalized = rest;
        }
    }

    while let Some(rest) = normalized.strip_suffix("@plt") {
        normalized = rest;
    }
    while let Some(rest) = normalized.strip_suffix(".plt") {
        normalized = rest;
    }
    if let Some((base, _)) = normalized.split_once('@') {
        normalized = base;
    }

    if let Some(rest) = normalized.strip_prefix("__isoc99_") {
        normalized = rest;
    }
    if let Some(rest) = normalized.strip_prefix("__gi_") {
        normalized = rest;
    }

    match normalized {
        "strlen" | "__strlen_chk" => Some("strlen"),
        "strcmp" => Some("strcmp"),
        "memcmp" => Some("memcmp"),
        "memcpy" | "__memcpy_chk" => Some("memcpy"),
        "memset" => Some("memset"),
        "malloc" | "__libc_malloc" | "__gi___libc_malloc" => Some("malloc"),
        "free" => Some("free"),
        "puts" => Some("puts"),
        "printf" | "__printf_chk" => Some("printf"),
        "exit" | "_exit" => Some("exit"),
        _ => {
            if normalized.starts_with("strlen") {
                Some("strlen")
            } else if normalized.starts_with("strcmp") {
                Some("strcmp")
            } else if normalized.starts_with("memcmp") {
                Some("memcmp")
            } else if normalized.starts_with("memcpy") {
                Some("memcpy")
            } else if normalized.starts_with("memset") {
                Some("memset")
            } else if normalized.starts_with("printf") || normalized == "__printf_chk" {
                Some("printf")
            } else if normalized.starts_with("puts") {
                Some("puts")
            } else if normalized == "malloc" || normalized.ends_with("malloc") {
                Some("malloc")
            } else if normalized == "free" || normalized.ends_with("free") {
                Some("free")
            } else if normalized.starts_with("exit") {
                Some("exit")
            } else {
                None
            }
        }
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
