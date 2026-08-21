//! Address parsing helpers shared across decompiler stages.

/// Parse an address from a var name such as:
/// - `const:0x403000`
/// - `const:403000`
/// - `const:42` (SSA payloads are hex by default)
/// - `ram:403000`
/// - `ram:403000_0`
pub(crate) fn parse_address_from_var_name(name: &str) -> Option<u64> {

    if let Some(rest) = name.strip_prefix("ram:") {
        let addr_str = rest.split('_').next().unwrap_or(rest);
        let addr_hex = addr_str
            .strip_prefix("0x")
            .or_else(|| addr_str.strip_prefix("0X"))
            .unwrap_or(addr_str);
        return u64::from_str_radix(addr_hex, 16).ok();
    }

    let rest = name.strip_prefix("const:")?;
    let value = rest.split('_').next().unwrap_or(rest);

    if let Some(hex) = value
        .strip_prefix("0x")
        .or_else(|| value.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }

    if value.chars().all(|c| c.is_ascii_hexdigit()) {
        return u64::from_str_radix(value, 16).ok();
    }

    value.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_const_addresses() {
        assert_eq!(
            parse_address_from_var_name("const:0x403000"),
            Some(0x403000)
        );
        assert_eq!(parse_address_from_var_name("const:403000"), Some(0x403000));
        assert_eq!(parse_address_from_var_name("const:42"), Some(0x42));
        assert_eq!(parse_address_from_var_name("const:0x42_0"), Some(0x42));
    }

    #[test]
    fn parses_ram_addresses() {
        assert_eq!(parse_address_from_var_name("ram:403000"), Some(0x403000));
        assert_eq!(parse_address_from_var_name("ram:403000_0"), Some(0x403000));
        assert_eq!(
            parse_address_from_var_name("ram:0x403000_1"),
            Some(0x403000)
        );
    }

    #[test]
    fn rejects_unknown_prefixes() {
        assert_eq!(parse_address_from_var_name("reg:rax"), None);
        assert_eq!(parse_address_from_var_name("tmp:1000"), None);
    }
}
