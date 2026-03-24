pub(crate) fn register_family_name(name: &str) -> Option<String> {
    let lower = name.to_ascii_lowercase();
    let base = lower
        .rsplit_once('_')
        .map(|(base, _)| base.to_string())
        .unwrap_or(lower);

    x86_register_family_name(&base).or_else(|| numbered_register_family_name(&base))
}

fn numbered_register_family_name(name: &str) -> Option<String> {
    let rest = name
        .strip_prefix('x')
        .or_else(|| name.strip_prefix('w'))
        .or_else(|| name.strip_prefix('r'))
        .or_else(|| name.strip_prefix('e'))?;
    (!rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_digit())).then(|| rest.to_string())
}

fn x86_register_family_name(name: &str) -> Option<String> {
    match name {
        "rax" | "eax" | "ax" | "al" | "ah" => Some("ax".to_string()),
        "rbx" | "ebx" | "bx" | "bl" | "bh" => Some("bx".to_string()),
        "rcx" | "ecx" | "cx" | "cl" | "ch" => Some("cx".to_string()),
        "rdx" | "edx" | "dx" | "dl" | "dh" => Some("dx".to_string()),
        "rsi" | "esi" | "sil" => Some("si".to_string()),
        "rdi" | "edi" | "dil" => Some("di".to_string()),
        _ => {
            let rest = name.strip_prefix('r')?;
            let digits = rest.trim_end_matches(['b', 'w', 'd']);
            (!digits.is_empty() && digits.chars().all(|ch| ch.is_ascii_digit()))
                .then(|| digits.to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::register_family_name;

    #[test]
    fn x86_aliases_share_a_family() {
        for name in ["rax", "eax", "ax", "al", "ah"] {
            assert_eq!(register_family_name(name).as_deref(), Some("ax"));
        }
        for name in ["r8", "r8d", "r8w", "r8b"] {
            assert_eq!(register_family_name(name).as_deref(), Some("8"));
        }
    }

    #[test]
    fn arm_numeric_aliases_still_share_a_family() {
        for name in ["x0", "w0", "x12", "w12"] {
            let expected = name.trim_start_matches(['x', 'w']);
            assert_eq!(register_family_name(name).as_deref(), Some(expected));
        }
    }
}
