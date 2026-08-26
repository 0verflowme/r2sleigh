use super::context::FoldArchConfig;

const X86_REGISTER_LIKE_BASES: &[&str] = &[
    "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "rip", "r8", "r9", "r10", "r11", "r12",
    "r13", "r14", "r15", "eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "esp", "eip", "ax", "bx",
    "cx", "dx", "si", "di", "bp", "sp", "al", "bl", "cl", "dl",
];

// Extension-point tables for future non-x86 behavior.
const ARM_REGISTER_LIKE_BASES: &[&str] = &[
    "sp", "fp", "lr", "pc", "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10",
    "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23",
    "x24", "x25", "x26", "x27", "x28", "x29", "x30", "w0", "w1", "w2", "w3", "w4", "w5", "w6",
    "w7", "w8", "w9", "w10", "w11", "w12", "w13", "w14", "w15", "w16", "w17", "w18", "w19", "w20",
    "w21", "w22", "w23", "w24", "w25", "w26", "w27", "w28", "w29", "w30", "r0", "r1", "r2", "r3",
    "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
];
const MIPS_REGISTER_LIKE_BASES: &[&str] = &[
    "sp", "fp", "ra", "gp", "a0", "a1", "a2", "a3", "v0", "v1", "t0", "t1", "t2", "t3", "t4", "t5",
    "t6", "t7", "t8", "t9",
];

/// The condition codes of the x86 register file, for fixtures that state a target.
///
/// Production derives this from the machine context rather than listing it, and
/// this list exists only so a test fixture can say which target it is about.
#[cfg(test)]
pub(crate) const X86_FLAG_REGISTERS: &[&str] = &[
    "ac", "af", "c0", "c1", "c2", "c3", "cf", "df", "id", "if", "iopl", "nt", "of", "pf", "rf",
    "sf", "tf", "vif", "vip", "vm", "zf",
];

fn normalized_base_name(name: &str) -> String {
    let lower = name.to_ascii_lowercase();
    let no_reg = lower.strip_prefix("reg:").unwrap_or(lower.as_str());
    let base = no_reg.split('_').next().unwrap_or(no_reg);
    base.to_string()
}

fn canonical_x86_arg_reg(base: &str) -> &str {
    match base {
        "edi" | "di" | "dil" => "rdi",
        "esi" | "si" | "sil" => "rsi",
        "edx" | "dx" | "dl" => "rdx",
        "ecx" | "cx" | "cl" => "rcx",
        "r8d" | "r8w" | "r8b" => "r8",
        "r9d" | "r9w" | "r9b" => "r9",
        "w0" => "x0",
        "w1" => "x1",
        "w2" => "x2",
        "w3" => "x3",
        "w4" => "x4",
        "w5" => "x5",
        "w6" => "x6",
        "w7" => "x7",
        "w8" => "x8",
        "w9" => "x9",
        "w10" => "x10",
        "w11" => "x11",
        "w12" => "x12",
        "w13" => "x13",
        "w14" => "x14",
        "w15" => "x15",
        "w16" => "x16",
        "w17" => "x17",
        other => other,
    }
}

impl FoldArchConfig {
    /// Whether this name spells a condition code on this target.
    pub(crate) fn is_flag_name(&self, name: &str) -> bool {
        self.flag_regs.contains(&crate::analysis::utils::flag_base_name(name))
    }

    pub(crate) fn is_stack_pointer_name(&self, name: &str) -> bool {
        let base = normalized_base_name(name);
        base == self.sp_name
            || matches!(base.as_str(), "rsp" | "esp" | "sp" | "x31" | "r13" | "$sp")
    }

    pub(crate) fn is_frame_pointer_name(&self, name: &str) -> bool {
        let base = normalized_base_name(name);
        base == self.fp_name || matches!(base.as_str(), "rbp" | "ebp" | "fp" | "x29" | "$fp")
    }

    pub(crate) fn is_stack_base_name(&self, name: &str) -> bool {
        self.is_stack_pointer_name(name) || self.is_frame_pointer_name(name)
    }

    pub(crate) fn is_register_like_base_name(&self, name: &str) -> bool {
        let base = normalized_base_name(name);
        if X86_REGISTER_LIKE_BASES.contains(&base.as_str())
            || ARM_REGISTER_LIKE_BASES.contains(&base.as_str())
            || MIPS_REGISTER_LIKE_BASES.contains(&base.as_str())
        {
            return true;
        }

        for prefix in ["xmm", "ymm", "zmm", "mm", "st"] {
            if let Some(rest) = base.strip_prefix(prefix)
                && !rest.is_empty()
                && rest.chars().all(|ch| ch.is_ascii_digit())
            {
                return true;
            }
        }

        false
    }

    pub(crate) fn is_return_register_name(&self, name: &str) -> bool {
        let base = normalized_base_name(name);

        if base == self.ret_reg_name || base == canonical_x86_arg_reg(&self.ret_reg_name) {
            return true;
        }

        if matches!(base.as_str(), "xmm0" | "st0") {
            return true;
        }

        match self.ptr_size {
            64 => matches!(base.as_str(), "rax" | "eax" | "ax" | "al"),
            _ => matches!(base.as_str(), "eax" | "ax" | "al"),
        }
    }
}
