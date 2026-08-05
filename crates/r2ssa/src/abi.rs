//! Canonical calling-convention register facts used by SSA analyses.

use std::collections::{BTreeMap, BTreeSet};

use r2il::ArchSpec;

use crate::SSAVar;

#[derive(Debug, Clone)]
struct AbiSlot {
    size: u32,
}

/// Architecture calling-convention profile shared by SSA fact producers.
#[derive(Debug, Clone, Default)]
pub struct AbiProfile {
    args: Vec<AbiSlot>,
    ret_aliases: BTreeSet<String>,
    alias_to_arg: BTreeMap<String, usize>,
    alias_is_ret: BTreeSet<String>,
}

impl AbiProfile {
    pub fn from_arch(arch: Option<&ArchSpec>) -> Self {
        let Some(arch) = arch else {
            return Self::default();
        };
        let lower = arch.name.to_ascii_lowercase();
        match lower.as_str() {
            "x86-64" | "x86_64" | "x64" | "amd64" => Self::new(
                vec![
                    ("rdi", 8, &["edi", "di", "dil"][..]),
                    ("rsi", 8, &["esi", "si", "sil"][..]),
                    ("rdx", 8, &["edx", "dx", "dl"][..]),
                    ("rcx", 8, &["ecx", "cx", "cl"][..]),
                    ("r8", 8, &["r8d", "r8w", "r8b"][..]),
                    ("r9", 8, &["r9d", "r9w", "r9b"][..]),
                ],
                &[("rax", &["eax", "ax", "al"][..])],
            ),
            name if name.starts_with("x86:")
                && (arch.addr_size == 8 || name.split(':').any(|part| part == "64")) =>
            {
                Self::new(
                    vec![
                        ("rdi", 8, &["edi", "di", "dil"][..]),
                        ("rsi", 8, &["esi", "si", "sil"][..]),
                        ("rdx", 8, &["edx", "dx", "dl"][..]),
                        ("rcx", 8, &["ecx", "cx", "cl"][..]),
                        ("r8", 8, &["r8d", "r8w", "r8b"][..]),
                        ("r9", 8, &["r9d", "r9w", "r9b"][..]),
                    ],
                    &[("rax", &["eax", "ax", "al"][..])],
                )
            }
            name if name.starts_with("x86:") => {
                Self::new(Vec::new(), &[("eax", &["ax", "al"][..])])
            }
            "x86" | "x86-32" | "i386" | "i686" => {
                Self::new(Vec::new(), &[("eax", &["ax", "al"][..])])
            }
            "arm" if arch.addr_size == 4 => Self::new(
                vec![
                    ("r0", 4, &[]),
                    ("r1", 4, &[]),
                    ("r2", 4, &[]),
                    ("r3", 4, &[]),
                ],
                &[("r0", &[])],
            ),
            "aarch64" | "arm64" => Self::new(
                vec![
                    ("x0", 8, &["w0"][..]),
                    ("x1", 8, &["w1"][..]),
                    ("x2", 8, &["w2"][..]),
                    ("x3", 8, &["w3"][..]),
                    ("x4", 8, &["w4"][..]),
                    ("x5", 8, &["w5"][..]),
                    ("x6", 8, &["w6"][..]),
                    ("x7", 8, &["w7"][..]),
                ],
                &[("x0", &["w0"][..])],
            ),
            name if name.starts_with("aarch64:") || name.starts_with("arm64:") => Self::new(
                vec![
                    ("x0", 8, &["w0"][..]),
                    ("x1", 8, &["w1"][..]),
                    ("x2", 8, &["w2"][..]),
                    ("x3", 8, &["w3"][..]),
                    ("x4", 8, &["w4"][..]),
                    ("x5", 8, &["w5"][..]),
                    ("x6", 8, &["w6"][..]),
                    ("x7", 8, &["w7"][..]),
                ],
                &[("x0", &["w0"][..])],
            ),
            "riscv32" | "riscv" if arch.addr_size == 4 => Self::new(
                vec![
                    ("a0", 4, &["x10"][..]),
                    ("a1", 4, &["x11"][..]),
                    ("a2", 4, &["x12"][..]),
                    ("a3", 4, &["x13"][..]),
                    ("a4", 4, &["x14"][..]),
                    ("a5", 4, &["x15"][..]),
                    ("a6", 4, &["x16"][..]),
                    ("a7", 4, &["x17"][..]),
                ],
                &[("a0", &["x10"][..])],
            ),
            "riscv64" | "riscv" => Self::new(
                vec![
                    ("a0", 8, &["x10"][..]),
                    ("a1", 8, &["x11"][..]),
                    ("a2", 8, &["x12"][..]),
                    ("a3", 8, &["x13"][..]),
                    ("a4", 8, &["x14"][..]),
                    ("a5", 8, &["x15"][..]),
                    ("a6", 8, &["x16"][..]),
                    ("a7", 8, &["x17"][..]),
                ],
                &[("a0", &["x10"][..])],
            ),
            _ => Self::default(),
        }
    }

    pub fn windows_x64() -> Self {
        Self::new(
            vec![
                ("rcx", 8, &["ecx", "cx", "cl"][..]),
                ("rdx", 8, &["edx", "dx", "dl"][..]),
                ("r8", 8, &["r8d", "r8w", "r8b"][..]),
                ("r9", 8, &["r9d", "r9w", "r9b"][..]),
            ],
            &[("rax", &["eax", "ax", "al"][..])],
        )
    }

    fn new(
        args: Vec<(&'static str, u32, &'static [&'static str])>,
        rets: &[(&'static str, &'static [&'static str])],
    ) -> Self {
        let mut out = Self::default();
        for (index, (primary, size, aliases)) in args.into_iter().enumerate() {
            out.args.push(AbiSlot { size });
            out.alias_to_arg.insert(primary.to_string(), index);
            for alias in aliases {
                out.alias_to_arg.insert((*alias).to_string(), index);
            }
        }
        for (primary, aliases) in rets {
            out.ret_aliases.insert((*primary).to_string());
            out.alias_is_ret.insert((*primary).to_string());
            for alias in *aliases {
                out.ret_aliases.insert((*alias).to_string());
                out.alias_is_ret.insert((*alias).to_string());
            }
        }
        out
    }

    pub fn argument_index(&self, name: &str) -> Option<usize> {
        self.alias_to_arg.get(&name.to_ascii_lowercase()).copied()
    }

    pub fn formal_argument_index(&self, var: &SSAVar) -> Option<usize> {
        (var.version == 0)
            .then(|| self.argument_index(&var.name))
            .flatten()
    }

    pub fn formal_address_argument_index(&self, var: &SSAVar) -> Option<usize> {
        let index = self.formal_argument_index(var)?;
        let slot = self.args.get(index)?;
        (var.size == slot.size).then_some(index)
    }

    pub fn is_return_register(&self, name: &str) -> bool {
        self.alias_is_ret.contains(&name.to_ascii_lowercase())
    }

    pub fn argument_count(&self) -> usize {
        self.args.len()
    }
}
