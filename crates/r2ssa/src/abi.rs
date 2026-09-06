//! Canonical calling-convention register facts used by SSA analyses.

#[cfg(test)]
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use r2il::ArchSpec;

use crate::machine_context::SourceMachineContext;
use crate::{CanonicalStorageId, CanonicalStorageSpace, MachineArchitectureFamily};

#[derive(Debug, Clone)]
struct AbiSlot {
    storage: Option<CanonicalStorageId>,
}

/// Architecture calling-convention profile shared by SSA fact producers.
#[derive(Debug, Clone, Default)]
pub struct AbiProfile {
    args: Vec<AbiSlot>,
    #[cfg(test)]
    alias_to_arg: BTreeMap<String, usize>,
    #[cfg(test)]
    alias_is_ret: BTreeSet<String>,
    source_owned: bool,
}

impl AbiProfile {
    pub(crate) fn from_machine_context(context: &SourceMachineContext) -> Option<Self> {
        let memory = context.memory_model();
        let abi = context.abi_model();
        if !memory.is_available()
            || !memory.is_coherent()
            || !abi.is_available()
            || !abi.is_coherent()
        {
            return None;
        }
        let arguments = abi
            .argument_registers()
            .iter()
            .map(|slot| (slot.index(), slot.storage()))
            .collect::<Vec<_>>();
        let returns = abi
            .return_registers()
            .iter()
            .map(|slot| slot.storage())
            .collect::<Vec<_>>();
        Self::from_canonical_storage_model(
            context.architecture_family(),
            memory.default_address_bits(),
            &arguments,
            &returns,
        )
    }

    fn from_canonical_storage_model(
        architecture_family: MachineArchitectureFamily,
        address_bits: u32,
        argument_registers: &[(u32, CanonicalStorageId)],
        return_registers: &[CanonicalStorageId],
    ) -> Option<Self> {
        let expected_bits = match architecture_family {
            MachineArchitectureFamily::X86
            | MachineArchitectureFamily::Arm
            | MachineArchitectureFamily::RiscV32
            | MachineArchitectureFamily::Mips32
            | MachineArchitectureFamily::PowerPc32 => 32,
            MachineArchitectureFamily::X86_64
            | MachineArchitectureFamily::AArch64
            | MachineArchitectureFamily::RiscV64
            | MachineArchitectureFamily::Mips64
            | MachineArchitectureFamily::PowerPc64 => 64,
            MachineArchitectureFamily::Unknown => return None,
        };
        if address_bits != expected_bits {
            return None;
        }

        let mut arguments = argument_registers.to_vec();
        arguments.sort_by_key(|(index, _)| *index);
        if arguments
            .iter()
            .enumerate()
            .any(|(expected, (index, _))| *index as usize != expected)
        {
            return None;
        }
        let mut out = Self {
            source_owned: true,
            ..Self::default()
        };
        let mut argument_storages = BTreeSet::new();
        for (_, storage) in arguments {
            if storage.space != CanonicalStorageSpace::Register
                || storage.size == 0
                || !argument_storages.insert(storage)
            {
                return None;
            }
            out.args.push(AbiSlot {
                storage: Some(storage),
            });
        }

        for &storage in return_registers {
            if storage.space != CanonicalStorageSpace::Register || storage.size == 0 {
                return None;
            }
        }
        Some(out)
    }

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
        _rets: &[(&'static str, &'static [&'static str])],
    ) -> Self {
        let mut out = Self::default();
        for (_primary, _size, _aliases) in args {
            #[cfg(test)]
            let index = out.args.len();
            out.args.push(AbiSlot { storage: None });
            #[cfg(test)]
            {
                out.alias_to_arg.insert(_primary.to_string(), index);
                for alias in _aliases {
                    out.alias_to_arg.insert((*alias).to_string(), index);
                }
            }
        }
        #[cfg(test)]
        for (primary, aliases) in _rets {
            out.alias_is_ret.insert((*primary).to_string());
            for alias in *aliases {
                out.alias_is_ret.insert((*alias).to_string());
            }
        }
        out
    }

    #[cfg(test)]
    pub(crate) fn argument_index(&self, name: &str) -> Option<usize> {
        self.alias_to_arg.get(&name.to_ascii_lowercase()).copied()
    }

    pub(crate) fn exact_argument_index_for_storage(
        &self,
        storage: CanonicalStorageId,
    ) -> Option<usize> {
        self.args
            .iter()
            .position(|slot| slot.storage == Some(storage))
    }

    pub(crate) const fn is_source_owned(&self) -> bool {
        self.source_owned
    }

    #[cfg(test)]
    pub(crate) fn is_return_register(&self, name: &str) -> bool {
        self.alias_is_ret.contains(&name.to_ascii_lowercase())
    }

    pub fn argument_count(&self) -> usize {
        self.args.len()
    }
}

#[cfg(test)]
mod tests {
    use r2il::{AddressSpace, RegisterDef};

    use super::*;
    use crate::machine_context::{
        SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn, SourceMachineRoles,
    };

    const ARGUMENT: CanonicalStorageId = register_storage(0, 8);
    const RETURNED: CanonicalStorageId = register_storage(8, 8);
    const STACK_POINTER: CanonicalStorageId = register_storage(16, 8);
    const RETURN_ADDRESS: CanonicalStorageId = register_storage(24, 8);

    const fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn exact_context(argument_names: &[&str], return_names: &[&str]) -> SourceMachineContext {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_space(AddressSpace::ram(8));
        for name in argument_names {
            arch.add_register(RegisterDef::new(*name, ARGUMENT.offset, ARGUMENT.size));
        }
        for name in return_names {
            arch.add_register(RegisterDef::new(*name, RETURNED.offset, RETURNED.size));
        }
        arch.add_register(RegisterDef::new(
            "source_sp",
            STACK_POINTER.offset,
            STACK_POINTER.size,
        ));
        arch.add_register(RegisterDef::new(
            "source_ra",
            RETURN_ADDRESS.offset,
            RETURN_ADDRESS.size,
        ));
        arch.return_registers = vec![RegisterDef::new(
            return_names[0],
            RETURNED.offset,
            RETURNED.size,
        )];
        let interface = SourceFunctionInterface::new_exact(
            b"abi-storage-only-test".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, ARGUMENT)],
            SourceFunctionReturn::Register { storage: RETURNED },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(RETURN_ADDRESS))
        .and_then(|interface| interface.with_stack_pointer_storage(STACK_POINTER))
        .expect("exact interface");
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(interface),
            SourceMachineRoles::default(),
            None,
            Vec::new(),
        );
        assert!(context.abi_model().is_coherent());
        context
    }

    #[test]
    fn exact_storage_model_requires_no_presentation_aliases() {
        let profile = AbiProfile::from_canonical_storage_model(
            MachineArchitectureFamily::X86_64,
            64,
            &[(0, ARGUMENT)],
            &[RETURNED],
        )
        .expect("canonical storage is sufficient");

        assert!(profile.is_source_owned());
        assert_eq!(profile.argument_count(), 1);
        assert_eq!(profile.exact_argument_index_for_storage(ARGUMENT), Some(0));
        assert!(profile.alias_to_arg.is_empty());
        assert!(profile.alias_is_ret.is_empty());
    }

    #[test]
    fn exact_machine_profile_ignores_multiple_presentation_aliases() {
        let context = exact_context(
            &["argument", "argument_alias", "another_argument_alias"],
            &["result", "result_alias"],
        );
        let profile = AbiProfile::from_machine_context(&context)
            .expect("presentation alias count does not affect exact ABI storage");

        assert_eq!(profile.exact_argument_index_for_storage(ARGUMENT), Some(0));
        assert!(profile.alias_to_arg.is_empty());
        assert!(profile.alias_is_ret.is_empty());
    }

    #[test]
    fn exact_machine_profile_ignores_renamed_presentation_aliases() {
        let first =
            AbiProfile::from_machine_context(&exact_context(&["first_arg"], &["first_ret"]))
                .expect("first spelling set");
        let renamed = AbiProfile::from_machine_context(&exact_context(
            &["completely_renamed_arg"],
            &["completely_renamed_ret"],
        ))
        .expect("renamed spelling set");

        for profile in [&first, &renamed] {
            assert!(profile.is_source_owned());
            assert_eq!(profile.argument_count(), 1);
            assert_eq!(profile.exact_argument_index_for_storage(ARGUMENT), Some(0));
            assert!(profile.alias_to_arg.is_empty());
            assert!(profile.alias_is_ret.is_empty());
        }
    }
}
