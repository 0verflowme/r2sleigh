use std::collections::{BTreeMap, HashSet};

use r2il::ArchSpec;
use r2ssa::{CanonicalStorageId, ObjectKind, SSAVar, SourceAbiClass, SsaArtifact};

use crate::memory::MemoryRegionKind;
use crate::sim::CallConv;
use crate::state::SymState;

struct ArchSeedProfile {
    arg_regs: &'static [&'static str],
    stack_regs: &'static [&'static str],
    stack_value: u64,
}

fn arch_seed_profile(arch: &ArchSpec) -> Option<ArchSeedProfile> {
    let arch_name = arch.name.to_ascii_lowercase();
    let looks_riscv = arch_name.contains("riscv") || arch_name.starts_with("rv");
    if arch_name == "x86-64" || arch_name == "x86_64" || (arch_name == "x86" && arch.addr_size == 8)
    {
        Some(ArchSeedProfile {
            arg_regs: &[
                "RDI", "RSI", "RDX", "RCX", "R8", "R9", "EDI", "ESI", "EDX", "ECX", "R8D", "R9D",
            ],
            stack_regs: &["RSP", "RBP"],
            stack_value: 0x7fff_ffff_0000u64,
        })
    } else if arch_name == "x86" {
        Some(ArchSeedProfile {
            arg_regs: &["EAX", "EBX", "ECX", "EDX", "ESI", "EDI"],
            stack_regs: &["ESP", "EBP"],
            stack_value: 0x7fff_0000u64,
        })
    } else if looks_riscv && (arch.addr_size == 8 || arch_name.contains("64")) {
        Some(ArchSeedProfile {
            arg_regs: &[
                "A0", "A1", "A2", "A3", "A4", "A5", "A6", "A7", "X10", "X11", "X12", "X13", "X14",
                "X15", "X16", "X17",
            ],
            stack_regs: &["SP", "S0", "FP", "X2", "X8"],
            stack_value: 0x7fff_ffff_0000u64,
        })
    } else if looks_riscv {
        Some(ArchSeedProfile {
            arg_regs: &[
                "A0", "A1", "A2", "A3", "A4", "A5", "A6", "A7", "X10", "X11", "X12", "X13", "X14",
                "X15", "X16", "X17",
            ],
            stack_regs: &["SP", "S0", "FP", "X2", "X8"],
            stack_value: 0x7fff_0000u64,
        })
    } else {
        None
    }
}

/// Explicit advisory seed mode for callers that have only an architecture
/// profile. Exact prepared workflows use [`seed_default_state_for_prepared`].
pub fn seed_default_state_for_arch<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    arch: Option<&ArchSpec>,
) {
    let Some(profile) = arch.and_then(arch_seed_profile) else {
        return;
    };

    let mut seen = HashSet::new();
    let mut maybe_seed = |var: &SSAVar| {
        if !var.is_register() || var.version != 0 {
            return;
        }

        let base_name = var.name.strip_prefix("reg:").unwrap_or(&var.name);
        let base = base_name.to_ascii_uppercase();
        let reg_name = var.display_name();
        if !seen.insert(reg_name.clone()) {
            return;
        }

        let bits = var.size * 8;
        if profile.stack_regs.contains(&base.as_str()) {
            state.set_concrete(&reg_name, profile.stack_value, bits);
            return;
        }

        if profile.arg_regs.contains(&base.as_str()) {
            let sym_name = base_name.to_ascii_lowercase();
            state.make_symbolic_named(&reg_name, &sym_name, bits);
        }
    };

    for block in prepared.blocks() {
        block.for_each_def(|def| maybe_seed(def.var));
        block.for_each_source(|src| maybe_seed(src.var));
    }

    seed_memory_regions_for_arch(state, prepared, arch);
}

fn exact_version_zero_registers_for_storage(
    prepared: &SsaArtifact,
    storage: CanonicalStorageId,
) -> BTreeMap<String, u32> {
    let mut registers = BTreeMap::new();
    let mut record = |var: &SSAVar| {
        if var.is_register()
            && var.version == 0
            && prepared.graph().canonical_storage_for_var(var) == Some(storage)
        {
            registers
                .entry(var.display_name())
                .or_insert(var.size.saturating_mul(8));
        }
    };
    for block in prepared.blocks() {
        block.for_each_def(|def| record(def.var));
        block.for_each_source(|src| record(src.var));
    }
    registers
}

fn exact_stack_value(prepared: &SsaArtifact) -> Option<u64> {
    let memory = prepared.machine_context().memory_model();
    if !memory.is_available() || !memory.is_coherent() {
        return None;
    }
    match memory.default_address_bits() {
        32 => Some(0x7fff_0000),
        64 => Some(0x7fff_ffff_0000),
        _ => None,
    }
}

/// Seed initial registers from the exact ABI and canonical machine roles of
/// one prepared artifact. Missing typed facts refuse seeding; this path never
/// falls back to architecture or register-name classification.
pub fn seed_default_state_for_prepared<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
) -> bool {
    if prepared.machine_context().effective_abi_class() == SourceAbiClass::Unknown {
        return false;
    }
    let Some(callconv) = CallConv::for_prepared(prepared) else {
        return false;
    };

    for index in 0..callconv.arg_capacity() {
        let Some(storage) = callconv.argument_storage(index) else {
            return false;
        };
        for (key, bits) in exact_version_zero_registers_for_storage(prepared, storage) {
            state.make_symbolic_named(&key, &format!("arg_{index}"), bits);
        }
    }

    if let (Some(stack_pointer), Some(stack_value)) = (
        prepared.machine_context().stack_pointer_carrier(),
        exact_stack_value(prepared),
    ) {
        for (key, bits) in exact_version_zero_registers_for_storage(prepared, stack_pointer) {
            state.set_concrete(&key, stack_value, bits);
        }
    }
    seed_memory_regions_for_prepared(state, prepared);
    true
}

const STACK_WINDOW_BELOW: u64 = 0x8000;
const STACK_WINDOW_SIZE: u64 = 0x10000;
const GLOBAL_TAIL_EXTENT: u64 = 0x1000;

/// Explicit advisory memory seed mode for architecture-only callers.
pub fn seed_memory_regions_for_arch<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    arch: Option<&ArchSpec>,
) {
    let stack_value = arch
        .and_then(arch_seed_profile)
        .map(|profile| profile.stack_value)
        .unwrap_or(0);
    let has_stack_objects = prepared.objects().objects.values().any(|object| {
        matches!(
            object.kind,
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. }
        )
    });
    if has_stack_objects && stack_value != 0 {
        let stack_base = stack_value.saturating_sub(STACK_WINDOW_BELOW);
        state.define_memory_region(
            MemoryRegionKind::Stack,
            "stack_window",
            Some(stack_base),
            Some(STACK_WINDOW_SIZE),
        );
    }

    let mut globals = prepared
        .objects()
        .objects
        .values()
        .filter_map(|object| match &object.kind {
            ObjectKind::Global { address, .. } => Some(*address),
            _ => None,
        })
        .collect::<Vec<_>>();
    globals.sort_unstable();
    globals.dedup();

    for (index, address) in globals.iter().copied().enumerate() {
        let next = globals.get(index + 1).copied();
        let extent = next
            .and_then(|next| next.checked_sub(address))
            .filter(|extent| *extent > 0)
            .unwrap_or(GLOBAL_TAIL_EXTENT);
        state.define_memory_region(
            MemoryRegionKind::Global,
            &format!("global_{address:x}"),
            Some(address),
            Some(extent),
        );
    }
}

/// Seed memory regions using only canonical prepared-machine facts.
pub fn seed_memory_regions_for_prepared<'ctx>(state: &mut SymState<'ctx>, prepared: &SsaArtifact) {
    let stack_value = exact_stack_value(prepared);
    let stack_pointer_is_projectable = prepared
        .machine_context()
        .stack_pointer_carrier()
        .is_some_and(|storage| {
            !exact_version_zero_registers_for_storage(prepared, storage).is_empty()
        });
    let has_stack_objects = prepared.objects().objects.values().any(|object| {
        matches!(
            object.kind,
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. }
        )
    });
    if has_stack_objects
        && stack_pointer_is_projectable
        && let Some(stack_value) = stack_value
    {
        state.define_memory_region(
            MemoryRegionKind::Stack,
            "stack_window",
            Some(stack_value.saturating_sub(STACK_WINDOW_BELOW)),
            Some(STACK_WINDOW_SIZE),
        );
    }

    let mut globals = prepared
        .objects()
        .objects
        .values()
        .filter_map(|object| match &object.kind {
            ObjectKind::Global { address, .. } => Some(*address),
            _ => None,
        })
        .collect::<Vec<_>>();
    globals.sort_unstable();
    globals.dedup();
    for (index, address) in globals.iter().copied().enumerate() {
        let next = globals.get(index + 1).copied();
        let extent = next
            .and_then(|next| next.checked_sub(address))
            .filter(|extent| *extent > 0)
            .unwrap_or(GLOBAL_TAIL_EXTENT);
        state.define_memory_region(
            MemoryRegionKind::Global,
            &format!("global_{address:x}"),
            Some(address),
            Some(extent),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::seed_default_state_for_prepared;
    use crate::state::SymState;
    use r2il::{AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::SsaArtifact;
    use z3::Context;

    fn exact_seed_artifact() -> SsaArtifact {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_space(AddressSpace::ram(8));
        for (name, offset) in [
            ("RCX", 0x80),
            ("RDX", 0x88),
            ("R8", 0x90),
            ("RAX", 0x70),
            ("RSP", 0xa0),
            ("RIP", 0xa8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, 8));
        }
        let mut block = R2ILBlock::new(0x1800, 1);
        for (unique, register) in [(0x10, 0x80), (0x20, 0x88), (0x30, 0x90), (0x40, 0xa0)] {
            block.push(R2ILOp::Copy {
                dst: Varnode::unique(unique, 8),
                src: Varnode::register(register, 8),
            });
        }
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2sym-runtime-exact-seed".to_vec(),
            "ms64",
            [0x80, 0x88, 0x90]
                .into_iter()
                .enumerate()
                .map(|(index, offset)| {
                    r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
                }),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0x70),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0xa0)))
        .and_then(|interface| interface.with_return_address_storage(storage(0xa8)))
        .expect("exact runtime seed interface");
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("exact runtime seed artifact")
            .with_name("main")
    }

    #[test]
    fn exact_initial_state_uses_canonical_abi_without_name_projection() {
        let ctx = Context::thread_local();
        let prepared = exact_seed_artifact();
        let mut state = SymState::new(&ctx, prepared.entry);

        assert!(seed_default_state_for_prepared(&mut state, &prepared));
        assert!(state.get_register("RCX_0").is_symbolic());
        assert!(state.get_register("RDX_0").is_symbolic());
        assert!(state.get_register("R8_0").is_symbolic());
        assert!(state.get_register("RSP_0").as_concrete().is_some());
        assert!(
            state
                .registers()
                .keys()
                .all(|name| !name.starts_with("main_")),
            "function names must not invent process-entry state"
        );
    }
}
