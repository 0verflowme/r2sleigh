use std::collections::HashSet;

use r2il::ArchSpec;
use r2ssa::{ObjectKind, SSAVar, SsaArtifact};

use crate::memory::MemoryRegionKind;
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

const STACK_WINDOW_BELOW: u64 = 0x8000;
const STACK_WINDOW_SIZE: u64 = 0x10000;
const GLOBAL_TAIL_EXTENT: u64 = 0x1000;

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
