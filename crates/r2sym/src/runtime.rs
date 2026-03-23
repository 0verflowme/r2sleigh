use std::collections::HashSet;

use r2il::ArchSpec;
use r2ssa::{PreparedFunctionSSA, SSAVar};

use crate::state::SymState;

pub fn seed_default_state_for_arch<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &PreparedFunctionSSA,
    arch: Option<&ArchSpec>,
) {
    let Some(arch) = arch else {
        return;
    };

    let arch_name = arch.name.to_ascii_lowercase();
    let looks_riscv = arch_name.contains("riscv") || arch_name.starts_with("rv");
    let (arg_regs, stack_regs, stack_value) = if arch_name == "x86-64"
        || arch_name == "x86_64"
        || (arch_name == "x86" && arch.addr_size == 8)
    {
        (
            [
                "RDI", "RSI", "RDX", "RCX", "R8", "R9", "EDI", "ESI", "EDX", "ECX", "R8D", "R9D",
            ]
            .as_slice(),
            ["RSP", "RBP"].as_slice(),
            0x7fff_ffff_0000u64,
        )
    } else if arch_name == "x86" {
        (
            ["EAX", "EBX", "ECX", "EDX", "ESI", "EDI"].as_slice(),
            ["ESP", "EBP"].as_slice(),
            0x7fff_0000u64,
        )
    } else if looks_riscv && (arch.addr_size == 8 || arch_name.contains("64")) {
        (
            [
                "A0", "A1", "A2", "A3", "A4", "A5", "A6", "A7", "X10", "X11", "X12", "X13", "X14",
                "X15", "X16", "X17",
            ]
            .as_slice(),
            ["SP", "S0", "FP", "X2", "X8"].as_slice(),
            0x7fff_ffff_0000u64,
        )
    } else if looks_riscv {
        (
            [
                "A0", "A1", "A2", "A3", "A4", "A5", "A6", "A7", "X10", "X11", "X12", "X13", "X14",
                "X15", "X16", "X17",
            ]
            .as_slice(),
            ["SP", "S0", "FP", "X2", "X8"].as_slice(),
            0x7fff_0000u64,
        )
    } else {
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
        if stack_regs.contains(&base.as_str()) {
            state.set_concrete(&reg_name, stack_value, bits);
            return;
        }

        if arg_regs.contains(&base.as_str()) {
            let sym_name = base_name.to_ascii_lowercase();
            state.make_symbolic_named(&reg_name, &sym_name, bits);
        }
    };

    for block in prepared.blocks() {
        block.for_each_def(|def| maybe_seed(def.var));
        block.for_each_source(|src| maybe_seed(src.var));
    }
}
