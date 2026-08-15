use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::OpenOptions;
use std::io::Write;

use r2il::ArchSpec;
use r2ssa::{ObjectKind, SSAVar, SsaArtifact};

use crate::PathExplorer;
use crate::executor::{CallHookResult, CallHookTag};
use crate::memory::MemoryRegionKind;
use crate::sim::{CallConv, PreparedFunctionScope};
use crate::state::{ExitStatus, SymState};
use crate::value::SymValue;

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

#[derive(Clone, Copy)]
struct MainArgRegisterProfile {
    argc: &'static [&'static str],
    argv: &'static [&'static str],
    envp: &'static [&'static str],
}

fn collect_registers(prepared: &SsaArtifact, only_version_zero: bool) -> BTreeMap<String, u32> {
    let mut registers = BTreeMap::new();
    let mut record = |var: &SSAVar| {
        if !var.is_register() || (only_version_zero && var.version != 0) {
            return;
        }
        registers
            .entry(var.display_name())
            .or_insert(var.size.saturating_mul(8));
    };
    for block in prepared.blocks() {
        block.for_each_def(|def| record(def.var));
        block.for_each_source(|src| record(src.var));
    }
    registers
}

fn collect_version_zero_registers(prepared: &SsaArtifact) -> BTreeMap<String, u32> {
    collect_registers(prepared, true)
}

fn normalized_main_like_name(name: &str) -> String {
    name.rsplit('.')
        .next()
        .unwrap_or(name)
        .trim_start_matches('_')
        .to_ascii_lowercase()
}

fn debug_main_seed_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_MAIN_SEED").is_some()
}

fn debug_main_seed_log(message: &str) {
    if !debug_main_seed_enabled() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_MAIN_SEED_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_main_seed.log".to_string());
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(file, "{message}");
    }
}

fn root_name_looks_like_main(scope: &PreparedFunctionScope, prepared: &SsaArtifact) -> bool {
    let name = scope
        .root()
        .and_then(|function| function.name.as_deref())
        .or(prepared.function().name.as_deref());
    let Some(name) = name else {
        return false;
    };
    let normalized = normalized_main_like_name(name);
    matches!(normalized.as_str(), "main" | "wmain")
}

fn detect_main_arg_register_profile(
    prepared: &SsaArtifact,
    arch: Option<&ArchSpec>,
) -> Option<MainArgRegisterProfile> {
    let registers = collect_version_zero_registers(prepared);
    let arch_looks_x64 = arch.is_some_and(|arch| {
        let name = arch.name.to_ascii_lowercase();
        (name.contains("x86") || name == "x64" || name == "amd64")
            && (arch.addr_size == 8 || name.contains("64"))
    });
    let has_windows = registers.keys().any(|name| {
        name.starts_with("RCX_0")
            || name.starts_with("ECX_0")
            || name.starts_with("RDX_0")
            || name.starts_with("EDX_0")
    });
    let has_sysv = registers.keys().any(|name| {
        name.starts_with("RDI_0")
            || name.starts_with("EDI_0")
            || name.starts_with("RSI_0")
            || name.starts_with("ESI_0")
    });

    if !(arch_looks_x64 || has_windows || has_sysv) {
        return None;
    }

    if has_windows || !has_sysv {
        Some(MainArgRegisterProfile {
            argc: &["RCX", "ECX"],
            argv: &["RDX", "EDX"],
            envp: &["R8", "R8D"],
        })
    } else {
        Some(MainArgRegisterProfile {
            argc: &["RDI", "EDI"],
            argv: &["RSI", "ESI"],
            envp: &["RDX", "EDX"],
        })
    }
}

fn infer_main_pointer_bits(
    prepared: &SsaArtifact,
    arch: Option<&ArchSpec>,
    profile: MainArgRegisterProfile,
) -> u32 {
    let registers = collect_registers(prepared, false);
    let from_registers = registers
        .iter()
        .filter_map(|(reg_name, bits)| {
            let (prefix, _) = reg_name.rsplit_once('_')?;
            (profile
                .argc
                .iter()
                .chain(profile.argv.iter())
                .chain(profile.envp.iter())
                .any(|candidate| prefix.eq_ignore_ascii_case(candidate)))
            .then_some(*bits)
        })
        .max();
    if let Some(bits) = from_registers {
        return bits;
    }

    arch.map(|spec| spec.addr_size.saturating_mul(8))
        .filter(|bits| *bits > 0)
        .or_else(|| {
            registers
                .into_iter()
                .filter_map(|(reg_name, bits)| {
                    let (prefix, _) = reg_name.rsplit_once('_')?;
                    (profile
                        .argc
                        .iter()
                        .chain(profile.argv.iter())
                        .chain(profile.envp.iter())
                        .any(|candidate| prefix.eq_ignore_ascii_case(candidate)))
                    .then_some(bits)
                })
                .max()
        })
        .unwrap_or(64)
}

fn set_register_family_concrete<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    family: &[&str],
    value: u64,
) {
    let registers = collect_version_zero_registers(prepared);
    for (reg_name, bits) in registers {
        let Some((prefix, _)) = reg_name.rsplit_once('_') else {
            continue;
        };
        if family
            .iter()
            .any(|candidate| prefix.eq_ignore_ascii_case(candidate))
        {
            state.set_concrete(&reg_name, value, bits);
        }
    }
}

fn seed_concrete_bytes<'ctx>(state: &mut SymState<'ctx>, addr: u64, bytes: &[u8]) {
    for (offset, byte) in bytes.iter().copied().enumerate() {
        let dst = SymValue::concrete(addr + offset as u64, 64);
        let value = SymValue::concrete(u64::from(byte), 8);
        state.mem_write(&dst, &value, 1);
    }
}

fn seed_process_like_main_arguments<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    scope: &PreparedFunctionScope,
    arch: Option<&ArchSpec>,
) {
    let is_main = root_name_looks_like_main(scope, prepared);
    debug_main_seed_log(&format!(
        "root_name={:?} prepared_name={:?} is_main={}",
        scope.root().and_then(|function| function.name.as_deref()),
        prepared.function().name.as_deref(),
        is_main
    ));
    if !is_main {
        return;
    }
    let Some(profile) = detect_main_arg_register_profile(prepared, arch) else {
        debug_main_seed_log("no compatible arg-register profile");
        return;
    };
    debug_main_seed_log(&format!(
        "profile argc={:?} argv={:?} envp={:?}",
        profile.argc, profile.argv, profile.envp
    ));

    let (_, argv0_addr) = state.allocate_heap_region("main_argv0", 0x10);
    seed_concrete_bytes(state, argv0_addr, b"prog\0");

    let (_, argv1_addr) = state.allocate_heap_region("main_argv1", MAIN_ARGV1_SYMBOLIC_BYTES + 1);
    for index in 0..MAIN_ARGV1_SYMBOLIC_BYTES {
        let byte = state.new_symbolic_input(&format!("argv1_byte_{index}"), 8);
        state.constrain_ne(&byte, 0);
        let dst = SymValue::concrete(argv1_addr + index, 64);
        state.mem_write(&dst, &byte, 1);
    }
    seed_concrete_bytes(state, argv1_addr + MAIN_ARGV1_SYMBOLIC_BYTES, &[0]);

    let (_, argv_table_addr) = state.allocate_heap_region("main_argv", 0x20);
    let ptr_bits = infer_main_pointer_bits(prepared, arch, profile);
    let ptr_size = (ptr_bits / 8) as usize;
    for (index, value) in [argv0_addr, argv1_addr, 0].into_iter().enumerate() {
        let dst = SymValue::concrete(argv_table_addr + (index * ptr_size) as u64, 64);
        let value = SymValue::concrete(value, ptr_bits);
        state.mem_write(&dst, &value, ptr_size as u32);
    }
    let argv0_slot = state
        .mem_read(&SymValue::concrete(argv_table_addr, 64), ptr_size as u32)
        .as_concrete()
        .unwrap_or_default();
    let argv1_slot = state
        .mem_read(
            &SymValue::concrete(argv_table_addr + ptr_size as u64, 64),
            ptr_size as u32,
        )
        .as_concrete()
        .unwrap_or_default();
    debug_main_seed_log(&format!(
        "ptr_bits={ptr_bits} ptr_size={ptr_size} argv0_addr={argv0_addr:#x} argv1_addr={argv1_addr:#x} argv_table_addr={argv_table_addr:#x} argv_slots=[{argv0_slot:#x}, {argv1_slot:#x}]"
    ));

    set_register_family_concrete(state, prepared, profile.argc, 2);
    set_register_family_concrete(state, prepared, profile.argv, argv_table_addr);
    set_register_family_concrete(state, prepared, profile.envp, 0);
    let mut seeded = state
        .registers()
        .iter()
        .filter_map(|(name, value)| {
            let (prefix, _) = name.rsplit_once('_')?;
            (profile
                .argc
                .iter()
                .chain(profile.argv.iter())
                .chain(profile.envp.iter())
                .any(|candidate| prefix.eq_ignore_ascii_case(candidate)))
            .then(|| format!("{name}={:#x}", value.as_concrete().unwrap_or_default()))
        })
        .collect::<Vec<_>>();
    seeded.sort();
    debug_main_seed_log(&format!("seeded registers {:?}", seeded));
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

pub fn seed_scope_state_for_arch<'ctx>(
    state: &mut SymState<'ctx>,
    prepared: &SsaArtifact,
    scope: &PreparedFunctionScope,
    arch: Option<&ArchSpec>,
) {
    seed_default_state_for_arch(state, prepared, arch);
    seed_process_like_main_arguments(state, prepared, scope, arch);
}

const STACK_WINDOW_BELOW: u64 = 0x8000;
const STACK_WINDOW_SIZE: u64 = 0x10000;
const GLOBAL_TAIL_EXTENT: u64 = 0x1000;
const MAIN_ARGV1_SYMBOLIC_BYTES: u64 = 0x40;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WindowsRuntimeHook {
    AddVectoredExceptionHandler,
    RaiseException,
    VirtualAlloc,
    VirtualProtect,
    HeapAlloc,
}

impl WindowsRuntimeHook {
    fn call_hook_tag(self) -> CallHookTag {
        match self {
            WindowsRuntimeHook::AddVectoredExceptionHandler => {
                CallHookTag::WindowsAddVectoredExceptionHandler
            }
            WindowsRuntimeHook::RaiseException => CallHookTag::WindowsRaiseException,
            WindowsRuntimeHook::VirtualAlloc => CallHookTag::WindowsVirtualAlloc,
            WindowsRuntimeHook::VirtualProtect => CallHookTag::WindowsVirtualProtect,
            WindowsRuntimeHook::HeapAlloc => CallHookTag::WindowsHeapAlloc,
        }
    }
}

fn arch_supports_windows_runtime(arch: &ArchSpec) -> bool {
    let name = arch.name.to_ascii_lowercase();
    (name.contains("x86") || name == "x64" || name == "amd64")
        && (arch.addr_size == 8 || name.contains("64"))
}

fn windows_x64_callconv() -> CallConv {
    CallConv::new(vec!["RCX", "RDX", "R8", "R9"], "RAX", 64, 64)
}

fn normalize_windows_runtime_hook(name: &str) -> Option<WindowsRuntimeHook> {
    let lower = name.to_ascii_lowercase();
    let normalized = lower.trim();
    if normalized.ends_with("addvectoredexceptionhandler") {
        Some(WindowsRuntimeHook::AddVectoredExceptionHandler)
    } else if normalized.ends_with("raiseexception") {
        Some(WindowsRuntimeHook::RaiseException)
    } else if normalized.ends_with("virtualalloc") {
        Some(WindowsRuntimeHook::VirtualAlloc)
    } else if normalized.ends_with("virtualprotect") {
        Some(WindowsRuntimeHook::VirtualProtect)
    } else if normalized.ends_with("heapalloc") {
        Some(WindowsRuntimeHook::HeapAlloc)
    } else {
        None
    }
}

fn page_protection_is_executable(value: u64) -> bool {
    matches!(value, 0x10 | 0x20 | 0x40 | 0x80)
}

fn seed_exception_continuation<'ctx>(
    state: &mut SymState<'ctx>,
    exception_code: u64,
    handler_addr: u64,
) -> CallHookResult {
    state.seed_exception_continuation(exception_code, handler_addr);
    CallHookResult::Jump(handler_addr)
}

fn apply_windows_runtime_hook<'ctx>(
    state: &mut SymState<'ctx>,
    hook: WindowsRuntimeHook,
) -> CallHookResult {
    let callconv = windows_x64_callconv();
    let call = callconv.collect_call_info(state, 4);
    match hook {
        WindowsRuntimeHook::AddVectoredExceptionHandler => {
            let handler = call.args.get(1).and_then(SymValue::as_concrete);
            if let Some(handler) = handler {
                state.register_exception_handler(handler);
                callconv.write_return(state, SymValue::concrete(handler, callconv.ret_bits()));
                CallHookResult::Fallthrough
            } else {
                CallHookResult::Terminate(ExitStatus::RuntimeBlocked(
                    crate::state::RuntimeBlockReason::MissingContinuationSeed,
                ))
            }
        }
        WindowsRuntimeHook::RaiseException => {
            let Some(exception_code) = call.args.first().and_then(SymValue::as_concrete) else {
                return CallHookResult::Terminate(ExitStatus::RuntimeBlocked(
                    crate::state::RuntimeBlockReason::MissingContinuationSeed,
                ));
            };
            let Some(handler_addr) = state.primary_exception_handler() else {
                return CallHookResult::Terminate(ExitStatus::RuntimeBlocked(
                    crate::state::RuntimeBlockReason::MissingExceptionHandler,
                ));
            };
            seed_exception_continuation(state, exception_code, handler_addr)
        }
        WindowsRuntimeHook::VirtualAlloc => {
            let size = call
                .args
                .get(1)
                .and_then(SymValue::as_concrete)
                .unwrap_or(0x1000)
                .max(1);
            let executable = call
                .args
                .get(3)
                .and_then(SymValue::as_concrete)
                .is_some_and(page_protection_is_executable);
            let (_region_id, base_addr) =
                state.allocate_heap_region(&format!("virtualalloc_{:x}", state.pc()), size);
            state.register_runtime_region_alias(base_addr, size, executable);
            callconv.write_return(state, SymValue::concrete(base_addr, callconv.ret_bits()));
            CallHookResult::Fallthrough
        }
        WindowsRuntimeHook::VirtualProtect => {
            let addr = call
                .args
                .first()
                .and_then(SymValue::as_concrete)
                .unwrap_or(0);
            let size = call
                .args
                .get(1)
                .and_then(SymValue::as_concrete)
                .unwrap_or(0)
                .max(1);
            let executable = call
                .args
                .get(2)
                .and_then(SymValue::as_concrete)
                .is_some_and(page_protection_is_executable);
            if executable {
                state.mark_runtime_region_executable(addr, size);
            }
            callconv.write_return(state, SymValue::concrete(1, callconv.ret_bits()));
            CallHookResult::Fallthrough
        }
        WindowsRuntimeHook::HeapAlloc => {
            let size = call
                .args
                .get(2)
                .and_then(SymValue::as_concrete)
                .unwrap_or(0x100)
                .max(1);
            let (_region_id, base_addr) =
                state.allocate_heap_region(&format!("heapalloc_{:x}", state.pc()), size);
            callconv.write_return(state, SymValue::concrete(base_addr, callconv.ret_bits()));
            CallHookResult::Fallthrough
        }
    }
}

pub fn install_runtime_hooks_for_scope<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    scope: &PreparedFunctionScope,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
) {
    let Some(arch) = arch else {
        return;
    };
    if !arch_supports_windows_runtime(arch) {
        return;
    }

    let mut targets = BTreeMap::new();
    for function in scope.functions().values() {
        for call in function.prepared.call_sites().by_id.values() {
            if let Some(target) = function.prepared.resolved_call_target(call)
                && let Some(raw_name) = symbol_map.get(&target)
                && let Some(kind) = normalize_windows_runtime_hook(raw_name)
            {
                targets.entry(target).or_insert(kind);
            }
        }
    }

    for (&target, raw_name) in symbol_map {
        let Some(kind) = normalize_windows_runtime_hook(raw_name) else {
            continue;
        };
        targets.entry(target).or_insert(kind);
    }

    for (target, kind) in targets {
        explorer.register_tagged_call_hook(target, kind.call_hook_tag(), move |state| {
            apply_windows_runtime_hook(state, kind)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::{
        WindowsRuntimeHook, apply_windows_runtime_hook, install_runtime_hooks_for_scope,
        seed_scope_state_for_arch,
    };
    use crate::executor::CallHookResult;
    use crate::path::PathExplorer;
    use crate::sim::{PreparedFunctionScope, ScopedPreparedFunction};
    use crate::state::SymState;
    use r2il::{AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{InterprocFunctionId, SsaArtifact};
    use std::collections::HashMap;
    use z3::Context;

    fn make_main_seed_arch(addr_size: u32) -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = addr_size;
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("RCX", 0x80, 8));
        arch.add_register(RegisterDef::new("ECX", 0x80, 4));
        arch.add_register(RegisterDef::new("RDX", 0x88, 8));
        arch.add_register(RegisterDef::new("EDX", 0x88, 4));
        arch.add_register(RegisterDef::new("R8", 0x90, 8));
        arch.add_register(RegisterDef::new("R8D", 0x90, 4));
        arch
    }

    fn make_main_seed_scope(arch: &ArchSpec) -> (SsaArtifact, PreparedFunctionScope) {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(0x80, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x20, 8),
            src: Varnode::register(0x88, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x30, 8),
            src: Varnode::register(0x90, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let prepared = SsaArtifact::for_symbolic(&[block], Some(arch))
            .expect("ssa")
            .with_name("main");
        let scope = PreparedFunctionScope::new(
            0x1000,
            vec![ScopedPreparedFunction {
                id: InterprocFunctionId(0x1000),
                name: Some("main".to_string()),
                prepared: prepared.clone(),
            }],
        )
        .expect("scope");
        (prepared, scope)
    }

    #[test]
    fn test_virtualalloc_hook_writes_current_return_alias() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1400_1000);
        state.set_concrete("RCX_4", 0, 64);
        state.set_concrete("RDX_4", 0x1000, 64);
        state.set_concrete("R8_4", 0x3000, 64);
        state.set_concrete("R9_4", 0x40, 64);
        state.set_concrete("RAX_7", 0xdead_beef, 64);

        let result = apply_windows_runtime_hook(&mut state, WindowsRuntimeHook::VirtualAlloc);
        assert_eq!(result, CallHookResult::Fallthrough);

        let base_addr = state
            .get_register("RAX_7")
            .as_concrete()
            .expect("virtualalloc return should be concrete");
        assert_ne!(base_addr, 0xdead_beef);
        let region = state
            .runtime_region_for_pc(base_addr)
            .expect("allocated runtime region should be registered");
        assert!(region.executable);
        assert_eq!(region.size, 0x1000);
    }

    #[test]
    fn main_seed_uses_register_width_for_argv_table_layout() {
        let ctx = Context::thread_local();
        let arch = make_main_seed_arch(4);
        let (prepared, scope) = make_main_seed_scope(&arch);
        let mut state = SymState::new(&ctx, 0x1000);

        seed_scope_state_for_arch(&mut state, &prepared, &scope, Some(&arch));

        let argv_addr = state
            .get_register("RDX_0")
            .as_concrete()
            .expect("argv register should be concrete");
        let argv0_addr = state
            .mem_read(&crate::SymValue::concrete(argv_addr, 64), 8)
            .as_concrete()
            .expect("argv[0] should be present");
        let argv1_addr = state
            .mem_read(&crate::SymValue::concrete(argv_addr + 8, 64), 8)
            .as_concrete()
            .expect("argv[1] should be written at pointer-width stride");

        assert_ne!(argv0_addr, 0);
        assert_ne!(argv1_addr, 0);
        assert_ne!(argv0_addr, argv1_addr);
        assert_eq!(
            state
                .mem_read(
                    &crate::SymValue::concrete(argv1_addr + super::MAIN_ARGV1_SYMBOLIC_BYTES, 64,),
                    1,
                )
                .as_concrete(),
            Some(0),
            "argv[1] should remain NUL-terminated",
        );
    }

    #[test]
    fn main_seed_only_initializes_version_zero_argument_registers() {
        let ctx = Context::thread_local();
        let arch = make_main_seed_arch(8);
        let (prepared, scope) = make_main_seed_scope(&arch);
        let mut state = SymState::new(&ctx, 0x1000);

        seed_scope_state_for_arch(&mut state, &prepared, &scope, Some(&arch));

        let argv_entry = state
            .get_register("RDX_0")
            .as_concrete()
            .expect("argv register should seed the entry SSA version");
        assert_ne!(argv_entry, 0);
        assert!(
            state.get_register("RDX_1").as_concrete().is_none(),
            "later SSA versions must be left for execution to define"
        );
        assert!(
            state.get_register("RCX_1").as_concrete().is_none(),
            "later argc versions must not be pre-seeded either"
        );
    }

    #[test]
    fn install_runtime_hooks_uses_symbol_map_imports_even_without_scope_calls() {
        let ctx = Context::thread_local();
        let arch = make_main_seed_arch(8);
        let (_prepared, scope) = make_main_seed_scope(&arch);
        let blocks = vec![
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![
                    R2ILOp::Call {
                        target: Varnode {
                            space: SpaceId::Ram,
                            offset: 0x401000,
                            size: 8,
                            meta: None,
                        },
                    },
                    R2ILOp::IntNotEqual {
                        dst: Varnode::unique(0x20, 1),
                        a: Varnode::register(0x100, 8),
                        b: Varnode::constant(0, 8),
                    },
                    R2ILOp::CBranch {
                        target: Varnode::constant(0x2010, 8),
                        cond: Varnode::unique(0x20, 1),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x2004,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
            },
            R2ILBlock {
                addr: 0x2010,
                size: 1,
                switch_info: None,
                op_metadata: Default::default(),
                ops: vec![R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                }],
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("ssa");
        let mut explorer = PathExplorer::new(&ctx);
        let symbol_map =
            HashMap::from([(0x401000, "sym.imp.KERNEL32.dll_VirtualAlloc".to_string())]);
        install_runtime_hooks_for_scope(&mut explorer, &scope, Some(&arch), &symbol_map);

        let mut state = SymState::new(&ctx, 0x2000);
        state.set_concrete("RDX_0", 0x1000, 64);
        state.set_concrete("R9_0", 0x40, 64);
        state.set_concrete("RAX_0", 0, 64);

        let paths = explorer.find_paths_to(&func, state, 0x2010);
        assert!(
            !paths.is_empty(),
            "symbol-map runtime imports should install hooks even when scope call discovery is absent"
        );
    }
}
