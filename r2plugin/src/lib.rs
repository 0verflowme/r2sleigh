//! r2sleigh radare2 plugin
//!
//! This module exposes a C-ABI for radare2 integration. It can load r2il
//! specs from disk, or build Sleigh-based disassemblers and lift instruction
//! bytes into r2il blocks with ESIL rendering.

// FFI functions receive raw pointers from radare2's C code and must dereference
// them. Making every exported function `unsafe fn` would be incorrect because
// the caller (radare2) uses a normal C function-pointer table, not Rust's
// `unsafe` calling convention.
#![allow(clippy::not_unsafe_ptr_arg_deref)]

mod analysis;
mod blocks;
mod context;
mod decompiler;
mod helpers;
mod types;

#[cfg(test)]
use analysis::ssa::{r2il_block_defuse_json, r2il_block_to_ssa_json};
use r2il::serialize::UserOpDef;
use r2il::{ArchSpec, R2ILBlock, R2ILOp, Varnode, serialize, validate_block_full};
use r2sleigh_export::{
    ExportFormat, InstructionAction, InstructionExportInput, export_instruction, op_json_named,
};
use r2sleigh_lift::{Disassembler, SemanticMetadataOptions, build_arch_spec, userop_map_for_arch};
use std::ffi::{CStr, CString};
use std::fs::OpenOptions;
use std::io::Write;
use std::os::raw::c_char;
use std::path::Path;
use std::ptr;
use std::slice;
use std::time::Instant;
#[cfg(test)]
use types::parse_const_value;
#[cfg(test)]
use types::{recover_vars_arch_profile, size_to_type, ssa_var_block_key};

/// Opaque context handle for C API.
pub struct R2ILContext {
    arch: Option<ArchSpec>,
    arch_name_cstr: Option<CString>,
    disasm: Option<Disassembler>,
    semantic_metadata_enabled: bool,
    error: Option<CString>,
}

impl R2ILContext {
    #[allow(dead_code)]
    fn new() -> Self {
        Self {
            arch: None,
            arch_name_cstr: None,
            disasm: None,
            semantic_metadata_enabled: true,
            error: None,
        }
    }

    fn with_arch(arch: ArchSpec) -> Self {
        let name = CString::new(arch.name.clone()).ok();
        Self {
            arch: Some(arch),
            arch_name_cstr: name,
            disasm: None,
            semantic_metadata_enabled: true,
            error: None,
        }
    }

    fn with_arch_and_disasm(arch: ArchSpec, disasm: Disassembler) -> Self {
        let name = CString::new(arch.name.clone()).ok();
        Self {
            arch: Some(arch),
            arch_name_cstr: name,
            disasm: Some(disasm),
            semantic_metadata_enabled: true,
            error: None,
        }
    }

    fn with_error(msg: &str) -> Self {
        Self {
            arch: None,
            arch_name_cstr: None,
            disasm: None,
            semantic_metadata_enabled: true,
            error: CString::new(msg).ok(),
        }
    }

    fn set_error(&mut self, msg: impl AsRef<str>) {
        self.error = CString::new(msg.as_ref()).ok();
    }

    fn clear_error(&mut self) {
        self.error = None;
    }
}

fn validate_block_in_context(ctx: &mut R2ILContext, block: &R2ILBlock) -> Result<(), String> {
    let Some(arch) = ctx.arch.as_ref() else {
        let msg = "missing arch context for semantic validation".to_string();
        ctx.set_error(&msg);
        return Err(msg);
    };

    validate_block_full(block, arch).map_err(|e| {
        let msg = format!("Invalid lifted block: {}", e);
        ctx.set_error(&msg);
        msg
    })
}

/// Load an r2il file and return a context handle.
///
/// Returns NULL on failure.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_load(path: *const c_char) -> *mut R2ILContext {
    if path.is_null() {
        return ptr::null_mut();
    }

    let path_str = unsafe {
        match CStr::from_ptr(path).to_str() {
            Ok(s) => s,
            Err(_) => return ptr::null_mut(),
        }
    };

    match serialize::load(Path::new(path_str)) {
        Ok(arch) => Box::into_raw(Box::new(R2ILContext::with_arch(arch))),
        Err(e) => Box::into_raw(Box::new(R2ILContext::with_error(&e.to_string()))),
    }
}

/// Initialize a context from a built-in architecture (Sleigh via sleigh-config).
///
/// Returns NULL on failure.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_arch_init(arch: *const c_char) -> *mut R2ILContext {
    if arch.is_null() {
        return ptr::null_mut();
    }

    let arch_str = unsafe {
        match CStr::from_ptr(arch).to_str() {
            Ok(s) => s,
            Err(_) => return ptr::null_mut(),
        }
    };

    match create_disassembler_for_arch(arch_str) {
        Ok((spec, dis)) => Box::into_raw(Box::new(R2ILContext::with_arch_and_disasm(spec, dis))),
        Err(e) => Box::into_raw(Box::new(R2ILContext::with_error(&e))),
    }
}

/// Free a context handle.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_free(ctx: *mut R2ILContext) {
    if !ctx.is_null() {
        unsafe {
            drop(Box::from_raw(ctx));
        }
    }
}

/// Check if the context has a loaded architecture.
///
/// Returns 1 if loaded, 0 otherwise.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_is_loaded(ctx: *const R2ILContext) -> i32 {
    if ctx.is_null() {
        return 0;
    }

    unsafe { if (*ctx).arch.is_some() { 1 } else { 0 } }
}

/// Get the architecture name.
///
/// Returns NULL if not loaded.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_arch_name(ctx: *const R2ILContext) -> *const c_char {
    if ctx.is_null() {
        return ptr::null();
    }

    unsafe {
        match &(*ctx).arch_name_cstr {
            Some(s) => s.as_ptr(),
            None => ptr::null(),
        }
    }
}

/// Get the last error message.
///
/// Returns NULL if no error.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_error(ctx: *const R2ILContext) -> *const c_char {
    if ctx.is_null() {
        return ptr::null();
    }

    unsafe {
        match &(*ctx).error {
            Some(s) => s.as_ptr(),
            None => ptr::null(),
        }
    }
}

/// Get the address size in bytes.
///
/// Returns 0 if not loaded.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_addr_size(ctx: *const R2ILContext) -> u32 {
    if ctx.is_null() {
        return 0;
    }

    unsafe {
        match &(*ctx).arch {
            Some(arch) => helpers::effective_addr_size_bytes(arch),
            None => 0,
        }
    }
}

/// Check if the architecture is big-endian.
///
/// Returns 1 for big-endian, 0 for little-endian or if not loaded.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_is_big_endian(ctx: *const R2ILContext) -> i32 {
    if ctx.is_null() {
        return 0;
    }

    unsafe {
        match &(*ctx).arch {
            Some(arch) => i32::from(arch.memory_endianness.to_legacy_big_endian()),
            None => 0,
        }
    }
}

/// Get the number of registers.
///
/// Returns 0 if not loaded.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_register_count(ctx: *const R2ILContext) -> usize {
    if ctx.is_null() {
        return 0;
    }

    unsafe {
        match &(*ctx).arch {
            Some(arch) => arch.registers.len(),
            None => 0,
        }
    }
}

/// Get the register profile string for radare2.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2il_get_reg_profile(ctx: *const R2ILContext) -> *mut c_char {
    if ctx.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let arch = match &ctx_ref.arch {
        Some(a) => a,
        None => return ptr::null_mut(),
    };

    let mut profile = String::new();
    let mut reg_meta: std::collections::HashMap<String, (u32, u64, String)> =
        std::collections::HashMap::new();

    // Emit all original register names from Sleigh.
    for reg in &arch.registers {
        profile.push_str(&format!(
            "gpr\t{}\t.{}\t{}\t0\n",
            reg.name,
            reg.size * 8,
            reg.offset
        ));
        reg_meta.insert(
            reg.name.to_ascii_lowercase(),
            (reg.size * 8, reg.offset, reg.name.clone()),
        );
    }

    // Emit lowercase aliases for case-insensitive lookups.
    let mut lowercase_aliases = Vec::new();
    for (name_lower, (bits, offset, original)) in &reg_meta {
        if original != name_lower {
            lowercase_aliases.push((name_lower.clone(), *bits, *offset));
        }
    }
    for (name_lower, bits, offset) in lowercase_aliases {
        profile.push_str(&format!("gpr\t{}\t.{}\t{}\t0\n", name_lower, bits, offset));
    }

    let mut stripped_aliases = Vec::new();
    for (original, (bits, offset, _)) in &reg_meta {
        if let Some(stripped) = original.strip_prefix('$')
            && !stripped.is_empty()
            && !reg_meta.contains_key(stripped)
        {
            stripped_aliases.push((stripped.to_string(), *bits, *offset));
        }
    }
    for (alias, bits, offset) in stripped_aliases {
        profile.push_str(&format!("gpr\t{}\t.{}\t{}\t0\n", alias, bits, offset));
        reg_meta.insert(alias.clone(), (bits, offset, alias));
    }

    // Synthesize missing aliases expected by radare2/ESIL for specific arches.
    let mut add_gpr_alias = |alias_name: &str, source_name: &str| {
        let alias_lower = alias_name.to_ascii_lowercase();
        if reg_meta.contains_key(&alias_lower) {
            return;
        }
        let Some((bits, offset, _)) = reg_meta.get(source_name).cloned() else {
            return;
        };
        profile.push_str(&format!("gpr\t{}\t.{}\t{}\t0\n", alias_lower, bits, offset));
        reg_meta.insert(alias_lower.clone(), (bits, offset, alias_lower));
    };

    let arch_name = arch.name.to_ascii_lowercase();
    let is_arm64 = arch_name.contains("aarch64") || arch_name.contains("arm64");
    if is_arm64 {
        // AArch64 Sleigh specs often expose CY/ZR/NG/OV instead of cf/zf/nf/vf.
        add_gpr_alias("cf", "cy");
        add_gpr_alias("zf", "zr");
        add_gpr_alias("nf", "ng");
        add_gpr_alias("vf", "ov");
        // ESIL/radare2 paths may reference lr directly; map it to x30.
        add_gpr_alias("lr", "x30");
    }

    let first_existing = |candidates: &[&str]| -> Option<String> {
        candidates
            .iter()
            .find_map(|name| reg_meta.get(*name).map(|(_, _, original)| original.clone()))
    };

    let pc = first_existing(&["pc", "$pc", "rip", "eip", "ip"]);
    let sp = first_existing(&["sp", "$sp", "rsp", "esp"]);
    let bp = first_existing(&["bp", "rbp", "ebp", "fp", "$fp", "s8", "$s8", "x29"]);

    let mut a_roles: [Option<String>; 8] = std::array::from_fn(|_| None);
    a_roles[0] = first_existing(&["rdi", "a0", "$a0", "x0", "w0", "r0"]);
    a_roles[1] = first_existing(&["rsi", "a1", "$a1", "x1", "w1", "r1"]);
    a_roles[2] = first_existing(&["rdx", "a2", "$a2", "x2", "w2", "r2"]);
    a_roles[3] = first_existing(&["rcx", "a3", "$a3", "x3", "w3", "r3"]);

    let mut r_roles: [Option<String>; 4] = std::array::from_fn(|_| None);
    r_roles[0] = first_existing(&["r0", "rax", "eax", "v0", "$v0", "x0", "w0"]);
    r_roles[1] = first_existing(&["r1", "v1", "$v1", "x1", "w1"]);
    r_roles[2] = first_existing(&["r2", "x2", "w2"]);
    r_roles[3] = first_existing(&["r3", "x3", "w3"]);

    let mut sn = first_existing(&["sn"]);

    if is_arm64 {
        for idx in 0..8 {
            if let Some(reg) = first_existing(&[&format!("x{idx}"), &format!("w{idx}")]) {
                a_roles[idx] = Some(reg.clone());
                if idx < 4 {
                    r_roles[idx] = Some(reg);
                }
            }
        }
        if sn.is_none() {
            sn = first_existing(&["x16", "x8"]);
        }
    }

    if let Some(n) = pc.as_deref() {
        profile.push_str(&format!("=PC\t{}\n", n));
    }
    if let Some(n) = sp.as_deref() {
        profile.push_str(&format!("=SP\t{}\n", n));
    }
    if let Some(n) = bp.as_deref() {
        profile.push_str(&format!("=BP\t{}\n", n));
    }
    for (idx, reg) in a_roles.iter().enumerate() {
        if let Some(n) = reg.as_deref() {
            profile.push_str(&format!("=A{}\t{}\n", idx, n));
        }
    }
    for (idx, reg) in r_roles.iter().enumerate() {
        if let Some(n) = reg.as_deref() {
            profile.push_str(&format!("=R{}\t{}\n", idx, n));
        }
    }
    if let Some(n) = sn.as_deref() {
        profile.push_str(&format!("=SN\t{}\n", n));
    }

    if let Some(n) = first_existing(&["cf"]).as_deref() {
        profile.push_str(&format!("=CF\t{}\n", n));
    }
    if let Some(n) = first_existing(&["zf"]).as_deref() {
        profile.push_str(&format!("=ZF\t{}\n", n));
    }
    if let Some(n) = first_existing(&["nf", "sf"]).as_deref() {
        profile.push_str(&format!("=SF\t{}\n", n));
    }
    if let Some(n) = first_existing(&["vf", "of"]).as_deref() {
        profile.push_str(&format!("=OF\t{}\n", n));
    }

    CString::new(profile).map_or(ptr::null_mut(), |c| c.into_raw())
}

/// Lift a single instruction into an r2il block.
///
/// Returns NULL on failure or if the context lacks a disassembler.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_lift(
    ctx: *mut R2ILContext,
    bytes: *const u8,
    len: usize,
    addr: u64,
) -> *mut R2ILBlock {
    if ctx.is_null() || bytes.is_null() || len == 0 {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &mut *ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let slice = unsafe { slice::from_raw_parts(bytes, len) };
    let lift_opts = SemanticMetadataOptions {
        enabled: ctx_ref.semantic_metadata_enabled,
        ..Default::default()
    };
    match disasm.lift_with_options(slice, addr, lift_opts) {
        Ok(block) => {
            if validate_block_in_context(ctx_ref, &block).is_err() {
                return ptr::null_mut();
            }
            ctx_ref.clear_error();
            Box::into_raw(Box::new(block))
        }
        Err(e) => {
            ctx_ref.set_error(e.to_string());
            ptr::null_mut()
        }
    }
}

/// Lift an entire basic block (multiple instructions) into an r2il block.
///
/// # Arguments
///
/// * `ctx` - The r2il context
/// * `bytes` - Instruction bytes for the block
/// * `len` - Length of the byte buffer
/// * `addr` - Starting address of the block
/// * `block_size` - Size of the basic block in bytes (from radare2)
///
/// Returns NULL on failure or if the context lacks a disassembler.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_lift_block(
    ctx: *mut R2ILContext,
    bytes: *const u8,
    len: usize,
    addr: u64,
    block_size: u32,
) -> *mut R2ILBlock {
    if ctx.is_null() || bytes.is_null() || len == 0 {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &mut *ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let slice = unsafe { slice::from_raw_parts(bytes, len) };
    let size = (block_size as usize).min(len);
    let lift_opts = SemanticMetadataOptions {
        enabled: ctx_ref.semantic_metadata_enabled,
        ..Default::default()
    };

    match disasm.lift_block_with_options(slice, addr, size, lift_opts) {
        Ok(block) => {
            if validate_block_in_context(ctx_ref, &block).is_err() {
                return ptr::null_mut();
            }
            ctx_ref.clear_error();
            Box::into_raw(Box::new(block))
        }
        Err(e) => {
            ctx_ref.set_error(e.to_string());
            ptr::null_mut()
        }
    }
}

/// Rewrite the logical address and size of a lifted block without touching its lifted ops.
///
/// This is used by the C wrapper to keep CFG ownership stable when a block must be
/// re-lifted from a recovered instruction boundary inside the original radare2 block.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_rewrite_layout(block: *mut R2ILBlock, addr: u64, size: u32) {
    if block.is_null() {
        return;
    }

    let block = unsafe { &mut *block };
    block.addr = addr;
    block.size = size;
}

/// Create a synthetic direct-branch block for CFG healing.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_new_branch(
    addr: u64,
    size: u32,
    target: u64,
    target_size: u32,
) -> *mut R2ILBlock {
    let mut block = R2ILBlock::new(addr, size);
    block.push(R2ILOp::Branch {
        target: Varnode::constant(target, target_size.max(1)),
    });
    Box::into_raw(Box::new(block))
}

/// Enable/disable semantic metadata auto-population during lifting.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_set_semantic_metadata_enabled(ctx: *mut R2ILContext, enabled: bool) {
    if ctx.is_null() {
        return;
    }
    let ctx_ref = unsafe { &mut *ctx };
    ctx_ref.semantic_metadata_enabled = enabled;
}

/// Free a lifted block.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_free(block: *mut R2ILBlock) {
    if !block.is_null() {
        unsafe { drop(Box::from_raw(block)) }
    }
}

/// Set switch table information for a block.
/// This should be called after lifting if the block contains a switch statement.
///
/// # Arguments
/// * `block` - The block to set switch info on
/// * `switch_addr` - Address of the switch instruction
/// * `min_val` - Minimum case value
/// * `max_val` - Maximum case value  
/// * `default_target` - Default case target address (0 if none)
/// * `case_values` - Array of case values
/// * `case_targets` - Array of case target addresses
/// * `num_cases` - Number of cases
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_set_switch_info(
    block: *mut R2ILBlock,
    switch_addr: u64,
    min_val: u64,
    max_val: u64,
    default_target: u64,
    case_values: *const u64,
    case_targets: *const u64,
    num_cases: usize,
) {
    if block.is_null() || case_values.is_null() || case_targets.is_null() {
        return;
    }

    let block = unsafe { &mut *block };

    // Build cases from arrays
    let mut cases = Vec::with_capacity(num_cases);
    for i in 0..num_cases {
        let value = unsafe { *case_values.add(i) };
        let target = unsafe { *case_targets.add(i) };
        cases.push(r2il::SwitchCase { value, target });
    }

    // Canonicalize radare2 switch metadata into the stricter R2IL invariant:
    // one case value has one deterministic target.
    cases.sort_by_key(|c| (c.value, c.target));
    cases.dedup_by_key(|c| c.value);

    let switch_info = r2il::SwitchInfo {
        switch_addr,
        min_val,
        max_val,
        default_target: if default_target != 0 {
            Some(default_target)
        } else {
            None
        },
        cases,
    };

    block.set_switch_info(switch_info);
}

/// Validate a lifted block against full (structural + semantic) r2il invariants.
///
/// Returns 1 when valid, 0 on invalid input or validation failure.
/// On validation failure, the context error string is updated.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_validate(ctx: *mut R2ILContext, block: *const R2ILBlock) -> i32 {
    if ctx.is_null() || block.is_null() {
        return 0;
    }

    let ctx_ref = unsafe { &mut *ctx };
    let block_ref = unsafe { &*block };

    let Some(arch) = ctx_ref.arch.as_ref() else {
        ctx_ref.set_error("missing arch context for semantic validation");
        return 0;
    };

    match validate_block_full(block_ref, arch) {
        Ok(()) => {
            ctx_ref.clear_error();
            1
        }
        Err(e) => {
            ctx_ref.set_error(format!("Invalid block: {}", e));
            0
        }
    }
}

/// Get the number of operations in a block.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_op_count(block: *const R2ILBlock) -> usize {
    if block.is_null() {
        return 0;
    }
    unsafe { (*block).ops.len() }
}

/// Get the ESIL string for a block (one line per op, joined with ';').
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_to_esil(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let input = InstructionExportInput {
        disasm,
        arch: match ctx_ref.arch.as_ref() {
            Some(a) => a,
            None => return ptr::null_mut(),
        },
        block: blk,
        addr: blk.addr,
        mnemonic: "",
        native_size: blk.size as usize,
    };
    match export_instruction(&input, InstructionAction::Lift, ExportFormat::Esil) {
        Ok(esil_lines) => {
            let joined = esil_lines
                .lines()
                .filter(|line| !line.is_empty())
                .collect::<Vec<_>>()
                .join(";");
            CString::new(joined).map_or(ptr::null_mut(), |s| s.into_raw())
        }
        Err(_) => ptr::null_mut(),
    }
}

/// Get a JSON representation of an operation in a block.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_op_json(block: *const R2ILBlock, index: usize) -> *mut c_char {
    if block.is_null() {
        return ptr::null_mut();
    }

    let blk = unsafe { &*block };
    if index >= blk.ops.len() {
        return ptr::null_mut();
    }

    match serde_json::to_string(&blk.ops[index]) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Get a JSON representation of an operation with register names resolved.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_op_json_named(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
    index: usize,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    if index >= blk.ops.len() {
        return ptr::null_mut();
    }

    match op_json_named(disasm, &blk.ops[index]) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Get the instruction size in bytes.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_size(block: *const R2ILBlock) -> u32 {
    if block.is_null() {
        return 0;
    }
    unsafe { (*block).size }
}

/// Get the block address.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_addr(block: *const R2ILBlock) -> u64 {
    if block.is_null() {
        return 0;
    }
    unsafe { (*block).addr }
}

/// Get the disassembly mnemonic for the instruction.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_mnemonic(
    ctx: *const R2ILContext,
    bytes: *const u8,
    len: usize,
    addr: u64,
) -> *mut c_char {
    if ctx.is_null() || bytes.is_null() || len == 0 {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let slice = unsafe { slice::from_raw_parts(bytes, len) };
    match disasm.disasm_native(slice, addr) {
        Ok((mnemonic, _size)) => CString::new(mnemonic).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Radare2 operation type constants (subset).
/// These match R_ANAL_OP_TYPE_* from radare2.
#[repr(C)]
pub struct R2AnalOpType;

impl R2AnalOpType {
    pub const NULL: u32 = 0;
    pub const JMP: u32 = 1;
    pub const UJMP: u32 = 2;
    pub const CJMP: u32 = 0x80000001; // JMP | COND
    pub const CALL: u32 = 3;
    pub const UCALL: u32 = 4;
    pub const RET: u32 = 5;
    pub const ILL: u32 = 6;
    pub const UNK: u32 = 7;
    pub const NOP: u32 = 8;
    pub const MOV: u32 = 9;
    pub const TRAP: u32 = 10;
    pub const SWI: u32 = 11;
    pub const PUSH: u32 = 13;
    pub const POP: u32 = 14;
    pub const CMP: u32 = 15;
    pub const ADD: u32 = 17;
    pub const SUB: u32 = 18;
    pub const MUL: u32 = 20;
    pub const DIV: u32 = 21;
    pub const SHR: u32 = 22;
    pub const SHL: u32 = 23;
    pub const SAR: u32 = 25;
    pub const OR: u32 = 26;
    pub const AND: u32 = 27;
    pub const XOR: u32 = 28;
    pub const NOT: u32 = 30;
    pub const STORE: u32 = 31;
    pub const LOAD: u32 = 32;
}

/// Infer the R_ANAL_OP_TYPE from the r2il operations in a block.
/// Returns R_ANAL_OP_TYPE_* constant.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_type(block: *const R2ILBlock) -> u32 {
    if block.is_null() {
        return R2AnalOpType::NULL;
    }

    let blk = unsafe { &*block };

    // Scan operations to determine instruction type
    // Priority: control flow > memory > arithmetic
    for op in &blk.ops {
        match op {
            R2ILOp::Return { .. } => return R2AnalOpType::RET,
            R2ILOp::Call { .. } => return R2AnalOpType::CALL,
            R2ILOp::CallInd { .. } => return R2AnalOpType::UCALL,
            R2ILOp::Branch { .. } => return R2AnalOpType::JMP,
            R2ILOp::BranchInd { .. } => return R2AnalOpType::UJMP,
            R2ILOp::CBranch { .. } => return R2AnalOpType::CJMP,
            _ => {}
        }
    }

    // Second pass: memory operations
    for op in &blk.ops {
        match op {
            R2ILOp::Store { .. }
            | R2ILOp::StoreConditional { .. }
            | R2ILOp::StoreGuarded { .. }
            | R2ILOp::AtomicCAS { .. } => return R2AnalOpType::STORE,
            R2ILOp::Load { .. } | R2ILOp::LoadLinked { .. } | R2ILOp::LoadGuarded { .. } => {
                return R2AnalOpType::LOAD;
            }
            _ => {}
        }
    }

    // Third pass: arithmetic/logic
    for op in &blk.ops {
        match op {
            R2ILOp::IntAdd { .. } => return R2AnalOpType::ADD,
            R2ILOp::IntSub { .. } => return R2AnalOpType::SUB,
            R2ILOp::IntMult { .. } => return R2AnalOpType::MUL,
            R2ILOp::IntDiv { .. } | R2ILOp::IntSDiv { .. } => return R2AnalOpType::DIV,
            R2ILOp::IntAnd { .. } => return R2AnalOpType::AND,
            R2ILOp::IntOr { .. } => return R2AnalOpType::OR,
            R2ILOp::IntXor { .. } => return R2AnalOpType::XOR,
            R2ILOp::IntNot { .. } => return R2AnalOpType::NOT,
            R2ILOp::IntLeft { .. } => return R2AnalOpType::SHL,
            R2ILOp::IntRight { .. } => return R2AnalOpType::SHR,
            R2ILOp::IntSRight { .. } => return R2AnalOpType::SAR,
            R2ILOp::IntEqual { .. }
            | R2ILOp::IntNotEqual { .. }
            | R2ILOp::IntLess { .. }
            | R2ILOp::IntSLess { .. }
            | R2ILOp::IntLessEqual { .. }
            | R2ILOp::IntSLessEqual { .. } => return R2AnalOpType::CMP,
            R2ILOp::Copy { .. } => return R2AnalOpType::MOV,
            _ => {}
        }
    }

    // Default: unknown
    if blk.ops.is_empty() {
        R2AnalOpType::NOP
    } else {
        R2AnalOpType::UNK
    }
}

/// Get the jump target address from a block (for JMP/CALL instructions).
/// Returns 0 if no jump target is found or if indirect.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_jump(block: *const R2ILBlock) -> u64 {
    if block.is_null() {
        return 0;
    }

    let blk = unsafe { &*block };

    for op in &blk.ops {
        match op {
            R2ILOp::Branch { target }
            | R2ILOp::Call { target }
            | R2ILOp::CBranch { target, .. } => {
                // Only return if target is a constant (direct jump)
                if target.space == r2il::SpaceId::Const || target.space == r2il::SpaceId::Ram {
                    return target.offset;
                }
            }
            _ => {}
        }
    }

    0
}

/// Get the fall-through address (for conditional jumps).
/// Returns addr + size for conditional branches, 0 otherwise.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_fail(block: *const R2ILBlock) -> u64 {
    if block.is_null() {
        return 0;
    }

    let blk = unsafe { &*block };

    // Check if this is a conditional branch
    for op in &blk.ops {
        if matches!(op, R2ILOp::CBranch { .. }) {
            return blk.addr + blk.size as u64;
        }
    }

    0
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_has_trailing_indirect_branch(block: *const R2ILBlock) -> bool {
    if block.is_null() {
        return false;
    }

    let blk = unsafe { &*block };
    matches!(blk.ops.last(), Some(R2ILOp::BranchInd { .. }))
}

/// Free a string returned by r2il functions.
#[unsafe(no_mangle)]
pub extern "C" fn r2il_string_free(s: *mut c_char) {
    if !s.is_null() {
        unsafe { drop(CString::from_raw(s)) };
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_has_native_worker_summary_family_ffi(name: *const c_char) -> bool {
    if name.is_null() {
        return false;
    }
    let Ok(name) = (unsafe { CStr::from_ptr(name) }).to_str() else {
        return false;
    };
    r2sym::has_native_worker_summary_family(name)
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_direct_named_worker_decompile_ffi(name: *const c_char) -> bool {
    if name.is_null() {
        return false;
    }
    let Ok(name) = (unsafe { CStr::from_ptr(name) }).to_str() else {
        return false;
    };
    r2engine::should_use_direct_named_native_worker_decompile(name)
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_direct_named_worker_type_projection_ffi(name: *const c_char) -> bool {
    if name.is_null() {
        return false;
    }
    let Ok(name) = (unsafe { CStr::from_ptr(name) }).to_str() else {
        return false;
    };
    r2engine::should_use_direct_named_native_worker_type_projection(name)
}

// ========== Typed Analysis FFI ==========

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::Hash;
use std::sync::{Arc, LazyLock, RwLock};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2ILBlockMemAccess {
    is_write: i32,
    size: u32,
    addr_reg: *const c_char,
    base: u64,
    has_base: i32,
    delta: i64,
    is_stack: i32,
    stack_base: *const c_char,
    stack_offset: i64,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2ILBlockImmediateValue {
    value: u64,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2ILBlockRegValue {
    name: *const c_char,
}

pub struct R2ILBlockAnalValues {
    memory: Vec<R2ILBlockMemAccess>,
    immediates: Vec<R2ILBlockImmediateValue>,
    reg_reads: Vec<R2ILBlockRegValue>,
    reg_writes: Vec<R2ILBlockRegValue>,
    _strings: Vec<CString>,
}

fn ffi_values_push_string(strings: &mut Vec<CString>, value: impl AsRef<str>) -> *const c_char {
    match CString::new(value.as_ref()) {
        Ok(s) => {
            strings.push(s);
            strings.last().map_or(ptr::null(), |s| s.as_ptr())
        }
        Err(_) => ptr::null(),
    }
}

/// Helper: extract all register varnodes that are read by an operation.
fn op_regs_read(op: &R2ILOp) -> Vec<&Varnode> {
    let mut regs = Vec::new();

    match op {
        // Data movement - src is read
        R2ILOp::Copy { src, .. } => {
            if src.is_register() {
                regs.push(src);
            }
        }
        R2ILOp::Load { addr, .. } => {
            if addr.is_register() {
                regs.push(addr);
            }
        }
        R2ILOp::LoadLinked { addr, .. } => {
            if addr.is_register() {
                regs.push(addr);
            }
        }
        R2ILOp::Store { addr, val, .. } => {
            if addr.is_register() {
                regs.push(addr);
            }
            if val.is_register() {
                regs.push(val);
            }
        }
        R2ILOp::StoreConditional { addr, val, .. } => {
            if addr.is_register() {
                regs.push(addr);
            }
            if val.is_register() {
                regs.push(val);
            }
        }
        R2ILOp::AtomicCAS {
            addr,
            expected,
            replacement,
            ..
        } => {
            if addr.is_register() {
                regs.push(addr);
            }
            if expected.is_register() {
                regs.push(expected);
            }
            if replacement.is_register() {
                regs.push(replacement);
            }
        }
        R2ILOp::LoadGuarded { addr, guard, .. } => {
            if addr.is_register() {
                regs.push(addr);
            }
            if guard.is_register() {
                regs.push(guard);
            }
        }
        R2ILOp::StoreGuarded {
            addr, val, guard, ..
        } => {
            if addr.is_register() {
                regs.push(addr);
            }
            if val.is_register() {
                regs.push(val);
            }
            if guard.is_register() {
                regs.push(guard);
            }
        }

        // Binary ops - a and b are read
        R2ILOp::IntAdd { a, b, .. }
        | R2ILOp::IntSub { a, b, .. }
        | R2ILOp::IntMult { a, b, .. }
        | R2ILOp::IntDiv { a, b, .. }
        | R2ILOp::IntSDiv { a, b, .. }
        | R2ILOp::IntRem { a, b, .. }
        | R2ILOp::IntSRem { a, b, .. }
        | R2ILOp::IntAnd { a, b, .. }
        | R2ILOp::IntOr { a, b, .. }
        | R2ILOp::IntXor { a, b, .. }
        | R2ILOp::IntLeft { a, b, .. }
        | R2ILOp::IntRight { a, b, .. }
        | R2ILOp::IntSRight { a, b, .. }
        | R2ILOp::IntEqual { a, b, .. }
        | R2ILOp::IntNotEqual { a, b, .. }
        | R2ILOp::IntLess { a, b, .. }
        | R2ILOp::IntSLess { a, b, .. }
        | R2ILOp::IntLessEqual { a, b, .. }
        | R2ILOp::IntSLessEqual { a, b, .. }
        | R2ILOp::IntCarry { a, b, .. }
        | R2ILOp::IntSCarry { a, b, .. }
        | R2ILOp::IntSBorrow { a, b, .. }
        | R2ILOp::BoolAnd { a, b, .. }
        | R2ILOp::BoolOr { a, b, .. }
        | R2ILOp::BoolXor { a, b, .. }
        | R2ILOp::Piece { hi: a, lo: b, .. }
        | R2ILOp::FloatAdd { a, b, .. }
        | R2ILOp::FloatSub { a, b, .. }
        | R2ILOp::FloatMult { a, b, .. }
        | R2ILOp::FloatDiv { a, b, .. }
        | R2ILOp::FloatEqual { a, b, .. }
        | R2ILOp::FloatNotEqual { a, b, .. }
        | R2ILOp::FloatLess { a, b, .. }
        | R2ILOp::FloatLessEqual { a, b, .. } => {
            if a.is_register() {
                regs.push(a);
            }
            if b.is_register() {
                regs.push(b);
            }
        }

        // Unary ops - src is read
        R2ILOp::IntNegate { src, .. }
        | R2ILOp::IntNot { src, .. }
        | R2ILOp::IntZExt { src, .. }
        | R2ILOp::IntSExt { src, .. }
        | R2ILOp::BoolNot { src, .. }
        | R2ILOp::PopCount { src, .. }
        | R2ILOp::Lzcount { src, .. }
        | R2ILOp::Subpiece { src, .. }
        | R2ILOp::FloatNeg { src, .. }
        | R2ILOp::FloatAbs { src, .. }
        | R2ILOp::FloatSqrt { src, .. }
        | R2ILOp::FloatNaN { src, .. }
        | R2ILOp::Int2Float { src, .. }
        | R2ILOp::FloatFloat { src, .. }
        | R2ILOp::Trunc { src, .. }
        | R2ILOp::FloatCeil { src, .. }
        | R2ILOp::FloatFloor { src, .. }
        | R2ILOp::FloatRound { src, .. } => {
            if src.is_register() {
                regs.push(src);
            }
        }

        // Control flow - target/cond are read
        R2ILOp::Branch { target }
        | R2ILOp::BranchInd { target }
        | R2ILOp::Call { target }
        | R2ILOp::CallInd { target }
        | R2ILOp::Return { target } => {
            if target.is_register() {
                regs.push(target);
            }
        }
        R2ILOp::CBranch { cond, target } => {
            if cond.is_register() {
                regs.push(cond);
            }
            if target.is_register() {
                regs.push(target);
            }
        }

        // CallOther - inputs are read
        R2ILOp::CallOther { inputs, .. } => {
            for inp in inputs {
                if inp.is_register() {
                    regs.push(inp);
                }
            }
        }

        // Float2Int - src is read
        R2ILOp::Float2Int { src, .. } | R2ILOp::New { src, .. } | R2ILOp::Cast { src, .. } => {
            if src.is_register() {
                regs.push(src);
            }
        }

        // Extract - src and position are read
        R2ILOp::Extract { src, position, .. } => {
            if src.is_register() {
                regs.push(src);
            }
            if position.is_register() {
                regs.push(position);
            }
        }

        // Insert - src, value, position are read
        R2ILOp::Insert {
            src,
            value,
            position,
            ..
        } => {
            if src.is_register() {
                regs.push(src);
            }
            if value.is_register() {
                regs.push(value);
            }
            if position.is_register() {
                regs.push(position);
            }
        }

        // SegmentOp - segment and offset are read
        R2ILOp::SegmentOp {
            segment, offset, ..
        } => {
            if segment.is_register() {
                regs.push(segment);
            }
            if offset.is_register() {
                regs.push(offset);
            }
        }

        // PtrAdd/PtrSub - base and index are read
        R2ILOp::PtrAdd { base, index, .. } | R2ILOp::PtrSub { base, index, .. } => {
            if base.is_register() {
                regs.push(base);
            }
            if index.is_register() {
                regs.push(index);
            }
        }

        // Multiequal - inputs are read
        R2ILOp::Multiequal { inputs, .. } => {
            for inp in inputs {
                if inp.is_register() {
                    regs.push(inp);
                }
            }
        }

        // Indirect - src and indirect are read
        R2ILOp::Indirect { src, indirect, .. } => {
            if src.is_register() {
                regs.push(src);
            }
            if indirect.is_register() {
                regs.push(indirect);
            }
        }

        // Ops with no register reads
        R2ILOp::Fence { .. }
        | R2ILOp::Nop
        | R2ILOp::Unimplemented
        | R2ILOp::Breakpoint
        | R2ILOp::CpuId { .. } => {}
    }

    regs
}

/// Helper: extract all register varnodes that are written by an operation.
fn op_regs_write(op: &R2ILOp) -> Vec<&Varnode> {
    let mut regs = Vec::new();

    match op {
        // All ops with dst field write to dst
        R2ILOp::Copy { dst, .. }
        | R2ILOp::Load { dst, .. }
        | R2ILOp::LoadLinked { dst, .. }
        | R2ILOp::AtomicCAS { dst, .. }
        | R2ILOp::LoadGuarded { dst, .. }
        | R2ILOp::IntAdd { dst, .. }
        | R2ILOp::IntSub { dst, .. }
        | R2ILOp::IntMult { dst, .. }
        | R2ILOp::IntDiv { dst, .. }
        | R2ILOp::IntSDiv { dst, .. }
        | R2ILOp::IntRem { dst, .. }
        | R2ILOp::IntSRem { dst, .. }
        | R2ILOp::IntNegate { dst, .. }
        | R2ILOp::IntAnd { dst, .. }
        | R2ILOp::IntOr { dst, .. }
        | R2ILOp::IntXor { dst, .. }
        | R2ILOp::IntNot { dst, .. }
        | R2ILOp::IntLeft { dst, .. }
        | R2ILOp::IntRight { dst, .. }
        | R2ILOp::IntSRight { dst, .. }
        | R2ILOp::IntEqual { dst, .. }
        | R2ILOp::IntNotEqual { dst, .. }
        | R2ILOp::IntLess { dst, .. }
        | R2ILOp::IntSLess { dst, .. }
        | R2ILOp::IntLessEqual { dst, .. }
        | R2ILOp::IntSLessEqual { dst, .. }
        | R2ILOp::IntZExt { dst, .. }
        | R2ILOp::IntSExt { dst, .. }
        | R2ILOp::IntCarry { dst, .. }
        | R2ILOp::IntSCarry { dst, .. }
        | R2ILOp::IntSBorrow { dst, .. }
        | R2ILOp::BoolAnd { dst, .. }
        | R2ILOp::BoolOr { dst, .. }
        | R2ILOp::BoolXor { dst, .. }
        | R2ILOp::BoolNot { dst, .. }
        | R2ILOp::PopCount { dst, .. }
        | R2ILOp::Lzcount { dst, .. }
        | R2ILOp::Piece { dst, .. }
        | R2ILOp::Subpiece { dst, .. }
        | R2ILOp::FloatAdd { dst, .. }
        | R2ILOp::FloatSub { dst, .. }
        | R2ILOp::FloatMult { dst, .. }
        | R2ILOp::FloatDiv { dst, .. }
        | R2ILOp::FloatNeg { dst, .. }
        | R2ILOp::FloatAbs { dst, .. }
        | R2ILOp::FloatSqrt { dst, .. }
        | R2ILOp::FloatEqual { dst, .. }
        | R2ILOp::FloatNotEqual { dst, .. }
        | R2ILOp::FloatLess { dst, .. }
        | R2ILOp::FloatLessEqual { dst, .. }
        | R2ILOp::FloatNaN { dst, .. }
        | R2ILOp::Int2Float { dst, .. }
        | R2ILOp::FloatFloat { dst, .. }
        | R2ILOp::Trunc { dst, .. }
        | R2ILOp::FloatCeil { dst, .. }
        | R2ILOp::FloatFloor { dst, .. }
        | R2ILOp::FloatRound { dst, .. } => {
            if dst.is_register() {
                regs.push(dst);
            }
        }

        // Store doesn't have a register dst
        R2ILOp::Store { .. } => {}
        R2ILOp::StoreConditional { result, .. } => {
            if let Some(out) = result
                && out.is_register()
            {
                regs.push(out);
            }
        }
        R2ILOp::StoreGuarded { .. } => {}

        // Control flow ops don't write registers directly
        R2ILOp::Branch { .. }
        | R2ILOp::BranchInd { .. }
        | R2ILOp::CBranch { .. }
        | R2ILOp::Call { .. }
        | R2ILOp::CallInd { .. }
        | R2ILOp::Return { .. } => {}

        // CallOther may have output
        R2ILOp::CallOther { output, .. } => {
            if let Some(out) = output
                && out.is_register()
            {
                regs.push(out);
            }
        }

        // Ops with dst field that write
        R2ILOp::Float2Int { dst, .. }
        | R2ILOp::CpuId { dst, .. }
        | R2ILOp::SegmentOp { dst, .. }
        | R2ILOp::New { dst, .. }
        | R2ILOp::Cast { dst, .. }
        | R2ILOp::Extract { dst, .. }
        | R2ILOp::Insert { dst, .. }
        | R2ILOp::Multiequal { dst, .. }
        | R2ILOp::Indirect { dst, .. }
        | R2ILOp::PtrAdd { dst, .. }
        | R2ILOp::PtrSub { dst, .. } => {
            if dst.is_register() {
                regs.push(dst);
            }
        }

        // Ops with no register writes
        R2ILOp::Fence { .. } | R2ILOp::Nop | R2ILOp::Unimplemented | R2ILOp::Breakpoint => {}
    }

    regs
}

/// Get registers read by the block as JSON array of names.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_regs_read(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let mut regs = BTreeSet::new();

    for op in &blk.ops {
        for reg in op_regs_read(op) {
            if let Some(name) = disasm.register_name(reg) {
                regs.insert(name);
            }
        }
    }

    let json_array =
        serde_json::to_string(&regs.into_iter().collect::<Vec<_>>()).unwrap_or_default();
    CString::new(json_array).map_or(ptr::null_mut(), |c| c.into_raw())
}

/// Get memory accesses by the block as JSON array.
/// Each entry includes legacy fields (`addr`, `size`, `write`) and richer metadata.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_mem_access(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let defs = build_stack_defs(&blk.ops);
    let mut accesses = Vec::new();

    let apply_additive_fields = |access: &mut serde_json::Value,
                                 op_index: usize,
                                 space_id: Option<r2il::SpaceId>,
                                 ordering: Option<r2il::MemoryOrdering>,
                                 atomic_kind: Option<r2il::AtomicKind>,
                                 guarded: bool| {
        if guarded {
            access["guarded"] = serde_json::Value::Bool(true);
        }
        if let Some(ord) = ordering.or_else(|| {
            blk.op_metadata
                .get(&op_index)
                .and_then(|m| m.memory_ordering)
        }) {
            access["ordering"] = serde_json::to_value(ord).unwrap_or(serde_json::Value::Null);
        }
        if let Some(kind) =
            atomic_kind.or_else(|| blk.op_metadata.get(&op_index).and_then(|m| m.atomic_kind))
        {
            access["atomic_kind"] = serde_json::to_value(kind).unwrap_or(serde_json::Value::Null);
        }
        if let Some(meta) = blk.op_metadata.get(&op_index) {
            if let Some(memory_class) = meta.memory_class {
                access["memory_class"] =
                    serde_json::to_value(memory_class).unwrap_or(serde_json::Value::Null);
            }
            if let Some(perms) = meta.permissions {
                access["permissions"] =
                    serde_json::to_value(perms).unwrap_or(serde_json::Value::Null);
            }
            if let Some(range) = meta.valid_range {
                access["range"] = serde_json::to_value(range).unwrap_or(serde_json::Value::Null);
            }
            if let Some(bank_id) = &meta.bank_id {
                access["bank_id"] = serde_json::Value::String(bank_id.clone());
            }
            if let Some(segment_id) = &meta.segment_id {
                access["segment_id"] = serde_json::Value::String(segment_id.clone());
            }
        }

        if let Some(space_id) = space_id
            && let Some(arch) = ctx_ref.arch.as_ref()
            && let Some(space) = arch.spaces.iter().find(|s| s.id == space_id)
        {
            if let Some(memory_class) = space.memory_class {
                access["memory_class"] =
                    serde_json::to_value(memory_class).unwrap_or(serde_json::Value::Null);
            }
            if access.get("permissions").is_none()
                && let Some(perms) = space.permissions
            {
                access["permissions"] =
                    serde_json::to_value(perms).unwrap_or(serde_json::Value::Null);
            }
            if access.get("range").is_none()
                && let Some(range) = space.valid_ranges.first()
            {
                access["range"] = serde_json::to_value(range).unwrap_or(serde_json::Value::Null);
            }
            if access.get("bank_id").is_none()
                && let Some(bank_id) = &space.bank_id
            {
                access["bank_id"] = serde_json::Value::String(bank_id.clone());
            }
            if access.get("segment_id").is_none()
                && let Some(segment_id) = &space.segment_id
            {
                access["segment_id"] = serde_json::Value::String(segment_id.clone());
            }
        }
    };

    for (op_index, op) in blk.ops.iter().enumerate() {
        match op {
            R2ILOp::Load { dst, space, addr } => {
                let mut access = serde_json::json!({
                    "type": "load",
                    "size": dst.size,
                    "write": false,
                    "addr": disasm.format_varnode(addr),
                });

                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }

                if let Some((base, offset)) = resolve_stack_addr(addr, disasm, &defs, &blk.ops) {
                    access["stack"] = serde_json::Value::Bool(true);
                    access["stack_offset"] = serde_json::Value::Number(offset.into());
                    access["stack_base"] = serde_json::Value::String(base);
                }

                apply_additive_fields(&mut access, op_index, Some(*space), None, None, false);
                accesses.push(access);
            }
            R2ILOp::LoadLinked {
                dst,
                space,
                addr,
                ordering,
            } => {
                let mut access = serde_json::json!({
                    "type": "load_linked",
                    "size": dst.size,
                    "write": false,
                    "addr": disasm.format_varnode(addr),
                });

                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }
                apply_additive_fields(
                    &mut access,
                    op_index,
                    Some(*space),
                    Some(*ordering),
                    Some(r2il::AtomicKind::LoadLinked),
                    false,
                );
                accesses.push(access);
            }
            R2ILOp::Store { space, addr, val } => {
                let mut access = serde_json::json!({
                    "type": "store",
                    "size": val.size,
                    "write": true,
                    "addr": disasm.format_varnode(addr),
                });

                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }
                if let Some(value) = varnode_to_json(val, disasm) {
                    access["value"] = value;
                }

                if let Some((base, offset)) = resolve_stack_addr(addr, disasm, &defs, &blk.ops) {
                    access["stack"] = serde_json::Value::Bool(true);
                    access["stack_offset"] = serde_json::Value::Number(offset.into());
                    access["stack_base"] = serde_json::Value::String(base);
                }

                apply_additive_fields(&mut access, op_index, Some(*space), None, None, false);
                accesses.push(access);
            }
            R2ILOp::StoreConditional {
                result,
                space,
                addr,
                val,
                ordering,
            } => {
                let mut access = serde_json::json!({
                    "type": "store_conditional",
                    "size": val.size,
                    "write": true,
                    "addr": disasm.format_varnode(addr),
                });
                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }
                if let Some(value) = varnode_to_json(val, disasm) {
                    access["value"] = value;
                }
                if let Some(dst) = result
                    && let Some(result_json) = varnode_to_json(dst, disasm)
                {
                    access["result"] = result_json;
                }
                apply_additive_fields(
                    &mut access,
                    op_index,
                    Some(*space),
                    Some(*ordering),
                    Some(r2il::AtomicKind::StoreConditional),
                    false,
                );
                accesses.push(access);
            }
            R2ILOp::AtomicCAS {
                dst,
                space,
                addr,
                expected,
                replacement,
                ordering,
            } => {
                let mut access = serde_json::json!({
                    "type": "atomic_cas",
                    "size": dst.size,
                    "write": true,
                    "addr": disasm.format_varnode(addr),
                });
                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }
                if let Some(value) = varnode_to_json(expected, disasm) {
                    access["expected"] = value;
                }
                if let Some(value) = varnode_to_json(replacement, disasm) {
                    access["replacement"] = value;
                }
                if let Some(value) = varnode_to_json(dst, disasm) {
                    access["result"] = value;
                }
                apply_additive_fields(
                    &mut access,
                    op_index,
                    Some(*space),
                    Some(*ordering),
                    Some(r2il::AtomicKind::CompareExchange),
                    false,
                );
                accesses.push(access);
            }
            R2ILOp::LoadGuarded {
                dst,
                space,
                addr,
                guard,
                ordering,
            } => {
                let mut access = serde_json::json!({
                    "type": "load_guarded",
                    "size": dst.size,
                    "write": false,
                    "addr": disasm.format_varnode(addr),
                });
                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }
                if let Some(value) = varnode_to_json(guard, disasm) {
                    access["guard"] = value;
                }
                apply_additive_fields(
                    &mut access,
                    op_index,
                    Some(*space),
                    Some(*ordering),
                    None,
                    true,
                );
                accesses.push(access);
            }
            R2ILOp::StoreGuarded {
                space,
                addr,
                val,
                guard,
                ordering,
            } => {
                let mut access = serde_json::json!({
                    "type": "store_guarded",
                    "size": val.size,
                    "write": true,
                    "addr": disasm.format_varnode(addr),
                });
                if let Some(detail) = varnode_to_json(addr, disasm) {
                    access["addr_detail"] = detail;
                }
                if let Some(value) = varnode_to_json(val, disasm) {
                    access["value"] = value;
                }
                if let Some(value) = varnode_to_json(guard, disasm) {
                    access["guard"] = value;
                }
                apply_additive_fields(
                    &mut access,
                    op_index,
                    Some(*space),
                    Some(*ordering),
                    None,
                    true,
                );
                accesses.push(access);
            }
            _ => {}
        }
    }

    let json = serde_json::to_string(&accesses).unwrap_or_default();
    CString::new(json).map_or(ptr::null_mut(), |c| c.into_raw())
}

/// Get all varnodes used by the block as JSON.
/// Includes registers, memory locations, constants, and temporaries.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_varnodes(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let mut seen: HashSet<(u8, u64, u32)> = HashSet::new();
    let mut varnodes: Vec<VarnodeInfo> = Vec::new();

    for op in &blk.ops {
        for vn in op_all_varnodes(op) {
            let space_id = match vn.space {
                r2il::SpaceId::Const => 0,
                r2il::SpaceId::Register => 1,
                r2il::SpaceId::Ram => 2,
                r2il::SpaceId::Unique => 3,
                r2il::SpaceId::Custom(n) => 4 + (n as u8),
            };
            let key = (space_id, vn.offset, vn.size);
            if seen.contains(&key) {
                continue;
            }
            seen.insert(key);

            let (name, space_str) = match vn.space {
                r2il::SpaceId::Const => (format!("0x{:x}", vn.offset), space_label(vn.space)),
                r2il::SpaceId::Register => {
                    let name = disasm
                        .register_name(vn)
                        .unwrap_or_else(|| format!("reg:0x{:x}", vn.offset));
                    (name, space_label(vn.space))
                }
                r2il::SpaceId::Ram => (format!("[0x{:x}]", vn.offset), space_label(vn.space)),
                r2il::SpaceId::Unique => (format!("tmp:0x{:x}", vn.offset), space_label(vn.space)),
                r2il::SpaceId::Custom(n) => (
                    format!("space{}:0x{:x}", n, vn.offset),
                    space_label(vn.space),
                ),
            };

            varnodes.push(VarnodeInfo {
                name,
                space: space_str,
                offset: vn.offset,
                size: vn.size,
                meta: vn.meta.clone(),
            });
        }
    }

    let json = serde_json::to_string(&varnodes).unwrap_or_default();
    CString::new(json).map_or(ptr::null_mut(), |c| c.into_raw())
}

fn block_values_for_ffi(
    ctx_ref: &R2ILContext,
    blk: &R2ILBlock,
    disasm: &Disassembler,
) -> R2ILBlockAnalValues {
    let defs = build_stack_defs(&blk.ops);
    let mut strings = Vec::new();
    let mut memory = Vec::new();
    let mut immediates = Vec::new();
    let mut seen_immediates: HashSet<(u64, u32)> = HashSet::new();
    let mut reg_reads = BTreeSet::new();
    let mut reg_writes = BTreeSet::new();

    for op in &blk.ops {
        for reg in op_regs_read(op) {
            if let Some(name) = disasm.register_name(reg) {
                reg_reads.insert(name);
            }
        }
        for reg in op_regs_write(op) {
            if let Some(name) = disasm.register_name(reg) {
                reg_writes.insert(name);
            }
        }
        for vn in op_all_varnodes(op) {
            if vn.space.is_const() && seen_immediates.insert((vn.offset, vn.size)) {
                immediates.push(R2ILBlockImmediateValue { value: vn.offset });
            }
        }
    }

    let mut push_mem = |addr: &Varnode, size: u32, is_write: bool| {
        let stack = resolve_stack_addr(addr, disasm, &defs, &blk.ops);
        let addr_reg = if addr.is_register() {
            disasm
                .register_name(addr)
                .map(|name| ffi_values_push_string(&mut strings, name))
                .unwrap_or(ptr::null())
        } else {
            ptr::null()
        };
        let (stack_base, stack_offset, is_stack) = match stack {
            Some((base, offset)) => (ffi_values_push_string(&mut strings, base), offset, 1),
            None => (ptr::null(), 0, 0),
        };
        memory.push(R2ILBlockMemAccess {
            is_write: i32::from(is_write),
            size,
            addr_reg,
            base: if addr.is_register() { 0 } else { addr.offset },
            has_base: i32::from(!addr.is_register()),
            delta: if addr.is_register() {
                addr.offset as i64
            } else {
                0
            },
            is_stack,
            stack_base,
            stack_offset,
        });
    };

    for op in &blk.ops {
        match op {
            R2ILOp::Load { dst, addr, .. }
            | R2ILOp::LoadLinked { dst, addr, .. }
            | R2ILOp::LoadGuarded { dst, addr, .. } => {
                push_mem(addr, dst.size, false);
            }
            R2ILOp::Store { addr, val, .. }
            | R2ILOp::StoreConditional { addr, val, .. }
            | R2ILOp::StoreGuarded { addr, val, .. } => {
                push_mem(addr, val.size, true);
            }
            R2ILOp::AtomicCAS { dst, addr, .. } => {
                push_mem(addr, dst.size, true);
            }
            _ => {}
        }
    }

    let reg_reads = reg_reads
        .into_iter()
        .filter_map(|name| {
            let ptr = ffi_values_push_string(&mut strings, name);
            (!ptr.is_null()).then_some(R2ILBlockRegValue { name: ptr })
        })
        .collect();
    let reg_writes = reg_writes
        .into_iter()
        .filter_map(|name| {
            let ptr = ffi_values_push_string(&mut strings, name);
            (!ptr.is_null()).then_some(R2ILBlockRegValue { name: ptr })
        })
        .collect();

    let _ = ctx_ref;
    R2ILBlockAnalValues {
        memory,
        immediates,
        reg_reads,
        reg_writes,
        _strings: strings,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_values_typed(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut R2ILBlockAnalValues {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }
    let ctx_ref = unsafe { &*ctx };
    let Some(disasm) = ctx_ref.disasm.as_ref() else {
        return ptr::null_mut();
    };
    let blk = unsafe { &*block };
    Box::into_raw(Box::new(block_values_for_ffi(ctx_ref, blk, disasm)))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_values_memory(
    values: *const R2ILBlockAnalValues,
    count: *mut usize,
) -> *const R2ILBlockMemAccess {
    if values.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let values = unsafe { &*values };
    if !count.is_null() {
        unsafe {
            *count = values.memory.len();
        }
    }
    values.memory.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_values_immediates(
    values: *const R2ILBlockAnalValues,
    count: *mut usize,
) -> *const R2ILBlockImmediateValue {
    if values.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let values = unsafe { &*values };
    if !count.is_null() {
        unsafe {
            *count = values.immediates.len();
        }
    }
    values.immediates.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_values_reg_reads(
    values: *const R2ILBlockAnalValues,
    count: *mut usize,
) -> *const R2ILBlockRegValue {
    if values.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let values = unsafe { &*values };
    if !count.is_null() {
        unsafe {
            *count = values.reg_reads.len();
        }
    }
    values.reg_reads.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_values_reg_writes(
    values: *const R2ILBlockAnalValues,
    count: *mut usize,
) -> *const R2ILBlockRegValue {
    if values.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let values = unsafe { &*values };
    if !count.is_null() {
        unsafe {
            *count = values.reg_writes.len();
        }
    }
    values.reg_writes.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_values_free(values: *mut R2ILBlockAnalValues) {
    if !values.is_null() {
        unsafe {
            drop(Box::from_raw(values));
        }
    }
}

fn space_label(space: r2il::SpaceId) -> String {
    match space {
        r2il::SpaceId::Const => "const".to_string(),
        r2il::SpaceId::Register => "register".to_string(),
        r2il::SpaceId::Ram => "ram".to_string(),
        r2il::SpaceId::Unique => "unique".to_string(),
        r2il::SpaceId::Custom(id) => format!("custom:{}", id),
    }
}

/// Helper: convert a varnode to JSON with register names resolved.
fn varnode_to_json(vn: &Varnode, disasm: &Disassembler) -> Option<serde_json::Value> {
    let mut json = serde_json::json!({
        "space": space_label(vn.space),
        "offset": vn.offset,
        "size": vn.size,
    });

    if vn.is_register()
        && let Some(name) = disasm.register_name(vn)
    {
        json["name"] = serde_json::Value::String(name);
    }
    if let Some(meta) = vn.meta.as_ref() {
        json["meta"] = serde_json::to_value(meta).ok()?;
    }

    Some(json)
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct VarnodeKey {
    space: r2il::SpaceId,
    offset: u64,
    size: u32,
}

fn varnode_key(vn: &Varnode) -> VarnodeKey {
    VarnodeKey {
        space: vn.space,
        offset: vn.offset,
        size: vn.size,
    }
}

fn const_value(vn: &Varnode) -> Option<i64> {
    if vn.space.is_const() {
        Some(vn.offset as i64)
    } else {
        None
    }
}

fn is_stack_reg_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("sp") || lower.contains("bp") || lower.contains("fp")
}

fn stack_reg_name(vn: &Varnode, disasm: &Disassembler) -> Option<String> {
    if !vn.is_register() {
        return None;
    }
    let name = disasm.register_name(vn)?;
    if is_stack_reg_name(&name) {
        Some(name)
    } else {
        None
    }
}

fn build_stack_defs(ops: &[R2ILOp]) -> HashMap<VarnodeKey, usize> {
    let mut defs = HashMap::new();
    for (idx, op) in ops.iter().enumerate() {
        let dst = match op {
            R2ILOp::Copy { dst, .. }
            | R2ILOp::IntAdd { dst, .. }
            | R2ILOp::IntSub { dst, .. }
            | R2ILOp::PtrAdd { dst, .. }
            | R2ILOp::PtrSub { dst, .. } => Some(dst),
            _ => None,
        };
        if let Some(dst) = dst {
            defs.insert(varnode_key(dst), idx);
        }
    }
    defs
}

/// Maximum depth for stack address resolution recursion.
/// This limit of 8 prevents infinite recursion in cyclic definitions while being
/// deep enough for typical stack address calculations like:
///   rbp -> temp1 (copy) -> temp2 (add offset) -> temp3 (sub) -> final address
/// In practice, most stack accesses resolve within 2-4 levels.
const STACK_RESOLVE_MAX_DEPTH: usize = 8;

fn resolve_stack_addr(
    vn: &Varnode,
    disasm: &Disassembler,
    defs: &HashMap<VarnodeKey, usize>,
    ops: &[R2ILOp],
) -> Option<(String, i64)> {
    let mut visited = HashSet::new();
    resolve_stack_addr_inner(vn, disasm, defs, ops, &mut visited, 0)
}

fn resolve_stack_addr_inner(
    vn: &Varnode,
    disasm: &Disassembler,
    defs: &HashMap<VarnodeKey, usize>,
    ops: &[R2ILOp],
    visited: &mut HashSet<VarnodeKey>,
    depth: usize,
) -> Option<(String, i64)> {
    if depth > STACK_RESOLVE_MAX_DEPTH {
        return None;
    }
    if let Some(name) = stack_reg_name(vn, disasm) {
        return Some((name, 0));
    }
    if !vn.space.is_unique() {
        return None;
    }

    let key = varnode_key(vn);
    if !visited.insert(key) {
        return None;
    }
    let idx = defs.get(&key)?;
    let op = &ops[*idx];

    match op {
        R2ILOp::Copy { src, .. } => {
            resolve_stack_addr_inner(src, disasm, defs, ops, visited, depth + 1)
        }
        R2ILOp::IntAdd { a, b, .. } => {
            if let Some((base, off)) =
                resolve_stack_addr_inner(a, disasm, defs, ops, visited, depth + 1)
                && let Some(c) = const_value(b)
            {
                return Some((base, off + c));
            }
            if let Some((base, off)) =
                resolve_stack_addr_inner(b, disasm, defs, ops, visited, depth + 1)
                && let Some(c) = const_value(a)
            {
                return Some((base, off + c));
            }
            None
        }
        R2ILOp::IntSub { a, b, .. } => {
            if let Some((base, off)) =
                resolve_stack_addr_inner(a, disasm, defs, ops, visited, depth + 1)
                && let Some(c) = const_value(b)
            {
                return Some((base, off - c));
            }
            None
        }
        R2ILOp::PtrAdd {
            base,
            index,
            element_size,
            ..
        } => {
            if let Some((base_name, off)) =
                resolve_stack_addr_inner(base, disasm, defs, ops, visited, depth + 1)
                && let Some(c) = const_value(index)
            {
                return Some((base_name, off + c * (*element_size as i64)));
            }
            None
        }
        R2ILOp::PtrSub {
            base,
            index,
            element_size,
            ..
        } => {
            if let Some((base_name, off)) =
                resolve_stack_addr_inner(base, disasm, defs, ops, visited, depth + 1)
                && let Some(c) = const_value(index)
            {
                return Some((base_name, off - c * (*element_size as i64)));
            }
            None
        }
        _ => None,
    }
}

#[cfg(test)]
use serde::Deserialize;
use serde::Serialize;

/// Get registers written by the block as JSON array of names.
/// Caller must free the returned string with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2il_block_regs_write(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let mut regs = BTreeSet::new();

    for op in &blk.ops {
        for reg in op_regs_write(op) {
            if let Some(name) = disasm.register_name(reg) {
                regs.insert(name);
            }
        }
    }

    let json_array =
        serde_json::to_string(&regs.into_iter().collect::<Vec<_>>()).unwrap_or_default();
    CString::new(json_array).map_or(ptr::null_mut(), |c| c.into_raw())
}

/// Varnode info for JSON output.
#[derive(Serialize)]
struct VarnodeInfo {
    name: String,
    space: String,
    offset: u64,
    size: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    meta: Option<r2il::VarnodeMetadata>,
}

/// Helper: collect all varnodes from an operation.
fn op_all_varnodes(op: &R2ILOp) -> Vec<&Varnode> {
    let mut vns = Vec::new();

    // Combine read and write varnodes
    vns.extend(op_regs_read(op));
    vns.extend(op_regs_write(op));

    // Also get non-register varnodes
    match op {
        R2ILOp::Copy { dst, src } => {
            if !dst.is_register() {
                vns.push(dst);
            }
            if !src.is_register() {
                vns.push(src);
            }
        }
        R2ILOp::Load { dst, addr, .. } => {
            if !dst.is_register() {
                vns.push(dst);
            }
            if !addr.is_register() {
                vns.push(addr);
            }
        }
        R2ILOp::LoadLinked { dst, addr, .. } => {
            if !dst.is_register() {
                vns.push(dst);
            }
            if !addr.is_register() {
                vns.push(addr);
            }
        }
        R2ILOp::Store { addr, val, .. } => {
            if !addr.is_register() {
                vns.push(addr);
            }
            if !val.is_register() {
                vns.push(val);
            }
        }
        R2ILOp::StoreConditional {
            result, addr, val, ..
        } => {
            if let Some(out) = result
                && !out.is_register()
            {
                vns.push(out);
            }
            if !addr.is_register() {
                vns.push(addr);
            }
            if !val.is_register() {
                vns.push(val);
            }
        }
        R2ILOp::AtomicCAS {
            dst,
            addr,
            expected,
            replacement,
            ..
        } => {
            if !dst.is_register() {
                vns.push(dst);
            }
            if !addr.is_register() {
                vns.push(addr);
            }
            if !expected.is_register() {
                vns.push(expected);
            }
            if !replacement.is_register() {
                vns.push(replacement);
            }
        }
        R2ILOp::LoadGuarded {
            dst, addr, guard, ..
        } => {
            if !dst.is_register() {
                vns.push(dst);
            }
            if !addr.is_register() {
                vns.push(addr);
            }
            if !guard.is_register() {
                vns.push(guard);
            }
        }
        R2ILOp::StoreGuarded {
            addr, val, guard, ..
        } => {
            if !addr.is_register() {
                vns.push(addr);
            }
            if !val.is_register() {
                vns.push(val);
            }
            if !guard.is_register() {
                vns.push(guard);
            }
        }
        // For binary ops, get non-register operands
        R2ILOp::IntAdd { dst, a, b }
        | R2ILOp::IntSub { dst, a, b }
        | R2ILOp::IntAnd { dst, a, b }
        | R2ILOp::IntOr { dst, a, b }
        | R2ILOp::IntXor { dst, a, b } => {
            if !dst.is_register() {
                vns.push(dst);
            }
            if !a.is_register() {
                vns.push(a);
            }
            if !b.is_register() {
                vns.push(b);
            }
        }
        _ => {} // Other ops handled by op_regs_read/write
    }

    vns
}

// ============================================================================
// SSA Functions
// ============================================================================

/// SSA operation info for JSON output.
#[derive(Serialize)]
struct SSAOpInfo {
    op: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    dst: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    sources: Vec<String>,
}

/// Convert SSAOp to JSON-serializable info.
fn ssa_op_to_info(op: &r2ssa::SSAOp) -> SSAOpInfo {
    use r2ssa::SSAOp::*;

    let op_name = match op {
        Phi { .. } => "Phi",
        Copy { .. } => "Copy",
        Load { .. } => "Load",
        Store { .. } => "Store",
        Fence { .. } => "Fence",
        LoadLinked { .. } => "LoadLinked",
        StoreConditional { .. } => "StoreConditional",
        AtomicCAS { .. } => "AtomicCAS",
        LoadGuarded { .. } => "LoadGuarded",
        StoreGuarded { .. } => "StoreGuarded",
        IntAdd { .. } => "IntAdd",
        IntSub { .. } => "IntSub",
        IntMult { .. } => "IntMult",
        IntDiv { .. } => "IntDiv",
        IntSDiv { .. } => "IntSDiv",
        IntRem { .. } => "IntRem",
        IntSRem { .. } => "IntSRem",
        IntNegate { .. } => "IntNegate",
        IntCarry { .. } => "IntCarry",
        IntSCarry { .. } => "IntSCarry",
        IntSBorrow { .. } => "IntSBorrow",
        IntAnd { .. } => "IntAnd",
        IntOr { .. } => "IntOr",
        IntXor { .. } => "IntXor",
        IntNot { .. } => "IntNot",
        IntLeft { .. } => "IntLeft",
        IntRight { .. } => "IntRight",
        IntSRight { .. } => "IntSRight",
        IntEqual { .. } => "IntEqual",
        IntNotEqual { .. } => "IntNotEqual",
        IntLess { .. } => "IntLess",
        IntSLess { .. } => "IntSLess",
        IntLessEqual { .. } => "IntLessEqual",
        IntSLessEqual { .. } => "IntSLessEqual",
        IntZExt { .. } => "IntZExt",
        IntSExt { .. } => "IntSExt",
        BoolNot { .. } => "BoolNot",
        BoolAnd { .. } => "BoolAnd",
        BoolOr { .. } => "BoolOr",
        BoolXor { .. } => "BoolXor",
        Piece { .. } => "Piece",
        Subpiece { .. } => "Subpiece",
        PopCount { .. } => "PopCount",
        Lzcount { .. } => "Lzcount",
        Branch { .. } => "Branch",
        CBranch { .. } => "CBranch",
        BranchInd { .. } => "BranchInd",
        Call { .. } => "Call",
        CallInd { .. } => "CallInd",
        CallDefine { .. } => "CallDefine",
        Return { .. } => "Return",
        FloatAdd { .. } => "FloatAdd",
        FloatSub { .. } => "FloatSub",
        FloatMult { .. } => "FloatMult",
        FloatDiv { .. } => "FloatDiv",
        FloatNeg { .. } => "FloatNeg",
        FloatAbs { .. } => "FloatAbs",
        FloatSqrt { .. } => "FloatSqrt",
        FloatCeil { .. } => "FloatCeil",
        FloatFloor { .. } => "FloatFloor",
        FloatRound { .. } => "FloatRound",
        FloatNaN { .. } => "FloatNaN",
        FloatEqual { .. } => "FloatEqual",
        FloatNotEqual { .. } => "FloatNotEqual",
        FloatLess { .. } => "FloatLess",
        FloatLessEqual { .. } => "FloatLessEqual",
        Int2Float { .. } => "Int2Float",
        Float2Int { .. } => "Float2Int",
        FloatFloat { .. } => "FloatFloat",
        Trunc { .. } => "Trunc",
        CallOther { .. } => "CallOther",
        Nop => "Nop",
        Unimplemented => "Unimplemented",
        CpuId { .. } => "CpuId",
        Breakpoint => "Breakpoint",
        PtrAdd { .. } => "PtrAdd",
        PtrSub { .. } => "PtrSub",
        SegmentOp { .. } => "SegmentOp",
        New { .. } => "New",
        Cast { .. } => "Cast",
        Extract { .. } => "Extract",
        Insert { .. } => "Insert",
    };

    SSAOpInfo {
        op: op_name.to_string(),
        dst: op.dst().map(|v| v.display_name()),
        sources: op.sources().iter().map(|v| v.display_name()).collect(),
    }
}

// Remaining taint/SSA/CFG/sym surfaces are implemented under r2plugin/src/analysis/.

// ============================================================================
// Architecture Helpers
// ============================================================================

/// Helper: build a disassembler and ArchSpec for a given arch string.
fn create_disassembler_for_arch(arch: &str) -> Result<(ArchSpec, Disassembler), String> {
    match arch.to_lowercase().as_str() {
        #[cfg(feature = "x86")]
        "x86-64" | "x86_64" | "x64" | "amd64" => {
            let spec = build_arch_spec(
                sleigh_config::processor_x86::SLA_X86_64,
                sleigh_config::processor_x86::PSPEC_X86_64,
                "x86-64",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_x86::SLA_X86_64,
                sleigh_config::processor_x86::PSPEC_X86_64,
                "x86-64",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "x86-64");
            Ok((spec, dis))
        }
        #[cfg(feature = "x86")]
        "x86" | "x86-32" | "i386" | "i686" => {
            let spec = build_arch_spec(
                sleigh_config::processor_x86::SLA_X86,
                sleigh_config::processor_x86::PSPEC_X86,
                "x86",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_x86::SLA_X86,
                sleigh_config::processor_x86::PSPEC_X86,
                "x86",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "x86");
            Ok((spec, dis))
        }
        #[cfg(feature = "arm")]
        "arm" | "arm32" | "arm-le" => {
            let spec = build_arch_spec(
                sleigh_config::processor_arm::SLA_ARM8_LE,
                // sleigh-config 1.x does not ship an ARM8 pspec; use a Cortex pspec instead.
                sleigh_config::processor_arm::PSPEC_ARMCORTEX,
                "ARM",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_arm::SLA_ARM8_LE,
                // sleigh-config 1.x does not ship an ARM8 pspec; use a Cortex pspec instead.
                sleigh_config::processor_arm::PSPEC_ARMCORTEX,
                "ARM",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "arm");
            Ok((spec, dis))
        }
        #[cfg(feature = "arm")]
        "arm64" | "arm64e" | "aarch64" => {
            let spec = build_arch_spec(
                sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
                sleigh_config::processor_aarch64::PSPEC_AARCH64,
                "aarch64",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
                sleigh_config::processor_aarch64::PSPEC_AARCH64,
                "aarch64",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "arm64");
            Ok((spec, dis))
        }
        #[cfg(feature = "mips")]
        "mips" | "mips32" | "mips32be" | "mipsbe" | "mipseb" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS32BE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32be",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS32BE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32be",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "mips32be");
            Ok((spec, dis))
        }
        #[cfg(feature = "mips")]
        "mipsel" | "mips32le" | "mips32el" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS32LE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32le",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS32LE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32le",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "mips32le");
            Ok((spec, dis))
        }
        #[cfg(feature = "mips")]
        "mips64" | "mips64be" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS64BE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64be",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS64BE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64be",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "mips64be");
            Ok((spec, dis))
        }
        #[cfg(feature = "mips")]
        "mips64el" | "mips64le" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS64LE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64le",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS64LE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64le",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "mips64le");
            Ok((spec, dis))
        }
        #[cfg(feature = "riscv")]
        "riscv64" | "rv64" | "rv64gc" => {
            let spec = build_arch_spec(
                sleigh_config::processor_riscv::SLA_RISCV_LP64D,
                sleigh_config::processor_riscv::PSPEC_RV64GC,
                "riscv64",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_riscv::SLA_RISCV_LP64D,
                sleigh_config::processor_riscv::PSPEC_RV64GC,
                "riscv64",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "riscv64");
            Ok((spec, dis))
        }
        #[cfg(feature = "riscv")]
        "riscv32" | "rv32" | "rv32gc" => {
            let spec = build_arch_spec(
                sleigh_config::processor_riscv::SLA_RISCV_ILP32D,
                sleigh_config::processor_riscv::PSPEC_RV32GC,
                "riscv32",
            )
            .map_err(|e| e.to_string())?;
            let dis = Disassembler::from_sla(
                sleigh_config::processor_riscv::SLA_RISCV_ILP32D,
                sleigh_config::processor_riscv::PSPEC_RV32GC,
                "riscv32",
            )
            .map_err(|e| e.to_string())?;
            let (spec, dis) = apply_userop_map(spec, dis, "riscv32");
            Ok((spec, dis))
        }
        _ => {
            let mut supported = vec![];
            #[cfg(feature = "x86")]
            supported.extend(["x86-64", "x86"]);
            #[cfg(feature = "arm")]
            supported.extend(["arm", "arm64", "aarch64"]);
            #[cfg(feature = "mips")]
            supported.extend(["mips32be", "mips32le", "mips64be", "mips64le"]);
            #[cfg(feature = "riscv")]
            supported.extend(["riscv64", "riscv32"]);

            if supported.is_empty() {
                Err(
                    "No architectures enabled; build with feature x86, arm, mips, or riscv"
                        .to_string(),
                )
            } else {
                Err(format!(
                    "Unknown architecture '{}'. Supported: {}",
                    arch,
                    supported.join(", ")
                ))
            }
        }
    }
}

fn apply_userop_map(
    mut spec: ArchSpec,
    mut disasm: Disassembler,
    arch: &str,
) -> (ArchSpec, Disassembler) {
    let userop_map = userop_map_for_arch(arch);
    disasm.set_userop_map(userop_map.clone());

    if !userop_map.is_empty() {
        let mut defs: Vec<UserOpDef> = userop_map
            .into_iter()
            .map(|(index, name)| UserOpDef { index, name })
            .collect();
        defs.sort_by_key(|def| def.index);
        spec.userops = defs;
    }

    (spec, disasm)
}

// Symbolic execution and CFG surfaces are implemented under r2plugin/src/analysis/.

// ============================================================================
// Decompiler Functions
// ============================================================================

#[unsafe(no_mangle)]
pub extern "C" fn r2dec_block_guard_comment_ffi(
    func_name: *const c_char,
    blocks: usize,
    max_blocks: usize,
) -> *mut c_char {
    let func_name = if func_name.is_null() {
        "unknown".to_string()
    } else {
        unsafe { CStr::from_ptr(func_name) }
            .to_str()
            .unwrap_or("unknown")
            .to_string()
    };
    CString::new(r2dec::block_guard_fallback_comment(
        &func_name, blocks, max_blocks,
    ))
    .map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2dec_cfg_guard_comment_ffi(
    func_name: *const c_char,
    block_count: usize,
    loop_count: usize,
    back_edge_count: usize,
    max_switch_cases: usize,
) -> *mut c_char {
    let func_name = if func_name.is_null() {
        "unknown".to_string()
    } else {
        unsafe { CStr::from_ptr(func_name) }
            .to_str()
            .unwrap_or("unknown")
            .to_string()
    };
    let summary = r2ssa::CFGRiskSummary {
        block_count,
        loop_count,
        back_edge_count,
        switch_block_count: usize::from(max_switch_cases > 0),
        max_switch_cases,
    };
    let Some(reason) = r2engine::cfg_guard_reason_from_summary(&summary) else {
        return ptr::null_mut();
    };
    CString::new(r2dec::artifact_guard_fallback_comment(&func_name, &reason))
        .map_or(ptr::null_mut(), |c| c.into_raw())
}

#[cfg(test)]
#[derive(Debug, Deserialize)]
struct AfcfjArg {
    #[serde(default)]
    name: Option<String>,
    #[serde(default, rename = "type")]
    ty: Option<String>,
}

#[cfg(test)]
#[derive(Debug, Deserialize)]
struct AfcfjFunction {
    #[serde(default, rename = "return")]
    return_type: Option<String>,
    #[serde(default)]
    ret: Option<String>,
    #[serde(default)]
    args: Vec<AfcfjArg>,
}

#[cfg(test)]
#[derive(Debug, Deserialize)]
#[serde(untagged)]
#[allow(dead_code)]
enum AfvjRef {
    Stack { base: String, offset: i64 },
    Register(String),
    Other(serde_json::Value),
}

#[cfg(test)]
#[derive(Debug, Deserialize)]
struct AfvjVar {
    #[serde(default)]
    name: Option<String>,
    #[serde(default, rename = "type")]
    ty: Option<String>,
    #[serde(default, rename = "ref")]
    reference: Option<AfvjRef>,
}

#[cfg(test)]
#[derive(Debug, Deserialize)]
struct AfvjPayload {
    #[serde(default)]
    reg: Vec<AfvjVar>,
    #[serde(default)]
    bp: Vec<AfvjVar>,
    #[serde(default)]
    sp: Vec<AfvjVar>,
}

#[cfg(test)]
fn parse_external_reg_params(
    json_str: &str,
    ptr_bits: u32,
) -> Vec<r2types::ExternalRegisterParamSpec> {
    let payload = match serde_json::from_str::<AfvjPayload>(json_str) {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };

    let mut used_names = std::collections::HashSet::new();
    payload
        .reg
        .into_iter()
        .enumerate()
        .map(|(idx, entry)| {
            let raw_name = entry.name.unwrap_or_else(|| format!("arg{}", idx));
            let mut name =
                sanitize_c_identifier(&raw_name).unwrap_or_else(|| format!("arg{}", idx + 1));
            if !is_generic_arg_name(&name) {
                name = uniquify_name(name, &mut used_names);
            }
            r2types::ExternalRegisterParamSpec {
                name,
                ty: entry
                    .ty
                    .as_deref()
                    .and_then(|raw| parse_external_type(raw, ptr_bits))
                    .as_ref()
                    .map(ctype_to_type_like),
                reg: entry
                    .reference
                    .and_then(|r| match r {
                        AfvjRef::Register(reg) => Some(reg),
                        _ => None,
                    })
                    .unwrap_or_default(),
            }
        })
        .collect()
}

#[cfg(test)]
fn merge_signature_with_reg_params(
    signature: Option<r2types::FunctionSignatureSpec>,
    reg_params: Vec<r2types::ExternalRegisterParamSpec>,
) -> Option<r2types::FunctionSignatureSpec> {
    if reg_params.is_empty() {
        return signature;
    }

    let mut sig = signature.unwrap_or_default();
    if sig.params.is_empty() {
        sig.params = reg_params
            .into_iter()
            .map(|param| r2types::FunctionParamSpec {
                name: param.name,
                ty: param.ty,
            })
            .collect();
        return Some(sig);
    }

    for (idx, reg_param) in reg_params.into_iter().enumerate() {
        if let Some(existing) = sig.params.get_mut(idx) {
            if existing.ty.is_none() {
                existing.ty = reg_param.ty.clone();
            }
            if is_generic_arg_name(&existing.name) && !is_generic_arg_name(&reg_param.name) {
                existing.name = reg_param.name;
            }
        } else {
            sig.params.push(r2types::FunctionParamSpec {
                name: reg_param.name,
                ty: reg_param.ty,
            });
        }
    }

    Some(sig)
}

fn parse_addr_name_map(json_str: &str) -> std::collections::HashMap<u64, String> {
    serde_json::from_str::<std::collections::HashMap<String, String>>(json_str)
        .ok()
        .map(|map| {
            map.into_iter()
                .filter_map(|(k, v)| {
                    let addr = if k.starts_with("0x") || k.starts_with("0X") {
                        u64::from_str_radix(&k[2..], 16).ok()
                    } else {
                        k.parse().ok()
                    };
                    addr.map(|a| (a, v))
                })
                .collect()
        })
        .unwrap_or_default()
}

#[cfg(test)]
fn sanitize_c_identifier(name: &str) -> Option<String> {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return None;
    }

    let mut out = String::new();
    for (idx, ch) in trimmed.chars().enumerate() {
        let normalized = if ch.is_ascii_alphanumeric() || ch == '_' {
            ch
        } else {
            '_'
        };
        if idx == 0 && normalized.is_ascii_digit() {
            out.push('_');
        }
        out.push(normalized);
    }

    if out.chars().all(|c| c == '_') {
        None
    } else {
        Some(out)
    }
}

#[cfg(test)]
fn uniquify_name(base: String, used: &mut std::collections::HashSet<String>) -> String {
    if used.insert(base.clone()) {
        return base;
    }
    let mut idx = 2usize;
    loop {
        let candidate = format!("{}_{}", base, idx);
        if used.insert(candidate.clone()) {
            return candidate;
        }
        idx += 1;
    }
}

#[cfg(test)]
fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

#[cfg(test)]
fn is_low_quality_stack_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("var_")
        || lower.starts_with("local_")
        || lower.starts_with("stack_")
        || lower == "saved_fp"
        || is_generic_arg_name(&lower)
}

#[cfg(test)]
fn parse_external_type(raw_ty: &str, ptr_bits: u32) -> Option<r2dec::CType> {
    let normalized = normalize_external_type_name(raw_ty);
    let parsed = r2types::parse_type_like_spec(&normalized, ptr_bits)?;
    Some(type_like_to_ctype(&parsed))
}

#[cfg(test)]
fn parse_external_signature(
    json_str: &str,
    ptr_bits: u32,
) -> Option<r2types::FunctionSignatureSpec> {
    let entries = serde_json::from_str::<Vec<AfcfjFunction>>(json_str).ok()?;
    parse_afcfj_signature_entries(entries, ptr_bits)
}

#[cfg(test)]
#[derive(Debug, Default)]
struct ParsedSignatureContext {
    current: Option<r2types::FunctionSignatureSpec>,
    known: std::collections::HashMap<String, r2types::FunctionType>,
}

#[cfg(test)]
fn parse_afcfj_signature_entries(
    entries: Vec<AfcfjFunction>,
    ptr_bits: u32,
) -> Option<r2types::FunctionSignatureSpec> {
    let first = entries.into_iter().next()?;

    let mut used_names = std::collections::HashSet::new();
    let mut params: Vec<_> = first
        .args
        .into_iter()
        .enumerate()
        .map(|(idx, arg)| {
            let fallback = format!("arg{}", idx + 1);
            let raw_name = arg.name.unwrap_or(fallback);
            let mut name =
                sanitize_c_identifier(&raw_name).unwrap_or_else(|| format!("arg{}", idx + 1));
            if !is_generic_arg_name(&name) {
                name = uniquify_name(name, &mut used_names);
            }
            r2types::FunctionParamSpec {
                name,
                ty: arg
                    .ty
                    .as_deref()
                    .and_then(|raw| parse_external_type(raw, ptr_bits))
                    .as_ref()
                    .map(ctype_to_type_like),
            }
        })
        .collect();
    if params.len() == 1
        && params[0].ty == Some(r2types::CTypeLike::Void)
        && is_generic_arg_name(&params[0].name)
    {
        params.clear();
    }

    let ret_type_raw = first.return_type.or(first.ret);
    let ret_type = ret_type_raw
        .as_deref()
        .and_then(|raw| parse_external_type(raw, ptr_bits))
        .as_ref()
        .map(ctype_to_type_like);

    Some(r2types::FunctionSignatureSpec { ret_type, params })
}

#[cfg(test)]
fn parse_afcfj_signature_value(
    value: &serde_json::Value,
    ptr_bits: u32,
) -> Option<r2types::FunctionSignatureSpec> {
    if value.is_array() {
        let entries = serde_json::from_value::<Vec<AfcfjFunction>>(value.clone()).ok()?;
        return parse_afcfj_signature_entries(entries, ptr_bits);
    }
    if value.is_object() {
        let entry = serde_json::from_value::<AfcfjFunction>(value.clone()).ok()?;
        return parse_afcfj_signature_entries(vec![entry], ptr_bits);
    }
    None
}

#[cfg(test)]
fn maybe_insert_known_signature(
    known: &mut std::collections::HashMap<String, r2types::FunctionType>,
    name: &str,
    sig: r2types::FunctionType,
) {
    if name.is_empty() {
        return;
    }
    known.insert(name.to_string(), sig.clone());

    for prefix in ["sym.imp.", "sym.", "dbg.", "fcn."] {
        if let Some(stripped) = name.strip_prefix(prefix)
            && !stripped.is_empty()
        {
            known.insert(stripped.to_string(), sig.clone());
        }
    }
}

#[cfg(test)]
fn parse_known_function_signatures(
    value: &serde_json::Value,
    ptr_bits: u32,
) -> std::collections::HashMap<String, r2types::FunctionType> {
    let mut out = std::collections::HashMap::new();
    let Some(entries) = value.as_array() else {
        return out;
    };

    for entry in entries {
        let Some(obj) = entry.as_object() else {
            continue;
        };

        let Some(name) = obj.get("name").and_then(|v| v.as_str()) else {
            continue;
        };

        let mut params = Vec::new();
        if let Some(args) = obj.get("args").and_then(|v| v.as_array()) {
            for arg in args {
                if let Some(arg_obj) = arg.as_object() {
                    let ty = arg_obj
                        .get("type")
                        .or_else(|| arg_obj.get("ty"))
                        .and_then(|v| v.as_str())
                        .and_then(|raw| r2types::parse_type_like_spec(raw, ptr_bits));
                    params.push(ty.unwrap_or(r2types::CTypeLike::Unknown));
                } else if let Some(raw) = arg.as_str() {
                    params.push(
                        r2types::parse_type_like_spec(raw, ptr_bits)
                            .unwrap_or(r2types::CTypeLike::Unknown),
                    );
                }
            }
        } else if let Some(argtypes) = obj.get("argtypes").and_then(|v| v.as_array()) {
            for raw in argtypes.iter().filter_map(|v| v.as_str()) {
                params.push(
                    r2types::parse_type_like_spec(raw, ptr_bits)
                        .unwrap_or(r2types::CTypeLike::Unknown),
                );
            }
        }

        let ret = obj
            .get("return")
            .or_else(|| obj.get("ret"))
            .or_else(|| obj.get("return_type"))
            .or_else(|| obj.get("rettype"))
            .or_else(|| obj.get("type"))
            .and_then(|v| v.as_str())
            .and_then(|raw| r2types::parse_type_like_spec(raw, ptr_bits))
            .unwrap_or(r2types::CTypeLike::Unknown);

        let variadic = obj
            .get("variadic")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);

        if params.is_empty() && matches!(ret, r2types::CTypeLike::Unknown) {
            continue;
        }

        let sig = r2types::FunctionType {
            return_type: ret,
            params,
            variadic,
        };
        maybe_insert_known_signature(&mut out, name, sig);
    }

    out
}

#[cfg(test)]
fn parse_signature_context(json_str: &str, ptr_bits: u32) -> ParsedSignatureContext {
    let mut parsed = ParsedSignatureContext::default();
    let Ok(value) = serde_json::from_str::<serde_json::Value>(json_str) else {
        parsed.current = parse_external_signature(json_str, ptr_bits);
        return parsed;
    };

    if value.is_array() {
        parsed.current = parse_afcfj_signature_value(&value, ptr_bits);
        return parsed;
    }

    let Some(obj) = value.as_object() else {
        return parsed;
    };

    if let Some(current) = obj.get("current") {
        parsed.current = parse_afcfj_signature_value(current, ptr_bits);
    }
    if let Some(known) = obj.get("known") {
        parsed.known = parse_known_function_signatures(known, ptr_bits);
    }

    parsed
}

#[cfg(test)]
fn parse_external_stack_vars(
    json_str: &str,
    ptr_bits: u32,
) -> std::collections::HashMap<i64, r2types::ExternalStackVarSpec> {
    let payload = match serde_json::from_str::<AfvjPayload>(json_str) {
        Ok(v) => v,
        Err(_) => return std::collections::HashMap::new(),
    };

    let mut vars = std::collections::HashMap::new();
    let mut used_names = std::collections::HashSet::new();

    for entry in payload.bp.into_iter().chain(payload.sp.into_iter()) {
        let Some(AfvjRef::Stack { base, offset }) = entry.reference else {
            continue;
        };

        let raw_name = entry
            .name
            .unwrap_or_else(|| format!("stack_{:x}", offset.unsigned_abs()));
        let Some(clean_name) = sanitize_c_identifier(&raw_name) else {
            continue;
        };
        let var_name = uniquify_name(clean_name, &mut used_names);
        let candidate = r2types::ExternalStackVarSpec {
            name: var_name,
            ty: entry
                .ty
                .as_deref()
                .and_then(|raw| parse_external_type(raw, ptr_bits))
                .as_ref()
                .map(ctype_to_type_like),
            base: match base.trim().to_ascii_lowercase().as_str() {
                "bp" | "ebp" | "rbp" | "fp" => r2types::ExternalStackBase::FramePointer,
                "sp" | "esp" | "rsp" => r2types::ExternalStackBase::StackPointer,
                _ => r2types::ExternalStackBase::Named(base),
            },
            role: r2types::ExternalStackSlotRole::Unknown,
            param_index: None,
            param_name: None,
            source_reg: None,
        };

        match vars.get(&offset) {
            None => {
                vars.insert(offset, candidate);
            }
            Some(existing) => {
                if is_low_quality_stack_name(&existing.name)
                    && !is_low_quality_stack_name(&candidate.name)
                {
                    vars.insert(offset, candidate);
                }
            }
        }
    }

    vars
}

/// Decompile a function with external context (function names, strings, symbols, signature, stack vars).
/// Returns C code as a string. Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2dec_function_with_context(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    func_name: *const c_char,
    func_names_json: *const c_char,
    strings_json: *const c_char,
    symbols_json: *const c_char,
    external_context_json: *const c_char,
) -> *mut c_char {
    r2dec_function_with_context_impl(R2DecFunctionWithContextInputs {
        ctx,
        blocks,
        num_blocks,
        fcn_addr: 0,
        func_name,
        func_names_json,
        strings_json,
        symbols_json,
        external_context_json,
        scope_functions: ptr::null(),
        scope_num_functions: 0,
    })
}

fn r2dec_function_with_context_impl(inputs: R2DecFunctionWithContextInputs) -> *mut c_char {
    let R2DecFunctionWithContextInputs {
        ctx,
        blocks,
        num_blocks,
        fcn_addr,
        func_name,
        func_names_json,
        strings_json,
        symbols_json,
        external_context_json,
        scope_functions,
        scope_num_functions,
    } = inputs;
    let Some(ctx_view) = context::require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(block_slice) = (unsafe { blocks::BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };

    let func_name_str = helpers::resolve_function_name(0, func_name);
    let ptr_bits = ctx_view.arch.map(helpers::effective_ptr_bits).unwrap_or(64);

    // Collect all JSON context strings on the main thread (from C pointers),
    // then move everything into the large-stack thread for SSA + decompilation.
    let func_names_str = helpers::cstr_or_default(func_names_json, "{}");
    let strings_str = helpers::cstr_or_default(strings_json, "{}");
    let symbols_str = helpers::cstr_or_default(symbols_json, "{}");
    let external_context_str = helpers::cstr_or_default(external_context_json, "{}");
    let symbolic_scope = if scope_functions.is_null() || scope_num_functions == 0 {
        None
    } else {
        unsafe {
            analysis::sym::build_symbolic_scope_from_ffi(
                scope_functions,
                scope_num_functions,
                ctx_view.arch,
                fcn_addr,
            )
        }
    };
    let Some(function_input) =
        types::build_function_input(ctx, blocks, num_blocks, fcn_addr, func_name)
    else {
        return ptr::null_mut();
    };
    let parsed_context = r2types::parse_external_context_json(&external_context_str, ptr_bits);
    let scope_facts = types::empty_interproc_scope_facts();
    let reg_type_hints = if ctx_view.semantic_metadata_enabled {
        types::collect_register_type_hints(block_slice.as_slice(), ctx_view.disasm)
    } else {
        std::collections::HashMap::new()
    };
    let analysis_request = types::engine_analyze_request_with_scope_facts(
        &function_input,
        &parsed_context,
        types::hash_string_payload(&external_context_str),
        &scope_facts,
        1,
        symbolic_scope.as_ref(),
        reg_type_hints,
        None,
        r2engine::EngineSemanticMode::Full,
        true,
    );
    let function_names = parse_addr_name_map(&func_names_str);
    let strings = parse_addr_name_map(&strings_str);
    let symbols = parse_addr_name_map(&symbols_str);
    let display_func_name = helpers::resolve_decompiler_display_name(
        fcn_addr,
        &func_name_str,
        &function_names,
        &symbols,
    );
    let (_, _, config) = r2dec::DecompilerConfig::for_arch(ctx_view.arch);

    // Run SSA construction + decompilation on a dedicated thread with a large
    // stack to prevent stack overflow on complex O2-optimized CFGs.
    let output =
        decompiler::run_engine_decompile_on_large_stack(r2engine::EngineFunctionDecompileRequest {
            analysis: analysis_request,
            display_name: display_func_name,
            function_names,
            strings,
            symbols,
            config,
            func_names_payload: func_names_str,
            strings_payload: strings_str,
            symbols_payload: symbols_str,
        });

    CString::new(output).map_or(ptr::null_mut(), |c| c.into_raw())
}

struct R2DecFunctionWithContextInputs {
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    func_name: *const c_char,
    func_names_json: *const c_char,
    strings_json: *const c_char,
    symbols_json: *const c_char,
    external_context_json: *const c_char,
    scope_functions: *const analysis::sym::R2ILFunctionBlocks,
    scope_num_functions: usize,
}

/// Decompile a function with external context and a prepared symbolic helper scope.
/// Returns C code as a string. Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2dec_function_with_context_scope(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    func_name: *const c_char,
    func_names_json: *const c_char,
    strings_json: *const c_char,
    symbols_json: *const c_char,
    external_context_json: *const c_char,
    scope_functions: *const analysis::sym::R2ILFunctionBlocks,
    scope_num_functions: usize,
) -> *mut c_char {
    r2dec_function_with_context_impl(R2DecFunctionWithContextInputs {
        ctx,
        blocks,
        num_blocks,
        fcn_addr,
        func_name,
        func_names_json,
        strings_json,
        symbols_json,
        external_context_json,
        scope_functions,
        scope_num_functions,
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn r2dec_function_with_session_context(
    input: *const R2SleighSessionInput,
    func_names_json: *const c_char,
    strings_json: *const c_char,
    symbols_json: *const c_char,
) -> *mut c_char {
    if input.is_null() {
        return ptr::null_mut();
    }
    let input = unsafe { &*input };
    let Some(ctx_view) = context::require_ctx_view(input.ctx) else {
        return ptr::null_mut();
    };
    let Some(block_slice) =
        (unsafe { blocks::BlockSlice::from_ffi(input.blocks, input.num_blocks) })
    else {
        return ptr::null_mut();
    };

    let func_name_str = helpers::resolve_function_name(input.function_addr, input.function_name);
    let ptr_bits = ctx_view.arch.map(helpers::effective_ptr_bits).unwrap_or(64);

    let func_names_str = helpers::cstr_or_default(func_names_json, "{}");
    let strings_str = helpers::cstr_or_default(strings_json, "{}");
    let symbols_str = helpers::cstr_or_default(symbols_json, "{}");
    let external_context = cstr_or_default(input.function_context.external_context_json, "{}");
    let scope_facts = unsafe { typed_interproc_scope_facts(&input.interproc_scope) };
    let interproc_iter = input.budget.interproc_iter.max(1);
    let interproc_max_iters = input.budget.interproc_max_iters.max(interproc_iter);
    let Some(function_input) = types::build_function_input(
        input.ctx,
        input.blocks,
        input.num_blocks,
        input.function_addr,
        input.function_name,
    ) else {
        return ptr::null_mut();
    };
    let inference_input = TypeWritebackInferenceInput {
        ctx: input.ctx,
        blocks: input.blocks,
        num_blocks: input.num_blocks,
        fcn_addr: input.function_addr,
        fcn_name: input.function_name,
        external_context_json: input.function_context.external_context_json,
        function_context: Some(&input.function_context),
        scope_functions: input.interproc_scope.functions,
        scope_num_functions: input.interproc_scope.num_functions,
        interproc: InterprocInferenceInput {
            iter: interproc_iter,
            max_iters: interproc_max_iters,
            converged: input.budget.interproc_converged != 0,
            scope_facts: &scope_facts,
            scope_report: None,
        },
        global_max_links: input.budget.global_max_links.max(1),
        max_type_decls: input.budget.max_type_decls.max(1),
        max_mutations: input.budget.max_mutations.max(1),
    };
    let symbolic_scope = build_inference_symbolic_scope(&inference_input, &function_input);
    let parsed_context = unsafe {
        typed_function_context_to_parsed(&input.function_context, &external_context, ptr_bits)
    };
    let external_context_hash = types::hash_string_payload(&external_context);
    let reg_type_hints = if ctx_view.semantic_metadata_enabled {
        types::collect_register_type_hints(block_slice.as_slice(), ctx_view.disasm)
    } else {
        std::collections::HashMap::new()
    };
    let analysis_request = types::engine_analyze_request_with_scope_facts(
        &function_input,
        &parsed_context,
        external_context_hash,
        &scope_facts,
        interproc_max_iters,
        symbolic_scope.as_ref(),
        reg_type_hints,
        None,
        r2engine::EngineSemanticMode::Full,
        true,
    );
    let function_names = parse_addr_name_map(&func_names_str);
    let strings = parse_addr_name_map(&strings_str);
    let symbols = parse_addr_name_map(&symbols_str);
    let display_func_name = helpers::resolve_decompiler_display_name(
        input.function_addr,
        &func_name_str,
        &function_names,
        &symbols,
    );
    let (_, _, config) = r2dec::DecompilerConfig::for_arch(ctx_view.arch);
    let output =
        decompiler::run_engine_decompile_on_large_stack(r2engine::EngineFunctionDecompileRequest {
            analysis: analysis_request,
            display_name: display_func_name,
            function_names,
            strings,
            symbols,
            config,
            func_names_payload: func_names_str,
            strings_payload: strings_str,
            symbols_payload: symbols_str,
        });

    CString::new(output).map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2dec_named_native_worker_summary(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
    fcn_name: *const c_char,
) -> *mut c_char {
    let Some(ctx_view) = context::require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let Some(block_slice) = (unsafe { blocks::BlockSlice::from_ffi(blocks, num_blocks) }) else {
        return ptr::null_mut();
    };
    let function_name = helpers::resolve_function_name(0, fcn_name);
    let ptr_bits = ctx_view.arch.map(helpers::effective_ptr_bits).unwrap_or(64);
    let output = decompiler::render_named_native_worker_summary(
        block_slice.into_inner(),
        &function_name,
        ctx_view.arch,
        ptr_bits,
    );
    output
        .and_then(|output| CString::new(output).ok())
        .map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2dec_named_native_worker_summary_direct(
    ctx: *const R2ILContext,
    fcn_addr: u64,
    fcn_name: *const c_char,
) -> *mut c_char {
    let Some(ctx_view) = context::require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let function_name = helpers::resolve_function_name(fcn_addr, fcn_name);
    let ptr_bits = ctx_view.arch.map(helpers::effective_ptr_bits).unwrap_or(64);
    let output = decompiler::render_direct_named_native_worker_summary(
        fcn_addr,
        &function_name,
        ctx_view.arch,
        ptr_bits,
    );
    output
        .and_then(|output| CString::new(output).ok())
        .map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_named_native_worker_type_json(
    ctx: *const R2ILContext,
    function_addr: u64,
    function_name: *const c_char,
    function_context: *const R2SleighFunctionContext,
    global_max_links: usize,
    max_type_decls: usize,
    max_mutations: usize,
) -> *mut c_char {
    let Some(ctx_view) = context::require_ctx_view(ctx) else {
        return ptr::null_mut();
    };
    let function_name = helpers::resolve_function_name(function_addr, function_name);
    let ptr_bits = ctx_view.arch.map(helpers::effective_ptr_bits).unwrap_or(64);
    let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(ctx_view.arch);
    let parsed_context = if function_context.is_null() {
        r2types::parse_external_context_json("{}", ptr_bits)
    } else {
        unsafe { typed_function_context_to_parsed(&*function_context, "{}", ptr_bits) }
    };
    let Some(projection) = r2engine::native_worker_type_projection(
        function_addr,
        &function_name,
        &arch_name,
        ptr_bits,
        &parsed_context,
        true,
    ) else {
        return ptr::null_mut();
    };
    let scope_facts = types::empty_interproc_scope_facts();
    let interproc = InterprocInferenceInput {
        iter: 1,
        max_iters: 1,
        converged: false,
        scope_facts: &scope_facts,
        scope_report: None,
    };
    let payload = semantic_type_fallback_payload(SemanticTypeFallbackPayloadInput {
        function_name: &function_name,
        arch_name: &arch_name,
        ptr_bits,
        callconv: parsed_context.callconv.as_deref(),
        interproc,
        compiled: &projection.semantic_artifact,
        function_facts: &projection.function_facts,
        symbolic_scope: None,
        apply_artifact_signature_hint: !projection.name_owned_signature,
        budget: TypeOutputBudget::new(global_max_links, max_type_decls, max_mutations),
    });
    serde_json::to_string(&payload)
        .ok()
        .and_then(|json| CString::new(json).ok())
        .map_or(ptr::null_mut(), |c| c.into_raw())
}

/// Decompile a single basic block to C code.
/// Returns C code as a string. Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2dec_block(ctx: *const R2ILContext, block: *const R2ILBlock) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let input = InstructionExportInput {
        disasm,
        arch: match ctx_ref.arch.as_ref() {
            Some(a) => a,
            None => return ptr::null_mut(),
        },
        block: blk,
        addr: blk.addr,
        mnemonic: "",
        native_size: blk.size as usize,
    };

    match export_instruction(&input, InstructionAction::Dec, ExportFormat::CLike) {
        Ok(output) => {
            let normalized = if output.trim().is_empty() {
                "/* r2dec: empty output */".to_string()
            } else {
                output
            };
            CString::new(normalized).map_or(ptr::null_mut(), |c| c.into_raw())
        }
        Err(_) => ptr::null_mut(),
    }
}

/// Get the C AST for a block as JSON.
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2dec_block_ast_json(
    ctx: *const R2ILContext,
    block: *const R2ILBlock,
) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };

    // Convert to SSA
    let ssa_block = r2ssa::block::to_ssa(blk, disasm);

    // Build statements from SSA ops
    let stmts: Vec<r2dec::CStmt> = r2dec::lower_ssa_ops_to_stmts(64, &ssa_block.ops);

    match serde_json::to_string_pretty(&stmts) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

// ============================================================================
// radare2 Deep Integration FFI - Variable Recovery and Data Refs
// ============================================================================

#[derive(Debug, Clone)]
#[cfg(test)]
pub(crate) struct InferredParam {
    name: String,
    ty: r2dec::CType,
    arg_index: usize,
    size_bytes: u32,
    evidence: TypeEvidence,
}

#[cfg(test)]
type TypeEvidence = r2types::SignatureTypeEvidence;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct InferredParamJson {
    name: String,
    #[serde(rename = "type")]
    param_type: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct InferredSignatureCcJson {
    function_name: String,
    signature: String,
    ret_type: String,
    params: Vec<InferredParamJson>,
    callconv: String,
    arch: String,
    confidence: u8,
    callconv_confidence: u8,
}

#[derive(Debug, serde::Serialize)]
struct VarTypeCandidateJson {
    name: String,
    kind: String,
    delta: i64,
    #[serde(rename = "type")]
    var_type: String,
    isarg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    reg: Option<String>,
    size: u32,
    confidence: u8,
    source: String,
    evidence: Vec<String>,
}

#[derive(Debug, serde::Serialize)]
struct VarRenameCandidateJson {
    name: String,
    target_name: String,
    confidence: u8,
    source: String,
    evidence: Vec<String>,
}

#[derive(Debug, serde::Serialize)]
struct StructFieldCandidateJson {
    name: String,
    offset: u64,
    #[serde(rename = "type")]
    field_type: String,
    confidence: u8,
}

#[derive(Debug, serde::Serialize)]
struct StructDeclCandidateJson {
    name: String,
    decl: String,
    confidence: u8,
    source: String,
    fields: Vec<StructFieldCandidateJson>,
}

#[derive(Debug, serde::Serialize)]
struct GlobalTypeLinkCandidateJson {
    addr: u64,
    #[serde(rename = "type")]
    target_type: String,
    confidence: u8,
    source: String,
}

#[derive(Debug, serde::Serialize)]
struct InterprocSummaryJson {
    callsite_count: usize,
    iterations: usize,
    max_iterations: usize,
    converged: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    summary: Option<r2ssa::FunctionSemanticSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    summary_json: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    scope: Option<serde_json::Value>,
}

#[derive(Debug, serde::Serialize, Default)]
struct TypeWritebackDiagnosticsJson {
    conflicts: Vec<String>,
    warnings: Vec<String>,
    solver_warnings: Vec<String>,
}

#[derive(Debug, Clone, serde::Serialize)]
struct PhaseTimingJson {
    phase: String,
    elapsed_us: u64,
}

#[derive(Debug, serde::Serialize)]
struct InferredTypeWritebackJson {
    function_name: String,
    signature: String,
    ret_type: String,
    params: Vec<InferredParamJson>,
    callconv: String,
    arch: String,
    confidence: u8,
    callconv_confidence: u8,
    var_type_candidates: Vec<VarTypeCandidateJson>,
    var_rename_candidates: Vec<VarRenameCandidateJson>,
    struct_decls: Vec<StructDeclCandidateJson>,
    global_type_links: Vec<GlobalTypeLinkCandidateJson>,
    interproc: InterprocSummaryJson,
    plans: r2types::AnalysisPlans,
    #[serde(skip_serializing_if = "r2ssa::AssumptionSet::is_empty")]
    assumptions: r2ssa::AssumptionSet,
    #[serde(skip_serializing_if = "r2types::AssumptionUsageReport::is_empty")]
    assumption_usage: r2types::AssumptionUsageReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    semantics: Option<r2sym::SemanticArtifact>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiled_semantics: Option<analysis::sym::CompiledSemanticInfo>,
    mutation_plan: SessionMutationPlanJson,
    diagnostics: TypeWritebackDiagnosticsJson,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    phase_timings: Vec<PhaseTimingJson>,
}

#[derive(Debug, serde::Serialize, Default)]
struct SessionMutationPlanJson {
    mutations: Vec<SessionMutationJson>,
    diagnostics: Vec<String>,
}

const R2SLEIGH_MUTATION_SIGNATURE: u32 = 0;
const R2SLEIGH_MUTATION_CALLCONV: u32 = 1;
const R2SLEIGH_MUTATION_VAR: u32 = 2;
const R2SLEIGH_MUTATION_VAR_RENAME: u32 = 3;
const R2SLEIGH_MUTATION_VAR_TYPE: u32 = 4;
const R2SLEIGH_MUTATION_XREF: u32 = 5;
const R2SLEIGH_MUTATION_COMMENT: u32 = 6;
const R2SLEIGH_MUTATION_FLAG: u32 = 7;
const R2SLEIGH_MUTATION_TYPE_DECL: u32 = 8;
const R2SLEIGH_MUTATION_TYPE_LINK: u32 = 9;

const R2SLEIGH_CONTEXT_VAR_REGISTER: u32 = 0;
const R2SLEIGH_CONTEXT_VAR_STACK: u32 = 1;
const R2SLEIGH_CONTEXT_STACK_LOCAL: u32 = 0;
const R2SLEIGH_CONTEXT_STACK_ARG: u32 = 1;
const R2SLEIGH_CONTEXT_STACK_HOME: u32 = 2;
const R2SLEIGH_CONTEXT_STACK_SAVED_REG: u32 = 3;
const R2SLEIGH_CONTEXT_STACK_SAVED_FP: u32 = 4;
const R2SLEIGH_CONTEXT_STACK_UNKNOWN: u32 = 5;
const R2SLEIGH_CONTEXT_BASE_STRUCT: u32 = 0;
const R2SLEIGH_CONTEXT_BASE_UNION: u32 = 1;
const R2SLEIGH_CONTEXT_BASE_ENUM: u32 = 2;
const R2SLEIGH_CONTEXT_BASE_TYPEDEF: u32 = 3;
const R2SLEIGH_CONTEXT_BASE_ATOMIC: u32 = 4;

#[repr(C)]
pub struct R2SleighContextParam {
    name: *const c_char,
    type_name: *const c_char,
    cc_reg: *const c_char,
}

#[repr(C)]
pub struct R2SleighContextVar {
    kind: u32,
    name: *const c_char,
    type_name: *const c_char,
    reg: *const c_char,
    base: *const c_char,
    offset: i64,
    has_offset: i32,
    role: u32,
    param_index: i64,
    param_name: *const c_char,
    source_reg: *const c_char,
    is_arg: i32,
}

#[repr(C)]
pub struct R2SleighContextBaseMember {
    name: *const c_char,
    type_name: *const c_char,
    offset: u64,
    size_bits: u64,
    has_size_bits: i32,
}

#[repr(C)]
pub struct R2SleighContextEnumVariant {
    name: *const c_char,
    value: i64,
}

#[repr(C)]
pub struct R2SleighContextBaseType {
    kind: u32,
    name: *const c_char,
    type_name: *const c_char,
    size_bits: u64,
    has_size_bits: i32,
    members: *const R2SleighContextBaseMember,
    num_members: usize,
    variants: *const R2SleighContextEnumVariant,
    num_variants: usize,
}

#[repr(C)]
pub struct R2SleighFunctionContext {
    schema_version: u32,
    dirty_epoch: u64,
    context_hash: u64,
    type_dirty_epoch: u64,
    external_context_json: *const c_char,
    signature_name: *const c_char,
    signature_ret_type: *const c_char,
    signature_callconv: *const c_char,
    signature_noreturn: i32,
    params: *const R2SleighContextParam,
    num_params: usize,
    vars: *const R2SleighContextVar,
    num_vars: usize,
    base_types: *const R2SleighContextBaseType,
    num_base_types: usize,
    assumptions_json: *const c_char,
}

#[repr(C)]
pub struct R2SleighInterprocSeed {
    id: u64,
    name: *const c_char,
    arg_count_hint: usize,
    has_arg_count_hint: i32,
}

#[repr(C)]
pub struct R2SleighInterprocScope {
    schema_version: u32,
    functions: *const analysis::sym::R2ILFunctionBlocks,
    num_functions: usize,
    seeds: *const R2SleighInterprocSeed,
    num_seeds: usize,
}

#[repr(C)]
pub struct R2SleighDebugSeed {
    schema_version: u32,
    seed_hash: u64,
}

#[repr(C)]
pub struct R2SleighBudgetConfig {
    schema_version: u32,
    interproc_iter: usize,
    interproc_max_iters: usize,
    interproc_converged: i32,
    global_max_links: usize,
    max_type_decls: usize,
    max_mutations: usize,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R2SleighAnalysisPolicy {
    mode: u32,
    type_writeback_mode: u32,
    type_min_conf: i32,
    type_rename_min_conf: i32,
    type_struct_min_conf: i32,
    type_interproc_max_iters: i32,
    type_max_blocks: i32,
    type_global_max_links: i32,
    type_max_decls: i32,
    type_max_mutations: i32,
}

const R2_ANAL_PLUGIN_ANALYSIS_DEPTH_BASIC: u32 = 1;
const R2_ANAL_PLUGIN_ANALYSIS_DEPTH_AGGRESSIVE: u32 = 3;
const R2SLEIGH_MODE_FAST: u32 = 0;
const R2SLEIGH_MODE_BALANCED: u32 = 1;
const R2SLEIGH_MODE_FULL: u32 = 2;
const R2SLEIGH_TYPE_WRITEBACK_OFF: u32 = 0;
const R2SLEIGH_TYPE_WRITEBACK_BALANCED: u32 = 1;
const R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE: u32 = 2;
const R2SLEIGH_TYPE_MIN_CONF_DEFAULT: i32 = 85;
const R2SLEIGH_TYPE_RENAME_MIN_CONF_DEFAULT: i32 = 93;
const R2SLEIGH_TYPE_STRUCT_MIN_CONF_DEFAULT: i32 = 85;

fn analysis_policy_for_depth(depth: u32) -> R2SleighAnalysisPolicy {
    let mut policy = R2SleighAnalysisPolicy {
        mode: R2SLEIGH_MODE_BALANCED,
        type_writeback_mode: R2SLEIGH_TYPE_WRITEBACK_BALANCED,
        type_min_conf: R2SLEIGH_TYPE_MIN_CONF_DEFAULT,
        type_rename_min_conf: R2SLEIGH_TYPE_RENAME_MIN_CONF_DEFAULT,
        type_struct_min_conf: R2SLEIGH_TYPE_STRUCT_MIN_CONF_DEFAULT,
        type_interproc_max_iters: 4,
        type_max_blocks: 200,
        type_global_max_links: 32,
        type_max_decls: 32,
        type_max_mutations: 128,
    };
    match depth {
        R2_ANAL_PLUGIN_ANALYSIS_DEPTH_BASIC => {
            policy.mode = R2SLEIGH_MODE_FAST;
            policy.type_writeback_mode = R2SLEIGH_TYPE_WRITEBACK_OFF;
            policy.type_interproc_max_iters = 1;
            policy.type_max_blocks = 96;
            policy.type_global_max_links = 8;
            policy.type_max_decls = 8;
            policy.type_max_mutations = 32;
        }
        R2_ANAL_PLUGIN_ANALYSIS_DEPTH_AGGRESSIVE => {
            policy.mode = R2SLEIGH_MODE_FULL;
            policy.type_writeback_mode = R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE;
            policy.type_interproc_max_iters = 12;
            policy.type_max_blocks = 500;
            policy.type_global_max_links = 128;
            policy.type_max_decls = 64;
            policy.type_max_mutations = 512;
        }
        _ => {}
    }
    policy
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_analysis_policy_for_depth(depth: u32) -> R2SleighAnalysisPolicy {
    analysis_policy_for_depth(depth)
}

#[repr(C)]
pub struct R2SleighSessionInput {
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    function_addr: u64,
    function_name: *const c_char,
    function_context: R2SleighFunctionContext,
    interproc_scope: R2SleighInterprocScope,
    debug_seed: R2SleighDebugSeed,
    budget: R2SleighBudgetConfig,
}

fn optional_cstr(ptr: *const c_char) -> Option<String> {
    if ptr.is_null() {
        return None;
    }
    let text = unsafe { CStr::from_ptr(ptr) }.to_string_lossy();
    let trimmed = text.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_string())
    }
}

fn typed_stack_role(role: u32) -> r2types::ExternalStackSlotRole {
    match role {
        R2SLEIGH_CONTEXT_STACK_LOCAL => r2types::ExternalStackSlotRole::Local,
        R2SLEIGH_CONTEXT_STACK_ARG => r2types::ExternalStackSlotRole::StackArg,
        R2SLEIGH_CONTEXT_STACK_HOME => r2types::ExternalStackSlotRole::ParamHome,
        R2SLEIGH_CONTEXT_STACK_SAVED_REG => r2types::ExternalStackSlotRole::SavedReg,
        R2SLEIGH_CONTEXT_STACK_SAVED_FP => r2types::ExternalStackSlotRole::SavedFp,
        R2SLEIGH_CONTEXT_STACK_UNKNOWN => r2types::ExternalStackSlotRole::Unknown,
        _ => r2types::ExternalStackSlotRole::Unknown,
    }
}

fn typed_base_type_kind(kind: u32) -> r2types::ExternalBaseTypeKind {
    match kind {
        R2SLEIGH_CONTEXT_BASE_STRUCT => r2types::ExternalBaseTypeKind::Struct,
        R2SLEIGH_CONTEXT_BASE_UNION => r2types::ExternalBaseTypeKind::Union,
        R2SLEIGH_CONTEXT_BASE_ENUM => r2types::ExternalBaseTypeKind::Enum,
        R2SLEIGH_CONTEXT_BASE_TYPEDEF => r2types::ExternalBaseTypeKind::Typedef,
        R2SLEIGH_CONTEXT_BASE_ATOMIC => r2types::ExternalBaseTypeKind::Atomic,
        _ => r2types::ExternalBaseTypeKind::Atomic,
    }
}

unsafe fn typed_function_context_to_parsed(
    context: &R2SleighFunctionContext,
    fallback_json: &str,
    ptr_bits: u32,
) -> r2types::ParsedExternalContext {
    let fallback = serde_json::from_str::<r2types::ExternalContextJson>(fallback_json).ok();
    let mut raw = r2types::ExternalContextJson {
        context: Some(r2types::ExternalContextMetadataJson {
            schema_version: (context.schema_version != 0).then_some(context.schema_version as u64),
            dirty_epoch: Some(context.dirty_epoch),
            type_dirty_epoch: (context.type_dirty_epoch != 0).then_some(context.type_dirty_epoch),
            context_hash: Some(context.context_hash),
        }),
        signature: None,
        vars: Vec::new(),
        base_types: Vec::new(),
        known_signatures: fallback
            .as_ref()
            .map(|ctx| ctx.known_signatures.clone())
            .unwrap_or_default(),
        assumptions: Vec::new(),
    };

    let params = if context.params.is_null() || context.num_params == 0 {
        &[][..]
    } else {
        unsafe { slice::from_raw_parts(context.params, context.num_params) }
    };
    let signature_params = params
        .iter()
        .map(|param| r2types::ExternalSignatureParamJson {
            name: optional_cstr(param.name),
            ty: optional_cstr(param.type_name),
            cc_reg: optional_cstr(param.cc_reg),
        })
        .collect::<Vec<_>>();
    let has_signature = optional_cstr(context.signature_name).is_some()
        || optional_cstr(context.signature_ret_type).is_some()
        || optional_cstr(context.signature_callconv).is_some()
        || context.signature_noreturn != 0
        || !signature_params.is_empty();
    if has_signature {
        raw.signature = Some(r2types::ExternalSignatureJson {
            name: optional_cstr(context.signature_name),
            ret_type: optional_cstr(context.signature_ret_type),
            callconv: optional_cstr(context.signature_callconv),
            noreturn: context.signature_noreturn != 0,
            params: signature_params,
        });
    }

    let vars = if context.vars.is_null() || context.num_vars == 0 {
        &[][..]
    } else {
        unsafe { slice::from_raw_parts(context.vars, context.num_vars) }
    };
    raw.vars = vars
        .iter()
        .enumerate()
        .map(|(idx, var)| {
            let (kind, is_register) = match var.kind {
                R2SLEIGH_CONTEXT_VAR_REGISTER => (r2types::ExternalVarKind::Register, true),
                R2SLEIGH_CONTEXT_VAR_STACK => (r2types::ExternalVarKind::Stack, false),
                _ => (r2types::ExternalVarKind::Stack, false),
            };
            let fallback_name = if is_register {
                format!("arg{}", idx + 1)
            } else {
                format!("stack_{:x}", var.offset)
            };
            r2types::ExternalVarJson {
                kind,
                name: optional_cstr(var.name).unwrap_or(fallback_name),
                ty: optional_cstr(var.type_name),
                is_arg: var.is_arg != 0,
                reg: optional_cstr(var.reg),
                base: optional_cstr(var.base),
                offset: (var.has_offset != 0).then_some(var.offset),
                role: Some(typed_stack_role(var.role)),
                param_index: (var.param_index >= 0).then_some(var.param_index as usize),
                param_name: optional_cstr(var.param_name),
                source_reg: optional_cstr(var.source_reg),
            }
        })
        .collect();

    let base_types = if context.base_types.is_null() || context.num_base_types == 0 {
        &[][..]
    } else {
        unsafe { slice::from_raw_parts(context.base_types, context.num_base_types) }
    };
    raw.base_types = if base_types.is_empty() {
        fallback
            .as_ref()
            .map(|ctx| ctx.base_types.clone())
            .unwrap_or_default()
    } else {
        base_types
            .iter()
            .map(|base_type| {
                let members = if base_type.members.is_null() || base_type.num_members == 0 {
                    &[][..]
                } else {
                    unsafe { slice::from_raw_parts(base_type.members, base_type.num_members) }
                };
                let variants = if base_type.variants.is_null() || base_type.num_variants == 0 {
                    &[][..]
                } else {
                    unsafe { slice::from_raw_parts(base_type.variants, base_type.num_variants) }
                };
                r2types::ExternalBaseTypeJson {
                    kind: typed_base_type_kind(base_type.kind),
                    name: optional_cstr(base_type.name).unwrap_or_default(),
                    members: members
                        .iter()
                        .map(|member| r2types::ExternalBaseTypeMemberJson {
                            name: optional_cstr(member.name).unwrap_or_default(),
                            ty: optional_cstr(member.type_name)
                                .unwrap_or_else(|| "void *".to_string()),
                            offset: member.offset,
                            size_bits: (member.has_size_bits != 0).then_some(member.size_bits),
                        })
                        .collect(),
                    variants: variants
                        .iter()
                        .map(|variant| r2types::ExternalEnumVariantJson {
                            name: optional_cstr(variant.name).unwrap_or_default(),
                            value: variant.value,
                        })
                        .collect(),
                    ty: optional_cstr(base_type.type_name),
                    size_bits: (base_type.has_size_bits != 0).then_some(base_type.size_bits),
                }
            })
            .collect()
    };

    if let Some(assumptions) = optional_cstr(context.assumptions_json)
        && let Ok(parsed) = serde_json::from_str::<Vec<r2ssa::AnalysisAssumption>>(&assumptions)
    {
        raw.assumptions = parsed;
    } else if let Some(fallback) = fallback.as_ref() {
        raw.assumptions = fallback.assumptions.clone();
    }

    r2types::parse_external_context(raw, ptr_bits)
}

unsafe fn typed_interproc_scope_facts(
    scope: &R2SleighInterprocScope,
) -> types::InterprocScopeFacts {
    if scope.seeds.is_null() || scope.num_seeds == 0 {
        return types::empty_interproc_scope_facts();
    }
    let seeds = unsafe { slice::from_raw_parts(scope.seeds, scope.num_seeds) };
    types::interproc_scope_facts_from_seed_entries(seeds.iter().map(|seed| {
        (
            seed.id,
            optional_cstr(seed.name),
            (seed.has_arg_count_hint != 0).then_some(seed.arg_count_hint),
        )
    }))
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighMutation {
    kind: u32,
    signature: *const c_char,
    callconv: *const c_char,
    old_name: *const c_char,
    name: *const c_char,
    reg: *const c_char,
    type_name: *const c_char,
    text: *const c_char,
    addr: u64,
    size: u64,
    delta: i64,
    var_kind: c_char,
    is_arg: i32,
    confidence: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSignatureParam {
    name: *const c_char,
    type_name: *const c_char,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSignatureFact {
    signature: *const c_char,
    ret_type: *const c_char,
    callconv: *const c_char,
    arch: *const c_char,
    params: *const R2SleighSignatureParam,
    num_params: usize,
    confidence: u8,
    callconv_confidence: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighAnnotation {
    addr: u64,
    comment: *const c_char,
}

pub struct R2SleighAnnotations {
    items: Vec<R2SleighAnnotation>,
    _strings: Vec<CString>,
}

pub struct R2SleighU64Array {
    values: Vec<u64>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighRuntimeSource {
    addr: u64,
    size: u64,
}

pub struct R2SleighRuntimeSources {
    items: Vec<R2SleighRuntimeSource>,
}

pub struct R2SleighSessionResult {
    report_json: CString,
    type_writeback_json: CString,
    type_writeback_hash: u64,
    mutations: Vec<R2SleighMutation>,
    signature_fact: R2SleighSignatureFact,
    _signature_params: Vec<R2SleighSignatureParam>,
    _strings: Vec<CString>,
}

#[derive(Clone, Copy, Default)]
struct TypeWritebackCacheEntry {
    key: u64,
    dep_hash: u64,
    payload_hash: u64,
    applied_hash: u64,
}

const TYPE_WRITEBACK_CACHE_LIMIT: usize = 4096;

struct BoundedArcCache<K, V>
where
    K: Copy + Eq + Hash + Ord,
{
    limit: usize,
    next_ticket: u64,
    items: HashMap<K, (u64, Arc<V>)>,
    recency: BTreeMap<(u64, K), K>,
}

impl<K, V> BoundedArcCache<K, V>
where
    K: Copy + Eq + Hash + Ord,
{
    fn new(limit: usize) -> Self {
        Self {
            limit,
            next_ticket: 1,
            items: HashMap::new(),
            recency: BTreeMap::new(),
        }
    }

    fn clear(&mut self) {
        self.next_ticket = 1;
        self.items.clear();
        self.recency.clear();
    }

    fn len(&self) -> usize {
        self.items.len()
    }

    fn get(&mut self, key: K) -> Option<Arc<V>> {
        let (_, value) = self.items.get(&key)?;
        let value = Arc::clone(value);
        self.touch_existing(key);
        Some(value)
    }

    fn put(&mut self, key: K, value: V) {
        if self.limit == 0 {
            return;
        }
        if self.items.contains_key(&key) {
            self.remove_recency(key);
        }
        while self.items.len() >= self.limit && !self.items.contains_key(&key) {
            self.evict_oldest();
        }
        let ticket = self.allocate_ticket();
        self.items.insert(key, (ticket, Arc::new(value)));
        self.recency.insert((ticket, key), key);
    }

    fn touch_existing(&mut self, key: K) {
        let Some((old_ticket, value)) = self
            .items
            .get(&key)
            .map(|(ticket, value)| (*ticket, Arc::clone(value)))
        else {
            return;
        };
        self.recency.remove(&(old_ticket, key));
        let ticket = self.allocate_ticket();
        self.items.insert(key, (ticket, value));
        self.recency.insert((ticket, key), key);
    }

    fn remove_recency(&mut self, key: K) {
        if let Some((ticket, _)) = self.items.get(&key) {
            self.recency.remove(&(*ticket, key));
        }
    }

    fn evict_oldest(&mut self) {
        let Some((recency_key, key)) = self
            .recency
            .iter()
            .next()
            .map(|(recency_key, key)| (*recency_key, *key))
        else {
            self.items.clear();
            return;
        };
        self.recency.remove(&recency_key);
        self.items.remove(&key);
    }

    fn allocate_ticket(&mut self) -> u64 {
        let ticket = self.next_ticket;
        self.next_ticket = self.next_ticket.wrapping_add(1).max(1);
        ticket
    }
}

static TYPE_WRITEBACK_CACHE: LazyLock<RwLock<BoundedArcCache<u64, TypeWritebackCacheEntry>>> =
    LazyLock::new(|| RwLock::new(BoundedArcCache::new(TYPE_WRITEBACK_CACHE_LIMIT)));

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_type_writeback_cache_clear() {
    TYPE_WRITEBACK_CACHE
        .write()
        .expect("type writeback cache lock poisoned")
        .clear();
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_type_writeback_cache_len() -> usize {
    TYPE_WRITEBACK_CACHE
        .read()
        .expect("type writeback cache lock poisoned")
        .len()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_type_writeback_cache_get(
    addr: u64,
    key: *mut u64,
    dep_hash: *mut u64,
    payload_hash: *mut u64,
    applied_hash: *mut u64,
) -> i32 {
    let Some(entry) = TYPE_WRITEBACK_CACHE
        .write()
        .expect("type writeback cache lock poisoned")
        .get(addr)
    else {
        return 0;
    };
    unsafe {
        if !key.is_null() {
            *key = entry.key;
        }
        if !dep_hash.is_null() {
            *dep_hash = entry.dep_hash;
        }
        if !payload_hash.is_null() {
            *payload_hash = entry.payload_hash;
        }
        if !applied_hash.is_null() {
            *applied_hash = entry.applied_hash;
        }
    }
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_type_writeback_cache_put(
    addr: u64,
    key: u64,
    dep_hash: u64,
    payload_hash: u64,
    applied_hash: u64,
) -> i32 {
    let mut cache = TYPE_WRITEBACK_CACHE
        .write()
        .expect("type writeback cache lock poisoned");
    cache.put(
        addr,
        TypeWritebackCacheEntry {
            key,
            dep_hash,
            payload_hash,
            applied_hash,
        },
    );
    1
}

#[cfg(test)]
mod type_writeback_cache_tests {
    use super::*;
    use std::sync::Mutex;

    static CACHE_TEST_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

    #[test]
    fn analysis_policy_tracks_native_radare2_depths() {
        let basic = analysis_policy_for_depth(R2_ANAL_PLUGIN_ANALYSIS_DEPTH_BASIC);
        assert_eq!(basic.mode, R2SLEIGH_MODE_FAST);
        assert_eq!(basic.type_writeback_mode, R2SLEIGH_TYPE_WRITEBACK_OFF);
        assert_eq!(basic.type_interproc_max_iters, 1);
        assert_eq!(basic.type_max_blocks, 96);
        assert_eq!(basic.type_global_max_links, 8);

        let balanced = analysis_policy_for_depth(0);
        assert_eq!(balanced.mode, R2SLEIGH_MODE_BALANCED);
        assert_eq!(
            balanced.type_writeback_mode,
            R2SLEIGH_TYPE_WRITEBACK_BALANCED
        );
        assert_eq!(balanced.type_interproc_max_iters, 4);
        assert_eq!(balanced.type_max_blocks, 200);
        assert_eq!(balanced.type_global_max_links, 32);

        let aggressive = analysis_policy_for_depth(R2_ANAL_PLUGIN_ANALYSIS_DEPTH_AGGRESSIVE);
        assert_eq!(aggressive.mode, R2SLEIGH_MODE_FULL);
        assert_eq!(
            aggressive.type_writeback_mode,
            R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE
        );
        assert_eq!(aggressive.type_interproc_max_iters, 12);
        assert_eq!(aggressive.type_max_blocks, 500);
        assert_eq!(aggressive.type_global_max_links, 128);
    }

    #[test]
    fn type_writeback_cache_is_rust_owned_and_address_keyed() {
        let _guard = CACHE_TEST_LOCK.lock().expect("cache test lock poisoned");
        r2sleigh_type_writeback_cache_clear();
        assert_eq!(r2sleigh_type_writeback_cache_len(), 0);

        assert_eq!(r2sleigh_type_writeback_cache_put(0x401000, 1, 2, 3, 4), 1);
        assert_eq!(r2sleigh_type_writeback_cache_len(), 1);

        let mut key = 0;
        let mut dep_hash = 0;
        let mut payload_hash = 0;
        let mut applied_hash = 0;
        assert_eq!(
            r2sleigh_type_writeback_cache_get(
                0x401000,
                &mut key,
                &mut dep_hash,
                &mut payload_hash,
                &mut applied_hash,
            ),
            1
        );
        assert_eq!((key, dep_hash, payload_hash, applied_hash), (1, 2, 3, 4));

        assert_eq!(
            r2sleigh_type_writeback_cache_put(0x401000, 10, 20, 30, 40),
            1
        );
        assert_eq!(r2sleigh_type_writeback_cache_len(), 1);
        assert_eq!(
            r2sleigh_type_writeback_cache_get(
                0x401000,
                &mut key,
                &mut dep_hash,
                &mut payload_hash,
                &mut applied_hash,
            ),
            1
        );
        assert_eq!(
            (key, dep_hash, payload_hash, applied_hash),
            (10, 20, 30, 40)
        );

        r2sleigh_type_writeback_cache_clear();
    }

    #[test]
    fn type_writeback_cache_evicts_oldest_entry_deterministically() {
        let _guard = CACHE_TEST_LOCK.lock().expect("cache test lock poisoned");
        r2sleigh_type_writeback_cache_clear();

        for idx in 0..TYPE_WRITEBACK_CACHE_LIMIT as u64 {
            assert_eq!(
                r2sleigh_type_writeback_cache_put(0x500000 + idx, idx, idx + 1, idx + 2, idx + 3),
                1
            );
        }
        assert_eq!(
            r2sleigh_type_writeback_cache_len(),
            TYPE_WRITEBACK_CACHE_LIMIT
        );

        let mut key = 0;
        let mut dep_hash = 0;
        let mut payload_hash = 0;
        let mut applied_hash = 0;
        assert_eq!(
            r2sleigh_type_writeback_cache_get(
                0x500000,
                &mut key,
                &mut dep_hash,
                &mut payload_hash,
                &mut applied_hash,
            ),
            1
        );
        assert_eq!((key, dep_hash, payload_hash, applied_hash), (0, 1, 2, 3));

        assert_eq!(
            r2sleigh_type_writeback_cache_put(0x600000, 9, 10, 11, 12),
            1
        );
        assert_eq!(
            r2sleigh_type_writeback_cache_len(),
            TYPE_WRITEBACK_CACHE_LIMIT
        );
        assert_eq!(
            r2sleigh_type_writeback_cache_get(
                0x500000,
                &mut key,
                &mut dep_hash,
                &mut payload_hash,
                &mut applied_hash,
            ),
            1
        );
        assert_eq!(
            r2sleigh_type_writeback_cache_get(
                0x500001,
                &mut key,
                &mut dep_hash,
                &mut payload_hash,
                &mut applied_hash,
            ),
            0
        );
        assert_eq!(
            r2sleigh_type_writeback_cache_get(
                0x600000,
                &mut key,
                &mut dep_hash,
                &mut payload_hash,
                &mut applied_hash,
            ),
            1
        );
        assert_eq!((key, dep_hash, payload_hash, applied_hash), (9, 10, 11, 12));

        r2sleigh_type_writeback_cache_clear();
    }
}

struct FunctionAnalysisSessionReport {
    report_json: String,
    type_writeback_json: String,
    type_writeback_hash: u64,
    mutations: Vec<R2SleighMutation>,
    signature_fact: R2SleighSignatureFact,
    signature_params: Vec<R2SleighSignatureParam>,
    strings: Vec<CString>,
}

#[derive(Debug, serde::Serialize)]
struct SessionMutationJson {
    kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    signature: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ret_type: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    params: Vec<InferredParamJson>,
    #[serde(skip_serializing_if = "Option::is_none")]
    callconv: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    old_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reg: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none", rename = "type")]
    type_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    text: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    addr: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    size: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    delta: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    var_kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    is_arg: Option<bool>,
    confidence: u8,
    source: String,
    evidence: Vec<String>,
}

#[derive(Debug, serde::Serialize)]
struct CfgRiskSummaryJson {
    block_count: usize,
    loop_count: usize,
    back_edge_count: usize,
    switch_block_count: usize,
    max_switch_cases: usize,
}

#[derive(Debug, serde::Serialize)]
struct SemanticRoutePlanJson {
    kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    comment: Option<String>,
}

#[derive(Debug, serde::Serialize)]
struct FunctionAnalysisSessionReportJson {
    function_name: String,
    function_addr: u64,
    cfg_risk: CfgRiskSummaryJson,
    plans: r2types::AnalysisPlans,
    #[serde(skip_serializing_if = "r2ssa::AssumptionSet::is_empty")]
    assumptions: r2ssa::AssumptionSet,
    #[serde(skip_serializing_if = "r2types::AssumptionUsageReport::is_empty")]
    assumption_usage: r2types::AssumptionUsageReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    semantic: Option<analysis::sym::CompiledSemanticInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    semantic_build_plan: Option<r2sym::ArtifactBuildPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    semantic_route: Option<SemanticRoutePlanJson>,
    #[serde(skip_serializing_if = "Option::is_none")]
    summary_diagnostics: Option<r2ssa::InterprocSummaryDiagnostics>,
    type_writeback: InferredTypeWritebackJson,
    prefer_bounded_type_plan: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    phase_timings: Vec<PhaseTimingJson>,
}

fn cfg_risk_summary_json(summary: r2ssa::CFGRiskSummary) -> CfgRiskSummaryJson {
    CfgRiskSummaryJson {
        block_count: summary.block_count,
        loop_count: summary.loop_count,
        back_edge_count: summary.back_edge_count,
        switch_block_count: summary.switch_block_count,
        max_switch_cases: summary.max_switch_cases,
    }
}

fn caller_prefers_bounded_type_plan(interproc: &InterprocInferenceInput<'_>) -> bool {
    interproc.max_iters <= 1 && !interproc.converged
}

fn phase_timing(phase: &str, start: Instant) -> PhaseTimingJson {
    PhaseTimingJson {
        phase: phase.to_string(),
        elapsed_us: start.elapsed().as_micros().min(u128::from(u64::MAX)) as u64,
    }
}

struct BoundedCfgTypePayloadInput<'a> {
    function_name: &'a str,
    arch_name: &'a str,
    ptr_bits: u32,
    callconv: Option<&'a str>,
    interproc: InterprocInferenceInput<'a>,
    function_facts: &'a r2types::FunctionFacts,
    symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
    budget: TypeOutputBudget,
    reason: String,
}

fn bounded_cfg_type_payload(input: BoundedCfgTypePayloadInput<'_>) -> InferredTypeWritebackJson {
    let plan = r2engine::bounded_cfg_type_writeback_plan(
        input.function_name,
        input.arch_name,
        input.ptr_bits,
        input.callconv,
        input.function_facts,
        input.reason,
    );
    writeback_plan_json(
        plan,
        InterprocSummaryJson {
            callsite_count: 0,
            iterations: input.interproc.iter.max(1),
            max_iterations: input.interproc.max_iters.max(input.interproc.iter.max(1)),
            converged: input.interproc.converged,
            summary: None,
            summary_json: None,
            scope: merged_interproc_scope_report(
                input.interproc.scope_report,
                input.symbolic_scope,
            ),
        },
        input.function_facts,
        None,
        None,
        input.budget,
    )
}

fn push_phase(timings: &mut Vec<PhaseTimingJson>, phase: &str, start: Instant) {
    timings.push(phase_timing(phase, start));
}

fn push_missing_zero_phase(timings: &mut Vec<PhaseTimingJson>, phase: &str) {
    if timings.iter().any(|timing| timing.phase == phase) {
        return;
    }
    timings.push(PhaseTimingJson {
        phase: phase.to_string(),
        elapsed_us: 0,
    });
}

fn complete_type_phase_timings(timings: &mut Vec<PhaseTimingJson>) {
    for phase in [
        "ssa_build",
        "interproc_summary",
        "semantic_artifact",
        "local_struct_inference",
        "local_field_access_inference",
        "recovered_vars",
        "writeback",
    ] {
        push_missing_zero_phase(timings, phase);
    }
}

fn semantic_route_plan_json(route: r2dec::SemanticRoutePlan) -> SemanticRoutePlanJson {
    match route {
        r2dec::SemanticRoutePlan::Standard => SemanticRoutePlanJson {
            kind: "standard".to_string(),
            reason: None,
            comment: None,
        },
        r2dec::SemanticRoutePlan::StructuredWorker { reason } => SemanticRoutePlanJson {
            kind: "structured_worker".to_string(),
            reason: Some(reason),
            comment: None,
        },
        r2dec::SemanticRoutePlan::LinearWorker { reason } => SemanticRoutePlanJson {
            kind: "linear_worker".to_string(),
            reason: Some(reason),
            comment: None,
        },
        r2dec::SemanticRoutePlan::SummaryIslands { reason } => SemanticRoutePlanJson {
            kind: "summary_islands".to_string(),
            reason: Some(reason),
            comment: None,
        },
        r2dec::SemanticRoutePlan::VmSummary { reason } => SemanticRoutePlanJson {
            kind: "vm_summary".to_string(),
            reason: Some(reason),
            comment: None,
        },
        r2dec::SemanticRoutePlan::FallbackComment { comment } => SemanticRoutePlanJson {
            kind: "fallback_comment".to_string(),
            reason: None,
            comment: Some(comment),
        },
    }
}

fn evidence_json(evidence: &[r2types::WritebackEvidence]) -> Vec<String> {
    evidence
        .iter()
        .map(|tag| tag.as_str().to_string())
        .collect()
}

fn struct_fields_json(fields: &[r2types::StructFieldCandidate]) -> Vec<StructFieldCandidateJson> {
    fields
        .iter()
        .map(|field| StructFieldCandidateJson {
            name: field.name.clone(),
            offset: field.offset,
            field_type: field.field_type.clone(),
            confidence: field.confidence,
        })
        .collect()
}

#[derive(Clone, Copy)]
struct TypeOutputBudget {
    global_max_links: usize,
    max_type_decls: usize,
    max_mutations: usize,
}

impl TypeOutputBudget {
    fn new(global_max_links: usize, max_type_decls: usize, max_mutations: usize) -> Self {
        Self {
            global_max_links: global_max_links.max(1),
            max_type_decls: max_type_decls.max(1),
            max_mutations: max_mutations.max(1),
        }
    }
}

fn push_budgeted_mutation(
    mutations: &mut Vec<SessionMutationJson>,
    diagnostics: &mut Vec<String>,
    emitted: &mut usize,
    skipped: &mut usize,
    budget: TypeOutputBudget,
    mutation: SessionMutationJson,
) {
    if *emitted < budget.max_mutations {
        mutations.push(mutation);
        *emitted += 1;
    } else {
        *skipped += 1;
        if *skipped == 1 {
            diagnostics.push(format!(
                "non-signature mutation plan truncated to {} item(s)",
                budget.max_mutations
            ));
        }
    }
}

fn mutation_plan_from_writeback(
    plan: &r2types::TypeWritebackPlan,
    budget: TypeOutputBudget,
) -> SessionMutationPlanJson {
    let mut mutations = Vec::new();
    let mut diagnostics = Vec::new();
    let mut emitted_budgeted = 0usize;
    let mut skipped_budgeted = 0usize;

    mutations.push(SessionMutationJson {
        kind: "signature".to_string(),
        signature: Some(plan.signature.signature.clone()),
        ret_type: Some(plan.signature.ret_type.clone()),
        params: plan
            .signature
            .params
            .iter()
            .map(|param| InferredParamJson {
                name: param.name.clone(),
                param_type: param.param_type.clone(),
            })
            .collect(),
        callconv: Some(plan.signature.callconv.clone()),
        old_name: None,
        name: Some(plan.signature.function_name.clone()),
        reg: None,
        type_name: None,
        text: None,
        addr: None,
        size: None,
        delta: None,
        var_kind: None,
        is_arg: None,
        confidence: plan.signature.confidence,
        source: "function_facts".to_string(),
        evidence: vec!["merged-signature".to_string()],
    });

    mutations.push(SessionMutationJson {
        kind: "callconv".to_string(),
        signature: None,
        ret_type: None,
        params: Vec::new(),
        callconv: Some(plan.signature.callconv.clone()),
        old_name: None,
        name: Some(plan.signature.function_name.clone()),
        reg: None,
        type_name: None,
        text: None,
        addr: None,
        size: None,
        delta: None,
        var_kind: None,
        is_arg: None,
        confidence: plan.signature.callconv_confidence,
        source: "function_facts".to_string(),
        evidence: vec!["calling-convention".to_string()],
    });

    for decl in plan.struct_decls.iter().take(budget.max_type_decls) {
        push_budgeted_mutation(
            &mut mutations,
            &mut diagnostics,
            &mut emitted_budgeted,
            &mut skipped_budgeted,
            budget,
            SessionMutationJson {
                kind: "type_decl".to_string(),
                signature: None,
                ret_type: None,
                params: Vec::new(),
                callconv: None,
                old_name: None,
                name: Some(decl.name.clone()),
                reg: None,
                type_name: None,
                text: Some(decl.decl.clone()),
                addr: None,
                size: None,
                delta: None,
                var_kind: None,
                is_arg: None,
                confidence: decl.confidence,
                source: decl.source.as_str().to_string(),
                evidence: vec!["struct-declaration".to_string()],
            },
        );
    }
    if plan.struct_decls.len() > budget.max_type_decls {
        diagnostics.push(format!(
            "type declaration mutation plan truncated from {} to {} item(s)",
            plan.struct_decls.len(),
            budget.max_type_decls
        ));
    }

    for candidate in &plan.var_type_candidates {
        if candidate.confidence >= 95 {
            push_budgeted_mutation(
                &mut mutations,
                &mut diagnostics,
                &mut emitted_budgeted,
                &mut skipped_budgeted,
                budget,
                SessionMutationJson {
                    kind: "var".to_string(),
                    signature: None,
                    ret_type: None,
                    params: Vec::new(),
                    callconv: None,
                    old_name: None,
                    name: Some(candidate.name.clone()),
                    reg: candidate.reg.clone(),
                    type_name: Some(candidate.var_type.clone()),
                    text: None,
                    addr: None,
                    size: Some(candidate.size as u64),
                    delta: Some(candidate.delta),
                    var_kind: Some(candidate.kind.clone()),
                    is_arg: Some(candidate.isarg),
                    confidence: candidate.confidence,
                    source: candidate.source.as_str().to_string(),
                    evidence: evidence_json(&candidate.evidence),
                },
            );
        }
        push_budgeted_mutation(
            &mut mutations,
            &mut diagnostics,
            &mut emitted_budgeted,
            &mut skipped_budgeted,
            budget,
            SessionMutationJson {
                kind: "var_type".to_string(),
                signature: None,
                ret_type: None,
                params: Vec::new(),
                callconv: None,
                old_name: Some(candidate.name.clone()),
                name: Some(candidate.name.clone()),
                reg: candidate.reg.clone(),
                type_name: Some(candidate.var_type.clone()),
                text: None,
                addr: None,
                size: Some(candidate.size as u64),
                delta: Some(candidate.delta),
                var_kind: Some(candidate.kind.clone()),
                is_arg: Some(candidate.isarg),
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: evidence_json(&candidate.evidence),
            },
        );
    }

    for candidate in &plan.var_rename_candidates {
        push_budgeted_mutation(
            &mut mutations,
            &mut diagnostics,
            &mut emitted_budgeted,
            &mut skipped_budgeted,
            budget,
            SessionMutationJson {
                kind: "var_rename".to_string(),
                signature: None,
                ret_type: None,
                params: Vec::new(),
                callconv: None,
                old_name: Some(candidate.name.clone()),
                name: Some(candidate.target_name.clone()),
                reg: None,
                type_name: None,
                text: None,
                addr: None,
                size: None,
                delta: None,
                var_kind: None,
                is_arg: None,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: evidence_json(&candidate.evidence),
            },
        );
    }

    for candidate in plan.global_type_links.iter().take(budget.global_max_links) {
        push_budgeted_mutation(
            &mut mutations,
            &mut diagnostics,
            &mut emitted_budgeted,
            &mut skipped_budgeted,
            budget,
            SessionMutationJson {
                kind: "type_link".to_string(),
                signature: None,
                ret_type: None,
                params: Vec::new(),
                callconv: None,
                old_name: None,
                name: None,
                reg: None,
                type_name: Some(candidate.target_type.clone()),
                text: None,
                addr: Some(candidate.addr),
                size: None,
                delta: None,
                var_kind: None,
                is_arg: None,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: vec!["global-type-link".to_string()],
            },
        );
    }
    if plan.global_type_links.len() > budget.global_max_links {
        diagnostics.push(format!(
            "global type-link mutation plan truncated from {} to {} item(s)",
            plan.global_type_links.len(),
            budget.global_max_links
        ));
    }

    SessionMutationPlanJson {
        mutations,
        diagnostics,
    }
}

fn session_mutation_kind_id(kind: &str) -> Option<u32> {
    match kind {
        "signature" => Some(R2SLEIGH_MUTATION_SIGNATURE),
        "callconv" => Some(R2SLEIGH_MUTATION_CALLCONV),
        "var" => Some(R2SLEIGH_MUTATION_VAR),
        "var_rename" => Some(R2SLEIGH_MUTATION_VAR_RENAME),
        "var_type" => Some(R2SLEIGH_MUTATION_VAR_TYPE),
        "xref" => Some(R2SLEIGH_MUTATION_XREF),
        "comment" => Some(R2SLEIGH_MUTATION_COMMENT),
        "flag" => Some(R2SLEIGH_MUTATION_FLAG),
        "type_decl" => Some(R2SLEIGH_MUTATION_TYPE_DECL),
        "type_link" => Some(R2SLEIGH_MUTATION_TYPE_LINK),
        _ => None,
    }
}

fn push_session_cstring(strings: &mut Vec<CString>, value: Option<&str>) -> *const c_char {
    let Some(value) = value.filter(|value| !value.is_empty()) else {
        return ptr::null();
    };
    let Ok(cstr) = CString::new(value) else {
        return ptr::null();
    };
    let ptr = cstr.as_ptr();
    strings.push(cstr);
    ptr
}

fn ffi_mutations_from_session_plan(
    plan: &SessionMutationPlanJson,
) -> (Vec<R2SleighMutation>, Vec<CString>) {
    let mut strings = Vec::new();
    let mut mutations = Vec::new();

    for mutation in &plan.mutations {
        let Some(kind) = session_mutation_kind_id(&mutation.kind) else {
            continue;
        };
        let var_kind = mutation
            .var_kind
            .as_deref()
            .and_then(|kind| kind.as_bytes().first().copied())
            .unwrap_or_default() as c_char;
        mutations.push(R2SleighMutation {
            kind,
            signature: push_session_cstring(&mut strings, mutation.signature.as_deref()),
            callconv: push_session_cstring(&mut strings, mutation.callconv.as_deref()),
            old_name: push_session_cstring(&mut strings, mutation.old_name.as_deref()),
            name: push_session_cstring(&mut strings, mutation.name.as_deref()),
            reg: push_session_cstring(&mut strings, mutation.reg.as_deref()),
            type_name: push_session_cstring(&mut strings, mutation.type_name.as_deref()),
            text: push_session_cstring(&mut strings, mutation.text.as_deref()),
            addr: mutation.addr.unwrap_or_default(),
            size: mutation.size.unwrap_or_default(),
            delta: mutation.delta.unwrap_or_default(),
            var_kind,
            is_arg: i32::from(mutation.is_arg.unwrap_or(false)),
            confidence: mutation.confidence,
        });
    }

    (mutations, strings)
}

fn ffi_signature_fact_from_type_writeback(
    type_writeback: &InferredTypeWritebackJson,
    strings: &mut Vec<CString>,
) -> (R2SleighSignatureFact, Vec<R2SleighSignatureParam>) {
    let mut params = Vec::with_capacity(type_writeback.params.len());
    for param in &type_writeback.params {
        params.push(R2SleighSignatureParam {
            name: push_session_cstring(strings, Some(param.name.as_str())),
            type_name: push_session_cstring(strings, Some(param.param_type.as_str())),
        });
    }
    let fact = R2SleighSignatureFact {
        signature: push_session_cstring(strings, Some(type_writeback.signature.as_str())),
        ret_type: push_session_cstring(strings, Some(type_writeback.ret_type.as_str())),
        callconv: push_session_cstring(strings, Some(type_writeback.callconv.as_str())),
        arch: push_session_cstring(strings, Some(type_writeback.arch.as_str())),
        params: if params.is_empty() {
            ptr::null()
        } else {
            params.as_ptr()
        },
        num_params: params.len(),
        confidence: type_writeback.confidence,
        callconv_confidence: type_writeback.callconv_confidence,
    };
    (fact, params)
}

fn writeback_plan_json(
    plan: r2types::TypeWritebackPlan,
    interproc: InterprocSummaryJson,
    function_facts: &r2types::FunctionFacts,
    semantics: Option<r2sym::SemanticArtifact>,
    compiled_semantics: Option<analysis::sym::CompiledSemanticInfo>,
    budget: TypeOutputBudget,
) -> InferredTypeWritebackJson {
    let mutation_plan = mutation_plan_from_writeback(&plan, budget);
    let mut warnings = plan.diagnostics.warnings;
    if plan.struct_decls.len() > budget.max_type_decls {
        warnings.push(format!(
            "type declaration report truncated from {} to {} item(s)",
            plan.struct_decls.len(),
            budget.max_type_decls
        ));
    }
    if plan.global_type_links.len() > budget.global_max_links {
        warnings.push(format!(
            "global type-link report truncated from {} to {} item(s)",
            plan.global_type_links.len(),
            budget.global_max_links
        ));
    }
    InferredTypeWritebackJson {
        function_name: plan.signature.function_name,
        signature: plan.signature.signature,
        ret_type: plan.signature.ret_type,
        params: plan
            .signature
            .params
            .into_iter()
            .map(|param| InferredParamJson {
                name: param.name,
                param_type: param.param_type,
            })
            .collect(),
        callconv: plan.signature.callconv,
        arch: plan.signature.arch,
        confidence: plan.signature.confidence,
        callconv_confidence: plan.signature.callconv_confidence,
        var_type_candidates: plan
            .var_type_candidates
            .into_iter()
            .map(|candidate| VarTypeCandidateJson {
                name: candidate.name,
                kind: candidate.kind,
                delta: candidate.delta,
                var_type: candidate.var_type,
                isarg: candidate.isarg,
                reg: candidate.reg,
                size: candidate.size,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: evidence_json(&candidate.evidence),
            })
            .collect(),
        var_rename_candidates: plan
            .var_rename_candidates
            .into_iter()
            .map(|candidate| VarRenameCandidateJson {
                name: candidate.name,
                target_name: candidate.target_name,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: evidence_json(&candidate.evidence),
            })
            .collect(),
        struct_decls: plan
            .struct_decls
            .into_iter()
            .take(budget.max_type_decls)
            .map(|decl| StructDeclCandidateJson {
                name: decl.name,
                decl: decl.decl,
                confidence: decl.confidence,
                source: decl.source.as_str().to_string(),
                fields: struct_fields_json(&decl.fields),
            })
            .collect(),
        global_type_links: plan
            .global_type_links
            .into_iter()
            .take(budget.global_max_links)
            .map(|candidate| GlobalTypeLinkCandidateJson {
                addr: candidate.addr,
                target_type: candidate.target_type,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
            })
            .collect(),
        interproc,
        plans: function_facts.plans.clone(),
        assumptions: function_facts.assumptions.clone(),
        assumption_usage: function_facts.assumption_usage.clone(),
        semantics,
        compiled_semantics,
        mutation_plan,
        diagnostics: TypeWritebackDiagnosticsJson {
            conflicts: plan.diagnostics.conflicts,
            warnings,
            solver_warnings: plan.diagnostics.solver_warnings,
        },
        phase_timings: Vec::new(),
    }
}

fn symbolic_scope_view_json(
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<serde_json::Value> {
    let scope = symbolic_scope?;
    let payloads = scope
        .helper_functions()
        .filter_map(|function| {
            function.name.as_ref().map(|name| {
                serde_json::json!({
                    "function_addr": function.id.0,
                    "function_name": name,
                })
            })
        })
        .collect::<Vec<_>>();
    let seeds = scope
        .helper_functions()
        .filter_map(|function| {
            function.name.as_ref().map(|name| {
                serde_json::json!({
                    "id": function.id.0,
                    "name": name,
                })
            })
        })
        .collect::<Vec<_>>();
    if seeds.is_empty() && payloads.is_empty() {
        return None;
    }
    Some(serde_json::json!({
        "phase": "symbolic_scope",
        "payloads": payloads,
        "seeds": seeds,
    }))
}

fn merged_interproc_scope_report(
    scope_report: Option<&serde_json::Value>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<serde_json::Value> {
    let Some(symbolic_scope_json) = symbolic_scope_view_json(symbolic_scope) else {
        return scope_report.cloned();
    };
    let Some(mut merged) = scope_report.cloned() else {
        return Some(symbolic_scope_json);
    };
    let (Some(merged_obj), Some(symbolic_obj)) =
        (merged.as_object_mut(), symbolic_scope_json.as_object())
    else {
        return Some(merged);
    };

    if !merged_obj.contains_key("phase")
        && let Some(phase) = symbolic_obj.get("phase")
    {
        merged_obj.insert("phase".to_string(), phase.clone());
    }
    for key in ["payloads", "seeds"] {
        let Some(serde_json::Value::Array(symbolic_items)) = symbolic_obj.get(key) else {
            continue;
        };
        let entry = merged_obj
            .entry(key.to_string())
            .or_insert_with(|| serde_json::Value::Array(Vec::new()));
        if let serde_json::Value::Array(items) = entry {
            items.extend(symbolic_items.iter().cloned());
        }
    }

    Some(merged)
}

fn type_writeback_payload_from_engine_response(
    response: r2engine::EngineTypeAnalysisResponse,
    interproc: InterprocInferenceInput<'_>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    budget: TypeOutputBudget,
) -> InferredTypeWritebackJson {
    let semantics = response.function_facts.semantics.clone();
    let compiled_semantics = semantics
        .as_ref()
        .map(analysis::sym::compiled_semantic_info);
    let scope = merged_interproc_scope_report(interproc.scope_report, symbolic_scope);
    let current_summary_json = response
        .current_summary
        .as_ref()
        .and_then(|summary| serde_json::to_string(summary).ok());

    writeback_plan_json(
        response.writeback_plan,
        InterprocSummaryJson {
            callsite_count: response.callsite_count,
            iterations: interproc.iter.max(1),
            max_iterations: interproc.max_iters.max(interproc.iter.max(1)),
            converged: interproc.converged,
            summary: response.current_summary,
            summary_json: current_summary_json,
            scope,
        },
        &response.function_facts,
        semantics,
        compiled_semantics,
        budget,
    )
}

struct SemanticTypeFallbackPayloadInput<'a> {
    function_name: &'a str,
    arch_name: &'a str,
    ptr_bits: u32,
    callconv: Option<&'a str>,
    interproc: InterprocInferenceInput<'a>,
    compiled: &'a r2sym::SemanticArtifact,
    function_facts: &'a r2types::FunctionFacts,
    symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
    apply_artifact_signature_hint: bool,
    budget: TypeOutputBudget,
}

fn semantic_type_fallback_payload(
    input: SemanticTypeFallbackPayloadInput<'_>,
) -> InferredTypeWritebackJson {
    let compiled_info = analysis::sym::compiled_semantic_info(input.compiled);
    let plan = r2engine::semantic_fallback_type_writeback_plan(
        input.function_name,
        input.arch_name,
        input.ptr_bits,
        input.callconv,
        input.compiled,
        input.function_facts,
        input.apply_artifact_signature_hint,
    );
    let mutation_plan = mutation_plan_from_writeback(&plan, input.budget);
    let mut warnings = plan.diagnostics.warnings;
    if plan.struct_decls.len() > input.budget.max_type_decls {
        warnings.push(format!(
            "type declaration report truncated from {} to {} item(s)",
            plan.struct_decls.len(),
            input.budget.max_type_decls
        ));
    }
    if plan.global_type_links.len() > input.budget.global_max_links {
        warnings.push(format!(
            "global type-link report truncated from {} to {} item(s)",
            plan.global_type_links.len(),
            input.budget.global_max_links
        ));
    }

    InferredTypeWritebackJson {
        function_name: plan.signature.function_name,
        signature: plan.signature.signature,
        ret_type: plan.signature.ret_type,
        params: plan
            .signature
            .params
            .into_iter()
            .map(|param| InferredParamJson {
                name: param.name,
                param_type: param.param_type,
            })
            .collect(),
        callconv: plan.signature.callconv,
        arch: plan.signature.arch,
        confidence: plan.signature.confidence,
        callconv_confidence: plan.signature.callconv_confidence,
        var_type_candidates: Vec::new(),
        var_rename_candidates: Vec::new(),
        struct_decls: plan
            .struct_decls
            .into_iter()
            .take(input.budget.max_type_decls)
            .map(|decl| StructDeclCandidateJson {
                name: decl.name,
                decl: decl.decl,
                confidence: decl.confidence,
                source: decl.source.as_str().to_string(),
                fields: struct_fields_json(&decl.fields),
            })
            .collect(),
        global_type_links: plan
            .global_type_links
            .into_iter()
            .take(input.budget.global_max_links)
            .map(|candidate| GlobalTypeLinkCandidateJson {
                addr: candidate.addr,
                target_type: candidate.target_type,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
            })
            .collect(),
        interproc: InterprocSummaryJson {
            callsite_count: 0,
            iterations: input.interproc.iter.max(1),
            max_iterations: input.interproc.max_iters.max(input.interproc.iter.max(1)),
            converged: input.interproc.converged,
            summary: None,
            summary_json: None,
            scope: merged_interproc_scope_report(
                input.interproc.scope_report,
                input.symbolic_scope,
            ),
        },
        plans: input.function_facts.plans.clone(),
        assumptions: input.function_facts.assumptions.clone(),
        assumption_usage: input.function_facts.assumption_usage.clone(),
        semantics: Some(input.compiled.clone()),
        compiled_semantics: Some(compiled_info),
        mutation_plan,
        diagnostics: TypeWritebackDiagnosticsJson {
            warnings,
            ..TypeWritebackDiagnosticsJson::default()
        },
        phase_timings: Vec::new(),
    }
}

#[cfg(test)]
const SIG_WRITEBACK_CONFIDENCE_MIN: u8 = 70;
#[cfg(test)]
const CC_WRITEBACK_CONFIDENCE_MIN: u8 = 80;

#[cfg(test)]
fn merge_initial_type_evidence(initial_ty: &r2dec::CType, evidence: &mut TypeEvidence) {
    r2types::merge_initial_signature_type_evidence(&ctype_to_type_like(initial_ty), evidence);
}

#[cfg(test)]
fn materialize_signature_ctype(ty: r2dec::CType, ptr_bits: u32) -> r2dec::CType {
    type_like_to_ctype(&r2types::materialize_signature_type_like(
        ctype_to_type_like(&ty),
        ptr_bits,
    ))
}

#[cfg(test)]
fn resolve_evidence_driven_type(
    initial_ty: r2dec::CType,
    var_size_bytes: u32,
    ptr_bits: u32,
    evidence: &TypeEvidence,
) -> r2dec::CType {
    type_like_to_ctype(&r2types::resolve_evidence_driven_signature_type(
        ctype_to_type_like(&initial_ty),
        var_size_bytes,
        ptr_bits,
        evidence,
    ))
}

#[cfg(test)]
fn collect_type_evidence_for_var(
    evidence_ctx: &r2types::SignatureTypeEvidenceContext,
    var: &r2ssa::SSAVar,
    initial_ty: &r2dec::CType,
) -> TypeEvidence {
    r2types::collect_signature_type_evidence_for_var(
        evidence_ctx,
        var,
        &ctype_to_type_like(initial_ty),
    )
}

#[cfg(test)]
fn type_like_to_ctype(ty: &r2types::CTypeLike) -> r2dec::CType {
    match ty {
        r2types::CTypeLike::Void => r2dec::CType::Void,
        r2types::CTypeLike::Bool => r2dec::CType::Bool,
        r2types::CTypeLike::Int { bits, signedness } => match signedness {
            r2types::Signedness::Unsigned => r2dec::CType::UInt(*bits),
            r2types::Signedness::Signed | r2types::Signedness::Unknown => r2dec::CType::Int(*bits),
        },
        r2types::CTypeLike::Float(bits) => r2dec::CType::Float(*bits),
        r2types::CTypeLike::Pointer(inner) => {
            r2dec::CType::Pointer(Box::new(type_like_to_ctype(inner)))
        }
        r2types::CTypeLike::Array(inner, len) => {
            r2dec::CType::Array(Box::new(type_like_to_ctype(inner)), *len)
        }
        r2types::CTypeLike::Struct(name) => r2dec::CType::Struct(name.clone()),
        r2types::CTypeLike::Union(name) => r2dec::CType::Union(name.clone()),
        r2types::CTypeLike::Enum(name) => r2dec::CType::Enum(name.clone()),
        r2types::CTypeLike::Typedef(name) => r2dec::CType::Typedef(name.clone()),
        r2types::CTypeLike::Function | r2types::CTypeLike::Unknown => r2dec::CType::Unknown,
    }
}

fn ctype_to_type_like(ty: &r2dec::CType) -> r2types::CTypeLike {
    match ty {
        r2dec::CType::Void => r2types::CTypeLike::Void,
        r2dec::CType::Bool => r2types::CTypeLike::Bool,
        r2dec::CType::Int(bits) => r2types::CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Signed,
        },
        r2dec::CType::UInt(bits) => r2types::CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Unsigned,
        },
        r2dec::CType::Float(bits) => r2types::CTypeLike::Float(*bits),
        r2dec::CType::Pointer(inner) => {
            r2types::CTypeLike::Pointer(Box::new(ctype_to_type_like(inner)))
        }
        r2dec::CType::Array(inner, len) => {
            r2types::CTypeLike::Array(Box::new(ctype_to_type_like(inner)), *len)
        }
        r2dec::CType::Struct(name) => r2types::CTypeLike::Struct(name.clone()),
        r2dec::CType::Union(name) => r2types::CTypeLike::Union(name.clone()),
        r2dec::CType::Enum(name) => r2types::CTypeLike::Enum(name.clone()),
        r2dec::CType::Typedef(name) => r2types::CTypeLike::Typedef(name.clone()),
        r2dec::CType::Function { .. } | r2dec::CType::Unknown => r2types::CTypeLike::Unknown,
    }
}

#[cfg(test)]
fn fallback_scalar_type(
    var_size_bytes: u32,
    evidence: &TypeEvidence,
    ptr_bits: u32,
) -> r2dec::CType {
    type_like_to_ctype(&r2types::resolve_evidence_driven_signature_type(
        r2types::CTypeLike::Unknown,
        var_size_bytes,
        ptr_bits,
        evidence,
    ))
}

#[cfg(test)]
fn sanitize_inferred_param_type(
    ty: r2dec::CType,
    var_size_bytes: u32,
    ptr_bits: u32,
) -> r2dec::CType {
    type_like_to_ctype(&r2types::resolve_evidence_driven_signature_type(
        ctype_to_type_like(&ty),
        var_size_bytes,
        ptr_bits,
        &TypeEvidence::default(),
    ))
}

#[cfg(test)]
fn infer_callconv_x86_64_from_counts(
    counts: &std::collections::HashMap<String, u32>,
) -> (String, u8) {
    r2types::compute_callconv_inference("x86-64", counts)
}

#[cfg(test)]
fn infer_signature_return_type(
    func: &r2ssa::SSAFunction,
    type_inference: &r2types::TypeInference,
    ptr_bits: u32,
    evidence_ctx: &r2types::SignatureTypeEvidenceContext,
) -> (r2dec::CType, TypeEvidence) {
    let (ty, evidence) =
        r2types::infer_signature_return_type(func, type_inference, ptr_bits, evidence_ctx);
    (type_like_to_ctype(&ty), evidence)
}

#[cfg(test)]
#[allow(dead_code)]
fn collect_version0_input_regs(
    func: &r2ssa::SSAFunction,
) -> std::collections::HashMap<String, u32> {
    r2types::collect_version0_input_regs(func)
}

#[cfg(test)]
fn compute_signature_confidence(
    params: &[InferredParam],
    ret_type: &r2dec::CType,
    ret_evidence: &TypeEvidence,
) -> u8 {
    let canonical_params = params
        .iter()
        .map(|param| r2types::SignatureParamCandidate {
            name: param.name.clone(),
            ty: ctype_to_type_like(&param.ty),
            arg_index: param.arg_index,
            size_bytes: param.size_bytes,
            evidence: param.evidence.clone(),
        })
        .collect::<Vec<_>>();
    r2types::compute_signature_confidence(
        &canonical_params,
        &ctype_to_type_like(ret_type),
        ret_evidence,
    )
}

#[cfg(test)]
fn compute_callconv_inference(
    arch_name: &str,
    input_counts: &std::collections::HashMap<String, u32>,
) -> (String, u8) {
    r2types::compute_callconv_inference(arch_name, input_counts)
}

#[cfg(test)]
fn is_informative_type(ty: &r2dec::CType) -> bool {
    !matches!(ty, r2dec::CType::Void | r2dec::CType::Unknown)
}

#[cfg(test)]
fn explicit_signature_context_strength(sig: &r2types::FunctionSignatureSpec) -> u8 {
    let typed_params = sig
        .params
        .iter()
        .filter(|param| {
            param
                .ty
                .as_ref()
                .map(type_like_to_ctype)
                .as_ref()
                .is_some_and(is_informative_type)
        })
        .count() as u8;
    let has_ret = sig
        .ret_type
        .as_ref()
        .map(type_like_to_ctype)
        .as_ref()
        .is_some_and(is_informative_type);
    let mut confidence = 76u8.saturating_add(typed_params.saturating_mul(4)).min(96);
    if has_ret {
        confidence = confidence.saturating_add(6).min(96);
    }
    confidence
}

#[cfg(test)]
fn normalize_inferred_param_name(
    raw_name: &str,
    fallback_idx: usize,
    used: &mut std::collections::HashSet<String>,
) -> String {
    let fallback = format!("arg{}", fallback_idx);
    let clean = sanitize_c_identifier(raw_name).unwrap_or_else(|| fallback.clone());
    let clean = if clean.is_empty() { fallback } else { clean };
    uniquify_name(clean, used)
}

#[cfg(test)]
fn format_afs_signature(
    function_name: &str,
    ret_type: &str,
    params: &[InferredParamJson],
) -> String {
    let params_str = if params.is_empty() {
        "void".to_string()
    } else {
        params
            .iter()
            .map(|p| format!("{} {}", p.param_type, p.name))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!("{ret_type} {function_name} ({params_str})")
}

fn cstr_or_default(ptr: *const c_char, default: &str) -> String {
    helpers::cstr_or_default(ptr, default)
}

#[cfg(test)]
fn is_opaque_placeholder_type_name(ty: &str) -> bool {
    let lower = ty.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return false;
    }
    let stripped = lower
        .strip_prefix("struct ")
        .unwrap_or(&lower)
        .trim_start()
        .trim_end_matches('*')
        .trim_end();
    stripped == "anon"
        || stripped.starts_with("anon_")
        || stripped.starts_with("type_0x")
        || lower.contains(" type_0x")
}

#[cfg(test)]
fn is_unmaterialized_aggregate_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower.is_empty() || lower == "anon" || lower.starts_with("anon_")
}

#[cfg(test)]
fn is_generic_type_string(ty: &str) -> bool {
    let normalized = normalize_external_type_name(ty);
    let lower = normalized.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return true;
    }
    if lower.starts_with("byte[") || lower.starts_with("int") || lower.starts_with("uint") {
        return true;
    }
    if is_opaque_placeholder_type_name(&lower) {
        return true;
    }
    matches!(
        lower.as_str(),
        "void *"
            | "void*"
            | "char *"
            | "char*"
            | "long"
            | "unsigned long"
            | "unsigned"
            | "int"
            | "unknown"
    )
}

#[cfg(test)]
fn normalize_external_type_name(ty: &str) -> String {
    let normalized = r2types::normalize_external_type_name(ty);
    if normalized.is_empty() || is_opaque_placeholder_type_name(&normalized) {
        "void *".to_string()
    } else {
        normalized
    }
}

#[cfg(test)]
fn estimate_parsed_c_type_size_bytes(ty: &r2dec::CType, ptr_bits: u32) -> Option<u64> {
    match ty {
        r2dec::CType::Void => Some(0),
        r2dec::CType::Bool => Some(1),
        r2dec::CType::Int(bits) | r2dec::CType::UInt(bits) | r2dec::CType::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        r2dec::CType::Pointer(_) | r2dec::CType::Function { .. } => {
            Some((ptr_bits / 8).max(1) as u64)
        }
        r2dec::CType::Array(inner, Some(count)) => {
            estimate_parsed_c_type_size_bytes(inner, ptr_bits)
                .map(|inner_size| inner_size.saturating_mul(*count as u64))
        }
        r2dec::CType::Array(inner, None) => estimate_parsed_c_type_size_bytes(inner, ptr_bits),
        r2dec::CType::Enum(_) => Some(4),
        r2dec::CType::Struct(_)
        | r2dec::CType::Union(_)
        | r2dec::CType::Typedef(_)
        | r2dec::CType::Unknown => None,
    }
}

#[cfg(test)]
fn estimate_c_type_size_bytes(ty: &str, ptr_bits: u32) -> u64 {
    if let Some(parsed) = parse_external_type(ty, ptr_bits)
        && let Some(size) = estimate_parsed_c_type_size_bytes(&parsed, ptr_bits)
        && size > 0
    {
        return size;
    }

    let lower = normalize_external_type_name(ty).trim().to_ascii_lowercase();
    if lower.contains('*') {
        return (ptr_bits / 8).max(1) as u64;
    }
    if lower == "double" || lower == "long double" {
        return 8;
    }
    1
}

#[cfg(test)]
fn build_struct_decl(
    name: &str,
    fields: &[StructFieldCandidateJson],
    ptr_bits: u32,
) -> Option<String> {
    if fields.is_empty() {
        return None;
    }
    let clean_name = sanitize_c_identifier(name)?;
    let mut lines = vec![format!("typedef struct {} {{", clean_name)];
    let mut cursor = 0u64;
    for field in fields {
        if field.offset > cursor {
            let gap = field.offset - cursor;
            lines.push(format!("  uint8_t _pad_{cursor:x}[{gap}];"));
            cursor = field.offset;
        }
        let field_name = sanitize_c_identifier(&field.name)
            .unwrap_or_else(|| format!("field_{:x}", field.offset));
        lines.push(format!("  {} {};", field.field_type, field_name));
        cursor = cursor.saturating_add(estimate_c_type_size_bytes(&field.field_type, ptr_bits));
    }
    lines.push(format!("}} {};", clean_name));
    Some(lines.join("\n"))
}

#[cfg(test)]
fn parse_existing_var_types(json_str: &str) -> std::collections::HashMap<String, String> {
    let mut out = std::collections::HashMap::new();
    let Ok(value) = serde_json::from_str::<serde_json::Value>(json_str) else {
        return out;
    };
    let Some(obj) = value.as_object() else {
        return out;
    };
    for bucket in ["reg", "bp", "sp"] {
        let Some(entries) = obj.get(bucket).and_then(|v| v.as_array()) else {
            continue;
        };
        for entry in entries {
            let Some(entry_obj) = entry.as_object() else {
                continue;
            };
            let Some(name) = entry_obj.get("name").and_then(|v| v.as_str()) else {
                continue;
            };
            let Some(ty) = entry_obj
                .get("type")
                .or_else(|| entry_obj.get("vartype"))
                .and_then(|v| v.as_str())
            else {
                continue;
            };
            out.entry(name.to_string())
                .or_insert_with(|| normalize_external_type_name(ty));
        }
    }
    out
}

#[cfg(test)]
fn collect_pointer_arg_slot_map(
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
) -> std::collections::HashMap<String, usize> {
    let (arg_regs, _, _) = recover_vars_arch_profile(arch);
    let arch_name = arch
        .map(|a| a.name.to_ascii_lowercase())
        .unwrap_or_default();
    let is_arm64 = arch_name.contains("aarch64") || arch_name.contains("arm64");
    let is_x86_64 = arch_name.contains("x86-64")
        || arch_name.contains("x86_64")
        || arch_name.contains("amd64")
        || arch_name.contains("x64");
    let is_riscv64 = arch_name.contains("riscv64") || arch_name.contains("rv64");

    let mut out = std::collections::HashMap::new();
    for (idx, (canonical, aliases)) in arg_regs.iter().enumerate() {
        let include_alias = |alias: &str| -> bool {
            if ptr_bits <= 32 {
                return true;
            }
            let alias = alias.to_ascii_lowercase();
            if is_arm64 {
                return alias.starts_with('x');
            }
            if is_x86_64 {
                return alias.starts_with('r');
            }
            if is_riscv64 {
                return alias.starts_with('x') || alias.starts_with('a');
            }
            alias == (*canonical).to_ascii_lowercase()
        };

        if include_alias(canonical) {
            out.insert((*canonical).to_string(), idx);
        }
        for alias in *aliases {
            if include_alias(alias) {
                out.insert((*alias).to_string(), idx);
            }
        }
    }
    out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(test)]
struct ArgAddrExpr {
    slot: usize,
    offset: i64,
    confidence: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(test)]
struct GlobalAddrExpr {
    base: u64,
    offset: i64,
    confidence: u8,
}

#[derive(Clone, Debug, Default)]
#[cfg(test)]
struct StructFieldEvidence {
    reads: u32,
    writes: u32,
    widths: std::collections::BTreeMap<u32, u32>,
    type_votes: std::collections::BTreeMap<String, u32>,
}

#[cfg(test)]
type SlotTypeOverrides = std::collections::HashMap<usize, String>;
#[cfg(test)]
type SlotFieldProfiles = std::collections::HashMap<usize, std::collections::BTreeMap<u64, String>>;
#[cfg(test)]
type SlotFieldEvidenceMap =
    std::collections::HashMap<usize, std::collections::BTreeMap<u64, StructFieldEvidence>>;
#[cfg(test)]
type StructInferenceArtifacts = (
    Vec<StructDeclCandidateJson>,
    SlotTypeOverrides,
    SlotFieldProfiles,
);

#[cfg(test)]
fn build_struct_inference_artifacts_from_field_evidence(
    slot_field_evidence: SlotFieldEvidenceMap,
    ptr_bits: u32,
    diagnostics: &mut TypeWritebackDiagnosticsJson,
) -> StructInferenceArtifacts {
    use std::collections::BTreeMap;
    use std::hash::{Hash, Hasher};

    let mut struct_decls = Vec::new();
    let mut slot_type_overrides = std::collections::HashMap::new();
    let mut slot_fields_for_links: HashMap<usize, BTreeMap<u64, String>> = HashMap::new();
    let mut slots: Vec<usize> = slot_field_evidence.keys().copied().collect();
    slots.sort_unstable();

    for slot in slots {
        let Some(fields_map) = slot_field_evidence.get(&slot) else {
            continue;
        };
        if fields_map.is_empty() {
            continue;
        }
        let mut shape = String::new();
        let mut fields = Vec::new();
        let mut normalized_fields: BTreeMap<u64, String> = BTreeMap::new();
        let mut confidence_acc: u32 = 0;
        for (offset, evidence) in fields_map {
            let total_votes: u32 = evidence.type_votes.values().copied().sum();
            let Some((field_type, field_votes)) = evidence
                .type_votes
                .iter()
                .max_by_key(|(_, count)| **count)
                .map(|(ty, count)| (ty.clone(), *count))
            else {
                continue;
            };
            if evidence.type_votes.len() > 1 {
                diagnostics.conflicts.push(format!(
                    "slot {slot} field +0x{offset:x} conflicting type votes {:?}",
                    evidence.type_votes
                ));
            }
            let strength = ((field_votes.saturating_mul(100)) / total_votes.max(1)) as u8;
            let rw_bonus = if evidence.reads > 0 && evidence.writes > 0 {
                10
            } else {
                0
            };
            let field_conf = 70u8.saturating_add(strength / 3).saturating_add(rw_bonus);
            confidence_acc = confidence_acc.saturating_add(field_conf as u32);
            shape.push_str(&format!("{offset:x}:{field_type};"));
            normalized_fields.insert(*offset, field_type.clone());
            fields.push(StructFieldCandidateJson {
                name: format!("f_{offset:x}"),
                offset: *offset,
                field_type,
                confidence: field_conf,
            });
        }
        if fields.is_empty() {
            continue;
        }
        let avg_conf = (confidence_acc / fields.len() as u32).clamp(1, 100) as u8;
        let allow_single_field = fields.len() == 1 && avg_conf >= 94;
        if fields.len() < 2 && !allow_single_field {
            continue;
        }
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hasher);
        let struct_name = format!("sla_struct_{:016x}", hasher.finish());
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        struct_decls.push(StructDeclCandidateJson {
            name: struct_name.clone(),
            decl,
            confidence: avg_conf.max(84),
            source: "local_inferred".to_string(),
            fields,
        });
        slot_fields_for_links.insert(slot, normalized_fields);
        slot_type_overrides.insert(slot, format!("struct {} *", struct_name));
    }

    (struct_decls, slot_type_overrides, slot_fields_for_links)
}

#[cfg(test)]
fn infer_structs_from_semantic_accesses(
    ssa_func: &r2ssa::SSAFunction,
    cfg: &r2dec::DecompilerConfig,
    ptr_bits: u32,
    diagnostics: &mut TypeWritebackDiagnosticsJson,
) -> StructInferenceArtifacts {
    let mut slot_field_evidence: SlotFieldEvidenceMap = HashMap::new();
    for access in r2dec::infer_local_struct_field_accesses(ssa_func, cfg) {
        let entry = slot_field_evidence
            .entry(access.arg_index)
            .or_default()
            .entry(access.field_offset)
            .or_default();
        if access.is_write {
            entry.writes = entry.writes.saturating_add(1);
        } else {
            entry.reads = entry.reads.saturating_add(1);
        }
        *entry.widths.entry(access.access_size).or_insert(0) += 1;
        *entry
            .type_votes
            .entry(size_to_type(access.access_size))
            .or_insert(0) += 1;
    }
    build_struct_inference_artifacts_from_field_evidence(slot_field_evidence, ptr_bits, diagnostics)
}

#[cfg(test)]
#[allow(dead_code)]
fn merge_struct_inference_artifacts(
    mut base: StructInferenceArtifacts,
    supplement: StructInferenceArtifacts,
) -> StructInferenceArtifacts {
    let (struct_decls, slot_type_overrides, slot_field_profiles) = &mut base;
    let (supp_structs, supp_types, supp_profiles) = supplement;

    let mut seen_names = struct_decls
        .iter()
        .map(|decl| decl.name.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    for decl in supp_structs {
        if seen_names.insert(decl.name.to_ascii_lowercase()) {
            struct_decls.push(decl);
        }
    }
    for (slot, ty) in supp_types {
        slot_type_overrides.insert(slot, ty);
    }
    for (slot, profile) in supp_profiles {
        slot_field_profiles.insert(slot, profile);
    }

    base
}

#[cfg(test)]
fn parse_ssa_const_offset(name: &str, ptr_bits: u32) -> Option<i64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);

    let raw = if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).ok()?
    } else if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        dec.parse::<u64>().ok()?
    } else {
        u64::from_str_radix(val_str, 16).ok()?
    };

    Some(signed_offset_from_const(raw, ptr_bits))
}

#[cfg(test)]
fn signed_offset_from_const(raw: u64, ptr_bits: u32) -> i64 {
    let bits = ptr_bits.clamp(8, 64);
    if bits == 64 {
        return raw as i64;
    }
    let mask = (1u64 << bits) - 1;
    let sign = 1u64 << (bits - 1);
    let v = raw & mask;
    if (v & sign) != 0 {
        (v | (!mask)) as i64
    } else {
        v as i64
    }
}

#[cfg(test)]
fn infer_structs_from_ssa(
    ssa_blocks: &[r2ssa::SSABlock],
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
    diagnostics: &mut TypeWritebackDiagnosticsJson,
) -> StructInferenceArtifacts {
    use std::collections::HashMap;

    let pointer_arg_slot_map = collect_pointer_arg_slot_map(arch, ptr_bits);
    let (_, _, cfg) = r2dec::DecompilerConfig::for_arch(arch);
    let sp_name = cfg.sp_name.to_ascii_lowercase();
    let fp_name = cfg.fp_name.to_ascii_lowercase();
    let mut addr_exprs: HashMap<String, ArgAddrExpr> = HashMap::new();
    let mut stack_addr_offsets: HashMap<String, i64> = HashMap::new();
    let mut stack_slot_values: HashMap<(u64, i64), ArgAddrExpr> = HashMap::new();
    let mut slot_field_evidence: SlotFieldEvidenceMap = HashMap::new();
    let offset_bound = 0x4000i64;
    let block_ops: HashMap<u64, HashMap<String, r2ssa::SSAOp>> = ssa_blocks
        .iter()
        .map(|block| {
            let ops = block
                .ops
                .iter()
                .filter_map(|op| {
                    op.dst()
                        .map(|dst| (ssa_var_block_key(block.addr, dst), op.clone()))
                })
                .collect::<HashMap<_, _>>();
            (block.addr, ops)
        })
        .collect();

    fn is_scaled_index_like(
        block_addr: u64,
        var: &r2ssa::SSAVar,
        ops_by_block: &HashMap<u64, HashMap<String, r2ssa::SSAOp>>,
        addr_exprs: &HashMap<String, ArgAddrExpr>,
        depth: u32,
    ) -> bool {
        if depth > 8 || var.is_const() {
            return false;
        }
        let key = ssa_var_block_key(block_addr, var);
        if addr_exprs.contains_key(&key) {
            return false;
        }
        let Some(op) = ops_by_block.get(&block_addr).and_then(|ops| ops.get(&key)) else {
            return true;
        };
        match op {
            r2ssa::SSAOp::Copy { src, .. }
            | r2ssa::SSAOp::Cast { src, .. }
            | r2ssa::SSAOp::New { src, .. }
            | r2ssa::SSAOp::IntZExt { src, .. }
            | r2ssa::SSAOp::IntSExt { src, .. }
            | r2ssa::SSAOp::Trunc { src, .. }
            | r2ssa::SSAOp::Subpiece { src, .. } => {
                is_scaled_index_like(block_addr, src, ops_by_block, addr_exprs, depth + 1)
            }
            r2ssa::SSAOp::IntMult { a, b, .. } => {
                (parse_ssa_const_offset(&a.name, 64).is_some()
                    && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1))
                    || (parse_ssa_const_offset(&b.name, 64).is_some()
                        && is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1))
            }
            r2ssa::SSAOp::IntLeft { a, b, .. } => {
                parse_ssa_const_offset(&b.name, 64).is_some()
                    && is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1)
            }
            r2ssa::SSAOp::IntSub { a, b, .. } => {
                parse_ssa_const_offset(&a.name, 64) == Some(0)
                    && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1)
            }
            r2ssa::SSAOp::Load { .. } | r2ssa::SSAOp::Phi { .. } => true,
            _ => false,
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            // Seed direct arg pointer provenance.
            op.for_each_source(&mut |src: &r2ssa::SSAVar| {
                if src.version != 0 {
                    return;
                }
                let key = src.name.to_ascii_lowercase();
                if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                    addr_exprs
                        .entry(ssa_var_block_key(block.addr, src))
                        .or_insert(ArgAddrExpr {
                            slot,
                            offset: 0,
                            confidence: 92,
                        });
                }
            });
        }
    }

    // Bounded propagation over pointer expression transforms.
    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                let addr_of = |var: &r2ssa::SSAVar, map: &HashMap<String, ArgAddrExpr>| {
                    if var.version == 0 {
                        let key = var.name.to_ascii_lowercase();
                        if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                            return Some(ArgAddrExpr {
                                slot,
                                offset: 0,
                                confidence: 92,
                            });
                        }
                    }
                    map.get(&ssa_var_block_key(block.addr, var)).copied()
                };
                let stack_slot_of =
                    |var: &r2ssa::SSAVar, stack_map: &HashMap<String, i64>| -> Option<i64> {
                        let key = ssa_var_block_key(block.addr, var);
                        stack_map.get(&key).copied()
                    };
                let set_expr =
                    |dst: &r2ssa::SSAVar,
                     expr: ArgAddrExpr,
                     map: &mut HashMap<String, ArgAddrExpr>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev.confidence >= expr.confidence => false,
                            _ => {
                                map.insert(key, expr);
                                true
                            }
                        }
                    };
                let set_stack_slot =
                    |dst: &r2ssa::SSAVar, offset: i64, map: &mut HashMap<String, i64>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev == offset => false,
                            _ => {
                                map.insert(key, offset);
                                true
                            }
                        }
                    };
                match op {
                    r2ssa::SSAOp::Copy { dst, src }
                    | r2ssa::SSAOp::Cast { dst, src }
                    | r2ssa::SSAOp::New { dst, src }
                    | r2ssa::SSAOp::IntZExt { dst, src }
                    | r2ssa::SSAOp::IntSExt { dst, src } => {
                        if let Some(mut expr) = addr_of(src, &addr_exprs) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                        if let Some(offset) = stack_slot_of(src, &stack_addr_offsets) {
                            changed |= set_stack_slot(dst, offset, &mut stack_addr_offsets);
                        }
                    }
                    r2ssa::SSAOp::Phi { dst, sources } => {
                        let mut selected = None;
                        let mut selected_slot = None;
                        for src in sources {
                            let Some(expr) = addr_of(src, &addr_exprs) else {
                                selected = None;
                                break;
                            };
                            selected = match selected {
                                None => Some(expr),
                                Some(prev)
                                    if prev.slot == expr.slot && prev.offset == expr.offset =>
                                {
                                    Some(ArgAddrExpr {
                                        slot: prev.slot,
                                        offset: prev.offset,
                                        confidence: prev.confidence.max(expr.confidence),
                                    })
                                }
                                _ => None,
                            };
                            let Some(slot) = stack_slot_of(src, &stack_addr_offsets) else {
                                selected_slot = None;
                                break;
                            };
                            selected_slot = match selected_slot {
                                None => Some(slot),
                                Some(prev) if prev == slot => Some(prev),
                                _ => None,
                            };
                            if selected.is_none() {
                                break;
                            }
                        }
                        if let Some(mut expr) = selected {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                        if let Some(slot) = selected_slot {
                            changed |= set_stack_slot(dst, slot, &mut stack_addr_offsets);
                        }
                    }
                    r2ssa::SSAOp::IntAdd { dst, a, b } => {
                        if let Some(off) = parse_ssa_const_offset(&b.name, ptr_bits) {
                            let a_lower = a.name.to_ascii_lowercase();
                            if a_lower == sp_name || a_lower == fp_name {
                                changed |= set_stack_slot(dst, off, &mut stack_addr_offsets);
                            }
                        }
                        if let Some(off) = parse_ssa_const_offset(&a.name, ptr_bits) {
                            let b_lower = b.name.to_ascii_lowercase();
                            if b_lower == sp_name || b_lower == fp_name {
                                changed |= set_stack_slot(dst, off, &mut stack_addr_offsets);
                            }
                        }
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                        {
                            let off = base.offset.saturating_add(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    ArgAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(a, &addr_exprs)
                            && is_scaled_index_like(block.addr, b, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                ArgAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&a.name, ptr_bits)
                        {
                            let off = base.offset.saturating_add(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    ArgAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && is_scaled_index_like(block.addr, a, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                ArgAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        }
                    }
                    r2ssa::SSAOp::IntSub { dst, a, b } => {
                        if let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits) {
                            let a_lower = a.name.to_ascii_lowercase();
                            if a_lower == sp_name || a_lower == fp_name {
                                changed |= set_stack_slot(
                                    dst,
                                    delta.saturating_neg(),
                                    &mut stack_addr_offsets,
                                );
                            }
                        }
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                        {
                            let off = base.offset.saturating_sub(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    ArgAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(a, &addr_exprs)
                            && is_scaled_index_like(block.addr, b, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                ArgAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        }
                    }
                    r2ssa::SSAOp::Store { addr, val, .. } => {
                        if let Some(offset) = stack_slot_of(addr, &stack_addr_offsets)
                            && let Some(mut expr) = addr_of(val, &addr_exprs)
                        {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            let key = (block.addr, offset);
                            match stack_slot_values.get(&key).copied() {
                                Some(prev) if prev.confidence >= expr.confidence => {}
                                _ => {
                                    stack_slot_values.insert(key, expr);
                                    changed = true;
                                }
                            }
                        }
                    }
                    r2ssa::SSAOp::Load { dst, addr, .. } => {
                        if let Some(offset) = stack_slot_of(addr, &stack_addr_offsets)
                            && let Some(mut expr) =
                                stack_slot_values.get(&(block.addr, offset)).copied()
                        {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            let resolve_addr = |addr: &r2ssa::SSAVar| -> Option<ArgAddrExpr> {
                if addr.version == 0 {
                    let key = addr.name.to_ascii_lowercase();
                    if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                        return Some(ArgAddrExpr {
                            slot,
                            offset: 0,
                            confidence: 92,
                        });
                    }
                }
                addr_exprs
                    .get(&ssa_var_block_key(block.addr, addr))
                    .copied()
            };
            match op {
                r2ssa::SSAOp::Load { dst, addr, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = slot_field_evidence
                            .entry(expr.slot)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.reads = entry.reads.saturating_add(1);
                        *entry.widths.entry(dst.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(dst.size)).or_insert(0) += 1;
                    }
                }
                r2ssa::SSAOp::Store { addr, val, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = slot_field_evidence
                            .entry(expr.slot)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.writes = entry.writes.saturating_add(1);
                        *entry.widths.entry(val.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(val.size)).or_insert(0) += 1;
                    }
                }
                _ => {}
            }
        }
    }

    build_struct_inference_artifacts_from_field_evidence(slot_field_evidence, ptr_bits, diagnostics)
}

#[cfg(test)]
fn collect_external_struct_candidates_from_db(
    db: &r2types::ExternalTypeDb,
    ptr_bits: u32,
) -> Vec<StructDeclCandidateJson> {
    let mut keys: Vec<String> = db.structs.keys().cloned().collect();
    keys.sort();

    let mut out = Vec::new();
    for key in keys {
        let Some(st) = db.structs.get(&key) else {
            continue;
        };
        if is_opaque_placeholder_type_name(&st.name) || st.fields.is_empty() {
            continue;
        }
        let mut fields = Vec::new();
        for (offset, field) in &st.fields {
            let raw_ty = field.ty.clone().unwrap_or_else(|| "uint8_t".to_string());
            fields.push(StructFieldCandidateJson {
                name: field.name.clone(),
                offset: *offset,
                field_type: normalize_external_type_name(&raw_ty),
                confidence: 95,
            });
        }
        let Some(decl) = build_struct_decl(&st.name, &fields, ptr_bits) else {
            continue;
        };
        out.push(StructDeclCandidateJson {
            name: st.name.clone(),
            decl,
            confidence: 95,
            source: "external_type_db".to_string(),
            fields,
        });
    }
    out
}

#[cfg(test)]
fn is_generic_signature_type(ty: Option<&r2types::CTypeLike>) -> bool {
    match ty {
        None => true,
        Some(r2types::CTypeLike::Unknown | r2types::CTypeLike::Void) => true,
        Some(r2types::CTypeLike::Pointer(inner)) => {
            matches!(
                inner.as_ref(),
                r2types::CTypeLike::Unknown | r2types::CTypeLike::Void
            )
        }
        _ => false,
    }
}

#[cfg(test)]
fn merge_slot_type_overrides_into_signature(
    mut signature: Option<r2types::FunctionSignatureSpec>,
    slot_type_overrides: &SlotTypeOverrides,
    ptr_bits: u32,
) -> Option<r2types::FunctionSignatureSpec> {
    if slot_type_overrides.is_empty() {
        return signature;
    }

    let max_slot = slot_type_overrides.keys().copied().max()?;
    let sig = signature.get_or_insert_with(Default::default);
    while sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(r2types::FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, raw_ty) in slot_type_overrides {
        let Some(parsed) = r2types::parse_type_like_spec(raw_ty, ptr_bits) else {
            continue;
        };
        let param = &mut sig.params[*slot];
        if is_generic_signature_type(param.ty.as_ref()) {
            param.ty = Some(parsed);
        }
    }

    signature
}

#[cfg(test)]
fn merge_local_structs_into_type_db(
    db: &mut r2types::ExternalTypeDb,
    struct_decls: &[StructDeclCandidateJson],
) {
    for decl in struct_decls {
        let key = decl.name.to_ascii_lowercase();
        db.structs.entry(key).or_insert_with(|| {
            let mut fields = std::collections::BTreeMap::new();
            for field in &decl.fields {
                fields.insert(
                    field.offset,
                    r2types::ExternalField {
                        name: field.name.clone(),
                        offset: field.offset,
                        ty: Some(field.field_type.clone()),
                    },
                );
            }
            r2types::ExternalStruct {
                name: decl.name.clone(),
                fields,
            }
        });
    }
}

#[cfg(test)]
pub(crate) fn enrich_decompiler_type_context(
    ssa_blocks: &[r2ssa::SSABlock],
    arch: Option<&ArchSpec>,
    ptr_bits: u32,
    signature: Option<r2types::FunctionSignatureSpec>,
    mut type_db: r2types::ExternalTypeDb,
) -> (
    Option<r2types::FunctionSignatureSpec>,
    r2types::ExternalTypeDb,
) {
    let mut diagnostics = TypeWritebackDiagnosticsJson::default();
    let (mut struct_decls, mut slot_type_overrides, slot_field_profiles) =
        infer_structs_from_ssa(ssa_blocks, arch, ptr_bits, &mut diagnostics);

    if !type_db.structs.is_empty() {
        let external_structs = collect_external_struct_candidates_from_db(&type_db, ptr_bits);
        align_local_structs_with_external(
            &mut struct_decls,
            &mut slot_type_overrides,
            &slot_field_profiles,
            &external_structs,
        );
    }

    prefer_stronger_local_struct_overrides(
        &struct_decls,
        &mut slot_type_overrides,
        &slot_field_profiles,
    );

    merge_local_structs_into_type_db(&mut type_db, &struct_decls);
    let signature =
        merge_slot_type_overrides_into_signature(signature, &slot_type_overrides, ptr_bits);
    (signature, type_db)
}

#[cfg(test)]
fn struct_fields_signature(fields: &[StructFieldCandidateJson]) -> Vec<(u64, String)> {
    let mut out: Vec<(u64, String)> = fields
        .iter()
        .map(|f| (f.offset, f.field_type.to_ascii_lowercase()))
        .collect();
    out.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    out
}

#[cfg(test)]
fn parse_struct_ptr_type_name(ty: &str) -> Option<String> {
    ty.trim()
        .strip_prefix("struct ")
        .and_then(|rest| rest.strip_suffix(" *"))
        .map(str::to_string)
}

#[cfg(test)]
fn local_struct_profile_score(
    decl: &StructDeclCandidateJson,
    profile: &std::collections::BTreeMap<u64, String>,
) -> Option<(usize, usize, usize, i32)> {
    if decl.source != "local_inferred" || profile.is_empty() {
        return None;
    }

    let field_map = decl
        .fields
        .iter()
        .map(|field| (field.offset, field.field_type.to_ascii_lowercase()))
        .collect::<std::collections::BTreeMap<_, _>>();

    let mut offset_matches = 0usize;
    let mut typed_matches = 0usize;
    for (offset, ty) in profile {
        let Some(field_ty) = field_map.get(offset) else {
            continue;
        };
        offset_matches += 1;
        if field_ty == &ty.to_ascii_lowercase() {
            typed_matches += 1;
        }
    }

    (offset_matches > 0).then_some((
        offset_matches,
        typed_matches,
        decl.fields.len(),
        i32::from(decl.confidence),
    ))
}

#[cfg(test)]
pub(crate) fn prefer_stronger_local_struct_overrides(
    struct_decls: &[StructDeclCandidateJson],
    slot_type_overrides: &mut std::collections::HashMap<usize, String>,
    slot_field_profiles: &std::collections::HashMap<usize, std::collections::BTreeMap<u64, String>>,
) {
    for (slot, ty) in slot_type_overrides.iter_mut() {
        let Some(profile) = slot_field_profiles.get(slot) else {
            continue;
        };
        if profile.is_empty() {
            continue;
        }

        let current_name = parse_struct_ptr_type_name(ty);
        let current_decl = current_name.as_ref().and_then(|name| {
            struct_decls
                .iter()
                .find(|decl| decl.name.eq_ignore_ascii_case(name))
        });
        if current_decl.is_some_and(|decl| decl.source == "external_type_db") {
            continue;
        }

        let current_score = current_decl.and_then(|decl| local_struct_profile_score(decl, profile));
        let best_local = struct_decls
            .iter()
            .filter_map(|decl| {
                local_struct_profile_score(decl, profile).map(|score| (score, decl.name.clone()))
            })
            .max_by(|(left_score, left_name), (right_score, right_name)| {
                left_score
                    .cmp(right_score)
                    .then_with(|| left_name.cmp(right_name))
            });

        let Some((best_score, best_name)) = best_local else {
            continue;
        };
        if current_score.is_none_or(|score| best_score > score) {
            *ty = format!("struct {} *", best_name);
        }
    }
}

#[cfg(test)]
fn structurally_compatible(local_fields: &[(u64, String)], ext_fields: &[(u64, String)]) -> bool {
    if local_fields.is_empty() || ext_fields.is_empty() {
        return false;
    }
    let mut matches = 0usize;
    for (off, ty) in local_fields {
        if ext_fields
            .iter()
            .any(|(eoff, ety)| eoff == off && ety == ty)
        {
            matches += 1;
        }
    }
    matches >= local_fields.len().min(2)
}

#[cfg(test)]
fn align_local_structs_with_external(
    struct_decls: &mut [StructDeclCandidateJson],
    slot_type_overrides: &mut std::collections::HashMap<usize, String>,
    slot_field_profiles: &std::collections::HashMap<usize, std::collections::BTreeMap<u64, String>>,
    external_structs: &[StructDeclCandidateJson],
) {
    let mut local_to_external: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    for local in struct_decls.iter_mut() {
        if local.source != "local_inferred" {
            continue;
        }
        let local_sig = struct_fields_signature(&local.fields);
        for ext in external_structs {
            let ext_sig = struct_fields_signature(&ext.fields);
            if structurally_compatible(&local_sig, &ext_sig) {
                local_to_external.insert(local.name.clone(), ext.name.clone());
                local.confidence = local.confidence.max(92);
                break;
            }
        }
    }

    for (slot, ty) in slot_type_overrides.iter_mut() {
        let Some(profile) = slot_field_profiles.get(slot) else {
            continue;
        };
        if profile.is_empty() {
            continue;
        }
        let replacement = external_structs.iter().find_map(|ext| {
            let ext_sig = struct_fields_signature(&ext.fields);
            let local_sig: Vec<(u64, String)> = profile
                .iter()
                .map(|(off, ty)| (*off, ty.to_ascii_lowercase()))
                .collect();
            if structurally_compatible(&local_sig, &ext_sig) {
                Some(ext.name.clone())
            } else {
                None
            }
        });
        if let Some(ext_name) = replacement {
            *ty = format!("struct {} *", ext_name);
            continue;
        }
        if let Some(local_name) = ty
            .strip_prefix("struct ")
            .and_then(|s| s.strip_suffix(" *"))
            .map(str::to_string)
            && let Some(ext_name) = local_to_external.get(&local_name)
        {
            *ty = format!("struct {} *", ext_name);
        }
    }
}

#[cfg(test)]
fn infer_global_field_profiles(
    ssa_blocks: &[r2ssa::SSABlock],
    ptr_bits: u32,
) -> std::collections::BTreeMap<u64, std::collections::BTreeMap<u64, StructFieldEvidence>> {
    use std::collections::{BTreeMap, HashMap};

    let mut addr_exprs: HashMap<String, GlobalAddrExpr> = HashMap::new();
    let mut field_evidence: BTreeMap<u64, BTreeMap<u64, StructFieldEvidence>> = BTreeMap::new();
    let offset_bound = 0x4000i64;

    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                let addr_of = |var: &r2ssa::SSAVar, map: &HashMap<String, GlobalAddrExpr>| {
                    parse_const_value(&var.name)
                        .filter(|addr| *addr >= 0x10000)
                        .map(|base| GlobalAddrExpr {
                            base,
                            offset: 0,
                            confidence: 92,
                        })
                        .or_else(|| map.get(&ssa_var_block_key(block.addr, var)).copied())
                };
                let set_expr =
                    |dst: &r2ssa::SSAVar,
                     expr: GlobalAddrExpr,
                     map: &mut HashMap<String, GlobalAddrExpr>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev.confidence >= expr.confidence => false,
                            _ => {
                                map.insert(key, expr);
                                true
                            }
                        }
                    };
                match op {
                    r2ssa::SSAOp::Copy { dst, src }
                    | r2ssa::SSAOp::Cast { dst, src }
                    | r2ssa::SSAOp::New { dst, src }
                    | r2ssa::SSAOp::IntZExt { dst, src }
                    | r2ssa::SSAOp::IntSExt { dst, src } => {
                        if let Some(mut expr) = addr_of(src, &addr_exprs) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    r2ssa::SSAOp::Phi { dst, sources } => {
                        let mut selected = None;
                        for src in sources {
                            let Some(expr) = addr_of(src, &addr_exprs) else {
                                continue;
                            };
                            selected = match selected {
                                None => Some(expr),
                                Some(prev)
                                    if prev.base == expr.base && prev.offset == expr.offset =>
                                {
                                    Some(GlobalAddrExpr {
                                        base: prev.base,
                                        offset: prev.offset,
                                        confidence: prev.confidence.max(expr.confidence),
                                    })
                                }
                                _ => None,
                            };
                            if selected.is_none() {
                                break;
                            }
                        }
                        if let Some(mut expr) = selected {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    r2ssa::SSAOp::IntAdd { dst, a, b } => {
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(raw) = parse_const_value(&b.name)
                        {
                            let off = base
                                .offset
                                .saturating_add(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && let Some(raw) = parse_const_value(&a.name)
                        {
                            let off = base
                                .offset
                                .saturating_add(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    r2ssa::SSAOp::IntSub { dst, a, b } => {
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(raw) = parse_const_value(&b.name)
                        {
                            let off = base
                                .offset
                                .saturating_sub(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    r2ssa::SSAOp::PtrAdd {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        if let Some(base_expr) = addr_of(base, &addr_exprs)
                            && let Some(raw) = parse_const_value(&index.name)
                        {
                            let scaled = signed_offset_from_const(raw, ptr_bits)
                                .saturating_mul((*element_size).into());
                            let off = base_expr.offset.saturating_add(scaled);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base_expr.base,
                                        offset: off,
                                        confidence: base_expr.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    r2ssa::SSAOp::PtrSub {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        if let Some(base_expr) = addr_of(base, &addr_exprs)
                            && let Some(raw) = parse_const_value(&index.name)
                        {
                            let scaled = signed_offset_from_const(raw, ptr_bits)
                                .saturating_mul((*element_size).into());
                            let off = base_expr.offset.saturating_sub(scaled);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base_expr.base,
                                        offset: off,
                                        confidence: base_expr.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            let resolve_addr = |addr: &r2ssa::SSAVar| -> Option<GlobalAddrExpr> {
                parse_const_value(&addr.name)
                    .filter(|base| *base >= 0x10000)
                    .map(|base| GlobalAddrExpr {
                        base,
                        offset: 0,
                        confidence: 92,
                    })
                    .or_else(|| {
                        addr_exprs
                            .get(&ssa_var_block_key(block.addr, addr))
                            .copied()
                    })
            };
            match op {
                r2ssa::SSAOp::Load { dst, addr, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = field_evidence
                            .entry(expr.base)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.reads = entry.reads.saturating_add(1);
                        *entry.widths.entry(dst.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(dst.size)).or_insert(0) += 1;
                    }
                }
                r2ssa::SSAOp::Store { addr, val, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = field_evidence
                            .entry(expr.base)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.writes = entry.writes.saturating_add(1);
                        *entry.widths.entry(val.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(val.size)).or_insert(0) += 1;
                    }
                }
                _ => {}
            }
        }
    }

    field_evidence
}

#[cfg(test)]
fn score_global_type_links(
    ssa_blocks: &[r2ssa::SSABlock],
    struct_decls: &[StructDeclCandidateJson],
    var_type_candidates: &[VarTypeCandidateJson],
    ptr_bits: u32,
) -> Vec<GlobalTypeLinkCandidateJson> {
    use std::collections::BTreeMap;

    let per_addr_profiles = infer_global_field_profiles(ssa_blocks, ptr_bits);
    if per_addr_profiles.is_empty() {
        return Vec::new();
    }

    let mut per_type_weight: BTreeMap<String, i32> = BTreeMap::new();
    let mut decl_profiles: BTreeMap<String, BTreeMap<u64, String>> = BTreeMap::new();
    for decl in struct_decls {
        let key = format!("struct {} *", decl.name);
        if is_generic_type_string(&key) {
            continue;
        }
        let source_boost = if decl.source == "external_type_db" {
            12
        } else {
            0
        };
        per_type_weight.insert(
            key.clone(),
            32 + source_boost + (decl.confidence as i32 / 6) + (decl.fields.len() as i32).min(16),
        );
        decl_profiles.insert(
            key,
            decl.fields
                .iter()
                .map(|field| {
                    (
                        field.offset,
                        normalize_external_type_name(&field.field_type).to_ascii_lowercase(),
                    )
                })
                .collect(),
        );
    }
    for var in var_type_candidates {
        if var.var_type.starts_with("struct ")
            && var.var_type.ends_with(" *")
            && !is_generic_type_string(&var.var_type)
        {
            *per_type_weight.entry(var.var_type.clone()).or_insert(30) +=
                4 + (var.confidence as i32 / 12);
        }
    }
    if per_type_weight.is_empty() {
        return Vec::new();
    }

    let mut per_addr_best: BTreeMap<u64, (String, i32)> = BTreeMap::new();
    for (addr, profile) in per_addr_profiles {
        if profile.is_empty() {
            continue;
        }
        let observed_fields = profile.len();
        let mut best: Option<(String, i32)> = None;
        for (ty, base_score) in &per_type_weight {
            let Some(decl_profile) = decl_profiles.get(ty) else {
                continue;
            };
            if observed_fields == 1 && decl_profile.len() > 1 {
                continue;
            }

            let mut exact_matches = 0i32;
            let mut declared_offsets = 0i32;
            let mut evidence_weight = 0i32;
            for (offset, evidence) in &profile {
                let Some(decl_ty) = decl_profile.get(offset) else {
                    continue;
                };
                let Some((observed_ty, votes)) = evidence
                    .type_votes
                    .iter()
                    .max_by_key(|(_, count)| **count)
                    .map(|(ty, count)| (normalize_external_type_name(ty), *count as i32))
                else {
                    continue;
                };
                declared_offsets += 1;
                if decl_ty == &observed_ty.to_ascii_lowercase() {
                    exact_matches += 1;
                    evidence_weight +=
                        votes + evidence.reads.min(4) as i32 + evidence.writes.min(4) as i32;
                }
            }
            if exact_matches == 0 {
                continue;
            }
            if observed_fields > 1 && exact_matches < observed_fields.min(2) as i32 {
                continue;
            }

            let score =
                *base_score + exact_matches * 18 + declared_offsets * 6 + evidence_weight.min(18);
            match best {
                Some((ref prev_ty, prev_score))
                    if prev_score > score || (prev_score == score && prev_ty <= ty) => {}
                _ => best = Some((ty.clone(), score)),
            }
        }
        if let Some(candidate) = best {
            per_addr_best.insert(addr, candidate);
        }
    }

    per_addr_best
        .into_iter()
        .map(|(addr, (target_type, score))| GlobalTypeLinkCandidateJson {
            addr,
            target_type,
            confidence: score.clamp(1, 99) as u8,
            source: "dataflow_ranked".to_string(),
        })
        .collect()
}

/// Infer function signature + calling convention for post-analysis write-back.
///
/// Returns JSON:
/// {"function_name":"...","signature":"...","ret_type":"...","params":[...],"callconv":"...","arch":"...","confidence":N}
///
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_infer_signature_cc_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
) -> *mut c_char {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    let Some(signature) = types::infer_signature_cc_from_analysis(&input, &analysis) else {
        return ptr::null_mut();
    };

    match serde_json::to_string(&types::signature_to_json(&signature)) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

fn direct_call_targets_from_analysis(analysis: &types::FunctionAnalysis) -> Vec<u64> {
    let mut targets = std::collections::BTreeSet::new();
    for call in analysis.ssa_func.call_sites().by_id.values() {
        if let Some(target) = call.direct_target {
            targets.insert(target);
        }
    }
    targets.into_iter().collect()
}

fn runtime_registration_targets_from_analysis(
    analysis: &types::FunctionAnalysis,
    arch: Option<&ArchSpec>,
    registration_call_targets: &[u64],
) -> Vec<u64> {
    fn debug_runtime_targets_enabled() -> bool {
        std::env::var_os("R2SLEIGH_DEBUG_RUNTIME_TARGETS").is_some()
    }

    fn debug_runtime_targets_log(message: &str) {
        if !debug_runtime_targets_enabled() {
            return;
        }
        let path = std::env::var("R2SLEIGH_DEBUG_RUNTIME_TARGETS_LOG")
            .unwrap_or_else(|_| "/tmp/r2sleigh_runtime_targets.log".to_string());
        if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
            let _ = writeln!(file, "{message}");
        }
    }

    let lower_arch = arch.map(|arch| arch.name.to_ascii_lowercase());
    let supports_windows_x64 = arch.is_some_and(|arch| {
        lower_arch.as_deref().is_some_and(|name| {
            (name.contains("x86") || matches!(name, "x64" | "amd64"))
                && (arch.addr_size == 8 || name.contains("64"))
        })
    });
    if !supports_windows_x64 || registration_call_targets.is_empty() {
        debug_runtime_targets_log(&format!(
            "skip supports_windows_x64={} arch={:?} registrations={}",
            supports_windows_x64,
            lower_arch.as_deref(),
            registration_call_targets.len()
        ));
        return Vec::new();
    }

    let registrations = registration_call_targets
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let observations =
        r2ssa::observe_call_arguments(&analysis.ssa_func, &r2ssa::AbiProfile::windows_x64());
    let mut targets = std::collections::BTreeSet::new();
    for (call_id, call) in &analysis.ssa_func.call_sites().by_id {
        let Some(target) = analysis.ssa_func.resolved_call_target(call) else {
            debug_runtime_targets_log(&format!("call_id={call_id:?} unresolved_target"));
            continue;
        };
        if !registrations.contains(&target) {
            debug_runtime_targets_log(&format!(
                "call_id={call_id:?} target=0x{target:x} not_registration"
            ));
            continue;
        }
        let Some(args) = observations.get(call_id) else {
            debug_runtime_targets_log(&format!(
                "call_id={call_id:?} target=0x{target:x} missing_args"
            ));
            continue;
        };
        let Some(r2ssa::CallArgObservation::Const(handler)) = args.get(1) else {
            debug_runtime_targets_log(&format!(
                "call_id={call_id:?} target=0x{target:x} handler_arg={:?}",
                args.get(1)
            ));
            continue;
        };
        if *handler >= 0x1000 {
            debug_runtime_targets_log(&format!(
                "call_id={call_id:?} target=0x{target:x} handler=0x{handler:x}"
            ));
            targets.insert(*handler);
        }
    }
    targets.into_iter().collect()
}

#[derive(Serialize)]
struct RuntimeMaterializedSourceJson {
    addr: u64,
    size: u64,
}

fn runtime_materialized_sources_from_analysis(
    analysis: &types::FunctionAnalysis,
    arch: Option<&ArchSpec>,
    copy_call_targets: &[u64],
) -> Vec<RuntimeMaterializedSourceJson> {
    let lower_arch = arch.map(|arch| arch.name.to_ascii_lowercase());
    let supports_windows_x64 = arch.is_some_and(|arch| {
        lower_arch.as_deref().is_some_and(|name| {
            (name.contains("x86") || matches!(name, "x64" | "amd64"))
                && (arch.addr_size == 8 || name.contains("64"))
        })
    });
    if !supports_windows_x64 || copy_call_targets.is_empty() {
        return Vec::new();
    }

    let copy_targets = copy_call_targets
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let observations =
        r2ssa::observe_call_arguments(&analysis.ssa_func, &r2ssa::AbiProfile::windows_x64());
    let mut sources = std::collections::BTreeMap::<u64, u64>::new();
    for (call_id, call) in &analysis.ssa_func.call_sites().by_id {
        let Some(target) = analysis.ssa_func.resolved_call_target(call) else {
            continue;
        };
        if !copy_targets.contains(&target) {
            continue;
        }
        let Some(args) = observations.get(call_id) else {
            continue;
        };
        let (
            Some(r2ssa::CallArgObservation::Const(source)),
            Some(r2ssa::CallArgObservation::Const(size)),
        ) = (args.get(1), args.get(2))
        else {
            continue;
        };
        if *source >= 0x1000 && *size > 0 {
            sources
                .entry(*source)
                .and_modify(|existing| *existing = (*existing).max(*size))
                .or_insert(*size);
        }
    }

    sources
        .into_iter()
        .map(|(addr, size)| RuntimeMaterializedSourceJson { addr, size })
        .collect()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_direct_call_targets_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
) -> *mut c_char {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    let payload = direct_call_targets_from_analysis(&analysis);
    match serde_json::to_string(&payload) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_direct_call_targets_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
) -> *mut R2SleighU64Array {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    Box::into_raw(Box::new(R2SleighU64Array {
        values: direct_call_targets_from_analysis(&analysis),
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_symbolic_scope_targets_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    registration_call_targets_json: *const c_char,
) -> *mut c_char {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    let registration_call_targets: Vec<u64> = serde_json::from_str(&helpers::cstr_or_default(
        registration_call_targets_json,
        "[]",
    ))
    .unwrap_or_default();
    let payload = runtime_registration_targets_from_analysis(
        &analysis,
        input.ctx.arch,
        &registration_call_targets,
    );
    match serde_json::to_string(&payload) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_symbolic_scope_targets_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    registration_call_targets: *const u64,
    num_registration_call_targets: usize,
) -> *mut R2SleighU64Array {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    let registration_call_targets = if registration_call_targets.is_null() {
        &[]
    } else {
        unsafe {
            std::slice::from_raw_parts(registration_call_targets, num_registration_call_targets)
        }
    };
    Box::into_raw(Box::new(R2SleighU64Array {
        values: runtime_registration_targets_from_analysis(
            &analysis,
            input.ctx.arch,
            registration_call_targets,
        ),
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_runtime_materialized_sources_json(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    copy_call_targets_json: *const c_char,
) -> *mut c_char {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    let copy_call_targets: Vec<u64> =
        serde_json::from_str(&helpers::cstr_or_default(copy_call_targets_json, "[]"))
            .unwrap_or_default();
    let payload =
        runtime_materialized_sources_from_analysis(&analysis, input.ctx.arch, &copy_call_targets);
    match serde_json::to_string(&payload) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_get_runtime_materialized_sources_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    copy_call_targets: *const u64,
    num_copy_call_targets: usize,
) -> *mut R2SleighRuntimeSources {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return ptr::null_mut();
    };
    let Some(analysis) = types::build_function_analysis(&input) else {
        return ptr::null_mut();
    };
    let copy_call_targets = if copy_call_targets.is_null() {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(copy_call_targets, num_copy_call_targets) }
    };
    let items =
        runtime_materialized_sources_from_analysis(&analysis, input.ctx.arch, copy_call_targets)
            .into_iter()
            .map(|source| R2SleighRuntimeSource {
                addr: source.addr,
                size: source.size,
            })
            .collect();
    Box::into_raw(Box::new(R2SleighRuntimeSources { items }))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_u64_array_items(
    array: *const R2SleighU64Array,
    count: *mut usize,
) -> *const u64 {
    if array.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let array = unsafe { &*array };
    if !count.is_null() {
        unsafe {
            *count = array.values.len();
        }
    }
    array.values.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_u64_array_free(array: *mut R2SleighU64Array) {
    if !array.is_null() {
        unsafe {
            drop(Box::from_raw(array));
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_runtime_sources_items(
    sources: *const R2SleighRuntimeSources,
    count: *mut usize,
) -> *const R2SleighRuntimeSource {
    if sources.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let sources = unsafe { &*sources };
    if !count.is_null() {
        unsafe {
            *count = sources.items.len();
        }
    }
    sources.items.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_runtime_sources_free(sources: *mut R2SleighRuntimeSources) {
    if !sources.is_null() {
        unsafe {
            drop(Box::from_raw(sources));
        }
    }
}

/// Infer full type write-back payload (signature + per-variable + structs + globals).
///
/// Returns JSON suitable for plugin-side confidence/conflict policy.
/// Caller must free with r2il_string_free().
#[derive(Clone, Copy)]
struct InterprocInferenceInput<'a> {
    iter: usize,
    max_iters: usize,
    converged: bool,
    scope_facts: &'a types::InterprocScopeFacts,
    scope_report: Option<&'a serde_json::Value>,
}

struct TypeWritebackInferenceInput<'a> {
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    external_context_json: *const c_char,
    function_context: Option<&'a R2SleighFunctionContext>,
    scope_functions: *const analysis::sym::R2ILFunctionBlocks,
    scope_num_functions: usize,
    interproc: InterprocInferenceInput<'a>,
    global_max_links: usize,
    max_type_decls: usize,
    max_mutations: usize,
}

struct SemanticWorkerLinearizationInput {
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    block_count: usize,
    loop_count: usize,
    back_edge_count: usize,
    max_switch_cases: usize,
    scope_functions: *const analysis::sym::R2ILFunctionBlocks,
    scope_num_functions: usize,
}

struct FunctionAnalysisSharedBundle {
    function_name: String,
    function_addr: u64,
    cfg_risk: CfgRiskSummaryJson,
    semantic_artifact: Option<r2sym::SemanticArtifact>,
    function_facts: r2types::FunctionFacts,
    semantic_route: Option<SemanticRoutePlanJson>,
    type_writeback: InferredTypeWritebackJson,
    prefer_bounded_type_plan: bool,
    phase_timings: Vec<PhaseTimingJson>,
}

fn build_inference_symbolic_scope(
    input: &TypeWritebackInferenceInput<'_>,
    function_input: &types::FunctionInput<'_>,
) -> Option<r2sym::PreparedFunctionScope> {
    if input.scope_functions.is_null() || input.scope_num_functions == 0 {
        None
    } else {
        unsafe {
            analysis::sym::build_symbolic_scope_from_ffi(
                input.scope_functions,
                input.scope_num_functions,
                function_input.ctx.arch,
                function_input.function_addr,
            )
        }
    }
}

fn build_function_analysis_shared_bundle(
    input: TypeWritebackInferenceInput<'_>,
) -> Option<FunctionAnalysisSharedBundle> {
    let mut phase_timings = Vec::new();
    let phase_start = Instant::now();
    let function_input = types::build_function_input(
        input.ctx,
        input.blocks,
        input.num_blocks,
        input.fcn_addr,
        input.fcn_name,
    )?;
    push_phase(&mut phase_timings, "function_input", phase_start);
    let external_context = cstr_or_default(input.external_context_json, "{}");
    let symbolic_scope = build_inference_symbolic_scope(&input, &function_input);
    let (_, ptr_bits, _) = r2dec::DecompilerConfig::for_arch(function_input.ctx.arch);
    let parsed_context = if let Some(function_context) = input.function_context {
        unsafe { typed_function_context_to_parsed(function_context, &external_context, ptr_bits) }
    } else {
        r2types::parse_external_context_json(&external_context, ptr_bits)
    };
    let external_context_fallback_hash = types::hash_string_payload(&external_context);
    let output_budget = TypeOutputBudget::new(
        input.global_max_links,
        input.max_type_decls,
        input.max_mutations,
    );
    let caller_requested_bounded_type_plan = caller_prefers_bounded_type_plan(&input.interproc);
    let phase_start = Instant::now();
    let reg_type_hints = if function_input.ctx.semantic_metadata_enabled {
        types::collect_register_type_hints(
            function_input.blocks.as_slice(),
            function_input.ctx.disasm,
        )
    } else {
        std::collections::HashMap::new()
    };
    let analysis_request = types::engine_analyze_request_with_scope_facts(
        &function_input,
        &parsed_context,
        external_context_fallback_hash,
        input.interproc.scope_facts,
        input.interproc.max_iters,
        symbolic_scope.as_ref(),
        reg_type_hints,
        None,
        r2engine::EngineSemanticMode::Full,
        true,
    );
    let response = types::engine_session().type_function(r2engine::EngineTypeAnalysisRequest {
        analysis: analysis_request,
        caller_prefers_bounded_type_plan: caller_requested_bounded_type_plan,
    })?;
    push_phase(&mut phase_timings, "engine_type_analysis", phase_start);

    let cfg_risk = cfg_risk_summary_json(response.cfg_summary);
    let semantic_artifact = response.function_facts.semantics.clone();
    let semantic_route = response
        .semantic_route
        .clone()
        .map(semantic_route_plan_json);
    let prefer_bounded_type_plan = response.route_decision.prefer_bounded_type_plan;
    let function_facts = response.function_facts.clone();
    let phase_start = Instant::now();
    let mut type_writeback = type_writeback_payload_from_engine_response(
        response,
        input.interproc,
        symbolic_scope.as_ref(),
        output_budget,
    );
    push_phase(&mut phase_timings, "writeback", phase_start);
    complete_type_phase_timings(&mut phase_timings);
    type_writeback.phase_timings = phase_timings.clone();

    Some(FunctionAnalysisSharedBundle {
        function_name: function_input.function_name.clone(),
        function_addr: function_input.function_addr,
        cfg_risk,
        semantic_artifact,
        function_facts,
        semantic_route,
        type_writeback,
        prefer_bounded_type_plan,
        phase_timings,
    })
}

fn function_analysis_session_report_json(
    mut bundle: FunctionAnalysisSharedBundle,
) -> Option<FunctionAnalysisSessionReport> {
    let phase_start = Instant::now();
    let _ = serde_json::to_string(&bundle.type_writeback).ok()?;
    push_phase(&mut bundle.phase_timings, "json_serialization", phase_start);
    bundle.type_writeback.phase_timings = bundle.phase_timings.clone();
    let type_writeback_json = serde_json::to_string(&bundle.type_writeback).ok()?;
    let type_writeback_hash = types::hash_string_payload(&type_writeback_json);
    let (mutations, strings) =
        ffi_mutations_from_session_plan(&bundle.type_writeback.mutation_plan);
    let mut strings = strings;
    let (signature_fact, signature_params) =
        ffi_signature_fact_from_type_writeback(&bundle.type_writeback, &mut strings);
    let semantic = bundle
        .semantic_artifact
        .as_ref()
        .map(analysis::sym::compiled_semantic_info);
    let semantic_build_plan = bundle
        .semantic_artifact
        .as_ref()
        .map(r2sym::SemanticArtifact::build_plan);
    let summary_diagnostics = bundle.function_facts.summary_view.diagnostics().cloned();
    let plans = bundle.function_facts.plans.clone();
    let assumptions = bundle.function_facts.assumptions.clone();
    let assumption_usage = bundle.function_facts.assumption_usage.clone();
    let payload = FunctionAnalysisSessionReportJson {
        function_name: bundle.function_name,
        function_addr: bundle.function_addr,
        cfg_risk: bundle.cfg_risk,
        plans,
        assumptions,
        assumption_usage,
        semantic,
        semantic_build_plan,
        semantic_route: bundle.semantic_route,
        summary_diagnostics,
        type_writeback: bundle.type_writeback,
        prefer_bounded_type_plan: bundle.prefer_bounded_type_plan,
        phase_timings: bundle.phase_timings,
    };
    let report_json = serde_json::to_string(&payload).ok()?;
    Some(FunctionAnalysisSessionReport {
        report_json,
        type_writeback_json,
        type_writeback_hash,
        mutations,
        signature_fact,
        signature_params,
        strings,
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_analyze(
    input: *const R2SleighSessionInput,
) -> *mut R2SleighSessionResult {
    if input.is_null() {
        return ptr::null_mut();
    }
    let input = unsafe { &*input };
    let scope_facts = unsafe { typed_interproc_scope_facts(&input.interproc_scope) };
    let interproc_iter = input.budget.interproc_iter.max(1);
    let interproc_max_iters = input.budget.interproc_max_iters.max(interproc_iter);
    let inference_input = TypeWritebackInferenceInput {
        ctx: input.ctx,
        blocks: input.blocks,
        num_blocks: input.num_blocks,
        fcn_addr: input.function_addr,
        fcn_name: input.function_name,
        external_context_json: input.function_context.external_context_json,
        function_context: Some(&input.function_context),
        scope_functions: input.interproc_scope.functions,
        scope_num_functions: input.interproc_scope.num_functions,
        interproc: InterprocInferenceInput {
            iter: interproc_iter,
            max_iters: interproc_max_iters,
            converged: input.budget.interproc_converged != 0,
            scope_facts: &scope_facts,
            scope_report: None,
        },
        global_max_links: input.budget.global_max_links.max(1),
        max_type_decls: input.budget.max_type_decls.max(1),
        max_mutations: input.budget.max_mutations.max(1),
    };
    let Some(bundle) = build_function_analysis_shared_bundle(inference_input) else {
        return ptr::null_mut();
    };
    let Some(FunctionAnalysisSessionReport {
        report_json,
        type_writeback_json,
        type_writeback_hash,
        mutations,
        mut signature_fact,
        signature_params,
        strings,
    }) = function_analysis_session_report_json(bundle)
    else {
        return ptr::null_mut();
    };
    let Ok(report_json) = CString::new(report_json) else {
        return ptr::null_mut();
    };
    let Ok(type_writeback_json) = CString::new(type_writeback_json) else {
        return ptr::null_mut();
    };
    if !signature_params.is_empty() {
        signature_fact.params = signature_params.as_ptr();
    }
    Box::into_raw(Box::new(R2SleighSessionResult {
        report_json,
        type_writeback_json,
        type_writeback_hash,
        mutations,
        signature_fact,
        _signature_params: signature_params,
        _strings: strings,
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_report_json(
    result: *const R2SleighSessionResult,
) -> *const c_char {
    if result.is_null() {
        return ptr::null();
    }
    unsafe { (*result).report_json.as_ptr() }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_type_writeback_json(
    result: *const R2SleighSessionResult,
) -> *const c_char {
    if result.is_null() {
        return ptr::null();
    }
    unsafe { (*result).type_writeback_json.as_ptr() }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_type_writeback_json_dup(
    result: *const R2SleighSessionResult,
) -> *mut c_char {
    if result.is_null() {
        return ptr::null_mut();
    }
    let bytes = unsafe { (*result).type_writeback_json.as_bytes() };
    CString::new(bytes.to_vec()).map_or(ptr::null_mut(), |cstr| cstr.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_type_writeback_hash(
    result: *const R2SleighSessionResult,
) -> u64 {
    if result.is_null() {
        return 0;
    }
    unsafe { (*result).type_writeback_hash }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_mutations(
    result: *const R2SleighSessionResult,
    count: *mut usize,
) -> *const R2SleighMutation {
    if result.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let result = unsafe { &*result };
    if !count.is_null() {
        unsafe {
            *count = result.mutations.len();
        }
    }
    result.mutations.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_signature_fact(
    result: *const R2SleighSessionResult,
) -> *const R2SleighSignatureFact {
    if result.is_null() {
        return ptr::null();
    }
    let result = unsafe { &*result };
    if result.signature_fact.signature.is_null() {
        return ptr::null();
    }
    &result.signature_fact
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_result_free(result: *mut R2SleighSessionResult) {
    if !result.is_null() {
        unsafe {
            drop(Box::from_raw(result));
        }
    }
}

/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_bounded_type_json_ffi(
    ctx: *const R2ILContext,
    fcn_name: *const c_char,
    reason: *const c_char,
    global_max_links: usize,
    max_type_decls: usize,
    max_mutations: usize,
) -> *mut c_char {
    let function_name = cstr_or_default(fcn_name, "unknown").to_string();
    let reason = cstr_or_default(reason, "bounded type plan").to_string();
    let arch = unsafe { ctx.as_ref().and_then(|ctx| ctx.arch.as_ref()) };
    let (arch_name, ptr_bits, _) = r2dec::DecompilerConfig::for_arch(arch);
    let scope_facts = types::empty_interproc_scope_facts();
    let interproc = InterprocInferenceInput {
        iter: 1,
        max_iters: 1,
        converged: false,
        scope_facts: &scope_facts,
        scope_report: None,
    };
    let function_facts = r2types::FunctionFacts::new(r2types::FunctionTypeFacts::default(), None);
    let mut payload = bounded_cfg_type_payload(BoundedCfgTypePayloadInput {
        function_name: &function_name,
        arch_name: &arch_name,
        ptr_bits,
        callconv: None,
        interproc,
        function_facts: &function_facts,
        symbolic_scope: None,
        budget: TypeOutputBudget::new(
            global_max_links.max(1),
            max_type_decls.max(1),
            max_mutations.max(1),
        ),
        reason,
    });
    payload.phase_timings = vec![PhaseTimingJson {
        phase: "bounded_preflight".to_string(),
        elapsed_us: 0,
    }];
    CString::new(serde_json::to_string(&payload).unwrap_or_else(|_| "{}".to_string()))
        .map_or(ptr::null_mut(), |c| c.into_raw())
}

fn semantic_worker_linearization_impl(input: SemanticWorkerLinearizationInput) -> *mut c_char {
    let summary = r2ssa::CFGRiskSummary {
        block_count: input.block_count,
        loop_count: input.loop_count,
        back_edge_count: input.back_edge_count,
        switch_block_count: usize::from(input.max_switch_cases > 0),
        max_switch_cases: input.max_switch_cases,
    };
    let Some(function_input) = types::build_function_input(
        input.ctx,
        input.blocks,
        input.num_blocks,
        input.fcn_addr,
        input.fcn_name,
    ) else {
        return ptr::null_mut();
    };
    let symbolic_scope = if input.scope_functions.is_null() || input.scope_num_functions == 0 {
        None
    } else {
        unsafe {
            analysis::sym::build_symbolic_scope_from_ffi(
                input.scope_functions,
                input.scope_num_functions,
                function_input.ctx.arch,
                function_input.function_addr,
            )
        }
    };
    let (arch_name, ptr_bits, _) = r2dec::DecompilerConfig::for_arch(function_input.ctx.arch);
    let semantic_artifact = if let Some(cached_artifact) =
        types::get_cached_function_analysis_artifact_with_scope(
            &function_input,
            "{}",
            symbolic_scope.as_ref(),
        ) {
        cached_artifact.function_facts.semantics
    } else {
        types::collect_detached_semantic_artifact(
            function_input.blocks.as_slice(),
            &function_input.function_name,
            function_input.ctx.arch,
            symbolic_scope.as_ref(),
        )
    };
    let Some(semantic_artifact) = semantic_artifact else {
        return ptr::null_mut();
    };
    let plan = r2types::build_semantic_type_fallback_plan(
        &function_input.function_name,
        &arch_name,
        ptr_bits,
        &semantic_artifact,
    );
    let type_facts = r2types::inferred_signature_to_function_type_facts(&plan.signature, ptr_bits);
    let function_facts = r2types::FunctionFacts::new(type_facts, Some(semantic_artifact.clone()));
    let fallback_comment = semantic_artifact
        .native_body()
        .is_some_and(|native| native.has_summary_islands())
        .then(|| {
            let reason = r2engine::cfg_guard_reason_from_summary(&summary)
                .unwrap_or_else(|| "semantic worker summary".to_string());
            r2dec::render_semantic_worker_linearization(&plan, Some(&semantic_artifact), &reason)
        });
    let Some(response) =
        types::engine_session().decompile_summary(r2engine::EngineSummaryDecompileRequest {
            function_name: function_input.function_name.clone(),
            cfg_summary: summary,
            function_facts,
            named_worker_guarded: true,
            config: r2dec::DecompilerConfig::for_arch(function_input.ctx.arch).2,
            render_cache_key: None,
            fallback_comment,
        })
    else {
        return ptr::null_mut();
    };
    let output = response.output;
    CString::new(output).map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_artifact_cache_key(input: *const R2SleighSessionInput) -> u64 {
    if input.is_null() {
        return 0;
    }
    let input = unsafe { &*input };
    let Some(function_input) = types::build_function_input(
        input.ctx,
        input.blocks,
        input.num_blocks,
        input.function_addr,
        input.function_name,
    ) else {
        return 0;
    };
    let external_context = cstr_or_default(input.function_context.external_context_json, "{}");
    let scope_facts = unsafe { typed_interproc_scope_facts(&input.interproc_scope) };
    let interproc_iter = input.budget.interproc_iter.max(1);
    let interproc_max_iters = input.budget.interproc_max_iters.max(interproc_iter);
    let inference_input = TypeWritebackInferenceInput {
        ctx: input.ctx,
        blocks: input.blocks,
        num_blocks: input.num_blocks,
        fcn_addr: input.function_addr,
        fcn_name: input.function_name,
        external_context_json: input.function_context.external_context_json,
        function_context: Some(&input.function_context),
        scope_functions: input.interproc_scope.functions,
        scope_num_functions: input.interproc_scope.num_functions,
        interproc: InterprocInferenceInput {
            iter: interproc_iter,
            max_iters: interproc_max_iters,
            converged: input.budget.interproc_converged != 0,
            scope_facts: &scope_facts,
            scope_report: None,
        },
        global_max_links: input.budget.global_max_links.max(1),
        max_type_decls: input.budget.max_type_decls.max(1),
        max_mutations: input.budget.max_mutations.max(1),
    };
    let symbolic_scope = build_inference_symbolic_scope(&inference_input, &function_input);
    let ptr_bits = function_input
        .ctx
        .arch
        .as_ref()
        .map(|arch| helpers::effective_ptr_bits(arch))
        .unwrap_or(64);
    let parsed_context = unsafe {
        typed_function_context_to_parsed(&input.function_context, &external_context, ptr_bits)
    };
    types::function_analysis_artifact_cache_identity_hash_with_parsed_context_and_scope_facts(
        &function_input,
        &parsed_context,
        types::hash_string_payload(&external_context),
        &scope_facts,
        interproc_max_iters,
        symbolic_scope.as_ref(),
    )
    .unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_session_interproc_summary_json(
    input: *const R2SleighSessionInput,
) -> *mut c_char {
    if input.is_null() {
        return ptr::null_mut();
    }
    let input = unsafe { &*input };
    let Some(function_input) = types::build_function_input(
        input.ctx,
        input.blocks,
        input.num_blocks,
        input.function_addr,
        input.function_name,
    ) else {
        return ptr::null_mut();
    };
    let external_context = cstr_or_default(input.function_context.external_context_json, "{}");
    let scope_facts = unsafe { typed_interproc_scope_facts(&input.interproc_scope) };
    let interproc_iter = input.budget.interproc_iter.max(1);
    let interproc_max_iters = input.budget.interproc_max_iters.max(interproc_iter);
    let inference_input = TypeWritebackInferenceInput {
        ctx: input.ctx,
        blocks: input.blocks,
        num_blocks: input.num_blocks,
        fcn_addr: input.function_addr,
        fcn_name: input.function_name,
        external_context_json: input.function_context.external_context_json,
        function_context: Some(&input.function_context),
        scope_functions: input.interproc_scope.functions,
        scope_num_functions: input.interproc_scope.num_functions,
        interproc: InterprocInferenceInput {
            iter: interproc_iter,
            max_iters: interproc_max_iters,
            converged: input.budget.interproc_converged != 0,
            scope_facts: &scope_facts,
            scope_report: None,
        },
        global_max_links: input.budget.global_max_links.max(1),
        max_type_decls: input.budget.max_type_decls.max(1),
        max_mutations: input.budget.max_mutations.max(1),
    };
    let symbolic_scope = build_inference_symbolic_scope(&inference_input, &function_input);
    let ptr_bits = function_input
        .ctx
        .arch
        .as_ref()
        .map(|arch| helpers::effective_ptr_bits(arch))
        .unwrap_or(64);
    let parsed_context = unsafe {
        typed_function_context_to_parsed(&input.function_context, &external_context, ptr_bits)
    };
    let Some(summary) = types::function_root_interproc_summary_with_parsed_context_and_scope_facts(
        &function_input,
        &parsed_context,
        types::hash_string_payload(&external_context),
        &scope_facts,
        interproc_max_iters,
        symbolic_scope.as_ref(),
    ) else {
        return ptr::null_mut();
    };
    serde_json::to_string(&summary)
        .ok()
        .and_then(|json| CString::new(json).ok())
        .map_or(ptr::null_mut(), |c| c.into_raw())
}

#[unsafe(no_mangle)]
pub extern "C" fn r2dec_semantic_worker_linearization_scope_ffi(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    block_count: usize,
    loop_count: usize,
    back_edge_count: usize,
    max_switch_cases: usize,
    scope_functions: *const analysis::sym::R2ILFunctionBlocks,
    scope_num_functions: usize,
) -> *mut c_char {
    semantic_worker_linearization_impl(SemanticWorkerLinearizationInput {
        ctx,
        blocks,
        num_blocks,
        fcn_addr,
        fcn_name,
        block_count,
        loop_count,
        back_edge_count,
        max_switch_cases,
        scope_functions,
        scope_num_functions,
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_alias_function_analysis_artifact_cache(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    fcn_addr: u64,
    fcn_name: *const c_char,
    source_external_context_json: *const c_char,
    target_external_context_json: *const c_char,
) -> i32 {
    let Some(function_input) =
        types::build_function_input(ctx, blocks, num_blocks, fcn_addr, fcn_name)
    else {
        return 0;
    };
    let source_external_context = cstr_or_default(source_external_context_json, "{}");
    let target_external_context = cstr_or_default(target_external_context_json, "{}");
    types::alias_cached_function_analysis_artifact(
        &function_input,
        &source_external_context,
        &target_external_context,
    ) as i32
}

/// Analyze a function and build SSA representation.
/// This is called after radare2 completes basic function analysis.
/// Returns 1 on success, 0 on failure.
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_analyze_fcn(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> i32 {
    let Some(input) = types::build_function_input(ctx, blocks, num_blocks, 0, ptr::null()) else {
        return 0;
    };
    if types::build_function_analysis(&input).is_none() {
        return 0;
    }

    1 // Success
}

fn enum_label<T: serde::Serialize>(value: T) -> Option<String> {
    serde_json::to_value(value)
        .ok()?
        .as_str()
        .map(str::to_string)
}

fn summarize_block_semantics(block: &R2ILBlock) -> Option<String> {
    use std::collections::BTreeSet;

    let mut storage_classes: BTreeSet<String> = BTreeSet::new();
    let mut memory_classes: BTreeSet<String> = BTreeSet::new();
    let mut orderings: BTreeSet<String> = BTreeSet::new();
    let mut atomic_kinds: BTreeSet<String> = BTreeSet::new();
    let mut pointer_like = false;

    for (op_index, op) in block.ops.iter().enumerate() {
        if let Some(meta) = block.op_metadata.get(&op_index) {
            if let Some(memory_class) = meta.memory_class
                && let Some(label) = enum_label(memory_class)
            {
                memory_classes.insert(label);
            }
            if let Some(ordering) = meta.memory_ordering
                && let Some(label) = enum_label(ordering)
            {
                orderings.insert(label);
            }
            if let Some(kind) = meta.atomic_kind
                && let Some(label) = enum_label(kind)
            {
                atomic_kinds.insert(label);
            }
        }

        for vn in op_all_varnodes(op) {
            if let Some(meta) = vn.meta.as_ref() {
                if let Some(storage_class) = meta.storage_class
                    && let Some(label) = enum_label(storage_class)
                {
                    storage_classes.insert(label);
                }
                if let Some(pointer_hint) = meta.pointer_hint
                    && !matches!(pointer_hint, r2il::PointerHint::Unknown)
                {
                    pointer_like = true;
                }
            }
        }
    }

    let mut parts = Vec::new();
    if !storage_classes.is_empty() {
        let labels: Vec<String> = storage_classes.into_iter().collect();
        parts.push(format!("storage={}", labels.join(",")));
    }
    if !memory_classes.is_empty() {
        let labels: Vec<String> = memory_classes.into_iter().collect();
        parts.push(format!("mem={}", labels.join(",")));
    }
    if !orderings.is_empty() {
        let labels: Vec<String> = orderings.into_iter().collect();
        parts.push(format!("ord={}", labels.join(",")));
    }
    if !atomic_kinds.is_empty() {
        let labels: Vec<String> = atomic_kinds.into_iter().collect();
        parts.push(format!("atomic={}", labels.join(",")));
    }
    if pointer_like {
        parts.push("ptr".to_string());
    }

    if parts.is_empty() {
        None
    } else {
        Some(parts.join(" "))
    }
}

fn is_filtered_cpu_flag_name_lower(name: &str) -> bool {
    const CPU_FLAGS: [&str; 8] = ["cf", "zf", "sf", "pf", "of", "af", "df", "tf"];
    CPU_FLAGS.iter().any(|flag| {
        name == *flag
            || name
                .strip_prefix(flag)
                .is_some_and(|rest| rest.starts_with('_'))
    })
}

fn is_real_reg(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    !lower.starts_with("tmp:")
        && !lower.starts_with("const:")
        && !lower.starts_with("ram:")
        && !is_filtered_cpu_flag_name_lower(&lower)
}

/// Annotation entry for analyze_fcn writeback.
#[derive(serde::Serialize)]
struct FcnAnnotation {
    addr: u64,
    comment: String,
}

fn function_annotations_for_ffi(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> Option<Vec<FcnAnnotation>> {
    let input = types::build_function_input(ctx, blocks, num_blocks, 0, ptr::null())?;

    let semantic_by_addr: std::collections::HashMap<u64, String> = input
        .blocks
        .as_slice()
        .iter()
        .filter_map(|block| summarize_block_semantics(block).map(|summary| (block.addr, summary)))
        .collect();

    // Build function-level SSA with phi nodes.
    let ssa_func =
        r2ssa::SSAFunction::from_blocks_with_arch(input.blocks.as_slice(), input.ctx.arch)?;

    let mut annotations = Vec::new();

    for block in ssa_func.blocks() {
        let mut parts = Vec::new();

        if !block.phis.is_empty() {
            let phi_vars: Vec<&str> = block
                .phis
                .iter()
                .map(|p| p.dst.name.as_str())
                .filter(|n| is_real_reg(n))
                .collect();
            if !phi_vars.is_empty() {
                let mut sorted = phi_vars;
                sorted.sort();
                sorted.dedup();
                if sorted.len() > 4 {
                    sorted.truncate(4);
                    sorted.push("...");
                }
                parts.push(format!("merges {}", sorted.join(",")));
            }
        }

        let mut func_inputs = Vec::new();
        for op in &block.ops {
            for src in op.sources() {
                if src.version == 0 && is_real_reg(&src.name) {
                    func_inputs.push(src.name.as_str());
                }
            }
        }
        func_inputs.sort();
        func_inputs.dedup();
        if !func_inputs.is_empty() {
            if func_inputs.len() > 5 {
                func_inputs.truncate(5);
                func_inputs.push("...");
            }
            parts.push(format!("uses {}", func_inputs.join(",")));
        }

        let mut defs = Vec::new();
        for op in &block.ops {
            if let Some(dst) = op.dst()
                && is_real_reg(&dst.name)
            {
                defs.push(dst.name.as_str());
            }
        }
        defs.sort();
        defs.dedup();
        if !defs.is_empty() {
            if defs.len() > 5 {
                defs.truncate(5);
                defs.push("...");
            }
            parts.push(format!("defines {}", defs.join(",")));
        }

        if let Some(meta_summary) = semantic_by_addr.get(&block.addr) {
            let mut summary = meta_summary.to_string();
            if summary.len() > 96 {
                summary.truncate(96);
                summary.push_str("...");
            }
            parts.push(format!("meta {}", summary));
        }

        if !parts.is_empty() {
            annotations.push(FcnAnnotation {
                addr: block.addr,
                comment: format!("sla: {}", parts.join("; ")),
            });
        }
    }

    if annotations.is_empty() {
        return None;
    }

    Some(annotations)
}

fn ffi_annotations_from_annotations(annotations: Vec<FcnAnnotation>) -> R2SleighAnnotations {
    let mut strings = Vec::with_capacity(annotations.len());
    let mut items = Vec::with_capacity(annotations.len());

    for annotation in annotations {
        let comment_ptr = match CString::new(annotation.comment) {
            Ok(comment) => {
                strings.push(comment);
                strings.last().map_or(ptr::null(), |s| s.as_ptr())
            }
            Err(_) => ptr::null(),
        };
        if !comment_ptr.is_null() {
            items.push(R2SleighAnnotation {
                addr: annotation.addr,
                comment: comment_ptr,
            });
        }
    }

    R2SleighAnnotations {
        items,
        _strings: strings,
    }
}

/// Analyze a function and return per-block annotations as JSON.
/// Returns a JSON array of {addr, comment} pairs summarizing SSA def-use info.
/// Uses function-level SSA with phi nodes for meaningful annotations.
/// Caller must free with r2il_string_free().
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_analyze_fcn_annotations(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> *mut c_char {
    let Some(annotations) = function_annotations_for_ffi(ctx, blocks, num_blocks) else {
        return ptr::null_mut();
    };

    match serde_json::to_string(&annotations) {
        Ok(s) => CString::new(s).map_or(ptr::null_mut(), |c| c.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_analyze_fcn_annotations_typed(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    _fcn_addr: u64,
) -> *mut R2SleighAnnotations {
    let Some(annotations) = function_annotations_for_ffi(ctx, blocks, num_blocks) else {
        return ptr::null_mut();
    };
    Box::into_raw(Box::new(ffi_annotations_from_annotations(annotations)))
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_annotations_items(
    annotations: *const R2SleighAnnotations,
    count: *mut usize,
) -> *const R2SleighAnnotation {
    if annotations.is_null() {
        if !count.is_null() {
            unsafe {
                *count = 0;
            }
        }
        return ptr::null();
    }
    let annotations = unsafe { &*annotations };
    if !count.is_null() {
        unsafe {
            *count = annotations.items.len();
        }
    }
    annotations.items.as_ptr()
}

#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_annotations_free(annotations: *mut R2SleighAnnotations) {
    if !annotations.is_null() {
        unsafe {
            drop(Box::from_raw(annotations));
        }
    }
}

#[cfg(test)]
fn signature_spec(
    ret_type: Option<r2dec::CType>,
    params: Vec<(&str, Option<r2dec::CType>)>,
) -> r2types::FunctionSignatureSpec {
    r2types::FunctionSignatureSpec {
        ret_type: ret_type.as_ref().map(ctype_to_type_like),
        params: params
            .into_iter()
            .map(|(name, ty)| r2types::FunctionParamSpec {
                name: name.to_string(),
                ty: ty.as_ref().map(ctype_to_type_like),
            })
            .collect(),
    }
}

#[cfg(test)]
fn set_signature_facts(
    decompiler: &mut r2dec::Decompiler,
    signature: Option<r2types::FunctionSignatureSpec>,
) {
    decompiler.set_type_facts(r2types::FunctionTypeFacts {
        merged_signature: signature,
        ..r2types::FunctionTypeFacts::default()
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;
    use std::ffi::{CStr, CString};

    fn type_like(ty: r2dec::CType) -> r2types::CTypeLike {
        ctype_to_type_like(&ty)
    }

    fn register_param(
        name: &str,
        ty: Option<r2dec::CType>,
        reg: &str,
    ) -> r2types::ExternalRegisterParamSpec {
        r2types::ExternalRegisterParamSpec {
            name: name.to_string(),
            ty: ty.as_ref().map(ctype_to_type_like),
            reg: reg.to_string(),
        }
    }

    #[test]
    fn semantic_comment_reg_filter_excludes_cpu_flags_case_insensitively() {
        for flag in [
            "cf", "zf", "sf", "pf", "of", "af", "df", "tf", "CF", "ZF_1", "of_12", "TF_99",
        ] {
            assert!(!is_real_reg(flag), "{flag} should be filtered out");
        }

        for name in ["rax", "rdi", "rflags", "eax", "XMM0"] {
            assert!(
                is_real_reg(name),
                "{name} should be kept as a real register"
            );
        }

        for synthetic in ["tmp:10", "const:4", "ram:1000", "TMP:5"] {
            assert!(
                !is_real_reg(synthetic),
                "{synthetic} should be excluded as non-register data"
            );
        }
    }

    #[test]
    fn switch_info_ffi_canonicalizes_duplicate_case_values() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let values = [0, 0, 4, 4, 8, 8];
        let targets = [0x3000, 0x2000, 0x4004, 0x4000, 0x5000, 0x5000];

        r2il_block_set_switch_info(
            &mut block,
            0x1000,
            0,
            8,
            0,
            values.as_ptr(),
            targets.as_ptr(),
            values.len(),
        );

        let switch_info = block.switch_info.expect("switch info");
        let cases: Vec<(u64, u64)> = switch_info
            .cases
            .iter()
            .map(|case| (case.value, case.target))
            .collect();
        assert_eq!(cases, vec![(0, 0x2000), (4, 0x4000), (8, 0x5000)]);
    }

    #[cfg(feature = "x86")]
    unsafe fn c_string_to_owned(ptr: *mut c_char) -> String {
        let out = unsafe { CStr::from_ptr(ptr) }
            .to_string_lossy()
            .into_owned();
        r2il_string_free(ptr);
        out
    }

    #[cfg(feature = "x86")]
    fn export_from_context(
        ctx_ref: &R2ILContext,
        block: &R2ILBlock,
        action: InstructionAction,
        format: ExportFormat,
    ) -> String {
        let disasm = ctx_ref.disasm.as_ref().expect("disassembler");
        let arch = ctx_ref.arch.as_ref().expect("arch spec");
        let input = InstructionExportInput {
            disasm,
            arch,
            block,
            addr: block.addr,
            mnemonic: "",
            native_size: block.size as usize,
        };
        export_instruction(&input, action, format).expect("export")
    }

    #[test]
    fn test_context_lifecycle_from_file() {
        let spec = r2sleigh_lift::create_x86_64_spec();
        let temp_path = "/tmp/test_r2il_plugin.r2il";
        serialize::save(&spec, Path::new(temp_path)).unwrap();

        let path_cstr = CString::new(temp_path).unwrap();
        let ctx = r2il_load(path_cstr.as_ptr());
        assert!(!ctx.is_null());
        assert_eq!(r2il_is_loaded(ctx), 1);

        let name_ptr = r2il_arch_name(ctx);
        assert!(!name_ptr.is_null());
        let name = unsafe { CStr::from_ptr(name_ptr) };
        assert_eq!(name.to_str().unwrap(), "x86-64");

        r2il_free(ctx);
        std::fs::remove_file(temp_path).ok();
    }

    #[test]
    #[cfg(feature = "x86")]
    fn test_lift_and_esil() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        // xor eax, eax (0x31 0xC0) padded to 16 bytes for libsla
        let mut bytes = vec![0x31, 0xC0];
        bytes.resize(16, 0);

        let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!block.is_null());
        assert!(r2il_block_op_count(block) > 0);

        let esil_ptr = r2il_block_to_esil(ctx, block);
        assert!(!esil_ptr.is_null());
        let esil = unsafe { CStr::from_ptr(esil_ptr) }
            .to_string_lossy()
            .into_owned();
        assert!(esil.contains("eax"));

        unsafe { drop(CString::from_raw(esil_ptr as *mut c_char)) };
        r2il_block_free(block);
        r2il_free(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn op_json_named_matches_exporter_output_shape() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        let mut bytes = vec![0x31, 0xC0];
        bytes.resize(16, 0);
        let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!block.is_null());

        let block_ref = unsafe { &*block };
        let ctx_ref = unsafe { &*ctx };
        let op_index = 0usize;
        let expected_json = op_json_named(
            ctx_ref.disasm.as_ref().expect("disassembler"),
            &block_ref.ops[op_index],
        )
        .expect("exporter op json");

        let json_ptr = r2il_block_op_json_named(ctx, block, op_index);
        assert!(!json_ptr.is_null());
        let ffi_json = unsafe { c_string_to_owned(json_ptr) };

        let expected_val: Value =
            serde_json::from_str(&expected_json).expect("expected json value");
        let ffi_val: Value = serde_json::from_str(&ffi_json).expect("ffi json value");
        assert_eq!(ffi_val, expected_val);

        r2il_block_free(block);
        r2il_free(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn block_to_esil_matches_exporter() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        let mut bytes = vec![0x31, 0xC0];
        bytes.resize(16, 0);
        let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!block.is_null());

        let ffi_ptr = r2il_block_to_esil(ctx, block);
        assert!(!ffi_ptr.is_null());
        let ffi_esil = unsafe { c_string_to_owned(ffi_ptr) };

        let ctx_ref = unsafe { &*ctx };
        let block_ref = unsafe { &*block };
        let expected = export_from_context(
            ctx_ref,
            block_ref,
            InstructionAction::Lift,
            ExportFormat::Esil,
        );
        let expected_joined = expected
            .lines()
            .filter(|line| !line.is_empty())
            .collect::<Vec<_>>()
            .join(";");
        assert_eq!(ffi_esil, expected_joined);

        r2il_block_free(block);
        r2il_free(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn block_to_ssa_json_matches_exporter() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        let mut bytes = vec![0x31, 0xC0];
        bytes.resize(16, 0);
        let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!block.is_null());

        let ffi_ptr = r2il_block_to_ssa_json(ctx, block);
        assert!(!ffi_ptr.is_null());
        let ffi_json = unsafe { c_string_to_owned(ffi_ptr) };

        let ctx_ref = unsafe { &*ctx };
        let block_ref = unsafe { &*block };
        let expected = export_from_context(
            ctx_ref,
            block_ref,
            InstructionAction::Ssa,
            ExportFormat::Json,
        );

        let ffi_val: Value = serde_json::from_str(&ffi_json).expect("ffi json");
        let expected_val: Value = serde_json::from_str(&expected).expect("expected json");
        assert_eq!(ffi_val, expected_val);

        r2il_block_free(block);
        r2il_free(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn block_defuse_json_matches_exporter() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        let mut bytes = vec![0x31, 0xC0];
        bytes.resize(16, 0);
        let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!block.is_null());

        let ffi_ptr = r2il_block_defuse_json(ctx, block);
        assert!(!ffi_ptr.is_null());
        let ffi_json = unsafe { c_string_to_owned(ffi_ptr) };

        let ctx_ref = unsafe { &*ctx };
        let block_ref = unsafe { &*block };
        let expected = export_from_context(
            ctx_ref,
            block_ref,
            InstructionAction::Defuse,
            ExportFormat::Json,
        );

        let ffi_val: Value = serde_json::from_str(&ffi_json).expect("ffi json");
        let expected_val: Value = serde_json::from_str(&expected).expect("expected json");
        assert_eq!(ffi_val, expected_val);

        r2il_block_free(block);
        r2il_free(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_block_c_like_matches_exporter_path() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        let mut bytes = vec![0x31, 0xC0];
        bytes.resize(16, 0);
        let block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!block.is_null());

        let ffi_ptr = r2dec_block(ctx, block);
        assert!(!ffi_ptr.is_null());
        let ffi_c_like = unsafe { c_string_to_owned(ffi_ptr) };

        let ctx_ref = unsafe { &*ctx };
        let block_ref = unsafe { &*block };
        let expected = export_from_context(
            ctx_ref,
            block_ref,
            InstructionAction::Dec,
            ExportFormat::CLike,
        );
        assert_eq!(ffi_c_like, expected);

        r2il_block_free(block);
        r2il_free(ctx);
    }

    #[test]
    fn test_null_handling() {
        assert!(r2il_load(ptr::null()).is_null());
        assert_eq!(r2il_is_loaded(ptr::null()), 0);
        assert!(r2il_arch_name(ptr::null()).is_null());
        r2il_free(ptr::null_mut());
        r2il_block_free(ptr::null_mut());
    }

    #[test]
    fn is_big_endian_uses_memory_endianness_shim() {
        let mut arch = ArchSpec::new("shim");
        arch.set_memory_endianness(r2il::Endianness::Big);
        let ctx = Box::into_raw(Box::new(R2ILContext::with_arch(arch)));
        assert_eq!(r2il_is_big_endian(ctx), 1);
        r2il_free(ctx);

        let mut arch = ArchSpec::new("shim2");
        arch.set_memory_endianness(r2il::Endianness::Mixed);
        let ctx = Box::into_raw(Box::new(R2ILContext::with_arch(arch)));
        assert_eq!(r2il_is_big_endian(ctx), 0);
        r2il_free(ctx);
    }

    #[test]
    fn test_parse_external_signature_with_args() {
        let json = r#"[{"name":"dbg.vuln_memcpy","args":[{"name":"user_input","type":"char *"},{"name":"user_len","type":"int32_t"}],"count":2}]"#;
        let sig = parse_external_signature(json, 64).expect("signature should parse");
        assert!(sig.ret_type.is_none());
        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.params[0].name, "user_input");
        assert_eq!(sig.params[1].name, "user_len");
        assert_eq!(
            sig.params[0].ty,
            Some(type_like(r2dec::CType::ptr(r2dec::CType::Int(8))))
        );
        assert_eq!(sig.params[1].ty, Some(type_like(r2dec::CType::Int(32))));
    }

    #[test]
    fn test_parse_external_signature_missing_return() {
        let json = r#"[{"name":"dbg.main","args":[{"name":"arg0","type":"int64_t"}]}]"#;
        let sig = parse_external_signature(json, 64).expect("signature should parse");
        assert!(sig.ret_type.is_none());
        assert_eq!(sig.params[0].name, "arg0");
    }

    #[test]
    fn test_parse_external_signature_drops_void_placeholder_param() {
        let json =
            r#"[{"name":"dbg.test","args":[{"name":"arg1","type":"void"}],"return":"int32_t"}]"#;
        let sig = parse_external_signature(json, 64).expect("signature should parse");
        assert_eq!(sig.ret_type, Some(type_like(r2dec::CType::Int(32))));
        assert!(
            sig.params.is_empty(),
            "single generic void placeholder should be treated as an empty parameter list"
        );
    }

    #[test]
    fn test_normalize_external_type_name_handles_type_prefixes() {
        assert_eq!(normalize_external_type_name("type.int"), "int");
        assert_eq!(
            normalize_external_type_name("const type.uint64_t *"),
            "uint64_t *"
        );
        assert_eq!(
            normalize_external_type_name("struct.sla_example *"),
            "struct sla_example *"
        );
        assert_eq!(
            normalize_external_type_name("struct type.foo_bar *"),
            "struct foo_bar *"
        );
        assert_eq!(normalize_external_type_name("type.LONG"), "long");
        assert_eq!(normalize_external_type_name("type.LONGU"), "unsigned long");
        assert_eq!(
            normalize_external_type_name("type.IOCPU_VTable.setCPUNumber"),
            "void *"
        );
    }

    #[test]
    fn test_parse_external_type_accepts_type_prefixed_primitives() {
        assert_eq!(
            parse_external_type("type.int", 64),
            Some(r2dec::CType::Int(32))
        );
        assert_eq!(
            parse_external_type("type.uint16_t *", 64),
            Some(r2dec::CType::ptr(r2dec::CType::UInt(16)))
        );
        assert_eq!(
            parse_external_type("struct.sla_node *", 64),
            Some(r2dec::CType::ptr(r2dec::CType::Struct(
                "sla_node".to_string()
            )))
        );
        assert_eq!(
            parse_external_type("type.IOCPU_VTable.setCPUNumber", 64),
            Some(r2dec::CType::ptr(r2dec::CType::Void))
        );
    }

    #[test]
    fn test_parse_external_type_accepts_canonical_signed_spellings() {
        assert_eq!(
            parse_external_type("signed int", 64),
            Some(r2dec::CType::Int(32))
        );
        assert_eq!(
            parse_external_type("signed short int", 64),
            Some(r2dec::CType::Int(16))
        );
        assert_eq!(
            parse_external_type("signed long", 64),
            Some(r2dec::CType::Int(64))
        );
        assert_eq!(
            parse_external_type("signed long *", 64),
            Some(r2dec::CType::ptr(r2dec::CType::Int(64)))
        );
    }

    #[test]
    fn test_parse_external_type_accepts_canonical_ssize_t_aliases() {
        assert_eq!(
            parse_external_type("intptr_t", 64),
            Some(r2dec::CType::Int(64))
        );
        assert_eq!(
            parse_external_type("type.intptr_t", 64),
            Some(r2dec::CType::Int(64))
        );
        assert_eq!(
            parse_external_type("ssize_t *", 64),
            Some(r2dec::CType::ptr(r2dec::CType::Int(64)))
        );
    }

    #[test]
    fn test_estimate_c_type_size_bytes_respects_ptr_width_for_long_and_size_t() {
        assert_eq!(estimate_c_type_size_bytes("long", 32), 4);
        assert_eq!(estimate_c_type_size_bytes("unsigned long", 32), 4);
        assert_eq!(estimate_c_type_size_bytes("size_t", 32), 4);
        assert_eq!(estimate_c_type_size_bytes("ssize_t", 32), 4);
        assert_eq!(estimate_c_type_size_bytes("intptr_t", 32), 4);

        assert_eq!(estimate_c_type_size_bytes("long", 64), 8);
        assert_eq!(estimate_c_type_size_bytes("unsigned long", 64), 8);
        assert_eq!(estimate_c_type_size_bytes("size_t", 64), 8);
        assert_eq!(estimate_c_type_size_bytes("ssize_t", 64), 8);
    }

    #[test]
    fn test_build_struct_decl_does_not_insert_fake_padding_for_32bit_long_layouts() {
        let decl = build_struct_decl(
            "demo",
            &[
                StructFieldCandidateJson {
                    name: "f_0".to_string(),
                    offset: 0,
                    field_type: "long".to_string(),
                    confidence: 90,
                },
                StructFieldCandidateJson {
                    name: "f_4".to_string(),
                    offset: 4,
                    field_type: "int32_t".to_string(),
                    confidence: 90,
                },
            ],
            32,
        )
        .expect("struct decl");
        assert!(
            !decl.contains("_pad_4"),
            "32-bit long should not force synthetic padding: {decl}"
        );
    }

    #[test]
    fn test_parse_existing_var_types_normalizes_type_prefixes() {
        let json = r#"{
            "reg":[{"name":"arg0","type":"type.int"}],
            "bp":[{"name":"local_10h","type":"struct.sla_pair *"}]
        }"#;
        let parsed = parse_existing_var_types(json);
        assert_eq!(parsed.get("arg0").map(String::as_str), Some("int"));
        assert_eq!(
            parsed.get("local_10h").map(String::as_str),
            Some("struct sla_pair *")
        );
    }

    #[test]
    fn test_parse_signature_context_legacy_array() {
        let json =
            r#"[{"name":"dbg.main","return":"int32_t","args":[{"name":"x","type":"int32_t"}]}]"#;
        let ctx = parse_signature_context(json, 64);
        assert!(
            ctx.current.is_some(),
            "legacy payload should parse current signature"
        );
        assert!(
            ctx.known.is_empty(),
            "legacy payload should not synthesize known signatures"
        );
    }

    #[test]
    fn test_parse_signature_context_object_with_known() {
        let json = r#"{
          "current":[{"name":"dbg.main","return":"int32_t","args":[{"name":"x","type":"int32_t"}]}],
          "known":[
            {"name":"sym.imp.printf","return":"int32_t","args":[{"name":"fmt","type":"char *"}],"variadic":true},
            {"name":"sym.imp.strlen","return":"size_t","args":[{"name":"s","type":"char *"}]}
          ],
          "cc":{"sysv":{"ret":"rax"}}
        }"#;
        let ctx = parse_signature_context(json, 64);
        assert!(ctx.current.is_some(), "current signature should parse");
        assert!(
            ctx.known.contains_key("sym.imp.printf"),
            "known map should include original symbol names"
        );
        assert!(
            ctx.known.contains_key("printf"),
            "known map should include stripped fallback aliases"
        );
        assert!(
            ctx.known.contains_key("sym.imp.strlen"),
            "known map should include additional signatures"
        );
    }

    #[test]
    fn test_parse_external_stack_vars_bp_sp() {
        let json = r#"{"sp":[{"name":"var_8h","kind":"var","type":"int64_t","ref":{"base":"RSP","offset":80}}],"bp":[{"name":"buf","kind":"var","type":"char[64]","ref":{"base":"RBP","offset":-64}},{"name":"user_input","kind":"var","type":"char *","ref":{"base":"RBP","offset":-72}}]}"#;
        let vars = parse_external_stack_vars(json, 64);
        assert_eq!(vars.get(&-64).map(|v| v.name.as_str()), Some("buf"));
        assert_eq!(vars.get(&-72).map(|v| v.name.as_str()), Some("user_input"));
        assert_eq!(
            vars.get(&80).and_then(|v| v.base.legacy_name()),
            Some("rsp".to_string())
        );
    }

    #[test]
    fn test_parse_external_reg_params_from_afvj_payload() {
        let json = r#"{"reg":[{"name":"arg0","kind":"reg","type":"int32_t","ref":"RDI"},{"name":"arg1","kind":"reg","type":"int32_t","ref":"RSI"}]}"#;
        let params = parse_external_reg_params(json, 64);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].name, "arg0");
        assert_eq!(params[0].ty, Some(type_like(r2dec::CType::Int(32))));
        assert_eq!(params[0].reg, "RDI");
        assert_eq!(params[1].name, "arg1");
        assert_eq!(params[1].ty, Some(type_like(r2dec::CType::Int(32))));
        assert_eq!(params[1].reg, "RSI");
    }

    #[test]
    fn test_merge_signature_with_reg_params_fills_missing_host_args() {
        let merged = merge_signature_with_reg_params(
            Some(signature_spec(Some(r2dec::CType::Int(32)), Vec::new())),
            vec![
                register_param("arg0", Some(r2dec::CType::Int(32)), "RDI"),
                register_param("arg1", Some(r2dec::CType::Int(32)), "RSI"),
            ],
        )
        .expect("merged signature");
        assert_eq!(merged.ret_type, Some(type_like(r2dec::CType::Int(32))));
        assert_eq!(merged.params.len(), 2);
        assert_eq!(merged.params[0].ty, Some(type_like(r2dec::CType::Int(32))));
        assert_eq!(merged.params[1].ty, Some(type_like(r2dec::CType::Int(32))));
    }

    #[test]
    fn test_name_sanitization_and_collisions() {
        let json = r#"{"bp":[{"name":"bad-name","type":"int","ref":{"base":"RBP","offset":-8}},{"name":"bad name","type":"int","ref":{"base":"RBP","offset":-16}}]}"#;
        let vars = parse_external_stack_vars(json, 64);
        let first = vars.get(&-8).expect("first var");
        let second = vars.get(&-16).expect("second var");
        assert_eq!(first.name, "bad_name");
        assert_ne!(first.name, second.name);
    }

    #[test]
    fn test_parse_external_type_db_tsj_struct_payload() {
        let json = r#"{
          "types": [
            {
              "kind": "struct",
              "name": "DemoStruct",
              "members": [
                {"name": "first", "offset": 0, "type": "int"},
                {"name": "thirteenth", "offset": 48, "type": "int"}
              ]
            }
          ]
        }"#;
        let db = r2types::ExternalTypeDb::from_tsj_json(json);
        assert!(db.diagnostics.is_empty(), "diagnostics should be empty");
        assert!(
            db.structs
                .get("demostruct")
                .and_then(|st| st.fields.get(&48))
                .is_some(),
            "DemoStruct field at offset 48 should be parsed"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn test_r2dec_with_context_uses_tsj_field_name() {
        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");
        assert_eq!(
            r2il_addr_size(ctx),
            8,
            "x86-64 FFI context should report an 8-byte address size"
        );

        // mov eax, [rdi + 0x30]
        let mut mov_bytes = vec![0x8b, 0x47, 0x30];
        mov_bytes.resize(16, 0);
        let block_load = r2il_lift(ctx, mov_bytes.as_ptr(), mov_bytes.len(), 0x1000);
        assert!(!block_load.is_null(), "load block should lift");

        // ret
        let mut ret_bytes = vec![0xc3];
        ret_bytes.resize(16, 0);
        let block_ret = r2il_lift(ctx, ret_bytes.as_ptr(), ret_bytes.len(), 0x1003);
        assert!(!block_ret.is_null(), "ret block should lift");

        let blocks: [*const R2ILBlock; 2] = [block_load, block_ret];
        let func_name = CString::new("demo").expect("valid function name");
        let empty_map = CString::new("{}").expect("valid empty json");
        let external_context_json = CString::new(
            r#"{
                "base_types":[
                    {
                        "kind":"struct",
                        "name":"DemoStruct",
                        "members":[
                            {"name":"thirteenth","offset":48,"type":"int"}
                        ]
                    }
                ]
            }"#,
        )
        .expect("valid tsj json");

        let out = r2dec_function_with_context(
            ctx,
            blocks.as_ptr(),
            blocks.len(),
            func_name.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            external_context_json.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        r2il_block_free(block_load);
        r2il_block_free(block_ret);
        r2il_free(ctx);

        assert!(
            output.contains("f_30")
                || output.contains("thirteenth")
                || output.contains("*(rdi + 30)")
                || output.contains("*(rdi + const_30)")
                || output.contains("*(rdi + 48)")
                || output.contains("*(rdi + const_48)")
                || output.contains("saved_fp"),
            "decompiler should keep decompilation stable with tsj context, got: {}",
            output
        );
    }

    #[test]
    fn effective_ptr_bits_falls_back_to_default_space_when_arch_addr_size_is_degenerate() {
        let arch_name = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch_name.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");
        let mut arch = unsafe { (*ctx).arch.clone().expect("arch spec") };
        r2il_free(ctx);
        arch.addr_size = 1;
        assert_eq!(
            crate::helpers::effective_addr_size_bytes(&arch),
            8,
            "effective address size should recover from Sleigh word-sized addr_size"
        );
        assert_eq!(crate::helpers::effective_ptr_bits(&arch), 64);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_function_with_context_keeps_live_x86_struct_array_member_shape() {
        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let bytes = [
            0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xe5, 0x48, 0x89, 0x7d, 0xf8, 0x89, 0x75,
            0xf4, 0x89, 0x55, 0xf0, 0x8b, 0x45, 0xf4, 0x48, 0x63, 0xd0, 0x48, 0x89, 0xd0, 0x48,
            0xc1, 0xe0, 0x03, 0x48, 0x29, 0xd0, 0x48, 0xc1, 0xe0, 0x03, 0x48, 0x89, 0xc2, 0x48,
            0x8b, 0x45, 0xf8, 0x48, 0x01, 0xc2, 0x8b, 0x45, 0xf0, 0x89, 0x42, 0x08, 0x8b, 0x45,
            0xf4, 0x48, 0x63, 0xd0, 0x48, 0x89, 0xd0, 0x48, 0xc1, 0xe0, 0x03, 0x48, 0x29, 0xd0,
            0x48, 0xc1, 0xe0, 0x03, 0x48, 0x89, 0xc2, 0x48, 0x8b, 0x45, 0xf8, 0x48, 0x01, 0xd0,
            0x8b, 0x48, 0x08, 0x8b, 0x45, 0xf4, 0x48, 0x63, 0xd0, 0x48, 0x89, 0xd0, 0x48, 0xc1,
            0xe0, 0x03, 0x48, 0x29, 0xd0, 0x48, 0xc1, 0xe0, 0x03, 0x48, 0x89, 0xc2, 0x48, 0x8b,
            0x45, 0xf8, 0x48, 0x01, 0xd0, 0x8b, 0x40, 0x34, 0x01, 0xc8, 0x5d, 0xc3,
        ];
        let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), 0x40182f, 124);
        assert!(!block.is_null(), "function block should lift");

        let blocks: [*const R2ILBlock; 1] = [block];
        let func_name = CString::new("dbg.test_struct_array_index").expect("valid function name");
        let empty_map = CString::new("{}").expect("valid empty json");
        let external_context_json = CString::new(
            r#"{
                "signature": {
                    "name": "dbg.test_struct_array_index",
                    "ret": "int32_t",
                    "callconv": "amd64",
                    "params": [
                        {"name": "arr", "type": "void *"},
                        {"name": "idx", "type": "int32_t"},
                        {"name": "v", "type": "int32_t"}
                    ]
                },
                "vars": [
                    {"kind":"register","name":"arg0","type":"void *","reg":"rdi"},
                    {"kind":"register","name":"arg1","type":"int64_t","reg":"rsi"},
                    {"kind":"register","name":"arg2","type":"void *","reg":"rdx"},
                    {"kind":"stack","name":"var_8h","type":"void *","base":"rsp","offset":0},
                    {"kind":"stack","name":"arr","type":"DemoStruct *","base":"rbp","offset":-8},
                    {"kind":"stack","name":"var_ch","type":"int32_t","base":"rbp","offset":-12},
                    {"kind":"stack","name":"var_10h","type":"int32_t","base":"rbp","offset":-16}
                ],
                "base_types": []
            }"#,
        )
        .expect("valid external context");

        let out = r2dec_function_with_context(
            ctx,
            blocks.as_ptr(),
            blocks.len(),
            func_name.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            external_context_json.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        r2il_block_free(block);
        r2il_free(ctx);

        assert!(
            output.contains("[idx].f_8") || output.contains("[idx].third"),
            "expected indexed-member store rendering in decompiled output, got:\n{output}"
        );
        assert!(
            output.contains("[idx].f_34") || output.contains("[idx].fourteenth"),
            "expected indexed-member load rendering in decompiled output, got:\n{output}"
        );
        assert!(
            !output.contains("*(arr +") && !output.contains("((rax_"),
            "expected semantic member rendering without raw pointer math, got:\n{output}"
        );
        let return_tail = output
            .split_once("return")
            .map(|(_, tail)| tail)
            .unwrap_or_default();
        assert!(
            return_tail.contains('+')
                && (return_tail.contains("[idx].f_34") || return_tail.contains("[idx].fourteenth"))
                && (return_tail.contains("[idx].f_8")
                    || return_tail.contains("[idx].third")
                    || return_tail.contains(" v")),
            "expected return expression to keep both struct-array terms, got:\n{output}"
        );
        assert!(
            !output.contains("local_"),
            "autogenerated stack-home locals should not leak through the live FFI decompile path, got:\n{output}"
        );
        assert!(
            output.contains("arr[idx].f_8 = v;"),
            "expected live FFI decompile path to keep parameter-home names under x86 context, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_function_with_context_keeps_live_x86_struct_field_offset_zero_member_shape() {
        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let bytes = [
            0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xe5, 0x48, 0x89, 0x7d, 0xf8, 0x89, 0x75,
            0xf4, 0x48, 0x8b, 0x45, 0xf8, 0x8b, 0x55, 0xf4, 0x89, 0x50, 0x30, 0x48, 0x8b, 0x45,
            0xf8, 0x8b, 0x50, 0x30, 0x48, 0x8b, 0x45, 0xf8, 0x8b, 0x00, 0x01, 0xd0, 0x5d, 0xc3,
        ];
        let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), 0x401667, 42);
        assert!(!block.is_null(), "function block should lift");

        let blocks: [*const R2ILBlock; 1] = [block];
        let func_name = CString::new("dbg.test_struct_field").expect("valid function name");
        let empty_map = CString::new("{}").expect("valid empty json");
        let external_context_json = CString::new(
            r#"{
                "signature": {
                    "name": "dbg.test_struct_field",
                    "ret": "int32_t",
                    "callconv": "amd64",
                    "params": [
                        {"name": "obj", "type": "DemoStruct *"},
                        {"name": "v", "type": "int32_t"}
                    ]
                },
                "vars": [
                    {"kind":"register","name":"obj","type":"DemoStruct *","reg":"rdi","param_index":0},
                    {"kind":"register","name":"v","type":"int32_t","reg":"rsi","param_index":1},
                    {"kind":"stack","name":"obj","type":"DemoStruct *","base":"rbp","offset":-8,"role":"param_home","param_index":0,"param_name":"obj","source_reg":"rdi"},
                    {"kind":"stack","name":"v","type":"int32_t","base":"rbp","offset":-12,"role":"param_home","param_index":1,"param_name":"v","source_reg":"rsi"}
                ],
                "base_types": []
            }"#,
        )
        .expect("valid external context");

        let out = r2dec_function_with_context(
            ctx,
            blocks.as_ptr(),
            blocks.len(),
            func_name.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            external_context_json.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        r2il_block_free(block);
        r2il_free(ctx);

        assert!(
            output.contains("obj->f_30 = v;") || output.contains("obj->thirteenth = v;"),
            "expected live FFI decompile to keep the field store shape, got:\n{output}"
        );
        assert!(
            (output.contains("obj->f_0") || output.contains("obj->first"))
                && (output.contains("obj->f_30") || output.contains("obj->thirteenth")),
            "expected live FFI decompile to keep both field loads, got:\n{output}"
        );
        assert!(
            !output.contains("return obj +"),
            "offset-zero field load should not collapse to the base pointer, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_function_with_context_keeps_live_x86_setlocale_owner_and_deref() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let lifted = [
            (
                "f30f1efa554889e54883ec10488d059c1900004889c6bf06000000e8affaffff488945f848837df8007507",
                0x401691,
                43,
            ),
            ("b800000000eb0a", 0x4016bc, 7),
            ("488b45f80fb6000fbec0", 0x4016c3, 10),
            ("c9c3", 0x4016cd, 2),
        ];
        let mut owned_blocks = Vec::new();
        for (hex, addr, size) in lifted {
            let bytes = decode_hex(hex);
            let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), addr, size);
            assert!(
                !block.is_null(),
                "setlocale wrapper block should lift at 0x{addr:x}"
            );
            owned_blocks.push(block);
        }

        let func_name = CString::new("dbg.test_setlocale_wrapper").expect("valid function name");
        let function_names =
            CString::new(r#"{"0x401160":"sym.imp.setlocale"}"#).expect("valid function name map");
        let strings_json = CString::new(r#"{"0x403040":"C"}"#).expect("valid strings map");
        let empty_map = CString::new("{}").expect("valid empty json");
        let external_context_json = CString::new(
            r#"{
                "signature": {
                    "name": "dbg.test_setlocale_wrapper",
                    "ret": "int32_t",
                    "callconv": "amd64",
                    "params": []
                },
                "vars": [
                    {"kind":"stack","name":"loc","type":"int8_t *","base":"rbp","offset":-8,"role":"local"}
                ],
                "base_types": []
            }"#,
        )
        .expect("valid setlocale external context");

        let out = r2dec_function_with_context(
            ctx,
            owned_blocks.as_ptr().cast(),
            owned_blocks.len(),
            func_name.as_ptr(),
            function_names.as_ptr(),
            strings_json.as_ptr(),
            empty_map.as_ptr(),
            external_context_json.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        for block in owned_blocks {
            r2il_block_free(block);
        }
        r2il_free(ctx);

        assert!(
            output.contains("loc = sym.imp.setlocale(6, \"C\");")
                || output.contains("loc = (int8_t*)sym.imp.setlocale(6, \"C\");"),
            "expected live FFI decompile to keep the owned call result, got:\n{output}"
        );
        assert!(
            output.contains("if (loc != 0)") || output.contains("if (!loc)"),
            "expected live FFI decompile to branch on loc, got:\n{output}"
        );
        assert!(
            output.contains("return *loc;")
                || output.contains("return (int32_t)*loc;")
                || output.contains("return loc[0];")
                || output.contains("return (int32_t)loc[0];"),
            "expected live FFI decompile to keep the dereferenced return, got:\n{output}"
        );
        assert!(
            !output.contains("return loc;"),
            "pointer local should not collapse to a raw pointer return, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_function_with_context_keeps_live_x86_entry0_no_self_xor_residue() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let bytes = decode_hex(
            "f30f1efa31ed4989d15e4889e24883e4f050544531c031c948c7c7b61b4000ff15233e0000",
        );
        let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), 0x401190, 37);
        assert!(!block.is_null(), "entry0 block should lift");

        let blocks: [*const R2ILBlock; 1] = [block];
        let func_name = CString::new("entry0").expect("valid function name");
        let function_names =
            CString::new(r#"{"0x401bb6":"dbg.main"}"#).expect("valid function name map");
        let empty_map = CString::new("{}").expect("valid empty json");

        let out = r2dec_function_with_context(
            ctx,
            blocks.as_ptr(),
            blocks.len(),
            func_name.as_ptr(),
            function_names.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        r2il_block_free(block);
        r2il_free(ctx);

        assert!(
            !output.contains(" = eax ^ eax;") && !output.contains(" = rax ^ rax;"),
            "entry0 decompile should not keep self-xor residue, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn test_varnode_to_json_includes_meta_when_set() {
        let (_, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let meta = r2il::VarnodeMetadata {
            scalar_kind: Some(r2il::ScalarKind::UnsignedInt),
            pointer_hint: Some(r2il::PointerHint::PointerLike),
            ..Default::default()
        };
        let vn = r2il::Varnode::register(0, 8).with_meta(meta);

        let value = varnode_to_json(&vn, &disasm).expect("varnode json");
        let meta_json = value
            .get("meta")
            .and_then(Value::as_object)
            .expect("meta object");
        assert_eq!(
            meta_json.get("scalar_kind").and_then(Value::as_str),
            Some("unsigned_int")
        );
        assert_eq!(
            meta_json.get("pointer_hint").and_then(Value::as_str),
            Some("pointer_like")
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn test_varnode_to_json_omits_meta_when_unset() {
        let (_, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let vn = r2il::Varnode::register(0, 8);

        let value = varnode_to_json(&vn, &disasm).expect("varnode json");
        assert!(
            value.get("meta").is_none(),
            "meta should be omitted when not set"
        );
    }

    #[test]
    fn test_generic_arg_detection() {
        assert!(is_generic_arg_name("arg0"));
        assert!(is_generic_arg_name("Arg12"));
        assert!(!is_generic_arg_name("user_input"));
    }

    #[test]
    fn test_format_afs_signature() {
        let params = vec![
            InferredParamJson {
                name: "a".to_string(),
                param_type: "int32_t".to_string(),
            },
            InferredParamJson {
                name: "b".to_string(),
                param_type: "int64_t".to_string(),
            },
        ];
        let sig = format_afs_signature("dbg.sum", "int32_t", &params);
        assert_eq!(sig, "int32_t dbg.sum (int32_t a, int64_t b)");
    }

    #[test]
    fn test_normalize_inferred_param_name_fallback_and_uniquify() {
        let mut used = std::collections::HashSet::new();
        let first = normalize_inferred_param_name("bad name", 0, &mut used);
        let second = normalize_inferred_param_name("bad name", 1, &mut used);
        let fallback = normalize_inferred_param_name("$$$", 2, &mut used);
        assert_eq!(first, "bad_name");
        assert_eq!(second, "bad_name_2");
        assert_eq!(fallback, "arg2");
    }

    #[test]
    fn test_sanitize_inferred_param_type_fallbacks_from_void() {
        let ty = sanitize_inferred_param_type(r2dec::CType::Void, 0, 64);
        assert_eq!(ty, r2dec::CType::Int(64));
    }

    #[test]
    fn materialize_signature_type_rewrites_unknown_pointer_to_void_ptr() {
        let ty = materialize_signature_ctype(r2dec::CType::ptr(r2dec::CType::Unknown), 64);
        assert_eq!(ty, r2dec::CType::void_ptr());
        assert_eq!(ty.to_string(), "void*");
    }

    #[test]
    fn materialize_signature_type_rewrites_unknown_return_to_scalar_fallback() {
        let ty = materialize_signature_ctype(r2dec::CType::Unknown, 64);
        assert_eq!(ty, r2dec::CType::Int(64));
    }

    #[test]
    fn fallback_scalar_type_prefers_narrow_evidence_for_wide_scalar_carrier() {
        let ty = fallback_scalar_type(
            8,
            &TypeEvidence {
                scalar_proven: 1,
                width_bits: 32,
                ..TypeEvidence::default()
            },
            64,
        );
        assert_eq!(ty, r2dec::CType::Int(32));
    }

    #[test]
    fn resolve_evidence_driven_type_can_narrow_wide_scalar_carrier() {
        let ty = resolve_evidence_driven_type(
            r2dec::CType::Int(64),
            8,
            64,
            &TypeEvidence {
                scalar_proven: 1,
                width_bits: 32,
                ..TypeEvidence::default()
            },
        );
        assert_eq!(ty, r2dec::CType::Int(32));
    }

    #[test]
    fn merge_initial_type_evidence_preserves_narrow_scalar_hint_over_wide_carrier_type() {
        let mut evidence = TypeEvidence {
            scalar_proven: 1,
            width_bits: 32,
            ..TypeEvidence::default()
        };
        merge_initial_type_evidence(&r2dec::CType::Int(64), &mut evidence);
        assert_eq!(evidence.width_bits, 32);
    }

    #[test]
    fn collect_type_evidence_uses_arm64_register_family_alias_when_only_w_view_is_present() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:sp8", 1, 8),
                    val: r2ssa::SSAVar::new("W0", 0, 4),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("tmp:eq", 1, 1),
                    a: r2ssa::SSAVar::new("W0", 0, 4),
                    b: r2ssa::SSAVar::new("const:0", 0, 4),
                },
            ],
        }];
        let evidence_ctx = types::collect_signature_type_evidence_context(&blocks);
        let evidence = collect_type_evidence_for_var(
            &evidence_ctx,
            &r2ssa::SSAVar::new("X0", 0, 8),
            &r2dec::CType::Int(64),
        );
        let ty = resolve_evidence_driven_type(r2dec::CType::Int(64), 8, 64, &evidence);

        assert_eq!(evidence.width_bits, 32);
        assert_eq!(ty, r2dec::CType::Int(32));
    }

    #[test]
    fn materialize_signature_type_rewrites_struct_anon_pointer_to_void_ptr() {
        let ty = materialize_signature_ctype(
            r2dec::CType::ptr(r2dec::CType::Struct("anon".to_string())),
            64,
        );
        assert_eq!(ty, r2dec::CType::void_ptr());
    }

    #[test]
    fn opaque_placeholder_detection_treats_anon_as_unmaterialized() {
        assert!(is_opaque_placeholder_type_name("struct anon *"));
        assert!(is_unmaterialized_aggregate_name("anon"));
    }

    #[test]
    fn test_infer_callconv_x86_64_prefers_amd64_for_sysv_inputs() {
        let mut counts = std::collections::HashMap::new();
        counts.insert("rdi".to_string(), 3);
        counts.insert("rsi".to_string(), 2);
        counts.insert("rdx".to_string(), 1);
        let (cc, confidence) = infer_callconv_x86_64_from_counts(&counts);
        assert_eq!(cc, "amd64");
        assert!(confidence >= 80);
    }

    #[test]
    fn test_infer_callconv_x86_64_prefers_ms_when_rcx_dominates() {
        let mut counts = std::collections::HashMap::new();
        counts.insert("rcx".to_string(), 3);
        counts.insert("rdx".to_string(), 2);
        counts.insert("r8".to_string(), 1);
        let (cc, confidence) = infer_callconv_x86_64_from_counts(&counts);
        assert_eq!(cc, "ms");
        assert!(confidence >= 70);
    }

    #[test]
    fn decompiler_cfg_guard_reason_trips_on_dense_looped_switch_summary() {
        let summary = r2ssa::CFGRiskSummary {
            block_count: 120,
            loop_count: 5,
            back_edge_count: 8,
            switch_block_count: 1,
            max_switch_cases: 40,
        };

        let reason =
            r2engine::cfg_guard_reason_from_summary(&summary).expect("guard reason expected");
        assert!(
            reason.contains("dense switch") || reason.contains("max_switch_cases"),
            "unexpected reason: {reason}"
        );
    }

    #[test]
    fn decompiler_cfg_guard_reason_trips_on_compact_looped_switch_summary() {
        let summary = r2ssa::CFGRiskSummary {
            block_count: 39,
            loop_count: 2,
            back_edge_count: 2,
            switch_block_count: 1,
            max_switch_cases: 47,
        };

        let reason =
            r2engine::cfg_guard_reason_from_summary(&summary).expect("guard reason expected");
        assert!(
            reason.contains("dense switch in looped CFG"),
            "unexpected reason: {reason}"
        );
    }

    #[test]
    fn decompiler_cfg_guard_reason_trips_on_large_back_edge_count() {
        let summary = r2ssa::CFGRiskSummary {
            block_count: 137,
            loop_count: 1,
            back_edge_count: 38,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        let reason =
            r2engine::cfg_guard_reason_from_summary(&summary).expect("guard reason expected");
        assert!(
            reason.contains("back_edges=38"),
            "expected back-edge detail in reason, got: {reason}"
        );
    }

    #[test]
    fn decompiler_cfg_guard_reason_allows_small_benign_cfgs() {
        let summary = r2ssa::CFGRiskSummary {
            block_count: 12,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        assert_eq!(r2engine::cfg_guard_reason_from_summary(&summary), None);
    }

    #[test]
    fn r2dec_cfg_guard_comment_ffi_reports_complex_loop_graph() {
        let name = CString::new("fcn.140010138").unwrap();
        let out = r2dec_cfg_guard_comment_ffi(name.as_ptr(), 107, 9, 17, 0);
        assert!(!out.is_null());
        let rendered = unsafe { CStr::from_ptr(out) }.to_str().unwrap().to_string();
        assert!(rendered.contains("r2dec fallback"));
        assert!(rendered.contains("complex loop graph"));
        r2il_string_free(out);
    }

    #[test]
    fn r2dec_cfg_guard_comment_ffi_returns_null_for_benign_summary() {
        let name = CString::new("sym.small").unwrap();
        let out = r2dec_cfg_guard_comment_ffi(name.as_ptr(), 12, 1, 1, 0);
        assert!(out.is_null());
    }

    #[test]
    fn moderate_dense_cfg_can_still_use_semantic_type_plan() {
        let moderate_dense = r2ssa::CFGRiskSummary {
            block_count: 55,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 1,
            max_switch_cases: 48,
        };
        assert!(r2engine::type_cfg_forces_bounded_plan(&moderate_dense));
        assert!(r2engine::type_cfg_allows_semantic_plan(&moderate_dense));

        let large_loop = r2ssa::CFGRiskSummary {
            block_count: 1977,
            loop_count: 9,
            back_edge_count: 17,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        assert!(r2engine::type_cfg_forces_bounded_plan(&large_loop));
        assert!(!r2engine::type_cfg_allows_semantic_plan(&large_loop));
    }

    fn test_compiled_condition(expr: &str) -> r2sym::BackwardConditionSummary {
        r2sym::BackwardConditionSummary {
            simplified: expr.to_string(),
            terms: vec![expr.to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: r2sym::BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        }
    }

    fn test_large_cfg_semantic_artifact() -> r2sym::SemanticArtifact {
        let compiled = test_compiled_condition("x == 0");
        let region = r2sym::SemanticRegion {
            anchor: 0x401000,
            frontier: std::collections::BTreeSet::from([0x401020, 0x401030]),
            control: vec![
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x401020,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("x == 0".to_string()),
                        compiled: Some(compiled.clone()),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x401030,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                        condition: Some("x != 0".to_string()),
                        compiled: None,
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x401020,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: None,
                        condition: Some("x == 0".to_string()),
                        compiled: Some(compiled.clone()),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
            memory: Vec::new(),
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x401020,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x401030,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
        };
        r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Residual,
            granularity: r2sym::ArtifactGranularity::Regioned,
            execution: r2sym::ExecutionModel::Native,
            body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
                summary: r2sym::NativeFunctionSummary {
                    slice_class: r2sym::SliceClass::Worker,
                    role_identity: None,
                    closure_functions: 4,
                    helper_functions: 3,
                    derived_summaries: 0,
                    derived_diagnostics: r2sym::DerivedSummaryDiagnostics::default(),
                    region_summaries: Vec::new(),
                    worker_summaries: Vec::new(),
                },
                regions: std::iter::once((region.key(), region)).collect(),
            }),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 1,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: true,
                residual_reasons: vec![r2sym::ResidualReason::LargeCfg],
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        }
    }

    #[test]
    fn summary_only_semantics_feed_types_instead_of_bounded_fallback() {
        let mut artifact = test_large_cfg_semantic_artifact();
        artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let cfg_risk = r2ssa::CFGRiskSummary {
            block_count: 200,
            loop_count: 8,
            back_edge_count: 12,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        assert!(r2engine::semantic_or_cfg_prefers_bounded_type_plan(
            &artifact, &cfg_risk
        ));
        assert!(!r2engine::semantic_artifact_needs_fallback_type_payload(
            &artifact, &cfg_risk
        ));
    }

    #[test]
    fn semantic_type_fallback_payload_preserves_assumptions() {
        let compiled = test_large_cfg_semantic_artifact();
        assert!(
            r2types::semantic_artifact_prefers_bounded_type_plan(&compiled),
            "expected large-CFG worker artifact to use bounded semantic type fallback"
        );

        let assumptions = r2ssa::AssumptionSet::new(vec![r2ssa::AnalysisAssumption {
            id: Some("seed-rdi".to_string()),
            scope: r2ssa::AssumptionScope::Function,
            provenance: r2ssa::AssumptionProvenance::User,
            subject: r2ssa::AssumptionSubject::Register {
                name: "rdi".to_string(),
            },
            value: r2ssa::AssumptionValue::Constant { value: 0xdead },
        }]);
        let type_facts = r2types::FunctionTypeFacts {
            merged_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: Some(r2types::CTypeLike::Void),
                params: vec![r2types::FunctionParamSpec {
                    name: "status".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    }),
                }],
            }),
            ..r2types::FunctionTypeFacts::default()
        };
        let function_facts = r2types::FunctionFacts::new(type_facts, Some(compiled.clone()))
            .with_assumptions(assumptions.clone());
        let scope_facts = types::empty_interproc_scope_facts();
        let payload = semantic_type_fallback_payload(SemanticTypeFallbackPayloadInput {
            function_name: "fcn.401000",
            arch_name: "x86-64",
            ptr_bits: 64,
            callconv: None,
            interproc: InterprocInferenceInput {
                iter: 0,
                max_iters: 0,
                converged: true,
                scope_facts: &scope_facts,
                scope_report: None,
            },
            compiled: &compiled,
            function_facts: &function_facts,
            symbolic_scope: None,
            apply_artifact_signature_hint: false,
            budget: TypeOutputBudget::new(64, usize::MAX, usize::MAX),
        });
        let value = serde_json::to_value(payload).expect("payload should serialize");
        assert_eq!(
            value["signature"].as_str(),
            Some("void fcn.401000 (int32_t status)"),
            "expected semantic fallback to preserve typed signature: {value:?}"
        );
        let Some(items) = value["assumptions"]["items"].as_array() else {
            panic!("expected serialized assumptions, got {value:?}");
        };
        assert_eq!(
            items.len(),
            1,
            "expected one serialized assumption: {value:?}"
        );
        assert_eq!(
            items[0]["subject"]["register"]["name"].as_str(),
            Some("rdi"),
            "expected register assumption to survive fallback payload: {value:?}"
        );
    }

    #[test]
    fn semantic_type_fallback_payload_preserves_name_owned_role_signature() {
        let summary = r2ssa::FunctionSemanticSummary::seed_for_name(
            r2ssa::InterprocFunctionId(0x11a9),
            "verror_at_line",
        )
        .unwrap_or_else(|| {
            r2ssa::FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(0x11a9),
                Some("verror_at_line".to_string()),
            )
        });
        let compiled = r2sym::compile_named_native_worker_summary_artifact(&summary, true)
            .expect("expected named diagnostic summary artifact");
        let role_signature = r2types::signature_hint_for_name_candidates(["verror_at_line"], 6)
            .expect("expected exact diagnostic role signature");
        let type_facts = r2types::FunctionTypeFacts {
            merged_signature: Some(role_signature),
            ..r2types::FunctionTypeFacts::default()
        };
        let assumptions = r2ssa::AssumptionSet::default();
        let function_facts = r2types::FunctionFacts::new(type_facts, Some(compiled.clone()))
            .with_assumptions(assumptions.clone());
        let scope_facts = types::empty_interproc_scope_facts();
        let payload = semantic_type_fallback_payload(SemanticTypeFallbackPayloadInput {
            function_name: "verror_at_line",
            arch_name: "x86-64",
            ptr_bits: 64,
            callconv: Some("amd64"),
            interproc: InterprocInferenceInput {
                iter: 1,
                max_iters: 1,
                converged: false,
                scope_facts: &scope_facts,
                scope_report: None,
            },
            compiled: &compiled,
            function_facts: &function_facts,
            symbolic_scope: None,
            apply_artifact_signature_hint: false,
            budget: TypeOutputBudget::new(64, usize::MAX, usize::MAX),
        });
        let value = serde_json::to_value(payload).expect("payload should serialize");
        assert_eq!(value["ret_type"].as_str(), Some("void"));
        assert_eq!(value["params"][3]["type"].as_str(), Some("unsigned int"));
        assert_eq!(
            value["params"][5]["type"].as_str(),
            Some("__va_list_tag*"),
            "expected exact role signature to outrank generic diagnostic wrapper: {value:?}"
        );
    }

    #[test]
    fn semantic_type_fallback_payload_keeps_named_role_over_weak_context_override() {
        let summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x11aa),
            Some("quotearg_n_options".to_string()),
        );
        let compiled = r2sym::compile_named_native_worker_summary_artifact(&summary, true)
            .expect("expected named quoting summary artifact");
        let type_facts = r2types::FunctionTypeFacts {
            merged_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: r2types::parse_type_like_spec("int8_t*", 64),
                params: vec![
                    r2types::FunctionParamSpec {
                        name: "n".to_string(),
                        ty: r2types::parse_type_like_spec("int", 64),
                    },
                    r2types::FunctionParamSpec {
                        name: "arg".to_string(),
                        ty: r2types::parse_type_like_spec("int8_t*", 64),
                    },
                    r2types::FunctionParamSpec {
                        name: "argsize".to_string(),
                        ty: r2types::parse_type_like_spec("uint8_t", 64),
                    },
                    r2types::FunctionParamSpec {
                        name: "options".to_string(),
                        ty: r2types::parse_type_like_spec("quoting_options*", 64),
                    },
                ],
            }),
            ..r2types::FunctionTypeFacts::default()
        };
        let type_facts = r2engine::type_facts_with_summary_projection(
            type_facts,
            "quotearg_n_options",
            "x86-64",
            64,
            &compiled,
        );
        let function_facts = r2types::FunctionFacts::new(type_facts, Some(compiled.clone()))
            .with_assumptions(r2ssa::AssumptionSet::default());
        let scope_facts = types::empty_interproc_scope_facts();
        let payload = semantic_type_fallback_payload(SemanticTypeFallbackPayloadInput {
            function_name: "quotearg_n_options",
            arch_name: "x86-64",
            ptr_bits: 64,
            callconv: Some("amd64"),
            interproc: InterprocInferenceInput {
                iter: 1,
                max_iters: 1,
                converged: false,
                scope_facts: &scope_facts,
                scope_report: None,
            },
            compiled: &compiled,
            function_facts: &function_facts,
            symbolic_scope: None,
            apply_artifact_signature_hint: false,
            budget: TypeOutputBudget::new(64, usize::MAX, usize::MAX),
        });
        let value = serde_json::to_value(payload).expect("payload should serialize");
        assert_eq!(value["ret_type"].as_str(), Some("int8_t*"));
        assert_eq!(value["params"][2]["type"].as_str(), Some("size_t"));
        assert_eq!(
            value["params"][3]["type"].as_str(),
            Some("quoting_options*")
        );
    }

    #[test]
    fn mutation_plan_materializes_session_writeback_kinds() {
        let plan = r2types::TypeWritebackPlan {
            signature: r2types::InferredSignature {
                function_name: "dbg.sum".to_string(),
                signature: "int32_t dbg.sum(int32_t a);".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![r2types::InferredSignatureParam {
                    name: "a".to_string(),
                    param_type: "int32_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 90,
            },
            var_type_candidates: vec![r2types::VarTypeCandidate {
                name: "var_8h".to_string(),
                kind: "b".to_string(),
                delta: -8,
                var_type: "int32_t".to_string(),
                isarg: false,
                reg: None,
                size: 4,
                confidence: 95,
                source: r2types::WritebackSource::ExternalTypeDb,
                evidence: vec![r2types::WritebackEvidence::ExternalStackAnnotation],
            }],
            var_rename_candidates: vec![r2types::VarRenameCandidate {
                name: "arg1".to_string(),
                target_name: "a".to_string(),
                confidence: 96,
                source: r2types::WritebackSource::ExistingState,
                evidence: vec![r2types::WritebackEvidence::ExternalParamName],
            }],
            struct_decls: Vec::new(),
            global_type_links: Vec::new(),
            diagnostics: r2types::TypeWritebackDiagnostics::default(),
        };

        let mutation_plan = mutation_plan_from_writeback(
            &plan,
            TypeOutputBudget::new(usize::MAX, usize::MAX, usize::MAX),
        );
        let kinds = mutation_plan
            .mutations
            .iter()
            .map(|mutation| mutation.kind.as_str())
            .collect::<Vec<_>>();

        assert_eq!(
            kinds,
            vec!["signature", "callconv", "var", "var_type", "var_rename"]
        );
        assert_eq!(
            mutation_plan.mutations[0].signature.as_deref(),
            Some("int32_t dbg.sum(int32_t a);")
        );
        assert_eq!(
            mutation_plan.mutations[3].type_name.as_deref(),
            Some("int32_t")
        );
        assert_eq!(mutation_plan.mutations[4].old_name.as_deref(), Some("arg1"));
        let (ffi_mutations, strings) = ffi_mutations_from_session_plan(&mutation_plan);
        assert_eq!(ffi_mutations.len(), 5);
        assert_eq!(strings.len(), 12);
        assert_eq!(ffi_mutations[0].kind, R2SLEIGH_MUTATION_SIGNATURE);
        assert_eq!(ffi_mutations[1].kind, R2SLEIGH_MUTATION_CALLCONV);
        assert_eq!(ffi_mutations[2].kind, R2SLEIGH_MUTATION_VAR);
        assert_eq!(ffi_mutations[3].kind, R2SLEIGH_MUTATION_VAR_TYPE);
        assert_eq!(ffi_mutations[4].kind, R2SLEIGH_MUTATION_VAR_RENAME);
        assert_eq!(ffi_mutations[2].delta, -8);
        assert_eq!(ffi_mutations[2].var_kind, b'b' as c_char);
        assert_eq!(ffi_mutations[2].confidence, 95);

        let function_facts = r2types::FunctionFacts::default();
        let payload = writeback_plan_json(
            plan,
            InterprocSummaryJson {
                callsite_count: 0,
                iterations: 1,
                max_iterations: 1,
                converged: true,
                summary: None,
                summary_json: None,
                scope: None,
            },
            &function_facts,
            None,
            None,
            TypeOutputBudget::new(64, usize::MAX, usize::MAX),
        );
        let mut fact_strings = Vec::new();
        let (signature_fact, signature_params) =
            ffi_signature_fact_from_type_writeback(&payload, &mut fact_strings);
        assert_eq!(signature_fact.confidence, 96);
        assert_eq!(signature_fact.callconv_confidence, 90);
        assert_eq!(signature_fact.num_params, 1);
        assert_eq!(signature_fact.params, signature_params.as_ptr());
        assert_eq!(
            unsafe { CStr::from_ptr(signature_fact.signature) }.to_str(),
            Ok("int32_t dbg.sum(int32_t a);")
        );
        assert_eq!(
            unsafe { CStr::from_ptr(signature_params[0].type_name) }.to_str(),
            Ok("int32_t")
        );
    }

    #[test]
    fn mutation_plan_respects_global_type_link_budget() {
        let plan = r2types::TypeWritebackPlan {
            signature: r2types::InferredSignature {
                function_name: "dbg.links".to_string(),
                signature: "void dbg.links(void);".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 90,
            },
            var_type_candidates: Vec::new(),
            var_rename_candidates: Vec::new(),
            struct_decls: Vec::new(),
            global_type_links: vec![
                r2types::GlobalTypeLinkCandidate {
                    addr: 0x404000,
                    target_type: "struct a *".to_string(),
                    confidence: 90,
                    source: r2types::WritebackSource::ExternalTypeDb,
                },
                r2types::GlobalTypeLinkCandidate {
                    addr: 0x404008,
                    target_type: "struct b *".to_string(),
                    confidence: 90,
                    source: r2types::WritebackSource::ExternalTypeDb,
                },
            ],
            diagnostics: r2types::TypeWritebackDiagnostics::default(),
        };

        let limited =
            mutation_plan_from_writeback(&plan, TypeOutputBudget::new(1, usize::MAX, usize::MAX));
        let all =
            mutation_plan_from_writeback(&plan, TypeOutputBudget::new(2, usize::MAX, usize::MAX));

        assert_eq!(
            limited
                .mutations
                .iter()
                .filter(|mutation| mutation.kind == "type_link")
                .count(),
            1
        );
        assert_eq!(
            all.mutations
                .iter()
                .filter(|mutation| mutation.kind == "type_link")
                .count(),
            2
        );
        assert_eq!(
            limited.diagnostics,
            vec!["global type-link mutation plan truncated from 2 to 1 item(s)"]
        );
    }

    #[test]
    fn type_output_budget_truncates_declarations_and_budgeted_mutations() {
        let plan = r2types::TypeWritebackPlan {
            signature: r2types::InferredSignature {
                function_name: "dbg.types".to_string(),
                signature: "void dbg.types(void);".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 90,
            },
            var_type_candidates: Vec::new(),
            var_rename_candidates: Vec::new(),
            struct_decls: vec![
                r2types::StructDeclCandidate {
                    name: "struct a".to_string(),
                    decl: "typedef struct a { int x; } a;".to_string(),
                    confidence: 90,
                    source: r2types::StructDeclSource::ExternalTypeDb,
                    fields: Vec::new(),
                },
                r2types::StructDeclCandidate {
                    name: "struct b".to_string(),
                    decl: "typedef struct b { int y; } b;".to_string(),
                    confidence: 90,
                    source: r2types::StructDeclSource::ExternalTypeDb,
                    fields: Vec::new(),
                },
            ],
            global_type_links: Vec::new(),
            diagnostics: r2types::TypeWritebackDiagnostics::default(),
        };

        let budget = TypeOutputBudget::new(64, 1, 1);
        let mutation_plan = mutation_plan_from_writeback(&plan, budget);
        assert_eq!(
            mutation_plan
                .mutations
                .iter()
                .filter(|mutation| mutation.kind == "type_decl")
                .count(),
            1
        );
        assert!(mutation_plan.diagnostics.iter().any(|diagnostic| {
            diagnostic == "type declaration mutation plan truncated from 2 to 1 item(s)"
        }));
        let payload = writeback_plan_json(
            plan,
            InterprocSummaryJson {
                callsite_count: 0,
                iterations: 1,
                max_iterations: 1,
                converged: true,
                summary: None,
                summary_json: None,
                scope: None,
            },
            &r2types::FunctionFacts::default(),
            None,
            None,
            budget,
        );
        assert_eq!(payload.struct_decls.len(), 1);
        assert!(
            payload.diagnostics.warnings.iter().any(|warning| {
                warning == "type declaration report truncated from 2 to 1 item(s)"
            })
        );
    }

    #[test]
    fn decompile_ready_large_cfg_worker_keeps_real_decompile_path() {
        let compiled = test_large_cfg_semantic_artifact();
        let function_facts =
            r2types::FunctionFacts::new(r2types::FunctionTypeFacts::default(), Some(compiled));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 1,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let decision = r2engine::decompile_route_decision(
            "fcn.401000",
            &function_facts,
            None,
            &function_facts.types,
            &cfg_summary,
        );
        assert!(!matches!(
            decision.route,
            r2dec::SemanticRoutePlan::FallbackComment { .. }
        ));
    }

    #[test]
    fn semantic_fallback_text_reports_canonical_region_counts() {
        let compiled = test_large_cfg_semantic_artifact();
        let output = r2dec::semantic_fallback_comment("_401000", Some(&compiled))
            .expect("typed semantic fallback comment");
        assert!(output.contains("semantic fallback: worker slice in residual mode"));
        assert!(output.contains("regions=1"));
        assert!(output.contains("actionable_conditions=3"));
        assert!(output.contains("exact_conditions=3"));
    }

    #[test]
    fn non_x86_strong_evidence_can_clear_signature_threshold() {
        let params = vec![
            InferredParam {
                name: "arg0".to_string(),
                ty: r2dec::CType::void_ptr(),
                arg_index: 0,
                size_bytes: 8,
                evidence: TypeEvidence {
                    pointer_proven: 1,
                    ..TypeEvidence::default()
                },
            },
            InferredParam {
                name: "arg1".to_string(),
                ty: r2dec::CType::Int(32),
                arg_index: 1,
                size_bytes: 4,
                evidence: TypeEvidence {
                    scalar_proven: 1,
                    width_bits: 32,
                    ..TypeEvidence::default()
                },
            },
            InferredParam {
                name: "arg2".to_string(),
                ty: r2dec::CType::Bool,
                arg_index: 2,
                size_bytes: 1,
                evidence: TypeEvidence {
                    bool_like: 1,
                    width_bits: 8,
                    ..TypeEvidence::default()
                },
            },
        ];
        let confidence = compute_signature_confidence(
            &params,
            &r2dec::CType::Int(32),
            &TypeEvidence {
                scalar_proven: 1,
                width_bits: 32,
                ..TypeEvidence::default()
            },
        );
        assert!(confidence >= SIG_WRITEBACK_CONFIDENCE_MIN);
    }

    #[test]
    fn unknown_noisy_evidence_stays_below_signature_threshold() {
        let params = vec![InferredParam {
            name: "arg0".to_string(),
            ty: r2dec::CType::Unknown,
            arg_index: 0,
            size_bytes: 8,
            evidence: TypeEvidence {
                pointer_likely: 1,
                scalar_likely: 1,
                ..TypeEvidence::default()
            },
        }];
        let confidence =
            compute_signature_confidence(&params, &r2dec::CType::Unknown, &TypeEvidence::default());
        assert!(confidence < SIG_WRITEBACK_CONFIDENCE_MIN);
    }

    #[test]
    fn explicit_external_signature_context_yields_high_confidence() {
        let ctx = signature_spec(
            Some(r2dec::CType::Int(32)),
            vec![("items", Some(r2dec::CType::ptr(r2dec::CType::Int(8))))],
        );
        let confidence = explicit_signature_context_strength(&ctx);
        assert!(confidence >= SIG_WRITEBACK_CONFIDENCE_MIN);
    }

    #[test]
    fn non_x86_callconv_confidence_stays_low_when_signature_is_high() {
        let params = vec![
            InferredParam {
                name: "arg0".to_string(),
                ty: r2dec::CType::void_ptr(),
                arg_index: 0,
                size_bytes: 8,
                evidence: TypeEvidence {
                    pointer_proven: 1,
                    ..TypeEvidence::default()
                },
            },
            InferredParam {
                name: "arg1".to_string(),
                ty: r2dec::CType::Int(64),
                arg_index: 1,
                size_bytes: 8,
                evidence: TypeEvidence {
                    scalar_proven: 1,
                    width_bits: 64,
                    ..TypeEvidence::default()
                },
            },
        ];
        let sig_conf = compute_signature_confidence(
            &params,
            &r2dec::CType::Int(64),
            &TypeEvidence {
                scalar_proven: 1,
                width_bits: 64,
                ..TypeEvidence::default()
            },
        );
        let (callconv, callconv_conf) =
            compute_callconv_inference("aarch64", &std::collections::HashMap::new());
        assert!(sig_conf >= SIG_WRITEBACK_CONFIDENCE_MIN);
        assert!(callconv.is_empty());
        assert!(callconv_conf < CC_WRITEBACK_CONFIDENCE_MIN);
    }

    #[test]
    fn callconv_confidence_is_stable_for_same_register_histogram() {
        let mut first = std::collections::HashMap::new();
        first.insert("rdi".to_string(), 2);
        first.insert("rsi".to_string(), 2);
        first.insert("rdx".to_string(), 1);

        let mut second = std::collections::HashMap::new();
        second.insert("rdx".to_string(), 1);
        second.insert("rsi".to_string(), 2);
        second.insert("rdi".to_string(), 2);

        let inferred_first = infer_callconv_x86_64_from_counts(&first);
        let inferred_second = infer_callconv_x86_64_from_counts(&second);
        assert_eq!(inferred_first, inferred_second);
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;

    fn test_function_context(external_context: &CString) -> R2SleighFunctionContext {
        R2SleighFunctionContext {
            schema_version: 1,
            dirty_epoch: 0,
            context_hash: 0,
            type_dirty_epoch: 0,
            external_context_json: external_context.as_ptr(),
            signature_name: ptr::null(),
            signature_ret_type: ptr::null(),
            signature_callconv: ptr::null(),
            signature_noreturn: 0,
            params: ptr::null(),
            num_params: 0,
            vars: ptr::null(),
            num_vars: 0,
            base_types: ptr::null(),
            num_base_types: 0,
            assumptions_json: ptr::null(),
        }
    }

    fn test_session_input(
        ctx: *const R2ILContext,
        blocks: &[*const R2ILBlock],
        function_addr: u64,
        function_name: &CString,
        external_context: &CString,
        seeds: &[R2SleighInterprocSeed],
        interproc_max_iters: usize,
    ) -> R2SleighSessionInput {
        R2SleighSessionInput {
            ctx,
            blocks: blocks.as_ptr(),
            num_blocks: blocks.len(),
            function_addr,
            function_name: function_name.as_ptr(),
            function_context: test_function_context(external_context),
            interproc_scope: R2SleighInterprocScope {
                schema_version: 1,
                functions: ptr::null(),
                num_functions: 0,
                seeds: seeds.as_ptr(),
                num_seeds: seeds.len(),
            },
            debug_seed: R2SleighDebugSeed {
                schema_version: 1,
                seed_hash: 0,
            },
            budget: R2SleighBudgetConfig {
                schema_version: 1,
                interproc_iter: 1,
                interproc_max_iters,
                interproc_converged: 1,
                global_max_links: 64,
                max_type_decls: 64,
                max_mutations: 256,
            },
        }
    }

    #[test]
    fn test_init_x86_64() {
        let arch_cstr = CString::new("x86-64").unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        if ctx_ptr.is_null() {
            panic!("r2il_arch_initreturnedNULL");
        }
        let ctx = unsafe { &*ctx_ptr };

        if let Some(err) = &ctx.error {
            // panic!("Contexthaserror:{:?}",err);
            // It might error if sleigh-config data is bad, but we want to see it
            println!("Contextwarn/error:{:?}", err);
        }
        // If we have an error, we might still have a partial context or it failed completely
        // r2il_arch_init returns context with error set if loading failed

        if ctx.arch.is_none() {
            panic!("ArchisNone(loadingfailed)");
        }

        let profile_ptr = r2il_get_reg_profile(ctx_ptr);
        assert!(!profile_ptr.is_null());
        let profile = unsafe { CStr::from_ptr(profile_ptr).to_str().unwrap() };
        println!("Profile: {}", profile);
        assert!(profile.contains("=PC\tRIP"));

        r2il_string_free(profile_ptr);
        r2il_free(ctx_ptr);
    }

    #[test]
    #[cfg(feature = "arm")]
    fn create_disassembler_for_arch_arm64() {
        let (spec, disasm) = create_disassembler_for_arch("arm64").expect("arm64 disassembler");
        assert_eq!(spec.name, "aarch64");
        assert!(spec.addr_size > 0);
        assert_eq!(
            disasm.userop_name(0),
            userop_map_for_arch("arm64").get(&0).map(String::as_str)
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn create_disassembler_for_arch_riscv64() {
        let (spec, disasm) = create_disassembler_for_arch("riscv64").expect("riscv64 disassembler");
        assert_eq!(spec.name, "riscv64");
        assert!(spec.addr_size > 0);
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Little);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Little);
        assert_eq!(
            disasm.userop_name(0),
            userop_map_for_arch("riscv64").get(&0).map(String::as_str)
        );
    }

    #[test]
    #[cfg(feature = "arm")]
    fn r2il_arch_init_arm64_loaded() {
        let arch_cstr = CString::new("arm64").unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        assert!(!ctx_ptr.is_null(), "context pointer should not be null");
        assert_eq!(r2il_is_loaded(ctx_ptr), 1, "arm64 context should be loaded");
        r2il_free(ctx_ptr);
    }

    #[cfg(any(feature = "arm", feature = "mips"))]
    fn profile_for_arch(arch: &str) -> String {
        let arch_cstr = CString::new(arch).unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        assert!(!ctx_ptr.is_null(), "context pointer should not be null");
        assert_eq!(
            r2il_is_loaded(ctx_ptr),
            1,
            "{arch} context should be loaded"
        );
        let profile_ptr = r2il_get_reg_profile(ctx_ptr);
        assert!(
            !profile_ptr.is_null(),
            "register profile should not be null"
        );
        let profile = unsafe { CStr::from_ptr(profile_ptr).to_str().unwrap().to_string() };
        r2il_string_free(profile_ptr);
        r2il_free(ctx_ptr);
        profile
    }

    #[cfg(any(feature = "arm", feature = "mips"))]
    fn role_target(profile: &str, role: &str) -> Option<String> {
        profile
            .lines()
            .find_map(|line| line.strip_prefix(&format!("={}\t", role)))
            .map(str::trim)
            .map(str::to_string)
    }

    #[test]
    #[cfg(feature = "arm")]
    fn arm64_reg_profile_includes_required_arg_aliases() {
        let profile = profile_for_arch("arm64");
        for role in ["A0", "A1", "A2", "A3", "SN"] {
            assert!(
                role_target(&profile, role).is_some(),
                "arm64 profile should define ={role}"
            );
        }
    }

    #[test]
    #[cfg(feature = "arm")]
    fn arm64_reg_profile_includes_condition_flag_names() {
        let profile = profile_for_arch("arm64");
        for flag in ["cf", "zf", "nf", "vf"] {
            assert!(
                profile.contains(&format!("gpr\t{flag}\t.")),
                "arm64 profile should define {flag} register alias"
            );
        }
    }

    #[test]
    #[cfg(feature = "arm")]
    fn arm64_reg_profile_has_flag_role_aliases() {
        let profile = profile_for_arch("arm64");
        for role in ["CF", "ZF", "SF", "OF"] {
            assert!(
                role_target(&profile, role).is_some(),
                "arm64 profile should define ={role}"
            );
        }
    }

    #[test]
    #[cfg(feature = "arm")]
    fn arm64_reg_profile_includes_lr_alias() {
        let profile = profile_for_arch("arm64");
        assert!(
            profile.contains("gpr\tlr\t."),
            "arm64 profile should define lr alias"
        );
    }

    #[test]
    #[cfg(feature = "arm")]
    fn reg_profile_alias_roles_target_existing_registers() {
        let profile = profile_for_arch("arm64");
        for role in ["A0", "A1", "A2", "A3", "SN", "CF", "ZF", "SF", "OF"] {
            let Some(target) = role_target(&profile, role) else {
                continue;
            };
            assert!(
                profile.contains(&format!("gpr\t{}\t.", target)),
                "={role} points to missing register '{}'",
                target
            );
        }
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn create_disassembler_for_arch_riscv32() {
        let (spec, disasm) = create_disassembler_for_arch("riscv32").expect("riscv32 disassembler");
        assert_eq!(spec.name, "riscv32");
        assert!(spec.addr_size > 0);
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Little);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Little);
        assert_eq!(
            disasm.userop_name(0),
            userop_map_for_arch("riscv32").get(&0).map(String::as_str)
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn r2il_arch_init_riscv64_loaded() {
        let arch_cstr = CString::new("riscv64").unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        assert!(!ctx_ptr.is_null(), "context pointer should not be null");
        assert_eq!(
            r2il_is_loaded(ctx_ptr),
            1,
            "riscv64 context should be loaded"
        );
        r2il_free(ctx_ptr);
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn r2il_arch_init_riscv32_loaded() {
        let arch_cstr = CString::new("riscv32").unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        assert!(!ctx_ptr.is_null(), "context pointer should not be null");
        assert_eq!(
            r2il_is_loaded(ctx_ptr),
            1,
            "riscv32 context should be loaded"
        );
        r2il_free(ctx_ptr);
    }

    #[test]
    #[cfg(feature = "mips")]
    fn create_disassembler_for_arch_mips32be() {
        let (spec, disasm) =
            create_disassembler_for_arch("mips32be").expect("mips32be disassembler");
        assert_eq!(spec.name, "mips32be");
        assert!(spec.addr_size > 0);
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Big);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Big);
        assert_eq!(
            disasm.userop_name(0),
            userop_map_for_arch("mips32be").get(&0).map(String::as_str)
        );
    }

    #[test]
    #[cfg(feature = "mips")]
    fn r2il_arch_init_mips32be_loaded() {
        let arch_cstr = CString::new("mips32be").unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        assert!(!ctx_ptr.is_null(), "context pointer should not be null");
        assert_eq!(
            r2il_is_loaded(ctx_ptr),
            1,
            "mips32be context should be loaded"
        );
        r2il_free(ctx_ptr);
    }

    #[test]
    #[cfg(feature = "mips")]
    fn mips32be_reg_profile_includes_arg_roles() {
        let profile = profile_for_arch("mips32be");
        for role in ["PC", "SP", "A0", "A1", "A2", "A3", "R0"] {
            assert!(
                role_target(&profile, role).is_some(),
                "mips32be profile should define ={role}"
            );
        }
    }

    #[test]
    fn score_global_links_prefers_stronger_struct_type_signal() {
        let block = r2ssa::SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    src: r2ssa::SSAVar::new("const:404d00", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:v", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:base", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:base_4", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:v2", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:base_4", 1, 8),
                },
            ],
        };
        let struct_decls = vec![
            StructDeclCandidateJson {
                name: "sla_struct_aaaa".to_string(),
                decl: "typedef struct sla_struct_aaaa { int32_t f_0; } sla_struct_aaaa;"
                    .to_string(),
                confidence: 88,
                source: "local_inferred".to_string(),
                fields: vec![StructFieldCandidateJson {
                    name: "f_0".to_string(),
                    offset: 0,
                    field_type: "int32_t".to_string(),
                    confidence: 88,
                }],
            },
            StructDeclCandidateJson {
                name: "ext_struct".to_string(),
                decl: "typedef struct ext_struct { int32_t f_0; int32_t f_4; } ext_struct;"
                    .to_string(),
                confidence: 95,
                source: "external_type_db".to_string(),
                fields: vec![
                    StructFieldCandidateJson {
                        name: "f_0".to_string(),
                        offset: 0,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidateJson {
                        name: "f_4".to_string(),
                        offset: 4,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            },
        ];
        let var_types = vec![VarTypeCandidateJson {
            name: "arg0".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "struct ext_struct *".to_string(),
            isarg: true,
            reg: Some("rdi".to_string()),
            size: 8,
            confidence: 97,
            source: "signature_registry".to_string(),
            evidence: vec!["test".to_string()],
        }];

        let links = score_global_type_links(&[block], &struct_decls, &var_types, 64);
        assert_eq!(links.len(), 1);
        assert_eq!(links[0].addr, 0x404d00);
        assert_eq!(links[0].target_type, "struct ext_struct *");
    }

    #[test]
    fn score_global_links_skips_opaque_placeholder_struct_types() {
        let block = r2ssa::SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    src: r2ssa::SSAVar::new("const:404d00", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:v", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:base", 1, 8),
                },
            ],
        };
        let struct_decls = vec![StructDeclCandidateJson {
            name: "type_0x15a".to_string(),
            decl: "typedef struct type_0x15a { int32_t f_0; } type_0x15a;".to_string(),
            confidence: 95,
            source: "external_type_db".to_string(),
            fields: vec![StructFieldCandidateJson {
                name: "f_0".to_string(),
                offset: 0,
                field_type: "int32_t".to_string(),
                confidence: 95,
            }],
        }];
        let links = score_global_type_links(&[block], &struct_decls, &[], 64);
        assert!(
            links.is_empty(),
            "opaque type_0x placeholder structs must not produce global links"
        );
    }

    #[test]
    fn score_global_links_do_not_broadcast_strong_type_to_unrelated_globals() {
        let block = r2ssa::SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base_a", 1, 8),
                    src: r2ssa::SSAVar::new("const:404d00", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:a0", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:base_a", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:base_a_4", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base_a", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:base_a_4", 1, 8),
                    val: r2ssa::SSAVar::new("tmp:a1", 1, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base_b", 1, 8),
                    src: r2ssa::SSAVar::new("const:405000", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:b0", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:base_b", 1, 8),
                },
            ],
        };
        let struct_decls = vec![StructDeclCandidateJson {
            name: "ext_struct".to_string(),
            decl: "typedef struct ext_struct { int32_t f_0; int32_t f_4; } ext_struct;".to_string(),
            confidence: 95,
            source: "external_type_db".to_string(),
            fields: vec![
                StructFieldCandidateJson {
                    name: "f_0".to_string(),
                    offset: 0,
                    field_type: "int32_t".to_string(),
                    confidence: 95,
                },
                StructFieldCandidateJson {
                    name: "f_4".to_string(),
                    offset: 4,
                    field_type: "int32_t".to_string(),
                    confidence: 95,
                },
            ],
        }];
        let var_types = vec![VarTypeCandidateJson {
            name: "arg0".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "struct ext_struct *".to_string(),
            isarg: true,
            reg: Some("rdi".to_string()),
            size: 8,
            confidence: 99,
            source: "signature_registry".to_string(),
            evidence: vec!["test".to_string()],
        }];

        let links = score_global_type_links(&[block], &struct_decls, &var_types, 64);
        assert_eq!(
            links.len(),
            1,
            "unrelated globals must not inherit the same type"
        );
        assert_eq!(links[0].addr, 0x404d00);
        assert_eq!(links[0].target_type, "struct ext_struct *");
    }

    #[test]
    fn interproc_summary_serializes_extended_fields() {
        let summary = InterprocSummaryJson {
            callsite_count: 3,
            iterations: 4,
            max_iterations: 12,
            converged: false,
            summary: None,
            summary_json: None,
            scope: Some(serde_json::json!({"mode":"worklist"})),
        };
        let value = serde_json::to_value(summary).expect("serialize interproc");
        assert_eq!(value["iterations"], 4);
        assert_eq!(value["max_iterations"], 12);
        assert_eq!(value["converged"], false);
        assert_eq!(value["scope"]["mode"], "worklist");
    }

    #[test]
    fn session_analyze_uses_typed_interproc_seed_for_wrapper_return_type() {
        let arch = CString::new("x86-64").expect("valid arch");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x2000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode {
                space: r2il::SpaceId::Register,
                offset: 0,
                size: 8,
                meta: None,
            },
        });
        let raw_block = Box::into_raw(Box::new(block));
        let blocks = [raw_block as *const R2ILBlock];

        let func_name = CString::new("sym.alloc_wrapper").expect("valid function name");
        let external_context = CString::new("{}").expect("valid context");
        let seed_name = CString::new("sym.imp.malloc").expect("valid seed name");
        let seeds = [R2SleighInterprocSeed {
            id: 8192,
            name: seed_name.as_ptr(),
            arg_count_hint: 0,
            has_arg_count_hint: 0,
        }];
        let input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &func_name,
            &external_context,
            &seeds,
            4,
        );
        let session = r2sleigh_session_analyze(&input);
        assert!(!session.is_null(), "session should not be null");
        let payload_ptr = r2sleigh_session_result_type_writeback_json(session);
        assert!(
            !payload_ptr.is_null(),
            "writeback payload should not be null"
        );
        let output = unsafe { CStr::from_ptr(payload_ptr) }
            .to_string_lossy()
            .to_string();
        let payload: serde_json::Value =
            serde_json::from_str(&output).expect("payload should parse");

        r2sleigh_session_result_free(session);
        r2il_block_free(raw_block);
        r2il_free(ctx);

        assert_eq!(
            payload["interproc"]["summary"]["return_relation"].as_str(),
            Some("HeapAlloc"),
            "payload={output}"
        );
        assert!(
            matches!(payload["ret_type"].as_str(), Some("void *" | "void*")),
            "payload={output}"
        );
    }

    #[test]
    fn session_interproc_summary_returns_typed_root_summary() {
        let arch = CString::new("x86-64").expect("valid arch");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x2000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode {
                space: r2il::SpaceId::Register,
                offset: 0,
                size: 8,
                meta: None,
            },
        });
        let raw_block = Box::into_raw(Box::new(block));
        let blocks = [raw_block as *const R2ILBlock];

        let func_name = CString::new("sym.alloc_wrapper").expect("valid function name");
        let external_context = CString::new("{}").expect("valid context");
        let seed_name = CString::new("sym.imp.malloc").expect("valid seed name");
        let seeds = [R2SleighInterprocSeed {
            id: 8192,
            name: seed_name.as_ptr(),
            arg_count_hint: 0,
            has_arg_count_hint: 0,
        }];
        let input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &func_name,
            &external_context,
            &seeds,
            4,
        );
        let out = r2sleigh_session_interproc_summary_json(&input);
        assert!(!out.is_null(), "summary json should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();
        let payload: serde_json::Value =
            serde_json::from_str(&output).expect("summary should parse");

        r2il_string_free(out);
        r2il_block_free(raw_block);
        r2il_free(ctx);

        assert_eq!(payload["return_relation"].as_str(), Some("HeapAlloc"));
    }

    #[test]
    fn function_analysis_artifact_cache_key_changes_with_interproc_scope() {
        let arch = CString::new("x86-64").expect("valid arch");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x2000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode {
                space: r2il::SpaceId::Register,
                offset: 0,
                size: 8,
                meta: None,
            },
        });
        let raw_block = Box::into_raw(Box::new(block));
        let blocks = [raw_block as *const R2ILBlock];

        let func_name = CString::new("sym.alloc_wrapper").expect("valid function name");
        let external_context = CString::new("{}").expect("valid context");
        let seed_name = CString::new("sym.imp.malloc").expect("valid seed name");
        let seeds = [R2SleighInterprocSeed {
            id: 8192,
            name: seed_name.as_ptr(),
            arg_count_hint: 0,
            has_arg_count_hint: 0,
        }];
        let empty_input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &func_name,
            &external_context,
            &[],
            1,
        );
        let seeded_input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &func_name,
            &external_context,
            &seeds,
            1,
        );
        let root_key = r2sleigh_session_artifact_cache_key(&empty_input);
        let seeded_key = r2sleigh_session_artifact_cache_key(&seeded_input);

        r2il_block_free(raw_block);
        r2il_free(ctx);

        assert_ne!(root_key, 0);
        assert_ne!(seeded_key, 0);
        assert_ne!(root_key, seeded_key);
    }

    #[test]
    fn function_analysis_artifact_cache_key_changes_with_interproc_budget() {
        let arch = CString::new("x86-64").expect("valid arch");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x2000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode {
                space: r2il::SpaceId::Register,
                offset: 0,
                size: 8,
                meta: None,
            },
        });
        let raw_block = Box::into_raw(Box::new(block));
        let blocks = [raw_block as *const R2ILBlock];

        let func_name = CString::new("sym.alloc_wrapper").expect("valid function name");
        let external_context = CString::new("{}").expect("valid context");
        let seed_name = CString::new("sym.imp.malloc").expect("valid seed name");
        let seeds = [R2SleighInterprocSeed {
            id: 8192,
            name: seed_name.as_ptr(),
            arg_count_hint: 0,
            has_arg_count_hint: 0,
        }];
        let low_budget_input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &func_name,
            &external_context,
            &seeds,
            1,
        );
        let high_budget_input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &func_name,
            &external_context,
            &seeds,
            4,
        );
        let low_budget_key = r2sleigh_session_artifact_cache_key(&low_budget_input);
        let high_budget_key = r2sleigh_session_artifact_cache_key(&high_budget_input);

        r2il_block_free(raw_block);
        r2il_free(ctx);

        assert_ne!(low_budget_key, 0);
        assert_ne!(high_budget_key, 0);
        assert_ne!(low_budget_key, high_budget_key);
    }

    #[test]
    fn function_analysis_artifact_cache_key_changes_with_function_name() {
        let arch = CString::new("x86-64").expect("valid arch");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Return {
            target: Varnode {
                space: r2il::SpaceId::Register,
                offset: 0,
                size: 8,
                meta: None,
            },
        });
        let raw_block = Box::into_raw(Box::new(block));
        let blocks = [raw_block as *const R2ILBlock];

        let first_name = CString::new("sym.first").expect("valid function name");
        let second_name = CString::new("sym.second").expect("valid function name");
        let external_context = CString::new("{}").expect("valid context");
        let first_input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &first_name,
            &external_context,
            &[],
            1,
        );
        let second_input = test_session_input(
            ctx,
            &blocks,
            0x401000,
            &second_name,
            &external_context,
            &[],
            1,
        );
        let first_key = r2sleigh_session_artifact_cache_key(&first_input);
        let second_key = r2sleigh_session_artifact_cache_key(&second_input);

        r2il_block_free(raw_block);
        r2il_free(ctx);

        assert_ne!(first_key, 0);
        assert_ne!(second_key, 0);
        assert_ne!(first_key, second_key);
    }

    #[test]
    fn direct_call_targets_json_reports_constant_call_target() {
        let arch = CString::new("x86-64").expect("valid arch");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x2000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode {
                space: r2il::SpaceId::Register,
                offset: 0,
                size: 8,
                meta: None,
            },
        });
        let raw_block = Box::into_raw(Box::new(block));
        let blocks = [raw_block as *const R2ILBlock];
        let func_name = CString::new("sym.alloc_wrapper").expect("valid function name");

        let out = r2sleigh_get_direct_call_targets_json(
            ctx,
            blocks.as_ptr(),
            blocks.len(),
            0x401000,
            func_name.as_ptr(),
        );
        assert!(!out.is_null(), "direct target payload should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();
        let targets: Vec<u64> = serde_json::from_str(&output).expect("targets should parse");

        r2il_string_free(out);
        r2il_block_free(raw_block);
        r2il_free(ctx);

        assert_eq!(targets, vec![0x2000], "payload={output}");
    }

    #[test]
    #[cfg(feature = "arm")]
    fn infer_structs_from_ssa_recovers_arm64_spilled_struct_fields() {
        let arch = ArchSpec::new("aarch64");
        let block = r2ssa::SSABlock {
            addr: 0x100000bb4,
            size: 52,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("X9", 2, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                },
            ],
        };

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) =
            infer_structs_from_ssa(&[block], Some(&arch), 64, &mut diagnostics);

        assert!(!struct_decls.is_empty(), "expected inferred struct decls");
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0), "expected offset 0 field");
        assert!(fields.contains_key(&0x30), "expected offset 0x30 field");
    }

    #[test]
    #[cfg(feature = "arm")]
    fn enrich_decompiler_type_context_prefers_stronger_local_struct_with_offset_zero_field() {
        let arch = ArchSpec::new("aarch64");
        let block = r2ssa::SSABlock {
            addr: 0x100000bb4,
            size: 52,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("X9", 2, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                },
            ],
        };

        let (signature, type_db) = enrich_decompiler_type_context(
            &[block],
            Some(&arch),
            64,
            Some(signature_spec(
                Some(r2dec::CType::Int(64)),
                vec![
                    (
                        "arg1",
                        Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Void))),
                    ),
                    ("arg2", Some(r2dec::CType::Int(32))),
                ],
            )),
            r2types::ExternalTypeDb::default(),
        );

        let struct_name = signature
            .and_then(|sig| sig.params.first().and_then(|param| param.ty.clone()))
            .and_then(|ty| match ty {
                r2types::CTypeLike::Pointer(inner) => match *inner {
                    r2types::CTypeLike::Struct(name) => Some(name),
                    _ => None,
                },
                _ => None,
            })
            .expect("expected arg0 to resolve to pointer-to-struct");

        let key = struct_name.to_ascii_lowercase();
        let st = type_db
            .structs
            .get(&key)
            .expect("resolved struct in type db");
        assert!(
            st.fields.contains_key(&0),
            "chosen struct override should retain offset-0 field, got {st:?}"
        );
        assert!(
            st.fields.contains_key(&0x30),
            "chosen struct override should retain offset-0x30 field, got {st:?}"
        );
    }

    #[test]
    #[cfg(feature = "arm")]
    fn infer_structs_from_ssa_recovers_arm64_indexed_struct_fields() {
        let arch = ArchSpec::new("aarch64");
        let block = r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("X10", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("X10", 4, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
            ],
        };

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) =
            infer_structs_from_ssa(&[block], Some(&arch), 64, &mut diagnostics);

        assert!(!struct_decls.is_empty(), "expected inferred struct decls");
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0x8), "expected offset 0x8 field");
        assert!(fields.contains_key(&0x34), "expected offset 0x34 field");
    }

    fn live_arm64_struct_array_index_block() -> r2ssa::SSABlock {
        r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X11", 1, 8),
                    src: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                    src: r2ssa::SSAVar::new("X10", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                    src: r2ssa::SSAVar::new("X10", 4, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 6, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("X9", 6, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
            ],
        }
    }

    fn live_arm64_array_index_block(is_negative: bool) -> r2ssa::SSABlock {
        let addr_op = if is_negative {
            r2ssa::SSAOp::IntSub {
                dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                a: r2ssa::SSAVar::new("X8", 1, 8),
                b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
            }
        } else {
            r2ssa::SSAOp::IntAdd {
                dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                a: r2ssa::SSAVar::new("X8", 1, 8),
                b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
            }
        };

        r2ssa::SSABlock {
            addr: 0x100000d80,
            size: 72,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 1, 1),
                    a: r2ssa::SSAVar::new("X8", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                r2ssa::SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 1, 1),
                    a: r2ssa::SSAVar::new("X8", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                addr_op,
                r2ssa::SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("W8", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X0", 1, 8),
                    src: r2ssa::SSAVar::new("W8", 1, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("PC", 1, 8),
                    src: r2ssa::SSAVar::new("X30", 0, 8),
                },
                r2ssa::SSAOp::Return {
                    target: r2ssa::SSAVar::new("PC", 1, 8),
                },
            ],
        }
    }

    fn observed_live_arm64_struct_array_index_block_full() -> r2ssa::SSABlock {
        r2ssa::SSABlock {
            addr: 0x100000e40,
            size: 96,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:10", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X11", 1, 8),
                    src: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 2, 8),
                    a: r2ssa::SSAVar::new("X10", 1, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                    src: r2ssa::SSAVar::new("X10", 2, 8),
                },
                r2ssa::SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 1, 1),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                r2ssa::SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 1, 1),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 1, 8),
                },
                r2ssa::SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 1, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 2, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    val: r2ssa::SSAVar::new("W8", 0, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X9", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X9", 4, 8),
                    a: r2ssa::SSAVar::new("X9", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                    src: r2ssa::SSAVar::new("X9", 4, 8),
                },
                r2ssa::SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 2, 1),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                r2ssa::SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 2, 1),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    a: r2ssa::SSAVar::new("X8", 2, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 2, 8),
                },
                r2ssa::SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 2, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 2, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                    a: r2ssa::SSAVar::new("X8", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 5, 8),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X8", 4, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 2, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X9", 5, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("X10", 3, 8),
                    src: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                },
                r2ssa::SSAOp::IntMult {
                    dst: r2ssa::SSAVar::new("X10", 4, 8),
                    a: r2ssa::SSAVar::new("X10", 3, 8),
                    b: r2ssa::SSAVar::new("const:38", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                    src: r2ssa::SSAVar::new("X10", 4, 8),
                },
                r2ssa::SSAOp::IntCarry {
                    dst: r2ssa::SSAVar::new("TMPCY", 3, 1),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                r2ssa::SSAOp::IntSCarry {
                    dst: r2ssa::SSAVar::new("TMPOV", 3, 1),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:12380", 3, 8),
                },
                r2ssa::SSAOp::IntSLess {
                    dst: r2ssa::SSAVar::new("TMPNG", 3, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::IntEqual {
                    dst: r2ssa::SSAVar::new("TMPZR", 3, 1),
                    a: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                    b: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X9", 6, 8),
                    src: r2ssa::SSAVar::new("tmp:12480", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                    a: r2ssa::SSAVar::new("X9", 6, 8),
                    b: r2ssa::SSAVar::new("const:34", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
                },
                r2ssa::SSAOp::IntZExt {
                    dst: r2ssa::SSAVar::new("X9", 7, 8),
                    src: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                },
            ],
        }
    }

    #[test]
    fn infer_structs_from_ssa_recovers_live_arm64_struct_array_index_pattern() {
        let arch = ArchSpec::new("aarch64");
        let block = live_arm64_struct_array_index_block();

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) =
            infer_structs_from_ssa(&[block], Some(&arch), 64, &mut diagnostics);

        assert!(
            !struct_decls.is_empty(),
            "expected inferred struct decls for live indexed-member pattern"
        );
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0x8), "expected offset 0x8 field");
        assert!(fields.contains_key(&0x34), "expected offset 0x34 field");
    }

    #[test]
    fn infer_structs_from_ssa_recovers_observed_live_arm64_struct_array_index_pattern() {
        let arch = ArchSpec::new("aarch64");
        let mut block = observed_live_arm64_struct_array_index_block_full();
        block.ops.extend([
            r2ssa::SSAOp::IntAdd {
                dst: r2ssa::SSAVar::new("tmp:sum", 1, 8),
                a: r2ssa::SSAVar::new("X8", 4, 8),
                b: r2ssa::SSAVar::new("X9", 7, 8),
            },
            r2ssa::SSAOp::Copy {
                dst: r2ssa::SSAVar::new("X0", 1, 8),
                src: r2ssa::SSAVar::new("tmp:sum", 1, 8),
            },
            r2ssa::SSAOp::Copy {
                dst: r2ssa::SSAVar::new("PC", 1, 8),
                src: r2ssa::SSAVar::new("X30", 0, 8),
            },
            r2ssa::SSAOp::Return {
                target: r2ssa::SSAVar::new("PC", 1, 8),
            },
        ]);

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) =
            infer_structs_from_ssa(&[block], Some(&arch), 64, &mut diagnostics);

        assert!(
            !struct_decls.is_empty(),
            "expected inferred struct decls for observed live indexed-member pattern; diagnostics={diagnostics:?}"
        );
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0x8), "expected offset 0x8 field");
        assert!(fields.contains_key(&0x34), "expected offset 0x34 field");
    }

    #[test]
    fn infer_structs_from_semantic_accesses_recovers_observed_live_arm64_struct_array_pattern() {
        let block = observed_live_arm64_struct_array_index_block_full();
        let raw = r2il::R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![r2il::R2ILOp::Return {
                target: r2il::Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = r2ssa::SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) = infer_structs_from_semantic_accesses(
            &func,
            &r2dec::DecompilerConfig::aarch64(),
            64,
            &mut diagnostics,
        );

        assert!(
            !struct_decls.is_empty(),
            "expected semantic access supplement to infer struct decls; diagnostics={diagnostics:?}"
        );
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0x8), "expected offset 0x8 field");
        assert!(fields.contains_key(&0x34), "expected offset 0x34 field");
    }

    #[test]
    fn infer_structs_from_semantic_accesses_recovers_observed_live_x86_struct_field_pattern() {
        let block = r2ssa::SSABlock {
            addr: 0x401667,
            size: 42,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RBP", 1, 8),
                    src: r2ssa::SSAVar::new("RSP", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RBP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("EDX", 1, 4),
                    src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("EDX", 1, 4),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 2, 8),
                    src: r2ssa::SSAVar::new("tmp:11f80", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 2, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 4, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 3, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RAX", 2, 8),
                },
            ],
        };
        let raw = r2il::R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![r2il::R2ILOp::Return {
                target: r2il::Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = r2ssa::SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym.test_struct_field");

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) = infer_structs_from_semantic_accesses(
            &func,
            &r2dec::DecompilerConfig::x86_64(),
            64,
            &mut diagnostics,
        );

        assert!(
            !struct_decls.is_empty(),
            "expected x86 semantic access supplement to infer struct decls; diagnostics={diagnostics:?}"
        );
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0x0), "expected offset 0x0 field");
        assert!(fields.contains_key(&0x30), "expected offset 0x30 field");
    }

    #[test]
    fn infer_structs_from_semantic_accesses_recovers_observed_live_x86_struct_array_pattern() {
        let block = r2ssa::SSABlock {
            addr: 0x40182f,
            size: 124,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RSP", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 0, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("RSP", 1, 8),
                    val: r2ssa::SSAVar::new("RBP", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    a: r2ssa::SSAVar::new("RSP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                    val: r2ssa::SSAVar::new("RDI", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    a: r2ssa::SSAVar::new("RSP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6a80", 1, 4),
                    src: r2ssa::SSAVar::new("ESI", 0, 4),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                    val: r2ssa::SSAVar::new("tmp:6a80", 1, 4),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    a: r2ssa::SSAVar::new("RSP", 1, 8),
                    b: r2ssa::SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6a80", 2, 4),
                    src: r2ssa::SSAVar::new("EDX", 0, 4),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                    val: r2ssa::SSAVar::new("tmp:6a80", 2, 4),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 2, 8),
                },
                r2ssa::SSAOp::IntSExt {
                    dst: r2ssa::SSAVar::new("RDX", 1, 8),
                    src: r2ssa::SSAVar::new("tmp:11f00", 1, 4),
                },
                r2ssa::SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 3, 8),
                    a: r2ssa::SSAVar::new("RDX", 1, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("RAX", 4, 8),
                    a: r2ssa::SSAVar::new("RAX", 3, 8),
                    b: r2ssa::SSAVar::new("RDX", 1, 8),
                },
                r2ssa::SSAOp::IntLeft {
                    dst: r2ssa::SSAVar::new("RAX", 5, 8),
                    a: r2ssa::SSAVar::new("RAX", 4, 8),
                    b: r2ssa::SSAVar::new("const:3", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("RDX", 3, 8),
                    a: r2ssa::SSAVar::new("RAX", 5, 8),
                    b: r2ssa::SSAVar::new("tmp:11f80", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:4700", 7, 8),
                    a: r2ssa::SSAVar::new("RDX", 3, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:4700", 7, 8),
                    val: r2ssa::SSAVar::new("tmp:11f00", 2, 4),
                },
            ],
        };
        let raw = r2il::R2ILBlock {
            addr: block.addr,
            size: block.size,
            ops: vec![r2il::R2ILOp::Return {
                target: r2il::Varnode::constant(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = r2ssa::SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym.test_struct_array_index");

        let mut diagnostics = TypeWritebackDiagnosticsJson::default();
        let (struct_decls, slot_types, slot_fields) = infer_structs_from_semantic_accesses(
            &func,
            &r2dec::DecompilerConfig::x86_64(),
            64,
            &mut diagnostics,
        );

        assert!(
            !struct_decls.is_empty(),
            "expected x86 semantic access supplement to infer struct decls; diagnostics={diagnostics:?}"
        );
        assert!(slot_types.contains_key(&0), "expected arg0 slot override");
        let fields = slot_fields.get(&0).expect("slot 0 field profile");
        assert!(fields.contains_key(&0x8), "expected offset 0x8 field");
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lifted_x86_struct_array_analysis_artifact_surfaces_local_struct_override() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let bytes = decode_hex(
            "f30f1efa554889e548897df88975f48955f08b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801c28b45f08942088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b48088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b403401c85dc3",
        );
        let block = disasm
            .lift_block(&bytes, 0x40182f, 124)
            .expect("lifted block");
        let pattern_ssa_func =
            r2ssa::SSAFunction::from_blocks_for_patterns(std::slice::from_ref(&block), Some(&arch))
                .expect("pattern ssa")
                .with_name("dbg.test_struct_array_index");
        let pattern_ssa_blocks: Vec<r2ssa::SSABlock> = pattern_ssa_func
            .blocks()
            .map(|block| r2ssa::SSABlock {
                addr: block.addr,
                size: block.size,
                ops: block.ops.clone(),
            })
            .collect();
        let mut semantic_diagnostics = TypeWritebackDiagnosticsJson::default();
        let semantic_structs = infer_structs_from_semantic_accesses(
            &pattern_ssa_func,
            &r2dec::DecompilerConfig::x86_64(),
            64,
            &mut semantic_diagnostics,
        );
        let mut raw_diagnostics = TypeWritebackDiagnosticsJson::default();
        let raw_structs =
            infer_structs_from_ssa(&pattern_ssa_blocks, Some(&arch), 64, &mut raw_diagnostics);
        let artifact = crate::types::build_detached_function_analysis_artifact(
            &[block],
            "dbg.test_struct_array_index",
            Some(&arch),
            64,
            false,
            &std::collections::HashMap::new(),
            "{}",
        )
        .expect("analysis artifact");

        let rendered = artifact
            .function_facts
            .types
            .merged_signature
            .as_ref()
            .and_then(|sig| sig.params.first())
            .and_then(|param| param.ty.as_ref())
            .map(type_like_to_ctype)
            .map(|ty| ty.to_string())
            .unwrap_or_default();
        let compact = rendered.replace(' ', "");
        assert!(
            compact.starts_with("struct")
                && compact.ends_with('*')
                && !compact.eq_ignore_ascii_case("void*"),
            "expected lifted-byte x86 artifact to override arg0 to a struct pointer, got signature={:?}, slot_overrides={:?}, slot_fields={:?}, type_db={:?}, semantic_structs={:?}, semantic_diagnostics={:?}, raw_structs={:?}, raw_diagnostics={:?}, pattern_ssa_blocks={:?}",
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs,
            semantic_structs,
            semantic_diagnostics,
            raw_structs,
            raw_diagnostics,
            pattern_ssa_blocks
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lifted_x86_struct_array_detached_artifact_with_live_context_keeps_struct_override() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let bytes = decode_hex(
            "f30f1efa554889e548897df88975f48955f08b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801c28b45f08942088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b48088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b403401c85dc3",
        );
        let block = disasm
            .lift_block(&bytes, 0x40182f, 124)
            .expect("lifted block");
        let reg_type_hints =
            crate::types::collect_register_type_hints(std::slice::from_ref(&block), &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.test_struct_array_index",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "arr", "type": "void *"},
                    {"name": "idx", "type": "int32_t"},
                    {"name": "v", "type": "int32_t"}
                ]
            },
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &[block],
            "dbg.test_struct_array_index",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        assert_eq!(
            artifact
                .function_facts
                .types
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_420703e08f70f00e *"),
            "expected live-context detached artifact to keep the local struct override, got merged_signature={:?}, slot_overrides={:?}, slot_fields={:?}, type_db={:?}",
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lifted_x86_struct_array_detached_artifact_keeps_sparse_field_offsets() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let bytes = decode_hex(
            "f30f1efa554889e548897df88975f48955f08b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801c28b45f08942088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b48088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b403401c85dc3",
        );
        let block = disasm
            .lift_block(&bytes, 0x40182f, 124)
            .expect("lifted block");
        let reg_type_hints =
            crate::types::collect_register_type_hints(std::slice::from_ref(&block), &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.test_struct_array_index",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "arr", "type": "void *"},
                    {"name": "idx", "type": "int32_t"},
                    {"name": "v", "type": "int32_t"}
                ]
            },
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &[block],
            "dbg.test_struct_array_index",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let struct_decl = artifact
            .writeback_plan
            .struct_decls
            .iter()
            .find(|decl| decl.name == "sla_struct_420703e08f70f00e")
            .expect("expected local struct decl");
        let field_offsets = struct_decl
            .fields
            .iter()
            .map(|field| (field.offset, field.name.as_str()))
            .collect::<Vec<_>>();
        assert_eq!(
            field_offsets,
            vec![(8, "f_8"), (0x34, "f_34")],
            "expected sparse field offsets to survive writeback plan, got {:?}",
            struct_decl.fields
        );

        let db_struct = artifact
            .function_facts
            .types
            .external_type_db
            .structs
            .get("sla_struct_420703e08f70f00e")
            .expect("expected merged struct in type db");
        assert_eq!(
            db_struct.fields.keys().copied().collect::<Vec<_>>(),
            vec![8, 0x34],
            "expected sparse field offsets in merged type db, got {:?}",
            db_struct.fields
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_struct_array_artifact_drives_member_load_return_rendering() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let bytes = decode_hex(
            "f30f1efa554889e548897df88975f48955f08b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801c28b45f08942088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b48088b45f44863d04889d048c1e0034829d048c1e0034889c2488b45f84801d08b403401c85dc3",
        );
        let block = disasm
            .lift_block(&bytes, 0x40182f, 124)
            .expect("lifted block");
        let reg_type_hints =
            crate::types::collect_register_type_hints(std::slice::from_ref(&block), &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.test_struct_array_index",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "arr", "type": "void *"},
                    {"name": "idx", "type": "int32_t"},
                    {"name": "v", "type": "int32_t"}
                ]
            },
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &[block],
            "dbg.test_struct_array_index",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([
            (0x401140, "sym.imp.memcpy".to_string()),
            (0x401150, "sym.imp.malloc".to_string()),
        ]));
        decompiler.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.malloc".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Unsigned,
                    }],
                    variadic: false,
                },
            ),
            (
                "sym.imp.memcpy".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Int {
                            bits: 64,
                            signedness: r2types::Signedness::Unsigned,
                        },
                    ],
                    variadic: false,
                },
            ),
        ]));
        let output = decompiler.decompile(&artifact.ssa_func);
        let pattern_ssa_blocks = artifact.pattern_ssa_func.local_ssa_blocks();
        let tail_ops: Vec<_> = artifact
            .pattern_ssa_func
            .local_ssa_blocks()
            .first()
            .map(|block| block.ops.iter().rev().take(16).cloned().collect::<Vec<_>>())
            .unwrap_or_default();
        let mut raw = r2il::R2ILBlock::new(0x40182f, 124);
        raw.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(0, 8),
        });
        let mut manual_func =
            r2ssa::SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        manual_func
            .get_block_mut(0x40182f)
            .expect("entry block")
            .ops = pattern_ssa_blocks[0].ops.clone();
        manual_func = manual_func.with_name("dbg.test_struct_array_index");
        let mut manual_decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        manual_decompiler.set_function_facts(artifact.function_facts.clone());
        let manual_output = manual_decompiler.decompile(&manual_func);

        assert!(
            output.contains("[idx].f_8"),
            "expected detached artifact store rendering in decompiled output, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
        assert!(
            output.contains("[idx].f_34"),
            "expected detached artifact load rendering in decompiled output, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
        assert!(
            output.contains("return arr[idx].f_8 + arr[idx].f_34;")
                || output.contains("return arr[idx].f_34 + arr[idx].f_8;"),
            "expected detached artifact return to preserve both member loads, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
        assert!(
            !output.contains("local_c ="),
            "dead x86 stack-home index carrier should not leak into decompiled output, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
        assert!(
            !output.contains("local_"),
            "autogenerated x86 stack-home locals should not leak into decompiled output, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
        assert!(
            output.contains("arr[idx].f_8 = v;"),
            "expected detached artifact store to inline the parameter value, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
        assert!(
            !output.contains("(int64_t)arr[idx].f_34"),
            "x86 scalar return should not widen the member load in decompiled output, got:\n{output}\nmanual_output:\n{manual_output}\ntail_ops={tail_ops:?}\nregister_params={:?}\nmerged_signature={:?}\nslot_overrides={:?}\nslot_fields={:?}\ntype_db={:?}",
            artifact.function_facts.types.register_params,
            artifact.function_facts.types.merged_signature,
            artifact.function_facts.types.slot_type_overrides,
            artifact.function_facts.types.slot_field_profiles,
            artifact.function_facts.types.external_type_db.structs
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_alloc_and_copy_artifact_keeps_authoritative_two_param_signature() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let bytes = decode_hex(
            "f30f1efa554889e54883ec2048897de8488975e0488b45e04883c0014889c7e87bfdffff488945f848837df8007507b800000000eb29488b55e0488b4de8488b45f84889ce4889c7e842fdffff488b55f8488b45e04801d0c60000488b45f8c9c3",
        );
        let block = disasm
            .lift_block(&bytes, 0x4013b1, 97)
            .expect("lifted block");
        let reg_type_hints =
            crate::types::collect_register_type_hints(std::slice::from_ref(&block), &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.alloc_and_copy",
                "ret": "int8_t *",
                "callconv": "amd64",
                "params": [
                    {"name": "src", "type": "int8_t *"},
                    {"name": "len", "type": "uint8_t"}
                ]
            },
            "vars": [
                {"kind":"register","name":"src","type":"int8_t *","reg":"rdi","param_index":0},
                {"kind":"register","name":"len","type":"uint8_t","reg":"rsi","param_index":1},
                {"kind":"stack","name":"src_home","type":"int8_t *","base":"rbp","offset":-24,"role":"param_home","param_index":0,"param_name":"src","source_reg":"rdi"},
                {"kind":"stack","name":"len_home","type":"uint8_t","base":"rbp","offset":-32,"role":"param_home","param_index":1,"param_name":"len","source_reg":"rsi"},
                {"kind":"stack","name":"buf","type":"int8_t *","base":"rbp","offset":-8,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &[block],
            "dbg.alloc_and_copy",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        assert_eq!(
            artifact
                .function_facts
                .types
                .merged_signature
                .as_ref()
                .expect("merged signature")
                .params
                .len(),
            2,
            "expected authoritative external signature to keep two params, got merged_signature={:?}",
            artifact.function_facts.types.merged_signature
        );
        assert_eq!(
            artifact.writeback_plan.signature.params.len(),
            2,
            "expected writeback signature to stay aligned with merged signature, got {:?}",
            artifact.writeback_plan.signature.params
        );
        assert_eq!(
            artifact.writeback_plan.signature.params[0].name, "src",
            "expected first param name to come from external signature, got merged_signature={:?}, writeback_signature={:?}",
            artifact.function_facts.types.merged_signature, artifact.writeback_plan.signature
        );
        assert_eq!(
            artifact.writeback_plan.signature.params[1].name, "len",
            "expected second param name to come from external signature, got merged_signature={:?}, writeback_signature={:?}",
            artifact.function_facts.types.merged_signature, artifact.writeback_plan.signature
        );

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([
            (0x401140, "sym.imp.memcpy".to_string()),
            (0x401150, "sym.imp.malloc".to_string()),
        ]));
        decompiler.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.malloc".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Unsigned,
                    }],
                    variadic: false,
                },
            ),
            (
                "sym.imp.memcpy".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Int {
                            bits: 64,
                            signedness: r2types::Signedness::Unsigned,
                        },
                    ],
                    variadic: false,
                },
            ),
        ]));
        let output = decompiler.decompile(&artifact.ssa_func);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();
        assert!(
            output.contains("sym.imp.memcpy(buf, src, len);"),
            "expected detached x86 alloc_and_copy to keep the malloc owner for memcpy, got:\n{output}\nssa_ops={ssa_ops:?}\nmerged_signature={:?}\nwriteback_signature={:?}",
            artifact.function_facts.types.merged_signature,
            artifact.writeback_plan.signature
        );
        assert!(
            output.contains("buf[len] = 0;"),
            "expected detached x86 alloc_and_copy to keep the malloc owner for the NUL store, got:\n{output}\nmerged_signature={:?}\nwriteback_signature={:?}",
            artifact.function_facts.types.merged_signature,
            artifact.writeback_plan.signature
        );
        assert!(
            output.contains("return buf;"),
            "expected detached x86 alloc_and_copy to return the owned malloc result, got:\n{output}\nmerged_signature={:?}\nwriteback_signature={:?}",
            artifact.function_facts.types.merged_signature,
            artifact.writeback_plan.signature
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_vuln_memcpy_artifact_keeps_authoritative_args() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![disasm
            .lift_block(
                &decode_hex(
                    "f30f1efa554889e54883ec5048897db88975b48b45b44863d0488b4db8488d45c04889ce4889c7e84bfeffff488d45c04889c6488d05051d00004889c7b800000000e800feffff90c9c3",
                ),
                0x4012c9,
                74,
            )
            .expect("vuln_memcpy block")];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.vuln_memcpy",
                "ret": "int64_t",
                "callconv": "amd64",
                "params": [
                    {"name": "user_input", "type": "int8_t *"},
                    {"name": "user_len", "type": "int32_t"}
                ]
            },
            "vars": [
                {"kind":"register","name":"user_input","type":"int8_t *","reg":"rdi","param_index":0},
                {"kind":"register","name":"user_len","type":"int32_t","reg":"rsi","param_index":1},
                {"kind":"stack","name":"user_input_home","type":"int8_t *","base":"rbp","offset":-72,"role":"param_home","param_index":0,"param_name":"user_input","source_reg":"rdi"},
                {"kind":"stack","name":"user_len_home","type":"int32_t","base":"rbp","offset":-76,"role":"param_home","param_index":1,"param_name":"user_len","source_reg":"rsi"},
                {"kind":"stack","name":"buf","type":"int8_t *","base":"rbp","offset":-64,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.vuln_memcpy",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([
            (0x401110, "sym.imp.printf".to_string()),
            (0x401140, "sym.imp.memcpy".to_string()),
        ]));
        decompiler.set_strings(HashMap::from([(0x403008, "Copied: %s\n".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([
            (
                "sym.imp.memcpy".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        })),
                        r2types::CTypeLike::Int {
                            bits: 64,
                            signedness: r2types::Signedness::Unsigned,
                        },
                    ],
                    variadic: false,
                },
            ),
            (
                "sym.imp.printf".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    },
                    params: vec![r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        },
                    ))],
                    variadic: true,
                },
            ),
        ]));
        let output = decompiler.decompile(&artifact.ssa_func);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();

        assert!(
            output.contains("sym.imp.memcpy(buf, user_input, user_len);"),
            "expected detached vuln_memcpy to keep authoritative memcpy args, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("sym.imp.printf(\"Copied: %s\\n\", buf);"),
            "expected detached vuln_memcpy to print the recovered buf local, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        for bad in [
            "arg1",
            "arg2",
            "tmp:",
            "*(rbp",
            "sym.imp.memcpy(buf, user_len, user_len)",
        ] {
            assert!(
                !output.contains(bad),
                "detached vuln_memcpy should not regress to {bad:?}, got:\n{output}\nssa_ops={ssa_ops:?}"
            );
        }
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_authenticate_artifact_keeps_strcmp_condition_shape() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec1048897df8488b45f8488d15801c00004889d64889c7e891fdffff85c07507",
                    ),
                    0x401379,
                    42,
                )
                .expect("authenticate entry"),
            disasm
                .lift_block(&decode_hex("b801000000eb05"), 0x4013a3, 7)
                .expect("authenticate false arm"),
            disasm
                .lift_block(&decode_hex("b800000000"), 0x4013aa, 5)
                .expect("authenticate true arm"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x4013af, 2)
                .expect("authenticate exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.authenticate",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "password", "type": "int8_t *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"password","type":"int8_t *","reg":"rdi","param_index":0},
                {"kind":"stack","name":"password_home","type":"int8_t *","base":"rbp","offset":-8,"role":"param_home","param_index":0,"param_name":"password","source_reg":"rdi"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.authenticate",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([(0x401130, "sym.imp.strcmp".to_string())]));
        decompiler.set_strings(HashMap::from([(0x403014, "secret123".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.strcmp".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                },
                params: vec![
                    r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    })),
                    r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    })),
                ],
                variadic: false,
            },
        )]));
        let output = decompiler.decompile(&artifact.ssa_func);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();

        assert!(
            output.contains("sym.imp.strcmp(password, \"secret123\")"),
            "expected detached authenticate to keep the strcmp call in the condition, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            !output.contains("0 != 0") && !output.contains("0 == 0"),
            "authenticate condition should not collapse to a constant, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_check_secret_artifact_keeps_branch_return_values() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex("f30f1efa554889e5897dfc817dfcadde00007507"),
                    0x401276,
                    20,
                )
                .expect("check_secret entry"),
            disasm
                .lift_block(&decode_hex("b801000000eb05"), 0x40128a, 7)
                .expect("check_secret then"),
            disasm
                .lift_block(&decode_hex("b800000000"), 0x401291, 5)
                .expect("check_secret else"),
            disasm
                .lift_block(&decode_hex("5dc3"), 0x401296, 2)
                .expect("check_secret exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.check_secret",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "x", "type": "int32_t"}
                ]
            },
            "vars": [
                {"kind":"register","name":"x","type":"int32_t","reg":"rdi","param_index":0},
                {"kind":"stack","name":"var_8h","type":"void *","base":"rsp","offset":0,"role":"unknown"},
                {"kind":"stack","name":"var_4h","type":"int32_t","base":"rbp","offset":-4,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.check_secret",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let then_ops: Vec<String> = artifact
            .ssa_func
            .get_block(0x40128a)
            .expect("then block")
            .ops
            .iter()
            .map(|op| format!("{op:?}"))
            .collect();
        let else_ops: Vec<String> = artifact
            .ssa_func
            .get_block(0x401291)
            .expect("else block")
            .ops
            .iter()
            .map(|op| format!("{op:?}"))
            .collect();
        let entry_ops: Vec<String> = artifact
            .ssa_func
            .get_block(0x401276)
            .expect("entry block")
            .ops
            .iter()
            .map(|op| format!("{op:?}"))
            .collect();
        let exit_block = artifact.ssa_func.get_block(0x401296).expect("exit block");
        let exit_ops: Vec<String> = exit_block.ops.iter().map(|op| format!("{op:?}")).collect();
        let exit_phis: Vec<String> = exit_block
            .phis
            .iter()
            .map(|phi| format!("{phi:?}"))
            .collect();

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        let output = decompiler.decompile(&artifact.ssa_func);
        let output_without_types =
            r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64()).decompile(&artifact.ssa_func);

        assert!(
            then_ops
                .iter()
                .any(|op| op.contains("Copy") && op.contains("RAX") && op.contains("const:1")),
            "prepared SSA should keep the then-arm return value, got then_ops={then_ops:?}"
        );
        assert!(
            else_ops
                .iter()
                .any(|op| op.contains("Copy") && op.contains("RAX") && op.contains("const:0")),
            "prepared SSA should keep the else-arm return value, got else_ops={else_ops:?}"
        );
        assert!(
            output.contains("if") && output.contains("return 1;") && output.contains("return 0;"),
            "expected detached check_secret to keep branch returns, got:\n{output}\noutput_without_types=\n{output_without_types}\nentry_ops={entry_ops:?}\nthen_ops={then_ops:?}\nelse_ops={else_ops:?}\nexit_ops={exit_ops:?}\nexit_phis={exit_phis:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_bool_carrier_artifact_keeps_branch_return_values() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e5897dec8975e88b45ec3b45e80f95c00fb6c08945fc8b45fc4898488945f048837df0007505",
                    ),
                    0x401b7f,
                    45,
                )
                .expect("bool-carrier entry"),
            disasm
                .lift_block(&decode_hex("8b45e8eb03"), 0x401bac, 5)
                .expect("bool-carrier else"),
            disasm
                .lift_block(&decode_hex("8b45ec"), 0x401bb1, 3)
                .expect("bool-carrier then"),
            disasm
                .lift_block(&decode_hex("5dc3"), 0x401bb4, 2)
                .expect("bool-carrier exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.test_bool_carrier_chain",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "x", "type": "int32_t"},
                    {"name": "y", "type": "int32_t"}
                ]
            },
            "vars": [
                {"kind":"register","name":"arg0","type":"int32_t","reg":"rdi","param_index":0},
                {"kind":"register","name":"arg1","type":"int32_t","reg":"rsi","param_index":1},
                {"kind":"stack","name":"var_18h","type":"int32_t","base":"rbp","offset":-24,"role":"local"},
                {"kind":"stack","name":"var_14h","type":"int32_t","base":"rbp","offset":-20,"role":"local"},
                {"kind":"stack","name":"var_10h","type":"int64_t","base":"rbp","offset":-16,"role":"local"},
                {"kind":"stack","name":"var_4h","type":"int32_t","base":"rbp","offset":-4,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.test_bool_carrier_chain",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        let output = decompiler.decompile(&artifact.ssa_func);
        let visible_bindings = artifact.function_facts.types.visible_bindings.clone();

        assert!(
            output.contains("if (x != y)")
                && output.contains("return x;")
                && output.contains("return y;")
                && !output.contains("local_14")
                && !output.contains("local_18")
                && !output.contains("var_14h")
                && !output.contains("var_18h"),
            "expected detached bool-carrier decompilation to keep param returns, got:\n{output}\nvisible_bindings={visible_bindings:#?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_setlocale_artifact_keeps_owned_call_result() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec10488d059c1900004889c6bf06000000e8affaffff488945f848837df8007507",
                    ),
                    0x401691,
                    43,
                )
                .expect("setlocale entry"),
            disasm
                .lift_block(&decode_hex("b800000000eb0a"), 0x4016bc, 7)
                .expect("setlocale false arm"),
            disasm
                .lift_block(&decode_hex("488b45f80fb6000fbec0"), 0x4016c3, 10)
                .expect("setlocale true arm"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x4016cd, 2)
                .expect("setlocale exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.test_setlocale_wrapper",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": []
            },
            "vars": [
                {"kind":"stack","name":"loc","type":"int8_t *","base":"rbp","offset":-8,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.test_setlocale_wrapper",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([(0x401160, "sym.imp.setlocale".to_string())]));
        decompiler.set_strings(HashMap::from([(0x403040, "C".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.setlocale".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                    bits: 8,
                    signedness: r2types::Signedness::Signed,
                })),
                params: vec![
                    r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    },
                    r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    })),
                ],
                variadic: false,
            },
        )]));
        let output = decompiler.decompile(&artifact.ssa_func);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();
        let block_succs: Vec<(u64, Vec<u64>)> = artifact
            .ssa_func
            .blocks()
            .map(|block| (block.addr, artifact.ssa_func.successors(block.addr)))
            .collect();

        assert!(
            output.contains("loc = (int8_t*)sym.imp.setlocale(6, \"C\");")
                || output.contains("loc = sym.imp.setlocale(6, \"C\");"),
            "expected detached setlocale wrapper to assign the owned call result to loc, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            output.contains("if (loc != 0)") || output.contains("if (!loc)"),
            "expected setlocale wrapper to branch on the owned loc value, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            !output.contains("loc = (int8_t*)loc;"),
            "setlocale wrapper should not collapse to self-assignment, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            output.contains("return loc[0];")
                || output.contains("return (int32_t)loc[0];")
                || output.contains("return *loc;")
                || output.contains("return (int32_t)*loc;"),
            "expected detached setlocale wrapper to return the first character of loc, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_setlocale_typed_input_keeps_owned_call_result() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec10488d059c1900004889c6bf06000000e8affaffff488945f848837df8007507",
                    ),
                    0x401691,
                    43,
                )
                .expect("setlocale entry"),
            disasm
                .lift_block(&decode_hex("b800000000eb0a"), 0x4016bc, 7)
                .expect("setlocale false arm"),
            disasm
                .lift_block(&decode_hex("488b45f80fb6000fbec0"), 0x4016c3, 10)
                .expect("setlocale true arm"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x4016cd, 2)
                .expect("setlocale exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.test_setlocale_wrapper",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": []
            },
            "vars": [
                {"kind":"stack","name":"loc","type":"int8_t *","base":"rbp","offset":-8,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.test_setlocale_wrapper",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let function_names = HashMap::from([(0x401160, "sym.imp.setlocale".to_string())]);
        let strings = HashMap::from([(0x403040, "C".to_string())]);
        let input = crate::decompiler::decompiler_input_from_artifact(
            artifact,
            function_names,
            strings,
            HashMap::new(),
            64,
        );
        let decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        let output = decompiler.decompile_input(&input);

        assert!(
            output.contains("loc = (int8_t*)sym.imp.setlocale(6, \"C\");")
                || output.contains("loc = sym.imp.setlocale(6, \"C\");"),
            "expected typed-input setlocale wrapper to assign the owned call result to loc, got:\n{output}"
        );
        assert!(
            output.contains("if (loc != 0)") || output.contains("if (!loc)"),
            "expected typed-input setlocale wrapper to branch on loc, got:\n{output}"
        );
        assert!(
            output.contains("return loc[0];")
                || output.contains("return (int32_t)loc[0];")
                || output.contains("return *loc;")
                || output.contains("return (int32_t)*loc;"),
            "expected typed-input setlocale wrapper to keep the dereferenced return, got:\n{output}"
        );
        assert!(
            !output.contains("return loc;"),
            "typed-input setlocale wrapper should not collapse to a raw pointer return, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_my_strdup_artifact_reuses_owned_call_results() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec2048897de8488b45e84889c7e8b2eeffff488945f8488b45f84883c0014889c7e8eeeeffff488945f048837df000741b",
                    ),
                    0x402272,
                    59,
                )
                .expect("my_strdup entry"),
            disasm
                .lift_block(
                    &decode_hex("488b45f8488d5001488b4de8488b45f04889ce4889c7e8a8eeffff"),
                    0x4022ad,
                    27,
                )
                .expect("my_strdup copy arm"),
            disasm
                .lift_block(&decode_hex("488b45f0c9c3"), 0x4022c8, 6)
                .expect("my_strdup exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.my_strdup",
                "ret": "int8_t *",
                "callconv": "amd64",
                "params": [
                    {"name": "s", "type": "int8_t *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"s","type":"int8_t *","reg":"rdi","param_index":0},
                {"kind":"stack","name":"s_home","type":"int8_t *","base":"rbp","offset":-24,"role":"param_home","param_index":0,"param_name":"s","source_reg":"rdi"},
                {"kind":"stack","name":"len","type":"uint64_t","base":"rbp","offset":-8,"role":"local"},
                {"kind":"stack","name":"dup","type":"int8_t *","base":"rbp","offset":-16,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.my_strdup",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut type_facts = artifact.function_facts.types.clone();
        type_facts.known_function_signatures.extend(HashMap::from([
            (
                "sym.imp.strlen".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Unsigned,
                    },
                    params: vec![r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Int {
                            bits: 8,
                            signedness: r2types::Signedness::Signed,
                        },
                    ))],
                    variadic: false,
                },
            ),
            (
                "sym.imp.malloc".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Unsigned,
                    }],
                    variadic: false,
                },
            ),
            (
                "sym.imp.memcpy".to_string(),
                r2types::FunctionType {
                    return_type: r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                    params: vec![
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Pointer(Box::new(r2types::CTypeLike::Unknown)),
                        r2types::CTypeLike::Int {
                            bits: 64,
                            signedness: r2types::Signedness::Unsigned,
                        },
                    ],
                    variadic: false,
                },
            ),
        ]));
        let context = r2dec::DecompilerContext::default()
            .with_type_facts(type_facts)
            .with_function_names(HashMap::from([
                (0x401140, "sym.imp.strlen".to_string()),
                (0x401170, "sym.imp.memcpy".to_string()),
                (0x401190, "sym.imp.malloc".to_string()),
            ]));
        let input = r2dec::DecompilerInput::new(artifact.ssa_func.clone(), context);
        let decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        let output = decompiler.decompile_input(&input);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();
        let block_succs: Vec<(u64, Vec<u64>)> = artifact
            .ssa_func
            .blocks()
            .map(|block| (block.addr, artifact.ssa_func.successors(block.addr)))
            .collect();

        assert!(
            output.contains("len = sym.imp.strlen(s);"),
            "expected my_strdup to keep a single owned strlen result, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            output.contains("dup = sym.imp.malloc(len + 1);"),
            "expected my_strdup to assign the owned malloc result to dup, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            output.contains("if (dup == 0)")
                || output.contains("if (!dup)")
                || output.contains("if (s_home == 0)")
                || output.contains("if (!s_home)"),
            "expected my_strdup null-check to stay source-like without replaying helper calls, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            output.contains("sym.imp.memcpy(dup, s, len + 1);"),
            "expected my_strdup to reuse dup and len in memcpy, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            output.contains("return dup;"),
            "expected my_strdup to return the owned dup result, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
        assert!(
            !output.contains("sym.imp.malloc(sym.imp.strlen(")
                && !output.contains("dup = rax;")
                && !output.contains("return len;"),
            "my_strdup should not replay helper calls or return the strlen result, got:\n{output}\nssa_ops={ssa_ops:?}\nblock_succs={block_succs:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_my_strdup_artifact_reuses_malloc_owner_with_generic_stack_local_name() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec2048897de8488b45e84889c7e8b2eeffff488945f8488b45f84883c0014889c7e8eeeeffff488945f048837df000741b",
                    ),
                    0x402272,
                    59,
                )
                .expect("my_strdup entry"),
            disasm
                .lift_block(
                    &decode_hex("488b45f8488d5001488b4de8488b45f04889ce4889c7e8a8eeffff"),
                    0x4022ad,
                    27,
                )
                .expect("my_strdup copy arm"),
            disasm
                .lift_block(&decode_hex("488b45f0c9c3"), 0x4022c8, 6)
                .expect("my_strdup exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.my_strdup_generic_local",
                "ret": "char *",
                "callconv": "amd64",
                "params": [
                    {"name": "s", "type": "char const *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"arg0","type":"int64_t","reg":"rdi","param_index":0},
                {"kind":"stack","name":"len","type":"size_t","base":"rbp","offset":-8,"role":"local"},
                {"kind":"stack","name":"var_10h","type":"int64_t","base":"rbp","offset":-16,"role":"local"},
                {"kind":"stack","name":"s_home","type":"char const *","base":"rbp","offset":-24,"role":"param_home","param_index":0,"param_name":"s","source_reg":"rdi"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.my_strdup_generic_local",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let function_names = HashMap::from([
            (0x401140, "sym.imp.strlen".to_string()),
            (0x401170, "sym.imp.memcpy".to_string()),
            (0x401190, "sym.imp.malloc".to_string()),
        ]);
        let input = crate::decompiler::decompiler_input_from_artifact(
            artifact.clone(),
            function_names,
            HashMap::new(),
            HashMap::new(),
            64,
        );
        let decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        let output = decompiler.decompile_input(&input);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();

        assert!(
            output.contains("len = sym.imp.strlen(s);"),
            "expected my_strdup to keep a single owned strlen result, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("var_10h = sym.imp.malloc(len + 1);")
                || output.contains("var_10h = (void*)sym.imp.malloc(len + 1);"),
            "expected my_strdup to bind the malloc result to the stack local owner even with a generic local name, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("sym.imp.memcpy(var_10h, s, len + 1);"),
            "expected my_strdup to reuse the generic stack local owner in memcpy, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("return var_10h;"),
            "expected my_strdup to return the generic stack local owner instead of replaying malloc, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            !output.contains("sym.imp.malloc(len + 1)")
                || output.matches("sym.imp.malloc(len + 1)").count() == 1,
            "expected my_strdup to keep a single visible malloc call, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_process_string_artifact_keeps_strlen_owner_and_hex_constant_shape() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                    ),
                    0x401337,
                    39,
                )
                .expect("process_string entry"),
            disasm
                .lift_block(&decode_hex("b8ffffffffeb12"), 0x40135e, 7)
                .expect("process_string too_long"),
            disasm
                .lift_block(&decode_hex("48837df8047707"), 0x401365, 7)
                .expect("process_string second_guard"),
            disasm
                .lift_block(&decode_hex("b8feffffffeb04"), 0x40136c, 7)
                .expect("process_string too_short"),
            disasm
                .lift_block(&decode_hex("488b45f8"), 0x401373, 4)
                .expect("process_string return_len"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x401377, 2)
                .expect("process_string exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.process_string",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "s", "type": "int8_t *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"s","type":"int8_t *","reg":"rdi","param_index":0},
                {"kind":"stack","name":"s_home","type":"int8_t *","base":"rbp","offset":-24,"role":"param_home","param_index":0,"param_name":"s","source_reg":"rdi"},
                {"kind":"stack","name":"len","type":"uint64_t","base":"rbp","offset":-8,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.process_string",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([(0x401100, "sym.imp.strlen".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.strlen".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Unsigned,
                },
                params: vec![r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))],
                variadic: false,
            },
        )]));
        let output = decompiler.decompile(&artifact.ssa_func);
        let ssa_ops: Vec<String> = artifact
            .ssa_func
            .blocks()
            .flat_map(|block| block.ops.iter().map(|op| format!("{op:?}")))
            .collect();

        assert!(
            output.contains("len = sym.imp.strlen(s);"),
            "expected process_string to keep the strlen owner, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            !output.contains("sym.imp.strlen(s)")
                || output.matches("sym.imp.strlen(s)").count() == 1,
            "process_string should not replay strlen, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("if (len > 100)") || output.contains("if (len > 0x64)"),
            "expected process_string to preserve the original 0x64/100 guard, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("return len;"),
            "expected process_string to return the owned len on the success path, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("return -1;"),
            "expected process_string to preserve the too-long return, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
        assert!(
            output.contains("return -2;"),
            "expected process_string to preserve the too-short return, got:\n{output}\nssa_ops={ssa_ops:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_process_string_artifact_accepts_size_t_external_local_type() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                    ),
                    0x401337,
                    39,
                )
                .expect("process_string entry"),
            disasm
                .lift_block(&decode_hex("b8ffffffffeb12"), 0x40135e, 7)
                .expect("process_string too_long"),
            disasm
                .lift_block(&decode_hex("48837df8047707"), 0x401365, 7)
                .expect("process_string second_guard"),
            disasm
                .lift_block(&decode_hex("b8feffffffeb04"), 0x40136c, 7)
                .expect("process_string too_short"),
            disasm
                .lift_block(&decode_hex("488b45f8"), 0x401373, 4)
                .expect("process_string return_len"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x401377, 2)
                .expect("process_string exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.process_string",
                "ret": "int32_t",
                "callconv": "amd64",
                "params": [
                    {"name": "s", "type": "int8_t *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"s","type":"int8_t *","reg":"rdi","param_index":0},
                {"kind":"stack","name":"s_home","type":"int8_t *","base":"rbp","offset":-24,"role":"param_home","param_index":0,"param_name":"s","source_reg":"rdi"},
                {"kind":"stack","name":"len","type":"size_t","base":"rbp","offset":-8,"role":"local"}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.process_string",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([(0x401100, "sym.imp.strlen".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.strlen".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Unsigned,
                },
                params: vec![r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))],
                variadic: false,
            },
        )]));
        let output = decompiler.decompile(&artifact.ssa_func);

        assert!(
            output.contains("len = sym.imp.strlen(s);"),
            "expected process_string to keep the strlen owner with a size_t local, got:\n{output}"
        );
        assert!(
            output.contains("if (len > 100)") || output.contains("if (len > 0x64)"),
            "expected process_string to preserve the upper-bound guard with a size_t local, got:\n{output}"
        );
        assert!(
            output.contains("return -1;"),
            "expected process_string to preserve the too-long return with a size_t local, got:\n{output}"
        );
        assert!(
            output.contains("return -2;"),
            "expected process_string to preserve the too-short return with a size_t local, got:\n{output}"
        );
        assert!(
            output.contains("return len;"),
            "expected process_string to preserve the success return owner with a size_t local, got:\n{output}"
        );
        assert!(
            !output.contains("uint8_t len") && !output.contains("\"\\x7f\""),
            "size_t local metadata should not collapse process_string into a byte-typed artifact, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_process_string_artifact_matches_live_external_slot_mix() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                    ),
                    0x401337,
                    39,
                )
                .expect("process_string entry"),
            disasm
                .lift_block(&decode_hex("b8ffffffffeb12"), 0x40135e, 7)
                .expect("process_string too_long"),
            disasm
                .lift_block(&decode_hex("48837df8047707"), 0x401365, 7)
                .expect("process_string second_guard"),
            disasm
                .lift_block(&decode_hex("b8feffffffeb04"), 0x40136c, 7)
                .expect("process_string too_short"),
            disasm
                .lift_block(&decode_hex("488b45f8"), 0x401373, 4)
                .expect("process_string return_len"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x401377, 2)
                .expect("process_string exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.process_string",
                "ret": "int",
                "callconv": "amd64",
                "params": [
                    {"name": "s", "type": "char *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"arg0","type":"int64_t","reg":"RDI"},
                {"kind":"stack","name":"s","type":"char *","base":"bp","role":"stack_arg","is_arg":true,"offset":-24},
                {"kind":"stack","name":"len","type":"size_t","base":"bp","role":"local","is_arg":false,"offset":-8},
                {"kind":"stack","name":"var_8h","type":"void *","base":"sp","role":"local","is_arg":false,"offset":32}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.process_string",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_facts(artifact.function_facts.clone());
        decompiler.set_function_names(HashMap::from([(0x401100, "sym.imp.strlen".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.strlen".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Unsigned,
                },
                params: vec![r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))],
                variadic: false,
            },
        )]));
        let output = decompiler.decompile(&artifact.ssa_func);

        assert!(
            output.contains("return -1;")
                && output.contains("return -2;")
                && output.contains("return len;"),
            "expected process_string to keep its signed return paths with the live external slot mix, got:\n{output}"
        );
        assert!(
            output.contains("if (len > 100)") || output.contains("if (len > 0x64)"),
            "expected live external slot mix to keep the upper-bound guard, got:\n{output}"
        );
        assert!(
            !output.contains("uint8_t len"),
            "live external slot mix should not narrow len to uint8_t, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn detached_x86_process_string_typed_input_matches_live_external_slot_mix() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let (arch, disasm) = create_disassembler_for_arch("x86-64").expect("disassembler");
        let blocks = vec![
            disasm
                .lift_block(
                    &decode_hex(
                        "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                    ),
                    0x401337,
                    39,
                )
                .expect("process_string entry"),
            disasm
                .lift_block(&decode_hex("b8ffffffffeb12"), 0x40135e, 7)
                .expect("process_string too_long"),
            disasm
                .lift_block(&decode_hex("48837df8047707"), 0x401365, 7)
                .expect("process_string second_guard"),
            disasm
                .lift_block(&decode_hex("b8feffffffeb04"), 0x40136c, 7)
                .expect("process_string too_short"),
            disasm
                .lift_block(&decode_hex("488b45f8"), 0x401373, 4)
                .expect("process_string return_len"),
            disasm
                .lift_block(&decode_hex("c9c3"), 0x401377, 2)
                .expect("process_string exit"),
        ];
        let reg_type_hints = crate::types::collect_register_type_hints(&blocks, &disasm);
        let external_context = serde_json::json!({
            "signature": {
                "name": "dbg.process_string",
                "ret": "int",
                "callconv": "amd64",
                "params": [
                    {"name": "s", "type": "char *"}
                ]
            },
            "vars": [
                {"kind":"register","name":"arg0","type":"int64_t","reg":"RDI"},
                {"kind":"stack","name":"s","type":"char *","base":"bp","role":"stack_arg","is_arg":true,"offset":-24},
                {"kind":"stack","name":"len","type":"size_t","base":"bp","role":"local","is_arg":false,"offset":-8},
                {"kind":"stack","name":"var_8h","type":"void *","base":"sp","role":"local","is_arg":false,"offset":32}
            ],
            "base_types": []
        })
        .to_string();

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.process_string",
            Some(&arch),
            64,
            true,
            &reg_type_hints,
            &external_context,
        )
        .expect("analysis artifact");

        let input = crate::decompiler::decompiler_input_from_artifact(
            artifact.clone(),
            HashMap::from([(0x401100, "sym.imp.strlen".to_string())]),
            HashMap::new(),
            HashMap::new(),
            64,
        );
        let empty_input = crate::decompiler::decompiler_input_from_artifact(
            artifact.clone(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            64,
        );
        let decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        let output = decompiler.decompile_input(&input);
        let empty_output = decompiler.decompile_input(&empty_input);
        let entry_ops: Vec<String> = artifact
            .ssa_func
            .get_block(0x401337)
            .expect("process_string entry block")
            .ops
            .iter()
            .map(|op| format!("{op:?}"))
            .collect();
        let predicate_debug: Vec<String> = artifact
            .ssa_func
            .predicates()
            .predicates
            .iter()
            .map(|(id, predicate)| {
                let comparison = predicate
                    .comparison
                    .as_ref()
                    .map(|cmp| {
                        let lhs = artifact
                            .ssa_func
                            .value_var(cmp.lhs)
                            .expect("compare lhs var");
                        let rhs = artifact
                            .ssa_func
                            .value_var(cmp.rhs)
                            .expect("compare rhs var");
                        format!(
                            "{:?} {}:{} {}:{}",
                            cmp.kind,
                            lhs.display_name(),
                            lhs.size,
                            rhs.display_name(),
                            rhs.size
                        )
                    })
                    .unwrap_or_else(|| "none".to_string());
                let condition = artifact
                    .ssa_func
                    .value_var(predicate.condition)
                    .expect("predicate condition var");
                format!(
                    "{id:?}@0x{:x}: cond={} cmp={comparison}",
                    predicate.block_addr,
                    condition.display_name()
                )
            })
            .collect();

        assert!(
            output.contains("len = sym.imp.strlen(s);"),
            "expected typed-input process_string to keep the strlen owner, got:\n{output}"
        );
        assert!(
            output.contains("if (len > 100)")
                || output.contains("if (len > 0x64)")
                || output.contains("if (len <= 100)")
                || output.contains("if (len <= 0x64)"),
            "expected typed-input process_string to keep the upper-bound guard semantically intact, got:\nwith_names=\n{output}\nwithout_names=\n{empty_output}\npredicates={predicate_debug:?}\nentry_ops={entry_ops:?}"
        );
        assert!(
            output.contains("return -1;")
                && output.contains("return -2;")
                && output.contains("return len;"),
            "expected typed-input process_string to keep its signed return paths, got:\n{output}"
        );
        assert!(
            !output.contains("len == 64"),
            "typed-input process_string should not reinterpret 0x64 as decimal 64, got:\nwith_names=\n{output}\nwithout_names=\n{empty_output}\npredicates={predicate_debug:?}\nentry_ops={entry_ops:?}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_function_with_context_keeps_process_string_signed_return_paths() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let lifted = [
            (
                "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                0x401337,
                39,
            ),
            ("b8ffffffffeb12", 0x40135e, 7),
            ("48837df8047707", 0x401365, 7),
            ("b8feffffffeb04", 0x40136c, 7),
            ("488b45f8", 0x401373, 4),
            ("c9c3", 0x401377, 2),
        ];
        let mut owned_blocks = Vec::new();
        for (hex, addr, size) in lifted {
            let bytes = decode_hex(hex);
            let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), addr, size);
            assert!(
                !block.is_null(),
                "process_string block should lift at 0x{addr:x}"
            );
            owned_blocks.push(block);
        }

        let func_name = CString::new("dbg.process_string").expect("valid function name");
        let function_names =
            CString::new(r#"{"0x401100":"sym.imp.strlen"}"#).expect("valid function name map");
        let empty_map = CString::new("{}").expect("valid empty json");
        let external_context_json = CString::new(
            r#"{
                "signature": {
                    "name": "dbg.process_string",
                    "ret": "int32_t",
                    "callconv": "amd64",
                    "params": [
                        {"name": "s", "type": "int8_t *"}
                    ]
                },
                "vars": [
                    {"kind":"register","name":"s","type":"int8_t *","reg":"rdi","param_index":0},
                    {"kind":"stack","name":"s_home","type":"int8_t *","base":"rbp","offset":-24,"role":"param_home","param_index":0,"param_name":"s","source_reg":"rdi"},
                    {"kind":"stack","name":"len","type":"uint64_t","base":"rbp","offset":-8,"role":"local"}
                ],
                "base_types": []
            }"#,
        )
        .expect("valid process_string external context");

        let out = r2dec_function_with_context(
            ctx,
            owned_blocks.as_ptr().cast(),
            owned_blocks.len(),
            func_name.as_ptr(),
            function_names.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            external_context_json.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        for block in owned_blocks {
            r2il_block_free(block);
        }
        r2il_free(ctx);

        assert!(
            output.contains("return -1;"),
            "expected FFI decompile to keep the too-long signed return, got:\n{output}"
        );
        assert!(
            output.contains("return -2;"),
            "expected FFI decompile to keep the too-short signed return, got:\n{output}"
        );
        assert!(
            output.contains("return len;"),
            "expected FFI decompile to keep the success return owner, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn r2dec_function_with_context_process_string_live_slot_mix_keeps_wide_len() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let lifted = [
            (
                "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                0x401337,
                39,
            ),
            ("b8ffffffffeb12", 0x40135e, 7),
            ("48837df8047707", 0x401365, 7),
            ("b8feffffffeb04", 0x40136c, 7),
            ("488b45f8", 0x401373, 4),
            ("c9c3", 0x401377, 2),
        ];
        let mut owned_blocks = Vec::new();
        for (hex, addr, size) in lifted {
            let bytes = decode_hex(hex);
            let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), addr, size);
            assert!(
                !block.is_null(),
                "process_string block should lift at 0x{addr:x}"
            );
            owned_blocks.push(block);
        }

        let func_name = CString::new("dbg.process_string").expect("valid function name");
        let empty_map = CString::new("{}").expect("valid empty json");
        let external_context_json = CString::new(
            r#"{
                "signature": {
                    "name": "dbg.process_string",
                    "ret": "int",
                    "callconv": "amd64",
                    "params": [
                        {"name": "s", "type": "char *"}
                    ]
                },
                "vars": [
                    {"kind":"register","name":"arg0","type":"int64_t","reg":"RDI"},
                    {"kind":"stack","name":"s","type":"char *","base":"bp","role":"stack_arg","is_arg":true,"offset":-24},
                    {"kind":"stack","name":"len","type":"size_t","base":"bp","role":"local","is_arg":false,"offset":-8},
                    {"kind":"stack","name":"var_8h","type":"void *","base":"sp","role":"local","is_arg":false,"offset":32}
                ],
                "base_types": []
            }"#,
        )
        .expect("valid process_string external context");

        let out = r2dec_function_with_context(
            ctx,
            owned_blocks.as_ptr().cast(),
            owned_blocks.len(),
            func_name.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            empty_map.as_ptr(),
            external_context_json.as_ptr(),
        );
        assert!(!out.is_null(), "decompilation output should not be null");
        let output = unsafe { CStr::from_ptr(out) }.to_string_lossy().to_string();

        r2il_string_free(out);
        for block in owned_blocks {
            r2il_block_free(block);
        }
        r2il_free(ctx);

        assert!(
            output.contains("return -1;")
                && output.contains("return -2;")
                && output.contains("return len;"),
            "expected FFI decompile to keep signed return paths with the live slot mix, got:\n{output}"
        );
        assert!(
            output.contains("if (len > 100)")
                || output.contains("if (len > 0x64)")
                || output.contains("if (ram:401100(s) > 100)")
                || output.contains("if (sub_401100(s) > 100)")
                || (output.contains("< 100") && output.contains("== 100")),
            "expected FFI decompile to keep the upper-bound guard with the live slot mix, got:\n{output}"
        );
        assert!(
            !output.contains("uint8_t len"),
            "FFI decompile path should not narrow len to uint8_t with the live slot mix, got:\n{output}"
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn type_writeback_ffi_process_string_keeps_pointer_width_len_for_live_slot_mix() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
            assert_eq!(bytes.len() % 2, 0, "hex input must have even length");
            bytes
                .chunks_exact(2)
                .map(|pair| {
                    let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                    let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                    (hi << 4) | lo
                })
                .collect()
        }

        let arch = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");

        let lifted = [
            (
                "f30f1efa554889e54883ec2048897de8488b45e84889c7e8adfdffff488945f848837df8647607",
                0x401337,
                39,
            ),
            ("b8ffffffffeb12", 0x40135e, 7),
            ("48837df8047707", 0x401365, 7),
            ("b8feffffffeb04", 0x40136c, 7),
            ("488b45f8", 0x401373, 4),
            ("c9c3", 0x401377, 2),
        ];
        let mut owned_blocks = Vec::new();
        for (hex, addr, size) in lifted {
            let bytes = decode_hex(hex);
            let block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), addr, size);
            assert!(
                !block.is_null(),
                "process_string block should lift at 0x{addr:x}"
            );
            owned_blocks.push(block);
        }

        let func_name = CString::new("dbg.process_string").expect("valid function name");
        let external_context = CString::new(
            r#"{
                "signature": {
                    "name": "dbg.process_string",
                    "ret": "int",
                    "callconv": "amd64",
                    "params": [
                        {"name": "s", "type": "char *"}
                    ]
                },
                "vars": [
                    {"kind":"register","name":"arg0","type":"int64_t","reg":"RDI"},
                    {"kind":"stack","name":"s","type":"char *","base":"bp","role":"stack_arg","is_arg":true,"offset":-24},
                    {"kind":"stack","name":"len","type":"size_t","base":"bp","role":"local","is_arg":false,"offset":-8},
                    {"kind":"stack","name":"var_8h","type":"void *","base":"sp","role":"local","is_arg":false,"offset":32}
                ],
                "base_types": []
            }"#,
        )
        .expect("valid process_string external context");

        let session_input = R2SleighSessionInput {
            ctx,
            blocks: owned_blocks.as_ptr().cast(),
            num_blocks: owned_blocks.len(),
            function_addr: 0,
            function_name: func_name.as_ptr(),
            function_context: R2SleighFunctionContext {
                schema_version: 1,
                dirty_epoch: 0,
                context_hash: 0,
                type_dirty_epoch: 0,
                external_context_json: external_context.as_ptr(),
                signature_name: ptr::null(),
                signature_ret_type: ptr::null(),
                signature_callconv: ptr::null(),
                signature_noreturn: 0,
                params: ptr::null(),
                num_params: 0,
                vars: ptr::null(),
                num_vars: 0,
                base_types: ptr::null(),
                num_base_types: 0,
                assumptions_json: ptr::null(),
            },
            interproc_scope: R2SleighInterprocScope {
                schema_version: 1,
                functions: ptr::null(),
                num_functions: 0,
                seeds: ptr::null(),
                num_seeds: 0,
            },
            debug_seed: R2SleighDebugSeed {
                schema_version: 1,
                seed_hash: 0,
            },
            budget: R2SleighBudgetConfig {
                schema_version: 1,
                interproc_iter: 1,
                interproc_max_iters: 1,
                interproc_converged: 1,
                global_max_links: 64,
                max_type_decls: 64,
                max_mutations: 256,
            },
        };
        let session = r2sleigh_session_analyze(&session_input);
        assert!(!session.is_null(), "session should not be null");
        let payload_ptr = r2sleigh_session_result_type_writeback_json(session);
        assert!(
            !payload_ptr.is_null(),
            "type writeback output should not be null"
        );
        let output = unsafe { CStr::from_ptr(payload_ptr) }
            .to_string_lossy()
            .to_string();
        let payload: serde_json::Value =
            serde_json::from_str(&output).expect("type writeback payload should parse");
        let parsed_context = r2types::parse_external_context_json(
            external_context.to_str().expect("context str"),
            64,
        );
        let parsed_len_slot = parsed_context.external_stack_vars.get(&-8).cloned();
        let recovered_out = crate::types::r2sleigh_recover_vars(
            ctx,
            owned_blocks.as_ptr().cast(),
            owned_blocks.len(),
            0,
        );
        assert!(
            !recovered_out.is_null(),
            "recover vars output should not be null"
        );
        let recovered_output = unsafe { CStr::from_ptr(recovered_out) }
            .to_string_lossy()
            .to_string();

        r2sleigh_session_result_free(session);
        r2il_string_free(recovered_out);
        for block in owned_blocks {
            r2il_block_free(block);
        }
        r2il_free(ctx);

        let candidates = payload
            .get("var_type_candidates")
            .and_then(|value| value.as_array())
            .expect("var_type_candidates array");
        let len_candidate = candidates
            .iter()
            .find(|candidate| {
                candidate.get("delta").and_then(|value| value.as_i64()) == Some(-8)
                    && candidate.get("target_name").is_none()
            })
            .expect("stack local candidate for len");
        let len_type = len_candidate
            .get("type")
            .and_then(|value| value.as_str())
            .expect("len type string");

        assert_ne!(
            len_type, "uint8_t",
            "live FFI type writeback path should not narrow len to uint8_t: {output}\nrecovered_vars={recovered_output}\nparsed_len_slot={parsed_len_slot:?}"
        );
    }

    #[test]
    fn enrich_decompiler_type_context_applies_live_arm64_struct_array_index_override() {
        let arch = ArchSpec::new("aarch64");
        let block = live_arm64_struct_array_index_block();
        let signature = Some(signature_spec(
            None,
            vec![
                (
                    "arg1",
                    Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Void))),
                ),
                ("arg2", Some(r2dec::CType::Int(32))),
                ("arg3", Some(r2dec::CType::Int(32))),
            ],
        ));

        let (signature, type_db) = enrich_decompiler_type_context(
            &[block],
            Some(&arch),
            64,
            signature,
            r2types::ExternalTypeDb::default(),
        );

        let signature = signature.expect("signature");
        let arg0 = signature.params.first().and_then(|param| param.ty.as_ref());
        let rendered = arg0
            .map(|ty| type_like_to_ctype(ty).to_string())
            .unwrap_or_default();
        let compact = rendered.replace(' ', "");
        assert!(
            compact.starts_with("struct")
                && compact.ends_with('*')
                && !compact.eq_ignore_ascii_case("void*"),
            "expected inferred struct pointer override, got {rendered}"
        );
        assert!(
            !type_db.structs.is_empty(),
            "expected inferred struct declarations in type db"
        );
    }

    #[test]
    fn enrich_decompiler_type_context_drives_live_arm64_struct_array_decompile() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let arch = ArchSpec::new("aarch64");
        let block = live_arm64_struct_array_index_block();
        let signature = Some(signature_spec(
            Some(r2dec::CType::Int(64)),
            vec![
                (
                    "arg1",
                    Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Void))),
                ),
                ("arg2", Some(r2dec::CType::Int(32))),
                ("arg3", Some(r2dec::CType::Int(32))),
            ],
        ));

        let (signature, type_db) = enrich_decompiler_type_context(
            std::slice::from_ref(&block),
            Some(&arch),
            64,
            signature,
            r2types::ExternalTypeDb::default(),
        );

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::aarch64());
        decompiler.set_type_facts(r2types::FunctionTypeFacts {
            merged_signature: signature,
            external_type_db: type_db,
            ..r2types::FunctionTypeFacts::default()
        });
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("struct ")
                && output.contains("* arg1")
                && !output.contains("void* arg1"),
            "expected struct-typed first argument in decompiled output, got:\n{output}"
        );
        assert!(
            !output.contains("arg1 ="),
            "indexed-member store path should not synthesize a bogus parameter assignment, got:\n{output}"
        );
        assert!(
            output.contains("f_8") && !output.contains("*(arg1 +"),
            "expected indexed-member store rendering in decompiled output, got:\n{output}"
        );
        assert!(
            !output.contains("\nx8 =") && !output.contains("\nstack_"),
            "dead register or stack artifacts should not leak into decompiled output, got:\n{output}"
        );
    }

    #[test]
    fn enrich_decompiler_type_context_drives_observed_live_arm64_struct_array_decompile() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let arch = ArchSpec::new("aarch64");
        let mut block = observed_live_arm64_struct_array_index_block_full();
        block.ops.extend([
            r2ssa::SSAOp::IntAdd {
                dst: r2ssa::SSAVar::new("tmp:sum", 1, 8),
                a: r2ssa::SSAVar::new("X8", 4, 8),
                b: r2ssa::SSAVar::new("X9", 7, 8),
            },
            r2ssa::SSAOp::Copy {
                dst: r2ssa::SSAVar::new("X0", 1, 8),
                src: r2ssa::SSAVar::new("tmp:sum", 1, 8),
            },
            r2ssa::SSAOp::Copy {
                dst: r2ssa::SSAVar::new("PC", 1, 8),
                src: r2ssa::SSAVar::new("X30", 0, 8),
            },
            r2ssa::SSAOp::Return {
                target: r2ssa::SSAVar::new("PC", 1, 8),
            },
        ]);
        let signature = Some(signature_spec(
            Some(r2dec::CType::Int(64)),
            vec![
                (
                    "arg1",
                    Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Void))),
                ),
                ("arg2", Some(r2dec::CType::Int(32))),
                ("arg3", Some(r2dec::CType::Int(32))),
            ],
        ));

        let (signature, type_db) = enrich_decompiler_type_context(
            std::slice::from_ref(&block),
            Some(&arch),
            64,
            signature,
            r2types::ExternalTypeDb::default(),
        );

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_struct_array_index");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::aarch64());
        decompiler.set_type_facts(r2types::FunctionTypeFacts {
            merged_signature: signature,
            external_type_db: type_db,
            ..r2types::FunctionTypeFacts::default()
        });
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("[arg2].f_8"),
            "expected indexed-member store rendering in decompiled output, got:\n{output}"
        );
        assert!(
            output.contains("[arg2].f_34"),
            "expected indexed-member load rendering in decompiled output, got:\n{output}"
        );
        assert!(
            !output.contains("arg1 ="),
            "indexed-member load path should not synthesize a bogus parameter assignment, got:\n{output}"
        );
        assert!(
            !output.contains("\nx8 =") && !output.contains("\nstack_"),
            "dead register or stack artifacts should not leak into decompiled output, got:\n{output}"
        );
    }

    #[test]
    fn live_arm64_array_index_decompile_keeps_plain_subscript_without_flag_noise() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let block = live_arm64_array_index_block(false);
        let signature = Some(signature_spec(
            Some(r2dec::CType::Int(64)),
            vec![
                (
                    "arg1",
                    Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Void))),
                ),
                ("arg2", Some(r2dec::CType::Int(32))),
            ],
        ));

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_array_index");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::aarch64());
        set_signature_facts(&mut decompiler, signature);
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("[arg2]"),
            "expected plain subscript rendering, got:\n{output}"
        );
        assert!(
            !output.contains("arg1 ="),
            "plain indexed load should not synthesize a bogus parameter assignment, got:\n{output}"
        );
        assert!(
            !output.contains(".p0"),
            "plain indexed load must not upgrade to a fake member, got:\n{output}"
        );
        assert!(
            !output.contains("tmpng")
                && !output.contains("tmpzr")
                && !output.contains("TMPCY")
                && !output.contains("TMPOV"),
            "dead arm64 flag temps should not leak into final output, got:\n{output}"
        );
        assert!(
            !output.contains("stack_8 =")
                && !output.contains("stack_4 =")
                && !output.contains("stack ="),
            "dead synthetic stack argument spills should not leak into final output, got:\n{output}"
        );
    }

    #[test]
    fn live_arm64_array_index_neg_decompile_keeps_negative_subscript_without_flag_noise() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let block = live_arm64_array_index_block(true);
        let signature = Some(signature_spec(
            Some(r2dec::CType::Int(64)),
            vec![
                (
                    "arg1",
                    Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Void))),
                ),
                ("arg2", Some(r2dec::CType::Int(32))),
            ],
        ));

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._test_array_index_neg");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::aarch64());
        set_signature_facts(&mut decompiler, signature);
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("[0 - arg2]") || output.contains("[-arg2]"),
            "expected negative subscript rendering, got:\n{output}"
        );
        assert!(
            !output.contains("arg1 ="),
            "negative indexed load should not synthesize a bogus parameter assignment, got:\n{output}"
        );
        assert!(
            !output.contains("[-0]"),
            "negative index must preserve the scalar index, got:\n{output}"
        );
        assert!(
            !output.contains("tmpng")
                && !output.contains("tmpzr")
                && !output.contains("TMPCY")
                && !output.contains("TMPOV"),
            "dead arm64 flag temps should not leak into final output, got:\n{output}"
        );
        assert!(
            !output.contains("stack_8 =")
                && !output.contains("stack_4 =")
                && !output.contains("stack ="),
            "dead synthetic stack argument spills should not leak into final output, got:\n{output}"
        );
    }

    #[test]
    fn detached_symbolic_branch_facts_prune_self_xor_guard_in_decompiler() {
        use r2il::{R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

        fn reg(offset: u64, size: u32) -> Varnode {
            Varnode {
                space: SpaceId::Register,
                offset,
                size,
                meta: None,
            }
        }

        fn konst(value: u64, size: u32) -> Varnode {
            Varnode {
                space: SpaceId::Const,
                offset: value,
                size,
                meta: None,
            }
        }

        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("EDI", 56, 4));
        arch.add_register(RegisterDef::new("RDI", 56, 8));

        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::IntXor {
                        dst: reg(0x80, 8),
                        a: reg(56, 8),
                        b: reg(56, 8),
                    },
                    R2ILOp::CBranch {
                        target: konst(0x1010, 8),
                        cond: reg(0x80, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: reg(0, 8),
                        src: konst(0, 8),
                    },
                    R2ILOp::Return { target: reg(0, 8) },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: reg(0, 8),
                        src: konst(1, 8),
                    },
                    R2ILOp::Return { target: reg(0, 8) },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let artifact = crate::types::build_detached_function_analysis_artifact(
            &blocks,
            "dbg.test_symbolic_xor_guard",
            Some(&arch),
            64,
            false,
            &HashMap::new(),
            "{}",
        )
        .expect("analysis artifact");

        let semantics = artifact
            .function_facts
            .semantics
            .as_ref()
            .expect("canonical semantics");
        assert_eq!(semantics.diagnostics.branches_pruned, 1);
        let native = semantics.native_body().expect("native semantics");
        assert_eq!(native.regions.len(), 1);
        let region = native.regions.values().next().expect("semantic region");
        assert!(region.targets.iter().any(|fact| {
            fact.value.status == r2sym::SymbolicReachabilityStatus::Unreachable
                && fact.value.branch_truth == Some(true)
        }));
        assert!(region.targets.iter().any(|fact| {
            fact.value.status == r2sym::SymbolicReachabilityStatus::Reachable
                && fact.value.branch_truth == Some(false)
        }));

        let decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        let output =
            decompiler.decompile_input(&crate::decompiler::decompiler_input_from_artifact(
                artifact,
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                64,
            ));

        assert!(
            output.contains("return 1;") || output.contains("return 0;"),
            "expected decompiled function body, got:\n{output}"
        );
        assert!(
            !output.contains("if ("),
            "symbolic branch facts should collapse the impossible guard, got:\n{output}"
        );
        assert!(
            !output.contains("return 1;"),
            "impossible self-xor branch should be removed, got:\n{output}"
        );
    }

    #[test]
    fn live_arm64_main_atoi_arg_keeps_semantic_root() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let block = r2ssa::SSABlock {
            addr: 0x100001000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::IntSub {
                    dst: r2ssa::SSAVar::new("SP", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 0, 8),
                    b: r2ssa::SSAVar::new("const:200", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:178", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:slot", 1, 8),
                    val: r2ssa::SSAVar::new("X1", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:slot", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:178", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:slot", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:arg", 1, 8),
                    a: r2ssa::SSAVar::new("X8", 1, 8),
                    b: r2ssa::SSAVar::new("const:8", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("X0", 1, 8),
                    space: "ram".to_string(),
                    addr: r2ssa::SSAVar::new("tmp:arg", 1, 8),
                },
                r2ssa::SSAOp::Call {
                    target: r2ssa::SSAVar::new("const:401040", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X0", 2, 8),
                    src: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("PC", 1, 8),
                    src: r2ssa::SSAVar::new("X30", 0, 8),
                },
                r2ssa::SSAOp::Return {
                    target: r2ssa::SSAVar::new("PC", 1, 8),
                },
            ],
        };

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._main");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::aarch64());
        set_signature_facts(
            &mut decompiler,
            Some(signature_spec(
                Some(r2dec::CType::Int(64)),
                vec![
                    ("arg1", Some(r2dec::CType::Int(32))),
                    (
                        "arg2",
                        Some(r2dec::CType::Pointer(Box::new(r2dec::CType::Pointer(
                            Box::new(r2dec::CType::Int(8)),
                        )))),
                    ),
                ],
            )),
        );
        decompiler.set_function_names(HashMap::from([(0x401040, "sym.imp.atoi".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.atoi".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                },
                params: vec![r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))],
                variadic: false,
            },
        )]));
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("sym.imp.atoi("),
            "expected imported atoi call, got:\n{output}"
        );
        assert!(
            output.contains("arg2") && !output.contains("stack_") && !output.contains("&stack"),
            "expected semantic argv-rooted atoi arg without stack placeholders, got:\n{output}"
        );
        assert!(
            !output.contains("atoi(*") && !output.contains("atoi(lr)"),
            "atoi imported arg should not regress to deref or transient register form, got:\n{output}"
        );
    }

    #[test]
    fn live_arm64_main_printf_format_arg_keeps_string_literal() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let block = r2ssa::SSABlock {
            addr: 0x100001100,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X8", 1, 8),
                    src: r2ssa::SSAVar::new("const:100002000", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("X0", 1, 8),
                    a: r2ssa::SSAVar::new("X8", 1, 8),
                    b: r2ssa::SSAVar::new("const:292", 0, 8),
                },
                r2ssa::SSAOp::Call {
                    target: r2ssa::SSAVar::new("const:401030", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("X0", 2, 8),
                    src: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("PC", 1, 8),
                    src: r2ssa::SSAVar::new("X30", 0, 8),
                },
                r2ssa::SSAOp::Return {
                    target: r2ssa::SSAVar::new("PC", 1, 8),
                },
            ],
        };

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("sym._main");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::aarch64());
        decompiler.set_function_names(HashMap::from([(0x401030, "sym.imp.printf".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.printf".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                },
                params: vec![r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))],
                variadic: true,
            },
        )]));
        decompiler.set_strings(HashMap::from([(
            0x100002292,
            "usage: vuln_test <n>\\n".to_string(),
        )]));
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("\"usage: vuln_test <n>\\\\n\""),
            "expected string literal printf arg, got:\n{output}"
        );
        assert!(
            !output.contains("0x100002000") && !output.contains("292"),
            "raw const-add format pointer should not survive, got:\n{output}"
        );
        assert!(
            !output.contains("printf(&stack)") && !output.contains("printf(0x"),
            "printf imported format arg should stay literalized, got:\n{output}"
        );
    }

    #[test]
    fn live_x86_main_printf_format_arg_keeps_string_literal() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let block = r2ssa::SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RDI", 1, 8),
                    src: r2ssa::SSAVar::new("const:40229e", 0, 8),
                },
                r2ssa::SSAOp::Call {
                    target: r2ssa::SSAVar::new("const:401030", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("RAX", 1, 8),
                    src: r2ssa::SSAVar::new("const:0", 0, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("PC", 1, 8),
                    src: r2ssa::SSAVar::new("RIP", 0, 8),
                },
                r2ssa::SSAOp::Return {
                    target: r2ssa::SSAVar::new("PC", 1, 8),
                },
            ],
        };

        let mut raw = R2ILBlock::new(block.addr, block.size);
        raw.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).expect("ssa function");
        func.get_block_mut(block.addr).expect("entry block").ops = block.ops;
        func = func.with_name("dbg.main");

        let mut decompiler = r2dec::Decompiler::new(r2dec::DecompilerConfig::x86_64());
        decompiler.set_function_names(HashMap::from([(0x401030, "sym.imp.printf".to_string())]));
        decompiler.set_known_function_signatures(HashMap::from([(
            "sym.imp.printf".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                },
                params: vec![r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))],
                variadic: true,
            },
        )]));
        decompiler.set_strings(HashMap::from([(
            0x40229e,
            "Unknown test: %d\\n".to_string(),
        )]));
        let output = decompiler.decompile(&func);

        assert!(
            output.contains("\"Unknown test: %d\\\\n\""),
            "expected x86 string literal printf arg, got:\n{output}"
        );
        assert!(
            !output.contains("printf(0x") && !output.contains("atoi(*rax)"),
            "x86 imported-call rendering must not regress to raw literal or deref arg, got:\n{output}"
        );
        assert!(
            !output.contains("printf(&stack)"),
            "x86 imported-call rendering must not regress to stack placeholder args, got:\n{output}"
        );
    }
}
