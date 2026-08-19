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
mod ffi_v2;
mod helpers;
#[cfg(test)]
mod plain_o2_lift_fixtures;
mod types;

use ffi_v2::R2SleighEngineRequestPayloadV2;

#[cfg(test)]
use analysis::ssa::{r2il_block_defuse_json, r2il_block_to_ssa_json};
use r2il::{ArchSpec, R2ILBlock, R2ILOp, SwitchCase, SwitchInfo, Varnode, validate_block_full};
use r2sleigh_export::{
    ExportFormat, InstructionAction, InstructionExportInput, SSA_JSON_SCHEMA_VERSION, SSAOpInfo,
    export_instruction, op_json_named, ssa_op_to_info,
};
use r2sleigh_lift::{Disassembler, SemanticMetadataOptions, build_arch_spec};
#[cfg(test)]
use r2types::recover_vars_arch_profile;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;
use std::slice;
#[cfg(test)]
use types::parse_const_value;
#[cfg(test)]
use types::{size_to_type, ssa_var_block_key};

/// Opaque context handle for C API.
pub struct R2ILContext {
    arch: Option<ArchSpec>,
    arch_name_cstr: Option<CString>,
    disasm: Option<Disassembler>,
    semantic_metadata_enabled: bool,
    error: Option<CString>,
}

type R2ILSwitchCaseFfi = ffi_v2::R2SleighSwitchCaseV2;

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

/// Initialize a context from a built-in architecture (Sleigh via sleigh-config).
///
/// Returns NULL on failure.
pub(crate) fn r2il_arch_init(arch: *const c_char) -> *mut R2ILContext {
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

/// Check if the context has a loaded architecture.
///
/// Returns 1 if loaded, 0 otherwise.
pub(crate) fn r2il_is_loaded(ctx: *const R2ILContext) -> i32 {
    if ctx.is_null() {
        return 0;
    }

    unsafe { if (*ctx).arch.is_some() { 1 } else { 0 } }
}

/// Get the architecture name.
///
/// Returns NULL if not loaded.
pub(crate) fn r2il_arch_name(ctx: *const R2ILContext) -> *const c_char {
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
pub(crate) fn r2il_error(ctx: *const R2ILContext) -> *const c_char {
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

/// Build the register profile for the V2 ownership wrapper.
pub(crate) fn r2il_get_reg_profile(ctx: *const R2ILContext) -> *mut c_char {
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

    let first_existing_at_width = |candidates: &[&str], bits: u32| -> Option<String> {
        candidates.iter().find_map(|name| {
            reg_meta
                .get(*name)
                .filter(|(candidate_bits, _, _)| *candidate_bits == bits)
                .map(|(_, _, original)| original.clone())
        })
    };

    let is_x86 = matches!(arch_name.as_str(), "x86" | "x86-64");
    let address_bits = arch.addr_size.checked_mul(8);
    let (pc, sp, bp) = if is_x86 {
        (
            address_bits.and_then(|bits| first_existing_at_width(&["rip", "eip", "ip"], bits)),
            address_bits.and_then(|bits| first_existing_at_width(&["rsp", "esp", "sp"], bits)),
            address_bits.and_then(|bits| first_existing_at_width(&["rbp", "ebp", "bp"], bits)),
        )
    } else {
        (
            first_existing(&["pc", "$pc", "rip", "eip", "ip"]),
            first_existing(&["sp", "$sp", "rsp", "esp"]),
            first_existing(&["bp", "rbp", "ebp", "fp", "$fp", "s8", "$s8", "x29"]),
        )
    };

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
pub(crate) fn r2il_lift(
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
pub(crate) fn r2il_lift_block(
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

/// Enable/disable semantic metadata auto-population during lifting.
pub(crate) fn r2il_set_semantic_metadata_enabled(ctx: *mut R2ILContext, enabled: bool) {
    if ctx.is_null() {
        return;
    }
    let ctx_ref = unsafe { &mut *ctx };
    ctx_ref.semantic_metadata_enabled = enabled;
}

/// Validate a lifted block against full (structural + semantic) r2il invariants.
///
/// Returns 1 when valid, 0 on invalid input or validation failure.
/// On validation failure, the context error string is updated.
pub(crate) fn r2il_block_validate(ctx: *mut R2ILContext, block: *const R2ILBlock) -> i32 {
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

/// Attach radare2 switch/jump-table facts to a lifted block.
///
/// Returns 1 when switch metadata was accepted, 0 when the input is absent or
/// cannot satisfy the r2il switch invariants.
pub(crate) struct R2ILSwitchInfoInput {
    pub(crate) block: *mut R2ILBlock,
    pub(crate) switch_addr: u64,
    pub(crate) min_val: u64,
    pub(crate) max_val: u64,
    pub(crate) default_target: u64,
    pub(crate) has_default: i32,
    pub(crate) cases: *const R2ILSwitchCaseFfi,
    pub(crate) case_count: usize,
}

pub(crate) fn r2il_block_set_switch_info(input: R2ILSwitchInfoInput) -> i32 {
    let R2ILSwitchInfoInput {
        block,
        switch_addr,
        min_val,
        max_val,
        default_target,
        has_default,
        cases,
        case_count,
    } = input;
    if block.is_null() || cases.is_null() || case_count == 0 {
        return 0;
    }

    let case_slice = unsafe { slice::from_raw_parts(cases, case_count) };
    let mut normalized = case_slice
        .iter()
        .filter_map(|case| {
            if case.target == u64::MAX {
                None
            } else {
                Some(SwitchCase {
                    value: case.value,
                    target: case.target,
                })
            }
        })
        .collect::<Vec<_>>();
    if normalized.is_empty() {
        return 0;
    }

    normalized.sort_by_key(|case| (case.value, case.target));
    normalized.dedup();
    if normalized
        .windows(2)
        .any(|window| window[0].value == window[1].value)
    {
        return 0;
    }

    let actual_min = normalized.first().map(|case| case.value).unwrap_or(0);
    let actual_max = normalized.last().map(|case| case.value).unwrap_or(0);
    let supplied_range_valid = min_val <= max_val
        && normalized
            .iter()
            .all(|case| case.value >= min_val && case.value <= max_val);
    let (range_min, range_max) = if supplied_range_valid {
        (min_val, max_val)
    } else {
        (actual_min, actual_max)
    };

    let default_target = if has_default != 0 && default_target != u64::MAX {
        Some(default_target)
    } else {
        None
    };

    let info = SwitchInfo {
        switch_addr,
        min_val: range_min,
        max_val: range_max,
        default_target,
        cases: normalized,
    };
    unsafe {
        (*block).set_switch_info(info);
    }
    1
}

/// Get the number of operations in a block.
pub(crate) fn r2il_block_op_count(block: *const R2ILBlock) -> usize {
    if block.is_null() {
        return 0;
    }
    unsafe { (*block).ops.len() }
}

type R2ILDirectCallIdentity = ffi_v2::R2SleighDirectCallIdentityV2;

/// Resolve one raw call instruction to exactly one lifted direct call.
/// Returns 1 on an exact match, 0 when absent, and -1 when ambiguous or when
/// the raw target disagrees with the lifted constant target.
pub(crate) fn r2il_block_direct_call_identity(
    block: *const R2ILBlock,
    raw_instruction_addr: u64,
    raw_target_addr: u64,
    output: *mut R2ILDirectCallIdentity,
) -> i32 {
    if block.is_null() || output.is_null() {
        return -1;
    }
    let block = unsafe { &*block };
    let mut selected = None;
    for (op_index, op) in block.ops.iter().enumerate() {
        let R2ILOp::Call { target } = op else {
            continue;
        };
        if block
            .op_metadata(op_index)
            .and_then(|metadata| metadata.instruction_addr)
            != Some(raw_instruction_addr)
        {
            continue;
        }
        if selected.is_some()
            || !matches!(target.space, r2il::SpaceId::Const)
            || target.offset != raw_target_addr
            || target.size == 0
        {
            return -1;
        }
        selected = Some((op_index, target));
    }
    let Some((op_index, target)) = selected else {
        return 0;
    };
    let (target_space, target_custom_space) = match target.space {
        r2il::SpaceId::Ram => (ffi_v2::R2SLEIGH_SOURCE_STORAGE_RAM_V2, 0),
        r2il::SpaceId::Register => (ffi_v2::R2SLEIGH_SOURCE_STORAGE_REGISTER_V2, 0),
        r2il::SpaceId::Unique => (ffi_v2::R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2, 0),
        r2il::SpaceId::Const => (ffi_v2::R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2, 0),
        r2il::SpaceId::Custom(id) => (ffi_v2::R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2, id),
    };
    unsafe {
        *output = R2ILDirectCallIdentity {
            op_index,
            target_space,
            target_custom_space,
            target_offset: target.offset,
            target_size: target.size,
        };
    }
    1
}

/// Get the ESIL string for a block (one line per op, joined with ';').
pub(crate) fn r2il_block_to_esil(ctx: *const R2ILContext, block: *const R2ILBlock) -> *mut c_char {
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
        Ok(esil) => CString::new(esil).map_or(ptr::null_mut(), |s| s.into_raw()),
        Err(_) => ptr::null_mut(),
    }
}

/// Get a JSON representation of an operation with register names resolved.
pub(crate) fn r2il_block_op_json_named(
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
pub(crate) fn r2il_block_size(block: *const R2ILBlock) -> u32 {
    if block.is_null() {
        return 0;
    }
    unsafe { (*block).size }
}

/// Get the block address.
pub(crate) fn r2il_block_addr(block: *const R2ILBlock) -> u64 {
    if block.is_null() {
        return 0;
    }
    unsafe { (*block).addr }
}

/// Build the disassembly mnemonic for the V2 ownership wrapper.
pub(crate) fn r2il_block_mnemonic(
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
pub(crate) fn r2il_block_type(block: *const R2ILBlock) -> u32 {
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
pub(crate) fn r2il_block_jump(block: *const R2ILBlock) -> u64 {
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
pub(crate) fn r2il_block_fail(block: *const R2ILBlock) -> u64 {
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

#[cfg(test)]
fn drop_test_ffi_string(s: *mut c_char) {
    if !s.is_null() {
        unsafe { drop(CString::from_raw(s)) };
    }
}

#[cfg(test)]
fn drop_test_context(context: *mut R2ILContext) {
    if !context.is_null() {
        unsafe { drop(Box::from_raw(context)) };
    }
}

#[cfg(test)]
fn drop_test_block(block: *mut R2ILBlock) {
    if !block.is_null() {
        unsafe { drop(Box::from_raw(block)) };
    }
}

// ========== Typed Analysis FFI ==========

use std::collections::{BTreeSet, HashMap, HashSet};

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
    op.inputs()
        .into_iter()
        .filter(|varnode| varnode.is_register())
        .collect()
}

/// Helper: extract all register varnodes that are written by an operation.
fn op_regs_write(op: &R2ILOp) -> Vec<&Varnode> {
    op.output()
        .into_iter()
        .filter(|varnode| varnode.is_register())
        .collect()
}

/// Get registers read by the block as JSON array of names.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2il_block_regs_read(
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

const R2IL_MEMORY_ACCESS_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, serde::Serialize)]
struct R2ILMemoryStackAddress {
    base: String,
    offset: i64,
}

#[derive(Debug, Default, serde::Serialize)]
struct R2ILMemoryAccessSemantics {
    #[serde(skip_serializing_if = "Option::is_none")]
    guarded: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ordering: Option<r2il::MemoryOrdering>,
    #[serde(skip_serializing_if = "Option::is_none")]
    atomic_kind: Option<r2il::AtomicKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_class: Option<r2il::MemoryClass>,
    #[serde(skip_serializing_if = "Option::is_none")]
    permissions: Option<r2il::MemoryPermissions>,
    #[serde(skip_serializing_if = "Option::is_none")]
    range: Option<r2il::MemoryRange>,
    #[serde(skip_serializing_if = "Option::is_none")]
    bank_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    segment_id: Option<String>,
}

#[derive(Debug, serde::Serialize)]
struct R2ILMemoryAccess {
    schema_version: u32,
    #[serde(rename = "type")]
    access_type: &'static str,
    size_bytes: u32,
    address: serde_json::Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    stack_address: Option<R2ILMemoryStackAddress>,
    #[serde(skip_serializing_if = "Option::is_none")]
    value: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    expected: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    replacement: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    guard: Option<serde_json::Value>,
    #[serde(flatten)]
    semantics: R2ILMemoryAccessSemantics,
}

impl R2ILMemoryAccess {
    fn new(access_type: &'static str, size_bytes: u32, address: serde_json::Value) -> Self {
        Self {
            schema_version: R2IL_MEMORY_ACCESS_SCHEMA_VERSION,
            access_type,
            size_bytes,
            address,
            stack_address: None,
            value: None,
            expected: None,
            replacement: None,
            result: None,
            guard: None,
            semantics: R2ILMemoryAccessSemantics::default(),
        }
    }
}

/// Get memory accesses by the block as one canonical JSON array.
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2il_block_mem_access(
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

    let apply_semantics = |access: &mut R2ILMemoryAccess,
                           op_index: usize,
                           space_id: Option<r2il::SpaceId>,
                           ordering: Option<r2il::MemoryOrdering>,
                           atomic_kind: Option<r2il::AtomicKind>,
                           guarded: bool| {
        access.semantics.guarded = guarded.then_some(true);
        access.semantics.ordering = ordering.or_else(|| {
            blk.op_metadata
                .get(&op_index)
                .and_then(|m| m.memory_ordering)
        });
        access.semantics.atomic_kind =
            atomic_kind.or_else(|| blk.op_metadata.get(&op_index).and_then(|m| m.atomic_kind));
        if let Some(meta) = blk.op_metadata.get(&op_index) {
            access.semantics.memory_class = meta.memory_class;
            access.semantics.permissions = meta.permissions;
            access.semantics.range = meta.valid_range;
            access.semantics.bank_id = meta.bank_id.clone();
            access.semantics.segment_id = meta.segment_id.clone();
        }

        if let Some(space_id) = space_id
            && let Some(arch) = ctx_ref.arch.as_ref()
            && let Some(space) = arch.spaces.iter().find(|s| s.id == space_id)
        {
            if let Some(memory_class) = space.memory_class {
                access.semantics.memory_class = Some(memory_class);
            }
            if access.semantics.permissions.is_none() {
                access.semantics.permissions = space.permissions;
            }
            if access.semantics.range.is_none() {
                access.semantics.range = space.valid_ranges.first().copied();
            }
            if access.semantics.bank_id.is_none() {
                access.semantics.bank_id = space.bank_id.clone();
            }
            if access.semantics.segment_id.is_none() {
                access.semantics.segment_id = space.segment_id.clone();
            }
        }
    };

    for (op_index, op) in blk.ops.iter().enumerate() {
        match op {
            R2ILOp::Load { dst, space, addr } => {
                let Some(address) = varnode_to_json(addr, disasm) else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("load", dst.size, address);

                if let Some((base, offset)) = resolve_stack_addr(addr, disasm, &defs, &blk.ops) {
                    access.stack_address = Some(R2ILMemoryStackAddress { base, offset });
                }

                apply_semantics(&mut access, op_index, Some(*space), None, None, false);
                accesses.push(access);
            }
            R2ILOp::LoadLinked {
                dst,
                space,
                addr,
                ordering,
            } => {
                let Some(address) = varnode_to_json(addr, disasm) else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("load_linked", dst.size, address);
                apply_semantics(
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
                let (Some(address), Some(value)) =
                    (varnode_to_json(addr, disasm), varnode_to_json(val, disasm))
                else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("store", val.size, address);
                access.value = Some(value);

                if let Some((base, offset)) = resolve_stack_addr(addr, disasm, &defs, &blk.ops) {
                    access.stack_address = Some(R2ILMemoryStackAddress { base, offset });
                }

                apply_semantics(&mut access, op_index, Some(*space), None, None, false);
                accesses.push(access);
            }
            R2ILOp::StoreConditional {
                result,
                space,
                addr,
                val,
                ordering,
            } => {
                let (Some(address), Some(value)) =
                    (varnode_to_json(addr, disasm), varnode_to_json(val, disasm))
                else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("store_conditional", val.size, address);
                access.value = Some(value);
                access.result = match result {
                    Some(dst) => {
                        let Some(result) = varnode_to_json(dst, disasm) else {
                            return ptr::null_mut();
                        };
                        Some(result)
                    }
                    None => None,
                };
                apply_semantics(
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
                let (Some(address), Some(expected), Some(replacement), Some(result)) = (
                    varnode_to_json(addr, disasm),
                    varnode_to_json(expected, disasm),
                    varnode_to_json(replacement, disasm),
                    varnode_to_json(dst, disasm),
                ) else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("atomic_cas", dst.size, address);
                access.expected = Some(expected);
                access.replacement = Some(replacement);
                access.result = Some(result);
                apply_semantics(
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
                let (Some(address), Some(guard)) = (
                    varnode_to_json(addr, disasm),
                    varnode_to_json(guard, disasm),
                ) else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("load_guarded", dst.size, address);
                access.guard = Some(guard);
                apply_semantics(
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
                let (Some(address), Some(value), Some(guard)) = (
                    varnode_to_json(addr, disasm),
                    varnode_to_json(val, disasm),
                    varnode_to_json(guard, disasm),
                ) else {
                    return ptr::null_mut();
                };
                let mut access = R2ILMemoryAccess::new("store_guarded", val.size, address);
                access.value = Some(value);
                access.guard = Some(guard);
                apply_semantics(
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
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2il_block_varnodes(ctx: *const R2ILContext, block: *const R2ILBlock) -> *mut c_char {
    if ctx.is_null() || block.is_null() {
        return ptr::null_mut();
    }

    let ctx_ref = unsafe { &*ctx };
    let disasm = match &ctx_ref.disasm {
        Some(d) => d,
        None => return ptr::null_mut(),
    };

    let blk = unsafe { &*block };
    let mut seen: HashSet<VarnodeKey> = HashSet::new();
    let mut varnodes: Vec<VarnodeInfo> = Vec::new();

    for op in &blk.ops {
        for vn in op_all_varnodes(op) {
            if !seen.insert(varnode_key(vn)) {
                continue;
            }

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

pub(crate) fn r2il_block_values_typed(
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

pub(crate) fn r2il_block_values_memory(
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

pub(crate) fn r2il_block_values_immediates(
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

pub(crate) fn r2il_block_values_reg_reads(
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

pub(crate) fn r2il_block_values_reg_writes(
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

pub(crate) fn r2il_block_values_free(values: *mut R2ILBlockAnalValues) {
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
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
/// Internal V2 wrapper immediately adopts the returned CString allocation.
pub(crate) fn r2il_block_regs_write(
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

// Symbolic execution and CFG surfaces are implemented under r2plugin/src/analysis/.

// ============================================================================
// Decompiler Functions
// ============================================================================

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
                    .and_then(|raw| parse_external_type(raw, ptr_bits)),
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
fn parse_external_type(raw_ty: &str, ptr_bits: u32) -> Option<r2types::CTypeLike> {
    r2types::parse_external_type_like_spec(raw_ty, ptr_bits)
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
                    .and_then(|raw| parse_external_type(raw, ptr_bits)),
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
        .and_then(|raw| parse_external_type(raw, ptr_bits));

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
                .and_then(|raw| parse_external_type(raw, ptr_bits)),
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

#[derive(Debug)]
pub(crate) struct EngineV2Output {
    pub(crate) output: String,
    pub(crate) metrics: r2engine::EngineMetrics,
    pub(crate) diagnostics: r2engine::EngineDiagnostics,
}

/// The name the source gives this function, when it gives one.
///
/// radare2 already knows what the function is called -- from a symbol, from
/// debug information, from a name the user set -- and the snapshot carries it.
/// Deriving a name from the entry address instead discards that and prints
/// `fcn_1000006b0` for a function the rest of the session calls
/// `dbg.process_string`. A name radare2 generated from the address itself
/// carries no more than the address does, so it is not preferred to our own.
fn source_function_name(trusted: &r2ssa::TrustedSsaArtifact) -> String {
    let function_addr = trusted.source().function().address();
    let named = trusted.source().presentation().display_name();
    if named.is_empty() || r2source::display_names::is_generated_function_name(named) {
        return format!("fcn_{function_addr:x}");
    }
    named.to_string()
}

fn trusted_engine_function_input(
    trusted: &r2ssa::TrustedSsaArtifact,
) -> r2engine::EngineFunctionInput {
    let function_addr = trusted.source().function().address();
    r2engine::EngineFunctionInput {
        function_name: source_function_name(trusted),
        function_addr,
        blocks: trusted.source_blocks().to_vec(),
        arch: Some(trusted.arch_spec().clone()),
        semantic_metadata_enabled: true,
        source_snapshot: None,
    }
}

fn r2sleigh_engine_decompile_trusted_output(
    _input: &R2SleighEngineRequestPayloadV2,
    trusted: std::sync::Arc<r2ssa::TrustedSsaArtifact>,
    execution: r2engine::EngineExecutionControl,
) -> Option<EngineV2Output> {
    let block_count = trusted.source_blocks().len();
    let function_input = trusted_engine_function_input(&trusted);
    let ptr_bits = helpers::effective_ptr_bits(trusted.arch_spec());
    let decompile_input = r2engine::EngineFunctionDecompileRequestInput::single_function(
        function_input,
        Some(ptr_bits),
        r2types::ParsedExternalContext::default(),
    )
    .with_input_quality(r2engine::EngineFunctionInputQuality::complete(block_count))
    .with_execution_control(execution)
    .with_trusted_ssa(trusted);
    let response = decompiler::run_engine_decompile(decompile_input);
    Some(EngineV2Output {
        output: response.output,
        metrics: response.metrics,
        diagnostics: response.diagnostics,
    })
}

fn r2sleigh_engine_type_function_trusted_output(
    _input: &R2SleighEngineRequestPayloadV2,
    trusted: std::sync::Arc<r2ssa::TrustedSsaArtifact>,
    execution: r2engine::EngineExecutionControl,
) -> Option<EngineV2Output> {
    let function_addr = trusted.source().function().address();
    let function_name = source_function_name(&trusted);
    let ptr_bits = helpers::effective_ptr_bits(trusted.arch_spec());
    let policy = r2engine::analysis_policy_for_radare2_depth(0);
    let writeback_budget = r2types::TypeWritebackMutationBudget::new(
        policy.type_global_max_links,
        policy.type_max_decls,
        policy.type_max_mutations,
    );
    let writeback_apply_policy =
        r2engine::type_writeback_apply_policy_for_mode(policy.type_writeback_mode);
    let mut request = r2engine::EngineFunctionAnalysisReportRequest::full_semantics_for_function(
        r2engine::EngineFunctionAnalysisReportRequestInput {
            function: trusted_engine_function_input(&trusted),
            ptr_bits: Some(ptr_bits),
            parsed_context: r2types::ParsedExternalContext::default(),
            interproc_max_iters: 1,
            interproc_converged: false,
            symbolic_scope: None,
            writeback_budget,
            writeback_apply_policy,
        },
    );
    request.analysis = request
        .analysis
        .with_execution_control(execution)
        .with_trusted_ssa(trusted);
    let response = match r2engine::EngineSession::new().type_function_checked(
        r2engine::EngineTypeAnalysisRequest::from_interproc_budget(request.analysis, 1, false),
    ) {
        Ok(response) => response,
        Err(refusal) => {
            return Some(EngineV2Output {
                output: serde_json::json!({
                    "refused": true,
                    "reason": refusal.reason,
                })
                .to_string(),
                metrics: *refusal.metrics,
                diagnostics: *refusal.diagnostics,
            });
        }
    };
    let metrics = response.metrics().clone();
    let diagnostics = response.diagnostics().clone();
    let report = r2engine::function_analysis_report_payload_from_type_response(
        function_name,
        function_addr,
        response,
        writeback_budget,
        writeback_apply_policy,
    );
    let type_writeback = r2engine::type_writeback_report_json_from_function_analysis(
        r2engine::EngineFunctionAnalysisTypeWritebackJsonRequest {
            report: &report,
            iterations: 1,
            max_iterations: 1,
            converged: false,
            scope_report: None,
            symbolic_scope: None,
        },
    );
    Some(EngineV2Output {
        output: serde_json::to_string(&type_writeback).ok()?,
        metrics,
        diagnostics,
    })
}

// ============================================================================
// radare2 Deep Integration FFI - Type Evidence and Data Refs
// ============================================================================

#[cfg(test)]
type TypeEvidence = r2types::SignatureTypeEvidence;

#[cfg(test)]
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct InferredParamJson {
    name: String,
    #[serde(rename = "type")]
    param_type: String,
}

#[cfg(test)]
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
#[cfg(test)]
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
#[cfg(test)]
struct StructFieldCandidateJson {
    name: String,
    offset: u64,
    #[serde(rename = "type")]
    field_type: String,
    confidence: u8,
}

#[derive(Debug, serde::Serialize)]
#[cfg(test)]
struct StructDeclCandidateJson {
    name: String,
    decl: String,
    confidence: u8,
    source: String,
    fields: Vec<StructFieldCandidateJson>,
}

#[derive(Debug, serde::Serialize)]
#[cfg(test)]
struct GlobalTypeLinkCandidateJson {
    addr: u64,
    #[serde(rename = "type")]
    target_type: String,
    confidence: u8,
    source: String,
}

#[derive(Debug, serde::Serialize, Default)]
#[cfg(test)]
struct TypeWritebackDiagnosticsJson {
    conflicts: Vec<String>,
    warnings: Vec<String>,
    solver_warnings: Vec<String>,
}

#[cfg(test)]
type InterprocSummaryJson = r2engine::EngineInterprocSummaryJson;

#[repr(C)]
#[cfg(test)]
pub struct R2SleighTypeWritebackApplyPolicy {
    schema_version: u32,
    mode: u32,
}

#[cfg(test)]
const R2SLEIGH_TYPE_WRITEBACK_OFF: u32 = 0;
#[cfg(test)]
const R2SLEIGH_TYPE_WRITEBACK_BALANCED: u32 = 1;
#[cfg(test)]
const R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE: u32 = 2;

#[cfg(test)]
fn type_writeback_apply_policy_from_ffi(
    policy: &R2SleighTypeWritebackApplyPolicy,
) -> r2types::TypeWritebackApplyPolicy {
    let mode = match policy.mode {
        R2SLEIGH_TYPE_WRITEBACK_BALANCED => r2engine::EngineTypeWritebackMode::Balanced,
        R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE => r2engine::EngineTypeWritebackMode::Aggressive,
        _ => r2engine::EngineTypeWritebackMode::Off,
    };
    r2engine::type_writeback_apply_policy_for_mode(mode)
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

#[cfg(test)]
const SIG_WRITEBACK_CONFIDENCE_MIN: u8 = 70;
#[cfg(test)]
const CC_WRITEBACK_CONFIDENCE_MIN: u8 = 80;

#[cfg(test)]
fn merge_initial_type_evidence(initial_ty: &r2types::CTypeLike, evidence: &mut TypeEvidence) {
    r2types::merge_initial_signature_type_evidence(initial_ty, evidence);
}

#[cfg(test)]
fn materialize_signature_type_like(ty: r2types::CTypeLike, ptr_bits: u32) -> r2types::CTypeLike {
    r2types::materialize_signature_type_like(ty, ptr_bits)
}

#[cfg(test)]
fn resolve_evidence_driven_type(
    initial_ty: r2types::CTypeLike,
    var_size_bytes: u32,
    ptr_bits: u32,
    evidence: &TypeEvidence,
) -> r2types::CTypeLike {
    r2types::resolve_evidence_driven_signature_type(initial_ty, var_size_bytes, ptr_bits, evidence)
}

#[cfg(test)]
fn collect_type_evidence_for_var(
    evidence_ctx: &r2types::SignatureTypeEvidenceContext,
    var: &r2ssa::SSAVar,
    initial_ty: &r2types::CTypeLike,
) -> TypeEvidence {
    r2types::collect_signature_type_evidence_for_var(evidence_ctx, var, initial_ty)
}

#[cfg(test)]
fn fallback_scalar_type(
    var_size_bytes: u32,
    evidence: &TypeEvidence,
    ptr_bits: u32,
) -> r2types::CTypeLike {
    r2types::resolve_evidence_driven_signature_type(
        r2types::CTypeLike::Unknown,
        var_size_bytes,
        ptr_bits,
        evidence,
    )
}

#[cfg(test)]
fn sanitize_inferred_param_type(
    ty: r2types::CTypeLike,
    var_size_bytes: u32,
    ptr_bits: u32,
) -> r2types::CTypeLike {
    r2types::resolve_evidence_driven_signature_type(
        ty,
        var_size_bytes,
        ptr_bits,
        &TypeEvidence::default(),
    )
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
) -> (r2types::CTypeLike, TypeEvidence) {
    r2types::infer_signature_return_type(func, type_inference, ptr_bits, evidence_ctx)
}

#[cfg(test)]
#[allow(dead_code)]
fn collect_version0_input_regs(
    func: &r2ssa::SSAFunction,
) -> std::collections::HashMap<String, u32> {
    r2types::collect_version0_input_regs(func)
}

#[cfg(test)]
fn compute_callconv_inference(
    arch_name: &str,
    input_counts: &std::collections::HashMap<String, u32>,
) -> (String, u8) {
    r2types::compute_callconv_inference(arch_name, input_counts)
}

#[cfg(test)]
fn is_informative_type(ty: &r2types::CTypeLike) -> bool {
    !matches!(ty, r2types::CTypeLike::Void | r2types::CTypeLike::Unknown)
}

#[cfg(test)]
fn explicit_signature_context_strength(sig: &r2types::FunctionSignatureSpec) -> u8 {
    let typed_params = sig
        .params
        .iter()
        .filter(|param| param.ty.as_ref().is_some_and(is_informative_type))
        .count() as u8;
    let has_ret = sig.ret_type.as_ref().is_some_and(is_informative_type);
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
fn estimate_parsed_c_type_size_bytes(ty: &r2types::CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        r2types::CTypeLike::Void => Some(0),
        r2types::CTypeLike::Bool => Some(1),
        r2types::CTypeLike::Int { bits, .. } | r2types::CTypeLike::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        r2types::CTypeLike::Pointer(_) | r2types::CTypeLike::Function => {
            Some((ptr_bits / 8).max(1) as u64)
        }
        r2types::CTypeLike::Array(inner, Some(count)) => {
            estimate_parsed_c_type_size_bytes(inner, ptr_bits)
                .map(|inner_size| inner_size.saturating_mul(*count as u64))
        }
        r2types::CTypeLike::Array(inner, None) => {
            estimate_parsed_c_type_size_bytes(inner, ptr_bits)
        }
        r2types::CTypeLike::Enum(_) => Some(4),
        r2types::CTypeLike::Struct(_)
        | r2types::CTypeLike::Union(_)
        | r2types::CTypeLike::Typedef(_)
        | r2types::CTypeLike::Unknown => None,
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
    let (arg_regs, _, _) = recover_vars_arch_profile(arch.map(|spec| spec.name.as_str()));
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
fn test_stack_register_names(arch: Option<&ArchSpec>, ptr_bits: u32) -> (String, String) {
    let arch_name = arch
        .map(|arch| arch.name.to_ascii_lowercase())
        .unwrap_or_default();
    match arch_name.as_str() {
        name if name.contains("x86-64") || name.contains("amd64") => {
            ("rsp".to_string(), "rbp".to_string())
        }
        name if name.contains("x86") || name.contains("i386") => {
            if ptr_bits >= 64 {
                ("rsp".to_string(), "rbp".to_string())
            } else {
                ("esp".to_string(), "ebp".to_string())
            }
        }
        name if name.contains("aarch64") || name.contains("arm64") => {
            ("sp".to_string(), "fp".to_string())
        }
        _ => ("sp".to_string(), "fp".to_string()),
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
    let (sp_name, fp_name) = test_stack_register_names(arch, ptr_bits);
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
    let kind = r2ssa::SSAVarNameKind::classify(&lower);
    !matches!(
        kind,
        r2ssa::SSAVarNameKind::Temporary
            | r2ssa::SSAVarNameKind::Constant
            | r2ssa::SSAVarNameKind::Memory
            | r2ssa::SSAVarNameKind::AddressSpace
    ) && !is_filtered_cpu_flag_name_lower(&lower)
}

/// Annotation entry for analyze_fcn writeback.
struct FcnAnnotation {
    addr: u64,
    comment: String,
}

fn function_annotations_for_ffi(
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
) -> Option<Vec<FcnAnnotation>> {
    let input = types::build_function_input(ctx, blocks, num_blocks)?;

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

pub(crate) fn r2sleigh_analyze_fcn_annotations_typed(
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

pub(crate) fn r2sleigh_annotations_items(
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

pub(crate) fn r2sleigh_annotations_free(annotations: *mut R2SleighAnnotations) {
    if !annotations.is_null() {
        unsafe {
            drop(Box::from_raw(annotations));
        }
    }
}

#[cfg(test)]
fn signature_spec(
    ret_type: Option<r2types::CTypeLike>,
    params: Vec<(&str, Option<r2types::CTypeLike>)>,
) -> r2types::FunctionSignatureSpec {
    r2types::FunctionSignatureSpec {
        ret_type,
        params: params
            .into_iter()
            .map(|(name, ty)| r2types::FunctionParamSpec {
                name: name.to_string(),
                ty,
            })
            .collect(),
    }
}

#[cfg(test)]
fn signed_type(bits: u32) -> r2types::CTypeLike {
    r2types::CTypeLike::Int {
        bits,
        signedness: r2types::Signedness::Signed,
    }
}

#[cfg(test)]
fn unsigned_type(bits: u32) -> r2types::CTypeLike {
    r2types::CTypeLike::Int {
        bits,
        signedness: r2types::Signedness::Unsigned,
    }
}

#[cfg(test)]
fn ptr_type(inner: r2types::CTypeLike) -> r2types::CTypeLike {
    r2types::CTypeLike::Pointer(Box::new(inner))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;
    use std::ffi::{CStr, CString};

    #[test]
    fn varnode_dedup_key_preserves_full_custom_space_id() {
        let low = Varnode::new(r2il::SpaceId::Custom(0), 0x1234, 8);
        let high = Varnode::new(r2il::SpaceId::Custom(256), 0x1234, 8);

        assert_ne!(varnode_key(&low), varnode_key(&high));
        assert_eq!(
            HashSet::from([varnode_key(&low), varnode_key(&high)]).len(),
            2
        );
    }

    #[test]
    fn c_data_ref_query_refuses_mismatched_record_contract_before_cast() {
        let source = include_str!("../r_anal_sleigh.c");
        let table_size_check = source
            .find("api->struct_size != sizeof (*api)")
            .expect("C consumer must reject mismatched API tables");
        let record_size_check = source
            .find("api->data_ref_size != sizeof (R2SleighDataRef)")
            .expect("C consumer must reject mismatched data-ref strides");
        let record_schema_check = source
            .find("api->data_ref_schema_version != R2SLEIGH_DATA_REF_SCHEMA_V2")
            .expect("C consumer must reject mismatched data-ref schemas");
        let record_cast = source
            .find("const R2SleighDataRef *typed_items")
            .expect("C consumer must retain the typed data-ref boundary");

        assert!(table_size_check < record_size_check);
        assert!(record_size_check < record_cast);
        assert!(record_schema_check < record_cast);
    }

    fn signature_param_candidate(
        name: &str,
        ty: r2types::CTypeLike,
        arg_index: usize,
        size_bytes: u32,
        evidence: TypeEvidence,
    ) -> r2types::SignatureParamCandidate {
        r2types::SignatureParamCandidate {
            name: name.to_string(),
            ty,
            arg_index,
            size_bytes,
            evidence,
        }
    }

    #[test]
    fn c_plugin_does_not_invent_empty_decompile_fallback() {
        let c_source = include_str!("../r_anal_sleigh.c");
        let rust_decompiler_source = include_str!("decompiler.rs");

        assert!(
            !c_source.contains("empty decompilation output"),
            "C glue must not invent decompile fallback text; r2engine/rust output owns refusal policy"
        );
        assert!(
            !c_source.contains("r2dec fallback: empty"),
            "C glue must print engine output only, not synthesize fallback semantics"
        );
        assert!(
            !rust_decompiler_source.contains("/* r2dec:"),
            "Rust plugin decompile wrapper must not synthesize r2dec-looking refusal comments"
        );
        assert!(
            !rust_decompiler_source.contains("failed to spawn decompiler thread")
                && !rust_decompiler_source.contains("decompilation panicked"),
            "Rust plugin decompile wrapper must fail closed instead of owning decompile error text"
        );
    }

    #[test]
    fn c_plugin_decj_projects_v2_responses_and_refuses_without_borrowed_snapshot() {
        let c_source = include_str!("../r_anal_sleigh.c");
        let project_start = c_source
            .find("static char *sleigh_engine_execute_v2_project(")
            .expect("V2 response projector");
        let project_end = c_source[project_start..]
            .find("static char *sleigh_engine_execute_v2(")
            .map(|offset| project_start + offset)
            .expect("legacy V2 output wrapper");
        let project = &c_source[project_start..project_end];
        let bytes = project
            .find("api->response_bytes (response, &bytes)")
            .expect("opaque response bytes inspection");
        let json = project[bytes..]
            .find("sleigh_engine_v2_response_json (&info, bytes)")
            .map(|offset| bytes + offset)
            .expect("structured JSON projection");
        let free = project[json..]
            .find("sleigh_engine_v2_release_or_preserve (api, &response, &session)")
            .map(|offset| json + offset)
            .expect("opaque response owner release");
        assert!(
            bytes < json && json < free,
            "all borrowed output, diagnostics, and timing views must be projected before response_free"
        );
        assert!(
            project.contains("api->response_info (response, &info)"),
            "decj metadata must come from the V2 response inspection API"
        );

        let response_json_start = c_source
            .find("static char *sleigh_engine_v2_response_json(")
            .expect("decj response JSON builder");
        let response_json_end = c_source[response_json_start..]
            .find("static char *sleigh_engine_execute_v2_project(")
            .map(|offset| response_json_start + offset)
            .expect("V2 executor after JSON builder");
        let response_json = &c_source[response_json_start..response_json_end];
        for field in [
            "schema_version",
            "rendered_output",
            "diagnostics",
            "outcome",
            "phase_timings",
            "ffi_conversion_elapsed_us",
            "refused",
            "error",
        ] {
            assert!(
                response_json.contains(field),
                "decj schema must expose {field}"
            );
        }
        assert!(
            c_source.contains("sleigh_json_is_single_object (")
                && response_json.contains("r_json_parsedup (diagnostics_text)")
                && response_json.contains("diagnostics->type != R_JSON_OBJECT")
                && response_json.contains("pj_rj (pj, diagnostics)"),
            "diagnostics must be one complete object and emitted structurally, never as a double-encoded string"
        );
        assert!(
            !response_json.contains("pj_raw")
                && !response_json.contains("pj_ks (pj, \"diagnostics\""),
            "unparsed diagnostics must never be injected into decj JSON"
        );
        assert!(
            project.contains("!info.diagnostics_json.data || !info.diagnostics_json.len")
                && project.contains("invalid output or diagnostics in V2 response"),
            "missing or malformed diagnostics must fail closed"
        );

        let decj_route = c_source
            .find("cmd_matches_exact_or_arg (cmd, \"sla.decj\")")
            .expect("public decj command route");
        let dec_route = c_source
            .find("cmd_matches_exact_or_arg (cmd, \"sla.dec\")")
            .expect("legacy dec command route");
        assert!(
            decj_route < dec_route,
            "the exact decj command must route before the backward-compatible dec command"
        );
        assert!(
            c_source.contains(
                "sla.decj is unavailable outside radare2's borrowed-snapshot decompiler provider; use pdd."
            ) && c_source.contains("sleigh_decompile_execute (anal, NULL, true)")
                && c_source.contains("\"borrowed_snapshot_required\"")
                && c_source.contains("R2SLEIGH_STATUS_UNSUPPORTED_V2"),
            "direct decj must return a structured refusal instead of constructing source authority"
        );
        assert!(
            c_source.contains("pj_knull (pj, \"rendered_output\")")
                && c_source.contains("pj_ks (pj, \"outcome\", \"error\")"),
            "transport and cancellation failures must not expose partial rendered output"
        );
    }

    #[test]
    fn c_plugin_never_imports_dwarf_during_analysis_or_decompilation() {
        let c_source = include_str!("../r_anal_sleigh.c");
        for forbidden in [
            "sleigh_import_dwarf_base_types_if_needed",
            "r_bin_dwarf_parse_",
            "r_anal_dwarf_process_info",
        ] {
            assert!(
                !c_source.contains(forbidden),
                "immutable snapshots require DWARF ingestion before plugin analysis: {forbidden}"
            );
        }
    }

    #[test]
    fn c_plugin_keeps_decompile_session_policy_out_of_c_glue() {
        let c_source = include_str!("../r_anal_sleigh.c");
        let start = c_source
            .find("static RCodeMeta *sleigh_decompile(")
            .expect("decompiler provider callback");
        let end = c_source[start..]
            .find("static char *sleigh_cmd(")
            .map(|offset| start + offset)
            .expect("command callback after decompiler provider");
        let decompile_block = &c_source[start..end];

        assert!(
            c_source.contains("R2SLEIGH_CAP_PLANNER_QUERY_V2")
                && c_source.contains("api->planner_query"),
            "non-core analysis/debug C paths must consume the generated V2 planner table"
        );
        for forbidden in [
            "R2SleighSessionPolicyPlan",
            "sleigh_session_policy_plan_for_function",
            "r2sleigh_session_policy_plan_for_depth",
            "session_policy_plan.",
            concat!("R2SleighSession", "Input session_input"),
            concat!("sleigh_session_", "input_init (&session_input"),
            concat!("r2dec_", "function_with_session_context"),
            "SLEIGH_TYPE_WRITEBACK_OFF",
        ] {
            assert!(
                !decompile_block.contains(forbidden),
                "a:sla.dec must not own decompile session policy fragment {forbidden:?}"
            );
        }
        assert!(
            !decompile_block.contains("sleigh_analysis_policy_for_anal"),
            "a:sla.dec must not assemble decompile policy from plugin-local analysis policy"
        );
        for forbidden in [
            "policy.type_writeback_mode",
            "policy.type_global_max_links",
            "policy.type_max_decls",
            "policy.type_max_mutations",
        ] {
            assert!(
                !decompile_block.contains(forbidden),
                "a:sla.dec must not own decompile session policy fragment {forbidden:?}"
            );
        }
        for forbidden in [
            "should_skip_decompile_symbolic_scope",
            "function_exceeds_helper_scope_budget",
            "r2sleigh_interproc_helper_scope_budget_allows",
            "prefer_bounded_semantic_type_plan",
            "? 1: policy.type_interproc_max_iters",
            "? false: true",
            "1, 1, true",
        ] {
            assert!(
                !c_source.contains(forbidden),
                "C glue must not own interproc/session policy fragment {forbidden:?}"
            );
        }
        for forbidden in [
            concat!("build_type_", "interproc_scope"),
            "SymFunctionScope sym_scope",
            concat!("SleighInterproc", "Seeds interproc_seeds"),
            "have_sym_scope",
            "sym_scope.functions",
            "interproc_seeds.items",
        ] {
            assert!(
                !decompile_block.contains(forbidden),
                "a:sla.dec must not build or pass plugin-owned interprocedural scope {forbidden:?}"
            );
        }
        for forbidden in [
            "build_decompiler_function_names_json",
            "build_decompiler_strings_json",
            "build_decompiler_symbols_json",
            "func_names_json",
            "strings_json",
            "symbols_json",
        ] {
            assert!(
                !decompile_block.contains(forbidden),
                "a:sla.dec must not collect or pass raw decompiler metadata side channel {forbidden:?}"
            );
        }
        assert!(
            decompile_block.contains("sleigh_engine_execute_v2 (")
                && decompile_block.contains("R2SLEIGH_REQUEST_DECOMPILE_V2"),
            "a:sla.dec must call the versioned engine boundary with decompile-only typed input"
        );
        for forbidden in [
            "/* r2dec: function target",
            "r_cons_printf (cons,\n\t\t\t\t\t\t\"/* r2dec:",
            "not found or could not be materialized",
        ] {
            assert!(
                !decompile_block.contains(forbidden),
                "a:sla.dec must not synthesize plugin-owned decompile refusal text {forbidden:?}"
            );
        }
    }

    #[test]
    fn c_plugin_decompile_uses_only_the_borrowed_snapshot_provider() {
        let c_source = include_str!("../r_anal_sleigh.c");
        let direct_start = c_source
            .find("static char *sleigh_decompile_execute(RAnal *anal")
            .expect("direct-command refusal helper");
        let direct_end = c_source[direct_start..]
            .find("static RCodeMeta *sleigh_decompile(")
            .map(|offset| direct_start + offset)
            .expect("borrowed-snapshot provider after direct refusal");
        let direct = &c_source[direct_start..direct_end];
        assert!(
            direct.contains("direct decompile commands cannot construct source authority")
                && direct.contains("borrowed_snapshot_required")
        );
        for forbidden in [
            "get_context (",
            "sleigh_engine_function_preflight",
            "lift_function_blocks",
            "snapshot_collect",
            "sleigh_engine_execute_v2 (",
        ] {
            assert!(
                !direct.contains(forbidden),
                "direct decompile refusal must not construct authority via {forbidden:?}"
            );
        }

        let provider_start = direct_end;
        let provider_end = c_source[provider_start..]
            .find("static char *sleigh_cmd(")
            .map(|offset| provider_start + offset)
            .expect("command callback after decompiler provider");
        let provider = &c_source[provider_start..provider_end];
        assert!(
            provider.contains("r2sleigh_wire_writer_new ()")
                && provider.contains("free (buffer)")
                && provider.contains("r2sleigh_wire_write_snapshot (writer, snapshot)")
                && provider.contains(".snapshot_buffer = buffer")
                && provider.contains("R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2")
                && provider.contains("sleigh_engine_execute_v2 (")
        );
        for forbidden in ["get_context (", "lift_function_blocks", "snapshot_collect"] {
            assert!(
                !provider.contains(forbidden),
                "borrowed-snapshot provider must not rebuild source state via {forbidden:?}"
            );
        }
    }

    #[test]
    fn c_plugin_sla_ssa_func_does_not_own_decompile_cfg_guard() {
        let c_source = include_str!("../r_anal_sleigh.c");
        let section = c_source
            .find("/* ========== Function-level SSA commands ========== */")
            .expect("function-level SSA command section");
        let start = c_source[section..]
            .find("if (!strcmp (cmd, \"sla.ssa.func\"))")
            .map(|offset| section + offset)
            .expect("a:sla.debug.ssa.func command block");
        let end = c_source[start..]
            .find("if (!strcmp (cmd, \"sla.ssa.func.opt\"))")
            .map(|offset| start + offset)
            .expect("next command after a:sla.debug.ssa.func");
        let ssa_func_block = &c_source[start..end];

        assert!(
            !c_source.contains("extern char *r2dec_cfg_guard_comment_ffi"),
            "C glue must not declare the plugin-owned CFG guard comment FFI"
        );
        assert!(
            !ssa_func_block.contains("r2dec_cfg_guard_comment_ffi"),
            "a:sla.debug.ssa.func must not call the plugin-owned CFG guard comment FFI"
        );
        assert!(
            !ssa_func_block.contains("/* r2dec:"),
            "a:sla.debug.ssa.func must not print r2dec CFG guard comments"
        );
        for forbidden in [
            "compute_decompile_cfg_risk_summary",
            "DecompileCFGRiskSummary",
            "is_autogenerated_function_name",
        ] {
            assert!(
                !c_source.contains(forbidden),
                "C glue must not retain local decompile CFG guard policy {forbidden:?}"
            );
        }
    }

    #[test]
    fn c_plugin_post_analysis_does_not_own_type_writeback_fixpoint() {
        let c_source = include_str!("../r_anal_sleigh.c");
        let rust_source = include_str!("lib.rs");

        for forbidden in [
            concat!("r2sleigh_type_writeback_", "fixpoint_"),
            concat!("collect_", "fixpoint_neighbor_candidates"),
            concat!("append_", "fixpoint_edge_candidate"),
            concat!("fixpoint_", "ref_kind_id"),
            concat!("type ", "fixpoint"),
            concat!("R2SleighTypeWriteback", "Fixpoint"),
            concat!("r2sleigh_type_writeback_", "cache_"),
            concat!("apply_type_writeback_", "session_result"),
            concat!("compute_callee_", "dependency_hash"),
            concat!("propagate_signature_", "to_direct_callers"),
            concat!("apply_inferred_", "signature_fact"),
            concat!("apply_inferred_", "callconv"),
            concat!("r2sleigh_session_result_", "mutations"),
            concat!("r2sleigh_session_result_type_", "writeback_json"),
            concat!("r2sleigh_bounded_", "type_json_ffi"),
        ] {
            assert!(
                !c_source.contains(forbidden),
                "C post-analysis must not own type-writeback policy {forbidden:?}"
            );
            assert!(
                !rust_source.contains(forbidden),
                "plugin Rust must not expose type-writeback policy ABI {forbidden:?}"
            );
        }
    }

    #[test]
    fn plugin_session_debug_abi_is_deleted() {
        let rust_source = include_str!("lib.rs");
        for forbidden in [
            concat!("pub extern \"C\" fn r2sleigh_session_", "analyze"),
            concat!(
                "pub extern \"C\" fn r2sleigh_session_result_",
                "report_json"
            ),
            concat!("pub extern \"C\" fn r2sleigh_session_result_", "free"),
            concat!(
                "pub extern \"C\" fn r2sleigh_session_interproc_",
                "summary_json"
            ),
            concat!("pub struct R2SleighSession", "Input"),
            concat!("fn session_", "analysis_input"),
            concat!("fn build_function_analysis_", "shared_bundle"),
        ] {
            assert!(
                !rust_source.contains(forbidden),
                "broad plugin session/debug ABI must stay deleted: {forbidden:?}"
            );
        }
    }

    #[test]
    fn plugin_decompile_boundary_has_no_legacy_direct_decompile_exports() {
        let rust_source = include_str!("lib.rs");
        let ffi_source = include_str!("ffi_v2.rs");
        let c_source = include_str!("../r_anal_sleigh.c");
        let forbidden_rust = [
            concat!("pub extern \"C\" fn r2dec_", "function_with_context"),
            concat!("pub extern \"C\" fn r2dec_", "function_with_context_scope"),
            concat!("fn r2dec_", "function_with_context_impl"),
            concat!("struct R2Dec", "FunctionWithContextInputs"),
            concat!("pub extern \"C\" fn r2dec_", "block("),
            concat!("pub extern \"C\" fn r2dec_", "block_ast_json"),
            concat!("pub extern \"C\" fn r2dec_", "named_native_worker_summary"),
            concat!(
                "pub extern \"C\" fn r2dec_",
                "semantic_worker_linearization_scope_ffi"
            ),
            concat!("pub extern \"C\" fn r2dec_", "block_guard_comment_ffi"),
            concat!("pub struct R2SleighEngine", "DecompileInput"),
            concat!("pub struct R2SleighEngine", "TypeFunctionInput"),
            concat!("pub extern \"C\" fn r2sleigh_engine_", "decompile_function"),
            concat!("pub extern \"C\" fn r2sleigh_engine_", "type_function_json"),
            concat!("execute_", "migration_shim"),
            concat!("legacy_", "input"),
            concat!("r2sleigh_ffi_sizeof_", "function_context"),
            concat!("r2sleigh_ffi_alignof_", "function_context"),
        ];
        for forbidden in forbidden_rust {
            assert!(
                !rust_source.contains(forbidden),
                "r2plugin Rust must not expose legacy direct decompile ABI {forbidden:?}"
            );
            assert!(
                !ffi_source.contains(forbidden),
                "V2 Rust must not retain legacy request transport {forbidden:?}"
            );
        }

        let forbidden_c = [
            concat!("r2dec_", "function_with_context("),
            concat!("r2dec_", "function_with_context_scope("),
            concat!("r2dec_", "block("),
            concat!("r2dec_", "block_ast_json("),
            concat!("r2dec_", "named_native_worker_summary("),
            concat!("r2dec_", "semantic_worker_linearization_scope_ffi("),
            concat!("r2dec_", "block_guard_comment_ffi("),
            concat!("R2SleighEngine", "DecompileInput"),
            concat!("R2SleighEngine", "TypeFunctionInput"),
        ];
        for forbidden in forbidden_c {
            assert!(
                !c_source.contains(forbidden),
                "C plugin glue must not declare or call legacy direct decompile ABI {forbidden:?}"
            );
        }
        let provider_start = c_source
            .find("static RCodeMeta *sleigh_decompile(const RAnalFunctionSnapshot *snapshot)")
            .expect("borrowed-snapshot decompiler provider");
        let provider_end = c_source[provider_start..]
            .find("static char *sleigh_cmd(")
            .map(|offset| provider_start + offset)
            .expect("command callback after provider");
        let provider = &c_source[provider_start..provider_end];
        assert!(
            provider.contains("r2sleigh_wire_writer_new ()")
                && provider.contains("free (buffer)")
                && provider.contains("r2sleigh_wire_write_snapshot (writer, snapshot)")
                && provider.contains("const R2SleighEngineRequestPayloadV2 payload")
                && provider.contains(".snapshot_buffer = buffer")
                && provider.contains("R2SLEIGH_REQUEST_DECOMPILE_V2")
                && provider.contains("R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2")
                && provider.contains("sleigh_engine_execute_v2 ("),
            "C plugin glue must route borrowed snapshots exclusively through the native V2 boundary"
        );
        assert!(!c_source.contains(concat!(
            "r2sleigh_engine_",
            "decompile_function (&decompile_input)"
        )));
    }

    fn register_param(
        name: &str,
        ty: Option<r2types::CTypeLike>,
        reg: &str,
    ) -> r2types::ExternalRegisterParamSpec {
        r2types::ExternalRegisterParamSpec {
            name: name.to_string(),
            ty,
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

        for synthetic in ["tmp:10", "const:4", "ram:1000", "space1:20", "TMP:5"] {
            assert!(
                !is_real_reg(synthetic),
                "{synthetic} should be excluded as non-register data"
            );
        }
    }

    #[test]
    fn switch_info_ffi_attaches_normalized_switch_facts() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let cases = [
            R2ILSwitchCaseFfi {
                value: 7,
                target: 0x3000,
            },
            R2ILSwitchCaseFfi {
                value: 0,
                target: 0x2000,
            },
            R2ILSwitchCaseFfi {
                value: 7,
                target: 0x3000,
            },
        ];

        let ok = r2il_block_set_switch_info(R2ILSwitchInfoInput {
            block: &mut block,
            switch_addr: 0x1010,
            min_val: 0,
            max_val: 7,
            default_target: 0x4000,
            has_default: 1,
            cases: cases.as_ptr(),
            case_count: cases.len(),
        });
        assert_eq!(ok, 1);

        let info = block.switch_info.as_ref().expect("switch info");
        assert_eq!(info.switch_addr, 0x1010);
        assert_eq!(info.min_val, 0);
        assert_eq!(info.max_val, 7);
        assert_eq!(info.default_target, Some(0x4000));
        assert_eq!(
            info.cases
                .iter()
                .map(|case| (case.value, case.target))
                .collect::<Vec<_>>(),
            vec![(0, 0x2000), (7, 0x3000)]
        );
    }

    #[test]
    fn switch_info_ffi_rejects_ambiguous_duplicate_case_values() {
        let mut block = R2ILBlock::new(0x1000, 4);
        let cases = [
            R2ILSwitchCaseFfi {
                value: 1,
                target: 0x2000,
            },
            R2ILSwitchCaseFfi {
                value: 1,
                target: 0x3000,
            },
        ];

        let ok = r2il_block_set_switch_info(R2ILSwitchInfoInput {
            block: &mut block,
            switch_addr: 0x1010,
            min_val: 0,
            max_val: 1,
            default_target: u64::MAX,
            has_default: 0,
            cases: cases.as_ptr(),
            case_count: cases.len(),
        });
        assert_eq!(ok, 0);
        assert!(block.switch_info.is_none());
    }

    #[cfg(feature = "x86")]
    unsafe fn c_string_to_owned(ptr: *mut c_char) -> String {
        let out = unsafe { CStr::from_ptr(ptr) }
            .to_string_lossy()
            .into_owned();
        drop_test_ffi_string(ptr);
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

    #[cfg(feature = "x86")]
    fn block_has_inline_varnode_metadata(block: &R2ILBlock) -> bool {
        block.ops.iter().any(|op| {
            op.output().is_some_and(|vn| vn.meta.is_some())
                || op.inputs().into_iter().any(|vn| vn.meta.is_some())
        })
    }

    #[cfg(feature = "x86")]
    fn block_has_advisory_semantic_metadata(block: &R2ILBlock) -> bool {
        block.op_metadata.values().any(|metadata| {
            metadata.memory_class.is_some()
                || metadata.endianness.is_some()
                || metadata.memory_ordering.is_some()
                || metadata.permissions.is_some()
                || metadata.valid_range.is_some()
                || metadata.bank_id.is_some()
                || metadata.segment_id.is_some()
                || metadata.atomic_kind.is_some()
        })
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
        drop_test_block(block);
        drop_test_context(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lift_respects_semantic_metadata_disable_toggle() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        // mov eax, dword ptr [rbp - 4]
        let mut bytes = vec![0x8b, 0x45, 0xfc];
        bytes.resize(16, 0);

        let enabled_block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!enabled_block.is_null());
        let enabled = unsafe { &*enabled_block };
        assert!(
            !block_has_inline_varnode_metadata(enabled),
            "semantic enrichment must not mutate canonical varnodes"
        );
        assert!(
            block_has_advisory_semantic_metadata(enabled),
            "default lift should retain advisory memory facts out of band"
        );
        let enabled_ops = enabled.ops.clone();
        drop_test_block(enabled_block);

        r2il_set_semantic_metadata_enabled(ctx, false);
        let disabled_block = r2il_lift(ctx, bytes.as_ptr(), bytes.len(), 0x1000);
        assert!(!disabled_block.is_null());
        let disabled = unsafe { &*disabled_block };
        assert!(
            !block_has_inline_varnode_metadata(disabled)
                && !block_has_advisory_semantic_metadata(disabled),
            "disabled semantic metadata must suppress only out-of-band enrichment"
        );
        assert_eq!(enabled_ops, disabled.ops);

        drop_test_block(disabled_block);
        drop_test_context(ctx);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lift_block_respects_semantic_metadata_disable_toggle() {
        let arch = CString::new("x86-64").unwrap();
        let ctx = r2il_arch_init(arch.as_ptr());
        assert!(!ctx.is_null());

        // mov eax, dword ptr [rbp - 4]
        let mut bytes = vec![0x8b, 0x45, 0xfc];
        bytes.resize(16, 0);

        let enabled_block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), 0x1000, 3);
        assert!(!enabled_block.is_null());
        let enabled = unsafe { &*enabled_block };
        assert!(
            !block_has_inline_varnode_metadata(enabled),
            "block enrichment must not mutate canonical varnodes"
        );
        assert!(
            block_has_advisory_semantic_metadata(enabled),
            "default block lift should retain advisory memory facts out of band"
        );
        let enabled_ops = enabled.ops.clone();
        drop_test_block(enabled_block);

        r2il_set_semantic_metadata_enabled(ctx, false);
        let disabled_block = r2il_lift_block(ctx, bytes.as_ptr(), bytes.len(), 0x1000, 3);
        assert!(!disabled_block.is_null());
        let disabled = unsafe { &*disabled_block };
        assert!(
            !block_has_inline_varnode_metadata(disabled)
                && !block_has_advisory_semantic_metadata(disabled),
            "disabled semantic metadata must suppress only out-of-band block enrichment"
        );
        assert!(
            disabled
                .op_metadata
                .values()
                .all(|metadata| metadata.instruction_addr.is_some())
        );
        assert_eq!(enabled_ops, disabled.ops);

        drop_test_block(disabled_block);
        drop_test_context(ctx);
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

        drop_test_block(block);
        drop_test_context(ctx);
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

        drop_test_block(block);
        drop_test_context(ctx);
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

        drop_test_block(block);
        drop_test_context(ctx);
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

        drop_test_block(block);
        drop_test_context(ctx);
    }

    #[test]
    fn test_null_handling() {
        assert_eq!(r2il_is_loaded(ptr::null()), 0);
        assert!(r2il_arch_name(ptr::null()).is_null());
        drop_test_context(ptr::null_mut());
        drop_test_block(ptr::null_mut());
    }

    #[test]
    fn test_parse_external_signature_with_args() {
        let json = r#"[{"name":"dbg.vuln_memcpy","args":[{"name":"user_input","type":"char *"},{"name":"user_len","type":"int32_t"}],"count":2}]"#;
        let sig = parse_external_signature(json, 64).expect("signature should parse");
        assert!(sig.ret_type.is_none());
        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.params[0].name, "user_input");
        assert_eq!(sig.params[1].name, "user_len");
        assert_eq!(sig.params[0].ty, Some(ptr_type(signed_type(8))));
        assert_eq!(sig.params[1].ty, Some(signed_type(32)));
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
        assert_eq!(sig.ret_type, Some(signed_type(32)));
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
    fn test_session_policy_plan_ffi_routes_to_engine() {
        assert_eq!(
            type_writeback_apply_policy_from_ffi(&R2SleighTypeWritebackApplyPolicy {
                schema_version: 0,
                mode: R2SLEIGH_TYPE_WRITEBACK_OFF,
            })
            .mode,
            r2types::TypeWritebackApplyMode::Off,
            "plugin FFI must route off mode through engine-owned policy mapping"
        );
        assert_eq!(
            type_writeback_apply_policy_from_ffi(&R2SleighTypeWritebackApplyPolicy {
                schema_version: 0,
                mode: R2SLEIGH_TYPE_WRITEBACK_BALANCED,
            })
            .mode,
            r2types::TypeWritebackApplyMode::Balanced,
            "plugin FFI must route balanced mode through engine-owned policy mapping"
        );
        assert_eq!(
            type_writeback_apply_policy_from_ffi(&R2SleighTypeWritebackApplyPolicy {
                schema_version: 0,
                mode: R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE,
            })
            .mode,
            r2types::TypeWritebackApplyMode::Aggressive,
            "plugin FFI must route aggressive mode through engine-owned policy mapping"
        );
    }

    #[test]
    fn test_parse_external_type_accepts_type_prefixed_primitives() {
        assert_eq!(parse_external_type("type.int", 64), Some(signed_type(32)));
        assert_eq!(
            parse_external_type("type.uint16_t *", 64),
            Some(ptr_type(unsigned_type(16)))
        );
        assert_eq!(
            parse_external_type("struct.sla_node *", 64),
            Some(ptr_type(r2types::CTypeLike::Struct("sla_node".to_string())))
        );
        assert_eq!(
            parse_external_type("type.IOCPU_VTable.setCPUNumber", 64),
            Some(ptr_type(r2types::CTypeLike::Void))
        );
    }

    #[test]
    fn test_parse_external_type_accepts_canonical_signed_spellings() {
        assert_eq!(parse_external_type("signed int", 64), Some(signed_type(32)));
        assert_eq!(
            parse_external_type("signed short int", 64),
            Some(signed_type(16))
        );
        assert_eq!(
            parse_external_type("signed long", 64),
            Some(signed_type(64))
        );
        assert_eq!(
            parse_external_type("signed long *", 64),
            Some(ptr_type(signed_type(64)))
        );
    }

    #[test]
    fn test_parse_external_type_accepts_canonical_ssize_t_aliases() {
        assert_eq!(parse_external_type("intptr_t", 64), Some(signed_type(64)));
        assert_eq!(
            parse_external_type("type.intptr_t", 64),
            Some(signed_type(64))
        );
        assert_eq!(
            parse_external_type("ssize_t *", 64),
            Some(ptr_type(signed_type(64)))
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
        assert_eq!(params[0].ty, Some(signed_type(32)));
        assert_eq!(params[0].reg, "RDI");
        assert_eq!(params[1].name, "arg1");
        assert_eq!(params[1].ty, Some(signed_type(32)));
        assert_eq!(params[1].reg, "RSI");
    }

    #[test]
    fn test_merge_signature_with_reg_params_fills_missing_host_args() {
        let merged = merge_signature_with_reg_params(
            Some(r2types::FunctionSignatureSpec {
                ret_type: Some(signed_type(32)),
                params: Vec::new(),
            }),
            vec![
                register_param("arg0", Some(signed_type(32)), "RDI"),
                register_param("arg1", Some(signed_type(32)), "RSI"),
            ],
        )
        .expect("merged signature");
        assert_eq!(merged.ret_type, Some(signed_type(32)));
        assert_eq!(merged.params.len(), 2);
        assert_eq!(merged.params[0].ty, Some(signed_type(32)));
        assert_eq!(merged.params[1].ty, Some(signed_type(32)));
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
    fn effective_ptr_bits_falls_back_to_default_space_when_arch_addr_size_is_degenerate() {
        let arch_name = CString::new("x86-64").expect("valid arch string");
        let ctx = r2il_arch_init(arch_name.as_ptr());
        assert!(!ctx.is_null(), "context should initialize");
        let mut arch = unsafe { (*ctx).arch.clone().expect("arch spec") };
        drop_test_context(ctx);
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
        let ty = sanitize_inferred_param_type(r2types::CTypeLike::Void, 0, 64);
        assert_eq!(ty, signed_type(64));
    }

    #[test]
    fn materialize_signature_type_rewrites_unknown_pointer_to_void_ptr() {
        let ty = materialize_signature_type_like(ptr_type(r2types::CTypeLike::Unknown), 64);
        assert_eq!(ty, ptr_type(r2types::CTypeLike::Void));
        assert_eq!(r2types::render_c_type_like(&ty), "void*");
    }

    #[test]
    fn materialize_signature_type_rewrites_unknown_return_to_scalar_fallback() {
        let ty = materialize_signature_type_like(r2types::CTypeLike::Unknown, 64);
        assert_eq!(ty, signed_type(64));
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
        assert_eq!(ty, signed_type(32));
    }

    #[test]
    fn resolve_evidence_driven_type_can_narrow_wide_scalar_carrier() {
        let ty = resolve_evidence_driven_type(
            signed_type(64),
            8,
            64,
            &TypeEvidence {
                scalar_proven: 1,
                width_bits: 32,
                ..TypeEvidence::default()
            },
        );
        assert_eq!(ty, signed_type(32));
    }

    #[test]
    fn merge_initial_type_evidence_preserves_narrow_scalar_hint_over_wide_carrier_type() {
        let mut evidence = TypeEvidence {
            scalar_proven: 1,
            width_bits: 32,
            ..TypeEvidence::default()
        };
        merge_initial_type_evidence(&signed_type(64), &mut evidence);
        assert_eq!(evidence.width_bits, 32);
    }

    #[test]
    fn collect_type_evidence_uses_arm64_register_family_alias_when_only_w_view_is_present() {
        let blocks = vec![r2ssa::SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
            &signed_type(64),
        );
        let ty = resolve_evidence_driven_type(signed_type(64), 8, 64, &evidence);

        assert_eq!(evidence.width_bits, 32);
        assert_eq!(ty, signed_type(32));
    }

    #[test]
    fn materialize_signature_type_rewrites_struct_anon_pointer_to_void_ptr() {
        let ty = materialize_signature_type_like(
            ptr_type(r2types::CTypeLike::Struct("anon".to_string())),
            64,
        );
        assert_eq!(ty, ptr_type(r2types::CTypeLike::Void));
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

    fn test_large_cfg_semantic_report() -> r2sym::SemanticArtifactReport {
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
        r2sym::SemanticArtifactReport {
            schema_version: r2sym::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
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
            },
        }
    }

    #[test]
    fn summary_only_report_keeps_bounded_type_advisory() {
        let mut artifact = test_large_cfg_semantic_report();
        artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let cfg_risk = r2ssa::CFGRiskSummary {
            block_count: 200,
            loop_count: 8,
            back_edge_count: 12,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        assert!(r2types::semantic_artifact_prefers_bounded_type_plan(
            &artifact
        ));
        assert_eq!(
            artifact.granularity,
            r2sym::ArtifactGranularity::SummaryOnly
        );
        assert_eq!(cfg_risk.block_count, 200);
    }

    #[test]
    fn semantic_type_fallback_payload_rejects_name_owned_role_signature() {
        let mut summary = r2sym::function_semantic_summary_seed_for_name(
            r2ssa::InterprocFunctionId(0x11a9),
            "verror_at_line",
        )
        .unwrap_or_else(|| {
            r2ssa::FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(0x11a9),
                Some("verror_at_line".to_string()),
            )
        });
        summary.callsite_count = 1;
        assert!(
            r2sym::compile_named_native_worker_summary_report(&summary, true).is_none(),
            "name-owned diagnostic roles must not materialize advisory fallback reports"
        );
    }

    #[test]
    fn semantic_type_fallback_payload_does_not_apply_name_hint_over_context_override() {
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x11aa),
            Some("quotearg_n_options".to_string()),
        );
        summary.callsite_count = 1;
        assert!(
            r2sym::compile_named_native_worker_summary_report(&summary, true).is_none(),
            "name-owned quoting roles must not materialize reports that could override context"
        );
    }

    #[test]
    fn semantic_report_exposes_canonical_region_counts() {
        let compiled = test_large_cfg_semantic_report();
        let native = compiled.native_body().expect("native report");
        assert_eq!(native.regions.len(), 1);
        assert_eq!(native.actionable_control_count(), 3);
        assert_eq!(native.exact_control_count(), 3);
    }

    #[test]
    fn non_x86_strong_evidence_can_clear_signature_threshold() {
        let params = vec![
            signature_param_candidate(
                "arg0",
                ptr_type(r2types::CTypeLike::Void),
                0,
                8,
                TypeEvidence {
                    pointer_proven: 1,
                    ..TypeEvidence::default()
                },
            ),
            signature_param_candidate(
                "arg1",
                signed_type(32),
                1,
                4,
                TypeEvidence {
                    scalar_proven: 1,
                    width_bits: 32,
                    ..TypeEvidence::default()
                },
            ),
            signature_param_candidate(
                "arg2",
                r2types::CTypeLike::Bool,
                2,
                1,
                TypeEvidence {
                    bool_like: 1,
                    width_bits: 8,
                    ..TypeEvidence::default()
                },
            ),
        ];
        let confidence = r2types::compute_signature_confidence(
            &params,
            &signed_type(32),
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
        let params = vec![signature_param_candidate(
            "arg0",
            r2types::CTypeLike::Unknown,
            0,
            8,
            TypeEvidence {
                pointer_likely: 1,
                scalar_likely: 1,
                ..TypeEvidence::default()
            },
        )];
        let confidence = r2types::compute_signature_confidence(
            &params,
            &r2types::CTypeLike::Unknown,
            &TypeEvidence::default(),
        );
        assert!(confidence < SIG_WRITEBACK_CONFIDENCE_MIN);
    }

    #[test]
    fn explicit_external_signature_context_yields_high_confidence() {
        let ctx = signature_spec(
            Some(signed_type(32)),
            vec![("items", Some(ptr_type(signed_type(8))))],
        );
        let confidence = explicit_signature_context_strength(&ctx);
        assert!(confidence >= SIG_WRITEBACK_CONFIDENCE_MIN);
    }

    #[test]
    fn non_x86_callconv_confidence_stays_low_when_signature_is_high() {
        let params = vec![
            signature_param_candidate(
                "arg0",
                ptr_type(r2types::CTypeLike::Void),
                0,
                8,
                TypeEvidence {
                    pointer_proven: 1,
                    ..TypeEvidence::default()
                },
            ),
            signature_param_candidate(
                "arg1",
                signed_type(64),
                1,
                8,
                TypeEvidence {
                    scalar_proven: 1,
                    width_bits: 64,
                    ..TypeEvidence::default()
                },
            ),
        ];
        let sig_conf = r2types::compute_signature_confidence(
            &params,
            &signed_type(64),
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

    fn x86_register_storage(arch: &ArchSpec, name: &str) -> r2ssa::CanonicalStorageId {
        let register = arch.get_register(name).expect("x86-64 source register");
        r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset: register.offset,
            size: register.size,
        }
    }

    fn x86_exact_test_snapshot(
        arch: &ArchSpec,
        revision: &str,
        parameter_registers: &[&str],
        parameter_homes: &[(u32, i64, u32)],
        local_slots: &[(i64, u32)],
        first_parameter_has_exact_struct_pointer: bool,
        call_sites: Vec<r2ssa::SourceCallSiteInterface>,
    ) -> std::sync::Arc<r2engine::EngineSourceSnapshot> {
        let revision = revision.as_bytes().to_vec();
        let parameter_storages = parameter_registers
            .iter()
            .map(|name| x86_register_storage(arch, name))
            .collect::<Vec<_>>();
        let parameters = parameter_storages
            .iter()
            .enumerate()
            .map(|(index, storage)| r2ssa::SourceAbiParameterSpec::new(index as u32, *storage))
            .collect::<Vec<_>>();
        let rbp = x86_register_storage(arch, "RBP");
        let mut stack_slots = parameter_homes
            .iter()
            .map(|(parameter, offset, size)| {
                r2ssa::SourceStackSlotSpec::new_parameter_home(
                    r2ssa::StackAddressBase::FramePointer,
                    rbp,
                    *offset,
                    *size,
                    *parameter,
                    parameter_storages[*parameter as usize],
                )
            })
            .collect::<Vec<_>>();
        stack_slots.extend(local_slots.iter().map(|(offset, size)| {
            r2ssa::SourceStackSlotSpec::new_local(
                r2ssa::StackAddressBase::FramePointer,
                rbp,
                *offset,
                *size,
            )
        }));
        let return_kind = r2ssa::SourceFunctionReturn::Register {
            storage: x86_register_storage(arch, "RAX"),
        };
        let interface = if first_parameter_has_exact_struct_pointer {
            let scalar_carrier =
                r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32);
            let parameter_logical_values = parameters
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    if index == 0 {
                        r2ssa::SourceLogicalValue::new(
                            2,
                            r2ssa::SourceCarrierProjection::new(
                                r2ssa::SourceCarrierKind::Full,
                                0,
                                64,
                            ),
                        )
                    } else {
                        r2ssa::SourceLogicalValue::new(1, scalar_carrier)
                    }
                })
                .collect::<Vec<_>>();
            let type_graph = r2ssa::SourceTypeGraph::new(
                [
                    r2ssa::SourceType::new(
                        0,
                        r2ssa::SourceTypeKind::Struct { aggregate_id: 0 },
                        56 * 8,
                        32,
                    ),
                    r2ssa::SourceType::new(1, r2ssa::SourceTypeKind::SignedInteger, 32, 32),
                    r2ssa::SourceType::new(
                        2,
                        r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                        64,
                        64,
                    ),
                ],
                [r2ssa::SourceAggregateLayout::new(
                    0,
                    0,
                    56 * 8,
                    32,
                    "FixtureStruct",
                    (0..14).map(|index| {
                        r2ssa::SourceAggregateMember::new(
                            index,
                            1,
                            u64::from(index) * 32,
                            32,
                            format!("field_{index}"),
                        )
                    }),
                )],
            )
            .expect("x86-64 pointer parameter type graph");
            r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
                revision.clone(),
                "sysv64",
                parameters,
                return_kind,
                stack_slots,
                parameter_logical_values,
                Some(r2ssa::SourceLogicalValue::new(1, scalar_carrier)),
                Some(type_graph),
            )
        } else {
            r2ssa::SourceFunctionInterface::new_exact(
                revision.clone(),
                "sysv64",
                parameters,
                return_kind,
                stack_slots,
            )
        }
        .and_then(|interface| {
            interface.with_return_address_storage(x86_register_storage(arch, "RIP"))
        })
        .and_then(|interface| {
            interface.with_stack_pointer_storage(x86_register_storage(arch, "RSP"))
        })
        .and_then(|interface| interface.with_frame_pointer_storage(rbp))
        .expect("exact x86-64 test source interface");
        std::sync::Arc::new(
            r2engine::EngineSourceSnapshot::new(revision, Some(interface), call_sites)
                .expect("immutable x86-64 test source snapshot"),
        )
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
        let arch = ctx.arch.as_ref().expect("x86-64 ArchSpec");
        assert_eq!(arch.addr_size, 8);
        for (role, target) in [("PC", "RIP"), ("SP", "RSP"), ("BP", "RBP")] {
            assert_eq!(role_target(profile, role).as_deref(), Some(target));
            let expected = arch
                .get_register(target)
                .expect("full-width x86 address register");
            assert_eq!(expected.size, arch.addr_size);
            assert_eq!(
                profile_register(profile, target),
                Some((expected.size * 8, expected.offset)),
                "={role} must target the exact full-width ArchSpec coordinates"
            );
        }

        drop_test_ffi_string(profile_ptr);
        drop_test_context(ctx_ptr);
    }

    #[test]
    #[cfg(feature = "arm")]
    fn create_disassembler_for_arch_arm64() {
        let (spec, _disasm) = create_disassembler_for_arch("arm64").expect("arm64 disassembler");
        assert_eq!(spec.name, "aarch64");
        assert_eq!(spec.addr_size, 8);
    }

    #[test]
    #[cfg(feature = "arm")]
    fn arm64_callother_stays_numeric_and_construction_stable() {
        const DMB_ISH: &[u8] = &[0xbf, 0x3b, 0x03, 0xd5];
        const ADDR: u64 = 0x410000;

        let mut decode_window = DMB_ISH.to_vec();
        decode_window.resize(16, 0);
        let (_, first) = create_disassembler_for_arch("arm64").expect("first arm64 disassembler");
        let (_, second) = create_disassembler_for_arch("arm64").expect("second arm64 disassembler");
        let first_block = first.lift(&decode_window, ADDR).expect("first DMB lift");
        let second_block = second.lift(&decode_window, ADDR).expect("second DMB lift");

        assert_eq!(first_block.ops, second_block.ops);
        let numeric_userops = first_block
            .ops
            .iter()
            .filter_map(|op| match op {
                R2ILOp::CallOther { userop, .. } => Some(*userop),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(!numeric_userops.is_empty());
        assert_eq!(
            numeric_userops,
            second_block
                .ops
                .iter()
                .filter_map(|op| match op {
                    R2ILOp::CallOther { userop, .. } => Some(*userop),
                    _ => None,
                })
                .collect::<Vec<_>>()
        );
        assert!(
            first
                .lift_genuine_block(&decode_window, ADDR, DMB_ISH.len())
                .is_err(),
            "plugin-created analysis disassemblers must not mint genuine authority"
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn create_disassembler_for_arch_riscv64() {
        let (spec, _disasm) =
            create_disassembler_for_arch("riscv64").expect("riscv64 disassembler");
        assert_eq!(spec.name, "riscv64");
        assert!(spec.addr_size > 0);
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Little);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Little);
    }

    #[test]
    #[cfg(feature = "arm")]
    fn r2il_arch_init_arm64_loaded() {
        let arch_cstr = CString::new("arm64").unwrap();
        let ctx_ptr = r2il_arch_init(arch_cstr.as_ptr());
        assert!(!ctx_ptr.is_null(), "context pointer should not be null");
        assert_eq!(r2il_is_loaded(ctx_ptr), 1, "arm64 context should be loaded");
        drop_test_context(ctx_ptr);
    }

    #[cfg(any(feature = "x86", feature = "arm", feature = "mips"))]
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
        drop_test_ffi_string(profile_ptr);
        drop_test_context(ctx_ptr);
        profile
    }

    fn role_target(profile: &str, role: &str) -> Option<String> {
        profile
            .lines()
            .find_map(|line| line.strip_prefix(&format!("={}\t", role)))
            .map(str::trim)
            .map(str::to_string)
    }

    fn profile_register(profile: &str, name: &str) -> Option<(u32, u64)> {
        profile.lines().find_map(|line| {
            let mut fields = line.split('\t');
            if fields.next()? != "gpr" || fields.next()? != name {
                return None;
            }
            let bits = fields.next()?.strip_prefix('.')?.parse::<u32>().ok()?;
            let offset = fields.next()?.parse::<u64>().ok()?;
            if fields.next()? != "0" || fields.next().is_some() {
                return None;
            }
            Some((bits, offset))
        })
    }

    #[test]
    #[cfg(feature = "x86")]
    fn x86_32_reg_profile_roles_use_address_width_coordinates() {
        let (arch, _) = create_disassembler_for_arch("x86").expect("x86 disassembler");
        assert_eq!(arch.addr_size, 4);
        let profile = profile_for_arch("x86");
        for (role, target) in [("PC", "EIP"), ("SP", "ESP"), ("BP", "EBP")] {
            assert_eq!(role_target(&profile, role).as_deref(), Some(target));
            let expected = arch
                .get_register(target)
                .expect("full-width x86 address register");
            assert_eq!(expected.size, arch.addr_size);
            assert_eq!(
                profile_register(&profile, target),
                Some((expected.size * 8, expected.offset)),
                "={role} must target the exact address-width ArchSpec coordinates"
            );
        }
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
        let (spec, _disasm) =
            create_disassembler_for_arch("riscv32").expect("riscv32 disassembler");
        assert_eq!(spec.name, "riscv32");
        assert!(spec.addr_size > 0);
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Little);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Little);
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
        drop_test_context(ctx_ptr);
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
        drop_test_context(ctx_ptr);
    }

    #[test]
    #[cfg(feature = "mips")]
    fn create_disassembler_for_arch_mips32be() {
        let (spec, _disasm) =
            create_disassembler_for_arch("mips32be").expect("mips32be disassembler");
        assert_eq!(spec.name, "mips32be");
        assert_eq!(spec.addr_size, 4);
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Big);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Big);
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
        drop_test_context(ctx_ptr);
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:base", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:base_4", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:v2", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:base_a", 1, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:base_a_4", 1, 8),
                    a: r2ssa::SSAVar::new("tmp:base_a", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:base_a_4", 1, 8),
                    val: r2ssa::SSAVar::new("tmp:a1", 1, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:base_b", 1, 8),
                    src: r2ssa::SSAVar::new("const:405000", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:b0", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("X9", 2, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 3, 8),
                    a: r2ssa::SSAVar::new("X9", 1, 8),
                    b: r2ssa::SSAVar::new("const:30", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("X9", 2, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 3, 4),
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                },
            ],
        };

        let (signature, type_db) = enrich_decompiler_type_context(
            &[block],
            Some(&arch),
            64,
            Some(signature_spec(
                Some(signed_type(64)),
                vec![
                    ("arg1", Some(ptr_type(r2types::CTypeLike::Void))),
                    ("arg2", Some(signed_type(32))),
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6400", 7, 8),
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 1, 8),
                    val: r2ssa::SSAVar::new("X0", 0, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6400", 1, 8),
                    val: r2ssa::SSAVar::new("W1", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6780", 1, 8),
                    val: r2ssa::SSAVar::new("W2", 0, 4),
                },
                r2ssa::SSAOp::Copy {
                    dst: r2ssa::SSAVar::new("tmp:6780", 2, 8),
                    src: r2ssa::SSAVar::new("SP", 1, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:24c00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 2, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 2, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 1, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 3, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 4, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 2, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
                    addr: r2ssa::SSAVar::new("tmp:6500", 4, 8),
                },
                r2ssa::SSAOp::IntAdd {
                    dst: r2ssa::SSAVar::new("tmp:6400", 6, 8),
                    a: r2ssa::SSAVar::new("SP", 1, 8),
                    b: r2ssa::SSAVar::new("const:4", 0, 8),
                },
                r2ssa::SSAOp::Load {
                    dst: r2ssa::SSAVar::new("tmp:26b00", 3, 4),
                    space: r2il::SpaceId::Ram,
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
                    space: r2il::SpaceId::Ram,
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
    #[cfg(feature = "x86")]
    fn lifted_x86_sum_array_retains_certified_parameter_home_and_residual() {
        fn decode_hex(bytes: &str) -> Vec<u8> {
            let bytes = bytes.as_bytes();
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
        let fixtures = [
            (
                0x100000610,
                "554889e548897df88975f4c745f000000000c745ec00000000",
            ),
            (0x100000629, "8b45ec3b45f47d1c"),
            (
                0x100000631,
                "488b45f848634dec8b04880345f08945f08b45ec83c0018945ecebdc",
            ),
            (0x10000064d, "8b45f05dc3"),
        ];
        let blocks = fixtures
            .into_iter()
            .map(|(addr, hex)| {
                let bytes = decode_hex(hex);
                disasm
                    .lift_block(&bytes, addr, bytes.len())
                    .expect("lifted sum_array block")
            })
            .collect::<Vec<_>>();
        let host_signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 64,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![
                r2types::FunctionParamSpec {
                    name: "arg0".to_string(),
                    ty: None,
                },
                r2types::FunctionParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Signed,
                    }),
                },
            ],
        };
        let parsed_context = r2types::ParsedExternalContext {
            current_signature: Some(host_signature.clone()),
            merged_signature: Some(host_signature),
            register_params: vec![
                r2types::ExternalRegisterParamSpec {
                    name: "arg0".to_string(),
                    ty: None,
                    reg: "RDI".to_string(),
                },
                r2types::ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 64,
                        signedness: r2types::Signedness::Signed,
                    }),
                    reg: "RSI".to_string(),
                },
            ],
            ..r2types::ParsedExternalContext::default()
        };
        let source_snapshot = x86_exact_test_snapshot(
            &arch,
            "sum-array/rev1",
            &["RDI", "RSI"],
            &[(0, -8, 8), (1, -12, 4)],
            &[(-16, 4), (-20, 4)],
            false,
            Vec::new(),
        );
        let response = r2engine::EngineSession::new().decompile_function_from_input(
            r2engine::EngineFunctionDecompileRequestInput::single_function(
                r2engine::EngineFunctionInput {
                    function_name: "sym._sum_array".to_string(),
                    function_addr: 0x100000610,
                    blocks,
                    arch: Some(arch.clone()),
                    semantic_metadata_enabled: false,
                    source_snapshot: Some(source_snapshot),
                },
                Some(64),
                parsed_context,
            ),
        );
        let len_home_objects = response
            .function_facts
            .render_facts()
            .stack_slots()
            .filter_map(|(object, _, offset, _)| (offset == -12).then_some(object))
            .collect::<Vec<_>>();
        let [len_home_object] = len_home_objects.as_slice() else {
            panic!("expected one -12 parameter home, got {len_home_objects:?}");
        };
        let len_home = response
            .function_facts
            .authorized_stack_param_owner_render(*len_home_object, -12)
            .unwrap_or_else(|| {
                panic!(
                    "second parameter home should authorize its signature owner; type_facts={:?}",
                    response.function_facts.type_facts()
                )
            });
        assert_eq!(len_home.name, "arg1");
        // Legacy facts stay inspectable and the render stays honest about its
        // status: the output carries its proof note rather than being withheld.
        assert!(
            (response.output.contains("r2dec residual:")
                || response.output.contains("r2dec proof:"))
                && !response.output.contains("for (int32_t var_14h = 0;")
                && !response.output.contains("return var_10h;"),
            "legacy facts must remain inspectable without authorizing production executable C; output={} render_facts={:?}",
            response.output,
            response.function_facts.render_facts()
        );
    }

    #[test]
    fn enrich_decompiler_type_context_applies_live_arm64_struct_array_index_override() {
        let arch = ArchSpec::new("aarch64");
        let block = live_arm64_struct_array_index_block();
        let signature = Some(signature_spec(
            None,
            vec![
                ("arg1", Some(ptr_type(r2types::CTypeLike::Void))),
                ("arg2", Some(signed_type(32))),
                ("arg3", Some(signed_type(32))),
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
        let rendered = arg0.map(r2types::render_c_type_like).unwrap_or_default();
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
    #[cfg(feature = "x86")]
    fn semantic_validator_rejects_mutated_copy_width() {
        let arch = CString::new("x86-64").unwrap();
        let context = r2il_arch_init(arch.as_ptr());
        let bytes = [
            0x31, 0xc0, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
            0x90, 0x90,
        ];
        let block = r2il_lift(context, bytes.as_ptr(), bytes.len(), 0x1000);
        assert_eq!(r2il_block_validate(context, block), 1);
        let block_ref = unsafe { &mut *block };
        let mut mutated = false;
        for op in &mut block_ref.ops {
            if let R2ILOp::Copy { src, .. } = op {
                src.size = src.size.saturating_add(1);
                mutated = true;
                break;
            }
        }
        assert!(mutated);
        assert_eq!(r2il_block_validate(context, block), 0);
        let error = unsafe { CStr::from_ptr(r2il_error(context)) }.to_string_lossy();
        assert!(error.contains("op.copy.width_mismatch") && error.contains("block.ops"));
        drop_test_block(block);
        drop_test_context(context);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn semantic_validator_rejects_out_of_range_op_metadata() {
        let arch = CString::new("x86-64").unwrap();
        let context = r2il_arch_init(arch.as_ptr());
        let bytes = [
            0x31, 0xc0, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
            0x90, 0x90,
        ];
        let block = r2il_lift(context, bytes.as_ptr(), bytes.len(), 0x1000);
        let block_ref = unsafe { &mut *block };
        block_ref.set_op_metadata(block_ref.ops.len(), r2il::OpMetadata::default());
        assert_eq!(r2il_block_validate(context, block), 0);
        let error = unsafe { CStr::from_ptr(r2il_error(context)) }.to_string_lossy();
        assert!(error.contains("block.op_metadata") && error.contains("index_oob"));
        drop_test_block(block);
        drop_test_context(context);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn semantic_validator_rejects_invalid_guarded_load() {
        let arch = CString::new("x86-64").unwrap();
        let context = r2il_arch_init(arch.as_ptr());
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::LoadGuarded {
            dst: Varnode::register(0, 8),
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(8, 8),
            guard: Varnode::register(16, 8),
            ordering: r2il::MemoryOrdering::Relaxed,
        });
        assert_eq!(r2il_block_validate(context, &block), 0);
        let error = unsafe { CStr::from_ptr(r2il_error(context)) }.to_string_lossy();
        assert!(error.contains("op.load_guarded.guard_size"));
        drop_test_context(context);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn op_json_preserves_mutated_varnode_metadata() {
        let arch = CString::new("x86-64").unwrap();
        let context = r2il_arch_init(arch.as_ptr());
        let bytes = [
            0x31, 0xc0, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
            0x90, 0x90,
        ];
        let block = r2il_lift(context, bytes.as_ptr(), bytes.len(), 0x1000);
        let metadata = r2il::VarnodeMetadata {
            scalar_kind: Some(r2il::ScalarKind::UnsignedInt),
            ..r2il::VarnodeMetadata::default()
        };
        let block_ref = unsafe { &mut *block };
        let op_index = block_ref
            .ops
            .iter_mut()
            .enumerate()
            .find_map(|(index, op)| {
                let R2ILOp::Copy { dst, .. } = op else {
                    return None;
                };
                dst.set_meta(metadata.clone());
                Some(index)
            })
            .expect("copy op");
        let raw = r2il_block_op_json_named(context, block, op_index);
        let json = unsafe { CStr::from_ptr(raw) }
            .to_string_lossy()
            .into_owned();
        drop_test_ffi_string(raw);
        assert!(json.contains("unsigned_int"));
        drop_test_block(block);
        drop_test_context(context);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn memory_render_has_one_exact_canonical_schema() {
        let arch = CString::new("x86-64").unwrap();
        let context = r2il_arch_init(arch.as_ptr());
        unsafe {
            (*context).arch = None;
        }
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push_with_metadata(
            R2ILOp::Load {
                dst: Varnode::register(0, 8),
                space: r2il::SpaceId::Ram,
                addr: Varnode::constant(0x1000, 8),
            },
            Some(r2il::OpMetadata {
                memory_class: Some(r2il::MemoryClass::Stack),
                memory_ordering: Some(r2il::MemoryOrdering::AcqRel),
                permissions: Some(r2il::MemoryPermissions {
                    read: true,
                    write: false,
                    execute: false,
                    volatile: false,
                    cacheable: true,
                }),
                valid_range: Some(r2il::MemoryRange {
                    start: 0x1000,
                    end: 0x2000,
                }),
                bank_id: Some("bank0".to_string()),
                segment_id: Some("seg0".to_string()),
                atomic_kind: Some(r2il::AtomicKind::ReadModifyWrite),
                ..r2il::OpMetadata::default()
            }),
        );
        let raw = r2il_block_mem_access(context, &block);
        assert!(!raw.is_null());
        let json = unsafe { CStr::from_ptr(raw) }
            .to_string_lossy()
            .into_owned();
        drop_test_ffi_string(raw);
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(
            parsed,
            serde_json::json!([{
                "schema_version": 1,
                "type": "load",
                "size_bytes": 8,
                "address": {"space": "const", "offset": 0x1000, "size": 8},
                "ordering": "acq_rel",
                "atomic_kind": "read_modify_write",
                "memory_class": "stack",
                "permissions": {
                    "read": true,
                    "write": false,
                    "execute": false,
                    "volatile": false,
                    "cacheable": true
                },
                "range": {"start": 0x1000, "end": 0x2000},
                "bank_id": "bank0",
                "segment_id": "seg0"
            }])
        );
        drop_test_context(context);
    }

    #[test]
    #[cfg(feature = "x86")]
    fn memory_render_covers_every_access_kind_without_legacy_keys() {
        let arch = CString::new("x86-64").unwrap();
        let context = r2il_arch_init(arch.as_ptr());
        let rsp = unsafe {
            (*context)
                .arch
                .as_ref()
                .and_then(|arch| arch.get_register("RSP"))
                .cloned()
                .expect("RSP register")
        };
        unsafe {
            (*context).arch = None;
        }

        let address = Varnode::constant(0x2000, 8);
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 4),
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(rsp.offset, rsp.size),
        });
        block.push(R2ILOp::LoadLinked {
            dst: Varnode::unique(0x11, 4),
            space: r2il::SpaceId::Ram,
            addr: address.clone(),
            ordering: r2il::MemoryOrdering::Acquire,
        });
        block.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: address.clone(),
            val: Varnode::constant(0x21, 4),
        });
        block.push(R2ILOp::StoreConditional {
            result: Some(Varnode::unique(0x12, 1)),
            space: r2il::SpaceId::Ram,
            addr: address.clone(),
            val: Varnode::constant(0x22, 4),
            ordering: r2il::MemoryOrdering::Release,
        });
        block.push(R2ILOp::AtomicCAS {
            dst: Varnode::unique(0x13, 4),
            space: r2il::SpaceId::Ram,
            addr: address.clone(),
            expected: Varnode::constant(0x23, 4),
            replacement: Varnode::constant(0x24, 4),
            ordering: r2il::MemoryOrdering::SeqCst,
        });
        block.push(R2ILOp::LoadGuarded {
            dst: Varnode::unique(0x14, 4),
            space: r2il::SpaceId::Ram,
            addr: address.clone(),
            guard: Varnode::constant(1, 1),
            ordering: r2il::MemoryOrdering::Relaxed,
        });
        block.push(R2ILOp::StoreGuarded {
            space: r2il::SpaceId::Ram,
            addr: address,
            val: Varnode::constant(0x25, 4),
            guard: Varnode::constant(1, 1),
            ordering: r2il::MemoryOrdering::AcqRel,
        });

        let raw = r2il_block_mem_access(context, &block);
        assert!(!raw.is_null());
        let json = unsafe { CStr::from_ptr(raw) }
            .to_string_lossy()
            .into_owned();
        drop_test_ffi_string(raw);
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(
            parsed,
            serde_json::json!([
                {
                    "schema_version": 1,
                    "type": "load",
                    "size_bytes": 4,
                    "address": {
                        "space": "register",
                        "offset": rsp.offset,
                        "size": rsp.size,
                        "name": "RSP"
                    },
                    "stack_address": {"base": "RSP", "offset": 0}
                },
                {
                    "schema_version": 1,
                    "type": "load_linked",
                    "size_bytes": 4,
                    "address": {"space": "const", "offset": 0x2000, "size": 8},
                    "ordering": "acquire",
                    "atomic_kind": "load_linked"
                },
                {
                    "schema_version": 1,
                    "type": "store",
                    "size_bytes": 4,
                    "address": {"space": "const", "offset": 0x2000, "size": 8},
                    "value": {"space": "const", "offset": 0x21, "size": 4}
                },
                {
                    "schema_version": 1,
                    "type": "store_conditional",
                    "size_bytes": 4,
                    "address": {"space": "const", "offset": 0x2000, "size": 8},
                    "value": {"space": "const", "offset": 0x22, "size": 4},
                    "result": {"space": "unique", "offset": 0x12, "size": 1},
                    "ordering": "release",
                    "atomic_kind": "store_conditional"
                },
                {
                    "schema_version": 1,
                    "type": "atomic_cas",
                    "size_bytes": 4,
                    "address": {"space": "const", "offset": 0x2000, "size": 8},
                    "expected": {"space": "const", "offset": 0x23, "size": 4},
                    "replacement": {"space": "const", "offset": 0x24, "size": 4},
                    "result": {"space": "unique", "offset": 0x13, "size": 4},
                    "ordering": "seq_cst",
                    "atomic_kind": "compare_exchange"
                },
                {
                    "schema_version": 1,
                    "type": "load_guarded",
                    "size_bytes": 4,
                    "address": {"space": "const", "offset": 0x2000, "size": 8},
                    "guard": {"space": "const", "offset": 1, "size": 1},
                    "guarded": true,
                    "ordering": "relaxed"
                },
                {
                    "schema_version": 1,
                    "type": "store_guarded",
                    "size_bytes": 4,
                    "address": {"space": "const", "offset": 0x2000, "size": 8},
                    "value": {"space": "const", "offset": 0x25, "size": 4},
                    "guard": {"space": "const", "offset": 1, "size": 1},
                    "guarded": true,
                    "ordering": "acq_rel"
                }
            ])
        );
        for access in parsed.as_array().expect("memory access array") {
            for legacy in [
                "addr",
                "addr_detail",
                "size",
                "write",
                "stack",
                "stack_base",
                "stack_offset",
            ] {
                assert!(
                    access.get(legacy).is_none(),
                    "canonical memory access retained legacy key {legacy}"
                );
            }
        }
        drop_test_context(context);
    }
}
