use std::collections::HashMap;

use r2il::{ArchSpec, R2ILBlock};
use r2sleigh_lift::Disassembler;
use serde::{Deserialize, Serialize};

use crate::{SSABlock, SSAFunction, SSAOp, SSAVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum DataRefKind {
    Code,
    Data,
}

impl DataRefKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Code => "c",
            Self::Data => "d",
        }
    }

    pub const fn as_char(self) -> char {
        match self {
            Self::Code => 'c',
            Self::Data => 'd',
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DataRefFact {
    pub from: u64,
    pub to: u64,
    pub kind: DataRefKind,
}

impl DataRefFact {
    const fn data(from: u64, to: u64) -> Self {
        Self {
            from,
            to,
            kind: DataRefKind::Data,
        }
    }

    const fn code(from: u64, to: u64) -> Self {
        Self {
            from,
            to,
            kind: DataRefKind::Code,
        }
    }
}

pub fn parse_const_value(name: &str) -> Option<u64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;

    let val_str = val_str.split('_').next().unwrap_or(val_str);

    if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }

    if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        return dec.parse::<u64>().ok();
    }
    if val_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return u64::from_str_radix(val_str, 16).ok();
    }
    val_str.parse::<u64>().ok()
}

fn parse_const_addr(name: &str) -> Option<u64> {
    parse_const_value(name).filter(|addr| *addr >= 0x10000)
}

fn ssa_var_key(var: &SSAVar) -> String {
    format!("{}_{}", var.name.to_ascii_lowercase(), var.version)
}

fn resolve_const_value(const_env: &HashMap<String, u64>, var: &SSAVar) -> Option<u64> {
    parse_const_value(&var.name).or_else(|| const_env.get(&ssa_var_key(var)).copied())
}

fn resolve_const_addr(const_env: &HashMap<String, u64>, var: &SSAVar) -> Option<u64> {
    resolve_const_value(const_env, var).filter(|addr| *addr >= 0x10000)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum MemorySlotKey {
    Absolute(u64),
    Stack { base: String, offset: i64 },
}

fn is_stack_base_name(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "sp" | "rsp" | "esp" | "fp" | "rbp" | "ebp" | "x29"
    )
}

fn resolve_memory_slot_key(
    addr_env: &HashMap<String, MemorySlotKey>,
    const_env: &HashMap<String, u64>,
    var: &SSAVar,
) -> Option<MemorySlotKey> {
    if let Some(addr) = resolve_const_addr(const_env, var) {
        return Some(MemorySlotKey::Absolute(addr));
    }

    let lower = var.name.to_ascii_lowercase();
    if is_stack_base_name(&lower) {
        return Some(MemorySlotKey::Stack {
            base: lower,
            offset: 0,
        });
    }

    addr_env.get(&ssa_var_key(var)).cloned()
}

fn resolve_absolute_addr_with_delta(addr: u64, delta: i64) -> Option<u64> {
    if delta >= 0 {
        addr.checked_add(delta as u64)
    } else {
        addr.checked_sub(delta.unsigned_abs())
    }
}

fn resolve_memory_slot_with_delta(base: MemorySlotKey, delta: i64) -> Option<MemorySlotKey> {
    match base {
        MemorySlotKey::Absolute(addr) => {
            resolve_absolute_addr_with_delta(addr, delta).map(MemorySlotKey::Absolute)
        }
        MemorySlotKey::Stack { base, offset } => offset
            .checked_add(delta)
            .map(|offset| MemorySlotKey::Stack { base, offset }),
    }
}

fn resolve_memory_slot_from_add_sub(
    addr_env: &HashMap<String, MemorySlotKey>,
    const_env: &HashMap<String, u64>,
    a: &SSAVar,
    b: &SSAVar,
    is_sub: bool,
) -> Option<MemorySlotKey> {
    if let Some(delta_raw) = resolve_const_value(const_env, b)
        && let Ok(delta) = i64::try_from(delta_raw)
        && let Some(base) = resolve_memory_slot_key(addr_env, const_env, a)
    {
        return resolve_memory_slot_with_delta(base, if is_sub { -delta } else { delta });
    }
    if !is_sub
        && let Some(delta_raw) = resolve_const_value(const_env, a)
        && let Ok(delta) = i64::try_from(delta_raw)
        && let Some(base) = resolve_memory_slot_key(addr_env, const_env, b)
    {
        return resolve_memory_slot_with_delta(base, delta);
    }
    None
}

const fn bit_width(size: u32) -> u32 {
    let bits = size.saturating_mul(8);
    if bits > 64 { 64 } else { bits }
}

fn mask_to_bits(value: u64, bits: u32) -> u64 {
    match bits {
        0 => 0,
        64.. => value,
        n => value & ((1u64 << n) - 1),
    }
}

fn sign_extend_bits(value: u64, bits: u32) -> u64 {
    if bits == 0 {
        return 0;
    }
    if bits >= 64 {
        return value;
    }
    let masked = mask_to_bits(value, bits);
    let sign_bit = 1u64 << (bits - 1);
    if (masked & sign_bit) != 0 {
        masked | (!0u64 << bits)
    } else {
        masked
    }
}

pub fn data_refs_from_ssa_with_op_sources(
    ssa_blocks: &[SSABlock],
    op_sources: Option<&[Vec<u64>]>,
) -> Vec<DataRefFact> {
    let mut refs = Vec::new();
    let mut const_env: HashMap<String, u64> = HashMap::new();
    let mut addr_env: HashMap<String, MemorySlotKey> = HashMap::new();
    let mut stack_value_env: HashMap<MemorySlotKey, u64> = HashMap::new();

    for (block_idx, block) in ssa_blocks.iter().enumerate() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let from = op_sources
                .and_then(|blocks| blocks.get(block_idx))
                .and_then(|ops| ops.get(op_idx))
                .copied()
                .unwrap_or(block.addr);
            match op {
                SSAOp::Copy { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        const_env.insert(ssa_var_key(dst), value);
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                }
                SSAOp::Load { addr, .. } => {
                    if let Some(target) = resolve_const_addr(&const_env, addr) {
                        refs.push(DataRefFact::data(from, target));
                    }
                    if let SSAOp::Load { dst, .. } = op
                        && let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, addr)
                        && let Some(value) = stack_value_env.get(&slot).copied()
                    {
                        const_env.insert(ssa_var_key(dst), value);
                        if value >= 0x10000 {
                            refs.push(DataRefFact::data(from, value));
                        }
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    if let Some(target) = resolve_const_addr(&const_env, addr) {
                        refs.push(DataRefFact::data(from, target));
                    }
                    if let Some(value_addr) = resolve_const_addr(&const_env, val) {
                        refs.push(DataRefFact::data(from, value_addr));
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, addr) {
                        if let Some(value) = resolve_const_value(&const_env, val) {
                            stack_value_env.insert(slot, value);
                        } else {
                            stack_value_env.remove(&slot);
                        }
                    }
                }
                SSAOp::IntAdd { dst, a, b } => {
                    let computed = if let (Some(lhs), Some(rhs)) = (
                        resolve_const_value(&const_env, a),
                        resolve_const_value(&const_env, b),
                    ) {
                        Some(lhs.wrapping_add(rhs))
                    } else {
                        None
                    };
                    if let Some(value) = computed {
                        const_env.insert(ssa_var_key(dst), value);
                    }
                    if let Some(slot) =
                        resolve_memory_slot_from_add_sub(&addr_env, &const_env, a, b, false)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = parse_const_addr(&a.name) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                    if let Some(addr) = parse_const_addr(&b.name) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                    if let Some(target) = computed
                        .filter(|value| *value >= 0x10000)
                        .or_else(|| resolve_const_addr(&const_env, dst))
                    {
                        refs.push(DataRefFact::data(from, target));
                    }
                }
                SSAOp::IntSub { dst, a, b } => {
                    let computed = if let (Some(lhs), Some(rhs)) = (
                        resolve_const_value(&const_env, a),
                        resolve_const_value(&const_env, b),
                    ) {
                        Some(lhs.wrapping_sub(rhs))
                    } else {
                        None
                    };
                    if let Some(value) = computed {
                        const_env.insert(ssa_var_key(dst), value);
                    }
                    if let Some(slot) =
                        resolve_memory_slot_from_add_sub(&addr_env, &const_env, a, b, true)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = parse_const_addr(&a.name) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                    if let Some(addr) = parse_const_addr(&b.name) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                    if let Some(target) = computed
                        .filter(|value| *value >= 0x10000)
                        .or_else(|| resolve_const_addr(&const_env, dst))
                    {
                        refs.push(DataRefFact::data(from, target));
                    }
                }
                SSAOp::PtrAdd {
                    dst,
                    base,
                    index,
                    element_size,
                } => {
                    if let (Some(base_val), Some(index_val)) = (
                        resolve_const_value(&const_env, base),
                        resolve_const_value(&const_env, index),
                    ) {
                        let scaled = index_val.wrapping_mul((*element_size).into());
                        const_env.insert(ssa_var_key(dst), base_val.wrapping_add(scaled));
                    }
                    if let Some(target) = resolve_const_addr(&const_env, dst) {
                        refs.push(DataRefFact::data(from, target));
                    }
                    if let Some(index_val) = resolve_const_value(&const_env, index)
                        && let Ok(delta) =
                            i64::try_from(index_val.wrapping_mul((*element_size).into()))
                        && let Some(base_slot) =
                            resolve_memory_slot_key(&addr_env, &const_env, base)
                        && let Some(slot) = resolve_memory_slot_with_delta(base_slot, delta)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                }
                SSAOp::PtrSub {
                    dst,
                    base,
                    index,
                    element_size,
                } => {
                    if let (Some(base_val), Some(index_val)) = (
                        resolve_const_value(&const_env, base),
                        resolve_const_value(&const_env, index),
                    ) {
                        let scaled = index_val.wrapping_mul((*element_size).into());
                        const_env.insert(ssa_var_key(dst), base_val.wrapping_sub(scaled));
                    }
                    if let Some(target) = resolve_const_addr(&const_env, dst) {
                        refs.push(DataRefFact::data(from, target));
                    }
                    if let Some(index_val) = resolve_const_value(&const_env, index)
                        && let Ok(delta) =
                            i64::try_from(index_val.wrapping_mul((*element_size).into()))
                        && let Some(base_slot) =
                            resolve_memory_slot_key(&addr_env, &const_env, base)
                        && let Some(slot) = resolve_memory_slot_with_delta(base_slot, -delta)
                    {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                }
                SSAOp::Cast { dst, src } | SSAOp::New { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        const_env.insert(ssa_var_key(dst), value);
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                }
                SSAOp::IntZExt { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        let src_bits = bit_width(src.size);
                        let dst_bits = bit_width(dst.size);
                        let zext = mask_to_bits(value, src_bits);
                        const_env.insert(ssa_var_key(dst), mask_to_bits(zext, dst_bits));
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                }
                SSAOp::IntSExt { dst, src } => {
                    if let Some(value) = resolve_const_value(&const_env, src) {
                        let src_bits = bit_width(src.size);
                        let dst_bits = bit_width(dst.size);
                        let sext = sign_extend_bits(value, src_bits);
                        const_env.insert(ssa_var_key(dst), mask_to_bits(sext, dst_bits));
                    }
                    if let Some(slot) = resolve_memory_slot_key(&addr_env, &const_env, src) {
                        addr_env.insert(ssa_var_key(dst), slot);
                    }
                    if let Some(addr) = resolve_const_addr(&const_env, src) {
                        refs.push(DataRefFact::data(from, addr));
                    }
                }
                SSAOp::Call { target, .. } | SSAOp::Branch { target } => {
                    if let Some(addr) = resolve_const_addr(&const_env, target) {
                        refs.push(DataRefFact::code(from, addr));
                    }
                }
                SSAOp::CallInd { target, .. } | SSAOp::BranchInd { target } => {
                    if let Some(addr) = resolve_const_addr(&const_env, target) {
                        refs.push(DataRefFact::code(from, addr));
                    }
                }
                SSAOp::CBranch { target, .. } => {
                    if let Some(addr) = resolve_const_addr(&const_env, target) {
                        refs.push(DataRefFact::code(from, addr));
                    }
                }
                _ => {}
            }
        }
    }

    refs.sort_by_key(|reference| (reference.from, reference.to));
    refs.dedup_by(|a, b| a.from == b.from && a.to == b.to);
    refs
}

pub fn data_refs_from_blocks(
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
    disasm: &Disassembler,
) -> Option<Vec<DataRefFact>> {
    let mut refs = Vec::new();
    let mut inst_ssa_blocks = Vec::new();
    let mut op_source_addrs = Vec::new();
    for block in blocks {
        inst_ssa_blocks.push(crate::block::to_ssa(block, disasm));
        op_source_addrs.push(
            block
                .ops
                .iter()
                .enumerate()
                .map(|(op_idx, _)| {
                    block
                        .op_metadata(op_idx)
                        .and_then(|meta| meta.instruction_addr)
                        .unwrap_or(block.addr)
                })
                .collect::<Vec<_>>(),
        );
    }
    refs.extend(data_refs_from_ssa_with_op_sources(
        &inst_ssa_blocks,
        Some(&op_source_addrs),
    ));

    let func = SSAFunction::from_blocks_for_data_refs(blocks, arch)?;
    let ssa_blocks: Vec<SSABlock> = func
        .blocks()
        .map(|block| SSABlock {
            addr: block.addr,
            size: block.size,
            ops: block.ops.clone(),
        })
        .collect();
    if ssa_blocks.is_empty() {
        return None;
    }

    refs.extend(data_refs_from_ssa_with_op_sources(&ssa_blocks, None));
    refs.sort_by_key(|reference| (reference.from, reference.to, reference.kind));
    refs.dedup_by(|a, b| a.from == b.from && a.to == b.to && a.kind == b.kind);
    Some(refs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    #[test]
    fn data_refs_resolve_const_add_chain_target() {
        let block = SSABlock {
            addr: 0x401000,
            size: 4,
            ops: vec![
                SSAOp::Copy {
                    dst: var("tmp:base", 1, 8),
                    src: var("const:dead0000", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: var("tmp:target", 1, 8),
                    a: var("tmp:base", 1, 8),
                    b: var("const:beef", 0, 8),
                },
                SSAOp::Load {
                    dst: var("tmp:load", 1, 4),
                    space: "ram".to_string(),
                    addr: var("tmp:target", 1, 8),
                },
            ],
        };

        let refs = data_refs_from_ssa_with_op_sources(&[block], None);
        assert!(refs.contains(&DataRefFact::data(0x401000, 0xdeadbeef)));
    }

    #[test]
    fn data_refs_ignore_small_const_add_chain() {
        let block = SSABlock {
            addr: 0x402000,
            size: 4,
            ops: vec![SSAOp::IntAdd {
                dst: var("tmp:small", 1, 8),
                a: var("const:40", 0, 8),
                b: var("const:2", 0, 8),
            }],
        };

        let refs = data_refs_from_ssa_with_op_sources(&[block], None);
        assert!(!refs.iter().any(|reference| reference.to == 0x42));
    }

    #[test]
    fn data_refs_resolve_const_add_chain_across_blocks() {
        let block_a = SSABlock {
            addr: 0x403000,
            size: 4,
            ops: vec![SSAOp::Copy {
                dst: var("tmp:base", 1, 8),
                src: var("const:dead0000", 0, 8),
            }],
        };
        let block_b = SSABlock {
            addr: 0x403004,
            size: 4,
            ops: vec![
                SSAOp::IntAdd {
                    dst: var("tmp:target", 1, 8),
                    a: var("tmp:base", 1, 8),
                    b: var("const:beef", 0, 8),
                },
                SSAOp::Load {
                    dst: var("tmp:load", 1, 4),
                    space: "ram".to_string(),
                    addr: var("tmp:target", 1, 8),
                },
            ],
        };

        let refs = data_refs_from_ssa_with_op_sources(&[block_a, block_b], None);
        assert!(refs.contains(&DataRefFact::data(0x403004, 0xdeadbeef)));
    }

    #[test]
    fn data_refs_use_per_op_source_addr_when_available() {
        let block = SSABlock {
            addr: 0x404000,
            size: 0x20,
            ops: vec![
                SSAOp::Copy {
                    dst: var("tmp:base", 1, 8),
                    src: var("const:404d00", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: var("tmp:target", 1, 8),
                    a: var("tmp:base", 1, 8),
                    b: var("const:108", 0, 8),
                },
                SSAOp::Load {
                    dst: var("tmp:load", 1, 8),
                    space: "ram".to_string(),
                    addr: var("tmp:target", 1, 8),
                },
            ],
        };
        let op_sources = vec![vec![0x404008, 0x40400c, 0x404010]];

        let refs = data_refs_from_ssa_with_op_sources(&[block], Some(&op_sources));
        assert!(refs.contains(&DataRefFact::data(0x40400c, 0x404e08)));
    }

    #[test]
    fn data_refs_use_per_op_source_addr_for_const_sub_chain() {
        let block = SSABlock {
            addr: 0x405000,
            size: 0x20,
            ops: vec![
                SSAOp::Copy {
                    dst: var("tmp:base", 1, 8),
                    src: var("const:405000", 0, 8),
                },
                SSAOp::IntSub {
                    dst: var("tmp:target", 1, 8),
                    a: var("tmp:base", 1, 8),
                    b: var("const:108", 0, 8),
                },
                SSAOp::Load {
                    dst: var("tmp:load", 1, 8),
                    space: "ram".to_string(),
                    addr: var("tmp:target", 1, 8),
                },
            ],
        };
        let op_sources = vec![vec![0x405008, 0x40500c, 0x405010]];

        let refs = data_refs_from_ssa_with_op_sources(&[block], Some(&op_sources));
        assert!(refs.contains(&DataRefFact::data(0x40500c, 0x404ef8)));
    }

    #[test]
    fn data_refs_resolve_const_add_chain_through_stack_spills() {
        let block = SSABlock {
            addr: 0x100001138,
            size: 0x3c,
            ops: vec![
                SSAOp::IntSub {
                    dst: var("SP", 1, 8),
                    a: var("SP", 0, 8),
                    b: var("const:10", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: var("tmp:6500", 1, 8),
                    a: var("SP", 1, 8),
                    b: var("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: var("tmp:6500", 1, 8),
                    val: var("const:404d00", 0, 8),
                },
                SSAOp::Load {
                    dst: var("X8", 4, 8),
                    space: "ram".to_string(),
                    addr: var("tmp:6500", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: var("tmp:11f80", 1, 8),
                    a: var("X8", 4, 8),
                    b: var("const:108", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: var("SP", 1, 8),
                    val: var("tmp:11f80", 1, 8),
                },
                SSAOp::Load {
                    dst: var("X9", 1, 8),
                    space: "ram".to_string(),
                    addr: var("SP", 1, 8),
                },
                SSAOp::IntSub {
                    dst: var("tmp:cmp", 1, 8),
                    a: var("X9", 1, 8),
                    b: var("const:404e08", 0, 8),
                },
            ],
        };
        let op_sources = vec![vec![
            0x100001138,
            0x10000113c,
            0x100001140,
            0x100001144,
            0x100001148,
            0x10000114c,
            0x100001150,
            0x100001154,
        ]];

        let refs = data_refs_from_ssa_with_op_sources(&[block], Some(&op_sources));
        assert!(refs.contains(&DataRefFact::data(0x100001148, 0x404e08)));
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    #[kani::proof]
    fn data_ref_bit_width_clamps_to_machine_word() {
        let size: u32 = kani::any();
        let bits = bit_width(size);

        assert!(bits <= 64);
        if size <= 8 {
            assert_eq!(bits, size * 8);
        } else {
            assert_eq!(bits, 64);
        }
    }

    #[kani::proof]
    fn data_ref_mask_to_bits_is_total_and_bounded() {
        let value: u64 = kani::any();
        let bits: u32 = kani::any();
        let masked = mask_to_bits(value, bits);

        if bits == 0 {
            assert_eq!(masked, 0);
        } else if bits >= 64 {
            assert_eq!(masked, value);
        } else {
            let expected = value & ((1u64 << bits) - 1);
            assert_eq!(masked, expected);
            assert_eq!(masked >> bits, 0);
        }
    }

    #[kani::proof]
    fn data_ref_absolute_addr_delta_uses_checked_arithmetic() {
        let addr: u64 = kani::any();
        let delta: i64 = kani::any();
        let resolved = resolve_absolute_addr_with_delta(addr, delta);

        let expected = if delta >= 0 {
            addr.checked_add(delta as u64)
        } else {
            addr.checked_sub(delta.unsigned_abs())
        };
        assert_eq!(resolved, expected);
    }
}
