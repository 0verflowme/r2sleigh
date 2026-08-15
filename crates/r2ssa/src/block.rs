//! SSA block and conversion from r2il.

use std::collections::HashMap;

use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
use r2sleigh_lift::Disassembler;
use serde::{Deserialize, Serialize};

use crate::op::SSAOp;
use crate::var::SSAVar;

/// An SSA basic block containing versioned operations.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SSABlock {
    /// The address of the instruction.
    pub addr: u64,
    /// The size of the instruction in bytes.
    pub size: u32,
    /// The SSA operations.
    pub ops: Vec<SSAOp>,
}

/// Context for SSA conversion, tracking variable versions.
#[derive(Debug, Default)]
pub struct SSAContext {
    /// Current version for each variable name.
    versions: HashMap<String, u32>,
    /// Versions allocated by the current operation but not yet visible to reads.
    pending_versions: HashMap<String, u32>,
}

impl SSAContext {
    /// Create a new SSA context.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the current version of a variable (for reading).
    /// Returns 0 if the variable hasn't been seen yet.
    pub fn current_version(&self, name: &str) -> u32 {
        *self.versions.get(name).unwrap_or(&0)
    }

    /// Allocate a new version for a variable (for writing).
    /// Returns the new version number.
    pub fn new_version(&mut self, name: &str) -> u32 {
        let entry = self.versions.entry(name.to_string()).or_insert(0);
        *entry += 1;
        *entry
    }

    fn defer_version(&mut self, name: &str) -> u32 {
        let current = self
            .pending_versions
            .get(name)
            .copied()
            .unwrap_or_else(|| self.current_version(name));
        let version = current + 1;
        self.pending_versions.insert(name.to_string(), version);
        version
    }

    fn commit_deferred_versions(&mut self) {
        for (name, version) in self.pending_versions.drain() {
            self.versions.insert(name, version);
        }
    }

    /// Get all variables that have been defined (version > 0).
    pub fn defined_vars(&self) -> impl Iterator<Item = (&str, u32)> {
        self.versions.iter().filter_map(|(name, &ver)| {
            if ver > 0 {
                Some((name.as_str(), ver))
            } else {
                None
            }
        })
    }
}

impl SSABlock {
    /// Create a new empty SSA block.
    pub fn new(addr: u64, size: u32) -> Self {
        Self {
            addr,
            size,
            ops: Vec::new(),
        }
    }

    /// Add an operation to this block.
    pub fn push(&mut self, op: SSAOp) {
        self.ops.push(op);
    }

    /// Get the number of operations.
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    /// Check if the block is empty.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }
}

/// Convert an r2il block to SSA form.
///
/// This performs single-block SSA conversion:
/// - Each read uses the current version of the variable
/// - Each write creates a new version
///
/// # Arguments
/// * `block` - The r2il block to convert
/// * `disasm` - Disassembler for resolving varnode names
///
/// # Returns
/// An SSA block with versioned variables
pub fn to_ssa(block: &R2ILBlock, disasm: &Disassembler) -> SSABlock {
    let mut ctx = SSAContext::new();
    let mut ssa_block = SSABlock::new(block.addr, block.size);

    for op in &block.ops {
        let ssa_op = convert_op(op, disasm, &mut ctx);
        ctx.commit_deferred_versions();
        ssa_block.push(ssa_op);
    }

    ssa_block
}

/// Convert a varnode to an SSA variable name.
///
/// For registers:
/// - If a name is found, use the name directly (e.g., "rax", "cf")
/// - If no name is found, use "reg:offset" fallback (e.g., "reg:10")
fn varnode_to_name(vn: &Varnode, disasm: &Disassembler) -> String {
    match vn.space {
        SpaceId::Register => disasm
            .register_name(vn)
            .map(|name| name.to_lowercase())
            .unwrap_or_else(|| format!("reg:{:x}", vn.offset)),
        SpaceId::Unique => format!("tmp:{:x}", vn.offset),
        SpaceId::Const => format!("const:{:x}", vn.offset),
        SpaceId::Ram => format!("ram:{:x}", vn.offset),
        SpaceId::Custom(id) => format!("space{}:{:x}", id, vn.offset),
    }
}

/// Convert a varnode to an SSA variable for reading (uses current version).
fn read_var(vn: &Varnode, disasm: &Disassembler, ctx: &SSAContext) -> SSAVar {
    let name = varnode_to_name(vn, disasm);
    let version = ctx.current_version(&name);
    SSAVar::new(name, version, vn.size)
}

/// Convert a varnode to an SSA variable for writing.
///
/// The new version remains invisible to reads until the current operation is
/// fully converted.
fn write_var(vn: &Varnode, disasm: &Disassembler, ctx: &mut SSAContext) -> SSAVar {
    let name = varnode_to_name(vn, disasm);
    let version = ctx.defer_version(&name);
    SSAVar::new(name, version, vn.size)
}

/// Convert an R2ILOp to an SSAOp.
fn convert_op(op: &R2ILOp, disasm: &Disassembler, ctx: &mut SSAContext) -> SSAOp {
    use R2ILOp::*;

    match op {
        Copy { dst, src } => SSAOp::Copy {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Load { dst, space, addr } => SSAOp::Load {
            dst: write_var(dst, disasm, ctx),
            space: *space,
            addr: read_var(addr, disasm, ctx),
        },

        Store { space, addr, val } => SSAOp::Store {
            space: *space,
            addr: read_var(addr, disasm, ctx),
            val: read_var(val, disasm, ctx),
        },
        Fence { ordering } => SSAOp::Fence {
            ordering: *ordering,
        },
        LoadLinked {
            dst,
            space,
            addr,
            ordering,
        } => SSAOp::LoadLinked {
            dst: write_var(dst, disasm, ctx),
            space: *space,
            addr: read_var(addr, disasm, ctx),
            ordering: *ordering,
        },
        StoreConditional {
            result,
            space,
            addr,
            val,
            ordering,
        } => SSAOp::StoreConditional {
            result: result.as_ref().map(|v| write_var(v, disasm, ctx)),
            space: *space,
            addr: read_var(addr, disasm, ctx),
            val: read_var(val, disasm, ctx),
            ordering: *ordering,
        },
        AtomicCAS {
            dst,
            space,
            addr,
            expected,
            replacement,
            ordering,
        } => SSAOp::AtomicCAS {
            dst: write_var(dst, disasm, ctx),
            space: *space,
            addr: read_var(addr, disasm, ctx),
            expected: read_var(expected, disasm, ctx),
            replacement: read_var(replacement, disasm, ctx),
            ordering: *ordering,
        },
        LoadGuarded {
            dst,
            space,
            addr,
            guard,
            ordering,
        } => SSAOp::LoadGuarded {
            dst: write_var(dst, disasm, ctx),
            space: *space,
            addr: read_var(addr, disasm, ctx),
            guard: read_var(guard, disasm, ctx),
            ordering: *ordering,
        },
        StoreGuarded {
            space,
            addr,
            val,
            guard,
            ordering,
        } => SSAOp::StoreGuarded {
            space: *space,
            addr: read_var(addr, disasm, ctx),
            val: read_var(val, disasm, ctx),
            guard: read_var(guard, disasm, ctx),
            ordering: *ordering,
        },

        IntAdd { dst, a, b } => SSAOp::IntAdd {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSub { dst, a, b } => SSAOp::IntSub {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntMult { dst, a, b } => SSAOp::IntMult {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntDiv { dst, a, b } => SSAOp::IntDiv {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSDiv { dst, a, b } => SSAOp::IntSDiv {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntRem { dst, a, b } => SSAOp::IntRem {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSRem { dst, a, b } => SSAOp::IntSRem {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntNegate { dst, src } => SSAOp::IntNegate {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        IntCarry { dst, a, b } => SSAOp::IntCarry {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSCarry { dst, a, b } => SSAOp::IntSCarry {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSBorrow { dst, a, b } => SSAOp::IntSBorrow {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntAnd { dst, a, b } => SSAOp::IntAnd {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntOr { dst, a, b } => SSAOp::IntOr {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntXor { dst, a, b } => SSAOp::IntXor {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntNot { dst, src } => SSAOp::IntNot {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        IntLeft { dst, a, b } => SSAOp::IntLeft {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntRight { dst, a, b } => SSAOp::IntRight {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSRight { dst, a, b } => SSAOp::IntSRight {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntEqual { dst, a, b } => SSAOp::IntEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntNotEqual { dst, a, b } => SSAOp::IntNotEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntLess { dst, a, b } => SSAOp::IntLess {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSLess { dst, a, b } => SSAOp::IntSLess {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntLessEqual { dst, a, b } => SSAOp::IntLessEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntSLessEqual { dst, a, b } => SSAOp::IntSLessEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        IntZExt { dst, src } => SSAOp::IntZExt {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        IntSExt { dst, src } => SSAOp::IntSExt {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        BoolNot { dst, src } => SSAOp::BoolNot {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        BoolAnd { dst, a, b } => SSAOp::BoolAnd {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        BoolOr { dst, a, b } => SSAOp::BoolOr {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        BoolXor { dst, a, b } => SSAOp::BoolXor {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        Piece { dst, hi, lo } => SSAOp::Piece {
            dst: write_var(dst, disasm, ctx),
            hi: read_var(hi, disasm, ctx),
            lo: read_var(lo, disasm, ctx),
        },

        Subpiece { dst, src, offset } => SSAOp::Subpiece {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
            offset: *offset,
        },

        PopCount { dst, src } => SSAOp::PopCount {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Lzcount { dst, src } => SSAOp::Lzcount {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Branch { target } => SSAOp::Branch {
            target: read_var(target, disasm, ctx),
        },

        CBranch { target, cond } => SSAOp::CBranch {
            target: read_var(target, disasm, ctx),
            cond: read_var(cond, disasm, ctx),
        },

        BranchInd { target } => SSAOp::BranchInd {
            target: read_var(target, disasm, ctx),
        },

        Call { target } => SSAOp::Call {
            target: read_var(target, disasm, ctx),
        },

        CallInd { target } => SSAOp::CallInd {
            target: read_var(target, disasm, ctx),
        },

        Return { target } => SSAOp::Return {
            target: read_var(target, disasm, ctx),
        },

        FloatAdd { dst, a, b } => SSAOp::FloatAdd {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatSub { dst, a, b } => SSAOp::FloatSub {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatMult { dst, a, b } => SSAOp::FloatMult {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatDiv { dst, a, b } => SSAOp::FloatDiv {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatNeg { dst, src } => SSAOp::FloatNeg {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatAbs { dst, src } => SSAOp::FloatAbs {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatSqrt { dst, src } => SSAOp::FloatSqrt {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatCeil { dst, src } => SSAOp::FloatCeil {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatFloor { dst, src } => SSAOp::FloatFloor {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatRound { dst, src } => SSAOp::FloatRound {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatNaN { dst, src } => SSAOp::FloatNaN {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatEqual { dst, a, b } => SSAOp::FloatEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatNotEqual { dst, a, b } => SSAOp::FloatNotEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatLess { dst, a, b } => SSAOp::FloatLess {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        FloatLessEqual { dst, a, b } => SSAOp::FloatLessEqual {
            dst: write_var(dst, disasm, ctx),
            a: read_var(a, disasm, ctx),
            b: read_var(b, disasm, ctx),
        },

        Int2Float { dst, src } => SSAOp::Int2Float {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Float2Int { dst, src } => SSAOp::Float2Int {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        FloatFloat { dst, src } => SSAOp::FloatFloat {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Trunc { dst, src } => SSAOp::Trunc {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        CallOther {
            output,
            userop,
            inputs,
        } => SSAOp::CallOther {
            output: output.as_ref().map(|o| write_var(o, disasm, ctx)),
            userop: *userop,
            inputs: inputs.iter().map(|i| read_var(i, disasm, ctx)).collect(),
        },

        Nop => SSAOp::Nop,

        Unimplemented => SSAOp::Unimplemented,

        CpuId { dst } => SSAOp::CpuId {
            dst: write_var(dst, disasm, ctx),
        },

        Breakpoint => SSAOp::Breakpoint,

        Multiequal { dst, inputs } => {
            // Multiequal is already a phi-like construct, convert to Phi
            SSAOp::Phi {
                dst: write_var(dst, disasm, ctx),
                sources: inputs.iter().map(|i| read_var(i, disasm, ctx)).collect(),
            }
        }

        Indirect { dst, src, .. } => {
            // Indirect is used for aliasing analysis; treat as copy for now
            SSAOp::Copy {
                dst: write_var(dst, disasm, ctx),
                src: read_var(src, disasm, ctx),
            }
        }

        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => SSAOp::PtrAdd {
            dst: write_var(dst, disasm, ctx),
            base: read_var(base, disasm, ctx),
            index: read_var(index, disasm, ctx),
            element_size: *element_size,
        },

        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => SSAOp::PtrSub {
            dst: write_var(dst, disasm, ctx),
            base: read_var(base, disasm, ctx),
            index: read_var(index, disasm, ctx),
            element_size: *element_size,
        },

        SegmentOp {
            dst,
            segment,
            offset,
        } => SSAOp::SegmentOp {
            dst: write_var(dst, disasm, ctx),
            segment: read_var(segment, disasm, ctx),
            offset: read_var(offset, disasm, ctx),
        },

        New { dst, src } => SSAOp::New {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Cast { dst, src } => SSAOp::Cast {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
        },

        Extract { dst, src, position } => SSAOp::Extract {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
            position: read_var(position, disasm, ctx),
        },

        Insert {
            dst,
            src,
            value,
            position,
        } => SSAOp::Insert {
            dst: write_var(dst, disasm, ctx),
            src: read_var(src, disasm, ctx),
            value: read_var(value, disasm, ctx),
            position: read_var(position, disasm, ctx),
        },

        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => {
            let cond = read_var(cond, disasm, ctx);
            let if_true = read_var(if_true, disasm, ctx);
            let if_false = read_var(if_false, disasm, ctx);
            SSAOp::Select {
                dst: write_var(dst, disasm, ctx),
                cond,
                if_true,
                if_false,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ssa_context_versioning() {
        let mut ctx = SSAContext::new();

        // First read should get version 0
        assert_eq!(ctx.current_version("RAX"), 0);

        // First write should get version 1
        assert_eq!(ctx.new_version("RAX"), 1);

        // Next read should get version 1
        assert_eq!(ctx.current_version("RAX"), 1);

        // Second write should get version 2
        assert_eq!(ctx.new_version("RAX"), 2);

        // Different variable starts at 0
        assert_eq!(ctx.current_version("RBX"), 0);
    }

    #[test]
    fn test_deferred_write_is_not_visible_to_same_op_reads() {
        let mut ctx = SSAContext::new();

        assert_eq!(ctx.defer_version("RAX"), 1);
        assert_eq!(ctx.current_version("RAX"), 0);
        ctx.commit_deferred_versions();
        assert_eq!(ctx.current_version("RAX"), 1);
    }

    #[test]
    fn test_ssa_block_basic() {
        let block = SSABlock::new(0x1000, 4);
        assert_eq!(block.addr, 0x1000);
        assert_eq!(block.size, 4);
        assert!(block.is_empty());
        assert_eq!(block.len(), 0);
    }
}
