//! Phi-node placement for SSA construction.
//!
//! This module implements the phi-node placement algorithm using the
//! iterated dominance frontier, as described by Cytron et al.

use std::collections::{HashMap, HashSet};

use crate::cfg::{BasicBlock, CFG};
use crate::domtree::DomTree;
use crate::naming::{RegisterNameMap, varnode_to_name};
use crate::op::SSAOp;
use crate::var::SSAVar;

/// Information about phi nodes to be placed in the CFG.
#[derive(Debug, Clone, Default)]
pub struct PhiPlacement {
    /// Phi nodes to place at each block: block addr -> list of (variable name, predecessor addrs)
    pub phis: HashMap<u64, Vec<PhiInfo>>,
}

/// Information about a single phi node.
#[derive(Debug, Clone)]
pub struct PhiInfo {
    /// The variable name (base name without version).
    pub var_name: String,
    /// The size of the variable in bytes.
    pub var_size: u32,
    /// The predecessor blocks that contribute values.
    pub predecessors: Vec<u64>,
}

impl PhiPlacement {
    /// Create a new empty phi placement.
    pub fn new() -> Self {
        Self::default()
    }

    /// Compute phi placement for a CFG given variable definitions.
    ///
    /// # Arguments
    /// * `cfg` - The control flow graph
    /// * `domtree` - The dominator tree for the CFG
    /// * `defs` - Map from variable name to the blocks where it's defined
    /// * `var_sizes` - Map from variable name to its size in bytes
    pub fn compute(
        cfg: &CFG,
        domtree: &DomTree,
        defs: &HashMap<String, HashSet<u64>>,
        var_sizes: &HashMap<String, u32>,
    ) -> Self {
        let mut placement = Self::new();

        let mut defs_by_name: Vec<(&String, &HashSet<u64>)> = defs.iter().collect();
        defs_by_name.sort_unstable_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        for (var_name, def_blocks) in defs_by_name {
            let mut def_list: Vec<u64> = def_blocks.iter().copied().collect();
            def_list.sort_unstable();
            let mut phi_blocks: Vec<u64> =
                domtree.iterated_frontier(&def_list).into_iter().collect();
            phi_blocks.sort_unstable();

            for phi_block in phi_blocks {
                let preds = cfg.predecessors(phi_block);
                if preds.len() >= 2 {
                    let size = var_sizes.get(var_name).copied().unwrap_or(8);
                    let phi_info = PhiInfo {
                        var_name: var_name.clone(),
                        var_size: size,
                        predecessors: preds,
                    };
                    placement.phis.entry(phi_block).or_default().push(phi_info);
                }
            }
        }

        for phis in placement.phis.values_mut() {
            phis.sort_unstable_by(|lhs, rhs| {
                lhs.var_name
                    .cmp(&rhs.var_name)
                    .then(lhs.var_size.cmp(&rhs.var_size))
                    .then(lhs.predecessors.cmp(&rhs.predecessors))
            });
        }

        placement
    }

    /// Get phi nodes for a specific block.
    pub fn get_phis(&self, block: u64) -> &[PhiInfo] {
        self.phis.get(&block).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Check if a block has any phi nodes.
    pub fn has_phis(&self, block: u64) -> bool {
        self.phis.get(&block).is_some_and(|v| !v.is_empty())
    }

    /// Get all blocks that have phi nodes.
    pub fn blocks_with_phis(&self) -> impl Iterator<Item = u64> + '_ {
        let mut blocks: Vec<u64> = self.phis.keys().copied().collect();
        blocks.sort_unstable();
        blocks.into_iter()
    }

    /// Get total number of phi nodes.
    pub fn total_phis(&self) -> usize {
        self.phis.values().map(|v| v.len()).sum()
    }
}

/// Collect variable definitions from a basic block's operations.
///
/// Returns a map from variable name to whether it's defined in this block.
pub fn collect_defs_from_block(block: &BasicBlock) -> HashSet<String> {
    let mut defs = HashSet::new();

    for op in &block.ops {
        if let Some(dst) = get_op_output(op) {
            defs.insert(dst);
        }
    }

    defs
}

/// Collect variable definitions from a CFG.
///
/// Returns:
/// - `defs`: Map from variable name to set of blocks where it's defined
/// - `var_sizes`: Map from variable name to its size
pub fn collect_defs_from_cfg(cfg: &CFG) -> (HashMap<String, HashSet<u64>>, HashMap<String, u32>) {
    collect_defs_from_cfg_with_names(cfg, None)
}

/// Collect variable definitions from a CFG with optional register names.
pub fn collect_defs_from_cfg_with_names(
    cfg: &CFG,
    reg_names: Option<&RegisterNameMap>,
) -> (HashMap<String, HashSet<u64>>, HashMap<String, u32>) {
    let mut defs: HashMap<String, HashSet<u64>> = HashMap::new();
    let mut var_sizes: HashMap<String, u32> = HashMap::new();

    for addr in cfg.block_addrs() {
        let Some(block) = cfg.get_block(addr) else {
            continue;
        };
        for op in &block.ops {
            if let Some((name, size)) = get_op_output_with_size(op, reg_names) {
                defs.entry(name.clone()).or_default().insert(block.addr);
                var_sizes.insert(name, size);
            }
        }
    }

    (defs, var_sizes)
}

/// Get the output variable name from an r2il operation.
fn get_op_output(op: &r2il::R2ILOp) -> Option<String> {
    get_op_output_with_size(op, None).map(|(name, _)| name)
}

/// Get the output variable name and size from an r2il operation.
fn get_op_output_with_size(
    op: &r2il::R2ILOp,
    reg_names: Option<&RegisterNameMap>,
) -> Option<(String, u32)> {
    use r2il::R2ILOp::*;

    let varnode = match op {
        Copy { dst, .. }
        | Load { dst, .. }
        | IntAdd { dst, .. }
        | IntSub { dst, .. }
        | IntMult { dst, .. }
        | IntDiv { dst, .. }
        | IntSDiv { dst, .. }
        | IntRem { dst, .. }
        | IntSRem { dst, .. }
        | IntNegate { dst, .. }
        | IntCarry { dst, .. }
        | IntSCarry { dst, .. }
        | IntSBorrow { dst, .. }
        | IntAnd { dst, .. }
        | IntOr { dst, .. }
        | IntXor { dst, .. }
        | IntNot { dst, .. }
        | IntLeft { dst, .. }
        | IntRight { dst, .. }
        | IntSRight { dst, .. }
        | IntEqual { dst, .. }
        | IntNotEqual { dst, .. }
        | IntLess { dst, .. }
        | IntSLess { dst, .. }
        | IntLessEqual { dst, .. }
        | IntSLessEqual { dst, .. }
        | IntZExt { dst, .. }
        | IntSExt { dst, .. }
        | BoolNot { dst, .. }
        | BoolAnd { dst, .. }
        | BoolOr { dst, .. }
        | BoolXor { dst, .. }
        | Piece { dst, .. }
        | Subpiece { dst, .. }
        | PopCount { dst, .. }
        | Lzcount { dst, .. }
        | FloatAdd { dst, .. }
        | FloatSub { dst, .. }
        | FloatMult { dst, .. }
        | FloatDiv { dst, .. }
        | FloatNeg { dst, .. }
        | FloatAbs { dst, .. }
        | FloatSqrt { dst, .. }
        | FloatCeil { dst, .. }
        | FloatFloor { dst, .. }
        | FloatRound { dst, .. }
        | FloatNaN { dst, .. }
        | FloatEqual { dst, .. }
        | FloatNotEqual { dst, .. }
        | FloatLess { dst, .. }
        | FloatLessEqual { dst, .. }
        | Int2Float { dst, .. }
        | Float2Int { dst, .. }
        | FloatFloat { dst, .. }
        | Trunc { dst, .. }
        | CpuId { dst }
        | Multiequal { dst, .. }
        | Indirect { dst, .. }
        | PtrAdd { dst, .. }
        | PtrSub { dst, .. }
        | SegmentOp { dst, .. }
        | New { dst, .. }
        | Cast { dst, .. }
        | Extract { dst, .. }
        | Insert { dst, .. } => Some(dst),
        CallOther { output, .. } => output.as_ref(),
        _ => None,
    };

    varnode.map(|vn| (varnode_to_name(vn, reg_names), vn.size))
}

/// Create SSA phi operations from phi placement info.
pub fn create_phi_ops(placement: &PhiPlacement, block_addr: u64) -> Vec<SSAOp> {
    let mut ops = Vec::new();

    for phi_info in placement.get_phis(block_addr) {
        // Create placeholder sources - these will be filled in during renaming
        let sources: Vec<SSAVar> = phi_info
            .predecessors
            .iter()
            .map(|_| SSAVar::new(&phi_info.var_name, 0, phi_info.var_size))
            .collect();

        let phi_op = SSAOp::Phi {
            dst: SSAVar::new(&phi_info.var_name, 0, phi_info.var_size),
            sources,
        };

        ops.push(phi_op);
    }

    ops
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};

    fn make_const(val: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size,
            meta: None,
        }
    }

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_ram(addr: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Ram,
            offset: addr,
            size,
            meta: None,
        }
    }

    #[test]
    fn test_phi_placement_diamond() {
        // Diamond CFG where both branches write to the same register
        //     A (0x1000) - entry
        //    / \
        //   B   C        - both write to reg:0
        //    \ /
        //     D (0x100c) - needs phi for reg:0
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8), // Write to reg:0
                        src: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x100c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8), // Write to reg:0
                    src: make_const(2, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        let domtree = DomTree::compute(&cfg);
        let (defs, var_sizes) = collect_defs_from_cfg(&cfg);

        let placement = PhiPlacement::compute(&cfg, &domtree, &defs, &var_sizes);

        // Should have a phi at block D (0x100c) for reg:0
        assert!(placement.has_phis(0x100c));
        let phis = placement.get_phis(0x100c);
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].var_name, "reg:0");
        assert_eq!(phis[0].predecessors.len(), 2);
    }

    #[test]
    fn test_no_phi_needed() {
        // Linear CFG - no phi needed
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        let domtree = DomTree::compute(&cfg);
        let (defs, var_sizes) = collect_defs_from_cfg(&cfg);

        let placement = PhiPlacement::compute(&cfg, &domtree, &defs, &var_sizes);

        // No phis needed in linear CFG
        assert_eq!(placement.total_phis(), 0);
    }

    #[test]
    fn test_collect_defs() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
                        src: make_const(2, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(3, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        let (defs, var_sizes) = collect_defs_from_cfg(&cfg);

        // reg:0 defined in both blocks
        assert!(defs.contains_key("reg:0"));
        assert_eq!(defs["reg:0"].len(), 2);

        // reg:8 defined only in first block
        assert!(defs.contains_key("reg:8"));
        assert_eq!(defs["reg:8"].len(), 1);

        // Sizes should be recorded
        assert_eq!(var_sizes.get("reg:0"), Some(&8));
        assert_eq!(var_sizes.get("reg:8"), Some(&8));
    }
}
