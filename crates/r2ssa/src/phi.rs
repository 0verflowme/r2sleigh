//! Phi-node placement for SSA construction.
//!
//! This module implements the phi-node placement algorithm using the
//! iterated dominance frontier, as described by Cytron et al.

use std::collections::{HashMap, HashSet};

use crate::cfg::{BasicBlock, CFG};
use crate::control::{SsaExecutionStopReason, SsaWorkControl, UncheckedSsaWorkControl};
use crate::domtree::DomTree;
use crate::naming::{RegisterNameMap, varnode_to_name};
use crate::op::SSAOp;
use crate::var::{CanonicalStorageId, SSAVar};

pub type DefinitionSitesByName = HashMap<String, HashSet<u64>>;
pub type DefinitionSizesByName = HashMap<String, u32>;
pub type CanonicalStorageByName = HashMap<String, CanonicalStorageId>;
pub type DefinitionCollection = (
    DefinitionSitesByName,
    DefinitionSizesByName,
    CanonicalStorageByName,
);

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
    /// Lifted storage identity, independent of register/display names.
    pub storage: Option<CanonicalStorageId>,
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
        Self::compute_with_storage(cfg, domtree, defs, var_sizes, &HashMap::new())
    }

    pub fn compute_with_storage(
        cfg: &CFG,
        domtree: &DomTree,
        defs: &HashMap<String, HashSet<u64>>,
        var_sizes: &HashMap<String, u32>,
        storage_by_name: &HashMap<String, CanonicalStorageId>,
    ) -> Self {
        Self::compute_with_storage_and_control(
            cfg,
            domtree,
            defs,
            var_sizes,
            storage_by_name,
            &UncheckedSsaWorkControl,
        )
        .expect("unchecked phi placement cannot stop")
    }

    /// Compute phi placement while polling dominance-frontier worklists.
    pub fn compute_with_storage_and_control<C: SsaWorkControl + ?Sized>(
        cfg: &CFG,
        domtree: &DomTree,
        defs: &HashMap<String, HashSet<u64>>,
        var_sizes: &HashMap<String, u32>,
        storage_by_name: &HashMap<String, CanonicalStorageId>,
        control: &C,
    ) -> Result<Self, SsaExecutionStopReason> {
        control.poll()?;
        let mut placement = Self::new();

        let mut defs_by_name: Vec<(&String, &HashSet<u64>)> = defs.iter().collect();
        defs_by_name.sort_unstable_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        for (var_name, def_blocks) in defs_by_name {
            control.poll()?;
            let mut def_list: Vec<u64> = def_blocks.iter().copied().collect();
            def_list.sort_unstable();
            let mut phi_blocks: Vec<u64> = domtree
                .iterated_frontier_with_control(&def_list, control)?
                .into_iter()
                .collect();
            phi_blocks.sort_unstable();

            for phi_block in phi_blocks {
                control.poll()?;
                let preds = cfg.predecessors(phi_block);
                if preds.len() >= 2 {
                    let size = var_sizes.get(var_name).copied().unwrap_or(8);
                    let storage = storage_by_name.get(var_name).copied().map(|mut storage| {
                        storage.size = size;
                        storage
                    });
                    let phi_info = PhiInfo {
                        var_name: var_name.clone(),
                        var_size: size,
                        storage,
                        predecessors: preds,
                    };
                    placement.phis.entry(phi_block).or_default().push(phi_info);
                }
            }
        }

        for phis in placement.phis.values_mut() {
            control.poll()?;
            phis.sort_unstable_by(|lhs, rhs| {
                lhs.var_name
                    .cmp(&rhs.var_name)
                    .then(lhs.var_size.cmp(&rhs.var_size))
                    .then(lhs.predecessors.cmp(&rhs.predecessors))
            });
        }

        control.poll()?;
        Ok(placement)
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
    let (defs, var_sizes, _) = collect_defs_from_cfg_with_names_and_storage(cfg, reg_names);
    (defs, var_sizes)
}

/// Collect definitions while retaining the lifted storage behind each name.
/// Aliases with different storage bases are deliberately omitted from the
/// storage map so callers fail closed rather than attach the wrong canonical
/// identity. Different widths of the same lifted storage base are retained;
/// phi placement applies the phi's exact width to that base.
pub fn collect_defs_from_cfg_with_names_and_storage(
    cfg: &CFG,
    reg_names: Option<&RegisterNameMap>,
) -> DefinitionCollection {
    collect_defs_from_cfg_with_names_storage_and_control(cfg, reg_names, &UncheckedSsaWorkControl)
        .expect("unchecked definition collection cannot stop")
}

/// Collect definitions and storage while polling the block/operation scan.
pub fn collect_defs_from_cfg_with_names_storage_and_control<C: SsaWorkControl + ?Sized>(
    cfg: &CFG,
    reg_names: Option<&RegisterNameMap>,
    control: &C,
) -> Result<DefinitionCollection, SsaExecutionStopReason> {
    control.poll()?;
    let mut defs: HashMap<String, HashSet<u64>> = HashMap::new();
    let mut var_sizes: HashMap<String, u32> = HashMap::new();
    let mut storage_by_name = HashMap::<String, CanonicalStorageId>::new();
    let mut ambiguous_names = HashSet::new();

    for addr in cfg.block_addrs() {
        control.poll()?;
        let Some(block) = cfg.get_block(addr) else {
            continue;
        };
        for op in &block.ops {
            control.poll()?;
            if let Some(varnode) = get_op_output_varnode(op) {
                let name = varnode_to_name(varnode, reg_names);
                let size = varnode.size;
                defs.entry(name.clone()).or_default().insert(block.addr);
                var_sizes.insert(name.clone(), size);
                let storage = CanonicalStorageId::from_varnode(varnode);
                if storage_by_name.get(&name).is_some_and(|existing| {
                    existing.space != storage.space || existing.offset != storage.offset
                }) {
                    ambiguous_names.insert(name.clone());
                } else {
                    storage_by_name.insert(name, storage);
                }
            }
        }
    }

    storage_by_name.retain(|name, _| !ambiguous_names.contains(name));
    control.poll()?;
    Ok((defs, var_sizes, storage_by_name))
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
    get_op_output_varnode(op).map(|vn| (varnode_to_name(vn, reg_names), vn.size))
}

fn get_op_output_varnode(op: &r2il::R2ILOp) -> Option<&r2il::Varnode> {
    use r2il::R2ILOp::*;

    match op {
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
    }
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

        let storage_by_name = HashMap::from([(
            "reg:0".to_string(),
            CanonicalStorageId {
                space: crate::CanonicalStorageSpace::Register,
                offset: 0,
                size: 4,
            },
        )]);
        let placement =
            PhiPlacement::compute_with_storage(&cfg, &domtree, &defs, &var_sizes, &storage_by_name);
        assert_eq!(
            placement.get_phis(0x100c)[0].storage,
            Some(CanonicalStorageId {
                space: crate::CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            })
        );
    }

    #[test]
    fn storage_collection_retains_one_base_across_widths_and_refuses_two_bases() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: Varnode::unique(0x200, 4),
                    src: make_const(1, 4),
                },
                R2ILOp::Copy {
                    dst: Varnode::unique(0x200, 8),
                    src: make_const(2, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let cfg = CFG::from_blocks(&[block]).expect("single block CFG");
        let (_, _, storage_by_name) = collect_defs_from_cfg_with_names_and_storage(&cfg, None);
        let storage = storage_by_name
            .get("tmp:200")
            .expect("same lifted base remains canonical");
        assert_eq!(storage.space, crate::CanonicalStorageSpace::Unique);
        assert_eq!(storage.offset, 0x200);

        let block = R2ILBlock {
            addr: 0x2000,
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
        };
        let cfg = CFG::from_blocks(&[block]).expect("single block CFG");
        let register_names =
            RegisterNameMap::from([((0, 8), "alias".to_string()), ((8, 8), "alias".to_string())]);
        let (_, _, storage_by_name) =
            collect_defs_from_cfg_with_names_and_storage(&cfg, Some(&register_names));
        assert!(!storage_by_name.contains_key("alias"));
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
