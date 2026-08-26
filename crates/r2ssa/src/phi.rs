//! Phi-node placement for SSA construction.
//!
//! This module implements the phi-node placement algorithm using the
//! iterated dominance frontier, as described by Cytron et al.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::cfg::{BasicBlock, CFG};
use crate::control::{SsaExecutionStopReason, SsaWorkControl, UncheckedSsaWorkControl};
use crate::domtree::DomTree;
use crate::naming::{RegisterNameMap, varnode_to_name};
use crate::var::{CanonicalStorageId, SSAVar};

/// Exact identity used by phi placement and SSA renaming.
///
/// The semantic name remains presentation advice. Width is part of the
/// identity because Sleigh may reuse one Unique offset for unrelated scratch
/// values of different widths, and register-name maps may expose multiple
/// slices under one spelling. Canonical storage completes the identity; the
/// name remains a separate presentation projection.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RenameIdentity {
    pub name: String,
    pub size: u32,
    pub storage: CanonicalStorageId,
}

impl RenameIdentity {
    pub fn new(name: impl Into<String>, storage: CanonicalStorageId) -> Self {
        Self {
            name: name.into(),
            size: storage.size,
            storage,
        }
    }

    pub fn from_varnode(varnode: &r2il::Varnode, reg_names: Option<&RegisterNameMap>) -> Self {
        Self::new(
            varnode_to_name(varnode, reg_names),
            CanonicalStorageId::from_varnode(varnode),
        )
    }

    pub fn synthetic(name: impl Into<String>, size: u32) -> Self {
        Self::new(name, CanonicalStorageId::unknown(0, size))
    }

    pub fn as_var(&self, version: u32, disambiguator: u32) -> SSAVar {
        SSAVar::new(&self.name, version, self.size).with_rename_disambiguator(disambiguator)
    }
}

pub type DefinitionSitesByIdentity = BTreeMap<RenameIdentity, BTreeSet<u64>>;
pub type CanonicalStorageByIdentity = BTreeMap<RenameIdentity, CanonicalStorageId>;
pub type DefinitionCollection = (DefinitionSitesByIdentity, CanonicalStorageByIdentity);

/// Information about phi nodes to be placed in the CFG.
#[derive(Debug, Clone, Default)]
pub struct PhiPlacement {
    /// Phi nodes to place at each block, keyed internally by exact rename identity.
    pub phis: HashMap<u64, Vec<PhiInfo>>,
}

/// Information about a single phi node.
#[derive(Debug, Clone)]
pub struct PhiInfo {
    /// Typed rename identity. The name inside it is retained for presentation.
    pub identity: RenameIdentity,
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
    /// * `defs` - Map from exact rename identity to definition blocks
    pub fn compute(cfg: &CFG, domtree: &DomTree, defs: &DefinitionSitesByIdentity) -> Self {
        Self::compute_with_storage(cfg, domtree, defs, &BTreeMap::new())
    }

    pub fn compute_with_storage(
        cfg: &CFG,
        domtree: &DomTree,
        defs: &DefinitionSitesByIdentity,
        storage_by_identity: &CanonicalStorageByIdentity,
    ) -> Self {
        Self::compute_with_storage_and_control(
            cfg,
            domtree,
            defs,
            storage_by_identity,
            &UncheckedSsaWorkControl,
        )
        .expect("unchecked phi placement cannot stop")
    }

    /// Compute phi placement while polling dominance-frontier worklists.
    pub fn compute_with_storage_and_control<C: SsaWorkControl + ?Sized>(
        cfg: &CFG,
        domtree: &DomTree,
        defs: &DefinitionSitesByIdentity,
        storage_by_identity: &CanonicalStorageByIdentity,
        control: &C,
    ) -> Result<Self, SsaExecutionStopReason> {
        control.poll()?;
        let mut placement = Self::new();

        for (identity, def_blocks) in defs {
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
                    let storage = storage_by_identity.get(identity).copied();
                    let phi_info = PhiInfo {
                        identity: identity.clone(),
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
                lhs.identity
                    .cmp(&rhs.identity)
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
/// Returns the exact rename identities defined in this block.
pub fn collect_defs_from_block(block: &BasicBlock) -> BTreeSet<RenameIdentity> {
    let mut defs = BTreeSet::new();

    for op in &block.ops {
        if let Some(dst) = get_op_output_varnode(op) {
            defs.insert(RenameIdentity::from_varnode(dst, None));
        }
    }

    defs
}

/// Collect variable definitions from a CFG.
///
/// Returns:
/// - `defs`: Map from exact rename identity to definition blocks
pub fn collect_defs_from_cfg(cfg: &CFG) -> DefinitionSitesByIdentity {
    collect_defs_from_cfg_with_names(cfg, None)
}

/// Collect variable definitions from a CFG with optional register names.
pub fn collect_defs_from_cfg_with_names(
    cfg: &CFG,
    reg_names: Option<&RegisterNameMap>,
) -> DefinitionSitesByIdentity {
    collect_defs_from_cfg_with_names_and_storage(cfg, reg_names).0
}

/// Collect definitions while retaining lifted storage per exact typed identity.
/// Widths and storage slices sharing one spelling remain distinct.
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
    let mut defs = DefinitionSitesByIdentity::new();
    let mut storage_by_identity = CanonicalStorageByIdentity::new();

    for addr in cfg.block_addrs() {
        control.poll()?;
        let Some(block) = cfg.get_block(addr) else {
            continue;
        };
        for op in &block.ops {
            control.poll()?;
            for varnode in op.inputs() {
                if !matches!(varnode.space, r2il::SpaceId::Const) {
                    let identity = RenameIdentity::from_varnode(varnode, reg_names);
                    defs.entry(identity.clone()).or_default();
                    storage_by_identity.insert(identity.clone(), identity.storage);
                }
            }
            if let Some(varnode) = get_op_output_varnode(op) {
                let identity = RenameIdentity::from_varnode(varnode, reg_names);
                defs.entry(identity.clone()).or_default().insert(block.addr);
                storage_by_identity.insert(identity.clone(), identity.storage);
            }
        }
    }

    control.poll()?;
    Ok((defs, storage_by_identity))
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
        let defs = collect_defs_from_cfg(&cfg);

        let placement = PhiPlacement::compute(&cfg, &domtree, &defs);

        // Should have a phi at block D (0x100c) for reg:0
        assert!(placement.has_phis(0x100c));
        let phis = placement.get_phis(0x100c);
        assert_eq!(phis.len(), 1);
        let identity = RenameIdentity::from_varnode(&make_reg(0, 8), None);
        assert_eq!(phis[0].identity, identity);
        assert_eq!(phis[0].predecessors.len(), 2);

        let storage_by_identity = BTreeMap::from([(
            identity,
            CanonicalStorageId {
                space: crate::CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            },
        )]);
        let placement =
            PhiPlacement::compute_with_storage(&cfg, &domtree, &defs, &storage_by_identity);
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
    fn storage_collection_keeps_widths_and_same_named_storages_distinct() {
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
        let (defs, storage_by_identity) = collect_defs_from_cfg_with_names_and_storage(&cfg, None);
        assert!(defs.contains_key(&RenameIdentity::from_varnode(
            &Varnode::unique(0x200, 4),
            None
        )));
        assert!(defs.contains_key(&RenameIdentity::from_varnode(
            &Varnode::unique(0x200, 8),
            None
        )));
        assert_eq!(storage_by_identity.len(), 2);

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
        let (_, storage_by_identity) =
            collect_defs_from_cfg_with_names_and_storage(&cfg, Some(&register_names));
        assert_eq!(storage_by_identity.len(), 2);
        assert!(
            storage_by_identity
                .keys()
                .all(|identity| identity.name == "alias")
        );
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
        let defs = collect_defs_from_cfg(&cfg);

        let placement = PhiPlacement::compute(&cfg, &domtree, &defs);

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
        let defs = collect_defs_from_cfg(&cfg);
        let reg0 = RenameIdentity::from_varnode(&make_reg(0, 8), None);
        let reg8 = RenameIdentity::from_varnode(&make_reg(8, 8), None);

        // reg:0 defined in both blocks
        assert!(defs.contains_key(&reg0));
        assert_eq!(defs[&reg0].len(), 2);

        // reg:8 defined only in first block
        assert!(defs.contains_key(&reg8));
        assert_eq!(defs[&reg8].len(), 1);
    }
}
