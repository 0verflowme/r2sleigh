//! Phi-node placement for SSA construction.
//!
//! This module implements the phi-node placement algorithm using the
//! iterated dominance frontier, as described by Cytron et al.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::cfg::CFG;
use crate::control::{SsaExecutionStopReason, SsaWorkControl};
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
mod tests {}
