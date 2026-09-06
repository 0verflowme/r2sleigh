use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::function::SSAFunction;
use crate::op::SSAOp;
use crate::var::SSAVar;
use crate::{CanonicalStorageId, CanonicalStorageSpace};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InstId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ValueId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct UseSite {
    pub inst: InstId,
    pub input_idx: usize,
}

#[cfg(test)]
mod tests {
    use super::{InstId, InstPayload, SsaGraph, UseSite};
    use crate::function::SSAFunction;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Register, offset, size)
    }

    /// Two registers written on both arms of a branch, merged.
    fn two_phi_merge() -> SSAFunction {
        let mut arch = ArchSpec::new("two-phi-merge");
        arch.add_register(RegisterDef::new("first", 0, 8));
        arch.add_register(RegisterDef::new("second", 8, 8));
        arch.add_register(RegisterDef::new("cond", 32, 1));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: reg(32, 1),
        });
        let arm = |addr: u64, first: u64, second: u64| {
            let mut block = R2ILBlock::new(addr, 4);
            block.push(R2ILOp::Copy {
                dst: reg(0, 8),
                src: Varnode::constant(first, 8),
            });
            block.push(R2ILOp::Copy {
                dst: reg(8, 8),
                src: Varnode::constant(second, 8),
            });
            block.push(R2ILOp::Branch {
                target: Varnode::constant(0x100c, 8),
            });
            block
        };
        let left = arm(0x1004, 0, 1);
        let right = arm(0x1008, 2, 3);
        let mut merge = R2ILBlock::new(0x100c, 4);
        merge.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[entry, left, right, merge], Some(&arch))
            .expect("two phi merge SSA")
    }

    /// A merge's storage belongs to the merge, not to its position in the block.
    ///
    /// This arrived with copy propagation, which asserted it by collapsing one
    /// of two phis and checking the survivor. Removing a phi is what exercises
    /// the property and the pass was only one way to do it, so the removal is
    /// done directly here and the pass is gone.
    #[test]
    fn phi_storage_identity_survives_removing_preceding_phi() {
        let mut func = two_phi_merge();
        let merge = func.get_block(0x100c).expect("merge block");
        assert_eq!(merge.phis.len(), 2, "the fixture must merge two registers");
        let retained_storage = merge.phis[1]
            .canonical_storage
            .expect("second merge storage");
        let retained_dst = merge.phis[1].dst.clone();
        assert_ne!(retained_storage, merge.phis[0].canonical_storage.unwrap());

        let merge = func.get_block_mut(0x100c).expect("merge block");
        merge.phis.remove(0);

        let merge = func.get_block(0x100c).expect("merge block");
        assert_eq!(merge.phis.len(), 1);
        assert_eq!(merge.phis[0].dst, retained_dst);
        assert_eq!(merge.phis[0].canonical_storage, Some(retained_storage));

        let graph = SsaGraph::from_function(&func);
        let graph_phi = graph
            .insts
            .iter()
            .find(|inst| matches!(inst.payload, InstPayload::Phi { .. }))
            .expect("retained graph phi");
        assert_eq!(
            graph_phi.canonical_storage,
            Some(retained_storage),
            "the graph must carry the surviving merge's own storage"
        );
    }

    #[test]
    fn use_sites_have_stable_instruction_then_input_order() {
        let mut sites = [
            UseSite {
                inst: InstId(3),
                input_idx: 1,
            },
            UseSite {
                inst: InstId(2),
                input_idx: 4,
            },
            UseSite {
                inst: InstId(3),
                input_idx: 0,
            },
        ];

        sites.sort();

        assert_eq!(
            sites,
            [
                UseSite {
                    inst: InstId(2),
                    input_idx: 4,
                },
                UseSite {
                    inst: InstId(3),
                    input_idx: 0,
                },
                UseSite {
                    inst: InstId(3),
                    input_idx: 1,
                },
            ]
        );
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GraphValue {
    pub id: ValueId,
    pub var: SSAVar,
    /// Name-independent storage retained from the lifted varnode.
    #[serde(default)]
    pub canonical_storage: Option<CanonicalStorageId>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[expect(
    clippy::large_enum_variant,
    reason = "graph instructions keep canonical SSA operations inline to avoid one heap allocation per instruction"
)]
pub enum InstPayload {
    Phi { predecessors: Vec<BlockId> },
    Op(SSAOp),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GraphInst {
    pub id: InstId,
    pub block: BlockId,
    pub ordinal: usize,
    pub inputs: Vec<ValueId>,
    pub output: Option<ValueId>,
    /// Name-independent lifted storage identity for phi nodes and for ordinary
    /// definitions when the graph is built with a source machine context.
    pub canonical_storage: Option<CanonicalStorageId>,
    pub payload: InstPayload,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GraphBlock {
    pub id: BlockId,
    pub addr: u64,
    pub size: u32,
    pub predecessors: Vec<BlockId>,
    pub successors: Vec<BlockId>,
    pub insts: Vec<InstId>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SsaGraph {
    pub entry: BlockId,
    pub block_order: Vec<BlockId>,
    pub blocks: Vec<GraphBlock>,
    pub insts: Vec<GraphInst>,
    pub values: Vec<GraphValue>,
    pub def_of: Vec<Option<InstId>>,
    pub uses_of: Vec<Vec<UseSite>>,
    pub block_by_addr: BTreeMap<u64, BlockId>,
    pub value_by_var: BTreeMap<SSAVar, ValueId>,
    pub op_inst_by_site: BTreeMap<(u64, usize), InstId>,
    pub op_site_by_inst: BTreeMap<InstId, (u64, usize)>,
}

impl SsaGraph {
    pub fn from_function(function: &SSAFunction) -> Self {
        Self::try_from_function(function).expect("SSA graph construction requires valid SSA")
    }

    /// Build a graph only after sealing the complete function-level SSA contract.
    #[expect(
        clippy::result_large_err,
        reason = "graph construction preserves the exact typed SSA validation failure at this artifact boundary"
    )]
    pub fn try_from_function(function: &SSAFunction) -> Result<Self, crate::SsaIntegrityError> {
        crate::validate_ssa_function(function)?;
        Ok(Self::from_function_with_storage(function))
    }

    pub(crate) fn from_function_with_storage(function: &SSAFunction) -> Self {
        let mut block_by_addr = BTreeMap::new();
        let mut block_order = Vec::new();
        let mut blocks = Vec::new();

        for (idx, &addr) in function.block_addrs().iter().enumerate() {
            let id = BlockId(idx as u32);
            block_by_addr.insert(addr, id);
            block_order.push(id);
            let size = function
                .get_block(addr)
                .map(|block| block.size)
                .unwrap_or_default();
            blocks.push(GraphBlock {
                id,
                addr,
                size,
                predecessors: Vec::new(),
                successors: Vec::new(),
                insts: Vec::new(),
            });
        }

        for block in &mut blocks {
            block.predecessors = function
                .predecessors(block.addr)
                .into_iter()
                .map(|addr| {
                    block_by_addr
                        .get(&addr)
                        .copied()
                        .expect("validated predecessor must name an SSA block")
                })
                .collect();
            block.successors = function
                .successors(block.addr)
                .into_iter()
                .map(|addr| {
                    block_by_addr
                        .get(&addr)
                        .copied()
                        .expect("validated successor must name an SSA block")
                })
                .collect();
        }

        let mut values = Vec::new();
        let mut value_by_var = BTreeMap::new();
        let mut def_of = Vec::new();
        let mut uses_of = Vec::new();
        let mut insts = Vec::new();
        let mut op_inst_by_site = BTreeMap::new();
        let mut op_site_by_inst = BTreeMap::new();

        let intern_value = |var: &SSAVar,
                            values: &mut Vec<GraphValue>,
                            value_by_var: &mut BTreeMap<SSAVar, ValueId>,
                            def_of: &mut Vec<Option<InstId>>,
                            uses_of: &mut Vec<Vec<UseSite>>| {
            if let Some(id) = value_by_var.get(var).copied() {
                return id;
            }
            let id = ValueId(values.len() as u32);
            let canonical_storage = function.canonical_storage_for_var(var).or_else(|| {
                var.constant_bits().map(|bits| CanonicalStorageId {
                    space: CanonicalStorageSpace::Constant,
                    offset: bits,
                    size: var.size,
                })
            });
            values.push(GraphValue {
                id,
                var: var.clone(),
                canonical_storage,
            });
            value_by_var.insert(var.clone(), id);
            def_of.push(None);
            uses_of.push(Vec::new());
            id
        };

        for block in function.blocks() {
            let block_id = block_by_addr[&block.addr];

            for (phi_idx, phi) in block.phis.iter().enumerate() {
                let inputs = phi
                    .sources
                    .iter()
                    .map(|(_, value)| {
                        intern_value(
                            value,
                            &mut values,
                            &mut value_by_var,
                            &mut def_of,
                            &mut uses_of,
                        )
                    })
                    .collect::<Vec<_>>();
                let output = intern_value(
                    &phi.dst,
                    &mut values,
                    &mut value_by_var,
                    &mut def_of,
                    &mut uses_of,
                );
                let inst_id = InstId(insts.len() as u32);
                for (input_idx, input) in inputs.iter().copied().enumerate() {
                    uses_of[input.0 as usize].push(UseSite {
                        inst: inst_id,
                        input_idx,
                    });
                }
                def_of[output.0 as usize] = Some(inst_id);
                let predecessors = phi
                    .sources
                    .iter()
                    .map(|(addr, _)| {
                        block_by_addr
                            .get(addr)
                            .copied()
                            .expect("validated phi predecessor must name an SSA block")
                    })
                    .collect();
                insts.push(GraphInst {
                    id: inst_id,
                    block: block_id,
                    ordinal: phi_idx,
                    inputs,
                    output: Some(output),
                    canonical_storage: phi.canonical_storage,
                    payload: InstPayload::Phi { predecessors },
                });
                blocks[block_id.0 as usize].insts.push(inst_id);
            }

            for (op_idx, op) in block.ops.iter().enumerate() {
                let inputs = op
                    .sources()
                    .into_iter()
                    .map(|value| {
                        intern_value(
                            value,
                            &mut values,
                            &mut value_by_var,
                            &mut def_of,
                            &mut uses_of,
                        )
                    })
                    .collect::<Vec<_>>();
                let output = op.dst().map(|dst| {
                    intern_value(
                        dst,
                        &mut values,
                        &mut value_by_var,
                        &mut def_of,
                        &mut uses_of,
                    )
                });
                let inst_id = InstId(insts.len() as u32);
                for (input_idx, input) in inputs.iter().copied().enumerate() {
                    uses_of[input.0 as usize].push(UseSite {
                        inst: inst_id,
                        input_idx,
                    });
                }
                if let Some(output) = output {
                    def_of[output.0 as usize] = Some(inst_id);
                }
                insts.push(GraphInst {
                    id: inst_id,
                    block: block_id,
                    ordinal: block.phis.len() + op_idx,
                    inputs,
                    output,
                    canonical_storage: output
                        .and_then(|value| values.get(value.0 as usize))
                        .and_then(|value| value.canonical_storage),
                    payload: InstPayload::Op(op.clone()),
                });
                blocks[block_id.0 as usize].insts.push(inst_id);
                op_inst_by_site.insert((block.addr, op_idx), inst_id);
                op_site_by_inst.insert(inst_id, (block.addr, op_idx));
            }
        }

        let entry = block_by_addr
            .get(&function.entry)
            .copied()
            .unwrap_or(BlockId(0));

        Self {
            entry,
            block_order,
            blocks,
            insts,
            values,
            def_of,
            uses_of,
            block_by_addr,
            value_by_var,
            op_inst_by_site,
            op_site_by_inst,
        }
    }

    pub fn block_id_for_addr(&self, addr: u64) -> Option<BlockId> {
        self.block_by_addr.get(&addr).copied()
    }

    /// Return storage provenance already retained at the lift/SSA boundary.
    /// This lookup never parses or resolves the variable's display name.
    pub fn canonical_storage_for_var(&self, var: &SSAVar) -> Option<CanonicalStorageId> {
        self.value_id_for_var(var)
            .and_then(|value| self.value(value))
            .and_then(|value| value.canonical_storage)
    }

    pub fn value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.value_by_var.get(var).copied()
    }

    pub fn inst_id_for_op_site(&self, block_addr: u64, op_idx: usize) -> Option<InstId> {
        self.op_inst_by_site.get(&(block_addr, op_idx)).copied()
    }

    pub fn op_site_for_inst(&self, id: InstId) -> Option<(u64, usize)> {
        self.op_site_by_inst.get(&id).copied()
    }

    pub fn block(&self, id: BlockId) -> Option<&GraphBlock> {
        self.blocks.get(id.0 as usize)
    }

    pub fn inst(&self, id: InstId) -> Option<&GraphInst> {
        self.insts.get(id.0 as usize)
    }

    pub fn value(&self, id: ValueId) -> Option<&GraphValue> {
        self.values.get(id.0 as usize)
    }

    /// Materialize an exact source-declared value at function entry.
    ///
    /// Calls read their register arguments implicitly. A parameter handed
    /// straight to a call therefore has no operation for graph construction to
    /// discover, even though the source function interface proves that the
    /// value exists. This adds that boundary value without inventing an
    /// instruction or a graph use; the exact call boundary supplies the read.
    pub(crate) fn ensure_entry_value(
        &mut self,
        var: SSAVar,
        storage: CanonicalStorageId,
    ) -> Option<ValueId> {
        if var.version != 0
            || var.size != storage.size
            || storage.space != CanonicalStorageSpace::Register
            || storage.size == 0
        {
            return None;
        }
        if let Some(id) = self.value_by_var.get(&var).copied() {
            let value = self.value(id)?;
            return (self.def_inst(id).is_none() && value.canonical_storage == Some(storage))
                .then_some(id);
        }
        let id = ValueId(u32::try_from(self.values.len()).ok()?);
        self.values.push(GraphValue {
            id,
            var: var.clone(),
            canonical_storage: Some(storage),
        });
        self.value_by_var.insert(var, id);
        self.def_of.push(None);
        self.uses_of.push(Vec::new());
        Some(id)
    }

    pub fn def_inst(&self, id: ValueId) -> Option<InstId> {
        self.def_of.get(id.0 as usize).copied().flatten()
    }

    pub fn use_sites(&self, id: ValueId) -> &[UseSite] {
        self.uses_of
            .get(id.0 as usize)
            .map(|sites| sites.as_slice())
            .unwrap_or(&[])
    }
}
