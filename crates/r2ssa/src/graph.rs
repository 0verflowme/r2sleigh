use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::function::SSAFunction;
use crate::op::SSAOp;
use crate::var::SSAVar;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InstId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ValueId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct UseSite {
    pub inst: InstId,
    pub input_idx: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GraphValue {
    pub id: ValueId,
    pub var: SSAVar,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
                .filter_map(|addr| block_by_addr.get(&addr).copied())
                .collect();
            block.successors = function
                .successors(block.addr)
                .into_iter()
                .filter_map(|addr| block_by_addr.get(&addr).copied())
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
            values.push(GraphValue {
                id,
                var: var.clone(),
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
                    .filter_map(|(addr, _)| block_by_addr.get(addr).copied())
                    .collect();
                insts.push(GraphInst {
                    id: inst_id,
                    block: block_id,
                    ordinal: phi_idx,
                    inputs,
                    output: Some(output),
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
