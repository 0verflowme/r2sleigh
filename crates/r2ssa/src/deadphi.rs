//! Merges that nothing observes.
//!
//! A lifted body merges every storage live across a join, so an exit block ends
//! up holding a phi for each condition-code bit and each Sleigh temporary that
//! happened to be written on either side. A twelve-instruction function produces
//! forty-nine of them, twenty-four at one loop header, and every rule that has to
//! decide what a loop carries, what deserves a name, or what the output owes has
//! to look at all of them and reject the ones that mean nothing.
//!
//! Removing them was not previously safe to attempt, because "nothing reads this"
//! was not a question the SSA could answer: the value a function returns has no
//! reader in its own body either. With [`crate::liveout`] saying what leaves
//! through the calling convention, the question is answerable, and the ordinary
//! answer applies -- a value is observed if something with an effect depends on
//! it, and a merge no observation depends on is not part of the program.
//!
//! This reports what it found rather than editing the function, so a caller can
//! act on it, count it, or disagree with it.

use std::collections::{BTreeSet, VecDeque};

use crate::function::SSAFunction;
use crate::graph::{SsaGraph, ValueId};
use crate::liveout::FunctionLiveOut;
use crate::op::SSAOp;

/// Whether an operation is observed for reasons beyond the value it produces.
///
/// Stores change memory, transfers change where execution goes, and calls do
/// whatever the callee does. Everything else is observed only through its result.
fn has_effect(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Store { .. }
            | SSAOp::StoreConditional { .. }
            | SSAOp::StoreGuarded { .. }
            | SSAOp::AtomicCAS { .. }
            | SSAOp::Fence { .. }
            | SSAOp::Branch { .. }
            | SSAOp::BranchInd { .. }
            | SSAOp::CBranch { .. }
            | SSAOp::Return { .. }
            | SSAOp::Call { .. }
            | SSAOp::CallInd { .. }
            | SSAOp::CallDefine { .. }
            | SSAOp::CallOther { .. }
            | SSAOp::Unimplemented { .. }
    )
}

/// Which merges no observation depends on.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DeadPhis {
    values: BTreeSet<ValueId>,
}

impl DeadPhis {
    /// Find the merges nothing observes, following what observation depends on.
    pub fn find(func: &SSAFunction, graph: &SsaGraph, live_out: &FunctionLiveOut) -> Self {
        let mut observed = BTreeSet::new();
        let mut pending = VecDeque::new();
        let mut observe = |value: ValueId,
                           observed: &mut BTreeSet<ValueId>,
                           pending: &mut VecDeque<ValueId>| {
            if observed.insert(value) {
                pending.push_back(value);
            }
        };

        for value in live_out.iter() {
            observe(value, &mut observed, &mut pending);
        }
        for block in func.blocks() {
            for op in &block.ops {
                if !has_effect(op) {
                    continue;
                }
                op.for_each_source(|input| {
                    if let Some(value) = graph.value_id_for_var(input) {
                        observe(value, &mut observed, &mut pending);
                    }
                });
            }
        }

        // Whatever an observation depends on is observed, transitively. The walk
        // is over the graph's own instruction inputs, so it visits each edge once.
        while let Some(value) = pending.pop_front() {
            let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
                continue;
            };
            for input in &inst.inputs {
                observe(*input, &mut observed, &mut pending);
            }
        }

        let mut dead = Self::default();
        for block in func.blocks() {
            for phi in &block.phis {
                let Some(value) = graph.value_id_for_var(&phi.dst) else {
                    continue;
                };
                if !observed.contains(&value) {
                    dead.values.insert(value);
                }
            }
        }
        dead
    }

    pub fn contains(&self, value: ValueId) -> bool {
        self.values.contains(&value)
    }

    pub fn iter(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.values.iter().copied()
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::AbiProfile;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Register, offset, size)
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RCX", 8, 8));
        arch.add_register(RegisterDef::new("RDX", 16, 8));
        arch.add_register(RegisterDef::new("ZF", 0x206, 1));
        arch.add_register(RegisterDef::new("RIP", 0x288, 8));
        arch
    }

    /// A diamond that merges the return register and a condition code, and returns.
    fn merging_function() -> SSAFunction {
        let entry = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntEqual {
                    dst: reg(0x206, 1),
                    a: reg(8, 8),
                    b: Varnode::constant(0, 8),
                },
                R2ILOp::CBranch {
                    cond: reg(0x206, 1),
                    target: Varnode::constant(0x1008, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let left = R2ILBlock {
            addr: 0x1004,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(1, 8),
                },
                R2ILOp::IntEqual {
                    dst: reg(0x206, 1),
                    a: reg(16, 8),
                    b: Varnode::constant(0, 8),
                },
                R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let right = R2ILBlock {
            addr: 0x1008,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(2, 8),
                },
                R2ILOp::IntEqual {
                    dst: reg(0x206, 1),
                    a: reg(16, 8),
                    b: Varnode::constant(1, 8),
                },
                R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let exit = R2ILBlock {
            addr: 0x100c,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: reg(0x288, 8),
            }],
            ..R2ILBlock::default()
        };
        SSAFunction::from_blocks_with_arch(&[entry, left, right, exit], Some(&arch()))
            .expect("ssa")
    }

    #[test]
    fn a_flag_merged_at_a_join_and_never_tested_again_is_not_part_of_the_program() {
        let func = merging_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &AbiProfile::from_arch(Some(&arch())));

        let dead = DeadPhis::find(&func, &graph, &live);

        let exit = func.get_block(0x100c).expect("exit block");
        let zf = exit
            .phis
            .iter()
            .find(|phi| phi.dst.name.eq_ignore_ascii_case("zf"))
            .and_then(|phi| graph.value_id_for_var(&phi.dst));
        assert!(
            zf.is_some_and(|value| dead.contains(value)),
            "a condition code merged and never tested is dead"
        );
    }

    #[test]
    fn the_merge_holding_the_returned_value_survives() {
        let func = merging_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &AbiProfile::from_arch(Some(&arch())));

        let dead = DeadPhis::find(&func, &graph, &live);

        let exit = func.get_block(0x100c).expect("exit block");
        let rax = exit
            .phis
            .iter()
            .find(|phi| phi.dst.name.eq_ignore_ascii_case("rax"))
            .and_then(|phi| graph.value_id_for_var(&phi.dst))
            .expect("the return register is merged at the exit");
        assert!(
            !dead.contains(rax),
            "the value the caller reads is observed even with no use site in this body"
        );
        assert!(graph.use_sites(rax).is_empty(), "and it has no use site");
    }

    #[test]
    fn a_flag_a_branch_still_tests_survives() {
        let func = merging_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &AbiProfile::from_arch(Some(&arch())));

        let dead = DeadPhis::find(&func, &graph, &live);

        // The entry block's condition is tested by its own CBranch, so nothing
        // about merging flags elsewhere may reach back and call it unobserved.
        let entry = func.get_block(0x1000).expect("entry block");
        let tested = entry
            .ops
            .iter()
            .find_map(|op| op.dst())
            .and_then(|dst| graph.value_id_for_var(dst))
            .expect("a defined condition");
        assert!(!dead.contains(tested));
    }
}
