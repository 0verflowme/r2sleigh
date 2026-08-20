//! Facts about a function that follow from its code, and nothing weaker.
//!
//! radare2's analysis pass writes what it discovers into its own stores, and a
//! consumer reading those stores cannot tell a proof from a guess. So only
//! proofs go in. Each fact here is derived from the lifted semantics and the
//! dominator tree, fails closed when the derivation does not complete, and
//! carries the reason it holds so a reader can check it.

use crate::function::{SSABlock, SSAFunction};
use crate::cfg::{BlockTerminator, CFG};

use crate::indirect::{
    PointerTable, ResolvedIndirectCall, definitions, resolve_constant, resolve_indirect_calls,
};
use crate::SSAOp;
use std::collections::HashMap;

/// A block no execution can enter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnreachableBlock {
    pub addr: u64,
    /// Why it cannot be entered, in the terms the proof used.
    pub reason: String,
}

/// Everything a function proves about itself.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvenFacts {
    pub indirect_calls: Vec<ResolvedIndirectCall>,
    pub unreachable_blocks: Vec<UnreachableBlock>,
}

impl ProvenFacts {
    pub fn is_empty(&self) -> bool {
        self.indirect_calls.is_empty() && self.unreachable_blocks.is_empty()
    }
}

/// The condition a branch tests, when that condition is already decided.
///
/// A conditional branch on a value the semantics pinned to a constant is not a
/// branch at all: one edge is taken on every execution and the other on none.
/// Deciding it is the same question the target resolver asks of an address, so
/// it is the same evaluator -- hardware builds a condition out of flags and
/// copies, and only following all of that reaches the comparison underneath.
fn decided_condition(
    defs: &HashMap<String, (&SSAOp, u64)>,
    blocks: &[SSABlock],
    block_addr: u64,
) -> Option<bool> {
    let block = blocks.iter().find(|block| block.addr == block_addr)?;
    let SSAOp::CBranch { cond, .. } = block.ops.last()? else {
        return None;
    };
    resolve_constant(defs, cond, 0).map(|value| value != 0)
}

/// Blocks that no execution reaches.
///
/// Two things put a block out of reach, and both are checked against the graph
/// rather than assumed: nothing branches to it at all, or the only branches to
/// it are edges a decided condition never takes. Anything less certain -- a
/// block reached only through a path we failed to lift, say -- is left alone,
/// because marking live code dead is the worst error this can make.
pub fn unreachable_blocks(blocks: &[SSABlock], cfg: &CFG) -> Vec<UnreachableBlock> {
    let Some(entry) = cfg.entry_block().map(|block| block.addr) else {
        return Vec::new();
    };
    // Walk forward from the entry, refusing to follow an edge a decided
    // condition proves is never taken. What the walk misses is unreachable.
    let defs = definitions(blocks);
    let mut reached = std::collections::HashSet::new();
    let mut queue = vec![entry];
    reached.insert(entry);
    while let Some(addr) = queue.pop() {
        let decided = decided_condition(&defs, blocks, addr);
        let terminator = cfg.get_block(addr).map(|block| block.terminator.clone());
        for successor in cfg.successors(addr) {
            if let (Some(taken), Some(BlockTerminator::ConditionalBranch { true_target, false_target })) =
                (decided, terminator.as_ref())
            {
                let never = if taken { *false_target } else { *true_target };
                // Only skip the dead edge when the two edges are distinct: a
                // branch to its own fallthrough reaches the block either way.
                if successor == never && true_target != false_target {
                    continue;
                }
            }
            if reached.insert(successor) {
                queue.push(successor);
            }
        }
    }
    let mut unreachable: Vec<_> = cfg
        .block_addrs()
        .filter(|addr| !reached.contains(addr))
        .map(|addr| UnreachableBlock {
            addr,
            reason: if cfg.predecessors(addr).is_empty() {
                "no branch reaches this block".to_string()
            } else {
                "every branch reaching this block tests a condition that decides against it"
                    .to_string()
            },
        })
        .collect();
    unreachable.sort_by_key(|block| block.addr);
    unreachable
}

/// Gather every fact the function proves.
pub fn prove<T: PointerTable>(function: &SSAFunction, tables: &[T]) -> ProvenFacts {
    let blocks = function.blocks().cloned().collect::<Vec<_>>();
    ProvenFacts {
        indirect_calls: resolve_indirect_calls(blocks.as_slice(), function.cfg(), function.domtree(), tables),
        unreachable_blocks: unreachable_blocks(blocks.as_slice(), function.cfg()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SSAVar;
    use crate::cfg::BasicBlock;

    fn var(name: &str) -> SSAVar {
        SSAVar::new(name, 1, 8)
    }

    /// `if (cond) goto 0x20; else fall through to 0x10`.
    ///
    /// `cond` is whatever `condition` defines, so a test can decide it or leave
    /// it open and get the same shape either way.
    fn branching(condition: Option<u64>) -> (Vec<SSABlock>, CFG) {
        let cond = var("cond");
        let mut ops = Vec::new();
        if let Some(value) = condition {
            ops.push(SSAOp::Copy {
                dst: cond.clone(),
                src: SSAVar::constant(value, 8),
            });
        }
        ops.push(SSAOp::CBranch {
            target: SSAVar::constant(0x20, 8),
            cond: cond.clone(),
        });
        let blocks = vec![
            SSABlock { addr: 0, phis: Vec::new(), size: 0x10, ops },
            SSABlock {
                addr: 0x10,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
            SSABlock {
                addr: 0x20,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
        ];
        let mut cfg = CFG::new(0);
        for block in &blocks {
            let mut basic = BasicBlock::new(block.addr);
            basic.size = block.size;
            basic.terminator = if block.addr == 0 {
                BlockTerminator::ConditionalBranch { true_target: 0x20, false_target: 0x10 }
            } else {
                BlockTerminator::Return
            };
            cfg.add_block(basic);
        }
        cfg.rebuild_edges();
        (blocks, cfg)
    }

    #[test]
    fn a_condition_that_is_always_true_leaves_the_other_arm_unreachable() {
        let (blocks, cfg) = branching(Some(1));
        let dead = unreachable_blocks(&blocks, &cfg);
        assert_eq!(dead.len(), 1);
        assert_eq!(dead[0].addr, 0x10);
    }

    #[test]
    fn a_condition_that_is_always_false_leaves_the_taken_arm_unreachable() {
        let (blocks, cfg) = branching(Some(0));
        let dead = unreachable_blocks(&blocks, &cfg);
        assert_eq!(dead.len(), 1);
        assert_eq!(dead[0].addr, 0x20);
    }

    #[test]
    fn an_undecided_condition_leaves_both_arms_alive() {
        // Nothing is proven about the condition, so nothing is proven about
        // either arm. A guess here would delete code that runs.
        let (blocks, cfg) = branching(None);
        assert!(unreachable_blocks(&blocks, &cfg).is_empty());
    }

    #[test]
    fn a_condition_decided_through_the_flags_still_decides_the_branch() {
        // What hardware emits: the comparison lands in a flag, the flag is
        // copied, and the branch tests its negation. `!(3 < 1)` is true on
        // every execution, so the fallthrough is never taken.
        let flag = var("cy");
        let carried = var("cy_copy");
        let negated = var("tmp:f00");
        let blocks = vec![
            SSABlock {
                addr: 0,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![
                    SSAOp::IntLess {
                        dst: flag.clone(),
                        a: SSAVar::constant(3, 4),
                        b: SSAVar::constant(1, 4),
                    },
                    SSAOp::Copy { dst: carried.clone(), src: flag.clone() },
                    SSAOp::BoolNot { dst: negated.clone(), src: carried.clone() },
                    SSAOp::CBranch {
                        target: SSAVar::constant(0x20, 8),
                        cond: negated.clone(),
                    },
                ],
            },
            SSABlock {
                addr: 0x10,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
            SSABlock {
                addr: 0x20,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
        ];
        let mut cfg = CFG::new(0);
        for block in &blocks {
            let mut basic = BasicBlock::new(block.addr);
            basic.size = block.size;
            basic.terminator = if block.addr == 0 {
                BlockTerminator::ConditionalBranch { true_target: 0x20, false_target: 0x10 }
            } else {
                BlockTerminator::Return
            };
            cfg.add_block(basic);
        }
        cfg.rebuild_edges();
        let dead = unreachable_blocks(&blocks, &cfg);
        assert_eq!(dead.len(), 1);
        assert_eq!(dead[0].addr, 0x10);
    }

    #[test]
    fn a_block_nothing_branches_to_is_unreachable() {
        let (mut blocks, mut cfg) = branching(None);
        blocks.push(SSABlock {
            addr: 0x30,
            phis: Vec::new(),
            size: 0x10,
            ops: vec![SSAOp::Return { target: var("ret") }],
        });
        let mut orphan = BasicBlock::new(0x30);
        orphan.size = 0x10;
        orphan.terminator = BlockTerminator::Return;
        cfg.add_block(orphan);
        cfg.rebuild_edges();
        let dead = unreachable_blocks(&blocks, &cfg);
        assert_eq!(dead.len(), 1);
        assert_eq!(dead[0].addr, 0x30);
        assert_eq!(dead[0].reason, "no branch reaches this block");
    }

    #[test]
    fn a_decided_branch_does_not_strand_a_block_another_path_reaches() {
        // 0x20 is both the taken arm of a branch that never takes it and the
        // fallthrough of 0x10, so it still runs.
        let (blocks, mut cfg) = branching(Some(0));
        cfg.set_terminator(0x10, BlockTerminator::Branch { target: 0x20 });
        cfg.rebuild_edges();
        assert!(unreachable_blocks(&blocks, &cfg).is_empty());
    }
}
