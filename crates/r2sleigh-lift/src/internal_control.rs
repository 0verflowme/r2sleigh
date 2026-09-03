//! Normalization for P-code-relative control flow inside one instruction.
//!
//! Ghidra usually encodes instruction-local branches with a constant-space
//! target whose signed offset is relative to the branch operation's index.
//! Some specifications instead resolve a skip to the RAM address of the next
//! instruction. Those edges are not machine CFG edges. Forward branches over
//! speculatable value operations are converted to explicit value selects;
//! unsupported local control becomes `Unimplemented` so downstream consumers
//! refuse instead of inventing a CFG.

use std::collections::{BTreeMap, HashMap, HashSet};

use r2il::{OpMetadata, R2ILBlock, R2ILOp, SpaceId, Varnode};

pub(crate) fn normalize_instruction_local_control(block: &mut R2ILBlock) {
    loop {
        let Some((branch_index, branch, target_index)) = block
            .ops
            .iter()
            .enumerate()
            .find_map(|(index, op)| local_branch(block, index, op))
        else {
            break;
        };

        if target_index <= branch_index || target_index > block.ops.len() {
            block.ops[branch_index] = R2ILOp::Unimplemented;
            continue;
        }

        match branch {
            LocalBranch::Unconditional(_) => {
                rewrite_unconditional_forward_branch(block, branch_index, target_index);
            }
            LocalBranch::Conditional { cond, .. } => {
                if block.ops[branch_index + 1..target_index]
                    .iter()
                    .all(R2ILOp::is_speculatable_value)
                {
                    rewrite_conditional_forward_branch(block, branch_index, target_index, cond);
                } else {
                    block.ops[branch_index] = R2ILOp::Unimplemented;
                }
            }
        }
    }
}

#[derive(Debug)]
enum LocalBranch {
    Unconditional(Varnode),
    Conditional { target: Varnode, cond: Varnode },
}

impl LocalBranch {
    fn target(&self) -> &Varnode {
        match self {
            Self::Unconditional(target) | Self::Conditional { target, .. } => target,
        }
    }
}

fn local_branch(
    block: &R2ILBlock,
    branch_index: usize,
    op: &R2ILOp,
) -> Option<(usize, LocalBranch, usize)> {
    let branch = match op {
        R2ILOp::Branch { target } => LocalBranch::Unconditional(target.clone()),
        R2ILOp::CBranch { target, cond } => LocalBranch::Conditional {
            target: target.clone(),
            cond: cond.clone(),
        },
        _ => return None,
    };
    let target_index = match branch.target().space {
        SpaceId::Const => relative_target_index(branch_index, branch.target()),
        // Some Sleigh specifications spell a local skip to the end of an
        // instruction as the RAM address of the following instruction rather
        // than as a constant-space relative P-code label. It is local only
        // when operations still follow the branch in this single-instruction
        // block; an ordinary native branch to its fallthrough has no such
        // operations and must remain control flow.
        SpaceId::Ram
            if branch_index + 1 < block.ops.len()
                && branch.target().offset == block.addr.checked_add(u64::from(block.size))? =>
        {
            Some(block.ops.len())
        }
        _ => None,
    }?;
    Some((branch_index, branch, target_index))
}

fn relative_target_index(branch_index: usize, target: &Varnode) -> Option<usize> {
    let bit_width = target.size.checked_mul(8)?;
    if bit_width == 0 || bit_width > 64 {
        return None;
    }
    let shift = 64u32.checked_sub(bit_width)?;
    let relative = ((target.offset << shift) as i64) >> shift;
    branch_index.checked_add_signed(isize::try_from(relative).ok()?)
}

fn rewrite_unconditional_forward_branch(
    block: &mut R2ILBlock,
    branch_index: usize,
    target_index: usize,
) {
    let old_ops = std::mem::take(&mut block.ops);
    let old_metadata = std::mem::take(&mut block.op_metadata);
    let mut ops = Vec::with_capacity(old_ops.len().saturating_sub(target_index - branch_index));
    let mut metadata = BTreeMap::new();

    for (old_index, op) in old_ops.into_iter().enumerate() {
        if old_index >= branch_index && old_index < target_index {
            continue;
        }
        push_with_old_metadata(&mut ops, &mut metadata, op, &old_metadata, old_index);
    }
    block.ops = ops;
    block.op_metadata = metadata;
}

fn rewrite_conditional_forward_branch(
    block: &mut R2ILBlock,
    branch_index: usize,
    target_index: usize,
    cond: Varnode,
) {
    let old_ops = std::mem::take(&mut block.ops);
    let old_metadata = std::mem::take(&mut block.op_metadata);
    let old_len = old_ops.len();
    let mut allocator = InstructionTempAllocator::for_ops(&old_ops);
    let mut ops = Vec::with_capacity(old_ops.len() + target_index - branch_index - 1);
    let mut metadata = BTreeMap::new();
    let mut live_at_target = HashSet::new();
    for op in old_ops[target_index..].iter().rev() {
        if let Some(output) = op.output() {
            live_at_target.remove(output);
        }
        live_at_target.extend(op.inputs().into_iter().cloned());
    }
    let mut candidates = HashMap::<Varnode, Varnode>::new();
    let mut preserved = Vec::<(Varnode, Varnode, usize)>::new();
    let mut preserved_index = HashMap::<Varnode, usize>::new();

    let emit_preserved = |ops: &mut Vec<R2ILOp>,
                          metadata: &mut BTreeMap<usize, OpMetadata>,
                          preserved: &[(Varnode, Varnode, usize)]| {
        for (dst, candidate, old_index) in preserved {
            push_with_old_metadata(
                ops,
                metadata,
                R2ILOp::Select {
                    dst: dst.clone(),
                    cond: cond.clone(),
                    if_true: dst.clone(),
                    if_false: candidate.clone(),
                },
                &old_metadata,
                *old_index,
            );
        }
    };

    for (old_index, mut op) in old_ops.into_iter().enumerate() {
        if old_index == branch_index {
            continue;
        }
        if old_index == target_index {
            emit_preserved(&mut ops, &mut metadata, &preserved);
        }
        if old_index > branch_index && old_index < target_index {
            for input in op.inputs_mut() {
                if let Some(candidate) = candidates.get(input) {
                    *input = candidate.clone();
                }
            }
            let Some(dst) = op.output().cloned() else {
                push_unimplemented(&mut ops, &mut metadata, &old_metadata, old_index);
                continue;
            };
            let Some(candidate) = allocator.allocate(dst.size) else {
                push_unimplemented(&mut ops, &mut metadata, &old_metadata, old_index);
                continue;
            };
            *op.output_mut()
                .expect("speculatable value operation has output") = candidate.clone();
            push_with_old_metadata(&mut ops, &mut metadata, op, &old_metadata, old_index);
            candidates.insert(dst.clone(), candidate.clone());
            if dst.space != SpaceId::Unique || live_at_target.contains(&dst) {
                if let Some(index) = preserved_index.get(&dst).copied() {
                    preserved[index] = (dst, candidate, old_index);
                } else {
                    preserved_index.insert(dst.clone(), preserved.len());
                    preserved.push((dst, candidate, old_index));
                }
            }
            continue;
        }
        push_with_old_metadata(&mut ops, &mut metadata, op, &old_metadata, old_index);
    }
    // No old operation visits `target_index` when the local label is one past
    // the instruction. Emit the externally surviving definitions here.
    if target_index == old_len {
        emit_preserved(&mut ops, &mut metadata, &preserved);
    }
    block.ops = ops;
    block.op_metadata = metadata;
}

fn push_unimplemented(
    ops: &mut Vec<R2ILOp>,
    metadata: &mut BTreeMap<usize, OpMetadata>,
    old_metadata: &BTreeMap<usize, OpMetadata>,
    old_index: usize,
) {
    push_with_old_metadata(
        ops,
        metadata,
        R2ILOp::Unimplemented,
        old_metadata,
        old_index,
    );
}

fn push_with_old_metadata(
    ops: &mut Vec<R2ILOp>,
    metadata: &mut BTreeMap<usize, OpMetadata>,
    op: R2ILOp,
    old_metadata: &BTreeMap<usize, OpMetadata>,
    old_index: usize,
) {
    let new_index = ops.len();
    ops.push(op);
    if let Some(meta) = old_metadata.get(&old_index) {
        metadata.insert(new_index, meta.clone());
    }
}

struct InstructionTempAllocator {
    next: u64,
}

impl InstructionTempAllocator {
    fn for_ops(ops: &[R2ILOp]) -> Self {
        let next = ops
            .iter()
            .flat_map(|op| op.inputs().into_iter().chain(op.output()))
            .filter(|varnode| varnode.space == SpaceId::Unique)
            .filter_map(|varnode| varnode.offset.checked_add(u64::from(varnode.size.max(1))))
            .max()
            .unwrap_or(0)
            .saturating_add(7)
            & !7;
        Self { next }
    }

    fn allocate(&mut self, size: u32) -> Option<Varnode> {
        let width = u64::from(size.max(1));
        let offset = self.next;
        self.next = self.next.checked_add(width)?.checked_add(7)? & !7;
        Some(Varnode::unique(offset, size))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conditional_relative_branch_becomes_value_select() {
        let result = Varnode::unique(0x100, 4);
        let divisor = Varnode::register(0x20, 4);
        let dividend = Varnode::register(0x24, 4);
        let cond = Varnode::unique(0x108, 1);
        let mut block = R2ILBlock::new(0x1000, 4);
        block.ops = vec![
            R2ILOp::Copy {
                dst: result.clone(),
                src: Varnode::constant(0, 4),
            },
            R2ILOp::IntEqual {
                dst: cond.clone(),
                a: divisor.clone(),
                b: Varnode::constant(0, 4),
            },
            R2ILOp::CBranch {
                target: Varnode::constant(2, 8),
                cond: cond.clone(),
            },
            R2ILOp::IntSDiv {
                dst: result.clone(),
                a: dividend,
                b: divisor,
            },
            R2ILOp::Copy {
                dst: Varnode::register(0x28, 4),
                src: result.clone(),
            },
        ];

        normalize_instruction_local_control(&mut block);

        assert!(
            !block
                .ops
                .iter()
                .any(|op| matches!(op, R2ILOp::CBranch { .. }))
        );
        let select = block
            .ops
            .iter()
            .find_map(|op| match op {
                R2ILOp::Select {
                    dst,
                    cond,
                    if_true,
                    if_false,
                } => Some((dst, cond, if_true, if_false)),
                _ => None,
            })
            .expect("value select");
        assert_eq!(select.0, &result);
        assert_eq!(select.1, &cond);
        assert_eq!(select.2, &result);
        assert_eq!(select.3.space, SpaceId::Unique);
        assert_ne!(select.3, &result);
    }

    #[test]
    fn conditional_relative_branch_over_effect_refuses() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.ops = vec![
            R2ILOp::CBranch {
                target: Varnode::constant(2, 8),
                cond: Varnode::register(0x20, 1),
            },
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::register(0x28, 8),
                val: Varnode::register(0x30, 4),
            },
        ];

        normalize_instruction_local_control(&mut block);

        assert!(matches!(block.ops.first(), Some(R2ILOp::Unimplemented)));
    }

    #[test]
    fn conditional_ram_branch_over_values_becomes_selects() {
        let flags = Varnode::register(0x20, 1);
        let candidate = Varnode::unique(0x100, 1);
        let cond = Varnode::unique(0x108, 1);
        let mut block = R2ILBlock::new(0x1000, 4);
        block.ops = vec![
            R2ILOp::CBranch {
                target: Varnode::ram(0x1004, 8),
                cond: cond.clone(),
            },
            R2ILOp::Copy {
                dst: candidate.clone(),
                src: Varnode::constant(1, 1),
            },
            R2ILOp::Copy {
                dst: flags.clone(),
                src: candidate.clone(),
            },
        ];

        normalize_instruction_local_control(&mut block);

        assert!(
            !block
                .ops
                .iter()
                .any(|op| matches!(op, R2ILOp::CBranch { .. }))
        );
        assert!(block.ops.iter().any(|op| matches!(
            op,
            R2ILOp::Select {
                dst,
                cond: select_cond,
                if_true,
                if_false,
            } if dst == &flags
                && select_cond == &cond
                && if_true == &flags
                && if_false.space == SpaceId::Unique
        )));
        assert!(
            block
                .ops
                .iter()
                .flat_map(R2ILOp::inputs)
                .all(|input| input != &candidate),
            "the undefined guarded temporary must be replaced by its candidate"
        );
    }

    #[test]
    fn terminal_ram_branch_to_following_instruction_stays_control_flow() {
        let branch = R2ILOp::CBranch {
            target: Varnode::ram(0x1004, 8),
            cond: Varnode::register(0x20, 1),
        };
        let mut block = R2ILBlock::new(0x1000, 4);
        block.ops = vec![branch.clone()];

        normalize_instruction_local_control(&mut block);

        assert_eq!(block.ops, vec![branch]);
    }
}
