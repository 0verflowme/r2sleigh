//! Normalization for P-code-relative control flow inside one instruction.
//!
//! Ghidra encodes instruction-local branches with a constant-space target whose
//! signed offset is relative to the branch operation's index. Those edges are
//! not machine CFG edges. Forward branches over speculatable value operations
//! are converted to explicit value selects; unsupported local control becomes
//! `Unimplemented` so downstream consumers refuse instead of inventing a CFG.

use std::collections::BTreeMap;

use r2il::{OpMetadata, R2ILBlock, R2ILOp, SpaceId, Varnode};

pub(crate) fn normalize_instruction_local_control(block: &mut R2ILBlock) {
    loop {
        let Some((branch_index, branch)) =
            block
                .ops
                .iter()
                .enumerate()
                .find_map(|(index, op)| match op {
                    R2ILOp::Branch { target } if target.space == SpaceId::Const => {
                        Some((index, LocalBranch::Unconditional(target.clone())))
                    }
                    R2ILOp::CBranch { target, cond } if target.space == SpaceId::Const => Some((
                        index,
                        LocalBranch::Conditional {
                            target: target.clone(),
                            cond: cond.clone(),
                        },
                    )),
                    _ => None,
                })
        else {
            break;
        };

        let Some(target_index) = relative_target_index(branch_index, branch.target()) else {
            block.ops[branch_index] = R2ILOp::Unimplemented;
            continue;
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
    let mut allocator = InstructionTempAllocator::for_ops(&old_ops);
    let mut ops = Vec::with_capacity(old_ops.len() + target_index - branch_index - 1);
    let mut metadata = BTreeMap::new();

    for (old_index, mut op) in old_ops.into_iter().enumerate() {
        if old_index == branch_index {
            continue;
        }
        if old_index > branch_index && old_index < target_index {
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
            push_with_old_metadata(
                &mut ops,
                &mut metadata,
                R2ILOp::Select {
                    dst: dst.clone(),
                    cond: cond.clone(),
                    if_true: dst,
                    if_false: candidate,
                },
                &old_metadata,
                old_index,
            );
            continue;
        }
        push_with_old_metadata(&mut ops, &mut metadata, op, &old_metadata, old_index);
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
}
