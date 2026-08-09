//! Exact x86-64 `push rbp; mov rbp, rsp; ...; pop rbp; ret` envelopes.
//!
//! The helper in this module intentionally proves only the standard frame
//! mechanics.  Callers remain responsible for classifying every instruction
//! between the prefix and suffix and every non-frame memory access.

use r2il::SpaceId;

use crate::function::SSAFunction;
use crate::graph::{InstId, SsaGraph, ValueId};
use crate::machine_context::{MachineMemoryEndianness, SourceMachineContext};
use crate::op::SSAOp;
use crate::var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar};

const RSP_OFFSET: u64 = 32;
const RBP_OFFSET: u64 = 40;
const RIP_OFFSET: u64 = 648;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct X86FrameRelativeRange {
    pub offset: i64,
    pub size_bytes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct X86StandardFrameFact {
    pub stack_storage: CanonicalStorageId,
    pub frame_pointer_storage: CanonicalStorageId,
    pub instruction_pointer_storage: CanonicalStorageId,
    pub memory_space: SpaceId,
    pub entry_stack: ValueId,
    pub allocated_stack: ValueId,
    pub saved_frame_pointer: ValueId,
    pub save_copy: InstId,
    pub allocate: InstId,
    pub save_store: InstId,
    pub establish_frame_pointer: InstId,
    pub restore_load: InstId,
    pub restored_stack: ValueId,
    pub pop_frame: InstId,
    pub restore_frame_pointer: InstId,
    pub return_target: ValueId,
    pub return_target_load: InstId,
    pub final_stack: ValueId,
    pub pop_return_target: InstId,
    pub return_inst: InstId,
    pub saved_frame_pointer_range: X86FrameRelativeRange,
    pub return_address_range: X86FrameRelativeRange,
    pub instructions: Box<[InstId]>,
}

pub(crate) fn collect_standard_x86_frame(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    block_addr: u64,
    suffix: usize,
) -> Option<X86StandardFrameFact> {
    let block = function.get_block(block_addr)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(block_addr, index);
    let (saved_var, frame_pointer_storage) = match op(0)? {
        SSAOp::Copy { dst, src } if src.version == 0 && dst.size == 8 && src.size == 8 => {
            (dst, storage(graph, src)?)
        }
        _ => return None,
    };
    let (entry_stack_var, allocated_stack_var, stack_storage) = match op(1)? {
        SSAOp::IntSub { dst, a, b } if a.version == 0 && constant(b, 8, 8) => {
            let stack = storage(graph, a)?;
            if storage(graph, dst)? != stack || stack.size != 8 {
                return None;
            }
            (a, dst, stack)
        }
        _ => return None,
    };
    match op(2)? {
        SSAOp::Store { addr, val, .. }
            if addr == allocated_stack_var && val == saved_var && val.size == 8 => {}
        _ => return None,
    }
    match op(3)? {
        SSAOp::Copy { dst, src }
            if src == allocated_stack_var && storage(graph, dst)? == frame_pointer_storage => {}
        _ => return None,
    }
    let dead_load_seed = match op(suffix)? {
        SSAOp::Copy { dst, src } if dst.size == 8 && constant(src, 0, 8) => value(graph, dst)?,
        _ => return None,
    };
    let (restored_frame_var, restored_frame, restore_load) = match op(suffix + 1)? {
        SSAOp::Load { dst, addr, .. } if addr == allocated_stack_var && dst.size == 8 => {
            (dst, value(graph, dst)?, inst(suffix + 1)?)
        }
        _ => return None,
    };
    let restore_copy = inst(suffix + 3)?;
    if dead_load_seed == restored_frame
        || graph
            .uses_of
            .get(dead_load_seed.0 as usize)
            .is_none_or(|uses| !uses.is_empty())
        || graph
            .uses_of
            .get(restored_frame.0 as usize)
            .is_none_or(|uses| {
                !matches!(uses.as_slice(), [use_site]
					if use_site.inst == restore_copy && use_site.input_idx == 0)
            })
    {
        return None;
    }
    let restored_stack_var = match op(suffix + 2)? {
        SSAOp::IntAdd { dst, a, b } if a == allocated_stack_var && constant(b, 8, 8) => dst,
        _ => return None,
    };
    if storage(graph, restored_stack_var)? != stack_storage {
        return None;
    }
    match op(suffix + 3)? {
        SSAOp::Copy { dst, src }
            if src == restored_frame_var && storage(graph, dst)? == frame_pointer_storage => {}
        _ => return None,
    }
    let (return_target_var, instruction_pointer_storage) = match op(suffix + 4)? {
        SSAOp::Load { dst, addr, .. } if addr == restored_stack_var && dst.size == 8 => {
            (dst, storage(graph, dst)?)
        }
        _ => return None,
    };
    let final_stack_var = match op(suffix + 5)? {
        SSAOp::IntAdd { dst, a, b } if a == restored_stack_var && constant(b, 8, 8) => dst,
        _ => return None,
    };
    if storage(graph, final_stack_var)? != stack_storage {
        return None;
    }
    match op(suffix + 6)? {
        SSAOp::Return { target } if target == return_target_var => {}
        _ => return None,
    }
    let memory_space = machine.memory_space_at(block_addr, 2)?;
    if machine.memory_space_at(block_addr, suffix + 1) != Some(memory_space)
        || machine.memory_space_at(block_addr, suffix + 4) != Some(memory_space)
    {
        return None;
    }
    if !register_at(stack_storage, RSP_OFFSET, 8)
        || !register_at(frame_pointer_storage, RBP_OFFSET, 8)
        || !register_at(instruction_pointer_storage, RIP_OFFSET, 8)
    {
        return None;
    }
    let memory = machine.memory_model().space(memory_space)?;
    if memory.address_bits() != 64
        || memory.word_size_bytes() != 1
        || memory.endianness() != MachineMemoryEndianness::Little
    {
        return None;
    }
    let instructions = (0..4)
        .chain(suffix..suffix + 7)
        .map(inst)
        .collect::<Option<Vec<_>>>()?;
    Some(X86StandardFrameFact {
        stack_storage,
        frame_pointer_storage,
        instruction_pointer_storage,
        memory_space,
        entry_stack: value(graph, entry_stack_var)?,
        allocated_stack: value(graph, allocated_stack_var)?,
        saved_frame_pointer: value(graph, saved_var)?,
        save_copy: inst(0)?,
        allocate: inst(1)?,
        save_store: inst(2)?,
        establish_frame_pointer: inst(3)?,
        restore_load,
        restored_stack: value(graph, restored_stack_var)?,
        pop_frame: inst(suffix + 2)?,
        restore_frame_pointer: restore_copy,
        return_target: value(graph, return_target_var)?,
        return_target_load: inst(suffix + 4)?,
        final_stack: value(graph, final_stack_var)?,
        pop_return_target: inst(suffix + 5)?,
        return_inst: inst(suffix + 6)?,
        saved_frame_pointer_range: X86FrameRelativeRange {
            offset: -8,
            size_bytes: 8,
        },
        return_address_range: X86FrameRelativeRange {
            offset: 0,
            size_bytes: 8,
        },
        instructions: instructions.into_boxed_slice(),
    })
}

fn constant(value: &SSAVar, expected: u64, size: u32) -> bool {
    value.size == size && value.constant_bits() == Some(expected)
}

fn storage(graph: &SsaGraph, value: &SSAVar) -> Option<CanonicalStorageId> {
    graph.canonical_storage_for_var(value)
}

fn register_at(storage: CanonicalStorageId, offset: u64, size: u32) -> bool {
    storage.space == CanonicalStorageSpace::Register
        && storage.offset == offset
        && storage.size == size
}

fn value(graph: &SsaGraph, value: &SSAVar) -> Option<ValueId> {
    graph.value_id_for_var(value)
}
