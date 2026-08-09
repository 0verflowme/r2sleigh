//! Exact source facts for the one-block x86-64 O2 integer guards.
//!
//! These facts deliberately describe the lifted machine shape rather than a
//! symbol name.  In particular, the returned C `int` is reconstructed from the
//! RAX zero-extension of an EAX zero followed by an AL boolean overlay;
//! treating either older definition as the boundary value would be unsound.

use r2il::SpaceId;

use crate::function::SSAFunction;
use crate::graph::{InstId, SsaGraph, ValueId};
use crate::machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineMemoryEndianness,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceTypeKind,
};
use crate::op::SSAOp;
use crate::semantic::{CallBoundarySlot, SourceBoundaryFacts, SourceReturnRegisterCompositionFact};
use crate::var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar};

pub const BRANCHLESS_GUARD_FACT_SCHEMA_VERSION: u32 = 1;

const RAX_OFFSET: u64 = 0;
const RSP_OFFSET: u64 = 32;
const RBP_OFFSET: u64 = 40;
const RSI_OFFSET: u64 = 48;
const RDI_OFFSET: u64 = 56;
const CF_OFFSET: u64 = 512;
const PF_OFFSET: u64 = 514;
const ZF_OFFSET: u64 = 518;
const SF_OFFSET: u64 = 519;
const OF_OFFSET: u64 = 523;
const RIP_OFFSET: u64 = 648;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchlessGuardKind {
    /// Exact `sub arg, expected; setz` lowering, equivalent to `arg == expected`.
    SimpleSubtractEqual { expected: u32 },
    DualWrap32XorOrEqual {
        sum_expected: u32,
        difference_expected: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchlessGuardAbiFact {
    pub revision_identity: Box<[u8]>,
    pub parameters: Box<[BranchlessGuardParameterFact]>,
    pub parameter_logical_values: Box<[SourceLogicalValue]>,
    pub return_logical_value: SourceLogicalValue,
    pub return_storage: CanonicalStorageId,
}

/// One full SysV AMD64 ABI carrier bound to its exact low 32-bit graph input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BranchlessGuardParameterFact {
    pub index: u32,
    pub abi_storage: CanonicalStorageId,
    pub low32_storage: CanonicalStorageId,
    pub low32_value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchlessGuardFlagPacketFact {
    pub value: ValueId,
    pub sign: InstId,
    pub zero_equal: InstId,
    pub zero_flag: ValueId,
    pub low_byte_mask: InstId,
    pub population_count: InstId,
    pub parity_mask: InstId,
    pub parity_equal: InstId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchlessGuardFrameFact {
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchlessGuardReturnFact {
    pub composition: SourceReturnRegisterCompositionFact,
    pub boolean: ValueId,
    pub zero_base: ValueId,
    pub return_target: ValueId,
    pub return_inst: InstId,
}

/// Name-independent exact evidence for one admitted whole function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchlessGuardFact {
    pub schema_version: u32,
    pub entry: u64,
    pub abi: BranchlessGuardAbiFact,
    pub kind: BranchlessGuardKind,
    pub frame: BranchlessGuardFrameFact,
    pub flag_packets: Box<[BranchlessGuardFlagPacketFact]>,
    pub returned: BranchlessGuardReturnFact,
    /// Every graph instruction, in exact source order.  This closes the usual
    /// dead-code hole: an unrelated computation cannot ride along for free.
    pub instruction_inventory: Box<[InstId]>,
    /// Exact instructions implementing the visible predicate and boolean.
    pub semantic_instructions: Box<[InstId]>,
    /// Exact standard ABI envelope instructions.
    pub frame_instructions: Box<[InstId]>,
}

impl BranchlessGuardFact {
    pub fn validate_against(&self, artifact: &crate::SsaArtifact) -> bool {
        self.schema_version == BRANCHLESS_GUARD_FACT_SCHEMA_VERSION
            && artifact.structured().branchless_guards.get(&self.entry) == Some(self)
    }
}

pub(crate) fn collect_branchless_guard_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> std::collections::BTreeMap<u64, BranchlessGuardFact> {
    let mut facts = std::collections::BTreeMap::new();
    let Some(fact) = collect_one(function, graph, boundaries, machine) else {
        return facts;
    };
    facts.insert(fact.entry, fact);
    facts
}

fn collect_one(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> Option<BranchlessGuardFact> {
    let [block_addr] = function.block_addrs() else {
        return None;
    };
    let block = function.get_block(*block_addr)?;
    if function.entry != *block_addr
        || !block.phis.is_empty()
        || !function.predecessors(*block_addr).is_empty()
        || !function.successors(*block_addr).is_empty()
        || !boundaries.calls.is_empty()
    {
        return None;
    }
    let abi = collect_abi(graph, machine)?;
    let (kind, frame, flag_packets, returned, semantic_instructions, frame_instructions) =
        match block.ops.len() {
            32 => collect_simple(function, graph, boundaries, machine, &abi, *block_addr)?,
            66 => collect_dual(function, graph, boundaries, machine, &abi, *block_addr)?,
            _ => return None,
        };
    let instruction_inventory = (0..block.ops.len())
        .map(|op_index| graph.inst_id_for_op_site(*block_addr, op_index))
        .collect::<Option<Vec<_>>>()?;
    if instruction_inventory.len() != graph.insts.len()
        || semantic_instructions
            .iter()
            .chain(&frame_instructions)
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            != instruction_inventory.iter().copied().collect()
    {
        return None;
    }
    Some(BranchlessGuardFact {
        schema_version: BRANCHLESS_GUARD_FACT_SCHEMA_VERSION,
        entry: *block_addr,
        abi,
        kind,
        frame,
        flag_packets: flag_packets.into_boxed_slice(),
        returned,
        instruction_inventory: instruction_inventory.into_boxed_slice(),
        semantic_instructions: semantic_instructions.into_boxed_slice(),
        frame_instructions: frame_instructions.into_boxed_slice(),
    })
}

fn collect_abi(graph: &SsaGraph, machine: &SourceMachineContext) -> Option<BranchlessGuardAbiFact> {
    if machine.schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
        || !machine.abi_model().is_available()
        || !machine.abi_model().is_coherent()
        || !machine.memory_model().is_available()
        || !machine.memory_model().is_coherent()
    {
        return None;
    }
    let interface = machine.function_interface()?;
    let types = interface.type_graph()?;
    let return_logical_value = interface.return_logical_value()?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity().is_empty()
        || interface.calling_convention() != "sysv_amd64"
        || !interface.stack_slots().is_empty()
        || types.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || types.types().len() != 1
        || !types.aggregates().is_empty()
        || types.types()[0].kind() != SourceTypeKind::SignedInteger
        || types.types()[0].size_bits() != 32
        || types.types()[0].align_bits() != 32
        || interface.parameters().is_empty()
        || !matches!(interface.parameters().len(), 1 | 2)
        || interface.parameter_logical_values().len() != interface.parameters().len()
        || interface
            .parameter_logical_values()
            .iter()
            .chain(std::iter::once(&return_logical_value))
            .any(|logical| {
                logical.type_id() != 0
                    || logical.carrier().kind() != SourceCarrierKind::LowBits
                    || logical.carrier().offset_bits() != 0
                    || logical.carrier().size_bits() != 32
            })
    {
        return None;
    }
    let return_storage = match interface.return_kind() {
        SourceFunctionReturn::Register { storage }
            if storage.space == CanonicalStorageSpace::Register
                && storage.offset == RAX_OFFSET
                && storage.size == 8 =>
        {
            storage
        }
        _ => return None,
    };
    if machine.abi_model().argument_registers().len() != interface.parameters().len()
        || machine.abi_model().return_registers().len() != 1
        || machine.abi_model().return_registers()[0].index() != 0
        || machine.abi_model().return_registers()[0].storage() != return_storage
    {
        return None;
    }
    let parameters = interface
        .parameters()
        .iter()
        .map(|parameter| {
            let expected_offset = match parameter.index() {
                0 => RDI_OFFSET,
                1 if interface.parameters().len() == 2 => RSI_OFFSET,
                _ => return None,
            };
            if parameter.storage().space != CanonicalStorageSpace::Register
                || parameter.storage().offset != expected_offset
                || parameter.storage().size != 8
                || machine
                    .abi_model()
                    .argument_registers()
                    .get(parameter.index() as usize)
                    .is_none_or(|slot| {
                        slot.index() != parameter.index() || slot.storage() != parameter.storage()
                    })
            {
                return None;
            }
            let low32_storage = CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: parameter.storage().offset,
                size: 4,
            };
            let candidates = graph
                .values
                .iter()
                .filter(|value| {
                    graph.def_inst(value.id).is_none()
                        && value.var.version == 0
                        && value.var.size == 4
                        && value.canonical_storage == Some(low32_storage)
                })
                .map(|value| value.id)
                .collect::<Vec<_>>();
            let [low32_value] = candidates.as_slice() else {
                return None;
            };
            Some(BranchlessGuardParameterFact {
                index: parameter.index(),
                abi_storage: parameter.storage(),
                low32_storage,
                low32_value: *low32_value,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(BranchlessGuardAbiFact {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        parameters: parameters.into_boxed_slice(),
        parameter_logical_values: interface
            .parameter_logical_values()
            .to_vec()
            .into_boxed_slice(),
        return_logical_value,
        return_storage,
    })
}

type CollectedGuard = (
    BranchlessGuardKind,
    BranchlessGuardFrameFact,
    Vec<BranchlessGuardFlagPacketFact>,
    BranchlessGuardReturnFact,
    Vec<InstId>,
    Vec<InstId>,
);

fn collect_simple(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
    abi: &BranchlessGuardAbiFact,
    block_addr: u64,
) -> Option<CollectedGuard> {
    let block = function.get_block(block_addr)?;
    if abi.parameters.len() != 1 {
        return None;
    }
    let frame = collect_frame(function, graph, machine, block_addr, 25)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(block_addr, index);
    let (cf, of) = match (op(4)?, op(5)?) {
        (
            SSAOp::Copy {
                dst: cf,
                src: zero0,
            },
            SSAOp::Copy {
                dst: of,
                src: zero1,
            },
        ) if constant(zero0, 0, 1) && constant(zero1, 0, 1) => {
            let cf = storage(graph, cf)?;
            let of = storage(graph, of)?;
            if !register_at(cf, CF_OFFSET, 1) || !register_at(of, OF_OFFSET, 1) {
                return None;
            }
            (cf, of)
        }
        _ => return None,
    };
    let zero_base_var = match op(6)? {
        SSAOp::IntXor { dst, a, b }
            if a == b
                && storage(graph, dst)?.offset == abi.return_storage.offset
                && storage(graph, dst)?.size == 4 =>
        {
            dst
        }
        _ => return None,
    };
    let zero_base_full = require_zext_alias(op(7)?, graph, zero_base_var)?;
    if storage(graph, zero_base_full)? != abi.return_storage {
        return None;
    }
    let zero_base = value(graph, zero_base_full)?;
    let zero_packet = collect_flag_packet(function, graph, machine, block_addr, 8, zero_base_var)?;
    let copied = match op(14)? {
        SSAOp::Copy { dst, src } if value(graph, src)? == abi.parameters[0].low32_value => dst,
        _ => return None,
    };
    let expected = match op(17)? {
        SSAOp::IntSub { dst, a, b } if a == copied => {
            let expected = u32::try_from(b.constant_bits()?).ok()?;
            if !constant(b, u64::from(expected), 4) {
                return None;
            }
            match (op(15)?, op(16)?) {
                (
                    SSAOp::IntLess {
                        dst: cf_dst,
                        a: cf_a,
                        b: cf_b,
                    },
                    SSAOp::IntSBorrow {
                        dst: of_dst,
                        a: of_a,
                        b: of_b,
                    },
                ) if cf_a == copied
                    && cf_b == b
                    && of_a == copied
                    && of_b == b
                    && storage(graph, cf_dst)? == cf
                    && storage(graph, of_dst)? == of => {}
                _ => return None,
            }
            (expected, dst)
        }
        _ => return None,
    };
    if copied.size != 4 || expected.1.size != 4 {
        return None;
    }
    let predicate_packet =
        collect_flag_packet(function, graph, machine, block_addr, 18, expected.1)?;
    let boolean_var = match op(24)? {
        SSAOp::Copy { dst, src } if value(graph, src)? == predicate_packet.zero_flag => dst,
        _ => return None,
    };
    let returned = collect_return(
        function,
        graph,
        boundaries,
        machine,
        block_addr,
        7,
        zero_base,
        24,
        boolean_var,
        31,
        frame.return_target,
        abi.return_storage,
    )?;
    let semantic_instructions = (4..25).map(inst).collect::<Option<Vec<_>>>()?;
    let frame_instructions = (0..4).chain(25..32).map(inst).collect::<Option<Vec<_>>>()?;
    Some((
        BranchlessGuardKind::SimpleSubtractEqual {
            expected: expected.0,
        },
        frame,
        vec![zero_packet, predicate_packet],
        returned,
        semantic_instructions,
        frame_instructions,
    ))
}

fn collect_dual(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
    abi: &BranchlessGuardAbiFact,
    block_addr: u64,
) -> Option<CollectedGuard> {
    let block = function.get_block(block_addr)?;
    if abi.parameters.len() != 2 {
        return None;
    }
    let frame = collect_frame(function, graph, machine, block_addr, 59)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(block_addr, index);
    let full_a = match op(4)? {
        SSAOp::IntMult { dst, a, b }
            if constant(b, 1, 8) && full_entry_carrier(a, abi.parameters[0], graph) =>
        {
            dst
        }
        _ => return None,
    };
    let sum64 = match op(5)? {
        SSAOp::IntAdd { dst, a, b }
            if b == full_a && full_entry_carrier(a, abi.parameters[1], graph) =>
        {
            dst
        }
        _ => return None,
    };
    let sum32 = match op(6)? {
        SSAOp::Subpiece {
            dst,
            src,
            offset: 0,
        } if src == sum64 && dst.size == 4 => dst,
        _ => return None,
    };
    require_zext_alias(op(7)?, graph, sum32)?;
    let (cf, of, difference) = match (op(8)?, op(9)?, op(10)?) {
        (
            SSAOp::IntLess { dst: cf, a, b },
            SSAOp::IntSBorrow {
                dst: of,
                a: of_a,
                b: of_b,
            },
            SSAOp::IntSub {
                dst: difference,
                a: sub_a,
                b: sub_b,
            },
        ) if value(graph, a)? == abi.parameters[0].low32_value
            && value(graph, b)? == abi.parameters[1].low32_value
            && of_a == a
            && of_b == b
            && sub_a == a
            && sub_b == b
            && difference.size == 4 =>
        {
            (storage(graph, cf)?, storage(graph, of)?, difference)
        }
        _ => return None,
    };
    if !register_at(cf, CF_OFFSET, 1) || !register_at(of, OF_OFFSET, 1) {
        return None;
    }
    require_zext_alias(op(11)?, graph, difference)?;
    let difference_packet =
        collect_flag_packet(function, graph, machine, block_addr, 12, difference)?;

    require_zero_flags(op(18)?, op(19)?, graph, cf, of)?;
    let (sum_guard, sum_expected) = collect_xor_constant(op(20)?, sum32)?;
    require_zext_alias(op(21)?, graph, sum_guard)?;
    let sum_packet = collect_flag_packet(function, graph, machine, block_addr, 22, sum_guard)?;

    require_zero_flags(op(28)?, op(29)?, graph, cf, of)?;
    let (difference_guard, difference_expected) = collect_xor_constant(op(30)?, difference)?;
    require_zext_alias(op(31)?, graph, difference_guard)?;
    let difference_guard_packet =
        collect_flag_packet(function, graph, machine, block_addr, 32, difference_guard)?;

    require_zero_flags(op(38)?, op(39)?, graph, cf, of)?;
    let zero_base_var = match op(40)? {
        SSAOp::IntXor { dst, a, b }
            if a == b
                && storage(graph, dst)?.offset == abi.return_storage.offset
                && storage(graph, dst)?.size == 4 =>
        {
            dst
        }
        _ => return None,
    };
    let zero_base_full = require_zext_alias(op(41)?, graph, zero_base_var)?;
    if storage(graph, zero_base_full)? != abi.return_storage {
        return None;
    }
    let zero_base = value(graph, zero_base_full)?;
    let zero_packet = collect_flag_packet(function, graph, machine, block_addr, 42, zero_base_var)?;

    require_zero_flags(op(48)?, op(49)?, graph, cf, of)?;
    let joined = match op(50)? {
        SSAOp::IntOr { dst, a, b } if a == difference_guard && b == sum_guard && dst.size == 4 => {
            dst
        }
        _ => return None,
    };
    require_zext_alias(op(51)?, graph, joined)?;
    let joined_packet = collect_flag_packet(function, graph, machine, block_addr, 52, joined)?;
    let boolean_var = match op(58)? {
        SSAOp::Copy { dst, src } if value(graph, src)? == joined_packet.zero_flag => dst,
        _ => return None,
    };
    let returned = collect_return(
        function,
        graph,
        boundaries,
        machine,
        block_addr,
        41,
        zero_base,
        58,
        boolean_var,
        65,
        frame.return_target,
        abi.return_storage,
    )?;
    let semantic_instructions = (4..59).map(inst).collect::<Option<Vec<_>>>()?;
    let frame_instructions = (0..4).chain(59..66).map(inst).collect::<Option<Vec<_>>>()?;
    Some((
        BranchlessGuardKind::DualWrap32XorOrEqual {
            sum_expected,
            difference_expected,
        },
        frame,
        vec![
            difference_packet,
            sum_packet,
            difference_guard_packet,
            zero_packet,
            joined_packet,
        ],
        returned,
        semantic_instructions,
        frame_instructions,
    ))
}

fn collect_frame(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    block_addr: u64,
    suffix: usize,
) -> Option<BranchlessGuardFrameFact> {
    let block = function.get_block(block_addr)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(block_addr, index);
    let (saved_var, frame_pointer_storage) = match op(0)? {
        SSAOp::Copy { dst, src } => (dst, storage(graph, src)?),
        _ => return None,
    };
    let (entry_stack_var, allocated_stack_var, stack_storage) = match op(1)? {
        SSAOp::IntSub { dst, a, b } if constant(b, 8, 8) => {
            let stack = storage(graph, a)?;
            if storage(graph, dst)? != stack || stack.size != 8 {
                return None;
            }
            (a, dst, stack)
        }
        _ => return None,
    };
    match op(2)? {
        SSAOp::Store { addr, val, .. } if addr == allocated_stack_var && val == saved_var => {}
        _ => return None,
    }
    match op(3)? {
        SSAOp::Copy { dst, src }
            if src == allocated_stack_var && storage(graph, dst)? == frame_pointer_storage => {}
        _ => return None,
    }
    let dead_load_seed = match op(suffix)? {
        SSAOp::Copy { dst, src } if constant(src, 0, 8) => value(graph, dst)?,
        _ => return None,
    };
    let (restored_frame_var, restored_frame, restore_load) = match op(suffix + 1)? {
        SSAOp::Load { dst, addr, .. } if addr == allocated_stack_var => {
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
        SSAOp::Load { dst, addr, .. } if addr == restored_stack_var => {
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
    Some(BranchlessGuardFrameFact {
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
    })
}

fn collect_return(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
    block_addr: u64,
    base_index: usize,
    zero_base: ValueId,
    overlay_index: usize,
    boolean_var: &SSAVar,
    return_index: usize,
    return_target: ValueId,
    return_storage: CanonicalStorageId,
) -> Option<BranchlessGuardReturnFact> {
    let return_inst = graph.inst_id_for_op_site(block_addr, return_index)?;
    let boundary = boundaries.returns.get(&return_inst)?;
    let [composition] = boundary.register_compositions.as_slice() else {
        return None;
    };
    if !boundary.complete
        || !boundary.values.is_empty()
        || !composition.validate(function, graph, machine, return_inst)
        || composition.slot
            != (CallBoundarySlot::Register {
                index: 0,
                storage: return_storage,
            })
        || composition.base.producer != graph.inst_id_for_op_site(block_addr, base_index)?
        || composition.base.storage != return_storage
        || composition.base.value != zero_base
        || composition.overlays.len() != 1
        || composition.overlays[0].definition.producer
            != graph.inst_id_for_op_site(block_addr, overlay_index)?
        || composition.overlays[0].definition.storage.space != CanonicalStorageSpace::Register
        || composition.overlays[0].definition.storage.offset != return_storage.offset
        || composition.overlays[0].definition.storage.size != 1
        || composition.overlays[0].offset_bytes != 0
        || composition.overlays[0].definition.value != value(graph, boolean_var)?
    {
        return None;
    }
    Some(BranchlessGuardReturnFact {
        composition: composition.clone(),
        boolean: value(graph, boolean_var)?,
        zero_base,
        return_target,
        return_inst,
    })
}

fn collect_flag_packet(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    block_addr: u64,
    start: usize,
    input: &SSAVar,
) -> Option<BranchlessGuardFlagPacketFact> {
    let block = function.get_block(block_addr)?;
    let op = |relative| block.ops.get(start + relative);
    let inst = |relative| graph.inst_id_for_op_site(block_addr, start + relative);
    match op(0)? {
        SSAOp::IntSLess { dst, a, b }
            if a == input
                && constant(b, 0, 4)
                && register_at(storage(graph, dst)?, SF_OFFSET, 1) => {}
        _ => return None,
    }
    let zero_flag = match op(1)? {
        SSAOp::IntEqual { dst, a, b }
            if a == input
                && constant(b, 0, 4)
                && register_at(storage(graph, dst)?, ZF_OFFSET, 1) =>
        {
            value(graph, dst)?
        }
        _ => return None,
    };
    let masked = match op(2)? {
        SSAOp::IntAnd { dst, a, b } if a == input && constant(b, 0xff, 4) => dst,
        _ => return None,
    };
    let population = match op(3)? {
        SSAOp::PopCount { dst, src } if src == masked && dst.size == 1 => dst,
        _ => return None,
    };
    let parity = match op(4)? {
        SSAOp::IntAnd { dst, a, b } if a == population && constant(b, 1, 1) => dst,
        _ => return None,
    };
    match op(5)? {
        SSAOp::IntEqual { dst, a, b }
            if a == parity
                && constant(b, 0, 1)
                && register_at(storage(graph, dst)?, PF_OFFSET, 1) => {}
        _ => return None,
    }
    Some(BranchlessGuardFlagPacketFact {
        value: value(graph, input)?,
        sign: inst(0)?,
        zero_equal: inst(1)?,
        zero_flag,
        low_byte_mask: inst(2)?,
        population_count: inst(3)?,
        parity_mask: inst(4)?,
        parity_equal: inst(5)?,
    })
}

fn require_zext_alias<'a>(
    op: &'a SSAOp,
    graph: &SsaGraph,
    input: &SSAVar,
) -> Option<&'a SSAVar> {
    let SSAOp::IntZExt { dst, src } = op else {
        return None;
    };
    let source = storage(graph, src)?;
    let destination = storage(graph, dst)?;
    (src == input
        && source.size == 4
        && destination.size == 8
        && source.offset == destination.offset)
        .then_some(dst)
}

fn require_zero_flags(
    cf_op: &SSAOp,
    of_op: &SSAOp,
    graph: &SsaGraph,
    cf: CanonicalStorageId,
    of: CanonicalStorageId,
) -> Option<()> {
    match (cf_op, of_op) {
        (
            SSAOp::Copy {
                dst: cf_dst,
                src: a,
            },
            SSAOp::Copy {
                dst: of_dst,
                src: b,
            },
        ) if constant(a, 0, 1)
            && constant(b, 0, 1)
            && storage(graph, cf_dst)? == cf
            && storage(graph, of_dst)? == of =>
        {
            Some(())
        }
        _ => None,
    }
}

fn collect_xor_constant<'a>(op: &'a SSAOp, input: &SSAVar) -> Option<(&'a SSAVar, u32)> {
    let SSAOp::IntXor { dst, a, b } = op else {
        return None;
    };
    if a != input || dst.size != 4 || b.size != 4 {
        return None;
    }
    Some((dst, u32::try_from(b.constant_bits()?).ok()?))
}

fn full_entry_carrier(
    value: &SSAVar,
    parameter: BranchlessGuardParameterFact,
    graph: &SsaGraph,
) -> bool {
    let Some(storage) = storage(graph, value) else {
        return false;
    };
    value.version == 0
        && storage.space == CanonicalStorageSpace::Register
        && storage.size == 8
        && storage == parameter.abi_storage
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

#[cfg(test)]
mod tests {
    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };

    use crate::{
        SourceAbiParameterSpec, SourceCarrierProjection, SourceFunctionInterface,
        SourceFunctionReturn, SourceLogicalValue, SourceType, SourceTypeGraph, SsaArtifact,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(7);
    const ENTRY: u64 = 0x1000;

    fn register(offset: u64, size: u32) -> Varnode {
        Varnode::register(offset, size)
    }

    fn constant(value: u64, size: u32) -> Varnode {
        Varnode::constant(value, size)
    }

    fn unique(next: &mut u64, size: u32) -> Varnode {
        let value = Varnode::unique(*next, size);
        *next += 0x80;
        value
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-branchless-guard-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("AL", 0, 1),
            ("EAX", 0, 4),
            ("RAX", 0, 8),
            ("ECX", 8, 4),
            ("RCX", 8, 8),
            ("RSP", 32, 8),
            ("RBP", 40, 8),
            ("ESI", 48, 4),
            ("RSI", 48, 8),
            ("EDI", 56, 4),
            ("RDI", 56, 8),
            ("CF", 512, 1),
            ("PF", 514, 1),
            ("ZF", 518, 1),
            ("SF", 519, 1),
            ("OF", 523, 1),
            ("RIP", 648, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn interface(parameter_count: usize, revision: &[u8]) -> SourceFunctionInterface {
        let types = SourceTypeGraph::new(
            [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
            [],
        )
        .expect("signed int type graph");
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let parameters = [storage(56), storage(48)]
            .into_iter()
            .take(parameter_count)
            .enumerate()
            .map(|(index, storage)| SourceAbiParameterSpec::new(index as u32, storage));
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "sysv_amd64",
            parameters,
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            (0..parameter_count).map(|_| SourceLogicalValue::new(0, low32)),
            Some(SourceLogicalValue::new(0, low32)),
            Some(types),
        )
        .expect("exact branchless interface")
    }

    fn push_frame_prefix(block: &mut R2ILBlock, next: &mut u64) {
        let saved = unique(next, 8);
        block.push(R2ILOp::Copy {
            dst: saved.clone(),
            src: register(40, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: register(32, 8),
            a: register(32, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: register(32, 8),
            val: saved,
        });
        block.push(R2ILOp::Copy {
            dst: register(40, 8),
            src: register(32, 8),
        });
    }

    fn push_flag_packet(block: &mut R2ILBlock, next: &mut u64, value: Varnode) {
        block.push(R2ILOp::IntSLess {
            dst: register(519, 1),
            a: value.clone(),
            b: constant(0, 4),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(518, 1),
            a: value.clone(),
            b: constant(0, 4),
        });
        let low = unique(next, 4);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: value,
            b: constant(0xff, 4),
        });
        let population = unique(next, 1);
        block.push(R2ILOp::PopCount {
            dst: population.clone(),
            src: low,
        });
        let parity = unique(next, 1);
        block.push(R2ILOp::IntAnd {
            dst: parity.clone(),
            a: population,
            b: constant(1, 1),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(514, 1),
            a: parity,
            b: constant(0, 1),
        });
    }

    fn push_zero_flags(block: &mut R2ILBlock) {
        block.push(R2ILOp::Copy {
            dst: register(512, 1),
            src: constant(0, 1),
        });
        block.push(R2ILOp::Copy {
            dst: register(523, 1),
            src: constant(0, 1),
        });
    }

    fn push_frame_suffix(block: &mut R2ILBlock, next: &mut u64) {
        let restored = unique(next, 8);
        block.push(R2ILOp::Copy {
            dst: restored.clone(),
            src: constant(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: restored,
            space: DATA,
            addr: register(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: register(32, 8),
            a: register(32, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Copy {
            dst: register(40, 8),
            src: unique_at_previous(next, 8),
        });
        block.push(R2ILOp::Load {
            dst: register(648, 8),
            space: DATA,
            addr: register(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: register(32, 8),
            a: register(32, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Return {
            target: register(648, 8),
        });
    }

    fn unique_at_previous(next: &u64, size: u32) -> Varnode {
        Varnode::unique(next.saturating_sub(0x80), size)
    }

    fn simple_block(entry: u64, expected: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 17);
        let mut next = 0x10000;
        push_frame_prefix(&mut block, &mut next);
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(0, 4),
            a: register(0, 4),
            b: register(0, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(0, 8),
            src: register(0, 4),
        });
        push_flag_packet(&mut block, &mut next, register(0, 4));
        let copied = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: register(56, 4),
        });
        block.push(R2ILOp::IntLess {
            dst: register(512, 1),
            a: copied.clone(),
            b: constant(expected, 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: register(523, 1),
            a: copied.clone(),
            b: constant(expected, 4),
        });
        let difference = unique(&mut next, 4);
        block.push(R2ILOp::IntSub {
            dst: difference.clone(),
            a: copied,
            b: constant(expected, 4),
        });
        push_flag_packet(&mut block, &mut next, difference);
        block.push(R2ILOp::Copy {
            dst: register(0, 1),
            src: register(518, 1),
        });
        push_frame_suffix(&mut block, &mut next);
        block
    }

    fn dual_block(entry: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 24);
        let mut next = 0x20000;
        push_frame_prefix(&mut block, &mut next);
        let scaled = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: scaled.clone(),
            a: register(56, 8),
            b: constant(1, 8),
        });
        let sum64 = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: sum64.clone(),
            a: register(48, 8),
            b: scaled,
        });
        block.push(R2ILOp::Subpiece {
            dst: register(8, 4),
            src: sum64,
            offset: 0,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(8, 8),
            src: register(8, 4),
        });
        block.push(R2ILOp::IntLess {
            dst: register(512, 1),
            a: register(56, 4),
            b: register(48, 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: register(523, 1),
            a: register(56, 4),
            b: register(48, 4),
        });
        block.push(R2ILOp::IntSub {
            dst: register(56, 4),
            a: register(56, 4),
            b: register(48, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(56, 8),
            src: register(56, 4),
        });
        push_flag_packet(&mut block, &mut next, register(56, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(8, 4),
            a: register(8, 4),
            b: constant(100, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(8, 8),
            src: register(8, 4),
        });
        push_flag_packet(&mut block, &mut next, register(8, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(56, 4),
            a: register(56, 4),
            b: constant(20, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(56, 8),
            src: register(56, 4),
        });
        push_flag_packet(&mut block, &mut next, register(56, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: register(0, 4),
            a: register(0, 4),
            b: register(0, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(0, 8),
            src: register(0, 4),
        });
        push_flag_packet(&mut block, &mut next, register(0, 4));
        push_zero_flags(&mut block);
        block.push(R2ILOp::IntOr {
            dst: register(56, 4),
            a: register(56, 4),
            b: register(8, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(56, 8),
            src: register(56, 4),
        });
        push_flag_packet(&mut block, &mut next, register(56, 4));
        block.push(R2ILOp::Copy {
            dst: register(0, 1),
            src: register(518, 1),
        });
        push_frame_suffix(&mut block, &mut next);
        block
    }

    fn artifact(block: R2ILBlock, parameter_count: usize) -> SsaArtifact {
        SsaArtifact::raw_with_interface(
            &[block],
            Some(&arch()),
            interface(parameter_count, b"branchless-guard-revision-1"),
        )
        .expect("branchless guard artifact")
    }

    #[test]
    fn exact_simple_guard_uses_full_rax_base_and_low_al_overlay() {
        let artifact = artifact(simple_block(ENTRY, 0xdead), 1);
        let fact = artifact
            .structured()
            .branchless_guards
            .get(&ENTRY)
            .expect("simple guard fact");
        assert_eq!(
            fact.kind,
            BranchlessGuardKind::SimpleSubtractEqual { expected: 0xdead }
        );
        assert_eq!(fact.abi.parameters[0].abi_storage.size, 8);
        assert_eq!(fact.abi.parameters[0].low32_storage.size, 4);
        assert_eq!(fact.abi.return_storage.size, 8);
        assert_eq!(fact.returned.composition.base.storage.size, 8);
        assert_eq!(
            fact.returned.composition.overlays[0]
                .definition
                .storage
                .size,
            1
        );
        assert!(fact.validate_against(&artifact));
    }

    #[test]
    fn exact_dual_guard_retains_wrap32_theorem_and_exact_inventory() {
        let artifact = artifact(dual_block(ENTRY), 2);
        let fact = artifact
            .structured()
            .branchless_guards
            .get(&ENTRY)
            .expect("dual guard fact");
        assert_eq!(
            fact.kind,
            BranchlessGuardKind::DualWrap32XorOrEqual {
                sum_expected: 100,
                difference_expected: 20,
            }
        );
        assert_eq!(fact.instruction_inventory.len(), 66);
        assert_eq!(fact.semantic_instructions.len(), 55);
        assert!(fact.validate_against(&artifact));
    }

    #[test]
    fn address_and_reconstruction_do_not_supply_authority() {
        let first = artifact(simple_block(ENTRY, 0xdead), 1);
        let rebuilt = artifact(simple_block(ENTRY, 0xdead), 1);
        assert_eq!(
            first.structured().branchless_guards,
            rebuilt.structured().branchless_guards
        );
        let relocated = artifact(simple_block(ENTRY + 0x4000, 0xdead), 1);
        let relocated_fact = relocated
            .structured()
            .branchless_guards
            .values()
            .next()
            .expect("relocated fact");
        assert_eq!(
            relocated_fact.kind,
            BranchlessGuardKind::SimpleSubtractEqual { expected: 0xdead }
        );

        let mut renamed_dead_seed = simple_block(ENTRY, 0xdead);
        let R2ILOp::Copy { dst, .. } = &mut renamed_dead_seed.ops[25] else {
            panic!("dead load seed copy");
        };
        *dst = Varnode::unique(0xfeed_0000, 8);
        let renamed = artifact(renamed_dead_seed, 1);
        assert_eq!(
            renamed
                .structured()
                .branchless_guards
                .get(&ENTRY)
                .expect("temporary-name-independent fact")
                .kind,
            BranchlessGuardKind::SimpleSubtractEqual { expected: 0xdead }
        );
    }

    #[test]
    fn interface_operation_and_overlay_mutations_fail_closed() {
        let block = simple_block(ENTRY, 0xdead);
        let wrong_interface = SourceFunctionInterface::new_exact_with_logical_types(
            b"branchless-guard-revision-1".to_vec(),
            "sysv_amd64",
            [SourceAbiParameterSpec::new(0, storage(56))],
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            [SourceLogicalValue::new(
                0,
                SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            )],
            Some(SourceLogicalValue::new(
                0,
                SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            )),
            Some(
                SourceTypeGraph::new(
                    [SourceType::new(0, SourceTypeKind::SignedInteger, 64, 64)],
                    [],
                )
                .expect("wrong type graph"),
            ),
        )
        .expect("coherent wrong interface");
        let wrong = SsaArtifact::raw_with_interface(&[block], Some(&arch()), wrong_interface)
            .expect("wrong-interface artifact");
        assert!(wrong.structured().branchless_guards.is_empty());

        let mut extra = simple_block(ENTRY, 0xdead);
        extra.ops.insert(
            24,
            R2ILOp::IntAdd {
                dst: Varnode::unique(0xfeed, 4),
                a: constant(1, 4),
                b: constant(2, 4),
            },
        );
        assert!(artifact(extra, 1).structured().branchless_guards.is_empty());

        let mut wrong_overlay = simple_block(ENTRY, 0xdead);
        wrong_overlay.ops[24] = R2ILOp::Copy {
            dst: register(0, 1),
            src: register(514, 1),
        };
        assert!(
            artifact(wrong_overlay, 1)
                .structured()
                .branchless_guards
                .is_empty()
        );
    }
}
