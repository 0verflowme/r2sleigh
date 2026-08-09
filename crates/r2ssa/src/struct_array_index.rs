//! Exact source facts for the pinned x86-64 `DemoStruct` array update.
//!
//! This recognizer is deliberately whole-function and name-independent.  It
//! accepts only the pinned O2 or O0 lowering whose source interface proves a
//! natural 56-byte aggregate made of fourteen signed 32-bit members.

use std::collections::{BTreeMap, BTreeSet};

use r2il::SpaceId;

use crate::StackAddressBase;
use crate::function::SSAFunction;
use crate::graph::{InstId, SsaGraph, ValueId};
use crate::machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION,
    SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCarrierKind, SourceFunctionReturn, SourceLogicalValue,
    SourceMachineContext, SourceStackSlotRole, SourceTypeKind,
};
use crate::op::SSAOp;
use crate::semantic::{
    CallBoundarySlot, CallBoundaryValueFact, SourceBoundaryFacts,
    SourceReturnRegisterCompositionFact, SourceReturnRegisterDefinitionFact,
};
use crate::var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar};
use crate::x86_frame::{X86StandardFrameFact, collect_standard_x86_frame};

pub const STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION: u32 = 1;

const RAX_OFFSET: u64 = 0;
const RCX_OFFSET: u64 = 8;
const RDX_OFFSET: u64 = 16;
const RSI_OFFSET: u64 = 48;
const RDI_OFFSET: u64 = 56;
const CF_OFFSET: u64 = 512;
const PF_OFFSET: u64 = 514;
const ZF_OFFSET: u64 = 518;
const SF_OFFSET: u64 = 519;
const OF_OFFSET: u64 = 523;
const MEMBER_COUNT: usize = 14;
const MEMBER_SIZE_BYTES: u32 = 4;
const STORED_MEMBER: u32 = 2;
const LOADED_MEMBER: u32 = 13;
const O2_OPERATION_COUNT: usize = 43;
const O2_SUFFIX: usize = 36;
const O0_OPERATION_COUNT: usize = 114;
const O0_SUFFIX: usize = 107;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructArrayIndexLowering {
    O2Register,
    O0ParameterHomes,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexTypeFact {
    pub signed_integer_type_id: u32,
    pub aggregate_type_id: u32,
    pub pointer_type_id: u32,
    pub aggregate_id: u32,
    pub stride_bytes: u64,
    pub align_bytes: u64,
    pub member_offsets_bytes: Box<[u64]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructArrayIndexParameterFact {
    pub index: u32,
    pub abi_storage: CanonicalStorageId,
    pub graph_storage: CanonicalStorageId,
    pub graph_value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexAbiFact {
    pub revision_identity: Box<[u8]>,
    pub parameters: Box<[StructArrayIndexParameterFact]>,
    pub parameter_logical_values: Box<[SourceLogicalValue]>,
    pub return_logical_value: SourceLogicalValue,
    pub return_storage: CanonicalStorageId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexScaleFact {
    pub signed_index: ValueId,
    pub sign_extend: InstId,
    pub extended_index: ValueId,
    pub wide_left_extend: InstId,
    pub wide_constant_extend: InstId,
    pub wide_multiply: InstId,
    pub scaled_multiply: InstId,
    pub scaled_index: ValueId,
    pub discarded_high_subpiece: InstId,
    pub product_sign_extend: InstId,
    pub overflow_compare: InstId,
    pub overflow_flag_copy: InstId,
    pub stride_bytes: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructArrayIndexAccessKind {
    Write,
    Read,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexAccessFact {
    pub kind: StructArrayIndexAccessKind,
    pub member_id: u32,
    pub member_offset_bytes: u64,
    pub size_bytes: u32,
    pub memory_space: SpaceId,
    pub base_add: InstId,
    pub unit_scale: InstId,
    pub address_add: InstId,
    pub address: ValueId,
    pub memory_inst: InstId,
    pub value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexFlagPacketFact {
    pub value: ValueId,
    pub sign: InstId,
    pub zero_equal: InstId,
    pub low_byte_mask: InstId,
    pub population_count: InstId,
    pub parity_mask: InstId,
    pub parity_equal: InstId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexHomeReloadFact {
    pub address_add: InstId,
    pub load: InstId,
    pub value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexHomeFact {
    pub parameter_index: u32,
    pub frame_pointer_offset: i64,
    pub entry_stack_offset: i64,
    pub size_bytes: u32,
    pub initializer_address_add: InstId,
    pub initializer_copy: InstId,
    pub initializer_store: InstId,
    pub stored_value: ValueId,
    pub reloads: Box<[StructArrayIndexHomeReloadFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexReturnFact {
    pub add: InstId,
    pub returned_value: ValueId,
    pub zero_extend: InstId,
    pub physical_full_register: ValueId,
    pub definition: SourceReturnRegisterDefinitionFact,
    pub composition: Option<SourceReturnRegisterCompositionFact>,
    pub return_target: ValueId,
    pub return_inst: InstId,
    pub wraps_at_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructArrayIndexFact {
    pub schema_version: u32,
    pub entry: u64,
    pub lowering: StructArrayIndexLowering,
    pub types: StructArrayIndexTypeFact,
    pub abi: StructArrayIndexAbiFact,
    pub frame: X86StandardFrameFact,
    pub homes: Box<[StructArrayIndexHomeFact]>,
    pub scales: Box<[StructArrayIndexScaleFact]>,
    pub value_preparation_instructions: Box<[InstId]>,
    pub accesses: Box<[StructArrayIndexAccessFact]>,
    pub address_flag_packets: Box<[StructArrayIndexFlagPacketFact]>,
    pub add_flags: StructArrayIndexFlagPacketFact,
    pub returned: StructArrayIndexReturnFact,
    pub instruction_inventory: Box<[InstId]>,
    pub semantic_instructions: Box<[InstId]>,
    pub frame_instructions: Box<[InstId]>,
}

impl StructArrayIndexFact {
    pub fn validate_against(&self, artifact: &crate::SsaArtifact) -> bool {
        self.schema_version == STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION
            && artifact.structured().struct_array_indexes.get(&self.entry) == Some(self)
    }
}

pub(crate) fn collect_struct_array_index_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> BTreeMap<u64, StructArrayIndexFact> {
    let mut facts = BTreeMap::new();
    let fact = collect_o2(function, graph, boundaries, machine)
        .or_else(|| collect_o0(function, graph, boundaries, machine));
    let Some(fact) = fact else {
        return facts;
    };
    facts.insert(fact.entry, fact);
    facts
}

fn collect_o2(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> Option<StructArrayIndexFact> {
    let [block_addr] = function.block_addrs() else {
        return None;
    };
    let block = function.get_block(*block_addr)?;
    if function.entry != *block_addr
        || !block.phis.is_empty()
        || !function.predecessors(*block_addr).is_empty()
        || !function.successors(*block_addr).is_empty()
        || !boundaries.calls.is_empty()
        || block.ops.len() != O2_OPERATION_COUNT
    {
        return None;
    }
    let types = collect_types(machine)?;
    let abi = collect_abi(graph, machine, &types, false)?;
    let frame = collect_standard_x86_frame(function, graph, machine, *block_addr, O2_SUFFIX)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(*block_addr, index);

    let value_input = graph.value(abi.parameters[2].graph_value)?.var.clone();
    let _value_copy = match op(4)? {
        SSAOp::Copy { dst, src }
            if value(graph, src)? == abi.parameters[2].graph_value
                && register_at(storage(graph, dst)?, RAX_OFFSET, 4) =>
        {
            dst
        }
        _ => return None,
    };
    let value_full = require_zext(op(5)?, &value_input)?;
    if !register_at(storage(graph, value_full)?, RAX_OFFSET, 8) {
        return None;
    }
    let scale = collect_scale(function, graph, machine, &abi, *block_addr)?;
    if scale.stride_bytes != types.stride_bytes {
        return None;
    }
    let stored = collect_address_and_store(
        function,
        graph,
        machine,
        &abi,
        &scale,
        *block_addr,
        15,
        STORED_MEMBER,
        &value_input,
    )?;
    let member_thirteen_offset = types
        .member_offsets_bytes
        .get(LOADED_MEMBER as usize)
        .copied()?;
    let (load_address, load_base_add, load_unit_scale, load_address_add) = collect_address(
        function,
        graph,
        &abi,
        &scale,
        *block_addr,
        20,
        member_thirteen_offset,
    )?;
    let load_indexes = [23usize, 25, 27];
    let reads = load_indexes
        .into_iter()
        .map(|index| {
            let SSAOp::Load { dst, addr, .. } = op(index)? else {
                return None;
            };
            if addr != &load_address || dst.size != MEMBER_SIZE_BYTES {
                return None;
            }
            Some(StructArrayIndexAccessFact {
                kind: StructArrayIndexAccessKind::Read,
                member_id: LOADED_MEMBER,
                member_offset_bytes: member_thirteen_offset,
                size_bytes: MEMBER_SIZE_BYTES,
                memory_space: machine.memory_space_at(*block_addr, index)?,
                base_add: load_base_add,
                unit_scale: load_unit_scale,
                address_add: load_address_add,
                address: value(graph, addr)?,
                memory_inst: inst(index)?,
                value: value(graph, dst)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    if reads
        .iter()
        .any(|read| read.memory_space != frame.memory_space)
        || stored.memory_space != frame.memory_space
        || reads
            .iter()
            .map(|read| read.value)
            .collect::<BTreeSet<_>>()
            .len()
            != 3
    {
        return None;
    }
    let load_vars = load_indexes
        .into_iter()
        .map(|index| match op(index)? {
            SSAOp::Load { dst, .. } => Some(dst),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    match (op(24)?, op(26)?, op(28)?) {
        (
            SSAOp::IntCarry { dst: cf, a, b },
            SSAOp::IntSCarry {
                dst: of,
                a: of_a,
                b: of_b,
            },
            SSAOp::IntAdd {
                dst,
                a: add_a,
                b: add_b,
            },
        ) if a == &value_input
            && b == load_vars[0]
            && of_a == &value_input
            && of_b == load_vars[1]
            && add_a == &value_input
            && add_b == load_vars[2]
            && dst.size == 4
            && register_at(storage(graph, cf)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1)
            && register_at(storage(graph, dst)?, RAX_OFFSET, 4) => {}
        _ => return None,
    }
    let returned_var = match op(28)? {
        SSAOp::IntAdd { dst, .. } => dst,
        _ => return None,
    };
    let return_full = require_zext_alias(op(29)?, graph, returned_var)?;
    if storage(graph, return_full)? != abi.return_storage {
        return None;
    }
    let add_flags =
        collect_flag_packet(function, graph, machine, *block_addr, 30, returned_var, 4)?;
    let returned = collect_return(
        function,
        graph,
        boundaries,
        *block_addr,
        28,
        returned_var,
        29,
        return_full,
        frame.return_target,
        abi.return_storage,
    )?;
    if returned.return_inst != frame.return_inst {
        return None;
    }

    let mut accesses = Vec::with_capacity(4);
    accesses.push(stored);
    accesses.extend(reads);
    if !accesses
        .windows(2)
        .all(|pair| pair[0].memory_inst < pair[1].memory_inst)
        || ranges_overlap(
            types.member_offsets_bytes[STORED_MEMBER as usize],
            MEMBER_SIZE_BYTES,
            types.member_offsets_bytes[LOADED_MEMBER as usize],
            MEMBER_SIZE_BYTES,
        )
    {
        return None;
    }
    let instruction_inventory = (0..O2_OPERATION_COUNT)
        .map(inst)
        .collect::<Option<Vec<_>>>()?;
    let semantic_instructions = (4..O2_SUFFIX).map(inst).collect::<Option<Vec<_>>>()?;
    let frame_instructions = frame.instructions.to_vec();
    let classified = semantic_instructions
        .iter()
        .chain(&frame_instructions)
        .copied()
        .collect::<BTreeSet<_>>();
    if instruction_inventory.len() != graph.insts.len()
        || classified.len() != instruction_inventory.len()
        || classified != instruction_inventory.iter().copied().collect()
    {
        return None;
    }
    Some(StructArrayIndexFact {
        schema_version: STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION,
        entry: *block_addr,
        lowering: StructArrayIndexLowering::O2Register,
        types,
        abi,
        frame,
        homes: Box::new([]),
        scales: Box::new([scale]),
        value_preparation_instructions: Box::new([inst(4)?, inst(5)?]),
        accesses: accesses.into_boxed_slice(),
        address_flag_packets: Box::new([]),
        add_flags,
        returned,
        instruction_inventory: instruction_inventory.into_boxed_slice(),
        semantic_instructions: semantic_instructions.into_boxed_slice(),
        frame_instructions: frame_instructions.into_boxed_slice(),
    })
}

fn collect_o0(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> Option<StructArrayIndexFact> {
    let [block_addr] = function.block_addrs() else {
        return None;
    };
    let block = function.get_block(*block_addr)?;
    if function.entry != *block_addr
        || !block.phis.is_empty()
        || !function.predecessors(*block_addr).is_empty()
        || !function.successors(*block_addr).is_empty()
        || !boundaries.calls.is_empty()
        || block.ops.len() != O0_OPERATION_COUNT
    {
        return None;
    }
    let types = collect_types(machine)?;
    let abi = collect_abi(graph, machine, &types, true)?;
    let frame = collect_standard_x86_frame(function, graph, machine, *block_addr, O0_SUFFIX)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(*block_addr, index);
    let frame_pointer = match op(3)? {
        SSAOp::Copy { dst, .. } => dst,
        _ => return None,
    };
    let arr_home = collect_home(
        function,
        graph,
        &abi,
        *block_addr,
        frame_pointer,
        0,
        -8,
        4,
        &[(17, 18), (43, 44), (70, 71)],
    )?;
    let idx_home = collect_home(
        function,
        graph,
        &abi,
        *block_addr,
        frame_pointer,
        1,
        -12,
        7,
        &[(20, 21), (46, 47), (73, 74)],
    )?;
    let value_home = collect_home(
        function,
        graph,
        &abi,
        *block_addr,
        frame_pointer,
        2,
        -16,
        10,
        &[(13, 14)],
    )?;
    if [
        arr_home.initializer_store,
        idx_home.initializer_store,
        value_home.initializer_store,
    ]
    .into_iter()
    .any(|store| {
        graph
            .op_site_for_inst(store)
            .and_then(|(addr, index)| machine.memory_space_at(addr, index))
            != Some(frame.memory_space)
    }) || arr_home
        .reloads
        .iter()
        .chain(&idx_home.reloads)
        .chain(&value_home.reloads)
        .any(|reload| {
            graph
                .op_site_for_inst(reload.load)
                .and_then(|(addr, index)| machine.memory_space_at(addr, index))
                != Some(frame.memory_space)
        })
    {
        return None;
    }
    let value_reload = graph.value(value_home.reloads[0].value)?.var.clone();
    match (op(15)?, op(16)?) {
        (
            SSAOp::Copy { dst, src },
            SSAOp::IntZExt {
                dst: full,
                src: zsrc,
            },
        ) if src == &value_reload
            && zsrc == &value_reload
            && register_at(storage(graph, dst)?, RCX_OFFSET, 4)
            && register_at(storage(graph, full)?, RCX_OFFSET, 8) => {}
        _ => return None,
    }

    let arr_reloads = arr_home
        .reloads
        .iter()
        .map(|reload| graph.value(reload.value).map(|value| value.var.clone()))
        .collect::<Option<Vec<_>>>()?;
    let idx_reloads = idx_home
        .reloads
        .iter()
        .map(|reload| graph.value(reload.value).map(|value| value.var.clone()))
        .collect::<Option<Vec<_>>>()?;
    let arr_carriers = [19usize, 45, 72]
        .into_iter()
        .zip(&arr_reloads)
        .map(|(index, reload)| match op(index)? {
            SSAOp::Copy { dst, src }
                if src == reload
                    && dst.size == 8
                    && register_at(
                        storage(graph, dst)?,
                        if index == 72 { RCX_OFFSET } else { RAX_OFFSET },
                        8,
                    ) =>
            {
                Some(dst.clone())
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let scale_starts = [22usize, 48, 75];
    let scale_offsets = [RDX_OFFSET, RCX_OFFSET, RDX_OFFSET];
    let scales = scale_starts
        .into_iter()
        .zip(scale_offsets)
        .zip(&idx_reloads)
        .map(|((start, offset), reload)| {
            collect_scale_packet(function, graph, machine, *block_addr, start, reload, offset)
        })
        .collect::<Option<Vec<_>>>()?;
    if scales
        .iter()
        .any(|scale| scale.stride_bytes != types.stride_bytes)
    {
        return None;
    }
    let address_packets = [(31usize, 34usize), (57, 60), (84, 87)]
        .into_iter()
        .zip(&arr_carriers)
        .zip(&scales)
        .map(|(((sum_start, flag_start), base), scale)| {
            let scaled = &graph.value(scale.scaled_index)?.var;
            collect_address_sum_packet(
                function,
                graph,
                machine,
                *block_addr,
                sum_start,
                flag_start,
                base,
                scaled,
            )
        })
        .collect::<Option<Vec<_>>>()?;
    let address_values = [33usize, 59, 86]
        .into_iter()
        .map(|index| match op(index)? {
            SSAOp::IntAdd { dst, .. } => Some(dst.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let final_address_indexes = [40usize, 66, 93];
    let member_offsets = [8u64, 8, 52];
    let final_addresses = final_address_indexes
        .into_iter()
        .zip(member_offsets)
        .zip(&address_values)
        .map(|((index, offset), base)| match op(index)? {
            SSAOp::IntAdd { dst, a, b } if a == base && constant(b, offset, 8) && dst.size == 8 => {
                Some(dst.clone())
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let stored_value = match op(41)? {
        SSAOp::Copy { dst, src } if src == &value_reload && dst.size == 4 => dst,
        _ => return None,
    };
    match op(42)? {
        SSAOp::Store { addr, val, .. } if addr == &final_addresses[0] && val == stored_value => {}
        _ => return None,
    }
    let member_two = match op(67)? {
        SSAOp::Load { dst, addr, .. } if addr == &final_addresses[1] && dst.size == 4 => dst,
        _ => return None,
    };
    match (op(68)?, op(69)?) {
        (
            SSAOp::Copy { dst, src },
            SSAOp::IntZExt {
                dst: full,
                src: zsrc,
            },
        ) if src == member_two
            && zsrc == member_two
            && register_at(storage(graph, dst)?, RAX_OFFSET, 4)
            && register_at(storage(graph, full)?, RAX_OFFSET, 8) => {}
        _ => return None,
    }
    let member_thirteen_indexes = [94usize, 96, 98];
    let member_thirteen = member_thirteen_indexes
        .into_iter()
        .map(|index| match op(index)? {
            SSAOp::Load { dst, addr, .. } if addr == &final_addresses[2] && dst.size == 4 => {
                Some(dst)
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let returned_var = match (op(95)?, op(97)?, op(99)?) {
        (
            SSAOp::IntCarry { dst: cf, a, b },
            SSAOp::IntSCarry {
                dst: of,
                a: of_a,
                b: of_b,
            },
            SSAOp::IntAdd {
                dst,
                a: add_a,
                b: add_b,
            },
        ) if a == member_two
            && b == member_thirteen[0]
            && of_a == member_two
            && of_b == member_thirteen[1]
            && add_a == member_two
            && add_b == member_thirteen[2]
            && register_at(storage(graph, cf)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1)
            && register_at(storage(graph, dst)?, RAX_OFFSET, 4) =>
        {
            dst
        }
        _ => return None,
    };
    let return_full = require_zext_alias(op(100)?, graph, returned_var)?;
    if storage(graph, return_full)? != abi.return_storage {
        return None;
    }
    let add_flags =
        collect_flag_packet(function, graph, machine, *block_addr, 101, returned_var, 4)?;
    let returned = collect_return(
        function,
        graph,
        boundaries,
        *block_addr,
        99,
        returned_var,
        100,
        return_full,
        frame.return_target,
        abi.return_storage,
    )?;
    if returned.return_inst != frame.return_inst {
        return None;
    }
    let access_specs = [
        (
            StructArrayIndexAccessKind::Write,
            STORED_MEMBER,
            42usize,
            stored_value,
        ),
        (
            StructArrayIndexAccessKind::Read,
            STORED_MEMBER,
            67usize,
            member_two,
        ),
        (
            StructArrayIndexAccessKind::Read,
            LOADED_MEMBER,
            94usize,
            member_thirteen[0],
        ),
        (
            StructArrayIndexAccessKind::Read,
            LOADED_MEMBER,
            96usize,
            member_thirteen[1],
        ),
        (
            StructArrayIndexAccessKind::Read,
            LOADED_MEMBER,
            98usize,
            member_thirteen[2],
        ),
    ];
    let accesses = access_specs
        .into_iter()
        .map(|(kind, member_id, memory_index, access_value)| {
            let address_group = if memory_index <= 42 {
                0
            } else if memory_index == 67 {
                1
            } else {
                2
            };
            Some(StructArrayIndexAccessFact {
                kind,
                member_id,
                member_offset_bytes: types.member_offsets_bytes[member_id as usize],
                size_bytes: MEMBER_SIZE_BYTES,
                memory_space: machine.memory_space_at(*block_addr, memory_index)?,
                base_add: inst([33, 59, 86][address_group])?,
                unit_scale: scales[address_group].scaled_multiply,
                address_add: inst(final_address_indexes[address_group])?,
                address: value(graph, &final_addresses[address_group])?,
                memory_inst: inst(memory_index)?,
                value: value(graph, access_value)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    if accesses
        .iter()
        .any(|access| access.memory_space != frame.memory_space)
        || !accesses
            .windows(2)
            .all(|pair| pair[0].memory_inst < pair[1].memory_inst)
        || accesses
            .iter()
            .skip(2)
            .map(|access| access.value)
            .collect::<BTreeSet<_>>()
            .len()
            != 3
        || ranges_overlap(8, 4, 52, 4)
    {
        return None;
    }
    let instruction_inventory = (0..O0_OPERATION_COUNT)
        .map(inst)
        .collect::<Option<Vec<_>>>()?;
    let semantic_instructions = (4..O0_SUFFIX).map(inst).collect::<Option<Vec<_>>>()?;
    let frame_instructions = frame.instructions.to_vec();
    let classified = semantic_instructions
        .iter()
        .chain(&frame_instructions)
        .copied()
        .collect::<BTreeSet<_>>();
    if instruction_inventory.len() != graph.insts.len()
        || classified.len() != instruction_inventory.len()
        || classified != instruction_inventory.iter().copied().collect()
    {
        return None;
    }
    Some(StructArrayIndexFact {
        schema_version: STRUCT_ARRAY_INDEX_FACT_SCHEMA_VERSION,
        entry: *block_addr,
        lowering: StructArrayIndexLowering::O0ParameterHomes,
        types,
        abi,
        frame,
        homes: vec![arr_home, idx_home, value_home].into_boxed_slice(),
        scales: scales.into_boxed_slice(),
        value_preparation_instructions: [15usize, 16, 41, 68, 69]
            .into_iter()
            .map(inst)
            .collect::<Option<Vec<_>>>()?
            .into_boxed_slice(),
        accesses: accesses.into_boxed_slice(),
        address_flag_packets: address_packets.into_boxed_slice(),
        add_flags,
        returned,
        instruction_inventory: instruction_inventory.into_boxed_slice(),
        semantic_instructions: semantic_instructions.into_boxed_slice(),
        frame_instructions: frame_instructions.into_boxed_slice(),
    })
}

fn collect_types(machine: &SourceMachineContext) -> Option<StructArrayIndexTypeFact> {
    let interface = machine.function_interface()?;
    let graph = interface.type_graph()?;
    if graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || graph.types().len() != 3
        || graph.aggregates().len() != 1
    {
        return None;
    }
    let aggregate = &graph.aggregates()[0];
    let signed = graph
        .types()
        .iter()
        .filter(|source_type| {
            source_type.kind() == SourceTypeKind::SignedInteger
                && source_type.size_bits() == 32
                && source_type.align_bits() == 32
        })
        .collect::<Vec<_>>();
    let [signed] = signed.as_slice() else {
        return None;
    };
    let aggregate_types = graph
        .types()
        .iter()
        .filter(|source_type| {
            source_type.kind()
                == (SourceTypeKind::Struct {
                    aggregate_id: aggregate.id(),
                })
        })
        .collect::<Vec<_>>();
    let [aggregate_type] = aggregate_types.as_slice() else {
        return None;
    };
    let pointers = graph
        .types()
        .iter()
        .filter(|source_type| {
            source_type.kind()
                == (SourceTypeKind::Pointer {
                    target_type_id: aggregate_type.id(),
                })
                && source_type.size_bits() == 64
                && source_type.align_bits() == 64
        })
        .collect::<Vec<_>>();
    let [pointer] = pointers.as_slice() else {
        return None;
    };
    if aggregate.type_id() != aggregate_type.id()
        || aggregate.size_bits() != 56 * 8
        || aggregate.align_bits() != 4 * 8
        || aggregate.members().len() != MEMBER_COUNT
        || aggregate
            .members()
            .iter()
            .enumerate()
            .any(|(index, member)| {
                member.member_id() != index as u32
                    || member.type_id() != signed.id()
                    || member.offset_bits() != (index as u64) * 32
                    || member.size_bits() != 32
            })
    {
        return None;
    }
    let stride_bytes = aggregate.size_bits().checked_div(8)?;
    Some(StructArrayIndexTypeFact {
        signed_integer_type_id: signed.id(),
        aggregate_type_id: aggregate_type.id(),
        pointer_type_id: pointer.id(),
        aggregate_id: aggregate.id(),
        stride_bytes,
        align_bytes: aggregate.align_bits() / 8,
        member_offsets_bytes: aggregate
            .members()
            .iter()
            .map(|member| member.offset_bits() / 8)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_home(
    function: &SSAFunction,
    graph: &SsaGraph,
    abi: &StructArrayIndexAbiFact,
    block_addr: u64,
    frame_pointer: &SSAVar,
    parameter_index: usize,
    frame_pointer_offset: i64,
    initializer_start: usize,
    reload_sites: &[(usize, usize)],
) -> Option<StructArrayIndexHomeFact> {
    let block = function.get_block(block_addr)?;
    let parameter = abi.parameters.get(parameter_index)?;
    let source = &graph.value(parameter.graph_value)?.var;
    let expected_size = parameter.graph_storage.size;
    let address = match block.ops.get(initializer_start)? {
        SSAOp::IntAdd { dst, a, b }
            if a == frame_pointer
                && constant(b, frame_pointer_offset as u64, 8)
                && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let copied = match block.ops.get(initializer_start + 1)? {
        SSAOp::Copy { dst, src } if src == source && dst.size == expected_size => dst,
        _ => return None,
    };
    match block.ops.get(initializer_start + 2)? {
        SSAOp::Store { addr, val, .. } if addr == address && val == copied => {}
        _ => return None,
    }
    let reloads = reload_sites
        .iter()
        .map(|(address_index, load_index)| {
            let reload_address = match block.ops.get(*address_index)? {
                SSAOp::IntAdd { dst, a, b }
                    if a == frame_pointer
                        && constant(b, frame_pointer_offset as u64, 8)
                        && dst.size == 8 =>
                {
                    dst
                }
                _ => return None,
            };
            let loaded = match block.ops.get(*load_index)? {
                SSAOp::Load { dst, addr, .. }
                    if addr == reload_address && dst.size == expected_size =>
                {
                    dst
                }
                _ => return None,
            };
            Some(StructArrayIndexHomeReloadFact {
                address_add: graph.inst_id_for_op_site(block_addr, *address_index)?,
                load: graph.inst_id_for_op_site(block_addr, *load_index)?,
                value: value(graph, loaded)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(StructArrayIndexHomeFact {
        parameter_index: parameter.index,
        frame_pointer_offset,
        entry_stack_offset: frame_pointer_offset.checked_sub(8)?,
        size_bytes: expected_size,
        initializer_address_add: graph.inst_id_for_op_site(block_addr, initializer_start)?,
        initializer_copy: graph.inst_id_for_op_site(block_addr, initializer_start + 1)?,
        initializer_store: graph.inst_id_for_op_site(block_addr, initializer_start + 2)?,
        stored_value: value(graph, copied)?,
        reloads: reloads.into_boxed_slice(),
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_scale_packet(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    block_addr: u64,
    start: usize,
    signed_index: &SSAVar,
    carrier_offset: u64,
) -> Option<StructArrayIndexScaleFact> {
    let block = function.get_block(block_addr)?;
    let op = |relative| block.ops.get(start + relative);
    let inst = |relative| graph.inst_id_for_op_site(block_addr, start + relative);
    let extended = match op(0)? {
        SSAOp::IntSExt { dst, src }
            if src == signed_index
                && dst.size == 8
                && register_at(storage(graph, dst)?, carrier_offset, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let wide_left = match op(1)? {
        SSAOp::IntSExt { dst, src } if src == extended && dst.size == 16 => dst,
        _ => return None,
    };
    let wide_constant = match op(2)? {
        SSAOp::IntSExt { dst, src } if constant(src, 56, 8) && dst.size == 16 => dst,
        _ => return None,
    };
    let wide_product = match op(3)? {
        SSAOp::IntMult { dst, a, b } if a == wide_left && b == wide_constant && dst.size == 16 => {
            dst
        }
        _ => return None,
    };
    let scaled = match op(4)? {
        SSAOp::IntMult { dst, a, b }
            if a == extended
                && constant(b, 56, 8)
                && register_at(storage(graph, dst)?, carrier_offset, 8) =>
        {
            dst
        }
        _ => return None,
    };
    match op(5)? {
        SSAOp::Subpiece { dst, src, offset }
            if src == wide_product && *offset == 8 && dst.size == 8 => {}
        _ => return None,
    }
    let sign_extended_product = match op(6)? {
        SSAOp::IntSExt { dst, src } if src == scaled && dst.size == 16 => dst,
        _ => return None,
    };
    let overflow = match op(7)? {
        SSAOp::IntNotEqual { dst, a, b }
            if a == sign_extended_product
                && b == wide_product
                && register_at(storage(graph, dst)?, CF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    match op(8)? {
        SSAOp::Copy { dst, src }
            if src == overflow && register_at(storage(graph, dst)?, OF_OFFSET, 1) => {}
        _ => return None,
    }
    Some(StructArrayIndexScaleFact {
        signed_index: value(graph, signed_index)?,
        sign_extend: inst(0)?,
        extended_index: value(graph, extended)?,
        wide_left_extend: inst(1)?,
        wide_constant_extend: inst(2)?,
        wide_multiply: inst(3)?,
        scaled_multiply: inst(4)?,
        scaled_index: value(graph, scaled)?,
        discarded_high_subpiece: inst(5)?,
        product_sign_extend: inst(6)?,
        overflow_compare: inst(7)?,
        overflow_flag_copy: inst(8)?,
        stride_bytes: 56,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_address_sum_packet(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    block_addr: u64,
    sum_start: usize,
    flag_start: usize,
    base: &SSAVar,
    scaled: &SSAVar,
) -> Option<StructArrayIndexFlagPacketFact> {
    let block = function.get_block(block_addr)?;
    match (
        block.ops.get(sum_start)?,
        block.ops.get(sum_start + 1)?,
        block.ops.get(sum_start + 2)?,
    ) {
        (
            SSAOp::IntCarry { dst: cf, a, b },
            SSAOp::IntSCarry {
                dst: of,
                a: of_a,
                b: of_b,
            },
            SSAOp::IntAdd {
                dst,
                a: add_a,
                b: add_b,
            },
        ) if a == base
            && b == scaled
            && of_a == base
            && of_b == scaled
            && add_a == base
            && add_b == scaled
            && register_at(storage(graph, cf)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1)
            && dst.size == 8 =>
        {
            collect_flag_packet(function, graph, machine, block_addr, flag_start, dst, 8)
        }
        _ => None,
    }
}

fn collect_abi(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    types: &StructArrayIndexTypeFact,
    expect_homes: bool,
) -> Option<StructArrayIndexAbiFact> {
    if machine.schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
        || !machine.abi_model().is_available()
        || !machine.abi_model().is_coherent()
        || !machine.memory_model().is_available()
        || !machine.memory_model().is_coherent()
    {
        return None;
    }
    let interface = machine.function_interface()?;
    let return_logical_value = interface.return_logical_value()?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity().is_empty()
        || interface.calling_convention() != "sysv_amd64"
        || !interface.stack_slot_roles_complete()
        || interface.parameters().len() != 3
        || interface.parameter_logical_values().len() != 3
        || interface.parameters()[0].index() != 0
        || interface.parameters()[1].index() != 1
        || interface.parameters()[2].index() != 2
        || !register_at(interface.parameters()[0].storage(), RDI_OFFSET, 8)
        || !register_at(interface.parameters()[1].storage(), RSI_OFFSET, 8)
        || !register_at(interface.parameters()[2].storage(), RDX_OFFSET, 8)
    {
        return None;
    }
    if expect_homes {
        let offsets = [-16i64, -12, -8];
        let sizes = [4u32, 4, 8];
        let parameter_indexes = [2u32, 1, 0];
        if interface.stack_slots().len() != 3
            || interface
                .stack_slots()
                .iter()
                .enumerate()
                .any(|(index, slot)| {
                    let parameter_index = parameter_indexes[index];
                    slot.base() != StackAddressBase::FramePointer
                        || !register_at(slot.base_storage(), 40, 8)
                        || slot.offset() != offsets[index]
                        || slot.size_bytes() != sizes[index]
                        || slot.role()
                            != (SourceStackSlotRole::ParameterHome {
                                parameter_index,
                                home_storage: interface.parameters()[parameter_index as usize]
                                    .storage(),
                            })
                })
        {
            return None;
        }
    } else if !interface.stack_slots().is_empty() {
        return None;
    }
    let logical = interface.parameter_logical_values();
    if logical[0].type_id() != types.pointer_type_id
        || logical[0].carrier().kind() != SourceCarrierKind::Full
        || logical[0].carrier().offset_bits() != 0
        || logical[0].carrier().size_bits() != 64
        || logical[1..].iter().any(|value| {
            value.type_id() != types.signed_integer_type_id
                || value.carrier().kind() != SourceCarrierKind::LowBits
                || value.carrier().offset_bits() != 0
                || value.carrier().size_bits() != 32
        })
        || return_logical_value.type_id() != types.signed_integer_type_id
        || return_logical_value.carrier().kind() != SourceCarrierKind::LowBits
        || return_logical_value.carrier().offset_bits() != 0
        || return_logical_value.carrier().size_bits() != 32
    {
        return None;
    }
    let return_storage = match interface.return_kind() {
        SourceFunctionReturn::Register { storage } if register_at(storage, RAX_OFFSET, 8) => {
            storage
        }
        _ => return None,
    };
    let expected = [
        (0, interface.parameters()[0].storage(), RDI_OFFSET, 8),
        (1, interface.parameters()[1].storage(), RSI_OFFSET, 4),
        (2, interface.parameters()[2].storage(), RDX_OFFSET, 4),
    ];
    let parameters = expected
        .into_iter()
        .map(|(index, abi_storage, offset, size)| {
            let graph_storage = CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset,
                size,
            };
            let candidates = graph
                .values
                .iter()
                .filter(|value| {
                    graph.def_inst(value.id).is_none()
                        && value.var.version == 0
                        && value.canonical_storage == Some(graph_storage)
                })
                .map(|value| value.id)
                .collect::<Vec<_>>();
            let [graph_value] = candidates.as_slice() else {
                return None;
            };
            Some(StructArrayIndexParameterFact {
                index,
                abi_storage,
                graph_storage,
                graph_value: *graph_value,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(StructArrayIndexAbiFact {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        parameters: parameters.into_boxed_slice(),
        parameter_logical_values: logical.to_vec().into_boxed_slice(),
        return_logical_value,
        return_storage,
    })
}

fn collect_scale(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    abi: &StructArrayIndexAbiFact,
    block_addr: u64,
) -> Option<StructArrayIndexScaleFact> {
    let block = function.get_block(block_addr)?;
    let op = |index| block.ops.get(index);
    let inst = |index| graph.inst_id_for_op_site(block_addr, index);
    let index_var = &graph.value(abi.parameters[1].graph_value)?.var;
    let extended = match op(6)? {
        SSAOp::IntSExt { dst, src }
            if src == index_var
                && dst.size == 8
                && register_at(storage(graph, dst)?, RCX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let wide_left = match op(7)? {
        SSAOp::IntSExt { dst, src } if src == extended && dst.size == 16 => dst,
        _ => return None,
    };
    let wide_constant = match op(8)? {
        SSAOp::IntSExt { dst, src } if constant(src, 56, 8) && dst.size == 16 => dst,
        _ => return None,
    };
    let wide_product = match op(9)? {
        SSAOp::IntMult { dst, a, b } if a == wide_left && b == wide_constant && dst.size == 16 => {
            dst
        }
        _ => return None,
    };
    let scaled = match op(10)? {
        SSAOp::IntMult { dst, a, b }
            if a == extended
                && constant(b, 56, 8)
                && dst.size == 8
                && register_at(storage(graph, dst)?, RCX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    match op(11)? {
        SSAOp::Subpiece { dst, src, offset }
            if src == wide_product && *offset == 8 && dst.size == 8 => {}
        _ => return None,
    }
    let sign_extended_product = match op(12)? {
        SSAOp::IntSExt { dst, src } if src == scaled && dst.size == 16 => dst,
        _ => return None,
    };
    let overflow = match op(13)? {
        SSAOp::IntNotEqual { dst, a, b }
            if a == sign_extended_product
                && b == wide_product
                && register_at(storage(graph, dst)?, CF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    match op(14)? {
        SSAOp::Copy { dst, src }
            if src == overflow && register_at(storage(graph, dst)?, OF_OFFSET, 1) => {}
        _ => return None,
    }
    Some(StructArrayIndexScaleFact {
        signed_index: abi.parameters[1].graph_value,
        sign_extend: inst(6)?,
        extended_index: value(graph, extended)?,
        wide_left_extend: inst(7)?,
        wide_constant_extend: inst(8)?,
        wide_multiply: inst(9)?,
        scaled_multiply: inst(10)?,
        scaled_index: value(graph, scaled)?,
        discarded_high_subpiece: inst(11)?,
        product_sign_extend: inst(12)?,
        overflow_compare: inst(13)?,
        overflow_flag_copy: inst(14)?,
        stride_bytes: 56,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_address_and_store(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    abi: &StructArrayIndexAbiFact,
    scale: &StructArrayIndexScaleFact,
    block_addr: u64,
    start: usize,
    member_id: u32,
    value_input: &SSAVar,
) -> Option<StructArrayIndexAccessFact> {
    let member_offset = u64::from(member_id).checked_mul(u64::from(MEMBER_SIZE_BYTES))?;
    let (address, base_add, unit_scale, address_add) = collect_address(
        function,
        graph,
        abi,
        scale,
        block_addr,
        start,
        member_offset,
    )?;
    let block = function.get_block(block_addr)?;
    let copied = match block.ops.get(start + 3)? {
        SSAOp::Copy { dst, src } if src == value_input && dst.size == MEMBER_SIZE_BYTES => dst,
        _ => return None,
    };
    match block.ops.get(start + 4)? {
        SSAOp::Store { addr, val, .. } if addr == &address && val == copied => {}
        _ => return None,
    }
    Some(StructArrayIndexAccessFact {
        kind: StructArrayIndexAccessKind::Write,
        member_id,
        member_offset_bytes: member_offset,
        size_bytes: MEMBER_SIZE_BYTES,
        memory_space: machine.memory_space_at(block_addr, start + 4)?,
        base_add,
        unit_scale,
        address_add,
        address: value(graph, &address)?,
        memory_inst: graph.inst_id_for_op_site(block_addr, start + 4)?,
        value: value(graph, copied)?,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_address(
    function: &SSAFunction,
    graph: &SsaGraph,
    abi: &StructArrayIndexAbiFact,
    scale: &StructArrayIndexScaleFact,
    block_addr: u64,
    start: usize,
    member_offset: u64,
) -> Option<(SSAVar, InstId, InstId, InstId)> {
    let block = function.get_block(block_addr)?;
    let pointer = &graph.value(abi.parameters[0].graph_value)?.var;
    let scaled = &graph.value(scale.scaled_index)?.var;
    let base = match block.ops.get(start)? {
        SSAOp::IntAdd { dst, a, b }
            if constant(a, member_offset, 8) && b == pointer && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let unit_scaled = match block.ops.get(start + 1)? {
        SSAOp::IntMult { dst, a, b } if a == scaled && constant(b, 1, 8) && dst.size == 8 => dst,
        _ => return None,
    };
    let address = match block.ops.get(start + 2)? {
        SSAOp::IntAdd { dst, a, b } if a == base && b == unit_scaled && dst.size == 8 => dst,
        _ => return None,
    };
    Some((
        address.clone(),
        graph.inst_id_for_op_site(block_addr, start)?,
        graph.inst_id_for_op_site(block_addr, start + 1)?,
        graph.inst_id_for_op_site(block_addr, start + 2)?,
    ))
}

fn collect_flag_packet(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    block_addr: u64,
    start: usize,
    input: &SSAVar,
    input_size: u32,
) -> Option<StructArrayIndexFlagPacketFact> {
    let block = function.get_block(block_addr)?;
    let op = |relative| block.ops.get(start + relative);
    let inst = |relative| graph.inst_id_for_op_site(block_addr, start + relative);
    match op(0)? {
        SSAOp::IntSLess { dst, a, b }
            if a == input
                && constant(b, 0, input_size)
                && register_at(storage(graph, dst)?, SF_OFFSET, 1) => {}
        _ => return None,
    }
    match op(1)? {
        SSAOp::IntEqual { dst, a, b }
            if a == input
                && constant(b, 0, input_size)
                && register_at(storage(graph, dst)?, ZF_OFFSET, 1) => {}
        _ => return None,
    }
    let masked = match op(2)? {
        SSAOp::IntAnd { dst, a, b } if a == input && constant(b, 0xff, input_size) => dst,
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
    Some(StructArrayIndexFlagPacketFact {
        value: value(graph, input)?,
        sign: inst(0)?,
        zero_equal: inst(1)?,
        low_byte_mask: inst(2)?,
        population_count: inst(3)?,
        parity_mask: inst(4)?,
        parity_equal: inst(5)?,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_return(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    block_addr: u64,
    add_index: usize,
    returned_var: &SSAVar,
    zext_index: usize,
    return_full: &SSAVar,
    return_target: ValueId,
    return_storage: CanonicalStorageId,
) -> Option<StructArrayIndexReturnFact> {
    let return_index = function.get_block(block_addr)?.ops.len().checked_sub(1)?;
    let return_inst = graph.inst_id_for_op_site(block_addr, return_index)?;
    let boundary = boundaries.returns.get(&return_inst)?;
    let zero_extend = graph.inst_id_for_op_site(block_addr, zext_index)?;
    let physical_full_register = value(graph, return_full)?;
    let definition = SourceReturnRegisterDefinitionFact {
        storage: return_storage,
        value: physical_full_register,
        producer: zero_extend,
    };
    if !boundary.complete
        || boundary.values.as_slice()
            != [CallBoundaryValueFact {
                slot: CallBoundarySlot::Register {
                    index: 0,
                    storage: return_storage,
                },
                value: physical_full_register,
            }]
        || !boundary.register_compositions.is_empty()
    {
        return None;
    }
    Some(StructArrayIndexReturnFact {
        add: graph.inst_id_for_op_site(block_addr, add_index)?,
        returned_value: value(graph, returned_var)?,
        zero_extend,
        physical_full_register,
        definition,
        composition: None,
        return_target,
        return_inst,
        wraps_at_bits: 32,
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

fn require_zext<'a>(op: &'a SSAOp, input: &SSAVar) -> Option<&'a SSAVar> {
    let SSAOp::IntZExt { dst, src } = op else {
        return None;
    };
    (src == input && src.size == 4 && dst.size == 8).then_some(dst)
}

fn ranges_overlap(left: u64, left_size: u32, right: u64, right_size: u32) -> bool {
    let Some(left_end) = left.checked_add(u64::from(left_size)) else {
        return true;
    };
    let Some(right_end) = right.checked_add(u64::from(right_size)) else {
        return true;
    };
    left < right_end && right < left_end
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
        SourceAbiParameterSpec, SourceAggregateLayout, SourceAggregateMember,
        SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
        SourceStackSlotSpec, SourceType, SourceTypeGraph, SsaArtifact, StackAddressBase,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(7);
    const ENTRY: u64 = 0x1000_00ab0;

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

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-struct-array-index-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("EAX", RAX_OFFSET, 4),
            ("RAX", RAX_OFFSET, 8),
            ("ECX", RCX_OFFSET, 4),
            ("RCX", RCX_OFFSET, 8),
            ("EDX", RDX_OFFSET, 4),
            ("RDX", RDX_OFFSET, 8),
            ("RSP", 32, 8),
            ("RBP", 40, 8),
            ("ESI", RSI_OFFSET, 4),
            ("RSI", RSI_OFFSET, 8),
            ("RDI", RDI_OFFSET, 8),
            ("CF", CF_OFFSET, 1),
            ("PF", PF_OFFSET, 1),
            ("ZF", ZF_OFFSET, 1),
            ("SF", SF_OFFSET, 1),
            ("OF", OF_OFFSET, 1),
            ("RIP", 648, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn type_graph(name_seed: &str) -> SourceTypeGraph {
        let members = (0..MEMBER_COUNT).map(|index| {
            SourceAggregateMember::new(
                index as u32,
                0,
                index as u64 * 32,
                32,
                format!("{name_seed}_member_{index}"),
            )
        });
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Struct { aggregate_id: 0 }, 448, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 1 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                1,
                448,
                32,
                format!("{name_seed}_aggregate"),
                members,
            )],
        )
        .expect("natural struct-array graph")
    }

    fn interface(name_seed: &str) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
                SourceAbiParameterSpec::new(2, storage(RDX_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX_OFFSET),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(type_graph(name_seed)),
        )
        .expect("exact struct-array interface")
    }

    fn o0_interface(name_seed: &str) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
                SourceAbiParameterSpec::new(2, storage(RDX_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX_OFFSET),
            },
            [
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(40),
                    -8,
                    8,
                    0,
                    storage(RDI_OFFSET),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(40),
                    -12,
                    4,
                    1,
                    storage(RSI_OFFSET),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    storage(40),
                    -16,
                    4,
                    2,
                    storage(RDX_OFFSET),
                ),
            ],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(type_graph(name_seed)),
        )
        .expect("exact O0 struct-array interface")
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

    fn push_flag_packet(block: &mut R2ILBlock, next: &mut u64, input: Varnode) {
        push_flag_packet_sized(block, next, input, 4);
    }

    fn push_flag_packet_sized(
        block: &mut R2ILBlock,
        next: &mut u64,
        input: Varnode,
        input_size: u32,
    ) {
        block.push(R2ILOp::IntSLess {
            dst: register(SF_OFFSET, 1),
            a: input.clone(),
            b: constant(0, input_size),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(ZF_OFFSET, 1),
            a: input.clone(),
            b: constant(0, input_size),
        });
        let low = unique(next, input_size);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: input,
            b: constant(0xff, input_size),
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
            dst: register(PF_OFFSET, 1),
            a: parity,
            b: constant(0, 1),
        });
    }

    fn push_frame_suffix(block: &mut R2ILBlock, next: &mut u64) {
        let restored = unique(next, 8);
        block.push(R2ILOp::Copy {
            dst: restored.clone(),
            src: constant(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: restored.clone(),
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
            src: restored,
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

    fn push_home(block: &mut R2ILBlock, next: &mut u64, offset: i64, source: Varnode) {
        let address = unique(next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(40, 8),
            b: constant(offset as u64, 8),
        });
        let copied = unique(next, source.size);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: source,
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: address,
            val: copied,
        });
    }

    fn reload_home(block: &mut R2ILBlock, next: &mut u64, offset: i64, size: u32) -> Varnode {
        let address = unique(next, 8);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(40, 8),
            b: constant(offset as u64, 8),
        });
        let loaded = unique(next, size);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: DATA,
            addr: address,
        });
        loaded
    }

    fn push_scale_packet(
        block: &mut R2ILBlock,
        next: &mut u64,
        input: Varnode,
        carrier_offset: u64,
    ) {
        block.push(R2ILOp::IntSExt {
            dst: register(carrier_offset, 8),
            src: input,
        });
        let wide_index = unique(next, 16);
        block.push(R2ILOp::IntSExt {
            dst: wide_index.clone(),
            src: register(carrier_offset, 8),
        });
        let wide_stride = unique(next, 16);
        block.push(R2ILOp::IntSExt {
            dst: wide_stride.clone(),
            src: constant(56, 8),
        });
        let wide_product = unique(next, 16);
        block.push(R2ILOp::IntMult {
            dst: wide_product.clone(),
            a: wide_index,
            b: wide_stride,
        });
        block.push(R2ILOp::IntMult {
            dst: register(carrier_offset, 8),
            a: register(carrier_offset, 8),
            b: constant(56, 8),
        });
        block.push(R2ILOp::Subpiece {
            dst: unique(next, 8),
            src: wide_product.clone(),
            offset: 8,
        });
        let extended = unique(next, 16);
        block.push(R2ILOp::IntSExt {
            dst: extended.clone(),
            src: register(carrier_offset, 8),
        });
        block.push(R2ILOp::IntNotEqual {
            dst: register(CF_OFFSET, 1),
            a: extended,
            b: wide_product,
        });
        block.push(R2ILOp::Copy {
            dst: register(OF_OFFSET, 1),
            src: register(CF_OFFSET, 1),
        });
    }

    fn push_address_sum(
        block: &mut R2ILBlock,
        next: &mut u64,
        base: Varnode,
        scaled_offset: u64,
        destination_offset: u64,
    ) {
        block.push(R2ILOp::IntCarry {
            dst: register(CF_OFFSET, 1),
            a: base.clone(),
            b: register(scaled_offset, 8),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF_OFFSET, 1),
            a: base.clone(),
            b: register(scaled_offset, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: register(destination_offset, 8),
            a: base,
            b: register(scaled_offset, 8),
        });
        push_flag_packet_sized(block, next, register(destination_offset, 8), 8);
    }

    fn o2_block(entry: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 23);
        let mut next = 0x10000;
        push_frame_prefix(&mut block, &mut next);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 4),
            src: register(RDX_OFFSET, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: register(RDX_OFFSET, 4),
        });
        block.push(R2ILOp::IntSExt {
            dst: register(RCX_OFFSET, 8),
            src: register(RSI_OFFSET, 4),
        });
        let wide_index = unique(&mut next, 16);
        block.push(R2ILOp::IntSExt {
            dst: wide_index.clone(),
            src: register(RCX_OFFSET, 8),
        });
        let wide_stride = unique(&mut next, 16);
        block.push(R2ILOp::IntSExt {
            dst: wide_stride.clone(),
            src: constant(56, 8),
        });
        let wide_product = unique(&mut next, 16);
        block.push(R2ILOp::IntMult {
            dst: wide_product.clone(),
            a: wide_index,
            b: wide_stride,
        });
        block.push(R2ILOp::IntMult {
            dst: register(RCX_OFFSET, 8),
            a: register(RCX_OFFSET, 8),
            b: constant(56, 8),
        });
        block.push(R2ILOp::Subpiece {
            dst: unique(&mut next, 8),
            src: wide_product.clone(),
            offset: 8,
        });
        let extended_product = unique(&mut next, 16);
        block.push(R2ILOp::IntSExt {
            dst: extended_product.clone(),
            src: register(RCX_OFFSET, 8),
        });
        block.push(R2ILOp::IntNotEqual {
            dst: register(CF_OFFSET, 1),
            a: extended_product,
            b: wide_product,
        });
        block.push(R2ILOp::Copy {
            dst: register(OF_OFFSET, 1),
            src: register(CF_OFFSET, 1),
        });
        let member_two_base = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_two_base.clone(),
            a: constant(8, 8),
            b: register(RDI_OFFSET, 8),
        });
        let member_two_scale = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: member_two_scale.clone(),
            a: register(RCX_OFFSET, 8),
            b: constant(1, 8),
        });
        let member_two_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_two_address.clone(),
            a: member_two_base,
            b: member_two_scale,
        });
        let stored_value = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: stored_value.clone(),
            src: register(RDX_OFFSET, 4),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: member_two_address,
            val: stored_value,
        });
        let member_thirteen_base = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_thirteen_base.clone(),
            a: constant(52, 8),
            b: register(RDI_OFFSET, 8),
        });
        let member_thirteen_scale = unique(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: member_thirteen_scale.clone(),
            a: register(RCX_OFFSET, 8),
            b: constant(1, 8),
        });
        let member_thirteen_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_thirteen_address.clone(),
            a: member_thirteen_base,
            b: member_thirteen_scale,
        });
        let load_one = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: load_one.clone(),
            space: DATA,
            addr: member_thirteen_address.clone(),
        });
        block.push(R2ILOp::IntCarry {
            dst: register(CF_OFFSET, 1),
            a: register(RDX_OFFSET, 4),
            b: load_one,
        });
        let load_two = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: load_two.clone(),
            space: DATA,
            addr: member_thirteen_address.clone(),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF_OFFSET, 1),
            a: register(RDX_OFFSET, 4),
            b: load_two,
        });
        let load_three = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: load_three.clone(),
            space: DATA,
            addr: member_thirteen_address,
        });
        block.push(R2ILOp::IntAdd {
            dst: register(RAX_OFFSET, 4),
            a: register(RDX_OFFSET, 4),
            b: load_three,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: register(RAX_OFFSET, 4),
        });
        push_flag_packet(&mut block, &mut next, register(RAX_OFFSET, 4));
        push_frame_suffix(&mut block, &mut next);
        assert_eq!(block.ops.len(), O2_OPERATION_COUNT);
        block
    }

    fn o0_block(entry: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(entry, 73);
        let mut next = 0x40000;
        push_frame_prefix(&mut block, &mut next);
        push_home(&mut block, &mut next, -8, register(RDI_OFFSET, 8));
        push_home(&mut block, &mut next, -12, register(RSI_OFFSET, 4));
        push_home(&mut block, &mut next, -16, register(RDX_OFFSET, 4));

        let value_reload = reload_home(&mut block, &mut next, -16, 4);
        block.push(R2ILOp::Copy {
            dst: register(RCX_OFFSET, 4),
            src: value_reload.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RCX_OFFSET, 8),
            src: value_reload.clone(),
        });
        let arr_one = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 8),
            src: arr_one,
        });
        let idx_one = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, idx_one, RDX_OFFSET);
        push_address_sum(
            &mut block,
            &mut next,
            register(RAX_OFFSET, 8),
            RDX_OFFSET,
            RAX_OFFSET,
        );
        let member_two_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_two_address.clone(),
            a: register(RAX_OFFSET, 8),
            b: constant(8, 8),
        });
        let stored = unique(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: stored.clone(),
            src: value_reload,
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: member_two_address,
            val: stored,
        });

        let arr_two = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 8),
            src: arr_two,
        });
        let idx_two = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, idx_two, RCX_OFFSET);
        push_address_sum(
            &mut block,
            &mut next,
            register(RAX_OFFSET, 8),
            RCX_OFFSET,
            RAX_OFFSET,
        );
        let member_two_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_two_address.clone(),
            a: register(RAX_OFFSET, 8),
            b: constant(8, 8),
        });
        let member_two = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: member_two.clone(),
            space: DATA,
            addr: member_two_address,
        });
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 4),
            src: member_two.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: member_two.clone(),
        });

        let arr_three = reload_home(&mut block, &mut next, -8, 8);
        block.push(R2ILOp::Copy {
            dst: register(RCX_OFFSET, 8),
            src: arr_three,
        });
        let idx_three = reload_home(&mut block, &mut next, -12, 4);
        push_scale_packet(&mut block, &mut next, idx_three, RDX_OFFSET);
        push_address_sum(
            &mut block,
            &mut next,
            register(RCX_OFFSET, 8),
            RDX_OFFSET,
            RCX_OFFSET,
        );
        let member_thirteen_address = unique(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: member_thirteen_address.clone(),
            a: register(RCX_OFFSET, 8),
            b: constant(52, 8),
        });
        let read_one = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read_one.clone(),
            space: DATA,
            addr: member_thirteen_address.clone(),
        });
        block.push(R2ILOp::IntCarry {
            dst: register(CF_OFFSET, 1),
            a: member_two.clone(),
            b: read_one,
        });
        let read_two = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read_two.clone(),
            space: DATA,
            addr: member_thirteen_address.clone(),
        });
        block.push(R2ILOp::IntSCarry {
            dst: register(OF_OFFSET, 1),
            a: member_two.clone(),
            b: read_two,
        });
        let read_three = unique(&mut next, 4);
        block.push(R2ILOp::Load {
            dst: read_three.clone(),
            space: DATA,
            addr: member_thirteen_address,
        });
        block.push(R2ILOp::IntAdd {
            dst: register(RAX_OFFSET, 4),
            a: member_two,
            b: read_three,
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: register(RAX_OFFSET, 4),
        });
        push_flag_packet(&mut block, &mut next, register(RAX_OFFSET, 4));
        push_frame_suffix(&mut block, &mut next);
        assert_eq!(block.ops.len(), O0_OPERATION_COUNT);
        block
    }

    fn artifact_with(block: R2ILBlock, interface: SourceFunctionInterface) -> SsaArtifact {
        SsaArtifact::raw_with_interface(&[block], Some(&arch()), interface)
            .expect("struct-array artifact")
    }

    fn artifact(block: R2ILBlock) -> SsaArtifact {
        artifact_with(block, interface("demo"))
    }

    fn rejects(block: R2ILBlock) {
        assert!(artifact(block).structured().struct_array_indexes.is_empty());
    }

    #[test]
    fn exact_o2_struct_array_fact_closes_layout_accesses_and_inventory() {
        let artifact = artifact(o2_block(ENTRY));
        let fact = artifact
            .structured()
            .struct_array_indexes
            .get(&ENTRY)
            .expect("exact O2 struct-array fact");
        assert_eq!(fact.types.stride_bytes, 56);
        assert_eq!(fact.types.member_offsets_bytes.len(), 14);
        assert_eq!(fact.accesses.len(), 4);
        assert_eq!(fact.accesses[0].kind, StructArrayIndexAccessKind::Write);
        assert_eq!(fact.accesses[0].member_id, 2);
        assert!(fact.accesses[1..].iter().all(|access| {
            access.kind == StructArrayIndexAccessKind::Read && access.member_id == 13
        }));
        assert_eq!(fact.returned.wraps_at_bits, 32);
        assert_eq!(fact.returned.composition, None);
        assert_eq!(
            fact.returned.definition.value,
            fact.returned.physical_full_register
        );
        assert_eq!(fact.returned.definition.producer, fact.returned.zero_extend);
        assert_eq!(fact.returned.definition.storage, fact.abi.return_storage);
        assert_eq!(fact.instruction_inventory.len(), 43);
        assert_eq!(fact.semantic_instructions.len(), 32);
        assert_eq!(fact.frame_instructions.len(), 11);
        assert!(fact.validate_against(&artifact));
    }

    #[test]
    fn exact_o0_struct_array_fact_proves_immutable_homes_and_reloads() {
        let artifact = artifact_with(o0_block(ENTRY), o0_interface("o0-demo"));
        let fact = artifact
            .structured()
            .struct_array_indexes
            .get(&ENTRY)
            .expect("exact O0 struct-array fact");
        assert_eq!(fact.lowering, StructArrayIndexLowering::O0ParameterHomes);
        assert_eq!(fact.homes.len(), 3);
        assert_eq!(fact.homes[0].reloads.len(), 3);
        assert_eq!(fact.homes[1].reloads.len(), 3);
        assert_eq!(fact.homes[2].reloads.len(), 1);
        assert_eq!(fact.scales.len(), 3);
        assert_eq!(fact.accesses.len(), 5);
        assert_eq!(fact.returned.composition, None);
        assert_eq!(
            fact.returned.definition.value,
            fact.returned.physical_full_register
        );
        assert_eq!(fact.instruction_inventory.len(), 114);
        assert_eq!(fact.semantic_instructions.len(), 103);
        assert!(fact.validate_against(&artifact));
    }

    #[test]
    fn o0_home_scale_and_repeated_read_mutations_fail_closed() {
        let mut wrong_home = o0_block(ENTRY);
        let R2ILOp::IntAdd { b, .. } = &mut wrong_home.ops[20] else {
            panic!("index home reload");
        };
        *b = constant((-8i64) as u64, 8);
        assert!(
            artifact_with(wrong_home, o0_interface("wrong-home"))
                .structured()
                .struct_array_indexes
                .is_empty()
        );

        let mut wrong_scale = o0_block(ENTRY);
        let R2ILOp::IntMult { b, .. } = &mut wrong_scale.ops[52] else {
            panic!("second scaled multiply");
        };
        *b = constant(48, 8);
        assert!(
            artifact_with(wrong_scale, o0_interface("wrong-scale"))
                .structured()
                .struct_array_indexes
                .is_empty()
        );

        let mut wrong_read = o0_block(ENTRY);
        let R2ILOp::Load { addr, .. } = &mut wrong_read.ops[96] else {
            panic!("second member-thirteen read");
        };
        *addr = Varnode::unique(0xbeef_0000, 8);
        assert!(
            artifact_with(wrong_read, o0_interface("wrong-read"))
                .structured()
                .struct_array_indexes
                .is_empty()
        );
    }

    #[test]
    fn relocation_and_source_names_do_not_supply_authority() {
        let relocated_entry = ENTRY + 0x5000;
        let relocated = artifact_with(o2_block(relocated_entry), interface("renamed"));
        let fact = relocated
            .structured()
            .struct_array_indexes
            .get(&relocated_entry)
            .expect("relocated name-independent fact");
        assert_eq!(fact.types.stride_bytes, 56);
        assert_eq!(fact.accesses[0].member_offset_bytes, 8);
        assert_eq!(fact.accesses[1].member_offset_bytes, 52);

        let mut renamed_temporary = o2_block(ENTRY);
        let replacement = Varnode::unique(0xfeed_0000, 4);
        let R2ILOp::Copy { dst, .. } = &mut renamed_temporary.ops[18] else {
            panic!("stored-value copy");
        };
        *dst = replacement.clone();
        let R2ILOp::Store { val, .. } = &mut renamed_temporary.ops[19] else {
            panic!("member store");
        };
        *val = replacement;
        assert!(
            artifact(renamed_temporary)
                .structured()
                .struct_array_indexes
                .contains_key(&ENTRY)
        );
    }

    #[test]
    fn type_and_abi_mutations_fail_closed() {
        let unsigned_graph = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Struct { aggregate_id: 0 }, 448, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 1 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                1,
                448,
                32,
                "unsigned",
                (0..14).map(|index| {
                    SourceAggregateMember::new(index, 0, u64::from(index) * 32, 32, "m")
                }),
            )],
        )
        .expect("unsigned graph");
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let wrong_types = SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
                SourceAbiParameterSpec::new(2, storage(RDX_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX_OFFSET),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(unsigned_graph),
        )
        .expect("coherent but semantically wrong graph");
        assert!(
            artifact_with(o2_block(ENTRY), wrong_types)
                .structured()
                .struct_array_indexes
                .is_empty()
        );

        let wrong_cc = SourceFunctionInterface::new_exact_with_logical_types(
            b"struct-array-index-revision-1".to_vec(),
            "amd64",
            [
                SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
                SourceAbiParameterSpec::new(2, storage(RDX_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: storage(RAX_OFFSET),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(type_graph("wrong-cc")),
        )
        .expect("coherent wrong calling convention");
        assert!(
            artifact_with(o2_block(ENTRY), wrong_cc)
                .structured()
                .struct_array_indexes
                .is_empty()
        );
    }

    #[test]
    fn arithmetic_memory_return_and_extra_op_mutations_fail_closed() {
        let mut wrong_extension = o2_block(ENTRY);
        wrong_extension.ops[6] = R2ILOp::IntZExt {
            dst: register(RCX_OFFSET, 8),
            src: register(RSI_OFFSET, 4),
        };
        rejects(wrong_extension);

        let mut wrong_stride = o2_block(ENTRY);
        let R2ILOp::IntMult { b, .. } = &mut wrong_stride.ops[10] else {
            panic!("scaled multiply");
        };
        *b = constant(55, 8);
        rejects(wrong_stride);

        let mut wrong_member = o2_block(ENTRY);
        let R2ILOp::IntAdd { a, .. } = &mut wrong_member.ops[20] else {
            panic!("member base");
        };
        *a = constant(48, 8);
        rejects(wrong_member);

        let mut wrong_read_address = o2_block(ENTRY);
        let R2ILOp::Load { addr, .. } = &mut wrong_read_address.ops[25] else {
            panic!("second member read");
        };
        *addr = Varnode::unique(0xf000, 8);
        rejects(wrong_read_address);

        let mut wrong_space = o2_block(ENTRY);
        let R2ILOp::Store { space, .. } = &mut wrong_space.ops[19] else {
            panic!("member store");
        };
        *space = SpaceId::Custom(9);
        rejects(wrong_space);

        let mut wrong_add = o2_block(ENTRY);
        let R2ILOp::IntAdd { dst, a, b } = wrong_add.ops[28].clone() else {
            panic!("return add");
        };
        wrong_add.ops[28] = R2ILOp::IntSub { dst, a, b };
        rejects(wrong_add);

        let mut stale_return = o2_block(ENTRY);
        let R2ILOp::IntZExt { src, .. } = &mut stale_return.ops[29] else {
            panic!("return zero extension");
        };
        *src = register(RDX_OFFSET, 4);
        rejects(stale_return);

        let mut extra = o2_block(ENTRY);
        extra.ops.insert(
            28,
            R2ILOp::IntAdd {
                dst: Varnode::unique(0xdead_0000, 4),
                a: constant(1, 4),
                b: constant(2, 4),
            },
        );
        rejects(extra);
    }

    #[test]
    fn frame_and_flag_mutations_fail_closed() {
        let mut wrong_frame = o2_block(ENTRY);
        let R2ILOp::IntSub { b, .. } = &mut wrong_frame.ops[1] else {
            panic!("stack allocation");
        };
        *b = constant(16, 8);
        rejects(wrong_frame);

        let mut wrong_flag = o2_block(ENTRY);
        let R2ILOp::IntAnd { b, .. } = &mut wrong_flag.ops[32] else {
            panic!("parity low-byte mask");
        };
        *b = constant(0xffff, 4);
        rejects(wrong_flag);
    }
}
