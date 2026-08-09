//! Exact source facts for the pinned x86-64 `sum_array` lowerings.
//!
//! The O0 lowering is admitted only after every operation and phi in the
//! four-block stack-backed loop has an exact disposition.  The pinned O2
//! lowering has a distinct fact: all eight accumulator phis must have explicit
//! zero and memory-lane producers, and the horizontal reduction, scalar tail,
//! and both returns must close exactly.  The older 40-op vector graph remains
//! an explicit refusal because it does not carry all eight lane projections.

use std::collections::{BTreeMap, BTreeSet};

use r2il::SpaceId;

use crate::StackAddressBase;
use crate::function::SSAFunction;
use crate::graph::{InstId, SsaGraph, ValueId};
use crate::machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineMemoryEndianness,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceStackSlotRole,
    SourceTypeKind,
};
use crate::op::SSAOp;
use crate::semantic::{
    CallBoundarySlot, SourceBoundaryFacts, SourceReturnRegisterCompositionFact,
    SourceReturnRegisterDefinitionFact,
};
use crate::var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar};

pub const SUM_ARRAY_FACT_SCHEMA_VERSION: u32 = 1;

const RAX_OFFSET: u64 = 0;
const RCX_OFFSET: u64 = 8;
const RDX_OFFSET: u64 = 16;
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
pub enum SumArrayLowering {
    O0ScalarHomes,
    O2Vectorized,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayTypeFact {
    pub signed_integer_type_id: u32,
    pub pointer_type_id: u32,
    pub element_size_bytes: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SumArrayParameterFact {
    pub index: u32,
    pub abi_storage: CanonicalStorageId,
    pub graph_storage: CanonicalStorageId,
    pub graph_value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayAbiFact {
    pub revision_identity: Box<[u8]>,
    pub parameters: Box<[SumArrayParameterFact]>,
    pub parameter_logical_values: Box<[SourceLogicalValue]>,
    pub return_logical_value: SourceLogicalValue,
    pub return_storage: CanonicalStorageId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SumArrayHomeRole {
    ArrayParameter,
    LengthParameter,
    SumLocal,
    IndexLocal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SumArrayHomeReloadFact {
    pub address_add: InstId,
    pub load: InstId,
    pub value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayHomeFact {
    pub role: SumArrayHomeRole,
    pub frame_pointer_offset: i64,
    pub entry_stack_offset: i64,
    pub size_bytes: u32,
    pub initializer_address_add: InstId,
    pub initializer_copy: InstId,
    pub initializer_store: InstId,
    pub initial_value: ValueId,
    pub reloads: Box<[SumArrayHomeReloadFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayFrameFact {
    pub stack_storage: CanonicalStorageId,
    pub frame_pointer_storage: CanonicalStorageId,
    pub instruction_pointer_storage: CanonicalStorageId,
    pub memory_space: SpaceId,
    pub entry_stack: ValueId,
    pub allocated_stack: ValueId,
    pub saved_frame_pointer: ValueId,
    pub restored_frame_pointer: ValueId,
    pub return_target: ValueId,
    pub instructions: Box<[InstId]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayPredicateFact {
    pub header_block: u64,
    pub body_block: u64,
    pub exit_block: u64,
    pub index: ValueId,
    pub length: ValueId,
    pub subtract: InstId,
    pub signed_overflow: InstId,
    pub sign: InstId,
    pub greater_or_equal: ValueId,
    pub branch: InstId,
    pub signed_width_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayReadFact {
    pub order: u32,
    pub memory_space: SpaceId,
    pub address: ValueId,
    pub load: InstId,
    pub value: ValueId,
    pub size_bytes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayScalarLoopFact {
    pub array_base: ValueId,
    pub index: ValueId,
    pub sign_extend_index: InstId,
    pub extended_index: ValueId,
    pub scale: InstId,
    pub scaled_index: ValueId,
    pub address_add: InstId,
    pub element_address: ValueId,
    pub reads: Box<[SumArrayReadFact]>,
    pub prior_sum_reads: Box<[SumArrayReadFact]>,
    pub add: InstId,
    pub next_sum: ValueId,
    pub sum_store: InstId,
    pub increment: InstId,
    pub next_index: ValueId,
    pub index_store: InstId,
    pub back_edge: InstId,
    pub wraps_at_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayReturnFact {
    pub sum_load: InstId,
    pub returned_low32: ValueId,
    pub zero_extend: InstId,
    pub physical_full_register: ValueId,
    pub definition: SourceReturnRegisterDefinitionFact,
    pub composition: Option<SourceReturnRegisterCompositionFact>,
    pub return_target: ValueId,
    pub return_inst: InstId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SumArrayInstructionClass {
    Semantic,
    Frame,
    Structural,
    ProvenDead,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SumArrayInstructionDispositionFact {
    pub instruction: InstId,
    pub block_index: u32,
    pub ordinal: u32,
    pub class: SumArrayInstructionClass,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayFact {
    pub schema_version: u32,
    pub entry: u64,
    pub lowering: SumArrayLowering,
    pub types: SumArrayTypeFact,
    pub abi: SumArrayAbiFact,
    pub frame: SumArrayFrameFact,
    pub homes: Box<[SumArrayHomeFact]>,
    pub predicate: SumArrayPredicateFact,
    pub scalar_loop: SumArrayScalarLoopFact,
    pub returned: SumArrayReturnFact,
    pub instruction_inventory: Box<[SumArrayInstructionDispositionFact]>,
}

impl SumArrayFact {
    pub fn validate_against(&self, artifact: &crate::SsaArtifact) -> bool {
        self.schema_version == SUM_ARRAY_FACT_SCHEMA_VERSION
            && artifact.structured().sum_arrays.get(&self.entry) == Some(self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2TopologyFact {
    pub blocks: Box<[u64]>,
    pub block_sizes: Box<[u32]>,
    pub operation_counts: Box<[u32]>,
    pub phi_counts: Box<[u32]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2FrameFact {
    pub memory_space: SpaceId,
    pub entry_stack: ValueId,
    pub saved_frame_pointer: ValueId,
    pub allocated_stack: ValueId,
    pub prologue: Box<[InstId]>,
    pub main_epilogue: Box<[InstId]>,
    pub zero_epilogue: Box<[InstId]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SumArrayO2GuardFact {
    pub block: u64,
    pub input: ValueId,
    pub condition: ValueId,
    pub branch: InstId,
    pub signed_width_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2VectorReadFact {
    pub order: u32,
    pub memory_space: SpaceId,
    pub address: ValueId,
    pub load: InstId,
    pub value: ValueId,
    pub size_bytes: u32,
    pub lane_projections: Box<[InstId]>,
    pub lane_values: Box<[ValueId]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SumArrayO2LaneFact {
    pub lane: u32,
    pub accumulator_storage: CanonicalStorageId,
    pub initial_projection: InstId,
    pub initial_value: ValueId,
    pub phi: InstId,
    pub phi_value: ValueId,
    pub load_projection: InstId,
    pub loaded_value: ValueId,
    pub add: InstId,
    pub next_value: ValueId,
    pub wraps_at_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2VectorLoopFact {
    pub preheader_block: u64,
    pub header_block: u64,
    pub byte_offset_phi: InstId,
    pub byte_offset: ValueId,
    pub bound: ValueId,
    pub reads: Box<[SumArrayO2VectorReadFact]>,
    pub lanes: Box<[SumArrayO2LaneFact]>,
    pub induction_add: InstId,
    pub next_byte_offset: ValueId,
    pub step_bytes: u32,
    pub back_edge: InstId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2ReductionFact {
    pub block: u64,
    pub input_lanes: Box<[ValueId]>,
    pub pairwise_adds: Box<[InstId]>,
    pub pairwise_values: Box<[ValueId]>,
    pub selector_packets: Box<[Box<[InstId]>]>,
    pub final_add: InstId,
    pub returned_low32: ValueId,
    pub zero_extend: InstId,
    pub physical_full_register: ValueId,
    pub wraps_at_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2ScalarTailFact {
    pub header_block: u64,
    pub accumulator_phi: InstId,
    pub accumulator: ValueId,
    pub index_phi: InstId,
    pub index: ValueId,
    pub length_phi: InstId,
    pub length: ValueId,
    pub scale: InstId,
    pub element_address: ValueId,
    pub reads: Box<[SumArrayReadFact]>,
    pub add: InstId,
    pub next_accumulator: ValueId,
    pub increment: InstId,
    pub next_index: ValueId,
    pub back_edge: InstId,
    pub wraps_at_bits: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SumArrayO2ReturnPath {
    VectorOrScalar,
    NonPositiveLength,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2ReturnFact {
    pub path: SumArrayO2ReturnPath,
    pub block: u64,
    pub returned_low32: ValueId,
    pub physical_full_register: ValueId,
    pub definition: SourceReturnRegisterDefinitionFact,
    pub composition: Option<SourceReturnRegisterCompositionFact>,
    pub return_target: ValueId,
    pub return_inst: InstId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayO2Fact {
    pub schema_version: u32,
    pub entry: u64,
    pub lowering: SumArrayLowering,
    pub types: SumArrayTypeFact,
    pub abi: SumArrayAbiFact,
    pub topology: SumArrayO2TopologyFact,
    pub frame: SumArrayO2FrameFact,
    pub guards: Box<[SumArrayO2GuardFact]>,
    pub vector_loop: SumArrayO2VectorLoopFact,
    pub reduction: SumArrayO2ReductionFact,
    pub scalar_tail: SumArrayO2ScalarTailFact,
    pub returns: Box<[SumArrayO2ReturnFact]>,
    pub instruction_inventory: Box<[SumArrayInstructionDispositionFact]>,
}

impl SumArrayO2Fact {
    pub fn validate_against(&self, artifact: &crate::SsaArtifact) -> bool {
        self.schema_version == SUM_ARRAY_FACT_SCHEMA_VERSION
            && artifact.structured().sum_array_o2.get(&self.entry) == Some(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SumArrayRefusalReason {
    IncompleteVectorLaneProvenance,
    VectorTopologyNotYetCertified,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumArrayRefusalFact {
    pub entry: u64,
    pub lowering: SumArrayLowering,
    pub reason: SumArrayRefusalReason,
    pub vector_read_count: u32,
    pub expected_lane_count: u32,
    pub proven_lane_count: u32,
}

pub(crate) struct SumArrayCollection {
    pub facts: BTreeMap<u64, SumArrayFact>,
    pub o2_facts: BTreeMap<u64, SumArrayO2Fact>,
    pub refusals: BTreeMap<u64, SumArrayRefusalFact>,
}

pub(crate) fn collect_sum_array_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> SumArrayCollection {
    let mut facts = BTreeMap::new();
    let mut o2_facts = BTreeMap::new();
    let mut refusals = BTreeMap::new();
    if let Some(fact) = collect_o0(function, graph, boundaries, machine) {
        facts.insert(fact.entry, fact);
    } else if let Some(fact) = collect_o2(function, graph, boundaries, machine) {
        o2_facts.insert(fact.entry, fact);
    } else if let Some(refusal) = collect_o2_lane_refusal(function, graph, machine) {
        refusals.insert(refusal.entry, refusal);
    }
    SumArrayCollection {
        facts,
        o2_facts,
        refusals,
    }
}

fn collect_o0(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> Option<SumArrayFact> {
    let [entry_addr, header_addr, body_addr, exit_addr] = function.block_addrs() else {
        return None;
    };
    let entry = function.get_block(*entry_addr)?;
    let header = function.get_block(*header_addr)?;
    let body = function.get_block(*body_addr)?;
    let exit = function.get_block(*exit_addr)?;
    if function.entry != *entry_addr
        || [
            entry.ops.len(),
            header.ops.len(),
            body.ops.len(),
            exit.ops.len(),
        ] != [16, 18, 46, 11]
        || [
            entry.phis.len(),
            header.phis.len(),
            body.phis.len(),
            exit.phis.len(),
        ] != [0, 20, 0, 0]
        || [entry.size, header.size, body.size, exit.size] != [25, 8, 28, 5]
        || function.predecessors(*entry_addr) != Vec::<u64>::new()
        || function.successors(*entry_addr) != vec![*header_addr]
        || as_set(function.predecessors(*header_addr)) != BTreeSet::from([*entry_addr, *body_addr])
        || as_set(function.successors(*header_addr)) != BTreeSet::from([*body_addr, *exit_addr])
        || function.predecessors(*body_addr) != vec![*header_addr]
        || function.successors(*body_addr) != vec![*header_addr]
        || function.predecessors(*exit_addr) != vec![*header_addr]
        || !function.successors(*exit_addr).is_empty()
        || !boundaries.calls.is_empty()
        || !matches_kinds(&entry.ops, &O0_ENTRY_KINDS)
        || !matches_kinds(&header.ops, &O0_HEADER_KINDS)
        || !matches_kinds(&body.ops, &O0_BODY_KINDS)
        || !matches_kinds(&exit.ops, &O0_EXIT_KINDS)
    {
        return None;
    }
    prove_dead_header_phis(header, graph, *entry_addr, *body_addr)?;
    let types = collect_types(machine)?;
    let abi = collect_abi(graph, machine, &types, true)?;
    let frame = collect_split_frame(function, graph, machine, *entry_addr, *exit_addr)?;
    let frame_pointer = match &entry.ops[3] {
        SSAOp::Copy { dst, .. } => dst,
        _ => return None,
    };
    let arr_home = collect_home(
        function,
        graph,
        *entry_addr,
        frame_pointer,
        SumArrayHomeRole::ArrayParameter,
        -8,
        8,
        4,
        abi.parameters[0].graph_value,
        &[(*body_addr, 0, 1)],
    )?;
    let len_home = collect_home(
        function,
        graph,
        *entry_addr,
        frame_pointer,
        SumArrayHomeRole::LengthParameter,
        -12,
        4,
        7,
        abi.parameters[1].graph_value,
        &[(*header_addr, 4, 5)],
    )?;
    let zero = match entry.ops.get(11)? {
        SSAOp::Copy { src, .. } if constant(src, 0, 4) => src,
        _ => return None,
    };
    let sum_home = collect_home(
        function,
        graph,
        *entry_addr,
        frame_pointer,
        SumArrayHomeRole::SumLocal,
        -16,
        4,
        10,
        value(graph, zero)?,
        &[
            (*body_addr, 11, 12),
            (*body_addr, 11, 14),
            (*body_addr, 11, 16),
            (*exit_addr, 0, 1),
        ],
    )?;
    let index_zero = match entry.ops.get(14)? {
        SSAOp::Copy { src, .. } if constant(src, 0, 4) => src,
        _ => return None,
    };
    let index_home = collect_home(
        function,
        graph,
        *entry_addr,
        frame_pointer,
        SumArrayHomeRole::IndexLocal,
        -20,
        4,
        13,
        value(graph, index_zero)?,
        &[
            (*header_addr, 0, 1),
            (*body_addr, 3, 4),
            (*body_addr, 28, 29),
        ],
    )?;
    for home in [&arr_home, &len_home, &sum_home, &index_home] {
        if machine.memory_space_at(
            *entry_addr,
            graph.op_site_for_inst(home.initializer_store)?.1,
        ) != Some(frame.memory_space)
            || home.reloads.iter().any(|reload| {
                graph
                    .op_site_for_inst(reload.load)
                    .and_then(|(addr, index)| machine.memory_space_at(addr, index))
                    != Some(frame.memory_space)
            })
        {
            return None;
        }
    }
    let predicate = collect_o0_predicate(
        function,
        graph,
        machine,
        *header_addr,
        *body_addr,
        *exit_addr,
        index_home.reloads[0].value,
        len_home.reloads[0].value,
    )?;
    let scalar_loop = collect_o0_loop(
        function,
        graph,
        machine,
        *body_addr,
        &arr_home,
        &sum_home,
        &index_home,
        frame.memory_space,
    )?;
    let returned = collect_o0_return(
        function,
        graph,
        boundaries,
        machine,
        *exit_addr,
        sum_home.reloads[3].value,
        abi.return_storage,
        frame.return_target,
    )?;
    let instruction_inventory = collect_o0_inventory(function, graph)?;
    if instruction_inventory.len() != graph.insts.len()
        || instruction_inventory
            .iter()
            .map(|item| item.instruction)
            .collect::<BTreeSet<_>>()
            != graph.insts.iter().map(|inst| inst.id).collect()
    {
        return None;
    }
    Some(SumArrayFact {
        schema_version: SUM_ARRAY_FACT_SCHEMA_VERSION,
        entry: *entry_addr,
        lowering: SumArrayLowering::O0ScalarHomes,
        types,
        abi,
        frame,
        homes: vec![arr_home, len_home, sum_home, index_home].into_boxed_slice(),
        predicate,
        scalar_loop,
        returned,
        instruction_inventory: instruction_inventory.into_boxed_slice(),
    })
}

fn collect_types(machine: &SourceMachineContext) -> Option<SumArrayTypeFact> {
    let interface = machine.function_interface()?;
    let graph = interface.type_graph()?;
    if graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || graph.types().len() != 2
        || !graph.aggregates().is_empty()
    {
        return None;
    }
    let signed = graph
        .types()
        .iter()
        .filter(|ty| {
            ty.kind() == SourceTypeKind::SignedInteger
                && ty.size_bits() == 32
                && ty.align_bits() == 32
        })
        .collect::<Vec<_>>();
    let [signed] = signed.as_slice() else {
        return None;
    };
    let pointers = graph
        .types()
        .iter()
        .filter(|ty| {
            ty.kind()
                == (SourceTypeKind::Pointer {
                    target_type_id: signed.id(),
                })
                && ty.size_bits() == 64
                && ty.align_bits() == 64
        })
        .collect::<Vec<_>>();
    let [pointer] = pointers.as_slice() else {
        return None;
    };
    Some(SumArrayTypeFact {
        signed_integer_type_id: signed.id(),
        pointer_type_id: pointer.id(),
        element_size_bytes: 4,
    })
}

fn collect_abi(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    types: &SumArrayTypeFact,
    expect_homes: bool,
) -> Option<SumArrayAbiFact> {
    if machine.schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
        || !machine.abi_model().is_available()
        || !machine.abi_model().is_coherent()
        || !machine.memory_model().is_available()
        || !machine.memory_model().is_coherent()
    {
        return None;
    }
    let interface = machine.function_interface()?;
    let returned = interface.return_logical_value()?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity().is_empty()
        || interface.calling_convention() != "sysv_amd64"
        || !interface.stack_slot_roles_complete()
        || interface.parameters().len() != 2
        || interface.parameter_logical_values().len() != 2
        || interface.parameters()[0].index() != 0
        || interface.parameters()[1].index() != 1
        || !register_at(interface.parameters()[0].storage(), RDI_OFFSET, 8)
        || !register_at(interface.parameters()[1].storage(), RSI_OFFSET, 8)
    {
        return None;
    }
    if expect_homes {
        let expected = [
            (-20, 4, SourceStackSlotRole::Local),
            (-16, 4, SourceStackSlotRole::Local),
            (
                -12,
                4,
                SourceStackSlotRole::ParameterHome {
                    parameter_index: 1,
                    home_storage: interface.parameters()[1].storage(),
                },
            ),
            (
                -8,
                8,
                SourceStackSlotRole::ParameterHome {
                    parameter_index: 0,
                    home_storage: interface.parameters()[0].storage(),
                },
            ),
        ];
        if interface.stack_slots().len() != expected.len()
            || expected.iter().any(|(offset, size, role)| {
                !interface.stack_slots().iter().any(|slot| {
                    slot.base() == StackAddressBase::FramePointer
                        && register_at(slot.base_storage(), RBP_OFFSET, 8)
                        && slot.offset() == *offset
                        && slot.size_bytes() == *size
                        && slot.role() == *role
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
        || logical[1].type_id() != types.signed_integer_type_id
        || logical[1].carrier().kind() != SourceCarrierKind::LowBits
        || logical[1].carrier().offset_bits() != 0
        || logical[1].carrier().size_bits() != 32
        || returned.type_id() != types.signed_integer_type_id
        || returned.carrier().kind() != SourceCarrierKind::LowBits
        || returned.carrier().offset_bits() != 0
        || returned.carrier().size_bits() != 32
    {
        return None;
    }
    let return_storage = match interface.return_kind() {
        SourceFunctionReturn::Register { storage } if register_at(storage, RAX_OFFSET, 8) => {
            storage
        }
        _ => return None,
    };
    if machine.abi_model().argument_registers().len() != 2
        || machine.abi_model().return_registers().len() != 1
        || machine.abi_model().argument_registers()[0].storage()
            != interface.parameters()[0].storage()
        || machine.abi_model().argument_registers()[1].storage()
            != interface.parameters()[1].storage()
        || machine.abi_model().return_registers()[0].storage() != return_storage
    {
        return None;
    }
    let expected = [
        (0, interface.parameters()[0].storage(), RDI_OFFSET, 8),
        (1, interface.parameters()[1].storage(), RSI_OFFSET, 4),
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
                .filter(|candidate| {
                    graph.def_inst(candidate.id).is_none()
                        && candidate.var.version == 0
                        && candidate.var.size == size
                        && candidate.canonical_storage == Some(graph_storage)
                })
                .map(|candidate| candidate.id)
                .collect::<Vec<_>>();
            let [graph_value] = candidates.as_slice() else {
                return None;
            };
            Some(SumArrayParameterFact {
                index,
                abi_storage,
                graph_storage,
                graph_value: *graph_value,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(SumArrayAbiFact {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        parameters: parameters.into_boxed_slice(),
        parameter_logical_values: logical.to_vec().into_boxed_slice(),
        return_logical_value: returned,
        return_storage,
    })
}

fn collect_split_frame(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    entry_addr: u64,
    exit_addr: u64,
) -> Option<SumArrayFrameFact> {
    let entry = function.get_block(entry_addr)?;
    let exit = function.get_block(exit_addr)?;
    let saved = match &entry.ops[0] {
        SSAOp::Copy { dst, src }
            if src.version == 0
                && src.size == 8
                && dst.size == 8
                && register_at(storage(graph, src)?, RBP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let allocated = match &entry.ops[1] {
        SSAOp::IntSub { dst, a, b }
            if a.version == 0
                && constant(b, 8, 8)
                && register_at(storage(graph, a)?, RSP_OFFSET, 8)
                && storage(graph, dst)? == storage(graph, a)? =>
        {
            dst
        }
        _ => return None,
    };
    match (&entry.ops[2], &entry.ops[3]) {
        (SSAOp::Store { addr, val, .. }, SSAOp::Copy { dst, src })
            if addr == allocated
                && val == saved
                && src == allocated
                && register_at(storage(graph, dst)?, RBP_OFFSET, 8) => {}
        _ => return None,
    }
    let dead_seed = match &exit.ops[4] {
        SSAOp::Copy { dst, src } if constant(src, 0, 8) && dst.size == 8 => value(graph, dst)?,
        _ => return None,
    };
    let restored = match &exit.ops[5] {
        SSAOp::Load { dst, addr, .. } if addr == allocated && dst.size == 8 => dst,
        _ => return None,
    };
    let restored_stack = match &exit.ops[6] {
        SSAOp::IntAdd { dst, a, b }
            if a == allocated
                && constant(b, 8, 8)
                && register_at(storage(graph, dst)?, RSP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    match &exit.ops[7] {
        SSAOp::Copy { dst, src }
            if src == restored && register_at(storage(graph, dst)?, RBP_OFFSET, 8) => {}
        _ => return None,
    }
    let target = match &exit.ops[8] {
        SSAOp::Load { dst, addr, .. }
            if addr == restored_stack && register_at(storage(graph, dst)?, RIP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let final_stack = match &exit.ops[9] {
        SSAOp::IntAdd { dst, a, b }
            if a == restored_stack
                && constant(b, 8, 8)
                && register_at(storage(graph, dst)?, RSP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    if !matches!(&exit.ops[10], SSAOp::Return { target: actual } if actual == target)
        || graph
            .uses_of
            .get(dead_seed.0 as usize)
            .is_none_or(|uses| !uses.is_empty())
        || final_stack.size != 8
    {
        return None;
    }
    let memory_space = machine.memory_space_at(entry_addr, 2)?;
    if [
        machine.memory_space_at(exit_addr, 5),
        machine.memory_space_at(exit_addr, 8),
    ]
    .into_iter()
    .any(|space| space != Some(memory_space))
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
        .map(|index| graph.inst_id_for_op_site(entry_addr, index))
        .chain((4..11).map(|index| graph.inst_id_for_op_site(exit_addr, index)))
        .collect::<Option<Vec<_>>>()?;
    Some(SumArrayFrameFact {
        stack_storage: storage(graph, allocated)?,
        frame_pointer_storage: match &entry.ops[0] {
            SSAOp::Copy { src, .. } => storage(graph, src)?,
            _ => return None,
        },
        instruction_pointer_storage: storage(graph, target)?,
        memory_space,
        entry_stack: match &entry.ops[1] {
            SSAOp::IntSub { a, .. } => value(graph, a)?,
            _ => return None,
        },
        allocated_stack: value(graph, allocated)?,
        saved_frame_pointer: value(graph, saved)?,
        restored_frame_pointer: value(graph, restored)?,
        return_target: value(graph, target)?,
        instructions: instructions.into_boxed_slice(),
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_home(
    function: &SSAFunction,
    graph: &SsaGraph,
    entry_addr: u64,
    frame_pointer: &SSAVar,
    role: SumArrayHomeRole,
    offset: i64,
    size: u32,
    initializer: usize,
    expected_initial: ValueId,
    reload_sites: &[(u64, usize, usize)],
) -> Option<SumArrayHomeFact> {
    let entry = function.get_block(entry_addr)?;
    let address = match entry.ops.get(initializer)? {
        SSAOp::IntAdd { dst, a, b }
            if a == frame_pointer && constant(b, offset as u64, 8) && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let copied = match entry.ops.get(initializer + 1)? {
        SSAOp::Copy { dst, src } if value(graph, src)? == expected_initial && dst.size == size => {
            dst
        }
        _ => return None,
    };
    match entry.ops.get(initializer + 2)? {
        SSAOp::Store { addr, val, .. } if addr == address && val == copied => {}
        _ => return None,
    }
    let reloads = reload_sites
        .iter()
        .map(|(block_addr, address_index, load_index)| {
            let block = function.get_block(*block_addr)?;
            let reload_address = match block.ops.get(*address_index)? {
                SSAOp::IntAdd { dst, a, b }
                    if a == frame_pointer && constant(b, offset as u64, 8) && dst.size == 8 =>
                {
                    dst
                }
                _ => return None,
            };
            let loaded = match block.ops.get(*load_index)? {
                SSAOp::Load { dst, addr, .. } if addr == reload_address && dst.size == size => dst,
                _ => return None,
            };
            Some(SumArrayHomeReloadFact {
                address_add: graph.inst_id_for_op_site(*block_addr, *address_index)?,
                load: graph.inst_id_for_op_site(*block_addr, *load_index)?,
                value: value(graph, loaded)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(SumArrayHomeFact {
        role,
        frame_pointer_offset: offset,
        entry_stack_offset: offset.checked_sub(8)?,
        size_bytes: size,
        initializer_address_add: graph.inst_id_for_op_site(entry_addr, initializer)?,
        initializer_copy: graph.inst_id_for_op_site(entry_addr, initializer + 1)?,
        initializer_store: graph.inst_id_for_op_site(entry_addr, initializer + 2)?,
        initial_value: value(graph, copied)?,
        reloads: reloads.into_boxed_slice(),
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_o0_predicate(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    header_addr: u64,
    body_addr: u64,
    exit_addr: u64,
    index: ValueId,
    length: ValueId,
) -> Option<SumArrayPredicateFact> {
    let block = function.get_block(header_addr)?;
    let index_var = &graph.value(index)?.var;
    let length_var = &graph.value(length)?.var;
    match (&block.ops[2], &block.ops[3], &block.ops[6]) {
        (
            SSAOp::Copy { dst: eax, src },
            SSAOp::IntZExt {
                dst: rax,
                src: zsrc,
            },
            SSAOp::Copy {
                dst: rhs,
                src: rhs_src,
            },
        ) if src == index_var
            && zsrc == index_var
            && rhs_src == length_var
            && register_at(storage(graph, eax)?, RAX_OFFSET, 4)
            && register_at(storage(graph, rax)?, RAX_OFFSET, 8)
            && rhs.size == 4 => {}
        _ => return None,
    }
    let rhs = block.ops[6].dst()?;
    let difference = match (&block.ops[7], &block.ops[8], &block.ops[9]) {
        (
            SSAOp::IntLess { dst: cf, a, b },
            SSAOp::IntSBorrow {
                dst: of,
                a: oa,
                b: ob,
            },
            SSAOp::IntSub { dst, a: sa, b: sb },
        ) if a == index_var
            && b == rhs
            && oa == index_var
            && ob == rhs
            && sa == index_var
            && sb == rhs
            && register_at(storage(graph, cf)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let sign = match &block.ops[10] {
        SSAOp::IntSLess { dst, a, b }
            if a == difference
                && constant(b, 0, 4)
                && register_at(storage(graph, dst)?, SF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    match_flag_tail(&block.ops[11..16], graph, difference, 4)?;
    let greater_or_equal = match &block.ops[16] {
        SSAOp::IntEqual { dst, a, b }
            if register_at(storage(graph, a)?, OF_OFFSET, 1) && b == sign =>
        {
            dst
        }
        _ => return None,
    };
    match &block.ops[17] {
        SSAOp::CBranch { cond, .. } if cond == greater_or_equal => {}
        _ => return None,
    }
    if as_set(function.successors(header_addr)) != BTreeSet::from([body_addr, exit_addr]) {
        return None;
    }
    Some(SumArrayPredicateFact {
        header_block: header_addr,
        body_block: body_addr,
        exit_block: exit_addr,
        index,
        length,
        subtract: graph.inst_id_for_op_site(header_addr, 9)?,
        signed_overflow: graph.inst_id_for_op_site(header_addr, 8)?,
        sign: graph.inst_id_for_op_site(header_addr, 10)?,
        greater_or_equal: value(graph, greater_or_equal)?,
        branch: graph.inst_id_for_op_site(header_addr, 17)?,
        signed_width_bits: 32,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_o0_loop(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    body_addr: u64,
    arr_home: &SumArrayHomeFact,
    sum_home: &SumArrayHomeFact,
    index_home: &SumArrayHomeFact,
    memory_space: SpaceId,
) -> Option<SumArrayScalarLoopFact> {
    let block = function.get_block(body_addr)?;
    let arr = &graph.value(arr_home.reloads[0].value)?.var;
    let index = &graph.value(index_home.reloads[1].value)?.var;
    let base = match &block.ops[2] {
        SSAOp::Copy { dst, src }
            if src == arr && register_at(storage(graph, dst)?, RAX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let extended = match &block.ops[5] {
        SSAOp::IntSExt { dst, src }
            if src == index && register_at(storage(graph, dst)?, RCX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let scaled = match &block.ops[6] {
        SSAOp::IntMult { dst, a, b } if a == extended && constant(b, 4, 8) => dst,
        _ => return None,
    };
    let address = match &block.ops[7] {
        SSAOp::IntAdd { dst, a, b } if a == base && b == scaled && dst.size == 8 => dst,
        _ => return None,
    };
    let element = match &block.ops[8] {
        SSAOp::Load { dst, addr, .. } if addr == address && dst.size == 4 => dst,
        _ => return None,
    };
    match (&block.ops[9], &block.ops[10]) {
        (
            SSAOp::Copy { dst, src },
            SSAOp::IntZExt {
                dst: wide,
                src: zsrc,
            },
        ) if src == element
            && zsrc == element
            && register_at(storage(graph, dst)?, RAX_OFFSET, 4)
            && register_at(storage(graph, wide)?, RAX_OFFSET, 8) => {}
        _ => return None,
    }
    let sum_reads = [12usize, 14, 16]
        .into_iter()
        .zip(sum_home.reloads.iter().take(3))
        .map(|(index, reload)| {
            let loaded = match block.ops.get(index)? {
                SSAOp::Load { dst, .. } => dst,
                _ => return None,
            };
            Some(SumArrayReadFact {
                order: u32::try_from(index).ok()?,
                memory_space: machine.memory_space_at(body_addr, index)?,
                address: match block.ops.get(11)? {
                    SSAOp::IntAdd { dst, .. } => value(graph, dst)?,
                    _ => return None,
                },
                load: reload.load,
                value: value(graph, loaded)?,
                size_bytes: 4,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    if sum_reads
        .iter()
        .any(|read| read.memory_space != memory_space)
        || sum_reads
            .iter()
            .map(|read| read.value)
            .collect::<BTreeSet<_>>()
            .len()
            != 3
    {
        return None;
    }
    let sum_vars = sum_reads
        .iter()
        .map(|read| graph.value(read.value).map(|value| &value.var))
        .collect::<Option<Vec<_>>>()?;
    match (&block.ops[13], &block.ops[15]) {
        (
            SSAOp::IntCarry { dst, a, b },
            SSAOp::IntSCarry {
                dst: of,
                a: oa,
                b: ob,
            },
        ) if a == element
            && b == sum_vars[0]
            && oa == element
            && ob == sum_vars[1]
            && register_at(storage(graph, dst)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1) => {}
        _ => return None,
    }
    let next_sum = match &block.ops[17] {
        SSAOp::IntAdd { dst, a, b } if a == element && b == sum_vars[2] && dst.size == 4 => dst,
        _ => return None,
    };
    match &block.ops[18] {
        SSAOp::IntZExt { dst, src }
            if src == next_sum && register_at(storage(graph, dst)?, RAX_OFFSET, 8) => {}
        _ => return None,
    }
    match_flag_packet(&block.ops[19..25], graph, next_sum, 4)?;
    let sum_address = match (&block.ops[11], &block.ops[25]) {
        (
            SSAOp::IntAdd { a, b, .. },
            SSAOp::IntAdd {
                dst,
                a: store_a,
                b: store_b,
            },
        ) if store_a == a && store_b == b && constant(store_b, (-16i64) as u64, 8) => dst,
        _ => return None,
    };
    match (&block.ops[26], &block.ops[27]) {
        (SSAOp::Copy { dst, src }, SSAOp::Store { addr, val, .. })
            if src == next_sum && addr == sum_address && val == dst => {}
        _ => return None,
    }
    let update_index = &graph.value(index_home.reloads[2].value)?.var;
    match &block.ops[30] {
        SSAOp::Copy { dst, src }
            if src == update_index && register_at(storage(graph, dst)?, RAX_OFFSET, 4) => {}
        _ => return None,
    }
    match &block.ops[31] {
        SSAOp::IntZExt { dst, src }
            if src == update_index && register_at(storage(graph, dst)?, RAX_OFFSET, 8) => {}
        _ => return None,
    }
    match (&block.ops[32], &block.ops[33]) {
        (
            SSAOp::IntCarry { dst, a, b },
            SSAOp::IntSCarry {
                dst: of,
                a: oa,
                b: ob,
            },
        ) if a == update_index
            && constant(b, 1, 4)
            && oa == update_index
            && constant(ob, 1, 4)
            && register_at(storage(graph, dst)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1) => {}
        _ => return None,
    }
    let next_index = match &block.ops[34] {
        SSAOp::IntAdd { dst, a, b } if a == update_index && constant(b, 1, 4) && dst.size == 4 => {
            dst
        }
        _ => return None,
    };
    match &block.ops[35] {
        SSAOp::IntZExt { dst, src }
            if src == next_index && register_at(storage(graph, dst)?, RAX_OFFSET, 8) => {}
        _ => return None,
    }
    match_flag_packet(&block.ops[36..42], graph, next_index, 4)?;
    let index_address = match (&block.ops[28], &block.ops[42]) {
        (
            SSAOp::IntAdd { a, b, .. },
            SSAOp::IntAdd {
                dst,
                a: store_a,
                b: store_b,
            },
        ) if store_a == a && store_b == b && constant(store_b, (-20i64) as u64, 8) => dst,
        _ => return None,
    };
    match (&block.ops[43], &block.ops[44], &block.ops[45]) {
        (SSAOp::Copy { dst, src }, SSAOp::Store { addr, val, .. }, SSAOp::Branch { .. })
            if src == next_index && addr == index_address && val == dst => {}
        _ => return None,
    }
    for index in [8usize, 12, 14, 16, 27, 44] {
        if machine.memory_space_at(body_addr, index) != Some(memory_space) {
            return None;
        }
    }
    let element_read = SumArrayReadFact {
        order: 0,
        memory_space,
        address: value(graph, address)?,
        load: graph.inst_id_for_op_site(body_addr, 8)?,
        value: value(graph, element)?,
        size_bytes: 4,
    };
    Some(SumArrayScalarLoopFact {
        array_base: value(graph, base)?,
        index: value(graph, index)?,
        sign_extend_index: graph.inst_id_for_op_site(body_addr, 5)?,
        extended_index: value(graph, extended)?,
        scale: graph.inst_id_for_op_site(body_addr, 6)?,
        scaled_index: value(graph, scaled)?,
        address_add: graph.inst_id_for_op_site(body_addr, 7)?,
        element_address: value(graph, address)?,
        reads: Box::new([element_read]),
        prior_sum_reads: sum_reads.into_boxed_slice(),
        add: graph.inst_id_for_op_site(body_addr, 17)?,
        next_sum: value(graph, next_sum)?,
        sum_store: graph.inst_id_for_op_site(body_addr, 27)?,
        increment: graph.inst_id_for_op_site(body_addr, 34)?,
        next_index: value(graph, next_index)?,
        index_store: graph.inst_id_for_op_site(body_addr, 44)?,
        back_edge: graph.inst_id_for_op_site(body_addr, 45)?,
        wraps_at_bits: 32,
    })
}

fn collect_o0_return(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    _machine: &SourceMachineContext,
    exit_addr: u64,
    returned_low32: ValueId,
    return_storage: CanonicalStorageId,
    return_target: ValueId,
) -> Option<SumArrayReturnFact> {
    let block = function.get_block(exit_addr)?;
    let low = &graph.value(returned_low32)?.var;
    match (&block.ops[2], &block.ops[3]) {
        (
            SSAOp::Copy { dst, src },
            SSAOp::IntZExt {
                dst: wide,
                src: zsrc,
            },
        ) if src == low
            && zsrc == low
            && register_at(storage(graph, dst)?, RAX_OFFSET, 4)
            && storage(graph, wide)? == return_storage => {}
        _ => return None,
    }
    let return_inst = graph.inst_id_for_op_site(exit_addr, 10)?;
    let boundary = boundaries.returns.get(&return_inst)?;
    let full_register = match &block.ops[3] {
        SSAOp::IntZExt { dst, .. } => value(graph, dst)?,
        _ => return None,
    };
    let definition = SourceReturnRegisterDefinitionFact {
        storage: return_storage,
        value: full_register,
        producer: graph.inst_id_for_op_site(exit_addr, 3)?,
    };
    if !boundary.complete
        || boundary.values.as_slice()
            != [crate::semantic::CallBoundaryValueFact {
                slot: CallBoundarySlot::Register {
                    index: 0,
                    storage: return_storage,
                },
                value: full_register,
            }]
        || !boundary.register_compositions.is_empty()
        || return_target
            != match &block.ops[10] {
                SSAOp::Return { target } => value(graph, target)?,
                _ => return None,
            }
    {
        return None;
    }
    Some(SumArrayReturnFact {
        sum_load: graph.inst_id_for_op_site(exit_addr, 1)?,
        returned_low32,
        zero_extend: graph.inst_id_for_op_site(exit_addr, 3)?,
        physical_full_register: full_register,
        definition,
        composition: None,
        return_target,
        return_inst,
    })
}

fn collect_o0_inventory(
    function: &SSAFunction,
    graph: &SsaGraph,
) -> Option<Vec<SumArrayInstructionDispositionFact>> {
    let mut inventory = Vec::new();
    for (block_index, block_addr) in function.block_addrs().iter().copied().enumerate() {
        let block = function.get_block(block_addr)?;
        for phi_index in 0..block.phis.len() {
            let instruction = *graph
                .block(graph.block_id_for_addr(block_addr)?)?
                .insts
                .get(phi_index)?;
            inventory.push(SumArrayInstructionDispositionFact {
                instruction,
                block_index: u32::try_from(block_index).ok()?,
                ordinal: u32::try_from(phi_index).ok()?,
                class: SumArrayInstructionClass::ProvenDead,
            });
        }
        for op_index in 0..block.ops.len() {
            let class = match block_index {
                0 if op_index < 4 => SumArrayInstructionClass::Frame,
                0 => SumArrayInstructionClass::Semantic,
                1 if op_index <= 6 => SumArrayInstructionClass::Semantic,
                1 => SumArrayInstructionClass::Structural,
                2 if matches!(op_index, 0..=12 | 17..=18 | 25..=31 | 34..=35 | 42..=44) => {
                    SumArrayInstructionClass::Semantic
                }
                2 => SumArrayInstructionClass::Structural,
                3 if op_index <= 3 => SumArrayInstructionClass::Semantic,
                3 => SumArrayInstructionClass::Frame,
                _ => return None,
            };
            inventory.push(SumArrayInstructionDispositionFact {
                instruction: graph.inst_id_for_op_site(block_addr, op_index)?,
                block_index: u32::try_from(block_index).ok()?,
                ordinal: u32::try_from(block.phis.len().checked_add(op_index)?).ok()?,
                class,
            });
        }
    }
    Some(inventory)
}

fn prove_dead_header_phis(
    header: &crate::function::SSABlock,
    graph: &SsaGraph,
    entry_addr: u64,
    body_addr: u64,
) -> Option<()> {
    for phi in &header.phis {
        if phi.sources.len() != 2
            || phi
                .sources
                .iter()
                .map(|(addr, _)| *addr)
                .collect::<BTreeSet<_>>()
                != BTreeSet::from([entry_addr, body_addr])
        {
            return None;
        }
        let output = graph.value_id_for_var(&phi.dst)?;
        if graph
            .uses_of
            .get(output.0 as usize)
            .is_none_or(|uses| !uses.is_empty())
        {
            return None;
        }
    }
    Some(())
}

fn collect_o2(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> Option<SumArrayO2Fact> {
    let block_addrs: [u64; 10] = function.block_addrs().try_into().ok()?;
    let [
        entry_addr,
        gate_addr,
        zero_addr,
        preheader_addr,
        vector_addr,
        reduction_addr,
        bridge_addr,
        scalar_addr,
        exit_addr,
        zero_exit_addr,
    ] = block_addrs;
    let expected_offsets = [0, 8, 15, 25, 64, 92, 122, 128, 139, 21];
    let expected_sizes = [8, 7, 6, 39, 28, 30, 6, 11, 2, 4];
    let expected_operations = [16, 14, 21, 119, 46, 154, 3, 42, 7, 17];
    let expected_phis = [0, 0, 0, 0, 27, 0, 0, 103, 103, 0];
    if function.entry != entry_addr
        || block_addrs
            .iter()
            .zip(expected_offsets)
            .any(|(addr, offset)| addr.checked_sub(entry_addr) != Some(offset))
        || function.blocks().map(|block| block.size).ne(expected_sizes)
        || function
            .blocks()
            .map(|block| block.ops.len())
            .ne(expected_operations)
        || function
            .blocks()
            .map(|block| block.phis.len())
            .ne(expected_phis)
        || function
            .blocks()
            .zip(O2_BLOCK_SIGNATURES)
            .any(|(block, signature)| !matches_o2_signature(&block.ops, signature))
        || function.predecessors(entry_addr) != Vec::<u64>::new()
        || as_set(function.successors(entry_addr)) != BTreeSet::from([gate_addr, zero_exit_addr])
        || function.predecessors(gate_addr) != vec![entry_addr]
        || as_set(function.successors(gate_addr)) != BTreeSet::from([zero_addr, preheader_addr])
        || function.predecessors(zero_addr) != vec![gate_addr]
        || function.successors(zero_addr) != vec![scalar_addr]
        || function.predecessors(preheader_addr) != vec![gate_addr]
        || function.successors(preheader_addr) != vec![vector_addr]
        || as_set(function.predecessors(vector_addr))
            != BTreeSet::from([preheader_addr, vector_addr])
        || as_set(function.successors(vector_addr)) != BTreeSet::from([vector_addr, reduction_addr])
        || function.predecessors(reduction_addr) != vec![vector_addr]
        || as_set(function.successors(reduction_addr)) != BTreeSet::from([bridge_addr, exit_addr])
        || function.predecessors(bridge_addr) != vec![reduction_addr]
        || function.successors(bridge_addr) != vec![scalar_addr]
        || as_set(function.predecessors(scalar_addr))
            != BTreeSet::from([zero_addr, bridge_addr, scalar_addr])
        || as_set(function.successors(scalar_addr)) != BTreeSet::from([scalar_addr, exit_addr])
        || as_set(function.predecessors(exit_addr)) != BTreeSet::from([reduction_addr, scalar_addr])
        || !function.successors(exit_addr).is_empty()
        || function.predecessors(zero_exit_addr) != vec![entry_addr]
        || !function.successors(zero_exit_addr).is_empty()
        || !boundaries.calls.is_empty()
        || boundaries.returns.len() != 2
    {
        return None;
    }

    let types = collect_types(machine)?;
    let abi = collect_abi(graph, machine, &types, false)?;
    let frame = collect_o2_frame(
        function,
        graph,
        machine,
        entry_addr,
        exit_addr,
        zero_exit_addr,
    )?;
    let vector_loop =
        collect_o2_vector_loop(function, graph, machine, &abi, preheader_addr, vector_addr)?;
    if vector_loop.lanes.len() != 8
        || vector_loop.reads.len() != 2
        || vector_loop.lanes.iter().any(|lane| {
            graph.def_inst(lane.initial_value) != Some(lane.initial_projection)
                || graph.def_inst(lane.loaded_value) != Some(lane.load_projection)
                || graph.def_inst(lane.phi_value) != Some(lane.phi)
                || graph.def_inst(lane.next_value) != Some(lane.add)
        })
    {
        return None;
    }
    let reduction =
        collect_o2_reduction(function, graph, machine, reduction_addr, &vector_loop.lanes)?;
    let guards = collect_o2_guards(
        function,
        graph,
        machine,
        &abi,
        entry_addr,
        gate_addr,
        preheader_addr,
        reduction_addr,
        exit_addr,
        zero_exit_addr,
    )?;
    let scalar_tail = collect_o2_scalar_tail(
        function,
        graph,
        machine,
        &abi,
        gate_addr,
        zero_addr,
        bridge_addr,
        scalar_addr,
        exit_addr,
        &vector_loop,
        &reduction,
    )?;

    let exit = function.get_block(exit_addr)?;
    let (exit_low_index, exit_low_phi) = o2_phi_at(exit, RAX_OFFSET, 4)?;
    let exit_low_inst = o2_phi_inst(graph, exit_addr, exit_low_index)?;
    let exit_low = exact_def(graph, &exit_low_phi.dst, exit_low_inst)?;
    let (exit_full_index, exit_full_phi) = o2_phi_at(exit, RAX_OFFSET, 8)?;
    let exit_full_inst = o2_phi_inst(graph, exit_addr, exit_full_index)?;
    let exit_full = exact_def(graph, &exit_full_phi.dst, exit_full_inst)?;
    let main_return = collect_o2_return(
        function,
        graph,
        boundaries,
        exit_addr,
        6,
        exit_low,
        exit_full,
        abi.return_storage,
        SumArrayO2ReturnPath::VectorOrScalar,
    )?;
    let zero_exit = function.get_block(zero_exit_addr)?;
    let zero_low = match zero_exit.ops.get(2)? {
        SSAOp::IntXor { dst, a, b }
            if a == b && register_at(storage(graph, dst)?, RAX_OFFSET, 4) =>
        {
            dst
        }
        _ => return None,
    };
    let zero_full = match zero_exit.ops.get(3)? {
        SSAOp::IntZExt { dst, src }
            if src == zero_low && register_at(storage(graph, dst)?, RAX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let zero_return = collect_o2_return(
        function,
        graph,
        boundaries,
        zero_exit_addr,
        16,
        value(graph, zero_low)?,
        value(graph, zero_full)?,
        abi.return_storage,
        SumArrayO2ReturnPath::NonPositiveLength,
    )?;
    let instruction_inventory = collect_o2_inventory(function, graph)?;
    if instruction_inventory.len() != graph.insts.len()
        || instruction_inventory
            .iter()
            .map(|item| item.instruction)
            .collect::<BTreeSet<_>>()
            != graph.insts.iter().map(|inst| inst.id).collect()
    {
        return None;
    }

    Some(SumArrayO2Fact {
        schema_version: SUM_ARRAY_FACT_SCHEMA_VERSION,
        entry: entry_addr,
        lowering: SumArrayLowering::O2Vectorized,
        types,
        abi,
        topology: SumArrayO2TopologyFact {
            blocks: block_addrs.into(),
            block_sizes: expected_sizes.into(),
            operation_counts: expected_operations.map(|count| count as u32).into(),
            phi_counts: expected_phis.map(|count| count as u32).into(),
        },
        frame,
        guards: guards.into_boxed_slice(),
        vector_loop,
        reduction,
        scalar_tail,
        returns: Box::new([main_return, zero_return]),
        instruction_inventory: instruction_inventory.into_boxed_slice(),
    })
}

fn collect_o2_frame(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    entry_addr: u64,
    main_exit_addr: u64,
    zero_exit_addr: u64,
) -> Option<SumArrayO2FrameFact> {
    macro_rules! frame_fail {
        ($_stage:literal) => {{
            return None;
        }};
    }
    macro_rules! frame_require {
        ($value:expr, $stage:literal) => {
            match $value {
                Some(value) => value,
                None => frame_fail!($stage),
            }
        };
    }
    let entry = frame_require!(function.get_block(entry_addr), "entry block");
    let saved = match &entry.ops[0] {
        SSAOp::Copy { dst, src }
            if src.version == 0
                && src.size == 8
                && dst.size == 8
                && register_at(
                    frame_require!(storage(graph, src), "saved source storage"),
                    RBP_OFFSET,
                    8,
                ) =>
        {
            dst
        }
        _ => frame_fail!("saved frame pointer"),
    };
    let allocated = match &entry.ops[1] {
        SSAOp::IntSub { dst, a, b }
            if a.version == 0
                && constant(b, 8, 8)
                && register_at(
                    frame_require!(storage(graph, a), "entry stack storage"),
                    RSP_OFFSET,
                    8,
                )
                && frame_require!(storage(graph, dst), "allocated stack storage")
                    == frame_require!(storage(graph, a), "entry stack storage repeat") =>
        {
            dst
        }
        _ => frame_fail!("stack allocation"),
    };
    match (&entry.ops[2], &entry.ops[3]) {
        (SSAOp::Store { addr, val, .. }, SSAOp::Copy { dst, src })
            if addr == allocated
                && val == saved
                && src == allocated
                && register_at(
                    frame_require!(storage(graph, dst), "frame pointer destination storage"),
                    RBP_OFFSET,
                    8,
                ) => {}
        _ => frame_fail!("prologue store/copy"),
    }
    let memory_space = frame_require!(
        machine.memory_space_at(entry_addr, 2),
        "prologue memory space"
    );
    let memory = frame_require!(
        machine.memory_model().space(memory_space),
        "memory space model"
    );
    if memory.address_bits() != 64
        || memory.word_size_bytes() != 1
        || memory.endianness() != MachineMemoryEndianness::Little
    {
        frame_fail!("memory model");
    }

    let check_epilogue = |block_addr: u64, start: usize| -> Option<Box<[InstId]>> {
        let block = frame_require!(function.get_block(block_addr), "epilogue block");
        let dead = match frame_require!(block.ops.get(start), "epilogue dead-seed op") {
            SSAOp::Copy { dst, src } if constant(src, 0, 8) && dst.size == 8 => dst,
            _ => frame_fail!("epilogue dead seed"),
        };
        let restored = match frame_require!(block.ops.get(start + 1), "epilogue saved-load op") {
            SSAOp::Load { dst, addr, .. } if addr == allocated && dst.size == 8 => dst,
            _ => frame_fail!("epilogue saved load"),
        };
        let restored_stack =
            match frame_require!(block.ops.get(start + 2), "epilogue first-stack-advance op") {
                SSAOp::IntAdd { dst, a, b }
                    if a == allocated
                        && constant(b, 8, 8)
                        && register_at(
                            frame_require!(storage(graph, dst), "restored stack storage"),
                            RSP_OFFSET,
                            8,
                        ) =>
                {
                    dst
                }
                _ => frame_fail!("epilogue first stack advance"),
            };
        match frame_require!(block.ops.get(start + 3), "epilogue frame-restore op") {
            SSAOp::Copy { dst, src }
                if src == restored
                    && register_at(
                        frame_require!(storage(graph, dst), "restored frame storage"),
                        RBP_OFFSET,
                        8,
                    ) => {}
            _ => frame_fail!("epilogue frame restore"),
        }
        let target = match frame_require!(block.ops.get(start + 4), "epilogue target-load op") {
            SSAOp::Load { dst, addr, .. }
                if addr == restored_stack
                    && register_at(
                        frame_require!(storage(graph, dst), "return target storage"),
                        RIP_OFFSET,
                        8,
                    ) =>
            {
                dst
            }
            _ => frame_fail!("epilogue target load"),
        };
        let final_stack =
            match frame_require!(block.ops.get(start + 5), "epilogue second-stack-advance op") {
                SSAOp::IntAdd { dst, a, b }
                    if a == restored_stack
                        && constant(b, 8, 8)
                        && register_at(
                            frame_require!(storage(graph, dst), "final stack storage"),
                            RSP_OFFSET,
                            8,
                        ) =>
                {
                    dst
                }
                _ => frame_fail!("epilogue second stack advance"),
            };
        let dead_value = frame_require!(value(graph, dead), "epilogue dead-seed value");
        let dead_uses = frame_require!(
            graph.uses_of.get(dead_value.0 as usize),
            "epilogue dead-seed uses"
        );
        if !matches!(frame_require!(block.ops.get(start + 6), "epilogue return op"), SSAOp::Return { target: actual } if actual == target)
            || !dead_uses.is_empty()
            || final_stack.size != 8
            || machine.memory_space_at(block_addr, start + 1) != Some(memory_space)
            || machine.memory_space_at(block_addr, start + 4) != Some(memory_space)
        {
            frame_fail!("epilogue closure/memory");
        }
        (start..start + 7)
            .map(|index| {
                Some(frame_require!(
                    graph.inst_id_for_op_site(block_addr, index),
                    "epilogue instruction site"
                ))
            })
            .collect::<Option<Vec<_>>>()
            .map(Vec::into_boxed_slice)
    };

    Some(SumArrayO2FrameFact {
        memory_space,
        entry_stack: match &entry.ops[1] {
            SSAOp::IntSub { a, .. } => {
                frame_require!(value(graph, a), "entry stack graph value")
            }
            _ => return None,
        },
        saved_frame_pointer: frame_require!(value(graph, saved), "saved frame pointer graph value"),
        allocated_stack: frame_require!(value(graph, allocated), "allocated stack graph value"),
        prologue: (0..4)
            .map(|index| {
                Some(frame_require!(
                    graph.inst_id_for_op_site(entry_addr, index),
                    "prologue instruction site"
                ))
            })
            .collect::<Option<Vec<_>>>()?
            .into_boxed_slice(),
        main_epilogue: check_epilogue(main_exit_addr, 0)?,
        zero_epilogue: check_epilogue(zero_exit_addr, 10)?,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_o2_return(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    block_addr: u64,
    return_index: usize,
    returned_low32: ValueId,
    physical_full_register: ValueId,
    return_storage: CanonicalStorageId,
    path: SumArrayO2ReturnPath,
) -> Option<SumArrayO2ReturnFact> {
    let block = function.get_block(block_addr)?;
    let return_inst = graph.inst_id_for_op_site(block_addr, return_index)?;
    let return_target = match block.ops.get(return_index)? {
        SSAOp::Return { target } => value(graph, target)?,
        _ => return None,
    };
    let producer = graph.def_inst(physical_full_register)?;
    let definition = SourceReturnRegisterDefinitionFact {
        storage: return_storage,
        value: physical_full_register,
        producer,
    };
    let boundary = boundaries.returns.get(&return_inst)?;
    if !boundary.complete
        || boundary.values.as_slice()
            != [crate::semantic::CallBoundaryValueFact {
                slot: CallBoundarySlot::Register {
                    index: 0,
                    storage: return_storage,
                },
                value: physical_full_register,
            }]
        || !boundary.register_compositions.is_empty()
        || graph.value(returned_low32)?.var.size != 4
        || graph.value(physical_full_register)?.var.size != 8
    {
        return None;
    }
    Some(SumArrayO2ReturnFact {
        path,
        block: block_addr,
        returned_low32,
        physical_full_register,
        definition,
        composition: None,
        return_target,
        return_inst,
    })
}

fn collect_o2_inventory(
    function: &SSAFunction,
    graph: &SsaGraph,
) -> Option<Vec<SumArrayInstructionDispositionFact>> {
    let mut inventory = Vec::new();
    for (block_index, block_addr) in function.block_addrs().iter().copied().enumerate() {
        let block = function.get_block(block_addr)?;
        for phi_index in 0..block.phis.len() {
            inventory.push(SumArrayInstructionDispositionFact {
                instruction: o2_phi_inst(graph, block_addr, phi_index)?,
                block_index: u32::try_from(block_index).ok()?,
                ordinal: u32::try_from(phi_index).ok()?,
                class: if matches!(block_index, 4 | 7 | 8) {
                    SumArrayInstructionClass::Semantic
                } else {
                    SumArrayInstructionClass::Structural
                },
            });
        }
        for op_index in 0..block.ops.len() {
            let class = if (block_index == 0 && op_index < 4)
                || (block_index == 8)
                || (block_index == 9 && op_index >= 10)
            {
                SumArrayInstructionClass::Frame
            } else if matches!(block_index, 0..=7 | 9) {
                SumArrayInstructionClass::Semantic
            } else {
                SumArrayInstructionClass::Structural
            };
            inventory.push(SumArrayInstructionDispositionFact {
                instruction: graph.inst_id_for_op_site(block_addr, op_index)?,
                block_index: u32::try_from(block_index).ok()?,
                ordinal: u32::try_from(block.phis.len().checked_add(op_index)?).ok()?,
                class,
            });
        }
    }
    Some(inventory)
}

fn collect_o2_selector_packet(
    block_addr: u64,
    block: &crate::function::SSABlock,
    graph: &SsaGraph,
    start: usize,
    selector: u32,
    sources: [&SSAVar; 4],
) -> Option<(Box<[InstId]>, ValueId)> {
    let mut term = None;
    let mut cursor = start;
    for (lane, source) in sources.into_iter().enumerate() {
        let equal = match block.ops.get(cursor)? {
            SSAOp::IntEqual { dst, a, b }
                if constant(a, u64::from(selector), 1)
                    && constant(b, u64::try_from(lane).ok()?, 1)
                    && dst.size == 1 =>
            {
                dst
            }
            _ => return None,
        };
        let enabled = match block.ops.get(cursor + 1)? {
            SSAOp::IntZExt { dst, src } if src == equal && dst.size == 4 => dst,
            _ => return None,
        };
        let selected = match block.ops.get(cursor + 2)? {
            SSAOp::IntMult { dst, a, b }
                if operands_are(a, b, enabled, source) && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        term = Some(if let Some(previous) = term {
            match block.ops.get(cursor + 3)? {
                SSAOp::IntAdd { dst, a, b }
                    if operands_are(a, b, previous, selected) && dst.size == 4 =>
                {
                    dst
                }
                _ => return None,
            }
        } else {
            selected
        });
        cursor += if lane == 0 { 3 } else { 4 };
    }
    if cursor != start + 15 {
        return None;
    }
    let instructions = (start..cursor)
        .map(|index| graph.inst_id_for_op_site(block_addr, index))
        .collect::<Option<Vec<_>>>()?
        .into_boxed_slice();
    let output = exact_def(graph, term?, *instructions.last()?)?;
    Some((instructions, output))
}

fn collect_o2_reduction(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    block_addr: u64,
    lanes: &[SumArrayO2LaneFact],
) -> Option<SumArrayO2ReductionFact> {
    let block = function.get_block(block_addr)?;
    let lane_values = lanes
        .iter()
        .map(|lane| graph.value(lane.next_value).map(|value| &value.var))
        .collect::<Option<Vec<_>>>()?;
    let lane_values: [&SSAVar; 8] = lane_values.try_into().ok()?;

    let mut pairwise_vars = Vec::new();
    let mut pairwise_values = Vec::new();
    let mut pairwise_adds = Vec::new();
    for lane in 0..4 {
        let add = graph.inst_id_for_op_site(block_addr, lane)?;
        let output = match block.ops.get(lane)? {
            SSAOp::IntAdd { dst, a, b }
                if operands_are(a, b, lane_values[lane], lane_values[lane + 4])
                    && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        pairwise_adds.push(add);
        pairwise_values.push(exact_def(graph, output, add)?);
        pairwise_vars.push(output);
    }
    let pairwise_vars: [&SSAVar; 4] = pairwise_vars.try_into().ok()?;

    let mut first_sources = Vec::new();
    for lane in 0..4 {
        let copied = match block.ops.get(4 + lane)? {
            SSAOp::Copy { dst, src } if src == pairwise_vars[lane] && dst.size == 4 => dst,
            _ => return None,
        };
        first_sources.push(copied);
    }
    let first_sources: [&SSAVar; 4] = first_sources.try_into().ok()?;
    let first_starts = [8, 23, 38, 53];
    let first_selectors = [2, 3, 2, 3];
    let mut packets = Vec::new();
    let mut first_selected = Vec::new();
    for (start, selector) in first_starts.into_iter().zip(first_selectors) {
        let (packet, selected) =
            collect_o2_selector_packet(block_addr, block, graph, start, selector, first_sources)?;
        packets.push(packet);
        first_selected.push(selected);
    }

    let mut horizontal_vars = Vec::new();
    for lane in 0..4 {
        let selected = &graph.value(first_selected[lane])?.var;
        let output = match block.ops.get(68 + lane)? {
            SSAOp::IntAdd { dst, a, b }
                if operands_are(a, b, selected, pairwise_vars[lane]) && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        horizontal_vars.push(output);
    }
    let horizontal_vars: [&SSAVar; 4] = horizontal_vars.try_into().ok()?;

    let mut second_sources = Vec::new();
    for lane in 0..4 {
        let copied = match block.ops.get(72 + lane)? {
            SSAOp::Copy { dst, src } if src == horizontal_vars[lane] && dst.size == 4 => dst,
            _ => return None,
        };
        second_sources.push(copied);
    }
    let second_sources: [&SSAVar; 4] = second_sources.try_into().ok()?;
    let mut second_selected = Vec::new();
    for start in [76, 91, 106, 121] {
        let (packet, selected) =
            collect_o2_selector_packet(block_addr, block, graph, start, 1, second_sources)?;
        packets.push(packet);
        second_selected.push(selected);
    }

    let mut final_vars = Vec::new();
    let mut final_ids = Vec::new();
    for lane in 0..4 {
        let selected = &graph.value(second_selected[lane])?.var;
        let add = graph.inst_id_for_op_site(block_addr, 136 + lane)?;
        let output = match block.ops.get(136 + lane)? {
            SSAOp::IntAdd { dst, a, b }
                if operands_are(a, b, selected, horizontal_vars[lane]) && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        final_ids.push(exact_def(graph, output, add)?);
        final_vars.push(output);
    }
    let low = final_vars[0];
    match block.ops.get(140)? {
        SSAOp::Copy { dst, src }
            if src == low && register_at(storage(graph, dst)?, RAX_OFFSET, 4) => {}
        _ => return None,
    }
    let full = match block.ops.get(141)? {
        SSAOp::IntZExt { dst, src }
            if src == low && register_at(storage(graph, dst)?, RAX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let zero_extend = graph.inst_id_for_op_site(block_addr, 141)?;

    Some(SumArrayO2ReductionFact {
        block: block_addr,
        input_lanes: lanes
            .iter()
            .map(|lane| lane.next_value)
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        pairwise_adds: pairwise_adds.into_boxed_slice(),
        pairwise_values: pairwise_values.into_boxed_slice(),
        selector_packets: packets.into_boxed_slice(),
        final_add: graph.inst_id_for_op_site(block_addr, 136)?,
        returned_low32: final_ids[0],
        zero_extend,
        physical_full_register: exact_def(graph, full, zero_extend)?,
        wraps_at_bits: 32,
    })
}

fn phi_source<'a>(phi: &'a crate::function::PhiNode, predecessor: u64) -> Option<&'a SSAVar> {
    let sources = phi
        .sources
        .iter()
        .filter(|(addr, _)| *addr == predecessor)
        .map(|(_, source)| source)
        .collect::<Vec<_>>();
    let [source] = sources.as_slice() else {
        return None;
    };
    Some(*source)
}

fn collect_o2_vector_loop(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    abi: &SumArrayAbiFact,
    preheader_addr: u64,
    header_addr: u64,
) -> Option<SumArrayO2VectorLoopFact> {
    let preheader = function.get_block(preheader_addr)?;
    let header = function.get_block(header_addr)?;
    let array_base = &graph.value(abi.parameters[0].graph_value)?.var;
    let length = &graph.value(abi.parameters[1].graph_value)?.var;

    let vector_count32 = match preheader.ops.get(4)? {
        SSAOp::IntAnd { dst, a, b }
            if a == length && constant(b, 0x7fff_fff8, 4) && dst.size == 4 =>
        {
            dst
        }
        _ => return None,
    };
    let _vector_count = match preheader.ops.get(5)? {
        SSAOp::IntZExt { dst, src } if src == vector_count32 && dst.size == 8 => dst,
        _ => return None,
    };
    let shifted = match (
        preheader.ops.get(12)?,
        preheader.ops.get(14)?,
        preheader.ops.get(16)?,
    ) {
        (
            SSAOp::Copy { src, .. },
            SSAOp::IntAnd { dst: amount, a, b },
            SSAOp::IntRight {
                dst,
                a: shifted_input,
                b: shifted_amount,
            },
        ) if src == length
            && constant(a, 3, 4)
            && constant(b, 31, 4)
            && shifted_input == length
            && shifted_amount == amount =>
        {
            dst
        }
        _ => return None,
    };
    let masked = match preheader.ops.get(54)? {
        SSAOp::IntAnd { dst, a, b }
            if a == shifted && constant(b, 0x0fff_ffff, 4) && dst.size == 4 =>
        {
            dst
        }
        _ => return None,
    };
    let masked_wide = match preheader.ops.get(55)? {
        SSAOp::IntZExt { dst, src } if src == masked && dst.size == 8 => dst,
        _ => return None,
    };
    let shift_amount = match preheader.ops.get(62)? {
        SSAOp::IntAnd { dst, a, b } if constant(a, 5, 4) && constant(b, 63, 4) && dst.size == 4 => {
            dst
        }
        _ => return None,
    };
    let bound = match preheader.ops.get(64)? {
        SSAOp::IntLeft { dst, a, b } if a == masked_wide && b == shift_amount && dst.size == 8 => {
            dst
        }
        _ => return None,
    };

    let first_zero = match preheader.ops.get(99)? {
        SSAOp::IntXor { dst, a, b } if a == b && dst.size == 16 => dst,
        _ => return None,
    };
    let second_zero = match preheader.ops.get(110)? {
        SSAOp::IntXor { dst, a, b } if a == b && dst.size == 16 => dst,
        _ => return None,
    };
    let byte_zero32 = match preheader.ops.get(102)? {
        SSAOp::IntXor { dst, a, b }
            if a == b && register_at(storage(graph, dst)?, RSI_OFFSET, 4) =>
        {
            dst
        }
        _ => return None,
    };
    let byte_zero = match preheader.ops.get(103)? {
        SSAOp::IntZExt { dst, src }
            if src == byte_zero32 && register_at(storage(graph, dst)?, RSI_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };

    let (byte_phi_index, byte_phi) = o2_phi_at(header, RSI_OFFSET, 8)?;
    let byte_phi_inst = o2_phi_inst(graph, header_addr, byte_phi_index)?;
    let byte_offset = exact_def(graph, &byte_phi.dst, byte_phi_inst)?;
    if byte_phi.sources.len() != 2
        || phi_source(byte_phi, preheader_addr)? != byte_zero
        || phi_source(byte_phi, header_addr)?
            != match header.ops.get(27)? {
                SSAOp::IntAdd { dst, .. } => dst,
                _ => return None,
            }
    {
        return None;
    }

    let scaled = match header.ops.get(0)? {
        SSAOp::IntMult { dst, a, b }
            if a == &byte_phi.dst && constant(b, 1, 8) && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let first_address = match header.ops.get(1)? {
        SSAOp::IntAdd { dst, a, b } if operands_are(a, b, array_base, scaled) && dst.size == 8 => {
            dst
        }
        _ => return None,
    };
    let (first_load, first_load_space) = match header.ops.get(2)? {
        SSAOp::Load {
            dst, space, addr, ..
        } if addr == first_address && dst.size == 16 => (dst, space),
        _ => return None,
    };
    match header.ops.get(3)? {
        SSAOp::Copy { src, .. } if src == first_load => {}
        _ => return None,
    }
    let advanced_base = match header.ops.get(12)? {
        SSAOp::IntAdd { dst, a, b }
            if operands_are(a, b, array_base, constant_ref(header.ops.get(12)?, 16, 8)?)
                && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let second_scaled = match header.ops.get(13)? {
        SSAOp::IntMult { dst, a, b }
            if a == &byte_phi.dst && constant(b, 1, 8) && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let second_address = match header.ops.get(14)? {
        SSAOp::IntAdd { dst, a, b }
            if operands_are(a, b, advanced_base, second_scaled) && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let (second_load, second_load_space) = match header.ops.get(15)? {
        SSAOp::Load {
            dst, space, addr, ..
        } if addr == second_address && dst.size == 16 => (dst, space),
        _ => return None,
    };
    match header.ops.get(16)? {
        SSAOp::Copy { src, .. } if src == second_load => {}
        _ => return None,
    }
    let memory_space = machine.memory_space_at(header_addr, 2)?;
    if second_load_space != first_load_space {
        return None;
    }

    let lane_offsets = [4608, 4612, 4616, 4620, 4672, 4676, 4680, 4684];
    let initial_indices = [111, 112, 113, 114, 115, 116, 117, 118];
    let projection_indices = [4, 6, 8, 10, 17, 19, 21, 23];
    let add_indices = [5, 7, 9, 11, 18, 20, 22, 24];
    let mut lanes = Vec::new();
    let mut read_projection_ids = [Vec::new(), Vec::new()];
    let mut read_lane_values = [Vec::new(), Vec::new()];
    for lane in 0..8 {
        let zero = if lane < 4 { first_zero } else { second_zero };
        let initial_index = initial_indices[lane];
        let initial_inst = graph.inst_id_for_op_site(preheader_addr, initial_index)?;
        let initial = match preheader.ops.get(initial_index)? {
            SSAOp::Subpiece { dst, src, offset }
                if src == zero
                    && *offset == u32::try_from((lane % 4) * 4).ok()?
                    && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        let initial_value = exact_def(graph, initial, initial_inst)?;
        let (phi_index, phi) = o2_phi_at(header, lane_offsets[lane], 4)?;
        let phi_inst = o2_phi_inst(graph, header_addr, phi_index)?;
        let phi_value = exact_def(graph, &phi.dst, phi_inst)?;
        if phi.sources.len() != 2 || phi_source(phi, preheader_addr)? != initial {
            return None;
        }
        let projection_index = projection_indices[lane];
        let projection_inst = graph.inst_id_for_op_site(header_addr, projection_index)?;
        let expected_load = if lane < 4 { first_load } else { second_load };
        let loaded = match header.ops.get(projection_index)? {
            SSAOp::Subpiece { dst, src, offset }
                if src == expected_load
                    && *offset == u32::try_from((lane % 4) * 4).ok()?
                    && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        let loaded_value = exact_def(graph, loaded, projection_inst)?;
        let add_index = add_indices[lane];
        let add_inst = graph.inst_id_for_op_site(header_addr, add_index)?;
        let next = match header.ops.get(add_index)? {
            SSAOp::IntAdd { dst, a, b }
                if operands_are(a, b, &phi.dst, loaded) && dst.size == 4 =>
            {
                dst
            }
            _ => return None,
        };
        let next_value = exact_def(graph, next, add_inst)?;
        if phi_source(phi, header_addr)? != next {
            return None;
        }
        let read = usize::from(lane >= 4);
        read_projection_ids[read].push(projection_inst);
        read_lane_values[read].push(loaded_value);
        lanes.push(SumArrayO2LaneFact {
            lane: u32::try_from(lane).ok()?,
            accumulator_storage: phi.canonical_storage?,
            initial_projection: initial_inst,
            initial_value,
            phi: phi_inst,
            phi_value,
            load_projection: projection_inst,
            loaded_value,
            add: add_inst,
            next_value,
            wraps_at_bits: 32,
        });
    }

    let induction = match header.ops.get(27)? {
        SSAOp::IntAdd { dst, a, b }
            if a == &byte_phi.dst
                && constant(b, 32, 8)
                && register_at(storage(graph, dst)?, RSI_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let bound_copy = match header.ops.get(34)? {
        SSAOp::Copy { dst, src } if src == bound && dst.size == 8 => dst,
        _ => return None,
    };
    let comparison = match header.ops.get(37)? {
        SSAOp::IntSub { dst, a, b } if a == bound_copy && b == induction && dst.size == 8 => dst,
        _ => return None,
    };
    let zero = match header.ops.get(39)? {
        SSAOp::IntEqual { dst, a, b } if a == comparison && constant(b, 0, 8) => dst,
        _ => return None,
    };
    let condition = match header.ops.get(44)? {
        SSAOp::BoolNot { dst, src } if src == zero => dst,
        _ => return None,
    };
    match header.ops.get(45)? {
        SSAOp::CBranch { cond, .. }
            if cond == condition
                && o2_conditional_edges(
                    function,
                    header_addr,
                    header_addr,
                    function
                        .successors(header_addr)
                        .into_iter()
                        .find(|target| *target != header_addr)?,
                ) => {}
        _ => return None,
    }

    let reads = [
        SumArrayO2VectorReadFact {
            order: 0,
            memory_space,
            address: value(graph, first_address)?,
            load: graph.inst_id_for_op_site(header_addr, 2)?,
            value: value(graph, first_load)?,
            size_bytes: 16,
            lane_projections: std::mem::take(&mut read_projection_ids[0]).into_boxed_slice(),
            lane_values: std::mem::take(&mut read_lane_values[0]).into_boxed_slice(),
        },
        SumArrayO2VectorReadFact {
            order: 1,
            memory_space,
            address: value(graph, second_address)?,
            load: graph.inst_id_for_op_site(header_addr, 15)?,
            value: value(graph, second_load)?,
            size_bytes: 16,
            lane_projections: std::mem::take(&mut read_projection_ids[1]).into_boxed_slice(),
            lane_values: std::mem::take(&mut read_lane_values[1]).into_boxed_slice(),
        },
    ];
    Some(SumArrayO2VectorLoopFact {
        preheader_block: preheader_addr,
        header_block: header_addr,
        byte_offset_phi: byte_phi_inst,
        byte_offset,
        bound: value(graph, bound)?,
        reads: Box::new(reads),
        lanes: lanes.into_boxed_slice(),
        induction_add: graph.inst_id_for_op_site(header_addr, 27)?,
        next_byte_offset: value(graph, induction)?,
        step_bytes: 32,
        back_edge: graph.inst_id_for_op_site(header_addr, 45)?,
    })
}

fn constant_ref(op: &SSAOp, expected: u64, size: u32) -> Option<&SSAVar> {
    match op {
        SSAOp::IntAdd { a, .. } if constant(a, expected, size) => Some(a),
        SSAOp::IntAdd { b, .. } if constant(b, expected, size) => Some(b),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_o2_scalar_tail(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    abi: &SumArrayAbiFact,
    gate_addr: u64,
    zero_addr: u64,
    bridge_addr: u64,
    header_addr: u64,
    exit_addr: u64,
    vector_loop: &SumArrayO2VectorLoopFact,
    reduction: &SumArrayO2ReductionFact,
) -> Option<SumArrayO2ScalarTailFact> {
    let gate = function.get_block(gate_addr)?;
    let zero = function.get_block(zero_addr)?;
    let bridge = function.get_block(bridge_addr)?;
    let header = function.get_block(header_addr)?;
    let exit = function.get_block(exit_addr)?;
    let array_base = &graph.value(abi.parameters[0].graph_value)?.var;
    let length32 = &graph.value(abi.parameters[1].graph_value)?.var;

    let zero_index32 = match zero.ops.get(2)? {
        SSAOp::IntXor { dst, a, b } if a == b && dst.size == 4 => dst,
        _ => return None,
    };
    let zero_index = match zero.ops.get(3)? {
        SSAOp::IntZExt { dst, src } if src == zero_index32 && dst.size == 8 => dst,
        _ => return None,
    };
    let zero_sum32 = match zero.ops.get(12)? {
        SSAOp::IntXor { dst, a, b } if a == b && dst.size == 4 => dst,
        _ => return None,
    };
    let zero_sum = match zero.ops.get(13)? {
        SSAOp::IntZExt { dst, src } if src == zero_sum32 && dst.size == 8 => dst,
        _ => return None,
    };
    let reduced_low = &graph.value(reduction.returned_low32)?.var;
    let reduced_full = &graph.value(reduction.physical_full_register)?.var;
    let vector_preheader = function.get_block(vector_loop.preheader_block)?;
    let vector_count32 = match vector_preheader.ops.get(4)? {
        SSAOp::IntAnd { dst, .. } => dst,
        _ => return None,
    };
    let vector_count = match vector_preheader.ops.get(5)? {
        SSAOp::IntZExt { dst, .. } => dst,
        _ => return None,
    };
    let vector_length = &graph.value(vector_loop.next_byte_offset)?.var;
    let bridge_length_low = match bridge.ops.get(2)? {
        SSAOp::Subpiece { dst, src, offset }
            if src == vector_length && *offset == 0 && dst.size == 4 =>
        {
            dst
        }
        _ => return None,
    };

    let (accumulator_low_index, accumulator_low_phi) = o2_phi_at(header, RAX_OFFSET, 4)?;
    let accumulator_low_inst = o2_phi_inst(graph, header_addr, accumulator_low_index)?;
    let accumulator_low = exact_def(graph, &accumulator_low_phi.dst, accumulator_low_inst)?;
    let (accumulator_index, accumulator_phi) = o2_phi_at(header, RAX_OFFSET, 8)?;
    let accumulator_inst = o2_phi_inst(graph, header_addr, accumulator_index)?;
    let accumulator = exact_def(graph, &accumulator_phi.dst, accumulator_inst)?;
    let (index_low_index, index_low_phi) = o2_phi_at(header, RDX_OFFSET, 4)?;
    let index_low_inst = o2_phi_inst(graph, header_addr, index_low_index)?;
    exact_def(graph, &index_low_phi.dst, index_low_inst)?;
    let (index_index, index_phi) = o2_phi_at(header, RDX_OFFSET, 8)?;
    let index_inst = o2_phi_inst(graph, header_addr, index_index)?;
    let index = exact_def(graph, &index_phi.dst, index_inst)?;
    let (length_low_index, length_low_phi) = o2_phi_at(header, RSI_OFFSET, 4)?;
    let length_low_inst = o2_phi_inst(graph, header_addr, length_low_index)?;
    exact_def(graph, &length_low_phi.dst, length_low_inst)?;
    let (length_index, length_phi) = o2_phi_at(header, RSI_OFFSET, 8)?;
    let length_inst = o2_phi_inst(graph, header_addr, length_index)?;
    let length = exact_def(graph, &length_phi.dst, length_inst)?;
    let expected_predecessors = BTreeSet::from([zero_addr, bridge_addr, header_addr]);
    for phi in [
        accumulator_low_phi,
        accumulator_phi,
        index_low_phi,
        index_phi,
        length_low_phi,
        length_phi,
    ] {
        if phi.sources.len() != 3
            || phi
                .sources
                .iter()
                .map(|(addr, _)| *addr)
                .collect::<BTreeSet<_>>()
                != expected_predecessors
        {
            return None;
        }
    }
    if phi_source(accumulator_low_phi, zero_addr)? != zero_sum32
        || phi_source(accumulator_low_phi, bridge_addr)? != reduced_low
        || phi_source(accumulator_phi, zero_addr)? != zero_sum
        || phi_source(accumulator_phi, bridge_addr)? != reduced_full
        || phi_source(index_low_phi, zero_addr)? != zero_index32
        || phi_source(index_low_phi, bridge_addr)? != vector_count32
        || phi_source(index_phi, zero_addr)? != zero_index
        || phi_source(index_phi, bridge_addr)? != vector_count
        || phi_source(length_low_phi, zero_addr)? != length32
        || phi_source(length_low_phi, bridge_addr)? != bridge_length_low
        || phi_source(length_phi, bridge_addr)? != vector_length
    {
        return None;
    }
    let zero_length_full = phi_source(length_phi, zero_addr)?;
    if zero_length_full.version != 0
        || zero_length_full.size != 8
        || !register_at(storage(graph, zero_length_full)?, RSI_OFFSET, 8)
        || graph.def_inst(value(graph, zero_length_full)?).is_some()
    {
        return None;
    }

    let scaled = match header.ops.get(0)? {
        SSAOp::IntMult { dst, a, b }
            if a == &index_phi.dst && constant(b, 4, 8) && dst.size == 8 =>
        {
            dst
        }
        _ => return None,
    };
    let address = match header.ops.get(1)? {
        SSAOp::IntAdd { dst, a, b } if operands_are(a, b, array_base, scaled) && dst.size == 8 => {
            dst
        }
        _ => return None,
    };
    let read_indices = [2, 5, 8];
    let slice_indices = [3, 6, 9];
    let mut reads = Vec::new();
    let mut loaded_vars = Vec::new();
    let scalar_memory_space = machine.memory_space_at(header_addr, 2)?;
    let mut scalar_space = None;
    for (order, (read_index, slice_index)) in
        read_indices.into_iter().zip(slice_indices).enumerate()
    {
        let (loaded, load_space) = match header.ops.get(read_index)? {
            SSAOp::Load {
                dst, space, addr, ..
            } if addr == address && dst.size == 4 => (dst, space),
            _ => return None,
        };
        if scalar_space.is_some_and(|expected| expected != load_space) {
            return None;
        }
        scalar_space = Some(load_space);
        match header.ops.get(slice_index)? {
            SSAOp::Subpiece { src, offset, .. } if src == &accumulator_phi.dst && *offset == 0 => {}
            _ => return None,
        }
        let load = graph.inst_id_for_op_site(header_addr, read_index)?;
        loaded_vars.push(loaded);
        reads.push(SumArrayReadFact {
            order: u32::try_from(order).ok()?,
            memory_space: scalar_memory_space,
            address: value(graph, address)?,
            load,
            value: exact_def(graph, loaded, load)?,
            size_bytes: 4,
        });
    }
    if reads
        .iter()
        .any(|read| read.memory_space != vector_loop.reads[0].memory_space)
    {
        return None;
    }
    let final_slice = match header.ops.get(9)? {
        SSAOp::Subpiece { dst, .. } => dst,
        _ => return None,
    };
    let add = graph.inst_id_for_op_site(header_addr, 10)?;
    let next_low = match header.ops.get(10)? {
        SSAOp::IntAdd { dst, a, b }
            if operands_are(a, b, final_slice, loaded_vars[2]) && dst.size == 4 =>
        {
            dst
        }
        _ => return None,
    };
    let next_low_value = exact_def(graph, next_low, add)?;
    let next_full = match header.ops.get(11)? {
        SSAOp::IntZExt { dst, src }
            if src == next_low && register_at(storage(graph, dst)?, RAX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let next_full_value = exact_def(
        graph,
        next_full,
        graph.inst_id_for_op_site(header_addr, 11)?,
    )?;
    let increment = graph.inst_id_for_op_site(header_addr, 19)?;
    let next_index = match header.ops.get(19)? {
        SSAOp::IntAdd { dst, a, b }
            if a == &index_phi.dst
                && constant(b, 1, 8)
                && register_at(storage(graph, dst)?, RDX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let next_index_value = exact_def(graph, next_index, increment)?;
    let original_length = match gate.ops.get(1)? {
        SSAOp::IntZExt { dst, src } if src == length32 => dst,
        _ => return None,
    };
    let copied_length = match header.ops.get(26)? {
        SSAOp::Copy { dst, src } if src == original_length && dst.size == 8 => dst,
        _ => return None,
    };
    let difference = match header.ops.get(29)? {
        SSAOp::IntSub { dst, a, b } if a == copied_length && b == next_index && dst.size == 8 => {
            dst
        }
        _ => return None,
    };
    let zero_flag = match header.ops.get(31)? {
        SSAOp::IntEqual { dst, a, b } if a == difference && constant(b, 0, 8) => dst,
        _ => return None,
    };
    let condition = match header.ops.get(36)? {
        SSAOp::BoolNot { dst, src } if src == zero_flag => dst,
        _ => return None,
    };
    let self_index_low = match header.ops.get(37)? {
        SSAOp::Subpiece { dst, src, offset } if src == next_index && *offset == 0 => dst,
        _ => return None,
    };
    let self_length_low = match header.ops.get(38)? {
        SSAOp::Subpiece { dst, src, offset } if src == &length_phi.dst && *offset == 0 => dst,
        _ => return None,
    };
    if phi_source(accumulator_low_phi, header_addr)? != next_low
        || phi_source(accumulator_phi, header_addr)? != next_full
        || phi_source(index_low_phi, header_addr)? != self_index_low
        || phi_source(index_phi, header_addr)? != next_index
        || phi_source(length_low_phi, header_addr)? != self_length_low
        || phi_source(length_phi, header_addr)? != &length_phi.dst
        || !matches!(header.ops.get(41)?, SSAOp::CBranch { cond, .. }
            if cond == condition && o2_conditional_edges(function, header_addr, header_addr, exit_addr))
    {
        return None;
    }

    let (_, exit_low_phi) = o2_phi_at(exit, RAX_OFFSET, 4)?;
    let (_, exit_full_phi) = o2_phi_at(exit, RAX_OFFSET, 8)?;
    if exit_low_phi.sources.len() != 2
        || exit_full_phi.sources.len() != 2
        || phi_source(exit_low_phi, reduction.block)? != reduced_low
        || phi_source(exit_low_phi, header_addr)? != next_low
        || phi_source(exit_full_phi, reduction.block)? != reduced_full
        || phi_source(exit_full_phi, header_addr)? != next_full
        || accumulator_low != value(graph, &accumulator_low_phi.dst)?
        || next_low_value != value(graph, next_low)?
        || next_full_value != value(graph, next_full)?
    {
        return None;
    }

    Some(SumArrayO2ScalarTailFact {
        header_block: header_addr,
        accumulator_phi: accumulator_inst,
        accumulator,
        index_phi: index_inst,
        index,
        length_phi: length_inst,
        length,
        scale: graph.inst_id_for_op_site(header_addr, 0)?,
        element_address: value(graph, address)?,
        reads: reads.into_boxed_slice(),
        add,
        next_accumulator: next_full_value,
        increment,
        next_index: next_index_value,
        back_edge: graph.inst_id_for_op_site(header_addr, 41)?,
        wraps_at_bits: 32,
    })
}

#[allow(clippy::too_many_arguments)]
fn collect_o2_guards(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    abi: &SumArrayAbiFact,
    entry_addr: u64,
    gate_addr: u64,
    preheader_addr: u64,
    reduction_addr: u64,
    exit_addr: u64,
    zero_exit_addr: u64,
) -> Option<Vec<SumArrayO2GuardFact>> {
    let length = &graph.value(abi.parameters[1].graph_value)?.var;
    let entry = function.get_block(entry_addr)?;
    let tested = match entry.ops.get(6)? {
        SSAOp::IntAnd { dst, a, b } if a == length && b == length && dst.size == 4 => dst,
        _ => return None,
    };
    match (&entry.ops[4], &entry.ops[5]) {
        (
            SSAOp::Copy {
                dst: cf,
                src: zero_cf,
            },
            SSAOp::Copy {
                dst: of,
                src: zero_of,
            },
        ) if constant(zero_cf, 0, 1)
            && constant(zero_of, 0, 1)
            && register_at(storage(graph, cf)?, CF_OFFSET, 1)
            && register_at(storage(graph, of)?, OF_OFFSET, 1) => {}
        _ => return None,
    }
    match_flag_packet(&entry.ops[7..13], graph, tested, 4)?;
    let signed_or_zero = match (&entry.ops[13], &entry.ops[14]) {
        (
            SSAOp::IntNotEqual { dst: signed, a, b },
            SSAOp::BoolOr {
                dst,
                a: zero,
                b: signed_input,
            },
        ) if signed_input == signed
            && register_at(storage(graph, a)?, OF_OFFSET, 1)
            && register_at(storage(graph, b)?, SF_OFFSET, 1)
            && register_at(storage(graph, zero)?, ZF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    match entry.ops.get(15)? {
        SSAOp::CBranch { cond, .. }
            if cond == signed_or_zero
                && o2_conditional_edges(function, entry_addr, zero_exit_addr, gate_addr) => {}
        _ => return None,
    }

    let gate = function.get_block(gate_addr)?;
    match (&gate.ops[0], &gate.ops[1]) {
        (SSAOp::Copy { src: low, .. }, SSAOp::IntZExt { src: wide_src, .. })
            if low == length && wide_src == length => {}
        _ => return None,
    }
    let copied = match gate.ops.get(2)? {
        SSAOp::Copy { dst, src } if src == length && dst.size == 4 => dst,
        _ => return None,
    };
    let carry = match gate.ops.get(3)? {
        SSAOp::IntLess { dst, a, b }
            if a == copied
                && constant(b, 8, 4)
                && register_at(storage(graph, dst)?, CF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let difference = match gate.ops.get(5)? {
        SSAOp::IntSub { dst, a, b } if a == copied && constant(b, 8, 4) => dst,
        _ => return None,
    };
    match_flag_packet(&gate.ops[6..12], graph, difference, 4)?;
    let at_least_eight = match gate.ops.get(12)? {
        SSAOp::BoolNot { dst, src } if src == carry => dst,
        _ => return None,
    };
    match gate.ops.get(13)? {
        SSAOp::CBranch { cond, .. }
            if cond == at_least_eight
                && o2_conditional_edges(
                    function,
                    gate_addr,
                    preheader_addr,
                    function
                        .successors(gate_addr)
                        .into_iter()
                        .find(|target| *target != preheader_addr)?,
                ) => {}
        _ => return None,
    }

    let preheader = function.get_block(preheader_addr)?;
    let vector_count = match preheader.ops.get(4)? {
        SSAOp::IntAnd { dst, a, b } if a == length && constant(b, 0x7fff_fff8, 4) => dst,
        _ => return None,
    };
    let reduction = function.get_block(reduction_addr)?;
    let copied_count = match reduction.ops.get(142)? {
        SSAOp::Copy { dst, src } if src == vector_count && dst.size == 4 => dst,
        _ => return None,
    };
    let tail_difference = match reduction.ops.get(145)? {
        SSAOp::IntSub { dst, a, b } if a == copied_count && b == length => dst,
        _ => return None,
    };
    match_flag_packet(&reduction.ops[146..152], graph, tail_difference, 4)?;
    let tail_equal = match reduction.ops.get(147)? {
        SSAOp::IntEqual { dst, .. } => dst,
        _ => return None,
    };
    let vector_length = match function.get_block(function.block_addrs()[4])?.ops.get(27)? {
        SSAOp::IntAdd { dst, .. } => dst,
        _ => return None,
    };
    match reduction.ops.get(152)? {
        SSAOp::Subpiece { src, offset, .. } if src == vector_length && *offset == 0 => {}
        _ => return None,
    }
    match reduction.ops.get(153)? {
        SSAOp::CBranch { cond, .. }
            if cond == tail_equal
                && o2_conditional_edges(
                    function,
                    reduction_addr,
                    exit_addr,
                    function
                        .successors(reduction_addr)
                        .into_iter()
                        .find(|target| *target != exit_addr)?,
                ) => {}
        _ => return None,
    }

    Some(vec![
        SumArrayO2GuardFact {
            block: entry_addr,
            input: abi.parameters[1].graph_value,
            condition: value(graph, signed_or_zero)?,
            branch: graph.inst_id_for_op_site(entry_addr, 15)?,
            signed_width_bits: 32,
        },
        SumArrayO2GuardFact {
            block: gate_addr,
            input: abi.parameters[1].graph_value,
            condition: value(graph, at_least_eight)?,
            branch: graph.inst_id_for_op_site(gate_addr, 13)?,
            signed_width_bits: 32,
        },
        SumArrayO2GuardFact {
            block: reduction_addr,
            input: value(graph, vector_count)?,
            condition: value(graph, tail_equal)?,
            branch: graph.inst_id_for_op_site(reduction_addr, 153)?,
            signed_width_bits: 32,
        },
    ])
}

fn o2_conditional_edges(
    function: &SSAFunction,
    block: u64,
    true_target: u64,
    false_target: u64,
) -> bool {
    matches!(
        function.cfg().edge_type(block, true_target),
        Some(crate::cfg::CFGEdge::True | crate::cfg::CFGEdge::Back)
    ) && function.cfg().edge_type(block, false_target) == Some(crate::cfg::CFGEdge::False)
}

fn collect_o2_lane_refusal(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
) -> Option<SumArrayRefusalFact> {
    let counts = function
        .blocks()
        .map(|block| (block.ops.len(), block.phis.len()))
        .collect::<Vec<_>>();
    let reason = stale_o2_refusal_reason(&counts)?;
    if function.block_addrs().len() != 10
        || function.entry != function.block_addrs()[0]
        || collect_types(machine)
            .and_then(|types| collect_abi(graph, machine, &types, false))
            .is_none()
    {
        return None;
    }
    let vector_addr = function.block_addrs()[4];
    let vector = function.get_block(vector_addr)?;
    let loads = vector
        .ops
        .iter()
        .enumerate()
        .filter_map(|(index, op)| match op {
            SSAOp::Load { dst, .. } if dst.size == 16 => Some((index, dst)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [(first_index, first), (second_index, second)] = loads.as_slice() else {
        return None;
    };
    if *first_index >= *second_index
        || machine.memory_space_at(vector_addr, *first_index)
            != machine.memory_space_at(vector_addr, *second_index)
    {
        return None;
    }
    let proven_lane_count = [first, second]
        .into_iter()
        .map(|load| explicit_lane_offsets(function, load))
        .map(|offsets| offsets.intersection(&BTreeSet::from([0, 4, 8, 12])).count())
        .sum::<usize>();
    Some(SumArrayRefusalFact {
        entry: function.entry,
        lowering: SumArrayLowering::O2Vectorized,
        reason,
        vector_read_count: 2,
        expected_lane_count: 8,
        proven_lane_count: u32::try_from(proven_lane_count).ok()?,
    })
}

const STALE_O2_INVENTORY: [(usize, usize); 10] = [
    (16, 0),
    (14, 0),
    (21, 0),
    (111, 0),
    (40, 27),
    (153, 0),
    (2, 0),
    (38, 103),
    (7, 103),
    (17, 0),
];

fn is_stale_o2_inventory(counts: &[(usize, usize)]) -> bool {
    counts == STALE_O2_INVENTORY
}

fn stale_o2_refusal_reason(counts: &[(usize, usize)]) -> Option<SumArrayRefusalReason> {
    is_stale_o2_inventory(counts).then_some(SumArrayRefusalReason::IncompleteVectorLaneProvenance)
}

fn explicit_lane_offsets(function: &SSAFunction, load: &&SSAVar) -> BTreeSet<u32> {
    function
        .blocks()
        .flat_map(|block| &block.ops)
        .filter_map(|op| match op {
            SSAOp::Subpiece { dst, src, offset } if src == *load && dst.size == 4 => Some(*offset),
            _ => None,
        })
        .collect()
}

fn o2_op_code(op: &SSAOp) -> char {
    match op {
        SSAOp::Copy { .. } => 'C',
        SSAOp::Load { .. } => 'L',
        SSAOp::Store { .. } => 'S',
        SSAOp::IntAdd { .. } => 'A',
        SSAOp::IntSub { .. } => 'U',
        SSAOp::IntMult { .. } => 'M',
        SSAOp::IntCarry { .. } => 'Y',
        SSAOp::IntSCarry { .. } => 'G',
        SSAOp::IntSBorrow { .. } => 'W',
        SSAOp::IntLess { .. } => 'D',
        SSAOp::IntSLess { .. } => 'd',
        SSAOp::IntEqual { .. } => 'E',
        SSAOp::IntNotEqual { .. } => 'N',
        SSAOp::IntAnd { .. } => 'a',
        SSAOp::IntOr { .. } => 'o',
        SSAOp::IntXor { .. } => 'x',
        SSAOp::IntRight { .. } => 'r',
        SSAOp::IntLeft { .. } => 'l',
        SSAOp::IntZExt { .. } => 'Z',
        SSAOp::IntSExt { .. } => 'X',
        SSAOp::PopCount { .. } => 'P',
        SSAOp::BoolNot { .. } => 'B',
        SSAOp::BoolOr { .. } => 'O',
        SSAOp::Branch { .. } => 'J',
        SSAOp::CBranch { .. } => 'Q',
        SSAOp::Return { .. } => 'R',
        SSAOp::Subpiece { .. } => 's',
        _ => '\0',
    }
}

fn matches_o2_signature(ops: &[SSAOp], signature: &str) -> bool {
    ops.len() == signature.len()
        && ops
            .iter()
            .zip(signature.chars())
            .all(|(op, expected)| o2_op_code(op) == expected)
}

fn o2_phi_at(
    block: &crate::function::SSABlock,
    offset: u64,
    size: u32,
) -> Option<(usize, &crate::function::PhiNode)> {
    let matches = block
        .phis
        .iter()
        .enumerate()
        .filter(|(_, phi)| {
            phi.canonical_storage
                .is_some_and(|storage| register_at(storage, offset, size))
        })
        .collect::<Vec<_>>();
    let [found] = matches.as_slice() else {
        return None;
    };
    Some(*found)
}

fn o2_phi_inst(graph: &SsaGraph, block_addr: u64, phi_index: usize) -> Option<InstId> {
    graph
        .block(graph.block_id_for_addr(block_addr)?)?
        .insts
        .get(phi_index)
        .copied()
}

fn exact_def(graph: &SsaGraph, var: &SSAVar, producer: InstId) -> Option<ValueId> {
    let value = value(graph, var)?;
    (graph.def_inst(value) == Some(producer)).then_some(value)
}

fn operands_are(a: &SSAVar, b: &SSAVar, first: &SSAVar, second: &SSAVar) -> bool {
    (a == first && b == second) || (a == second && b == first)
}

const O2_BLOCK_SIGNATURES: [&str; 10] = [
    "CUSCCCadEaPaENOQ",
    "CZCDWUdEaPaEBQ",
    "CCxZdEaPaECCxZdEaPaEJ",
    "CZCCaZdEaPaECZaCrZNUraNBaaoEdBaaoNdBaaoEBaaoaPaEBaaoCCaZdEaPaEaClNUldBaaoEdxBaaoNdBaaoEBaaoaPaEBaaoxCCxZdEaPaExssssssss",
    "MALCsAsAsAsAAMALCsAsAsAsAYGAdEaPaECDWUdEaPaEBQ",
    "AAAACCCCEZMEZMAEZMAEZMAEZMEZMAEZMAEZMAEZMEZMAEZMAEZMAEZMEZMAEZMAEZMAAAAACCCCEZMEZMAEZMAEZMAEZMEZMAEZMAEZMAEZMEZMAEZMAEZMAEZMEZMAEZMAEZMAAAAACZCDWUdEaPaEsQ",
    "MAs",
    "MALsYLsGLsAZdEaPaEGAdEaPaECDWUdEaPaEBssssQ",
    "CLACLAR",
    "CCxZdEaPaECLACLAR",
];

fn match_flag_packet(
    ops: &[SSAOp],
    graph: &SsaGraph,
    input: &SSAVar,
    size: u32,
) -> Option<()> {
    let [sign, zero, low, population, parity, parity_equal] = ops else {
        return None;
    };
    let low_var = match low {
        SSAOp::IntAnd { dst, a, b } if a == input && constant(b, 0xff, size) => dst,
        _ => return None,
    };
    let population_var = match population {
        SSAOp::PopCount { dst, src } if src == low_var => dst,
        _ => return None,
    };
    let parity_var = match parity {
        SSAOp::IntAnd { dst, a, b } if a == population_var && constant(b, 1, 1) => dst,
        _ => return None,
    };
    if !matches!(sign, SSAOp::IntSLess { dst, a, b }
        if a == input && constant(b, 0, size) && register_at(storage(graph, dst)?, SF_OFFSET, 1))
        || !matches!(zero, SSAOp::IntEqual { dst, a, b }
            if a == input && constant(b, 0, size) && register_at(storage(graph, dst)?, ZF_OFFSET, 1))
        || !matches!(parity_equal, SSAOp::IntEqual { dst, a, b }
            if a == parity_var && constant(b, 0, 1) && register_at(storage(graph, dst)?, PF_OFFSET, 1))
    {
        return None;
    }
    Some(())
}

fn match_flag_tail(
    ops: &[SSAOp],
    graph: &SsaGraph,
    input: &SSAVar,
    size: u32,
) -> Option<()> {
    let [zero, low, population, parity, parity_equal] = ops else {
        return None;
    };
    let low_var = match low {
        SSAOp::IntAnd { dst, a, b } if a == input && constant(b, 0xff, size) => dst,
        _ => return None,
    };
    let population_var = match population {
        SSAOp::PopCount { dst, src } if src == low_var => dst,
        _ => return None,
    };
    let parity_var = match parity {
        SSAOp::IntAnd { dst, a, b } if a == population_var && constant(b, 1, 1) => dst,
        _ => return None,
    };
    if !matches!(zero, SSAOp::IntEqual { dst, a, b }
        if a == input && constant(b, 0, size) && register_at(storage(graph, dst)?, ZF_OFFSET, 1))
        || !matches!(parity_equal, SSAOp::IntEqual { dst, a, b }
            if a == parity_var && constant(b, 0, 1) && register_at(storage(graph, dst)?, PF_OFFSET, 1))
    {
        return None;
    }
    Some(())
}

fn as_set(values: Vec<u64>) -> BTreeSet<u64> {
    values.into_iter().collect()
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

#[derive(Clone, Copy)]
enum OpKind {
    Copy,
    Load,
    Store,
    IntAdd,
    IntSub,
    IntMult,
    IntCarry,
    IntSCarry,
    IntSBorrow,
    IntLess,
    IntSLess,
    IntEqual,
    IntAnd,
    IntZExt,
    IntSExt,
    PopCount,
    Branch,
    CBranch,
    Return,
}

impl OpKind {
    fn matches(self, op: &SSAOp) -> bool {
        matches!(
            (self, op),
            (Self::Copy, SSAOp::Copy { .. })
                | (Self::Load, SSAOp::Load { .. })
                | (Self::Store, SSAOp::Store { .. })
                | (Self::IntAdd, SSAOp::IntAdd { .. })
                | (Self::IntSub, SSAOp::IntSub { .. })
                | (Self::IntMult, SSAOp::IntMult { .. })
                | (Self::IntCarry, SSAOp::IntCarry { .. })
                | (Self::IntSCarry, SSAOp::IntSCarry { .. })
                | (Self::IntSBorrow, SSAOp::IntSBorrow { .. })
                | (Self::IntLess, SSAOp::IntLess { .. })
                | (Self::IntSLess, SSAOp::IntSLess { .. })
                | (Self::IntEqual, SSAOp::IntEqual { .. })
                | (Self::IntAnd, SSAOp::IntAnd { .. })
                | (Self::IntZExt, SSAOp::IntZExt { .. })
                | (Self::IntSExt, SSAOp::IntSExt { .. })
                | (Self::PopCount, SSAOp::PopCount { .. })
                | (Self::Branch, SSAOp::Branch { .. })
                | (Self::CBranch, SSAOp::CBranch { .. })
                | (Self::Return, SSAOp::Return { .. })
        )
    }
}

fn matches_kinds(ops: &[SSAOp], expected: &[OpKind]) -> bool {
    ops.len() == expected.len() && ops.iter().zip(expected).all(|(op, kind)| kind.matches(op))
}

const O0_ENTRY_KINDS: [OpKind; 16] = [
    OpKind::Copy,
    OpKind::IntSub,
    OpKind::Store,
    OpKind::Copy,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Store,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Store,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Store,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Store,
];

const O0_HEADER_KINDS: [OpKind; 18] = [
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::Copy,
    OpKind::IntZExt,
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::Copy,
    OpKind::IntLess,
    OpKind::IntSBorrow,
    OpKind::IntSub,
    OpKind::IntSLess,
    OpKind::IntEqual,
    OpKind::IntAnd,
    OpKind::PopCount,
    OpKind::IntAnd,
    OpKind::IntEqual,
    OpKind::IntEqual,
    OpKind::CBranch,
];

const O0_BODY_KINDS: [OpKind; 46] = [
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::Copy,
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::IntSExt,
    OpKind::IntMult,
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::Copy,
    OpKind::IntZExt,
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::IntCarry,
    OpKind::Load,
    OpKind::IntSCarry,
    OpKind::Load,
    OpKind::IntAdd,
    OpKind::IntZExt,
    OpKind::IntSLess,
    OpKind::IntEqual,
    OpKind::IntAnd,
    OpKind::PopCount,
    OpKind::IntAnd,
    OpKind::IntEqual,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Store,
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::Copy,
    OpKind::IntZExt,
    OpKind::IntCarry,
    OpKind::IntSCarry,
    OpKind::IntAdd,
    OpKind::IntZExt,
    OpKind::IntSLess,
    OpKind::IntEqual,
    OpKind::IntAnd,
    OpKind::PopCount,
    OpKind::IntAnd,
    OpKind::IntEqual,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Store,
    OpKind::Branch,
];

const O0_EXIT_KINDS: [OpKind; 11] = [
    OpKind::IntAdd,
    OpKind::Load,
    OpKind::Copy,
    OpKind::IntZExt,
    OpKind::Copy,
    OpKind::Load,
    OpKind::IntAdd,
    OpKind::Copy,
    OpKind::Load,
    OpKind::IntAdd,
    OpKind::Return,
];

#[cfg(all(test, feature = "sleigh-config"))]
mod tests {
    use r2il::{AddressSpace, R2ILBlock, R2ILOp, Varnode};
    use r2sleigh_lift::{Disassembler, build_arch_spec};

    use crate::{
        SourceAbiParameterSpec, SourceCarrierProjection, SourceFunctionInterface,
        SourceFunctionReturn, SourceLogicalValue, SourceStackSlotSpec, SourceType, SourceTypeGraph,
        SsaArtifact,
    };

    use super::*;

    fn decode_hex(encoded: &str) -> Vec<u8> {
        encoded
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| {
                let high = (pair[0] as char).to_digit(16).expect("hex digit") as u8;
                let low = (pair[1] as char).to_digit(16).expect("hex digit") as u8;
                (high << 4) | low
            })
            .collect()
    }

    fn x86() -> (r2il::ArchSpec, Disassembler) {
        let arch = build_arch_spec(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("x86-64 architecture");
        let disassembler = Disassembler::from_sla(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "x86-64",
        )
        .expect("x86-64 disassembler");
        (arch, disassembler)
    }

    fn full_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn types() -> SourceTypeGraph {
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            [],
        )
        .expect("sum-array types")
    }

    fn interface(
        revision: &[u8],
        homes: bool,
        calling_convention: &str,
    ) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let stack_slots = homes.then(|| {
            vec![
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -20,
                    4,
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -16,
                    4,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -12,
                    4,
                    1,
                    full_storage(RSI_OFFSET),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -8,
                    8,
                    0,
                    full_storage(RDI_OFFSET),
                ),
            ]
        });
        SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            calling_convention,
            [
                SourceAbiParameterSpec::new(0, full_storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, full_storage(RSI_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: full_storage(RAX_OFFSET),
            },
            stack_slots.unwrap_or_default(),
            [
                SourceLogicalValue::new(
                    1,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(types()),
        )
        .expect("exact sum-array interface")
    }

    fn lift_blocks(base: u64, encoded: &[&str]) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
        let (mut arch, disassembler) = x86();
        let mut address = base;
        let blocks = encoded
            .iter()
            .map(|encoded| {
                let bytes = decode_hex(encoded);
                let block = disassembler
                    .lift_block(&bytes, address, bytes.len())
                    .expect("pinned x86 block");
                address += bytes.len() as u64;
                block
            })
            .collect::<Vec<_>>();
        let lifted_spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        for space in lifted_spaces {
            if !arch.spaces.iter().any(|candidate| candidate.id == space) {
                arch.add_space(AddressSpace::new(space, "sleigh-data", 8));
            }
        }
        (arch, blocks)
    }

    fn o0_blocks(base: u64) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
        lift_blocks(
            base,
            &[
                "554889e548897df88975f4c745f000000000c745ec00000000",
                "8b45ec3b45f47d1c",
                "488b45f848634dec8b04880345f08945f08b45ec83c0018945ecebdc",
                "8b45f05dc3",
            ],
        )
    }

    fn o2_blocks(base: u64) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
        lift_blocks(
            base,
            &[
                "554889e585f67e0d",
                "89f183fe08730a",
                "31d231c0eb6b",
                "31c05dc3",
                "89ca81e2f8ffff7f89c8c1e80325ffffff0f48c1e005660fefc031f6660fefc90f1f8000000000",
                "f30f6f1437660ffec2f30f6f543710660ffeca4883c6204839f075e4",
                "660ffec8660f70c1ee660ffec1660f70c855660ffec8660f7ec839ca7411",
                "660f1f440000",
                "03049748ffc24839d175f5",
                "5dc3",
            ],
        )
    }

    fn o0_artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let (arch, blocks) = o0_blocks(base);
        SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(revision, true, "sysv_amd64"),
        )
        .expect("prepared O0 sum-array artifact")
    }

    fn o2_artifact(base: u64, revision: &[u8]) -> SsaArtifact {
        let (arch, blocks) = o2_blocks(base);
        SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(revision, false, "sysv_amd64"),
        )
        .expect("prepared O2 sum-array artifact")
    }

    #[test]
    fn exact_o0_sum_array_closes_every_instruction_and_phi() {
        let artifact = o0_artifact(0x1000_0610, b"sum-array-o0-a");
        let fact = artifact
            .structured()
            .sum_arrays
            .get(&artifact.function().entry)
            .expect("exact O0 fact");
        assert_eq!(fact.lowering, SumArrayLowering::O0ScalarHomes);
        assert_eq!(
            fact.instruction_inventory.len(),
            artifact.graph().insts.len()
        );
        assert_eq!(fact.homes.len(), 4);
        assert_eq!(fact.scalar_loop.reads.len(), 1);
        assert_eq!(fact.scalar_loop.prior_sum_reads.len(), 3);
        assert_eq!(fact.returned.composition, None);
        assert!(fact.validate_against(&artifact));
    }

    #[test]
    fn o0_recognition_is_relocation_and_cosmetic_revision_independent() {
        let first = o0_artifact(0x1000_0610, b"cosmetic-source-a");
        let second = o0_artifact(0x2000_0610, b"cosmetic-source-b");
        let first_fact = first
            .structured()
            .sum_arrays
            .values()
            .next()
            .expect("first fact");
        let second_fact = second
            .structured()
            .sum_arrays
            .values()
            .next()
            .expect("second fact");
        assert_eq!(first_fact.lowering, second_fact.lowering);
        assert_eq!(first_fact.types, second_fact.types);
        assert_eq!(
            first_fact.instruction_inventory.len(),
            second_fact.instruction_inventory.len()
        );
        assert_eq!(
            first_fact
                .instruction_inventory
                .iter()
                .map(|item| item.class)
                .collect::<Vec<_>>(),
            second_fact
                .instruction_inventory
                .iter()
                .map(|item| item.class)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn o0_semantic_mutation_and_wrong_abi_fail_closed() {
        let (arch, mut blocks) = o0_blocks(0x1000_0610);
        let body = blocks.get_mut(2).expect("body block");
        let multiply = body
            .ops
            .iter_mut()
            .find_map(|op| match op {
                R2ILOp::IntMult { b, .. } if b.offset == 4 => Some(b),
                _ => None,
            })
            .expect("element scale");
        *multiply = Varnode::constant(8, 8);
        let mutated = SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(b"sum-array-mutated", true, "sysv_amd64"),
        )
        .expect("mutated artifact remains analyzable");
        assert!(mutated.structured().sum_arrays.is_empty());

        let (arch, blocks) = o0_blocks(0x1000_0610);
        let wrong_abi = SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(b"sum-array-wrong-abi", true, "win64"),
        )
        .expect("wrong-ABI artifact remains analyzable");
        assert!(wrong_abi.structured().sum_arrays.is_empty());
    }

    #[test]
    fn exact_o2_sum_array_closes_vector_reduction_tail_and_returns() {
        let artifact = o2_artifact(0x1000_0620, b"sum-array-o2");
        assert!(artifact.structured().sum_arrays.is_empty());
        assert!(artifact.structured().sum_array_refusals.is_empty());
        let fact = artifact
            .structured()
            .sum_array_o2
            .get(&artifact.function().entry)
            .expect("exact O2 fact");
        assert_eq!(fact.lowering, SumArrayLowering::O2Vectorized);
        assert_eq!(
            fact.topology.operation_counts.as_ref(),
            [16, 14, 21, 119, 46, 154, 3, 42, 7, 17]
        );
        assert_eq!(
            fact.instruction_inventory.len(),
            artifact.graph().insts.len()
        );
        assert_eq!(fact.vector_loop.reads.len(), 2);
        assert_eq!(fact.vector_loop.lanes.len(), 8);
        assert!(fact.vector_loop.reads.iter().all(|read| {
            read.size_bytes == 16 && read.lane_projections.len() == 4 && read.lane_values.len() == 4
        }));
        for lane in &fact.vector_loop.lanes {
            assert_eq!(
                artifact.graph().def_inst(lane.initial_value),
                Some(lane.initial_projection)
            );
            assert_eq!(artifact.graph().def_inst(lane.phi_value), Some(lane.phi));
            assert_eq!(
                artifact.graph().def_inst(lane.loaded_value),
                Some(lane.load_projection)
            );
            assert_eq!(artifact.graph().def_inst(lane.next_value), Some(lane.add));
            assert_eq!(lane.wraps_at_bits, 32);
        }
        assert_eq!(fact.reduction.input_lanes.len(), 8);
        assert_eq!(fact.reduction.pairwise_adds.len(), 4);
        assert_eq!(fact.reduction.selector_packets.len(), 8);
        assert!(
            fact.reduction
                .selector_packets
                .iter()
                .all(|packet| packet.len() == 15)
        );
        assert_eq!(
            artifact.graph().def_inst(fact.reduction.returned_low32),
            Some(fact.reduction.final_add)
        );
        assert_eq!(
            artifact
                .graph()
                .def_inst(fact.reduction.physical_full_register),
            Some(fact.reduction.zero_extend)
        );
        assert_eq!(fact.scalar_tail.reads.len(), 3);
        assert!(fact.scalar_tail.reads.windows(2).all(|pair| {
            pair[0].order < pair[1].order
                && pair[0].load != pair[1].load
                && pair[0].address == pair[1].address
                && pair[0].memory_space == pair[1].memory_space
        }));
        assert_eq!(fact.returns.len(), 2);
        assert!(
            fact.returns
                .iter()
                .all(|returned| returned.composition.is_none())
        );
        assert!(fact.validate_against(&artifact));
    }

    #[test]
    fn stale_pre_alias_o2_inventory_remains_refusal_only() {
        assert!(is_stale_o2_inventory(&STALE_O2_INVENTORY));
        let artifact = o2_artifact(0x1000_0620, b"normalized-o2-not-stale");
        let normalized = artifact
            .function()
            .blocks()
            .map(|block| (block.ops.len(), block.phis.len()))
            .collect::<Vec<_>>();
        assert!(!is_stale_o2_inventory(&normalized));
        assert!(artifact.structured().sum_array_refusals.is_empty());
        assert!(
            artifact
                .structured()
                .sum_array_o2
                .contains_key(&artifact.function().entry)
        );
        assert_eq!(
            stale_o2_refusal_reason(&STALE_O2_INVENTORY),
            Some(SumArrayRefusalReason::IncompleteVectorLaneProvenance)
        );
    }

    #[test]
    fn o2_recognition_is_relocation_revision_and_temporary_name_independent() {
        let relocated = o2_artifact(0x2000_0620, b"cosmetic-source-revision");
        assert!(
            relocated
                .structured()
                .sum_array_o2
                .contains_key(&0x2000_0620)
        );

        let (arch, mut blocks) = o2_blocks(0x1000_0620);
        let replacement = Varnode::unique(0xfeed_0000, 8);
        let R2ILOp::Copy { dst, .. } = &mut blocks[0].ops[0] else {
            panic!("saved-frame-pointer temporary");
        };
        *dst = replacement.clone();
        let R2ILOp::Store { val, .. } = &mut blocks[0].ops[2] else {
            panic!("saved-frame-pointer store");
        };
        *val = replacement;
        let renamed = SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(b"renamed-temp", false, "sysv_amd64"),
        )
        .expect("renamed O2 artifact remains analyzable");
        assert!(renamed.structured().sum_array_o2.contains_key(&0x1000_0620));
    }

    #[test]
    fn o2_semantic_and_abi_mutations_fail_closed() {
        let (arch, mut wrong_read) = o2_blocks(0x1000_0620);
        let address = wrong_read[5]
            .ops
            .iter_mut()
            .find_map(|op| match op {
                R2ILOp::Load { addr, .. } if addr.size == 8 => Some(addr),
                _ => None,
            })
            .expect("first vector address");
        *address = Varnode::unique(0xbeef_0000, 8);
        let mutated = SsaArtifact::for_decompile_with_interface(
            &wrong_read,
            Some(&arch),
            interface(b"wrong-vector-read", false, "sysv_amd64"),
        )
        .expect("mutated O2 artifact remains analyzable");
        assert!(mutated.structured().sum_array_o2.is_empty());
        assert!(mutated.structured().sum_array_refusals.is_empty());

        let (arch, blocks) = o2_blocks(0x1000_0620);
        let wrong_abi = SsaArtifact::for_decompile_with_interface(
            &blocks,
            Some(&arch),
            interface(b"wrong-o2-abi", false, "win64"),
        )
        .expect("wrong-ABI O2 artifact remains analyzable");
        assert!(wrong_abi.structured().sum_array_o2.is_empty());
    }
}
