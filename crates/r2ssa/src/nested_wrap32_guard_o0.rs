//! Exact source facts for the six-block x86-64 O0 nested wrap32 guard.
//!
//! The admitted shape computes two 32-bit wrapping expressions, tests them in
//! sequence, stores one or zero in a private result carrier, and returns the
//! merged carrier through RAX.  Recognition is deliberately independent of
//! symbol names, absolute block addresses, and temporary display names.

use std::collections::{BTreeMap, BTreeSet};

use r2il::SpaceId;

use crate::cfg::BlockTerminator;
use crate::function::{SSAFunction, StackAddressBase};
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineMemoryEndianness,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceStackSlotRole,
    SourceTypeKind,
};
use crate::op::SSAOp;
use crate::semantic::{
    CallBoundarySlot, MemoryDefFact, MemorySSAFacts, MemoryUseFact, ObjectId, ObjectKind,
    ObjectModel, PredicateFacts, RelativeMemoryAddress, SourceBoundaryFacts, StructuredAccessId,
    StructuredMemoryAccessFact,
};
use crate::var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar};

pub const NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION: u32 = 1;

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

const HEADER_OPS: usize = 66;
const SECOND_OPS: usize = 14;
const SUCCESS_OPS: usize = 4;
const FORWARDER_OPS: usize = 1;
const FAILURE_OPS: usize = 3;
const EXIT_OPS: usize = 11;
const FAILURE_PHIS: usize = 13;
const EXIT_PHIS: usize = 14;
const ORDINARY_INSTRUCTIONS: usize =
    HEADER_OPS + SECOND_OPS + SUCCESS_OPS + FORWARDER_OPS + FAILURE_OPS + EXIT_OPS;
const PHI_INSTRUCTIONS: usize = FAILURE_PHIS + EXIT_PHIS;
const TOTAL_INSTRUCTIONS: usize = ORDINARY_INSTRUCTIONS + PHI_INSTRUCTIONS;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NestedWrap32GuardO0InstructionClass {
    FrameEnvelope,
    ParameterHomeState,
    Wrap32Arithmetic,
    LocalSpillState,
    ComparisonPacket,
    NestedControl,
    PrivateResultCarrier,
    ReturnComposition,
    MachineRelayPhi,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0InstructionDisposition {
    pub inst: InstId,
    pub class: NestedWrap32GuardO0InstructionClass,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0TopologyFact {
    pub header: u64,
    pub second: u64,
    pub success: u64,
    pub forwarder: u64,
    pub failure: u64,
    pub exit: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0ParameterFact {
    pub index: u32,
    pub abi_storage: CanonicalStorageId,
    pub low32_storage: CanonicalStorageId,
    pub low32_value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedWrap32GuardO0AbiFact {
    pub revision_identity: Box<[u8]>,
    pub parameters: Box<[NestedWrap32GuardO0ParameterFact]>,
    pub parameter_logical_values: Box<[SourceLogicalValue]>,
    pub return_logical_value: SourceLogicalValue,
    pub return_storage: CanonicalStorageId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0FrameFact {
    pub memory_space: SpaceId,
    pub entry_stack: ValueId,
    pub allocated_stack: ValueId,
    pub saved_frame_pointer: ValueId,
    pub established_frame_pointer: ValueId,
    pub restored_frame_pointer: ValueId,
    pub restored_stack: ValueId,
    pub return_target: ValueId,
    pub final_stack: ValueId,
    pub return_inst: InstId,
    pub saved_frame_pointer_range: NestedWrap32GuardO0PhysicalRange,
    pub return_address_range: NestedWrap32GuardO0PhysicalRange,
    pub instructions: [InstId; 11],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0PhysicalRange {
    pub offset_from_entry_stack: i64,
    pub size_bytes: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0AccessFact {
    pub access: StructuredAccessId,
    pub object: ObjectId,
    pub value: Option<ValueId>,
    pub memory_uses: usize,
    pub memory_defs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedWrap32GuardO0SlotFact {
    pub base: StackAddressBase,
    pub frame_pointer_offset: i64,
    pub entry_stack_offset: i64,
    pub size_bytes: u32,
    pub object: ObjectId,
    pub accesses: Box<[NestedWrap32GuardO0AccessFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedWrap32GuardO0SlotsFact {
    pub parameter_homes: Box<[NestedWrap32GuardO0SlotFact]>,
    pub sum: NestedWrap32GuardO0SlotFact,
    pub difference: NestedWrap32GuardO0SlotFact,
    pub result: NestedWrap32GuardO0SlotFact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0FlagPacketFact {
    pub value: ValueId,
    pub sign: ValueId,
    pub zero: ValueId,
    pub low_byte: ValueId,
    pub population: ValueId,
    pub parity_bit: ValueId,
    pub parity: ValueId,
    pub instructions: [InstId; 6],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0ArithmeticFact {
    pub left: ValueId,
    pub right: ValueId,
    pub result: ValueId,
    pub carry_or_borrow: ValueId,
    pub signed_overflow: ValueId,
    pub flag_packet: NestedWrap32GuardO0FlagPacketFact,
    pub wraps_at_bits: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0ComparisonFact {
    pub block: u64,
    pub address: ValueId,
    pub loaded: ValueId,
    pub copied_operand: ValueId,
    pub expected: u32,
    pub carry_or_borrow: ValueId,
    pub signed_overflow: ValueId,
    pub difference: ValueId,
    pub flag_packet: NestedWrap32GuardO0FlagPacketFact,
    pub inverted_zero: ValueId,
    pub branch_inst: InstId,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedWrap32GuardO0PhiLayerFact {
    pub block: u64,
    pub predecessors: [u64; 2],
    pub phis: Box<[InstId]>,
    pub outputs: Box<[ValueId]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedWrap32GuardO0ReturnFact {
    pub result_load: StructuredAccessId,
    pub loaded_result: ValueId,
    pub low32_copy: InstId,
    pub zero_extend: InstId,
    pub returned_value: ValueId,
    pub return_inst: InstId,
    pub return_target: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedWrap32GuardO0Fact {
    pub schema_version: u32,
    pub topology: NestedWrap32GuardO0TopologyFact,
    pub abi: NestedWrap32GuardO0AbiFact,
    pub frame: NestedWrap32GuardO0FrameFact,
    pub slots: NestedWrap32GuardO0SlotsFact,
    pub sum: NestedWrap32GuardO0ArithmeticFact,
    pub difference: NestedWrap32GuardO0ArithmeticFact,
    pub sum_comparison: NestedWrap32GuardO0ComparisonFact,
    pub difference_comparison: NestedWrap32GuardO0ComparisonFact,
    pub failure_phis: NestedWrap32GuardO0PhiLayerFact,
    pub exit_phis: NestedWrap32GuardO0PhiLayerFact,
    pub success_address: ValueId,
    pub success_value: ValueId,
    pub failure_address: ValueId,
    pub failure_value: ValueId,
    pub returned: NestedWrap32GuardO0ReturnFact,
    pub instruction_inventory: Box<[InstId]>,
    pub dispositions: Box<[NestedWrap32GuardO0InstructionDisposition]>,
}

impl NestedWrap32GuardO0Fact {
    pub fn validate_against_parts(
        &self,
        function: &SSAFunction,
        graph: &SsaGraph,
        objects: &ObjectModel,
        memory: &MemorySSAFacts,
        predicates: &PredicateFacts,
        boundaries: &SourceBoundaryFacts,
        memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
        machine: &SourceMachineContext,
    ) -> bool {
        self.schema_version == NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION
            && collect_one(
                function,
                graph,
                objects,
                memory,
                predicates,
                boundaries,
                memory_accesses,
                machine,
            )
            .as_ref()
                == Some(self)
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_nested_wrap32_guard_o0_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    boundaries: &SourceBoundaryFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
) -> BTreeMap<u64, NestedWrap32GuardO0Fact> {
    let mut facts = BTreeMap::new();
    let Some(fact) = collect_one(
        function,
        graph,
        objects,
        memory,
        predicates,
        boundaries,
        memory_accesses,
        machine,
    ) else {
        return facts;
    };
    facts.insert(fact.topology.header, fact);
    facts
}

#[allow(clippy::too_many_arguments)]
fn collect_one(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    boundaries: &SourceBoundaryFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
) -> Option<NestedWrap32GuardO0Fact> {
    let topology = collect_topology(function)?;
    let header = function.get_block(topology.header)?;
    let second = function.get_block(topology.second)?;
    let success = function.get_block(topology.success)?;
    let forwarder = function.get_block(topology.forwarder)?;
    let failure = function.get_block(topology.failure)?;
    let exit = function.get_block(topology.exit)?;
    if header.ops.len() != HEADER_OPS
        || second.ops.len() != SECOND_OPS
        || success.ops.len() != SUCCESS_OPS
        || forwarder.ops.len() != FORWARDER_OPS
        || failure.ops.len() != FAILURE_OPS
        || exit.ops.len() != EXIT_OPS
        || !header.phis.is_empty()
        || !second.phis.is_empty()
        || !success.phis.is_empty()
        || !forwarder.phis.is_empty()
        || failure.phis.len() != FAILURE_PHIS
        || exit.phis.len() != EXIT_PHIS
        || !boundaries.calls.is_empty()
        || predicates.predicates.len() != 2
        || !predicates.switches.is_empty()
        || predicates.block_assumptions.len() != 4
        || predicates
            .block_assumptions
            .values()
            .any(|assumptions| assumptions.len() != 1)
    {
        return None;
    }

    let abi = collect_abi(graph, boundaries, machine)?;
    let frame = collect_frame(function, graph, machine, topology)?;
    let op = |block: u64, index: usize| function.get_block(block)?.ops.get(index);

    let parameter_home_0 = collect_parameter_home(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        topology.header,
        4,
        -8,
        abi.parameters[0],
        &[(10, 11), (31, 32)],
    )?;
    let parameter_home_1 = collect_parameter_home(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        topology.header,
        7,
        -12,
        abi.parameters[1],
        &[(14, 15), (14, 17), (14, 19), (35, 36), (35, 38), (35, 40)],
    )?;

    let sum_left = load_value(op(topology.header, 11)?, graph)?;
    let sum_right = load_value(op(topology.header, 19)?, graph)?;
    let sum = collect_arithmetic(
        function,
        graph,
        machine,
        topology.header,
        10,
        14,
        [15, 17, 19],
        16,
        18,
        20,
        22,
        false,
    )?;
    if sum.left != sum_left || sum.right != sum_right {
        return None;
    }
    let difference = collect_arithmetic(
        function,
        graph,
        machine,
        topology.header,
        31,
        35,
        [36, 38, 40],
        37,
        39,
        41,
        43,
        true,
    )?;

    let sum_slot = collect_local_slot(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        -16,
        &[
            (topology.header, 28, 30, true),
            (topology.header, 52, 53, false),
        ],
    )?;
    let difference_slot = collect_local_slot(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        -20,
        &[
            (topology.header, 49, 51, true),
            (topology.second, 0, 1, false),
        ],
    )?;
    if !single_store_reaches_all_loads(memory, &parameter_home_0)
        || !single_store_reaches_all_loads(memory, &parameter_home_1)
        || !single_store_reaches_all_loads(memory, &sum_slot)
        || !single_store_reaches_all_loads(memory, &difference_slot)
    {
        return None;
    }
    let sum_store_value = access_value(&sum_slot, true)?;
    let difference_store_value = access_value(&difference_slot, true)?;
    if !value_is_copy_of(graph, sum_store_value, sum.result)
        || !value_is_copy_of(graph, difference_store_value, difference.result)
    {
        return None;
    }

    let sum_comparison = collect_comparison(
        function,
        graph,
        machine,
        topology.header,
        52,
        0x64,
        topology.failure,
        topology.second,
    )?;
    let difference_comparison = collect_comparison(
        function,
        graph,
        machine,
        topology.second,
        0,
        0x14,
        topology.forwarder,
        topology.success,
    )?;
    if sum_comparison.loaded != access_value(&sum_slot, false)?
        || difference_comparison.loaded != access_value(&difference_slot, false)?
        || !predicate_is_exact(predicates, sum_comparison)
        || !predicate_is_exact(predicates, difference_comparison)
    {
        return None;
    }

    let (success_address, success_value) =
        collect_result_store(function, graph, machine, topology.success, 1, topology.exit)?;
    match op(topology.forwarder, 0)? {
        SSAOp::Branch { .. } => {}
        _ => return None,
    }
    let (failure_address, failure_value) =
        collect_result_store(function, graph, machine, topology.failure, 0, topology.exit)?;
    let result_slot = collect_local_slot(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        -4,
        &[
            (topology.success, 0, 2, true),
            (topology.failure, 0, 2, true),
            (topology.exit, 0, 1, false),
        ],
    )?;
    let result_values = result_slot
        .accesses
        .iter()
        .filter_map(|access| access.value)
        .collect::<BTreeSet<_>>();
    if result_values
        != BTreeSet::from([
            success_value,
            failure_value,
            load_access_value(&result_slot)?,
        ])
        || !exact_result_memory_phi(
            memory,
            &result_slot,
            topology.success,
            topology.failure,
            topology.exit,
        )
    {
        return None;
    }

    let failure_phis = collect_phi_layer(
        function,
        graph,
        topology.failure,
        [topology.header, topology.forwarder],
        &comparison_relay_pairs(sum_comparison, difference_comparison),
    )?;
    let fail_outputs = failure_phis.outputs.as_ref();
    let mut second_values = comparison_relay_values(difference_comparison);
    if fail_outputs.len() != second_values.len() || second_values.len() != FAILURE_PHIS {
        return None;
    }
    let mut exit_pairs = second_values
        .drain(..FAILURE_PHIS - 1)
        .zip(fail_outputs[..FAILURE_PHIS - 1].iter().copied())
        .collect::<Vec<_>>();
    exit_pairs.push((success_address, failure_address));
    exit_pairs.push((success_value, failure_value));
    let exit_phis = collect_phi_layer(
        function,
        graph,
        topology.exit,
        [topology.success, topology.failure],
        &exit_pairs,
    )?;

    let returned = collect_return(function, graph, boundaries, machine, topology, &result_slot)?;
    if returned.return_inst != frame.return_inst || returned.return_target != frame.return_target {
        return None;
    }

    let slots = NestedWrap32GuardO0SlotsFact {
        parameter_homes: vec![parameter_home_0, parameter_home_1].into_boxed_slice(),
        sum: sum_slot,
        difference: difference_slot,
        result: result_slot,
    };
    let slot_objects = slots
        .parameter_homes
        .iter()
        .chain([&slots.sum, &slots.difference, &slots.result])
        .map(|slot| slot.object)
        .collect::<BTreeSet<_>>();
    if slot_objects.len() != 5
        || !physical_ranges_are_exact_and_disjoint(&frame, &slots)
        || !all_slot_addresses_are_confined(graph, objects, &slots)
        || !all_memory_accesses_are_expected(function, graph, memory_accesses, &frame, &slots)
    {
        return None;
    }

    let (instruction_inventory, dispositions) =
        collect_inventory_and_dispositions(function, graph, topology, &failure_phis, &exit_phis)?;
    if instruction_inventory.len() != TOTAL_INSTRUCTIONS
        || graph.insts.len() != TOTAL_INSTRUCTIONS
        || dispositions.len() != TOTAL_INSTRUCTIONS
    {
        return None;
    }

    Some(NestedWrap32GuardO0Fact {
        schema_version: NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION,
        topology,
        abi,
        frame,
        slots,
        sum,
        difference,
        sum_comparison,
        difference_comparison,
        failure_phis,
        exit_phis,
        success_address,
        success_value,
        failure_address,
        failure_value,
        returned,
        instruction_inventory,
        dispositions,
    })
}

fn collect_topology(function: &SSAFunction) -> Option<NestedWrap32GuardO0TopologyFact> {
    if function.block_addrs().len() != 6 {
        return None;
    }
    let header = function.entry;
    let (failure, second) = conditional_successors(function, header)?;
    let (forwarder, success) = conditional_successors(function, second)?;
    let forwarder_successors = function.successors(forwarder);
    let [forwarded_failure] = forwarder_successors.as_slice() else {
        return None;
    };
    if *forwarded_failure != failure {
        return None;
    }
    let failure_successors = function.successors(failure);
    let [failure_exit] = failure_successors.as_slice() else {
        return None;
    };
    let success_successors = function.successors(success);
    let [success_exit] = success_successors.as_slice() else {
        return None;
    };
    if failure_exit != success_exit {
        return None;
    }
    let exit = *failure_exit;
    let expected = BTreeSet::from([header, second, success, forwarder, failure, exit]);
    if function
        .block_addrs()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        != expected
        || function.predecessors(header) != Vec::<u64>::new()
        || function.predecessors(second) != [header]
        || function.predecessors(success) != [second]
        || function.predecessors(forwarder) != [second]
        || sorted(function.predecessors(failure)) != sorted(vec![header, forwarder])
        || sorted(function.predecessors(exit)) != sorted(vec![success, failure])
        || !function.successors(exit).is_empty()
        || !matches!(function.cfg().get_block(success)?.terminator, BlockTerminator::Branch { target } if target == exit)
        || !matches!(function.cfg().get_block(forwarder)?.terminator, BlockTerminator::Branch { target } if target == failure)
        || !matches!(function.cfg().get_block(failure)?.terminator, BlockTerminator::Fallthrough { next } if next == exit)
        || !matches!(
            function.cfg().get_block(exit)?.terminator,
            BlockTerminator::Return
        )
    {
        return None;
    }
    Some(NestedWrap32GuardO0TopologyFact {
        header,
        second,
        success,
        forwarder,
        failure,
        exit,
    })
}

fn conditional_successors(function: &SSAFunction, block: u64) -> Option<(u64, u64)> {
    match function.cfg().get_block(block)?.terminator {
        BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } if function.successors(block) == [true_target, false_target] => {
            Some((true_target, false_target))
        }
        _ => None,
    }
}

fn sorted(mut values: Vec<u64>) -> Vec<u64> {
    values.sort_unstable();
    values
}

fn collect_abi(
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
) -> Option<NestedWrap32GuardO0AbiFact> {
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
    let [integer] = types.types() else {
        return None;
    };
    let [first, second] = interface.parameters() else {
        return None;
    };
    let [first_logical, second_logical] = interface.parameter_logical_values() else {
        return None;
    };
    let return_logical = interface.return_logical_value()?;
    let return_storage = match interface.return_kind() {
        SourceFunctionReturn::Register { storage } => storage,
        SourceFunctionReturn::Void => return None,
    };
    let exact_logical = |logical: SourceLogicalValue| {
        logical.type_id() == 0
            && logical.carrier().kind() == SourceCarrierKind::LowBits
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == 32
    };
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity().is_empty()
        || interface.calling_convention() != "sysv_amd64"
        || !interface.stack_slot_roles_complete()
        || types.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || !types.aggregates().is_empty()
        || integer.kind() != SourceTypeKind::SignedInteger
        || integer.size_bits() != 32
        || integer.align_bits() != 32
        || !exact_logical(*first_logical)
        || !exact_logical(*second_logical)
        || !exact_logical(return_logical)
        || first.index() != 0
        || second.index() != 1
        || !register_at(first.storage(), RDI_OFFSET, 8)
        || !register_at(second.storage(), RSI_OFFSET, 8)
        || !register_at(return_storage, RAX_OFFSET, 8)
        || machine.abi_model().argument_registers().len() != 2
        || machine.abi_model().return_registers().len() != 1
    {
        return None;
    }
    let frame_storage = register_storage(machine, RBP_OFFSET, 8)?;
    let slots = interface.stack_slots();
    let slot_matches = |offset, role| {
        slots
            .iter()
            .filter(|slot| {
                slot.base() == StackAddressBase::FramePointer
                    && slot.base_storage() == frame_storage
                    && slot.offset() == offset
                    && slot.size_bytes() == 4
                    && slot.role() == role
            })
            .count()
            == 1
    };
    if slots.len() != 4
        || !slot_matches(
            -8,
            SourceStackSlotRole::ParameterHome {
                parameter_index: 0,
                home_storage: first.storage(),
            },
        )
        || !slot_matches(
            -12,
            SourceStackSlotRole::ParameterHome {
                parameter_index: 1,
                home_storage: second.storage(),
            },
        )
        || !slot_matches(-16, SourceStackSlotRole::Local)
        || !slot_matches(-20, SourceStackSlotRole::Local)
    {
        return None;
    }
    let low32 = [
        entry_low32(graph, machine, RDI_OFFSET)?,
        entry_low32(graph, machine, RSI_OFFSET)?,
    ];
    let parameters = [first, second]
        .into_iter()
        .zip(low32)
        .map(
            |(source, (low32_storage, low32_value))| NestedWrap32GuardO0ParameterFact {
                index: source.index(),
                abi_storage: source.storage(),
                low32_storage,
                low32_value,
            },
        )
        .collect::<Vec<_>>();
    if !boundaries.parameters.is_empty() {
        return None;
    }
    Some(NestedWrap32GuardO0AbiFact {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        parameters: parameters.into_boxed_slice(),
        parameter_logical_values: vec![*first_logical, *second_logical].into_boxed_slice(),
        return_logical_value: return_logical,
        return_storage,
    })
}

fn entry_low32(
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    offset: u64,
) -> Option<(CanonicalStorageId, ValueId)> {
    let mut values = graph.values.iter().filter_map(|value| {
        if graph.def_inst(value.id).is_some() || value.var.version != 0 {
            return None;
        }
        let storage = value.canonical_storage?;
        register_at(storage, offset, 4).then_some((storage, value.id))
    });
    let value = values.next()?;
    values.next().is_none().then_some(value)
}

fn collect_frame(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    topology: NestedWrap32GuardO0TopologyFact,
) -> Option<NestedWrap32GuardO0FrameFact> {
    let header = function.get_block(topology.header)?;
    let exit = function.get_block(topology.exit)?;
    let inst = |block, index| graph.inst_id_for_op_site(block, index);
    let (saved_var, entry_fp) = match header.ops.first()? {
        SSAOp::Copy { dst, src }
            if src.version == 0 && register_var(graph, src, RBP_OFFSET, 8) && dst.size == 8 =>
        {
            (dst, value(graph, src)?)
        }
        _ => return None,
    };
    let (allocated_var, entry_stack) = match header.ops.get(1)? {
        SSAOp::IntSub { dst, a, b }
            if a.version == 0
                && register_var(graph, a, RSP_OFFSET, 8)
                && register_var(graph, dst, RSP_OFFSET, 8)
                && constant(b, 8, 8) =>
        {
            (dst, value(graph, a)?)
        }
        _ => return None,
    };
    match header.ops.get(2)? {
        SSAOp::Store { addr, val, .. } if addr == allocated_var && val == saved_var => {}
        _ => return None,
    }
    let established_var = match header.ops.get(3)? {
        SSAOp::Copy { dst, src }
            if src == allocated_var && register_var(graph, dst, RBP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let dead_seed = match exit.ops.get(4)? {
        SSAOp::Copy { dst, src } if dst.size == 8 && constant(src, 0, 8) => value(graph, dst)?,
        _ => return None,
    };
    if !graph.uses_of.get(dead_seed.0 as usize)?.is_empty() {
        return None;
    }
    let restored_var = match exit.ops.get(5)? {
        SSAOp::Load { dst, addr, .. } if addr == allocated_var && dst.size == 8 => dst,
        _ => return None,
    };
    let restored_stack_var = match exit.ops.get(6)? {
        SSAOp::IntAdd { dst, a, b }
            if a == allocated_var
                && constant(b, 8, 8)
                && register_var(graph, dst, RSP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    match exit.ops.get(7)? {
        SSAOp::Copy { dst, src }
            if src == restored_var && register_var(graph, dst, RBP_OFFSET, 8) => {}
        _ => return None,
    }
    let target_var = match exit.ops.get(8)? {
        SSAOp::Load { dst, addr, .. }
            if addr == restored_stack_var && register_var(graph, dst, RIP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let final_stack_var = match exit.ops.get(9)? {
        SSAOp::IntAdd { dst, a, b }
            if a == restored_stack_var
                && constant(b, 8, 8)
                && register_var(graph, dst, RSP_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    match exit.ops.get(10)? {
        SSAOp::Return { target } if target == target_var => {}
        _ => return None,
    }
    let memory_space = machine.memory_space_at(topology.header, 2)?;
    if machine.memory_space_at(topology.exit, 5) != Some(memory_space)
        || machine.memory_space_at(topology.exit, 8) != Some(memory_space)
    {
        return None;
    }
    let memory_model = machine.memory_model().space(memory_space)?;
    if memory_model.address_bits() != 64
        || memory_model.word_size_bytes() != 1
        || memory_model.endianness() != MachineMemoryEndianness::Little
        || entry_fp == entry_stack
    {
        return None;
    }
    Some(NestedWrap32GuardO0FrameFact {
        memory_space,
        entry_stack,
        allocated_stack: value(graph, allocated_var)?,
        saved_frame_pointer: value(graph, saved_var)?,
        established_frame_pointer: value(graph, established_var)?,
        restored_frame_pointer: value(graph, restored_var)?,
        restored_stack: value(graph, restored_stack_var)?,
        return_target: value(graph, target_var)?,
        final_stack: value(graph, final_stack_var)?,
        return_inst: inst(topology.exit, 10)?,
        saved_frame_pointer_range: NestedWrap32GuardO0PhysicalRange {
            offset_from_entry_stack: -8,
            size_bytes: 8,
        },
        return_address_range: NestedWrap32GuardO0PhysicalRange {
            offset_from_entry_stack: 0,
            size_bytes: 8,
        },
        instructions: [
            inst(topology.header, 0)?,
            inst(topology.header, 1)?,
            inst(topology.header, 2)?,
            inst(topology.header, 3)?,
            inst(topology.exit, 4)?,
            inst(topology.exit, 5)?,
            inst(topology.exit, 6)?,
            inst(topology.exit, 7)?,
            inst(topology.exit, 8)?,
            inst(topology.exit, 9)?,
            inst(topology.exit, 10)?,
        ],
    })
}

fn collect_parameter_home(
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
    block: u64,
    address_index: usize,
    offset: i64,
    parameter: NestedWrap32GuardO0ParameterFact,
    reload_sites: &[(usize, usize)],
) -> Option<NestedWrap32GuardO0SlotFact> {
    let function_block = graph.block(graph.block_id_for_addr(block)?)?;
    let _ = function_block;
    let init_address = graph.inst_id_for_op_site(block, address_index)?;
    let init_copy = graph.inst_id_for_op_site(block, address_index + 1)?;
    let init_store = graph.inst_id_for_op_site(block, address_index + 2)?;
    let address_op = graph.inst(init_address)?;
    let copy_op = graph.inst(init_copy)?;
    let store_op = graph.inst(init_store)?;
    let InstPayload::Op(SSAOp::IntAdd { dst, a, b }) = &address_op.payload else {
        return None;
    };
    if !register_var(graph, a, RBP_OFFSET, 8) || !signed_constant(b, offset, 8) {
        return None;
    }
    let InstPayload::Op(SSAOp::Copy { dst: copied, src }) = &copy_op.payload else {
        return None;
    };
    if value(graph, src)? != parameter.low32_value || copied.size != 4 {
        return None;
    }
    let InstPayload::Op(SSAOp::Store { addr, val, .. }) = &store_op.payload else {
        return None;
    };
    if addr != dst || val != copied {
        return None;
    }
    let mut sites = vec![(block, address_index, address_index + 2, true)];
    sites.extend(
        reload_sites
            .iter()
            .map(|(reload_address, reload)| (block, *reload_address, *reload, false)),
    );
    collect_slot(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        offset,
        &sites,
    )
}

fn collect_local_slot(
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
    offset: i64,
    sites: &[(u64, usize, usize, bool)],
) -> Option<NestedWrap32GuardO0SlotFact> {
    collect_slot(
        graph,
        objects,
        memory,
        memory_accesses,
        machine,
        offset,
        sites,
    )
}

fn collect_slot(
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    _machine: &SourceMachineContext,
    offset: i64,
    sites: &[(u64, usize, usize, bool)],
) -> Option<NestedWrap32GuardO0SlotFact> {
    let mut collected = Vec::new();
    let mut object = None;
    for (block, address_index, memory_index, write) in sites {
        let address_inst = graph.inst_id_for_op_site(*block, *address_index)?;
        let InstPayload::Op(SSAOp::IntAdd { dst: address, a, b }) =
            &graph.inst(address_inst)?.payload
        else {
            return None;
        };
        if !register_var(graph, a, RBP_OFFSET, 8) || !signed_constant(b, offset, 8) {
            return None;
        }
        let access = exact_access_at(memory_accesses, graph, *block, *memory_index, *write)?;
        if access.address != value(graph, address)?
            || access.width != 4
            || !access.provenance_complete
        {
            return None;
        }
        let fact = objects.object(access.object)?;
        if !matches!(fact.kind, ObjectKind::StackSlot { base: StackAddressBase::FramePointer, offset: actual } | ObjectKind::FrameObject { base: StackAddressBase::FramePointer, offset: actual } if actual == offset)
        {
            return None;
        }
        if object
            .replace(access.object)
            .is_some_and(|previous| previous != access.object)
        {
            return None;
        }
        let (uses, defs) = exact_memory_annotations(memory, access)?;
        collected.push(NestedWrap32GuardO0AccessFact {
            access: access.id,
            object: access.object,
            value: access.value,
            memory_uses: uses,
            memory_defs: defs,
        });
    }
    Some(NestedWrap32GuardO0SlotFact {
        base: StackAddressBase::FramePointer,
        frame_pointer_offset: offset,
        entry_stack_offset: offset.checked_sub(8)?,
        size_bytes: 4,
        object: object?,
        accesses: collected.into_boxed_slice(),
    })
}

fn exact_access_at<'a>(
    memory_accesses: &'a BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    graph: &SsaGraph,
    block: u64,
    op_index: usize,
    write: bool,
) -> Option<&'a StructuredMemoryAccessFact> {
    let inst = graph.inst_id_for_op_site(block, op_index)?;
    let mut candidates = memory_accesses
        .values()
        .filter(|access| access.id.inst == inst && access.is_write == write);
    let access = candidates.next()?;
    (candidates.next().is_none()
        && access.id.ordinal == 0
        && access.block_addr == block
        && access.op_index == op_index)
        .then_some(access)
}

fn exact_memory_annotations(
    memory: &MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<(usize, usize)> {
    let uses = memory
        .uses_by_inst
        .get(&access.id.inst)
        .map_or(&[][..], Vec::as_slice);
    let defs = memory
        .defs_by_inst
        .get(&access.id.inst)
        .map_or(&[][..], Vec::as_slice);
    let exact_use = |use_fact: &MemoryUseFact| {
        use_fact.location.object == access.object
            && use_fact.location.address == RelativeMemoryAddress::Exact(0)
            && use_fact.location.size == access.width
    };
    let exact_def = |def: &MemoryDefFact| {
        def.location.object == access.object
            && def.location.address == RelativeMemoryAddress::Exact(0)
            && def.location.size == access.width
    };
    if uses.iter().any(|fact| !exact_use(fact)) || defs.iter().any(|fact| !exact_def(fact)) {
        return None;
    }
    match access.is_write {
        true if uses.is_empty() && defs.len() == 1 => Some((0, 1)),
        false if uses.len() == 1 && defs.is_empty() => Some((1, 0)),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_arithmetic(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    block: u64,
    left_address: usize,
    right_address: usize,
    right_loads: [usize; 3],
    carry_index: usize,
    overflow_index: usize,
    result_index: usize,
    flag_start: usize,
    subtract: bool,
) -> Option<NestedWrap32GuardO0ArithmeticFact> {
    let ops = &function.get_block(block)?.ops;
    let left = match ops.get(left_address + 1)? {
        SSAOp::Load { dst, .. } if dst.size == 4 => dst,
        _ => return None,
    };
    match ops.get(left_address + 2)? {
        SSAOp::Copy { dst, src } if src == left && register_var(graph, dst, RAX_OFFSET, 4) => {}
        _ => return None,
    }
    match ops.get(left_address + 3)? {
        SSAOp::IntZExt { dst, src } if src == left && register_var(graph, dst, RAX_OFFSET, 8) => {
        }
        _ => return None,
    }
    let right_values = right_loads
        .into_iter()
        .map(|index| match ops.get(index)? {
            SSAOp::Load { dst, .. } if dst.size == 4 => Some(dst),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    if right_values.len() != 3 || !matches!(ops.get(right_address), Some(SSAOp::IntAdd { .. })) {
        return None;
    }
    let (carry_var, carry_left_var, carry_right_var) = binary_var_output(ops.get(carry_index)?)?;
    let (overflow_var, overflow_left_var, overflow_right_var) =
        binary_var_output(ops.get(overflow_index)?)?;
    let carry = value(graph, carry_var)?;
    let carry_left = value(graph, carry_left_var)?;
    let carry_right = value(graph, carry_right_var)?;
    let overflow = value(graph, overflow_var)?;
    let overflow_left = value(graph, overflow_left_var)?;
    let overflow_right = value(graph, overflow_right_var)?;
    if carry_left != value(graph, left)?
        || overflow_left != value(graph, left)?
        || carry_right != value(graph, right_values[0])?
        || overflow_right != value(graph, right_values[1])?
        || !register_var(graph, carry_var, CF_OFFSET, 1)
        || !register_var(graph, overflow_var, OF_OFFSET, 1)
        || if subtract {
            !matches!(ops.get(carry_index)?, SSAOp::IntLess { .. })
                || !matches!(ops.get(overflow_index)?, SSAOp::IntSBorrow { .. })
        } else {
            !matches!(ops.get(carry_index)?, SSAOp::IntCarry { .. })
                || !matches!(ops.get(overflow_index)?, SSAOp::IntSCarry { .. })
        }
    {
        return None;
    }
    let (result_var, result_left, result_right) = binary_var_output(ops.get(result_index)?)?;
    if result_left != left
        || result_right != right_values[2]
        || result_var.size != 4
        || if subtract {
            !matches!(ops.get(result_index)?, SSAOp::IntSub { .. })
        } else {
            !matches!(ops.get(result_index)?, SSAOp::IntAdd { .. })
        }
    {
        return None;
    }
    match ops.get(result_index + 1)? {
        SSAOp::IntZExt { dst, src }
            if src == result_var && register_var(graph, dst, RAX_OFFSET, 8) => {}
        _ => return None,
    }
    let flag_packet = collect_flag_packet(function, graph, machine, block, flag_start, result_var)?;
    Some(NestedWrap32GuardO0ArithmeticFact {
        left: value(graph, left)?,
        right: value(graph, right_values[2])?,
        result: value(graph, result_var)?,
        carry_or_borrow: carry,
        signed_overflow: overflow,
        flag_packet,
        wraps_at_bits: 32,
    })
}

fn collect_flag_packet(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    block: u64,
    start: usize,
    input: &SSAVar,
) -> Option<NestedWrap32GuardO0FlagPacketFact> {
    let ops = &function.get_block(block)?.ops;
    let sign = match ops.get(start)? {
        SSAOp::IntSLess { dst, a, b }
            if a == input
                && constant(b, 0, input.size)
                && register_var(graph, dst, SF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let zero = match ops.get(start + 1)? {
        SSAOp::IntEqual { dst, a, b }
            if a == input
                && constant(b, 0, input.size)
                && register_var(graph, dst, ZF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let low = match ops.get(start + 2)? {
        SSAOp::IntAnd { dst, a, b } if a == input && constant(b, 0xff, input.size) => dst,
        _ => return None,
    };
    let population = match ops.get(start + 3)? {
        SSAOp::PopCount { dst, src } if src == low => dst,
        _ => return None,
    };
    let parity_bit = match ops.get(start + 4)? {
        SSAOp::IntAnd { dst, a, b } if a == population && constant(b, 1, population.size) => dst,
        _ => return None,
    };
    let parity = match ops.get(start + 5)? {
        SSAOp::IntEqual { dst, a, b }
            if a == parity_bit
                && constant(b, 0, parity_bit.size)
                && register_var(graph, dst, PF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let inst = |index| graph.inst_id_for_op_site(block, index);
    Some(NestedWrap32GuardO0FlagPacketFact {
        value: value(graph, input)?,
        sign: value(graph, sign)?,
        zero: value(graph, zero)?,
        low_byte: value(graph, low)?,
        population: value(graph, population)?,
        parity_bit: value(graph, parity_bit)?,
        parity: value(graph, parity)?,
        instructions: [
            inst(start)?,
            inst(start + 1)?,
            inst(start + 2)?,
            inst(start + 3)?,
            inst(start + 4)?,
            inst(start + 5)?,
        ],
    })
}

fn collect_comparison(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    block: u64,
    start: usize,
    expected: u32,
    true_target: u64,
    false_target: u64,
) -> Option<NestedWrap32GuardO0ComparisonFact> {
    let ops = &function.get_block(block)?.ops;
    let address = match ops.get(start)? {
        SSAOp::IntAdd { dst, a, b }
            if register_var(graph, a, RBP_OFFSET, 8)
                && b.size == 8
                && matches!(b.constant_bits(), Some(value) if value as i64 == if start == 52 { -16 } else { -20 }) =>
        {
            dst
        }
        _ => return None,
    };
    let loaded = match ops.get(start + 1)? {
        SSAOp::Load { dst, addr, .. } if addr == address && dst.size == 4 => dst,
        _ => return None,
    };
    let copied = match ops.get(start + 2)? {
        SSAOp::Copy { dst, src } if src == loaded => dst,
        _ => return None,
    };
    let expected_var = SSAVar::constant(u64::from(expected), 4);
    let carry = match ops.get(start + 3)? {
        SSAOp::IntLess { dst, a, b }
            if a == copied && b == &expected_var && register_var(graph, dst, CF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let overflow = match ops.get(start + 4)? {
        SSAOp::IntSBorrow { dst, a, b }
            if a == copied && b == &expected_var && register_var(graph, dst, OF_OFFSET, 1) =>
        {
            dst
        }
        _ => return None,
    };
    let difference = match ops.get(start + 5)? {
        SSAOp::IntSub { dst, a, b } if a == copied && b == &expected_var => dst,
        _ => return None,
    };
    let flag_packet = collect_flag_packet(function, graph, machine, block, start + 6, difference)?;
    let inverted = match ops.get(start + 12)? {
        SSAOp::BoolNot { dst, src } if value(graph, src)? == flag_packet.zero => dst,
        _ => return None,
    };
    match ops.get(start + 13)? {
        SSAOp::CBranch { cond, .. } if cond == inverted => {}
        _ => return None,
    }
    let branch_inst = graph.inst_id_for_op_site(block, start + 13)?;
    Some(NestedWrap32GuardO0ComparisonFact {
        block,
        address: value(graph, address)?,
        loaded: value(graph, loaded)?,
        copied_operand: value(graph, copied)?,
        expected,
        carry_or_borrow: value(graph, carry)?,
        signed_overflow: value(graph, overflow)?,
        difference: value(graph, difference)?,
        flag_packet,
        inverted_zero: value(graph, inverted)?,
        branch_inst,
        true_target,
        false_target,
    })
}

fn predicate_is_exact(
    predicates: &PredicateFacts,
    expected: NestedWrap32GuardO0ComparisonFact,
) -> bool {
    let mut candidates = predicates.predicates.values().filter(|predicate| {
        predicate.block_addr == expected.block
            && predicate.condition == expected.inverted_zero
            && predicate.true_target == expected.true_target
            && predicate.false_target == expected.false_target
    });
    let Some(predicate) = candidates.next() else {
        return false;
    };
    if candidates.next().is_some() {
        return false;
    }
    [(expected.true_target, true), (expected.false_target, false)]
        .into_iter()
        .all(|(target, truth)| {
            let Some(assumptions) = predicates.block_assumptions.get(&target) else {
                return false;
            };
            let Some(assumption) = assumptions.first() else {
                return false;
            };
            assumptions.len() == 1
                && assumption.predecessor == expected.block
                && assumption.predicate == predicate.id
                && assumption.truth == truth
        })
}

fn collect_result_store(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    block: u64,
    expected: u32,
    target: u64,
) -> Option<(ValueId, ValueId)> {
    let ops = &function.get_block(block)?.ops;
    let address = match ops.first()? {
        SSAOp::IntAdd { dst, a, b }
            if register_var(graph, a, RBP_OFFSET, 8) && signed_constant(b, -4, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let copied = match ops.get(1)? {
        SSAOp::Copy { dst, src } if dst.size == 4 && constant(src, u64::from(expected), 4) => dst,
        _ => return None,
    };
    match ops.get(2)? {
        SSAOp::Store { addr, val, .. } if addr == address && val == copied => {}
        _ => return None,
    }
    if block != target {
        match ops.get(3) {
            Some(SSAOp::Branch { .. }) => {}
            None if ops.len() == 3 => {}
            _ => return None,
        }
    }
    Some((value(graph, address)?, value(graph, copied)?))
}

fn exact_result_memory_phi(
    memory: &MemorySSAFacts,
    result: &NestedWrap32GuardO0SlotFact,
    success: u64,
    failure: u64,
    exit: u64,
) -> bool {
    let stores = result
        .accesses
        .iter()
        .filter(|access| access.memory_defs == 1)
        .collect::<Vec<_>>();
    let loads = result
        .accesses
        .iter()
        .filter(|access| access.memory_uses == 1)
        .collect::<Vec<_>>();
    let ([success_store, failure_store], [load]) = (stores.as_slice(), loads.as_slice()) else {
        return false;
    };
    let Some(success_def) = memory
        .defs_by_inst
        .get(&success_store.access.inst)
        .and_then(|defs| defs.as_slice().first())
    else {
        return false;
    };
    let Some(failure_def) = memory
        .defs_by_inst
        .get(&failure_store.access.inst)
        .and_then(|defs| defs.as_slice().first())
    else {
        return false;
    };
    let Some(load_use) = memory
        .uses_by_inst
        .get(&load.access.inst)
        .and_then(|uses| uses.as_slice().first())
    else {
        return false;
    };
    let expected = BTreeMap::from([
        (success, success_def.next_version),
        (failure, failure_def.next_version),
    ]);
    let candidates = memory
        .phis_by_block
        .get(&exit)
        .map_or(&[][..], Vec::as_slice);
    let mut matching = candidates.iter().filter(|phi| {
        phi.object == result.object
            && phi.location == load_use.location
            && phi.output_version == load_use.version
            && phi.inputs.iter().copied().collect::<BTreeMap<_, _>>() == expected
            && phi.inputs.len() == 2
    });
    matching.next().is_some() && matching.next().is_none()
}

fn single_store_reaches_all_loads(
    memory: &MemorySSAFacts,
    slot: &NestedWrap32GuardO0SlotFact,
) -> bool {
    let stores = slot
        .accesses
        .iter()
        .filter(|access| access.memory_defs == 1)
        .collect::<Vec<_>>();
    let [store] = stores.as_slice() else {
        return false;
    };
    let Some(definition) = memory
        .defs_by_inst
        .get(&store.access.inst)
        .and_then(|defs| defs.as_slice().first())
    else {
        return false;
    };
    let loads = slot
        .accesses
        .iter()
        .filter(|access| access.memory_uses == 1)
        .collect::<Vec<_>>();
    !loads.is_empty()
        && loads.iter().all(|load| {
            memory
                .uses_by_inst
                .get(&load.access.inst)
                .and_then(|uses| uses.as_slice().first())
                .is_some_and(|use_fact| use_fact.version == definition.next_version)
        })
}

fn comparison_relay_values(fact: NestedWrap32GuardO0ComparisonFact) -> Vec<ValueId> {
    vec![
        fact.carry_or_borrow,
        fact.signed_overflow,
        fact.flag_packet.parity,
        fact.flag_packet.sign,
        fact.flag_packet.zero,
        fact.loaded,
        fact.inverted_zero,
        fact.flag_packet.low_byte,
        fact.flag_packet.population,
        fact.flag_packet.parity_bit,
        fact.copied_operand,
        fact.difference,
        fact.address,
    ]
}

fn comparison_relay_pairs(
    first: NestedWrap32GuardO0ComparisonFact,
    second: NestedWrap32GuardO0ComparisonFact,
) -> Vec<(ValueId, ValueId)> {
    comparison_relay_values(first)
        .into_iter()
        .zip(comparison_relay_values(second))
        .collect()
}

fn collect_phi_layer(
    function: &SSAFunction,
    graph: &SsaGraph,
    block: u64,
    predecessors: [u64; 2],
    expected_pairs: &[(ValueId, ValueId)],
) -> Option<NestedWrap32GuardO0PhiLayerFact> {
    let ssa_block = function.get_block(block)?;
    if ssa_block.phis.len() != expected_pairs.len()
        || sorted(function.predecessors(block)) != sorted(predecessors.to_vec())
    {
        return None;
    }
    let mut remaining = ssa_block.phis.iter().enumerate().collect::<Vec<_>>();
    let mut phis = Vec::with_capacity(expected_pairs.len());
    let mut outputs = Vec::with_capacity(expected_pairs.len());
    for (left, right) in expected_pairs {
        let position = remaining.iter().position(|(_, phi)| {
            let sources = phi
                .sources
                .iter()
                .filter_map(|(predecessor, value)| {
                    graph
                        .value_id_for_var(value)
                        .map(|value| (*predecessor, value))
                })
                .collect::<BTreeMap<_, _>>();
            phi.sources.len() == 2
                && sources.len() == 2
                && sources.get(&predecessors[0]) == Some(left)
                && sources.get(&predecessors[1]) == Some(right)
        });
        let (phi_index, phi) = remaining.remove(position?);
        let output = graph.value_id_for_var(&phi.dst)?;
        let inst = graph.def_inst(output)?;
        if !matches!(graph.inst(inst)?.payload, InstPayload::Phi { .. })
            || graph.inst(inst)?.canonical_storage != phi.canonical_storage
            || graph.block(graph.inst(inst)?.block)?.addr != block
            || phi_index >= ssa_block.phis.len()
        {
            return None;
        }
        phis.push(inst);
        outputs.push(output);
    }
    if !remaining.is_empty() {
        return None;
    }
    Some(NestedWrap32GuardO0PhiLayerFact {
        block,
        predecessors,
        phis: phis.into_boxed_slice(),
        outputs: outputs.into_boxed_slice(),
    })
}

fn collect_return(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    machine: &SourceMachineContext,
    topology: NestedWrap32GuardO0TopologyFact,
    result: &NestedWrap32GuardO0SlotFact,
) -> Option<NestedWrap32GuardO0ReturnFact> {
    let ops = &function.get_block(topology.exit)?.ops;
    let loaded = match ops.get(1)? {
        SSAOp::Load { dst, .. } if dst.size == 4 => dst,
        _ => return None,
    };
    let low32_copy = graph.inst_id_for_op_site(topology.exit, 2)?;
    match ops.get(2)? {
        SSAOp::Copy { dst, src } if src == loaded && register_var(graph, dst, RAX_OFFSET, 4) => {}
        _ => return None,
    }
    let returned = match ops.get(3)? {
        SSAOp::IntZExt { dst, src }
            if src == loaded && register_var(graph, dst, RAX_OFFSET, 8) =>
        {
            dst
        }
        _ => return None,
    };
    let return_inst = graph.inst_id_for_op_site(topology.exit, 10)?;
    let boundary = boundaries.returns.get(&return_inst)?;
    let [boundary_value] = boundary.values.as_slice() else {
        return None;
    };
    let return_storage = register_storage(machine, RAX_OFFSET, 8)?;
    if boundaries.returns.len() != 1
        || !boundary.complete
        || !boundary.register_compositions.is_empty()
        || boundary_value.slot
            != (CallBoundarySlot::Register {
                index: 0,
                storage: return_storage,
            })
        || boundary_value.value != value(graph, returned)?
    {
        return None;
    }
    Some(NestedWrap32GuardO0ReturnFact {
        result_load: result
            .accesses
            .iter()
            .find(|access| access.memory_uses == 1)?
            .access,
        loaded_result: value(graph, loaded)?,
        low32_copy,
        zero_extend: graph.inst_id_for_op_site(topology.exit, 3)?,
        returned_value: value(graph, returned)?,
        return_inst,
        return_target: match ops.get(10)? {
            SSAOp::Return { target } => value(graph, target)?,
            _ => return None,
        },
    })
}

fn all_slot_addresses_are_confined(
    graph: &SsaGraph,
    objects: &ObjectModel,
    slots: &NestedWrap32GuardO0SlotsFact,
) -> bool {
    let slot_iter =
        slots
            .parameter_homes
            .iter()
            .chain([&slots.sum, &slots.difference, &slots.result]);
    slot_iter.into_iter().all(|slot| {
        let allowed = slot
            .accesses
            .iter()
            .map(|access| access.access.inst)
            .collect::<BTreeSet<_>>();
        objects
            .value_objects
            .iter()
            .filter(|(_, object)| **object == slot.object)
            .all(|(value, _)| {
                address_value_is_confined(graph, *value, &allowed, &mut BTreeSet::new())
            })
    })
}

fn physical_ranges_are_exact_and_disjoint(
    frame: &NestedWrap32GuardO0FrameFact,
    slots: &NestedWrap32GuardO0SlotsFact,
) -> bool {
    let mut ranges = slots
        .parameter_homes
        .iter()
        .chain([&slots.sum, &slots.difference, &slots.result])
        .map(|slot| NestedWrap32GuardO0PhysicalRange {
            offset_from_entry_stack: slot.entry_stack_offset,
            size_bytes: slot.size_bytes,
        })
        .chain([frame.saved_frame_pointer_range, frame.return_address_range])
        .collect::<Vec<_>>();
    ranges.sort_by_key(|range| range.offset_from_entry_stack);
    let expected = [
        (-28, 4),
        (-24, 4),
        (-20, 4),
        (-16, 4),
        (-12, 4),
        (-8, 8),
        (0, 8),
    ];
    ranges
        .iter()
        .map(|range| (range.offset_from_entry_stack, range.size_bytes))
        .eq(expected)
        && ranges.windows(2).all(|pair| {
            pair[0]
                .offset_from_entry_stack
                .checked_add(i64::from(pair[0].size_bytes))
                .is_some_and(|end| end <= pair[1].offset_from_entry_stack)
        })
}

fn address_value_is_confined(
    graph: &SsaGraph,
    value: ValueId,
    allowed: &BTreeSet<InstId>,
    visiting: &mut BTreeSet<ValueId>,
) -> bool {
    if !visiting.insert(value) {
        return false;
    }
    let confined = graph.use_sites(value).iter().all(|use_site| {
        let Some(inst) = graph.inst(use_site.inst) else {
            return false;
        };
        if allowed.contains(&use_site.inst) {
            return use_site.input_idx == 0
                && matches!(
                    inst.payload,
                    InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. })
                );
        }
        matches!(inst.payload, InstPayload::Phi { .. })
            && inst
                .output
                .is_some_and(|output| address_value_is_confined(graph, output, allowed, visiting))
    });
    visiting.remove(&value);
    confined
}

fn all_memory_accesses_are_expected(
    function: &SSAFunction,
    graph: &SsaGraph,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    frame: &NestedWrap32GuardO0FrameFact,
    slots: &NestedWrap32GuardO0SlotsFact,
) -> bool {
    let slot_accesses = slots
        .parameter_homes
        .iter()
        .chain([&slots.sum, &slots.difference, &slots.result])
        .flat_map(|slot| slot.accesses.iter().map(|access| access.access));
    let frame_accesses = [
        frame.instructions[2],
        frame.instructions[5],
        frame.instructions[8],
    ]
    .into_iter()
    .map(|inst| StructuredAccessId { inst, ordinal: 0 });
    let expected = slot_accesses.chain(frame_accesses).collect::<BTreeSet<_>>();
    let actual_ops = function
        .blocks()
        .flat_map(|block| {
            block.ops.iter().enumerate().filter_map(move |(index, op)| {
                matches!(op, SSAOp::Load { .. } | SSAOp::Store { .. })
                    .then(|| graph.inst_id_for_op_site(block.addr, index))
                    .flatten()
                    .map(|inst| StructuredAccessId { inst, ordinal: 0 })
            })
        })
        .collect::<BTreeSet<_>>();
    expected == actual_ops
        && expected == memory_accesses.keys().copied().collect::<BTreeSet<_>>()
        && expected.len() == 20
}

fn collect_inventory_and_dispositions(
    function: &SSAFunction,
    graph: &SsaGraph,
    topology: NestedWrap32GuardO0TopologyFact,
    failure_phis: &NestedWrap32GuardO0PhiLayerFact,
    exit_phis: &NestedWrap32GuardO0PhiLayerFact,
) -> Option<(
    Box<[InstId]>,
    Box<[NestedWrap32GuardO0InstructionDisposition]>,
)> {
    let mut inventory = Vec::with_capacity(TOTAL_INSTRUCTIONS);
    let mut dispositions = Vec::with_capacity(TOTAL_INSTRUCTIONS);
    let mut add_ops = |block, start, end, class| {
        push_op_range(
            graph,
            block,
            start,
            end,
            class,
            &mut inventory,
            &mut dispositions,
        )
    };
    add_ops(
        topology.header,
        0,
        4,
        NestedWrap32GuardO0InstructionClass::FrameEnvelope,
    )?;
    add_ops(
        topology.header,
        4,
        10,
        NestedWrap32GuardO0InstructionClass::ParameterHomeState,
    )?;
    add_ops(
        topology.header,
        10,
        28,
        NestedWrap32GuardO0InstructionClass::Wrap32Arithmetic,
    )?;
    add_ops(
        topology.header,
        28,
        31,
        NestedWrap32GuardO0InstructionClass::LocalSpillState,
    )?;
    add_ops(
        topology.header,
        31,
        49,
        NestedWrap32GuardO0InstructionClass::Wrap32Arithmetic,
    )?;
    add_ops(
        topology.header,
        49,
        52,
        NestedWrap32GuardO0InstructionClass::LocalSpillState,
    )?;
    add_ops(
        topology.header,
        52,
        65,
        NestedWrap32GuardO0InstructionClass::ComparisonPacket,
    )?;
    add_ops(
        topology.header,
        65,
        66,
        NestedWrap32GuardO0InstructionClass::NestedControl,
    )?;
    add_ops(
        topology.second,
        0,
        13,
        NestedWrap32GuardO0InstructionClass::ComparisonPacket,
    )?;
    add_ops(
        topology.second,
        13,
        14,
        NestedWrap32GuardO0InstructionClass::NestedControl,
    )?;
    add_ops(
        topology.success,
        0,
        3,
        NestedWrap32GuardO0InstructionClass::PrivateResultCarrier,
    )?;
    add_ops(
        topology.success,
        3,
        4,
        NestedWrap32GuardO0InstructionClass::NestedControl,
    )?;
    add_ops(
        topology.forwarder,
        0,
        1,
        NestedWrap32GuardO0InstructionClass::NestedControl,
    )?;
    drop(add_ops);
    for inst in failure_phis
        .phis
        .iter()
        .chain(exit_phis.phis.iter())
        .copied()
    {
        inventory.push(inst);
        dispositions.push(NestedWrap32GuardO0InstructionDisposition {
            inst,
            class: NestedWrap32GuardO0InstructionClass::MachineRelayPhi,
        });
    }
    push_op_range(
        graph,
        topology.failure,
        0,
        3,
        NestedWrap32GuardO0InstructionClass::PrivateResultCarrier,
        &mut inventory,
        &mut dispositions,
    )?;
    push_op_range(
        graph,
        topology.exit,
        0,
        4,
        NestedWrap32GuardO0InstructionClass::ReturnComposition,
        &mut inventory,
        &mut dispositions,
    )?;
    push_op_range(
        graph,
        topology.exit,
        4,
        10,
        NestedWrap32GuardO0InstructionClass::FrameEnvelope,
        &mut inventory,
        &mut dispositions,
    )?;
    push_op_range(
        graph,
        topology.exit,
        10,
        11,
        NestedWrap32GuardO0InstructionClass::ReturnComposition,
        &mut inventory,
        &mut dispositions,
    )?;
    let exact = graph
        .insts
        .iter()
        .map(|inst| inst.id)
        .collect::<BTreeSet<_>>();
    let owned = inventory.iter().copied().collect::<BTreeSet<_>>();
    if inventory.len() != TOTAL_INSTRUCTIONS
        || dispositions.len() != TOTAL_INSTRUCTIONS
        || owned.len() != TOTAL_INSTRUCTIONS
        || exact != owned
        || function
            .blocks()
            .map(|block| block.ops.len() + block.phis.len())
            .sum::<usize>()
            != TOTAL_INSTRUCTIONS
    {
        return None;
    }
    Some((
        inventory.into_boxed_slice(),
        dispositions.into_boxed_slice(),
    ))
}

#[allow(clippy::too_many_arguments)]
fn push_op_range(
    graph: &SsaGraph,
    block: u64,
    start: usize,
    end: usize,
    class: NestedWrap32GuardO0InstructionClass,
    inventory: &mut Vec<InstId>,
    dispositions: &mut Vec<NestedWrap32GuardO0InstructionDisposition>,
) -> Option<()> {
    for index in start..end {
        let inst = graph.inst_id_for_op_site(block, index)?;
        inventory.push(inst);
        dispositions.push(NestedWrap32GuardO0InstructionDisposition { inst, class });
    }
    Some(())
}

fn value_is_copy_of(graph: &SsaGraph, output: ValueId, input: ValueId) -> bool {
    let Some(inst) = graph.def_inst(output).and_then(|inst| graph.inst(inst)) else {
        return false;
    };
    matches!(inst.payload, InstPayload::Op(SSAOp::Copy { .. }))
        && inst.inputs.as_slice() == [input]
        && inst.output == Some(output)
}

fn binary_var_output(op: &SSAOp) -> Option<(&SSAVar, &SSAVar, &SSAVar)> {
    match op {
        SSAOp::IntAdd { dst, a, b }
        | SSAOp::IntSub { dst, a, b }
        | SSAOp::IntLess { dst, a, b }
        | SSAOp::IntCarry { dst, a, b }
        | SSAOp::IntSCarry { dst, a, b }
        | SSAOp::IntSBorrow { dst, a, b } => Some((dst, a, b)),
        _ => None,
    }
}

fn access_value(slot: &NestedWrap32GuardO0SlotFact, write: bool) -> Option<ValueId> {
    let mut values = slot.accesses.iter().filter_map(|access| {
        ((access.memory_defs == 1) == write)
            .then_some(access.value)
            .flatten()
    });
    let value = values.next()?;
    values.next().is_none().then_some(value)
}

fn load_access_value(slot: &NestedWrap32GuardO0SlotFact) -> Option<ValueId> {
    let mut values = slot
        .accesses
        .iter()
        .filter(|access| access.memory_uses == 1)
        .filter_map(|access| access.value);
    let value = values.next()?;
    values.next().is_none().then_some(value)
}

fn load_value(op: &SSAOp, graph: &SsaGraph) -> Option<ValueId> {
    match op {
        SSAOp::Load { dst, .. } => value(graph, dst),
        _ => None,
    }
}

fn signed_constant(value: &SSAVar, expected: i64, size: u32) -> bool {
    value.size == size && value.constant_bits() == Some(expected as u64)
}

fn constant(value: &SSAVar, expected: u64, size: u32) -> bool {
    value.size == size && value.constant_bits() == Some(expected)
}

fn register_var(graph: &SsaGraph, value: &SSAVar, offset: u64, size: u32) -> bool {
    graph
        .canonical_storage_for_var(value)
        .is_some_and(|storage| register_at(storage, offset, size))
}

fn register_storage(
    machine: &SourceMachineContext,
    offset: u64,
    size: u32,
) -> Option<CanonicalStorageId> {
    let mut storages = machine
        .register_storages_by_name()
        .values()
        .copied()
        .filter(|storage| register_at(*storage, offset, size));
    let storage = storages.next()?;
    storages.next().is_none().then_some(storage)
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
    use r2il::{AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, Varnode};

    use crate::SsaArtifact;
    use crate::machine_context::{
        SourceAbiParameterSpec, SourceCarrierProjection, SourceFunctionInterface,
        SourceStackSlotSpec, SourceType, SourceTypeGraph,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(7);
    const ADDRESS: u64 = 0x4700;
    const COPY: u64 = 0x6a80;
    const CMP_LOAD: u64 = 0x11f00;
    const CMP_CONDITION: u64 = 0x12800;
    const CMP_LOW: u64 = 0x2c200;
    const CMP_POPULATION: u64 = 0x2c280;
    const CMP_PARITY_BIT: u64 = 0x2c300;
    const CMP_OPERAND: u64 = 0x3e900;
    const CMP_DIFFERENCE: u64 = 0x3ea00;

    fn register(offset: u64, size: u32) -> Varnode {
        Varnode::register(offset, size)
    }

    fn constant(value: u64, size: u32) -> Varnode {
        Varnode::constant(value, size)
    }

    fn temporary(offset: u64, size: u32, shift: u64) -> Varnode {
        Varnode::unique(offset + shift, size)
    }

    fn full_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-nested-wrap32-guard-o0-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("EAX", RAX_OFFSET, 4),
            ("RAX", RAX_OFFSET, 8),
            ("RSP", RSP_OFFSET, 8),
            ("RBP", RBP_OFFSET, 8),
            ("ESI", RSI_OFFSET, 4),
            ("RSI", RSI_OFFSET, 8),
            ("EDI", RDI_OFFSET, 4),
            ("RDI", RDI_OFFSET, 8),
            ("CF", CF_OFFSET, 1),
            ("PF", PF_OFFSET, 1),
            ("ZF", ZF_OFFSET, 1),
            ("SF", SF_OFFSET, 1),
            ("OF", OF_OFFSET, 1),
            ("RIP", RIP_OFFSET, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn interface(signed: bool) -> SourceFunctionInterface {
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let integer_kind = if signed {
            SourceTypeKind::SignedInteger
        } else {
            SourceTypeKind::UnsignedInteger
        };
        SourceFunctionInterface::new_exact_with_logical_types(
            b"nested-wrap32-guard-o0-revision-1".to_vec(),
            "sysv_amd64",
            [
                SourceAbiParameterSpec::new(0, full_storage(RDI_OFFSET)),
                SourceAbiParameterSpec::new(1, full_storage(RSI_OFFSET)),
            ],
            SourceFunctionReturn::Register {
                storage: full_storage(RAX_OFFSET),
            },
            [
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -8,
                    4,
                    0,
                    full_storage(RDI_OFFSET),
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -12,
                    4,
                    1,
                    full_storage(RSI_OFFSET),
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -16,
                    4,
                ),
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    full_storage(RBP_OFFSET),
                    -20,
                    4,
                ),
            ],
            [
                SourceLogicalValue::new(0, low32),
                SourceLogicalValue::new(0, low32),
            ],
            Some(SourceLogicalValue::new(0, low32)),
            Some(
                SourceTypeGraph::new([SourceType::new(0, integer_kind, 32, 32)], [])
                    .expect("one exact integer type"),
            ),
        )
        .expect("exact nested-guard interface")
    }

    fn push_frame_prefix(block: &mut R2ILBlock, shift: u64) {
        let saved = temporary(0x27000, 8, shift);
        block.push(R2ILOp::Copy {
            dst: saved.clone(),
            src: register(RBP_OFFSET, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: register(RSP_OFFSET, 8),
            a: register(RSP_OFFSET, 8),
            b: constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: register(RSP_OFFSET, 8),
            val: saved,
        });
        block.push(R2ILOp::Copy {
            dst: register(RBP_OFFSET, 8),
            src: register(RSP_OFFSET, 8),
        });
    }

    fn push_address(block: &mut R2ILBlock, offset: i64, shift: u64) -> Varnode {
        let address = temporary(ADDRESS, 8, shift);
        block.push(R2ILOp::IntAdd {
            dst: address.clone(),
            a: register(RBP_OFFSET, 8),
            b: constant(offset as u64, 8),
        });
        address
    }

    fn push_copy_store(block: &mut R2ILBlock, offset: i64, value: Varnode, shift: u64) -> Varnode {
        let address = push_address(block, offset, shift);
        let copied = temporary(COPY, 4, shift);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: value,
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: address,
            val: copied.clone(),
        });
        copied
    }

    fn push_load(block: &mut R2ILBlock, offset: i64, destination: Varnode, shift: u64) -> Varnode {
        let address = push_address(block, offset, shift);
        block.push(R2ILOp::Load {
            dst: destination.clone(),
            space: DATA,
            addr: address,
        });
        destination
    }

    fn push_flag_packet(block: &mut R2ILBlock, input: Varnode, shift: u64) {
        block.push(R2ILOp::IntSLess {
            dst: register(SF_OFFSET, 1),
            a: input.clone(),
            b: constant(0, input.size),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(ZF_OFFSET, 1),
            a: input.clone(),
            b: constant(0, input.size),
        });
        let low = temporary(CMP_LOW, 4, shift);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: input,
            b: constant(0xff, 4),
        });
        let population = temporary(CMP_POPULATION, 1, shift);
        block.push(R2ILOp::PopCount {
            dst: population.clone(),
            src: low,
        });
        let parity_bit = temporary(CMP_PARITY_BIT, 1, shift);
        block.push(R2ILOp::IntAnd {
            dst: parity_bit.clone(),
            a: population,
            b: constant(1, 1),
        });
        block.push(R2ILOp::IntEqual {
            dst: register(PF_OFFSET, 1),
            a: parity_bit,
            b: constant(0, 1),
        });
    }

    fn push_arithmetic(
        block: &mut R2ILBlock,
        subtract: bool,
        result_offset: i64,
        seed: u64,
        shift: u64,
    ) {
        let left = push_load(block, -8, temporary(seed, 4, shift), shift);
        block.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 4),
            src: left.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: left.clone(),
        });
        let first_right = push_load(block, -12, temporary(seed + 0x80, 4, shift), shift);
        if subtract {
            block.push(R2ILOp::IntLess {
                dst: register(CF_OFFSET, 1),
                a: left.clone(),
                b: first_right,
            });
        } else {
            block.push(R2ILOp::IntCarry {
                dst: register(CF_OFFSET, 1),
                a: left.clone(),
                b: first_right,
            });
        }
        let second_right = temporary(seed + 0x100, 4, shift);
        block.push(R2ILOp::Load {
            dst: second_right.clone(),
            space: DATA,
            addr: temporary(ADDRESS, 8, shift),
        });
        if subtract {
            block.push(R2ILOp::IntSBorrow {
                dst: register(OF_OFFSET, 1),
                a: left.clone(),
                b: second_right,
            });
        } else {
            block.push(R2ILOp::IntSCarry {
                dst: register(OF_OFFSET, 1),
                a: left.clone(),
                b: second_right,
            });
        }
        let third_right = temporary(seed + 0x180, 4, shift);
        block.push(R2ILOp::Load {
            dst: third_right.clone(),
            space: DATA,
            addr: temporary(ADDRESS, 8, shift),
        });
        let result = temporary(seed + 0x200, 4, shift);
        if subtract {
            block.push(R2ILOp::IntSub {
                dst: result.clone(),
                a: left,
                b: third_right,
            });
        } else {
            block.push(R2ILOp::IntAdd {
                dst: result.clone(),
                a: left,
                b: third_right,
            });
        }
        block.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: result.clone(),
        });
        push_flag_packet(block, result.clone(), shift);
        push_copy_store(block, result_offset, result, shift);
    }

    fn push_comparison(
        block: &mut R2ILBlock,
        offset: i64,
        expected: u32,
        true_target: u64,
        shift: u64,
    ) {
        let loaded = push_load(block, offset, temporary(CMP_LOAD, 4, shift), shift);
        let copied = temporary(CMP_OPERAND, 4, shift);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntLess {
            dst: register(CF_OFFSET, 1),
            a: copied.clone(),
            b: constant(u64::from(expected), 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: register(OF_OFFSET, 1),
            a: copied.clone(),
            b: constant(u64::from(expected), 4),
        });
        let difference = temporary(CMP_DIFFERENCE, 4, shift);
        block.push(R2ILOp::IntSub {
            dst: difference.clone(),
            a: copied,
            b: constant(u64::from(expected), 4),
        });
        push_flag_packet(block, difference, shift);
        let condition = temporary(CMP_CONDITION, 1, shift);
        block.push(R2ILOp::BoolNot {
            dst: condition.clone(),
            src: register(ZF_OFFSET, 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::ram(true_target, 8),
            cond: condition,
        });
    }

    fn blocks(base: u64, shift: u64) -> Vec<R2ILBlock> {
        let second_addr = base + 0x22;
        let success_addr = second_addr + 6;
        let forwarder_addr = success_addr + 9;
        let failure_addr = forwarder_addr + 2;
        let exit_addr = failure_addr + 7;

        let mut header = R2ILBlock::new(base, 0x22);
        push_frame_prefix(&mut header, shift);
        push_copy_store(&mut header, -8, register(RDI_OFFSET, 4), shift);
        push_copy_store(&mut header, -12, register(RSI_OFFSET, 4), shift);
        push_arithmetic(&mut header, false, -16, 0x10000, shift);
        push_arithmetic(&mut header, true, -20, 0x11000, shift);
        push_comparison(&mut header, -16, 0x64, failure_addr, shift);
        assert_eq!(header.ops.len(), HEADER_OPS);

        let mut second = R2ILBlock::new(second_addr, 6);
        push_comparison(&mut second, -20, 0x14, forwarder_addr, shift);
        assert_eq!(second.ops.len(), SECOND_OPS);

        let mut success = R2ILBlock::new(success_addr, 9);
        push_copy_store(&mut success, -4, constant(1, 4), shift);
        success.push(R2ILOp::Branch {
            target: Varnode::ram(exit_addr, 8),
        });

        let mut forwarder = R2ILBlock::new(forwarder_addr, 2);
        forwarder.push(R2ILOp::Branch {
            target: Varnode::ram(failure_addr, 8),
        });

        let mut failure = R2ILBlock::new(failure_addr, 7);
        push_copy_store(&mut failure, -4, constant(0, 4), shift);

        let mut exit = R2ILBlock::new(exit_addr, 5);
        let result_address = push_address(&mut exit, -4, shift);
        let result = temporary(0x12000, 4, shift);
        exit.push(R2ILOp::Load {
            dst: result.clone(),
            space: DATA,
            addr: result_address,
        });
        exit.push(R2ILOp::Copy {
            dst: register(RAX_OFFSET, 4),
            src: result.clone(),
        });
        exit.push(R2ILOp::IntZExt {
            dst: register(RAX_OFFSET, 8),
            src: result,
        });
        exit.push(R2ILOp::Copy {
            dst: temporary(0x13000, 8, shift),
            src: constant(0, 8),
        });
        let restored = temporary(0x13100, 8, shift);
        exit.push(R2ILOp::Load {
            dst: restored.clone(),
            space: DATA,
            addr: register(RSP_OFFSET, 8),
        });
        exit.push(R2ILOp::IntAdd {
            dst: register(RSP_OFFSET, 8),
            a: register(RSP_OFFSET, 8),
            b: constant(8, 8),
        });
        exit.push(R2ILOp::Copy {
            dst: register(RBP_OFFSET, 8),
            src: restored,
        });
        exit.push(R2ILOp::Load {
            dst: register(RIP_OFFSET, 8),
            space: DATA,
            addr: register(RSP_OFFSET, 8),
        });
        exit.push(R2ILOp::IntAdd {
            dst: register(RSP_OFFSET, 8),
            a: register(RSP_OFFSET, 8),
            b: constant(8, 8),
        });
        exit.push(R2ILOp::Return {
            target: register(RIP_OFFSET, 8),
        });
        assert_eq!(exit.ops.len(), EXIT_OPS);

        vec![header, second, success, forwarder, failure, exit]
    }

    fn artifact(blocks: &[R2ILBlock], signed: bool) -> SsaArtifact {
        SsaArtifact::for_decompile_with_interface(blocks, Some(&arch()), interface(signed))
            .expect("prepared nested guard")
    }

    fn collect(artifact: &SsaArtifact) -> Option<NestedWrap32GuardO0Fact> {
        collect_one(
            artifact.function(),
            artifact.graph(),
            artifact.objects(),
            artifact.memory(),
            artifact.predicates(),
            &artifact.facts().boundaries,
            &artifact.facts().structured.memory_accesses,
            artifact.machine_context(),
        )
    }

    #[test]
    fn exact_fixture_is_name_relocation_and_temporary_independent() {
        for (base, shift) in [(0x1000, 0), (0x71_0000, 0x80_0000)] {
            let artifact = artifact(&blocks(base, shift), true).with_name("cosmetic-only");
            let fact = collect(&artifact).expect("exact nested guard fact");
            assert_eq!(fact.topology.header, base);
            assert_eq!(fact.instruction_inventory.len(), TOTAL_INSTRUCTIONS);
            assert_eq!(fact.dispositions.len(), TOTAL_INSTRUCTIONS);
            assert_eq!(fact.failure_phis.phis.len(), FAILURE_PHIS);
            assert_eq!(fact.exit_phis.phis.len(), EXIT_PHIS);
            assert!(fact.validate_against_parts(
                artifact.function(),
                artifact.graph(),
                artifact.objects(),
                artifact.memory(),
                artifact.predicates(),
                &artifact.facts().boundaries,
                &artifact.facts().structured.memory_accesses,
                artifact.machine_context(),
            ));
        }
    }

    #[test]
    fn wrong_type_constant_result_or_extra_operation_refuses() {
        let exact_blocks = blocks(0x1000, 0);
        assert!(collect(&artifact(&exact_blocks, false)).is_none());

        let mut wrong_constant = exact_blocks.clone();
        let R2ILOp::IntSub { b, .. } = &mut wrong_constant[0].ops[57] else {
            panic!("first compare subtraction");
        };
        *b = constant(0x65, 4);
        assert!(collect(&artifact(&wrong_constant, true)).is_none());

        let mut wrong_result = blocks(0x2000, 0);
        let R2ILOp::Copy { src, .. } = &mut wrong_result[2].ops[1] else {
            panic!("success value copy");
        };
        *src = constant(2, 4);
        assert!(collect(&artifact(&wrong_result, true)).is_none());

        let mut extra = blocks(0x3000, 0);
        extra[0].ops.insert(10, R2ILOp::Nop);
        assert!(collect(&artifact(&extra, true)).is_none());
    }

    #[test]
    fn changed_control_edge_refuses() {
        let mut changed = blocks(0x4000, 0);
        let success = changed[2].addr;
        let R2ILOp::CBranch { target, .. } = &mut changed[0].ops[65] else {
            panic!("header branch");
        };
        *target = Varnode::ram(success, 8);
        assert!(collect(&artifact(&changed, true)).is_none());
    }
}
