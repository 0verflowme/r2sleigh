//! Sealed source fact for the exact ARM64 O0 stack-backed `fnv_fold` shape.
//!
//! This module deliberately does not generalize the four-block O2 FNV fact.
//! The admitted O0 function has a different proof shape: its induction,
//! accumulator, and ASCII byte are memory carriers in one SP-only leaf frame.

use std::collections::{BTreeMap, BTreeSet};

use r2il::SpaceId;

use crate::cfg::BlockTerminator;
use crate::function::{SSAFunction, StackAddressBase, StackAddressRoot};
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineMemoryEndianness,
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceStackSlotRole,
    SourceTypeKind,
};
use crate::op::SSAOp;
use crate::semantic::{
    CallBoundarySlot, CompareKind, MemoryDefFact, MemoryLocation, MemoryPhiFact, MemorySSAFacts,
    MemoryUseFact, MemoryVersion, ObjectId, ObjectKind, ObjectModel, PredicateFacts, PredicateId,
    RelativeMemoryAddress, SourceBoundaryFacts, SourceFormalParameterFact, StructuredAccessId,
    StructuredLoopFact, StructuredLoopKind, StructuredMemoryAccessFact,
};
use crate::var::{CanonicalStorageId, CanonicalStorageSpace};

pub const CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION: u32 = 1;

const FRAME_SIZE: u64 = 0x30;
const OFFSET_BASIS: u64 = 0x1465_0fb0_739d_0383;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0TopologyFact {
    pub entry: u64,
    pub header: u64,
    pub first_forwarder: u64,
    pub first_predicate_block: u64,
    pub second_forwarder: u64,
    pub second_predicate_block: u64,
    pub lowercase_forwarder: u64,
    pub lowercase_block: u64,
    pub hash_block: u64,
    pub latch: u64,
    pub exit: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0AbiFact {
    pub revision_identity: Box<[u8]>,
    pub pointer_parameter: SourceFormalParameterFact,
    pub length_parameter: SourceFormalParameterFact,
    pub return_storage: CanonicalStorageId,
    pub pointer_logical: SourceLogicalValue,
    pub length_logical: SourceLogicalValue,
    pub return_logical: SourceLogicalValue,
    pub memory_space: SpaceId,
    pub memory_address_bits: u32,
    pub memory_word_size_bytes: u32,
    pub memory_endianness: MachineMemoryEndianness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0AccessFact {
    pub access: StructuredAccessId,
    pub object: ObjectId,
    pub address: ValueId,
    pub value: ValueId,
    pub is_write: bool,
    pub width: u32,
    pub memory_space: SpaceId,
    pub memory_uses: Box<[MemoryUseFact]>,
    pub memory_defs: Box<[MemoryDefFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0SlotFact {
    pub object: ObjectId,
    pub declared_offset_from_allocated_sp: i64,
    pub offset_from_entry_sp: i64,
    pub width: u32,
    pub role: SourceStackSlotRole,
    pub accesses: Box<[StructuredAccessId]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0FrameFact {
    pub stack_storage: CanonicalStorageId,
    pub link_register_storage: CanonicalStorageId,
    pub entry_sp: ValueId,
    pub allocated_sp: ValueId,
    pub allocate_inst: InstId,
    pub allocate_arithmetic_inst: InstId,
    pub allocate_support_insts: Box<[InstId]>,
    pub restored_sp: ValueId,
    pub restore_inst: InstId,
    pub restore_arithmetic_inst: InstId,
    pub restore_support_insts: Box<[InstId]>,
    pub address_support_insts: Box<[InstId]>,
    pub return_address: ValueId,
    pub return_target: ValueId,
    pub return_target_support_insts: Box<[InstId]>,
    pub return_inst: InstId,
    pub homes: Box<[CanonicalFnvFoldO0SlotFact]>,
    pub locals: Box<[CanonicalFnvFoldO0SlotFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0PredicateFact {
    pub predicate: PredicateId,
    pub condition: ValueId,
    pub branch_inst: InstId,
    pub witness_insts: Box<[InstId]>,
    pub lhs: ValueId,
    pub rhs: ValueId,
    pub kind: CompareKind,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0IndexFact {
    pub object: ObjectId,
    pub initializer_store: StructuredAccessId,
    pub initializer_support_insts: Box<[InstId]>,
    pub initializer_version: MemoryVersion,
    pub phi: MemoryPhiFact,
    pub header_load: StructuredAccessId,
    pub address_load: StructuredAccessId,
    pub latch_load: StructuredAccessId,
    pub update: ValueId,
    pub update_inst: InstId,
    pub update_support_insts: Box<[InstId]>,
    pub update_store: StructuredAccessId,
    pub update_version: MemoryVersion,
    pub buffer_address: ValueId,
    pub buffer_access: StructuredAccessId,
    pub buffer_object: ObjectId,
    pub raw_byte: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0ParameterHomeRelayFact {
    pub parameter_index: u32,
    pub initializer_store: StructuredAccessId,
    pub initializer_version: MemoryVersion,
    pub phi: MemoryPhiFact,
    pub reload: StructuredAccessId,
    pub value: ValueId,
}

/// Source-lifetime alias policy for the one external byte read.
///
/// Construction proves that the analyzer's escaped-unknown read is rooted only
/// in the exact parameter-Home relay plus the loop index. Its conservative
/// aliases are retained rather than rewritten as a parameter-object version.
/// Presence also witnesses a completely classified five-object private frame,
/// no frame-derived value escaping through a store or return, and the exact
/// source `u8 *` external-input contract retained in the enclosing ABI fact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0ExternalReadAliasPolicyFact {
    pub complete_frame_separation: bool,
    pub frame_address_escape_free: bool,
    pub source_external_byte_pointer: bool,
    pub external_object: ObjectId,
    pub external_read: StructuredAccessId,
    pub pointer_home: CanonicalFnvFoldO0ParameterHomeRelayFact,
    pub index_load: StructuredAccessId,
    pub address: ValueId,
    pub address_inst: InstId,
    pub address_support_insts: Box<[InstId]>,
    pub classified_frame_objects: Box<[ObjectId]>,
    pub external_memory_use: MemoryUseFact,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0AsciiFact {
    pub object: ObjectId,
    pub initial_store: StructuredAccessId,
    pub initial_version: MemoryVersion,
    pub first_load: StructuredAccessId,
    pub first_predicate: CanonicalFnvFoldO0PredicateFact,
    pub second_load: StructuredAccessId,
    pub second_predicate: CanonicalFnvFoldO0PredicateFact,
    pub lowercase_load: StructuredAccessId,
    pub lowercase: ValueId,
    pub lowercase_inst: InstId,
    pub lowercase_support_insts: Box<[InstId]>,
    pub lowercase_store: StructuredAccessId,
    pub lowercase_version: MemoryVersion,
    pub merge_phi: MemoryPhiFact,
    pub merge_load: StructuredAccessId,
    pub selected_byte: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0HashFact {
    pub object: ObjectId,
    pub offset_basis: u64,
    pub initializer: ValueId,
    pub initializer_witness_insts: Box<[InstId]>,
    pub initializer_store: StructuredAccessId,
    pub initializer_version: MemoryVersion,
    pub phi: MemoryPhiFact,
    pub body_load: StructuredAccessId,
    pub selected64: ValueId,
    pub selected64_inst: InstId,
    pub xor: ValueId,
    pub xor_inst: InstId,
    pub xor_store: StructuredAccessId,
    pub xor_version: MemoryVersion,
    pub xor_reload: StructuredAccessId,
    pub prime: ValueId,
    pub prime_value: u64,
    pub prime_witness_insts: Box<[InstId]>,
    pub product: ValueId,
    pub multiply_inst: InstId,
    pub product_store: StructuredAccessId,
    pub product_version: MemoryVersion,
    pub exit_load: StructuredAccessId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0ReturnFact {
    pub hash_access: StructuredAccessId,
    pub hash_version: MemoryVersion,
    pub value: ValueId,
    pub storage: CanonicalStorageId,
    pub return_inst: InstId,
    pub return_target: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0MemoryFact {
    /// Complete canonical instruction-ID inventory for downstream obligation joins.
    /// Its retained order is not semantic evidence for block or source phases.
    pub instruction_inventory: Box<[InstId]>,
    /// Pure SSA instructions outside the exact observable dependency closure.
    /// The source obligation inventory must independently classify every one
    /// as proven dead before certification may absorb it.
    pub proven_dead_instructions: Box<[InstId]>,
    pub accesses: Box<[CanonicalFnvFoldO0AccessFact]>,
    pub unused_provisional_phis: Box<[MemoryPhiFact]>,
    pub conservative_alias_only_header_phis: Box<[MemoryPhiFact]>,
}

/// Exact, name-independent source evidence for the admitted ARM64 O0 function.
/// Downstream certification must still exhaustively join instruction and effect
/// obligations before authorizing a rendered function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalFnvFoldO0Fact {
    pub schema_version: u32,
    pub loop_id: crate::semantic::LoopId,
    pub topology: CanonicalFnvFoldO0TopologyFact,
    pub abi: CanonicalFnvFoldO0AbiFact,
    pub frame: CanonicalFnvFoldO0FrameFact,
    pub memory: CanonicalFnvFoldO0MemoryFact,
    pub loop_guard: CanonicalFnvFoldO0PredicateFact,
    pub index: CanonicalFnvFoldO0IndexFact,
    pub length_home: CanonicalFnvFoldO0ParameterHomeRelayFact,
    pub external_read_policy: CanonicalFnvFoldO0ExternalReadAliasPolicyFact,
    pub ascii: CanonicalFnvFoldO0AsciiFact,
    pub hash: CanonicalFnvFoldO0HashFact,
    pub returned: CanonicalFnvFoldO0ReturnFact,
}

impl CanonicalFnvFoldO0Fact {
    pub fn validate_against(&self, artifact: &crate::function::SsaArtifact) -> bool {
        if self.schema_version != CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION {
            return false;
        }
        let facts = collect_canonical_fnv_fold_o0_facts(
            artifact.function(),
            artifact.graph(),
            artifact.objects(),
            artifact.memory(),
            artifact.predicates(),
            &artifact.facts().boundaries,
            &artifact.structured().loops,
            &artifact.structured().memory_accesses,
            artifact.machine_context(),
        );
        facts.len() == 1 && facts.get(&self.topology.header) == Some(self)
    }
}

#[derive(Clone, Copy)]
struct SlotDeclaration {
    base_storage: CanonicalStorageId,
    declared_offset: i64,
    physical_offset: i64,
    width: u32,
    role: SourceStackSlotRole,
}

struct TopologyCandidate<'a> {
    fact: CanonicalFnvFoldO0TopologyFact,
    loop_fact: &'a StructuredLoopFact,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_canonical_fnv_fold_o0_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    boundaries: &SourceBoundaryFacts,
    loops: &BTreeMap<crate::semantic::LoopId, StructuredLoopFact>,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
) -> BTreeMap<u64, CanonicalFnvFoldO0Fact> {
    let mut facts = BTreeMap::new();
    let Some(topology) = topology_candidate(function, loops) else {
        return facts;
    };
    let Some(fact) = collect_one(
        function,
        graph,
        objects,
        memory,
        predicates,
        boundaries,
        memory_accesses,
        machine,
        topology,
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
    topology: TopologyCandidate<'_>,
) -> Option<CanonicalFnvFoldO0Fact> {
    if machine.schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
        || !machine.abi_model().is_available()
        || !machine.abi_model().is_coherent()
        || !machine.memory_model().is_available()
        || !machine.memory_model().is_coherent()
        || !boundaries.calls.is_empty()
        || !function_has_only_plain_memory_and_no_calls(function)
    {
        return None;
    }
    let memory_space = unique_access_memory_space(graph, memory_accesses, machine)?;
    let abi = collect_abi(machine, boundaries, memory_space)?;
    let declarations = collect_slot_declarations(machine, &abi)?;
    let slots_by_offset = collect_slots(objects, memory_accesses, &declarations)?;
    let buffer_object = unique_buffer_object(
        objects,
        memory_accesses,
        &slots_by_offset,
        abi.pointer_parameter.index,
    )?;
    let access_inventory = collect_access_inventory(
        graph,
        memory,
        memory_accesses,
        machine,
        memory_space,
        &topology.fact,
        &slots_by_offset,
        buffer_object,
    )?;

    let frame = collect_frame(
        function,
        graph,
        machine,
        &abi,
        &declarations,
        &slots_by_offset,
        &topology.fact,
        &access_inventory,
    )?;
    let buf_home = slot_accesses(&access_inventory, slot(&slots_by_offset, -8)?.object, 2)?;
    let n_home = slot_accesses(&access_inventory, slot(&slots_by_offset, -16)?.object, 2)?;
    let hash_accesses = slot_accesses(&access_inventory, slot(&slots_by_offset, -24)?.object, 6)?;
    let index_accesses = slot_accesses(&access_inventory, slot(&slots_by_offset, -32)?.object, 5)?;
    let byte_accesses = slot_accesses(&access_inventory, slot(&slots_by_offset, -33)?.object, 6)?;
    let index_header_access = *index_accesses.get(1)?;
    let index_address_access = *index_accesses.get(2)?;
    let hash_exit_access = *hash_accesses.get(5)?;
    let buffer_accesses = slot_accesses(&access_inventory, buffer_object, 1)?;
    let [buf_init, buf_reload] = buf_home.as_slice() else {
        return None;
    };
    let [n_init, n_reload] = n_home.as_slice() else {
        return None;
    };
    if copy_root(graph, buf_init.value)? != abi.pointer_parameter.value
        || copy_root(graph, n_init.value)? != abi.length_parameter.value
    {
        return None;
    }
    let pointer_home = collect_parameter_home_relay(
        memory,
        &topology.fact,
        abi.pointer_parameter.index,
        buf_init,
        buf_reload,
    )?;
    let length_home = collect_parameter_home_relay(
        memory,
        &topology.fact,
        abi.length_parameter.index,
        n_init,
        n_reload,
    )?;

    let index = collect_index(
        graph,
        memory,
        &topology.fact,
        &index_accesses,
        &buffer_accesses,
        buffer_object,
    )?;
    let external_read_policy = collect_external_read_policy(
        graph,
        &abi,
        frame.allocated_sp,
        &slots_by_offset,
        &pointer_home,
        index_address_access,
        *buffer_accesses.first()?,
    )?;
    let loop_guard = collect_predicate(
        graph,
        predicates,
        topology.fact.header,
        CompareKind::LessEqual,
        n_reload.value,
        index_header_access.value,
        [topology.fact.exit, topology.fact.first_forwarder],
    )?;
    if topology.loop_fact.condition != Some(loop_guard.predicate) {
        return None;
    }
    let ascii = collect_ascii(
        graph,
        memory,
        predicates,
        &topology.fact,
        &byte_accesses,
        index.raw_byte,
    )?;
    let hash = collect_hash(
        graph,
        memory,
        &topology.fact,
        &hash_accesses,
        ascii.selected_byte,
    )?;
    let returned = collect_return(
        graph,
        boundaries,
        &abi,
        &frame,
        &hash,
        hash_exit_access,
        machine,
    )?;
    let (instruction_inventory, proven_dead_instructions) = collect_exact_instruction_inventory(
        graph,
        &topology.fact,
        &frame,
        &access_inventory,
        [&loop_guard, &ascii.first_predicate, &ascii.second_predicate],
    )?;
    let effective_phis = BTreeSet::from([
        (index.phi.object, index.phi.output_version),
        (ascii.merge_phi.object, ascii.merge_phi.output_version),
        (hash.phi.object, hash.phi.output_version),
        (pointer_home.phi.object, pointer_home.phi.output_version),
        (length_home.phi.object, length_home.phi.output_version),
    ]);
    let (unused_provisional_phis, conservative_alias_only_header_phis) =
        collect_non_effective_header_phis(
            memory,
            &topology.fact,
            &effective_phis,
            &slots_by_offset,
            &external_read_policy,
        )?;

    Some(CanonicalFnvFoldO0Fact {
        schema_version: CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION,
        loop_id: topology.loop_fact.id,
        topology: topology.fact,
        abi,
        frame,
        memory: CanonicalFnvFoldO0MemoryFact {
            instruction_inventory: instruction_inventory.into_boxed_slice(),
            proven_dead_instructions: proven_dead_instructions.into_boxed_slice(),
            accesses: access_inventory.into_boxed_slice(),
            unused_provisional_phis: unused_provisional_phis.into_boxed_slice(),
            conservative_alias_only_header_phis: conservative_alias_only_header_phis
                .into_boxed_slice(),
        },
        loop_guard,
        index,
        length_home,
        external_read_policy,
        ascii,
        hash,
        returned,
    })
}

/// Prove that the exact O0 witness owns every retained SSA instruction.
///
/// The admitted side-effect/control roots are the exact memory accesses, frame
/// allocation/restoration, and one source terminator per canonical block. All
/// pure operation producers must be dependencies of those roots. Register SSA
/// phis may remain as structural normalization artifacts, but they do not pull
/// their otherwise-dead inputs into the admitted set. This prevents an
/// unrelated trap, unknown effect, or dead computation from acquiring FNV
/// authority merely because it happens to reside in one of the eleven blocks.
fn collect_exact_instruction_inventory(
    graph: &SsaGraph,
    topology: &CanonicalFnvFoldO0TopologyFact,
    frame: &CanonicalFnvFoldO0FrameFact,
    accesses: &[CanonicalFnvFoldO0AccessFact],
    predicates: [&CanonicalFnvFoldO0PredicateFact; 3],
) -> Option<(Vec<InstId>, Vec<InstId>)> {
    let expected_controls = BTreeMap::from([
        (topology.entry, 0_u8),
        (topology.header, 1),
        (topology.first_forwarder, 0),
        (topology.first_predicate_block, 1),
        (topology.second_forwarder, 0),
        (topology.second_predicate_block, 1),
        (topology.lowercase_forwarder, 0),
        (topology.lowercase_block, 0),
        (topology.hash_block, 0),
        (topology.latch, 0),
        (topology.exit, 2),
    ]);
    if expected_controls.len() != 11 {
        return None;
    }

    let mut controls = BTreeMap::new();
    for inst in &graph.insts {
        let InstPayload::Op(op) = &inst.payload else {
            continue;
        };
        let kind = match op {
            SSAOp::Branch { .. } => 0,
            SSAOp::CBranch { .. } => 1,
            SSAOp::Return { .. } => 2,
            _ => continue,
        };
        let block = graph.block(inst.block)?.addr;
        if controls.insert(block, (inst.id, kind)).is_some() {
            return None;
        }
    }
    if controls.len() != expected_controls.len()
        || controls
            .iter()
            .any(|(block, (_, kind))| expected_controls.get(block) != Some(kind))
        || controls.keys().copied().collect::<BTreeSet<_>>()
            != expected_controls.keys().copied().collect()
        || controls.get(&topology.exit).map(|(inst, _)| *inst) != Some(frame.return_inst)
        || predicates.iter().any(|predicate| {
            graph
                .op_site_for_inst(predicate.branch_inst)
                .is_none_or(|(block, _)| {
                    controls.get(&block).map(|(inst, _)| *inst) != Some(predicate.branch_inst)
                })
        })
    {
        return None;
    }

    let mut roots = accesses
        .iter()
        .map(|access| access.access.inst)
        .collect::<BTreeSet<_>>();
    roots.insert(frame.allocate_inst);
    roots.insert(frame.restore_inst);
    roots.extend(controls.values().map(|(inst, _)| *inst));

    let mut admitted = BTreeSet::new();
    let mut pending = roots.into_iter().collect::<Vec<_>>();
    while let Some(inst_id) = pending.pop() {
        if !admitted.insert(inst_id) {
            continue;
        }
        let inst = graph.inst(inst_id)?;
        pending.extend(
            inst.inputs
                .iter()
                .filter_map(|value| graph.def_inst(*value)),
        );
    }
    let unadmitted = graph
        .insts
        .iter()
        .filter(|inst| !admitted.contains(&inst.id))
        .collect::<Vec<_>>();
    if unadmitted.iter().any(|inst| {
        !matches!(
            &inst.payload,
            InstPayload::Phi { .. }
                | InstPayload::Op(
                    SSAOp::Copy { .. }
                        | SSAOp::IntSub { .. }
                        | SSAOp::IntCarry { .. }
                        | SSAOp::IntSCarry { .. }
                        | SSAOp::IntSBorrow { .. }
                        | SSAOp::IntEqual { .. }
                        | SSAOp::IntLessEqual { .. }
                        | SSAOp::IntSLess { .. }
                        | SSAOp::IntZExt { .. }
                        | SSAOp::Subpiece { offset: 0, .. }
                )
        )
    }) {
        return None;
    }
    let proven_dead_instructions = unadmitted
        .into_iter()
        .map(|inst| inst.id)
        .collect::<Vec<_>>();
    Some((
        graph.insts.iter().map(|inst| inst.id).collect(),
        proven_dead_instructions,
    ))
}

fn topology_candidate<'a>(
    function: &SSAFunction,
    loops: &'a BTreeMap<crate::semantic::LoopId, StructuredLoopFact>,
) -> Option<TopologyCandidate<'a>> {
    if function.num_blocks() != 11 {
        return None;
    }
    let mut candidates = loops.values().filter(|loop_fact| {
        loop_fact.kind == StructuredLoopKind::Natural
            && loop_fact.body.len() == 9
            && loop_fact.latches.len() == 1
            && loop_fact.exits.len() == 1
    });
    let loop_fact = candidates.next()?;
    if candidates.next().is_some() {
        return None;
    }
    let entry = function.entry;
    let [latch] = loop_fact.latches.as_slice() else {
        return None;
    };
    let [exit] = loop_fact.exits.as_slice() else {
        return None;
    };
    let (header, latch, exit) = (loop_fact.header, *latch, *exit);
    let first_forwarder = other_successor(function, header, exit)?;
    let first_predicate_block = sole_successor(function, first_forwarder)?;
    let (
        second_forwarder,
        second_predicate_block,
        lowercase_forwarder,
        lowercase_block,
        hash_block,
    ) = unique_topology_tail(function, first_predicate_block, latch)?;
    if loop_fact.header != header
        || sole_successor(function, hash_block)? != latch
        || sole_successor(function, latch)? != header
        || sole_successor(function, entry)? != header
        || function
            .predecessors(header)
            .into_iter()
            .collect::<BTreeSet<_>>()
            != BTreeSet::from([entry, latch])
        || function
            .predecessors(hash_block)
            .into_iter()
            .collect::<BTreeSet<_>>()
            != BTreeSet::from([
                first_predicate_block,
                second_predicate_block,
                lowercase_block,
            ])
        || function
            .block_addrs()
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            != BTreeSet::from([
                entry,
                header,
                first_forwarder,
                first_predicate_block,
                second_forwarder,
                second_predicate_block,
                lowercase_forwarder,
                lowercase_block,
                hash_block,
                latch,
                exit,
            ])
        || function
            .block_addrs()
            .iter()
            .map(|block| function.successors(*block).len())
            .sum::<usize>()
            != 13
        || !is_branch_to(function, entry, header)
        || !is_conditional(function, header, exit, first_forwarder)
        || !is_branch_to(function, first_forwarder, first_predicate_block)
        || !is_conditional_to_set(
            function,
            first_predicate_block,
            [hash_block, second_forwarder],
        )
        || !is_branch_to(function, second_forwarder, second_predicate_block)
        || !is_conditional_to_set(
            function,
            second_predicate_block,
            [hash_block, lowercase_forwarder],
        )
        || !is_branch_to(function, lowercase_forwarder, lowercase_block)
        || !is_branch_to(function, lowercase_block, hash_block)
        || !is_branch_to(function, hash_block, latch)
        || !is_branch_to(function, latch, header)
        || !matches!(
            function
                .cfg()
                .get_block(exit)
                .map(|block| &block.terminator),
            Some(BlockTerminator::Return)
        )
    {
        return None;
    }
    let body = loop_fact.body.iter().copied().collect::<BTreeSet<_>>();
    if body
        != BTreeSet::from([
            header,
            first_forwarder,
            first_predicate_block,
            second_forwarder,
            second_predicate_block,
            lowercase_forwarder,
            lowercase_block,
            hash_block,
            latch,
        ])
    {
        return None;
    }
    Some(TopologyCandidate {
        fact: CanonicalFnvFoldO0TopologyFact {
            entry,
            header,
            first_forwarder,
            first_predicate_block,
            second_forwarder,
            second_predicate_block,
            lowercase_forwarder,
            lowercase_block,
            hash_block,
            latch,
            exit,
        },
        loop_fact,
    })
}

fn collect_abi(
    machine: &SourceMachineContext,
    boundaries: &SourceBoundaryFacts,
    memory_space_id: SpaceId,
) -> Option<CanonicalFnvFoldO0AbiFact> {
    let interface = machine.function_interface()?;
    let [pointer_spec, length_spec] = interface.parameters() else {
        return None;
    };
    let SourceFunctionReturn::Register {
        storage: return_storage,
    } = interface.return_kind()
    else {
        return None;
    };
    let [pointer_logical, length_logical] = interface.parameter_logical_values() else {
        return None;
    };
    let return_logical = interface.return_logical_value()?;
    let type_graph = interface.type_graph()?;
    let pointer_type = type_graph.types().get(pointer_logical.type_id() as usize)?;
    let SourceTypeKind::Pointer { target_type_id } = pointer_type.kind() else {
        return None;
    };
    let byte_type = type_graph.types().get(target_type_id as usize)?;
    let length_type = type_graph.types().get(length_logical.type_id() as usize)?;
    let return_type = type_graph.types().get(return_logical.type_id() as usize)?;
    let full64 = |logical: SourceLogicalValue| {
        logical.carrier().kind() == SourceCarrierKind::Full
            && logical.carrier().offset_bits() == 0
            && logical.carrier().size_bits() == 64
    };
    let memory_space = machine.memory_model().space(memory_space_id)?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity().is_empty()
        || !interface.stack_slot_roles_complete()
        || interface.stack_slots().len() != 5
        || type_graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        || type_graph.types().len() != 3
        || !type_graph.aggregates().is_empty()
        || pointer_spec.index() != 0
        || length_spec.index() != 1
        || pointer_spec.storage().size != 8
        || length_spec.storage().size != 8
        || return_storage.size != 8
        || return_storage != pointer_spec.storage()
        || pointer_type.size_bits() != 64
        || pointer_type.align_bits() != 64
        || byte_type.kind() != SourceTypeKind::UnsignedInteger
        || byte_type.size_bits() != 8
        || byte_type.align_bits() != 8
        || length_type.kind() != SourceTypeKind::UnsignedInteger
        || length_type.size_bits() != 64
        || length_type.align_bits() != 64
        || return_type != length_type
        || !full64(*pointer_logical)
        || !full64(*length_logical)
        || !full64(return_logical)
        || memory_space.address_bits() != 64
        || memory_space.word_size_bytes() != 1
        || memory_space.endianness() != MachineMemoryEndianness::Little
        || boundaries.parameters.len() != 2
        || !boundaries.calls.is_empty()
    {
        return None;
    }
    let pointer_parameter = *boundaries.parameters.get(&0)?;
    let length_parameter = *boundaries.parameters.get(&1)?;
    if pointer_parameter.index != 0
        || length_parameter.index != 1
        || pointer_parameter.storage != pointer_spec.storage()
        || length_parameter.storage != length_spec.storage()
    {
        return None;
    }
    Some(CanonicalFnvFoldO0AbiFact {
        revision_identity: interface.revision_identity().to_vec().into_boxed_slice(),
        pointer_parameter,
        length_parameter,
        return_storage,
        pointer_logical: *pointer_logical,
        length_logical: *length_logical,
        return_logical,
        memory_space: memory_space_id,
        memory_address_bits: memory_space.address_bits(),
        memory_word_size_bytes: memory_space.word_size_bytes(),
        memory_endianness: memory_space.endianness(),
    })
}

fn collect_slot_declarations(
    machine: &SourceMachineContext,
    abi: &CanonicalFnvFoldO0AbiFact,
) -> Option<BTreeMap<i64, SlotDeclaration>> {
    let interface = machine.function_interface()?;
    let declarations = interface
        .stack_slots()
        .iter()
        .map(|slot| {
            let physical_offset = slot.offset().checked_sub(i64::try_from(FRAME_SIZE).ok()?)?;
            Some((
                physical_offset,
                SlotDeclaration {
                    base_storage: slot.base_storage(),
                    declared_offset: slot.offset(),
                    physical_offset,
                    width: slot.size_bytes(),
                    role: slot.role(),
                },
            ))
        })
        .collect::<Option<BTreeMap<_, _>>>()?;
    let expected = [
        (-33, 15, 1, SourceStackSlotRole::Local),
        (-32, 16, 8, SourceStackSlotRole::Local),
        (-24, 24, 8, SourceStackSlotRole::Local),
        (
            -16,
            32,
            8,
            SourceStackSlotRole::ParameterHome {
                parameter_index: 1,
                home_storage: abi.length_parameter.storage,
            },
        ),
        (
            -8,
            40,
            8,
            SourceStackSlotRole::ParameterHome {
                parameter_index: 0,
                home_storage: abi.pointer_parameter.storage,
            },
        ),
    ];
    if declarations.len() != expected.len()
        || expected.iter().any(|(physical, declared, width, role)| {
            declarations.get(physical).is_none_or(|declaration| {
                declaration.physical_offset != *physical
                    || declaration.declared_offset != *declared
                    || declaration.width != *width
                    || declaration.role != *role
            })
        })
        || interface
            .stack_slots()
            .iter()
            .any(|slot| slot.base() != StackAddressBase::StackPointer)
    {
        return None;
    }
    let storage = declarations.values().next()?.base_storage;
    if storage.size != 8
        || declarations
            .values()
            .any(|declaration| declaration.base_storage != storage)
    {
        return None;
    }
    Some(declarations)
}

fn collect_slots(
    objects: &ObjectModel,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    declarations: &BTreeMap<i64, SlotDeclaration>,
) -> Option<BTreeMap<i64, CanonicalFnvFoldO0SlotFact>> {
    let mut slots = BTreeMap::new();
    for declaration in declarations.values() {
        let root = StackAddressRoot {
            base: StackAddressBase::StackPointer,
            offset: declaration.physical_offset,
        };
        let object = *objects.stack_objects.get(&root)?;
        if objects.object(object).is_none_or(|object| {
            object.kind
                != (ObjectKind::StackSlot {
                    base: StackAddressBase::StackPointer,
                    offset: declaration.physical_offset,
                })
        }) {
            return None;
        }
        let mut accesses = memory_accesses
            .values()
            .filter(|access| access.object == object)
            .map(|access| access.id)
            .collect::<Vec<_>>();
        accesses.sort_unstable();
        slots.insert(
            declaration.physical_offset,
            CanonicalFnvFoldO0SlotFact {
                object,
                declared_offset_from_allocated_sp: declaration.declared_offset,
                offset_from_entry_sp: declaration.physical_offset,
                width: declaration.width,
                role: declaration.role,
                accesses: accesses.into_boxed_slice(),
            },
        );
    }
    Some(slots)
}

fn unique_access_memory_space(
    graph: &SsaGraph,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
) -> Option<SpaceId> {
    if memory_accesses.len() != 22 {
        return None;
    }
    let mut unique = None;
    for access in memory_accesses.values() {
        let (block_addr, op_index) = graph.op_site_for_inst(access.id.inst)?;
        let observed = machine.memory_space_at(block_addr, op_index)?;
        if unique.is_some_and(|space| space != observed) {
            return None;
        }
        unique = Some(observed);
    }
    let space = unique?;
    let model = machine.memory_model().space(space)?;
    (space == SpaceId::Ram
        && model.address_bits() == 64
        && model.word_size_bytes() == 1
        && model.endianness() == MachineMemoryEndianness::Little)
        .then_some(space)
}

fn unique_buffer_object(
    objects: &ObjectModel,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    pointer_parameter_index: u32,
) -> Option<ObjectId> {
    let frame_objects = slots
        .values()
        .map(|slot| slot.object)
        .collect::<BTreeSet<_>>();
    let external = memory_accesses
        .values()
        .filter(|access| !frame_objects.contains(&access.object))
        .collect::<Vec<_>>();
    let [access] = external.as_slice() else {
        return None;
    };
    (!access.is_write
        && access.width == 1
        && access.provenance_complete
        && objects
            .parameter_objects
            .get(&(pointer_parameter_index as usize))
            == Some(&access.object)
        && objects.object(access.object).map(|object| &object.kind)
            == Some(&ObjectKind::Parameter {
                index: pointer_parameter_index as usize,
            }))
    .then_some(access.object)
}

#[allow(clippy::too_many_arguments)]
fn collect_access_inventory(
    graph: &SsaGraph,
    memory: &MemorySSAFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine: &SourceMachineContext,
    memory_space: SpaceId,
    topology: &CanonicalFnvFoldO0TopologyFact,
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    buffer: ObjectId,
) -> Option<Vec<CanonicalFnvFoldO0AccessFact>> {
    if memory_accesses.len() != 22 || machine.memory_spaces_by_op().len() != 22 {
        return None;
    }
    let allowed_objects = slots
        .values()
        .map(|slot| slot.object)
        .chain(std::iter::once(buffer))
        .collect::<BTreeSet<_>>();
    let mut inventory = Vec::with_capacity(22);
    for access in memory_accesses.values() {
        if (!access.provenance_complete && access.object != buffer)
            || !allowed_objects.contains(&access.object)
            || access.id.ordinal != 0
        {
            return None;
        }
        let (block_addr, op_index) = graph.op_site_for_inst(access.id.inst)?;
        let space = machine.memory_space_at(block_addr, op_index)?;
        if space != memory_space {
            return None;
        }
        let value = access.value?;
        let uses = memory
            .uses_by_inst
            .get(&access.id.inst)
            .cloned()
            .unwrap_or_default();
        let defs = memory
            .defs_by_inst
            .get(&access.id.inst)
            .cloned()
            .unwrap_or_default();
        let buffer_read = access.object == buffer;
        let memory_ssa_matches = if buffer_read {
            !access.is_write
                && defs.is_empty()
                && matches!(uses.as_slice(), [use_fact]
                if use_fact.location.object == buffer
                    && use_fact.location.size == 1
                    && !matches!(use_fact.location.address, RelativeMemoryAddress::Unknown)
                    && use_fact.version == (MemoryVersion {
                        object: buffer,
                        version: 0,
                    }))
        } else {
            (access.is_write && defs.len() == 1 && uses.is_empty()
                || !access.is_write && uses.len() == 1 && defs.is_empty())
                && uses.iter().all(|use_fact| {
                    use_fact.location.object == access.object
                        && use_fact.location.size == access.width
                })
                && defs.iter().all(|def| {
                    def.location.object == access.object && def.location.size == access.width
                })
        };
        if !memory_ssa_matches {
            return None;
        }
        let expected_width = slots
            .values()
            .find(|slot| slot.object == access.object)
            .map_or(1, |slot| slot.width);
        if access.width != expected_width
            || (access.object != buffer
                && uses
                    .iter()
                    .map(|use_fact| &use_fact.location.address)
                    .chain(defs.iter().map(|def| &def.location.address))
                    .any(|address| *address != RelativeMemoryAddress::Exact(0)))
        {
            return None;
        }
        inventory.push(CanonicalFnvFoldO0AccessFact {
            access: access.id,
            object: access.object,
            address: access.address,
            value,
            is_write: access.is_write,
            width: access.width,
            memory_space: space,
            memory_uses: uses.into_boxed_slice(),
            memory_defs: defs.into_boxed_slice(),
        });
    }
    let ranks = topology_rank(topology);
    if ranks.len() != 11 {
        return None;
    }
    let mut ranked = Vec::with_capacity(inventory.len());
    for access in inventory {
        let (block, op_index) = graph.op_site_for_inst(access.access.inst)?;
        let rank = ranks.get(&block).copied()?;
        ranked.push(((rank, op_index, access.access.ordinal), access));
    }
    ranked.sort_by_key(|(rank, _)| *rank);
    Some(ranked.into_iter().map(|(_, access)| access).collect())
}

fn collect_frame(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    abi: &CanonicalFnvFoldO0AbiFact,
    declarations: &BTreeMap<i64, SlotDeclaration>,
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    topology: &CanonicalFnvFoldO0TopologyFact,
    accesses: &[CanonicalFnvFoldO0AccessFact],
) -> Option<CanonicalFnvFoldO0FrameFact> {
    let stack_storage = declarations.values().next()?.base_storage;
    let writes = register_writes(graph, machine, stack_storage);
    if writes.len() != 2 {
        return None;
    }
    let allocate_inst = unique_stack_write(graph, &writes, topology.entry, false, FRAME_SIZE)?;
    let restore_inst = unique_stack_write(graph, &writes, topology.exit, true, FRAME_SIZE)?;
    if allocate_inst == restore_inst
        || writes.iter().copied().collect::<BTreeSet<_>>()
            != BTreeSet::from([allocate_inst, restore_inst])
    {
        return None;
    }
    let allocate = graph.inst(allocate_inst)?;
    let restore = graph.inst(restore_inst)?;
    let (entry_sp, allocated_sp, allocate_arithmetic_inst, allocate_support_insts) =
        exact_stack_delta(graph, allocate, false, FRAME_SIZE)?;
    let (restore_input, restored_sp, restore_arithmetic_inst, restore_support_insts) =
        exact_stack_delta(graph, restore, true, FRAME_SIZE)?;
    if allocated_sp != restore_input
        || !is_entry_value(graph, entry_sp)
        || graph.op_site_for_inst(allocate_inst)?.0 != topology.entry
        || graph.op_site_for_inst(restore_inst)?.0 != topology.exit
        || graph.value(restored_sp)?.var.size != 8
    {
        return None;
    }
    let returns = function
        .blocks()
        .flat_map(|block| {
            block
                .ops
                .iter()
                .enumerate()
                .filter_map(move |(op_index, op)| {
                    matches!(op, SSAOp::Return { .. }).then_some((block.addr, op_index))
                })
        })
        .collect::<Vec<_>>();
    let [(return_block, return_op_index)] = returns.as_slice() else {
        return None;
    };
    let return_inst = graph.inst_id_for_op_site(*return_block, *return_op_index)?;
    let return_def = graph.inst(return_inst)?;
    let [return_target] = return_def.inputs.as_slice() else {
        return None;
    };
    let (return_address, return_target_support_insts) =
        copy_root_with_insts(graph, *return_target)?;
    let link_register_storage = value_storage(graph, machine, return_address)?;
    let expected_link_register_storage = machine.function_interface()?.return_address_storage()?;
    if *return_block != topology.exit
        || link_register_storage.space != CanonicalStorageSpace::Register
        || link_register_storage.size != 8
        || link_register_storage != expected_link_register_storage
        || link_register_storage == stack_storage
        || link_register_storage == abi.return_storage
        || link_register_storage == abi.length_parameter.storage
        || !is_entry_value(graph, return_address)
        || !register_writes(graph, machine, link_register_storage).is_empty()
        || !same_block_op_order(graph, restore_inst, return_inst)
    {
        return None;
    }
    let homes = slots
        .values()
        .filter(|slot| matches!(slot.role, SourceStackSlotRole::ParameterHome { .. }))
        .cloned()
        .collect::<Vec<_>>();
    let locals = slots
        .values()
        .filter(|slot| slot.role == SourceStackSlotRole::Local)
        .cloned()
        .collect::<Vec<_>>();
    if homes.len() != 2 || locals.len() != 3 || slots_overlap(slots) {
        return None;
    }
    let address_support_insts = stack_access_address_support(graph, accesses, slots, allocated_sp)?;
    Some(CanonicalFnvFoldO0FrameFact {
        stack_storage,
        link_register_storage,
        entry_sp,
        allocated_sp,
        allocate_inst,
        allocate_arithmetic_inst,
        allocate_support_insts: allocate_support_insts.into_boxed_slice(),
        restored_sp,
        restore_inst,
        restore_arithmetic_inst,
        restore_support_insts: restore_support_insts.into_boxed_slice(),
        address_support_insts: address_support_insts.into_boxed_slice(),
        return_address,
        return_target: *return_target,
        return_target_support_insts: return_target_support_insts.into_boxed_slice(),
        return_inst,
        homes: homes.into_boxed_slice(),
        locals: locals.into_boxed_slice(),
    })
}

fn stack_access_address_support(
    graph: &SsaGraph,
    inventory: &[CanonicalFnvFoldO0AccessFact],
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    allocated_sp: ValueId,
) -> Option<Vec<InstId>> {
    let mut support = BTreeSet::new();
    for slot in slots.values() {
        for access in inventory
            .iter()
            .filter(|access| access.object == slot.object)
        {
            support.extend(address_base_plus_support(
                graph,
                access.address,
                allocated_sp,
                u64::try_from(slot.declared_offset_from_allocated_sp).ok()?,
            )?);
        }
    }
    Some(support.into_iter().collect())
}

fn address_base_plus_support(
    graph: &SsaGraph,
    address: ValueId,
    base: ValueId,
    offset: u64,
) -> Option<Vec<InstId>> {
    let (root, mut support) = copy_root_with_insts(graph, address)?;
    let (base_root, base_support) = copy_root_with_insts(graph, base)?;
    let Some(inst) = graph.def_inst(root).and_then(|inst| graph.inst(inst)) else {
        if offset != 0 || root != base_root {
            return None;
        }
        support.extend(base_support);
        support.sort_unstable();
        support.dedup();
        return Some(support);
    };
    let [left, right] = inst.inputs.as_slice() else {
        return None;
    };
    if !matches!(&inst.payload, InstPayload::Op(SSAOp::IntAdd { .. }))
        || value_width(graph, root) != Some(64)
    {
        return None;
    }
    let (left_root, left_support) = copy_root_with_insts(graph, *left)?;
    let (right_root, right_support) = copy_root_with_insts(graph, *right)?;
    let (constant, selected_base_support) = match (left_root == base_root, right_root == base_root)
    {
        (true, false) => (*right, left_support),
        (false, true) => (*left, right_support),
        _ => return None,
    };
    let (actual_offset, constant_support) = evaluate_exact_constant(graph, constant, 64)?;
    if actual_offset != offset {
        return None;
    }
    support.push(inst.id);
    support.extend(base_support);
    support.extend(selected_base_support);
    support.extend(constant_support);
    support.sort_unstable();
    support.dedup();
    Some(support)
}

fn collect_index(
    graph: &SsaGraph,
    memory: &MemorySSAFacts,
    topology: &CanonicalFnvFoldO0TopologyFact,
    accesses: &[&CanonicalFnvFoldO0AccessFact],
    buffer_accesses: &[&CanonicalFnvFoldO0AccessFact],
    buffer_object: ObjectId,
) -> Option<CanonicalFnvFoldO0IndexFact> {
    let [
        initializer,
        header_load,
        address_load,
        latch_load,
        update_store,
    ] = accesses
    else {
        return None;
    };
    let [buffer_load] = buffer_accesses else {
        return None;
    };
    let (initializer_value, initializer_support_insts) =
        evaluate_exact_constant(graph, initializer.value, 64)?;
    if !initializer.is_write
        || header_load.is_write
        || address_load.is_write
        || latch_load.is_write
        || !update_store.is_write
        || buffer_load.is_write
        || initializer_value != 0
        || store_def(initializer)?.previous_version.version != 0
        || graph.op_site_for_inst(initializer.access.inst)?.0 != topology.entry
        || graph.op_site_for_inst(header_load.access.inst)?.0 != topology.header
        || graph.op_site_for_inst(address_load.access.inst)?.0 != topology.first_predicate_block
        || graph.op_site_for_inst(latch_load.access.inst)?.0 != topology.latch
        || graph.op_site_for_inst(update_store.access.inst)?.0 != topology.latch
        || graph.op_site_for_inst(buffer_load.access.inst)?.0 != topology.first_predicate_block
    {
        return None;
    }
    let initializer_version = store_version(initializer)?;
    let update_version = store_version(update_store)?;
    let phi = unique_phi(
        memory,
        topology.header,
        initializer.object,
        initializer.width,
        &[
            (topology.entry, initializer_version),
            (topology.latch, update_version),
        ],
    )?;
    if [header_load, address_load, latch_load]
        .iter()
        .any(|access| load_version(access) != Some(phi.output_version))
        || store_def(update_store)?.previous_version != phi.output_version
    {
        return None;
    }
    let (update, update_inst, update_support_insts) =
        exact_add_constant(graph, update_store.value, latch_load.value, 64, 1)?;
    let expression = graph
        .value(buffer_load.address)
        .map(|_| buffer_load.address)?;
    if buffer_load.object != buffer_object || buffer_load.width != 1 {
        return None;
    }
    Some(CanonicalFnvFoldO0IndexFact {
        object: initializer.object,
        initializer_store: initializer.access,
        initializer_support_insts: initializer_support_insts.into_boxed_slice(),
        initializer_version,
        phi,
        header_load: header_load.access,
        address_load: address_load.access,
        latch_load: latch_load.access,
        update,
        update_inst,
        update_support_insts: update_support_insts.into_boxed_slice(),
        update_store: update_store.access,
        update_version,
        buffer_address: expression,
        buffer_access: buffer_load.access,
        buffer_object,
        raw_byte: buffer_load.value,
    })
}

fn collect_parameter_home_relay(
    memory: &MemorySSAFacts,
    topology: &CanonicalFnvFoldO0TopologyFact,
    parameter_index: u32,
    initializer_store: &CanonicalFnvFoldO0AccessFact,
    reload: &CanonicalFnvFoldO0AccessFact,
) -> Option<CanonicalFnvFoldO0ParameterHomeRelayFact> {
    if !initializer_store.is_write
        || reload.is_write
        || initializer_store.object != reload.object
        || initializer_store.width != 8
        || reload.width != 8
        || store_def(initializer_store)?.previous_version.version != 0
        || memory
            .defs_by_inst
            .get(&initializer_store.access.inst)
            .map(Vec::as_slice)
            != Some(initializer_store.memory_defs.as_ref())
        || memory
            .uses_by_inst
            .get(&reload.access.inst)
            .map(Vec::as_slice)
            != Some(reload.memory_uses.as_ref())
    {
        return None;
    }
    let initializer_version = store_version(initializer_store)?;
    let mut candidates = memory
        .phis_by_block
        .get(&topology.header)?
        .iter()
        .filter(|phi| {
            phi.object == initializer_store.object
                && phi.output_version.object == initializer_store.object
                && phi.location
                    == (MemoryLocation {
                        object: initializer_store.object,
                        address: RelativeMemoryAddress::Exact(0),
                        size: 8,
                    })
                && phi.inputs.len() == 2
                && phi.inputs.iter().copied().collect::<BTreeSet<_>>()
                    == BTreeSet::from([
                        (topology.entry, initializer_version),
                        (topology.latch, phi.output_version),
                    ])
        });
    let phi = candidates.next()?.clone();
    if candidates.next().is_some()
        || load_version(reload)? != phi.output_version
        || memory
            .defs_by_inst
            .values()
            .flatten()
            .filter(|def| def.location.object == initializer_store.object)
            .count()
            != 1
    {
        return None;
    }
    Some(CanonicalFnvFoldO0ParameterHomeRelayFact {
        parameter_index,
        initializer_store: initializer_store.access,
        initializer_version,
        phi,
        reload: reload.access,
        value: reload.value,
    })
}

fn collect_external_read_policy(
    graph: &SsaGraph,
    abi: &CanonicalFnvFoldO0AbiFact,
    allocated_sp: ValueId,
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    pointer_home: &CanonicalFnvFoldO0ParameterHomeRelayFact,
    index_load: &CanonicalFnvFoldO0AccessFact,
    external_read: &CanonicalFnvFoldO0AccessFact,
) -> Option<CanonicalFnvFoldO0ExternalReadAliasPolicyFact> {
    let (_address_root, address_inst, address_support_insts) = exact_add_values(
        graph,
        external_read.address,
        pointer_home.value,
        index_load.value,
        64,
    )?;
    let classified_frame_objects = slots
        .values()
        .map(|slot| slot.object)
        .collect::<BTreeSet<_>>();
    let [external_memory_use] = external_read.memory_uses.as_ref() else {
        return None;
    };
    if abi.pointer_parameter.index != 0
        || pointer_home.parameter_index != abi.pointer_parameter.index
        || external_read.is_write
        || external_read.width != 1
        || !external_read.memory_defs.is_empty()
        || external_memory_use.location.object != external_read.object
        || external_memory_use.location.size != 1
        || matches!(
            external_memory_use.location.address,
            RelativeMemoryAddress::Unknown
        )
        || external_memory_use.version
            != (MemoryVersion {
                object: external_read.object,
                version: 0,
            })
        || classified_frame_objects.contains(&external_read.object)
        || !frame_address_escape_free(graph, allocated_sp)
    {
        return None;
    }
    Some(CanonicalFnvFoldO0ExternalReadAliasPolicyFact {
        complete_frame_separation: true,
        frame_address_escape_free: true,
        source_external_byte_pointer: true,
        external_object: external_read.object,
        external_read: external_read.access,
        pointer_home: pointer_home.clone(),
        index_load: index_load.access,
        address: external_read.address,
        address_inst,
        address_support_insts: address_support_insts.into_boxed_slice(),
        classified_frame_objects: classified_frame_objects.into_iter().collect(),
        external_memory_use: external_memory_use.clone(),
    })
}

fn frame_address_escape_free(graph: &SsaGraph, allocated_sp: ValueId) -> bool {
    graph.insts.iter().all(|inst| {
        let escaped_value = match &inst.payload {
            InstPayload::Op(
                SSAOp::Store { val, .. }
                | SSAOp::StoreGuarded { val, .. }
                | SSAOp::StoreConditional { val, .. },
            ) => graph.value_id_for_var(val),
            InstPayload::Op(SSAOp::AtomicCAS { replacement, .. }) => {
                graph.value_id_for_var(replacement)
            }
            InstPayload::Op(SSAOp::Return { target }) => graph.value_id_for_var(target),
            _ => None,
        };
        escaped_value.is_none_or(|value| !value_depends_on(graph, value, allocated_sp))
    })
}

fn value_depends_on(graph: &SsaGraph, value: ValueId, source: ValueId) -> bool {
    fn visit(
        graph: &SsaGraph,
        value: ValueId,
        source: ValueId,
        visited: &mut BTreeSet<ValueId>,
    ) -> bool {
        if same_value(graph, value, source) {
            return true;
        }
        if !visited.insert(value) {
            return false;
        }
        let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
            return false;
        };
        if matches!(&inst.payload, InstPayload::Op(SSAOp::Load { .. })) {
            return false;
        }
        inst.inputs
            .iter()
            .any(|input| visit(graph, *input, source, visited))
    }
    visit(graph, value, source, &mut BTreeSet::new())
}

fn collect_ascii(
    graph: &SsaGraph,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    topology: &CanonicalFnvFoldO0TopologyFact,
    accesses: &[&CanonicalFnvFoldO0AccessFact],
    raw_byte: ValueId,
) -> Option<CanonicalFnvFoldO0AsciiFact> {
    let [
        initial_store,
        first_load,
        second_load,
        lowercase_load,
        lowercase_store,
        merge_load,
    ] = accesses
    else {
        return None;
    };
    if !initial_store.is_write
        || first_load.is_write
        || second_load.is_write
        || lowercase_load.is_write
        || !lowercase_store.is_write
        || merge_load.is_write
        || graph.op_site_for_inst(initial_store.access.inst)?.0 != topology.first_predicate_block
        || graph.op_site_for_inst(first_load.access.inst)?.0 != topology.first_predicate_block
        || graph.op_site_for_inst(second_load.access.inst)?.0 != topology.second_predicate_block
        || graph.op_site_for_inst(lowercase_load.access.inst)?.0 != topology.lowercase_block
        || graph.op_site_for_inst(lowercase_store.access.inst)?.0 != topology.lowercase_block
        || graph.op_site_for_inst(merge_load.access.inst)?.0 != topology.hash_block
        || !low_byte_is_from(graph, initial_store.value, raw_byte)
    {
        return None;
    }
    let initial_version = store_version(initial_store)?;
    if [first_load, second_load, lowercase_load]
        .iter()
        .any(|access| load_version(access) != Some(initial_version))
        || store_def(lowercase_store)?.previous_version != initial_version
    {
        return None;
    }
    let first_predicate = collect_predicate(
        graph,
        predicates,
        topology.first_predicate_block,
        CompareKind::SignedLess,
        first_load.value,
        constant_value(graph, 32, 0x41)?,
        [topology.hash_block, topology.second_forwarder],
    )?;
    let second_predicate = collect_predicate(
        graph,
        predicates,
        topology.second_predicate_block,
        CompareKind::SignedLess,
        constant_value(graph, 32, 0x5a)?,
        second_load.value,
        [topology.hash_block, topology.lowercase_forwarder],
    )?;
    let (lowercase, lowercase_inst, lowercase_support_insts) =
        exact_add_constant_low_byte(graph, lowercase_store.value, lowercase_load.value, 0x20)?;
    let lowercase_version = store_version(lowercase_store)?;
    let merge_phi = unique_phi(
        memory,
        topology.hash_block,
        initial_store.object,
        1,
        &[
            (topology.first_predicate_block, initial_version),
            (topology.second_predicate_block, initial_version),
            (topology.lowercase_block, lowercase_version),
        ],
    )?;
    if load_version(merge_load)? != merge_phi.output_version {
        return None;
    }
    Some(CanonicalFnvFoldO0AsciiFact {
        object: initial_store.object,
        initial_store: initial_store.access,
        initial_version,
        first_load: first_load.access,
        first_predicate,
        second_load: second_load.access,
        second_predicate,
        lowercase_load: lowercase_load.access,
        lowercase,
        lowercase_inst,
        lowercase_support_insts: lowercase_support_insts.into_boxed_slice(),
        lowercase_store: lowercase_store.access,
        lowercase_version,
        merge_phi,
        merge_load: merge_load.access,
        selected_byte: merge_load.value,
    })
}

fn collect_hash(
    graph: &SsaGraph,
    memory: &MemorySSAFacts,
    topology: &CanonicalFnvFoldO0TopologyFact,
    accesses: &[&CanonicalFnvFoldO0AccessFact],
    selected_byte: ValueId,
) -> Option<CanonicalFnvFoldO0HashFact> {
    let [
        initializer_store,
        body_load,
        xor_store,
        xor_reload,
        product_store,
        exit_load,
    ] = accesses
    else {
        return None;
    };
    if !initializer_store.is_write
        || body_load.is_write
        || !xor_store.is_write
        || xor_reload.is_write
        || !product_store.is_write
        || exit_load.is_write
        || graph.op_site_for_inst(initializer_store.access.inst)?.0 != topology.entry
        || graph.op_site_for_inst(body_load.access.inst)?.0 != topology.hash_block
        || graph.op_site_for_inst(xor_store.access.inst)?.0 != topology.hash_block
        || graph.op_site_for_inst(xor_reload.access.inst)?.0 != topology.hash_block
        || graph.op_site_for_inst(product_store.access.inst)?.0 != topology.hash_block
        || graph.op_site_for_inst(exit_load.access.inst)?.0 != topology.exit
        || store_def(initializer_store)?.previous_version.version != 0
    {
        return None;
    }
    let (offset_basis, initializer_witness) =
        evaluate_exact_constant(graph, initializer_store.value, 64)?;
    if offset_basis != OFFSET_BASIS {
        return None;
    }
    let initializer_version = store_version(initializer_store)?;
    let product_version = store_version(product_store)?;
    let phi = unique_phi(
        memory,
        topology.header,
        initializer_store.object,
        8,
        &[
            (topology.entry, initializer_version),
            (topology.latch, product_version),
        ],
    )?;
    if load_version(body_load)? != phi.output_version
        || load_version(exit_load)? != phi.output_version
        || store_def(xor_store)?.previous_version != phi.output_version
    {
        return None;
    }
    let selected64 = zero_extend_to(graph, selected_byte, 64)?;
    let selected64_inst = graph.def_inst(selected64)?;
    let (xor, xor_inst) = exact_commutative_binary(
        graph,
        xor_store.value,
        body_load.value,
        selected64,
        64,
        |op| matches!(op, SSAOp::IntXor { .. }),
    )?;
    let xor_version = store_version(xor_store)?;
    if load_version(xor_reload)? != xor_version
        || store_def(product_store)?.previous_version != xor_version
    {
        return None;
    }
    let (product_root, _) = copy_root_with_insts(graph, product_store.value)?;
    let product_def = graph.inst(graph.def_inst(product_root)?)?;
    let InstPayload::Op(SSAOp::IntMult { .. }) = &product_def.payload else {
        return None;
    };
    let [left, right] = product_def.inputs.as_slice() else {
        return None;
    };
    let (prime, prime_witness) = if same_value(graph, *left, xor_reload.value) {
        (*right, evaluate_exact_constant(graph, *right, 64)?)
    } else if same_value(graph, *right, xor_reload.value) {
        (*left, evaluate_exact_constant(graph, *left, 64)?)
    } else {
        return None;
    };
    if prime_witness.0 != FNV_PRIME || value_width(graph, product_root) != Some(64) {
        return None;
    }
    Some(CanonicalFnvFoldO0HashFact {
        object: initializer_store.object,
        offset_basis,
        initializer: initializer_store.value,
        initializer_witness_insts: initializer_witness.into_boxed_slice(),
        initializer_store: initializer_store.access,
        initializer_version,
        phi,
        body_load: body_load.access,
        selected64,
        selected64_inst,
        xor,
        xor_inst,
        xor_store: xor_store.access,
        xor_version,
        xor_reload: xor_reload.access,
        prime,
        prime_value: prime_witness.0,
        prime_witness_insts: prime_witness.1.into_boxed_slice(),
        product: product_root,
        multiply_inst: product_def.id,
        product_store: product_store.access,
        product_version,
        exit_load: exit_load.access,
    })
}

fn collect_return(
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
    abi: &CanonicalFnvFoldO0AbiFact,
    frame: &CanonicalFnvFoldO0FrameFact,
    hash: &CanonicalFnvFoldO0HashFact,
    exit_load: &CanonicalFnvFoldO0AccessFact,
    machine: &SourceMachineContext,
) -> Option<CanonicalFnvFoldO0ReturnFact> {
    let boundary = boundaries.returns.get(&frame.return_inst)?;
    let [returned] = boundary.values.as_slice() else {
        return None;
    };
    if !boundary.complete
        || returned.slot
            != (CallBoundarySlot::Register {
                index: 0,
                storage: abi.return_storage,
            })
        || returned.value != exit_load.value
        || load_version(exit_load)? != hash.phi.output_version
        || value_storage(graph, machine, returned.value) != Some(abi.return_storage)
        || !same_block_op_order(graph, exit_load.access.inst, frame.restore_inst)
    {
        return None;
    }
    Some(CanonicalFnvFoldO0ReturnFact {
        hash_access: exit_load.access,
        hash_version: hash.phi.output_version,
        value: returned.value,
        storage: abi.return_storage,
        return_inst: frame.return_inst,
        return_target: frame.return_target,
    })
}

fn collect_predicate(
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    block_addr: u64,
    kind: CompareKind,
    expected_lhs: ValueId,
    expected_rhs: ValueId,
    targets: [u64; 2],
) -> Option<CanonicalFnvFoldO0PredicateFact> {
    let [true_target, false_target] = targets;
    let mut block_predicates = predicates
        .predicates
        .values()
        .filter(|predicate| predicate.block_addr == block_addr);
    let predicate = block_predicates.next()?;
    if block_predicates.next().is_some() {
        return None;
    }
    let comparison = predicate.comparison.as_ref()?;
    if comparison.kind != kind
        || !same_value_or_extension(graph, comparison.lhs, expected_lhs)
        || !same_value_or_extension(graph, comparison.rhs, expected_rhs)
        || predicate.true_target != true_target
        || predicate.false_target != false_target
        || value_width(graph, predicate.condition) != Some(8)
    {
        return None;
    }
    let block = graph.block(graph.block_id_for_addr(block_addr)?)?;
    let branches = block
        .insts
        .iter()
        .filter_map(|inst| {
            graph
                .inst(*inst)
                .filter(|inst| matches!(&inst.payload, InstPayload::Op(SSAOp::CBranch { .. })))
                .map(|inst| inst.id)
        })
        .collect::<Vec<_>>();
    let [branch_inst] = branches.as_slice() else {
        return None;
    };
    let witness_insts = predicate_witness_insts(graph, block_addr, predicate.condition)?;
    Some(CanonicalFnvFoldO0PredicateFact {
        predicate: predicate.id,
        condition: predicate.condition,
        branch_inst: *branch_inst,
        witness_insts: witness_insts.into_boxed_slice(),
        lhs: comparison.lhs,
        rhs: comparison.rhs,
        kind,
        true_target,
        false_target,
    })
}

fn predicate_witness_insts(
    graph: &SsaGraph,
    block_addr: u64,
    condition: ValueId,
) -> Option<Vec<InstId>> {
    let mut pending = vec![condition];
    let mut visited = BTreeSet::new();
    let mut witness = BTreeSet::new();
    while let Some(value) = pending.pop() {
        if !visited.insert(value) {
            continue;
        }
        let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
            continue;
        };
        if graph.block(inst.block)?.addr != block_addr {
            continue;
        }
        let InstPayload::Op(op) = &inst.payload else {
            return None;
        };
        if matches!(op, SSAOp::Load { .. }) {
            continue;
        }
        if !matches!(
            op,
            SSAOp::Copy { .. }
                | SSAOp::IntSub { .. }
                | SSAOp::IntAnd { .. }
                | SSAOp::IntOr { .. }
                | SSAOp::IntXor { .. }
                | SSAOp::IntEqual { .. }
                | SSAOp::IntNotEqual { .. }
                | SSAOp::IntLess { .. }
                | SSAOp::IntSLess { .. }
                | SSAOp::IntLessEqual { .. }
                | SSAOp::IntSLessEqual { .. }
                | SSAOp::IntSCarry { .. }
                | SSAOp::IntSBorrow { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::IntSExt { .. }
                | SSAOp::Subpiece { offset: 0, .. }
                | SSAOp::BoolNot { .. }
                | SSAOp::BoolAnd { .. }
                | SSAOp::BoolOr { .. }
                | SSAOp::BoolXor { .. }
        ) {
            return None;
        }
        witness.insert(inst.id);
        pending.extend(inst.inputs.iter().copied());
    }
    (!witness.is_empty()).then_some(witness.into_iter().collect())
}

fn collect_non_effective_header_phis(
    memory: &MemorySSAFacts,
    topology: &CanonicalFnvFoldO0TopologyFact,
    effective: &BTreeSet<(ObjectId, MemoryVersion)>,
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    policy: &CanonicalFnvFoldO0ExternalReadAliasPolicyFact,
) -> Option<(Vec<MemoryPhiFact>, Vec<MemoryPhiFact>)> {
    if memory
        .uses_by_inst
        .get(&policy.external_read.inst)
        .map(Vec::as_slice)
        != Some(std::slice::from_ref(&policy.external_memory_use))
        || memory.defs_by_inst.contains_key(&policy.external_read.inst)
    {
        return None;
    }
    let slot_objects = slots
        .values()
        .map(|slot| slot.object)
        .collect::<BTreeSet<_>>();
    let mut unused = Vec::new();
    let mut conservative_alias_only = Vec::new();
    for (block, phis) in &memory.phis_by_block {
        for phi in phis {
            if effective.contains(&(phi.object, phi.output_version)) {
                continue;
            }
            let policy_read = policy.external_memory_use.version == phi.output_version;
            let non_policy_read = memory
                .uses_by_inst
                .iter()
                .filter(|(inst, _)| **inst != policy.external_read.inst)
                .flat_map(|(_, uses)| uses)
                .any(|use_fact| use_fact.version == phi.output_version);
            let feeds_phi = memory
                .phis_by_block
                .values()
                .flatten()
                .flat_map(|candidate| &candidate.inputs)
                .any(|(_, version)| *version == phi.output_version);
            let killed_only = memory
                .defs_by_inst
                .values()
                .flatten()
                .filter(|def| def.previous_version == phi.output_version)
                .all(|def| def.location == phi.location);
            if *block != topology.header
                || !slot_objects.contains(&phi.object)
                || phi.location.object != phi.object
                || phi.output_version.object != phi.object
                || phi.location.address != RelativeMemoryAddress::Exact(0)
                || non_policy_read
                || feeds_phi
                || !killed_only
            {
                return None;
            }
            if policy_read {
                conservative_alias_only.push(phi.clone());
            } else {
                unused.push(phi.clone());
            }
        }
    }
    Some((unused, conservative_alias_only))
}

fn function_has_only_plain_memory_and_no_calls(function: &SSAFunction) -> bool {
    function.blocks().flat_map(|block| &block.ops).all(|op| {
        !matches!(
            op,
            SSAOp::LoadLinked { .. }
                | SSAOp::StoreConditional { .. }
                | SSAOp::AtomicCAS { .. }
                | SSAOp::LoadGuarded { .. }
                | SSAOp::StoreGuarded { .. }
                | SSAOp::Fence { .. }
                | SSAOp::Call { .. }
                | SSAOp::CallInd { .. }
                | SSAOp::CallOther { .. }
                | SSAOp::CallDefine { .. }
                | SSAOp::Unimplemented
        )
    })
}

fn slot_accesses(
    inventory: &[CanonicalFnvFoldO0AccessFact],
    object: ObjectId,
    expected: usize,
) -> Option<Vec<&CanonicalFnvFoldO0AccessFact>> {
    let accesses = inventory
        .iter()
        .filter(|access| access.object == object)
        .collect::<Vec<_>>();
    (accesses.len() == expected).then_some(accesses)
}

fn slot(
    slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>,
    physical_offset: i64,
) -> Option<&CanonicalFnvFoldO0SlotFact> {
    slots.get(&physical_offset)
}

fn store_version(access: &CanonicalFnvFoldO0AccessFact) -> Option<MemoryVersion> {
    Some(store_def(access)?.next_version)
}

fn load_version(access: &CanonicalFnvFoldO0AccessFact) -> Option<MemoryVersion> {
    Some(load_use(access)?.version)
}

fn store_def(access: &CanonicalFnvFoldO0AccessFact) -> Option<&MemoryDefFact> {
    let [def] = access.memory_defs.as_ref() else {
        return None;
    };
    Some(def)
}

fn load_use(access: &CanonicalFnvFoldO0AccessFact) -> Option<&MemoryUseFact> {
    let [use_fact] = access.memory_uses.as_ref() else {
        return None;
    };
    Some(use_fact)
}

fn unique_phi(
    memory: &MemorySSAFacts,
    block: u64,
    object: ObjectId,
    width: u32,
    inputs: &[(u64, MemoryVersion)],
) -> Option<MemoryPhiFact> {
    let expected = inputs.iter().copied().collect::<BTreeSet<_>>();
    let mut candidates = memory.phis_by_block.get(&block)?.iter().filter(|phi| {
        phi.object == object
            && phi.location
                == (MemoryLocation {
                    object,
                    address: RelativeMemoryAddress::Exact(0),
                    size: width,
                })
            && phi.inputs.iter().copied().collect::<BTreeSet<_>>() == expected
    });
    let phi = candidates.next()?.clone();
    candidates.next().is_none().then_some(phi)
}

fn exact_stack_delta(
    graph: &SsaGraph,
    inst: &crate::graph::GraphInst,
    add: bool,
    delta: u64,
) -> Option<(ValueId, ValueId, InstId, Vec<InstId>)> {
    let final_output = inst.output?;
    let (arithmetic_output, mut support) = copy_root_with_insts(graph, final_output)?;
    support.retain(|support_inst| *support_inst != inst.id);
    let arithmetic = graph.inst(graph.def_inst(arithmetic_output)?)?;
    let matches = matches!(
        (&arithmetic.payload, add),
        (InstPayload::Op(SSAOp::IntAdd { .. }), true)
            | (InstPayload::Op(SSAOp::IntSub { .. }), false)
    );
    let [input, constant] = arithmetic.inputs.as_slice() else {
        return None;
    };
    if !matches {
        return None;
    }
    let (actual, constant_support) = evaluate_exact_constant(graph, *constant, 64)?;
    if actual != delta {
        return None;
    }
    support.extend(constant_support);
    support.sort_unstable();
    support.dedup();
    Some((*input, final_output, arithmetic.id, support))
}

fn exact_add_constant(
    graph: &SsaGraph,
    value: ValueId,
    input: ValueId,
    width: u32,
    constant: u64,
) -> Option<(ValueId, InstId, Vec<InstId>)> {
    let (root, mut support) = copy_root_with_insts(graph, value)?;
    let inst = graph.inst(graph.def_inst(root)?)?;
    if !matches!(&inst.payload, InstPayload::Op(SSAOp::IntAdd { .. }))
        || value_width(graph, root) != Some(width)
        || inst.inputs.len() != 2
    {
        return None;
    }
    let [left, right] = inst.inputs.as_slice() else {
        return None;
    };
    let constant_operand = if same_value_or_extension(graph, *left, input) {
        *right
    } else if same_value_or_extension(graph, *right, input) {
        *left
    } else {
        return None;
    };
    let (actual, constant_support) = evaluate_exact_constant(graph, constant_operand, width)?;
    if actual != constant {
        return None;
    }
    support.extend(constant_support);
    support.sort_unstable();
    support.dedup();
    Some((root, inst.id, support))
}

fn exact_add_values(
    graph: &SsaGraph,
    value: ValueId,
    left: ValueId,
    right: ValueId,
    width: u32,
) -> Option<(ValueId, InstId, Vec<InstId>)> {
    let (root, support) = copy_root_with_insts(graph, value)?;
    let inst = graph.inst(graph.def_inst(root)?)?;
    let [actual_left, actual_right] = inst.inputs.as_slice() else {
        return None;
    };
    (matches!(&inst.payload, InstPayload::Op(SSAOp::IntAdd { .. }))
        && value_width(graph, root) == Some(width)
        && ((same_value(graph, *actual_left, left) && same_value(graph, *actual_right, right))
            || (same_value(graph, *actual_left, right) && same_value(graph, *actual_right, left))))
    .then_some((root, inst.id, support))
}

fn exact_add_constant_low_byte(
    graph: &SsaGraph,
    stored: ValueId,
    input: ValueId,
    constant: u64,
) -> Option<(ValueId, InstId, Vec<InstId>)> {
    let mut current = stored;
    for _ in 0..8 {
        if let Some(result) = exact_add_constant(graph, current, input, 32, constant) {
            return Some(result);
        }
        let inst = graph.inst(graph.def_inst(current)?)?;
        let [source] = inst.inputs.as_slice() else {
            return None;
        };
        match &inst.payload {
            InstPayload::Op(
                SSAOp::Copy { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::Subpiece { offset: 0, .. }
                | SSAOp::Trunc { .. },
            ) => current = *source,
            _ => return None,
        }
    }
    None
}

fn exact_commutative_binary(
    graph: &SsaGraph,
    value: ValueId,
    left: ValueId,
    right: ValueId,
    width: u32,
    matches_op: impl Fn(&SSAOp) -> bool,
) -> Option<(ValueId, InstId)> {
    let (root, _) = copy_root_with_insts(graph, value)?;
    let inst = graph.inst(graph.def_inst(root)?)?;
    let InstPayload::Op(op) = &inst.payload else {
        return None;
    };
    let [a, b] = inst.inputs.as_slice() else {
        return None;
    };
    (matches_op(op)
        && value_width(graph, root) == Some(width)
        && ((same_value(graph, *a, left) && same_value(graph, *b, right))
            || (same_value(graph, *a, right) && same_value(graph, *b, left))))
    .then_some((root, inst.id))
}

fn low_byte_is_from(graph: &SsaGraph, value: ValueId, source: ValueId) -> bool {
    if same_value(graph, value, source) && value_width(graph, value) == Some(8) {
        return true;
    }
    let mut current = value;
    for _ in 0..8 {
        if current == source {
            return true;
        }
        let Some(inst) = graph.def_inst(current).and_then(|inst| graph.inst(inst)) else {
            return false;
        };
        let [input] = inst.inputs.as_slice() else {
            return false;
        };
        match &inst.payload {
            InstPayload::Op(
                SSAOp::Copy { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::Subpiece { offset: 0, .. }
                | SSAOp::Trunc { .. },
            ) => current = *input,
            _ => return false,
        }
    }
    false
}

fn zero_extend_to(graph: &SsaGraph, source: ValueId, width: u32) -> Option<ValueId> {
    graph.values.iter().find_map(|value| {
        (value_width(graph, value.id) == Some(width)
            && zero_extension_root(graph, value.id) == Some(source))
        .then_some(value.id)
    })
}

fn zero_extension_root(graph: &SsaGraph, value: ValueId) -> Option<ValueId> {
    let mut current = value;
    let mut saw_extension = false;
    let mut retained_width = value_width(graph, value)?;
    for _ in 0..8 {
        let Some(inst) = graph.def_inst(current).and_then(|inst| graph.inst(inst)) else {
            return saw_extension.then_some(current);
        };
        let [source] = inst.inputs.as_slice() else {
            return None;
        };
        match &inst.payload {
            InstPayload::Op(SSAOp::Copy { .. }) => current = *source,
            InstPayload::Op(SSAOp::IntZExt { .. }) => {
                if value_width(graph, *source)? > retained_width {
                    return None;
                }
                saw_extension = true;
                current = *source;
            }
            InstPayload::Op(SSAOp::Subpiece { offset: 0, .. } | SSAOp::Trunc { .. }) => {
                retained_width = retained_width.min(value_width(graph, current)?);
                current = *source;
            }
            _ => return saw_extension.then_some(current),
        }
    }
    None
}

fn same_value_or_extension(graph: &SsaGraph, actual: ValueId, expected: ValueId) -> bool {
    same_value(graph, actual, expected)
        || zero_extension_root(graph, actual).is_some_and(|root| same_value(graph, root, expected))
        || zero_extension_root(graph, expected).is_some_and(|root| same_value(graph, actual, root))
}

fn same_value(graph: &SsaGraph, left: ValueId, right: ValueId) -> bool {
    copy_root(graph, left)
        .zip(copy_root(graph, right))
        .is_some_and(|(left, right)| {
            left == right
                || graph
                    .value(left)
                    .zip(graph.value(right))
                    .is_some_and(|(left, right)| {
                        left.var.size == right.var.size
                            && left.var.constant_bits().is_some()
                            && left.var.constant_bits() == right.var.constant_bits()
                    })
        })
}

fn copy_root(graph: &SsaGraph, value: ValueId) -> Option<ValueId> {
    copy_root_with_insts(graph, value).map(|(root, _)| root)
}

fn copy_root_with_insts(graph: &SsaGraph, value: ValueId) -> Option<(ValueId, Vec<InstId>)> {
    let mut current = value;
    let mut insts = Vec::new();
    let mut visited = BTreeSet::new();
    while visited.insert(current) {
        let Some(inst) = graph.def_inst(current).and_then(|inst| graph.inst(inst)) else {
            return Some((current, insts));
        };
        if !matches!(&inst.payload, InstPayload::Op(SSAOp::Copy { .. })) {
            return Some((current, insts));
        }
        let [source] = inst.inputs.as_slice() else {
            return None;
        };
        if value_width(graph, current) != value_width(graph, *source) {
            return None;
        }
        insts.push(inst.id);
        current = *source;
    }
    None
}

fn evaluate_exact_constant(
    graph: &SsaGraph,
    value: ValueId,
    width: u32,
) -> Option<(u64, Vec<InstId>)> {
    fn evaluate(
        graph: &SsaGraph,
        value: ValueId,
        width: u32,
        visiting: &mut BTreeSet<ValueId>,
    ) -> Option<(u64, BTreeSet<InstId>)> {
        if value_width(graph, value)? != width {
            return None;
        }
        if let Some(bits) = graph.value(value)?.var.constant_bits() {
            return Some((mask_to_width(bits, width)?, BTreeSet::new()));
        }
        if !visiting.insert(value) {
            return None;
        }
        let inst = graph.inst(graph.def_inst(value)?)?;
        let evaluated = match &inst.payload {
            InstPayload::Op(SSAOp::Copy { .. }) => {
                let [source] = inst.inputs.as_slice() else {
                    return None;
                };
                evaluate(graph, *source, width, visiting)
            }
            InstPayload::Op(SSAOp::IntAnd { .. } | SSAOp::IntOr { .. }) => {
                let [left, right] = inst.inputs.as_slice() else {
                    return None;
                };
                let (left_value, mut left_witness) = evaluate(graph, *left, width, visiting)?;
                let (right_value, right_witness) = evaluate(graph, *right, width, visiting)?;
                left_witness.extend(right_witness);
                let value = if matches!(&inst.payload, InstPayload::Op(SSAOp::IntAnd { .. })) {
                    left_value & right_value
                } else {
                    left_value | right_value
                };
                Some((mask_to_width(value, width)?, left_witness))
            }
            _ => None,
        };
        visiting.remove(&value);
        let (value, mut witness) = evaluated?;
        witness.insert(inst.id);
        Some((value, witness))
    }
    let (value, witness) = evaluate(graph, value, width, &mut BTreeSet::new())?;
    Some((value, witness.into_iter().collect()))
}

fn value_width(graph: &SsaGraph, value: ValueId) -> Option<u32> {
    graph.value(value)?.var.size.checked_mul(8)
}

fn constant_is(graph: &SsaGraph, value: ValueId, width: u32, expected: u64) -> bool {
    value_width(graph, value) == Some(width)
        && graph
            .value(value)
            .and_then(|value| value.var.constant_bits())
            .and_then(|value| mask_to_width(value, width))
            == Some(expected)
}

fn constant_value(graph: &SsaGraph, width: u32, expected: u64) -> Option<ValueId> {
    graph
        .values
        .iter()
        .find(|value| constant_is(graph, value.id, width, expected))
        .map(|value| value.id)
}

fn mask_to_width(value: u64, width: u32) -> Option<u64> {
    match width {
        1..=63 => Some(value & ((1u64 << width) - 1)),
        64 => Some(value),
        _ => None,
    }
}

fn value_storage(
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    value: ValueId,
) -> Option<CanonicalStorageId> {
    let value = graph.value(value)?;
    let storage = value.canonical_storage?;
    (value.var.size == storage.size).then_some(storage)
}

fn register_writes(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    storage: CanonicalStorageId,
) -> Vec<InstId> {
    graph
        .insts
        .iter()
        .filter(|inst| {
            inst.output
                .is_some_and(|value| value_storage(graph, machine, value) == Some(storage))
        })
        .map(|inst| inst.id)
        .collect()
}

fn is_entry_value(graph: &SsaGraph, value: ValueId) -> bool {
    graph
        .value(value)
        .is_some_and(|value| value.var.version == 0)
        && graph.def_inst(value).is_none()
}

fn same_block_op_order(graph: &SsaGraph, left: InstId, right: InstId) -> bool {
    match (graph.op_site_for_inst(left), graph.op_site_for_inst(right)) {
        (Some((left_block, left_op)), Some((right_block, right_op))) => {
            left_block == right_block && left_op < right_op
        }
        _ => false,
    }
}

fn unique_stack_write(
    graph: &SsaGraph,
    writes: &[InstId],
    block: u64,
    add: bool,
    delta: u64,
) -> Option<InstId> {
    let mut candidates = writes.iter().copied().filter(|inst_id| {
        graph.op_site_for_inst(*inst_id).map(|site| site.0) == Some(block)
            && graph
                .inst(*inst_id)
                .is_some_and(|inst| exact_stack_delta(graph, inst, add, delta).is_some())
    });
    let candidate = candidates.next()?;
    candidates.next().is_none().then_some(candidate)
}

fn slots_overlap(slots: &BTreeMap<i64, CanonicalFnvFoldO0SlotFact>) -> bool {
    let slots = slots.values().collect::<Vec<_>>();
    slots.iter().enumerate().any(|(index, left)| {
        slots[index.saturating_add(1)..].iter().any(|right| {
            let left_end = left.offset_from_entry_sp + i64::from(left.width);
            let right_end = right.offset_from_entry_sp + i64::from(right.width);
            left.offset_from_entry_sp < right_end && right.offset_from_entry_sp < left_end
        })
    })
}

fn sole_successor(function: &SSAFunction, block: u64) -> Option<u64> {
    let successors = function.successors(block);
    let [successor] = successors.as_slice() else {
        return None;
    };
    Some(*successor)
}

fn two_successors(function: &SSAFunction, block: u64) -> Option<[u64; 2]> {
    let successors = function.successors(block);
    let [first, second] = successors.as_slice() else {
        return None;
    };
    Some([*first, *second])
}

fn other_successor(function: &SSAFunction, block: u64, excluded: u64) -> Option<u64> {
    let [first, second] = two_successors(function, block)?;
    match (first == excluded, second == excluded) {
        (true, false) => Some(second),
        (false, true) => Some(first),
        _ => None,
    }
}

fn unique_topology_tail(
    function: &SSAFunction,
    first_predicate_block: u64,
    latch: u64,
) -> Option<(u64, u64, u64, u64, u64)> {
    let [first, second] = two_successors(function, first_predicate_block)?;
    let mut candidates = BTreeSet::new();
    for (hash_block, second_forwarder) in [(first, second), (second, first)] {
        let Some(second_predicate_block) = sole_successor(function, second_forwarder) else {
            continue;
        };
        let Some(lowercase_forwarder) =
            other_successor(function, second_predicate_block, hash_block)
        else {
            continue;
        };
        let Some(lowercase_block) = sole_successor(function, lowercase_forwarder) else {
            continue;
        };
        if sole_successor(function, lowercase_block) == Some(hash_block)
            && sole_successor(function, hash_block) == Some(latch)
        {
            candidates.insert((
                second_forwarder,
                second_predicate_block,
                lowercase_forwarder,
                lowercase_block,
                hash_block,
            ));
        }
    }
    let mut candidates = candidates.into_iter();
    let candidate = candidates.next()?;
    candidates.next().is_none().then_some(candidate)
}

fn topology_rank(topology: &CanonicalFnvFoldO0TopologyFact) -> BTreeMap<u64, usize> {
    [
        topology.entry,
        topology.header,
        topology.first_forwarder,
        topology.first_predicate_block,
        topology.second_forwarder,
        topology.second_predicate_block,
        topology.lowercase_forwarder,
        topology.lowercase_block,
        topology.hash_block,
        topology.latch,
        topology.exit,
    ]
    .into_iter()
    .enumerate()
    .map(|(rank, block)| (block, rank))
    .collect()
}

fn is_branch_to(function: &SSAFunction, block: u64, target: u64) -> bool {
    matches!(
        function.cfg().get_block(block).map(|block| &block.terminator),
        Some(BlockTerminator::Branch { target: actual }) if *actual == target
    )
}

fn is_conditional(function: &SSAFunction, block: u64, true_target: u64, false_target: u64) -> bool {
    matches!(
        function.cfg().get_block(block).map(|block| &block.terminator),
        Some(BlockTerminator::ConditionalBranch {
            true_target: actual_true,
            false_target: actual_false,
        }) if *actual_true == true_target && *actual_false == false_target
    )
}

fn is_conditional_to_set(function: &SSAFunction, block: u64, targets: [u64; 2]) -> bool {
    let Some(actual) = two_successors(function, block) else {
        return false;
    };
    actual.into_iter().collect::<BTreeSet<_>>() == targets.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::{CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION, FNV_PRIME, OFFSET_BASIS};
    use crate::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind,
        SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
        SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeKind, SsaArtifact,
        StackAddressBase,
    };
    use r2il::{ArchSpec, R2ILOp, SpaceId};
    use r2sleigh_lift::{Disassembler, build_arch_spec};

    const REAL_FNV_SOURCE_SHA256: &str =
        "6524278ba4cd32a72dcf9cbcc385275999a50c3449d0e97035736891bcddff09";
    const REAL_FNV_O0_FUNCTION_SHA256: &str =
        "36af3c68ac0783e3d38125798a0644860fde98454361b46ebc72bd166b96f697";
    const REAL_FNV_O0_BINARY_SHA256: &str =
        "295868f8dab7d5d3e3304b17bce6a19f8948cca620068492f081c658146fe3bb";
    const REAL_FNV_O0_BINARY_PATH: &str = "tests/r2r/bins/r2sleigh_manual_limits_O0";
    const REAL_FNV_O0_COMPILER_COMMAND: &str = "gcc -O0 -g -fno-inline -fno-omit-frame-pointer -fno-stack-protector -no-pie -o tests/r2r/bins/r2sleigh_manual_limits_O0 tests/gold/manual_limits.c";
    const REAL_FNV_O0_BASE: u64 = 0x1_0000_075c;
    const REAL_FNV_O0_BLOCKS: &[&str] = &[
        "ffc300d1e01700f9e11300f9687080d2a873aef208f6c1f2a88ce2f2e80f00f9ff0b00f901000014",
        "e80b40f9e91340f9080109eb42040054",
        "01000014",
        "e81740f9e90b40f90801098b08014039e83f0039e83f4039080501714b010054",
        "01000014",
        "e83f403908690171cc000054",
        "01000014",
        "e83f403908810011e83f003901000014",
        "e83f4039e90308aae80f40f9080109cae80f00f9e80f40f9693680d20920c0f2087d099be80f00f901000014",
        "e80b40f908050091e80b00f9dcffff17",
        "e00f40f9ffc30091c0035fd6",
    ];

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

    fn sha256_hex(bytes: &[u8]) -> String {
        format!("{:x}", Sha256::digest(bytes))
    }

    fn real_storage(arch: &ArchSpec, register: &str) -> CanonicalStorageId {
        let register = arch
            .get_register(register)
            .expect("pinned AARCH64 register");
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: register.offset,
            size: register.size,
        }
    }

    fn real_interface(arch: &ArchSpec) -> SourceFunctionInterface {
        let sp = real_storage(arch, "sp");
        let slots = vec![
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 15, 1),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 16, 8),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 24, 8),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::StackPointer,
                sp,
                32,
                8,
                1,
                real_storage(arch, "x1"),
            ),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::StackPointer,
                sp,
                40,
                8,
                0,
                real_storage(arch, "x0"),
            ),
        ];
        let types = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
            ],
            [],
        )
        .expect("real O0 FNV type graph");
        let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
        SourceFunctionInterface::new_exact_with_logical_types(
            b"real-arm64-fnv-fold-o0-v1".to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, real_storage(arch, "x0")),
                SourceAbiParameterSpec::new(1, real_storage(arch, "x1")),
            ],
            SourceFunctionReturn::Register {
                storage: real_storage(arch, "x0"),
            },
            slots,
            [
                SourceLogicalValue::new(1, full64),
                SourceLogicalValue::new(2, full64),
            ],
            Some(SourceLogicalValue::new(2, full64)),
            Some(types),
        )
        .and_then(|interface| interface.with_return_address_storage(real_storage(arch, "x30")))
        .expect("real O0 FNV interface")
    }

    fn real_o0_artifact() -> SsaArtifact {
        let arch = build_arch_spec(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AARCH64 architecture");
        let disassembler = Disassembler::from_sla(
            sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
            sleigh_config::processor_aarch64::PSPEC_AARCH64,
            "aarch64",
        )
        .expect("AARCH64 disassembler");
        let mut address = REAL_FNV_O0_BASE;
        let blocks = REAL_FNV_O0_BLOCKS
            .iter()
            .map(|encoded| {
                let bytes = decode_hex(encoded);
                let block = disassembler
                    .lift_block(&bytes, address, bytes.len())
                    .expect("pinned real ARM64 O0 FNV block");
                address += bytes.len() as u64;
                block
            })
            .collect::<Vec<_>>();
        let spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(!spaces.is_empty(), "real FNV lift must access memory");
        assert!(
            spaces.iter().all(|space| *space == SpaceId::Ram),
            "real ARM64 FNV accesses must use the architectural Ram space: {spaces:?}"
        );
        let interface = real_interface(&arch);
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .expect("prepared real ARM64 O0 FNV artifact")
    }

    #[test]
    fn real_arm64_apple_silicon_o0_lift_collects_exact_fnv_fact() {
        let provenance = format!(
            "binary={REAL_FNV_O0_BINARY_PATH} binary_sha256={REAL_FNV_O0_BINARY_SHA256} command={REAL_FNV_O0_COMPILER_COMMAND}"
        );
        assert_eq!(
            sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
            REAL_FNV_SOURCE_SHA256,
            "source provenance changed: {provenance}"
        );
        let function_bytes = REAL_FNV_O0_BLOCKS
            .iter()
            .flat_map(|encoded| decode_hex(encoded))
            .collect::<Vec<_>>();
        assert_eq!(function_bytes.len(), 200, "{provenance}");
        assert_eq!(
            sha256_hex(&function_bytes),
            REAL_FNV_O0_FUNCTION_SHA256,
            "function-byte provenance changed: {provenance}"
        );

        let artifact = real_o0_artifact();
        let facts = artifact
            .structured()
            .canonical_fnv_fold_o0
            .values()
            .collect::<Vec<_>>();
        let [fact] = facts.as_slice() else {
            panic!("one exact real ARM64 O0 FNV fact: {provenance}")
        };
        assert!(fact.validate_against(&artifact));
        assert_eq!(
            fact.schema_version,
            CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION
        );
        assert_eq!(fact.hash.offset_basis, OFFSET_BASIS);
        assert_eq!(fact.hash.prime_value, FNV_PRIME);
        assert_eq!(fact.memory.accesses.len(), 22);
        assert_eq!(
            fact.memory.instruction_inventory.len(),
            artifact.graph().insts.len()
        );
        assert_eq!(fact.frame.homes.len(), 2);
        assert_eq!(fact.frame.locals.len(), 3);
        assert_eq!(fact.frame.link_register_storage.size, 8);
        assert_eq!(fact.returned.storage.size, 8);
    }
}
