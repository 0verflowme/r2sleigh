//! Exact source facts for a two-arm conditional return funnel.
//!
//! This recognizer is intentionally narrow. It admits only a whole-function
//! diamond with one terminal ABI return and either a register phi or a private
//! stack result slot carrying the two arm values into the shared join.

use std::collections::{BTreeMap, BTreeSet};

use crate::CanonicalStorageId;
use crate::cfg::BlockTerminator;
use crate::function::{SSAFunction, StackAddressBase};
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::machine_context::SourceMachineContext;
use crate::op::SSAOp;
use crate::semantic::{
    MemoryDefFact, MemoryLocation, MemoryPhiFact, MemorySSAFacts, MemoryUseFact, MemoryVersion,
    ObjectId, ObjectKind, ObjectModel, PredicateFact, PredicateFacts, PredicateId,
    RelativeMemoryAddress, SourceBoundaryFacts, StructuredAccessId, StructuredMemoryAccessFact,
};

/// One predicate-selected producer feeding a conditional return funnel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConditionalReturnCandidateFact {
    pub truth: bool,
    pub edge_target: u64,
    pub forwarder: Option<u64>,
    pub producer_block: u64,
    pub producer_inst: InstId,
    pub value: ValueId,
}

/// One exact phi input owned by a branch predecessor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConditionalReturnPhiInputFact {
    pub predecessor: u64,
    pub value: ValueId,
}

/// Register-phi carrier for a conditional return funnel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionalReturnRegisterPhiFact {
    pub phi: ValueId,
    pub phi_inst: InstId,
    pub storage: CanonicalStorageId,
    pub inputs: Vec<ConditionalReturnPhiInputFact>,
}

/// Private stack-slot carrier for a conditional return funnel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionalReturnStackSlotFact {
    pub object: ObjectId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub width: u32,
    /// Exactly the two arm stores followed by the unique join load.
    pub accesses: Vec<StructuredAccessId>,
    pub true_store: StructuredAccessId,
    pub false_store: StructuredAccessId,
    pub load: StructuredAccessId,
    pub merged_version: MemoryVersion,
    pub reaching_definitions: Vec<(u64, MemoryVersion)>,
    pub loaded_value: ValueId,
}

/// Exact carrier used by a conditional return funnel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionalReturnCarrierFact {
    RegisterPhi(ConditionalReturnRegisterPhiFact),
    PrivateStackSlot(ConditionalReturnStackSlotFact),
}

/// Exact two-arm conditional whose candidate values meet at one ABI return.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionalReturnFunnelFact {
    pub predicate: PredicateId,
    pub branch_block: u64,
    pub condition: ValueId,
    pub true_target: u64,
    pub false_target: u64,
    pub true_candidate: ConditionalReturnCandidateFact,
    pub false_candidate: ConditionalReturnCandidateFact,
    pub join_block: u64,
    pub return_inst: InstId,
    pub return_storage: CanonicalStorageId,
    pub return_value: ValueId,
    /// Carrier-to-ABI conversion/copy instructions in execution order.
    pub return_value_chain: Vec<InstId>,
    pub carrier: ConditionalReturnCarrierFact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ArmPath {
    edge_target: u64,
    forwarder: Option<u64>,
    producer: u64,
    join: u64,
}

#[derive(Debug, Clone)]
struct StackCarrierCandidate {
    fact: ConditionalReturnStackSlotFact,
    true_candidate: ConditionalReturnCandidateFact,
    false_candidate: ConditionalReturnCandidateFact,
    return_value_chain: Vec<InstId>,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_conditional_return_funnel_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    boundaries: &SourceBoundaryFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine_context: &SourceMachineContext,
) -> BTreeMap<PredicateId, ConditionalReturnFunnelFact> {
    predicates
        .predicates
        .iter()
        .filter_map(|(predicate_id, predicate)| {
            collect_conditional_return_funnel(
                function,
                graph,
                objects,
                memory,
                predicate,
                boundaries,
                memory_accesses,
                machine_context,
            )
            .map(|fact| (*predicate_id, fact))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn collect_conditional_return_funnel(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicate: &PredicateFact,
    boundaries: &SourceBoundaryFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine_context: &SourceMachineContext,
) -> Option<ConditionalReturnFunnelFact> {
    if function.entry != predicate.block_addr {
        return None;
    }
    let branch = function.cfg().get_block(predicate.block_addr)?;
    if !matches!(
        branch.terminator,
        BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } if true_target == predicate.true_target && false_target == predicate.false_target
    ) {
        return None;
    }
    let (return_inst, return_block, return_storage, return_value) =
        unique_terminal_abi_return(function, graph, boundaries)?;

    let true_paths = arm_paths(function, predicate.true_target);
    let false_paths = arm_paths(function, predicate.false_target);
    let mut facts = Vec::new();
    for true_path in &true_paths {
        for false_path in &false_paths {
            if true_path.producer == false_path.producer
                || true_path.join != false_path.join
                || true_path.join != return_block
                || function.predecessors(true_path.join).as_slice()
                    != sorted_pair(true_path.producer, false_path.producer).as_slice()
                || !function_shape_is_closed(
                    function,
                    predicate.block_addr,
                    *true_path,
                    *false_path,
                )
            {
                continue;
            }

            let register =
                register_phi_carrier(function, graph, *true_path, *false_path, return_value);
            let stack = private_stack_carrier(
                graph,
                objects,
                memory,
                memory_accesses,
                machine_context,
                *true_path,
                *false_path,
                return_value,
            );
            let (true_candidate, false_candidate, return_value_chain, carrier) =
                match (register, stack) {
                    (Some((register, true_candidate, false_candidate, chain)), None) => (
                        true_candidate,
                        false_candidate,
                        chain,
                        ConditionalReturnCarrierFact::RegisterPhi(register),
                    ),
                    (None, Some(stack)) => (
                        stack.true_candidate,
                        stack.false_candidate,
                        stack.return_value_chain,
                        ConditionalReturnCarrierFact::PrivateStackSlot(stack.fact),
                    ),
                    (Some(_), Some(_)) | (None, None) => continue,
                };
            facts.push(ConditionalReturnFunnelFact {
                predicate: predicate.id,
                branch_block: predicate.block_addr,
                condition: predicate.condition,
                true_target: predicate.true_target,
                false_target: predicate.false_target,
                true_candidate,
                false_candidate,
                join_block: return_block,
                return_inst,
                return_storage,
                return_value,
                return_value_chain,
                carrier,
            });
        }
    }
    match facts.as_mut_slice() {
        [fact] => Some(fact.clone()),
        _ => None,
    }
}

fn unique_terminal_abi_return(
    function: &SSAFunction,
    graph: &SsaGraph,
    boundaries: &SourceBoundaryFacts,
) -> Option<(InstId, u64, CanonicalStorageId, ValueId)> {
    let mut returns = boundaries.returns.values().filter_map(|boundary| {
        let [value] = boundary.values.as_slice() else {
            return None;
        };
        if !boundary.complete {
            return None;
        }
        let crate::semantic::CallBoundarySlot::Register { index: 0, storage } = value.slot else {
            return None;
        };
        let (block_addr, op_index) = graph.op_site_for_inst(boundary.at)?;
        let block = function.get_block(block_addr)?;
        matches!(block.ops.get(op_index), Some(SSAOp::Return { .. })).then_some((
            boundary.at,
            block_addr,
            storage,
            value.value,
        ))
    });
    let result = returns.next()?;
    if returns.next().is_some()
        || boundaries.returns.len() != 1
        || !function.successors(result.1).is_empty()
        || !matches!(
            function.cfg().get_block(result.1)?.terminator,
            BlockTerminator::Return
        )
    {
        return None;
    }
    Some(result)
}

fn arm_paths(function: &SSAFunction, edge_target: u64) -> Vec<ArmPath> {
    let mut paths = Vec::new();
    if let [join] = function.successors(edge_target).as_slice() {
        paths.push(ArmPath {
            edge_target,
            forwarder: None,
            producer: edge_target,
            join: *join,
        });
        if block_is_empty_forwarder(function, edge_target)
            && let [next_join] = function.successors(*join).as_slice()
        {
            paths.push(ArmPath {
                edge_target,
                forwarder: Some(edge_target),
                producer: *join,
                join: *next_join,
            });
        }
    }
    paths
}

fn block_is_empty_forwarder(function: &SSAFunction, block_addr: u64) -> bool {
    let Some(block) = function.get_block(block_addr) else {
        return false;
    };
    block.phis.is_empty()
        && block
            .ops
            .iter()
            .all(|op| matches!(op, SSAOp::Branch { .. }))
        && matches!(
            function
                .cfg()
                .get_block(block_addr)
                .map(|block| &block.terminator),
            Some(BlockTerminator::Branch { .. } | BlockTerminator::Fallthrough { .. })
        )
}

fn function_shape_is_closed(
    function: &SSAFunction,
    branch: u64,
    true_path: ArmPath,
    false_path: ArmPath,
) -> bool {
    let expected = [
        Some(branch),
        Some(true_path.producer),
        true_path.forwarder,
        Some(false_path.producer),
        false_path.forwarder,
        Some(true_path.join),
    ]
    .into_iter()
    .flatten()
    .collect::<BTreeSet<_>>();
    let actual = function
        .block_addrs()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    expected == actual
        && true_path
            .forwarder
            .is_none_or(|forwarder| function.predecessors(forwarder).as_slice() == [branch])
        && false_path
            .forwarder
            .is_none_or(|forwarder| function.predecessors(forwarder).as_slice() == [branch])
        && function.predecessors(true_path.producer).as_slice()
            == [true_path.forwarder.unwrap_or(branch)]
        && function.predecessors(false_path.producer).as_slice()
            == [false_path.forwarder.unwrap_or(branch)]
}

fn sorted_pair(left: u64, right: u64) -> Vec<u64> {
    let mut pair = vec![left, right];
    pair.sort_unstable();
    pair
}

fn register_phi_carrier(
    function: &SSAFunction,
    graph: &SsaGraph,
    true_path: ArmPath,
    false_path: ArmPath,
    return_value: ValueId,
) -> Option<(
    ConditionalReturnRegisterPhiFact,
    ConditionalReturnCandidateFact,
    ConditionalReturnCandidateFact,
    Vec<InstId>,
)> {
    let join = function.get_block(true_path.join)?;
    let mut candidates = Vec::new();
    for phi in &join.phis {
        let Some(storage) = phi.canonical_storage else {
            continue;
        };
        if phi.sources.len() != 2 {
            continue;
        }
        let Some(phi_value) = graph.value_id_for_var(&phi.dst) else {
            continue;
        };
        let Some(mut chain) =
            value_chain_to_carrier(graph, true_path.join, return_value, phi_value)
        else {
            continue;
        };
        chain.reverse();
        let source_for = |predecessor| {
            phi.sources
                .iter()
                .find(|(source_predecessor, _)| *source_predecessor == predecessor)
                .and_then(|(_, value)| graph.value_id_for_var(value))
        };
        let Some(true_value) = source_for(true_path.producer) else {
            continue;
        };
        let Some(false_value) = source_for(false_path.producer) else {
            continue;
        };
        let Some(true_inst) = producer_inst_in_block(graph, true_value, true_path.producer) else {
            continue;
        };
        let Some(false_inst) = producer_inst_in_block(graph, false_value, false_path.producer)
        else {
            continue;
        };
        if true_inst == false_inst {
            continue;
        }
        let mut inputs = vec![
            ConditionalReturnPhiInputFact {
                predecessor: true_path.producer,
                value: true_value,
            },
            ConditionalReturnPhiInputFact {
                predecessor: false_path.producer,
                value: false_value,
            },
        ];
        inputs.sort_by_key(|input| input.predecessor);
        candidates.push((
            ConditionalReturnRegisterPhiFact {
                phi: phi_value,
                phi_inst: graph.def_inst(phi_value)?,
                storage,
                inputs,
            },
            candidate_fact(true, true_path, true_inst, true_value),
            candidate_fact(false, false_path, false_inst, false_value),
            chain,
        ));
    }
    match candidates.as_mut_slice() {
        [candidate] => Some(candidate.clone()),
        _ => None,
    }
}

fn producer_inst_in_block(graph: &SsaGraph, value: ValueId, block_addr: u64) -> Option<InstId> {
    let inst = graph.def_inst(value)?;
    let graph_block = graph.block(graph.inst(inst)?.block)?;
    (graph_block.addr == block_addr).then_some(inst)
}

#[allow(clippy::too_many_arguments)]
fn private_stack_carrier(
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    memory_accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine_context: &SourceMachineContext,
    true_path: ArmPath,
    false_path: ArmPath,
    return_value: ValueId,
) -> Option<StackCarrierCandidate> {
    let mut candidates = Vec::new();
    for load in memory_accesses
        .values()
        .filter(|access| !access.is_write && access.block_addr == true_path.join)
    {
        if !load.provenance_complete || load.width == 0 {
            continue;
        }
        let Some(loaded_value) = load.value else {
            continue;
        };
        let Some(mut return_value_chain) =
            value_chain_to_carrier(graph, true_path.join, return_value, loaded_value)
        else {
            continue;
        };
        return_value_chain.reverse();
        let Some((base, offset)) =
            exact_private_stack_slot(objects, machine_context, load.object, load.width)
        else {
            continue;
        };
        let Some(load_use) = unique_exact_memory_use(memory, load) else {
            continue;
        };
        let Some(true_store) = unique_stack_store(
            memory,
            memory_accesses,
            true_path.producer,
            &load_use.location,
        ) else {
            continue;
        };
        let Some(false_store) = unique_stack_store(
            memory,
            memory_accesses,
            false_path.producer,
            &load_use.location,
        ) else {
            continue;
        };
        let Some(true_def) = unique_exact_memory_def(memory, true_store) else {
            continue;
        };
        let Some(false_def) = unique_exact_memory_def(memory, false_store) else {
            continue;
        };
        let Some(memory_phi) = exact_memory_phi(
            memory,
            true_path.join,
            &load_use.location,
            load_use.version,
            true_path.producer,
            true_def.next_version,
            false_path.producer,
            false_def.next_version,
        ) else {
            continue;
        };
        if !all_aliasing_accesses_are_exact(
            objects,
            memory,
            &load_use.location,
            true_store.id.inst,
            false_store.id.inst,
            load.id.inst,
        ) || !stack_addresses_do_not_escape(
            graph,
            objects,
            load.object,
            [true_store.id.inst, false_store.id.inst, load.id.inst],
        ) {
            continue;
        }
        let Some(true_value) = true_store.value else {
            continue;
        };
        let Some(false_value) = false_store.value else {
            continue;
        };
        let mut accesses = vec![true_store.id, false_store.id, load.id];
        accesses.sort_by_key(|access| {
            memory_accesses
                .get(access)
                .map(|fact| (fact.block_addr, fact.op_index, fact.is_write))
                .unwrap_or_default()
        });
        let mut reaching_definitions = memory_phi.inputs.clone();
        reaching_definitions.sort_by_key(|(predecessor, _)| *predecessor);
        candidates.push(StackCarrierCandidate {
            fact: ConditionalReturnStackSlotFact {
                object: load.object,
                base,
                offset,
                width: load.width,
                accesses,
                true_store: true_store.id,
                false_store: false_store.id,
                load: load.id,
                merged_version: memory_phi.output_version,
                reaching_definitions,
                loaded_value,
            },
            true_candidate: candidate_fact(true, true_path, true_store.id.inst, true_value),
            false_candidate: candidate_fact(false, false_path, false_store.id.inst, false_value),
            return_value_chain,
        });
    }
    match candidates.as_mut_slice() {
        [candidate] => Some(candidate.clone()),
        _ => None,
    }
}

fn candidate_fact(
    truth: bool,
    path: ArmPath,
    producer_inst: InstId,
    value: ValueId,
) -> ConditionalReturnCandidateFact {
    ConditionalReturnCandidateFact {
        truth,
        edge_target: path.edge_target,
        forwarder: path.forwarder,
        producer_block: path.producer,
        producer_inst,
        value,
    }
}

fn value_chain_to_carrier(
    graph: &SsaGraph,
    join_block: u64,
    start: ValueId,
    carrier: ValueId,
) -> Option<Vec<InstId>> {
    let mut current = start;
    let mut seen = BTreeSet::new();
    let mut chain = Vec::new();
    while current != carrier {
        if !seen.insert(current) {
            return None;
        }
        let inst_id = graph.def_inst(current)?;
        let inst = graph.inst(inst_id)?;
        if graph.block(inst.block)?.addr != join_block || inst.inputs.len() != 1 {
            return None;
        }
        if !matches!(
            inst.payload,
            InstPayload::Op(
                SSAOp::Copy { .. }
                    | SSAOp::IntZExt { .. }
                    | SSAOp::IntSExt { .. }
                    | SSAOp::Trunc { .. }
                    | SSAOp::Cast { .. }
                    | SSAOp::Subpiece { .. }
            )
        ) {
            return None;
        }
        chain.push(inst_id);
        current = inst.inputs[0];
    }
    Some(chain)
}

fn exact_private_stack_slot(
    objects: &ObjectModel,
    machine_context: &SourceMachineContext,
    object: ObjectId,
    width: u32,
) -> Option<(StackAddressBase, i64)> {
    let fact = objects.object(object)?;
    let (base, offset) = match fact.kind {
        ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
            (base, offset)
        }
        ObjectKind::Parameter { .. }
        | ObjectKind::Global { .. }
        | ObjectKind::HeapAlloc { .. }
        | ObjectKind::EscapedUnknown => return None,
    };
    let interface = machine_context.function_interface()?;
    let mut slots = interface.stack_slots().iter().filter(|slot| {
        slot.base() == base && slot.offset() == offset && slot.size_bytes() == width
    });
    slots.next()?;
    if slots.next().is_some() {
        return None;
    }
    Some((base, offset))
}

fn unique_exact_memory_use<'a>(
    memory: &'a MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<&'a MemoryUseFact> {
    let uses = memory.uses_by_inst.get(&access.id.inst)?;
    let [use_fact] = uses.as_slice() else {
        return None;
    };
    (use_fact.location.object == access.object
        && use_fact.location.size == access.width
        && use_fact.location.address == RelativeMemoryAddress::Exact(0))
    .then_some(use_fact)
}

fn unique_exact_memory_def<'a>(
    memory: &'a MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<&'a MemoryDefFact> {
    let defs = memory.defs_by_inst.get(&access.id.inst)?;
    let [def] = defs.as_slice() else {
        return None;
    };
    (def.location.object == access.object
        && def.location.size == access.width
        && def.location.address == RelativeMemoryAddress::Exact(0))
    .then_some(def)
}

fn unique_stack_store<'a>(
    memory: &MemorySSAFacts,
    memory_accesses: &'a BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    block_addr: u64,
    location: &MemoryLocation,
) -> Option<&'a StructuredMemoryAccessFact> {
    let mut stores = memory_accesses.values().filter(|access| {
        access.is_write
            && access.provenance_complete
            && access.block_addr == block_addr
            && access.object == location.object
            && access.width == location.size
            && unique_exact_memory_def(memory, access).is_some_and(|def| def.location == *location)
    });
    let store = stores.next()?;
    stores.next().is_none().then_some(store)
}

#[allow(clippy::too_many_arguments)]
fn exact_memory_phi<'a>(
    memory: &'a MemorySSAFacts,
    join: u64,
    location: &MemoryLocation,
    loaded_version: MemoryVersion,
    true_predecessor: u64,
    true_version: MemoryVersion,
    false_predecessor: u64,
    false_version: MemoryVersion,
) -> Option<&'a MemoryPhiFact> {
    let expected = BTreeMap::from([
        (true_predecessor, true_version),
        (false_predecessor, false_version),
    ]);
    let mut phis = memory.phis_by_block.get(&join)?.iter().filter(|phi| {
        phi.location == *location
            && phi.output_version == loaded_version
            && phi.inputs.iter().copied().collect::<BTreeMap<_, _>>() == expected
            && phi.inputs.len() == 2
    });
    let phi = phis.next()?;
    phis.next().is_none().then_some(phi)
}

fn all_aliasing_accesses_are_exact(
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    target: &MemoryLocation,
    true_store: InstId,
    false_store: InstId,
    load: InstId,
) -> bool {
    let allowed_defs = BTreeSet::from([true_store, false_store]);
    let allowed_uses = BTreeSet::from([load]);
    memory.defs_by_inst.iter().all(|(inst, defs)| {
        defs.iter().all(|def| {
            !super::semantic::memory_locations_may_alias(objects, &def.location, target)
                || (allowed_defs.contains(inst) && def.location == *target)
        })
    }) && memory.uses_by_inst.iter().all(|(inst, uses)| {
        uses.iter().all(|use_fact| {
            !super::semantic::memory_locations_may_alias(objects, &use_fact.location, target)
                || (allowed_uses.contains(inst) && use_fact.location == *target)
        })
    })
}

fn stack_addresses_do_not_escape(
    graph: &SsaGraph,
    objects: &ObjectModel,
    object: ObjectId,
    allowed_accesses: [InstId; 3],
) -> bool {
    let allowed = allowed_accesses.into_iter().collect::<BTreeSet<_>>();
    objects
        .value_objects
        .iter()
        .filter(|(_, value_object)| **value_object == object)
        .all(|(value, _)| address_value_is_confined(graph, *value, &allowed, &mut BTreeSet::new()))
}

fn address_value_is_confined(
    graph: &SsaGraph,
    value: ValueId,
    allowed_accesses: &BTreeSet<InstId>,
    visiting: &mut BTreeSet<ValueId>,
) -> bool {
    if !visiting.insert(value) {
        return false;
    }
    let confined = graph.use_sites(value).iter().all(|use_site| {
        let Some(inst) = graph.inst(use_site.inst) else {
            return false;
        };
        if allowed_accesses.contains(&use_site.inst) {
            return use_site.input_idx == 0
                && matches!(
                    inst.payload,
                    InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. })
                );
        }
        matches!(inst.payload, InstPayload::Phi { .. })
            && inst.output.is_some_and(|output| {
                address_value_is_confined(graph, output, allowed_accesses, visiting)
            })
    });
    visiting.remove(&value);
    confined
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine_context::{
        SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn, SourceStackSlotSpec,
    };
    use crate::{CanonicalStorageSpace, SsaArtifact};
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("conditional-return-test");
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("x0", 8, 8));
        arch.add_register(RegisterDef::new("w0", 8, 4));
        arch.add_register(RegisterDef::new("arg0", 16, 8));
        arch.add_register(RegisterDef::new("pc", 24, 8));
        arch
    }

    fn test_interface(with_stack_slot: bool) -> SourceFunctionInterface {
        test_interface_with_return(with_stack_slot, storage(8, 8))
    }

    fn test_interface_with_return(
        with_stack_slot: bool,
        return_storage: CanonicalStorageId,
    ) -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"conditional-return-revision-1".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, storage(16, 8))],
            SourceFunctionReturn::Register {
                storage: return_storage,
            },
            with_stack_slot.then_some(SourceStackSlotSpec::new(
                StackAddressBase::StackPointer,
                storage(0, 8),
                -4,
                4,
            )),
        )
        .expect("test function interface")
    }

    fn branch_entry(true_target: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(0x1000, 4);
        let cond = Varnode::unique(0x10, 1);
        block.push(R2ILOp::IntEqual {
            dst: cond.clone(),
            a: Varnode::register(16, 8),
            b: Varnode::constant(0xdead, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::ram(true_target, 8),
            cond,
        });
        block
    }

    fn register_funnel_blocks() -> Vec<R2ILBlock> {
        let entry = branch_entry(0x1020);
        let mut false_arm = R2ILBlock::new(0x1004, 4);
        false_arm.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0, 8),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });
        let mut true_arm = R2ILBlock::new(0x1020, 4);
        true_arm.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(1, 8),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });
        let mut join = R2ILBlock::new(0x1030, 4);
        join.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        vec![entry, false_arm, true_arm, join]
    }

    fn stack_addr(unique: u64) -> (R2ILOp, Varnode) {
        let address = Varnode::unique(unique, 8);
        (
            R2ILOp::IntAdd {
                dst: address.clone(),
                a: Varnode::register(0, 8),
                b: Varnode::constant(u64::MAX - 3, 8),
            },
            address,
        )
    }

    fn stack_store_arm(addr: u64, value: u64, unique: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        let (address_op, address) = stack_addr(unique);
        block.push(address_op);
        block.push(R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: address,
            val: Varnode::constant(value, 4),
        });
        block.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });
        block
    }

    fn stack_funnel_blocks(with_forwarder: bool) -> Vec<R2ILBlock> {
        let true_target = 0x1020;
        let entry = branch_entry(true_target);
        let mut blocks = vec![entry];
        if with_forwarder {
            let mut forwarder = R2ILBlock::new(0x1004, 4);
            forwarder.push(R2ILOp::Branch {
                target: Varnode::ram(0x1008, 8),
            });
            blocks.push(forwarder);
            blocks.push(stack_store_arm(0x1008, 0, 0x30));
        } else {
            blocks.push(stack_store_arm(0x1004, 0, 0x30));
        }
        blocks.push(stack_store_arm(0x1020, 1, 0x40));
        let mut join = R2ILBlock::new(0x1030, 4);
        let (address_op, address) = stack_addr(0x50);
        let loaded = Varnode::unique(0x60, 4);
        join.push(address_op);
        join.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: r2il::SpaceId::Ram,
            addr: address,
        });
        join.push(R2ILOp::IntZExt {
            dst: Varnode::register(8, 8),
            src: loaded,
        });
        join.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });
        blocks.push(join);
        blocks
    }

    fn artifact(blocks: &[R2ILBlock], with_stack_slot: bool) -> SsaArtifact {
        if with_stack_slot {
            SsaArtifact::for_decompile_with_interface(
                blocks,
                Some(&test_arch()),
                test_interface(true),
            )
            .expect("decompiler-prepared conditional return artifact")
        } else {
            SsaArtifact::raw_with_interface(blocks, Some(&test_arch()), test_interface(false))
                .expect("raw conditional return artifact")
        }
    }

    #[test]
    fn admits_exact_register_phi_funnel_with_polarity() {
        let artifact = artifact(&register_funnel_blocks(), false);
        let facts = &artifact.structured().conditional_return_funnels;
        let collected = facts.values().collect::<Vec<_>>();
        let [fact] = collected.as_slice() else {
            panic!("one exact register funnel: {facts:?}");
        };
        assert_eq!(fact.branch_block, 0x1000);
        assert_eq!(fact.true_target, 0x1020);
        assert_eq!(fact.false_target, 0x1004);
        assert!(fact.true_candidate.truth);
        assert!(!fact.false_candidate.truth);
        assert_eq!(fact.true_candidate.producer_block, 0x1020);
        assert_eq!(fact.false_candidate.producer_block, 0x1004);
        assert!(matches!(
            fact.carrier,
            ConditionalReturnCarrierFact::RegisterPhi(_)
        ));
    }

    #[test]
    fn admits_private_stack_funnel_and_enumerates_exact_accesses() {
        let artifact = artifact(&stack_funnel_blocks(true), true);
        let facts = &artifact.structured().conditional_return_funnels;
        let collected = facts.values().collect::<Vec<_>>();
        let [fact] = collected.as_slice() else {
            panic!("one exact stack funnel: {facts:?}");
        };
        assert_eq!(fact.false_candidate.forwarder, Some(0x1004));
        let ConditionalReturnCarrierFact::PrivateStackSlot(slot) = &fact.carrier else {
            panic!("private stack carrier: {:?}", fact.carrier);
        };
        assert_eq!(slot.base, StackAddressBase::StackPointer);
        assert_eq!(slot.offset, -4);
        assert_eq!(slot.width, 4);
        assert_eq!(slot.accesses.len(), 3);
        assert_eq!(slot.reaching_definitions.len(), 2);
        assert_eq!(fact.return_value_chain.len(), 1);
    }

    #[test]
    fn rejects_two_empty_forwarders_on_one_arm() {
        let mut blocks = stack_funnel_blocks(true);
        blocks[1].ops[0] = R2ILOp::Branch {
            target: Varnode::ram(0x1006, 8),
        };
        let mut second = R2ILBlock::new(0x1006, 2);
        second.push(R2ILOp::Branch {
            target: Varnode::ram(0x1008, 8),
        });
        blocks.insert(2, second);
        assert!(
            artifact(&blocks, true)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );
    }

    #[test]
    fn rejects_cross_edge_into_optional_forwarder() {
        let mut blocks = stack_funnel_blocks(true);
        blocks[3].ops.pop();
        blocks[3].push(R2ILOp::CBranch {
            target: Varnode::ram(0x1004, 8),
            cond: Varnode::unique(0xa0, 1),
        });
        assert!(
            artifact(&blocks, true)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );
    }

    #[test]
    fn rejects_register_fanin_and_wrong_abi_width() {
        let mut fanin = register_funnel_blocks();
        let mut extra = R2ILBlock::new(0x1040, 4);
        extra.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });
        fanin.push(extra);
        assert!(
            artifact(&fanin, false)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );

        let blocks = register_funnel_blocks();
        let wrong_width = SsaArtifact::raw_with_interface(
            &blocks,
            Some(&test_arch()),
            test_interface_with_return(false, storage(8, 4)),
        )
        .expect("wrong-width return artifact");
        assert!(
            wrong_width
                .structured()
                .conditional_return_funnels
                .is_empty()
        );
    }

    #[test]
    fn rejects_read_before_write_and_extra_slot_write() {
        let mut missing_write = stack_funnel_blocks(false);
        missing_write[1].ops.remove(1);
        assert!(
            artifact(&missing_write, true)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );

        let mut extra_write = stack_funnel_blocks(false);
        let (address_op, address) = stack_addr(0x70);
        extra_write[0].ops.insert(1, address_op);
        extra_write[0].ops.insert(
            2,
            R2ILOp::Store {
                space: r2il::SpaceId::Ram,
                addr: address,
                val: Varnode::constant(7, 4),
            },
        );
        assert!(
            artifact(&extra_write, true)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );
    }

    #[test]
    fn rejects_slot_address_escape_and_unknown_alias() {
        let mut escaped = stack_funnel_blocks(false);
        let address = match &escaped[1].ops[0] {
            R2ILOp::IntAdd { dst, .. } => dst.clone(),
            _ => panic!("stack address calculation"),
        };
        escaped[1].ops.insert(
            1,
            R2ILOp::Copy {
                dst: Varnode::register(16, 8),
                src: address,
            },
        );
        assert!(
            artifact(&escaped, true)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );

        let mut alias = stack_funnel_blocks(false);
        alias[1].ops.insert(
            1,
            R2ILOp::Load {
                dst: Varnode::unique(0x80, 4),
                space: r2il::SpaceId::Ram,
                addr: Varnode::unique(0x90, 8),
            },
        );
        assert!(
            artifact(&alias, true)
                .structured()
                .conditional_return_funnels
                .is_empty()
        );
    }

    #[test]
    fn rejects_ambiguous_load_reaching_definition() {
        let artifact = artifact(&stack_funnel_blocks(false), true);
        let fact = artifact
            .structured()
            .conditional_return_funnels
            .values()
            .next()
            .expect("baseline stack funnel");
        let ConditionalReturnCarrierFact::PrivateStackSlot(slot) = &fact.carrier else {
            panic!("stack carrier");
        };
        let mut memory = artifact.memory().clone();
        let uses = memory
            .uses_by_inst
            .get_mut(&slot.load.inst)
            .expect("load memory use");
        uses.push(uses[0].clone());
        let facts = collect_conditional_return_funnel_facts(
            artifact.function(),
            artifact.graph(),
            artifact.objects(),
            &memory,
            artifact.predicates(),
            &artifact.facts().boundaries,
            &artifact.structured().memory_accesses,
            artifact.machine_context(),
        );
        assert!(facts.is_empty());
    }
}
