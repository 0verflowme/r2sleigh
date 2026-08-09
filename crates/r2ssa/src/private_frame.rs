//! Sealed source facts for one exact x86-64 O0 private-frame envelope.
//!
//! These facts retain source and SSA identities only. They are deliberately
//! not renderer or certification authority.

use std::collections::BTreeSet;

use crate::function::{FunctionPrepareMode, SSAFunction, StackAddressBase};
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::machine_context::{
    MACHINE_CONTEXT_SCHEMA_VERSION, SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SourceCarrierKind,
    SourceMachineContext, SourceStackSlotRole, SourceTypeKind,
};
use crate::op::SSAOp;
use crate::semantic::{
    MemoryDefFact, MemoryUseFact, MemoryVersion, ObjectId, ObjectKind, ObjectModel, PredicateId,
    PreparedFunctionFacts, RelativeMemoryAddress, StructuredAccessId, StructuredMemoryAccessFact,
};
use crate::{CanonicalStorageId, CanonicalStorageSpace};

pub const PRIVATE_FRAME_FACT_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrivateFrameStackUpdateFact {
    pub inst: InstId,
    pub input: ValueId,
    pub output: ValueId,
    pub delta: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrivateFrameRegisterCopyFact {
    pub inst: InstId,
    pub input: ValueId,
    pub output: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameHomeReloadFact {
    pub access: StructuredAccessId,
    pub value: ValueId,
    pub memory_version: MemoryVersion,
    pub memory_uses: Box<[MemoryUseFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameHomeFact {
    pub object: ObjectId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub width: u32,
    pub parameter_index: u32,
    pub parameter_storage: CanonicalStorageId,
    pub abi_parameter_value: ValueId,
    pub parameter_value: ValueId,
    pub init_store: StructuredAccessId,
    pub init_memory_version: MemoryVersion,
    pub init_memory_defs: Box<[MemoryDefFact]>,
    pub reloads: Vec<PrivateFrameHomeReloadFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameAccessMemoryFact {
    pub access: StructuredAccessId,
    pub memory_defs: Box<[MemoryDefFact]>,
    pub memory_uses: Box<[MemoryUseFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameLocalFact {
    pub object: ObjectId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub width: u32,
    pub accesses: Vec<StructuredAccessId>,
    pub access_memory: Vec<PrivateFrameAccessMemoryFact>,
    pub predicate: PredicateId,
    pub branch_block: u64,
    pub true_target: u64,
    pub false_target: u64,
    pub true_store: StructuredAccessId,
    pub true_value: ValueId,
    pub false_store: StructuredAccessId,
    pub false_value: ValueId,
    pub true_producer: u64,
    pub false_producer: u64,
    pub join_block: u64,
    pub join_load: StructuredAccessId,
    pub loaded_value: ValueId,
    pub return_inst: InstId,
    pub return_storage: CanonicalStorageId,
    pub return_value: ValueId,
    pub return_relay_insts: Box<[InstId]>,
    pub return_transform_insts: Box<[InstId]>,
    pub conditional_funnel: Option<PredicateId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameSavedFramePointerFact {
    pub store_object: ObjectId,
    pub load_object: ObjectId,
    pub store: StructuredAccessId,
    pub load: StructuredAccessId,
    pub stored_value: ValueId,
    pub loaded_value: ValueId,
    pub restored_value: ValueId,
    pub capture: PrivateFrameRegisterCopyFact,
    pub restore: PrivateFrameRegisterCopyFact,
    pub store_memory_defs: Box<[MemoryDefFact]>,
    pub load_memory_uses: Box<[MemoryUseFact]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameReturnAddressFact {
    pub object: ObjectId,
    pub load: StructuredAccessId,
    pub stack_value: ValueId,
    pub target: ValueId,
    pub return_inst: InstId,
    pub memory_uses: Box<[MemoryUseFact]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrivateFramePhysicalRangeFact {
    pub start_from_entry_sp: i64,
    pub end_from_entry_sp: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrivateFrameFact {
    pub schema_version: u32,
    pub revision_identity: Box<[u8]>,
    pub entry_block: u64,
    pub exit_block: u64,
    pub pointer_width_bytes: u32,
    pub entry_sp_storage: CanonicalStorageId,
    pub entry_fp_storage: CanonicalStorageId,
    pub entry_pc_storage: CanonicalStorageId,
    pub entry_sp: ValueId,
    pub entry_fp: ValueId,
    pub push: PrivateFrameStackUpdateFact,
    pub frame_pointer_set: PrivateFrameRegisterCopyFact,
    pub saved_frame_pointer: PrivateFrameSavedFramePointerFact,
    pub pop: PrivateFrameStackUpdateFact,
    pub return_address: PrivateFrameReturnAddressFact,
    pub return_advance: PrivateFrameStackUpdateFact,
    pub home: PrivateFrameHomeFact,
    pub local: PrivateFrameLocalFact,
    pub saved_frame_pointer_range: PrivateFramePhysicalRangeFact,
    pub home_range: PrivateFramePhysicalRangeFact,
    pub local_range: PrivateFramePhysicalRangeFact,
    pub return_address_range: PrivateFramePhysicalRangeFact,
}

#[derive(Clone, Copy)]
struct SlotDeclaration {
    base: StackAddressBase,
    base_storage: CanonicalStorageId,
    offset: i64,
    width: u32,
    role: SourceStackSlotRole,
}

#[derive(Clone, Copy)]
struct AccessView<'a> {
    fact: &'a StructuredMemoryAccessFact,
}

struct StackEnvelopeCandidate {
    storage: CanonicalStorageId,
    entry_sp: ValueId,
    push: PrivateFrameStackUpdateFact,
    saved_store: StructuredAccessId,
    saved_stored_value: ValueId,
    saved_capture: PrivateFrameRegisterCopyFact,
    saved_load: StructuredAccessId,
    saved_loaded_value: ValueId,
    pop: PrivateFrameStackUpdateFact,
    return_load: StructuredAccessId,
    return_target: ValueId,
    return_advance: PrivateFrameStackUpdateFact,
    return_inst: InstId,
    exit_block: u64,
    pc_storage: CanonicalStorageId,
}

pub(crate) fn collect_private_frame_fact(
    mode: FunctionPrepareMode,
    function: &SSAFunction,
    graph: &SsaGraph,
    facts: &PreparedFunctionFacts,
    machine: &SourceMachineContext,
    expected_revision: &[u8],
) -> Option<PrivateFrameFact> {
    if mode != FunctionPrepareMode::Decompile
        || expected_revision.is_empty()
        || machine.schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
        || !machine.memory_model().is_available()
        || !machine.memory_model().is_coherent()
        || !machine.abi_model().is_coherent()
        || !facts.boundaries.calls.is_empty()
        || function
            .blocks()
            .flat_map(|block| &block.ops)
            .any(|op| matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }))
    {
        return None;
    }
    let interface = machine.function_interface()?;
    if interface.schema_version() != SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        || interface.revision_identity() != expected_revision
        || !interface.stack_slot_roles_complete()
    {
        return None;
    }
    let pointer_width = machine
        .memory_model()
        .default_address_bits()
        .checked_div(8)?;
    if pointer_width != 8 {
        return None;
    }
    let declarations = interface
        .stack_slots()
        .iter()
        .map(|slot| SlotDeclaration {
            base: slot.base(),
            base_storage: slot.base_storage(),
            offset: slot.offset(),
            width: slot.size_bytes(),
            role: slot.role(),
        })
        .collect::<Vec<_>>();
    let Some(first) = declarations.first().copied() else {
        return None;
    };
    if declarations.len() > 2
        || declarations.iter().enumerate().any(|(index, declaration)| {
            declarations[index.saturating_add(1)..]
                .iter()
                .any(|other| declarations_overlap(*declaration, *other))
        })
        || !declarations
            .iter()
            .all(|slot| slot.base == StackAddressBase::FramePointer)
    {
        return None;
    }
    let fp_storage = first.base_storage;
    if fp_storage.size != pointer_width
        || declarations
            .iter()
            .any(|slot| slot.base_storage != fp_storage)
    {
        return None;
    }
    let mut homes = declarations
        .iter()
        .copied()
        .filter(|slot| matches!(slot.role, SourceStackSlotRole::ParameterHome { .. }));
    let home_decl = homes.next()?;
    if homes.next().is_some() {
        return None;
    }
    let locals = declarations
        .iter()
        .copied()
        .filter(|slot| slot.role == SourceStackSlotRole::Local)
        .collect::<Vec<_>>();
    let local_decl = match locals.as_slice() {
        [local] => *local,
        [] if declarations.len() == 1 => {
            infer_hidden_private_local_declaration(facts, fp_storage, home_decl)?
        }
        [] | [_, _, ..] => return None,
    };
    let SourceStackSlotRole::ParameterHome {
        parameter_index,
        home_storage,
    } = home_decl.role
    else {
        return None;
    };
    let source_parameter = interface
        .parameters()
        .get(usize::try_from(parameter_index).ok()?)?;
    if source_parameter.index() != parameter_index || source_parameter.storage() != home_storage {
        return None;
    }
    let abi_parameter_value = match facts.boundaries.parameters.get(&parameter_index) {
        Some(parameter)
            if parameter.index == parameter_index && parameter.storage == home_storage =>
        {
            parameter.value
        }
        None if facts.boundaries.parameters.is_empty() => private_low_parameter_entry_value(
            graph,
            machine,
            parameter_index,
            home_storage,
            home_decl.width,
        )?,
        Some(_) | None => return None,
    };

    let fp_writes = register_writes(graph, machine, fp_storage);
    if fp_writes.len() != 2 {
        return None;
    }
    let entry_fp = entry_value(graph, machine, fp_storage)?;
    if !is_entry_value(graph, entry_fp) {
        return None;
    }
    let mut envelope_candidates = machine
        .register_storages_by_name()
        .values()
        .copied()
        .filter(|storage| storage.size == pointer_width && *storage != fp_storage)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter_map(|storage| {
            collect_stack_envelope_candidate(
                function,
                graph,
                facts,
                machine,
                storage,
                entry_fp,
                pointer_width,
            )
        });
    let envelope = envelope_candidates.next()?;
    if envelope_candidates.next().is_some() || envelope.pc_storage == fp_storage {
        return None;
    }
    let sp_storage = envelope.storage;
    let pc_storage = envelope.pc_storage;
    let entry_sp = envelope.entry_sp;
    let push = envelope.push;
    let saved_store = access_view(
        facts,
        facts
            .structured
            .memory_accesses
            .get(&envelope.saved_store)?,
    )?;
    let pop = envelope.pop;
    let return_advance = envelope.return_advance;
    let return_target = envelope.return_target;
    let saved_load = unique_envelope_load(facts, push.output, None, pointer_width)?;
    let return_load = unique_envelope_load(facts, pop.output, Some(return_target), pointer_width)?;
    if saved_load.fact.id != envelope.saved_load || return_load.fact.id != envelope.return_load {
        return None;
    }
    let return_inst = envelope.return_inst;
    let exit_block = envelope.exit_block;
    let saved_loaded_value = envelope.saved_loaded_value;
    let saved_stored_value = envelope.saved_stored_value;
    let saved_capture = envelope.saved_capture;
    let frame_pointer_set =
        unique_register_copy(graph, machine, &fp_writes, fp_storage, Some(push.output))?;
    let restore = unique_register_copy(
        graph,
        machine,
        &fp_writes,
        fp_storage,
        Some(saved_loaded_value),
    )?;
    let entry_block = function.entry;
    if !site_order(graph, saved_capture.inst, push.inst)
        || !site_order(graph, push.inst, saved_store.fact.id.inst)
        || !site_order(graph, saved_store.fact.id.inst, frame_pointer_set.inst)
        || !site_precedes(
            function,
            graph,
            frame_pointer_set.inst,
            saved_load.fact.id.inst,
        )
        || !site_order(graph, saved_load.fact.id.inst, pop.inst)
        || !site_order(graph, pop.inst, restore.inst)
        || !site_order(graph, restore.inst, return_load.fact.id.inst)
        || !site_order(graph, return_load.fact.id.inst, return_advance.inst)
        || !site_order(graph, return_advance.inst, return_inst)
        || graph.op_site_for_inst(push.inst)?.0 != entry_block
        || graph.op_site_for_inst(frame_pointer_set.inst)?.0 != entry_block
        || graph.op_site_for_inst(saved_load.fact.id.inst)?.0 != exit_block
    {
        return None;
    }

    let home = collect_home(
        function,
        graph,
        facts,
        machine,
        home_decl,
        parameter_index,
        home_storage,
        abi_parameter_value,
        saved_store.fact.object,
        frame_pointer_set.inst,
        saved_load.fact.id.inst,
    )?;
    let local = collect_local(
        function,
        graph,
        facts,
        machine,
        local_decl,
        home.reloads[0].value,
        return_inst,
        saved_load.fact.id.inst,
    )?;
    let saved_frame_pointer_range = physical_range(-8, pointer_width)?;
    let home_range = physical_range(physical_slot_start(home.base, home.offset)?, home.width)?;
    let local_range = physical_range(physical_slot_start(local.base, local.offset)?, local.width)?;
    let return_address_range = physical_range(0, pointer_width)?;
    let ranges = [
        saved_frame_pointer_range,
        home_range,
        local_range,
        return_address_range,
    ];
    if ranges.iter().enumerate().any(|(index, range)| {
        ranges[index.saturating_add(1)..]
            .iter()
            .any(|other| physical_ranges_overlap(*range, *other))
    }) {
        return None;
    }
    let expected_alias_objects = BTreeSet::from([home.object, local.object]);
    let saved_load_memory_uses =
        exact_envelope_memory_uses(facts, saved_load.fact.id.inst, &expected_alias_objects)?;
    let return_memory_uses =
        exact_envelope_memory_uses(facts, return_load.fact.id.inst, &expected_alias_objects)?;
    let saved_store_memory_defs = facts
        .memory
        .defs_by_inst
        .get(&saved_store.fact.id.inst)?
        .clone()
        .into_boxed_slice();
    if saved_store_memory_defs.is_empty()
        || saved_store_memory_defs.iter().any(|def| {
            def.location.object != saved_store.fact.object
                || def.location.address != RelativeMemoryAddress::Exact(0)
                || def.location.size != pointer_width
        })
    {
        return None;
    }
    let known_memory_objects = BTreeSet::from([
        saved_store.fact.object,
        saved_load.fact.object,
        return_load.fact.object,
        home.object,
        local.object,
    ]);
    if !all_memory_versions_are_known(facts, &known_memory_objects) {
        return None;
    }
    let declared_address_defs =
        object_address_definition_uses(graph, &facts.objects, &[home.object, local.object])?;
    if !all_memory_is_exact_private_frame(
        facts,
        [
            (saved_store.fact.id, -8, pointer_width),
            (saved_load.fact.id, -8, pointer_width),
            (return_load.fact.id, 0, pointer_width),
        ],
        &home,
        &local,
    ) || !object_addresses_are_confined(
        graph,
        &facts.objects,
        home.object,
        &home
            .reloads
            .iter()
            .map(|reload| reload.access.inst)
            .chain(std::iter::once(home.init_store.inst))
            .collect(),
    ) || !object_addresses_are_confined(
        graph,
        &facts.objects,
        local.object,
        &local.accesses.iter().map(|access| access.inst).collect(),
    ) || !value_uses_are_exact(
        graph,
        push.output,
        &[
            (saved_store.fact.id.inst, 0),
            (saved_load.fact.id.inst, 0),
            (frame_pointer_set.inst, 0),
            (pop.inst, 0),
        ],
    ) || !value_uses_are_exact(graph, saved_stored_value, &[(saved_store.fact.id.inst, 1)])
        || !value_uses_are_exact(graph, saved_loaded_value, &[(restore.inst, 0)])
        || !value_uses_are_exact(
            graph,
            pop.output,
            &[(return_load.fact.id.inst, 0), (return_advance.inst, 0)],
        )
        || !value_uses_are_exact(graph, return_target, &[(return_inst, 0)])
        || !value_uses_are_exact(graph, entry_fp, &[(saved_capture.inst, 0)])
        || !value_uses_are_exact(graph, entry_sp, &[(push.inst, 0)])
        || !value_uses_are_exact(graph, frame_pointer_set.output, &declared_address_defs)
        || !value_uses_are_exact(graph, restore.output, &[])
        || !value_uses_are_exact(graph, return_advance.output, &[])
    {
        return None;
    }

    Some(PrivateFrameFact {
        schema_version: PRIVATE_FRAME_FACT_SCHEMA_VERSION,
        revision_identity: expected_revision.to_vec().into_boxed_slice(),
        entry_block,
        exit_block,
        pointer_width_bytes: pointer_width,
        entry_sp_storage: sp_storage,
        entry_fp_storage: fp_storage,
        entry_pc_storage: pc_storage,
        entry_sp,
        entry_fp,
        push,
        frame_pointer_set,
        saved_frame_pointer: PrivateFrameSavedFramePointerFact {
            store_object: saved_store.fact.object,
            load_object: saved_load.fact.object,
            store: saved_store.fact.id,
            load: saved_load.fact.id,
            stored_value: saved_stored_value,
            loaded_value: saved_loaded_value,
            restored_value: restore.output,
            capture: saved_capture,
            restore,
            store_memory_defs: saved_store_memory_defs,
            load_memory_uses: saved_load_memory_uses,
        },
        pop,
        return_address: PrivateFrameReturnAddressFact {
            object: return_load.fact.object,
            load: return_load.fact.id,
            stack_value: pop.output,
            target: return_target,
            return_inst,
            memory_uses: return_memory_uses,
        },
        return_advance,
        home,
        local,
        saved_frame_pointer_range,
        home_range,
        local_range,
        return_address_range,
    })
}

fn collect_stack_envelope_candidate(
    function: &SSAFunction,
    graph: &SsaGraph,
    facts: &PreparedFunctionFacts,
    machine: &SourceMachineContext,
    storage: CanonicalStorageId,
    entry_fp: ValueId,
    pointer_width: u32,
) -> Option<StackEnvelopeCandidate> {
    let writes = register_writes(graph, machine, storage);
    if writes.len() != 3 {
        return None;
    }
    let push = unique_stack_update(graph, machine, &writes, storage, -8, None)?;
    if !is_entry_value(graph, push.input) {
        return None;
    }
    let saved_store = unique_access(facts, push.output, None, true, pointer_width)?;
    let saved_stored_value = saved_store.fact.value?;
    let saved_capture = exact_copy_from(graph, saved_stored_value, entry_fp)?;
    let saved_load = unique_envelope_load(facts, push.output, None, pointer_width)?;
    let saved_loaded_value = saved_load.fact.value?;
    let pop = unique_stack_update(graph, machine, &writes, storage, 8, Some(push.output))?;
    let (return_target, return_inst, exit_block) = unique_return_target(graph, function)?;
    let return_load = unique_envelope_load(facts, pop.output, Some(return_target), pointer_width)?;
    if graph.inst(return_load.fact.id.inst)?.output != Some(return_target) {
        return None;
    }
    let pc_storage = value_storage(graph, machine, return_target)?;
    if pc_storage.space != CanonicalStorageSpace::Register
        || pc_storage.size != pointer_width
        || machine.function_interface()?.return_address_storage()? != pc_storage
        || pc_storage == storage
        || register_writes(graph, machine, pc_storage).as_slice() != [return_load.fact.id.inst]
    {
        return None;
    }
    let return_advance =
        unique_stack_update(graph, machine, &writes, storage, 8, Some(pop.output))?;
    if !site_order(graph, saved_load.fact.id.inst, pop.inst)
        || !site_order(graph, pop.inst, return_load.fact.id.inst)
        || !site_order(graph, return_load.fact.id.inst, return_advance.inst)
        || !site_order(graph, return_advance.inst, return_inst)
    {
        return None;
    }
    Some(StackEnvelopeCandidate {
        storage,
        entry_sp: push.input,
        push,
        saved_store: saved_store.fact.id,
        saved_stored_value,
        saved_capture,
        saved_load: saved_load.fact.id,
        saved_loaded_value,
        pop,
        return_load: return_load.fact.id,
        return_target,
        return_advance,
        return_inst,
        exit_block,
        pc_storage,
    })
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

fn exact_copy_from(
    graph: &SsaGraph,
    output: ValueId,
    required_input: ValueId,
) -> Option<PrivateFrameRegisterCopyFact> {
    let inst_id = graph.def_inst(output)?;
    let inst = graph.inst(inst_id)?;
    let InstPayload::Op(SSAOp::Copy { src, .. }) = &inst.payload else {
        return None;
    };
    let input = graph.value_id_for_var(src)?;
    (input == required_input && inst.output == Some(output)).then_some(
        PrivateFrameRegisterCopyFact {
            inst: inst_id,
            input,
            output,
        },
    )
}

fn value_uses_are_exact(graph: &SsaGraph, value: ValueId, expected: &[(InstId, usize)]) -> bool {
    let actual = graph
        .use_sites(value)
        .iter()
        .map(|site| (site.inst, site.input_idx))
        .collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    actual == expected
}

fn object_address_definition_uses(
    graph: &SsaGraph,
    objects: &ObjectModel,
    expected_objects: &[ObjectId],
) -> Option<Vec<(InstId, usize)>> {
    let mut definitions = Vec::new();
    for (value, object) in &objects.value_objects {
        if !expected_objects.contains(object) {
            continue;
        }
        let inst = graph.def_inst(*value)?;
        if !matches!(
            graph.inst(inst)?.payload,
            InstPayload::Op(SSAOp::IntAdd { .. })
        ) {
            return None;
        }
        definitions.push((inst, 0));
    }
    (!definitions.is_empty()).then_some(definitions)
}

fn physical_slot_start(base: StackAddressBase, offset: i64) -> Option<i64> {
    match base {
        StackAddressBase::FramePointer => offset.checked_sub(8),
        StackAddressBase::StackPointer => Some(offset),
    }
}

fn physical_range(start: i64, width: u32) -> Option<PrivateFramePhysicalRangeFact> {
    Some(PrivateFramePhysicalRangeFact {
        start_from_entry_sp: start,
        end_from_entry_sp: start.checked_add(i64::from(width))?,
    })
}

fn physical_ranges_overlap(
    left: PrivateFramePhysicalRangeFact,
    right: PrivateFramePhysicalRangeFact,
) -> bool {
    left.start_from_entry_sp < right.end_from_entry_sp
        && right.start_from_entry_sp < left.end_from_entry_sp
}

fn exact_envelope_memory_uses(
    facts: &PreparedFunctionFacts,
    inst: InstId,
    expected_alias_objects: &BTreeSet<ObjectId>,
) -> Option<Box<[MemoryUseFact]>> {
    let uses = facts.memory.uses_by_inst.get(&inst)?;
    let actual_alias_objects = uses
        .iter()
        .map(|use_fact| use_fact.version.object)
        .collect::<BTreeSet<_>>();
    (uses.len() == expected_alias_objects.len()
        && actual_alias_objects == *expected_alias_objects
        && uses.iter().all(|use_fact| use_fact.version.version > 0))
    .then(|| uses.clone().into_boxed_slice())
}

fn declarations_overlap(left: SlotDeclaration, right: SlotDeclaration) -> bool {
    let (Some(left_start), Some(right_start)) = (
        physical_slot_start(left.base, left.offset),
        physical_slot_start(right.base, right.offset),
    ) else {
        return true;
    };
    let Some(left_end) = left_start.checked_add(i64::from(left.width)) else {
        return true;
    };
    let Some(right_end) = right_start.checked_add(i64::from(right.width)) else {
        return true;
    };
    left_start < right_end && right_start < left_end
}

/// Infer only the compiler-generated result carrier used by the exact private
/// frame diamond. Source declarations remain authoritative for the parameter
/// home; this candidate is admitted solely when the retained object model has
/// one disjoint FP-relative object with exactly two stores and one load of one
/// width. `collect_local` subsequently proves the branch topology, constants,
/// MemorySSA chain, nonescape, and ABI return use.
fn infer_hidden_private_local_declaration(
    facts: &PreparedFunctionFacts,
    fp_storage: CanonicalStorageId,
    home: SlotDeclaration,
) -> Option<SlotDeclaration> {
    let candidates = facts
        .objects
        .objects
        .values()
        .filter_map(|object| {
            let (base, offset) = match object.kind {
                ObjectKind::StackSlot { base, offset }
                | ObjectKind::FrameObject { base, offset } => (base, offset),
                ObjectKind::Parameter { .. }
                | ObjectKind::Global { .. }
                | ObjectKind::HeapAlloc { .. }
                | ObjectKind::EscapedUnknown => return None,
            };
            if base != StackAddressBase::FramePointer {
                return None;
            }
            let accesses = facts
                .structured
                .memory_accesses
                .values()
                .filter(|access| access.object == object.id)
                .collect::<Vec<_>>();
            let width = accesses.first()?.width;
            let writes = accesses.iter().filter(|access| access.is_write).count();
            let reads = accesses.len().saturating_sub(writes);
            let declaration = SlotDeclaration {
                base,
                base_storage: fp_storage,
                offset,
                width,
                role: SourceStackSlotRole::Local,
            };
            (accesses.len() == 3
                && writes == 2
                && reads == 1
                && width > 0
                && accesses.iter().all(|access| {
                    access.width == width && memory_access_locations_are_exact(facts, access)
                })
                && !declarations_overlap(home, declaration))
            .then_some(declaration)
        })
        .collect::<Vec<_>>();
    let [candidate] = candidates.as_slice() else {
        return None;
    };
    Some(*candidate)
}

fn value_has_storage(
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    value: ValueId,
    storage: CanonicalStorageId,
) -> bool {
    graph.value(value).is_some_and(|value| {
        value.var.size == storage.size && value.canonical_storage == Some(storage)
    })
}

fn is_entry_value(graph: &SsaGraph, value: ValueId) -> bool {
    graph
        .value(value)
        .is_some_and(|value| value.var.version == 0)
        && graph.def_inst(value).is_none()
}

fn entry_value(
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    storage: CanonicalStorageId,
) -> Option<ValueId> {
    let mut values = graph.values.iter().filter(|value| {
        value.var.version == 0
            && value.var.size == storage.size
            && value.canonical_storage == Some(storage)
    });
    let value = values.next()?.id;
    values.next().is_none().then_some(value)
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
                .is_some_and(|value| value_has_storage(graph, machine, value, storage))
        })
        .map(|inst| inst.id)
        .collect()
}

fn unique_stack_update(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    writes: &[InstId],
    storage: CanonicalStorageId,
    delta: i64,
    required_input: Option<ValueId>,
) -> Option<PrivateFrameStackUpdateFact> {
    let mut matches = writes.iter().filter_map(|inst_id| {
        let inst = graph.inst(*inst_id)?;
        let InstPayload::Op(op) = &inst.payload else {
            return None;
        };
        let (dst, input, constant, actual_delta) = match op {
            SSAOp::IntSub { dst, a, b } => (dst, a, b, -i64::try_from(b.constant_bits()?).ok()?),
            SSAOp::IntAdd { dst, a, b } => (dst, a, b, i64::try_from(b.constant_bits()?).ok()?),
            _ => return None,
        };
        let input_value = graph.value_id_for_var(input)?;
        let output_value = graph.value_id_for_var(dst)?;
        (actual_delta == delta
            && constant.size == storage.size
            && value_has_storage(graph, machine, input_value, storage)
            && value_has_storage(graph, machine, output_value, storage)
            && required_input.is_none_or(|required| required == input_value))
        .then_some(PrivateFrameStackUpdateFact {
            inst: *inst_id,
            input: input_value,
            output: output_value,
            delta,
        })
    });
    let fact = matches.next()?;
    matches.next().is_none().then_some(fact)
}

fn unique_register_copy(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    writes: &[InstId],
    output_storage: CanonicalStorageId,
    required_input: Option<ValueId>,
) -> Option<PrivateFrameRegisterCopyFact> {
    let mut matches = writes.iter().filter_map(|inst_id| {
        let inst = graph.inst(*inst_id)?;
        let InstPayload::Op(SSAOp::Copy { dst, src }) = &inst.payload else {
            return None;
        };
        let input = graph.value_id_for_var(src)?;
        let output = graph.value_id_for_var(dst)?;
        (value_has_storage(graph, machine, output, output_storage)
            && required_input.is_none_or(|required| required == input))
        .then_some(PrivateFrameRegisterCopyFact {
            inst: *inst_id,
            input,
            output,
        })
    });
    let fact = matches.next()?;
    matches.next().is_none().then_some(fact)
}

fn access_view<'a>(
    facts: &'a PreparedFunctionFacts,
    access: &'a StructuredMemoryAccessFact,
) -> Option<AccessView<'a>> {
    if !access.provenance_complete || access.width == 0 {
        return None;
    }
    if access.is_write {
        let defs = facts.memory.defs_by_inst.get(&access.id.inst)?;
        let [def] = defs.as_slice() else {
            return None;
        };
        (def.location.object == access.object
            && def.location.size == access.width
            && def.location.address == RelativeMemoryAddress::Exact(0))
        .then_some(AccessView { fact: access })
    } else {
        let uses = facts.memory.uses_by_inst.get(&access.id.inst)?;
        let [use_fact] = uses.as_slice() else {
            return None;
        };
        (use_fact.location.object == access.object
            && use_fact.location.size == access.width
            && use_fact.location.address == RelativeMemoryAddress::Exact(0))
        .then_some(AccessView { fact: access })
    }
}

fn unique_access<'a>(
    facts: &'a PreparedFunctionFacts,
    address: ValueId,
    value: Option<ValueId>,
    is_write: bool,
    width: u32,
) -> Option<AccessView<'a>> {
    let mut matches = facts
        .structured
        .memory_accesses
        .values()
        .filter_map(|access| {
            (access.address == address
                && access.is_write == is_write
                && access.width == width
                && value.is_none_or(|required| access.value == Some(required)))
            .then(|| access_view(facts, access))?
        });
    let access = matches.next()?;
    matches.next().is_none().then_some(access)
}

fn unique_envelope_load<'a>(
    facts: &'a PreparedFunctionFacts,
    address: ValueId,
    value: Option<ValueId>,
    width: u32,
) -> Option<AccessView<'a>> {
    let mut matches = facts.structured.memory_accesses.values().filter(|access| {
        access.address == address
            && !access.is_write
            && access.width == width
            && value.is_none_or(|required| access.value == Some(required))
    });
    let access = matches.next()?;
    if matches.next().is_some() || access.provenance_complete {
        return None;
    }
    let uses = facts.memory.uses_by_inst.get(&access.id.inst)?;
    if uses.len() != 2
        || uses.iter().any(|use_fact| {
            use_fact.location.object != access.object
                || use_fact.location.address != RelativeMemoryAddress::Exact(0)
                || use_fact.location.size != width
                || use_fact.version.version == 0
        })
        || uses
            .iter()
            .map(|use_fact| use_fact.version)
            .collect::<BTreeSet<_>>()
            .len()
            != uses.len()
    {
        return None;
    }
    Some(AccessView { fact: access })
}

fn private_home_parameter_value(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    parameter_index: u32,
    parameter_storage: CanonicalStorageId,
    abi_parameter_value: ValueId,
    home_width: u32,
    stored_value: ValueId,
) -> Option<ValueId> {
    if stored_value == abi_parameter_value && parameter_storage.size == home_width {
        return Some(stored_value);
    }
    let stored = graph.value(stored_value)?;
    let stored_storage = stored.canonical_storage?;
    let width_bits = u64::from(home_width).checked_mul(8)?;
    if graph.def_inst(stored_value).is_some()
        || stored.var.version != 0
        || stored.var.size != home_width
        || parameter_storage.space != CanonicalStorageSpace::Register
        || stored_storage.space != CanonicalStorageSpace::Register
        || stored_storage.offset != parameter_storage.offset
        || stored_storage.size != home_width
        || home_width >= parameter_storage.size
    {
        return None;
    }
    let interface = machine.function_interface()?;
    let logical = *interface
        .parameter_logical_values()
        .get(usize::try_from(parameter_index).ok()?)?;
    if logical.carrier().kind() != SourceCarrierKind::LowBits
        || logical.carrier().offset_bits() != 0
        || logical.carrier().size_bits() != width_bits
    {
        return None;
    }
    let source_type = interface
        .type_graph()?
        .types()
        .get(usize::try_from(logical.type_id()).ok()?)?;
    (source_type.kind() == SourceTypeKind::SignedInteger
        && source_type.size_bits() == width_bits
        && source_type.align_bits() == width_bits)
        .then_some(stored_value)
}

fn private_low_parameter_entry_value(
    graph: &SsaGraph,
    machine: &SourceMachineContext,
    parameter_index: u32,
    parameter_storage: CanonicalStorageId,
    home_width: u32,
) -> Option<ValueId> {
    if parameter_storage.space != CanonicalStorageSpace::Register
        || home_width >= parameter_storage.size
    {
        return None;
    }
    let low_storage = CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset: parameter_storage.offset,
        size: home_width,
    };
    let low_value = entry_value(graph, machine, low_storage)?;
    let interface = machine.function_interface()?;
    let logical = *interface
        .parameter_logical_values()
        .get(usize::try_from(parameter_index).ok()?)?;
    let width_bits = u64::from(home_width).checked_mul(8)?;
    let source_type = interface
        .type_graph()?
        .types()
        .get(usize::try_from(logical.type_id()).ok()?)?;
    (is_entry_value(graph, low_value)
        && logical.carrier().kind() == SourceCarrierKind::LowBits
        && logical.carrier().offset_bits() == 0
        && logical.carrier().size_bits() == width_bits
        && source_type.kind() == SourceTypeKind::SignedInteger
        && source_type.size_bits() == width_bits
        && source_type.align_bits() == width_bits)
        .then_some(low_value)
}

#[allow(clippy::too_many_arguments)]
fn collect_home(
    function: &SSAFunction,
    graph: &SsaGraph,
    facts: &PreparedFunctionFacts,
    machine: &SourceMachineContext,
    declaration: SlotDeclaration,
    parameter_index: u32,
    parameter_storage: CanonicalStorageId,
    abi_parameter_value: ValueId,
    saved_alias_object: ObjectId,
    after: InstId,
    before: InstId,
) -> Option<PrivateFrameHomeFact> {
    let object = unique_declared_object(&facts.objects, declaration)?;
    let accesses = facts
        .structured
        .memory_accesses
        .values()
        .filter(|access| access.object == object)
        .collect::<Vec<_>>();
    let [first, second] = accesses.as_slice() else {
        return None;
    };
    let (init, reload) = match (first.is_write, second.is_write) {
        (true, false) => (*first, *second),
        (false, true) => (*second, *first),
        _ => return None,
    };
    let parameter_value = private_home_parameter_value(
        graph,
        machine,
        parameter_index,
        parameter_storage,
        abi_parameter_value,
        declaration.width,
        init.value?,
    )?;
    if !memory_access_locations_are_exact(facts, init)
        || !memory_access_locations_are_exact(facts, reload)
    {
        return None;
    }
    let init_defs = facts.memory.defs_by_inst.get(&init.id.inst)?;
    let init_versions = init_defs
        .iter()
        .map(|def| def.next_version)
        .collect::<BTreeSet<_>>();
    let mut init_versions = init_versions.into_iter();
    let init_memory_version = init_versions.next()?;
    if init_versions.next().is_some() {
        return None;
    }
    let reload_uses = facts.memory.uses_by_inst.get(&reload.id.inst)?;
    let previous_alias_objects = init_defs
        .iter()
        .map(|def| def.previous_version.object)
        .collect::<BTreeSet<_>>();
    if init.value != Some(parameter_value)
        || previous_alias_objects != BTreeSet::from([saved_alias_object])
        || reload_uses.len() != 1
        || reload_uses[0].version != init_memory_version
        || reload_uses
            .iter()
            .map(|use_fact| use_fact.version.object)
            .collect::<BTreeSet<_>>()
            != BTreeSet::from([object])
        || reload_uses
            .iter()
            .any(|use_fact| use_fact.version.version == 0)
        || !site_precedes(function, graph, after, init.id.inst)
        || !site_order(graph, init.id.inst, reload.id.inst)
        || !site_precedes(function, graph, reload.id.inst, before)
    {
        return None;
    }
    Some(PrivateFrameHomeFact {
        object,
        base: declaration.base,
        offset: declaration.offset,
        width: declaration.width,
        parameter_index,
        parameter_storage,
        abi_parameter_value,
        parameter_value,
        init_store: init.id,
        init_memory_version,
        init_memory_defs: init_defs.clone().into_boxed_slice(),
        reloads: vec![PrivateFrameHomeReloadFact {
            access: reload.id,
            value: reload.value?,
            memory_version: init_memory_version,
            memory_uses: reload_uses.clone().into_boxed_slice(),
        }],
    })
}

fn private_frame_return_transform(
    graph: &SsaGraph,
    _machine: &SourceMachineContext,
    loaded_value: ValueId,
    returned_value: ValueId,
    return_storage: CanonicalStorageId,
) -> Option<(Box<[InstId]>, Box<[InstId]>)> {
    if loaded_value == returned_value {
        return Some((Box::new([]), Box::new([])));
    }
    let returned = graph.value(returned_value)?;
    if returned.canonical_storage != Some(return_storage) {
        return None;
    }
    let mut current = returned_value;
    let mut reverse = Vec::new();
    while current != loaded_value && reverse.len() < 2 {
        let inst_id = graph.def_inst(current)?;
        let inst = graph.inst(inst_id)?;
        if inst.output != Some(current) {
            return None;
        }
        let input = match &inst.payload {
            InstPayload::Op(SSAOp::Copy { src, .. })
            | InstPayload::Op(SSAOp::IntZExt { src, .. }) => graph.value_id_for_var(src)?,
            InstPayload::Op(_) | InstPayload::Phi { .. } => return None,
        };
        reverse.push(inst_id);
        current = input;
    }
    if current != loaded_value {
        return None;
    }
    reverse.reverse();
    let mut relays = Vec::new();
    if let [zext] = reverse.as_slice()
        && matches!(
            graph.inst(*zext)?.payload,
            InstPayload::Op(SSAOp::IntZExt { .. })
        )
    {
        let mut copies = graph.use_sites(loaded_value).iter().filter_map(|use_site| {
            if use_site.inst == *zext || use_site.input_idx != 0 {
                return None;
            }
            let instruction = graph.inst(use_site.inst)?;
            let InstPayload::Op(SSAOp::Copy { .. }) = &instruction.payload else {
                return None;
            };
            let output = instruction.output?;
            (graph.value(output)?.var.size == graph.value(loaded_value)?.var.size
                && graph.use_sites(output).is_empty()
                && site_order(graph, use_site.inst, *zext))
            .then_some(use_site.inst)
        });
        if let Some(copy) = copies.next() {
            if copies.next().is_some() {
                return None;
            }
            relays.push(copy);
        }
    }
    let widths = std::iter::once(loaded_value)
        .chain(reverse.iter().filter_map(|inst| graph.inst(*inst)?.output))
        .map(|value| graph.value(value).map(|value| value.var.size))
        .collect::<Option<Vec<_>>>()?;
    let exact_shape = match reverse.as_slice() {
        [only] => match &graph.inst(*only)?.payload {
            InstPayload::Op(SSAOp::Copy { .. }) => widths[0] == widths[1],
            InstPayload::Op(SSAOp::IntZExt { .. }) => widths[0] < widths[1],
            _ => false,
        },
        [copy, zext] => {
            matches!(
                graph.inst(*copy)?.payload,
                InstPayload::Op(SSAOp::Copy { .. })
            ) && matches!(
                graph.inst(*zext)?.payload,
                InstPayload::Op(SSAOp::IntZExt { .. })
            ) && widths[0] == widths[1]
                && widths[1] < widths[2]
        }
        [] | [_, _, ..] => false,
    };
    let transform_uses_are_exact = reverse.iter().enumerate().all(|(index, inst)| {
        let input = if index == 0 {
            loaded_value
        } else {
            graph
                .inst(reverse[index - 1])
                .and_then(|previous| previous.output)
                .unwrap_or(ValueId(u32::MAX))
        };
        graph.use_sites(input)
            != [crate::graph::UseSite {
                inst: *inst,
                input_idx: 0,
            }]
    });
    let relay_uses_are_exact = match relays.as_slice() {
        [] => transform_uses_are_exact,
        [copy] => {
            let [transform] = reverse.as_slice() else {
                return None;
            };
            graph.use_sites(loaded_value)
                == [
                    crate::graph::UseSite {
                        inst: *copy,
                        input_idx: 0,
                    },
                    crate::graph::UseSite {
                        inst: *transform,
                        input_idx: 0,
                    },
                ]
        }
        [_, _, ..] => false,
    };
    if !exact_shape || !relay_uses_are_exact {
        return None;
    }
    Some((relays.into_boxed_slice(), reverse.into_boxed_slice()))
}

fn collect_local(
    function: &SSAFunction,
    graph: &SsaGraph,
    facts: &PreparedFunctionFacts,
    machine: &SourceMachineContext,
    declaration: SlotDeclaration,
    home_reload_value: ValueId,
    return_inst: InstId,
    before: InstId,
) -> Option<PrivateFrameLocalFact> {
    let object = unique_declared_object(&facts.objects, declaration)?;
    let mut access_facts = facts
        .structured
        .memory_accesses
        .values()
        .filter(|access| access.object == object)
        .collect::<Vec<_>>();
    if access_facts.len() != 3
        || access_facts
            .iter()
            .any(|access| !memory_access_locations_are_exact(facts, access))
    {
        return None;
    }
    access_facts.sort_by_key(|access| access.id);
    let accesses = access_facts.iter().map(|access| access.id).collect();
    let access_memory = access_facts
        .iter()
        .map(|access| PrivateFrameAccessMemoryFact {
            access: access.id,
            memory_defs: facts
                .memory
                .defs_by_inst
                .get(&access.id.inst)
                .cloned()
                .unwrap_or_default()
                .into_boxed_slice(),
            memory_uses: facts
                .memory
                .uses_by_inst
                .get(&access.id.inst)
                .cloned()
                .unwrap_or_default()
                .into_boxed_slice(),
        })
        .collect();
    let mut predicates = facts.predicates.predicates.values();
    let predicate = predicates.next()?;
    if predicates.next().is_some() || predicate.block_addr != function.entry {
        return None;
    }
    let comparison = predicate
        .comparison
        .as_ref()
        .or(predicate.evaluated_comparison.as_ref())?;
    if comparison.lhs != home_reload_value && comparison.rhs != home_reload_value {
        return None;
    }
    let mut true_stores = access_facts
        .iter()
        .copied()
        .filter(|access| access.is_write && access.block_addr == predicate.true_target);
    let true_store = true_stores.next()?;
    if true_stores.next().is_some() {
        return None;
    }
    let mut false_stores = access_facts
        .iter()
        .copied()
        .filter(|access| access.is_write && access.block_addr == predicate.false_target);
    let false_store = false_stores.next()?;
    if false_stores.next().is_some() {
        return None;
    }
    let true_value = true_store.value?;
    let false_value = false_store.value?;
    if graph.value(true_value)?.var.constant_bits() != Some(1)
        || graph.value(false_value)?.var.constant_bits() != Some(0)
    {
        return None;
    }
    let mut loads = access_facts
        .iter()
        .copied()
        .filter(|access| !access.is_write);
    let load = loads.next()?;
    if loads.next().is_some() {
        return None;
    }
    let loaded_value = load.value?;
    let true_successors = function.successors(predicate.true_target);
    let false_successors = function.successors(predicate.false_target);
    let ([join_block], [other_join]) = (true_successors.as_slice(), false_successors.as_slice())
    else {
        return None;
    };
    let mut join_predecessors = function.predecessors(*join_block);
    join_predecessors.sort_unstable();
    let mut expected_predecessors = vec![predicate.true_target, predicate.false_target];
    expected_predecessors.sort_unstable();
    let expected_blocks = BTreeSet::from([
        predicate.block_addr,
        predicate.true_target,
        predicate.false_target,
        *join_block,
    ]);
    if join_block != other_join
        || load.block_addr != *join_block
        || join_predecessors != expected_predecessors
        || function
            .block_addrs()
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            != expected_blocks
        || !site_order(graph, load.id.inst, before)
    {
        return None;
    }
    let return_boundary = facts.boundaries.returns.get(&return_inst)?;
    let [return_carrier] = return_boundary.values.as_slice() else {
        return None;
    };
    let crate::semantic::CallBoundarySlot::Register {
        index: 0,
        storage: return_storage,
    } = return_carrier.slot
    else {
        return None;
    };
    if !return_boundary.complete {
        return None;
    }
    let (return_relay_insts, return_transform_insts) = private_frame_return_transform(
        graph,
        machine,
        loaded_value,
        return_carrier.value,
        return_storage,
    )?;
    let funnels = facts
        .structured
        .conditional_return_funnels
        .values()
        .filter_map(|funnel| match &funnel.carrier {
            crate::ConditionalReturnCarrierFact::PrivateStackSlot(slot)
                if slot.object == object =>
            {
                Some(funnel.predicate)
            }
            crate::ConditionalReturnCarrierFact::RegisterPhi(_)
            | crate::ConditionalReturnCarrierFact::PrivateStackSlot(_) => None,
        })
        .collect::<Vec<_>>();
    let conditional_funnel = match funnels.as_slice() {
        [] => None,
        [predicate] => Some(*predicate),
        [_, _, ..] => return None,
    };
    Some(PrivateFrameLocalFact {
        object,
        base: declaration.base,
        offset: declaration.offset,
        width: declaration.width,
        accesses,
        access_memory,
        predicate: predicate.id,
        branch_block: predicate.block_addr,
        true_target: predicate.true_target,
        false_target: predicate.false_target,
        true_store: true_store.id,
        true_value,
        false_store: false_store.id,
        false_value,
        true_producer: predicate.true_target,
        false_producer: predicate.false_target,
        join_block: *join_block,
        join_load: load.id,
        loaded_value,
        return_inst,
        return_storage,
        return_value: return_carrier.value,
        return_relay_insts,
        return_transform_insts,
        conditional_funnel,
    })
}

fn unique_declared_object(objects: &ObjectModel, declaration: SlotDeclaration) -> Option<ObjectId> {
    let mut matches = objects.objects.values().filter(|object| {
        matches!(
            object.kind,
            ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset }
                if base == declaration.base && offset == declaration.offset
        )
    });
    let object = matches.next()?.id;
    matches.next().is_none().then_some(object)
}

fn unique_return_target(
    graph: &SsaGraph,
    function: &SSAFunction,
) -> Option<(ValueId, InstId, u64)> {
    let mut returns = graph.insts.iter().filter_map(|inst| {
        let InstPayload::Op(SSAOp::Return {
            target: return_target,
        }) = &inst.payload
        else {
            return None;
        };
        let target = graph.value_id_for_var(return_target)?;
        graph
            .block(inst.block)
            .map(|block| (target, inst.id, block.addr))
    });
    let result = returns.next()?;
    if returns.next().is_some()
        || !function.successors(result.2).is_empty()
        || graph
            .insts
            .iter()
            .filter(|inst| matches!(inst.payload, InstPayload::Op(SSAOp::Return { .. })))
            .count()
            != 1
    {
        return None;
    }
    Some(result)
}

fn site_order(graph: &SsaGraph, before: InstId, after: InstId) -> bool {
    let Some((before_block, before_index)) = graph.op_site_for_inst(before) else {
        return false;
    };
    let Some((after_block, after_index)) = graph.op_site_for_inst(after) else {
        return false;
    };
    before_block == after_block && before_index < after_index
}

fn site_precedes(function: &SSAFunction, graph: &SsaGraph, before: InstId, after: InstId) -> bool {
    let Some((before_block, before_index)) = graph.op_site_for_inst(before) else {
        return false;
    };
    let Some((after_block, after_index)) = graph.op_site_for_inst(after) else {
        return false;
    };
    if before_block == after_block {
        before_index < after_index
    } else {
        function.dominates(before_block, after_block)
    }
}

fn object_physical_start(objects: &ObjectModel, object: ObjectId) -> Option<i64> {
    match objects.object(object)?.kind {
        ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
            physical_slot_start(base, offset)
        }
        ObjectKind::Parameter { .. }
        | ObjectKind::Global { .. }
        | ObjectKind::HeapAlloc { .. }
        | ObjectKind::EscapedUnknown => None,
    }
}

fn all_memory_is_exact_private_frame(
    facts: &PreparedFunctionFacts,
    envelope: [(StructuredAccessId, i64, u32); 3],
    home: &PrivateFrameHomeFact,
    local: &PrivateFrameLocalFact,
) -> bool {
    let mut expected = envelope.into_iter().collect::<Vec<_>>();
    expected.push((
        home.init_store,
        physical_slot_start(home.base, home.offset).unwrap_or(i64::MAX),
        home.width,
    ));
    expected.extend(home.reloads.iter().map(|reload| {
        (
            reload.access,
            physical_slot_start(home.base, home.offset).unwrap_or(i64::MAX),
            home.width,
        )
    }));
    expected.extend(local.accesses.iter().map(|access| {
        (
            *access,
            physical_slot_start(local.base, local.offset).unwrap_or(i64::MAX),
            local.width,
        )
    }));
    if expected.len() != facts.structured.memory_accesses.len() {
        return false;
    }
    facts.structured.memory_accesses.values().all(|access| {
        let Some(start) = object_physical_start(&facts.objects, access.object) else {
            return false;
        };
        expected
            .iter()
            .find(|(id, _, _)| *id == access.id)
            .is_some_and(|(_, expected_start, width)| {
                *expected_start == start
                    && *width == access.width
                    && memory_access_locations_are_exact(facts, access)
            })
    })
}

fn memory_access_locations_are_exact(
    facts: &PreparedFunctionFacts,
    access: &StructuredMemoryAccessFact,
) -> bool {
    if access.is_write {
        facts
            .memory
            .defs_by_inst
            .get(&access.id.inst)
            .is_some_and(|defs| {
                !defs.is_empty()
                    && defs.iter().all(|def| {
                        def.location.object == access.object
                            && def.location.address == RelativeMemoryAddress::Exact(0)
                            && def.location.size == access.width
                    })
            })
    } else {
        facts
            .memory
            .uses_by_inst
            .get(&access.id.inst)
            .is_some_and(|uses| {
                !uses.is_empty()
                    && uses.iter().all(|use_fact| {
                        use_fact.location.object == access.object
                            && use_fact.location.address == RelativeMemoryAddress::Exact(0)
                            && use_fact.location.size == access.width
                    })
            })
    }
}

fn all_memory_versions_are_known(
    facts: &PreparedFunctionFacts,
    known_objects: &BTreeSet<ObjectId>,
) -> bool {
    facts.memory.defs_by_inst.values().flatten().all(|def| {
        known_objects.contains(&def.previous_version.object)
            && known_objects.contains(&def.next_version.object)
    }) && facts
        .memory
        .uses_by_inst
        .values()
        .flatten()
        .all(|use_fact| {
            use_fact.version.version > 0 && known_objects.contains(&use_fact.version.object)
        })
}

fn object_addresses_are_confined(
    graph: &SsaGraph,
    objects: &ObjectModel,
    object: ObjectId,
    allowed_accesses: &BTreeSet<InstId>,
) -> bool {
    objects
        .value_objects
        .iter()
        .filter(|(_, candidate)| **candidate == object)
        .all(|(value, _)| {
            graph.use_sites(*value).iter().all(|use_site| {
                (allowed_accesses.contains(&use_site.inst)
                    && use_site.input_idx == 0
                    && graph.inst(use_site.inst).is_some_and(|inst| {
                        matches!(
                            inst.payload,
                            InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. })
                        )
                    }))
                    || graph.inst(use_site.inst).is_some_and(|inst| {
                        matches!(inst.payload, InstPayload::Phi { .. })
                            && inst
                                .output
                                .is_some_and(|output| graph.use_sites(output).is_empty())
                    })
            })
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine_context::{
        SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn, SourceStackSlotSpec,
    };
    use crate::{CanonicalStorageSpace, SsaArtifact};
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    const REVISION: &[u8] = b"check-secret-private-frame-v1";

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("eax", 0, 4));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("edi", 8, 4));
        arch.add_register(RegisterDef::new("rsp", 16, 8));
        arch.add_register(RegisterDef::new("rbp", 24, 8));
        arch.add_register(RegisterDef::new("rip", 32, 8));
        arch
    }

    fn interface() -> SourceFunctionInterface {
        interface_with_slots(true, slots())
    }

    fn slots() -> Vec<SourceStackSlotSpec> {
        vec![
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(24, 8),
                -8,
                4,
                0,
                storage(8, 4),
            ),
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, storage(24, 8), -4, 4),
        ]
    }

    fn interface_with_slots(
        exact_roles: bool,
        slots: Vec<SourceStackSlotSpec>,
    ) -> SourceFunctionInterface {
        let parameters = [SourceAbiParameterSpec::new(0, storage(8, 4))];
        let return_kind = SourceFunctionReturn::Register {
            storage: storage(0, 4),
        };
        let interface = if exact_roles {
            SourceFunctionInterface::new_exact(
                REVISION.to_vec(),
                "sysv",
                parameters,
                return_kind,
                slots,
            )
            .expect("exact check_secret interface")
        } else {
            SourceFunctionInterface::new(REVISION.to_vec(), "sysv", parameters, return_kind, slots)
                .expect("compatible check_secret interface")
        };
        interface
            .with_return_address_storage(storage(32, 8))
            .expect("check_secret return-address storage")
    }

    fn frame_address(unique: u64, offset: i64) -> (R2ILOp, Varnode) {
        let address = Varnode::unique(unique, 8);
        (
            R2ILOp::IntAdd {
                dst: address.clone(),
                a: Varnode::register(24, 8),
                b: Varnode::constant(offset as u64, 8),
            },
            address,
        )
    }

    fn blocks() -> Vec<R2ILBlock> {
        let mut entry = R2ILBlock::new(0x1000, 0x10);
        let saved_fp = Varnode::unique(0x10, 8);
        entry.push(R2ILOp::Copy {
            dst: saved_fp.clone(),
            src: Varnode::register(24, 8),
        });
        entry.push(R2ILOp::IntSub {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
            val: saved_fp,
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: Varnode::register(16, 8),
        });
        let (home_address_op, home_address) = frame_address(0x20, -8);
        entry.push(home_address_op);
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: home_address.clone(),
            val: Varnode::register(8, 4),
        });
        let home_value = Varnode::unique(0x28, 4);
        entry.push(R2ILOp::Load {
            dst: home_value.clone(),
            space: SpaceId::Ram,
            addr: home_address,
        });
        let condition = Varnode::unique(0x30, 1);
        entry.push(R2ILOp::IntEqual {
            dst: condition.clone(),
            a: home_value,
            b: Varnode::constant(0x5ec2e7, 4),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x1020, 8),
            cond: condition,
        });

        let mut false_arm = R2ILBlock::new(0x1010, 0x10);
        let (false_address_op, false_address) = frame_address(0x40, -4);
        false_arm.push(false_address_op);
        false_arm.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: false_address,
            val: Varnode::constant(0, 4),
        });
        false_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });

        let mut true_arm = R2ILBlock::new(0x1020, 0x10);
        let (true_address_op, true_address) = frame_address(0x50, -4);
        true_arm.push(true_address_op);
        true_arm.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: true_address,
            val: Varnode::constant(1, 4),
        });
        true_arm.push(R2ILOp::Branch {
            target: Varnode::ram(0x1030, 8),
        });

        let mut join = R2ILBlock::new(0x1030, 0x10);
        let (local_address_op, local_address) = frame_address(0x60, -4);
        join.push(local_address_op);
        join.push(R2ILOp::Load {
            dst: Varnode::register(0, 4),
            space: SpaceId::Ram,
            addr: local_address,
        });
        let restored_fp = Varnode::unique(0x70, 8);
        join.push(R2ILOp::Load {
            dst: restored_fp.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        join.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: restored_fp,
        });
        join.push(R2ILOp::Load {
            dst: Varnode::register(32, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        join.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        join.push(R2ILOp::Return {
            target: Varnode::register(32, 8),
        });

        vec![entry, false_arm, true_arm, join]
    }

    fn artifact() -> SsaArtifact {
        SsaArtifact::for_decompile_with_interface(&blocks(), Some(&arch()), interface())
            .expect("full check_secret artifact")
    }

    fn assert_rejected(
        blocks: Vec<R2ILBlock>,
        arch: ArchSpec,
        interface: SourceFunctionInterface,
        boundary: &str,
    ) {
        let artifact = SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .unwrap_or_else(|| panic!("{boundary}: full artifact must still build"));
        assert!(
            artifact.private_frame().is_none(),
            "{boundary}: mutation must fail closed"
        );
    }

    #[test]
    fn retains_exact_revision_bound_private_frame_and_home_fact() {
        let artifact = artifact();
        let fact = artifact
            .private_frame()
            .expect("exact private frame source fact");

        assert_eq!(fact.schema_version, PRIVATE_FRAME_FACT_SCHEMA_VERSION);
        assert_eq!(&*fact.revision_identity, REVISION);
        assert_eq!(fact.entry_block, 0x1000);
        assert_eq!(fact.exit_block, 0x1030);
        assert_eq!(fact.pointer_width_bytes, 8);
        assert_eq!(fact.entry_sp_storage, storage(16, 8));
        assert_eq!(fact.entry_fp_storage, storage(24, 8));
        assert_eq!(fact.entry_pc_storage, storage(32, 8));
        assert_eq!(fact.push.delta, -8);
        assert_eq!(fact.pop.delta, 8);
        assert_eq!(fact.return_advance.delta, 8);
        assert_eq!(fact.push.output, fact.pop.input);
        assert_eq!(fact.pop.output, fact.return_advance.input);
        assert_eq!(fact.saved_frame_pointer.capture.input, fact.entry_fp);
        assert_eq!(
            fact.saved_frame_pointer.capture.output,
            fact.saved_frame_pointer.stored_value
        );
        assert_eq!(fact.home.parameter_index, 0);
        assert_eq!(fact.home.parameter_storage, storage(8, 4));
        assert_eq!(fact.home.reloads.len(), 1);
        assert_eq!(
            fact.home.init_memory_version,
            fact.home.reloads[0].memory_version
        );
        assert_eq!(fact.home.reloads[0].memory_uses.len(), 1);
        assert_eq!(fact.saved_frame_pointer.load_memory_uses.len(), 2);
        assert_eq!(fact.return_address.memory_uses.len(), 2);
        assert!(fact.local.conditional_funnel.is_none());
        assert_eq!(fact.local.accesses.len(), 3);
        assert_eq!(fact.local.access_memory.len(), 3);
        assert_eq!(fact.saved_frame_pointer_range.start_from_entry_sp, -8);
        assert_eq!(fact.home_range.start_from_entry_sp, -16);
        assert_eq!(fact.local_range.start_from_entry_sp, -12);
        assert_eq!(fact.return_address_range.start_from_entry_sp, 0);
        assert!(
            artifact
                .graph()
                .inst(fact.return_address.return_inst)
                .is_some()
        );
        assert!(
            artifact
                .facts()
                .structured
                .memory_accesses
                .contains_key(&fact.return_address.load)
        );
    }

    #[test]
    fn derives_one_hidden_private_result_carrier_without_a_source_local() {
        let mut declared = slots();
        declared.pop();
        let artifact = SsaArtifact::for_decompile_with_interface(
            &blocks(),
            Some(&arch()),
            interface_with_slots(true, declared),
        )
        .expect("artifact with only the declared parameter home");
        let fact = artifact
            .private_frame()
            .expect("structurally private hidden result carrier");
        assert_eq!(fact.home.offset, -8);
        assert_eq!(fact.local.offset, -4);
        assert_eq!(fact.local.width, 4);
        assert_eq!(fact.local.accesses.len(), 3);
    }

    #[test]
    fn rejects_envelope_identity_delta_order_storage_and_control_mutations() {
        let mut mutated = blocks();
        mutated[0].ops[0] = R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(0, 8),
        };
        assert_rejected(mutated, arch(), interface(), "saved-FP identity");

        let mut mutated = blocks();
        mutated[0].ops[1] = R2ILOp::IntSub {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(16, 8),
        };
        assert_rejected(mutated, arch(), interface(), "PUSH delta");

        let mut mutated = blocks();
        mutated[0].ops.swap(2, 3);
        assert_rejected(mutated, arch(), interface(), "prologue order");

        let mismatched_fp = vec![
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(0, 8),
                -8,
                4,
                0,
                storage(8, 4),
            ),
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, storage(0, 8), -4, 4),
        ];
        assert_rejected(
            blocks(),
            arch(),
            interface_with_slots(true, mismatched_fp),
            "FP storage",
        );

        let mut mutated = blocks();
        mutated[3].ops[3] = R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(16, 8),
        };
        assert_rejected(mutated, arch(), interface(), "POP delta");

        let mut mutated = blocks();
        mutated[3].ops[6] = R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(16, 8),
        };
        assert_rejected(mutated, arch(), interface(), "RET delta");

        let mut mutated = blocks();
        let unbound_pc = Varnode::unique(0x90, 8);
        mutated[3].ops[5] = R2ILOp::Load {
            dst: unbound_pc.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        };
        mutated[3].ops[7] = R2ILOp::Return { target: unbound_pc };
        assert_rejected(mutated, arch(), interface(), "PC storage");

        let mut mutated = blocks();
        mutated[3].ops[7] = R2ILOp::Return {
            target: Varnode::register(0, 8),
        };
        assert_rejected(mutated, arch(), interface(), "return control identity");

        let mut mutated = blocks();
        mutated[3].ops[4] = R2ILOp::Copy {
            dst: Varnode::register(24, 8),
            src: Varnode::register(0, 8),
        };
        assert_rejected(mutated, arch(), interface(), "saved-FP restore identity");
    }

    #[test]
    fn rejects_home_access_alias_clobber_role_and_provenance_mutations() {
        let mut mutated = blocks();
        mutated[0].ops[5] = R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x20, 8),
            val: Varnode::register(0, 4),
        };
        assert_rejected(mutated, arch(), interface(), "Home parameter identity");

        let mut mutated = blocks();
        mutated[0].ops.insert(
            7,
            R2ILOp::Load {
                dst: Varnode::unique(0x98, 4),
                space: SpaceId::Ram,
                addr: Varnode::unique(0x20, 8),
            },
        );
        assert_rejected(mutated, arch(), interface(), "extra Home access");

        let mut mutated = blocks();
        mutated[0].ops.insert(
            6,
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x20, 8),
                val: Varnode::constant(7, 4),
            },
        );
        assert_rejected(mutated, arch(), interface(), "Home clobber/version");

        let mut mutated = blocks();
        mutated[0].ops.swap(5, 6);
        assert_rejected(mutated, arch(), interface(), "Home init/reload order");

        assert_rejected(
            blocks(),
            arch(),
            interface_with_slots(false, slots()),
            "incomplete roles",
        );

        let role_mismatch = vec![
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, storage(24, 8), -8, 4),
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, storage(24, 8), -4, 4),
        ];
        assert_rejected(
            blocks(),
            arch(),
            interface_with_slots(true, role_mismatch),
            "Home role",
        );

        let aliased_bases = vec![
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(24, 8),
                -8,
                4,
                0,
                storage(8, 4),
            ),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, storage(16, 8), -16, 4),
        ];
        assert_rejected(
            blocks(),
            arch(),
            interface_with_slots(true, aliased_bases),
            "overlapping FP/SP declarations",
        );

        let mut mutated = blocks();
        mutated[0].ops[4] = R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(24, 8),
            b: Varnode::register(8, 8),
        };
        assert_rejected(mutated, arch(), interface(), "dynamic Home provenance");
    }

    #[test]
    fn rejects_escape_extra_access_call_and_revision_mutations() {
        let mut mutated = blocks();
        mutated[3].ops.insert(
            3,
            R2ILOp::Load {
                dst: Varnode::unique(0xa0, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(16, 8),
            },
        );
        assert_rejected(
            mutated,
            arch(),
            interface(),
            "extra envelope address access",
        );

        let mut mutated = blocks();
        mutated[0].ops.insert(
            8,
            R2ILOp::Call {
                target: Varnode::ram(0x2000, 8),
            },
        );
        assert_rejected(mutated, arch(), interface(), "call boundary");

        let artifact = artifact();
        assert!(
            collect_private_frame_fact(
                artifact.mode(),
                artifact.function(),
                artifact.graph(),
                artifact.facts(),
                artifact.machine_context(),
                b"stale-check-secret-revision",
            )
            .is_none(),
            "source revision identity must remain exact"
        );
    }

    #[test]
    fn rejects_local_kind_value_topology_return_and_live_phi_mutations() {
        let mut mutated = blocks();
        mutated[1].ops[1] = R2ILOp::Load {
            dst: Varnode::unique(0xb0, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x40, 8),
        };
        assert_rejected(mutated, arch(), interface(), "Local access kind");

        let mut mutated = blocks();
        mutated[2].ops[1] = R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x50, 8),
            val: Varnode::constant(2, 4),
        };
        assert_rejected(mutated, arch(), interface(), "Local true value");

        let mut mutated = blocks();
        mutated[1].ops[2] = R2ILOp::Branch {
            target: Varnode::ram(0x1020, 8),
        };
        assert_rejected(mutated, arch(), interface(), "Local diamond topology");

        let mut mutated = blocks();
        let indirect_return_value = Varnode::unique(0xc0, 4);
        mutated[3].ops[1] = R2ILOp::Load {
            dst: indirect_return_value.clone(),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x60, 8),
        };
        mutated[3].ops.insert(
            2,
            R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(0, 4),
            },
        );
        assert_rejected(
            mutated,
            arch(),
            interface(),
            "Local loaded ABI return value",
        );

        let mut mutated = blocks();
        mutated[3].ops.insert(
            0,
            R2ILOp::Copy {
                dst: Varnode::unique(0xd0, 8),
                src: Varnode::unique(0x40, 8),
            },
        );
        assert_rejected(mutated, arch(), interface(), "live Local address phi");

        let mut mutated = blocks();
        mutated[3].ops.swap(4, 5);
        assert_rejected(mutated, arch(), interface(), "epilogue restore/load order");

        let wide_return_interface = SourceFunctionInterface::new_exact(
            REVISION.to_vec(),
            "sysv",
            [SourceAbiParameterSpec::new(0, storage(8, 4))],
            SourceFunctionReturn::Register {
                storage: storage(0, 8),
            },
            slots(),
        )
        .expect("wide-return mutation interface");
        assert_rejected(
            blocks(),
            arch(),
            wide_return_interface,
            "Local ABI return storage",
        );

        let mut narrow_pointer_arch = arch();
        narrow_pointer_arch.addr_size = 4;
        assert_rejected(blocks(), narrow_pointer_arch, interface(), "pointer width");
    }
}
