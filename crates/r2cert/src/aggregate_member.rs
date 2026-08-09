//! Sealed source-layout evidence for exact aggregate member accesses.
//!
//! This module does not authorize C rendering. It only joins immutable source
//! type authority with the already-certified machine memory statement and its
//! exact source obligation.

use std::collections::BTreeMap;

use r2ssa::{
    AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION, AggregateAccessBinding, AggregateAccessProjection,
    CanonicalInstructionId, MachineAddressSpace, MachineBuildError, MachineValueUse, ObjectId,
    SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SemanticObligationComponent, SemanticObligationId,
    SemanticObligationKind, SourceAggregateLayout, SourceCarrierKind, SourceLogicalValue,
    SourceType, SourceTypeGraph, SourceTypeKind, SsaArtifact, StructuredAccessId, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedAbiParameter, CertifiedArtifactOrigin,
    CertifiedMemoryExecutionPolicy, CertifiedMemoryStatement, CertifiedMemoryStatementKind,
};

pub const CERTIFIED_AGGREGATE_MEMBER_ACCESS_CONTRACT_VERSION: u32 = 1;

/// Complete naturally aligned scalar layout reached through one pointer type.
///
/// `member_types` is in the same order as `aggregate.members()`. Names are
/// retained from the immutable source snapshot but never participate in
/// admission decisions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNaturalScalarAggregateLayout {
    pointer_type: SourceType,
    aggregate_type: SourceType,
    aggregate: SourceAggregateLayout,
    member_types: Box<[SourceType]>,
}

impl CertifiedNaturalScalarAggregateLayout {
    pub const fn pointer_type(&self) -> &SourceType {
        &self.pointer_type
    }

    pub const fn aggregate_type(&self) -> &SourceType {
        &self.aggregate_type
    }

    pub const fn aggregate(&self) -> &SourceAggregateLayout {
        &self.aggregate
    }

    pub const fn member_types(&self) -> &[SourceType] {
        &self.member_types
    }
}

/// Exact structured memory subeffect retained by an aggregate certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateStructuredAccess {
    access: StructuredAccessId,
    block_addr: u64,
    op_index: usize,
    object: ObjectId,
    address: ValueId,
    value: Option<ValueId>,
    is_write: bool,
    width_bytes: u32,
    provenance_complete: bool,
}

impl CertifiedAggregateStructuredAccess {
    pub const fn access(&self) -> StructuredAccessId {
        self.access
    }

    pub const fn block_addr(&self) -> u64 {
        self.block_addr
    }

    pub const fn op_index(&self) -> usize {
        self.op_index
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn address(&self) -> ValueId {
        self.address
    }

    pub const fn value(&self) -> Option<ValueId> {
        self.value
    }

    pub const fn is_write(&self) -> bool {
        self.is_write
    }

    pub const fn width_bytes(&self) -> u32 {
        self.width_bytes
    }

    pub const fn provenance_complete(&self) -> bool {
        self.provenance_complete
    }
}

/// Exact read or write semantics of the retained source operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedAggregateMemberAccessSemantics {
    Read {
        address: ValueId,
        result: MachineValueUse,
    },
    Write {
        address: ValueId,
        value: MachineValueUse,
    },
}

/// Sealed proof that one plain RAM access is exactly one naturally laid-out
/// scalar member of an ABI pointer parameter.
///
/// This is a certification fact, not a [`super::CertifiedRenderPermit`]. A
/// renderer must separately prove a closed typed region before emitting C.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateMemberAccess {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    interface_revision: Box<[u8]>,
    parameter: CertifiedAbiParameter,
    parameter_logical_value: SourceLogicalValue,
    source_type_graph: SourceTypeGraph,
    layout: CertifiedNaturalScalarAggregateLayout,
    projection: AggregateAccessProjection,
    structured_access: CertifiedAggregateStructuredAccess,
    space: MachineAddressSpace,
    semantics: CertifiedAggregateMemberAccessSemantics,
    memory_statement: CertifiedMemoryStatement,
    memory_obligation: SemanticObligationId,
}

impl CertifiedAggregateMemberAccess {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn contract_version(&self) -> u32 {
        self.contract_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn interface_revision(&self) -> &[u8] {
        &self.interface_revision
    }

    pub const fn parameter(&self) -> &CertifiedAbiParameter {
        &self.parameter
    }

    pub const fn parameter_logical_value(&self) -> SourceLogicalValue {
        self.parameter_logical_value
    }

    pub const fn source_type_graph(&self) -> &SourceTypeGraph {
        &self.source_type_graph
    }

    pub const fn layout(&self) -> &CertifiedNaturalScalarAggregateLayout {
        &self.layout
    }

    pub const fn projection(&self) -> &AggregateAccessProjection {
        &self.projection
    }

    pub const fn structured_access(&self) -> &CertifiedAggregateStructuredAccess {
        &self.structured_access
    }

    pub const fn space(&self) -> MachineAddressSpace {
        self.space
    }

    pub const fn semantics(&self) -> &CertifiedAggregateMemberAccessSemantics {
        &self.semantics
    }

    pub const fn memory_statement(&self) -> &CertifiedMemoryStatement {
        &self.memory_statement
    }

    pub const fn memory_obligation(&self) -> SemanticObligationId {
        self.memory_obligation
    }

    pub const fn access(&self) -> StructuredAccessId {
        self.projection.access
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.memory_statement.producer()
    }

    #[cfg(test)]
    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let machine_context = super::CertifiedMachineContext::from_artifact(artifact)?;
        let topology = super::certified_source_topology(artifact)?;
        let origin = super::certified_artifact_origin(artifact, &machine_context, &topology)?;
        let abi_parameters = super::certified_abi_parameters(artifact)?;
        let memory_statements = super::certified_memory_statements(artifact)?;
        let expected = certified_aggregate_member_accesses(
            artifact,
            &origin,
            &abi_parameters,
            &memory_statements,
        )?
        .remove(&self.access())
        .ok_or(MachineBuildError::ObligationMismatch(self.access().inst))?;
        if expected == *self {
            Ok(())
        } else {
            Err(MachineBuildError::ObligationMismatch(self.access().inst))
        }
    }
}

fn source_type(graph: &SourceTypeGraph, type_id: u32) -> Option<&SourceType> {
    usize::try_from(type_id)
        .ok()
        .and_then(|index| graph.types().get(index))
        .filter(|source_type| source_type.id() == type_id)
}

fn source_aggregate(graph: &SourceTypeGraph, aggregate_id: u32) -> Option<&SourceAggregateLayout> {
    usize::try_from(aggregate_id)
        .ok()
        .and_then(|index| graph.aggregates().get(index))
        .filter(|aggregate| aggregate.id() == aggregate_id)
}

fn align_up(value: u64, alignment: u64) -> Option<u64> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return None;
    }
    let mask = alignment - 1;
    value.checked_add(mask).map(|aligned| aligned & !mask)
}

fn certified_natural_scalar_layout(
    graph: &SourceTypeGraph,
    projection: &AggregateAccessProjection,
) -> Option<CertifiedNaturalScalarAggregateLayout> {
    if graph.schema_version() != SOURCE_TYPE_GRAPH_SCHEMA_VERSION {
        return None;
    }
    let pointer_type = source_type(graph, projection.pointer_type_id)?;
    if pointer_type.kind()
        != (SourceTypeKind::Pointer {
            target_type_id: projection.struct_type_id,
        })
    {
        return None;
    }
    let aggregate_type = source_type(graph, projection.struct_type_id)?;
    if aggregate_type.kind()
        != (SourceTypeKind::Struct {
            aggregate_id: projection.aggregate_id,
        })
    {
        return None;
    }
    let aggregate = source_aggregate(graph, projection.aggregate_id)?;
    if aggregate.type_id() != aggregate_type.id()
        || aggregate.size_bits() != aggregate_type.size_bits()
        || aggregate.align_bits() != aggregate_type.align_bits()
        || aggregate.members().is_empty()
    {
        return None;
    }

    let mut member_types = Vec::with_capacity(aggregate.members().len());
    let mut cursor = 0u64;
    let mut maximum_alignment = 0u64;
    for (position, member) in aggregate.members().iter().enumerate() {
        let member_type = source_type(graph, member.type_id())?;
        if u32::try_from(position) != Ok(member.member_id())
            || !matches!(
                member_type.kind(),
                SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger
            )
            || member.size_bits() != member_type.size_bits()
            || align_up(cursor, member_type.align_bits()) != Some(member.offset_bits())
        {
            return None;
        }
        cursor = member.offset_bits().checked_add(member.size_bits())?;
        maximum_alignment = maximum_alignment.max(member_type.align_bits());
        member_types.push(member_type.clone());
    }
    if maximum_alignment != aggregate.align_bits()
        || align_up(cursor, maximum_alignment) != Some(aggregate.size_bits())
    {
        return None;
    }

    let selected = aggregate
        .members()
        .get(usize::try_from(projection.member_id).ok()?)?;
    let selected_type = member_types.get(usize::try_from(projection.member_id).ok()?)?;
    if selected.member_id() != projection.member_id
        || selected.type_id() != projection.member_type_id
        || selected_type.id() != projection.member_type_id
        || selected.offset_bits() != projection.byte_offset.checked_mul(8)?
        || selected.size_bits() != u64::from(projection.byte_width).checked_mul(8)?
    {
        return None;
    }

    Some(CertifiedNaturalScalarAggregateLayout {
        pointer_type: pointer_type.clone(),
        aggregate_type: aggregate_type.clone(),
        aggregate: aggregate.clone(),
        member_types: member_types.into_boxed_slice(),
    })
}

fn try_certified_aggregate_member_access(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    access_key: StructuredAccessId,
    projection: &AggregateAccessProjection,
) -> Result<Option<CertifiedAggregateMemberAccess>, MachineBuildError> {
    let Some(interface) = artifact.machine_context().function_interface() else {
        return Ok(None);
    };
    let Some(type_graph) = interface.type_graph() else {
        return Ok(None);
    };
    if origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || origin.source() != artifact.obligations()
        || origin.machine_context().source() != artifact.machine_context()
        || projection.schema_version != AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION
        || projection.source_revision_identity.as_ref() != interface.revision_identity()
        || projection.access != access_key
        || projection.producer != access_key.inst
    {
        return Ok(None);
    }

    let Some(parameter_index) = usize::try_from(projection.source_parameter_index).ok() else {
        return Ok(None);
    };
    let Some(parameter_spec) = interface.parameters().get(parameter_index) else {
        return Ok(None);
    };
    let Some(parameter) = abi_parameters.get(&projection.source_parameter_index) else {
        return Ok(None);
    };
    let Some(parameter_logical_value) = interface
        .parameter_logical_values()
        .get(parameter_index)
        .copied()
    else {
        return Ok(None);
    };
    if parameter_spec.index() != projection.source_parameter_index
        || parameter.index() != parameter_spec.index()
        || parameter.storage() != parameter_spec.storage()
        || parameter_logical_value.type_id() != projection.pointer_type_id
    {
        return Ok(None);
    }
    let Some(pointer_type) = source_type(type_graph, projection.pointer_type_id) else {
        return Ok(None);
    };
    let carrier = parameter_logical_value.carrier();
    if carrier.kind() != SourceCarrierKind::Full
        || carrier.offset_bits() != 0
        || carrier.size_bits() != pointer_type.size_bits()
        || u64::from(parameter.storage().size).checked_mul(8) != Some(pointer_type.size_bits())
        || parameter.value().is_none()
    {
        return Ok(None);
    }

    let Some(structured) = artifact.structured().memory_accesses.get(&access_key) else {
        return Ok(None);
    };
    let Some(address_expression) = artifact
        .addresses()
        .parameter_expression(structured.address)
    else {
        return Ok(None);
    };
    if structured.id != access_key
        || !structured.provenance_complete
        || structured.width != projection.byte_width
        || artifact
            .machine_context()
            .memory_space_at(structured.block_addr, structured.op_index)
            != Some(r2il::SpaceId::Ram)
        || artifact.graph().op_site_for_inst(access_key.inst)
            != Some((structured.block_addr, structured.op_index))
        || !address_expression.terms.is_empty()
        || address_expression.offset < 0
        || u64::try_from(address_expression.offset) != Ok(projection.byte_offset)
        || u32::try_from(address_expression.parameter) != Ok(projection.source_parameter_index)
        || address_expression.parameter_storage != Some(parameter.storage())
    {
        return Ok(None);
    }

    let Some(source_disposition) = artifact
        .obligations()
        .instruction_for_inst(projection.producer)
    else {
        return Err(MachineBuildError::MissingInstructionDisposition(
            projection.producer,
        ));
    };
    let Some(memory_statement) = memory_statements.get(&source_disposition.id) else {
        return Ok(None);
    };
    let Some(memory_obligation) = memory_statement.source_obligations().iter().next().copied()
    else {
        return Ok(None);
    };
    let Some(width_bits) = projection.byte_width.checked_mul(8) else {
        return Ok(None);
    };
    let expected_obligation_kind = if structured.is_write {
        SemanticObligationKind::ObservableMemoryWrite
    } else {
        SemanticObligationKind::ObservableMemoryRead
    };
    let Some(source_obligation) = artifact.obligations().obligations().get(&memory_obligation)
    else {
        return Ok(None);
    };
    if memory_statement.source_obligations().len() != 1
        || memory_statement.access() != access_key
        || memory_statement.producer() != source_disposition.id
        || memory_statement.object() != structured.object
        || memory_statement.address().binding().value() != structured.address
        || memory_statement.address().memory_access() != Some(access_key)
        || memory_statement.space() != MachineAddressSpace::Ram
        || memory_statement.width_bits() != width_bits
        || memory_statement.execution()
            != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrderViaHelper
        || memory_obligation.instruction != source_disposition.id
        || memory_obligation.kind != expected_obligation_kind
        || memory_obligation.component
            != SemanticObligationComponent::MemoryAccess(access_key.ordinal)
        || source_obligation.source_inst != projection.producer
    {
        return Ok(None);
    }

    let Some(instruction) = artifact.graph().inst(projection.producer) else {
        return Err(MachineBuildError::MissingInstruction(projection.producer));
    };
    let semantics = match (
        &instruction.payload,
        projection.binding,
        memory_statement.kind(),
    ) {
        (
            r2ssa::InstPayload::Op(r2ssa::SSAOp::Load { dst, addr, .. }),
            AggregateAccessBinding::Read { result },
            CertifiedMemoryStatementKind::Read {
                result: certified_result,
            },
        ) if artifact.graph().value_id_for_var(addr) == Some(structured.address)
            && artifact.graph().value_id_for_var(dst) == Some(result)
            && structured.value == Some(result)
            && !structured.is_write
            && instruction.output == Some(result)
            && instruction.inputs.as_slice() == [structured.address]
            && certified_result.binding().value() == result
            && certified_result.producer() == Some(source_disposition.id) =>
        {
            CertifiedAggregateMemberAccessSemantics::Read {
                address: structured.address,
                result: certified_result.clone(),
            }
        }
        (
            r2ssa::InstPayload::Op(r2ssa::SSAOp::Store { addr, val, .. }),
            AggregateAccessBinding::Write { value },
            CertifiedMemoryStatementKind::Write {
                value: certified_value,
            },
        ) if artifact.graph().value_id_for_var(addr) == Some(structured.address)
            && artifact.graph().value_id_for_var(val) == Some(value)
            && structured.value == Some(value)
            && structured.is_write
            && instruction.output.is_none()
            && instruction.inputs.as_slice() == [structured.address, value]
            && certified_value.binding().value() == value =>
        {
            CertifiedAggregateMemberAccessSemantics::Write {
                address: structured.address,
                value: certified_value.clone(),
            }
        }
        _ => return Ok(None),
    };

    let Some(layout) = certified_natural_scalar_layout(type_graph, projection) else {
        return Ok(None);
    };
    Ok(Some(CertifiedAggregateMemberAccess {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_AGGREGATE_MEMBER_ACCESS_CONTRACT_VERSION,
        origin: origin.clone(),
        interface_revision: interface.revision_identity().to_vec().into_boxed_slice(),
        parameter: parameter.clone(),
        parameter_logical_value,
        source_type_graph: type_graph.clone(),
        layout,
        projection: projection.clone(),
        structured_access: CertifiedAggregateStructuredAccess {
            access: structured.id,
            block_addr: structured.block_addr,
            op_index: structured.op_index,
            object: structured.object,
            address: structured.address,
            value: structured.value,
            is_write: structured.is_write,
            width_bytes: structured.width,
            provenance_complete: structured.provenance_complete,
        },
        space: MachineAddressSpace::Ram,
        semantics,
        memory_statement: memory_statement.clone(),
        memory_obligation,
    }))
}

pub(super) fn certified_aggregate_member_accesses(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
) -> Result<BTreeMap<StructuredAccessId, CertifiedAggregateMemberAccess>, MachineBuildError> {
    let facts = artifact.aggregate_accesses();
    if facts.schema_version() != AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION {
        return Ok(BTreeMap::new());
    }
    let Some(interface) = artifact.machine_context().function_interface() else {
        return Ok(BTreeMap::new());
    };
    let Some(projections) = facts.projections_for_revision(interface.revision_identity()) else {
        return Ok(BTreeMap::new());
    };
    let mut certified = BTreeMap::new();
    for (access, projection) in projections {
        let Some(candidate) = try_certified_aggregate_member_access(
            artifact,
            origin,
            abi_parameters,
            memory_statements,
            *access,
            projection,
        )?
        else {
            continue;
        };
        if certified.insert(*access, candidate).is_some() {
            return Err(MachineBuildError::ObligationMismatch(access.inst));
        }
    }
    Ok(certified)
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceAggregateMember,
        SourceCarrierKind, SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn,
        SourceLogicalValue, SourceType, SourceTypeGraph, SsaArtifact,
    };

    use super::*;
    use crate::{CertifiedMachineFunction, CertifiedMachineProjection};

    const REVISION: &[u8] = b"certified-demo-struct-revision";

    fn register_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.alignment = 4;
        arch.add_register(RegisterDef::new("x0", 0, 8));
        arch.add_register(RegisterDef::new("w0", 0, 4));
        arch.add_register(RegisterDef::new("x1", 8, 8));
        arch.add_register(RegisterDef::new("w1", 8, 4));
        arch.add_register(RegisterDef::new("x2", 16, 8));
        arch.add_register(RegisterDef::new("w2", 16, 4));
        arch.add_register(RegisterDef::new("x3", 24, 8));
        arch
    }

    fn demo_struct_graph(member_kind: SourceTypeKind) -> SourceTypeGraph {
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 56 * 8, 32),
                SourceType::new(1, member_kind, 32, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                0,
                56 * 8,
                32,
                "DemoStruct",
                (0..14).map(|index| {
                    SourceAggregateMember::new(
                        index,
                        1,
                        u64::from(index) * 32,
                        32,
                        format!("member_{index}"),
                    )
                }),
            )],
        )
        .expect("valid DemoStruct graph")
    }

    fn wide_demo_struct_graph() -> SourceTypeGraph {
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 56 * 8, 64),
                SourceType::new(1, SourceTypeKind::UnsignedInteger, 64, 64),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                0,
                56 * 8,
                64,
                "WideDemoStruct",
                (0..7).map(|index| {
                    SourceAggregateMember::new(
                        index,
                        1,
                        u64::from(index) * 64,
                        64,
                        format!("wide_member_{index}"),
                    )
                }),
            )],
        )
        .expect("valid wide DemoStruct graph")
    }

    fn interface(
        revision: &[u8],
        pointer_storage: u64,
        graph: SourceTypeGraph,
    ) -> SourceFunctionInterface {
        let scalar = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_with_logical_types(
            revision.to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, register_storage(pointer_storage)),
                SourceAbiParameterSpec::new(1, register_storage(8)),
                SourceAbiParameterSpec::new(2, register_storage(16)),
            ],
            SourceFunctionReturn::Void,
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(1, scalar),
                SourceLogicalValue::new(1, scalar),
            ],
            None,
            Some(graph),
        )
        .expect("valid source interface")
    }

    fn exact_blocks(space: SpaceId) -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x20, 4),
            space,
            addr: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(52, 8),
        });
        block.push(R2ILOp::Store {
            space,
            addr: Varnode::unique(0x30, 8),
            val: Varnode::register(16, 4),
        });
        vec![block]
    }

    fn artifact_with(
        blocks: &[R2ILBlock],
        revision: &[u8],
        pointer_storage: u64,
        graph: SourceTypeGraph,
    ) -> SsaArtifact {
        SsaArtifact::for_decompile_with_interface(
            blocks,
            Some(&arch()),
            interface(revision, pointer_storage, graph),
        )
        .expect("prepared DemoStruct artifact")
    }

    fn artifact() -> SsaArtifact {
        artifact_with(
            &exact_blocks(SpaceId::Ram),
            REVISION,
            0,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        )
    }

    fn access_ids(artifact: &SsaArtifact) -> (StructuredAccessId, StructuredAccessId) {
        let load = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 1)
            .expect("load instruction");
        let store = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 3)
            .expect("store instruction");
        (
            StructuredAccessId {
                inst: load,
                ordinal: 0,
            },
            StructuredAccessId {
                inst: store,
                ordinal: 0,
            },
        )
    }

    #[test]
    fn demo_struct_load_and_store_receive_exact_non_rendering_certificates() {
        let artifact = artifact();
        assert_eq!(artifact.aggregate_accesses().len(), 2);
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified aggregate projection");
        let strict = CertifiedMachineFunction::from_artifact(&artifact)
            .expect("certified aggregate machine function");
        let (load_id, store_id) = access_ids(&artifact);
        let load_producer = artifact
            .obligations()
            .instruction_for_inst(load_id.inst)
            .expect("load disposition")
            .id;
        assert!(
            certified
                .memory_statement_for_producer(load_producer)
                .is_some()
        );
        assert!(
            certified
                .abi_parameters()
                .get(&0)
                .and_then(CertifiedAbiParameter::value)
                .is_some()
        );
        assert_eq!(certified.aggregate_member_accesses().len(), 2);
        assert_eq!(strict.aggregate_member_accesses().len(), 2);

        let load = certified
            .aggregate_member_access(load_id)
            .expect("third-member load certificate");
        assert_eq!(load.schema_version(), CERTIFICATION_SCHEMA_VERSION);
        assert_eq!(
            load.contract_version(),
            CERTIFIED_AGGREGATE_MEMBER_ACCESS_CONTRACT_VERSION
        );
        assert_eq!(load.interface_revision(), REVISION);
        assert_eq!(load.parameter().index(), 0);
        assert_eq!(load.parameter().storage(), register_storage(0));
        assert_eq!(load.parameter_logical_value().type_id(), 2);
        assert_eq!(load.source_type_graph().types().len(), 3);
        assert_eq!(load.layout().aggregate().members().len(), 14);
        assert_eq!(load.layout().member_types().len(), 14);
        assert_eq!(load.projection().member_id, 2);
        assert_eq!(
            (load.projection().byte_offset, load.projection().byte_width),
            (8, 4)
        );
        assert_eq!(load.structured_access().access(), load_id);
        assert!(load.structured_access().provenance_complete());
        assert_eq!(load.space(), MachineAddressSpace::Ram);
        assert!(matches!(
            load.semantics(),
            CertifiedAggregateMemberAccessSemantics::Read { address, result }
                if *address == load.structured_access().address()
                    && result.binding().value()
                        == load.structured_access().value().expect("load result")
        ));
        assert_eq!(load.memory_statement().source_obligations().len(), 1);
        assert!(
            load.memory_statement()
                .source_obligations()
                .contains(&load.memory_obligation())
        );
        load.validate_against_artifact(&artifact)
            .expect("load certificate revalidates");

        let store = certified
            .aggregate_member_access(store_id)
            .expect("fourteenth-member store certificate");
        assert_eq!(store.projection().member_id, 13);
        assert_eq!(
            (
                store.projection().byte_offset,
                store.projection().byte_width
            ),
            (52, 4)
        );
        assert!(matches!(
            store.semantics(),
            CertifiedAggregateMemberAccessSemantics::Write { address, value }
                if *address == store.structured_access().address()
                    && value.binding().value()
                        == store.structured_access().value().expect("stored value")
        ));
        store
            .validate_against_artifact(&artifact)
            .expect("store certificate revalidates");
        assert!(!certified.finish().authorizes_certified_c());
    }

    #[test]
    fn certificate_mutations_break_every_exact_binding() {
        let artifact = artifact();
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified aggregate projection");
        let (load_id, store_id) = access_ids(&artifact);
        let original = certified
            .aggregate_member_access(load_id)
            .expect("load certificate")
            .clone();
        let store = certified
            .aggregate_member_access(store_id)
            .expect("store certificate");
        let assert_invalid = |candidate: &CertifiedAggregateMemberAccess| {
            assert!(candidate.validate_against_artifact(&artifact).is_err());
        };

        let mut mutated = original.clone();
        mutated.schema_version += 1;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.contract_version += 1;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.interface_revision = b"other-revision".to_vec().into_boxed_slice();
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.projection.source_parameter_index = 1;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.parameter = store.parameter().clone();
        mutated.parameter.index = 1;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.parameter.storage = register_storage(8);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.parameter_logical_value = SourceLogicalValue::new(
            1,
            SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32),
        );
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.source_type_graph = demo_struct_graph(SourceTypeKind::UnsignedInteger);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.layout.member_types[0] =
            SourceType::new(1, SourceTypeKind::UnsignedInteger, 32, 32);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        let mut wide_projection = original.projection.clone();
        wide_projection.member_id = 1;
        wide_projection.byte_width = 8;
        mutated.layout =
            certified_natural_scalar_layout(&wide_demo_struct_graph(), &wide_projection)
                .expect("valid alternate natural layout");
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.projection.byte_offset += 4;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.projection.byte_width += 4;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.projection.access.ordinal += 1;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.projection.producer = store_id.inst;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.structured_access.op_index += 1;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.structured_access.is_write = true;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.semantics = store.semantics().clone();
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.projection.binding = AggregateAccessBinding::Write {
            value: original.structured_access.address,
        };
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.structured_access.value = Some(original.structured_access.address);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.space = MachineAddressSpace::Custom(7);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.structured_access.provenance_complete = false;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_statement.object = ObjectId(mutated.memory_statement.object.0 + 1);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        let CertifiedAggregateMemberAccessSemantics::Read { result, .. } = original.semantics()
        else {
            panic!("load semantics expected");
        };
        mutated.memory_statement.address = result.clone();
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_statement.kind = store.memory_statement.kind().clone();
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_obligation = store.memory_obligation();
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_obligation.kind = SemanticObligationKind::ObservableMemoryWrite;
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_obligation.component = SemanticObligationComponent::MemoryAccess(1);
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_obligation.instruction = store.producer();
        assert_invalid(&mutated);
        let mut mutated = original.clone();
        mutated.memory_statement.source_obligations =
            store.memory_statement().source_obligations().clone();
        assert_invalid(&mutated);
        let mut mutated = original;
        mutated.memory_statement = store.memory_statement().clone();
        assert_invalid(&mutated);
    }

    #[test]
    fn changed_source_revision_storage_and_type_graph_do_not_revalidate() {
        let original_artifact = artifact();
        let certified = CertifiedMachineProjection::from_artifact(&original_artifact)
            .expect("certified aggregate projection");
        let (load_id, _) = access_ids(&original_artifact);
        let original = certified
            .aggregate_member_access(load_id)
            .expect("load certificate");

        let different_revision = artifact_with(
            &exact_blocks(SpaceId::Ram),
            b"different-revision",
            0,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        );
        assert!(
            original
                .validate_against_artifact(&different_revision)
                .is_err()
        );
        let different_storage = artifact_with(
            &exact_blocks(SpaceId::Ram),
            REVISION,
            24,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        );
        assert!(
            original
                .validate_against_artifact(&different_storage)
                .is_err()
        );
        let different_type_graph = artifact_with(
            &exact_blocks(SpaceId::Ram),
            REVISION,
            0,
            demo_struct_graph(SourceTypeKind::UnsignedInteger),
        );
        assert!(
            original
                .validate_against_artifact(&different_type_graph)
                .is_err()
        );
    }

    #[test]
    fn dynamic_aliased_wrong_space_and_wrong_width_accesses_remain_uncertified() {
        let mut dynamic = R2ILBlock::new(0x1000, 4);
        dynamic.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x40, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(56, 8),
        });
        dynamic.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x50, 8),
            a: Varnode::register(0, 8),
            b: Varnode::unique(0x40, 8),
        });
        dynamic.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x60, 8),
            a: Varnode::unique(0x50, 8),
            b: Varnode::constant(8, 8),
        });
        dynamic.push(R2ILOp::Load {
            dst: Varnode::unique(0x70, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x60, 8),
        });
        let dynamic = artifact_with(
            &[dynamic],
            REVISION,
            0,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        );
        assert!(
            CertifiedMachineProjection::from_artifact(&dynamic)
                .expect("dynamic projection")
                .aggregate_member_accesses()
                .is_empty()
        );

        let mut aliased = R2ILBlock::new(0x1000, 4);
        aliased.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x80, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        });
        aliased.push(R2ILOp::Load {
            dst: Varnode::unique(0x90, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x80, 8),
        });
        let aliased = artifact_with(
            &[aliased],
            REVISION,
            0,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        );
        assert!(
            CertifiedMachineProjection::from_artifact(&aliased)
                .expect("aliased projection")
                .aggregate_member_accesses()
                .is_empty()
        );

        let wrong_space = artifact_with(
            &exact_blocks(SpaceId::Custom(7)),
            REVISION,
            0,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        );
        assert!(wrong_space.aggregate_accesses().is_empty());
        assert!(CertifiedMachineProjection::from_artifact(&wrong_space).is_err());

        let mut wrong_width = R2ILBlock::new(0x1000, 4);
        wrong_width.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0xa0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(8, 8),
        });
        wrong_width.push(R2ILOp::Load {
            dst: Varnode::unique(0xb0, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0xa0, 8),
        });
        let wrong_width = artifact_with(
            &[wrong_width],
            REVISION,
            0,
            demo_struct_graph(SourceTypeKind::SignedInteger),
        );
        assert!(
            CertifiedMachineProjection::from_artifact(&wrong_width)
                .expect("wrong-width projection")
                .aggregate_member_accesses()
                .is_empty()
        );
    }
}
