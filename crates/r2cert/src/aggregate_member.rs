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
/// This is a certification fact, not a [`super::CertifiedLedgerClosure`]. A
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
        || source_obligation.source.graph_inst() != Some(projection.producer)
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
