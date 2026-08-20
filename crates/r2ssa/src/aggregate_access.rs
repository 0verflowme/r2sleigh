//! Exact source-layout projections for scalar aggregate member accesses.
//!
//! This pass only joins facts already owned by r2ssa: a revision-bound source
//! type graph, canonical parameter-relative address provenance, and one exact
//! structured RAM access.  Failure to prove every part leaves the access
//! unprojected.

use std::collections::BTreeMap;

use r2il::SpaceId;
use serde::Serialize;

use crate::{
    AddressProvenanceFacts, InstId, InstPayload, SSAOp, SourceMachineContext, SourceTypeKind,
    SsaGraph, StructuredAccessId, StructuredMemoryAccessFact, ValueId,
};

pub const AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION: u32 = 3;

/// Exact scalar value carried by one projected memory effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum AggregateAccessBinding {
    Read { result: ValueId },
    Write { value: ValueId },
}

/// Exact source-layout array index retained by one aggregate access.
///
/// The coefficient is not caller policy: it is admitted only when it equals
/// the byte size of the revision-bound aggregate layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct AggregateElementIndexProjection {
    pub value: ValueId,
    pub stride_bytes: u64,
}

/// One exact access to a scalar member in a source-owned aggregate layout.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AggregateAccessProjection {
    pub schema_version: u32,
    pub source_revision_identity: Box<[u8]>,
    pub source_parameter_index: u32,
    pub pointer_type_id: u32,
    pub struct_type_id: u32,
    pub aggregate_id: u32,
    pub member_id: u32,
    pub member_type_id: u32,
    pub element_index: Option<AggregateElementIndexProjection>,
    pub byte_offset: u64,
    pub byte_width: u32,
    pub space: SpaceId,
    pub access: StructuredAccessId,
    pub producer: InstId,
    pub binding: AggregateAccessBinding,
}

/// Revision-sealed aggregate access projections keyed by canonical access ID.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AggregateAccessProjectionFacts {
    schema_version: u32,
    source_revision_identity: Option<Box<[u8]>>,
    projections: BTreeMap<StructuredAccessId, AggregateAccessProjection>,
}

impl Default for AggregateAccessProjectionFacts {
    fn default() -> Self {
        Self {
            schema_version: AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION,
            source_revision_identity: None,
            projections: BTreeMap::new(),
        }
    }
}

impl AggregateAccessProjectionFacts {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub fn source_revision_identity(&self) -> Option<&[u8]> {
        self.source_revision_identity.as_deref()
    }

    pub fn projection(
        &self,
        source_revision_identity: &[u8],
        access: StructuredAccessId,
    ) -> Option<&AggregateAccessProjection> {
        (self.source_revision_identity.as_deref() == Some(source_revision_identity))
            .then(|| self.projections.get(&access))
            .flatten()
    }

    pub fn projections_for_revision(
        &self,
        source_revision_identity: &[u8],
    ) -> Option<&BTreeMap<StructuredAccessId, AggregateAccessProjection>> {
        (self.source_revision_identity.as_deref() == Some(source_revision_identity))
            .then_some(&self.projections)
    }

    pub fn len(&self) -> usize {
        self.projections.len()
    }

    pub fn is_empty(&self) -> bool {
        self.projections.is_empty()
    }
}

fn graph_type(graph: &crate::SourceTypeGraph, type_id: u32) -> Option<&crate::SourceType> {
    usize::try_from(type_id)
        .ok()
        .and_then(|index| graph.types().get(index))
        .filter(|source_type| source_type.id() == type_id)
}

fn exact_access_binding(
    graph: &SsaGraph,
    access: &StructuredMemoryAccessFact,
    expected_space: SpaceId,
) -> Option<AggregateAccessBinding> {
    if access.id.ordinal != 0
        || graph.op_site_for_inst(access.id.inst) != Some((access.block_addr, access.op_index))
    {
        return None;
    }
    let instruction = graph.inst(access.id.inst)?;
    if instruction.id != access.id.inst {
        return None;
    }
    match (&instruction.payload, access.is_write) {
        (InstPayload::Op(SSAOp::Load { dst, space, addr }), false) => {
            let address = graph.value_id_for_var(addr)?;
            let result = graph.value_id_for_var(dst)?;
            (*space == expected_space
                && address == access.address
                && access.value == Some(result)
                && instruction.output == Some(result)
                && dst.size == access.width)
                .then_some(AggregateAccessBinding::Read { result })
        }
        (InstPayload::Op(SSAOp::Store { space, addr, val }), true) => {
            let address = graph.value_id_for_var(addr)?;
            let value = graph.value_id_for_var(val)?;
            (*space == expected_space
                && address == access.address
                && access.value == Some(value)
                && instruction.output.is_none()
                && val.size == access.width)
                .then_some(AggregateAccessBinding::Write { value })
        }
        _ => None,
    }
}

pub(crate) fn collect_aggregate_access_projections(
    graph: &SsaGraph,
    addresses: &AddressProvenanceFacts,
    accesses: &BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    machine_context: &SourceMachineContext,
) -> AggregateAccessProjectionFacts {
    let Some(interface) = machine_context.function_interface() else {
        return AggregateAccessProjectionFacts::default();
    };
    let Some(type_graph) = interface.type_graph() else {
        return AggregateAccessProjectionFacts::default();
    };
    let revision = interface.revision_identity().to_vec().into_boxed_slice();
    let mut projections = BTreeMap::new();
    for (access_id, access) in accesses {
        let Some(space) = machine_context.memory_space_at(access.block_addr, access.op_index)
        else {
            continue;
        };
        if *access_id != access.id || !access.provenance_complete || space != SpaceId::Ram {
            continue;
        }
        let Some(binding) = exact_access_binding(graph, access, space) else {
            continue;
        };
        let Some(expression) = addresses.parameter_expression(access.address) else {
            continue;
        };
        if expression.offset < 0 {
            continue;
        }
        let Ok(parameter_index) = u32::try_from(expression.parameter) else {
            continue;
        };
        let Some(parameter) = interface.parameters().get(expression.parameter) else {
            continue;
        };
        let Some(logical_value) = interface
            .parameter_logical_values()
            .get(expression.parameter)
        else {
            continue;
        };
        if parameter.index() != parameter_index {
            continue;
        }
        if expression.parameter_storage != Some(parameter.storage()) {
            continue;
        }
        let pointer_type_id = logical_value.type_id();
        let Some(pointer_type) = graph_type(type_graph, pointer_type_id) else {
            continue;
        };
        let SourceTypeKind::Pointer {
            target_type_id: struct_type_id,
        } = pointer_type.kind()
        else {
            continue;
        };
        let Some(struct_type) = graph_type(type_graph, struct_type_id) else {
            continue;
        };
        let SourceTypeKind::Struct { aggregate_id } = struct_type.kind() else {
            continue;
        };
        let Some(aggregate) = usize::try_from(aggregate_id)
            .ok()
            .and_then(|index| type_graph.aggregates().get(index))
            .filter(|aggregate| {
                aggregate.id() == aggregate_id && aggregate.type_id() == struct_type_id
            })
        else {
            continue;
        };
        if aggregate.size_bits() == 0 || !aggregate.size_bits().is_multiple_of(8) {
            continue;
        }
        let aggregate_size_bytes = aggregate.size_bits() / 8;
        let element_index = match expression.terms.as_slice() {
            [] => None,
            [term]
                if term.coefficient > 0
                    && u64::try_from(term.coefficient) == Ok(aggregate_size_bytes)
                    && graph.value(term.value).is_some() =>
            {
                Some(AggregateElementIndexProjection {
                    value: term.value,
                    stride_bytes: aggregate_size_bytes,
                })
            }
            _ => continue,
        };
        let Ok(byte_offset) = u64::try_from(expression.offset) else {
            continue;
        };
        let Some(offset_bits) = byte_offset.checked_mul(8) else {
            continue;
        };
        let size_bits = u64::from(access.width) * 8;
        let mut matching_members = aggregate.members().iter().filter(|member| {
            member.offset_bits() == offset_bits && member.size_bits() == size_bits
        });
        let Some(member) = matching_members.next() else {
            continue;
        };
        if matching_members.next().is_some() {
            continue;
        }
        let Some(member_type) = graph_type(type_graph, member.type_id()) else {
            continue;
        };
        // What decides whether an access lands on a member is where it lands
        // and how wide it is, not what kind the member is. Requiring an integer
        // meant a store to `s->next` projected onto nothing.
        if member_type.size_bits() != size_bits {
            continue;
        }
        let projection = AggregateAccessProjection {
            schema_version: AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION,
            source_revision_identity: revision.clone(),
            source_parameter_index: parameter_index,
            pointer_type_id,
            struct_type_id,
            aggregate_id,
            member_id: member.member_id(),
            member_type_id: member.type_id(),
            element_index,
            byte_offset,
            byte_width: access.width,
            space,
            access: access.id,
            producer: access.id.inst,
            binding,
        };
        if projections.insert(access.id, projection).is_some() {
            projections.remove(&access.id);
        }
    }
    AggregateAccessProjectionFacts {
        schema_version: AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION,
        source_revision_identity: Some(revision),
        projections,
    }
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    use super::*;
    use crate::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceAggregateLayout,
        SourceAggregateMember, SourceCarrierKind, SourceCarrierProjection, SourceFunctionInterface,
        SourceFunctionReturn, SourceLogicalValue, SourceType, SourceTypeGraph,
    };

    const REVISION: &[u8] = b"demo-struct-layout-revision";

    fn register_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn aarch64_arch() -> ArchSpec {
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

    fn demo_struct_graph() -> SourceTypeGraph {
        let members = (0..14).map(|index| {
            SourceAggregateMember::new(
                index,
                1,
                u64::from(index) * 32,
                32,
                format!("member_{index}"),
            )
        });
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 56 * 8, 32),
                SourceType::new(1, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            [SourceAggregateLayout::new(
                0,
                0,
                56 * 8,
                32,
                "DemoStruct",
                members,
            )],
        )
        .expect("valid DemoStruct graph")
    }

    fn source_interface(exact_graph: bool) -> SourceFunctionInterface {
        source_interface_with_pointer_storage(exact_graph, 0)
    }

    fn source_interface_with_pointer_storage(
        exact_graph: bool,
        pointer_offset: u64,
    ) -> SourceFunctionInterface {
        let parameters = [
            SourceAbiParameterSpec::new(0, register_storage(pointer_offset)),
            SourceAbiParameterSpec::new(1, register_storage(8)),
            SourceAbiParameterSpec::new(2, register_storage(16)),
        ];
        if !exact_graph {
            return SourceFunctionInterface::new(
                REVISION.to_vec(),
                "aapcs64",
                parameters,
                SourceFunctionReturn::Void,
                [],
            )
            .expect("valid untyped source interface");
        }
        let scalar_carrier = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_with_logical_types(
            REVISION.to_vec(),
            "aapcs64",
            parameters,
            SourceFunctionReturn::Void,
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(1, scalar_carrier),
                SourceLogicalValue::new(1, scalar_carrier),
            ],
            None,
            Some(demo_struct_graph()),
        )
        .expect("valid exact source interface")
    }

    fn exact_member_blocks() -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x20, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(52, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x30, 8),
            val: Varnode::register(16, 4),
        });
        vec![block]
    }

    fn single_load_blocks(
        base: Varnode,
        offset: u64,
        width: u32,
        space: SpaceId,
    ) -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: base,
            b: Varnode::constant(offset, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x20, width),
            space,
            addr: Varnode::unique(0x10, 8),
        });
        vec![block]
    }

    fn artifact(blocks: &[R2ILBlock], exact_graph: bool) -> crate::SsaArtifact {
        artifact_with_interface(blocks, source_interface(exact_graph))
    }

    fn artifact_with_interface(
        blocks: &[R2ILBlock],
        interface: SourceFunctionInterface,
    ) -> crate::SsaArtifact {
        crate::SsaArtifact::for_decompile_with_interface(blocks, Some(&aarch64_arch()), interface)
            .expect("prepared source-backed SSA")
    }

    #[test]
    fn exact_demo_struct_load_and_store_project_stable_member_facts() {
        let artifact = artifact(&exact_member_blocks(), true);
        let facts = artifact.aggregate_accesses();
        let projections = facts
            .projections_for_revision(REVISION)
            .expect("matching source revision");
        assert_eq!(
            facts.schema_version(),
            AGGREGATE_ACCESS_PROJECTION_SCHEMA_VERSION
        );
        assert_eq!(projections.len(), 2);

        let load_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 1)
            .expect("load instruction");
        let load_access = StructuredAccessId {
            inst: load_inst,
            ordinal: 0,
        };
        let load = facts
            .projection(REVISION, load_access)
            .expect("third-member load projection");
        assert_eq!(load.source_revision_identity.as_ref(), REVISION);
        assert_eq!(load.source_parameter_index, 0);
        assert_eq!(load.pointer_type_id, 2);
        assert_eq!(load.struct_type_id, 0);
        assert_eq!(load.aggregate_id, 0);
        assert_eq!(load.member_id, 2);
        assert_eq!(load.member_type_id, 1);
        assert_eq!(load.element_index, None);
        assert_eq!((load.byte_offset, load.byte_width), (8, 4));
        assert_eq!(load.space, SpaceId::Ram);
        assert_eq!(load.access, load_access);
        assert_eq!(load.producer, load_inst);
        let AggregateAccessBinding::Read { result } = load.binding else {
            panic!("load projection must retain its exact result value");
        };
        assert_eq!(artifact.graph().def_inst(result), Some(load_inst));

        let store_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 3)
            .expect("store instruction");
        let store_access = StructuredAccessId {
            inst: store_inst,
            ordinal: 0,
        };
        let store = facts
            .projection(REVISION, store_access)
            .expect("fourteenth-member store projection");
        assert_eq!(store.member_id, 13);
        assert_eq!((store.byte_offset, store.byte_width), (52, 4));
        assert_eq!(store.producer, store_inst);
        let AggregateAccessBinding::Write { value } = store.binding else {
            panic!("store projection must retain its exact stored value");
        };
        assert_eq!(
            artifact.structured().memory_accesses[&store_access].value,
            Some(value)
        );

        assert!(facts.projections_for_revision(b"other-revision").is_none());
        assert!(facts.projection(b"other-revision", load_access).is_none());
    }

    #[test]
    fn aggregate_projection_rejects_missing_or_mutated_authority() {
        let exact_blocks = exact_member_blocks();
        assert!(
            artifact(&exact_blocks, false)
                .aggregate_accesses()
                .is_empty()
        );

        let wrong_base = single_load_blocks(Varnode::register(8, 8), 8, 4, SpaceId::Ram);
        assert!(artifact(&wrong_base, true).aggregate_accesses().is_empty());

        let declared_other_base = single_load_blocks(Varnode::register(0, 8), 8, 4, SpaceId::Ram);
        assert!(
            artifact_with_interface(
                &declared_other_base,
                source_interface_with_pointer_storage(true, 24),
            )
            .aggregate_accesses()
            .is_empty()
        );

        let wrong_offset = single_load_blocks(Varnode::register(0, 8), 10, 4, SpaceId::Ram);
        assert!(
            artifact(&wrong_offset, true)
                .aggregate_accesses()
                .is_empty()
        );

        let wrong_width = single_load_blocks(Varnode::register(0, 8), 8, 8, SpaceId::Ram);
        assert!(artifact(&wrong_width, true).aggregate_accesses().is_empty());

        let wrong_space = single_load_blocks(Varnode::register(0, 8), 8, 4, SpaceId::Custom(7));
        assert!(artifact(&wrong_space, true).aggregate_accesses().is_empty());

        let nonzero_index = single_load_blocks(Varnode::register(0, 8), 64, 4, SpaceId::Ram);
        assert!(
            artifact(&nonzero_index, true)
                .aggregate_accesses()
                .is_empty()
        );

        let mut dynamic = R2ILBlock::new(0x1000, 4);
        dynamic.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(56, 8),
        });
        dynamic.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(0, 8),
            b: Varnode::unique(0x10, 8),
        });
        dynamic.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        dynamic.push(R2ILOp::Load {
            dst: Varnode::unique(0x40, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x30, 8),
        });
        let indexed = artifact(&[dynamic], true);
        let indexed_access = StructuredAccessId {
            inst: indexed
                .graph()
                .inst_id_for_op_site(0x1000, 3)
                .expect("indexed load instruction"),
            ordinal: 0,
        };
        let indexed_projection = indexed
            .aggregate_accesses()
            .projection(REVISION, indexed_access)
            .expect("exact aggregate-stride index projection");
        let index = indexed_projection
            .element_index
            .expect("indexed projection must retain its exact SSA index");
        assert_eq!(index.stride_bytes, 56);
        assert_eq!(
            indexed
                .addresses()
                .parameter_expression(indexed.structured().memory_accesses[&indexed_access].address)
                .and_then(|expression| expression.terms.first())
                .map(|term| term.value),
            Some(index.value)
        );

        let mut wrong_stride = R2ILBlock::new(0x1000, 4);
        wrong_stride.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(48, 8),
        });
        wrong_stride.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(0, 8),
            b: Varnode::unique(0x10, 8),
        });
        wrong_stride.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::constant(8, 8),
        });
        wrong_stride.push(R2ILOp::Load {
            dst: Varnode::unique(0x40, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x30, 8),
        });
        assert!(
            artifact(&[wrong_stride], true)
                .aggregate_accesses()
                .is_empty()
        );

        let mut aliased = R2ILBlock::new(0x1000, 4);
        aliased.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        });
        aliased.push(R2ILOp::Load {
            dst: Varnode::unique(0x20, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        assert!(artifact(&[aliased], true).aggregate_accesses().is_empty());

        let positive = artifact(&exact_blocks, true);
        let load_id = StructuredAccessId {
            inst: positive
                .graph()
                .inst_id_for_op_site(0x1000, 1)
                .expect("load instruction"),
            ordinal: 0,
        };
        let mut ambiguous_accesses = positive.structured().memory_accesses.clone();
        ambiguous_accesses
            .get_mut(&load_id)
            .expect("load access")
            .provenance_complete = false;
        let recollected = collect_aggregate_access_projections(
            positive.graph(),
            positive.addresses(),
            &ambiguous_accesses,
            positive.machine_context(),
        );
        assert!(recollected.projection(REVISION, load_id).is_none());

        let mut mismatched_graph = positive.graph().clone();
        let instruction = mismatched_graph
            .insts
            .get_mut(load_id.inst.0 as usize)
            .expect("load instruction");
        let InstPayload::Op(SSAOp::Load { space, .. }) = &mut instruction.payload else {
            panic!("expected source load");
        };
        *space = SpaceId::Custom(7);
        let recollected = collect_aggregate_access_projections(
            &mismatched_graph,
            positive.addresses(),
            &positive.structured().memory_accesses,
            positive.machine_context(),
        );
        assert!(
            recollected.projection(REVISION, load_id).is_none(),
            "a Custom source op must not reuse a Ram machine-context projection"
        );
    }
}
