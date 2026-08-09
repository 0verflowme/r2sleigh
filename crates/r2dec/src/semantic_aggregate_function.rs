//! Closed semantic-C functions for exact aggregate member memory accesses.
//!
//! The rendered field expression supplies only a certified byte address to the
//! existing RAM helper ABI. It is never used as an ordinary C load or store.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CertifiedAggregateMemberAccess, CertifiedAggregateMemberAccessSemantics,
    CertifiedArtifactOrigin, CertifiedMachineProjection, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedNaturalScalarAggregateLayout,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalStorageId, InstPayload, MachineBuildError,
    MachineValueBinding, SSAOp, SourceCarrierKind, SourceFunctionInterface, SourceFunctionReturn,
    SourceTypeGraph, SourceTypeKind, SsaArtifact, StructuredAccessId,
};
use serde::Serialize;

use crate::semantic_c::{
    SEMANTIC_C_HELPERS, SemanticCError, SemanticCFunctionReturn, SemanticCInputOrigin,
    SemanticCParameter, storage_type, value_name,
};
use crate::semantic_memory_function::{
    CertifiedMemorySemanticCFunction, CertifiedMemorySemanticCFunctionError,
    PLAIN_RAM_HELPER_DECLARATIONS, memory_helper_name, render_value_use,
};

pub const CERTIFIED_AGGREGATE_MEMBER_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedAggregateMemberSemanticCFunctionScope {
    SingleTerminalReturnBlockWithExactAggregateMembers,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedAggregateScalarSignedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateStructMemberManifest {
    member_id: u32,
    type_id: u32,
    offset_bits: u64,
    size_bits: u64,
    align_bits: u64,
    signedness: CertifiedAggregateScalarSignedness,
}

impl CertifiedAggregateStructMemberManifest {
    pub const fn member_id(&self) -> u32 {
        self.member_id
    }

    pub const fn type_id(&self) -> u32 {
        self.type_id
    }

    pub const fn offset_bits(&self) -> u64 {
        self.offset_bits
    }

    pub const fn size_bits(&self) -> u64 {
        self.size_bits
    }

    pub const fn align_bits(&self) -> u64 {
        self.align_bits
    }

    pub const fn signedness(&self) -> CertifiedAggregateScalarSignedness {
        self.signedness
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateStructLayoutManifest {
    pointer_type_id: u32,
    struct_type_id: u32,
    aggregate_id: u32,
    size_bits: u64,
    align_bits: u64,
    members: Box<[CertifiedAggregateStructMemberManifest]>,
}

impl CertifiedAggregateStructLayoutManifest {
    pub const fn pointer_type_id(&self) -> u32 {
        self.pointer_type_id
    }

    pub const fn struct_type_id(&self) -> u32 {
        self.struct_type_id
    }

    pub const fn aggregate_id(&self) -> u32 {
        self.aggregate_id
    }

    pub const fn size_bits(&self) -> u64 {
        self.size_bits
    }

    pub const fn align_bits(&self) -> u64 {
        self.align_bits
    }

    pub const fn members(&self) -> &[CertifiedAggregateStructMemberManifest] {
        &self.members
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedAggregateSemanticCParameterKind {
    AggregatePointer {
        pointer_type_id: u32,
        struct_type_id: u32,
    },
    Scalar {
        type_id: u32,
        width_bits: u64,
        signedness: CertifiedAggregateScalarSignedness,
        carrier_kind: SourceCarrierKind,
        carrier_width_bits: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateSemanticCParameter {
    index: u32,
    storage: CanonicalStorageId,
    binding: Option<MachineValueBinding>,
    kind: CertifiedAggregateSemanticCParameterKind,
}

impl CertifiedAggregateSemanticCParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn binding(&self) -> Option<MachineValueBinding> {
        self.binding
    }

    pub const fn kind(&self) -> &CertifiedAggregateSemanticCParameterKind {
        &self.kind
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedAggregateSemanticCReturn {
    Void,
    Scalar {
        storage: CanonicalStorageId,
        binding: MachineValueBinding,
        type_id: u32,
        width_bits: u64,
        signedness: CertifiedAggregateScalarSignedness,
        carrier_kind: SourceCarrierKind,
        carrier_width_bits: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedAggregateMemberRenderDirection {
    Read { result: MachineValueBinding },
    Write { value: MachineValueBinding },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateMemberRenderAccess {
    producer: CanonicalInstructionId,
    access: StructuredAccessId,
    parameter_index: u32,
    member_id: u32,
    member_type_id: u32,
    byte_offset: u64,
    byte_width: u32,
    address: MachineValueBinding,
    direction: CertifiedAggregateMemberRenderDirection,
    statement: CertifiedMemoryStatement,
    certificate: CertifiedAggregateMemberAccess,
}

impl CertifiedAggregateMemberRenderAccess {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn access(&self) -> StructuredAccessId {
        self.access
    }

    pub const fn parameter_index(&self) -> u32 {
        self.parameter_index
    }

    pub const fn member_id(&self) -> u32 {
        self.member_id
    }

    pub const fn member_type_id(&self) -> u32 {
        self.member_type_id
    }

    pub const fn byte_offset(&self) -> u64 {
        self.byte_offset
    }

    pub const fn byte_width(&self) -> u32 {
        self.byte_width
    }

    pub const fn address(&self) -> MachineValueBinding {
        self.address
    }

    pub const fn direction(&self) -> CertifiedAggregateMemberRenderDirection {
        self.direction
    }

    pub const fn statement(&self) -> &CertifiedMemoryStatement {
        &self.statement
    }

    pub const fn certificate(&self) -> &CertifiedAggregateMemberAccess {
        &self.certificate
    }
}

/// A closed aggregate-member function layered on the existing plain-RAM
/// terminal-return typed-output seal. Aggregate spelling introduces no new
/// source obligation and therefore carries no duplicate authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateMemberSemanticCFunction {
    schema_version: u32,
    scope: CertifiedAggregateMemberSemanticCFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    interface_revision: Box<[u8]>,
    source_interface: SourceFunctionInterface,
    pointer_parameter_index: u32,
    layout: CertifiedAggregateStructLayoutManifest,
    parameters: Box<[CertifiedAggregateSemanticCParameter]>,
    return_kind: CertifiedAggregateSemanticCReturn,
    accesses: Box<[CertifiedAggregateMemberRenderAccess]>,
    memory_order: Box<[CanonicalInstructionId]>,
    address_producers: BTreeSet<CanonicalInstructionId>,
    memory: CertifiedMemorySemanticCFunction,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CertifiedAggregateMemberSemanticCFunctionError {
    Machine(MachineBuildError),
    Memory(CertifiedMemorySemanticCFunctionError),
    SemanticC(SemanticCError),
    MissingSourceInterface,
    MissingTypeGraph,
    MissingAggregate(CanonicalInstructionId),
    UnsupportedAddress(CanonicalInstructionId),
    UnsupportedParameter(u32),
    InvalidReturn,
    InvalidFunction(Vec<String>),
}

impl std::fmt::Display for CertifiedAggregateMemberSemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "certified aggregate-member semantic C function failed: {self:?}"
        )
    }
}

impl std::error::Error for CertifiedAggregateMemberSemanticCFunctionError {}

impl From<MachineBuildError> for CertifiedAggregateMemberSemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<CertifiedMemorySemanticCFunctionError>
    for CertifiedAggregateMemberSemanticCFunctionError
{
    fn from(error: CertifiedMemorySemanticCFunctionError) -> Self {
        Self::Memory(error)
    }
}

impl From<SemanticCError> for CertifiedAggregateMemberSemanticCFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn source_type(graph: &SourceTypeGraph, type_id: u32) -> Option<&r2ssa::SourceType> {
    usize::try_from(type_id)
        .ok()
        .and_then(|index| graph.types().get(index))
        .filter(|source_type| source_type.id() == type_id)
}

fn scalar_signedness(kind: SourceTypeKind) -> Option<CertifiedAggregateScalarSignedness> {
    match kind {
        SourceTypeKind::SignedInteger => Some(CertifiedAggregateScalarSignedness::Signed),
        SourceTypeKind::UnsignedInteger => Some(CertifiedAggregateScalarSignedness::Unsigned),
        SourceTypeKind::Pointer { .. } | SourceTypeKind::Struct { .. } => None,
    }
}

fn layout_manifest(
    layout: &CertifiedNaturalScalarAggregateLayout,
) -> Option<CertifiedAggregateStructLayoutManifest> {
    let pointer_type_id = layout.pointer_type().id();
    let struct_type_id = layout.aggregate_type().id();
    let SourceTypeKind::Pointer {
        target_type_id: pointer_target,
    } = layout.pointer_type().kind()
    else {
        return None;
    };
    let SourceTypeKind::Struct { aggregate_id } = layout.aggregate_type().kind() else {
        return None;
    };
    if pointer_target != struct_type_id
        || layout.aggregate().id() != aggregate_id
        || layout.aggregate().type_id() != struct_type_id
        || layout.aggregate().members().len() != layout.member_types().len()
    {
        return None;
    }
    let members = layout
        .aggregate()
        .members()
        .iter()
        .zip(layout.member_types())
        .map(|(member, member_type)| {
            Some(CertifiedAggregateStructMemberManifest {
                member_id: member.member_id(),
                type_id: member.type_id(),
                offset_bits: member.offset_bits(),
                size_bits: member.size_bits(),
                align_bits: member_type.align_bits(),
                signedness: scalar_signedness(member_type.kind())?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(CertifiedAggregateStructLayoutManifest {
        pointer_type_id,
        struct_type_id,
        aggregate_id,
        size_bits: layout.aggregate().size_bits(),
        align_bits: layout.aggregate().align_bits(),
        members: members.into_boxed_slice(),
    })
}

fn access_manifest(
    certificate: &CertifiedAggregateMemberAccess,
) -> Option<CertifiedAggregateMemberRenderAccess> {
    let projection = certificate.projection();
    let statement = certificate.memory_statement();
    let direction = match (certificate.semantics(), statement.kind()) {
        (
            CertifiedAggregateMemberAccessSemantics::Read { result, .. },
            CertifiedMemoryStatementKind::Read {
                result: statement_result,
            },
        ) if result == statement_result => CertifiedAggregateMemberRenderDirection::Read {
            result: result.binding(),
        },
        (
            CertifiedAggregateMemberAccessSemantics::Write { value, .. },
            CertifiedMemoryStatementKind::Write {
                value: statement_value,
            },
        ) if value == statement_value => CertifiedAggregateMemberRenderDirection::Write {
            value: value.binding(),
        },
        _ => return None,
    };
    Some(CertifiedAggregateMemberRenderAccess {
        producer: certificate.producer(),
        access: certificate.access(),
        parameter_index: projection.source_parameter_index,
        member_id: projection.member_id,
        member_type_id: projection.member_type_id,
        byte_offset: projection.byte_offset,
        byte_width: projection.byte_width,
        address: statement.address().binding(),
        direction,
        statement: statement.clone(),
        certificate: certificate.clone(),
    })
}

fn semantic_parameter_by_index(
    parameters: &[SemanticCParameter],
    index: u32,
) -> Option<&SemanticCParameter> {
    usize::try_from(index)
        .ok()
        .and_then(|position| parameters.get(position))
        .filter(|parameter| parameter.index() == index)
}

fn parameter_manifests(
    source: &SourceFunctionInterface,
    semantic: &[SemanticCParameter],
    pointer_parameter_index: u32,
    pointer_layout: &CertifiedAggregateStructLayoutManifest,
) -> Option<Vec<CertifiedAggregateSemanticCParameter>> {
    let graph = source.type_graph()?;
    if source.parameters().len() != semantic.len()
        || source.parameters().len() != source.parameter_logical_values().len()
    {
        return None;
    }
    source
        .parameters()
        .iter()
        .zip(source.parameter_logical_values())
        .map(|(source_parameter, logical)| {
            let semantic_parameter =
                semantic_parameter_by_index(semantic, source_parameter.index())?;
            if semantic_parameter.storage() != source_parameter.storage()
                || semantic_parameter.ty().width_bits()
                    != source_parameter.storage().size.checked_mul(8)?
            {
                return None;
            }
            let source_type = source_type(graph, logical.type_id())?;
            let carrier = logical.carrier();
            let kind = if source_parameter.index() == pointer_parameter_index {
                if logical.type_id() != pointer_layout.pointer_type_id
                    || source_type.kind()
                        != (SourceTypeKind::Pointer {
                            target_type_id: pointer_layout.struct_type_id,
                        })
                    || carrier.kind() != SourceCarrierKind::Full
                    || carrier.offset_bits() != 0
                    || carrier.size_bits() != source_type.size_bits()
                {
                    return None;
                }
                CertifiedAggregateSemanticCParameterKind::AggregatePointer {
                    pointer_type_id: pointer_layout.pointer_type_id,
                    struct_type_id: pointer_layout.struct_type_id,
                }
            } else {
                let signedness = scalar_signedness(source_type.kind())?;
                if carrier.offset_bits() != 0
                    || carrier.size_bits() != source_type.size_bits()
                    || !matches!(source_type.size_bits(), 8 | 16 | 32 | 64)
                    || !matches!(
                        carrier.kind(),
                        SourceCarrierKind::Full | SourceCarrierKind::LowBits
                    )
                {
                    return None;
                }
                CertifiedAggregateSemanticCParameterKind::Scalar {
                    type_id: logical.type_id(),
                    width_bits: source_type.size_bits(),
                    signedness,
                    carrier_kind: carrier.kind(),
                    carrier_width_bits: u64::from(source_parameter.storage().size)
                        .checked_mul(8)?,
                }
            };
            Some(CertifiedAggregateSemanticCParameter {
                index: source_parameter.index(),
                storage: source_parameter.storage(),
                binding: semantic_parameter.value(),
                kind,
            })
        })
        .collect()
}

fn return_manifest(
    source: &SourceFunctionInterface,
    semantic_return: &SemanticCFunctionReturn,
    returned_binding: Option<MachineValueBinding>,
) -> Option<CertifiedAggregateSemanticCReturn> {
    match (
        source.return_kind(),
        source.return_logical_value(),
        semantic_return,
        returned_binding,
    ) {
        (SourceFunctionReturn::Void, None, SemanticCFunctionReturn::Void, None) => {
            Some(CertifiedAggregateSemanticCReturn::Void)
        }
        (
            SourceFunctionReturn::Register { storage },
            Some(logical),
            SemanticCFunctionReturn::Register {
                storage: semantic_storage,
                ty,
            },
            Some(binding),
        ) if storage == *semantic_storage
            && binding.width_bits() == ty.width_bits()
            && ty.width_bits() == storage.size.checked_mul(8)? =>
        {
            let graph = source.type_graph()?;
            let source_type = source_type(graph, logical.type_id())?;
            let carrier = logical.carrier();
            let signedness = scalar_signedness(source_type.kind())?;
            if carrier.offset_bits() != 0
                || carrier.size_bits() != source_type.size_bits()
                || !matches!(source_type.size_bits(), 8 | 16 | 32 | 64)
            {
                return None;
            }
            Some(CertifiedAggregateSemanticCReturn::Scalar {
                storage,
                binding,
                type_id: logical.type_id(),
                width_bits: source_type.size_bits(),
                signedness,
                carrier_kind: carrier.kind(),
                carrier_width_bits: u64::from(storage.size).checked_mul(8)?,
            })
        }
        _ => None,
    }
}

fn returned_binding(
    memory: &CertifiedMemorySemanticCFunction,
) -> Option<Option<MachineValueBinding>> {
    memory
        .returned()
        .and_then(|returned| match returned.values() {
            [] => Some(None),
            [value] => Some(Some(value.binding())),
            _ => None,
        })
}

fn direct_address_producers(
    artifact: &SsaArtifact,
    pointer: MachineValueBinding,
    accesses: &[CertifiedAggregateMemberRenderAccess],
) -> Result<BTreeSet<CanonicalInstructionId>, CertifiedAggregateMemberSemanticCFunctionError> {
    let pointer_value = pointer.value();
    let mut producers = BTreeSet::new();
    let mut allowed_pointer_users = BTreeSet::new();
    let mut memory_by_address = BTreeMap::<_, BTreeSet<_>>::new();
    for access in accesses {
        if access.address.value() == pointer_value && access.byte_offset == 0 {
            allowed_pointer_users.insert(access.access.inst);
            if access.statement.address().producer().is_some() {
                return Err(
                    CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(
                        access.producer,
                    ),
                );
            }
            continue;
        }
        memory_by_address
            .entry(access.address.value())
            .or_default()
            .insert(access.access.inst);
        let Some(definition) = artifact.graph().def_inst(access.address.value()) else {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        };
        let Some(instruction) = artifact.graph().inst(definition) else {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        };
        let InstPayload::Op(SSAOp::IntAdd { .. }) = &instruction.payload else {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        };
        if instruction.output != Some(access.address.value()) || instruction.inputs.len() != 2 {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        }
        let constant_matches = |value| {
            artifact
                .graph()
                .value(value)
                .and_then(|value| value.var.constant_bits())
                == Some(access.byte_offset)
        };
        if !((instruction.inputs[0] == pointer_value && constant_matches(instruction.inputs[1]))
            || (instruction.inputs[1] == pointer_value && constant_matches(instruction.inputs[0])))
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        }
        let Some(source) = artifact.obligations().instruction_for_inst(definition) else {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        };
        if access.statement.address().producer() != Some(source.id) {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
            );
        }
        allowed_pointer_users.insert(definition);
        producers.insert(source.id);
    }
    if artifact
        .graph()
        .use_sites(pointer_value)
        .iter()
        .any(|use_site| !allowed_pointer_users.contains(&use_site.inst))
    {
        return Err(
            CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(
                accesses[0].producer,
            ),
        );
    }
    for (address, memory_users) in memory_by_address {
        if artifact
            .graph()
            .use_sites(address)
            .iter()
            .any(|use_site| !memory_users.contains(&use_site.inst))
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(
                    accesses[0].producer,
                ),
            );
        }
    }
    Ok(producers)
}

impl CertifiedAggregateMemberSemanticCFunction {
    pub fn from_artifact(
        artifact: &SsaArtifact,
    ) -> Result<Self, CertifiedAggregateMemberSemanticCFunctionError> {
        let memory = CertifiedMemorySemanticCFunction::from_artifact(artifact)?;
        let certified = CertifiedMachineProjection::from_artifact(artifact)?;
        let memory_origin = memory.layer().accounting().origin();
        if certified.origin() != memory_origin {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                    "aggregate and memory certification origins differ".to_string(),
                ]),
            );
        }
        let source_interface = artifact
            .machine_context()
            .function_interface()
            .cloned()
            .ok_or(CertifiedAggregateMemberSemanticCFunctionError::MissingSourceInterface)?;
        let semantic_interface = memory
            .layer()
            .accounting()
            .expression_layer()
            .function_interface()
            .ok_or(CertifiedAggregateMemberSemanticCFunctionError::MissingSourceInterface)?;
        let _ = source_interface
            .type_graph()
            .ok_or(CertifiedAggregateMemberSemanticCFunctionError::MissingTypeGraph)?;

        let mut accesses = Vec::new();
        for step in memory.layer().steps() {
            let Some(reference) = step.memory() else {
                continue;
            };
            let statement = memory.layer().resolve_memory_statement(reference).ok_or(
                CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(step.source()),
            )?;
            let certificate = certified
                .aggregate_member_access(statement.access())
                .ok_or(
                    CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(step.source()),
                )?;
            if certificate.origin() != memory_origin || certificate.memory_statement() != statement
            {
                return Err(
                    CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(step.source()),
                );
            }
            accesses.push(access_manifest(certificate).ok_or(
                CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(step.source()),
            )?);
        }
        if accesses.is_empty()
            || accesses.len() != memory.memory_order().len()
            || accesses.len() != certified.aggregate_member_accesses().len()
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                    "every memory statement must have exactly one aggregate certificate"
                        .to_string(),
                ]),
            );
        }
        let first = accesses
            .first()
            .expect("aggregate access list is checked nonempty");
        let pointer_parameter_index = first.parameter_index;
        let layout = layout_manifest(first.certificate.layout()).ok_or(
            CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(first.producer),
        )?;
        let revision = first.certificate.interface_revision();
        let graph = first.certificate.source_type_graph();
        if accesses.iter().any(|access| {
            access.parameter_index != pointer_parameter_index
                || access.certificate.interface_revision() != revision
                || access.certificate.source_type_graph() != graph
                || layout_manifest(access.certificate.layout()).as_ref() != Some(&layout)
                || access.certificate.parameter().index() != pointer_parameter_index
                || access.certificate.parameter().storage()
                    != first.certificate.parameter().storage()
        }) {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                    "aggregate accesses mix revision, base parameter, or layout authority"
                        .to_string(),
                ]),
            );
        }
        if source_interface.revision_identity() != revision
            || source_interface.type_graph() != Some(graph)
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                    "aggregate source interface differs from its certificates".to_string(),
                ]),
            );
        }

        let parameters = parameter_manifests(
            &source_interface,
            semantic_interface.parameters(),
            pointer_parameter_index,
            &layout,
        )
        .ok_or(
            CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                pointer_parameter_index,
            ),
        )?;
        let pointer_parameter = parameters
            .iter()
            .find(|parameter| parameter.index == pointer_parameter_index)
            .ok_or(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                    pointer_parameter_index,
                ),
            )?;
        let pointer_binding = pointer_parameter.binding.ok_or(
            CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                pointer_parameter_index,
            ),
        )?;
        if pointer_binding
            != first
                .certificate
                .parameter()
                .value()
                .map(|value| value.binding())
                .ok_or(
                    CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                        pointer_parameter_index,
                    ),
                )?
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                    pointer_parameter_index,
                ),
            );
        }
        let expression_layer = memory.layer().accounting().expression_layer();
        if expression_layer.input_origins().get(&pointer_binding)
            != Some(&SemanticCInputOrigin::AbiParameter {
                index: pointer_parameter_index,
                storage: pointer_parameter.storage,
            })
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                    pointer_parameter_index,
                ),
            );
        }
        let returned_binding = returned_binding(&memory)
            .ok_or(CertifiedAggregateMemberSemanticCFunctionError::InvalidReturn)?;
        let return_kind = return_manifest(
            &source_interface,
            semantic_interface.return_kind(),
            returned_binding,
        )
        .ok_or(CertifiedAggregateMemberSemanticCFunctionError::InvalidReturn)?;
        let address_producers = direct_address_producers(artifact, pointer_binding, &accesses)?;
        for producer in &address_producers {
            let Some(step) = memory
                .layer()
                .steps()
                .iter()
                .find(|step| step.source() == *producer)
            else {
                return Err(
                    CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(*producer),
                );
            };
            if step.memory().is_some()
                || step
                    .value()
                    .and_then(|reference| memory.layer().resolve_value(reference))
                    .is_none_or(|entity| {
                        !accesses
                            .iter()
                            .any(|access| entity.output() == access.address)
                    })
            {
                return Err(
                    CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(*producer),
                );
            }
        }

        let function = Self {
            schema_version: CERTIFIED_AGGREGATE_MEMBER_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: CertifiedAggregateMemberSemanticCFunctionScope::SingleTerminalReturnBlockWithExactAggregateMembers,
            name: format!("certified_aggregate_sub_{:x}", memory.layer().accounting().block_addr()),
            origin: memory_origin.clone(),
            interface_revision: revision.to_vec().into_boxed_slice(),
            source_interface,
            pointer_parameter_index,
            layout,
            parameters: parameters.into_boxed_slice(),
            return_kind,
            memory_order: memory.memory_order().to_vec().into_boxed_slice(),
            accesses: accesses.into_boxed_slice(),
            address_producers,
            memory,
        };
        let audit = function.audit();
        if !audit.has_exact_closed_aggregate_memory_return() {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(audit.invalid),
            );
        }
        function.render_body()?;
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedAggregateMemberSemanticCFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn interface_revision(&self) -> &[u8] {
        &self.interface_revision
    }

    pub const fn source_interface(&self) -> &SourceFunctionInterface {
        &self.source_interface
    }

    pub const fn pointer_parameter_index(&self) -> u32 {
        self.pointer_parameter_index
    }

    pub const fn layout(&self) -> &CertifiedAggregateStructLayoutManifest {
        &self.layout
    }

    pub const fn parameters(&self) -> &[CertifiedAggregateSemanticCParameter] {
        &self.parameters
    }

    pub const fn return_kind(&self) -> &CertifiedAggregateSemanticCReturn {
        &self.return_kind
    }

    pub const fn accesses(&self) -> &[CertifiedAggregateMemberRenderAccess] {
        &self.accesses
    }

    pub const fn memory_order(&self) -> &[CanonicalInstructionId] {
        &self.memory_order
    }

    pub const fn memory_function(&self) -> &CertifiedMemorySemanticCFunction {
        &self.memory
    }

    pub fn audit(&self) -> CertifiedAggregateMemberSemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        let memory_audit = self.memory.audit();
        let semantic_interface = self
            .memory
            .layer()
            .accounting()
            .expression_layer()
            .function_interface();
        if self.schema_version != CERTIFIED_AGGREGATE_MEMBER_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("aggregate function schema mismatch".to_string());
        }
        if self.scope
            != CertifiedAggregateMemberSemanticCFunctionScope::SingleTerminalReturnBlockWithExactAggregateMembers
        {
            invalid.push("aggregate function scope mismatch".to_string());
        }
        if !memory_audit.has_exact_closed_memory_return() {
            invalid.push("embedded memory function is not exact and closed".to_string());
        }
        if self.origin != *self.memory.layer().accounting().origin() {
            invalid.push("aggregate function origin mismatch".to_string());
        }
        if self.interface_revision.as_ref() != self.source_interface.revision_identity() {
            invalid.push("aggregate interface revision mismatch".to_string());
        }
        let Some(semantic_interface) = semantic_interface else {
            invalid.push("aggregate function has no semantic interface".to_string());
            return CertifiedAggregateMemberSemanticCFunctionAuditReport { invalid };
        };
        let expected_parameters = parameter_manifests(
            &self.source_interface,
            semantic_interface.parameters(),
            self.pointer_parameter_index,
            &self.layout,
        );
        if expected_parameters.as_deref() != Some(self.parameters.as_ref()) {
            invalid.push("aggregate parameter manifest mismatch".to_string());
        }
        let expected_return = returned_binding(&self.memory).and_then(|binding| {
            return_manifest(
                &self.source_interface,
                semantic_interface.return_kind(),
                binding,
            )
        });
        if expected_return.as_ref() != Some(&self.return_kind) {
            invalid.push("aggregate return manifest mismatch".to_string());
        }
        if self.memory_order.as_ref() != self.memory.memory_order() {
            invalid.push("aggregate memory order mismatch".to_string());
        }
        let expected_address_producers = self
            .accesses
            .iter()
            .filter_map(|access| access.statement.address().producer())
            .collect::<BTreeSet<_>>();
        if expected_address_producers != self.address_producers {
            invalid.push("aggregate address-producer manifest mismatch".to_string());
        }
        if self.accesses.len() != self.memory_order.len() {
            invalid.push("aggregate access count differs from memory count".to_string());
        }
        for (position, access) in self.accesses.iter().enumerate() {
            let expected = access_manifest(&access.certificate);
            if expected.as_ref() != Some(access) {
                invalid.push(format!("aggregate access manifest mismatch at {position}"));
            }
            if access.producer
                != self
                    .memory_order
                    .get(position)
                    .copied()
                    .unwrap_or(access.producer)
                || access.certificate.origin() != &self.origin
                || access.certificate.interface_revision() != self.interface_revision.as_ref()
                || access.certificate.projection().source_parameter_index
                    != self.pointer_parameter_index
                || access.certificate.memory_statement() != &access.statement
                || layout_manifest(access.certificate.layout()).as_ref() != Some(&self.layout)
            {
                invalid.push(format!("aggregate certificate join mismatch at {position}"));
            }
            let source_parameter = usize::try_from(self.pointer_parameter_index)
                .ok()
                .and_then(|index| self.source_interface.parameters().get(index));
            let source_logical = usize::try_from(self.pointer_parameter_index)
                .ok()
                .and_then(|index| self.source_interface.parameter_logical_values().get(index));
            if self.source_interface.type_graph() != Some(access.certificate.source_type_graph())
                || source_parameter.is_none_or(|parameter| {
                    parameter.index() != self.pointer_parameter_index
                        || parameter.storage() != access.certificate.parameter().storage()
                })
                || source_logical.copied() != Some(access.certificate.parameter_logical_value())
            {
                invalid.push(format!(
                    "aggregate source-interface certificate mismatch at {position}"
                ));
            }
            let statement = self
                .memory
                .layer()
                .steps()
                .iter()
                .find(|step| step.source() == access.producer)
                .and_then(|step| step.memory())
                .and_then(|reference| self.memory.layer().resolve_memory_statement(reference));
            if statement != Some(&access.statement) {
                invalid.push(format!("aggregate statement mismatch at {position}"));
            }
        }
        if let Err(error) = self.validate_render_sequence() {
            invalid.push(format!("aggregate render sequence is invalid: {error}"));
        }
        CertifiedAggregateMemberSemanticCFunctionAuditReport { invalid }
    }

    pub fn render_certified_c(
        &self,
    ) -> Result<String, CertifiedAggregateMemberSemanticCFunctionError> {
        let audit = self.audit();
        if !audit.has_exact_closed_aggregate_memory_return() {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(audit.invalid),
            );
        }
        self.render_body()
    }

    fn validate_render_sequence(
        &self,
    ) -> Result<(), CertifiedAggregateMemberSemanticCFunctionError> {
        let pointer = self
            .parameters
            .iter()
            .find(|parameter| parameter.index == self.pointer_parameter_index)
            .ok_or(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                    self.pointer_parameter_index,
                ),
            )?;
        if !matches!(
            pointer.kind,
            CertifiedAggregateSemanticCParameterKind::AggregatePointer { .. }
        ) || pointer.binding.is_none()
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::UnsupportedParameter(
                    self.pointer_parameter_index,
                ),
            );
        }
        let mut observed = Vec::new();
        for step in self.memory.layer().steps() {
            if let Some(reference) = step.memory() {
                let statement = self
                    .memory
                    .layer()
                    .resolve_memory_statement(reference)
                    .ok_or(
                        CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                            step.source(),
                        ),
                    )?;
                let access = self
                    .accesses
                    .iter()
                    .find(|access| access.producer == step.source())
                    .ok_or(
                        CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                            step.source(),
                        ),
                    )?;
                if access.statement != *statement
                    || access.access != statement.access()
                    || access.address != statement.address().binding()
                {
                    return Err(
                        CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                            step.source(),
                        ),
                    );
                }
                observed.push(step.source());
                continue;
            }
            if self.address_producers.contains(&step.source()) {
                let entity = step
                    .value()
                    .and_then(|reference| self.memory.layer().resolve_value(reference));
                if entity.is_none_or(|entity| {
                    !self
                        .accesses
                        .iter()
                        .any(|access| access.address == entity.output())
                }) {
                    return Err(
                        CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(
                            step.source(),
                        ),
                    );
                }
                continue;
            }
            if let Some(reference) = step.value() {
                let entity = self.memory.layer().resolve_value(reference).ok_or(
                    CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![format!(
                        "missing value entity for {}",
                        step.source()
                    )]),
                )?;
                self.memory
                    .layer()
                    .accounting()
                    .expression_layer()
                    .render_expr(entity.root())?;
            }
        }
        if observed.as_slice() != self.memory_order.as_ref() {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                    "aggregate helper order differs from source order".to_string(),
                ]),
            );
        }
        Ok(())
    }

    fn render_body(&self) -> Result<String, CertifiedAggregateMemberSemanticCFunctionError> {
        self.validate_render_sequence()?;
        let expressions = self.memory.layer().accounting().expression_layer();
        let mut output = String::new();
        output.push_str("#include <stddef.h>\n#include <stdint.h>\n#include <string.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        output.push('\n');
        output.push_str(SIGNED_BITCAST_HELPERS);
        output.push('\n');
        output.push_str(PLAIN_RAM_HELPER_DECLARATIONS);
        output.push('\n');
        self.render_layout(&mut output)?;
        self.render_signature(&mut output)?;
        for parameter in &self.parameters {
            let argument_name = format!("arg_{}", parameter.index);
            match &parameter.kind {
                CertifiedAggregateSemanticCParameterKind::AggregatePointer { .. } => {
                    writeln!(&mut output, "\t(void){argument_name};")
                        .expect("String writes cannot fail");
                }
                CertifiedAggregateSemanticCParameterKind::Scalar { width_bits, .. } => {
                    writeln!(&mut output, "\t(void){argument_name};")
                        .expect("String writes cannot fail");
                    if let Some(binding) = parameter.binding {
                        writeln!(
                            &mut output,
                            "\t{} {} = ({})((uint{}_t){argument_name});",
                            storage_type(
                                semantic_parameter_by_index(
                                    expressions
                                        .function_interface()
                                        .expect("audited semantic interface")
                                        .parameters(),
                                    parameter.index,
                                )
                                .expect("audited semantic parameter")
                                .ty(),
                            )?,
                            value_name(binding),
                            storage_type(
                                semantic_parameter_by_index(
                                    expressions
                                        .function_interface()
                                        .expect("audited semantic interface")
                                        .parameters(),
                                    parameter.index,
                                )
                                .expect("audited semantic parameter")
                                .ty(),
                            )?,
                            width_bits,
                        )
                        .expect("String writes cannot fail");
                        writeln!(&mut output, "\t(void){};", value_name(binding))
                            .expect("String writes cannot fail");
                    }
                }
            }
        }
        for step in self.memory.layer().steps() {
            if let Some(reference) = step.memory() {
                let statement = self
                    .memory
                    .layer()
                    .resolve_memory_statement(reference)
                    .expect("audited memory statement");
                let access = self
                    .accesses
                    .iter()
                    .find(|access| access.producer == step.source())
                    .expect("audited aggregate access");
                let helper = memory_helper_name(statement);
                let pointer = format!("arg_{}", access.parameter_index);
                let field = format!("field_{}", access.member_id);
                let qualifier = if matches!(
                    access.direction,
                    CertifiedAggregateMemberRenderDirection::Read { .. }
                ) {
                    "const uint8_t"
                } else {
                    "uint8_t"
                };
                let address =
                    format!("((uint64_t)(uintptr_t)(({qualifier} *)&{pointer}->{field}))");
                match statement.kind() {
                    CertifiedMemoryStatementKind::Read { result } => {
                        writeln!(
                            &mut output,
                            "\t{} {} = {helper}({address});",
                            storage_type(result.ty())?,
                            value_name(result.binding())
                        )
                        .expect("String writes cannot fail");
                    }
                    CertifiedMemoryStatementKind::Write { value } => {
                        writeln!(
                            &mut output,
                            "\t{helper}({address}, ({})({}));",
                            storage_type(value.ty())?,
                            render_value_use(value)
                        )
                        .expect("String writes cannot fail");
                    }
                }
                continue;
            }
            if self.address_producers.contains(&step.source()) {
                continue;
            }
            let Some(reference) = step.value() else {
                continue;
            };
            let entity = self
                .memory
                .layer()
                .resolve_value(reference)
                .expect("audited value entity");
            writeln!(
                &mut output,
                "\t{} {} = {};",
                storage_type(
                    expressions
                        .expr(entity.root())
                        .expect("audited expression")
                        .ty()
                )?,
                value_name(entity.output()),
                expressions.render_expr(entity.root())?
            )
            .expect("String writes cannot fail");
        }
        match self.return_kind {
            CertifiedAggregateSemanticCReturn::Void => output.push_str("\treturn;\n"),
            CertifiedAggregateSemanticCReturn::Scalar {
                binding,
                width_bits,
                signedness,
                ..
            } => {
                let value = value_name(binding);
                match signedness {
                    CertifiedAggregateScalarSignedness::Unsigned => {
                        writeln!(&mut output, "\treturn (uint{width_bits}_t)({value});")
                            .expect("String writes cannot fail")
                    }
                    CertifiedAggregateScalarSignedness::Signed => writeln!(
                        &mut output,
                        "\treturn r2s_i{width_bits}_from_bits((uint{width_bits}_t)({value}));"
                    )
                    .expect("String writes cannot fail"),
                }
            }
        }
        output.push_str("}\n");
        Ok(output)
    }

    fn render_layout(
        &self,
        output: &mut String,
    ) -> Result<(), CertifiedAggregateMemberSemanticCFunctionError> {
        let struct_name = format!("r2s_struct_{}", self.layout.aggregate_id);
        writeln!(output, "typedef struct {struct_name} {{").expect("String writes cannot fail");
        for member in &self.layout.members {
            writeln!(
                output,
                "\t{} field_{};",
                scalar_c_type(member.signedness, member.size_bits)?,
                member.member_id
            )
            .expect("String writes cannot fail");
        }
        writeln!(output, "}} {struct_name};").expect("String writes cannot fail");
        writeln!(
            output,
            "_Static_assert(sizeof({struct_name}) == {}U, \"aggregate size mismatch\");",
            self.layout.size_bits / 8
        )
        .expect("String writes cannot fail");
        writeln!(
            output,
            "_Static_assert(_Alignof({struct_name}) == {}U, \"aggregate alignment mismatch\");",
            self.layout.align_bits / 8
        )
        .expect("String writes cannot fail");
        for member in &self.layout.members {
            writeln!(
                output,
                "_Static_assert(offsetof({struct_name}, field_{}) == {}U, \"member offset mismatch\");",
                member.member_id,
                member.offset_bits / 8
            )
            .expect("String writes cannot fail");
        }
        output.push('\n');
        Ok(())
    }

    fn render_signature(
        &self,
        output: &mut String,
    ) -> Result<(), CertifiedAggregateMemberSemanticCFunctionError> {
        let return_type = match self.return_kind {
            CertifiedAggregateSemanticCReturn::Void => "void".to_string(),
            CertifiedAggregateSemanticCReturn::Scalar {
                width_bits,
                signedness,
                ..
            } => scalar_c_type(signedness, width_bits)?.to_string(),
        };
        write!(output, "{return_type} {}(", self.name).expect("String writes cannot fail");
        for (position, parameter) in self.parameters.iter().enumerate() {
            if position > 0 {
                output.push_str(", ");
            }
            match parameter.kind {
                CertifiedAggregateSemanticCParameterKind::AggregatePointer { .. } => write!(
                    output,
                    "r2s_struct_{} *arg_{}",
                    self.layout.aggregate_id, parameter.index
                )
                .expect("String writes cannot fail"),
                CertifiedAggregateSemanticCParameterKind::Scalar {
                    width_bits,
                    signedness,
                    ..
                } => write!(
                    output,
                    "{} arg_{}",
                    scalar_c_type(signedness, width_bits)?,
                    parameter.index
                )
                .expect("String writes cannot fail"),
            }
        }
        output.push_str(") {\n");
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateMemberSemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl CertifiedAggregateMemberSemanticCFunctionAuditReport {
    pub fn has_exact_closed_aggregate_memory_return(&self) -> bool {
        self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}

fn scalar_c_type(
    signedness: CertifiedAggregateScalarSignedness,
    width_bits: u64,
) -> Result<&'static str, CertifiedAggregateMemberSemanticCFunctionError> {
    match (signedness, width_bits) {
        (CertifiedAggregateScalarSignedness::Signed, 8) => Ok("int8_t"),
        (CertifiedAggregateScalarSignedness::Signed, 16) => Ok("int16_t"),
        (CertifiedAggregateScalarSignedness::Signed, 32) => Ok("int32_t"),
        (CertifiedAggregateScalarSignedness::Signed, 64) => Ok("int64_t"),
        (CertifiedAggregateScalarSignedness::Unsigned, 8) => Ok("uint8_t"),
        (CertifiedAggregateScalarSignedness::Unsigned, 16) => Ok("uint16_t"),
        (CertifiedAggregateScalarSignedness::Unsigned, 32) => Ok("uint32_t"),
        (CertifiedAggregateScalarSignedness::Unsigned, 64) => Ok("uint64_t"),
        _ => Err(
            CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![format!(
                "unsupported scalar C width {width_bits}"
            )]),
        ),
    }
}

const SIGNED_BITCAST_HELPERS: &str = r#"static inline int8_t r2s_i8_from_bits(uint8_t bits) {
    int8_t value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static inline int16_t r2s_i16_from_bits(uint16_t bits) {
    int16_t value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static inline int32_t r2s_i32_from_bits(uint32_t bits) {
    int32_t value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static inline int64_t r2s_i64_from_bits(uint64_t bits) {
    int64_t value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}
"#;

#[cfg(test)]
mod tests {
    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };
    use r2ssa::{
        CanonicalStorageSpace, SourceAbiParameterSpec, SourceAggregateLayout,
        SourceAggregateMember, SourceCarrierProjection, SourceLogicalValue, SourceType,
    };

    use super::*;

    const REVISION: &[u8] = b"aggregate-semantic-c-revision-1";

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
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
        arch.add_register(RegisterDef::new("x4", 32, 8));
        arch.add_register(RegisterDef::new("w4", 32, 4));
        arch.add_register(RegisterDef::new("x30", 48, 8));
        arch.add_space(AddressSpace::ram(8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn demo_struct_graph_with_names(aggregate_name: &str, member_prefix: &str) -> SourceTypeGraph {
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
                aggregate_name,
                (0..14).map(|index| {
                    SourceAggregateMember::new(
                        index,
                        1,
                        u64::from(index) * 32,
                        32,
                        format!("{member_prefix}_{index}"),
                    )
                }),
            )],
        )
        .expect("valid DemoStruct source graph")
    }

    fn demo_struct_graph() -> SourceTypeGraph {
        demo_struct_graph_with_names("SourceNamesAreNotRenderAuthority", "untrusted_member_name")
    }

    fn pointer_logical() -> SourceLogicalValue {
        SourceLogicalValue::new(
            2,
            SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
        )
    }

    fn scalar_logical(kind: SourceCarrierKind) -> SourceLogicalValue {
        SourceLogicalValue::new(1, SourceCarrierProjection::new(kind, 0, 32))
    }

    fn artifact(
        block: R2ILBlock,
        parameters: Vec<SourceAbiParameterSpec>,
        parameter_logical_values: Vec<SourceLogicalValue>,
        return_kind: SourceFunctionReturn,
        return_logical_value: Option<SourceLogicalValue>,
    ) -> SsaArtifact {
        artifact_with_graph(
            block,
            parameters,
            parameter_logical_values,
            return_kind,
            return_logical_value,
            demo_struct_graph(),
        )
    }

    fn artifact_with_graph(
        block: R2ILBlock,
        parameters: Vec<SourceAbiParameterSpec>,
        parameter_logical_values: Vec<SourceLogicalValue>,
        return_kind: SourceFunctionReturn,
        return_logical_value: Option<SourceLogicalValue>,
        graph: SourceTypeGraph,
    ) -> SsaArtifact {
        let interface = SourceFunctionInterface::new_with_logical_types(
            REVISION.to_vec(),
            "aapcs64",
            parameters,
            return_kind,
            [],
            parameter_logical_values,
            return_logical_value,
            Some(graph),
        )
        .expect("valid exact source interface");
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch()), interface)
            .expect("prepared aggregate semantic-C artifact")
    }

    fn pointer_parameter() -> SourceAbiParameterSpec {
        SourceAbiParameterSpec::new(0, register_storage(0, 8))
    }

    fn load_return_artifact_with_graph(graph: SourceTypeGraph) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x9000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::register(32, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(48, 8),
        });
        artifact_with_graph(
            block,
            vec![pointer_parameter()],
            vec![pointer_logical()],
            SourceFunctionReturn::Register {
                storage: register_storage(32, 4),
            },
            Some(scalar_logical(SourceCarrierKind::Full)),
            graph,
        )
    }

    fn load_return_artifact() -> SsaArtifact {
        load_return_artifact_with_graph(demo_struct_graph())
    }

    fn store_parameter_artifact() -> SsaArtifact {
        let mut block = R2ILBlock::new(0x9010, 4);
        block.push(R2ILOp::Subpiece {
            dst: Varnode::unique(0x18, 4),
            src: Varnode::register(8, 8),
            offset: 0,
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(52, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x20, 8),
            val: Varnode::unique(0x18, 4),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(48, 8),
        });
        artifact(
            block,
            vec![
                pointer_parameter(),
                SourceAbiParameterSpec::new(1, register_storage(8, 8)),
            ],
            vec![
                pointer_logical(),
                scalar_logical(SourceCarrierKind::LowBits),
            ],
            SourceFunctionReturn::Void,
            None,
        )
    }

    fn read_write_artifact() -> SsaArtifact {
        let mut block = R2ILBlock::new(0x9020, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x40, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x30, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x50, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(52, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x50, 8),
            val: Varnode::unique(0x40, 4),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(48, 8),
        });
        artifact(
            block,
            vec![pointer_parameter()],
            vec![pointer_logical()],
            SourceFunctionReturn::Void,
            None,
        )
    }

    fn assert_machine_context_refused(artifact: &SsaArtifact) {
        assert!(matches!(
            CertifiedAggregateMemberSemanticCFunction::from_artifact(artifact),
            Err(CertifiedAggregateMemberSemanticCFunctionError::Memory(
                CertifiedMemorySemanticCFunctionError::Machine(
                    MachineBuildError::MachineContextMismatch
                )
            ))
        ));
    }

    #[test]
    fn hand_authored_aggregate_fixtures_refuse_renderer_authority() {
        assert_machine_context_refused(&load_return_artifact());
        assert_machine_context_refused(&store_parameter_artifact());
        assert_machine_context_refused(&read_write_artifact());
    }

    #[test]
    fn hand_authored_aggregate_name_variant_refuses_renderer_authority() {
        assert_machine_context_refused(&load_return_artifact_with_graph(
            demo_struct_graph_with_names("CosmeticOnlyRename", "also_cosmetic"),
        ));
    }

    #[test]
    fn hand_authored_unprojected_memory_sibling_refuses_renderer_authority() {
        let mut block = R2ILBlock::new(0x9030, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x60, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x70, 4),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x60, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x80, 4),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x1000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(48, 8),
        });
        let artifact = artifact(
            block,
            vec![pointer_parameter()],
            vec![pointer_logical()],
            SourceFunctionReturn::Void,
            None,
        );
        assert_machine_context_refused(&artifact);
    }
}
