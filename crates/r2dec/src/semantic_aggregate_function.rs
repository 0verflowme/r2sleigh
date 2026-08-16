//! Closed semantic-C functions for exact aggregate member memory accesses.
//!
//! The rendered field expression supplies only a certified byte address to the
//! existing RAM helper ABI. It is never used as an ordinary C load or store.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use r2cert::{
    CertifiedAggregateMemberAccess, CertifiedAggregateMemberAccessSemantics,
    CertifiedArtifactOrigin, CertifiedMachineProjection, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedNaturalScalarAggregateLayout,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalStorageId, InstPayload, MachineBuildError, MachineSignedness,
    MachineValueBinding, MachineValueUse, SSAOp, SourceCarrierKind, SourceFunctionInterface,
    SourceFunctionReturn, SourceTypeGraph, SourceTypeKind, SsaArtifact, StructuredAccessId,
    TrustedSsaArtifact, ValueId,
};
use serde::Serialize;

use crate::semantic_c::{
    SemanticCError, SemanticCFunctionReturn, SemanticCHelper, SemanticCHelperSet,
    SemanticCInputOrigin, SemanticCParameter, insert_semantic_c_helpers, storage_type, value_name,
};
use crate::semantic_memory_function::{
    CertifiedMemorySemanticCFunction, CertifiedMemorySemanticCFunctionError,
    PLAIN_RAM_HELPER_DECLARATIONS, memory_helper_name, private_stack_local_name, render_value_use,
};

pub const CERTIFIED_AGGREGATE_MEMBER_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 = 6;

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
    name: String,
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

    pub fn name(&self) -> &str {
        &self.name
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
    name: String,
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

    pub fn name(&self) -> &str {
        &self.name
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
    name: String,
    storage: CanonicalStorageId,
    binding: Option<MachineValueBinding>,
    kind: CertifiedAggregateSemanticCParameterKind,
}

impl CertifiedAggregateSemanticCParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub fn name(&self) -> &str {
        &self.name
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateElementRenderIndex {
    binding: MachineValueBinding,
    stride_bytes: u64,
    source_parameter_index: Option<u32>,
}

impl CertifiedAggregateElementRenderIndex {
    pub const fn binding(self) -> MachineValueBinding {
        self.binding
    }

    pub const fn stride_bytes(self) -> u64 {
        self.stride_bytes
    }

    pub const fn source_parameter_index(self) -> Option<u32> {
        self.source_parameter_index
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAggregateMemberRenderAccess {
    producer: CanonicalInstructionId,
    access: StructuredAccessId,
    parameter_index: u32,
    member_id: u32,
    member_type_id: u32,
    element_index: Option<CertifiedAggregateElementRenderIndex>,
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

    pub const fn element_index(&self) -> Option<CertifiedAggregateElementRenderIndex> {
        self.element_index
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
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedAggregateMemberSemanticCFunction {
    schema_version: u32,
    scope: CertifiedAggregateMemberSemanticCFunctionScope,
    name: String,
    source_display_name: String,
    source_parameter_names: Box<[Box<str>]>,
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
    address_values: BTreeSet<MachineValueBinding>,
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

fn is_c_keyword(name: &str) -> bool {
    matches!(
        name,
        "auto"
            | "break"
            | "case"
            | "char"
            | "const"
            | "continue"
            | "default"
            | "do"
            | "double"
            | "else"
            | "enum"
            | "extern"
            | "float"
            | "for"
            | "goto"
            | "if"
            | "inline"
            | "int"
            | "long"
            | "register"
            | "restrict"
            | "return"
            | "short"
            | "signed"
            | "sizeof"
            | "static"
            | "struct"
            | "switch"
            | "typedef"
            | "union"
            | "unsigned"
            | "void"
            | "volatile"
            | "while"
            | "_Alignas"
            | "_Alignof"
            | "_Atomic"
            | "_Bool"
            | "_Complex"
            | "_Generic"
            | "_Imaginary"
            | "_Noreturn"
            | "_Static_assert"
            | "_Thread_local"
    )
}

fn c_identifier(source: &str, fallback: impl FnOnce() -> String) -> String {
    let mut rendered = String::with_capacity(source.len());
    for (position, byte) in source.bytes().enumerate() {
        let allowed = byte.is_ascii_alphanumeric() || byte == b'_';
        let starts_identifier = byte.is_ascii_alphabetic() || byte == b'_';
        if allowed && (position != 0 || starts_identifier) {
            rendered.push(char::from(byte));
        } else if allowed {
            rendered.push('_');
            rendered.push(char::from(byte));
        } else {
            rendered.push('_');
        }
    }
    if rendered.is_empty() || is_c_keyword(&rendered) {
        fallback()
    } else {
        rendered
    }
}

fn c_function_identifier(source: &str, fallback: impl FnOnce() -> String) -> String {
    let basename = source
        .rsplit_once('.')
        .map_or(source, |(_, basename)| basename);
    c_identifier(basename, fallback)
}

fn unique_c_identifier(
    source: &str,
    fallback: impl Fn() -> String,
    used: &mut BTreeSet<String>,
) -> String {
    let mut rendered = c_identifier(source, &fallback);
    if used.insert(rendered.clone()) {
        return rendered;
    }
    rendered = fallback();
    let mut suffix = 0_u32;
    while !used.insert(rendered.clone()) {
        suffix = suffix.saturating_add(1);
        rendered = format!("{}_{}", fallback(), suffix);
    }
    rendered
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
    let mut used_member_names = BTreeSet::new();
    let members = layout
        .aggregate()
        .members()
        .iter()
        .zip(layout.member_types())
        .map(|(member, member_type)| {
            Some(CertifiedAggregateStructMemberManifest {
                member_id: member.member_id(),
                name: unique_c_identifier(
                    member.name(),
                    || format!("field_{}", member.member_id()),
                    &mut used_member_names,
                ),
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
        name: c_identifier(layout.aggregate().name(), || {
            format!("r2s_struct_{aggregate_id}")
        }),
        size_bits: layout.aggregate().size_bits(),
        align_bits: layout.aggregate().align_bits(),
        members: members.into_boxed_slice(),
    })
}

fn access_manifest(
    certificate: &CertifiedAggregateMemberAccess,
    source_parameter_index: Option<u32>,
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
        element_index: certificate.element_index().map(|index| {
            CertifiedAggregateElementRenderIndex {
                binding: index.value().binding(),
                stride_bytes: index.stride_bytes(),
                source_parameter_index,
            }
        }),
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
    source_names: &[Box<str>],
    pointer_parameter_index: u32,
    pointer_layout: &CertifiedAggregateStructLayoutManifest,
) -> Option<Vec<CertifiedAggregateSemanticCParameter>> {
    let graph = source.type_graph()?;
    if source.parameters().len() != semantic.len()
        || source.parameters().len() != source.parameter_logical_values().len()
        || source.parameters().len() != source_names.len()
    {
        return None;
    }
    let mut used_names = BTreeSet::new();
    source
        .parameters()
        .iter()
        .zip(source.parameter_logical_values())
        .zip(source_names)
        .map(|((source_parameter, logical), source_name)| {
            let semantic_parameter =
                semantic_parameter_by_index(semantic, source_parameter.index())?;
            let projection = semantic_parameter.projection();
            if semantic_parameter.storage() != source_parameter.storage()
                || projection.source_type_id() != logical.type_id()
                || projection.carrier() != logical.carrier()
                || u64::from(semantic_parameter.ty().width_bits()) != logical.carrier().size_bits()
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
                    || projection.logical_ty().is_some()
                {
                    return None;
                }
                CertifiedAggregateSemanticCParameterKind::AggregatePointer {
                    pointer_type_id: pointer_layout.pointer_type_id,
                    struct_type_id: pointer_layout.struct_type_id,
                }
            } else {
                let signedness = scalar_signedness(source_type.kind())?;
                let logical_ty = projection.logical_ty()?;
                let expected_signedness = match signedness {
                    CertifiedAggregateScalarSignedness::Signed => MachineSignedness::Signed,
                    CertifiedAggregateScalarSignedness::Unsigned => MachineSignedness::Unsigned,
                };
                if carrier.offset_bits() != 0
                    || carrier.size_bits() != source_type.size_bits()
                    || !matches!(source_type.size_bits(), 8 | 16 | 32 | 64)
                    || logical_ty.width_bits() != u32::try_from(source_type.size_bits()).ok()?
                    || logical_ty.signedness() != Some(expected_signedness)
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
                name: unique_c_identifier(
                    source_name,
                    || format!("arg_{}", source_parameter.index()),
                    &mut used_names,
                ),
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

#[derive(Debug, Default)]
struct CertifiedAggregateAddressSlice {
    producers: BTreeSet<CanonicalInstructionId>,
    values: BTreeSet<MachineValueBinding>,
}

fn is_affine_address_transport(payload: &InstPayload) -> bool {
    matches!(
        payload,
        InstPayload::Op(
            SSAOp::Copy { .. }
                | SSAOp::Cast { .. }
                | SSAOp::New { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::IntSExt { .. }
                | SSAOp::Trunc { .. }
                | SSAOp::Subpiece { offset: 0, .. }
                | SSAOp::IntNegate { .. }
                | SSAOp::IntAdd { .. }
                | SSAOp::IntSub { .. }
                | SSAOp::IntMult { .. }
                | SSAOp::IntLeft { .. }
                | SSAOp::PtrAdd { .. }
                | SSAOp::PtrSub { .. }
        )
    )
}

fn collect_address_value(
    artifact: &SsaArtifact,
    access: &CertifiedAggregateMemberRenderAccess,
    value: ValueId,
    visiting: &mut BTreeSet<ValueId>,
    visited: &mut BTreeSet<ValueId>,
    slice: &mut CertifiedAggregateAddressSlice,
) -> Result<(), CertifiedAggregateMemberSemanticCFunctionError> {
    if !visiting.insert(value) {
        return Err(
            CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
        );
    }
    if !visited.insert(value) {
        visiting.remove(&value);
        return Ok(());
    }
    let graph_value = artifact.graph().value(value).ok_or(
        CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
    )?;
    let projection = access.certificate.projection();
    let is_index = access
        .element_index
        .is_some_and(|index| index.binding().value() == value);
    let is_base = artifact
        .addresses()
        .parameter_expression(value)
        .is_some_and(|expression| {
            usize::try_from(projection.source_parameter_index) == Ok(expression.parameter)
                && expression.parameter_storage == Some(access.certificate.parameter().storage())
                && expression.terms.is_empty()
                && expression.offset == 0
        });
    if graph_value.var.constant_bits().is_some() || is_index || is_base {
        visiting.remove(&value);
        return Ok(());
    }
    let definition = artifact.graph().def_inst(value).ok_or(
        CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
    )?;
    let instruction = artifact.graph().inst(definition).ok_or(
        CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
    )?;
    if instruction.output != Some(value) || !is_affine_address_transport(&instruction.payload) {
        return Err(
            CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
        );
    }
    let source = artifact
        .obligations()
        .instruction_for_inst(definition)
        .ok_or(
            CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(access.producer),
        )?;
    slice.producers.insert(source.id);
    slice.values.insert(
        MachineValueUse::from_artifact(artifact, value)
            .map_err(CertifiedAggregateMemberSemanticCFunctionError::Machine)?
            .binding(),
    );
    for input in &instruction.inputs {
        collect_address_value(artifact, access, *input, visiting, visited, slice)?;
    }
    visiting.remove(&value);
    Ok(())
}

fn exact_address_slice(
    artifact: &SsaArtifact,
    accesses: &[CertifiedAggregateMemberRenderAccess],
) -> Result<CertifiedAggregateAddressSlice, CertifiedAggregateMemberSemanticCFunctionError> {
    let mut slice = CertifiedAggregateAddressSlice::default();
    let mut visited = BTreeSet::new();
    for access in accesses {
        collect_address_value(
            artifact,
            access,
            access.address.value(),
            &mut BTreeSet::new(),
            &mut visited,
            &mut slice,
        )?;
    }
    Ok(slice)
}

fn exact_unary_transport_input(
    artifact: &SsaArtifact,
    value: ValueId,
    signedness: CertifiedAggregateScalarSignedness,
    allow_extension: bool,
) -> Option<ValueId> {
    let definition = artifact.graph().def_inst(value)?;
    let instruction = artifact.graph().inst(definition)?;
    let [input] = instruction.inputs.as_slice() else {
        return None;
    };
    let output_width = MachineValueUse::from_artifact(artifact, value)
        .ok()?
        .binding()
        .width_bits();
    let input_width = MachineValueUse::from_artifact(artifact, *input)
        .ok()?
        .binding()
        .width_bits();
    let accepted = match &instruction.payload {
        InstPayload::Op(SSAOp::Copy { .. } | SSAOp::Cast { .. } | SSAOp::New { .. }) => {
            input_width == output_width
        }
        InstPayload::Op(SSAOp::IntSExt { .. }) => {
            allow_extension
                && signedness == CertifiedAggregateScalarSignedness::Signed
                && input_width < output_width
        }
        InstPayload::Op(SSAOp::IntZExt { .. }) => {
            allow_extension
                && signedness == CertifiedAggregateScalarSignedness::Unsigned
                && input_width < output_width
        }
        InstPayload::Phi { .. } | InstPayload::Op(_) => false,
    };
    accepted.then_some(*input)
}

fn exact_transport_reaches(
    artifact: &SsaArtifact,
    mut value: ValueId,
    target: ValueId,
    signedness: CertifiedAggregateScalarSignedness,
    allow_extension: bool,
) -> bool {
    let mut visited = BTreeSet::new();
    while visited.insert(value) {
        if value == target {
            return true;
        }
        let Some(input) = exact_unary_transport_input(artifact, value, signedness, allow_extension)
        else {
            return false;
        };
        value = input;
    }
    false
}

fn exact_index_source_parameter(
    artifact: &SsaArtifact,
    memory: &CertifiedMemorySemanticCFunction,
    parameters: &[CertifiedAggregateSemanticCParameter],
    index: MachineValueBinding,
) -> Option<u32> {
    let mut candidates = BTreeSet::new();
    for parameter in parameters {
        let CertifiedAggregateSemanticCParameterKind::Scalar {
            width_bits,
            signedness,
            ..
        } = parameter.kind
        else {
            continue;
        };
        let Some(parameter_binding) = parameter.binding else {
            continue;
        };
        for local in memory.private_stack_locals() {
            for flow in local.load_flows() {
                let CertifiedMemoryStatementKind::Read { result } = flow.load().statement().kind()
                else {
                    continue;
                };
                if result.binding().width_bits() != u32::try_from(width_bits).ok()?
                    || !exact_transport_reaches(
                        artifact,
                        index.value(),
                        result.binding().value(),
                        signedness,
                        true,
                    )
                {
                    continue;
                }
                let Some(store) = flow
                    .definition(flow.root_version())
                    .and_then(|item| item.store())
                else {
                    continue;
                };
                let CertifiedMemoryStatementKind::Write { value } = store.statement().kind() else {
                    continue;
                };
                if value.binding().width_bits() == parameter_binding.width_bits()
                    && exact_transport_reaches(
                        artifact,
                        value.binding().value(),
                        parameter_binding.value(),
                        signedness,
                        false,
                    )
                {
                    candidates.insert(parameter.index);
                }
            }
        }
    }
    let mut candidates = candidates.into_iter();
    let parameter = candidates.next()?;
    candidates.next().is_none().then_some(parameter)
}

impl CertifiedAggregateMemberSemanticCFunction {
    pub fn from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, CertifiedAggregateMemberSemanticCFunctionError> {
        let artifact = trusted.artifact();
        let memory = CertifiedMemorySemanticCFunction::from_artifact_for_typed_layer(trusted)?;
        let certified = CertifiedMachineProjection::from_artifact(trusted)?;
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

        let private_stack = memory.private_stack_access_map()?;
        let non_private_memory_order = memory.non_private_memory_order()?;
        let mut accesses = Vec::new();
        for step in memory.layer().steps() {
            let Some(reference) = step.memory() else {
                continue;
            };
            let statement = memory.layer().resolve_memory_statement(reference).ok_or(
                CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(step.source()),
            )?;
            if private_stack.contains_key(&step.source()) {
                continue;
            }
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
            accesses.push(access_manifest(certificate, None).ok_or(
                CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(step.source()),
            )?);
        }
        if accesses.is_empty()
            || accesses.len() != non_private_memory_order.len()
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
        let revision = first.certificate.interface_revision().to_vec();
        let graph = first.certificate.source_type_graph();
        if accesses.iter().any(|access| {
            access.parameter_index != pointer_parameter_index
                || access.certificate.interface_revision() != revision.as_slice()
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
        if source_interface.revision_identity() != revision.as_slice()
            || source_interface.type_graph() != Some(graph)
        {
            return Err(
                CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                    "aggregate source interface differs from its certificates".to_string(),
                ]),
            );
        }

        let source_display_name = trusted.source().presentation().display_name().to_string();
        let source_parameter_names = trusted.source().presentation().parameter_names().to_vec();
        let parameters = parameter_manifests(
            &source_interface,
            semantic_interface.parameters(),
            trusted.source().presentation().parameter_names(),
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
        for access in &mut accesses {
            if let Some(index) = access.element_index.as_mut() {
                index.source_parameter_index =
                    exact_index_source_parameter(artifact, &memory, &parameters, index.binding);
            }
        }
        let returned_binding = returned_binding(&memory)
            .ok_or(CertifiedAggregateMemberSemanticCFunctionError::InvalidReturn)?;
        let return_kind = return_manifest(
            &source_interface,
            semantic_interface.return_kind(),
            returned_binding,
        )
        .ok_or(CertifiedAggregateMemberSemanticCFunctionError::InvalidReturn)?;
        let address_slice = exact_address_slice(artifact, &accesses)?;
        for producer in &address_slice.producers {
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
                    .is_none_or(|entity| !address_slice.values.contains(&entity.output()))
            {
                return Err(
                    CertifiedAggregateMemberSemanticCFunctionError::UnsupportedAddress(*producer),
                );
            }
        }

        let fallback_name = || {
            format!(
                "certified_aggregate_sub_{:x}",
                memory.layer().accounting().block_addr()
            )
        };
        let mut name = c_function_identifier(&source_display_name, fallback_name);
        if name == layout.name {
            name = fallback_name();
        }
        let function = Self {
            schema_version: CERTIFIED_AGGREGATE_MEMBER_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope: CertifiedAggregateMemberSemanticCFunctionScope::SingleTerminalReturnBlockWithExactAggregateMembers,
            name,
            source_display_name,
            source_parameter_names: source_parameter_names.into_boxed_slice(),
            origin: memory_origin.clone(),
            interface_revision: revision.into_boxed_slice(),
            source_interface,
            pointer_parameter_index,
            layout,
            parameters: parameters.into_boxed_slice(),
            return_kind,
            memory_order: non_private_memory_order.into_boxed_slice(),
            accesses: accesses.into_boxed_slice(),
            address_producers: address_slice.producers,
            address_values: address_slice.values,
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
        let fallback_name = || {
            format!(
                "certified_aggregate_sub_{:x}",
                self.memory.layer().accounting().block_addr()
            )
        };
        let mut expected_name = c_function_identifier(&self.source_display_name, fallback_name);
        if expected_name == self.layout.name {
            expected_name = fallback_name();
        }
        if self.name != expected_name {
            invalid.push("aggregate function presentation mismatch".to_string());
        }
        let Some(semantic_interface) = semantic_interface else {
            invalid.push("aggregate function has no semantic interface".to_string());
            return CertifiedAggregateMemberSemanticCFunctionAuditReport { invalid };
        };
        let expected_parameters = parameter_manifests(
            &self.source_interface,
            semantic_interface.parameters(),
            &self.source_parameter_names,
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
        match self.memory.non_private_memory_order() {
            Ok(order) if self.memory_order.as_ref() == order.as_slice() => {}
            _ => invalid.push("aggregate memory order mismatch".to_string()),
        }
        let expected_address_values = self
            .address_producers
            .iter()
            .filter_map(|producer| {
                self.memory
                    .layer()
                    .steps()
                    .iter()
                    .find(|step| step.source() == *producer)
                    .and_then(|step| step.value())
                    .and_then(|reference| self.memory.layer().resolve_value(reference))
                    .map(|entity| entity.output())
            })
            .collect::<BTreeSet<_>>();
        if expected_address_values != self.address_values
            || expected_address_values.len() != self.address_producers.len()
        {
            invalid.push("aggregate address-slice manifest mismatch".to_string());
        }
        if self.accesses.len() != self.memory_order.len() {
            invalid.push("aggregate access count differs from memory count".to_string());
        }
        for (position, access) in self.accesses.iter().enumerate() {
            let source_parameter_index = access
                .element_index
                .and_then(CertifiedAggregateElementRenderIndex::source_parameter_index);
            let expected = access_manifest(&access.certificate, source_parameter_index);
            if expected.as_ref() != Some(access) {
                invalid.push(format!("aggregate access manifest mismatch at {position}"));
            }
            if source_parameter_index.is_some_and(|source_parameter_index| {
                self.parameters.iter().all(|parameter| {
                    parameter.index != source_parameter_index
                        || !matches!(
                            parameter.kind,
                            CertifiedAggregateSemanticCParameterKind::Scalar { .. }
                        )
                })
            }) {
                invalid.push(format!(
                    "aggregate index source parameter mismatch at {position}"
                ));
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
        let mut defined = self
            .parameters
            .iter()
            .filter_map(|parameter| parameter.binding)
            .collect::<BTreeSet<_>>();
        let expressions = self.memory.layer().accounting().expression_layer();
        let mut materialized = expressions.materialized_expression_roots(&defined)?;
        let private_stack = self.memory.private_stack_access_map()?;
        let private_stack_address_producers = self.memory.private_stack_address_producers();
        let private_stack_transport_producers = self.memory.private_stack_transport_producers();
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
                if private_stack.contains_key(&step.source()) {
                    if let CertifiedMemoryStatementKind::Read { result } = statement.kind() {
                        defined.insert(result.binding());
                        let root = expressions.memory_read_root(statement)?;
                        if root.is_some_and(|root| {
                            materialized.insert(root, result.binding()).is_some()
                        }) {
                            return Err(
                                CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                                    step.source(),
                                ),
                            );
                        }
                    }
                    continue;
                }
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
                    || access
                        .element_index
                        .is_some_and(|index| !defined.contains(&index.binding()))
                {
                    return Err(
                        CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                            step.source(),
                        ),
                    );
                }
                if let CertifiedMemoryStatementKind::Read { result } = statement.kind() {
                    defined.insert(result.binding());
                    let root = expressions.memory_read_root(statement)?;
                    if root
                        .is_some_and(|root| materialized.insert(root, result.binding()).is_some())
                    {
                        return Err(
                            CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                                step.source(),
                            ),
                        );
                    }
                }
                observed.push(step.source());
                continue;
            }
            if private_stack_address_producers.contains(&step.source())
                || private_stack_transport_producers.contains(&step.source())
            {
                continue;
            }
            if self.address_producers.contains(&step.source()) {
                let entity = step
                    .value()
                    .and_then(|reference| self.memory.layer().resolve_value(reference));
                if entity.is_none_or(|entity| !self.address_values.contains(&entity.output())) {
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
                expressions.render_expr_with_materialized_roots(
                    entity.root(),
                    &materialized,
                    &mut SemanticCHelperSet::default(),
                )?;
                defined.insert(entity.output());
                if materialized
                    .insert(entity.root(), entity.output())
                    .is_some()
                {
                    return Err(
                        CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![
                            format!("duplicate materialized value for {}", step.source()),
                        ]),
                    );
                }
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
        let mut helpers = SemanticCHelperSet::default();
        output.push_str("#include <stddef.h>\n#include <stdint.h>\n\n");
        let helper_insertion = output.len();
        output.push('\n');
        output.push_str(PLAIN_RAM_HELPER_DECLARATIONS);
        output.push('\n');
        self.render_layout(&mut output)?;
        self.render_signature(&mut output)?;
        let mut defined = BTreeSet::new();
        for parameter in &self.parameters {
            let argument_name = &parameter.name;
            match &parameter.kind {
                CertifiedAggregateSemanticCParameterKind::AggregatePointer { .. } => {
                    if let Some(binding) = parameter.binding {
                        writeln!(
                            &mut output,
                            "\tuint64_t {} = (uint64_t)(uintptr_t){argument_name};",
                            value_name(binding),
                        )
                        .expect("String writes cannot fail");
                        defined.insert(binding);
                    } else {
                        writeln!(&mut output, "\t(void){argument_name};")
                            .expect("String writes cannot fail");
                    }
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
                        defined.insert(binding);
                    }
                }
            }
        }
        let mut materialized = expressions.materialized_expression_roots(&defined)?;
        let private_stack = self.memory.private_stack_access_map()?;
        let private_stack_address_producers = self.memory.private_stack_address_producers();
        let private_stack_transport_producers = self.memory.private_stack_transport_producers();
        let mut initialized_private_stack = BTreeSet::new();
        for step in self.memory.layer().steps() {
            if let Some(reference) = step.memory() {
                let statement = self
                    .memory
                    .layer()
                    .resolve_memory_statement(reference)
                    .expect("audited memory statement");
                if let Some(local) = private_stack.get(&step.source()) {
                    let local_name = private_stack_local_name(local);
                    match statement.kind() {
                        CertifiedMemoryStatementKind::Read { result } => {
                            let root = expressions.memory_read_root(statement)?;
                            let ty = storage_type(result.ty())?;
                            writeln!(
                                &mut output,
                                "\t{ty} {} = ({ty}){local_name};",
                                value_name(result.binding()),
                            )
                            .expect("String writes cannot fail");
                            writeln!(&mut output, "\t(void){};", value_name(result.binding()))
                                .expect("String writes cannot fail");
                            defined.insert(result.binding());
                            if root.is_some_and(|root| {
                                materialized.insert(root, result.binding()).is_some()
                            }) {
                                return Err(
                                    CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                                        step.source(),
                                    ),
                                );
                            }
                        }
                        CertifiedMemoryStatementKind::Write { value } => {
                            let ty = storage_type(value.ty())?;
                            if initialized_private_stack.insert(local.local_index()) {
                                writeln!(
                                    &mut output,
                                    "\t{ty} {local_name} = ({ty})({});",
                                    render_value_use(value),
                                )
                                .expect("String writes cannot fail");
                            } else {
                                writeln!(
                                    &mut output,
                                    "\t{local_name} = ({ty})({});",
                                    render_value_use(value),
                                )
                                .expect("String writes cannot fail");
                            }
                        }
                    }
                    continue;
                }
                let access = self
                    .accesses
                    .iter()
                    .find(|access| access.producer == step.source())
                    .expect("audited aggregate access");
                let helper = memory_helper_name(statement);
                let pointer = self
                    .parameters
                    .iter()
                    .find(|parameter| parameter.index == access.parameter_index)
                    .map(|parameter| parameter.name.as_str())
                    .expect("audited aggregate pointer parameter");
                let field = self
                    .layout
                    .members
                    .iter()
                    .find(|member| member.member_id == access.member_id)
                    .map(|member| member.name.as_str())
                    .expect("audited aggregate member");
                let qualifier = if matches!(
                    access.direction,
                    CertifiedAggregateMemberRenderDirection::Read { .. }
                ) {
                    "const uint8_t"
                } else {
                    "uint8_t"
                };
                let member = access.element_index.map_or_else(
                    || format!("{pointer}->{field}"),
                    |index| {
                        let rendered_index = index
                            .source_parameter_index()
                            .and_then(|source_parameter_index| {
                                self.parameters
                                    .iter()
                                    .find(|parameter| parameter.index == source_parameter_index)
                            })
                            .map_or_else(
                                || value_name(index.binding()),
                                |parameter| parameter.name.clone(),
                            );
                        format!("{pointer}[{rendered_index}].{field}")
                    },
                );
                let address = format!("((uint64_t)(uintptr_t)(({qualifier} *)&{member}))");
                match statement.kind() {
                    CertifiedMemoryStatementKind::Read { result } => {
                        let root = expressions.memory_read_root(statement)?;
                        writeln!(
                            &mut output,
                            "\t{} {} = {helper}({address});",
                            storage_type(result.ty())?,
                            value_name(result.binding())
                        )
                        .expect("String writes cannot fail");
                        writeln!(&mut output, "\t(void){};", value_name(result.binding()))
                            .expect("String writes cannot fail");
                        defined.insert(result.binding());
                        if root.is_some_and(|root| {
                            materialized.insert(root, result.binding()).is_some()
                        }) {
                            return Err(
                                CertifiedAggregateMemberSemanticCFunctionError::MissingAggregate(
                                    step.source(),
                                ),
                            );
                        }
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
            if private_stack_address_producers.contains(&step.source())
                || private_stack_transport_producers.contains(&step.source())
            {
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
                expressions.render_expr_with_materialized_roots(
                    entity.root(),
                    &materialized,
                    &mut helpers,
                )?
            )
            .expect("String writes cannot fail");
            writeln!(&mut output, "\t(void){};", value_name(entity.output()))
                .expect("String writes cannot fail");
            defined.insert(entity.output());
            if materialized
                .insert(entity.root(), entity.output())
                .is_some()
            {
                return Err(
                    CertifiedAggregateMemberSemanticCFunctionError::InvalidFunction(vec![format!(
                        "duplicate materialized value for {}",
                        step.source()
                    )]),
                );
            }
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
                    CertifiedAggregateScalarSignedness::Signed => {
                        let helper = match width_bits {
                            8 => SemanticCHelper::I8FromBits,
                            16 => SemanticCHelper::I16FromBits,
                            32 => SemanticCHelper::I32FromBits,
                            64 => SemanticCHelper::I64FromBits,
                            _ => {
                                return Err(
                                    CertifiedAggregateMemberSemanticCFunctionError::InvalidReturn,
                                );
                            }
                        };
                        helpers.insert(helper);
                        writeln!(
                            &mut output,
                            "\treturn {}((uint{width_bits}_t)({value}));",
                            helper.call_name()
                        )
                        .expect("String writes cannot fail")
                    }
                }
            }
        }
        output.push_str("}\n");
        insert_semantic_c_helpers(&mut output, helper_insertion, &helpers);
        Ok(output)
    }

    fn render_layout(
        &self,
        output: &mut String,
    ) -> Result<(), CertifiedAggregateMemberSemanticCFunctionError> {
        let struct_name = &self.layout.name;
        writeln!(output, "typedef struct {struct_name} {{").expect("String writes cannot fail");
        for member in &self.layout.members {
            writeln!(
                output,
                "\t{} {};",
                scalar_c_type(member.signedness, member.size_bits)?,
                member.name
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
                "_Static_assert(offsetof({struct_name}, {}) == {}U, \"member offset mismatch\");",
                member.name,
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
                CertifiedAggregateSemanticCParameterKind::AggregatePointer { .. } => {
                    write!(output, "{} *{}", self.layout.name, parameter.name)
                        .expect("String writes cannot fail")
                }
                CertifiedAggregateSemanticCParameterKind::Scalar {
                    width_bits,
                    signedness,
                    ..
                } => write!(
                    output,
                    "{} {}",
                    scalar_c_type(signedness, width_bits)?,
                    parameter.name
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

#[cfg(test)]
mod tests {
    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };
    use r2ssa::{
        CanonicalStorageSpace, MachineType, SourceAbiParameterSpec, SourceAggregateLayout,
        SourceAggregateMember, SourceCarrierProjection, SourceLogicalValue, SourceType,
    };

    use super::*;
    use crate::semantic_c::validated_semantic_parameter_for_test;

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

    fn parameter_manifest_graph(
        parameter_type_id: u32,
        parameter_kind: SourceTypeKind,
        parameter_bits: u64,
    ) -> SourceTypeGraph {
        let member_type_id = if parameter_type_id == 1 { 3 } else { 1 };
        let scalar = |id| {
            if id == parameter_type_id {
                SourceType::new(id, parameter_kind, parameter_bits, parameter_bits)
            } else {
                SourceType::new(id, SourceTypeKind::SignedInteger, 32, 32)
            }
        };
        SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 56 * 8, 32),
                scalar(1),
                SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                scalar(3),
            ],
            [SourceAggregateLayout::new(
                0,
                0,
                56 * 8,
                32,
                "TestOnlyAggregate",
                (0..14).map(|index| {
                    SourceAggregateMember::new(
                        index,
                        member_type_id,
                        u64::from(index) * 32,
                        32,
                        format!("member_{index}"),
                    )
                }),
            )],
        )
        .expect("valid parameter-manifest source graph")
    }

    fn parameter_manifest_source(
        parameter_type_id: u32,
        parameter_kind: SourceTypeKind,
        parameter_bits: u64,
        carrier_kind: SourceCarrierKind,
    ) -> SourceFunctionInterface {
        SourceFunctionInterface::new_with_logical_types(
            REVISION.to_vec(),
            "aapcs64",
            [
                pointer_parameter(),
                SourceAbiParameterSpec::new(1, register_storage(8, 8)),
            ],
            SourceFunctionReturn::Void,
            [],
            [
                pointer_logical(),
                SourceLogicalValue::new(
                    parameter_type_id,
                    SourceCarrierProjection::new(carrier_kind, 0, parameter_bits),
                ),
            ],
            None,
            Some(parameter_manifest_graph(
                parameter_type_id,
                parameter_kind,
                parameter_bits,
            )),
        )
        .expect("valid parameter-manifest source interface")
    }

    fn parameter_manifest_layout() -> CertifiedAggregateStructLayoutManifest {
        CertifiedAggregateStructLayoutManifest {
            pointer_type_id: 2,
            struct_type_id: 0,
            aggregate_id: 0,
            name: "TestOnlyAggregate".to_string(),
            size_bits: 56 * 8,
            align_bits: 32,
            members: (0..14)
                .map(|member_id| CertifiedAggregateStructMemberManifest {
                    member_id,
                    name: format!("member_{member_id}"),
                    type_id: 3,
                    offset_bits: u64::from(member_id) * 32,
                    size_bits: 32,
                    align_bits: 32,
                    signedness: CertifiedAggregateScalarSignedness::Signed,
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        }
    }

    fn validated_manifest_parameters(
        source: &SourceFunctionInterface,
    ) -> Result<Vec<SemanticCParameter>, SemanticCError> {
        let unsigned = |width_bits| MachineType::Integer {
            width_bits,
            signedness: MachineSignedness::Unsigned,
        };
        Ok(vec![
            validated_semantic_parameter_for_test(
                source,
                0,
                register_storage(0, 8),
                None,
                unsigned(64),
            )?,
            validated_semantic_parameter_for_test(
                source,
                1,
                CanonicalStorageId {
                    size: u32::try_from(
                        source.parameter_logical_values()[1].carrier().size_bits() / 8,
                    )
                    .map_err(|_| SemanticCError::InvalidCertifiedFunctionInterface)?,
                    ..register_storage(8, 8)
                },
                None,
                unsigned(
                    u32::try_from(source.parameter_logical_values()[1].carrier().size_bits())
                        .map_err(|_| SemanticCError::InvalidCertifiedFunctionInterface)?,
                ),
            )?,
        ])
    }

    fn manifest_parameter_names() -> Box<[Box<str>]> {
        [Box::<str>::from("pointer"), Box::<str>::from("scalar")].into()
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

    fn assert_hand_authored_non_authoritative(artifact: &SsaArtifact) {
        assert_eq!(
            artifact.provenance_kind(),
            r2ssa::SsaArtifactProvenanceKind::Manual
        );
    }

    #[test]
    fn exact_parameter_manifest_accepts_pointer_and_signed_low_bits_scalar() {
        let source = parameter_manifest_source(
            1,
            SourceTypeKind::SignedInteger,
            32,
            SourceCarrierKind::LowBits,
        );
        let semantic = validated_manifest_parameters(&source)
            .expect("production-validated semantic parameters");
        assert_eq!(semantic[0].projection().logical_ty(), None);
        assert_eq!(semantic[0].storage(), register_storage(0, 8));
        assert_eq!(semantic[0].ty().width_bits(), 64);
        assert_eq!(semantic[1].storage(), register_storage(8, 8));
        assert_eq!(semantic[1].ty().width_bits(), 32);
        assert_eq!(
            semantic[1].projection().logical_ty(),
            Some(&MachineType::Integer {
                width_bits: 32,
                signedness: MachineSignedness::Signed,
            })
        );
        let names = manifest_parameter_names();
        let manifest =
            parameter_manifests(&source, &semantic, &names, 0, &parameter_manifest_layout())
                .expect("exact aggregate parameter manifest");
        let [pointer, scalar] = manifest.as_slice() else {
            panic!("exact pointer and scalar parameter manifests")
        };
        assert_eq!(pointer.name(), "pointer");
        assert_eq!(scalar.name(), "scalar");
        assert!(matches!(
            pointer.kind(),
            CertifiedAggregateSemanticCParameterKind::AggregatePointer {
                pointer_type_id: 2,
                struct_type_id: 0,
            }
        ));
        assert!(matches!(
            scalar.kind(),
            CertifiedAggregateSemanticCParameterKind::Scalar {
                type_id: 1,
                width_bits: 32,
                signedness: CertifiedAggregateScalarSignedness::Signed,
                carrier_kind: SourceCarrierKind::LowBits,
                carrier_width_bits: 64,
            }
        ));
    }

    #[test]
    fn source_presentation_names_are_c_safe_and_collision_free() {
        assert_eq!(c_function_identifier("dbg.test.name", String::new), "name");
        assert_eq!(
            c_identifier("struct", || "fallback".to_string()),
            "fallback"
        );
        assert_eq!(c_identifier("9lives", String::new), "_9lives");
        assert_eq!(c_identifier("field-name", String::new), "field_name");

        let mut used = BTreeSet::new();
        assert_eq!(
            unique_c_identifier("field-name", || "field_0".to_string(), &mut used),
            "field_name"
        );
        assert_eq!(
            unique_c_identifier("field_name", || "field_1".to_string(), &mut used),
            "field_1"
        );
    }

    #[test]
    fn exact_parameter_manifest_refuses_graph_projection_and_source_mutations() {
        let source = parameter_manifest_source(
            1,
            SourceTypeKind::SignedInteger,
            32,
            SourceCarrierKind::LowBits,
        );
        let semantic = validated_manifest_parameters(&source)
            .expect("production-validated semantic parameters");
        assert_eq!(
            validated_semantic_parameter_for_test(
                &source,
                1,
                register_storage(8, 8),
                None,
                MachineType::Integer {
                    width_bits: 64,
                    signedness: MachineSignedness::Unsigned,
                },
            ),
            Err(SemanticCError::InvalidCertifiedFunctionInterface),
            "a 32-bit LowBits carrier cannot acquire a 64-bit graph projection"
        );

        let type_id_mutation = parameter_manifest_source(
            3,
            SourceTypeKind::SignedInteger,
            32,
            SourceCarrierKind::LowBits,
        );
        assert_eq!(
            parameter_manifests(
                &type_id_mutation,
                &semantic,
                &manifest_parameter_names(),
                0,
                &parameter_manifest_layout(),
            ),
            None,
            "the sealed projection type ID must match the source logical value"
        );

        let full_width_source = parameter_manifest_source(
            1,
            SourceTypeKind::SignedInteger,
            64,
            SourceCarrierKind::Full,
        );
        let full_width_semantic = validated_manifest_parameters(&full_width_source)
            .expect("valid alternate full-width projection");
        assert_eq!(
            parameter_manifests(
                &source,
                &full_width_semantic,
                &manifest_parameter_names(),
                0,
                &parameter_manifest_layout(),
            ),
            None,
            "the sealed Full64 carrier cannot satisfy a LowBits32 source value"
        );

        let unsigned_source = parameter_manifest_source(
            1,
            SourceTypeKind::UnsignedInteger,
            32,
            SourceCarrierKind::LowBits,
        );
        let unsigned_semantic = validated_manifest_parameters(&unsigned_source)
            .expect("valid alternate unsigned projection");
        assert_eq!(
            parameter_manifests(
                &source,
                &unsigned_semantic,
                &manifest_parameter_names(),
                0,
                &parameter_manifest_layout(),
            ),
            None,
            "the sealed unsigned logical type cannot satisfy signed source authority"
        );
    }

    #[test]
    fn hand_authored_aggregate_fixtures_refuse_renderer_authority() {
        assert_hand_authored_non_authoritative(&load_return_artifact());
        assert_hand_authored_non_authoritative(&store_parameter_artifact());
        assert_hand_authored_non_authoritative(&read_write_artifact());
    }

    #[test]
    fn hand_authored_aggregate_name_variant_refuses_renderer_authority() {
        assert_hand_authored_non_authoritative(&load_return_artifact_with_graph(
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
        assert_hand_authored_non_authoritative(&artifact);
    }
}
