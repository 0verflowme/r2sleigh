//! Immutable machine context captured with an SSA artifact.
//!
//! Legacy `SSAOp` memory-space strings are presentation data and cannot serve
//! as proof. This snapshot retains the typed r2il address space at each source
//! operation site together with the architecture memory model used to lift it.

use std::collections::{BTreeMap, BTreeSet};

use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, SpaceId, effective_arch_address_size};
use serde::Serialize;

use crate::function::SSAFunction;
use crate::op::SSAOp;
use crate::semantic::CallSiteId;
use crate::{CanonicalStorageId, CanonicalStorageSpace, StackAddressBase};

pub const MACHINE_CONTEXT_SCHEMA_VERSION: u32 = 8;
pub const SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION: u32 = 5;
pub const SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION: u32 = 1;
pub const SOURCE_TYPE_GRAPH_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceTypeKind {
    SignedInteger,
    UnsignedInteger,
    Pointer { target_type_id: u32 },
    Struct { aggregate_id: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceType {
    id: u32,
    kind: SourceTypeKind,
    size_bits: u64,
    align_bits: u64,
}

impl SourceType {
    pub const fn new(id: u32, kind: SourceTypeKind, size_bits: u64, align_bits: u64) -> Self {
        Self {
            id,
            kind,
            size_bits,
            align_bits,
        }
    }

    pub const fn id(&self) -> u32 {
        self.id
    }

    pub const fn kind(&self) -> SourceTypeKind {
        self.kind
    }

    pub const fn size_bits(&self) -> u64 {
        self.size_bits
    }

    pub const fn align_bits(&self) -> u64 {
        self.align_bits
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceCarrierKind {
    Full,
    LowBits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SourceCarrierProjection {
    kind: SourceCarrierKind,
    offset_bits: u64,
    size_bits: u64,
}

impl SourceCarrierProjection {
    pub const fn new(kind: SourceCarrierKind, offset_bits: u64, size_bits: u64) -> Self {
        Self {
            kind,
            offset_bits,
            size_bits,
        }
    }

    pub const fn kind(&self) -> SourceCarrierKind {
        self.kind
    }

    pub const fn offset_bits(&self) -> u64 {
        self.offset_bits
    }

    pub const fn size_bits(&self) -> u64 {
        self.size_bits
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SourceLogicalValue {
    type_id: u32,
    carrier: SourceCarrierProjection,
}

impl SourceLogicalValue {
    pub const fn new(type_id: u32, carrier: SourceCarrierProjection) -> Self {
        Self { type_id, carrier }
    }

    pub const fn type_id(self) -> u32 {
        self.type_id
    }

    pub const fn carrier(&self) -> SourceCarrierProjection {
        self.carrier
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceAggregateMember {
    member_id: u32,
    type_id: u32,
    offset_bits: u64,
    size_bits: u64,
    name: String,
}

impl SourceAggregateMember {
    pub fn new(
        member_id: u32,
        type_id: u32,
        offset_bits: u64,
        size_bits: u64,
        name: impl Into<String>,
    ) -> Self {
        Self {
            member_id,
            type_id,
            offset_bits,
            size_bits,
            name: name.into(),
        }
    }

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

    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceAggregateLayout {
    id: u32,
    type_id: u32,
    size_bits: u64,
    align_bits: u64,
    name: String,
    members: Box<[SourceAggregateMember]>,
}

impl SourceAggregateLayout {
    pub fn new(
        id: u32,
        type_id: u32,
        size_bits: u64,
        align_bits: u64,
        name: impl Into<String>,
        members: impl IntoIterator<Item = SourceAggregateMember>,
    ) -> Self {
        Self {
            id,
            type_id,
            size_bits,
            align_bits,
            name: name.into(),
            members: members.into_iter().collect::<Vec<_>>().into_boxed_slice(),
        }
    }

    pub const fn id(&self) -> u32 {
        self.id
    }

    pub const fn type_id(&self) -> u32 {
        self.type_id
    }

    pub const fn size_bits(&self) -> u64 {
        self.size_bits
    }

    pub const fn align_bits(&self) -> u64 {
        self.align_bits
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn members(&self) -> &[SourceAggregateMember] {
        &self.members
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceTypeGraph {
    schema_version: u32,
    types: Box<[SourceType]>,
    aggregates: Box<[SourceAggregateLayout]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceTypeGraphError {
    Empty,
    InvalidType,
    InvalidAggregate,
    InvalidMember,
}

impl std::fmt::Display for SourceTypeGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid source type graph: {self:?}")
    }
}

impl std::error::Error for SourceTypeGraphError {}

fn source_align_up(value: u64, alignment: u64) -> Option<u64> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return None;
    }
    let mask = alignment - 1;
    value.checked_add(mask).map(|aligned| aligned & !mask)
}

impl SourceTypeGraph {
    pub fn new(
        types: impl IntoIterator<Item = SourceType>,
        aggregates: impl IntoIterator<Item = SourceAggregateLayout>,
    ) -> Result<Self, SourceTypeGraphError> {
        let types = types.into_iter().collect::<Vec<_>>();
        let aggregates = aggregates.into_iter().collect::<Vec<_>>();
        if types.is_empty() {
            return Err(SourceTypeGraphError::Empty);
        }
        for (position, source_type) in types.iter().enumerate() {
            if u32::try_from(position) != Ok(source_type.id)
                || source_type.size_bits == 0
                || source_type.size_bits % 8 != 0
                || source_type.align_bits == 0
                || source_type.align_bits % 8 != 0
                || !source_type.align_bits.is_power_of_two()
                || source_type.align_bits > source_type.size_bits
            {
                return Err(SourceTypeGraphError::InvalidType);
            }
            match source_type.kind {
                SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger => {
                    if !matches!(source_type.size_bits, 8 | 16 | 32 | 64)
                        || source_type.align_bits != source_type.size_bits
                    {
                        return Err(SourceTypeGraphError::InvalidType);
                    }
                }
                SourceTypeKind::Pointer { target_type_id } => {
                    if source_type.size_bits != 64
                        || source_type.align_bits != 64
                        || usize::try_from(target_type_id)
                            .ok()
                            .and_then(|id| types.get(id))
                            .is_none_or(|target| {
                                matches!(target.kind, SourceTypeKind::Pointer { .. })
                            })
                    {
                        return Err(SourceTypeGraphError::InvalidType);
                    }
                }
                SourceTypeKind::Struct { aggregate_id } => {
                    if usize::try_from(aggregate_id)
                        .ok()
                        .is_none_or(|id| id >= aggregates.len())
                    {
                        return Err(SourceTypeGraphError::InvalidType);
                    }
                }
            }
        }
        for (position, aggregate) in aggregates.iter().enumerate() {
            if u32::try_from(position) != Ok(aggregate.id)
                || usize::try_from(aggregate.type_id)
                    .ok()
                    .and_then(|id| types.get(id))
                    .is_none_or(|source_type| {
                        source_type.size_bits != aggregate.size_bits
                            || source_type.align_bits != aggregate.align_bits
                            || source_type.kind
                                != (SourceTypeKind::Struct {
                                    aggregate_id: aggregate.id,
                                })
                    })
                || aggregate.members.is_empty()
            {
                return Err(SourceTypeGraphError::InvalidAggregate);
            }
            let mut cursor = 0u64;
            let mut maximum_alignment = 0u64;
            for (member_position, member) in aggregate.members.iter().enumerate() {
                let Some(member_type) = usize::try_from(member.type_id)
                    .ok()
                    .and_then(|id| types.get(id))
                else {
                    return Err(SourceTypeGraphError::InvalidMember);
                };
                if u32::try_from(member_position) != Ok(member.member_id)
                    || !matches!(
                        member_type.kind,
                        SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger
                    )
                    || member.size_bits != member_type.size_bits
                    || member.offset_bits % 8 != 0
                    || source_align_up(cursor, member_type.align_bits) != Some(member.offset_bits)
                {
                    return Err(SourceTypeGraphError::InvalidMember);
                }
                cursor = member
                    .offset_bits
                    .checked_add(member.size_bits)
                    .ok_or(SourceTypeGraphError::InvalidMember)?;
                maximum_alignment = maximum_alignment.max(member_type.align_bits);
            }
            if maximum_alignment != aggregate.align_bits
                || source_align_up(cursor, maximum_alignment) != Some(aggregate.size_bits)
            {
                return Err(SourceTypeGraphError::InvalidAggregate);
            }
        }
        if types
            .iter()
            .filter(|source_type| matches!(source_type.kind, SourceTypeKind::Struct { .. }))
            .count()
            != aggregates.len()
        {
            return Err(SourceTypeGraphError::InvalidAggregate);
        }
        Ok(Self {
            schema_version: SOURCE_TYPE_GRAPH_SCHEMA_VERSION,
            types: types.into_boxed_slice(),
            aggregates: aggregates.into_boxed_slice(),
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn types(&self) -> &[SourceType] {
        &self.types
    }

    pub const fn aggregates(&self) -> &[SourceAggregateLayout] {
        &self.aggregates
    }

    fn validates_logical_value(&self, value: SourceLogicalValue, carrier_size_bytes: u32) -> bool {
        let Some(source_type) = usize::try_from(value.type_id)
            .ok()
            .and_then(|id| self.types.get(id))
        else {
            return false;
        };
        let carrier_bits = u64::from(carrier_size_bytes) * 8;
        if value.carrier.offset_bits != 0
            || value.carrier.size_bits != source_type.size_bits
            || source_type.size_bits > carrier_bits
        {
            return false;
        }
        match value.carrier.kind {
            SourceCarrierKind::Full => source_type.size_bits == carrier_bits,
            SourceCarrierKind::LowBits => {
                source_type.size_bits < carrier_bits
                    && matches!(
                        source_type.kind,
                        SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger
                    )
            }
        }
    }

    fn all_types_reachable(&self, roots: impl IntoIterator<Item = u32>) -> bool {
        let mut reachable = BTreeSet::new();
        let mut worklist = Vec::new();
        for root in roots {
            if usize::try_from(root)
                .ok()
                .is_none_or(|id| id >= self.types.len())
            {
                return false;
            }
            if reachable.insert(root) {
                worklist.push(root);
            }
        }
        while let Some(type_id) = worklist.pop() {
            match self.types[type_id as usize].kind {
                SourceTypeKind::Pointer { target_type_id } => {
                    if reachable.insert(target_type_id) {
                        worklist.push(target_type_id);
                    }
                }
                SourceTypeKind::Struct { aggregate_id } => {
                    for member in &self.aggregates[aggregate_id as usize].members {
                        if reachable.insert(member.type_id) {
                            worklist.push(member.type_id);
                        }
                    }
                }
                SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger => {}
            }
        }
        reachable.len() == self.types.len()
    }
}

/// One explicit full-width register parameter in a function snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SourceAbiParameterSpec {
    index: u32,
    storage: CanonicalStorageId,
}

impl SourceAbiParameterSpec {
    pub const fn new(index: u32, storage: CanonicalStorageId) -> Self {
        Self { index, storage }
    }

    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }
}

/// Explicit source return contract. Absence of an interface remains unknown;
/// `Void` is therefore materially different from no return information.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceFunctionReturn {
    Void,
    Register { storage: CanonicalStorageId },
}

/// One exactly sized stack resource supplied by the immutable source snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceStackSlotRole {
    /// Compatibility-only resource with no local or parameter-home authority.
    UnclassifiedResource,
    Local,
    ParameterHome {
        parameter_index: u32,
        home_storage: CanonicalStorageId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SourceStackSlotSpec {
    base: StackAddressBase,
    base_storage: CanonicalStorageId,
    offset: i64,
    size_bytes: u32,
    role: SourceStackSlotRole,
}

impl SourceStackSlotSpec {
    /// Compatibility constructor. The result cannot prove a Local or parameter Home role.
    pub const fn new(
        base: StackAddressBase,
        base_storage: CanonicalStorageId,
        offset: i64,
        size_bytes: u32,
    ) -> Self {
        Self {
            base,
            base_storage,
            offset,
            size_bytes,
            role: SourceStackSlotRole::UnclassifiedResource,
        }
    }

    pub const fn new_local(
        base: StackAddressBase,
        base_storage: CanonicalStorageId,
        offset: i64,
        size_bytes: u32,
    ) -> Self {
        Self {
            base,
            base_storage,
            offset,
            size_bytes,
            role: SourceStackSlotRole::Local,
        }
    }

    pub const fn new_parameter_home(
        base: StackAddressBase,
        base_storage: CanonicalStorageId,
        offset: i64,
        size_bytes: u32,
        parameter_index: u32,
        home_storage: CanonicalStorageId,
    ) -> Self {
        Self {
            base,
            base_storage,
            offset,
            size_bytes,
            role: SourceStackSlotRole::ParameterHome {
                parameter_index,
                home_storage,
            },
        }
    }

    pub const fn base(&self) -> StackAddressBase {
        self.base
    }

    pub const fn base_storage(&self) -> CanonicalStorageId {
        self.base_storage
    }

    pub const fn offset(&self) -> i64 {
        self.offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub const fn role(&self) -> SourceStackSlotRole {
        self.role
    }
}

/// Coherent, revision-bound function interface injected by the source owner.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceFunctionInterface {
    schema_version: u32,
    revision_identity: Box<[u8]>,
    calling_convention: String,
    parameters: Box<[SourceAbiParameterSpec]>,
    return_kind: SourceFunctionReturn,
    return_address_storage: Option<CanonicalStorageId>,
    stack_slots: Box<[SourceStackSlotSpec]>,
    parameter_logical_values: Box<[SourceLogicalValue]>,
    return_logical_value: Option<SourceLogicalValue>,
    type_graph: Option<SourceTypeGraph>,
    stack_slot_roles_complete: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceFunctionInterfaceError {
    EmptyRevisionIdentity,
    EmptyCallingConvention,
    InvalidParameterOrder,
    InvalidRegisterStorage,
    InvalidReturnAddressStorage,
    OverlappingRegisterStorages,
    InvalidStackSlot,
    InvalidStackSlotRole,
    OverlappingStackSlots,
    InvalidLogicalTypes,
}

impl std::fmt::Display for SourceFunctionInterfaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid source function interface: {self:?}")
    }
}

impl std::error::Error for SourceFunctionInterfaceError {}

impl SourceFunctionInterface {
    pub fn new(
        revision_identity: impl Into<Vec<u8>>,
        calling_convention: impl Into<String>,
        parameters: impl IntoIterator<Item = SourceAbiParameterSpec>,
        return_kind: SourceFunctionReturn,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        Self::new_with_logical_types_internal(
            revision_identity,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            Vec::new(),
            None,
            None,
            false,
        )
    }

    pub fn new_exact(
        revision_identity: impl Into<Vec<u8>>,
        calling_convention: impl Into<String>,
        parameters: impl IntoIterator<Item = SourceAbiParameterSpec>,
        return_kind: SourceFunctionReturn,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        Self::new_with_logical_types_internal(
            revision_identity,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            Vec::new(),
            None,
            None,
            true,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new_with_logical_types(
        revision_identity: impl Into<Vec<u8>>,
        calling_convention: impl Into<String>,
        parameters: impl IntoIterator<Item = SourceAbiParameterSpec>,
        return_kind: SourceFunctionReturn,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
        parameter_logical_values: impl IntoIterator<Item = SourceLogicalValue>,
        return_logical_value: Option<SourceLogicalValue>,
        type_graph: Option<SourceTypeGraph>,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        Self::new_with_logical_types_internal(
            revision_identity,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            parameter_logical_values,
            return_logical_value,
            type_graph,
            false,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new_exact_with_logical_types(
        revision_identity: impl Into<Vec<u8>>,
        calling_convention: impl Into<String>,
        parameters: impl IntoIterator<Item = SourceAbiParameterSpec>,
        return_kind: SourceFunctionReturn,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
        parameter_logical_values: impl IntoIterator<Item = SourceLogicalValue>,
        return_logical_value: Option<SourceLogicalValue>,
        type_graph: Option<SourceTypeGraph>,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        Self::new_with_logical_types_internal(
            revision_identity,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            parameter_logical_values,
            return_logical_value,
            type_graph,
            true,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_with_logical_types_internal(
        revision_identity: impl Into<Vec<u8>>,
        calling_convention: impl Into<String>,
        parameters: impl IntoIterator<Item = SourceAbiParameterSpec>,
        return_kind: SourceFunctionReturn,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
        parameter_logical_values: impl IntoIterator<Item = SourceLogicalValue>,
        return_logical_value: Option<SourceLogicalValue>,
        type_graph: Option<SourceTypeGraph>,
        require_exact_stack_slot_roles: bool,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        let revision_identity = revision_identity.into();
        if revision_identity.is_empty() {
            return Err(SourceFunctionInterfaceError::EmptyRevisionIdentity);
        }
        let calling_convention = calling_convention.into();
        if calling_convention.trim().is_empty() {
            return Err(SourceFunctionInterfaceError::EmptyCallingConvention);
        }
        let parameters = parameters.into_iter().collect::<Vec<_>>();
        if parameters
            .iter()
            .enumerate()
            .any(|(index, parameter)| u32::try_from(index) != Ok(parameter.index))
        {
            return Err(SourceFunctionInterfaceError::InvalidParameterOrder);
        }
        if parameters
            .iter()
            .any(|parameter| !valid_register_storage(parameter.storage))
            || matches!(
                return_kind,
                SourceFunctionReturn::Register { storage }
                    if !valid_register_storage(storage)
            )
        {
            return Err(SourceFunctionInterfaceError::InvalidRegisterStorage);
        }
        if parameters.iter().enumerate().any(|(index, parameter)| {
            parameters[index.saturating_add(1)..]
                .iter()
                .any(|other| register_storages_overlap(parameter.storage, other.storage))
        }) {
            return Err(SourceFunctionInterfaceError::OverlappingRegisterStorages);
        }
        let mut stack_slots = stack_slots.into_iter().collect::<Vec<_>>();
        if stack_slots.iter().any(|slot| {
            !valid_register_storage(slot.base_storage)
                || slot.size_bytes == 0
                || slot
                    .offset
                    .checked_add(i64::from(slot.size_bytes))
                    .is_none()
        }) {
            return Err(SourceFunctionInterfaceError::InvalidStackSlot);
        }
        stack_slots.sort_by_key(|slot| (slot.base, slot.offset, slot.size_bytes));
        if stack_slots.iter().enumerate().any(|(index, slot)| {
            stack_slots[index.saturating_add(1)..]
                .iter()
                .any(|other| slot.base == other.base && slot.base_storage != other.base_storage)
        }) {
            return Err(SourceFunctionInterfaceError::InvalidStackSlot);
        }
        if stack_slots.windows(2).any(|pair| {
            pair[0].base == pair[1].base
                && pair[0]
                    .offset
                    .checked_add(i64::from(pair[0].size_bytes))
                    .is_none_or(|end| end > pair[1].offset)
        }) {
            return Err(SourceFunctionInterfaceError::OverlappingStackSlots);
        }
        let mut parameter_homes = BTreeSet::new();
        for slot in &stack_slots {
            match slot.role {
                SourceStackSlotRole::UnclassifiedResource => {
                    if require_exact_stack_slot_roles {
                        return Err(SourceFunctionInterfaceError::InvalidStackSlotRole);
                    }
                }
                SourceStackSlotRole::Local => {}
                SourceStackSlotRole::ParameterHome {
                    parameter_index,
                    home_storage,
                } => {
                    let Ok(parameter_index_usize) = usize::try_from(parameter_index) else {
                        return Err(SourceFunctionInterfaceError::InvalidStackSlotRole);
                    };
                    if !valid_register_storage(home_storage)
                        || parameters
                            .get(parameter_index_usize)
                            .is_none_or(|parameter| {
                                parameter.index != parameter_index
                                    || parameter.storage != home_storage
                            })
                        || !parameter_homes.insert(parameter_index)
                    {
                        return Err(SourceFunctionInterfaceError::InvalidStackSlotRole);
                    }
                }
            }
        }
        let parameter_logical_values = parameter_logical_values.into_iter().collect::<Vec<_>>();
        match type_graph.as_ref() {
            None => {
                if !parameter_logical_values.is_empty() || return_logical_value.is_some() {
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes);
                }
            }
            Some(graph) => {
                if parameter_logical_values.len() != parameters.len()
                    || parameter_logical_values
                        .iter()
                        .zip(&parameters)
                        .any(|(value, parameter)| {
                            !graph.validates_logical_value(*value, parameter.storage.size)
                        })
                    || match (return_kind, return_logical_value) {
                        (SourceFunctionReturn::Void, None) => false,
                        (SourceFunctionReturn::Register { storage }, Some(value)) => {
                            !graph.validates_logical_value(value, storage.size)
                        }
                        _ => true,
                    }
                    || !graph.all_types_reachable(
                        parameter_logical_values
                            .iter()
                            .map(|value| value.type_id())
                            .chain(return_logical_value.map(SourceLogicalValue::type_id)),
                    )
                {
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes);
                }
            }
        }
        Ok(Self {
            schema_version: SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION,
            revision_identity: revision_identity.into_boxed_slice(),
            calling_convention,
            parameters: parameters.into_boxed_slice(),
            return_kind,
            return_address_storage: None,
            stack_slots: stack_slots.into_boxed_slice(),
            parameter_logical_values: parameter_logical_values.into_boxed_slice(),
            return_logical_value,
            type_graph,
            stack_slot_roles_complete: require_exact_stack_slot_roles,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub fn calling_convention(&self) -> &str {
        &self.calling_convention
    }

    pub const fn parameters(&self) -> &[SourceAbiParameterSpec] {
        &self.parameters
    }

    pub const fn return_kind(&self) -> SourceFunctionReturn {
        self.return_kind
    }

    /// Bind the machine return-address carrier supplied by the immutable
    /// source snapshot. Exact frame/return certificates require this role;
    /// they never infer it from a register name.
    pub fn with_return_address_storage(
        mut self,
        storage: CanonicalStorageId,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        if !valid_register_storage(storage) {
            return Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage);
        }
        self.return_address_storage = Some(storage);
        Ok(self)
    }

    pub const fn return_address_storage(&self) -> Option<CanonicalStorageId> {
        self.return_address_storage
    }

    pub const fn stack_slots(&self) -> &[SourceStackSlotSpec] {
        &self.stack_slots
    }

    pub const fn parameter_logical_values(&self) -> &[SourceLogicalValue] {
        &self.parameter_logical_values
    }

    pub const fn return_logical_value(&self) -> Option<SourceLogicalValue> {
        self.return_logical_value
    }

    pub const fn type_graph(&self) -> Option<&SourceTypeGraph> {
        self.type_graph.as_ref()
    }

    pub const fn stack_slot_roles_complete(&self) -> bool {
        self.stack_slot_roles_complete
    }
}

fn valid_register_storage(storage: CanonicalStorageId) -> bool {
    storage.space == CanonicalStorageSpace::Register
        && storage.size > 0
        && storage
            .offset
            .checked_add(u64::from(storage.size))
            .is_some()
}

fn register_storages_overlap(left: CanonicalStorageId, right: CanonicalStorageId) -> bool {
    let Some(left_end) = left.offset.checked_add(u64::from(left.size)) else {
        return true;
    };
    let Some(right_end) = right.offset.checked_add(u64::from(right.size)) else {
        return true;
    };
    left.offset < right_end && right.offset < left_end
}

/// Stable identity of one call in the raw lifted input, before SSA inserts
/// synthetic call-boundary definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct SourceCallSiteIdentity {
    block_addr: u64,
    op_index: usize,
    target: CanonicalStorageId,
}

impl SourceCallSiteIdentity {
    pub const fn new(block_addr: u64, op_index: usize, target: CanonicalStorageId) -> Self {
        Self {
            block_addr,
            op_index,
            target,
        }
    }

    pub const fn block_addr(self) -> u64 {
        self.block_addr
    }

    pub const fn op_index(self) -> usize {
        self.op_index
    }

    pub const fn target(self) -> CanonicalStorageId {
        self.target
    }
}

/// One ordered, full-width register argument at an explicit call boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SourceCallArgumentSpec {
    index: u32,
    storage: CanonicalStorageId,
}

impl SourceCallArgumentSpec {
    pub const fn new(index: u32, storage: CanonicalStorageId) -> Self {
        Self { index, storage }
    }

    pub const fn index(self) -> u32 {
        self.index
    }

    pub const fn storage(self) -> CanonicalStorageId {
        self.storage
    }
}

/// Explicit result contract for one call. Absence of a callsite interface is
/// unknown and is deliberately distinct from `Void`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceCallResult {
    Void,
    Register { storage: CanonicalStorageId },
}

/// Source-owned prototype and observed carrier contract for one exact raw
/// callsite.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceCallSiteInterface {
    schema_version: u32,
    revision_identity: Box<[u8]>,
    identity: SourceCallSiteIdentity,
    complete: bool,
    calling_convention: String,
    arguments: Box<[SourceCallArgumentSpec]>,
    variadic: bool,
    noreturn: bool,
    result: SourceCallResult,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceCallSiteInterfaceError {
    EmptyRevisionIdentity,
    InvalidTargetStorage,
    EmptyCallingConvention,
    InvalidArgumentOrder,
    InvalidRegisterStorage,
    OverlappingRegisterStorages,
    NoreturnWithResult,
}

impl std::fmt::Display for SourceCallSiteInterfaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid source callsite interface: {self:?}")
    }
}

impl std::error::Error for SourceCallSiteInterfaceError {}

impl SourceCallSiteInterface {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        revision_identity: impl Into<Vec<u8>>,
        identity: SourceCallSiteIdentity,
        complete: bool,
        calling_convention: impl Into<String>,
        arguments: impl IntoIterator<Item = SourceCallArgumentSpec>,
        variadic: bool,
        noreturn: bool,
        result: SourceCallResult,
    ) -> Result<Self, SourceCallSiteInterfaceError> {
        let revision_identity = revision_identity.into();
        if revision_identity.is_empty() {
            return Err(SourceCallSiteInterfaceError::EmptyRevisionIdentity);
        }
        if !valid_call_target_storage(identity.target) {
            return Err(SourceCallSiteInterfaceError::InvalidTargetStorage);
        }
        let calling_convention = calling_convention.into();
        if calling_convention.trim().is_empty() {
            return Err(SourceCallSiteInterfaceError::EmptyCallingConvention);
        }
        let arguments = arguments.into_iter().collect::<Vec<_>>();
        if arguments
            .iter()
            .enumerate()
            .any(|(index, argument)| u32::try_from(index) != Ok(argument.index))
        {
            return Err(SourceCallSiteInterfaceError::InvalidArgumentOrder);
        }
        if arguments
            .iter()
            .any(|argument| !valid_register_storage(argument.storage))
            || matches!(
                result,
                SourceCallResult::Register { storage } if !valid_register_storage(storage)
            )
        {
            return Err(SourceCallSiteInterfaceError::InvalidRegisterStorage);
        }
        if arguments.iter().enumerate().any(|(index, argument)| {
            arguments[index.saturating_add(1)..]
                .iter()
                .any(|other| register_storages_overlap(argument.storage, other.storage))
        }) {
            return Err(SourceCallSiteInterfaceError::OverlappingRegisterStorages);
        }
        if noreturn && !matches!(result, SourceCallResult::Void) {
            return Err(SourceCallSiteInterfaceError::NoreturnWithResult);
        }
        Ok(Self {
            schema_version: SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION,
            revision_identity: revision_identity.into_boxed_slice(),
            identity,
            complete,
            calling_convention,
            arguments: arguments.into_boxed_slice(),
            variadic,
            noreturn,
            result,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn identity(&self) -> SourceCallSiteIdentity {
        self.identity
    }

    pub const fn is_complete(&self) -> bool {
        self.complete
    }

    pub fn calling_convention(&self) -> &str {
        &self.calling_convention
    }

    pub const fn arguments(&self) -> &[SourceCallArgumentSpec] {
        &self.arguments
    }

    pub const fn is_variadic(&self) -> bool {
        self.variadic
    }

    pub const fn is_noreturn(&self) -> bool {
        self.noreturn
    }

    pub const fn result(&self) -> SourceCallResult {
        self.result
    }
}

fn valid_call_target_storage(storage: CanonicalStorageId) -> bool {
    !storage.is_unknown()
        && storage.size > 0
        && storage
            .offset
            .checked_add(u64::from(storage.size))
            .is_some()
}

/// One canonical register carrier in the immutable ABI snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct MachineAbiRegisterSlot {
    index: u32,
    storage: CanonicalStorageId,
}

impl MachineAbiRegisterSlot {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }
}

/// Typed calling-convention carrier snapshot injected with the function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineAbiModel {
    schema_version: u32,
    available: bool,
    coherent: bool,
    argument_registers: Box<[MachineAbiRegisterSlot]>,
    return_registers: Box<[MachineAbiRegisterSlot]>,
}

impl MachineAbiModel {
    fn unavailable() -> Self {
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: false,
            coherent: false,
            argument_registers: Box::new([]),
            return_registers: Box::new([]),
        }
    }

    fn from_interface(interface: Option<&SourceFunctionInterface>) -> Self {
        let Some(interface) = interface else {
            return Self::unavailable();
        };
        let argument_registers = interface
            .parameters()
            .iter()
            .map(|parameter| MachineAbiRegisterSlot {
                index: parameter.index(),
                storage: parameter.storage(),
            })
            .collect::<Vec<_>>();
        let return_registers = match interface.return_kind() {
            SourceFunctionReturn::Void => Vec::new(),
            SourceFunctionReturn::Register { storage } => {
                vec![MachineAbiRegisterSlot { index: 0, storage }]
            }
        };
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: true,
            coherent: true,
            argument_registers: argument_registers.into_boxed_slice(),
            return_registers: return_registers.into_boxed_slice(),
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn is_available(&self) -> bool {
        self.available
    }

    pub const fn is_coherent(&self) -> bool {
        self.coherent
    }

    pub const fn argument_registers(&self) -> &[MachineAbiRegisterSlot] {
        &self.argument_registers
    }

    pub const fn return_registers(&self) -> &[MachineAbiRegisterSlot] {
        &self.return_registers
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineMemoryEndianness {
    Little,
    Big,
    Mixed,
    Custom,
    Unknown,
}

impl From<Endianness> for MachineMemoryEndianness {
    fn from(endianness: Endianness) -> Self {
        match endianness {
            Endianness::Little => Self::Little,
            Endianness::Big => Self::Big,
            Endianness::Mixed => Self::Mixed,
            Endianness::Custom => Self::Custom,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineMemorySpace {
    space: SpaceId,
    address_bits: u32,
    word_size_bytes: u32,
    endianness: MachineMemoryEndianness,
}

impl MachineMemorySpace {
    pub const fn space(&self) -> SpaceId {
        self.space
    }

    pub const fn address_bits(&self) -> u32 {
        self.address_bits
    }

    pub const fn word_size_bytes(&self) -> u32 {
        self.word_size_bytes
    }

    pub const fn endianness(&self) -> MachineMemoryEndianness {
        self.endianness
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineMemoryModel {
    schema_version: u32,
    available: bool,
    coherent: bool,
    default_address_bits: u32,
    alignment_bytes: u32,
    default_endianness: MachineMemoryEndianness,
    spaces: Box<[MachineMemorySpace]>,
}

impl MachineMemoryModel {
    fn unavailable() -> Self {
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: false,
            coherent: false,
            default_address_bits: 0,
            alignment_bytes: 0,
            default_endianness: MachineMemoryEndianness::Unknown,
            spaces: Box::new([]),
        }
    }

    fn from_arch(arch: Option<&ArchSpec>) -> Self {
        let Some(arch) = arch else {
            return Self::unavailable();
        };
        let effective_address_size = effective_arch_address_size(arch);
        let default_address_bits = effective_address_size.checked_mul(8).unwrap_or(0);
        let mut coherent = default_address_bits > 0 && arch.alignment > 0;
        let default_endianness = MachineMemoryEndianness::from(arch.memory_endianness);
        let mut spaces = Vec::with_capacity(arch.spaces.len() + 1);

        for source in &arch.spaces {
            if spaces
                .iter()
                .any(|space: &MachineMemorySpace| space.space == source.id)
            {
                coherent = false;
                continue;
            }
            let address_size = if source.addr_size > 1 {
                source.addr_size
            } else {
                effective_address_size
            };
            let address_bits = address_size.checked_mul(8).unwrap_or(0);
            if address_bits == 0 || source.word_size == 0 {
                coherent = false;
            }
            spaces.push(MachineMemorySpace {
                space: source.id,
                address_bits,
                word_size_bytes: source.word_size,
                endianness: source
                    .endianness
                    .map(MachineMemoryEndianness::from)
                    .unwrap_or(default_endianness),
            });
        }
        if !spaces.iter().any(|space| space.space == SpaceId::Ram) {
            spaces.push(MachineMemorySpace {
                space: SpaceId::Ram,
                address_bits: default_address_bits,
                word_size_bytes: 1,
                endianness: default_endianness,
            });
        }
        spaces.sort_by_key(|space| space_sort_key(space.space));

        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            available: true,
            coherent,
            default_address_bits,
            alignment_bytes: arch.alignment,
            default_endianness,
            spaces: spaces.into_boxed_slice(),
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn is_available(&self) -> bool {
        self.available
    }

    pub const fn is_coherent(&self) -> bool {
        self.coherent
    }

    pub const fn default_address_bits(&self) -> u32 {
        self.default_address_bits
    }

    pub const fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub const fn default_endianness(&self) -> MachineMemoryEndianness {
        self.default_endianness
    }

    pub const fn spaces(&self) -> &[MachineMemorySpace] {
        &self.spaces
    }

    pub fn space(&self, space: SpaceId) -> Option<&MachineMemorySpace> {
        self.spaces
            .iter()
            .find(|candidate| candidate.space == space)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceMachineContext {
    schema_version: u32,
    memory_model: MachineMemoryModel,
    function_interface: Option<SourceFunctionInterface>,
    abi_model: MachineAbiModel,
    register_storages_by_name: BTreeMap<String, CanonicalStorageId>,
    raw_call_sites_by_id: BTreeMap<CallSiteId, SourceCallSiteIdentity>,
    call_site_interfaces: BTreeMap<SourceCallSiteIdentity, SourceCallSiteInterface>,
    call_site_interfaces_coherent: bool,
    memory_spaces_by_op: BTreeMap<(u64, usize), SpaceId>,
}

impl SourceMachineContext {
    pub(crate) fn from_blocks(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Self {
        Self::from_blocks_with_interfaces(blocks, arch, None, Vec::new())
    }

    pub(crate) fn from_blocks_with_interfaces(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: Option<SourceFunctionInterface>,
        call_site_interfaces: Vec<SourceCallSiteInterface>,
    ) -> Self {
        let register_storages_by_name: BTreeMap<String, CanonicalStorageId> = arch
            .into_iter()
            .flat_map(|arch| &arch.registers)
            .map(|register| {
                (
                    register.name.to_ascii_lowercase(),
                    CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: register.offset,
                        size: register.size,
                    },
                )
            })
            .collect();
        let mut abi_model = MachineAbiModel::from_interface(function_interface.as_ref());
        if let Some(interface) = function_interface.as_ref() {
            let declared_storages_exist = interface
                .parameters()
                .iter()
                .map(SourceAbiParameterSpec::storage)
                .chain(match interface.return_kind() {
                    SourceFunctionReturn::Void => None,
                    SourceFunctionReturn::Register { storage } => Some(storage),
                })
                .chain(
                    interface
                        .stack_slots()
                        .iter()
                        .map(SourceStackSlotSpec::base_storage),
                )
                .all(|storage| {
                    register_storages_by_name
                        .values()
                        .any(|actual| *actual == storage)
                });
            abi_model.coherent &= declared_storages_exist;
        }
        let raw_call_sites_by_id = collect_raw_call_site_identities(blocks);
        let raw_call_sites = raw_call_sites_by_id
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        let expected_call_site_revision = function_interface
            .as_ref()
            .map(|interface| interface.revision_identity().to_vec().into_boxed_slice())
            .or_else(|| {
                call_site_interfaces
                    .first()
                    .map(|interface| interface.revision_identity().to_vec().into_boxed_slice())
            });
        let mut call_site_interfaces_by_identity = BTreeMap::new();
        let mut claimed_sites = BTreeSet::new();
        let mut call_site_interfaces_coherent = true;
        for interface in call_site_interfaces {
            let identity = interface.identity();
            let site = (identity.block_addr(), identity.op_index());
            let carriers_exist = interface
                .arguments()
                .iter()
                .map(|argument| argument.storage())
                .chain(match interface.result() {
                    SourceCallResult::Void => None,
                    SourceCallResult::Register { storage } => Some(storage),
                })
                .all(|storage| {
                    register_storages_by_name
                        .values()
                        .any(|actual| *actual == storage)
                });
            if interface.schema_version() != SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION
                || expected_call_site_revision.as_deref() != Some(interface.revision_identity())
                || !raw_call_sites.contains(&identity)
                || !claimed_sites.insert(site)
                || !carriers_exist
                || call_site_interfaces_by_identity
                    .insert(identity, interface)
                    .is_some()
            {
                call_site_interfaces_coherent = false;
            }
        }
        let memory_spaces_by_op = blocks
            .iter()
            .flat_map(|block| {
                block
                    .ops
                    .iter()
                    .enumerate()
                    .filter_map(move |(op_index, op)| {
                        memory_space(op).map(|space| ((block.addr, op_index), space))
                    })
            })
            .collect();
        Self {
            schema_version: MACHINE_CONTEXT_SCHEMA_VERSION,
            memory_model: MachineMemoryModel::from_arch(arch),
            function_interface,
            abi_model,
            register_storages_by_name,
            raw_call_sites_by_id,
            call_site_interfaces: call_site_interfaces_by_identity,
            call_site_interfaces_coherent,
            memory_spaces_by_op,
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn memory_model(&self) -> &MachineMemoryModel {
        &self.memory_model
    }

    pub const fn abi_model(&self) -> &MachineAbiModel {
        &self.abi_model
    }

    pub const fn function_interface(&self) -> Option<&SourceFunctionInterface> {
        self.function_interface.as_ref()
    }

    pub fn register_storage(&self, name: &str) -> Option<CanonicalStorageId> {
        self.register_storages_by_name
            .get(&name.to_ascii_lowercase())
            .copied()
    }

    pub const fn register_storages_by_name(&self) -> &BTreeMap<String, CanonicalStorageId> {
        &self.register_storages_by_name
    }

    pub const fn raw_call_sites_by_id(&self) -> &BTreeMap<CallSiteId, SourceCallSiteIdentity> {
        &self.raw_call_sites_by_id
    }

    pub fn raw_call_site_identity(&self, call_site: CallSiteId) -> Option<SourceCallSiteIdentity> {
        self.raw_call_sites_by_id.get(&call_site).copied()
    }

    pub const fn call_site_interfaces(
        &self,
    ) -> &BTreeMap<SourceCallSiteIdentity, SourceCallSiteInterface> {
        &self.call_site_interfaces
    }

    pub const fn call_site_interfaces_are_coherent(&self) -> bool {
        self.call_site_interfaces_coherent
    }

    pub fn call_site_interface(&self, call_site: CallSiteId) -> Option<&SourceCallSiteInterface> {
        if !self.call_site_interfaces_coherent {
            return None;
        }
        self.raw_call_site_identity(call_site)
            .and_then(|identity| self.call_site_interfaces.get(&identity))
    }

    pub fn memory_space_at(&self, block_addr: u64, op_index: usize) -> Option<SpaceId> {
        self.memory_spaces_by_op
            .get(&(block_addr, op_index))
            .copied()
    }

    pub const fn memory_spaces_by_op(&self) -> &BTreeMap<(u64, usize), SpaceId> {
        &self.memory_spaces_by_op
    }

    /// Rebind raw lifted memory-space identities to the completed SSA operation
    /// sites. SSA preparation may insert non-memory register-alias operations,
    /// but it must retain the order and count of memory operations in each
    /// block. Any violation clears the map so certification fails closed.
    pub(crate) fn remap_memory_sites_to_prepared(&mut self, function: &SSAFunction) -> bool {
        let mut raw_by_block = BTreeMap::<u64, Vec<SpaceId>>::new();
        for ((block_addr, _), space) in &self.memory_spaces_by_op {
            raw_by_block.entry(*block_addr).or_default().push(*space);
        }

        let mut prepared_by_block = BTreeMap::<u64, Vec<usize>>::new();
        for block in function.blocks() {
            let sites = block
                .ops
                .iter()
                .enumerate()
                .filter_map(|(op_index, op)| is_memory_op(op).then_some(op_index))
                .collect::<Vec<_>>();
            if !sites.is_empty() {
                prepared_by_block.insert(block.addr, sites);
            }
        }

        if raw_by_block.len() != prepared_by_block.len()
            || raw_by_block.iter().any(|(block_addr, raw)| {
                prepared_by_block
                    .get(block_addr)
                    .is_none_or(|prepared| prepared.len() != raw.len())
            })
        {
            self.memory_spaces_by_op.clear();
            return false;
        }

        let mut remapped = BTreeMap::new();
        for (block_addr, spaces) in raw_by_block {
            let Some(sites) = prepared_by_block.get(&block_addr) else {
                self.memory_spaces_by_op.clear();
                return false;
            };
            for (op_index, space) in sites.iter().copied().zip(spaces) {
                remapped.insert((block_addr, op_index), space);
            }
        }
        self.memory_spaces_by_op = remapped;
        true
    }
}

fn is_memory_op(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Load { .. }
            | SSAOp::Store { .. }
            | SSAOp::LoadLinked { .. }
            | SSAOp::StoreConditional { .. }
            | SSAOp::AtomicCAS { .. }
            | SSAOp::LoadGuarded { .. }
            | SSAOp::StoreGuarded { .. }
    )
}

fn collect_raw_call_site_identities(
    blocks: &[R2ILBlock],
) -> BTreeMap<CallSiteId, SourceCallSiteIdentity> {
    let mut raw_calls = blocks
        .iter()
        .flat_map(|block| {
            block
                .ops
                .iter()
                .enumerate()
                .filter_map(move |(op_index, op)| match op {
                    R2ILOp::Call { target } => Some((
                        block.addr,
                        op_index,
                        Some(SourceCallSiteIdentity::new(
                            block.addr,
                            op_index,
                            CanonicalStorageId::from_varnode(target),
                        )),
                    )),
                    R2ILOp::CallInd { .. } => Some((block.addr, op_index, None)),
                    _ => None,
                })
        })
        .collect::<Vec<_>>();
    raw_calls.sort_unstable_by_key(|(block_addr, op_index, _)| (*block_addr, *op_index));
    raw_calls
        .into_iter()
        .enumerate()
        .filter_map(|(index, (_, _, identity))| {
            u32::try_from(index)
                .ok()
                .zip(identity)
                .map(|(index, identity)| (CallSiteId(index), identity))
        })
        .collect()
}

fn memory_space(op: &R2ILOp) -> Option<SpaceId> {
    match op {
        R2ILOp::Load { space, .. }
        | R2ILOp::Store { space, .. }
        | R2ILOp::LoadLinked { space, .. }
        | R2ILOp::StoreConditional { space, .. }
        | R2ILOp::AtomicCAS { space, .. }
        | R2ILOp::LoadGuarded { space, .. }
        | R2ILOp::StoreGuarded { space, .. } => Some(*space),
        _ => None,
    }
}

fn space_sort_key(space: SpaceId) -> (u8, u32) {
    match space {
        SpaceId::Ram => (0, 0),
        SpaceId::Register => (1, 0),
        SpaceId::Unique => (2, 0),
        SpaceId::Const => (3, 0),
        SpaceId::Custom(id) => (4, id),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{AddressSpace, RegisterDef, Varnode};

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    #[test]
    fn function_interface_rejects_overlapping_parameter_aliases() {
        assert_eq!(
            SourceFunctionInterface::new(
                b"overlapping-register-interface".to_vec(),
                "test-abi",
                [
                    SourceAbiParameterSpec::new(0, register_storage(0, 8)),
                    SourceAbiParameterSpec::new(1, register_storage(4, 4)),
                ],
                SourceFunctionReturn::Void,
                [],
            ),
            Err(SourceFunctionInterfaceError::OverlappingRegisterStorages)
        );
    }

    #[test]
    fn exact_function_interface_retains_local_and_parameter_home_roles() {
        let parameter_storage = register_storage(0, 8);
        let base_storage = register_storage(64, 8);
        let interface = SourceFunctionInterface::new_exact(
            b"exact-stack-slot-roles".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            SourceFunctionReturn::Void,
            [
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    base_storage,
                    -16,
                    8,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    base_storage,
                    -8,
                    8,
                    0,
                    parameter_storage,
                ),
            ],
        )
        .expect("classified stack-slot roles are exact");

        assert!(interface.stack_slot_roles_complete());
        assert_eq!(
            interface.stack_slots()[0].role(),
            SourceStackSlotRole::Local
        );
        assert_eq!(
            interface.stack_slots()[1].role(),
            SourceStackSlotRole::ParameterHome {
                parameter_index: 0,
                home_storage: parameter_storage,
            }
        );
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let artifact =
            crate::SsaArtifact::for_decompile_with_interface(&[block], None, interface.clone())
                .expect("SSA artifact retains the exact source interface");
        assert_eq!(
            artifact.machine_context().function_interface(),
            Some(&interface)
        );

        let compatibility = SourceFunctionInterface::new(
            b"compatibility-stack-slot".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
            )],
        )
        .expect("unclassified compatibility resource remains representable");
        assert!(!compatibility.stack_slot_roles_complete());
        assert_eq!(
            compatibility.stack_slots()[0].role(),
            SourceStackSlotRole::UnclassifiedResource
        );
    }

    #[test]
    fn exact_function_interface_rejects_malformed_parameter_homes() {
        let parameter_storage = register_storage(0, 8);
        let base_storage = register_storage(64, 8);
        let build = |slots| {
            SourceFunctionInterface::new_exact(
                b"malformed-stack-slot-role".to_vec(),
                "test-abi",
                [SourceAbiParameterSpec::new(0, parameter_storage)],
                SourceFunctionReturn::Void,
                slots,
            )
        };

        assert_eq!(
            build(vec![SourceStackSlotSpec::new(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
            )]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
        assert_eq!(
            build(vec![SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
                1,
                parameter_storage,
            )]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
        assert_eq!(
            build(vec![SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                base_storage,
                -8,
                8,
                0,
                register_storage(8, 8),
            )]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
        assert_eq!(
            build(vec![
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    base_storage,
                    -8,
                    8,
                    0,
                    parameter_storage,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::StackPointer,
                    register_storage(72, 8),
                    -8,
                    8,
                    0,
                    parameter_storage,
                ),
            ]),
            Err(SourceFunctionInterfaceError::InvalidStackSlotRole)
        );
    }

    fn demo_struct_type_graph() -> SourceTypeGraph {
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
        .expect("valid exact DemoStruct graph")
    }

    #[test]
    fn function_interface_retains_exact_logical_type_graph() {
        assert_eq!(
            SourceTypeGraph::new(
                [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 16)],
                [],
            ),
            Err(SourceTypeGraphError::InvalidType)
        );
        assert_eq!(
            SourceTypeGraph::new(
                [
                    SourceType::new(0, SourceTypeKind::Struct { aggregate_id: 0 }, 32, 32,),
                    SourceType::new(1, SourceTypeKind::SignedInteger, 32, 32),
                    SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 0 }, 32, 32,),
                ],
                [SourceAggregateLayout::new(
                    0,
                    0,
                    32,
                    32,
                    "OneField",
                    [SourceAggregateMember::new(0, 1, 0, 32, "value")],
                )],
            ),
            Err(SourceTypeGraphError::InvalidType)
        );
        let parameters = [
            SourceAbiParameterSpec::new(0, register_storage(0, 8)),
            SourceAbiParameterSpec::new(1, register_storage(8, 8)),
            SourceAbiParameterSpec::new(2, register_storage(16, 8)),
        ];
        let low_i32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        let interface = SourceFunctionInterface::new_with_logical_types(
            b"exact-type-layout".to_vec(),
            "test-abi",
            parameters,
            SourceFunctionReturn::Register {
                storage: register_storage(24, 8),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(1, low_i32),
                SourceLogicalValue::new(1, low_i32),
            ],
            Some(SourceLogicalValue::new(1, low_i32)),
            Some(demo_struct_type_graph()),
        )
        .expect("valid exact logical interface");

        assert_eq!(
            interface.schema_version(),
            SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        );
        assert_eq!(interface.parameter_logical_values()[0].type_id(), 2);
        assert_eq!(
            interface.parameter_logical_values()[1].carrier().kind(),
            SourceCarrierKind::LowBits
        );
        let graph = interface.type_graph().expect("retained exact graph");
        assert_eq!(graph.schema_version(), SOURCE_TYPE_GRAPH_SCHEMA_VERSION);
        assert_eq!(graph.types().len(), 3);
        assert_eq!(graph.aggregates()[0].name(), "DemoStruct");
        assert_eq!(graph.aggregates()[0].members()[2].offset_bits(), 8 * 8);
        assert_eq!(graph.aggregates()[0].members()[13].offset_bits(), 52 * 8);

        let invalid = SourceFunctionInterface::new_with_logical_types(
            b"exact-type-layout".to_vec(),
            "test-abi",
            parameters,
            SourceFunctionReturn::Register {
                storage: register_storage(24, 8),
            },
            [],
            [
                SourceLogicalValue::new(
                    2,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(
                    1,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 32),
                ),
                SourceLogicalValue::new(1, low_i32),
            ],
            Some(SourceLogicalValue::new(1, low_i32)),
            Some(demo_struct_type_graph()),
        );
        assert_eq!(
            invalid,
            Err(SourceFunctionInterfaceError::InvalidLogicalTypes)
        );
    }

    #[test]
    fn function_interface_accepts_exact_unsigned_byte_pointee() {
        let graph = SourceTypeGraph::new(
            [
                SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
            ],
            [],
        )
        .expect("unsigned-byte pointer graph");
        let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
        let interface = SourceFunctionInterface::new_exact_with_logical_types(
            b"fnv-u8-pointer-revision".to_vec(),
            "aapcs64",
            [
                SourceAbiParameterSpec::new(0, register_storage(0, 8)),
                SourceAbiParameterSpec::new(1, register_storage(8, 8)),
            ],
            SourceFunctionReturn::Register {
                storage: register_storage(0, 8),
            },
            [],
            [
                SourceLogicalValue::new(1, full64),
                SourceLogicalValue::new(2, full64),
            ],
            Some(SourceLogicalValue::new(2, full64)),
            Some(graph),
        )
        .expect("exact FNV logical interface");

        let graph = interface.type_graph().expect("logical graph");
        assert_eq!(
            graph.types()[1].kind(),
            SourceTypeKind::Pointer { target_type_id: 0 }
        );
        assert_eq!(graph.types()[0].kind(), SourceTypeKind::UnsignedInteger);
    }

    #[test]
    fn source_type_graph_rejects_pointer_to_pointer() {
        assert_eq!(
            SourceTypeGraph::new(
                [
                    SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
                    SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64,),
                    SourceType::new(2, SourceTypeKind::Pointer { target_type_id: 1 }, 64, 64,),
                ],
                [],
            ),
            Err(SourceTypeGraphError::InvalidType)
        );
    }

    #[test]
    fn callsite_interface_rejects_bad_order_overlap_and_noreturn_result() {
        let identity = SourceCallSiteIdentity::new(
            0x1000,
            0,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Ram,
                offset: 0x2000,
                size: 8,
            },
        );
        assert_eq!(
            SourceCallSiteInterface::new(
                b"call-revision".to_vec(),
                identity,
                true,
                "test-abi",
                [SourceCallArgumentSpec::new(1, register_storage(0, 8))],
                false,
                false,
                SourceCallResult::Void,
            ),
            Err(SourceCallSiteInterfaceError::InvalidArgumentOrder)
        );
        assert_eq!(
            SourceCallSiteInterface::new(
                b"call-revision".to_vec(),
                identity,
                true,
                "test-abi",
                [
                    SourceCallArgumentSpec::new(0, register_storage(0, 8)),
                    SourceCallArgumentSpec::new(1, register_storage(4, 8)),
                ],
                false,
                false,
                SourceCallResult::Void,
            ),
            Err(SourceCallSiteInterfaceError::OverlappingRegisterStorages)
        );
        assert_eq!(
            SourceCallSiteInterface::new(
                b"call-revision".to_vec(),
                identity,
                true,
                "test-abi",
                [],
                false,
                true,
                SourceCallResult::Register {
                    storage: register_storage(0, 8),
                },
            ),
            Err(SourceCallSiteInterfaceError::NoreturnWithResult)
        );
    }

    #[test]
    fn raw_direct_callsite_ids_are_sorted_and_retain_exact_targets() {
        let low_target = Varnode::ram(0x3000, 8);
        let high_target = Varnode::ram(0x4000, 8);
        let mut high = R2ILBlock::new(0x2000, 4);
        high.push(R2ILOp::Call {
            target: high_target.clone(),
        });
        let mut low = R2ILBlock::new(0x1000, 4);
        low.push(R2ILOp::Call {
            target: low_target.clone(),
        });

        let context = SourceMachineContext::from_blocks(&[high, low], None);
        assert_eq!(
            context.raw_call_site_identity(CallSiteId(0)),
            Some(SourceCallSiteIdentity::new(
                0x1000,
                0,
                CanonicalStorageId::from_varnode(&low_target),
            ))
        );
        assert_eq!(
            context.raw_call_site_identity(CallSiteId(1)),
            Some(SourceCallSiteIdentity::new(
                0x2000,
                0,
                CanonicalStorageId::from_varnode(&high_target),
            ))
        );
    }

    #[test]
    fn prepared_memory_sites_follow_inserted_register_alias_operations() {
        let mut arch = ArchSpec::new("prepared-memory-site-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rdi", 0, 8));
        arch.add_register(RegisterDef::new("edi", 0, 4));
        arch.add_register(RegisterDef::new("rax", 8, 8));
        arch.add_register(RegisterDef::new("eax", 8, 4));

        let mut block = R2ILBlock::new(0x2400, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 4),
            space: SpaceId::Custom(7),
            addr: Varnode::register(8, 4),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(8, 8),
        });

        let function = SSAFunction::from_blocks_for_decompile(&[block.clone()], Some(&arch))
            .expect("prepared SSA");
        let prepared_index = function
            .get_block(0x2400)
            .expect("prepared block")
            .ops
            .iter()
            .position(is_memory_op)
            .expect("prepared memory operation");
        assert!(prepared_index > 1, "alias extraction must precede the load");

        let mut context = SourceMachineContext::from_blocks(&[block], Some(&arch));
        assert_eq!(context.memory_space_at(0x2400, 1), Some(SpaceId::Custom(7)));
        assert!(context.remap_memory_sites_to_prepared(&function));
        assert_eq!(
            context.memory_space_at(0x2400, prepared_index),
            Some(SpaceId::Custom(7))
        );
        assert_eq!(context.memory_spaces_by_op().len(), 1);
    }

    #[test]
    fn interface_registers_missing_from_architecture_are_incoherent() {
        let interface = SourceFunctionInterface::new(
            b"missing-register-interface".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, register_storage(0, 8))],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("valid standalone interface");
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            None,
            Some(interface),
            Vec::new(),
        );
        assert!(context.abi_model().is_available());
        assert!(!context.abi_model().is_coherent());
    }

    #[test]
    fn stack_base_storage_missing_from_architecture_is_incoherent() {
        let interface = SourceFunctionInterface::new(
            b"missing-stack-base-interface".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new(
                StackAddressBase::StackPointer,
                register_storage(52, 4),
                -16,
                4,
            )],
        )
        .expect("valid standalone stack interface");
        let mut arch = ArchSpec::new("stack-base-mismatch-test");
        arch.addr_size = 4;
        arch.add_register(RegisterDef::new("r0", 0, 4));
        let context = SourceMachineContext::from_blocks_with_interfaces(
            &[],
            Some(&arch),
            Some(interface),
            Vec::new(),
        );

        assert!(context.abi_model().is_available());
        assert!(!context.abi_model().is_coherent());
    }

    #[test]
    fn missing_architecture_keeps_typed_sites_but_marks_model_unavailable() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 4),
            space: SpaceId::Custom(7),
            addr: Varnode::register(0, 8),
        });
        let context = SourceMachineContext::from_blocks(&[block], None);

        assert!(!context.memory_model().is_available());
        assert!(!context.memory_model().is_coherent());
        assert_eq!(context.memory_space_at(0x1000, 0), Some(SpaceId::Custom(7)));
    }

    #[test]
    fn architecture_snapshot_applies_per_space_endianness() {
        let mut arch = ArchSpec::new("test-be");
        arch.addr_size = 8;
        arch.alignment = 4;
        arch.set_memory_endianness(Endianness::Big);
        let mut custom = AddressSpace::new(SpaceId::Custom(3), "little-data", 4);
        custom.word_size = 2;
        custom.endianness = Some(Endianness::Little);
        arch.add_space(custom);
        let context = SourceMachineContext::from_blocks(&[], Some(&arch));
        let model = context.memory_model();

        assert!(model.is_available());
        assert!(model.is_coherent());
        assert_eq!(model.default_address_bits(), 64);
        assert_eq!(model.default_endianness(), MachineMemoryEndianness::Big);
        assert_eq!(
            model
                .space(SpaceId::Ram)
                .map(MachineMemorySpace::endianness),
            Some(MachineMemoryEndianness::Big)
        );
        let custom = model.space(SpaceId::Custom(3)).expect("custom space");
        assert_eq!(custom.address_bits(), 32);
        assert_eq!(custom.word_size_bytes(), 2);
        assert_eq!(custom.endianness(), MachineMemoryEndianness::Little);
    }

    #[test]
    fn architecture_snapshot_uses_r2il_effective_address_size_fallback() {
        let mut arch = ArchSpec::new("fallback-address-size");
        arch.addr_size = 1;
        arch.add_register(RegisterDef::new("pc", 0, 8));
        arch.add_space(AddressSpace::new(SpaceId::Custom(9), "fallback", 1));
        let context = SourceMachineContext::from_blocks(&[], Some(&arch));
        let model = context.memory_model();

        assert_eq!(model.default_address_bits(), 64);
        assert_eq!(
            model
                .space(SpaceId::Custom(9))
                .map(MachineMemorySpace::address_bits),
            Some(64)
        );
        assert_eq!(
            model
                .space(SpaceId::Ram)
                .map(MachineMemorySpace::address_bits),
            Some(64)
        );
    }
}
