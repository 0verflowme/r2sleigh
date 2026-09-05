//! Source-owned storage, type, ABI, stack, and call-site contracts.
//!
//! These values are validated data, not certification authority. Only an
//! [`OwnedFunctionSnapshot`] created by the audited snapshot-ingress module
//! binds them to one immutable source capture.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

/// Name-independent storage identity retained from a lifted varnode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CanonicalStorageSpace {
    Ram,
    Register,
    Unique,
    Constant,
    Custom(u32),
    /// Programmatically synthesized SSA with no lifted storage provenance.
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CanonicalStorageId {
    pub space: CanonicalStorageSpace,
    pub offset: u64,
    pub size: u32,
}

/// Where a storage lives, without saying how much of it a write touched.
///
/// A `CanonicalStorageId` records a slice: `EAX` and `RAX` differ in it because
/// they differ in size, which makes two writes to one register look like writes
/// to two places. A location is the register, and the slice is what a
/// particular access took of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CanonicalLocation {
    pub space: CanonicalStorageSpace,
    pub offset: u64,
}

impl CanonicalStorageId {
    /// The place this slice is a slice of.
    pub const fn location(self) -> CanonicalLocation {
        CanonicalLocation {
            space: self.space,
            offset: self.offset,
        }
    }

    pub const fn from_varnode(varnode: &r2il::Varnode) -> Self {
        let space = match varnode.space {
            r2il::SpaceId::Ram => CanonicalStorageSpace::Ram,
            r2il::SpaceId::Register => CanonicalStorageSpace::Register,
            r2il::SpaceId::Unique => CanonicalStorageSpace::Unique,
            r2il::SpaceId::Const => CanonicalStorageSpace::Constant,
            r2il::SpaceId::Custom(id) => CanonicalStorageSpace::Custom(id),
        };
        Self {
            space,
            offset: varnode.offset,
            size: varnode.size,
        }
    }

    pub const fn unknown(ordinal: u64, size: u32) -> Self {
        Self {
            space: CanonicalStorageSpace::Unknown,
            offset: ordinal,
            size,
        }
    }

    pub const fn is_unknown(self) -> bool {
        matches!(self.space, CanonicalStorageSpace::Unknown)
    }
}

/// Canonical base used to form a proven stack address.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum StackAddressBase {
    FramePointer,
    StackPointer,
}

pub const SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION: u32 = 11;
pub const SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION: u32 = 3;
pub const SOURCE_TYPE_GRAPH_SCHEMA_VERSION: u32 = 1;

/// Typed classification of one source-owned calling-convention spelling.
///
/// The source spelling remains available for presentation, but semantic
/// consumers use this closed value. Classification happens once when a source
/// contract is constructed; consumers must not parse the spelling again.
#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub enum SourceAbiClass {
    /// The source supplied no convention, or explicitly marked it unknown.
    #[default]
    Unknown,
    /// The source supplied a convention outside the closed vocabulary below.
    Other,
    Microsoft,
    MicrosoftX64,
    SystemV,
    SystemVAMD64,
    Aapcs,
    Aapcs64,
    RiscV32,
    RiscV64,
    Cdecl,
    Stdcall,
    Fastcall,
    Thiscall,
    Vectorcall,
}

impl SourceAbiClass {
    /// Classify an exact source spelling without architecture or symbol hints.
    pub fn from_source_spelling(spelling: &str) -> Self {
        let mut normalized = String::with_capacity(spelling.len());
        for ch in spelling.trim().chars() {
            if ch.is_ascii_alphanumeric() {
                normalized.push(ch.to_ascii_lowercase());
            } else if ch.is_ascii_whitespace() || matches!(ch, '-' | '_' | ':' | '.' | '/') {
                continue;
            } else {
                return Self::Other;
            }
        }
        match normalized.as_str() {
            "" | "unknown" | "unspecified" | "default" | "none" => Self::Unknown,
            "ms" | "msvc" | "microsoft" => Self::Microsoft,
            "ms64" | "msx64" | "win64" | "windowsx64" | "microsoftx64" | "x64windows"
            | "amd64windows" => Self::MicrosoftX64,
            "sysv" | "systemv" => Self::SystemV,
            "amd64" | "sysv64" | "sysvamd64" | "systemvamd64" | "amd64sysv" | "x8664sysv" => {
                Self::SystemVAMD64
            }
            "aapcs" => Self::Aapcs,
            "aapcs64" => Self::Aapcs64,
            "riscv32" | "rv32" => Self::RiscV32,
            "riscv64" | "rv64" => Self::RiscV64,
            "cdecl" => Self::Cdecl,
            "stdcall" => Self::Stdcall,
            "fastcall" => Self::Fastcall,
            "thiscall" => Self::Thiscall,
            "vectorcall" => Self::Vectorcall,
            _ => Self::Other,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceTypeKind {
    SignedInteger,
    UnsignedInteger,
    Pointer {
        target_type_id: u32,
    },
    Struct {
        aggregate_id: u32,
    },
    /// An object the graph does not describe. It has no size and no layout
    /// and exists only as a pointer's target: it is how `void *` is placed
    /// without inventing what it points at.
    Void,
    /// Code. Like `Void` it has no size and is only a pointer's target; the
    /// signature is not carried, so a pointer to it is a function pointer
    /// whose parameters the graph does not state.
    Code,
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
        // A function that mentions no type has an empty graph. That is a
        // complete account of the types it uses, not an absent one, and
        // rejecting it refused every function whose body needs nothing named.
        for (position, source_type) in types.iter().enumerate() {
            if u32::try_from(position) != Ok(source_type.id) {
                return Err(SourceTypeGraphError::InvalidType);
            }
            // An opaque kind has no size and no alignment, by definition;
            // every other kind is an object and has both.
            if matches!(
                source_type.kind,
                SourceTypeKind::Void | SourceTypeKind::Code
            ) {
                if source_type.size_bits != 0 || source_type.align_bits != 0 {
                    return Err(SourceTypeGraphError::InvalidType);
                }
                continue;
            }
            if source_type.size_bits == 0
                || !source_type.size_bits.is_multiple_of(8)
                || source_type.align_bits == 0
                || !source_type.align_bits.is_multiple_of(8)
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
                    // `char **argv` is ordinary C, and reachability already walks targets through a visited set
                    if !matches!(source_type.size_bits, 32 | 64)
                        || source_type.align_bits != source_type.size_bits
                        || usize::try_from(target_type_id)
                            .ok()
                            .and_then(|id| types.get(id))
                            .is_none()
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
                SourceTypeKind::Void | SourceTypeKind::Code => {}
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
                    .filter(|member_type| {
                        !matches!(
                            member_type.kind,
                            SourceTypeKind::Void | SourceTypeKind::Code
                        )
                    })
                else {
                    return Err(SourceTypeGraphError::InvalidMember);
                };
                // Any type this graph already validated may be a member. What
                // has to hold of a member is where it sits, not what it is:
                // admitting only integers refused `struct state *next`, and
                // with it every function that mentions an ordinary C struct.
                // A member holds a whole number of its element type: one for a
                // plain member, more for an array. Demanding exactly one refused
                // every struct with an array in it, and refusing the struct lost
                // the layout of its other members too, so a `VmState` holding
                // `int32_t r[8]` reached the consumer with no layout at all.
                if u32::try_from(member_position) != Ok(member.member_id)
                    || member.size_bits == 0
                    || member_type.size_bits == 0
                    || !member.size_bits.is_multiple_of(member_type.size_bits)
                    || !member.offset_bits.is_multiple_of(8)
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

    /// Check source pointer types against the exact captured machine width.
    /// Structural type construction alone cannot grant this machine-specific
    /// fact because the type graph is also used by analysis-only callers.
    pub fn validates_pointer_width(&self, pointer_bits: u32) -> bool {
        self.types.iter().all(|source_type| {
            !matches!(source_type.kind, SourceTypeKind::Pointer { .. })
                || source_type.size_bits == u64::from(pointer_bits)
        })
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
                SourceTypeKind::SignedInteger
                | SourceTypeKind::UnsignedInteger
                | SourceTypeKind::Void
                | SourceTypeKind::Code => {}
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

/// Exact source-owned mechanism used to recover the return address and final
/// stack-pointer delta. Absence remains unknown and grants no authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceReturnMechanism {
    Stacked {
        stack_offset: i64,
        slot_size_bytes: u32,
        stack_pointer_delta_bytes: u32,
        address_size_bytes: u32,
    },
}

/// Exact source-owned direction in which a callee acquires private stack
/// storage by moving the architectural stack pointer away from its entry
/// value. This is an ownership contract, not an inference from an architecture
/// name, calling-convention string, or observed instruction spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, serde::Deserialize)]
pub enum SourceStackGrowth {
    LowerAddresses,
    HigherAddresses,
}

/// Revision-bound stack-allocation authority supplied by the immutable source
/// snapshot. While an exact SP move in `growth` remains live and unrestored,
/// the half-open interval between the entry SP and that moved SP belongs to the
/// callee. `implicit_active_sp_bytes` describes exactly that many bytes beyond
/// the active SP in the growth direction, including when the active SP still
/// equals its entry value. This is geometric authority only: a consumer must
/// independently prove that no intervening call or other source-declared
/// invalidation can overwrite the implicit area while any certified value is
/// live. Absence grants no allocation or implicit-stack authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct SourceStackAllocationContract {
    growth: SourceStackGrowth,
    implicit_active_sp_bytes: u32,
}

impl SourceStackAllocationContract {
    /// Construct the exact legacy envelope with no implicit bytes beyond the
    /// active SP. Wire producers for the current schema must still transport
    /// the explicit zero field.
    pub const fn new(growth: SourceStackGrowth) -> Self {
        Self::with_implicit_active_sp_bytes(growth, 0)
    }

    pub const fn with_implicit_active_sp_bytes(
        growth: SourceStackGrowth,
        implicit_active_sp_bytes: u32,
    ) -> Self {
        Self {
            growth,
            implicit_active_sp_bytes,
        }
    }

    pub const fn growth(self) -> SourceStackGrowth {
        self.growth
    }

    pub const fn implicit_active_sp_bytes(self) -> u32 {
        self.implicit_active_sp_bytes
    }

    /// Return the exact half-open entry-SP-relative geometric envelope for
    /// `active_sp_offset`. The active offset must move in the source-owned
    /// growth direction (or remain zero), and all endpoint arithmetic is
    /// checked. This does not prove the implicit portion survives a call.
    pub fn owned_entry_relative_envelope(
        self,
        active_sp_offset: i64,
    ) -> Option<std::ops::Range<i64>> {
        let implicit_bytes = i64::from(self.implicit_active_sp_bytes);
        match self.growth {
            SourceStackGrowth::LowerAddresses if active_sp_offset <= 0 => {
                Some(active_sp_offset.checked_sub(implicit_bytes)?..0)
            }
            SourceStackGrowth::HigherAddresses if active_sp_offset >= 0 => {
                Some(0..active_sp_offset.checked_add(implicit_bytes)?)
            }
            SourceStackGrowth::LowerAddresses | SourceStackGrowth::HigherAddresses => None,
        }
    }

    /// Check that one non-empty byte range is wholly inside the exact owned
    /// envelope for the supplied active SP. This rejects endpoint overflow,
    /// opposite-direction SP movement, and ranges crossing either boundary.
    pub fn owns_entry_relative_range(
        self,
        active_sp_offset: i64,
        offset: i64,
        size_bytes: u32,
    ) -> bool {
        if size_bytes == 0 {
            return false;
        }
        let Some(end) = offset.checked_add(i64::from(size_bytes)) else {
            return false;
        };
        self.owned_entry_relative_envelope(active_sp_offset)
            .is_some_and(|envelope| offset >= envelope.start && end <= envelope.end)
    }

    pub fn owns_entry_relative_reservation(self, offset: i64, size_bytes: u32) -> bool {
        if size_bytes == 0 {
            return false;
        }
        match self.growth {
            SourceStackGrowth::LowerAddresses => {
                offset < 0 && offset.checked_add(i64::from(size_bytes)) == Some(0)
            }
            SourceStackGrowth::HigherAddresses => offset == 0,
        }
    }
}

impl SourceReturnMechanism {
    pub const fn stack_offset(self) -> i64 {
        match self {
            Self::Stacked { stack_offset, .. } => stack_offset,
        }
    }

    pub const fn slot_size_bytes(self) -> u32 {
        match self {
            Self::Stacked {
                slot_size_bytes, ..
            } => slot_size_bytes,
        }
    }

    pub const fn stack_pointer_delta_bytes(self) -> u32 {
        match self {
            Self::Stacked {
                stack_pointer_delta_bytes,
                ..
            } => stack_pointer_delta_bytes,
        }
    }

    pub const fn address_size_bytes(self) -> u32 {
        match self {
            Self::Stacked {
                address_size_bytes, ..
            } => address_size_bytes,
        }
    }
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
    /// The slot's declared type as a node of the interface's type graph.
    /// Absent when the interface carries no graph or the graph could not
    /// place the declaration; never a guess.
    logical_type: Option<u32>,
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
            logical_type: None,
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
            logical_type: None,
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
            logical_type: None,
        }
    }

    /// The same slot with its declared type named as a graph node.
    pub const fn with_logical_type(self, type_id: u32) -> Self {
        Self {
            logical_type: Some(type_id),
            ..self
        }
    }

    pub const fn logical_type(&self) -> Option<u32> {
        self.logical_type
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

    /// The same slot stated against another base.
    ///
    /// A source declares a slot against the register it saw the code use,
    /// and a consumer that identifies objects by their entry-relative
    /// position has to restate a frame-pointer slot before the two can be
    /// compared. Width and role are properties of the slot, not of the
    /// coordinate, so they carry over unchanged.
    pub const fn restated(
        self,
        base: StackAddressBase,
        base_storage: CanonicalStorageId,
        offset: i64,
    ) -> Self {
        Self {
            base,
            base_storage,
            offset,
            size_bytes: self.size_bytes,
            role: self.role,
            logical_type: self.logical_type,
        }
    }
}

/// The register names a source spells for the machine role carriers.
///
/// A name is the only part of a source-reported carrier that means the same
/// thing to the architecture that gets lifted. Everything else about the
/// carrier -- its offset above all -- is stated in the source's own register
/// numbering and has to be re-derived from the name before it can be compared
/// with anything the lift produced.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceRoleRegisterNames {
    return_address: Option<SourceRegisterName>,
    stack_pointer: Option<SourceRegisterName>,
    frame_pointer: Option<SourceRegisterName>,
}

/// One register spelling, stored inline.
///
/// Register names are short by construction, and holding one inline keeps the
/// carriers a machine states about itself copyable, which is what every
/// consumer of them already assumes. A name too long for the buffer is refused
/// rather than truncated: a truncated spelling would resolve to a different
/// register, which is the exact failure this type exists to prevent.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct SourceRegisterName {
    bytes: [u8; SOURCE_REGISTER_NAME_MAX],
    len: u8,
}

/// Longest register spelling a source may state.
pub const SOURCE_REGISTER_NAME_MAX: usize = 32;

impl SourceRegisterName {
    /// Take a spelling, refusing one that is empty, over-long, or not plain
    /// ASCII -- a register name outside that set is not one this transport can
    /// compare, and guessing at it would place the wrong register.
    pub fn new(name: &str) -> Option<Self> {
        if name.is_empty() || name.len() > SOURCE_REGISTER_NAME_MAX || !name.is_ascii() {
            return None;
        }
        let mut bytes = [0u8; SOURCE_REGISTER_NAME_MAX];
        bytes[..name.len()].copy_from_slice(name.as_bytes());
        Some(Self {
            bytes,
            len: name.len() as u8,
        })
    }

    pub fn as_str(&self) -> &str {
        // The only constructor accepts ASCII, so the prefix is always UTF-8.
        std::str::from_utf8(&self.bytes[..usize::from(self.len)]).unwrap_or("")
    }
}

impl PartialEq for SourceRegisterName {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for SourceRegisterName {}

impl SourceRoleRegisterNames {
    /// A capture that spelled no carrier at all.
    pub const fn none() -> Self {
        Self {
            return_address: None,
            stack_pointer: None,
            frame_pointer: None,
        }
    }

    /// Record what the source called each carrier. An empty spelling is no
    /// name: a carrier the source could not name is one the consumer must do
    /// without, never one it may place by its offset.
    pub fn new(
        return_address: Option<&str>,
        stack_pointer: Option<&str>,
        frame_pointer: Option<&str>,
    ) -> Self {
        let spelled = |name: Option<&str>| name.and_then(SourceRegisterName::new);
        Self {
            return_address: spelled(return_address),
            stack_pointer: spelled(stack_pointer),
            frame_pointer: spelled(frame_pointer),
        }
    }

    pub fn return_address(&self) -> Option<&str> {
        self.return_address.as_ref().map(SourceRegisterName::as_str)
    }

    pub fn stack_pointer(&self) -> Option<&str> {
        self.stack_pointer.as_ref().map(SourceRegisterName::as_str)
    }

    pub fn frame_pointer(&self) -> Option<&str> {
        self.frame_pointer.as_ref().map(SourceRegisterName::as_str)
    }
}

/// Coherent, revision-bound function interface injected by the source owner.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceFunctionInterface {
    schema_version: u32,
    revision_identity: Box<[u8]>,
    calling_convention: String,
    abi_class: SourceAbiClass,
    parameters: Box<[SourceAbiParameterSpec]>,
    return_kind: SourceFunctionReturn,
    return_address_storage: Option<CanonicalStorageId>,
    stack_pointer_storage: Option<CanonicalStorageId>,
    frame_pointer_storage: Option<CanonicalStorageId>,
    /// How the source spells each role carrier's register.
    ///
    /// The source numbers registers in its own arena, which says nothing about
    /// where the lifted architecture puts the same register: on arm64 the
    /// source calls the link register offset zero and the architecture calls it
    /// 16624. A storage taken from the source therefore names a different
    /// register, or none, until it is resolved through the architecture's own
    /// table -- and a comparison against a value's storage silently never
    /// matched. The name is what survives that translation, so it is what the
    /// capture carries.
    role_register_names: SourceRoleRegisterNames,
    return_mechanism: Option<SourceReturnMechanism>,
    stack_slots: Box<[SourceStackSlotSpec]>,
    parameter_logical_values: Box<[SourceLogicalValue]>,
    return_logical_value: Option<SourceLogicalValue>,
    type_graph: Option<SourceTypeGraph>,
    stack_slot_roles_complete: bool,
    /// The convention states that a callee restores these carriers, so a
    /// consumer may treat them as surviving a call rather than assuming it.
    stack_pointer_preserved_across_calls: bool,
    frame_pointer_preserved_across_calls: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceFunctionInterfaceError {
    EmptyRevisionIdentity,
    EmptyCallingConvention,
    InvalidParameterOrder,
    InvalidRegisterStorage,
    InvalidReturnAddressStorage,
    InvalidStackPointerStorage,
    InvalidFramePointerStorage,
    InvalidReturnMechanism,
    OverlappingRegisterStorages,
    InvalidStackSlot,
    InvalidStackSlotRole,
    OverlappingStackSlots,
    /// The logical types do not describe the physical interface. The reason
    /// names which of the five conditions failed: a consumer that only ever
    /// saw the verdict had no way to tell a lane that overran its carrier
    /// from a type nothing could reach.
    InvalidLogicalTypes {
        reason: &'static str,
    },
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
        let abi_class = SourceAbiClass::from_source_spelling(&calling_convention);
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
        // size zero means the extent was never established, which only an exact role claim may refuse
        if stack_slots.iter().any(|slot| {
            !valid_register_storage(slot.base_storage)
                || (require_exact_stack_slot_roles && slot.size_bytes == 0)
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
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                        reason: "logical values without a type graph",
                    });
                }
                if stack_slots.iter().any(|slot| slot.logical_type.is_some()) {
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                        reason: "a slot names a type without a type graph",
                    });
                }
            }
            Some(graph) => {
                if parameter_logical_values.len() != parameters.len() {
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                        reason: "one logical value per parameter",
                    });
                }
                if parameter_logical_values
                    .iter()
                    .zip(&parameters)
                    .any(|(value, parameter)| {
                        !graph.validates_logical_value(*value, parameter.storage.size)
                    })
                {
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                        reason: "a parameter's logical value does not fit its carrier",
                    });
                }
                match (return_kind, return_logical_value) {
                    (SourceFunctionReturn::Void, None) => {}
                    (SourceFunctionReturn::Register { storage }, Some(value)) => {
                        if !graph.validates_logical_value(value, storage.size) {
                            return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                                reason: "the return's logical value does not fit its carrier",
                            });
                        }
                    }
                    _ => {
                        return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                            reason: "return kind and return logical value disagree",
                        });
                    }
                }
                // A slot's declared type is a root like a parameter's: the
                // graph holds every type the interface names, and the locals
                // name types too.
                if !graph.all_types_reachable(
                    parameter_logical_values
                        .iter()
                        .map(|value| value.type_id())
                        .chain(return_logical_value.map(SourceLogicalValue::type_id))
                        .chain(stack_slots.iter().filter_map(|slot| slot.logical_type)),
                ) {
                    r2il::refusal_evidence!(
                        "logical-types",
                        "roots {:?} return {:?} slots {:?} against a graph of {} types",
                        parameter_logical_values
                            .iter()
                            .map(|value| value.type_id())
                            .collect::<Vec<_>>(),
                        return_logical_value.map(SourceLogicalValue::type_id),
                        stack_slots
                            .iter()
                            .filter_map(|slot| slot.logical_type)
                            .collect::<Vec<_>>(),
                        graph.types.len()
                    );
                    return Err(SourceFunctionInterfaceError::InvalidLogicalTypes {
                        reason: "a logical type is not in the graph",
                    });
                }
            }
        }
        Ok(Self {
            schema_version: SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION,
            revision_identity: revision_identity.into_boxed_slice(),
            calling_convention,
            abi_class,
            parameters: parameters.into_boxed_slice(),
            return_kind,
            return_address_storage: None,
            stack_pointer_storage: None,
            frame_pointer_storage: None,
            role_register_names: SourceRoleRegisterNames::none(),
            return_mechanism: None,
            stack_slots: stack_slots.into_boxed_slice(),
            parameter_logical_values: parameter_logical_values.into_boxed_slice(),
            return_logical_value,
            type_graph,
            stack_slot_roles_complete: require_exact_stack_slot_roles,
            // Preservation is recorded by the capture, which is where the
            // convention is known; a bare interface claims neither.
            stack_pointer_preserved_across_calls: false,
            frame_pointer_preserved_across_calls: false,
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

    pub const fn abi_class(&self) -> SourceAbiClass {
        self.abi_class
    }

    pub const fn parameters(&self) -> &[SourceAbiParameterSpec] {
        &self.parameters
    }

    pub const fn return_kind(&self) -> SourceFunctionReturn {
        self.return_kind
    }

    pub fn return_address_storage_is_valid(&self, storage: CanonicalStorageId) -> bool {
        valid_register_storage(storage)
            && !self
                .parameters
                .iter()
                .map(SourceAbiParameterSpec::storage)
                .chain(match self.return_kind {
                    SourceFunctionReturn::Void => None,
                    SourceFunctionReturn::Register { storage } => Some(storage),
                })
                .chain(self.stack_pointer_storage)
                .chain(self.frame_pointer_storage)
                .chain(
                    self.stack_slots
                        .iter()
                        .map(SourceStackSlotSpec::base_storage),
                )
                .chain(self.stack_slots.iter().filter_map(|slot| match slot.role {
                    SourceStackSlotRole::ParameterHome { home_storage, .. } => Some(home_storage),
                    SourceStackSlotRole::UnclassifiedResource | SourceStackSlotRole::Local => None,
                }))
                .any(|other| register_storages_overlap(storage, other))
    }

    pub fn stack_pointer_storage_is_valid(&self, storage: CanonicalStorageId) -> bool {
        let overlaps_non_stack_role = self
            .parameters
            .iter()
            .map(SourceAbiParameterSpec::storage)
            .chain(match self.return_kind {
                SourceFunctionReturn::Void => None,
                SourceFunctionReturn::Register { storage } => Some(storage),
            })
            .chain(self.return_address_storage)
            .chain(self.frame_pointer_storage)
            .chain(self.stack_slots.iter().filter_map(|slot| match slot.role {
                SourceStackSlotRole::ParameterHome { home_storage, .. } => Some(home_storage),
                SourceStackSlotRole::UnclassifiedResource | SourceStackSlotRole::Local => None,
            }))
            .chain(
                self.stack_slots
                    .iter()
                    .filter(|slot| slot.base == StackAddressBase::FramePointer)
                    .map(SourceStackSlotSpec::base_storage),
            )
            .any(|other| register_storages_overlap(storage, other));
        let mismatched_stack_base = self
            .stack_slots
            .iter()
            .filter(|slot| slot.base == StackAddressBase::StackPointer)
            .any(|slot| slot.base_storage != storage);
        let mismatched_frame_width = self
            .frame_pointer_storage
            .is_some_and(|frame_pointer| frame_pointer.size != storage.size);
        valid_register_storage(storage)
            && !overlaps_non_stack_role
            && !mismatched_stack_base
            && !mismatched_frame_width
    }

    pub fn frame_pointer_storage_is_valid(&self, storage: CanonicalStorageId) -> bool {
        let overlaps_non_frame_role = self
            .parameters
            .iter()
            .map(SourceAbiParameterSpec::storage)
            .chain(match self.return_kind {
                SourceFunctionReturn::Void => None,
                SourceFunctionReturn::Register { storage } => Some(storage),
            })
            .chain(self.return_address_storage)
            .chain(self.stack_pointer_storage)
            .chain(self.stack_slots.iter().filter_map(|slot| match slot.role {
                SourceStackSlotRole::ParameterHome { home_storage, .. } => Some(home_storage),
                SourceStackSlotRole::UnclassifiedResource | SourceStackSlotRole::Local => None,
            }))
            .chain(
                self.stack_slots
                    .iter()
                    .filter(|slot| slot.base == StackAddressBase::StackPointer)
                    .map(SourceStackSlotSpec::base_storage),
            )
            .any(|other| register_storages_overlap(storage, other));
        let mismatched_frame_base = self
            .stack_slots
            .iter()
            .filter(|slot| slot.base == StackAddressBase::FramePointer)
            .any(|slot| slot.base_storage != storage);
        let Some(stack_pointer) = self.stack_pointer_storage else {
            return false;
        };
        let mismatched_stack_width = stack_pointer.size != storage.size;
        valid_register_storage(storage)
            && !overlaps_non_frame_role
            && !mismatched_frame_base
            && !mismatched_stack_width
    }

    /// Bind the machine return-address carrier supplied by the immutable
    /// source snapshot. Exact frame/return certificates require this role;
    /// they never infer it from a register name.
    pub fn with_return_address_storage(
        mut self,
        storage: CanonicalStorageId,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        if self
            .return_mechanism
            .is_some_and(|_| self.return_address_storage != Some(storage))
        {
            return Err(SourceFunctionInterfaceError::InvalidReturnMechanism);
        }
        if !self.return_address_storage_is_valid(storage) {
            return Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage);
        }
        self.return_address_storage = Some(storage);
        Ok(self)
    }

    pub const fn return_address_storage(&self) -> Option<CanonicalStorageId> {
        self.return_address_storage
    }

    /// Record how the source spelled each role carrier.
    pub const fn with_role_register_names(mut self, names: SourceRoleRegisterNames) -> Self {
        self.role_register_names = names;
        self
    }

    pub const fn role_register_names(&self) -> SourceRoleRegisterNames {
        self.role_register_names
    }

    /// Replace the role carriers with the storages the lifted architecture
    /// gives for the names the source spelled.
    ///
    /// This is the one place a source-numbered carrier becomes an
    /// architecture-numbered one, and it runs before anything compares a
    /// carrier with a value. A carrier the architecture cannot place is
    /// dropped rather than kept at its source offset: an absent carrier costs
    /// the certificates that need it, while a carrier at an offset belonging
    /// to some other register is a false statement about the machine.
    pub fn with_arch_resolved_role_carriers(
        mut self,
        return_address: Option<CanonicalStorageId>,
        stack_pointer: Option<CanonicalStorageId>,
        frame_pointer: Option<CanonicalStorageId>,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        if return_address.is_some_and(|storage| !self.return_address_storage_is_valid(storage)) {
            return Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage);
        }
        if stack_pointer.is_some_and(|storage| !self.stack_pointer_storage_is_valid(storage)) {
            return Err(SourceFunctionInterfaceError::InvalidStackPointerStorage);
        }
        self.return_address_storage = return_address;
        self.stack_pointer_storage = stack_pointer;
        // The frame pointer is validated against the carriers just installed,
        // since its rule is that it overlaps neither of them.
        if frame_pointer.is_some_and(|storage| !self.frame_pointer_storage_is_valid(storage)) {
            return Err(SourceFunctionInterfaceError::InvalidFramePointerStorage);
        }
        self.frame_pointer_storage = frame_pointer;
        Ok(self)
    }

    /// Bind the source-owned full-width stack-pointer carrier. This identity
    /// is never inferred from stack resources or register names.
    pub fn with_stack_pointer_storage(
        mut self,
        storage: CanonicalStorageId,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        if self
            .return_mechanism
            .is_some_and(|_| self.stack_pointer_storage != Some(storage))
        {
            return Err(SourceFunctionInterfaceError::InvalidReturnMechanism);
        }
        if !self.stack_pointer_storage_is_valid(storage) {
            return Err(SourceFunctionInterfaceError::InvalidStackPointerStorage);
        }
        self.stack_pointer_storage = Some(storage);
        Ok(self)
    }

    pub const fn stack_pointer_storage(&self) -> Option<CanonicalStorageId> {
        self.stack_pointer_storage
    }

    /// Bind the source-owned full-width frame-pointer carrier. This explicit
    /// fact remains available when the source has no frame-based stack slots.
    pub fn with_frame_pointer_storage(
        mut self,
        storage: CanonicalStorageId,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        if self
            .frame_pointer_storage
            .is_some_and(|bound| bound != storage)
            || !self.frame_pointer_storage_is_valid(storage)
        {
            return Err(SourceFunctionInterfaceError::InvalidFramePointerStorage);
        }
        self.frame_pointer_storage = Some(storage);
        Ok(self)
    }

    pub const fn frame_pointer_storage(&self) -> Option<CanonicalStorageId> {
        self.frame_pointer_storage
    }

    /// Bind an exact stacked return-address contract. The return address is at
    /// entry SP + 0, occupies one complete address-sized slot, and the return
    /// advances SP by exactly that slot width.
    pub fn with_exact_stacked_return(
        mut self,
        stack_offset: i64,
        slot_size_bytes: u32,
        stack_pointer_delta_bytes: u32,
        address_size_bytes: u32,
    ) -> Result<Self, SourceFunctionInterfaceError> {
        let Some(return_address) = self.return_address_storage else {
            return Err(SourceFunctionInterfaceError::InvalidReturnMechanism);
        };
        let Some(stack_pointer) = self.stack_pointer_storage else {
            return Err(SourceFunctionInterfaceError::InvalidReturnMechanism);
        };
        let return_slot_end = i64::from(slot_size_bytes);
        let overlaps_stack_slot = self.stack_slots.iter().any(|slot| {
            if slot.base != StackAddressBase::StackPointer || slot.base_storage != stack_pointer {
                return false;
            }
            let Some(slot_end) = slot.offset.checked_add(i64::from(slot.size_bytes)) else {
                return true;
            };
            slot.offset < return_slot_end && 0 < slot_end
        });
        if stack_offset != 0
            || slot_size_bytes == 0
            || slot_size_bytes != stack_pointer_delta_bytes
            || slot_size_bytes != address_size_bytes
            || return_address.size != address_size_bytes
            || stack_pointer.size != address_size_bytes
            || !self.return_address_storage_is_valid(return_address)
            || !self.stack_pointer_storage_is_valid(stack_pointer)
            || register_storages_overlap(return_address, stack_pointer)
            || overlaps_stack_slot
        {
            return Err(SourceFunctionInterfaceError::InvalidReturnMechanism);
        }
        self.return_mechanism = Some(SourceReturnMechanism::Stacked {
            stack_offset,
            slot_size_bytes,
            stack_pointer_delta_bytes,
            address_size_bytes,
        });
        Ok(self)
    }

    pub const fn return_mechanism(&self) -> Option<SourceReturnMechanism> {
        self.return_mechanism
    }

    /// Return the unique full frame-pointer carrier from an exact stack-slot
    /// contract. This derives a storage identity only; it grants no frame
    /// certification authority.
    pub fn exact_frame_pointer_storage(&self) -> Option<CanonicalStorageId> {
        if let Some(storage) = self.frame_pointer_storage {
            return self
                .frame_pointer_storage_is_valid(storage)
                .then_some(storage);
        }
        if !self.stack_slot_roles_complete
            || self
                .stack_slots
                .iter()
                .any(|slot| slot.role == SourceStackSlotRole::UnclassifiedResource)
        {
            return None;
        }
        let mut frame_slots = self
            .stack_slots
            .iter()
            .filter(|slot| slot.base == StackAddressBase::FramePointer);
        let storage = frame_slots.next()?.base_storage;
        if !valid_register_storage(storage) || frame_slots.any(|slot| slot.base_storage != storage)
        {
            return None;
        }
        let stack_pointer = self.stack_pointer_storage?;
        let return_address = self.return_address_storage?;
        if storage.size != stack_pointer.size
            || !self.stack_pointer_storage_is_valid(stack_pointer)
            || !self.return_address_storage_is_valid(return_address)
        {
            return None;
        }
        let overlaps_source_carrier = self
            .parameters
            .iter()
            .map(SourceAbiParameterSpec::storage)
            .chain(match self.return_kind {
                SourceFunctionReturn::Void => None,
                SourceFunctionReturn::Register { storage } => Some(storage),
            })
            .chain(Some(return_address))
            .chain(Some(stack_pointer))
            .chain(
                self.stack_slots
                    .iter()
                    .filter(|slot| slot.base == StackAddressBase::StackPointer)
                    .map(SourceStackSlotSpec::base_storage),
            )
            .chain(self.stack_slots.iter().filter_map(|slot| match slot.role {
                SourceStackSlotRole::ParameterHome { home_storage, .. } => Some(home_storage),
                SourceStackSlotRole::UnclassifiedResource | SourceStackSlotRole::Local => None,
            }))
            .any(|other| register_storages_overlap(storage, other));
        (!overlaps_source_carrier).then_some(storage)
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

    /// Record that the convention restores these carriers across a call.
    pub fn with_preserved_call_carriers(
        mut self,
        stack_pointer: bool,
        frame_pointer: bool,
    ) -> Self {
        self.stack_pointer_preserved_across_calls = stack_pointer;
        self.frame_pointer_preserved_across_calls = frame_pointer;
        self
    }

    pub const fn stack_pointer_preserved_across_calls(&self) -> bool {
        self.stack_pointer_preserved_across_calls
    }

    pub const fn frame_pointer_preserved_across_calls(&self) -> bool {
        self.frame_pointer_preserved_across_calls
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

/// Source-owned rule that can prove how many arguments one variadic callsite
/// passes.
///
/// This is deliberately attached to the exact callsite interface rather than
/// to a callee type. A variadic prototype names only its fixed prefix; each
/// call's literal format decides the length of its own tail.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SourceVariadicArgumentCountRule {
    /// radare2's recovered prototype named this fixed parameter `format`.
    Radare2FormatString { parameter_index: u32 },
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
    abi_class: SourceAbiClass,
    arguments: Box<[SourceCallArgumentSpec]>,
    variadic: bool,
    variadic_argument_count_rule: Option<SourceVariadicArgumentCountRule>,
    noreturn: bool,
    result: SourceCallResult,
    /// Exact callee-owned interface recovered from a body in the same capture.
    ///
    /// This is a runtime projection rather than snapshot input, so it is
    /// excluded from the source wire representation. The call-site carrier
    /// contract above remains the admission gate; [`Self::with_exact_callee_interface`]
    /// accepts this projection only when every carrier agrees.
    #[serde(skip)]
    exact_callee_interface: Option<Box<SourceFunctionInterface>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceCallSiteInterfaceError {
    EmptyRevisionIdentity,
    InvalidTargetStorage,
    EmptyCallingConvention,
    InvalidArgumentOrder,
    InvalidRegisterStorage,
    OverlappingRegisterStorages,
    VariadicCountRuleOnFixedPrototype,
    InvalidFormatParameterIndex,
    NoreturnWithResult,
    IncompatibleCalleeInterface,
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
        let abi_class = SourceAbiClass::from_source_spelling(&calling_convention);
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
            abi_class,
            arguments: arguments.into_boxed_slice(),
            variadic,
            variadic_argument_count_rule: None,
            noreturn,
            result,
            exact_callee_interface: None,
        })
    }

    /// Attach a callee-owned logical interface when its physical call
    /// contract is exactly this call site's contract.
    pub fn with_exact_callee_interface(
        mut self,
        callee: SourceFunctionInterface,
    ) -> Result<Self, SourceCallSiteInterfaceError> {
        let expected_result = match callee.return_kind() {
            SourceFunctionReturn::Void => SourceCallResult::Void,
            SourceFunctionReturn::Register { storage } => SourceCallResult::Register { storage },
        };
        let carriers_match = self.complete
            && !self.variadic
            && !self.noreturn
            && self.abi_class == callee.abi_class()
            && self.revision_identity() == callee.revision_identity()
            && self.result == expected_result
            && self.arguments.len() == callee.parameters().len()
            && self
                .arguments
                .iter()
                .zip(callee.parameters())
                .all(|(argument, parameter)| {
                    argument.index() == parameter.index()
                        && argument.storage() == parameter.storage()
                });
        if !carriers_match {
            return Err(SourceCallSiteInterfaceError::IncompatibleCalleeInterface);
        }
        self.exact_callee_interface = Some(Box::new(callee));
        Ok(self)
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

    pub const fn abi_class(&self) -> SourceAbiClass {
        self.abi_class
    }

    pub const fn arguments(&self) -> &[SourceCallArgumentSpec] {
        &self.arguments
    }

    pub const fn is_variadic(&self) -> bool {
        self.variadic
    }

    /// Bind the format parameter identified by the source owner's recovered
    /// prototype. The checked builder keeps an untrusted presentation name
    /// from manufacturing an out-of-range semantic role.
    pub fn with_radare2_format_parameter(
        mut self,
        parameter_index: u32,
    ) -> Result<Self, SourceCallSiteInterfaceError> {
        if !self.variadic {
            return Err(SourceCallSiteInterfaceError::VariadicCountRuleOnFixedPrototype);
        }
        if usize::try_from(parameter_index)
            .ok()
            .is_none_or(|index| index >= self.arguments.len())
        {
            return Err(SourceCallSiteInterfaceError::InvalidFormatParameterIndex);
        }
        self.variadic_argument_count_rule =
            Some(SourceVariadicArgumentCountRule::Radare2FormatString { parameter_index });
        Ok(self)
    }

    pub const fn variadic_argument_count_rule(&self) -> Option<SourceVariadicArgumentCountRule> {
        self.variadic_argument_count_rule
    }

    pub const fn is_noreturn(&self) -> bool {
        self.noreturn
    }

    pub const fn result(&self) -> SourceCallResult {
        self.result
    }

    pub fn exact_callee_interface(&self) -> Option<&SourceFunctionInterface> {
        self.exact_callee_interface.as_deref()
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

#[cfg(test)]
mod tests {
    use super::*;

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn exact_return_interface(
        revision: &[u8],
        calling_convention: &str,
        stack_slots: impl IntoIterator<Item = SourceStackSlotSpec>,
    ) -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            revision.to_vec(),
            calling_convention,
            [],
            SourceFunctionReturn::Void,
            stack_slots,
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(80, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(72, 8)))
        .expect("exact return carriers")
    }

    fn test_call_site(calling_convention: &str) -> SourceCallSiteInterface {
        SourceCallSiteInterface::new(
            b"abi-class-callsite".to_vec(),
            SourceCallSiteIdentity::new(
                0x1000,
                0,
                CanonicalStorageId {
                    space: CanonicalStorageSpace::Constant,
                    offset: 0x2000,
                    size: 8,
                },
            ),
            true,
            calling_convention,
            [],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("test callsite")
    }

    #[test]
    fn abi_class_synonyms_are_classified_once_on_each_source_contract() {
        let slots = SourceConventionSlots::new("windows_x64", [], None).expect("slots");
        assert_eq!(slots.abi_class(), SourceAbiClass::MicrosoftX64);
        assert_eq!(slots.calling_convention(), "windows_x64");

        let function = SourceFunctionInterface::new_exact(
            b"abi-class-function".to_vec(),
            "sysv-amd64",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("function interface");
        assert_eq!(function.abi_class(), SourceAbiClass::SystemVAMD64);
        assert_eq!(function.calling_convention(), "sysv-amd64");

        let callsite = test_call_site("microsoft-x64");
        assert_eq!(callsite.abi_class(), SourceAbiClass::MicrosoftX64);
        assert_eq!(callsite.calling_convention(), "microsoft-x64");

        assert_eq!(
            SourceAbiClass::from_source_spelling("ms"),
            SourceAbiClass::Microsoft
        );

        for spelling in ["win64", "windows-x64", "MS_X64"] {
            assert_eq!(
                SourceAbiClass::from_source_spelling(spelling),
                SourceAbiClass::MicrosoftX64
            );
        }
        for spelling in ["sysv64", "system-v-amd64", "x86_64_sysv"] {
            assert_eq!(
                SourceAbiClass::from_source_spelling(spelling),
                SourceAbiClass::SystemVAMD64
            );
        }
    }

    #[test]
    fn abi_class_preserves_renamed_other_spellings_as_presentation_only() {
        let first = SourceConventionSlots::new("vendor-abi-a", [], None).expect("first slots");
        let renamed =
            SourceConventionSlots::new("renamed-vendor-abi", [], None).expect("renamed slots");

        assert_eq!(first.abi_class(), SourceAbiClass::Other);
        assert_eq!(renamed.abi_class(), SourceAbiClass::Other);
        assert_ne!(first.calling_convention(), renamed.calling_convention());
    }

    #[test]
    fn a_format_count_rule_is_checked_against_the_variadic_fixed_prefix() {
        let identity = SourceCallSiteIdentity::new(
            0x1000,
            0,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Constant,
                offset: 0x2000,
                size: 8,
            },
        );
        let arguments = [
            SourceCallArgumentSpec::new(0, register_storage(0, 8)),
            SourceCallArgumentSpec::new(1, register_storage(8, 8)),
        ];
        let variadic = SourceCallSiteInterface::new(
            b"format-rule".to_vec(),
            identity,
            true,
            "sysv-amd64",
            arguments,
            true,
            false,
            SourceCallResult::Void,
        )
        .expect("variadic interface")
        .with_radare2_format_parameter(1)
        .expect("second fixed parameter is the format");
        assert_eq!(
            variadic.variadic_argument_count_rule(),
            Some(SourceVariadicArgumentCountRule::Radare2FormatString { parameter_index: 1 })
        );
        assert_eq!(
            variadic.clone().with_radare2_format_parameter(2),
            Err(SourceCallSiteInterfaceError::InvalidFormatParameterIndex)
        );

        let fixed = SourceCallSiteInterface::new(
            b"fixed-format-rule".to_vec(),
            identity,
            true,
            "sysv-amd64",
            arguments,
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("fixed interface");
        assert_eq!(
            fixed.with_radare2_format_parameter(1),
            Err(SourceCallSiteInterfaceError::VariadicCountRuleOnFixedPrototype)
        );
    }

    #[test]
    fn abi_class_keeps_unknown_and_source_specific_spellings_honest() {
        let absent = SourceConventionSlots::new("", [], None).expect("absent convention slots");
        assert_eq!(absent.abi_class(), SourceAbiClass::Unknown);
        assert_eq!(
            SourceFunctionInterface::new_exact(
                b"unknown-function-abi".to_vec(),
                "unknown",
                [],
                SourceFunctionReturn::Void,
                [],
            )
            .expect("unknown function convention")
            .abi_class(),
            SourceAbiClass::Unknown
        );
        assert_eq!(
            test_call_site("default").abi_class(),
            SourceAbiClass::Unknown
        );
        assert_eq!(
            SourceAbiClass::from_source_spelling("amd64"),
            SourceAbiClass::SystemVAMD64,
            "radare2's exact callconv field uses amd64 for System V AMD64"
        );
        assert_eq!(
            SourceAbiClass::from_source_spelling("aapcs64"),
            SourceAbiClass::Aapcs64
        );
        assert_eq!(
            SourceAbiClass::from_source_spelling("riscv64"),
            SourceAbiClass::RiscV64
        );
    }

    #[test]
    fn slot_of_unestablished_extent_is_kept_without_an_exact_role_claim() {
        let stack_pointer = register_storage(72, 8);
        let slots = [
            SourceStackSlotSpec::new(StackAddressBase::StackPointer, stack_pointer, -40, 0),
            SourceStackSlotSpec::new(StackAddressBase::StackPointer, stack_pointer, -16, 8),
        ];
        let interface = SourceFunctionInterface::new(
            b"revision".to_vec(),
            "amd64",
            [],
            SourceFunctionReturn::Void,
            slots,
        )
        .expect("a located slot of unknown extent is still a fact");
        assert_eq!(interface.stack_slots().len(), 2);
        assert!(!interface.stack_slot_roles_complete());
    }

    #[test]
    fn exact_role_claim_refuses_a_slot_of_unestablished_extent() {
        let stack_pointer = register_storage(72, 8);
        assert_eq!(
            SourceFunctionInterface::new_exact(
                b"revision".to_vec(),
                "amd64",
                [],
                SourceFunctionReturn::Void,
                [SourceStackSlotSpec::new_local(
                    StackAddressBase::StackPointer,
                    stack_pointer,
                    -40,
                    0,
                )],
            ),
            Err(SourceFunctionInterfaceError::InvalidStackSlot)
        );
    }

    #[test]
    fn exact_stacked_return_is_revision_bound_and_name_independent() {
        let stack_pointer = register_storage(72, 8);
        let slots = [
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, stack_pointer, -8, 8),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, stack_pointer, 8, 8),
        ];
        let exact = exact_return_interface(b"stacked-revision-a", "abi-display-a", slots)
            .with_exact_stacked_return(0, 8, 8, 8)
            .expect("exact stacked return");
        assert_eq!(
            exact.schema_version(),
            SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        );
        assert_eq!(exact.revision_identity(), b"stacked-revision-a");
        assert_eq!(
            exact.return_mechanism(),
            Some(SourceReturnMechanism::Stacked {
                stack_offset: 0,
                slot_size_bytes: 8,
                stack_pointer_delta_bytes: 8,
                address_size_bytes: 8,
            })
        );
        let mechanism = exact.return_mechanism().expect("stacked mechanism");
        assert_eq!(mechanism.stack_offset(), 0);
        assert_eq!(mechanism.slot_size_bytes(), 8);
        assert_eq!(mechanism.stack_pointer_delta_bytes(), 8);
        assert_eq!(mechanism.address_size_bytes(), 8);

        let renamed = exact_return_interface(b"stacked-revision-b", "abi-display-b", slots)
            .with_exact_stacked_return(0, 8, 8, 8)
            .expect("renamed exact stacked return");
        assert_eq!(renamed.return_mechanism(), exact.return_mechanism());
        assert_ne!(renamed.revision_identity(), exact.revision_identity());
        assert_ne!(renamed.calling_convention(), exact.calling_convention());
    }

    #[test]
    fn exact_stacked_return_rejects_missing_or_incoherent_carriers() {
        let unbound = SourceFunctionInterface::new_exact(
            b"stacked-unbound".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("unbound exact interface");
        assert_eq!(
            unbound.clone().with_exact_stacked_return(0, 8, 8, 8),
            Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
        );
        assert_eq!(
            unbound
                .clone()
                .with_return_address_storage(register_storage(80, 8))
                .expect("return-address-only interface")
                .with_exact_stacked_return(0, 8, 8, 8),
            Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
        );
        assert_eq!(
            unbound
                .with_stack_pointer_storage(register_storage(72, 8))
                .expect("stack-pointer-only interface")
                .with_exact_stacked_return(0, 8, 8, 8),
            Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
        );

        let exact = exact_return_interface(b"stacked-carriers", "test-abi", []);
        let mut invalid_return_address = exact.clone();
        invalid_return_address.return_address_storage = Some(CanonicalStorageId {
            space: CanonicalStorageSpace::Ram,
            offset: 80,
            size: 8,
        });
        assert_eq!(
            invalid_return_address.with_exact_stacked_return(0, 8, 8, 8),
            Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
        );
        let mut overlapping = exact.clone();
        overlapping.return_address_storage = overlapping.stack_pointer_storage;
        assert_eq!(
            overlapping.with_exact_stacked_return(0, 8, 8, 8),
            Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
        );
        let mut narrow_stack_pointer = exact;
        narrow_stack_pointer.stack_pointer_storage = Some(register_storage(72, 4));
        assert_eq!(
            narrow_stack_pointer.with_exact_stacked_return(0, 8, 8, 8),
            Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
        );
    }

    #[test]
    fn exact_stacked_return_rejects_inexact_geometry_and_stack_overlap() {
        let exact = exact_return_interface(b"stacked-geometry", "test-abi", []);
        for geometry in [(1, 8, 8, 8), (0, 0, 0, 0), (0, 8, 4, 8), (0, 8, 8, 4)] {
            assert_eq!(
                exact
                    .clone()
                    .with_exact_stacked_return(geometry.0, geometry.1, geometry.2, geometry.3,),
                Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
            );
        }

        let stack_pointer = register_storage(72, 8);
        for (offset, size) in [(0, 8), (-4, 8), (4, 8)] {
            let overlapping = exact_return_interface(
                b"stacked-overlap",
                "test-abi",
                [SourceStackSlotSpec::new_local(
                    StackAddressBase::StackPointer,
                    stack_pointer,
                    offset,
                    size,
                )],
            );
            assert_eq!(
                overlapping.with_exact_stacked_return(0, 8, 8, 8),
                Err(SourceFunctionInterfaceError::InvalidReturnMechanism)
            );
        }
    }

    #[test]
    fn exact_stacked_return_cannot_be_invalidated_by_carrier_rebinding() {
        let exact = exact_return_interface(b"stacked-sealed", "test-abi", [])
            .with_exact_stacked_return(0, 8, 8, 8)
            .expect("exact stacked return");
        assert!(
            exact
                .clone()
                .with_return_address_storage(register_storage(88, 8))
                .is_err()
        );
        assert!(
            exact
                .clone()
                .with_stack_pointer_storage(register_storage(96, 8))
                .is_err()
        );
        assert_eq!(
            exact
                .clone()
                .with_return_address_storage(register_storage(80, 8))
                .expect("idempotent return-address binding")
                .return_mechanism(),
            exact.return_mechanism()
        );
        assert_eq!(
            exact
                .clone()
                .with_stack_pointer_storage(register_storage(72, 8))
                .expect("idempotent stack-pointer binding")
                .return_mechanism(),
            exact.return_mechanism()
        );
    }

    #[test]
    fn exact_frame_pointer_storage_requires_one_disjoint_exact_base() {
        let parameter = register_storage(0, 8);
        let result = register_storage(8, 8);
        let frame_pointer = register_storage(64, 8);
        let stack_pointer = register_storage(72, 8);
        let return_address = register_storage(80, 8);
        let exact = SourceFunctionInterface::new_exact(
            b"exact-frame-pointer".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, parameter)],
            SourceFunctionReturn::Register { storage: result },
            [
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    frame_pointer,
                    -16,
                    8,
                ),
                SourceStackSlotSpec::new_parameter_home(
                    StackAddressBase::FramePointer,
                    frame_pointer,
                    -8,
                    8,
                    0,
                    parameter,
                ),
                SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, stack_pointer, 0, 8),
            ],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("coherent exact frame carriers");
        assert_eq!(exact.exact_frame_pointer_storage(), Some(frame_pointer));

        let unbound = SourceFunctionInterface::new_exact(
            b"unbound-frame-pointer".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .expect("unbound exact stack roles");
        assert_eq!(unbound.exact_frame_pointer_storage(), None);
        assert_eq!(
            unbound
                .clone()
                .with_return_address_storage(return_address)
                .expect("return-address-only binding")
                .exact_frame_pointer_storage(),
            None
        );
        assert_eq!(
            unbound
                .with_stack_pointer_storage(stack_pointer)
                .expect("stack-pointer-only binding")
                .exact_frame_pointer_storage(),
            None
        );

        let inexact = SourceFunctionInterface::new(
            b"advisory-frame-pointer".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .expect("advisory frame resource");
        assert_eq!(inexact.exact_frame_pointer_storage(), None);

        let stack_only = SourceFunctionInterface::new_exact(
            b"stack-only".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::StackPointer,
                stack_pointer,
                0,
                8,
            )],
        )
        .expect("exact stack-only resource");
        assert_eq!(stack_only.exact_frame_pointer_storage(), None);

        let parameter_overlap = SourceFunctionInterface::new_exact(
            b"frame-parameter-overlap".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, frame_pointer)],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("representable overlapping source carriers");
        assert_eq!(parameter_overlap.exact_frame_pointer_storage(), None);

        let result_overlap = SourceFunctionInterface::new_exact(
            b"frame-result-overlap".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Register {
                storage: frame_pointer,
            },
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("representable overlapping result carrier");
        assert_eq!(result_overlap.exact_frame_pointer_storage(), None);

        let narrow_frame_pointer = register_storage(88, 4);
        let width_mismatch = SourceFunctionInterface::new_exact(
            b"frame-stack-width-mismatch".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                narrow_frame_pointer,
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("representable frame/SP width mismatch");
        assert_eq!(width_mismatch.exact_frame_pointer_storage(), None);

        let stack_overlap = SourceFunctionInterface::new_exact(
            b"frame-stack-overlap".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [
                SourceStackSlotSpec::new_local(
                    StackAddressBase::FramePointer,
                    frame_pointer,
                    -8,
                    8,
                ),
                SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, frame_pointer, 0, 8),
            ],
        )
        .expect("representable overlapping stack bases");
        assert_eq!(stack_overlap.exact_frame_pointer_storage(), None);
    }

    #[test]
    fn explicit_frame_pointer_storage_is_exact_without_stack_slots_and_name_independent() {
        let frame_pointer = register_storage(64, 8);
        let stack_pointer = register_storage(72, 8);
        let return_address = register_storage(80, 8);
        let build = |revision: &[u8], calling_convention: &str| {
            SourceFunctionInterface::new_exact(
                revision.to_vec(),
                calling_convention,
                [],
                SourceFunctionReturn::Void,
                [],
            )
            .and_then(|interface| interface.with_return_address_storage(return_address))
            .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
            .and_then(|interface| interface.with_frame_pointer_storage(frame_pointer))
        };
        let explicit = build(b"explicit-frame-a", "abi-display-a").expect("explicit frame fact");
        assert_eq!(explicit.frame_pointer_storage(), Some(frame_pointer));
        assert_eq!(explicit.exact_frame_pointer_storage(), Some(frame_pointer));

        let renamed = build(b"explicit-frame-b", "abi-display-b").expect("renamed frame fact");
        assert_eq!(
            renamed.frame_pointer_storage(),
            explicit.frame_pointer_storage()
        );
        assert_eq!(
            renamed.exact_frame_pointer_storage(),
            explicit.exact_frame_pointer_storage()
        );
        assert_ne!(renamed.revision_identity(), explicit.revision_identity());
        assert_ne!(renamed.calling_convention(), explicit.calling_convention());
    }

    #[test]
    fn explicit_frame_pointer_storage_rejects_incoherent_carriers() {
        let parameter = register_storage(0, 8);
        let result = register_storage(8, 8);
        let frame_pointer = register_storage(64, 8);
        let stack_pointer = register_storage(72, 8);
        let return_address = register_storage(80, 8);
        let no_stack_pointer = SourceFunctionInterface::new_exact(
            b"explicit-frame-no-sp".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("slotless interface");
        assert_eq!(
            no_stack_pointer.with_frame_pointer_storage(frame_pointer),
            Err(SourceFunctionInterfaceError::InvalidFramePointerStorage)
        );
        let base = SourceFunctionInterface::new_exact(
            b"explicit-frame-validation".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, parameter)],
            SourceFunctionReturn::Register { storage: result },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(return_address))
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("bound source carriers");

        for overlapping in [parameter, result, stack_pointer, return_address] {
            assert_eq!(
                base.clone().with_frame_pointer_storage(overlapping),
                Err(SourceFunctionInterfaceError::InvalidFramePointerStorage)
            );
        }
        assert_eq!(
            base.clone()
                .with_frame_pointer_storage(register_storage(64, 4)),
            Err(SourceFunctionInterfaceError::InvalidFramePointerStorage)
        );
        assert_eq!(
            base.clone().with_frame_pointer_storage(CanonicalStorageId {
                space: CanonicalStorageSpace::Ram,
                offset: 64,
                size: 8,
            }),
            Err(SourceFunctionInterfaceError::InvalidFramePointerStorage)
        );

        let explicit = base
            .with_frame_pointer_storage(frame_pointer)
            .expect("valid frame pointer");
        assert_eq!(
            explicit
                .clone()
                .with_frame_pointer_storage(register_storage(88, 8)),
            Err(SourceFunctionInterfaceError::InvalidFramePointerStorage)
        );
        assert_eq!(
            explicit.clone().with_return_address_storage(frame_pointer),
            Err(SourceFunctionInterfaceError::InvalidReturnAddressStorage)
        );
        assert_eq!(
            explicit.with_stack_pointer_storage(register_storage(96, 4)),
            Err(SourceFunctionInterfaceError::InvalidStackPointerStorage)
        );
    }

    #[test]
    fn explicit_frame_pointer_storage_must_match_every_frame_slot_base() {
        let frame_pointer = register_storage(64, 8);
        let other_frame_pointer = register_storage(88, 8);
        let interface = SourceFunctionInterface::new_exact(
            b"explicit-frame-slots".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(72, 8)))
        .expect("exact frame slot with stack pointer");
        assert_eq!(
            interface
                .clone()
                .with_frame_pointer_storage(other_frame_pointer),
            Err(SourceFunctionInterfaceError::InvalidFramePointerStorage)
        );
        assert_eq!(
            interface
                .with_frame_pointer_storage(frame_pointer)
                .expect("matching explicit frame base")
                .exact_frame_pointer_storage(),
            Some(frame_pointer)
        );
    }

    #[test]
    fn stack_allocation_contract_requires_exact_sp_and_owns_only_its_growth_interval() {
        let lower = SourceStackAllocationContract::new(SourceStackGrowth::LowerAddresses);
        let higher = SourceStackAllocationContract::new(SourceStackGrowth::HigherAddresses);
        let base = SourceMachineRoles::default();
        assert_eq!(
            base.with_stack_allocation_contract(lower),
            Err(SourceMachineRolesError::InvalidStackAllocationContract)
        );

        let exact = SourceMachineRoles::new(None, Some(register_storage(72, 8)))
            .and_then(|roles| roles.with_stack_allocation_contract(lower))
            .expect("exact downward stack allocation contract");
        assert_eq!(exact.stack_allocation_contract(), Some(lower));
        assert!(lower.owns_entry_relative_reservation(-16, 16));
        assert!(!lower.owns_entry_relative_reservation(0, 16));
        assert!(higher.owns_entry_relative_reservation(0, 16));
        assert!(!higher.owns_entry_relative_reservation(-16, 16));
        assert_eq!(
            exact.with_stack_allocation_contract(higher),
            Err(SourceMachineRolesError::InvalidStackAllocationContract)
        );
    }

    #[test]
    fn stack_allocation_contract_checks_implicit_active_sp_envelopes() {
        let lower = SourceStackAllocationContract::with_implicit_active_sp_bytes(
            SourceStackGrowth::LowerAddresses,
            128,
        );
        assert_eq!(lower.implicit_active_sp_bytes(), 128);
        assert_eq!(lower.owned_entry_relative_envelope(0), Some(-128..0));
        assert_eq!(lower.owned_entry_relative_envelope(-32), Some(-160..0));
        assert_eq!(lower.owned_entry_relative_envelope(1), None);
        assert_eq!(lower.owned_entry_relative_envelope(i64::MIN), None);
        assert!(lower.owns_entry_relative_range(0, -128, 128));
        assert!(lower.owns_entry_relative_range(-32, -160, 128));
        assert!(lower.owns_entry_relative_range(-32, -32, 32));
        assert!(!lower.owns_entry_relative_range(0, -129, 128));
        assert!(!lower.owns_entry_relative_range(0, -128, 0));
        assert!(!lower.owns_entry_relative_range(0, -1, 2));

        let higher = SourceStackAllocationContract::with_implicit_active_sp_bytes(
            SourceStackGrowth::HigherAddresses,
            128,
        );
        assert_eq!(higher.owned_entry_relative_envelope(0), Some(0..128));
        assert_eq!(higher.owned_entry_relative_envelope(32), Some(0..160));
        assert_eq!(higher.owned_entry_relative_envelope(-1), None);
        assert_eq!(higher.owned_entry_relative_envelope(i64::MAX), None);
        assert!(higher.owns_entry_relative_range(0, 0, 128));
        assert!(higher.owns_entry_relative_range(32, 32, 128));
        assert!(higher.owns_entry_relative_range(32, 0, 32));
        assert!(!higher.owns_entry_relative_range(0, 1, 128));
        assert!(!higher.owns_entry_relative_range(i64::MAX, i64::MAX, 1));

        let no_implicit = SourceStackAllocationContract::new(SourceStackGrowth::LowerAddresses);
        assert_eq!(no_implicit.owned_entry_relative_envelope(0), Some(0..0));
        assert!(!no_implicit.owns_entry_relative_range(0, 0, 1));
        assert!(no_implicit.owns_entry_relative_range(-16, -16, 16));
    }
}

/// Machine carriers radare2 knows from its register profile.
///
/// These are deliberately separate from [`SourceFunctionInterface`]. Which
/// register holds a return address, and which one is the stack pointer, are
/// properties of the machine: radare2 resolves them from register aliases and
/// they are available whether or not any ABI was recovered. The interface, by
/// contrast, describes an ABI — parameters, calling convention, return type —
/// and exists only when debug information supplied one.
///
/// Carrying both in one structure is what previously made the machine carriers
/// unreachable without debug information, because the whole structure was
/// captured all-or-nothing. Keeping them apart lets a function be reasoned
/// about on its machine facts while its ABI facts stay honestly absent.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SourceMachineRoles {
    return_address_storage: Option<CanonicalStorageId>,
    stack_pointer_storage: Option<CanonicalStorageId>,
    /// How the source spells these two carriers, for the same reason the
    /// interface records it: the offsets beside them are in the source's
    /// register numbering and mean nothing to the lifted architecture.
    role_register_names: SourceRoleRegisterNames,
    stack_allocation_contract: Option<SourceStackAllocationContract>,
    call_preserved_carriers: Option<SourceCallPreservedCarriers>,
}

/// Whether a call leaves the carriers that address the frame where they were.
///
/// A convention fact, like the stack allocation contract beside it, and the
/// source publishes it whether or not it recovered a prototype -- which is the
/// point. Everything entry-relative about a frame depends on it: if a call may
/// move the stack pointer, no offset taken before one means anything after, so
/// a function that calls loses every fact about its own frame without it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceCallPreservedCarriers {
    stack_pointer: bool,
    frame_pointer: bool,
}

impl SourceCallPreservedCarriers {
    pub const fn new(stack_pointer: bool, frame_pointer: bool) -> Self {
        Self {
            stack_pointer,
            frame_pointer,
        }
    }

    pub const fn stack_pointer(self) -> bool {
        self.stack_pointer
    }

    pub const fn frame_pointer(self) -> bool {
        self.frame_pointer
    }

    /// Whether both carriers that can address a frame survive a call.
    pub const fn frame_survives_a_call(self) -> bool {
        self.stack_pointer && self.frame_pointer
    }
}

/// Where the calling convention would place arguments and the result.
///
/// This describes the convention, not the function. The slots are known even
/// when no prototype was recovered, and they say where a caller *would* leave a
/// value, never that this function takes one. A consumer recovering parameters
/// from machine code intersects this candidate list against what the function
/// reads before writing; without it there is nothing to intersect against, and
/// importing a guessed prototype instead would defeat the purpose.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceConventionSlots {
    calling_convention: String,
    abi_class: SourceAbiClass,
    argument_slots: Box<[CanonicalStorageId]>,
    result_slot: Option<CanonicalStorageId>,
}

impl SourceConventionSlots {
    /// Build the candidate slots, rejecting anything that is not a well-formed
    /// register location or that names the same register twice.
    pub fn new(
        calling_convention: impl Into<String>,
        argument_slots: impl IntoIterator<Item = CanonicalStorageId>,
        result_slot: Option<CanonicalStorageId>,
    ) -> Result<Self, SourceMachineRolesError> {
        let calling_convention = calling_convention.into();
        let abi_class = SourceAbiClass::from_source_spelling(&calling_convention);
        let argument_slots = argument_slots.into_iter().collect::<Vec<_>>();
        if argument_slots
            .iter()
            .any(|storage| !valid_register_storage(*storage))
            || result_slot.is_some_and(|storage| !valid_register_storage(storage))
        {
            return Err(SourceMachineRolesError::InvalidRegisterStorage);
        }
        // A convention that named one register twice would make the candidate
        // order meaningless, so it is refused rather than deduplicated.
        for (index, storage) in argument_slots.iter().enumerate() {
            if argument_slots[..index].contains(storage) {
                return Err(SourceMachineRolesError::InvalidRegisterStorage);
            }
        }
        Ok(Self {
            calling_convention,
            abi_class,
            argument_slots: argument_slots.into_boxed_slice(),
            result_slot,
        })
    }

    /// Convention these candidates belong to, named even when no prototype was
    /// recovered.
    pub fn calling_convention(&self) -> &str {
        &self.calling_convention
    }

    pub const fn abi_class(&self) -> SourceAbiClass {
        self.abi_class
    }

    pub const fn argument_slots(&self) -> &[CanonicalStorageId] {
        &self.argument_slots
    }

    pub const fn result_slot(&self) -> Option<CanonicalStorageId> {
        self.result_slot
    }

    pub const fn is_empty(&self) -> bool {
        self.argument_slots.is_empty() && self.result_slot.is_none()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceMachineRolesError {
    InvalidRegisterStorage,
    InvalidStackAllocationContract,
}

impl SourceMachineRoles {
    /// Build the machine carriers, rejecting any storage that is not a
    /// well-formed register location.
    pub fn new(
        return_address_storage: Option<CanonicalStorageId>,
        stack_pointer_storage: Option<CanonicalStorageId>,
    ) -> Result<Self, SourceMachineRolesError> {
        if return_address_storage.is_some_and(|storage| !valid_register_storage(storage))
            || stack_pointer_storage.is_some_and(|storage| !valid_register_storage(storage))
        {
            return Err(SourceMachineRolesError::InvalidRegisterStorage);
        }
        Ok(Self {
            return_address_storage,
            stack_pointer_storage,
            role_register_names: SourceRoleRegisterNames::none(),
            stack_allocation_contract: None,
            call_preserved_carriers: None,
        })
    }

    /// Record how the source spelled these carriers.
    #[must_use]
    pub const fn with_role_register_names(mut self, names: SourceRoleRegisterNames) -> Self {
        self.role_register_names = names;
        self
    }

    pub const fn role_register_names(&self) -> SourceRoleRegisterNames {
        self.role_register_names
    }

    /// Replace the carriers with the storages the lifted architecture gives
    /// for the names the source spelled, dropping one the architecture cannot
    /// place. This mirrors the interface's resolution and exists for the same
    /// reason: these offsets arrive in the source's numbering.
    pub fn with_arch_resolved_carriers(
        mut self,
        return_address: Option<CanonicalStorageId>,
        stack_pointer: Option<CanonicalStorageId>,
    ) -> Result<Self, SourceMachineRolesError> {
        if return_address.is_some_and(|storage| !valid_register_storage(storage))
            || stack_pointer.is_some_and(|storage| !valid_register_storage(storage))
        {
            return Err(SourceMachineRolesError::InvalidRegisterStorage);
        }
        // The allocation contract is a statement about the stack pointer, so
        // it cannot outlive a stack pointer the architecture would not place.
        if stack_pointer.is_none() {
            self.stack_allocation_contract = None;
        }
        self.return_address_storage = return_address;
        self.stack_pointer_storage = stack_pointer;
        Ok(self)
    }

    /// Bind what a call leaves the frame carriers holding. Like the allocation
    /// contract, this is a convention fact and stays available when no exact
    /// prototype was recovered.
    #[must_use]
    pub const fn with_call_preserved_carriers(
        mut self,
        carriers: SourceCallPreservedCarriers,
    ) -> Self {
        self.call_preserved_carriers = Some(carriers);
        self
    }

    pub const fn call_preserved_carriers(&self) -> Option<SourceCallPreservedCarriers> {
        self.call_preserved_carriers
    }

    /// Bind exact geometric ownership around the architectural stack pointer.
    /// This is a machine/convention fact and remains available when no exact
    /// function prototype was recovered.
    pub fn with_stack_allocation_contract(
        mut self,
        contract: SourceStackAllocationContract,
    ) -> Result<Self, SourceMachineRolesError> {
        if self.stack_pointer_storage.is_none()
            || self
                .stack_allocation_contract
                .is_some_and(|bound| bound != contract)
        {
            return Err(SourceMachineRolesError::InvalidStackAllocationContract);
        }
        self.stack_allocation_contract = Some(contract);
        Ok(self)
    }

    pub const fn return_address_storage(&self) -> Option<CanonicalStorageId> {
        self.return_address_storage
    }

    pub const fn stack_pointer_storage(&self) -> Option<CanonicalStorageId> {
        self.stack_pointer_storage
    }

    pub const fn stack_allocation_contract(&self) -> Option<SourceStackAllocationContract> {
        self.stack_allocation_contract
    }

    /// True when neither carrier is known, which is the state of a source that
    /// could not resolve its register aliases at all.
    pub const fn is_empty(&self) -> bool {
        self.return_address_storage.is_none()
            && self.stack_pointer_storage.is_none()
            && self.stack_allocation_contract.is_none()
    }
}
