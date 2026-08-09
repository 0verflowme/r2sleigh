use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION, CanonicalFnvFoldO0AccessFact,
    CanonicalFnvFoldO0Fact, CanonicalFnvFoldO0ParameterHomeRelayFact,
    CanonicalFnvFoldO0PredicateFact, CanonicalInstructionId, CanonicalStorageId, CompareKind,
    InstId, LoopId, MachineAddressSpace, MachineBuildError, MachineMemoryEndianness, MemoryDefFact,
    MemoryLocation, MemoryPhiFact, MemoryUseFact, MemoryVersion, ObjectId, PredicateId,
    RelativeMemoryAddress, SemanticInstructionState, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind, SourceLogicalValue, SourceStackSlotRole,
    SsaArtifact, StructuredAccessId, ValueId,
};
use serde::Serialize;

use crate::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedAbiParameter, CertifiedArtifactOrigin,
    CertifiedRenderPermit, CertifiedSourceTerminator, CertifiedSourceTopology, ObligationLedger,
    RenderAuthorizationError, TypedRegionMapping,
};

pub const CERTIFIED_FNV_FOLD_O0_CONTRACT_VERSION: u32 = 1;
pub const CERTIFIED_FNV_FOLD_O0_OFFSET_BASIS: u64 = 0x1465_0fb0_739d_0383;
pub const CERTIFIED_FNV_FOLD_O0_PRIME: u64 = 0x0000_0100_0000_01b3;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedFnvFoldO0DispositionClass {
    ProvenDead,
    FrameState,
    InvariantHomeRelay,
    ExternalAliasSealing,
    ForwarderControl,
    LoopControl,
    Semantics,
    Return,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedFnvFoldO0PhiDispositionClass {
    EffectiveLoopState,
    EffectiveInvariantHomeRelay,
    ConservativeAliasConsumed,
    UnusedProvisional,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedFnvFoldO0CompareKind {
    Equal,
    NotEqual,
    Less,
    SignedLess,
    LessEqual,
    SignedLessEqual,
}

impl From<CompareKind> for CertifiedFnvFoldO0CompareKind {
    fn from(kind: CompareKind) -> Self {
        match kind {
            CompareKind::Equal => Self::Equal,
            CompareKind::NotEqual => Self::NotEqual,
            CompareKind::Less => Self::Less,
            CompareKind::SignedLess => Self::SignedLess,
            CompareKind::LessEqual => Self::LessEqual,
            CompareKind::SignedLessEqual => Self::SignedLessEqual,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CertifiedFnvFoldO0MemoryVersion {
    object: ObjectId,
    version: u32,
}

impl CertifiedFnvFoldO0MemoryVersion {
    pub const fn object(self) -> ObjectId {
        self.object
    }

    pub const fn version(self) -> u32 {
        self.version
    }
}

impl From<MemoryVersion> for CertifiedFnvFoldO0MemoryVersion {
    fn from(version: MemoryVersion) -> Self {
        Self {
            object: version.object,
            version: version.version,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0AffineAddressTerm {
    value: ValueId,
    coefficient: i64,
}

impl CertifiedFnvFoldO0AffineAddressTerm {
    pub const fn value(&self) -> ValueId {
        self.value
    }
    pub const fn coefficient(&self) -> i64 {
        self.coefficient
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedFnvFoldO0RelativeAddress {
    Exact(i64),
    Affine {
        terms: Box<[CertifiedFnvFoldO0AffineAddressTerm]>,
        offset: i64,
    },
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0MemoryLocation {
    object: ObjectId,
    address: CertifiedFnvFoldO0RelativeAddress,
    size: u32,
}

impl CertifiedFnvFoldO0MemoryLocation {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn address(&self) -> &CertifiedFnvFoldO0RelativeAddress {
        &self.address
    }

    pub const fn size(&self) -> u32 {
        self.size
    }
}

fn memory_location(location: &MemoryLocation) -> Option<CertifiedFnvFoldO0MemoryLocation> {
    let address = match &location.address {
        RelativeMemoryAddress::Exact(offset) => CertifiedFnvFoldO0RelativeAddress::Exact(*offset),
        RelativeMemoryAddress::Unknown => CertifiedFnvFoldO0RelativeAddress::Unknown,
        RelativeMemoryAddress::Affine { terms, offset } => {
            CertifiedFnvFoldO0RelativeAddress::Affine {
                terms: terms
                    .iter()
                    .map(|term| CertifiedFnvFoldO0AffineAddressTerm {
                        value: term.value,
                        coefficient: term.coefficient,
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
                offset: *offset,
            }
        }
    };
    Some(CertifiedFnvFoldO0MemoryLocation {
        object: location.object,
        address,
        size: location.size,
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0MemoryUse {
    location: CertifiedFnvFoldO0MemoryLocation,
    version: CertifiedFnvFoldO0MemoryVersion,
}

impl CertifiedFnvFoldO0MemoryUse {
    pub const fn location(&self) -> &CertifiedFnvFoldO0MemoryLocation {
        &self.location
    }

    pub const fn version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.version
    }
}

fn memory_use(use_fact: &MemoryUseFact) -> Option<CertifiedFnvFoldO0MemoryUse> {
    Some(CertifiedFnvFoldO0MemoryUse {
        location: memory_location(&use_fact.location)?,
        version: use_fact.version.into(),
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0MemoryDef {
    location: CertifiedFnvFoldO0MemoryLocation,
    previous_version: CertifiedFnvFoldO0MemoryVersion,
    next_version: CertifiedFnvFoldO0MemoryVersion,
}

impl CertifiedFnvFoldO0MemoryDef {
    pub const fn location(&self) -> &CertifiedFnvFoldO0MemoryLocation {
        &self.location
    }

    pub const fn previous_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.previous_version
    }

    pub const fn next_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.next_version
    }
}

fn memory_def(def: &MemoryDefFact) -> Option<CertifiedFnvFoldO0MemoryDef> {
    Some(CertifiedFnvFoldO0MemoryDef {
        location: memory_location(&def.location)?,
        previous_version: def.previous_version.into(),
        next_version: def.next_version.into(),
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0MemoryPhi {
    object: ObjectId,
    location: CertifiedFnvFoldO0MemoryLocation,
    output_version: CertifiedFnvFoldO0MemoryVersion,
    inputs: Box<[(u64, CertifiedFnvFoldO0MemoryVersion)]>,
    disposition: CertifiedFnvFoldO0PhiDispositionClass,
}

impl CertifiedFnvFoldO0MemoryPhi {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn location(&self) -> &CertifiedFnvFoldO0MemoryLocation {
        &self.location
    }

    pub const fn output_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.output_version
    }

    pub const fn inputs(&self) -> &[(u64, CertifiedFnvFoldO0MemoryVersion)] {
        &self.inputs
    }

    pub const fn disposition(&self) -> CertifiedFnvFoldO0PhiDispositionClass {
        self.disposition
    }
}

fn memory_phi(
    phi: &MemoryPhiFact,
    disposition: CertifiedFnvFoldO0PhiDispositionClass,
) -> Option<CertifiedFnvFoldO0MemoryPhi> {
    Some(CertifiedFnvFoldO0MemoryPhi {
        object: phi.object,
        location: memory_location(&phi.location)?,
        output_version: phi.output_version.into(),
        inputs: phi
            .inputs
            .iter()
            .map(|(block, version)| (*block, (*version).into()))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        disposition,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CertifiedFnvFoldO0AccessId {
    producer: CanonicalInstructionId,
    ordinal: u32,
}

impl CertifiedFnvFoldO0AccessId {
    pub const fn producer(self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn ordinal(self) -> u32 {
        self.ordinal
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Access {
    id: CertifiedFnvFoldO0AccessId,
    object: ObjectId,
    address: ValueId,
    value: ValueId,
    is_write: bool,
    width: u32,
    memory_space: MachineAddressSpace,
    memory_uses: Box<[CertifiedFnvFoldO0MemoryUse]>,
    memory_defs: Box<[CertifiedFnvFoldO0MemoryDef]>,
}

impl CertifiedFnvFoldO0Access {
    pub const fn id(&self) -> CertifiedFnvFoldO0AccessId {
        self.id
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn address(&self) -> ValueId {
        self.address
    }

    pub const fn value(&self) -> ValueId {
        self.value
    }

    pub const fn is_write(&self) -> bool {
        self.is_write
    }

    pub const fn width(&self) -> u32 {
        self.width
    }

    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }

    pub const fn memory_uses(&self) -> &[CertifiedFnvFoldO0MemoryUse] {
        &self.memory_uses
    }

    pub const fn memory_defs(&self) -> &[CertifiedFnvFoldO0MemoryDef] {
        &self.memory_defs
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Slot {
    object: ObjectId,
    declared_offset_from_allocated_sp: i64,
    offset_from_entry_sp: i64,
    width: u32,
    role: SourceStackSlotRole,
    accesses: Box<[CertifiedFnvFoldO0AccessId]>,
}

impl CertifiedFnvFoldO0Slot {
    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn declared_offset_from_allocated_sp(&self) -> i64 {
        self.declared_offset_from_allocated_sp
    }

    pub const fn offset_from_entry_sp(&self) -> i64 {
        self.offset_from_entry_sp
    }

    pub const fn width(&self) -> u32 {
        self.width
    }

    pub const fn role(&self) -> SourceStackSlotRole {
        self.role
    }

    pub const fn accesses(&self) -> &[CertifiedFnvFoldO0AccessId] {
        &self.accesses
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Topology {
    entry: u64,
    header: u64,
    first_forwarder: u64,
    first_predicate_block: u64,
    second_forwarder: u64,
    second_predicate_block: u64,
    lowercase_forwarder: u64,
    lowercase_block: u64,
    hash_block: u64,
    latch: u64,
    exit: u64,
}

impl CertifiedFnvFoldO0Topology {
    pub const fn entry(&self) -> u64 {
        self.entry
    }
    pub const fn header(&self) -> u64 {
        self.header
    }
    pub const fn first_forwarder(&self) -> u64 {
        self.first_forwarder
    }
    pub const fn first_predicate_block(&self) -> u64 {
        self.first_predicate_block
    }
    pub const fn second_forwarder(&self) -> u64 {
        self.second_forwarder
    }
    pub const fn second_predicate_block(&self) -> u64 {
        self.second_predicate_block
    }
    pub const fn lowercase_forwarder(&self) -> u64 {
        self.lowercase_forwarder
    }
    pub const fn lowercase_block(&self) -> u64 {
        self.lowercase_block
    }
    pub const fn hash_block(&self) -> u64 {
        self.hash_block
    }
    pub const fn latch(&self) -> u64 {
        self.latch
    }
    pub const fn exit(&self) -> u64 {
        self.exit
    }

    fn ordered(&self) -> [u64; 11] {
        [
            self.entry,
            self.header,
            self.first_forwarder,
            self.first_predicate_block,
            self.second_forwarder,
            self.second_predicate_block,
            self.lowercase_forwarder,
            self.lowercase_block,
            self.hash_block,
            self.latch,
            self.exit,
        ]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Phase {
    block: u64,
    producers: Box<[CanonicalInstructionId]>,
}

impl CertifiedFnvFoldO0Phase {
    pub const fn block(&self) -> u64 {
        self.block
    }
    pub const fn producers(&self) -> &[CanonicalInstructionId] {
        &self.producers
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Predicate {
    predicate: PredicateId,
    condition: ValueId,
    branch: CanonicalInstructionId,
    witnesses: Box<[CanonicalInstructionId]>,
    lhs: ValueId,
    rhs: ValueId,
    kind: CertifiedFnvFoldO0CompareKind,
    true_target: u64,
    false_target: u64,
}

impl CertifiedFnvFoldO0Predicate {
    pub const fn predicate(&self) -> PredicateId {
        self.predicate
    }
    pub const fn condition(&self) -> ValueId {
        self.condition
    }
    pub const fn branch(&self) -> CanonicalInstructionId {
        self.branch
    }
    pub const fn witnesses(&self) -> &[CanonicalInstructionId] {
        &self.witnesses
    }
    pub const fn lhs(&self) -> ValueId {
        self.lhs
    }
    pub const fn rhs(&self) -> ValueId {
        self.rhs
    }
    pub const fn kind(&self) -> CertifiedFnvFoldO0CompareKind {
        self.kind
    }
    pub const fn true_target(&self) -> u64 {
        self.true_target
    }
    pub const fn false_target(&self) -> u64 {
        self.false_target
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Frame {
    stack_storage: CanonicalStorageId,
    link_register_storage: CanonicalStorageId,
    entry_sp: ValueId,
    allocated_sp: ValueId,
    allocate: CanonicalInstructionId,
    allocate_arithmetic: CanonicalInstructionId,
    allocate_support: Box<[CanonicalInstructionId]>,
    restored_sp: ValueId,
    restore: CanonicalInstructionId,
    restore_arithmetic: CanonicalInstructionId,
    restore_support: Box<[CanonicalInstructionId]>,
    address_support: Box<[CanonicalInstructionId]>,
    return_address: ValueId,
    return_target: ValueId,
    return_target_support: Box<[CanonicalInstructionId]>,
    return_instruction: CanonicalInstructionId,
    homes: Box<[CertifiedFnvFoldO0Slot]>,
    locals: Box<[CertifiedFnvFoldO0Slot]>,
}

impl CertifiedFnvFoldO0Frame {
    pub const fn stack_storage(&self) -> CanonicalStorageId {
        self.stack_storage
    }
    pub const fn link_register_storage(&self) -> CanonicalStorageId {
        self.link_register_storage
    }
    pub const fn entry_sp(&self) -> ValueId {
        self.entry_sp
    }
    pub const fn allocated_sp(&self) -> ValueId {
        self.allocated_sp
    }
    pub const fn allocate(&self) -> CanonicalInstructionId {
        self.allocate
    }
    pub const fn allocate_arithmetic(&self) -> CanonicalInstructionId {
        self.allocate_arithmetic
    }
    pub const fn allocate_support(&self) -> &[CanonicalInstructionId] {
        &self.allocate_support
    }
    pub const fn restored_sp(&self) -> ValueId {
        self.restored_sp
    }
    pub const fn restore(&self) -> CanonicalInstructionId {
        self.restore
    }
    pub const fn restore_arithmetic(&self) -> CanonicalInstructionId {
        self.restore_arithmetic
    }
    pub const fn restore_support(&self) -> &[CanonicalInstructionId] {
        &self.restore_support
    }
    pub const fn address_support(&self) -> &[CanonicalInstructionId] {
        &self.address_support
    }
    pub const fn return_target(&self) -> ValueId {
        self.return_target
    }
    pub const fn return_address(&self) -> ValueId {
        self.return_address
    }
    pub const fn return_target_support(&self) -> &[CanonicalInstructionId] {
        &self.return_target_support
    }
    pub const fn return_instruction(&self) -> CanonicalInstructionId {
        self.return_instruction
    }
    pub const fn homes(&self) -> &[CertifiedFnvFoldO0Slot] {
        &self.homes
    }
    pub const fn locals(&self) -> &[CertifiedFnvFoldO0Slot] {
        &self.locals
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Index {
    object: ObjectId,
    initializer_store: CertifiedFnvFoldO0AccessId,
    initializer_support_instructions: Box<[CanonicalInstructionId]>,
    initializer_version: CertifiedFnvFoldO0MemoryVersion,
    phi: CertifiedFnvFoldO0MemoryPhi,
    header_load: CertifiedFnvFoldO0AccessId,
    address_load: CertifiedFnvFoldO0AccessId,
    latch_load: CertifiedFnvFoldO0AccessId,
    update: ValueId,
    update_instruction: CanonicalInstructionId,
    update_support_instructions: Box<[CanonicalInstructionId]>,
    update_store: CertifiedFnvFoldO0AccessId,
    update_version: CertifiedFnvFoldO0MemoryVersion,
    buffer_address: ValueId,
    buffer_access: CertifiedFnvFoldO0AccessId,
    buffer_object: ObjectId,
    raw_byte: ValueId,
}

impl CertifiedFnvFoldO0Index {
    pub const fn object(&self) -> ObjectId {
        self.object
    }
    pub const fn initializer_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.initializer_store
    }
    pub const fn initializer_support_instructions(&self) -> &[CanonicalInstructionId] {
        &self.initializer_support_instructions
    }
    pub const fn initializer_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.initializer_version
    }
    pub const fn phi(&self) -> &CertifiedFnvFoldO0MemoryPhi {
        &self.phi
    }
    pub const fn header_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.header_load
    }
    pub const fn address_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.address_load
    }
    pub const fn latch_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.latch_load
    }
    pub const fn update(&self) -> ValueId {
        self.update
    }
    pub const fn update_instruction(&self) -> CanonicalInstructionId {
        self.update_instruction
    }
    pub const fn update_support_instructions(&self) -> &[CanonicalInstructionId] {
        &self.update_support_instructions
    }
    pub const fn update_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.update_store
    }
    pub const fn update_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.update_version
    }
    pub const fn buffer_address(&self) -> ValueId {
        self.buffer_address
    }
    pub const fn buffer_access(&self) -> CertifiedFnvFoldO0AccessId {
        self.buffer_access
    }
    pub const fn buffer_object(&self) -> ObjectId {
        self.buffer_object
    }
    pub const fn raw_byte(&self) -> ValueId {
        self.raw_byte
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Ascii {
    object: ObjectId,
    initial_store: CertifiedFnvFoldO0AccessId,
    initial_version: CertifiedFnvFoldO0MemoryVersion,
    first_load: CertifiedFnvFoldO0AccessId,
    first_predicate: CertifiedFnvFoldO0Predicate,
    second_load: CertifiedFnvFoldO0AccessId,
    second_predicate: CertifiedFnvFoldO0Predicate,
    lowercase_load: CertifiedFnvFoldO0AccessId,
    lowercase: ValueId,
    lowercase_instruction: CanonicalInstructionId,
    lowercase_support_instructions: Box<[CanonicalInstructionId]>,
    lowercase_store: CertifiedFnvFoldO0AccessId,
    lowercase_version: CertifiedFnvFoldO0MemoryVersion,
    merge_phi: CertifiedFnvFoldO0MemoryPhi,
    merge_load: CertifiedFnvFoldO0AccessId,
    selected_byte: ValueId,
}

impl CertifiedFnvFoldO0Ascii {
    pub const fn object(&self) -> ObjectId {
        self.object
    }
    pub const fn initial_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.initial_store
    }
    pub const fn initial_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.initial_version
    }
    pub const fn first_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.first_load
    }
    pub const fn first_predicate(&self) -> &CertifiedFnvFoldO0Predicate {
        &self.first_predicate
    }
    pub const fn second_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.second_load
    }
    pub const fn second_predicate(&self) -> &CertifiedFnvFoldO0Predicate {
        &self.second_predicate
    }
    pub const fn lowercase_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.lowercase_load
    }
    pub const fn lowercase(&self) -> ValueId {
        self.lowercase
    }
    pub const fn lowercase_instruction(&self) -> CanonicalInstructionId {
        self.lowercase_instruction
    }
    pub const fn lowercase_support_instructions(&self) -> &[CanonicalInstructionId] {
        &self.lowercase_support_instructions
    }
    pub const fn lowercase_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.lowercase_store
    }
    pub const fn lowercase_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.lowercase_version
    }
    pub const fn merge_phi(&self) -> &CertifiedFnvFoldO0MemoryPhi {
        &self.merge_phi
    }
    pub const fn merge_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.merge_load
    }
    pub const fn selected_byte(&self) -> ValueId {
        self.selected_byte
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Hash {
    object: ObjectId,
    offset_basis: u64,
    initializer: ValueId,
    initializer_witnesses: Box<[CanonicalInstructionId]>,
    initializer_store: CertifiedFnvFoldO0AccessId,
    initializer_version: CertifiedFnvFoldO0MemoryVersion,
    phi: CertifiedFnvFoldO0MemoryPhi,
    body_load: CertifiedFnvFoldO0AccessId,
    selected64: ValueId,
    selected64_instruction: CanonicalInstructionId,
    xor: ValueId,
    xor_instruction: CanonicalInstructionId,
    xor_store: CertifiedFnvFoldO0AccessId,
    xor_version: CertifiedFnvFoldO0MemoryVersion,
    xor_reload: CertifiedFnvFoldO0AccessId,
    prime: ValueId,
    prime_value: u64,
    prime_witnesses: Box<[CanonicalInstructionId]>,
    product: ValueId,
    multiply_instruction: CanonicalInstructionId,
    product_store: CertifiedFnvFoldO0AccessId,
    product_version: CertifiedFnvFoldO0MemoryVersion,
    exit_load: CertifiedFnvFoldO0AccessId,
}

impl CertifiedFnvFoldO0Hash {
    pub const fn object(&self) -> ObjectId {
        self.object
    }
    pub const fn offset_basis(&self) -> u64 {
        self.offset_basis
    }
    pub const fn initializer(&self) -> ValueId {
        self.initializer
    }
    pub const fn initializer_witnesses(&self) -> &[CanonicalInstructionId] {
        &self.initializer_witnesses
    }
    pub const fn initializer_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.initializer_store
    }
    pub const fn initializer_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.initializer_version
    }
    pub const fn phi(&self) -> &CertifiedFnvFoldO0MemoryPhi {
        &self.phi
    }
    pub const fn body_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.body_load
    }
    pub const fn selected64(&self) -> ValueId {
        self.selected64
    }
    pub const fn selected64_instruction(&self) -> CanonicalInstructionId {
        self.selected64_instruction
    }
    pub const fn xor(&self) -> ValueId {
        self.xor
    }
    pub const fn xor_instruction(&self) -> CanonicalInstructionId {
        self.xor_instruction
    }
    pub const fn xor_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.xor_store
    }
    pub const fn xor_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.xor_version
    }
    pub const fn xor_reload(&self) -> CertifiedFnvFoldO0AccessId {
        self.xor_reload
    }
    pub const fn prime(&self) -> ValueId {
        self.prime
    }
    pub const fn prime_value(&self) -> u64 {
        self.prime_value
    }
    pub const fn prime_witnesses(&self) -> &[CanonicalInstructionId] {
        &self.prime_witnesses
    }
    pub const fn product(&self) -> ValueId {
        self.product
    }
    pub const fn multiply_instruction(&self) -> CanonicalInstructionId {
        self.multiply_instruction
    }
    pub const fn product_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.product_store
    }
    pub const fn product_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.product_version
    }
    pub const fn exit_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.exit_load
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0ExternalAliasPolicy {
    complete_frame_separation: bool,
    frame_address_escape_free: bool,
    source_external_byte_pointer: bool,
    external_object: ObjectId,
    external_read: CertifiedFnvFoldO0AccessId,
    pointer_home: CertifiedFnvFoldO0ParameterHomeRelay,
    index_load: CertifiedFnvFoldO0AccessId,
    address: ValueId,
    address_instruction: CanonicalInstructionId,
    address_support_instructions: Box<[CanonicalInstructionId]>,
    classified_frame_objects: Box<[ObjectId]>,
    external_memory_use: CertifiedFnvFoldO0MemoryUse,
}

impl CertifiedFnvFoldO0ExternalAliasPolicy {
    pub const fn complete_frame_separation(&self) -> bool {
        self.complete_frame_separation
    }
    pub const fn frame_address_escape_free(&self) -> bool {
        self.frame_address_escape_free
    }
    pub const fn source_external_byte_pointer(&self) -> bool {
        self.source_external_byte_pointer
    }
    pub const fn external_object(&self) -> ObjectId {
        self.external_object
    }
    pub const fn external_read(&self) -> CertifiedFnvFoldO0AccessId {
        self.external_read
    }
    pub const fn pointer_home(&self) -> &CertifiedFnvFoldO0ParameterHomeRelay {
        &self.pointer_home
    }
    pub const fn index_load(&self) -> CertifiedFnvFoldO0AccessId {
        self.index_load
    }
    pub const fn address(&self) -> ValueId {
        self.address
    }
    pub const fn address_instruction(&self) -> CanonicalInstructionId {
        self.address_instruction
    }
    pub const fn address_support_instructions(&self) -> &[CanonicalInstructionId] {
        &self.address_support_instructions
    }
    pub const fn classified_frame_objects(&self) -> &[ObjectId] {
        &self.classified_frame_objects
    }
    pub const fn external_memory_use(&self) -> &CertifiedFnvFoldO0MemoryUse {
        &self.external_memory_use
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0ParameterHomeRelay {
    parameter_index: u32,
    initializer_store: CertifiedFnvFoldO0AccessId,
    initializer_version: CertifiedFnvFoldO0MemoryVersion,
    phi: CertifiedFnvFoldO0MemoryPhi,
    reload: CertifiedFnvFoldO0AccessId,
    value: ValueId,
}

impl CertifiedFnvFoldO0ParameterHomeRelay {
    pub const fn parameter_index(&self) -> u32 {
        self.parameter_index
    }
    pub const fn initializer_store(&self) -> CertifiedFnvFoldO0AccessId {
        self.initializer_store
    }
    pub const fn initializer_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.initializer_version
    }
    pub const fn phi(&self) -> &CertifiedFnvFoldO0MemoryPhi {
        &self.phi
    }
    pub const fn reload(&self) -> CertifiedFnvFoldO0AccessId {
        self.reload
    }
    pub const fn value(&self) -> ValueId {
        self.value
    }
}

/// Sealed whole-function certificate for the exact eleven-block ARM64 O0 FNV fold.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFnvFoldO0Function {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    revision_identity: Box<[u8]>,
    loop_id: LoopId,
    topology: CertifiedFnvFoldO0Topology,
    phases: Box<[CertifiedFnvFoldO0Phase]>,
    pointer_parameter: CertifiedAbiParameter,
    length_parameter: CertifiedAbiParameter,
    return_storage: CanonicalStorageId,
    pointer_logical: SourceLogicalValue,
    length_logical: SourceLogicalValue,
    return_logical: SourceLogicalValue,
    memory_space: MachineAddressSpace,
    memory_address_bits: u32,
    memory_word_size_bytes: u32,
    memory_endianness: MachineMemoryEndianness,
    frame: CertifiedFnvFoldO0Frame,
    accesses: Box<[CertifiedFnvFoldO0Access]>,
    unused_provisional_phis: Box<[CertifiedFnvFoldO0MemoryPhi]>,
    conservative_alias_only_header_phis: Box<[CertifiedFnvFoldO0MemoryPhi]>,
    loop_guard: CertifiedFnvFoldO0Predicate,
    index: CertifiedFnvFoldO0Index,
    length_home: CertifiedFnvFoldO0ParameterHomeRelay,
    external_alias_policy: CertifiedFnvFoldO0ExternalAliasPolicy,
    ascii: CertifiedFnvFoldO0Ascii,
    hash: CertifiedFnvFoldO0Hash,
    returned_hash_access: CertifiedFnvFoldO0AccessId,
    returned_hash_version: CertifiedFnvFoldO0MemoryVersion,
    returned_value: ValueId,
    return_instruction: CanonicalInstructionId,
    return_target: ValueId,
    proven_dead_producers: Box<[CanonicalInstructionId]>,
    instruction_dispositions: Box<[(CanonicalInstructionId, CertifiedFnvFoldO0DispositionClass)]>,
    obligation_dispositions: Box<[(SemanticObligationId, CertifiedFnvFoldO0DispositionClass)]>,
}

impl CertifiedFnvFoldO0Function {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }
    pub const fn contract_version(&self) -> u32 {
        self.contract_version
    }
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }
    pub const fn loop_id(&self) -> LoopId {
        self.loop_id
    }
    pub const fn topology(&self) -> &CertifiedFnvFoldO0Topology {
        &self.topology
    }
    pub const fn phases(&self) -> &[CertifiedFnvFoldO0Phase] {
        &self.phases
    }
    pub const fn pointer_parameter(&self) -> &CertifiedAbiParameter {
        &self.pointer_parameter
    }
    pub const fn length_parameter(&self) -> &CertifiedAbiParameter {
        &self.length_parameter
    }
    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }
    pub const fn pointer_logical(&self) -> SourceLogicalValue {
        self.pointer_logical
    }
    pub const fn length_logical(&self) -> SourceLogicalValue {
        self.length_logical
    }
    pub const fn return_logical(&self) -> SourceLogicalValue {
        self.return_logical
    }
    pub const fn memory_space(&self) -> MachineAddressSpace {
        self.memory_space
    }
    pub const fn memory_address_bits(&self) -> u32 {
        self.memory_address_bits
    }
    pub const fn memory_word_size_bytes(&self) -> u32 {
        self.memory_word_size_bytes
    }
    pub const fn memory_endianness(&self) -> MachineMemoryEndianness {
        self.memory_endianness
    }
    pub const fn frame(&self) -> &CertifiedFnvFoldO0Frame {
        &self.frame
    }
    pub const fn accesses(&self) -> &[CertifiedFnvFoldO0Access] {
        &self.accesses
    }
    pub const fn unused_provisional_phis(&self) -> &[CertifiedFnvFoldO0MemoryPhi] {
        &self.unused_provisional_phis
    }
    pub const fn conservative_alias_only_header_phis(&self) -> &[CertifiedFnvFoldO0MemoryPhi] {
        &self.conservative_alias_only_header_phis
    }
    pub const fn loop_guard(&self) -> &CertifiedFnvFoldO0Predicate {
        &self.loop_guard
    }
    pub const fn index(&self) -> &CertifiedFnvFoldO0Index {
        &self.index
    }
    pub const fn length_home(&self) -> &CertifiedFnvFoldO0ParameterHomeRelay {
        &self.length_home
    }
    pub const fn external_alias_policy(&self) -> &CertifiedFnvFoldO0ExternalAliasPolicy {
        &self.external_alias_policy
    }
    pub const fn ascii(&self) -> &CertifiedFnvFoldO0Ascii {
        &self.ascii
    }
    pub const fn hash(&self) -> &CertifiedFnvFoldO0Hash {
        &self.hash
    }
    pub const fn returned_hash_access(&self) -> CertifiedFnvFoldO0AccessId {
        self.returned_hash_access
    }
    pub const fn returned_hash_version(&self) -> CertifiedFnvFoldO0MemoryVersion {
        self.returned_hash_version
    }
    pub const fn returned_value(&self) -> ValueId {
        self.returned_value
    }
    pub const fn return_instruction(&self) -> CanonicalInstructionId {
        self.return_instruction
    }
    pub const fn proven_dead_producers(&self) -> &[CanonicalInstructionId] {
        &self.proven_dead_producers
    }
    pub const fn return_target(&self) -> ValueId {
        self.return_target
    }
    pub const fn instruction_dispositions(
        &self,
    ) -> &[(CanonicalInstructionId, CertifiedFnvFoldO0DispositionClass)] {
        &self.instruction_dispositions
    }
    pub const fn obligation_dispositions(
        &self,
    ) -> &[(SemanticObligationId, CertifiedFnvFoldO0DispositionClass)] {
        &self.obligation_dispositions
    }

    pub(crate) fn validate(&self, source: &SemanticObligationInventory) -> Result<(), ()> {
        if self.schema_version != CERTIFICATION_SCHEMA_VERSION
            || self.contract_version != CERTIFIED_FNV_FOLD_O0_CONTRACT_VERSION
            || self.origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || !self
                .origin
                .matches_retained_source(source, self.origin.topology())
            || self.origin.source() != source
            || self.revision_identity.is_empty()
            || self.hash.offset_basis != CERTIFIED_FNV_FOLD_O0_OFFSET_BASIS
            || self.hash.prime_value != CERTIFIED_FNV_FOLD_O0_PRIME
            || self.pointer_parameter.index() != 0
            || self.length_parameter.index() != 1
            || self.memory_address_bits != 64
            || self.memory_word_size_bytes != 1
            || self.memory_endianness != MachineMemoryEndianness::Little
            || self.memory_space != MachineAddressSpace::Ram
            || !self.obligation_surface_is_exact(source)
        {
            return Err(());
        }
        let Some(interface) = self.origin.machine_context().source().function_interface() else {
            return Err(());
        };
        if interface.revision_identity() != self.revision_identity.as_ref() {
            return Err(());
        }
        let blocks = self.topology.ordered();
        if blocks.into_iter().collect::<BTreeSet<_>>().len() != 11
            || self.origin.topology().blocks().len() != 11
            || self.origin.topology().entry_addr() != self.topology.entry
            || self.phases.len() != 11
        {
            return Err(());
        }
        if !self.valid_topology() {
            return Err(());
        }
        for (phase, block) in self.phases.iter().zip(blocks) {
            let Some(source_block) = self.origin.topology().block(block) else {
                return Err(());
            };
            if phase.block != block || phase.producers.as_ref() != source_block.instructions() {
                return Err(());
            }
        }
        let source_instructions = source
            .instructions()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let certified_instructions = self
            .instruction_dispositions
            .iter()
            .map(|(producer, _)| *producer)
            .collect::<BTreeSet<_>>();
        let transition_support = self
            .index
            .initializer_support_instructions
            .iter()
            .chain(self.index.update_support_instructions.iter())
            .chain(self.ascii.lowercase_support_instructions.iter())
            .chain(
                self.external_alias_policy
                    .address_support_instructions
                    .iter(),
            )
            .chain(self.frame.allocate_support.iter())
            .chain(self.frame.restore_support.iter())
            .chain(self.frame.address_support.iter())
            .chain(self.frame.return_target_support.iter())
            .copied()
            .collect::<BTreeSet<_>>();
        if source_instructions != certified_instructions
            || !transition_support.is_subset(&source_instructions)
            || transition_support.len()
                != self.index.initializer_support_instructions.len()
                    + self.index.update_support_instructions.len()
                    + self.ascii.lowercase_support_instructions.len()
                    + self
                        .external_alias_policy
                        .address_support_instructions
                        .len()
                    + self.frame.allocate_support.len()
                    + self.frame.restore_support.len()
                    + self.frame.address_support.len()
                    + self.frame.return_target_support.len()
            || self.instruction_dispositions.len() != certified_instructions.len()
            || !self
                .instruction_dispositions
                .windows(2)
                .all(|window| window[0].0 < window[1].0)
            || self.obligation_dispositions.len() != source.obligations().len()
            || !self
                .obligation_dispositions
                .windows(2)
                .all(|window| window[0].0 < window[1].0)
            || self
                .obligation_dispositions
                .iter()
                .map(|(obligation, _)| *obligation)
                .collect::<BTreeSet<_>>()
                != source.obligations().keys().copied().collect()
        {
            return Err(());
        }
        let instruction_classes = self
            .instruction_dispositions
            .iter()
            .copied()
            .collect::<BTreeMap<_, _>>();
        let proven_dead = self
            .proven_dead_producers
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if proven_dead.len() != self.proven_dead_producers.len()
            || !self
                .proven_dead_producers
                .windows(2)
                .all(|window| window[0] < window[1])
            || self
                .instruction_dispositions
                .iter()
                .any(|(producer, class)| {
                    let expected = proven_dead.contains(producer);
                    (*class == CertifiedFnvFoldO0DispositionClass::ProvenDead) != expected
                        || expected
                            && source
                                .instructions()
                                .get(producer)
                                .is_none_or(|instruction| {
                                    instruction.state != SemanticInstructionState::ProvenDead
                                        || !instruction.obligations.is_empty()
                                })
                })
            || self
                .obligation_dispositions
                .iter()
                .any(|(obligation, class)| {
                    *class == CertifiedFnvFoldO0DispositionClass::ProvenDead
                        || instruction_classes.get(&obligation.instruction) != Some(class)
                })
            || source.instructions().iter().any(|(producer, instruction)| {
                (instruction.state == SemanticInstructionState::ProvenDead)
                    != proven_dead.contains(producer)
            })
        {
            return Err(());
        }
        if self.accesses.len() != 22 || self.frame.homes.len() != 2 || self.frame.locals.len() != 3
        {
            return Err(());
        }
        let invariant_home_relays = BTreeSet::from([
            self.external_alias_policy
                .pointer_home
                .initializer_store
                .producer,
            self.external_alias_policy.pointer_home.reload.producer,
            self.length_home.initializer_store.producer,
            self.length_home.reload.producer,
        ]);
        let mut expected_frame_state = self
            .frame
            .homes
            .iter()
            .chain(self.frame.locals.iter())
            .flat_map(|slot| slot.accesses.iter().map(|access| access.producer))
            .chain([
                self.frame.allocate,
                self.frame.allocate_arithmetic,
                self.frame.restore,
                self.frame.restore_arithmetic,
            ])
            .chain(self.frame.allocate_support.iter().copied())
            .chain(self.frame.restore_support.iter().copied())
            .chain(self.frame.address_support.iter().copied())
            .chain(self.frame.return_target_support.iter().copied())
            .collect::<BTreeSet<_>>();
        expected_frame_state.retain(|producer| !invariant_home_relays.contains(producer));
        let actual_frame_state = self
            .instruction_dispositions
            .iter()
            .filter_map(|(producer, class)| {
                (*class == CertifiedFnvFoldO0DispositionClass::FrameState).then_some(*producer)
            })
            .collect::<BTreeSet<_>>();
        if expected_frame_state != actual_frame_state
            || !expected_frame_state.is_disjoint(&proven_dead)
            || expected_frame_state.contains(&self.return_instruction)
        {
            return Err(());
        }
        if !self.valid_home_relay(&self.external_alias_policy.pointer_home, 0)
            || !self.valid_home_relay(&self.length_home, 1)
            || self.length_home.value != self.loop_guard.lhs
            || self.external_alias_policy.external_read != self.index.buffer_access
            || self.external_alias_policy.external_object != self.index.buffer_object
            || self.external_alias_policy.index_load != self.index.address_load
            || self.external_alias_policy.address != self.index.buffer_address
            || self
                .accesses
                .iter()
                .find(|access| access.id == self.index.header_load)
                .is_none_or(|access| access.value != self.loop_guard.rhs)
            || self
                .accesses
                .iter()
                .find(|access| access.id == self.index.buffer_access)
                .is_none_or(|access| access.value != self.index.raw_byte)
            || !self.external_alias_policy.complete_frame_separation
            || !self.external_alias_policy.frame_address_escape_free
            || !self.external_alias_policy.source_external_byte_pointer
        {
            return Err(());
        }
        if self.frame.return_instruction != self.return_instruction
            || self.frame.return_target != self.return_target
            || self.returned_hash_access != self.hash.exit_load
            || self.returned_hash_version.object != self.hash.object
            || self
                .accesses
                .iter()
                .find(|access| access.id == self.returned_hash_access)
                .is_none_or(|access| {
                    access.is_write
                        || access.value != self.returned_value
                        || access.memory_uses.len() != 1
                        || access.memory_uses[0].version != self.returned_hash_version
                })
        {
            return Err(());
        }
        let ascii_accesses = BTreeSet::from([
            self.ascii.initial_store,
            self.ascii.first_load,
            self.ascii.second_load,
            self.ascii.lowercase_load,
            self.ascii.lowercase_store,
            self.ascii.merge_load,
        ]);
        let hash_accesses = BTreeSet::from([
            self.hash.initializer_store,
            self.hash.body_load,
            self.hash.xor_store,
            self.hash.xor_reload,
            self.hash.product_store,
            self.hash.exit_load,
        ]);
        let index_accesses = BTreeSet::from([
            self.index.initializer_store,
            self.index.header_load,
            self.index.address_load,
            self.index.latch_load,
            self.index.update_store,
        ]);
        if ascii_accesses.len() != 6
            || hash_accesses.len() != 6
            || index_accesses.len() != 5
            || !ascii_accesses.iter().all(|id| {
                self.accesses
                    .iter()
                    .any(|access| access.id == *id && access.object == self.ascii.object)
            })
            || !hash_accesses.iter().all(|id| {
                self.accesses
                    .iter()
                    .any(|access| access.id == *id && access.object == self.hash.object)
            })
            || !index_accesses.iter().all(|id| {
                self.accesses
                    .iter()
                    .any(|access| access.id == *id && access.object == self.index.object)
            })
            || !self
                .accesses
                .iter()
                .filter(|access| access.object == self.ascii.object)
                .all(|access| ascii_accesses.contains(&access.id))
            || !self
                .accesses
                .iter()
                .filter(|access| access.object == self.hash.object)
                .all(|access| hash_accesses.contains(&access.id))
            || !self
                .accesses
                .iter()
                .filter(|access| access.object == self.index.object)
                .all(|access| index_accesses.contains(&access.id))
            || self
                .accesses
                .iter()
                .find(|access| access.id == self.ascii.merge_load)
                .is_none_or(|access| access.value != self.ascii.selected_byte)
            || self.ascii.merge_phi.object != self.ascii.object
            || self.index.phi.object != self.index.object
            || self.hash.phi.object != self.hash.object
        {
            return Err(());
        }
        let frame_objects = self
            .frame
            .homes
            .iter()
            .chain(self.frame.locals.iter())
            .map(|slot| slot.object)
            .collect::<BTreeSet<_>>();
        if frame_objects.len() != 5
            || self
                .external_alias_policy
                .classified_frame_objects
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                != frame_objects
            || self.external_alias_policy.classified_frame_objects.len() != 5
            || frame_objects.contains(&self.external_alias_policy.external_object)
        {
            return Err(());
        }
        let coordinates = self
            .frame
            .homes
            .iter()
            .chain(self.frame.locals.iter())
            .map(|slot| {
                (
                    slot.declared_offset_from_allocated_sp,
                    slot.offset_from_entry_sp,
                    slot.width,
                )
            })
            .collect::<BTreeSet<_>>();
        if coordinates
            != BTreeSet::from([
                (15, -33, 1),
                (16, -32, 8),
                (24, -24, 8),
                (32, -16, 8),
                (40, -8, 8),
            ])
            || self
                .frame
                .homes
                .iter()
                .any(|slot| !matches!(slot.role, SourceStackSlotRole::ParameterHome { .. }))
            || self
                .frame
                .locals
                .iter()
                .any(|slot| slot.role != SourceStackSlotRole::Local)
        {
            return Err(());
        }
        if !self.conservative_alias_only_header_phis.is_empty() {
            return Err(());
        }
        let external_use = &self.external_alias_policy.external_memory_use;
        let Some(index_value) = self
            .accesses
            .iter()
            .find(|access| access.id == self.external_alias_policy.index_load)
            .map(|access| access.value)
        else {
            return Err(());
        };
        if external_use.location.object != self.external_alias_policy.external_object
            || external_use.location.size != 1
            || external_use.version
                != (CertifiedFnvFoldO0MemoryVersion {
                    object: self.external_alias_policy.external_object,
                    version: 0,
                })
            || !matches!(
                &external_use.location.address,
                CertifiedFnvFoldO0RelativeAddress::Affine { terms, offset }
                    if *offset == 0
                        && matches!(terms.as_ref(), [term]
                            if term.value == index_value && term.coefficient == 1)
            )
        {
            return Err(());
        }
        let Some(external_access) = self
            .accesses
            .iter()
            .find(|access| access.id == self.external_alias_policy.external_read)
        else {
            return Err(());
        };
        if external_access.object != self.external_alias_policy.external_object
            || external_access.is_write
            || external_access.width != 1
            || !external_access.memory_defs.is_empty()
            || external_access.memory_uses.as_ref()
                != std::slice::from_ref(&self.external_alias_policy.external_memory_use)
            || self
                .accesses
                .iter()
                .filter(|access| access.object == self.external_alias_policy.external_object)
                .count()
                != 1
        {
            return Err(());
        }
        let access_ids = self
            .accesses
            .iter()
            .map(|access| access.id)
            .collect::<BTreeSet<_>>();
        let frame_access_ids = self
            .frame
            .homes
            .iter()
            .chain(self.frame.locals.iter())
            .flat_map(|slot| slot.accesses.iter().copied())
            .collect::<BTreeSet<_>>();
        if access_ids.len() != 22
            || frame_access_ids.len() != 21
            || !frame_access_ids.is_subset(&access_ids)
            || frame_access_ids.contains(&self.external_alias_policy.external_read)
            || access_ids
                .difference(&frame_access_ids)
                .copied()
                .collect::<BTreeSet<_>>()
                != BTreeSet::from([self.external_alias_policy.external_read])
        {
            return Err(());
        }
        if [&self.index.phi, &self.ascii.merge_phi, &self.hash.phi]
            .into_iter()
            .any(|phi| {
                phi.disposition != CertifiedFnvFoldO0PhiDispositionClass::EffectiveLoopState
                    || phi.location.object != phi.object
            })
            || self.unused_provisional_phis.iter().any(|phi| {
                phi.disposition != CertifiedFnvFoldO0PhiDispositionClass::UnusedProvisional
                    || phi.location.address != CertifiedFnvFoldO0RelativeAddress::Exact(0)
                    || phi.location.object != phi.object
            })
        {
            return Err(());
        }
        Ok(())
    }

    fn obligation_surface_is_exact(&self, source: &SemanticObligationInventory) -> bool {
        let external_read = self.external_alias_policy.external_read.producer;
        source.instructions().values().all(|instruction| {
            fnv_fold_o0_instruction_state_is_supported(
                instruction.state,
                instruction.id,
                external_read,
            )
        }) && source
            .obligations()
            .values()
            .all(|obligation| fnv_fold_o0_obligation_is_supported(obligation.id, external_read))
    }

    fn valid_home_relay(&self, relay: &CertifiedFnvFoldO0ParameterHomeRelay, index: u32) -> bool {
        relay.parameter_index == index
            && relay.initializer_version.version != 0
            && relay.phi.disposition
                == CertifiedFnvFoldO0PhiDispositionClass::EffectiveInvariantHomeRelay
            && relay.phi.object == relay.initializer_version.object
            && relay.phi.output_version.object == relay.initializer_version.object
            && relay.phi.output_version.version != 0
            && relay.phi.output_version != relay.initializer_version
            && relay.phi.location.object == relay.phi.object
            && relay.phi.location.address == CertifiedFnvFoldO0RelativeAddress::Exact(0)
            && relay.phi.location.size == 8
            && relay.phi.inputs.len() == 2
            && relay.phi.inputs.iter().copied().collect::<BTreeSet<_>>()
                == BTreeSet::from([
                    (self.topology.entry, relay.initializer_version),
                    (self.topology.latch, relay.phi.output_version),
                ])
            && self.accesses.iter().any(|access| {
                access.id == relay.initializer_store
                    && access.is_write
                    && access.object == relay.initializer_version.object
                    && access.width == 8
                    && access.memory_defs.len() == 1
                    && access.memory_defs[0].previous_version.object
                        == relay.initializer_version.object
                    && access.memory_defs[0].previous_version.version == 0
                    && access.memory_defs[0].next_version == relay.initializer_version
            })
            && self.accesses.iter().any(|access| {
                access.id == relay.reload
                    && !access.is_write
                    && access.object == relay.initializer_version.object
                    && access.width == 8
                    && access.value == relay.value
                    && access.memory_uses.len() == 1
                    && access.memory_uses[0].version == relay.phi.output_version
            })
    }

    fn valid_topology(&self) -> bool {
        let branch = |from, to| {
            matches!(
                self.origin.topology().block(from).map(|block| block.terminator()),
                Some(CertifiedSourceTerminator::Branch { target }) if *target == to
            )
        };
        let conditional = |from, true_target, false_target| {
            matches!(
                self.origin.topology().block(from).map(|block| block.terminator()),
                Some(CertifiedSourceTerminator::ConditionalBranch {
                    true_target: actual_true,
                    false_target: actual_false,
                }) if *actual_true == true_target && *actual_false == false_target
            )
        };
        branch(self.topology.entry, self.topology.header)
            && conditional(
                self.topology.header,
                self.topology.exit,
                self.topology.first_forwarder,
            )
            && branch(
                self.topology.first_forwarder,
                self.topology.first_predicate_block,
            )
            && conditional(
                self.topology.first_predicate_block,
                self.topology.hash_block,
                self.topology.second_forwarder,
            )
            && branch(
                self.topology.second_forwarder,
                self.topology.second_predicate_block,
            )
            && conditional(
                self.topology.second_predicate_block,
                self.topology.hash_block,
                self.topology.lowercase_forwarder,
            )
            && branch(
                self.topology.lowercase_forwarder,
                self.topology.lowercase_block,
            )
            && branch(self.topology.lowercase_block, self.topology.hash_block)
            && branch(self.topology.hash_block, self.topology.latch)
            && branch(self.topology.latch, self.topology.header)
            && matches!(
                self.origin
                    .topology()
                    .block(self.topology.exit)
                    .map(|block| block.terminator()),
                Some(CertifiedSourceTerminator::Return)
            )
            && self.loop_guard.branch.block_addr == self.topology.header
            && self.loop_guard.kind == CertifiedFnvFoldO0CompareKind::LessEqual
            && self.loop_guard.true_target == self.topology.exit
            && self.loop_guard.false_target == self.topology.first_forwarder
            && self.ascii.first_predicate.branch.block_addr == self.topology.first_predicate_block
            && self.ascii.first_predicate.kind == CertifiedFnvFoldO0CompareKind::SignedLess
            && self.ascii.first_predicate.true_target == self.topology.hash_block
            && self.ascii.first_predicate.false_target == self.topology.second_forwarder
            && self.ascii.second_predicate.branch.block_addr == self.topology.second_predicate_block
            && self.ascii.second_predicate.kind == CertifiedFnvFoldO0CompareKind::SignedLess
            && self.ascii.second_predicate.true_target == self.topology.hash_block
            && self.ascii.second_predicate.false_target == self.topology.lowercase_forwarder
    }
}

fn fnv_fold_o0_instruction_state_is_supported(
    state: SemanticInstructionState,
    instruction: CanonicalInstructionId,
    external_read: CanonicalInstructionId,
) -> bool {
    state != SemanticInstructionState::UnsupportedUnknown || instruction == external_read
}

fn fnv_fold_o0_obligation_is_supported(
    obligation: SemanticObligationId,
    external_read: CanonicalInstructionId,
) -> bool {
    match obligation.kind {
        SemanticObligationKind::LiveValueProducer
        | SemanticObligationKind::ObservableMemoryRead
        | SemanticObligationKind::ObservableMemoryWrite
        | SemanticObligationKind::LoopCarriedState
        | SemanticObligationKind::LiveStateTransition
        | SemanticObligationKind::ControlPredicate
        | SemanticObligationKind::ControlTransfer
        | SemanticObligationKind::Return
        | SemanticObligationKind::ReturnValue => true,
        SemanticObligationKind::VolatileOrUnknownEffect => obligation.instruction == external_read,
        SemanticObligationKind::Call
        | SemanticObligationKind::CallArgument
        | SemanticObligationKind::CallResult
        | SemanticObligationKind::Trap
        | SemanticObligationKind::Atomicity
        | SemanticObligationKind::MemoryOrdering => false,
    }
}

fn home_relay(
    artifact: &SsaArtifact,
    fact: &CanonicalFnvFoldO0ParameterHomeRelayFact,
) -> Result<CertifiedFnvFoldO0ParameterHomeRelay, MachineBuildError> {
    Ok(CertifiedFnvFoldO0ParameterHomeRelay {
        parameter_index: fact.parameter_index,
        initializer_store: access_id(artifact, fact.initializer_store)?,
        initializer_version: fact.initializer_version.into(),
        phi: memory_phi(
            &fact.phi,
            CertifiedFnvFoldO0PhiDispositionClass::EffectiveInvariantHomeRelay,
        )
        .ok_or(MachineBuildError::TopologyMismatch)?,
        reload: access_id(artifact, fact.reload)?,
        value: fact.value,
    })
}

fn canonical(
    artifact: &SsaArtifact,
    inst: InstId,
) -> Result<CanonicalInstructionId, MachineBuildError> {
    artifact
        .obligations()
        .instruction_for_inst(inst)
        .map(|instruction| instruction.id)
        .ok_or(MachineBuildError::MissingInstructionDisposition(inst))
}

fn canonical_insts(
    artifact: &SsaArtifact,
    insts: &[InstId],
) -> Result<Box<[CanonicalInstructionId]>, MachineBuildError> {
    insts
        .iter()
        .map(|inst| canonical(artifact, *inst))
        .collect::<Result<Vec<_>, _>>()
        .map(Vec::into_boxed_slice)
}

fn access_id(
    artifact: &SsaArtifact,
    access: StructuredAccessId,
) -> Result<CertifiedFnvFoldO0AccessId, MachineBuildError> {
    Ok(CertifiedFnvFoldO0AccessId {
        producer: canonical(artifact, access.inst)?,
        ordinal: access.ordinal,
    })
}

fn access(
    artifact: &SsaArtifact,
    fact: &CanonicalFnvFoldO0AccessFact,
) -> Result<CertifiedFnvFoldO0Access, MachineBuildError> {
    Ok(CertifiedFnvFoldO0Access {
        id: access_id(artifact, fact.access)?,
        object: fact.object,
        address: fact.address,
        value: fact.value,
        is_write: fact.is_write,
        width: fact.width,
        memory_space: fact.memory_space.into(),
        memory_uses: fact
            .memory_uses
            .iter()
            .map(memory_use)
            .collect::<Option<Vec<_>>>()
            .ok_or(MachineBuildError::TopologyMismatch)?
            .into_boxed_slice(),
        memory_defs: fact
            .memory_defs
            .iter()
            .map(memory_def)
            .collect::<Option<Vec<_>>>()
            .ok_or(MachineBuildError::TopologyMismatch)?
            .into_boxed_slice(),
    })
}

fn slot(
    artifact: &SsaArtifact,
    fact: &r2ssa::CanonicalFnvFoldO0SlotFact,
) -> Result<CertifiedFnvFoldO0Slot, MachineBuildError> {
    Ok(CertifiedFnvFoldO0Slot {
        object: fact.object,
        declared_offset_from_allocated_sp: fact.declared_offset_from_allocated_sp,
        offset_from_entry_sp: fact.offset_from_entry_sp,
        width: fact.width,
        role: fact.role,
        accesses: fact
            .accesses
            .iter()
            .map(|access| access_id(artifact, *access))
            .collect::<Result<Vec<_>, _>>()?
            .into_boxed_slice(),
    })
}

fn predicate(
    artifact: &SsaArtifact,
    fact: &CanonicalFnvFoldO0PredicateFact,
) -> Result<CertifiedFnvFoldO0Predicate, MachineBuildError> {
    Ok(CertifiedFnvFoldO0Predicate {
        predicate: fact.predicate,
        condition: fact.condition,
        branch: canonical(artifact, fact.branch_inst)?,
        witnesses: canonical_insts(artifact, &fact.witness_insts)?,
        lhs: fact.lhs,
        rhs: fact.rhs,
        kind: fact.kind.into(),
        true_target: fact.true_target,
        false_target: fact.false_target,
    })
}

fn single_fact(
    artifact: &SsaArtifact,
) -> Result<Option<&CanonicalFnvFoldO0Fact>, MachineBuildError> {
    let facts = &artifact.structured().canonical_fnv_fold_o0;
    let mut values = facts.values();
    let Some(fact) = values.next() else {
        return Ok(None);
    };
    if values.next().is_some()
        || facts.get(&fact.topology.header) != Some(fact)
        || fact.schema_version != CANONICAL_FNV_FOLD_O0_FACT_SCHEMA_VERSION
        || !fact.validate_against(artifact)
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(Some(fact))
}

struct FnvFoldO0DispositionContext<'a> {
    external_read: CanonicalInstructionId,
    return_instruction: CanonicalInstructionId,
    invariant_home_relay_producers: &'a BTreeSet<CanonicalInstructionId>,
    frame_producers: &'a BTreeSet<CanonicalInstructionId>,
    forwarder_blocks: &'a BTreeSet<u64>,
}

impl FnvFoldO0DispositionContext<'_> {
    fn class_for(
        &self,
        producer: CanonicalInstructionId,
        proven_dead: bool,
        kind: Option<SemanticObligationKind>,
    ) -> CertifiedFnvFoldO0DispositionClass {
        if proven_dead {
            CertifiedFnvFoldO0DispositionClass::ProvenDead
        } else if producer == self.external_read {
            CertifiedFnvFoldO0DispositionClass::ExternalAliasSealing
        } else if self.invariant_home_relay_producers.contains(&producer) {
            CertifiedFnvFoldO0DispositionClass::InvariantHomeRelay
        } else if matches!(
            kind,
            Some(
                SemanticObligationKind::ControlPredicate | SemanticObligationKind::ControlTransfer
            )
        ) {
            if self.forwarder_blocks.contains(&producer.block_addr) {
                CertifiedFnvFoldO0DispositionClass::ForwarderControl
            } else {
                CertifiedFnvFoldO0DispositionClass::LoopControl
            }
        } else if producer == self.return_instruction {
            CertifiedFnvFoldO0DispositionClass::Return
        } else if self.frame_producers.contains(&producer) {
            CertifiedFnvFoldO0DispositionClass::FrameState
        } else {
            CertifiedFnvFoldO0DispositionClass::Semantics
        }
    }
}

pub(crate) fn validate_fnv_fold_o0_projection(
    artifact: &SsaArtifact,
    projection: &r2ssa::MachineProjection,
    witness: &CertifiedFnvFoldO0Function,
) -> Result<(), MachineBuildError> {
    let fact = single_fact(artifact)?.ok_or(MachineBuildError::TopologyMismatch)?;
    if projection.failures().is_empty()
        && projection.entity_for_output(fact.index.raw_byte).is_some()
        && witness.validate(artifact.obligations()).is_ok()
    {
        Ok(())
    } else {
        Err(MachineBuildError::TopologyMismatch)
    }
}

pub(crate) fn certified_fnv_fold_o0(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    projection: &r2ssa::MachineProjection,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
) -> Result<Option<CertifiedFnvFoldO0Function>, MachineBuildError> {
    let Some(fact) = single_fact(artifact)? else {
        return Ok(None);
    };
    if origin.source() != artifact.obligations()
        || origin.topology() != topology
        || !fact.external_read_policy.complete_frame_separation
        || !fact.external_read_policy.frame_address_escape_free
        || !fact.external_read_policy.source_external_byte_pointer
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    if !projection.failures().is_empty()
        || projection.entity_for_output(fact.index.raw_byte).is_none()
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let mismatch = || MachineBuildError::TopologyMismatch;
    let pointer_parameter = abi_parameters
        .get(&fact.abi.pointer_parameter.index)
        .filter(|parameter| {
            parameter.storage() == fact.abi.pointer_parameter.storage
                && parameter.value().is_some_and(|value| {
                    value.binding().value() == fact.abi.pointer_parameter.value
                })
        })
        .cloned()
        .ok_or_else(mismatch)?;
    let length_parameter = abi_parameters
        .get(&fact.abi.length_parameter.index)
        .filter(|parameter| {
            parameter.storage() == fact.abi.length_parameter.storage
                && parameter
                    .value()
                    .is_some_and(|value| value.binding().value() == fact.abi.length_parameter.value)
        })
        .cloned()
        .ok_or_else(mismatch)?;
    let certified_topology = CertifiedFnvFoldO0Topology {
        entry: fact.topology.entry,
        header: fact.topology.header,
        first_forwarder: fact.topology.first_forwarder,
        first_predicate_block: fact.topology.first_predicate_block,
        second_forwarder: fact.topology.second_forwarder,
        second_predicate_block: fact.topology.second_predicate_block,
        lowercase_forwarder: fact.topology.lowercase_forwarder,
        lowercase_block: fact.topology.lowercase_block,
        hash_block: fact.topology.hash_block,
        latch: fact.topology.latch,
        exit: fact.topology.exit,
    };
    let phases = certified_topology
        .ordered()
        .into_iter()
        .map(|block| {
            let source = topology.block(block).ok_or_else(mismatch)?;
            Ok(CertifiedFnvFoldO0Phase {
                block,
                producers: source.instructions().to_vec().into_boxed_slice(),
            })
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?
        .into_boxed_slice();
    let instruction_inventory = fact
        .memory
        .instruction_inventory
        .iter()
        .map(|inst| canonical(artifact, *inst))
        .collect::<Result<Vec<_>, _>>()?;
    let phase_inventory = phases
        .iter()
        .flat_map(|phase| phase.producers.iter().copied())
        .collect::<Vec<_>>();
    if instruction_inventory
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        != phase_inventory.iter().copied().collect()
        || instruction_inventory.len() != phase_inventory.len()
    {
        return Err(mismatch());
    }
    let mut proven_dead_producers = fact
        .memory
        .proven_dead_instructions
        .iter()
        .map(|inst| canonical(artifact, *inst))
        .collect::<Result<Vec<_>, _>>()?;
    proven_dead_producers.sort_unstable();
    if proven_dead_producers.is_empty()
        || proven_dead_producers
            .windows(2)
            .any(|window| window[0] == window[1])
    {
        return Err(mismatch());
    }
    let proven_dead = proven_dead_producers
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let accesses = fact
        .memory
        .accesses
        .iter()
        .map(|fact| access(artifact, fact))
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let unused_provisional_phis = fact
        .memory
        .unused_provisional_phis
        .iter()
        .map(|phi| {
            memory_phi(
                phi,
                CertifiedFnvFoldO0PhiDispositionClass::UnusedProvisional,
            )
            .ok_or_else(mismatch)
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let conservative_alias_only_header_phis = fact
        .memory
        .conservative_alias_only_header_phis
        .iter()
        .map(|phi| {
            memory_phi(
                phi,
                CertifiedFnvFoldO0PhiDispositionClass::ConservativeAliasConsumed,
            )
            .ok_or_else(mismatch)
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    let external_read = access_id(artifact, fact.external_read_policy.external_read)?;
    let return_instruction = canonical(artifact, fact.returned.return_inst)?;
    let mut frame_producers = fact
        .memory
        .accesses
        .iter()
        .filter(|access| access.object != fact.external_read_policy.external_object)
        .map(|access| canonical(artifact, access.access.inst))
        .collect::<Result<BTreeSet<_>, _>>()?;
    frame_producers.insert(canonical(artifact, fact.frame.allocate_inst)?);
    frame_producers.insert(canonical(artifact, fact.frame.allocate_arithmetic_inst)?);
    frame_producers.insert(canonical(artifact, fact.frame.restore_inst)?);
    frame_producers.insert(canonical(artifact, fact.frame.restore_arithmetic_inst)?);
    frame_producers.extend(canonical_insts(
        artifact,
        &fact.frame.allocate_support_insts,
    )?);
    frame_producers.extend(canonical_insts(
        artifact,
        &fact.frame.restore_support_insts,
    )?);
    frame_producers.extend(canonical_insts(
        artifact,
        &fact.frame.address_support_insts,
    )?);
    frame_producers.extend(canonical_insts(
        artifact,
        &fact.frame.return_target_support_insts,
    )?);
    let forwarder_blocks = BTreeSet::from([
        fact.topology.first_forwarder,
        fact.topology.second_forwarder,
        fact.topology.lowercase_forwarder,
    ]);
    let invariant_home_relay_producers = [
        fact.external_read_policy.pointer_home.initializer_store,
        fact.external_read_policy.pointer_home.reload,
        fact.length_home.initializer_store,
        fact.length_home.reload,
    ]
    .into_iter()
    .map(|access| canonical(artifact, access.inst))
    .collect::<Result<BTreeSet<_>, _>>()?;
    if invariant_home_relay_producers.len() != 4 {
        return Err(mismatch());
    }
    let disposition_context = FnvFoldO0DispositionContext {
        external_read: external_read.producer,
        return_instruction,
        invariant_home_relay_producers: &invariant_home_relay_producers,
        frame_producers: &frame_producers,
        forwarder_blocks: &forwarder_blocks,
    };
    let mut instruction_dispositions = artifact
        .obligations()
        .instructions()
        .iter()
        .map(|(producer, instruction)| {
            let kind = instruction
                .obligations
                .iter()
                .map(|obligation| obligation.kind)
                .find(|kind| {
                    matches!(
                        kind,
                        SemanticObligationKind::ControlPredicate
                            | SemanticObligationKind::ControlTransfer
                    )
                });
            (
                *producer,
                disposition_context.class_for(*producer, proven_dead.contains(producer), kind),
            )
        })
        .collect::<Vec<_>>();
    instruction_dispositions.sort_by_key(|(producer, _)| *producer);
    let mut obligation_dispositions = artifact
        .obligations()
        .obligations()
        .keys()
        .copied()
        .map(|obligation| {
            Ok((
                obligation,
                disposition_context.class_for(obligation.instruction, false, Some(obligation.kind)),
            ))
        })
        .collect::<Result<Vec<_>, MachineBuildError>>()?;
    obligation_dispositions.sort_by_key(|(obligation, _)| *obligation);
    let witness = CertifiedFnvFoldO0Function {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_FNV_FOLD_O0_CONTRACT_VERSION,
        origin: origin.clone(),
        revision_identity: fact.abi.revision_identity.clone(),
        loop_id: fact.loop_id,
        topology: certified_topology,
        phases,
        pointer_parameter,
        length_parameter,
        return_storage: fact.abi.return_storage,
        pointer_logical: fact.abi.pointer_logical,
        length_logical: fact.abi.length_logical,
        return_logical: fact.abi.return_logical,
        memory_space: fact.abi.memory_space.into(),
        memory_address_bits: fact.abi.memory_address_bits,
        memory_word_size_bytes: fact.abi.memory_word_size_bytes,
        memory_endianness: fact.abi.memory_endianness,
        frame: CertifiedFnvFoldO0Frame {
            stack_storage: fact.frame.stack_storage,
            link_register_storage: fact.frame.link_register_storage,
            entry_sp: fact.frame.entry_sp,
            allocated_sp: fact.frame.allocated_sp,
            allocate: canonical(artifact, fact.frame.allocate_inst)?,
            allocate_arithmetic: canonical(artifact, fact.frame.allocate_arithmetic_inst)?,
            allocate_support: canonical_insts(artifact, &fact.frame.allocate_support_insts)?,
            restored_sp: fact.frame.restored_sp,
            restore: canonical(artifact, fact.frame.restore_inst)?,
            restore_arithmetic: canonical(artifact, fact.frame.restore_arithmetic_inst)?,
            restore_support: canonical_insts(artifact, &fact.frame.restore_support_insts)?,
            address_support: canonical_insts(artifact, &fact.frame.address_support_insts)?,
            return_address: fact.frame.return_address,
            return_target: fact.frame.return_target,
            return_target_support: canonical_insts(
                artifact,
                &fact.frame.return_target_support_insts,
            )?,
            return_instruction,
            homes: fact
                .frame
                .homes
                .iter()
                .map(|fact| slot(artifact, fact))
                .collect::<Result<Vec<_>, _>>()?
                .into_boxed_slice(),
            locals: fact
                .frame
                .locals
                .iter()
                .map(|fact| slot(artifact, fact))
                .collect::<Result<Vec<_>, _>>()?
                .into_boxed_slice(),
        },
        accesses,
        unused_provisional_phis,
        conservative_alias_only_header_phis,
        loop_guard: predicate(artifact, &fact.loop_guard)?,
        index: CertifiedFnvFoldO0Index {
            object: fact.index.object,
            initializer_store: access_id(artifact, fact.index.initializer_store)?,
            initializer_support_instructions: canonical_insts(
                artifact,
                &fact.index.initializer_support_insts,
            )?,
            initializer_version: fact.index.initializer_version.into(),
            phi: memory_phi(
                &fact.index.phi,
                CertifiedFnvFoldO0PhiDispositionClass::EffectiveLoopState,
            )
            .ok_or_else(mismatch)?,
            header_load: access_id(artifact, fact.index.header_load)?,
            address_load: access_id(artifact, fact.index.address_load)?,
            latch_load: access_id(artifact, fact.index.latch_load)?,
            update: fact.index.update,
            update_instruction: canonical(artifact, fact.index.update_inst)?,
            update_support_instructions: canonical_insts(
                artifact,
                &fact.index.update_support_insts,
            )?,
            update_store: access_id(artifact, fact.index.update_store)?,
            update_version: fact.index.update_version.into(),
            buffer_address: fact.index.buffer_address,
            buffer_access: access_id(artifact, fact.index.buffer_access)?,
            buffer_object: fact.index.buffer_object,
            raw_byte: fact.index.raw_byte,
        },
        length_home: home_relay(artifact, &fact.length_home)?,
        external_alias_policy: CertifiedFnvFoldO0ExternalAliasPolicy {
            complete_frame_separation: fact.external_read_policy.complete_frame_separation,
            frame_address_escape_free: fact.external_read_policy.frame_address_escape_free,
            source_external_byte_pointer: fact.external_read_policy.source_external_byte_pointer,
            external_object: fact.external_read_policy.external_object,
            external_read,
            pointer_home: home_relay(artifact, &fact.external_read_policy.pointer_home)?,
            index_load: access_id(artifact, fact.external_read_policy.index_load)?,
            address: fact.external_read_policy.address,
            address_instruction: canonical(artifact, fact.external_read_policy.address_inst)?,
            address_support_instructions: canonical_insts(
                artifact,
                &fact.external_read_policy.address_support_insts,
            )?,
            classified_frame_objects: fact.external_read_policy.classified_frame_objects.clone(),
            external_memory_use: memory_use(&fact.external_read_policy.external_memory_use)
                .ok_or_else(mismatch)?,
        },
        ascii: CertifiedFnvFoldO0Ascii {
            object: fact.ascii.object,
            initial_store: access_id(artifact, fact.ascii.initial_store)?,
            initial_version: fact.ascii.initial_version.into(),
            first_load: access_id(artifact, fact.ascii.first_load)?,
            first_predicate: predicate(artifact, &fact.ascii.first_predicate)?,
            second_load: access_id(artifact, fact.ascii.second_load)?,
            second_predicate: predicate(artifact, &fact.ascii.second_predicate)?,
            lowercase_load: access_id(artifact, fact.ascii.lowercase_load)?,
            lowercase: fact.ascii.lowercase,
            lowercase_instruction: canonical(artifact, fact.ascii.lowercase_inst)?,
            lowercase_support_instructions: canonical_insts(
                artifact,
                &fact.ascii.lowercase_support_insts,
            )?,
            lowercase_store: access_id(artifact, fact.ascii.lowercase_store)?,
            lowercase_version: fact.ascii.lowercase_version.into(),
            merge_phi: memory_phi(
                &fact.ascii.merge_phi,
                CertifiedFnvFoldO0PhiDispositionClass::EffectiveLoopState,
            )
            .ok_or_else(mismatch)?,
            merge_load: access_id(artifact, fact.ascii.merge_load)?,
            selected_byte: fact.ascii.selected_byte,
        },
        hash: CertifiedFnvFoldO0Hash {
            object: fact.hash.object,
            offset_basis: fact.hash.offset_basis,
            initializer: fact.hash.initializer,
            initializer_witnesses: canonical_insts(artifact, &fact.hash.initializer_witness_insts)?,
            initializer_store: access_id(artifact, fact.hash.initializer_store)?,
            initializer_version: fact.hash.initializer_version.into(),
            phi: memory_phi(
                &fact.hash.phi,
                CertifiedFnvFoldO0PhiDispositionClass::EffectiveLoopState,
            )
            .ok_or_else(mismatch)?,
            body_load: access_id(artifact, fact.hash.body_load)?,
            selected64: fact.hash.selected64,
            selected64_instruction: canonical(artifact, fact.hash.selected64_inst)?,
            xor: fact.hash.xor,
            xor_instruction: canonical(artifact, fact.hash.xor_inst)?,
            xor_store: access_id(artifact, fact.hash.xor_store)?,
            xor_version: fact.hash.xor_version.into(),
            xor_reload: access_id(artifact, fact.hash.xor_reload)?,
            prime: fact.hash.prime,
            prime_value: fact.hash.prime_value,
            prime_witnesses: canonical_insts(artifact, &fact.hash.prime_witness_insts)?,
            product: fact.hash.product,
            multiply_instruction: canonical(artifact, fact.hash.multiply_inst)?,
            product_store: access_id(artifact, fact.hash.product_store)?,
            product_version: fact.hash.product_version.into(),
            exit_load: access_id(artifact, fact.hash.exit_load)?,
        },
        returned_hash_access: access_id(artifact, fact.returned.hash_access)?,
        returned_hash_version: fact.returned.hash_version.into(),
        returned_value: fact.returned.value,
        return_instruction,
        return_target: fact.returned.return_target,
        proven_dead_producers: proven_dead_producers.into_boxed_slice(),
        instruction_dispositions: instruction_dispositions.into_boxed_slice(),
        obligation_dispositions: obligation_dispositions.into_boxed_slice(),
    };
    witness
        .validate(artifact.obligations())
        .map_err(|_| mismatch())?;
    Ok(Some(witness))
}

pub fn certify_fnv_fold_o0_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    witness: &CertifiedFnvFoldO0Function,
) -> Result<CertifiedRenderPermit, RenderAuthorizationError> {
    if origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || !origin.matches_retained_source(origin.source(), origin.topology())
        || witness.origin() != origin
        || witness.validate(origin.source()).is_err()
    {
        return Err(RenderAuthorizationError::InvalidOrigin);
    }
    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for mapping in &mappings {
        if !seen.insert(mapping.obligation()) {
            return Err(RenderAuthorizationError::DuplicateMapping(
                mapping.obligation(),
            ));
        }
        let [effect] = ledger.effects(mapping.obligation()) else {
            return Err(RenderAuthorizationError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || !effect.is_exact_fnv_fold_o0(witness, mapping.obligation())
        {
            return Err(RenderAuthorizationError::InvalidRegionDisposition(
                mapping.obligation(),
            ));
        }
    }
    if seen != origin.source().obligations().keys().copied().collect()
        || mappings.len() != origin.source().obligations().len()
    {
        return Err(RenderAuthorizationError::IncompleteLedger);
    }
    Ok(CertifiedRenderPermit::new_fnv_fold_o0(
        origin.clone(),
        mappings.into_boxed_slice(),
    ))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use r2il::{ArchSpec, R2ILOp, SpaceId};
    use r2sleigh_lift::{Disassembler, build_arch_spec};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind,
        SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
        SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeKind, SsaArtifact,
        StackAddressBase,
    };
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::{CertifiedMachineFunction, CertifiedTypedRegionKind, EffectDisposition};

    const REAL_FNV_SOURCE_SHA256: &str =
        "6524278ba4cd32a72dcf9cbcc385275999a50c3449d0e97035736891bcddff09";
    const REAL_FNV_O0_FUNCTION_SHA256: &str =
        "36af3c68ac0783e3d38125798a0644860fde98454361b46ebc72bd166b96f697";
    const REAL_FNV_O0_BINARY_SHA256: &str =
        "295868f8dab7d5d3e3304b17bce6a19f8948cca620068492f081c658146fe3bb";
    const REAL_FNV_O0_BINARY_PATH: &str = "tests/r2r/bins/r2sleigh_manual_limits_O0";
    const REAL_FNV_O0_COMPILER_COMMAND: &str = "gcc -O0 -g -fno-inline -fno-omit-frame-pointer -fno-stack-protector -no-pie -o tests/r2r/bins/r2sleigh_manual_limits_O0 tests/gold/manual_limits.c";
    const REAL_FNV_O0_BASE: u64 = 0x1_0000_075c;
    const REAL_FNV_O0_HEADER: u64 = 0x1_0000_0784;
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

    fn assert_real_provenance() {
        let provenance = format!(
            "binary={REAL_FNV_O0_BINARY_PATH} binary_sha256={REAL_FNV_O0_BINARY_SHA256} command={REAL_FNV_O0_COMPILER_COMMAND}"
        );
        assert_eq!(
            sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
            REAL_FNV_SOURCE_SHA256,
            "source provenance changed: {provenance}"
        );
        assert_eq!(
            sha256_hex(include_bytes!(
                "../../../tests/r2r/bins/r2sleigh_manual_limits_O0"
            )),
            REAL_FNV_O0_BINARY_SHA256,
            "binary provenance changed: {provenance}"
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

    fn artifact() -> SsaArtifact {
        assert_real_provenance();
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
                assert_eq!(
                    block.size as usize,
                    bytes.len(),
                    "real block must be fully consumed"
                );
                address += bytes.len() as u64;
                block
            })
            .collect::<Vec<_>>();
        let memory_spaces = blocks
            .iter()
            .flat_map(|block| &block.ops)
            .filter_map(|op| match op {
                R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            memory_spaces.len(),
            22,
            "pinned real memory operation count"
        );
        assert!(
            memory_spaces.iter().all(|space| *space == SpaceId::Ram),
            "real ARM64 LOAD/STORE spaces must translate to Ram: {memory_spaces:?}"
        );
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), real_interface(&arch))
            .expect("prepared real ARM64 O0 FNV artifact")
    }

    fn machine() -> CertifiedMachineFunction {
        CertifiedMachineFunction::from_artifact(&artifact()).expect("real O0 FNV certificate")
    }

    fn disposition(
        producer: CanonicalInstructionId,
        class: CertifiedFnvFoldO0DispositionClass,
    ) -> EffectDisposition {
        match class {
            CertifiedFnvFoldO0DispositionClass::ProvenDead => {
                panic!("producer-only O0 disposition cannot map an obligation")
            }
            CertifiedFnvFoldO0DispositionClass::FrameState => {
                EffectDisposition::AbsorbedIntoFnvFoldO0FrameState { producer }
            }
            CertifiedFnvFoldO0DispositionClass::InvariantHomeRelay => {
                EffectDisposition::AbsorbedIntoFnvFoldO0InvariantHomeRelay { producer }
            }
            CertifiedFnvFoldO0DispositionClass::ExternalAliasSealing => {
                EffectDisposition::AbsorbedIntoFnvFoldO0ExternalAlias { producer }
            }
            CertifiedFnvFoldO0DispositionClass::ForwarderControl => {
                EffectDisposition::AbsorbedIntoFnvFoldO0Forwarder { producer }
            }
            CertifiedFnvFoldO0DispositionClass::LoopControl => {
                EffectDisposition::AbsorbedIntoFnvFoldO0LoopControl { producer }
            }
            CertifiedFnvFoldO0DispositionClass::Semantics => {
                EffectDisposition::AbsorbedIntoFnvFoldO0Semantics { producer }
            }
            CertifiedFnvFoldO0DispositionClass::Return => {
                EffectDisposition::AbsorbedIntoFnvFoldO0Return { producer }
            }
        }
    }

    fn mappings(witness: &CertifiedFnvFoldO0Function) -> Vec<TypedRegionMapping> {
        witness
            .obligation_dispositions()
            .iter()
            .map(|(obligation, class)| {
                TypedRegionMapping::new(*obligation, disposition(obligation.instruction, *class))
            })
            .collect()
    }

    fn assert_corrupt(machine: &CertifiedMachineFunction, witness: CertifiedFnvFoldO0Function) {
        assert!(witness.validate(machine.source()).is_err());
        assert!(
            certify_fnv_fold_o0_region(
                machine.origin(),
                machine.ledger(),
                mappings(&witness),
                &witness,
            )
            .is_err()
        );
    }

    fn assert_compact_reference_corruption_rejected(
        mutate: impl FnOnce(&mut crate::CertifiedFnvFoldO0EvidenceRef),
    ) {
        let mut machine = machine();
        let witness = machine.fnv_fold_o0().expect("real O0 FNV witness");
        let mappings = mappings(witness);
        let obligation = witness.obligation_dispositions()[0].0;
        let [effect] = machine
            .certification
            .ledger
            .effects
            .get_mut(&obligation)
            .expect("O0 ledger effect")
            .as_mut_slice()
        else {
            panic!("single O0 ledger effect")
        };
        let crate::DispositionEvidence::FnvFoldO0(reference) = &mut effect.evidence else {
            panic!("compact O0 evidence")
        };
        mutate(reference);
        assert!(!machine.finish().invalid().is_empty());
        assert!(
            certify_fnv_fold_o0_region(
                machine.origin(),
                machine.ledger(),
                mappings,
                machine.fnv_fold_o0().expect("real O0 FNV witness"),
            )
            .is_err()
        );
    }

    #[test]
    fn real_o0_fnv_certificate_closes_the_whole_ledger() {
        let machine = machine();
        let witness = machine.fnv_fold_o0().expect("real O0 FNV witness");
        assert_eq!(witness.topology().header(), REAL_FNV_O0_HEADER);
        assert_eq!(witness.accesses().len(), 22);
        assert_eq!(
            witness
                .external_alias_policy()
                .pointer_home()
                .phi()
                .disposition(),
            CertifiedFnvFoldO0PhiDispositionClass::EffectiveInvariantHomeRelay
        );
        assert_eq!(
            witness.length_home().phi().disposition(),
            CertifiedFnvFoldO0PhiDispositionClass::EffectiveInvariantHomeRelay
        );
        let report = machine.finish();
        assert!(report.has_exactly_one_disposition_per_source());
        assert!(report.residualized().is_empty());
        assert!(report.refused().is_empty());
        let permit = certify_fnv_fold_o0_region(
            machine.origin(),
            machine.ledger(),
            mappings(witness),
            witness,
        )
        .expect("real opaque O0 FNV permit");
        assert!(permit.authorizes_certified_c());
        assert_eq!(
            permit.region_kind(),
            CertifiedTypedRegionKind::FnvFoldO0Function
        );
    }

    #[test]
    fn real_certificate_surface_refuses_trap_and_unrelated_unsupported_effects() {
        let machine = machine();
        let witness = machine.fnv_fold_o0().expect("real O0 FNV witness");
        assert!(witness.obligation_surface_is_exact(machine.source()));

        let external_read = witness.external_alias_policy().external_read().producer();
        let unrelated = witness.return_instruction();
        let obligation = |instruction, kind| SemanticObligationId {
            instruction,
            kind,
            component: r2ssa::SemanticObligationComponent::Whole,
        };
        assert!(fnv_fold_o0_instruction_state_is_supported(
            SemanticInstructionState::UnsupportedUnknown,
            external_read,
            external_read,
        ));
        assert!(!fnv_fold_o0_instruction_state_is_supported(
            SemanticInstructionState::UnsupportedUnknown,
            unrelated,
            external_read,
        ));
        assert!(fnv_fold_o0_obligation_is_supported(
            obligation(
                external_read,
                SemanticObligationKind::VolatileOrUnknownEffect,
            ),
            external_read,
        ));
        assert!(!fnv_fold_o0_obligation_is_supported(
            obligation(unrelated, SemanticObligationKind::VolatileOrUnknownEffect),
            external_read,
        ));
        assert!(!fnv_fold_o0_obligation_is_supported(
            obligation(unrelated, SemanticObligationKind::Trap),
            external_read,
        ));
    }

    #[test]
    fn real_compact_ledger_evidence_is_exact_and_does_not_duplicate_the_witness() {
        #[derive(serde::Serialize)]
        struct SerializedOrigin<'a> {
            graph_snapshot: &'a [u8],
        }

        #[derive(serde::Serialize)]
        struct SerializedO0Retention<'a> {
            machine_origin: SerializedOrigin<'a>,
            witness_origin: SerializedOrigin<'a>,
            effects: Vec<crate::CertifiedFnvFoldO0EvidenceRef>,
        }

        let machine = machine();
        let witness = machine.fnv_fold_o0().expect("real O0 FNV witness");
        let effects = witness
            .obligation_dispositions()
            .iter()
            .map(|(obligation, _)| {
                let [effect] = machine.ledger().effects(*obligation) else {
                    panic!("single O0 ledger effect")
                };
                let crate::DispositionEvidence::FnvFoldO0(reference) = effect.evidence else {
                    panic!("compact O0 evidence")
                };
                reference
            })
            .collect::<Vec<_>>();
        let retention = SerializedO0Retention {
            machine_origin: SerializedOrigin {
                graph_snapshot: &machine.origin().graph_snapshot,
            },
            witness_origin: SerializedOrigin {
                graph_snapshot: &witness.origin().graph_snapshot,
            },
            effects,
        };
        let serialized_retention =
            serde_json::to_string(&retention).expect("serialized O0 retention shape");
        let serialized_machine = postcard::to_stdvec(&machine).expect("serialized machine");
        let serialized_ledger = postcard::to_stdvec(machine.ledger()).expect("serialized ledger");
        let serialized_witness = postcard::to_stdvec(witness).expect("serialized witness");

        assert_eq!(
            serialized_retention.matches("\"graph_snapshot\"").count(),
            2
        );
        assert!(serialized_ledger.len() < serialized_witness.len() * 2);
        assert!(serialized_machine.len() < serialized_witness.len() * 4);
        assert!(
            std::mem::size_of::<crate::CertifiedFnvFoldO0EvidenceRef>()
                <= 2 * std::mem::size_of::<u32>()
        );
        assert!(
            witness
                .obligation_dispositions()
                .iter()
                .all(|(obligation, class)| {
                    let [effect] = machine.ledger().effects(*obligation) else {
                        return false;
                    };
                    matches!(
                        effect.evidence,
                        crate::DispositionEvidence::FnvFoldO0(reference)
                            if reference.proof_slot == crate::CERTIFIED_FNV_FOLD_O0_PROOF_SLOT
                                && reference.class == *class
                    )
                })
        );
    }

    #[test]
    fn real_compact_ledger_evidence_rejects_slot_and_class_corruption() {
        assert_compact_reference_corruption_rejected(|reference| {
            reference.proof_slot = reference.proof_slot.wrapping_add(1);
        });
        assert_compact_reference_corruption_rejected(|reference| {
            reference.class = CertifiedFnvFoldO0DispositionClass::ProvenDead;
        });
    }

    #[test]
    fn real_certificate_rejects_loss_duplication_order_and_disposition_corruption() {
        let machine = machine();
        let original = machine.fnv_fold_o0().expect("witness").clone();

        let mut loss = original.clone();
        loss.obligation_dispositions =
            loss.obligation_dispositions[..loss.obligation_dispositions.len() - 1].into();
        assert_corrupt(&machine, loss);

        let mut duplicate = original.clone();
        let mut obligations = duplicate.obligation_dispositions.to_vec();
        obligations.push(obligations[0]);
        obligations.sort_by_key(|entry| entry.0);
        duplicate.obligation_dispositions = obligations.into_boxed_slice();
        assert_corrupt(&machine, duplicate);

        let mut order = original.clone();
        order.obligation_dispositions.swap(0, 1);
        assert_corrupt(&machine, order);

        let mut wrong_class = original;
        wrong_class.obligation_dispositions[0].1 = CertifiedFnvFoldO0DispositionClass::Return;
        assert_corrupt(&machine, wrong_class);
    }

    #[test]
    fn real_certificate_rejects_provenance_topology_constants_abi_and_return_corruption() {
        let machine = machine();
        let original = machine.fnv_fold_o0().expect("witness").clone();

        let mut provenance = original.clone();
        provenance.revision_identity[0] ^= 1;
        assert_corrupt(&machine, provenance);

        let mut topology = original.clone();
        std::mem::swap(
            &mut topology.topology.hash_block,
            &mut topology.topology.latch,
        );
        assert_corrupt(&machine, topology);

        let mut constant = original.clone();
        constant.hash.prime_value ^= 1;
        assert_corrupt(&machine, constant);

        let mut abi = original.clone();
        abi.memory_address_bits = 32;
        assert_corrupt(&machine, abi);

        let mut returned = original;
        returned.returned_hash_version.version ^= 1;
        assert_corrupt(&machine, returned);
    }

    #[test]
    fn real_certificate_rejects_relay_phi_memory_and_predicate_corruption() {
        let machine = machine();
        let original = machine.fnv_fold_o0().expect("witness").clone();

        let mut relay = original.clone();
        relay.length_home.phi.inputs[1].1 = relay.length_home.initializer_version;
        assert_corrupt(&machine, relay);

        let mut phi_class = original.clone();
        phi_class.external_alias_policy.pointer_home.phi.disposition =
            CertifiedFnvFoldO0PhiDispositionClass::UnusedProvisional;
        assert_corrupt(&machine, phi_class);

        let mut access = original.clone();
        access.accesses = access.accesses[1..].into();
        assert_corrupt(&machine, access);

        let mut predicate = original;
        let hash_block = predicate.topology.hash_block;
        predicate.ascii.second_predicate.false_target = hash_block;
        assert_corrupt(&machine, predicate);
    }

    #[test]
    fn real_certified_inventories_are_exact_and_non_overlapping() {
        let artifact = artifact();
        let machine =
            CertifiedMachineFunction::from_artifact(&artifact).expect("real O0 FNV certificate");
        let witness = machine.fnv_fold_o0().expect("witness");
        let instruction_ids = witness
            .instruction_dispositions()
            .iter()
            .map(|entry| entry.0)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            instruction_ids,
            machine.source().instructions().keys().copied().collect()
        );
        let alias = witness
            .conservative_alias_only_header_phis()
            .iter()
            .map(CertifiedFnvFoldO0MemoryPhi::output_version)
            .collect::<BTreeSet<_>>();
        let unused = witness
            .unused_provisional_phis()
            .iter()
            .map(CertifiedFnvFoldO0MemoryPhi::output_version)
            .collect::<BTreeSet<_>>();
        assert!(alias.is_disjoint(&unused));

        let proven_dead = witness
            .instruction_dispositions()
            .iter()
            .filter_map(|(producer, class)| {
                (*class == CertifiedFnvFoldO0DispositionClass::ProvenDead).then_some(*producer)
            })
            .collect::<BTreeSet<_>>();
        let expected_proven_dead = artifact
            .structured()
            .canonical_fnv_fold_o0
            .get(&REAL_FNV_O0_HEADER)
            .expect("real O0 fact")
            .memory
            .proven_dead_instructions
            .iter()
            .map(|inst| canonical(&artifact, *inst).expect("canonical proven-dead instruction"))
            .collect::<BTreeSet<_>>();
        assert_eq!(proven_dead, expected_proven_dead);
        assert!(!proven_dead.is_empty());
        assert!(proven_dead.iter().all(|producer| {
            let instruction = machine
                .source()
                .instructions()
                .get(producer)
                .expect("dead structural producer");
            instruction.state == SemanticInstructionState::ProvenDead
                && instruction.obligations.is_empty()
                && artifact.graph().inst(instruction.inst).is_some()
        }));
        assert!(proven_dead.iter().any(|producer| {
            let instruction = &machine.source().instructions()[producer];
            artifact
                .graph()
                .inst(instruction.inst)
                .is_some_and(|inst| matches!(inst.payload, r2ssa::InstPayload::Phi { .. }))
        }));
        assert!(proven_dead.iter().any(|producer| {
            let instruction = &machine.source().instructions()[producer];
            artifact
                .graph()
                .inst(instruction.inst)
                .is_some_and(|inst| !matches!(inst.payload, r2ssa::InstPayload::Phi { .. }))
        }));
        assert!(
            witness
                .obligation_dispositions()
                .iter()
                .all(|(_, class)| *class != CertifiedFnvFoldO0DispositionClass::ProvenDead)
        );
    }
}
