//! Canonical semantic sidecar facts for prepared SSA functions.
//!
//! These facts keep object, memory, predicate, and call-site provenance in
//! `r2ssa` so downstream crates stop reconstructing them independently.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use r2il::SpaceId;
use serde::{Deserialize, Serialize};

use crate::address::{AddressProvenanceFacts, collect_address_provenance};
use crate::assumption::{AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue};
use crate::cfg::BlockTerminator;
use crate::function::{DecompilePrepFacts, SSAFunction, StackAddressBase, StackAddressRoot};
use crate::graph::{InstId, InstPayload, SsaGraph, UseSite, ValueId};
use crate::machine_context::{
    MachineRegisterGeometryState, SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION,
    SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCallResult, SourceCallSiteIdentity, SourceCarrierKind,
    SourceFunctionReturn, SourceLogicalValue, SourceMachineContext, SourceTypeKind,
};
use crate::obligation::SemanticObligationInventory;
use crate::op::SSAOp;
use crate::span::StorageSpans;
use crate::var::{CanonicalStorageId, CanonicalStorageSpace, SSAVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ObjectId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PredicateId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ControlDomainId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CallSiteId(pub u32);

/// Stable identity for a semantic entity inside one prepared SSA artifact.
///
/// These IDs are derived only from canonical SSA/object identities and ABI
/// parameter slots. They deliberately do not depend on rendered names, AST
/// positions, or traversal order in downstream consumers. Re-preparing the
/// same canonical [`SSAFunction`] therefore produces the same semantic IDs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticId {
    Expression(ValueId),
    Parameter(u32),
    StackSlot(ObjectId),
    LoopCarrier(ValueId),
    MemoryAccess(StructuredAccessId),
    Return(InstId),
    Call(CallSiteId),
    Predicate(PredicateId),
    ControlDomain(ControlDomainId),
    Effect(InstId),
}

impl SemanticId {
    pub const fn expression(value: ValueId) -> Self {
        Self::Expression(value)
    }

    pub fn parameter(slot: usize) -> Option<Self> {
        u32::try_from(slot).ok().map(Self::Parameter)
    }

    pub const fn stack_slot(object: ObjectId) -> Self {
        Self::StackSlot(object)
    }

    pub const fn loop_carrier(phi: ValueId) -> Self {
        Self::LoopCarrier(phi)
    }

    pub const fn memory_access(access: StructuredAccessId) -> Self {
        Self::MemoryAccess(access)
    }

    pub const fn return_value(at: InstId) -> Self {
        Self::Return(at)
    }

    pub const fn call(call_site: CallSiteId) -> Self {
        Self::Call(call_site)
    }

    pub const fn predicate(predicate: PredicateId) -> Self {
        Self::Predicate(predicate)
    }

    pub const fn control_domain(domain: ControlDomainId) -> Self {
        Self::ControlDomain(domain)
    }

    pub const fn effect(at: InstId) -> Self {
        Self::Effect(at)
    }
}

impl std::fmt::Display for SemanticId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expression(value) => write!(f, "expr:{}", value.0),
            Self::Parameter(slot) => write!(f, "param:{slot}"),
            Self::StackSlot(object) => write!(f, "stack:{}", object.0),
            Self::LoopCarrier(phi) => write!(f, "loop-carrier:{}", phi.0),
            Self::MemoryAccess(access) => {
                write!(f, "memory:{}:{}", access.inst.0, access.ordinal)
            }
            Self::Return(at) => write!(f, "return:{}", at.0),
            Self::Call(call_site) => write!(f, "call:{}", call_site.0),
            Self::Predicate(predicate) => write!(f, "predicate:{}", predicate.0),
            Self::ControlDomain(domain) => write!(f, "domain:{}", domain.0),
            Self::Effect(at) => write!(f, "effect:{}", at.0),
        }
    }
}

fn memory_space_order(space: SpaceId) -> (u8, u32) {
    match space {
        SpaceId::Ram => (0, 0),
        SpaceId::Register => (1, 0),
        SpaceId::Unique => (2, 0),
        SpaceId::Const => (3, 0),
        SpaceId::Custom(id) => (4, id),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectSpaceId(pub SpaceId);

impl Ord for ObjectSpaceId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        memory_space_order(self.0).cmp(&memory_space_order(other.0))
    }
}

impl PartialOrd for ObjectSpaceId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemoryObjectKey {
    pub value: ValueId,
    pub space: SpaceId,
}

impl Ord for MemoryObjectKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value
            .cmp(&other.value)
            .then_with(|| memory_space_order(self.space).cmp(&memory_space_order(other.space)))
    }
}

impl PartialOrd for MemoryObjectKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StackObjectKey {
    pub root: StackAddressRoot,
    pub space: SpaceId,
}

impl Ord for StackObjectKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.root
            .cmp(&other.root)
            .then_with(|| memory_space_order(self.space).cmp(&memory_space_order(other.space)))
    }
}

impl PartialOrd for StackObjectKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParameterObjectKey {
    pub index: usize,
    pub space: SpaceId,
}

impl Ord for ParameterObjectKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index
            .cmp(&other.index)
            .then_with(|| memory_space_order(self.space).cmp(&memory_space_order(other.space)))
    }
}

impl PartialOrd for ParameterObjectKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GlobalObjectKey {
    pub space: SpaceId,
    pub address: u64,
}

impl Ord for GlobalObjectKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        memory_space_order(self.space)
            .cmp(&memory_space_order(other.space))
            .then_with(|| self.address.cmp(&other.address))
    }
}

impl PartialOrd for GlobalObjectKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectKind {
    StackSlot {
        space: SpaceId,
        base: StackAddressBase,
        offset: i64,
    },
    FrameObject {
        space: SpaceId,
        base: StackAddressBase,
        offset: i64,
    },
    Parameter {
        space: SpaceId,
        index: usize,
    },
    Global {
        space: SpaceId,
        address: u64,
    },
    HeapAlloc {
        space: SpaceId,
        call_site: CallSiteId,
    },
    EscapedUnknown {
        space: SpaceId,
    },
}

impl ObjectKind {
    pub const fn space(&self) -> SpaceId {
        match self {
            Self::StackSlot { space, .. }
            | Self::FrameObject { space, .. }
            | Self::Parameter { space, .. }
            | Self::Global { space, .. }
            | Self::HeapAlloc { space, .. }
            | Self::EscapedUnknown { space } => *space,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectFact {
    pub id: ObjectId,
    pub kind: ObjectKind,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObjectModel {
    pub objects: BTreeMap<ObjectId, ObjectFact>,
    pub value_objects: BTreeMap<MemoryObjectKey, ObjectId>,
    pub stack_objects: BTreeMap<StackObjectKey, ObjectId>,
    /// Machine-proven entry-SP coordinates for source-coordinate stack
    /// objects. Missing entries are intentionally treated as unknown.
    pub entry_stack_roots: BTreeMap<ObjectId, StackAddressRoot>,
    /// Exact modular address width for each source-owned memory space.
    /// Alias refinement is disabled when this source fact is unavailable.
    pub address_bits_by_space: BTreeMap<ObjectSpaceId, u32>,
    pub parameter_objects: BTreeMap<ParameterObjectKey, ObjectId>,
    pub global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    pub escaped_unknown: BTreeMap<ObjectSpaceId, ObjectId>,
}

impl ObjectModel {
    pub fn object_for_value(&self, value: ValueId, space: SpaceId) -> Option<ObjectId> {
        self.value_objects
            .get(&MemoryObjectKey { value, space })
            .copied()
    }

    pub fn object_for_var(
        &self,
        graph: &SsaGraph,
        value: &SSAVar,
        space: SpaceId,
    ) -> Option<ObjectId> {
        graph
            .value_id_for_var(value)
            .and_then(|value_id| self.object_for_value(value_id, space))
    }

    pub fn object(&self, id: ObjectId) -> Option<&ObjectFact> {
        self.objects.get(&id)
    }

    pub fn escaped_unknown_object(&self, space: SpaceId) -> Option<ObjectId> {
        self.escaped_unknown.get(&ObjectSpaceId(space)).copied()
    }

    pub fn memory_spaces(&self) -> impl Iterator<Item = SpaceId> + '_ {
        self.escaped_unknown.keys().map(|space| space.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryVersion {
    pub object: ObjectId,
    pub version: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RelativeMemoryAddress {
    Exact(i64),
    Affine {
        terms: Vec<crate::AffineAddressTerm>,
        offset: i64,
    },
    Unknown,
}

impl RelativeMemoryAddress {
    pub fn exact_offset(&self) -> Option<i64> {
        match self {
            Self::Exact(offset) => Some(*offset),
            Self::Affine { .. } | Self::Unknown => None,
        }
    }

    pub fn constant_offset(&self) -> Option<i64> {
        match self {
            Self::Exact(offset) | Self::Affine { offset, .. } => Some(*offset),
            Self::Unknown => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemoryLocation {
    pub space: SpaceId,
    pub object: ObjectId,
    pub address: RelativeMemoryAddress,
    pub size: u32,
}

impl Ord for MemoryLocation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        memory_space_order(self.space)
            .cmp(&memory_space_order(other.space))
            .then_with(|| self.object.cmp(&other.object))
            .then_with(|| self.address.cmp(&other.address))
            .then_with(|| self.size.cmp(&other.size))
    }
}

impl PartialOrd for MemoryLocation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryUseFact {
    pub location: MemoryLocation,
    pub version: MemoryVersion,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryDefFact {
    pub location: MemoryLocation,
    pub previous_version: MemoryVersion,
    pub next_version: MemoryVersion,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryPhiFact {
    pub object: ObjectId,
    pub location: MemoryLocation,
    pub output_version: MemoryVersion,
    pub inputs: Vec<(u64, MemoryVersion)>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MemorySSAFacts {
    pub uses_by_inst: BTreeMap<InstId, Vec<MemoryUseFact>>,
    pub defs_by_inst: BTreeMap<InstId, Vec<MemoryDefFact>>,
    pub phis_by_block: BTreeMap<u64, Vec<MemoryPhiFact>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareKind {
    Equal,
    NotEqual,
    Less,
    SignedLess,
    LessEqual,
    SignedLessEqual,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompareProvenance {
    pub kind: CompareKind,
    pub lhs: ValueId,
    pub rhs: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredicateFact {
    pub id: PredicateId,
    pub block_addr: u64,
    pub condition: ValueId,
    pub comparison: Option<CompareProvenance>,
    /// Comparison at the machine branch program point before algebraic
    /// normalization (for example, `sub_result != 0`).
    pub evaluated_comparison: Option<CompareProvenance>,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockAssumption {
    pub predecessor: u64,
    pub predicate: PredicateId,
    pub truth: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchPredicateFact {
    pub block_addr: u64,
    pub selector: Option<ValueId>,
    pub cases: Vec<(u64, u64)>,
    pub default: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PredicateFacts {
    pub predicates: BTreeMap<PredicateId, PredicateFact>,
    pub block_assumptions: BTreeMap<u64, Vec<BlockAssumption>>,
    pub switches: BTreeMap<u64, SwitchPredicateFact>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallMemoryEffect {
    ReadOnly,
    WriteOnly,
    ReadWrite,
    Alloc,
    Free,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallSiteFact {
    pub id: CallSiteId,
    pub at: InstId,
    /// Exact raw lifted identity when this fact belongs to an artifact-backed
    /// source machine context. Synthetic/context-free facts leave it absent.
    pub raw_identity: Option<SourceCallSiteIdentity>,
    pub target: ValueId,
    pub direct_target: Option<u64>,
    pub fallthrough: Option<u64>,
    pub memory_effect: CallMemoryEffect,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CallSiteFacts {
    pub by_id: BTreeMap<CallSiteId, CallSiteFact>,
    pub by_inst: BTreeMap<InstId, CallSiteId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CallBoundarySlot {
    Register {
        index: u32,
        storage: crate::CanonicalStorageId,
    },
    Stack(i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallBoundaryValueFact {
    pub slot: CallBoundarySlot,
    pub value: ValueId,
}

/// Where a call argument's value comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceCallArgumentValue {
    /// The function never defines this carrier before the call, so the value
    /// the callee receives is the one this function was entered with. No SSA
    /// value is named for it, because nothing in this function read it: a call
    /// takes its arguments implicitly.
    PreservedEntry,
    /// An exact value defined in this function reaches the call.
    Value(ValueId),
}

/// One argument carrier at a call boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceCallArgumentFact {
    pub slot: CallBoundarySlot,
    pub value: SourceCallArgumentValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCallBoundaryFact {
    pub call_site: CallSiteId,
    pub at: InstId,
    pub calling_convention: Option<String>,
    pub variadic: Option<bool>,
    pub noreturn: Option<bool>,
    pub result_kind: Option<SourceCallResult>,
    pub arguments: Vec<SourceCallArgumentFact>,
    pub results: Vec<CallBoundaryValueFact>,
    /// False until an ABI-aware boundary pass proves that every slot is known.
    pub complete: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceReturnBoundaryFact {
    pub at: InstId,
    pub values: Vec<CallBoundaryValueFact>,
    /// Exact source-declared return-address carrier consumed by this return.
    pub return_address: Option<SourceReturnAddressFact>,
    /// Exact register values that require ordered contained-slice writes to
    /// reconstruct. These are deliberately not also exposed through `values`:
    /// a single stale full-width definition is not the value at the boundary.
    pub register_compositions: Vec<SourceReturnRegisterCompositionFact>,
    /// Exact full-width stack-pointer value reaching this return when the
    /// source interface declares the typed stack-pointer carrier.
    pub exit_stack_pointer: Option<SourceReturnStackPointerFact>,
    /// False when the current source facts cannot distinguish void from an
    /// unresolved return carrier or cannot recover declared exit machine state.
    pub complete: bool,
    /// True when the exit machine state alone is fully recovered: the return
    /// address carrier and the exit stack pointer are both known. This is
    /// independent of whether any ABI described the values the return carries,
    /// so it holds for functions with no recovered ABI at all.
    pub machine_state_complete: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceReturnAddressFact {
    /// Exact source-declared return-address carrier transported to the return.
    pub storage: CanonicalStorageId,
    /// Exact control-target value consumed by the return. This may either be
    /// the carrier itself or the result of one immediately preceding,
    /// full-width `Copy` from that carrier.
    pub value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceReturnStackPointerFact {
    /// The lifted function never defines or consumes this carrier, and every
    /// predecessor path reaches the return without a call or overlapping
    /// partial/full-width write. The architectural entry value is therefore
    /// preserved without inventing an SSA value that does not exist.
    PreservedEntry { storage: CanonicalStorageId },
    /// A concrete graph value reaches the return. Its producer, when any, is
    /// rooted by the semantic-obligation inventory.
    ReachingValue {
        storage: CanonicalStorageId,
        value: ValueId,
    },
}

impl SourceReturnStackPointerFact {
    pub const fn storage(self) -> CanonicalStorageId {
        match self {
            Self::PreservedEntry { storage } | Self::ReachingValue { storage, .. } => storage,
        }
    }

    pub const fn value(self) -> Option<ValueId> {
        match self {
            Self::PreservedEntry { .. } => None,
            Self::ReachingValue { value, .. } => Some(value),
        }
    }
}

/// Schema for exact ABI return-register compositions.
pub const SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION: u32 = 1;

/// One canonical register definition retained by a return composition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceReturnRegisterDefinitionFact {
    pub storage: CanonicalStorageId,
    pub value: ValueId,
    pub producer: InstId,
}

/// One ordered contained-slice write over a full-width return-register base.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceReturnRegisterOverlayFact {
    pub definition: SourceReturnRegisterDefinitionFact,
    /// Physical byte offset from the start of the ABI return storage.
    pub offset_bytes: u32,
}

/// Exact boundary value reconstructed from a full-width base and every later
/// overlapping register write, in source order.
///
/// The base supplies every bit not replaced by an overlay. Validation binds
/// each canonical storage/value/producer identity back to the source graph and
/// rejects missing, reordered, intervening, or non-contained overlaps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceReturnRegisterCompositionFact {
    pub schema_version: u32,
    pub slot: CallBoundarySlot,
    pub base: SourceReturnRegisterDefinitionFact,
    pub overlays: Vec<SourceReturnRegisterOverlayFact>,
}

impl SourceReturnRegisterCompositionFact {
    /// Canonical definitions in the exact order needed for reconstruction.
    pub fn ordered_definitions(&self) -> impl Iterator<Item = &SourceReturnRegisterDefinitionFact> {
        std::iter::once(&self.base).chain(self.overlays.iter().map(|overlay| &overlay.definition))
    }

    /// Validate this composition against the exact prepared source artifact.
    pub fn validate(
        &self,
        function: &SSAFunction,
        graph: &SsaGraph,
        machine_context: &SourceMachineContext,
        boundary_at: InstId,
    ) -> bool {
        validate_return_register_composition(self, function, graph, machine_context, boundary_at)
    }
}

/// One exact source-declared ABI parameter and its canonical graph carrier.
///
/// `abi_storage` is the source calling-convention carrier. `graph_storage`
/// is the exact, source-declared logical projection used by SSA; it is never
/// inferred from a register name or an overlapping storage range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceFormalParameterFact {
    pub index: u32,
    pub abi_storage: CanonicalStorageId,
    pub graph_storage: CanonicalStorageId,
    pub logical_value: SourceLogicalValue,
    pub value: ValueId,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceBoundaryFacts {
    pub parameters: BTreeMap<u32, SourceFormalParameterFact>,
    pub calls: BTreeMap<CallSiteId, SourceCallBoundaryFact>,
    pub returns: BTreeMap<InstId, SourceReturnBoundaryFact>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LoopId(pub u32);

/// A control-flow fact that must hold whenever a block executes.
///
/// Switch arms retain all values targeting one edge because a multi-label arm
/// is a disjunction, not several independent guards.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ControlGuard {
    Branch {
        predicate: PredicateId,
        truth: bool,
    },
    SwitchArm {
        block_addr: u64,
        case_values: Vec<u64>,
        includes_default: bool,
    },
}

/// Canonical control context shared by every path reaching a block.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ControlDomain {
    pub id: ControlDomainId,
    pub guards: Vec<ControlGuard>,
    pub loops: Vec<LoopId>,
    /// False means the CFG had no fully representable path proof for this block.
    pub complete: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ControlDomainFacts {
    pub domains: BTreeMap<ControlDomainId, ControlDomain>,
    pub by_block: BTreeMap<u64, ControlDomainId>,
}

impl ControlDomainFacts {
    pub fn for_block(&self, block_addr: u64) -> Option<&ControlDomain> {
        self.by_block
            .get(&block_addr)
            .and_then(|id| self.domains.get(id))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProofNodeId {
    pub owner: &'static str,
    pub kind: &'static str,
    pub anchor: u64,
    pub ordinal: u64,
}

impl ProofNodeId {
    pub const fn new(owner: &'static str, kind: &'static str, anchor: u64, ordinal: u64) -> Self {
        Self {
            owner,
            kind,
            anchor,
            ordinal,
        }
    }

    pub const fn loop_certificate(header: u64, loop_id: LoopId) -> Self {
        Self::new("r2ssa", "loop", header, loop_id.0 as u64)
    }

    pub const fn switch_certificate(block_addr: u64) -> Self {
        Self::new("r2ssa", "switch", block_addr, 0)
    }
}

impl std::fmt::Display for ProofNodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:0x{:x}:{}",
            self.owner, self.kind, self.anchor, self.ordinal
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructuredLoopKind {
    Natural,
    SelfLoop,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoopCarrierEdgeValue {
    pub predecessor: u64,
    pub value: ValueId,
    /// Exact phi input consuming `value` on `predecessor`'s edge.
    ///
    /// Loop-carrier facts are an in-memory prepared-fact contract and are not
    /// part of r2ssa's serde schema, so this field does not change persisted
    /// artifact compatibility.
    pub site: UseSite,
}

impl LoopCarrierEdgeValue {
    /// Prove that this edge names the exact indexed input and predecessor of a
    /// canonical graph phi. This is O(1) in the size of the graph.
    pub fn validate(&self, graph: &SsaGraph) -> bool {
        loop_carrier_phi_input_matches(graph, self.predecessor, self.value, self.site)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoopCarrierUpdateFact {
    pub predecessor: u64,
    pub value: ValueId,
    /// Exact header-phi input consuming `value` on `predecessor`'s edge.
    pub site: UseSite,
    /// Values bit-identical to `value` through same-width copy chains.
    pub identity_values: BTreeSet<ValueId>,
}

/// Exact program-point role one SSA value has in a certified loop carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LoopCarrierMemberRole {
    HeaderPhi,
    Entry,
    LatchUpdate,
    UpdateIdentity,
    DominatingInitializer,
    StorageContinuation,
    PostLoopMerge,
    ProjectedPeer,
}

/// One sorted, source-owned member row for a loop carrier.
///
/// A value may have more than one role: for example, an update value is also
/// one of its exact copy-chain identities. The dense graph remains the owner of
/// definitions and uses; this row only seals the coalescing relation already
/// proven by those facts.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoopCarrierMemberFact {
    pub value: ValueId,
    pub roles: BTreeSet<LoopCarrierMemberRole>,
}

impl LoopCarrierUpdateFact {
    /// Prove that this update names the exact indexed input and predecessor of
    /// a canonical graph phi. This is O(1) in the size of the graph.
    pub fn validate(&self, graph: &SsaGraph) -> bool {
        loop_carrier_phi_input_matches(graph, self.predecessor, self.value, self.site)
    }
}

/// A loop-carried mutable value proven directly from header phi edges.
///
/// `identity_values` contains phi outputs that denote the carrier state after
/// structured control flow chooses an incoming edge. Entry and update values
/// remain expressions; consumers must not globally replace them with the
/// carrier because their meaning depends on the edge program point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCarrierFact {
    pub id: SemanticId,
    pub loop_id: LoopId,
    pub header: u64,
    pub phi: ValueId,
    pub width: u32,
    pub identity_values: BTreeSet<ValueId>,
    pub entries: Vec<LoopCarrierEdgeValue>,
    pub updates: Vec<LoopCarrierUpdateFact>,
    /// Entry-valued predecessor edges that dominate the loop header and can
    /// initialize the coalesced carrier before zero-iteration exits.
    pub dominating_initializers: Vec<LoopCarrierEdgeValue>,
    /// Complete exact members, sorted by `ValueId` and sealed from the role
    /// facts above plus post-loop and projected-peer certificates.
    pub members: Vec<LoopCarrierMemberFact>,
}

impl LoopCarrierFact {
    /// Exact source-owned coalescing membership for this carrier.
    ///
    /// The rows are sealed in [`StructuredLoopFact::validate_carrier_members`];
    /// this projection deliberately contains no second membership algorithm.
    pub fn coalescing_values(&self) -> BTreeSet<ValueId> {
        self.members.iter().map(|member| member.value).collect()
    }

    /// Validate every retained edge against the graph that owns this fact.
    ///
    /// Entry and update sites must be inputs of this carrier's header phi.
    /// Dominating initializer sites must be inputs of a phi whose output is
    /// one of this carrier's certified identity values.
    pub fn validate(&self, graph: &SsaGraph) -> bool {
        let Some(phi_inst) = graph.def_inst(self.phi) else {
            return false;
        };
        let Some(inst) = graph.inst(phi_inst) else {
            return false;
        };
        if !matches!(inst.payload, InstPayload::Phi { .. })
            || inst.output != Some(self.phi)
            || graph.block(inst.block).map(|block| block.addr) != Some(self.header)
            || self.id != SemanticId::loop_carrier(self.phi)
        {
            return false;
        }

        let entry_values = self
            .entries
            .iter()
            .map(|entry| entry.value)
            .collect::<BTreeSet<_>>();

        self.entries
            .iter()
            .all(|edge| edge.site.inst == phi_inst && edge.validate(graph))
            && self
                .updates
                .iter()
                .all(|update| update.site.inst == phi_inst && update.validate(graph))
            && self.dominating_initializers.iter().all(|edge| {
                edge.site.inst != phi_inst
                    && edge.validate(graph)
                    && entry_values.contains(&edge.value)
                    && graph
                        .inst(edge.site.inst)
                        .and_then(|inst| inst.output)
                        .is_some_and(|output| self.identity_values.contains(&output))
            })
    }
}

fn loop_carrier_phi_input_matches(
    graph: &SsaGraph,
    predecessor: u64,
    value: ValueId,
    site: UseSite,
) -> bool {
    let Some(inst) = graph.inst(site.inst) else {
        return false;
    };
    let InstPayload::Phi { predecessors } = &inst.payload else {
        return false;
    };

    inst.inputs.get(site.input_idx) == Some(&value)
        && predecessors
            .get(site.input_idx)
            .and_then(|predecessor| graph.block(*predecessor))
            .map(|block| block.addr)
            == Some(predecessor)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredLoopFact {
    pub id: LoopId,
    pub kind: StructuredLoopKind,
    pub header: u64,
    pub latches: Vec<u64>,
    pub body: Vec<u64>,
    pub exits: Vec<u64>,
    pub condition: Option<PredicateId>,
    pub carriers: Vec<LoopCarrierFact>,
    pub induction_phi: Option<ValueId>,
    pub induction_init: Option<ValueId>,
    pub induction_update: Option<ValueId>,
    pub bound: Option<ValueId>,
}

impl StructuredLoopFact {
    /// Recompute and validate the sorted carrier-member rows against their
    /// exact graph, storage-run, and source machine contracts.
    ///
    /// A single [`LoopCarrierFact`] cannot validate projected peers because
    /// peerhood is a relation among the carriers in one loop. Keeping this
    /// check on the loop fact prevents a stored peer row and its owning loop
    /// from becoming two independently mutable answers.
    pub fn validate_carrier_members(
        &self,
        graph: &SsaGraph,
        storage_spans: &StorageSpans,
        machine_context: Option<&SourceMachineContext>,
    ) -> bool {
        if self.carriers.iter().any(|carrier| {
            carrier.loop_id != self.id
                || carrier.header != self.header
                || !carrier.validate(graph)
        }) {
            return false;
        }
        let body = self.body.iter().copied().collect::<BTreeSet<_>>();
        let latches = self.latches.iter().copied().collect::<BTreeSet<_>>();
        loop_carrier_member_rows(
            graph,
            self.header,
            &latches,
            &body,
            storage_spans,
            machine_context,
            &self.carriers,
        )
        .is_some_and(|expected| {
            expected.len() == self.carriers.len()
                && self
                    .carriers
                    .iter()
                    .zip(expected)
                    .all(|(carrier, expected)| carrier.members == expected)
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct StructuredAccessId {
    pub inst: InstId,
    pub ordinal: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredMemoryAccessFact {
    pub id: StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub space: SpaceId,
    pub object: ObjectId,
    pub address: ValueId,
    pub value: Option<ValueId>,
    pub is_write: bool,
    pub width: u32,
    /// True only when exactly one memory-SSA fact annotates this raw subeffect.
    pub provenance_complete: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredRecursiveCallFact {
    pub call_site: CallSiteId,
    pub block_addr: u64,
    pub op_index: usize,
    pub target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCertificate {
    pub proof_node: ProofNodeId,
    pub loop_id: LoopId,
    pub header: u64,
    pub latches: Vec<u64>,
    pub body: Vec<u64>,
    pub exits: Vec<u64>,
    pub condition: Option<PredicateId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchCertificate {
    pub proof_node: ProofNodeId,
    pub block_addr: u64,
    pub selector: Option<ValueId>,
    pub cases: Vec<(u64, u64)>,
    pub default: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfRegionCertificate {
    pub predicate: PredicateId,
    pub block_addr: u64,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionCertificate {
    pub value: ValueId,
    pub defining_inst: Option<InstId>,
    pub inputs: Vec<ValueId>,
    pub width: u32,
    pub renderable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryAccessCertificate {
    pub access: StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub space: SpaceId,
    pub object: ObjectId,
    pub address: ValueId,
    pub value: Option<ValueId>,
    pub is_write: bool,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSlotCertificate {
    pub object: ObjectId,
    pub space: SpaceId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub size: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallsiteCertificate {
    pub call_site: CallSiteId,
    pub at: InstId,
    pub block_addr: u64,
    pub op_index: usize,
    pub target: ValueId,
    pub direct_target: Option<u64>,
    pub fallthrough: Option<u64>,
    pub argument_values: Vec<ValueId>,
    pub stack_argument_values: Vec<StackCallArgumentCertificate>,
    pub argument_certificates: Vec<CallArgumentCertificate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackCallArgumentCertificate {
    pub stack_offset: i64,
    pub value: ValueId,
    pub memory_access: StructuredAccessId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArgumentCertificate {
    pub index: usize,
    pub value: ValueId,
    pub location: CallArgumentLocation,
    pub source_inst: Option<InstId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallArgumentLocation {
    Register {
        name: String,
    },
    Stack {
        object: ObjectId,
        offset: i64,
        memory_access: StructuredAccessId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallResultCertificate {
    pub call_site: CallSiteId,
    pub at: InstId,
    pub block_addr: u64,
    pub op_index: usize,
    pub value: ValueId,
    pub width: u32,
    pub relation: CallResultValueRelation,
    pub carrier: ReturnCarrier,
    pub owner: Option<ValueOwner>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallResultValueRelation {
    Identity,
    Derived,
}

impl CallResultValueRelation {
    pub fn is_identity(self) -> bool {
        self == Self::Identity
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnCarrier {
    Register {
        storage: CanonicalStorageId,
    },
    StackSlot {
        object: ObjectId,
        offset: i64,
        memory_access: Option<StructuredAccessId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueOwner {
    Value(ValueId),
    StackSlot { object: ObjectId, offset: i64 },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackReloadSourceCertificate {
    pub value: ValueId,
    pub reload: ValueId,
    pub source: ValueId,
    pub canonical_source: ValueId,
    pub object: ObjectId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub value_width: u32,
    pub memory_width: u32,
    pub store_access: StructuredAccessId,
    pub load_access: StructuredAccessId,
    pub store_inst: InstId,
    pub load_inst: InstId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnValueCertificate {
    pub at: InstId,
    pub block_addr: u64,
    pub op_index: usize,
    pub value: ValueId,
    pub width: u32,
    pub carrier: Option<ReturnCarrier>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedProofFailure {
    pub owner: &'static str,
    pub anchor: u64,
    pub obligation: &'static str,
    pub reason: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreparedFunctionCertificates {
    pub loops: BTreeMap<LoopId, LoopCertificate>,
    pub switches: BTreeMap<u64, SwitchCertificate>,
    pub if_regions: BTreeMap<PredicateId, IfRegionCertificate>,
    pub expressions: BTreeMap<ValueId, ExpressionCertificate>,
    pub memory_accesses: BTreeMap<StructuredAccessId, MemoryAccessCertificate>,
    pub memory_accesses_by_op: BTreeMap<(u64, usize, bool), Vec<StructuredAccessId>>,
    pub stack_slots: BTreeMap<ObjectId, StackSlotCertificate>,
    pub callsites: BTreeMap<CallSiteId, CallsiteCertificate>,
    pub callsites_by_inst: BTreeMap<InstId, CallSiteId>,
    pub call_results: BTreeMap<ValueId, CallResultCertificate>,
    pub call_results_by_inst: BTreeMap<InstId, ValueId>,
    pub call_results_by_callsite: BTreeMap<CallSiteId, Vec<ValueId>>,
    pub stack_reloads: BTreeMap<ValueId, StackReloadSourceCertificate>,
    pub returns: Vec<ReturnValueCertificate>,
    pub returns_by_inst: BTreeMap<InstId, usize>,
    pub failures: Vec<PreparedProofFailure>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StructuredDataflowFacts {
    pub loops: BTreeMap<LoopId, StructuredLoopFact>,
    /// Cyclic CFG blocks not represented by a structured loop fact.
    pub unstructured_cycle_blocks: BTreeSet<u64>,
    pub memory_accesses: BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    pub recursive_calls: BTreeMap<CallSiteId, StructuredRecursiveCallFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreparedAssumptionBindingKind {
    Predicate {
        predicate: PredicateId,
        block_addr: u64,
        predecessor: Option<u64>,
        truth: bool,
    },
    Register {
        name: String,
        state_name: String,
        symbol_name: String,
        bits: u32,
    },
    StackSlot {
        base: StackAddressBase,
        offset: i64,
        object: ObjectId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedAssumptionBinding {
    pub assumption: crate::AnalysisAssumption,
    pub binding: PreparedAssumptionBindingKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedFunctionFacts {
    pub addresses: AddressProvenanceFacts,
    pub objects: ObjectModel,
    pub memory: MemorySSAFacts,
    pub predicates: PredicateFacts,
    pub call_sites: CallSiteFacts,
    pub boundaries: SourceBoundaryFacts,
    pub structured: StructuredDataflowFacts,
    pub control_domains: ControlDomainFacts,
    pub certificates: PreparedFunctionCertificates,
    pub obligations: SemanticObligationInventory,
    pub assumptions: AssumptionSet,
    pub applied_assumption_bindings: Vec<PreparedAssumptionBinding>,
    pub assumption_usage: AssumptionUsageReport,
}

impl PreparedFunctionFacts {
    pub fn collect(function: &SSAFunction, graph: &SsaGraph) -> Self {
        let storage_spans = StorageSpans::compute(function, graph);
        Self::collect_inner(
            function,
            graph,
            &storage_spans,
            &AssumptionSet::default(),
            None,
        )
    }

    pub fn collect_with_assumptions(
        function: &SSAFunction,
        graph: &SsaGraph,
        assumptions: &AssumptionSet,
    ) -> Self {
        let storage_spans = StorageSpans::compute(function, graph);
        Self::collect_inner(function, graph, &storage_spans, assumptions, None)
    }

    pub(crate) fn collect_with_context(
        function: &SSAFunction,
        graph: &SsaGraph,
        storage_spans: &StorageSpans,
        assumptions: &AssumptionSet,
        machine_context: &SourceMachineContext,
    ) -> Self {
        Self::collect_inner(
            function,
            graph,
            storage_spans,
            assumptions,
            Some(machine_context),
        )
    }

    fn collect_inner(
        function: &SSAFunction,
        graph: &SsaGraph,
        storage_spans: &StorageSpans,
        assumptions: &AssumptionSet,
        machine_context: Option<&SourceMachineContext>,
    ) -> Self {
        let addresses = collect_address_provenance(function, graph, machine_context);
        let call_sites = collect_call_sites(
            function,
            graph,
            function.decompile_prep_facts(),
            machine_context,
        );
        let (objects, memory) = collect_object_and_memory_facts(
            function,
            graph,
            &addresses,
            &call_sites,
            machine_context,
        );
        let predicates = collect_predicate_facts(function, graph);
        let boundaries =
            collect_source_boundary_facts(function, graph, &call_sites, machine_context);
        let live_out = machine_context
            .and_then(crate::abi::AbiProfile::from_machine_context)
            .map(|abi| crate::liveout::FunctionLiveOut::compute(function, graph, &abi))
            .unwrap_or_default();
        let structured = collect_structured_dataflow_facts(
            function,
            graph,
            StructuredCollectionInputs {
                objects: &objects,
                memory: &memory,
                predicates: &predicates,
                call_sites: &call_sites,
                live_out: &live_out,
                storage_spans,
                machine_context,
            },
        );
        let control_domains = collect_control_domain_facts(function, &predicates, &structured);
        let obligations = SemanticObligationInventory::collect(graph, &structured, &boundaries);
        let certificates = collect_prepared_function_certificates(
            &boundaries,
            function,
            graph,
            &objects,
            &memory,
            &predicates,
            &call_sites,
            &structured,
        );
        let (applied_assumption_bindings, assumption_usage) =
            collect_prepared_assumption_usage(graph, &objects, &predicates, assumptions);
        Self {
            addresses,
            objects,
            memory,
            predicates,
            call_sites,
            boundaries,
            structured,
            control_domains,
            certificates,
            obligations,
            assumptions: assumptions.clone(),
            applied_assumption_bindings,
            assumption_usage,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PredicateBranchAssumptionResolution {
    Applied {
        predicate: PredicateId,
        block_addr: u64,
        predecessor: Option<u64>,
        truth: bool,
    },
    Ignored,
    Conflict(String),
}

fn resolve_predicate_branch_assumption(
    predicates: &PredicateFacts,
    assumption: &crate::AnalysisAssumption,
) -> Option<PredicateBranchAssumptionResolution> {
    let (
        AssumptionSubject::Predicate {
            predicate,
            block_addr,
            predecessor,
        },
        AssumptionValue::Branch { truth },
    ) = (&assumption.subject, &assumption.value)
    else {
        return None;
    };
    let Some(fact) = predicates.predicates.get(predicate) else {
        return Some(PredicateBranchAssumptionResolution::Ignored);
    };
    if fact.block_addr != *block_addr {
        return Some(PredicateBranchAssumptionResolution::Conflict(format!(
            "predicate block mismatch (expected 0x{block_addr:x}, observed 0x{:x})",
            fact.block_addr
        )));
    }
    if let Some(predecessor) = predecessor {
        let expected = if *truth {
            fact.true_target
        } else {
            fact.false_target
        };
        if *predecessor != expected {
            return Some(PredicateBranchAssumptionResolution::Conflict(format!(
                "branch predecessor 0x{predecessor:x} does not match selected edge 0x{expected:x}"
            )));
        }
    }
    Some(PredicateBranchAssumptionResolution::Applied {
        predicate: *predicate,
        block_addr: *block_addr,
        predecessor: *predecessor,
        truth: *truth,
    })
}

fn contradictory_predicate_assumptions(
    predicates: &PredicateFacts,
    assumptions: &AssumptionSet,
) -> BTreeSet<PredicateId> {
    let mut truths = BTreeMap::<PredicateId, BTreeSet<bool>>::new();
    for assumption in assumptions.iter() {
        let Some(PredicateBranchAssumptionResolution::Applied {
            predicate, truth, ..
        }) = resolve_predicate_branch_assumption(predicates, assumption)
        else {
            continue;
        };
        truths.entry(predicate).or_default().insert(truth);
    }
    truths
        .into_iter()
        .filter_map(|(predicate, truths)| (truths.len() > 1).then_some(predicate))
        .collect()
}

fn collect_prepared_assumption_usage(
    graph: &SsaGraph,
    objects: &ObjectModel,
    base_predicates: &PredicateFacts,
    assumptions: &AssumptionSet,
) -> (Vec<PreparedAssumptionBinding>, AssumptionUsageReport) {
    let mut bindings = Vec::new();
    let mut usage = AssumptionUsageReport::default();
    let contradictory = contradictory_predicate_assumptions(base_predicates, assumptions);

    for assumption in assumptions.iter() {
        if let Some(resolution) = resolve_predicate_branch_assumption(base_predicates, assumption) {
            match resolution {
                PredicateBranchAssumptionResolution::Applied {
                    predicate,
                    block_addr,
                    predecessor,
                    truth,
                } => {
                    if contradictory.contains(&predicate) {
                        usage.mark_conflict(
                            assumption,
                            format!("contradictory branch truths for predicate {}", predicate.0),
                        );
                        continue;
                    }
                    usage.mark_applied(assumption);
                    bindings.push(PreparedAssumptionBinding {
                        assumption: assumption.clone(),
                        binding: PreparedAssumptionBindingKind::Predicate {
                            predicate,
                            block_addr,
                            predecessor,
                            truth,
                        },
                    });
                }
                PredicateBranchAssumptionResolution::Ignored => {
                    usage.mark_ignored(assumption);
                }
                PredicateBranchAssumptionResolution::Conflict(reason) => {
                    usage.mark_conflict(assumption, reason);
                }
            }
            continue;
        }
        match (&assumption.subject, &assumption.value) {
            (AssumptionSubject::Register { name }, _) => {
                let Some(value) = graph.values.iter().find(|value| {
                    value.var.version == 0
                        && value.var.is_register()
                        && value.var.name.eq_ignore_ascii_case(name)
                }) else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                usage.mark_applied(assumption);
                bindings.push(PreparedAssumptionBinding {
                    assumption: assumption.clone(),
                    binding: PreparedAssumptionBindingKind::Register {
                        name: value.var.name.clone(),
                        state_name: value.var.display_name(),
                        symbol_name: value
                            .var
                            .name
                            .strip_prefix("reg:")
                            .unwrap_or(&value.var.name)
                            .to_ascii_lowercase(),
                        bits: value.var.size.saturating_mul(8),
                    },
                });
            }
            (AssumptionSubject::StackSlot { base, offset }, _) => {
                let Some((root, object)) =
                    objects.stack_objects.iter().find_map(|(key, object)| {
                        let root = key.root;
                        let matches_base = matches!(
                            (base.as_str(), root.base),
                            ("bp", StackAddressBase::FramePointer)
                                | ("frame", StackAddressBase::FramePointer)
                                | ("rbp", StackAddressBase::FramePointer)
                                | ("sp", StackAddressBase::StackPointer)
                                | ("stack", StackAddressBase::StackPointer)
                                | ("rsp", StackAddressBase::StackPointer)
                        );
                        (key.space == SpaceId::Ram && matches_base && root.offset == *offset)
                            .then_some((root, *object))
                    })
                else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                usage.mark_applied(assumption);
                bindings.push(PreparedAssumptionBinding {
                    assumption: assumption.clone(),
                    binding: PreparedAssumptionBindingKind::StackSlot {
                        base: root.base,
                        offset: root.offset,
                        object,
                    },
                });
            }
            _ => usage.mark_ignored(assumption),
        }
    }

    (bindings, usage)
}

#[derive(Debug, Clone)]
struct ObjectModelBuilder<'a> {
    facts: Option<&'a DecompilePrepFacts>,
    addresses: &'a AddressProvenanceFacts,
    objects: BTreeMap<ObjectId, ObjectFact>,
    value_objects: BTreeMap<MemoryObjectKey, ObjectId>,
    stack_objects: BTreeMap<StackObjectKey, ObjectId>,
    entry_stack_roots: BTreeMap<ObjectId, StackAddressRoot>,
    ambiguous_entry_stack_objects: BTreeSet<ObjectId>,
    address_bits_by_space: BTreeMap<ObjectSpaceId, u32>,
    parameter_objects: BTreeMap<ParameterObjectKey, ObjectId>,
    global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    escaped_unknown: BTreeMap<ObjectSpaceId, ObjectId>,
    next_object_id: u32,
}

impl<'a> ObjectModelBuilder<'a> {
    fn new(
        facts: Option<&'a DecompilePrepFacts>,
        addresses: &'a AddressProvenanceFacts,
        machine_context: Option<&SourceMachineContext>,
    ) -> Self {
        let escaped_unknown_id = ObjectId(0);
        let mut objects = BTreeMap::new();
        objects.insert(
            escaped_unknown_id,
            ObjectFact {
                id: escaped_unknown_id,
                kind: ObjectKind::EscapedUnknown {
                    space: SpaceId::Ram,
                },
            },
        );
        let mut escaped_unknown = BTreeMap::new();
        escaped_unknown.insert(ObjectSpaceId(SpaceId::Ram), escaped_unknown_id);
        let address_bits_by_space = machine_context
            .filter(|context| context.memory_model().is_coherent())
            .map(|context| {
                context
                    .memory_model()
                    .spaces()
                    .iter()
                    .filter(|space| space.address_bits() > 0 && space.address_bits() <= 64)
                    .map(|space| (ObjectSpaceId(space.space()), space.address_bits()))
                    .collect()
            })
            .unwrap_or_default();
        Self {
            facts,
            addresses,
            objects,
            value_objects: BTreeMap::new(),
            stack_objects: BTreeMap::new(),
            entry_stack_roots: BTreeMap::new(),
            ambiguous_entry_stack_objects: BTreeSet::new(),
            address_bits_by_space,
            parameter_objects: BTreeMap::new(),
            global_objects: BTreeMap::new(),
            escaped_unknown,
            next_object_id: 1,
        }
    }

    fn build(mut self, function: &SSAFunction, graph: &SsaGraph) -> ObjectModel {
        if let Some(facts) = self.facts {
            let mut stack_roots: Vec<StackAddressRoot> =
                facts.stack_address_roots.values().copied().collect();
            stack_roots.sort_unstable();
            stack_roots.dedup();
            for root in stack_roots {
                self.ensure_stack_object(root, SpaceId::Ram);
            }
            for var in facts.stack_address_roots.keys() {
                let _ = self.object_for_address_value(graph, var, SpaceId::Ram);
            }
        }
        let parameter_indices = self
            .addresses
            .parameter_expressions
            .values()
            .map(|expression| expression.parameter)
            .collect::<BTreeSet<_>>();
        for parameter in parameter_indices {
            self.ensure_parameter_object(parameter, SpaceId::Ram);
        }

        for block in function.blocks() {
            for op in &block.ops {
                match op {
                    SSAOp::Load { addr, space, .. }
                    | SSAOp::Store { addr, space, .. }
                    | SSAOp::LoadLinked { addr, space, .. }
                    | SSAOp::StoreConditional { addr, space, .. }
                    | SSAOp::AtomicCAS { addr, space, .. }
                    | SSAOp::LoadGuarded { addr, space, .. }
                    | SSAOp::StoreGuarded { addr, space, .. } => {
                        let _ = self.object_for_address_value(graph, addr, *space);
                    }
                    _ => {}
                }
            }
        }

        ObjectModel {
            objects: self.objects,
            value_objects: self.value_objects,
            stack_objects: self.stack_objects,
            entry_stack_roots: self.entry_stack_roots,
            address_bits_by_space: self.address_bits_by_space,
            parameter_objects: self.parameter_objects,
            global_objects: self.global_objects,
            escaped_unknown: self.escaped_unknown,
        }
    }

    fn object_for_address_value(
        &mut self,
        graph: &SsaGraph,
        value: &SSAVar,
        space: SpaceId,
    ) -> ObjectId {
        let Some(value_id) = graph.value_id_for_var(value) else {
            return self.ensure_escaped_unknown(space);
        };
        let key = MemoryObjectKey {
            value: value_id,
            space,
        };
        if let Some(object) = self.value_objects.get(&key).copied() {
            return object;
        }

        let _ = self.ensure_escaped_unknown(space);
        let object = if space == SpaceId::Ram {
            if let Some(root) = resolve_stack_root(self.facts, value) {
                let object = self.ensure_stack_object(root, space);
                if let Some(entry_root) = resolve_entry_stack_root(self.facts, value) {
                    self.record_entry_stack_root(object, entry_root);
                }
                object
            } else if let Some(expression) = self.addresses.parameter_expression(value_id) {
                self.ensure_parameter_object(expression.parameter, space)
            } else if let Some(address) = resolve_const_value(self.facts, value) {
                self.ensure_global_object(GlobalObjectKey { space, address })
            } else {
                self.ensure_escaped_unknown(space)
            }
        } else if let Some(address) = resolve_const_value(self.facts, value) {
            self.ensure_global_object(GlobalObjectKey { space, address })
        } else {
            self.ensure_escaped_unknown(space)
        };
        self.value_objects.insert(key, object);
        object
    }

    fn ensure_stack_object(&mut self, root: StackAddressRoot, space: SpaceId) -> ObjectId {
        debug_assert_eq!(space, SpaceId::Ram);
        let key = StackObjectKey { root, space };
        if let Some(object) = self.stack_objects.get(&key).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::StackSlot {
                    space,
                    base: root.base,
                    offset: root.offset,
                },
            },
        );
        self.stack_objects.insert(key, id);
        id
    }

    fn ensure_global_object(&mut self, key: GlobalObjectKey) -> ObjectId {
        if let Some(object) = self.global_objects.get(&key).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::Global {
                    space: key.space,
                    address: key.address,
                },
            },
        );
        self.global_objects.insert(key, id);
        id
    }

    fn record_entry_stack_root(&mut self, object: ObjectId, root: StackAddressRoot) {
        if self.ambiguous_entry_stack_objects.contains(&object) {
            return;
        }
        match self.entry_stack_roots.get(&object) {
            Some(existing) if *existing == root => {}
            Some(_) => {
                self.entry_stack_roots.remove(&object);
                self.ambiguous_entry_stack_objects.insert(object);
            }
            None => {
                self.entry_stack_roots.insert(object, root);
            }
        }
    }

    fn ensure_parameter_object(&mut self, index: usize, space: SpaceId) -> ObjectId {
        debug_assert_eq!(space, SpaceId::Ram);
        let key = ParameterObjectKey { index, space };
        if let Some(object) = self.parameter_objects.get(&key).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::Parameter { space, index },
            },
        );
        self.parameter_objects.insert(key, id);
        id
    }

    fn ensure_escaped_unknown(&mut self, space: SpaceId) -> ObjectId {
        let key = ObjectSpaceId(space);
        if let Some(object) = self.escaped_unknown.get(&key).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::EscapedUnknown { space },
            },
        );
        self.escaped_unknown.insert(key, id);
        id
    }

    fn alloc_object_id(&mut self) -> ObjectId {
        let id = ObjectId(self.next_object_id);
        self.next_object_id = self.next_object_id.saturating_add(1);
        id
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AccessSummary {
    uses: Vec<MemoryLocation>,
    defs: Vec<MemoryLocation>,
}

fn collect_object_and_memory_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    addresses: &AddressProvenanceFacts,
    call_sites: &CallSiteFacts,
    machine_context: Option<&SourceMachineContext>,
) -> (ObjectModel, MemorySSAFacts) {
    let facts = function.decompile_prep_facts();
    let builder = ObjectModelBuilder::new(facts, addresses, machine_context);
    let object_model = builder.build(function, graph);
    let access_summaries =
        collect_access_summaries(function, graph, facts, addresses, &object_model, call_sites);
    let memory = build_memory_ssa(function, graph, &object_model, access_summaries);
    (object_model, memory)
}

fn collect_access_summaries(
    function: &SSAFunction,
    graph: &SsaGraph,
    prep_facts: Option<&DecompilePrepFacts>,
    addresses: &AddressProvenanceFacts,
    object_model: &ObjectModel,
    call_sites: &CallSiteFacts,
) -> BTreeMap<InstId, AccessSummary> {
    let mut summaries = BTreeMap::new();

    for block in function.blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let Some(inst_id) = graph.inst_id_for_op_site(block.addr, op_idx) else {
                continue;
            };
            let mut uses = Vec::new();
            let mut defs = Vec::new();
            match op {
                SSAOp::Load { dst, addr, space }
                | SSAOp::LoadLinked {
                    dst, addr, space, ..
                }
                | SSAOp::LoadGuarded {
                    dst, addr, space, ..
                } => {
                    uses.push(memory_location_for_addr(
                        prep_facts,
                        addresses,
                        object_model,
                        graph,
                        addr,
                        *space,
                        dst.size,
                    ));
                }
                SSAOp::Store { addr, val, space }
                | SSAOp::StoreGuarded {
                    addr, val, space, ..
                } => {
                    defs.push(memory_location_for_addr(
                        prep_facts,
                        addresses,
                        object_model,
                        graph,
                        addr,
                        *space,
                        val.size,
                    ));
                }
                SSAOp::StoreConditional {
                    addr, val, space, ..
                } => {
                    let location = memory_location_for_addr(
                        prep_facts,
                        addresses,
                        object_model,
                        graph,
                        addr,
                        *space,
                        val.size,
                    );
                    uses.push(location.clone());
                    defs.push(location);
                }
                SSAOp::AtomicCAS {
                    addr,
                    expected,
                    replacement,
                    space,
                    ..
                } => {
                    let location = memory_location_for_addr(
                        prep_facts,
                        addresses,
                        object_model,
                        graph,
                        addr,
                        *space,
                        expected.size.max(replacement.size),
                    );
                    uses.push(location.clone());
                    defs.push(location);
                }
                SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                    if call_sites.by_inst.contains_key(&inst_id) {
                        for space in object_model.memory_spaces() {
                            let Some(object) = object_model.escaped_unknown_object(space) else {
                                continue;
                            };
                            let location = MemoryLocation {
                                space,
                                object,
                                address: RelativeMemoryAddress::Unknown,
                                size: 0,
                            };
                            uses.push(location.clone());
                            defs.push(location);
                        }
                    }
                }
                _ => {}
            }
            if !uses.is_empty() || !defs.is_empty() {
                summaries.insert(inst_id, AccessSummary { uses, defs });
            }
        }
    }

    summaries
}

fn build_memory_ssa(
    function: &SSAFunction,
    graph: &SsaGraph,
    object_model: &ObjectModel,
    access_summaries: BTreeMap<InstId, AccessSummary>,
) -> MemorySSAFacts {
    let mut phis_by_block = BTreeMap::new();

    let mut next_version_by_object = BTreeMap::<ObjectId, u32>::new();
    for object in object_model.objects.keys() {
        next_version_by_object.insert(*object, 1);
    }

    let mut def_versions = BTreeMap::<InstId, Vec<MemoryVersion>>::new();
    for (inst_id, summary) in &access_summaries {
        if summary.defs.is_empty() {
            continue;
        }
        let versions = summary
            .defs
            .iter()
            .map(|location| {
                let next = next_version_by_object.entry(location.object).or_insert(1);
                let version = MemoryVersion {
                    object: location.object,
                    version: *next,
                };
                *next = next.saturating_add(1);
                version
            })
            .collect::<Vec<_>>();
        def_versions.insert(*inst_id, versions);
    }

    let mut in_states = BTreeMap::<u64, BTreeMap<MemoryLocation, MemoryVersion>>::new();
    let mut out_states = BTreeMap::<u64, BTreeMap<MemoryLocation, MemoryVersion>>::new();
    let mut phi_versions = BTreeMap::<(u64, MemoryLocation), MemoryVersion>::new();
    let mut phi_inputs = BTreeMap::<(u64, MemoryLocation), Vec<(u64, MemoryVersion)>>::new();
    let (uses_by_inst, defs_by_inst) = loop {
        let mut changed = false;
        let mut uses_by_inst = BTreeMap::<InstId, Vec<MemoryUseFact>>::new();
        let mut defs_by_inst = BTreeMap::<InstId, Vec<MemoryDefFact>>::new();
        for &block_addr in function.block_addrs() {
            let preds = function.predecessors(block_addr);
            let mut in_state = BTreeMap::new();

            if !preds.is_empty() {
                let locations = preds
                    .iter()
                    .filter_map(|pred| out_states.get(pred))
                    .flat_map(|state| state.keys().cloned())
                    .collect::<BTreeSet<_>>();
                for location in locations {
                    let inputs = preds
                        .iter()
                        .map(|pred| {
                            let version = out_states
                                .get(pred)
                                .and_then(|state| state.get(&location).copied())
                                .unwrap_or(MemoryVersion {
                                    object: location.object,
                                    version: 0,
                                });
                            (*pred, version)
                        })
                        .collect::<Vec<_>>();
                    let first_version = inputs.first().map(|(_, version)| *version);
                    let merged = if inputs
                        .iter()
                        .all(|(_, version)| Some(*version) == first_version)
                    {
                        first_version.expect("inputs is not empty")
                    } else {
                        let key = (block_addr, location.clone());
                        let phi = phi_versions.entry(key.clone()).or_insert_with(|| {
                            let next = next_version_by_object.entry(location.object).or_insert(1);
                            let version = MemoryVersion {
                                object: location.object,
                                version: *next,
                            };
                            *next = next.saturating_add(1);
                            version
                        });
                        phi_inputs.insert(key, inputs);
                        *phi
                    };
                    if merged.version != 0 {
                        in_state.insert(location, merged);
                    }
                }
            }

            if in_states.get(&block_addr) != Some(&in_state) {
                in_states.insert(block_addr, in_state.clone());
                changed = true;
            }

            let mut state = in_state;
            let Some(block) = function.get_block(block_addr) else {
                continue;
            };
            for (op_idx, _) in block.ops.iter().enumerate() {
                let Some(inst_id) = graph.inst_id_for_op_site(block_addr, op_idx) else {
                    continue;
                };
                let Some(summary) = access_summaries.get(&inst_id) else {
                    continue;
                };
                for location in &summary.uses {
                    let mut reaching = state
                        .iter()
                        .filter(|(candidate, _)| {
                            memory_locations_may_alias(object_model, candidate, location)
                        })
                        .map(|(_, version)| *version)
                        .collect::<BTreeSet<_>>();
                    if reaching.is_empty() {
                        reaching.insert(MemoryVersion {
                            object: location.object,
                            version: 0,
                        });
                    }
                    for version in reaching {
                        uses_by_inst
                            .entry(inst_id)
                            .or_default()
                            .push(MemoryUseFact {
                                location: location.clone(),
                                version,
                            });
                    }
                }
                if let Some(def_versions_for_op) = def_versions.get(&inst_id) {
                    for (location, next_version) in
                        summary.defs.iter().zip(def_versions_for_op.iter())
                    {
                        let mut previous = state
                            .iter()
                            .filter(|(candidate, _)| {
                                memory_locations_may_alias(object_model, candidate, location)
                            })
                            .map(|(_, version)| *version)
                            .collect::<BTreeSet<_>>();
                        if previous.is_empty() {
                            previous.insert(MemoryVersion {
                                object: location.object,
                                version: 0,
                            });
                        }
                        for previous_version in previous {
                            defs_by_inst
                                .entry(inst_id)
                                .or_default()
                                .push(MemoryDefFact {
                                    location: location.clone(),
                                    previous_version,
                                    next_version: *next_version,
                                });
                        }
                        state.retain(|candidate, _| {
                            !memory_locations_may_alias(object_model, candidate, location)
                        });
                        state.insert(location.clone(), *next_version);
                    }
                }
            }

            if out_states.get(&block_addr) != Some(&state) {
                out_states.insert(block_addr, state);
                changed = true;
            }
        }

        if !changed {
            break (uses_by_inst, defs_by_inst);
        }
    };

    for ((block_addr, location), output_version) in phi_versions {
        let inputs = phi_inputs
            .remove(&(block_addr, location.clone()))
            .unwrap_or_default();
        phis_by_block
            .entry(block_addr)
            .or_insert_with(Vec::new)
            .push(MemoryPhiFact {
                object: location.object,
                location,
                output_version,
                inputs,
            });
    }

    MemorySSAFacts {
        uses_by_inst,
        defs_by_inst,
        phis_by_block,
    }
}

pub(crate) fn memory_locations_may_alias(
    objects: &ObjectModel,
    left: &MemoryLocation,
    right: &MemoryLocation,
) -> bool {
    let Some(left_object) = objects.object(left.object) else {
        return true;
    };
    let Some(right_object) = objects.object(right.object) else {
        return true;
    };
    if left_object.kind.space() != left.space || right_object.kind.space() != right.space {
        return true;
    }
    if left.space != right.space {
        return false;
    }
    let address_bits = objects
        .address_bits_by_space
        .get(&ObjectSpaceId(left.space))
        .copied();
    if left.object == right.object {
        return address_bits.is_some_and(|address_bits| {
            modular_memory_ranges_may_overlap(
                0,
                &left.address,
                left.size,
                0,
                &right.address,
                right.size,
                address_bits,
            )
        }) || address_bits.is_none();
    }
    if matches!(
        left_object.kind,
        ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. }
    ) && matches!(
        right_object.kind,
        ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. }
    ) && let (Some(left_root), Some(right_root)) = (
        objects.entry_stack_roots.get(&left.object),
        objects.entry_stack_roots.get(&right.object),
    ) && left_root.base == StackAddressBase::StackPointer
        && right_root.base == StackAddressBase::StackPointer
        && let Some(address_bits) = address_bits
    {
        return modular_memory_ranges_may_overlap(
            i128::from(left_root.offset),
            &left.address,
            left.size,
            i128::from(right_root.offset),
            &right.address,
            right.size,
            address_bits,
        );
    }
    match (&left_object.kind, &right_object.kind) {
        (ObjectKind::EscapedUnknown { .. }, _) | (_, ObjectKind::EscapedUnknown { .. }) => true,
        (
            ObjectKind::Parameter { .. },
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. },
        )
        | (
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. },
            ObjectKind::Parameter { .. },
        ) => false,
        (ObjectKind::Parameter { .. }, _) | (_, ObjectKind::Parameter { .. }) => true,
        (
            ObjectKind::Global {
                space: left_space,
                address: left_base,
            },
            ObjectKind::Global {
                space: right_space,
                address: right_base,
            },
        ) => {
            left_space != right_space
                || address_bits.is_none_or(|address_bits| {
                    modular_memory_ranges_may_overlap(
                        i128::from(*left_base),
                        &left.address,
                        left.size,
                        i128::from(*right_base),
                        &right.address,
                        right.size,
                        address_bits,
                    )
                })
        }
        (
            ObjectKind::StackSlot {
                base: left_base,
                offset: left_offset,
                ..
            }
            | ObjectKind::FrameObject {
                base: left_base,
                offset: left_offset,
                ..
            },
            ObjectKind::StackSlot {
                base: right_base,
                offset: right_offset,
                ..
            }
            | ObjectKind::FrameObject {
                base: right_base,
                offset: right_offset,
                ..
            },
        ) if left_base == right_base => address_bits.is_none_or(|address_bits| {
            modular_memory_ranges_may_overlap(
                i128::from(*left_offset),
                &left.address,
                left.size,
                i128::from(*right_offset),
                &right.address,
                right.size,
                address_bits,
            )
        }),
        (
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. },
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. },
        ) => true,
        (
            ObjectKind::HeapAlloc {
                call_site: left, ..
            },
            ObjectKind::HeapAlloc {
                call_site: right, ..
            },
        ) => left == right,
        _ => false,
    }
}

fn modular_memory_ranges_may_overlap(
    left_base: i128,
    left: &RelativeMemoryAddress,
    left_size: u32,
    right_base: i128,
    right: &RelativeMemoryAddress,
    right_size: u32,
    address_bits: u32,
) -> bool {
    if address_bits == 0 || address_bits > 64 || left_size == 0 || right_size == 0 {
        return true;
    }
    let (Some(left), Some(right)) = (left.exact_offset(), right.exact_offset()) else {
        return modular_affine_ranges_may_overlap(
            left_base,
            left,
            left_size,
            right_base,
            right,
            right_size,
            address_bits,
        );
    };
    let modulus = 1_i128 << address_bits;
    let left_size = i128::from(left_size);
    let right_size = i128::from(right_size);
    if left_size >= modulus || right_size >= modulus {
        return true;
    }
    let left_start = (left_base + i128::from(left)).rem_euclid(modulus);
    let right_start = (right_base + i128::from(right)).rem_euclid(modulus);
    modular_intervals_overlap(left_start, left_size, right_start, right_size, modulus)
}

fn modular_affine_ranges_may_overlap(
    left_base: i128,
    left: &RelativeMemoryAddress,
    left_size: u32,
    right_base: i128,
    right: &RelativeMemoryAddress,
    right_size: u32,
    address_bits: u32,
) -> bool {
    let (Some((left_terms, left_offset)), Some((right_terms, right_offset))) =
        (relative_affine_parts(left), relative_affine_parts(right))
    else {
        return true;
    };
    let mut difference = BTreeMap::<ValueId, i128>::new();
    for term in left_terms {
        *difference.entry(term.value).or_default() += i128::from(term.coefficient);
    }
    for term in right_terms {
        *difference.entry(term.value).or_default() -= i128::from(term.coefficient);
    }
    difference.retain(|_, coefficient| *coefficient != 0);
    let address_modulus = 1_u128 << address_bits;
    let congruence_modulus = difference
        .values()
        .map(|coefficient| coefficient.unsigned_abs())
        .fold(address_modulus, gcd_u128);
    let Ok(congruence_modulus) = i128::try_from(congruence_modulus) else {
        return true;
    };
    let constant = left_base + i128::from(left_offset) - right_base - i128::from(right_offset);
    let low = -i128::from(left_size.saturating_sub(1));
    let high = i128::from(right_size.saturating_sub(1));
    let candidate =
        low + (constant.rem_euclid(congruence_modulus) - low).rem_euclid(congruence_modulus);
    candidate <= high
}

fn relative_affine_parts(
    address: &RelativeMemoryAddress,
) -> Option<(&[crate::AffineAddressTerm], i64)> {
    match address {
        RelativeMemoryAddress::Exact(offset) => Some((&[], *offset)),
        RelativeMemoryAddress::Affine { terms, offset } => Some((terms, *offset)),
        RelativeMemoryAddress::Unknown => None,
    }
}

fn modular_intervals_overlap(
    left_start: i128,
    left_size: i128,
    right_start: i128,
    right_size: i128,
    modulus: i128,
) -> bool {
    let split = |start: i128, size: i128| {
        let end = start + size;
        if end <= modulus {
            [(start, end), (0, 0)]
        } else {
            [(start, modulus), (0, end - modulus)]
        }
    };
    let left = split(left_start, left_size);
    let right = split(right_start, right_size);
    left.into_iter().any(|(left_start, left_end)| {
        left_start < left_end
            && right.iter().any(|(right_start, right_end)| {
                right_start < right_end && left_start < *right_end && *right_start < left_end
            })
    })
}

fn gcd_u128(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

struct StructuredCollectionInputs<'a> {
    objects: &'a ObjectModel,
    memory: &'a MemorySSAFacts,
    predicates: &'a PredicateFacts,
    call_sites: &'a CallSiteFacts,
    /// What the caller reads, so a value with no reader in this body is not
    /// mistaken for one nothing reads at all.
    live_out: &'a crate::liveout::FunctionLiveOut,
    storage_spans: &'a StorageSpans,
    machine_context: Option<&'a SourceMachineContext>,
}

fn collect_structured_dataflow_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    inputs: StructuredCollectionInputs<'_>,
) -> StructuredDataflowFacts {
    let loops = collect_structured_loop_facts(
        function,
        graph,
        inputs.predicates,
        inputs.live_out,
        inputs.storage_spans,
        inputs.machine_context,
    );
    let memory_accesses =
        collect_structured_memory_access_facts(function, graph, inputs.objects, inputs.memory);
    StructuredDataflowFacts {
        unstructured_cycle_blocks: collect_unstructured_cycle_blocks(graph, &loops),
        loops,
        memory_accesses,
        recursive_calls: collect_structured_recursive_call_facts(
            function,
            graph,
            inputs.call_sites,
        ),
    }
}

fn collect_source_boundary_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_sites: &CallSiteFacts,
    machine_context: Option<&SourceMachineContext>,
) -> SourceBoundaryFacts {
    let mut facts = SourceBoundaryFacts::default();

    if let Some(machine_context) = machine_context
        .filter(|context| context.abi_model().is_available() && context.abi_model().is_coherent())
        && let Some(interface) = machine_context.function_interface()
        && let Some(type_graph) = interface.type_graph()
        && interface.schema_version() == SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
        && type_graph.schema_version() == SOURCE_TYPE_GRAPH_SCHEMA_VERSION
        && interface.parameters().len() == interface.parameter_logical_values().len()
        && machine_context.abi_model().argument_registers().len() == interface.parameters().len()
    {
        for (parameter, logical_value) in interface
            .parameters()
            .iter()
            .zip(interface.parameter_logical_values())
        {
            let abi_storage = parameter.storage();
            if machine_context
                .abi_model()
                .argument_registers()
                .iter()
                .filter(|slot| slot.index() == parameter.index() && slot.storage() == abi_storage)
                .count()
                != 1
            {
                continue;
            }
            let Some(graph_storage) =
                projected_formal_parameter_storage(abi_storage, *logical_value, type_graph)
            else {
                continue;
            };
            let candidates = graph
                .values
                .iter()
                .filter(|value| {
                    graph.def_inst(value.id).is_none()
                        && value.var.version == 0
                        && value.var.size == graph_storage.size
                        && value.canonical_storage == Some(graph_storage)
                })
                .map(|value| value.id)
                .collect::<Vec<_>>();
            if let [value] = candidates.as_slice() {
                facts.parameters.insert(
                    parameter.index(),
                    SourceFormalParameterFact {
                        index: parameter.index(),
                        abi_storage,
                        graph_storage,
                        logical_value: *logical_value,
                        value: *value,
                    },
                );
            }
        }
    }

    for call_site in call_sites.by_id.values() {
        let mut boundary = SourceCallBoundaryFact {
            call_site: call_site.id,
            at: call_site.at,
            calling_convention: None,
            variadic: None,
            noreturn: None,
            result_kind: None,
            arguments: Vec::new(),
            results: Vec::new(),
            // Calls carry implicit machine state. Only an exact source-owned
            // callsite interface may change this state to complete.
            complete: false,
        };
        if let Some((machine_context, interface)) = machine_context
            .and_then(|context| {
                context
                    .call_site_interface(call_site.id)
                    .map(|interface| (context, interface))
            })
            .filter(|(_, interface)| call_site.raw_identity == Some(interface.identity()))
        {
            boundary.calling_convention = Some(interface.calling_convention().to_string());
            boundary.variadic = Some(interface.is_variadic());
            boundary.noreturn = Some(interface.is_noreturn());
            boundary.result_kind = Some(interface.result());
            if interface.is_complete()
                && let Some((block_addr, op_index)) = graph.op_site_for_inst(call_site.at)
            {
                let arguments = interface
                    .arguments()
                    .iter()
                    .filter_map(|argument| {
                        // An argument the function passes straight through from
                        // its own entry has no definition here and is never read
                        // explicitly, so no SSA value names it. That is a
                        // description of where the value comes from, not a
                        // failure to find it.
                        reaching_abi_argument_in_block(
                            function,
                            graph,
                            machine_context,
                            block_addr,
                            op_index,
                            argument.storage(),
                        )
                        .map(|value| SourceCallArgumentFact {
                            slot: CallBoundarySlot::Register {
                                index: argument.index(),
                                storage: argument.storage(),
                            },
                            value,
                        })
                    })
                    .collect::<Vec<_>>();
                let results = match interface.result() {
                    SourceCallResult::Void => Some(Vec::new()),
                    SourceCallResult::Register { storage } => call_result_value_after_call(
                        function,
                        graph,
                        machine_context,
                        block_addr,
                        op_index,
                        storage,
                    )
                    .map(|value| {
                        vec![CallBoundaryValueFact {
                            slot: CallBoundarySlot::Register { index: 0, storage },
                            value,
                        }]
                    }),
                };
                if arguments.len() == interface.arguments().len()
                    && let Some(results) = results
                {
                    boundary.arguments = arguments;
                    boundary.results = results;
                    boundary.complete = true;
                }
            }
        }
        facts.calls.insert(call_site.id, boundary);
    }

    for inst in &graph.insts {
        if matches!(inst.payload, InstPayload::Op(SSAOp::Return { .. })) {
            let mut values = Vec::new();
            let mut register_compositions = Vec::new();
            let mut return_address = None;
            let mut exit_stack_pointer = None;
            let mut complete = false;
            let mut machine_state_complete = false;
            // Machine exit state and return values are separate questions. The
            // carriers holding the return address and the stack pointer come
            // from the machine, so they are recoverable for any function; the
            // values a return carries are an ABI question and stay gated on a
            // coherent ABI. Gating both on the ABI is what previously left a
            // function without debug information with no exit facts at all.
            if let Some(machine_context) = machine_context {
                let abi_is_coherent = machine_context.abi_model().is_available()
                    && machine_context.abi_model().is_coherent();
                let stack_pointer_storage = machine_context.stack_pointer_carrier();
                let return_address_storage = machine_context.return_address_carrier();
                let return_slots = machine_context.abi_model().return_registers();
                match abi_is_coherent
                    .then(|| {
                        machine_context
                            .function_interface()
                            .map(|interface| interface.return_kind())
                    })
                    .flatten()
                {
                    Some(SourceFunctionReturn::Void) => complete = true,
                    Some(SourceFunctionReturn::Register { .. }) => {
                        if let Some((block_addr, op_index)) = graph.op_site_for_inst(inst.id) {
                            for slot in return_slots {
                                match reaching_abi_return_register_in_block(
                                    function,
                                    graph,
                                    machine_context,
                                    block_addr,
                                    op_index,
                                    slot.index(),
                                    slot.storage(),
                                    inst.id,
                                ) {
                                    Some(ReachingAbiReturnRegister::Exact(value)) => {
                                        values.push(CallBoundaryValueFact {
                                            slot: CallBoundarySlot::Register {
                                                index: slot.index(),
                                                storage: slot.storage(),
                                            },
                                            value,
                                        });
                                    }
                                    Some(ReachingAbiReturnRegister::Composition(composition)) => {
                                        register_compositions.push(composition);
                                    }
                                    None => {}
                                }
                            }
                            complete = !return_slots.is_empty()
                                && values.len().saturating_add(register_compositions.len())
                                    == return_slots.len();
                        }
                    }
                    _ => {}
                }
                if let Some(storage) = stack_pointer_storage {
                    exit_stack_pointer = graph
                        .op_site_for_inst(inst.id)
                        .and_then(|(block_addr, op_index)| {
                            reaching_preserved_abi_value_in_block(
                                function,
                                graph,
                                machine_context,
                                block_addr,
                                op_index,
                                storage,
                            )
                        })
                        .map(|state| match state {
                            ReachingAbiState::PreservedEntry => {
                                SourceReturnStackPointerFact::PreservedEntry { storage }
                            }
                            ReachingAbiState::Value(value) => {
                                SourceReturnStackPointerFact::ReachingValue { storage, value }
                            }
                        });
                    complete &= exit_stack_pointer.is_some();
                }
                if let Some(storage) = return_address_storage {
                    return_address = exact_return_address_fact(graph, inst, storage);
                    complete &= return_address.is_some();
                }
                machine_state_complete = return_address.is_some() && exit_stack_pointer.is_some();
            }
            facts.returns.insert(
                inst.id,
                SourceReturnBoundaryFact {
                    at: inst.id,
                    values,
                    return_address,
                    register_compositions,
                    exit_stack_pointer,
                    complete,
                    machine_state_complete,
                },
            );
        }
    }
    facts
}

fn exact_return_address_fact(
    graph: &SsaGraph,
    return_inst: &crate::graph::GraphInst,
    storage: CanonicalStorageId,
) -> Option<SourceReturnAddressFact> {
    let [target_id] = return_inst.inputs.as_slice() else {
        return None;
    };
    let target = graph.value(*target_id)?;
    if target.var.size == storage.size && target.canonical_storage == Some(storage) {
        return Some(SourceReturnAddressFact {
            storage,
            value: target.id,
        });
    }

    // Some exact instruction semantics transport a declared return-address
    // carrier into the architectural control target immediately before the
    // return. Admit only that one-hop, full-width terminal transport. Broader
    // copy chains, casts, phis, partial aliases, and cross-block/non-terminal
    // definitions need distinct proofs.
    let producer = graph.def_inst(target.id).and_then(|id| graph.inst(id))?;
    let [source_id] = producer.inputs.as_slice() else {
        return None;
    };
    let source = graph.value(*source_id)?;
    let InstPayload::Op(SSAOp::Copy { dst, src }) = &producer.payload else {
        return None;
    };
    (producer.block == return_inst.block
        && producer.ordinal.checked_add(1) == Some(return_inst.ordinal)
        && producer.output == Some(target.id)
        && target.var == *dst
        && source.var == *src
        && target.var.size == storage.size
        && source.var.size == storage.size
        && source.canonical_storage == Some(storage))
    .then_some(SourceReturnAddressFact {
        storage,
        value: target.id,
    })
}

fn projected_formal_parameter_storage(
    abi_storage: CanonicalStorageId,
    logical_value: SourceLogicalValue,
    type_graph: &crate::SourceTypeGraph,
) -> Option<CanonicalStorageId> {
    let source_type = type_graph.types().get(logical_value.type_id() as usize)?;
    let carrier = logical_value.carrier();
    let abi_bits = u64::from(abi_storage.size).checked_mul(8)?;
    if abi_storage.space != CanonicalStorageSpace::Register
        || carrier.offset_bits() != 0
        || carrier.size_bits() == 0
        || carrier.size_bits() != source_type.size_bits()
        || !carrier.size_bits().is_multiple_of(8)
    {
        return None;
    }
    match carrier.kind() {
        SourceCarrierKind::Full if carrier.size_bits() == abi_bits => Some(abi_storage),
        SourceCarrierKind::LowBits
            if carrier.size_bits() < abi_bits
                && matches!(
                    source_type.kind(),
                    SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger
                ) =>
        {
            Some(CanonicalStorageId {
                space: abi_storage.space,
                offset: abi_storage.offset,
                size: u32::try_from(carrier.size_bits() / 8).ok()?,
            })
        }
        _ => None,
    }
}

enum ReachingAbiReturnRegister {
    Exact(ValueId),
    Composition(SourceReturnRegisterCompositionFact),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReachingAbiState {
    PreservedEntry,
    Value(ValueId),
}

#[allow(clippy::too_many_arguments)]
fn reaching_abi_return_register_in_block(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine_context: &SourceMachineContext,
    block_addr: u64,
    boundary_op_index: usize,
    slot_index: u32,
    storage: CanonicalStorageId,
    boundary_at: InstId,
) -> Option<ReachingAbiReturnRegister> {
    let block = function.get_block(block_addr)?;
    let mut reverse_overlays = Vec::new();

    for (op_index, op) in block.ops.get(..boundary_op_index)?.iter().enumerate().rev() {
        if matches!(
            op,
            SSAOp::Call { .. }
                | SSAOp::CallInd { .. }
                | SSAOp::CallOther { .. }
                | SSAOp::CallDefine { .. }
                | SSAOp::Return { .. }
        ) {
            return None;
        }
        if op.dst().is_none() {
            continue;
        }
        let producer = graph.inst_id_for_op_site(block_addr, op_index)?;
        let Some(dst_storage) = graph.inst(producer).and_then(|inst| inst.canonical_storage) else {
            continue;
        };
        if !register_storages_overlap(dst_storage, storage) {
            continue;
        }
        let value = graph.inst(producer)?.output?;
        let definition = SourceReturnRegisterDefinitionFact {
            storage: dst_storage,
            value,
            producer,
        };
        if dst_storage == storage {
            if reverse_overlays.is_empty() {
                return Some(ReachingAbiReturnRegister::Exact(value));
            }
            reverse_overlays.reverse();
            let composition = SourceReturnRegisterCompositionFact {
                schema_version: SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION,
                slot: CallBoundarySlot::Register {
                    index: slot_index,
                    storage,
                },
                base: definition,
                overlays: reverse_overlays,
            };
            if !composition.validate(function, graph, machine_context, boundary_at) {
                return None;
            }
            return Some(ReachingAbiReturnRegister::Composition(composition));
        }
        let offset_bytes = contained_register_storage_offset(storage, dst_storage)?;
        reverse_overlays.push(SourceReturnRegisterOverlayFact {
            definition,
            offset_bytes,
        });
    }

    if reverse_overlays.is_empty() {
        reaching_abi_value_in_block(
            function,
            graph,
            machine_context,
            block_addr,
            boundary_op_index,
            storage,
        )
        .map(ReachingAbiReturnRegister::Exact)
    } else {
        None
    }
}

fn reaching_abi_value_in_block(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine_context: &SourceMachineContext,
    block_addr: u64,
    boundary_op_index: usize,
    storage: CanonicalStorageId,
) -> Option<ValueId> {
    reaching_abi_value_in_block_with_policy(
        function,
        graph,
        machine_context,
        block_addr,
        boundary_op_index,
        storage,
        true,
    )
    .and_then(|state| match state {
        ReachingAbiState::PreservedEntry => None,
        ReachingAbiState::Value(value) => Some(value),
    })
}

/// Resolve one call argument carrier, keeping the preserved-entry case.
fn reaching_abi_argument_in_block(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine_context: &SourceMachineContext,
    block_addr: u64,
    boundary_op_index: usize,
    storage: CanonicalStorageId,
) -> Option<SourceCallArgumentValue> {
    reaching_abi_value_in_block_with_policy(
        function,
        graph,
        machine_context,
        block_addr,
        boundary_op_index,
        storage,
        true,
    )
    .map(|state| match state {
        ReachingAbiState::PreservedEntry => SourceCallArgumentValue::PreservedEntry,
        ReachingAbiState::Value(value) => SourceCallArgumentValue::Value(value),
    })
}

fn reaching_preserved_abi_value_in_block(
    function: &SSAFunction,
    graph: &SsaGraph,
    machine_context: &SourceMachineContext,
    block_addr: u64,
    boundary_op_index: usize,
    storage: CanonicalStorageId,
) -> Option<ReachingAbiState> {
    reaching_abi_value_in_block_with_policy(
        function,
        graph,
        machine_context,
        block_addr,
        boundary_op_index,
        storage,
        false,
    )
    .or_else(|| {
        storage_is_untouched_on_all_predecessor_paths(
            function,
            graph,
            block_addr,
            boundary_op_index,
            storage,
        )
        .then_some(ReachingAbiState::PreservedEntry)
    })
}

fn storage_is_untouched_on_all_predecessor_paths(
    function: &SSAFunction,
    graph: &SsaGraph,
    block_addr: u64,
    boundary_op_index: usize,
    storage: CanonicalStorageId,
) -> bool {
    let mut pending = vec![(block_addr, boundary_op_index)];
    let mut visited = BTreeSet::new();
    let mut reached_entry = false;
    while let Some((candidate_addr, end_op_index)) = pending.pop() {
        if !visited.insert(candidate_addr) {
            continue;
        }
        let Some(block) = function.get_block(candidate_addr) else {
            return false;
        };
        let Some(ops) = block.ops.get(..end_op_index) else {
            return false;
        };
        for (op_index, op) in ops.iter().enumerate() {
            if matches!(
                op,
                SSAOp::Call { .. }
                    | SSAOp::CallInd { .. }
                    | SSAOp::CallOther { .. }
                    | SSAOp::CallDefine { .. }
                    | SSAOp::Return { .. }
            ) {
                return false;
            }
            if op.dst().is_none() {
                continue;
            }
            let Some(inst) = graph
                .inst_id_for_op_site(candidate_addr, op_index)
                .and_then(|inst| graph.inst(inst))
            else {
                return false;
            };
            if inst
                .canonical_storage
                .is_some_and(|written| register_storages_overlap(written, storage))
            {
                return false;
            }
        }
        if candidate_addr == function.entry {
            reached_entry = true;
            continue;
        }
        let predecessors = function.predecessors(candidate_addr);
        if predecessors.is_empty() {
            return false;
        }
        pending.extend(predecessors.into_iter().filter_map(|predecessor| {
            function
                .get_block(predecessor)
                .map(|block| (predecessor, block.ops.len()))
        }));
    }
    reached_entry
}

fn reaching_abi_value_in_block_with_policy(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine_context: &SourceMachineContext,
    block_addr: u64,
    boundary_op_index: usize,
    storage: CanonicalStorageId,
    allow_distinct_phi_inputs: bool,
) -> Option<ReachingAbiState> {
    let visited = BTreeSet::new();
    reaching_abi_value_before(
        function,
        graph,
        block_addr,
        boundary_op_index,
        storage,
        &visited,
        allow_distinct_phi_inputs,
    )
}

fn reaching_abi_value_before(
    function: &SSAFunction,
    graph: &SsaGraph,
    block_addr: u64,
    boundary_op_index: usize,
    storage: CanonicalStorageId,
    visited: &BTreeSet<u64>,
    allow_distinct_phi_inputs: bool,
) -> Option<ReachingAbiState> {
    if visited.contains(&block_addr) {
        return None;
    }
    let mut path_visited = visited.clone();
    path_visited.insert(block_addr);
    let block = function.get_block(block_addr)?;
    for (op_index, op) in block.ops.get(..boundary_op_index)?.iter().enumerate().rev() {
        if matches!(
            op,
            SSAOp::Call { .. }
                | SSAOp::CallInd { .. }
                | SSAOp::CallOther { .. }
                | SSAOp::CallDefine { .. }
                | SSAOp::Return { .. }
        ) {
            return None;
        }
        if op.dst().is_none() {
            continue;
        }
        let Some(producer) = graph.inst_id_for_op_site(block_addr, op_index) else {
            continue;
        };
        let Some(dst_storage) = graph.inst(producer).and_then(|inst| inst.canonical_storage) else {
            continue;
        };
        if !register_storages_overlap(dst_storage, storage) {
            continue;
        }
        if dst_storage != storage {
            // A later overlapping slice means an older exact-width definition
            // is not the value at this boundary. Generic boundary recovery has
            // no implicit register-merge semantics, so it must fail closed.
            return None;
        }
        return graph
            .inst(producer)
            .and_then(|inst| inst.output)
            .map(ReachingAbiState::Value);
    }
    let phi_insts = block
        .phis
        .iter()
        .filter(|phi| phi.canonical_storage == Some(storage))
        .filter_map(|phi| graph.value_id_for_var(&phi.dst))
        .filter_map(|value| graph.def_inst(value))
        .collect::<Vec<_>>();
    if let [phi_inst] = phi_insts.as_slice() {
        let phi = graph.inst(*phi_inst)?;
        if allow_distinct_phi_inputs {
            return phi.output.map(ReachingAbiState::Value);
        }
        let [first, rest @ ..] = phi.inputs.as_slice() else {
            return None;
        };
        return rest
            .iter()
            .all(|input| input == first)
            .then_some(ReachingAbiState::Value(*first));
    }
    if !phi_insts.is_empty() {
        return None;
    }
    let predecessors = function.predecessors(block_addr);
    if predecessors.is_empty() {
        let block_id = graph.block_by_addr.get(&block_addr)?;
        if *block_id != graph.entry {
            return None;
        }
        let candidates = graph
            .values
            .iter()
            .filter(|value| {
                graph.def_inst(value.id).is_none()
                    && value.var.version == 0
                    && value.var.size == storage.size
                    && value.canonical_storage == Some(storage)
            })
            .map(|value| value.id)
            .collect::<Vec<_>>();
        return match candidates.as_slice() {
            [value] => Some(ReachingAbiState::Value(*value)),
            [] => Some(ReachingAbiState::PreservedEntry),
            _ => None,
        };
    }
    let values = predecessors
        .iter()
        .map(|predecessor| {
            let predecessor_block = function.get_block(*predecessor)?;
            reaching_abi_value_before(
                function,
                graph,
                *predecessor,
                predecessor_block.ops.len(),
                storage,
                &path_visited,
                allow_distinct_phi_inputs,
            )
        })
        .collect::<Option<Vec<_>>>()?;
    let [first, rest @ ..] = values.as_slice() else {
        return None;
    };
    rest.iter().all(|value| value == first).then_some(*first)
}

fn register_storages_overlap(left: CanonicalStorageId, right: CanonicalStorageId) -> bool {
    if left.space != CanonicalStorageSpace::Register
        || right.space != CanonicalStorageSpace::Register
    {
        return false;
    }
    let Some(left_end) = left.offset.checked_add(u64::from(left.size)) else {
        return true;
    };
    let Some(right_end) = right.offset.checked_add(u64::from(right.size)) else {
        return true;
    };
    left.offset < right_end && right.offset < left_end
}

fn contained_register_storage_offset(
    container: CanonicalStorageId,
    contained: CanonicalStorageId,
) -> Option<u32> {
    if container.space != CanonicalStorageSpace::Register
        || contained.space != CanonicalStorageSpace::Register
        || contained.size == 0
        || contained.size >= container.size
        || contained.offset < container.offset
    {
        return None;
    }
    let container_end = container.offset.checked_add(u64::from(container.size))?;
    let contained_end = contained.offset.checked_add(u64::from(contained.size))?;
    if contained_end > container_end {
        return None;
    }
    u32::try_from(contained.offset.checked_sub(container.offset)?).ok()
}

fn canonical_register_definition(
    function: &SSAFunction,
    graph: &SsaGraph,
    producer: InstId,
) -> Option<(SourceReturnRegisterDefinitionFact, u64, usize)> {
    let (block_addr, op_index) = graph.op_site_for_inst(producer)?;
    let op = function.get_block(block_addr)?.ops.get(op_index)?;
    let dst = op.dst()?;
    let storage = graph.inst(producer)?.canonical_storage?;
    if storage.space != CanonicalStorageSpace::Register || storage.size != dst.size {
        return None;
    }
    let value = graph.inst(producer)?.output?;
    if graph
        .value(value)
        .is_none_or(|graph_value| graph_value.var != *dst)
    {
        return None;
    }
    Some((
        SourceReturnRegisterDefinitionFact {
            storage,
            value,
            producer,
        },
        block_addr,
        op_index,
    ))
}

fn validate_return_register_composition(
    composition: &SourceReturnRegisterCompositionFact,
    function: &SSAFunction,
    graph: &SsaGraph,
    machine_context: &SourceMachineContext,
    boundary_at: InstId,
) -> bool {
    if composition.schema_version != SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION
        || composition.overlays.is_empty()
    {
        return false;
    }
    let CallBoundarySlot::Register {
        index: return_index,
        storage: return_storage,
    } = composition.slot
    else {
        return false;
    };
    if return_storage.space != CanonicalStorageSpace::Register
        || return_storage.size == 0
        || !machine_context.abi_model().is_available()
        || !machine_context.abi_model().is_coherent()
        || machine_context
            .function_interface()
            .is_none_or(|interface| {
                interface.return_kind()
                    != (SourceFunctionReturn::Register {
                        storage: return_storage,
                    })
            })
        || machine_context
            .abi_model()
            .return_registers()
            .iter()
            .filter(|slot| slot.index() == return_index && slot.storage() == return_storage)
            .count()
            != 1
        || machine_context.abi_model().return_registers().len() != 1
    {
        return false;
    }
    let Some((base, block_addr, base_op_index)) =
        canonical_register_definition(function, graph, composition.base.producer)
    else {
        return false;
    };
    if base != composition.base || base.storage != return_storage {
        return false;
    }
    let Some((boundary_block_addr, boundary_op_index)) = graph.op_site_for_inst(boundary_at) else {
        return false;
    };
    if boundary_block_addr != block_addr
        || base_op_index >= boundary_op_index
        || !matches!(
            function
                .get_block(boundary_block_addr)
                .and_then(|block| block.ops.get(boundary_op_index)),
            Some(SSAOp::Return { .. })
        )
    {
        return false;
    }

    let mut expected = Vec::with_capacity(composition.overlays.len().saturating_add(1));
    expected.push(composition.base);
    let mut previous_op_index = base_op_index;
    for overlay in &composition.overlays {
        let Some((definition, overlay_block_addr, op_index)) =
            canonical_register_definition(function, graph, overlay.definition.producer)
        else {
            return false;
        };
        if definition != overlay.definition
            || overlay_block_addr != block_addr
            || op_index <= previous_op_index
            || op_index >= boundary_op_index
            || contained_register_storage_offset(return_storage, definition.storage)
                != Some(overlay.offset_bytes)
        {
            return false;
        }
        previous_op_index = op_index;
        expected.push(definition);
    }

    let Some(block) = function.get_block(block_addr) else {
        return false;
    };
    let mut actual = Vec::new();
    for op_index in base_op_index..boundary_op_index {
        let Some(op) = block.ops.get(op_index) else {
            return false;
        };
        if op_index != base_op_index
            && matches!(
                op,
                SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
            )
        {
            return false;
        }
        if op.dst().is_none() {
            continue;
        }
        let Some(producer) = graph.inst_id_for_op_site(block_addr, op_index) else {
            return false;
        };
        let Some(storage) = graph.inst(producer).and_then(|inst| inst.canonical_storage) else {
            continue;
        };
        if !register_storages_overlap(storage, return_storage) {
            continue;
        }
        let Some((definition, _, _)) = canonical_register_definition(function, graph, producer)
        else {
            return false;
        };
        actual.push(definition);
    }
    actual == expected
}

fn call_result_value_after_call(
    function: &SSAFunction,
    graph: &SsaGraph,
    _machine_context: &SourceMachineContext,
    block_addr: u64,
    call_op_index: usize,
    storage: CanonicalStorageId,
) -> Option<ValueId> {
    let block = function.get_block(block_addr)?;
    let mut candidates = block
        .ops
        .get(call_op_index.checked_add(1)?..)?
        .iter()
        .enumerate()
        .take_while(|(_, op)| matches!(op, SSAOp::CallDefine { .. }))
        .filter_map(|(relative_index, op)| {
            let SSAOp::CallDefine { dst } = op else {
                return None;
            };
            let inst = graph.inst_id_for_op_site(
                block_addr,
                call_op_index
                    .saturating_add(1)
                    .saturating_add(relative_index),
            )?;
            let graph_inst = graph.inst(inst)?;
            if dst.size != storage.size || graph_inst.canonical_storage != Some(storage) {
                return None;
            }
            graph_inst.output
        })
        .collect::<Vec<_>>();
    match candidates.as_mut_slice() {
        [value] => Some(*value),
        _ => None,
    }
}

fn collect_prepared_function_certificates(
    boundaries: &SourceBoundaryFacts,
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    call_sites: &CallSiteFacts,
    structured: &StructuredDataflowFacts,
) -> PreparedFunctionCertificates {
    let loops = structured
        .loops
        .iter()
        .map(|(id, fact)| {
            (
                *id,
                LoopCertificate {
                    proof_node: ProofNodeId::loop_certificate(fact.header, *id),
                    loop_id: *id,
                    header: fact.header,
                    latches: fact.latches.clone(),
                    body: fact.body.clone(),
                    exits: fact.exits.clone(),
                    condition: fact.condition,
                },
            )
        })
        .collect();

    let switches = predicates
        .switches
        .iter()
        .filter(|(_, fact)| !fact.cases.is_empty())
        .map(|(block_addr, fact)| {
            (
                *block_addr,
                SwitchCertificate {
                    proof_node: ProofNodeId::switch_certificate(*block_addr),
                    block_addr: *block_addr,
                    selector: fact.selector,
                    cases: fact.cases.clone(),
                    default: fact.default,
                },
            )
        })
        .collect();

    let if_regions = predicates
        .predicates
        .iter()
        .map(|(id, fact)| {
            (
                *id,
                IfRegionCertificate {
                    predicate: *id,
                    block_addr: fact.block_addr,
                    true_target: fact.true_target,
                    false_target: fact.false_target,
                },
            )
        })
        .collect();

    let renderable_expressions = collect_renderable_expression_values(function, graph, structured);
    let expressions = graph
        .values
        .iter()
        .map(|value| {
            let defining_inst = graph.def_of.get(value.id.0 as usize).and_then(|id| *id);
            let inputs = defining_inst
                .and_then(|inst| graph.inst(inst))
                .map(|inst| inst.inputs.clone())
                .unwrap_or_default();
            (
                value.id,
                ExpressionCertificate {
                    value: value.id,
                    defining_inst,
                    inputs,
                    width: value.var.size,
                    renderable: renderable_expressions.contains(&value.id),
                },
            )
        })
        .collect();

    let mut memory_accesses_by_op = BTreeMap::<(u64, usize, bool), Vec<StructuredAccessId>>::new();
    let memory_accesses = structured
        .memory_accesses
        .iter()
        .map(|(id, fact)| {
            memory_accesses_by_op
                .entry((fact.block_addr, fact.op_index, fact.is_write))
                .or_default()
                .push(*id);
            (
                *id,
                MemoryAccessCertificate {
                    access: *id,
                    block_addr: fact.block_addr,
                    op_index: fact.op_index,
                    space: fact.space,
                    object: fact.object,
                    address: fact.address,
                    value: fact.value,
                    is_write: fact.is_write,
                    width: fact.width,
                },
            )
        })
        .collect();

    let stack_slots = objects
        .objects
        .iter()
        .filter_map(|(object, fact)| match fact.kind {
            ObjectKind::StackSlot {
                space: SpaceId::Ram,
                base,
                offset,
            }
            | ObjectKind::FrameObject {
                space: SpaceId::Ram,
                base,
                offset,
            } => Some((
                *object,
                StackSlotCertificate {
                    object: *object,
                    space: SpaceId::Ram,
                    base,
                    offset,
                    size: None,
                },
            )),
            ObjectKind::StackSlot { .. }
            | ObjectKind::FrameObject { .. }
            | ObjectKind::Global { .. }
            | ObjectKind::Parameter { .. }
            | ObjectKind::HeapAlloc { .. }
            | ObjectKind::EscapedUnknown { .. } => None,
        })
        .collect();

    let mut callsites_by_inst = BTreeMap::new();
    let callsites = call_sites
        .by_id
        .iter()
        .map(|(id, fact)| {
            let (block_addr, op_index) = graph.op_site_for_inst(fact.at).unwrap_or_default();
            let stack_argument_values =
                collect_stack_call_argument_values(function, graph, objects, structured, fact);
            let mut argument_certificates =
                collect_register_call_argument_certificates(function, graph, fact);
            argument_certificates.extend(collect_stack_call_argument_certificates(
                &stack_argument_values,
                structured,
            ));
            callsites_by_inst.insert(fact.at, *id);
            (
                *id,
                CallsiteCertificate {
                    call_site: *id,
                    at: fact.at,
                    block_addr,
                    op_index,
                    target: fact.target,
                    direct_target: fact.direct_target,
                    fallthrough: fact.fallthrough,
                    argument_values: collect_call_argument_values(function, graph, fact),
                    stack_argument_values,
                    argument_certificates,
                },
            )
        })
        .collect();

    let (call_results, call_results_by_inst, call_results_by_callsite) =
        collect_call_result_certificates(
            boundaries, function, graph, objects, call_sites, structured,
        );
    let stack_reloads =
        collect_stack_reload_source_certificates(function, graph, objects, memory, structured);
    let (returns, returns_by_inst) =
        collect_return_value_certificates(boundaries, graph, &stack_reloads);

    PreparedFunctionCertificates {
        loops,
        switches,
        if_regions,
        expressions,
        memory_accesses,
        memory_accesses_by_op,
        stack_slots,
        callsites,
        callsites_by_inst,
        call_results,
        call_results_by_inst,
        call_results_by_callsite,
        stack_reloads,
        returns,
        returns_by_inst,
        failures: Vec::new(),
    }
}

fn collect_renderable_expression_values(
    function: &SSAFunction,
    graph: &SsaGraph,
    structured: &StructuredDataflowFacts,
) -> BTreeSet<ValueId> {
    let certified_memory_read_insts = structured
        .memory_accesses
        .values()
        .filter(|access| !access.is_write && access.width > 0)
        .map(|access| access.id.inst)
        .collect::<BTreeSet<_>>();
    let mut renderable = BTreeSet::new();
    let mut ready = VecDeque::new();

    for value in &graph.values {
        if expression_leaf_is_renderable(value) && renderable.insert(value.id) {
            ready.push_back(value.id);
        }
    }

    let mut eligible = vec![false; graph.insts.len()];
    let mut missing_inputs = vec![0usize; graph.insts.len()];
    for inst in &graph.insts {
        let Some(output) = inst.output else {
            continue;
        };
        if graph.value(output).is_none_or(|value| value.var.size == 0) {
            continue;
        }
        if !expression_inst_is_renderable(function, graph, inst, &certified_memory_read_insts) {
            continue;
        }

        if matches!(&inst.payload, InstPayload::Phi { .. }) {
            renderable.insert(output);
            ready.push_back(output);
        } else if matches!(
            &inst.payload,
            InstPayload::Op(
                SSAOp::Copy { .. }
                    | SSAOp::New { .. }
                    | SSAOp::Subpiece { .. }
                    | SSAOp::Piece { .. }
                    | SSAOp::IntZExt { .. }
                    | SSAOp::IntSExt { .. }
                    | SSAOp::Trunc { .. }
                    | SSAOp::Cast { .. }
            )
        ) {
            let input_renderable = inst.inputs.iter().all(|i| renderable.contains(i));
            if input_renderable {
                renderable.insert(output);
                ready.push_back(output);
            } else {
                eligible[inst.id.0 as usize] = true;
                missing_inputs[inst.id.0 as usize] = inst
                    .inputs
                    .iter()
                    .filter(|input| !renderable.contains(input))
                    .count();
            }
        } else {
            eligible[inst.id.0 as usize] = true;
            missing_inputs[inst.id.0 as usize] = inst
                .inputs
                .iter()
                .filter(|input| !renderable.contains(input))
                .count();
            if missing_inputs[inst.id.0 as usize] == 0 && renderable.insert(output) {
                ready.push_back(output);
            }
        }
    }

    loop {
        while let Some(value) = ready.pop_front() {
            for use_site in graph.use_sites(value) {
                let inst_idx = use_site.inst.0 as usize;
                if !eligible.get(inst_idx).copied().unwrap_or(false)
                    || missing_inputs.get(inst_idx).copied().unwrap_or(0) == 0
                {
                    continue;
                }
                missing_inputs[inst_idx] -= 1;
                if missing_inputs[inst_idx] == 0
                    && let Some(output) = graph.inst(use_site.inst).and_then(|inst| inst.output)
                    && renderable.insert(output)
                {
                    ready.push_back(output);
                }
            }
        }

        let mut added_loop_phi = false;
        for inst in &graph.insts {
            let Some(output) = inst.output else {
                continue;
            };
            if renderable.contains(&output) {
                continue;
            }
            if expression_loop_phi_is_renderable(
                function,
                graph,
                structured,
                inst,
                &renderable,
                &certified_memory_read_insts,
            ) && renderable.insert(output)
            {
                ready.push_back(output);
                added_loop_phi = true;
            }
        }
        if !added_loop_phi {
            break;
        }
    }

    renderable
}

fn expression_leaf_is_renderable(value: &crate::graph::GraphValue) -> bool {
    value.var.size > 0
        && (value.var.constant_bits().is_some()
            || (value.var.version == 0
                && matches!(
                    value.canonical_storage,
                    Some(CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        ..
                    })
                )))
}

fn expression_inst_is_renderable(
    _function: &SSAFunction,
    _graph: &SsaGraph,
    inst: &crate::graph::GraphInst,
    certified_memory_read_insts: &BTreeSet<InstId>,
) -> bool {
    match &inst.payload {
        InstPayload::Phi { .. } => true,
        InstPayload::Op(op) => {
            expression_op_is_pure(op)
                || (op.is_memory_read() && certified_memory_read_insts.contains(&inst.id))
        }
    }
}

fn expression_phi_is_identity_renderable(graph: &SsaGraph, inst: &crate::graph::GraphInst) -> bool {
    let Some(first) = inst.inputs.first() else {
        return false;
    };
    expression_phi_is_identity(inst) && !expression_value_depends_on_memory_read(graph, *first)
}

fn expression_phi_is_identity(inst: &crate::graph::GraphInst) -> bool {
    let Some(first) = inst.inputs.first() else {
        return false;
    };
    inst.inputs.iter().all(|input| input == first)
}

fn expression_phi_is_renderable(
    function: &SSAFunction,
    graph: &SsaGraph,
    inst: &crate::graph::GraphInst,
) -> bool {
    expression_phi_is_identity_renderable(graph, inst)
        || expression_phi_has_single_canonical_root(function, graph, inst)
}

fn expression_phi_has_single_canonical_root(
    function: &SSAFunction,
    graph: &SsaGraph,
    inst: &crate::graph::GraphInst,
) -> bool {
    let Some(prep_facts) = function.decompile_prep_facts() else {
        return false;
    };
    let mut roots = inst.inputs.iter().filter_map(|input| {
        let var = graph.value(*input).map(|value| &value.var)?;
        let root = prep_facts.canonical_root_of(var).unwrap_or(var);
        graph.value_id_for_var(root).or(Some(*input))
    });
    let Some(first) = roots.next() else {
        return false;
    };
    if expression_value_depends_on_memory_read(graph, first) {
        return false;
    }
    roots.all(|root| root == first)
}

fn expression_value_depends_on_memory_read(graph: &SsaGraph, value: ValueId) -> bool {
    let mut stack = vec![(value, 0usize)];
    let mut visited = BTreeSet::new();

    while let Some((current, depth)) = stack.pop() {
        if depth >= 32 || !visited.insert(current) {
            continue;
        }
        let Some(inst) = graph
            .def_inst(current)
            .and_then(|inst_id| graph.inst(inst_id))
        else {
            continue;
        };
        if matches!(&inst.payload, InstPayload::Op(op) if op.is_memory_read()) {
            return true;
        }
        stack.extend(inst.inputs.iter().map(|input| (*input, depth + 1)));
    }

    false
}

fn expression_loop_phi_is_renderable(
    function: &SSAFunction,
    graph: &SsaGraph,
    structured: &StructuredDataflowFacts,
    inst: &crate::graph::GraphInst,
    renderable: &BTreeSet<ValueId>,
    certified_memory_read_insts: &BTreeSet<InstId>,
) -> bool {
    let InstPayload::Phi { predecessors } = &inst.payload else {
        return false;
    };
    let Some(output) = inst.output else {
        return false;
    };
    let Some(header) = graph.block(inst.block).map(|block| block.addr) else {
        return false;
    };
    let Some(loop_fact) = structured.loops.values().find(|fact| fact.header == header) else {
        return false;
    };
    if inst.inputs.len() != predecessors.len() {
        return false;
    }

    let latches = loop_fact.latches.iter().copied().collect::<BTreeSet<_>>();
    let env = ExpressionRenderEnv {
        function,
        graph,
        certified_memory_read_insts,
    };
    let mut saw_entry = false;
    let mut saw_backedge = false;
    for (pred_id, input) in predecessors.iter().zip(inst.inputs.iter().copied()) {
        let Some(pred_addr) = graph.block(*pred_id).map(|block| block.addr) else {
            return false;
        };
        if latches.contains(&pred_addr) {
            saw_backedge = true;
            let mut visited = BTreeSet::new();
            if !value_renderable_modulo_loop_phi(&env, input, output, renderable, &mut visited, 0) {
                return false;
            }
        } else {
            saw_entry = true;
            if !renderable.contains(&input) {
                return false;
            }
        }
    }

    saw_entry && saw_backedge
}

struct ExpressionRenderEnv<'a> {
    function: &'a SSAFunction,
    graph: &'a SsaGraph,
    certified_memory_read_insts: &'a BTreeSet<InstId>,
}

fn value_renderable_modulo_loop_phi(
    env: &ExpressionRenderEnv<'_>,
    value: ValueId,
    loop_phi: ValueId,
    renderable: &BTreeSet<ValueId>,
    visited: &mut BTreeSet<ValueId>,
    depth: usize,
) -> bool {
    if value == loop_phi || renderable.contains(&value) {
        return true;
    }
    if depth >= 32 || !visited.insert(value) {
        return false;
    }

    let result = env
        .graph
        .def_inst(value)
        .and_then(|inst_id| env.graph.inst(inst_id))
        .is_some_and(|inst| {
            let eligible = match &inst.payload {
                InstPayload::Phi { .. } => {
                    expression_phi_is_renderable(env.function, env.graph, inst)
                }
                InstPayload::Op(op) => {
                    expression_op_is_pure(op)
                        || (op.is_memory_read()
                            && env.certified_memory_read_insts.contains(&inst.id))
                }
            };
            eligible
                && inst.inputs.iter().all(|input| {
                    value_renderable_modulo_loop_phi(
                        env,
                        *input,
                        loop_phi,
                        renderable,
                        visited,
                        depth + 1,
                    )
                })
        });

    visited.remove(&value);
    result
}

fn expression_op_is_pure(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Copy { .. }
            | SSAOp::IntAdd { .. }
            | SSAOp::IntSub { .. }
            | SSAOp::IntMult { .. }
            | SSAOp::IntDiv { .. }
            | SSAOp::IntSDiv { .. }
            | SSAOp::IntRem { .. }
            | SSAOp::IntSRem { .. }
            | SSAOp::IntNegate { .. }
            | SSAOp::IntCarry { .. }
            | SSAOp::IntSCarry { .. }
            | SSAOp::IntSBorrow { .. }
            | SSAOp::IntAnd { .. }
            | SSAOp::IntOr { .. }
            | SSAOp::IntXor { .. }
            | SSAOp::IntNot { .. }
            | SSAOp::IntLeft { .. }
            | SSAOp::IntRight { .. }
            | SSAOp::IntSRight { .. }
            | SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLessEqual { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::BoolNot { .. }
            | SSAOp::BoolAnd { .. }
            | SSAOp::BoolOr { .. }
            | SSAOp::BoolXor { .. }
            | SSAOp::Piece { .. }
            | SSAOp::Subpiece { .. }
            | SSAOp::PopCount { .. }
            | SSAOp::Lzcount { .. }
            | SSAOp::FloatAdd { .. }
            | SSAOp::FloatSub { .. }
            | SSAOp::FloatMult { .. }
            | SSAOp::FloatDiv { .. }
            | SSAOp::FloatNeg { .. }
            | SSAOp::FloatAbs { .. }
            | SSAOp::FloatSqrt { .. }
            | SSAOp::FloatCeil { .. }
            | SSAOp::FloatFloor { .. }
            | SSAOp::FloatRound { .. }
            | SSAOp::FloatNaN { .. }
            | SSAOp::FloatEqual { .. }
            | SSAOp::FloatNotEqual { .. }
            | SSAOp::FloatLess { .. }
            | SSAOp::FloatLessEqual { .. }
            | SSAOp::Int2Float { .. }
            | SSAOp::Float2Int { .. }
            | SSAOp::FloatFloat { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::PtrAdd { .. }
            | SSAOp::PtrSub { .. }
            | SSAOp::SegmentOp { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Extract { .. }
            | SSAOp::Insert { .. }
            | SSAOp::Select { .. }
    )
}

fn collect_return_value_certificates(
    boundaries: &SourceBoundaryFacts,
    graph: &SsaGraph,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
) -> (Vec<ReturnValueCertificate>, BTreeMap<InstId, usize>) {
    let mut returns = Vec::new();
    let mut returns_by_inst = BTreeMap::new();

    for (boundary_at, boundary) in &boundaries.returns {
        if boundary.at != *boundary_at
            || !boundary.complete
            || !boundary.register_compositions.is_empty()
        {
            continue;
        }
        let [boundary_value] = boundary.values.as_slice() else {
            // A complete void boundary is authoritative, but it owns no value.
            continue;
        };
        let Some((block_addr, op_index)) = graph.op_site_for_inst(boundary.at) else {
            continue;
        };
        let Some(inst) = graph.inst(boundary.at) else {
            continue;
        };
        if !matches!(inst.payload, InstPayload::Op(SSAOp::Return { .. })) {
            continue;
        }
        let Some(value) = graph.value(boundary_value.value) else {
            continue;
        };
        let carrier = return_carrier_for_boundary_value(boundary_value, stack_reloads);
        returns_by_inst.insert(boundary.at, returns.len());
        returns.push(ReturnValueCertificate {
            at: boundary.at,
            block_addr,
            op_index,
            value: boundary_value.value,
            width: value.var.size,
            carrier,
        });
    }

    (returns, returns_by_inst)
}

fn return_carrier_for_boundary_value(
    boundary: &CallBoundaryValueFact,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
) -> Option<ReturnCarrier> {
    match boundary.slot {
        CallBoundarySlot::Register { .. } => return_carrier_for_boundary_slot(boundary.slot),
        CallBoundarySlot::Stack(offset) => {
            let reload = stack_reloads.get(&boundary.value)?;
            (reload.offset == offset).then_some(ReturnCarrier::StackSlot {
                object: reload.object,
                offset: reload.offset,
                memory_access: Some(reload.load_access),
            })
        }
    }
}

fn ram_memory_access_matches_source(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    access: &StructuredMemoryAccessFact,
) -> bool {
    if access.space != SpaceId::Ram
        || !access.provenance_complete
        || access.id.ordinal != 0
        || graph.op_site_for_inst(access.id.inst) != Some((access.block_addr, access.op_index))
        || objects.object_for_value(access.address, SpaceId::Ram) != Some(access.object)
        || objects
            .object(access.object)
            .is_none_or(|object| object.kind.space() != SpaceId::Ram)
    {
        return false;
    }
    let Some(graph_inst) = graph.inst(access.id.inst) else {
        return false;
    };
    let Some(prepared_op) = function
        .get_block(access.block_addr)
        .and_then(|block| block.ops.get(access.op_index))
    else {
        return false;
    };
    let InstPayload::Op(graph_op) = &graph_inst.payload else {
        return false;
    };
    if graph_op != prepared_op {
        return false;
    }
    match graph_op {
        SSAOp::Load {
            space: SpaceId::Ram,
            dst,
            addr,
        } => {
            !access.is_write
                && graph.value_id_for_var(addr) == Some(access.address)
                && graph.value_id_for_var(dst) == access.value
                && access.width == dst.size
        }
        SSAOp::Store {
            space: SpaceId::Ram,
            addr,
            val,
        } => {
            access.is_write
                && graph.value_id_for_var(addr) == Some(access.address)
                && graph.value_id_for_var(val) == access.value
                && access.width == val.size
        }
        _ => false,
    }
}

fn collect_stack_reload_source_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    structured: &StructuredDataflowFacts,
) -> BTreeMap<ValueId, StackReloadSourceCertificate> {
    let store_sources = collect_stack_store_sources(function, graph, objects, memory, structured);
    let mut certificates = BTreeMap::new();
    let mut ready = VecDeque::new();

    for access in structured.memory_accesses.values().filter(|access| {
        !access.is_write && ram_memory_access_matches_source(function, graph, objects, access)
    }) {
        let Some(value) = access.value else {
            continue;
        };
        let Some((base, offset)) = stack_object_root(objects, access.object) else {
            continue;
        };
        let Some(use_fact) = unique_memory_use_for_access(memory, access) else {
            continue;
        };
        let Some(source) = store_sources.get(&use_fact.version) else {
            continue;
        };
        if source.object != access.object || source.memory_width != access.width {
            continue;
        }
        let cert = StackReloadSourceCertificate {
            value,
            reload: value,
            source: source.value,
            canonical_source: source.canonical_source,
            object: access.object,
            base,
            offset,
            value_width: graph
                .value(value)
                .map(|value| value.var.size)
                .unwrap_or(access.width),
            memory_width: access.width,
            store_access: source.access,
            load_access: access.id,
            store_inst: source.access.inst,
            load_inst: access.id.inst,
        };
        insert_stack_reload_source_certificate(&mut certificates, &mut ready, cert);
    }

    while let Some(value) = ready.pop_front() {
        let Some(cert) = certificates.get(&value).cloned() else {
            continue;
        };
        for use_site in graph.use_sites(value) {
            let Some(inst) = graph.inst(use_site.inst) else {
                continue;
            };
            let Some(output) = stack_reload_propagation_output(inst, value) else {
                continue;
            };
            if certificates.contains_key(&output) {
                continue;
            }
            let value_width = graph
                .value(output)
                .map(|value| value.var.size)
                .unwrap_or(cert.value_width);
            insert_stack_reload_source_certificate(
                &mut certificates,
                &mut ready,
                StackReloadSourceCertificate {
                    value: output,
                    value_width,
                    ..cert.clone()
                },
            );
        }
    }

    certificates
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct StackStoreSource {
    value: ValueId,
    canonical_source: ValueId,
    object: ObjectId,
    memory_width: u32,
    access: StructuredAccessId,
}

fn collect_stack_store_sources(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    structured: &StructuredDataflowFacts,
) -> BTreeMap<MemoryVersion, StackStoreSource> {
    let mut sources = BTreeMap::new();
    for access in structured.memory_accesses.values().filter(|access| {
        access.is_write && ram_memory_access_matches_source(function, graph, objects, access)
    }) {
        let Some(value) = access.value else {
            continue;
        };
        if stack_object_root(objects, access.object).is_none() {
            continue;
        }
        let Some(def_fact) = unique_memory_def_for_access(memory, access) else {
            continue;
        };
        sources.insert(
            def_fact.next_version,
            StackStoreSource {
                value,
                canonical_source: canonical_stack_source_value(function, graph, value),
                object: access.object,
                memory_width: access.width,
                access: access.id,
            },
        );
    }
    sources
}

fn insert_stack_reload_source_certificate(
    certificates: &mut BTreeMap<ValueId, StackReloadSourceCertificate>,
    ready: &mut VecDeque<ValueId>,
    cert: StackReloadSourceCertificate,
) {
    let value = cert.value;
    if certificates.contains_key(&value) {
        return;
    }
    certificates.insert(value, cert);
    ready.push_back(value);
}

fn stack_reload_propagation_output(
    inst: &crate::graph::GraphInst,
    source: ValueId,
) -> Option<ValueId> {
    let output = inst.output?;
    match &inst.payload {
        InstPayload::Op(
            SSAOp::Copy { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Subpiece { .. },
        ) if inst.inputs.len() == 1 && inst.inputs.first().copied() == Some(source) => Some(output),
        InstPayload::Phi { .. } if expression_phi_is_identity(inst) => {
            (inst.inputs.first().copied() == Some(source)).then_some(output)
        }
        _ => None,
    }
}

fn unique_memory_def_for_access<'a>(
    memory: &'a MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<&'a MemoryDefFact> {
    let mut matches = memory
        .defs_by_inst
        .get(&access.id.inst)
        .into_iter()
        .flatten()
        .filter(|def| {
            def.location.space == access.space
                && def.location.object == access.object
                && def.location.size == access.width
        });
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn unique_memory_use_for_access<'a>(
    memory: &'a MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<&'a MemoryUseFact> {
    let mut matches = memory
        .uses_by_inst
        .get(&access.id.inst)
        .into_iter()
        .flatten()
        .filter(|use_fact| {
            use_fact.location.space == access.space
                && use_fact.location.object == access.object
                && use_fact.location.size == access.width
        });
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn canonical_stack_source_value(
    function: &SSAFunction,
    graph: &SsaGraph,
    source: ValueId,
) -> ValueId {
    let Some(var) = graph.value(source).map(|value| &value.var) else {
        return source;
    };
    let root = canonical_value_root(function.decompile_prep_facts(), var);
    graph.value_id_for_var(root).unwrap_or(source)
}

type CallResultCertificateIndexes = (
    BTreeMap<ValueId, CallResultCertificate>,
    BTreeMap<InstId, ValueId>,
    BTreeMap<CallSiteId, Vec<ValueId>>,
);

fn collect_call_result_certificates(
    boundaries: &SourceBoundaryFacts,
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    call_sites: &CallSiteFacts,
    structured: &StructuredDataflowFacts,
) -> CallResultCertificateIndexes {
    let mut call_results = BTreeMap::new();
    let mut call_results_by_inst = BTreeMap::new();
    let mut call_results_by_callsite = BTreeMap::<CallSiteId, Vec<ValueId>>::new();
    let callsites_by_op = call_sites
        .by_id
        .iter()
        .filter_map(|(id, fact)| graph.op_site_for_inst(fact.at).map(|site| (site, *id)))
        .collect::<BTreeMap<_, _>>();
    let mut out_states = BTreeMap::<u64, CallResultFlowState>::new();
    let mut worklist = function
        .blocks()
        .map(|block| block.addr)
        .collect::<VecDeque<_>>();
    let mut queued = function
        .blocks()
        .map(|block| block.addr)
        .collect::<BTreeSet<_>>();

    while let Some(block_addr) = worklist.pop_front() {
        queued.remove(&block_addr);
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let input = merge_call_result_flow_predecessors(function, &out_states, block_addr);
        let output = process_call_result_flow_block(
            boundaries,
            function,
            block,
            graph,
            objects,
            call_sites,
            structured,
            &callsites_by_op,
            input,
            &mut call_results,
            &mut call_results_by_inst,
            &mut call_results_by_callsite,
        );
        if out_states.get(&block_addr) == Some(&output) {
            continue;
        }
        out_states.insert(block_addr, output);
        for succ in function.successors(block_addr) {
            if queued.insert(succ) {
                worklist.push_back(succ);
            }
        }
    }

    for values in call_results_by_callsite.values_mut() {
        values.sort_unstable();
        values.dedup();
    }

    (call_results, call_results_by_inst, call_results_by_callsite)
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct CallResultFlowState {
    tracked: BTreeMap<ValueId, CallResultCertificate>,
    stack_owners: BTreeMap<(ObjectId, i64), CallResultCertificate>,
}

fn merge_call_result_flow_predecessors(
    function: &SSAFunction,
    out_states: &BTreeMap<u64, CallResultFlowState>,
    block_addr: u64,
) -> CallResultFlowState {
    let preds = function.predecessors(block_addr);
    let Some((first, rest)) = preds.split_first() else {
        return CallResultFlowState::default();
    };
    let mut merged = out_states.get(first).cloned().unwrap_or_default();
    for pred in rest {
        let pred_state = out_states.get(pred).cloned().unwrap_or_default();
        merged
            .tracked
            .retain(|value, cert| pred_state.tracked.get(value) == Some(cert));
        merged
            .stack_owners
            .retain(|slot, cert| pred_state.stack_owners.get(slot) == Some(cert));
    }
    merged
}

#[allow(clippy::too_many_arguments)]
fn process_call_result_flow_block(
    boundaries: &SourceBoundaryFacts,
    function: &SSAFunction,
    block: &crate::FunctionSSABlock,
    graph: &SsaGraph,
    objects: &ObjectModel,
    call_sites: &CallSiteFacts,
    structured: &StructuredDataflowFacts,
    callsites_by_op: &BTreeMap<(u64, usize), CallSiteId>,
    mut state: CallResultFlowState,
    call_results: &mut BTreeMap<ValueId, CallResultCertificate>,
    call_results_by_inst: &mut BTreeMap<InstId, ValueId>,
    call_results_by_callsite: &mut BTreeMap<CallSiteId, Vec<ValueId>>,
) -> CallResultFlowState {
    let mut active_call = None;
    for (op_index, op) in block.ops.iter().enumerate() {
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                kill_return_register_flow_values(&mut state);
                active_call = callsites_by_op.get(&(block.addr, op_index)).copied();
            }
            SSAOp::CallDefine { dst } => {
                let Some(call_site_id) = active_call else {
                    continue;
                };
                let Some(call_site) = call_sites.by_id.get(&call_site_id) else {
                    continue;
                };
                let Some(value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let Some(boundary) = boundaries
                    .calls
                    .get(&call_site_id)
                    .filter(|boundary| boundary.complete)
                else {
                    continue;
                };
                let mut exact_results = boundary
                    .results
                    .iter()
                    .filter(|result| result.value == value);
                let Some(result) = exact_results.next() else {
                    continue;
                };
                if exact_results.next().is_some() {
                    continue;
                }
                let Some(carrier) = return_carrier_for_boundary_slot(result.slot) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: call_site_id,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(call_site.at),
                    block_addr: block.addr,
                    op_index,
                    value,
                    width: dst.size,
                    relation: CallResultValueRelation::Identity,
                    carrier,
                    owner: Some(ValueOwner::Value(value)),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            SSAOp::Copy { dst, src } => {
                let Some(src_value) = graph.value_id_for_var(src) else {
                    continue;
                };
                let Some(source) = state.tracked.get(&src_value) else {
                    continue;
                };
                let Some(dst_value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: source.call_site,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(source.at),
                    block_addr: block.addr,
                    op_index,
                    value: dst_value,
                    width: dst.size,
                    relation: source.relation,
                    carrier: source.carrier.clone(),
                    owner: source.owner.clone().or(Some(ValueOwner::Value(src_value))),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src, .. }
            | SSAOp::Subpiece { dst, src, .. } => {
                let Some(src_value) = graph.value_id_for_var(src) else {
                    continue;
                };
                let Some(source) = state.tracked.get(&src_value) else {
                    continue;
                };
                let Some(dst_value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: source.call_site,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(source.at),
                    block_addr: block.addr,
                    op_index,
                    value: dst_value,
                    width: dst.size,
                    relation: CallResultValueRelation::Derived,
                    carrier: source.carrier.clone(),
                    owner: source.owner.clone().or(Some(ValueOwner::Value(src_value))),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            SSAOp::Store {
                space: SpaceId::Ram,
                val,
                ..
            } => {
                let value = graph.value_id_for_var(val);
                let stack_access = value
                    .and_then(|value| {
                        stack_memory_access_at(StackMemoryAccessInput {
                            function,
                            graph,
                            structured,
                            objects,
                            block_addr: block.addr,
                            op_index,
                            is_write: true,
                            value: Some(value),
                        })
                    })
                    .or_else(|| {
                        stack_memory_access_at(StackMemoryAccessInput {
                            function,
                            graph,
                            structured,
                            objects,
                            block_addr: block.addr,
                            op_index,
                            is_write: true,
                            value: None,
                        })
                    });
                let Some((object, offset, _access)) = stack_access else {
                    continue;
                };
                let Some(value) = value else {
                    state.stack_owners.remove(&(object, offset));
                    continue;
                };
                let Some(source) = state.tracked.get(&value).cloned() else {
                    state.stack_owners.remove(&(object, offset));
                    continue;
                };
                state.stack_owners.insert(
                    (object, offset),
                    CallResultCertificate {
                        owner: Some(ValueOwner::StackSlot { object, offset }),
                        ..source.clone()
                    },
                );
                call_results.entry(value).and_modify(|cert| {
                    cert.owner = Some(ValueOwner::StackSlot { object, offset });
                });
                state.tracked.entry(value).and_modify(|cert| {
                    cert.owner = Some(ValueOwner::StackSlot { object, offset });
                });
            }
            SSAOp::Load {
                space: SpaceId::Ram,
                dst,
                ..
            } => {
                let Some(dst_value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let Some((object, offset, access)) =
                    stack_memory_access_at(StackMemoryAccessInput {
                        function,
                        graph,
                        structured,
                        objects,
                        block_addr: block.addr,
                        op_index,
                        is_write: false,
                        value: Some(dst_value),
                    })
                else {
                    continue;
                };
                let Some(source) = state.stack_owners.get(&(object, offset)) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: source.call_site,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(source.at),
                    block_addr: block.addr,
                    op_index,
                    value: dst_value,
                    width: dst.size,
                    relation: source.relation,
                    carrier: ReturnCarrier::StackSlot {
                        object,
                        offset,
                        memory_access: Some(access),
                    },
                    owner: Some(ValueOwner::StackSlot { object, offset }),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            _ => {}
        }
    }
    state
}

fn kill_return_register_flow_values(state: &mut CallResultFlowState) {
    state
        .tracked
        .retain(|_, certificate| !matches!(certificate.carrier, ReturnCarrier::Register { .. }));
}

fn insert_call_result_certificate(
    call_results: &mut BTreeMap<ValueId, CallResultCertificate>,
    call_results_by_inst: &mut BTreeMap<InstId, ValueId>,
    call_results_by_callsite: &mut BTreeMap<CallSiteId, Vec<ValueId>>,
    tracked: &mut BTreeMap<ValueId, CallResultCertificate>,
    cert: CallResultCertificate,
) {
    call_results_by_inst.insert(cert.at, cert.value);
    call_results_by_callsite
        .entry(cert.call_site)
        .or_default()
        .push(cert.value);
    tracked.insert(cert.value, cert.clone());
    call_results.insert(cert.value, cert);
}

struct StackMemoryAccessInput<'a> {
    function: &'a SSAFunction,
    graph: &'a SsaGraph,
    structured: &'a StructuredDataflowFacts,
    objects: &'a ObjectModel,
    block_addr: u64,
    op_index: usize,
    is_write: bool,
    value: Option<ValueId>,
}

fn stack_memory_access_at(
    input: StackMemoryAccessInput<'_>,
) -> Option<(ObjectId, i64, StructuredAccessId)> {
    input
        .structured
        .memory_accesses
        .iter()
        .filter(|(_, access)| {
            access.block_addr == input.block_addr
                && access.op_index == input.op_index
                && access.is_write == input.is_write
                && input.value.is_none_or(|value| access.value == Some(value))
                && ram_memory_access_matches_source(
                    input.function,
                    input.graph,
                    input.objects,
                    access,
                )
        })
        .filter_map(|(access_id, access)| {
            stack_object_offset(input.objects, access.object)
                .map(|offset| (access.object, offset, *access_id))
        })
        .next()
}

fn return_carrier_for_boundary_slot(slot: CallBoundarySlot) -> Option<ReturnCarrier> {
    match slot {
        CallBoundarySlot::Register { storage, .. } => Some(ReturnCarrier::Register { storage }),
        CallBoundarySlot::Stack(_) => None,
    }
}

fn collect_structured_loop_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    live_out: &crate::liveout::FunctionLiveOut,
    storage_spans: &StorageSpans,
    machine_context: Option<&SourceMachineContext>,
) -> BTreeMap<LoopId, StructuredLoopFact> {
    let mut latches_by_header = BTreeMap::<u64, BTreeSet<u64>>::new();
    for &block_addr in function.block_addrs() {
        for succ in function.successors(block_addr) {
            if function.dominates(succ, block_addr) {
                latches_by_header
                    .entry(succ)
                    .or_default()
                    .insert(block_addr);
            }
        }
    }

    let mut loops = BTreeMap::new();
    for (idx, (header, latches)) in latches_by_header.into_iter().enumerate() {
        let id = LoopId(idx as u32);
        let body_set = natural_loop_body(function, header, &latches);
        let body = body_set.iter().copied().collect::<Vec<_>>();
        let exits = loop_exits(function, &body_set);
        let condition = loop_condition(predicates, header, &body_set, &exits);
        let carriers = loop_carrier_facts(
            function,
            graph,
            id,
            header,
            &latches,
            &body_set,
            live_out,
            storage_spans,
            machine_context,
        );
        let (induction_phi, induction_init, induction_update) =
            loop_induction_values(graph, predicates, condition, header, &latches, &body_set);
        let bound = loop_bound_value(
            graph,
            predicates,
            condition,
            induction_phi,
            induction_update,
        );
        loops.insert(
            id,
            StructuredLoopFact {
                id,
                kind: if latches.contains(&header) {
                    StructuredLoopKind::SelfLoop
                } else {
                    StructuredLoopKind::Natural
                },
                header,
                latches: latches.iter().copied().collect(),
                body,
                exits,
                condition,
                carriers,
                induction_phi,
                induction_init,
                induction_update,
                bound,
            },
        );
    }
    loops
}

fn collect_unstructured_cycle_blocks(
    graph: &SsaGraph,
    loops: &BTreeMap<LoopId, StructuredLoopFact>,
) -> BTreeSet<u64> {
    let covered = loops
        .values()
        .flat_map(|loop_fact| loop_fact.body.iter().copied())
        .collect::<BTreeSet<_>>();
    graph
        .blocks
        .iter()
        .filter(|block| !covered.contains(&block.addr))
        .filter(|block| {
            let mut visited = BTreeSet::new();
            let mut pending = block.successors.clone();
            while let Some(candidate) = pending.pop() {
                if candidate == block.id {
                    return true;
                }
                if !visited.insert(candidate) {
                    continue;
                }
                if let Some(candidate) = graph.block(candidate) {
                    pending.extend(candidate.successors.iter().copied());
                }
            }
            false
        })
        .map(|block| block.addr)
        .collect()
}

fn loop_carrier_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    loop_id: LoopId,
    header: u64,
    latches: &BTreeSet<u64>,
    loop_body: &BTreeSet<u64>,
    live_out: &crate::liveout::FunctionLiveOut,
    storage_spans: &StorageSpans,
    machine_context: Option<&SourceMachineContext>,
) -> Vec<LoopCarrierFact> {
    let Some(header_block) = function.get_block(header) else {
        return Vec::new();
    };
    let mut carriers = header_block
        .phis
        .iter()
        .filter_map(|phi| {
            let phi_value = graph.value_id_for_var(&phi.dst)?;
            let phi_inst = graph.def_inst(phi_value)?;
            // Pruned SSA is not guaranteed at this seam. A loop-local output
            // can induce a syntactic header phi whose value is never read;
            // such a dead merge carries no live state and must not acquire a
            // preservation obligation. Being read includes being read by the
            // caller, which the use list alone cannot see: a function's result
            // has no reader anywhere inside it.
            if !crate::liveout::is_read(graph, live_out, phi_value) {
                return None;
            }
            let mut entries = Vec::new();
            let mut updates = Vec::new();
            for (input_idx, (predecessor, source)) in phi.sources.iter().enumerate() {
                let edge = LoopCarrierEdgeValue {
                    predecessor: *predecessor,
                    value: graph.value_id_for_var(source)?,
                    site: UseSite {
                        inst: phi_inst,
                        input_idx,
                    },
                };
                if !edge.validate(graph) {
                    return None;
                }
                if latches.contains(predecessor) {
                    updates.push(LoopCarrierUpdateFact {
                        predecessor: edge.predecessor,
                        value: edge.value,
                        site: edge.site,
                        identity_values: exact_copy_identity_values(graph, edge.value),
                    });
                } else {
                    entries.push(edge);
                }
            }
            if entries.is_empty() || updates.is_empty() {
                return None;
            }
            entries.sort_unstable();
            entries.dedup();
            updates.sort_unstable();
            updates.dedup();
            Some(LoopCarrierFact {
                id: SemanticId::loop_carrier(phi_value),
                loop_id,
                header,
                phi: phi_value,
                width: phi.dst.size,
                identity_values: BTreeSet::from([phi_value]),
                entries,
                updates,
                dominating_initializers: Vec::new(),
                members: Vec::new(),
            })
        })
        .collect::<Vec<_>>();

    // A post-loop phi such as `result = phi(init, update)` denotes the same
    // mutable carrier after structured control flow. Resolve the transitive
    // relation through a sorted worklist: every phi edge is reconsidered only
    // when a newly certified output can change its answer.
    let mut owners_by_value = BTreeMap::<ValueId, BTreeSet<usize>>::new();
    let mut continuing_owners_by_value = BTreeMap::<ValueId, BTreeSet<usize>>::new();
    for (carrier_index, carrier) in carriers.iter().enumerate() {
        for value in carrier
            .identity_values
            .iter()
            .copied()
            .chain(carrier.entries.iter().map(|edge| edge.value))
            .chain(carrier.updates.iter().flat_map(|update| {
                std::iter::once(update.value).chain(update.identity_values.iter().copied())
            }))
        {
            owners_by_value
                .entry(value)
                .or_default()
                .insert(carrier_index);
        }
        for value in carrier
            .identity_values
            .iter()
            .copied()
            .chain(carrier.updates.iter().flat_map(|update| {
                std::iter::once(update.value).chain(update.identity_values.iter().copied())
            }))
        {
            continuing_owners_by_value
                .entry(value)
                .or_default()
                .insert(carrier_index);
        }
    }
    let mut pending = graph
        .insts
        .iter()
        .filter(|inst| {
            matches!(inst.payload, InstPayload::Phi { .. })
                && graph
                    .block(inst.block)
                    .is_some_and(|block| block.addr != header)
        })
        .map(|inst| inst.id)
        .collect::<BTreeSet<_>>();
    while let Some(phi_inst) = pending.pop_first() {
        let Some(inst) = graph.inst(phi_inst) else {
            continue;
        };
        let InstPayload::Phi { predecessors } = &inst.payload else {
            continue;
        };
        let Some(output) = inst.output else {
            continue;
        };
        if owners_by_value.contains_key(&output)
            || predecessors.len() != inst.inputs.len()
            || inst.inputs.is_empty()
            || inst.inputs.iter().copied().collect::<BTreeSet<_>>().len() != inst.inputs.len()
        {
            continue;
        }
        let Some(mut candidate_owners) = inst
            .inputs
            .first()
            .and_then(|input| owners_by_value.get(input))
            .cloned()
        else {
            continue;
        };
        for input in inst.inputs.iter().skip(1) {
            let Some(input_owners) = owners_by_value.get(input) else {
                candidate_owners.clear();
                break;
            };
            candidate_owners.retain(|owner| input_owners.contains(owner));
        }
        candidate_owners.retain(|owner| {
            inst.inputs.iter().any(|input| {
                continuing_owners_by_value
                    .get(input)
                    .is_some_and(|owners| owners.contains(owner))
            })
        });
        if candidate_owners.len() != 1 {
            continue;
        }
        let carrier_index = *candidate_owners
            .first()
            .expect("one exact carrier owner remains");
        let source_edges = predecessors
            .iter()
            .copied()
            .zip(inst.inputs.iter().copied())
            .enumerate()
            .filter_map(|(input_idx, (predecessor, value))| {
                let edge = LoopCarrierEdgeValue {
                    predecessor: graph.block(predecessor)?.addr,
                    value,
                    site: UseSite {
                        inst: phi_inst,
                        input_idx,
                    },
                };
                edge.validate(graph).then_some(edge)
            })
            .collect::<Vec<_>>();
        if source_edges.len() != inst.inputs.len()
            || !carriers[carrier_index].identity_values.insert(output)
        {
            continue;
        }
        for edge in source_edges {
            if carriers[carrier_index]
                .entries
                .iter()
                .any(|entry| entry.value == edge.value)
                && function.dominates(edge.predecessor, header)
            {
                carriers[carrier_index]
                    .dominating_initializers
                    .push(edge);
            }
        }
        owners_by_value
            .entry(output)
            .or_default()
            .insert(carrier_index);
        continuing_owners_by_value
            .entry(output)
            .or_default()
            .insert(carrier_index);
        for site in graph.use_sites(output) {
            if graph
                .inst(site.inst)
                .is_some_and(|use_inst| matches!(use_inst.payload, InstPayload::Phi { .. }))
            {
                pending.insert(site.inst);
            }
        }
    }

    for carrier in &mut carriers {
        carrier.dominating_initializers.sort_unstable();
        carrier.dominating_initializers.dedup();
    }
    carriers.retain(|carrier| carrier.validate(graph));
    carriers.sort_by_key(|carrier| carrier.phi);
    let Some(member_rows) = loop_carrier_member_rows(
        graph,
        header,
        latches,
        loop_body,
        storage_spans,
        machine_context,
        &carriers,
    ) else {
        return Vec::new();
    };
    for (carrier, members) in carriers.iter_mut().zip(member_rows) {
        carrier.members = members;
    }
    carriers
}

#[derive(Debug, Clone)]
struct LoopCarrierPeerCandidate {
    phi: ValueId,
    width: u32,
    entries: Vec<LoopCarrierEdgeValue>,
    updates: Vec<LoopCarrierUpdateFact>,
}

type LoopCarrierMemberRoles = BTreeMap<ValueId, BTreeSet<LoopCarrierMemberRole>>;

fn insert_loop_carrier_member_role(
    rows: &mut LoopCarrierMemberRoles,
    value: ValueId,
    role: LoopCarrierMemberRole,
) -> bool {
    rows.entry(value).or_default().insert(role)
}

fn insert_loop_carrier_peer_roles(
    rows: &mut LoopCarrierMemberRoles,
    peer: &LoopCarrierPeerCandidate,
) {
    insert_loop_carrier_member_role(rows, peer.phi, LoopCarrierMemberRole::ProjectedPeer);
    for entry in &peer.entries {
        insert_loop_carrier_member_role(rows, entry.value, LoopCarrierMemberRole::Entry);
        insert_loop_carrier_member_role(
            rows,
            entry.value,
            LoopCarrierMemberRole::ProjectedPeer,
        );
    }
    for update in &peer.updates {
        insert_loop_carrier_member_role(rows, update.value, LoopCarrierMemberRole::LatchUpdate);
        insert_loop_carrier_member_role(
            rows,
            update.value,
            LoopCarrierMemberRole::ProjectedPeer,
        );
        for identity in &update.identity_values {
            insert_loop_carrier_member_role(
                rows,
                *identity,
                LoopCarrierMemberRole::UpdateIdentity,
            );
            insert_loop_carrier_member_role(
                rows,
                *identity,
                LoopCarrierMemberRole::ProjectedPeer,
            );
        }
    }
}

fn loop_carrier_peer_candidates(
    graph: &SsaGraph,
    header: u64,
    latches: &BTreeSet<u64>,
) -> Vec<LoopCarrierPeerCandidate> {
    let Some(header_block) = graph
        .block_id_for_addr(header)
        .and_then(|block| graph.block(block))
    else {
        return Vec::new();
    };
    let mut candidates = header_block
        .insts
        .iter()
        .filter_map(|inst_id| {
            let inst = graph.inst(*inst_id)?;
            let InstPayload::Phi { predecessors } = &inst.payload else {
                return None;
            };
            let phi = inst.output?;
            let width = graph.value(phi)?.var.size;
            if predecessors.len() != inst.inputs.len() || inst.inputs.is_empty() {
                return None;
            }
            let mut entries = Vec::new();
            let mut updates = Vec::new();
            for (input_idx, (predecessor, value)) in predecessors
                .iter()
                .copied()
                .zip(inst.inputs.iter().copied())
                .enumerate()
            {
                let predecessor = graph.block(predecessor)?.addr;
                let site = UseSite {
                    inst: *inst_id,
                    input_idx,
                };
                let edge = LoopCarrierEdgeValue {
                    predecessor,
                    value,
                    site,
                };
                if !edge.validate(graph) {
                    return None;
                }
                if latches.contains(&predecessor) {
                    updates.push(LoopCarrierUpdateFact {
                        predecessor,
                        value,
                        site,
                        identity_values: exact_copy_identity_values(graph, value),
                    });
                } else {
                    entries.push(edge);
                }
            }
            if entries.is_empty() || updates.is_empty() {
                return None;
            }
            entries.sort_unstable();
            entries.dedup();
            updates.sort_unstable();
            updates.dedup();
            Some(LoopCarrierPeerCandidate {
                phi,
                width,
                entries,
                updates,
            })
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| candidate.phi);
    candidates.dedup_by_key(|candidate| candidate.phi);
    candidates
}

fn exact_loop_carrier_register_storage(
    graph: &SsaGraph,
    machine_context: &SourceMachineContext,
    value: ValueId,
) -> Option<CanonicalStorageId> {
    if machine_context.register_geometry_state() != MachineRegisterGeometryState::Available {
        return None;
    }
    let written = graph.value(value)?.canonical_storage?;
    if written.space != CanonicalStorageSpace::Register {
        return None;
    }
    let projection = machine_context.register_projection(written)?;
    if projection.written.offset != written.offset || projection.written.size != written.size {
        return None;
    }
    let r2il::RegisterProjectionDisposition::Bound { carrier, .. } = projection.disposition else {
        return None;
    };
    Some(CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset: carrier.offset,
        size: carrier.size,
    })
}

fn loop_carrier_projection_key(
    graph: &SsaGraph,
    storage_spans: &StorageSpans,
    machine_context: &SourceMachineContext,
    candidate: &LoopCarrierPeerCandidate,
) -> Option<(
    CanonicalStorageId,
    crate::span::SpanId,
    Vec<u64>,
    Vec<u64>,
)> {
    let carrier = exact_loop_carrier_register_storage(graph, machine_context, candidate.phi)?;
    let state = std::iter::once(candidate.phi)
        .chain(candidate.updates.iter().flat_map(|update| {
            std::iter::once(update.value).chain(update.identity_values.iter().copied())
        }))
        .collect::<BTreeSet<_>>();
    if !storage_spans.all_one_span(state.iter().copied()) {
        return None;
    }
    let span = storage_spans.span_of(candidate.phi)?;
    let entry_predecessors = candidate
        .entries
        .iter()
        .map(|edge| edge.predecessor)
        .collect::<Vec<_>>();
    let update_predecessors = candidate
        .updates
        .iter()
        .map(|update| update.predecessor)
        .collect::<Vec<_>>();
    Some((carrier, span, entry_predecessors, update_predecessors))
}

fn expand_loop_carrier_storage_continuations(
    graph: &SsaGraph,
    storage_spans: &StorageSpans,
    rows: &mut LoopCarrierMemberRoles,
) -> Option<()> {
    let spans = rows
        .keys()
        .copied()
        .map(|value| storage_spans.span_of(value))
        .collect::<Option<BTreeSet<_>>>()?;
    for span in spans {
        for value in storage_spans.members(span)? {
            let graph_value = graph.value(*value)?;
            if graph_value.var.is_const() {
                continue;
            }
            insert_loop_carrier_member_role(
                rows,
                *value,
                LoopCarrierMemberRole::StorageContinuation,
            );
        }
    }
    Some(())
}

fn loop_carrier_member_rows(
    graph: &SsaGraph,
    header: u64,
    latches: &BTreeSet<u64>,
    loop_body: &BTreeSet<u64>,
    storage_spans: &StorageSpans,
    machine_context: Option<&SourceMachineContext>,
    carriers: &[LoopCarrierFact],
) -> Option<Vec<Vec<LoopCarrierMemberFact>>> {
    if carriers
        .iter()
        .any(|carrier| carrier.header != header || !carrier.validate(graph))
    {
        return None;
    }

    let mut rows = carriers
        .iter()
        .map(|carrier| {
            let mut rows = LoopCarrierMemberRoles::new();
            insert_loop_carrier_member_role(
                &mut rows,
                carrier.phi,
                LoopCarrierMemberRole::HeaderPhi,
            );
            for identity in &carrier.identity_values {
                if *identity == carrier.phi {
                    continue;
                }
                let role = graph
                    .def_inst(*identity)
                    .and_then(|inst| graph.inst(inst))
                    .and_then(|inst| graph.block(inst.block))
                    .map(|block| {
                        if loop_body.contains(&block.addr) {
                            LoopCarrierMemberRole::StorageContinuation
                        } else {
                            LoopCarrierMemberRole::PostLoopMerge
                        }
                    })?;
                insert_loop_carrier_member_role(&mut rows, *identity, role);
            }
            for entry in &carrier.entries {
                insert_loop_carrier_member_role(
                    &mut rows,
                    entry.value,
                    LoopCarrierMemberRole::Entry,
                );
            }
            for update in &carrier.updates {
                insert_loop_carrier_member_role(
                    &mut rows,
                    update.value,
                    LoopCarrierMemberRole::LatchUpdate,
                );
                for identity in &update.identity_values {
                    insert_loop_carrier_member_role(
                        &mut rows,
                        *identity,
                        LoopCarrierMemberRole::UpdateIdentity,
                    );
                }
            }
            for initializer in &carrier.dominating_initializers {
                insert_loop_carrier_member_role(
                    &mut rows,
                    initializer.value,
                    LoopCarrierMemberRole::DominatingInitializer,
                );
            }
            Some(rows)
        })
        .collect::<Option<Vec<_>>>()?;

    let candidates = loop_carrier_peer_candidates(graph, header, latches);
    let mut leader_by_carrier = (0..carriers.len()).collect::<Vec<_>>();
    if let Some(machine_context) = machine_context {
        let mut candidates_by_key = BTreeMap::<_, Vec<usize>>::new();
        for (index, candidate) in candidates.iter().enumerate() {
            let Some(key) = loop_carrier_projection_key(
                graph,
                storage_spans,
                machine_context,
                candidate,
            ) else {
                continue;
            };
            candidates_by_key.entry(key).or_default().push(index);
        }
        let carrier_by_phi = carriers
            .iter()
            .enumerate()
            .map(|(index, carrier)| (carrier.phi, index))
            .collect::<BTreeMap<_, _>>();
        for candidate_group in candidates_by_key.values() {
            let Some((leader, leader_candidate)) = candidate_group
                .iter()
                .filter_map(|candidate_index| {
                    let candidate = &candidates[*candidate_index];
                    carrier_by_phi
                        .get(&candidate.phi)
                        .copied()
                        .map(|carrier_index| (carrier_index, *candidate_index))
                })
                .max_by_key(|(carrier_index, candidate_index)| {
                    (
                        candidates[*candidate_index].width,
                        std::cmp::Reverse(carriers[*carrier_index].phi),
                    )
                })
            else {
                continue;
            };
            let leader_width = candidates[leader_candidate].width;
            for candidate_index in candidate_group {
                let candidate = &candidates[*candidate_index];
                if let Some(peer_carrier) = carrier_by_phi.get(&candidate.phi).copied() {
                    leader_by_carrier[peer_carrier] = leader;
                }
                if candidate.width == leader_width {
                    continue;
                }
                insert_loop_carrier_peer_roles(&mut rows[leader], candidate);
                if let Some(peer_carrier) = carrier_by_phi.get(&candidate.phi).copied() {
                    insert_loop_carrier_peer_roles(
                        &mut rows[peer_carrier],
                        &candidates[leader_candidate],
                    );
                }
            }
        }
    }

    for row in &mut rows {
        expand_loop_carrier_storage_continuations(graph, storage_spans, row)?;
    }

    let mut roots_by_span = BTreeMap::<crate::span::SpanId, BTreeSet<usize>>::new();
    for (carrier_index, row) in rows.iter().enumerate() {
        let root = leader_by_carrier[carrier_index];
        if root != carrier_index {
            continue;
        }
        for value in row.keys() {
            roots_by_span
                .entry(storage_spans.span_of(*value)?)
                .or_default()
                .insert(root);
        }
    }

    let mut pending = graph
        .insts
        .iter()
        .filter(|inst| matches!(inst.payload, InstPayload::Phi { .. }))
        .filter_map(|inst| {
            graph
                .block(inst.block)
                .map(|block| (inst.id, block.addr))
        })
        .filter(|(_, block_addr)| *block_addr != header && !loop_body.contains(block_addr))
        .map(|(inst, _)| inst)
        .collect::<BTreeSet<_>>();
    while let Some(inst_id) = pending.pop_first() {
        let inst = graph.inst(inst_id)?;
        let InstPayload::Phi { .. } = &inst.payload else {
            continue;
        };
        let output = inst.output?;
        let block_addr = graph.block(inst.block)?.addr;
        if block_addr == header || loop_body.contains(&block_addr) || inst.inputs.len() < 2 {
            continue;
        }
        let output_span = storage_spans.span_of(output)?;
        let Some(candidate_roots) = roots_by_span.get(&output_span) else {
            continue;
        };
        let output_width = graph.value(output)?.var.size;
        let mut matches = candidate_roots
            .iter()
            .copied()
            .filter(|root| {
                let row = &rows[*root];
                let all_owned = inst.inputs.iter().all(|input| row.contains_key(input));
                let has_carried_state = inst.inputs.iter().any(|input| {
                    row.get(input).is_some_and(|roles| {
                        roles.contains(&LoopCarrierMemberRole::LatchUpdate)
                            || roles.contains(&LoopCarrierMemberRole::UpdateIdentity)
                            || roles.contains(&LoopCarrierMemberRole::PostLoopMerge)
                    })
                });
                let has_other_state = inst.inputs.iter().any(|input| {
                    row.get(input).is_some_and(|roles| {
                        !roles.contains(&LoopCarrierMemberRole::LatchUpdate)
                            && !roles.contains(&LoopCarrierMemberRole::UpdateIdentity)
                            && !roles.contains(&LoopCarrierMemberRole::PostLoopMerge)
                    })
                });
                let carrier = &carriers[*root];
                let width_is_exact = output_width == carrier.width;
                let projected_width_is_exact = !width_is_exact
                    && machine_context.is_some_and(|context| {
                        match (
                            exact_loop_carrier_register_storage(graph, context, output),
                            exact_loop_carrier_register_storage(graph, context, carrier.phi),
                        ) {
                            (Some(output), Some(carrier)) => output == carrier,
                            _ => false,
                        }
                    });
                all_owned
                    && has_carried_state
                    && has_other_state
                    && (width_is_exact || projected_width_is_exact)
            });
        let Some(root) = matches.next() else {
            continue;
        };
        if matches.next().is_some() {
            continue;
        }
        if insert_loop_carrier_member_role(
            &mut rows[root],
            output,
            LoopCarrierMemberRole::PostLoopMerge,
        ) {
            for site in graph.use_sites(output) {
                if graph.inst(site.inst).is_some_and(|use_inst| {
                    matches!(use_inst.payload, InstPayload::Phi { .. })
                        && graph.block(use_inst.block).is_some_and(|block| {
                            block.addr != header && !loop_body.contains(&block.addr)
                        })
                }) {
                    pending.insert(site.inst);
                }
            }
        }
    }

    Some(
        rows.into_iter()
            .map(|rows| {
                rows.into_iter()
                    .map(|(value, roles)| LoopCarrierMemberFact { value, roles })
                    .collect()
            })
            .collect(),
    )
}

fn exact_copy_identity_values(graph: &SsaGraph, root: ValueId) -> BTreeSet<ValueId> {
    let mut identities = BTreeSet::from([root]);
    let mut pending = vec![root];
    while let Some(value) = pending.pop() {
        let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
            continue;
        };
        let InstPayload::Op(SSAOp::Copy { dst, src }) = &inst.payload else {
            continue;
        };
        if dst.size != src.size {
            continue;
        }
        let Some(source) = graph.value_id_for_var(src) else {
            continue;
        };
        if identities.insert(source) {
            pending.push(source);
        }
    }
    identities
}

fn natural_loop_body(
    function: &SSAFunction,
    header: u64,
    latches: &BTreeSet<u64>,
) -> BTreeSet<u64> {
    let mut body = BTreeSet::new();
    body.insert(header);
    let mut stack = latches.iter().copied().collect::<Vec<_>>();
    while let Some(addr) = stack.pop() {
        if !function.dominates(header, addr) {
            continue;
        }
        if !body.insert(addr) {
            continue;
        }
        for pred in function.predecessors(addr) {
            if !body.contains(&pred) {
                stack.push(pred);
            }
        }
    }
    body
}

fn loop_exits(function: &SSAFunction, body: &BTreeSet<u64>) -> Vec<u64> {
    let mut exits = BTreeSet::new();
    for block in body {
        for succ in function.successors(*block) {
            if !body.contains(&succ) {
                exits.insert(succ);
            }
        }
    }
    exits.into_iter().collect()
}

fn loop_condition(
    predicates: &PredicateFacts,
    header: u64,
    body: &BTreeSet<u64>,
    exits: &[u64],
) -> Option<PredicateId> {
    let exit_set = exits.iter().copied().collect::<BTreeSet<_>>();
    predicates
        .predicates
        .values()
        .filter(|predicate| body.contains(&predicate.block_addr))
        .filter(|predicate| {
            (body.contains(&predicate.true_target) && exit_set.contains(&predicate.false_target))
                || (body.contains(&predicate.false_target)
                    && exit_set.contains(&predicate.true_target))
        })
        .min_by_key(|predicate| {
            (
                usize::from(predicate.block_addr != header),
                predicate.block_addr,
                predicate.id,
            )
        })
        .map(|predicate| predicate.id)
}

fn loop_induction_values(
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    condition: Option<PredicateId>,
    header: u64,
    latches: &BTreeSet<u64>,
    body: &BTreeSet<u64>,
) -> (Option<ValueId>, Option<ValueId>, Option<ValueId>) {
    let Some(header_id) = graph.block_id_for_addr(header) else {
        return (None, None, None);
    };
    let Some(header_block) = graph.block(header_id) else {
        return (None, None, None);
    };

    let mut best = None;
    for inst_id in &header_block.insts {
        let Some(inst) = graph.inst(*inst_id) else {
            continue;
        };
        let InstPayload::Phi { predecessors } = &inst.payload else {
            continue;
        };
        let Some(output) = inst.output else {
            continue;
        };
        let mut init = None;
        let mut update = None;
        for (pred_id, input) in predecessors
            .iter()
            .copied()
            .zip(inst.inputs.iter().copied())
        {
            let Some(pred_addr) = graph.block(pred_id).map(|block| block.addr) else {
                continue;
            };
            if latches.contains(&pred_addr) {
                update = Some(input);
            } else if !body.contains(&pred_addr) {
                init = Some(input);
            }
        }
        if init.is_none() || update.is_none() {
            continue;
        }
        let condition_dependency_rank = condition
            .and_then(|condition| predicates.predicates.get(&condition))
            .and_then(|predicate| predicate.comparison.as_ref())
            .is_some_and(|comparison| {
                value_depends_on(graph, comparison.lhs, output)
                    || value_depends_on(graph, comparison.rhs, output)
            });
        let low_value_rank = is_low_value_induction_phi(graph, output);
        let candidate = (
            usize::from(!condition_dependency_rank),
            usize::from(low_value_rank),
            output,
            init,
            update,
        );
        if best.as_ref().is_none_or(
            |current: &(usize, usize, ValueId, Option<ValueId>, Option<ValueId>)| {
                candidate < *current
            },
        ) {
            best = Some(candidate);
        }
    }
    best.map(|(_, _, phi, init, update)| (Some(phi), init, update))
        .unwrap_or((None, None, None))
}

fn is_low_value_induction_phi(graph: &SsaGraph, value: ValueId) -> bool {
    let Some(var) = graph.value(value).map(|value| &value.var) else {
        return true;
    };
    let name = var.name.trim_start_matches("reg:").to_ascii_lowercase();
    matches!(name.as_str(), "cf" | "pf" | "af" | "zf" | "sf" | "of")
        || name.starts_with("flag")
        || name.starts_with("tmp")
        || name == "rsp"
        || name == "esp"
        || name == "rbp"
        || name == "ebp"
}

fn loop_bound_value(
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    condition: Option<PredicateId>,
    induction_phi: Option<ValueId>,
    induction_update: Option<ValueId>,
) -> Option<ValueId> {
    let comparison = predicates
        .predicates
        .get(&condition?)?
        .comparison
        .as_ref()?;
    let induction = induction_phi.or(induction_update)?;
    let lhs_depends = value_depends_on(graph, comparison.lhs, induction);
    let rhs_depends = value_depends_on(graph, comparison.rhs, induction);
    match (lhs_depends, rhs_depends) {
        (true, false) => Some(comparison.rhs),
        (false, true) => Some(comparison.lhs),
        _ => None,
    }
}

fn value_depends_on(graph: &SsaGraph, value: ValueId, needle: ValueId) -> bool {
    if value == needle {
        return true;
    }
    let mut visited = BTreeSet::new();
    let mut stack = vec![(value, 0usize)];
    while let Some((current, depth)) = stack.pop() {
        if current == needle {
            return true;
        }
        if depth >= 16 || !visited.insert(current) {
            continue;
        }
        let Some(def_inst) = graph.def_inst(current) else {
            continue;
        };
        let Some(inst) = graph.inst(def_inst) else {
            continue;
        };
        for input in &inst.inputs {
            stack.push((*input, depth + 1));
        }
    }
    false
}

fn collect_structured_memory_access_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
) -> BTreeMap<StructuredAccessId, StructuredMemoryAccessFact> {
    let mut access_facts = BTreeMap::new();
    for block in function.blocks() {
        for (op_index, op) in block.ops.iter().enumerate() {
            let Some(inst) = graph.inst_id_for_op_site(block.addr, op_index) else {
                continue;
            };
            let mut ordinal = 0u32;
            match op {
                SSAOp::Load { dst, addr, space }
                | SSAOp::LoadLinked {
                    dst, addr, space, ..
                }
                | SSAOp::LoadGuarded {
                    dst, addr, space, ..
                } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        insert_raw_memory_subeffect(
                            &mut access_facts,
                            memory,
                            objects,
                            inst,
                            &mut ordinal,
                            block.addr,
                            op_index,
                            address,
                            *space,
                            graph.value_id_for_var(dst),
                            false,
                            dst.size,
                        );
                    }
                }
                SSAOp::Store { addr, val, space }
                | SSAOp::StoreGuarded {
                    addr, val, space, ..
                } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        insert_raw_memory_subeffect(
                            &mut access_facts,
                            memory,
                            objects,
                            inst,
                            &mut ordinal,
                            block.addr,
                            op_index,
                            address,
                            *space,
                            graph.value_id_for_var(val),
                            true,
                            val.size,
                        );
                    }
                }
                SSAOp::StoreConditional {
                    addr, val, space, ..
                } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        insert_raw_memory_subeffect(
                            &mut access_facts,
                            memory,
                            objects,
                            inst,
                            &mut ordinal,
                            block.addr,
                            op_index,
                            address,
                            *space,
                            None,
                            false,
                            val.size,
                        );
                        insert_raw_memory_subeffect(
                            &mut access_facts,
                            memory,
                            objects,
                            inst,
                            &mut ordinal,
                            block.addr,
                            op_index,
                            address,
                            *space,
                            graph.value_id_for_var(val),
                            true,
                            val.size,
                        );
                    }
                }
                SSAOp::AtomicCAS {
                    dst,
                    addr,
                    replacement,
                    space,
                    ..
                } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        insert_raw_memory_subeffect(
                            &mut access_facts,
                            memory,
                            objects,
                            inst,
                            &mut ordinal,
                            block.addr,
                            op_index,
                            address,
                            *space,
                            graph.value_id_for_var(dst),
                            false,
                            replacement.size,
                        );
                        insert_raw_memory_subeffect(
                            &mut access_facts,
                            memory,
                            objects,
                            inst,
                            &mut ordinal,
                            block.addr,
                            op_index,
                            address,
                            *space,
                            graph.value_id_for_var(replacement),
                            true,
                            replacement.size,
                        );
                    }
                }
                _ => {}
            }
        }
    }
    access_facts
}

#[allow(clippy::too_many_arguments)]
fn insert_raw_memory_subeffect(
    access_facts: &mut BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    memory: &MemorySSAFacts,
    objects: &ObjectModel,
    inst: InstId,
    ordinal: &mut u32,
    block_addr: u64,
    op_index: usize,
    address: ValueId,
    space: SpaceId,
    value: Option<ValueId>,
    is_write: bool,
    width: u32,
) {
    let annotations = if is_write {
        memory
            .defs_by_inst
            .get(&inst)
            .into_iter()
            .flatten()
            .map(|fact| &fact.location)
            .collect::<BTreeSet<_>>()
    } else {
        memory
            .uses_by_inst
            .get(&inst)
            .into_iter()
            .flatten()
            .map(|fact| &fact.location)
            .collect::<BTreeSet<_>>()
    };
    let matching = annotations
        .iter()
        .filter(|location| {
            location.size == width
                && location.space == space
                && objects
                    .object(location.object)
                    .is_some_and(|object| object.kind.space() == space)
        })
        .collect::<Vec<_>>();
    let provenance_complete = annotations.len() == 1 && matching.len() == 1;
    let object = matching
        .first()
        .map(|location| location.object)
        .or_else(|| objects.escaped_unknown_object(space))
        .unwrap_or(ObjectId(0));
    insert_structured_memory_access(
        access_facts,
        inst,
        ordinal,
        block_addr,
        op_index,
        space,
        object,
        address,
        value,
        is_write,
        width,
        provenance_complete,
    );
}

#[allow(clippy::too_many_arguments)]
fn insert_structured_memory_access(
    access_facts: &mut BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    inst: InstId,
    ordinal: &mut u32,
    block_addr: u64,
    op_index: usize,
    space: SpaceId,
    object: ObjectId,
    address: ValueId,
    value: Option<ValueId>,
    is_write: bool,
    width: u32,
    provenance_complete: bool,
) {
    let id = StructuredAccessId {
        inst,
        ordinal: *ordinal,
    };
    *ordinal = (*ordinal).saturating_add(1);
    access_facts.insert(
        id,
        StructuredMemoryAccessFact {
            id,
            block_addr,
            op_index,
            space,
            object,
            address,
            value,
            is_write,
            width,
            provenance_complete,
        },
    );
}

fn collect_structured_recursive_call_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_sites: &CallSiteFacts,
) -> BTreeMap<CallSiteId, StructuredRecursiveCallFact> {
    let mut recursive_calls = BTreeMap::new();
    for (call_site, fact) in &call_sites.by_id {
        let Some(target) = fact.direct_target else {
            continue;
        };
        if target != function.entry {
            continue;
        }
        let Some((block_addr, op_index)) = graph.op_site_for_inst(fact.at) else {
            continue;
        };
        recursive_calls.insert(
            *call_site,
            StructuredRecursiveCallFact {
                call_site: *call_site,
                block_addr,
                op_index,
                target,
            },
        );
    }
    recursive_calls
}

fn collect_predicate_facts(function: &SSAFunction, graph: &SsaGraph) -> PredicateFacts {
    let mut predicates = BTreeMap::new();
    let mut block_assumptions = BTreeMap::<u64, Vec<BlockAssumption>>::new();
    let mut switches = BTreeMap::new();
    let compare_defs = collect_compare_defs(function, graph);
    let evaluated_compare_defs = &compare_defs.evaluated;
    let compare_defs = &compare_defs.normalized;
    let mut next_predicate_id = 0u32;

    for &block_addr in function.block_addrs() {
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let Some(cfg_block) = function.cfg().get_block(block_addr) else {
            continue;
        };
        match &cfg_block.terminator {
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                let Some(SSAOp::CBranch { cond, .. }) = block.ops.last() else {
                    continue;
                };
                let id = PredicateId(next_predicate_id);
                next_predicate_id = next_predicate_id.saturating_add(1);
                predicates.insert(
                    id,
                    PredicateFact {
                        id,
                        block_addr,
                        condition: graph
                            .value_id_for_var(cond)
                            .expect("predicate condition in graph"),
                        comparison: compare_defs.get(cond).cloned(),
                        evaluated_comparison: evaluated_compare_defs.get(cond).cloned(),
                        true_target: *true_target,
                        false_target: *false_target,
                    },
                );
                block_assumptions
                    .entry(*true_target)
                    .or_default()
                    .push(BlockAssumption {
                        predecessor: block_addr,
                        predicate: id,
                        truth: true,
                    });
                block_assumptions
                    .entry(*false_target)
                    .or_default()
                    .push(BlockAssumption {
                        predecessor: block_addr,
                        predicate: id,
                        truth: false,
                    });
            }
            BlockTerminator::Switch { cases, default } => {
                switches.insert(
                    block_addr,
                    SwitchPredicateFact {
                        block_addr,
                        selector: function
                            .infer_switch_selector_var(block.addr)
                            .and_then(|selector| graph.value_id_for_var(&selector)),
                        cases: cases.clone(),
                        default: *default,
                    },
                );
            }
            _ => {}
        }
    }

    PredicateFacts {
        predicates,
        block_assumptions,
        switches,
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ControlDomainState {
    guards: BTreeSet<ControlGuard>,
    complete: bool,
}

fn collect_control_domain_facts(
    function: &SSAFunction,
    predicates: &PredicateFacts,
    structured: &StructuredDataflowFacts,
) -> ControlDomainFacts {
    let mut guard_universe = BTreeSet::new();
    for &predecessor in function.block_addrs() {
        for successor in function.successors(predecessor) {
            if let (Some(guard), _) =
                control_guard_for_edge(function, predicates, predecessor, successor)
            {
                guard_universe.insert(guard);
            }
        }
    }
    let mut states = function
        .block_addrs()
        .iter()
        .copied()
        .map(|addr| {
            (
                addr,
                Some(ControlDomainState {
                    guards: guard_universe.clone(),
                    complete: true,
                }),
            )
        })
        .collect::<BTreeMap<_, _>>();
    states.insert(
        function.entry,
        Some(ControlDomainState {
            guards: BTreeSet::new(),
            complete: true,
        }),
    );

    let iteration_limit = function
        .num_blocks()
        .saturating_mul(guard_universe.len().saturating_add(2))
        .max(8);
    for _ in 0..iteration_limit {
        let previous = states.clone();
        let mut changed = false;
        for &block_addr in function.block_addrs() {
            if block_addr == function.entry {
                continue;
            }
            let predecessors = function.predecessors(block_addr);
            if predecessors.is_empty() {
                let state = Some(ControlDomainState {
                    guards: BTreeSet::new(),
                    complete: false,
                });
                if states.get(&block_addr) != Some(&state) {
                    states.insert(block_addr, state);
                    changed = true;
                }
                continue;
            }

            let mut incoming = Vec::new();
            for predecessor in predecessors {
                let Some(mut state) = previous.get(&predecessor).cloned().flatten() else {
                    continue;
                };
                let (guard, edge_complete) =
                    control_guard_for_edge(function, predicates, predecessor, block_addr);
                if let Some(guard) = guard {
                    state.guards.insert(guard);
                }
                state.complete &= edge_complete;
                incoming.push(state);
            }
            if incoming.is_empty() {
                continue;
            }

            let mut guards = incoming[0].guards.clone();
            for state in &incoming[1..] {
                guards = guards.intersection(&state.guards).cloned().collect();
            }
            let state = Some(ControlDomainState {
                guards,
                complete: incoming.iter().all(|state| state.complete),
            });
            if states.get(&block_addr) != Some(&state) {
                states.insert(block_addr, state);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut loops_by_block = BTreeMap::<u64, Vec<LoopId>>::new();
    for (loop_id, loop_fact) in &structured.loops {
        for block_addr in &loop_fact.body {
            loops_by_block
                .entry(*block_addr)
                .or_default()
                .push(*loop_id);
        }
    }
    for loops in loops_by_block.values_mut() {
        loops.sort_unstable();
        loops.dedup();
    }

    let mut domain_ids = BTreeMap::<(Vec<ControlGuard>, Vec<LoopId>, bool), ControlDomainId>::new();
    let mut domains = BTreeMap::new();
    let mut by_block = BTreeMap::new();
    for &block_addr in function.block_addrs() {
        let state = states
            .remove(&block_addr)
            .flatten()
            .unwrap_or(ControlDomainState {
                guards: BTreeSet::new(),
                complete: false,
            });
        let guards = state.guards.into_iter().collect::<Vec<_>>();
        let loops = loops_by_block.remove(&block_addr).unwrap_or_default();
        let key = (guards.clone(), loops.clone(), state.complete);
        let id = if let Some(id) = domain_ids.get(&key).copied() {
            id
        } else {
            let id = ControlDomainId(domain_ids.len() as u32);
            domain_ids.insert(key, id);
            domains.insert(
                id,
                ControlDomain {
                    id,
                    guards,
                    loops,
                    complete: state.complete,
                },
            );
            id
        };
        by_block.insert(block_addr, id);
    }
    ControlDomainFacts { domains, by_block }
}

fn control_guard_for_edge(
    function: &SSAFunction,
    predicates: &PredicateFacts,
    predecessor: u64,
    successor: u64,
) -> (Option<ControlGuard>, bool) {
    let Some(block) = function.cfg().get_block(predecessor) else {
        return (None, false);
    };
    match &block.terminator {
        BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } => {
            if true_target == false_target {
                return (None, *true_target == successor);
            }
            let predicate = predicates
                .predicates
                .values()
                .find(|fact| fact.block_addr == predecessor)
                .map(|fact| fact.id);
            let Some(predicate) = predicate else {
                return (None, false);
            };
            if *true_target == successor {
                (
                    Some(ControlGuard::Branch {
                        predicate,
                        truth: true,
                    }),
                    true,
                )
            } else if *false_target == successor {
                (
                    Some(ControlGuard::Branch {
                        predicate,
                        truth: false,
                    }),
                    true,
                )
            } else {
                (None, false)
            }
        }
        BlockTerminator::Switch { cases, default } => {
            let mut case_values = cases
                .iter()
                .filter_map(|(value, target)| (*target == successor).then_some(*value))
                .collect::<Vec<_>>();
            case_values.sort_unstable();
            case_values.dedup();
            let includes_default = *default == Some(successor);
            if case_values.is_empty() && !includes_default {
                return (None, false);
            }
            (
                Some(ControlGuard::SwitchArm {
                    block_addr: predecessor,
                    case_values,
                    includes_default,
                }),
                true,
            )
        }
        BlockTerminator::IndirectBranch if function.successors(predecessor).len() > 1 => {
            (None, false)
        }
        _ => (None, function.successors(predecessor).contains(&successor)),
    }
}

fn collect_call_sites(
    function: &SSAFunction,
    graph: &SsaGraph,
    prep_facts: Option<&DecompilePrepFacts>,
    machine_context: Option<&SourceMachineContext>,
) -> CallSiteFacts {
    let mut by_id = BTreeMap::new();
    let mut by_inst = BTreeMap::new();
    let mut next_id = 0u32;

    for &block_addr in function.block_addrs() {
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let fallthrough = match function
            .cfg()
            .get_block(block_addr)
            .map(|block| &block.terminator)
        {
            Some(BlockTerminator::Call { fallthrough, .. })
            | Some(BlockTerminator::IndirectCall { fallthrough }) => *fallthrough,
            _ => None,
        };

        for (op_idx, op) in block.ops.iter().enumerate() {
            let target = match op {
                SSAOp::Call { target } | SSAOp::CallInd { target } => target.clone(),
                _ => continue,
            };
            let Some(inst_id) = graph.inst_id_for_op_site(block_addr, op_idx) else {
                continue;
            };
            let Some(target_id) = graph.value_id_for_var(&target) else {
                continue;
            };
            let id = CallSiteId(next_id);
            next_id = next_id.saturating_add(1);
            let raw_identity = machine_context
                .and_then(|context| context.raw_call_site_identity(id))
                .filter(|identity| identity.block_addr() == block_addr);
            let direct_target = resolve_graph_literal_value(graph, prep_facts, &target)
                .or_else(|| raw_identity.and_then(direct_target_from_raw_identity));
            by_inst.insert(inst_id, id);
            by_id.insert(
                id,
                CallSiteFact {
                    id,
                    at: inst_id,
                    raw_identity,
                    target: target_id,
                    direct_target,
                    fallthrough: if op_idx + 1 == block.ops.len() {
                        fallthrough
                    } else {
                        None
                    },
                    memory_effect: CallMemoryEffect::Unknown,
                },
            );
        }
    }

    CallSiteFacts { by_id, by_inst }
}

fn collect_call_argument_values(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_site: &CallSiteFact,
) -> Vec<ValueId> {
    let mut by_index = collect_call_argument_slots(function, graph, call_site)
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    let mut values = Vec::new();
    for index in 0..16 {
        let Some(value) = by_index.remove(&index) else {
            break;
        };
        values.push(value);
    }
    values
}

fn collect_call_argument_slots(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_site: &CallSiteFact,
) -> Vec<(usize, ValueId)> {
    let Some((block_addr, op_idx)) = graph.op_site_for_inst(call_site.at) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut by_index = BTreeMap::<usize, ValueId>::new();
    for op in block.ops[..op_idx].iter().rev() {
        if matches!(
            op,
            SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
        ) {
            break;
        }
        let Some((index, value, _)) = call_argument_value_for_op(op, graph) else {
            continue;
        };
        by_index.entry(index).or_insert(value);
    }

    by_index.into_iter().collect()
}

fn collect_register_call_argument_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_site: &CallSiteFact,
) -> Vec<CallArgumentCertificate> {
    let Some((block_addr, op_idx)) = graph.op_site_for_inst(call_site.at) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut by_index = BTreeMap::<usize, CallArgumentCertificate>::new();
    for (producer_idx, op) in block.ops[..op_idx].iter().enumerate().rev() {
        if matches!(
            op,
            SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
        ) {
            break;
        }
        let Some((index, value, register)) = call_argument_value_for_op(op, graph) else {
            continue;
        };
        by_index.entry(index).or_insert(CallArgumentCertificate {
            index,
            value,
            location: CallArgumentLocation::Register { name: register },
            source_inst: graph.inst_id_for_op_site(block_addr, producer_idx),
        });
    }

    let mut certificates = Vec::new();
    for index in 0..16 {
        let Some(certificate) = by_index.remove(&index) else {
            break;
        };
        certificates.push(certificate);
    }
    certificates
}

fn collect_stack_call_argument_values(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    structured: &StructuredDataflowFacts,
    call_site: &CallSiteFact,
) -> Vec<StackCallArgumentCertificate> {
    let Some((block_addr, op_idx)) = graph.op_site_for_inst(call_site.at) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut by_offset = BTreeMap::<i64, StackCallArgumentCertificate>::new();
    for (producer_idx, op) in block.ops[..op_idx].iter().enumerate().rev() {
        if matches!(
            op,
            SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
        ) {
            break;
        }
        let SSAOp::Store {
            space: SpaceId::Ram,
            val,
            ..
        } = op
        else {
            continue;
        };
        let Some(value) = graph.value_id_for_var(val) else {
            continue;
        };

        for (access_id, access) in structured.memory_accesses.iter().filter(|(_, access)| {
            access.block_addr == block_addr
                && access.op_index == producer_idx
                && access.is_write
                && ram_memory_access_matches_source(function, graph, objects, access)
        }) {
            if access.value != Some(value) {
                continue;
            }
            let Some(offset) = stack_pointer_object_offset(objects, access.object) else {
                continue;
            };
            if offset < 0 {
                continue;
            }
            by_offset
                .entry(offset)
                .or_insert(StackCallArgumentCertificate {
                    stack_offset: offset,
                    value,
                    memory_access: *access_id,
                });
        }
    }

    by_offset.into_values().collect()
}

fn collect_stack_call_argument_certificates(
    stack_argument_values: &[StackCallArgumentCertificate],
    structured: &StructuredDataflowFacts,
) -> Vec<CallArgumentCertificate> {
    stack_argument_values
        .iter()
        .enumerate()
        .filter_map(|(index, stack_arg)| {
            let access = structured.memory_accesses.get(&stack_arg.memory_access)?;
            Some(CallArgumentCertificate {
                index,
                value: stack_arg.value,
                location: CallArgumentLocation::Stack {
                    object: access.object,
                    offset: stack_arg.stack_offset,
                    memory_access: stack_arg.memory_access,
                },
                source_inst: Some(stack_arg.memory_access.inst),
            })
        })
        .collect()
}

fn stack_pointer_object_offset(objects: &ObjectModel, object: ObjectId) -> Option<i64> {
    let fact = objects.object(object)?;
    match fact.kind {
        ObjectKind::StackSlot {
            space: SpaceId::Ram,
            base: StackAddressBase::StackPointer,
            offset,
            ..
        }
        | ObjectKind::FrameObject {
            space: SpaceId::Ram,
            base: StackAddressBase::StackPointer,
            offset,
            ..
        } => Some(offset),
        _ => None,
    }
}

fn stack_object_offset(objects: &ObjectModel, object: ObjectId) -> Option<i64> {
    stack_object_root(objects, object).map(|(_, offset)| offset)
}

fn stack_object_root(objects: &ObjectModel, object: ObjectId) -> Option<(StackAddressBase, i64)> {
    let fact = objects.object(object)?;
    match fact.kind {
        ObjectKind::StackSlot {
            space: SpaceId::Ram,
            base,
            offset,
        }
        | ObjectKind::FrameObject {
            space: SpaceId::Ram,
            base,
            offset,
        } => Some((base, offset)),
        _ => None,
    }
}

fn call_argument_value_for_op(op: &SSAOp, graph: &SsaGraph) -> Option<(usize, ValueId, String)> {
    // A call defines every register the callee may destroy, and those
    // definitions are emitted after it, so the walk back from the next call
    // reaches them before it reaches the call that made them. Their
    // destinations are argument registers, but they are what a call leaves
    // behind rather than what the next one was given.
    if matches!(op, SSAOp::CallDefine { .. }) {
        return None;
    }
    let dst = op.dst()?;
    let index = canonical_abi_arg_index(&dst.name)?;
    let source = match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => graph.value_id_for_var(src),
        _ => None,
    }
    .or_else(|| graph.value_id_for_var(dst))?;
    Some((index, source, dst.name.clone()))
}

fn canonical_abi_arg_index(name: &str) -> Option<usize> {
    match name.to_ascii_lowercase().as_str() {
        "rdi" | "edi" | "di" | "dil" => Some(0),
        "rsi" | "esi" | "si" | "sil" => Some(1),
        "rdx" | "edx" | "dx" | "dl" => Some(2),
        "rcx" | "ecx" | "cx" | "cl" => Some(3),
        "r8" | "r8d" | "r8w" | "r8b" => Some(4),
        "r9" | "r9d" | "r9w" | "r9b" => Some(5),
        "x0" | "w0" | "a0" => Some(0),
        "x1" | "w1" | "a1" => Some(1),
        "x2" | "w2" | "a2" => Some(2),
        "x3" | "w3" | "a3" => Some(3),
        "x4" | "w4" | "a4" => Some(4),
        "x5" | "w5" | "a5" => Some(5),
        "x6" | "w6" | "a6" => Some(6),
        "x7" | "w7" | "a7" => Some(7),
        _ => None,
    }
}

struct CompareDefinitions {
    normalized: BTreeMap<SSAVar, CompareProvenance>,
    evaluated: BTreeMap<SSAVar, CompareProvenance>,
}

fn collect_compare_defs(function: &SSAFunction, graph: &SsaGraph) -> CompareDefinitions {
    let mut normalized = BTreeMap::<SSAVar, CompareProvenance>::new();
    let mut evaluated = BTreeMap::<SSAVar, CompareProvenance>::new();
    let copy_sources = collect_compare_copy_sources(function);
    let mut sub_sources = BTreeMap::<SSAVar, (ValueId, ValueId)>::new();
    let mut signed_overflow_sources = BTreeMap::<SSAVar, (ValueId, ValueId)>::new();
    let mut signed_sign_sources = BTreeMap::<SSAVar, (ValueId, ValueId)>::new();

    for block in function.blocks() {
        for op in &block.ops {
            if let SSAOp::IntSub { dst, a, b } = op
                && let (Some(lhs), Some(rhs)) = (
                    canonical_compare_operand(graph, &copy_sources, a),
                    canonical_compare_operand(graph, &copy_sources, b),
                )
            {
                sub_sources.insert(dst.clone(), (lhs, rhs));
            }
        }
    }

    for block in function.blocks() {
        for op in &block.ops {
            if let SSAOp::IntSBorrow { dst, a, b } = op
                && let (Some(lhs), Some(rhs)) = (
                    canonical_compare_operand(graph, &copy_sources, a),
                    canonical_compare_operand(graph, &copy_sources, b),
                )
            {
                signed_overflow_sources.insert(dst.clone(), (lhs, rhs));
            }
            if let SSAOp::IntSLess { dst, a, b } = op
                && const_value(b) == Some(0)
                && let Some((lhs, rhs)) = sub_sources.get(a).copied()
            {
                signed_sign_sources.insert(dst.clone(), (lhs, rhs));
            }
        }
    }
    propagate_compare_source_aliases(function, &mut signed_overflow_sources);
    propagate_compare_source_aliases(function, &mut signed_sign_sources);

    for block in function.blocks() {
        for op in &block.ops {
            let Some((dst, kind, lhs, rhs)) = compare_components(op) else {
                if let Some((dst, kind, lhs, rhs)) = signed_flag_compare_components(
                    graph,
                    op,
                    &signed_overflow_sources,
                    &signed_sign_sources,
                ) {
                    let comparison = CompareProvenance { kind, lhs, rhs };
                    normalized.insert(dst.clone(), comparison.clone());
                    evaluated.insert(dst.clone(), comparison);
                }
                continue;
            };
            let Some(lhs_id) = canonical_compare_operand(graph, &copy_sources, lhs) else {
                continue;
            };
            let Some(rhs_id) = canonical_compare_operand(graph, &copy_sources, rhs) else {
                continue;
            };
            evaluated.insert(
                dst.clone(),
                CompareProvenance {
                    kind,
                    lhs: lhs_id,
                    rhs: rhs_id,
                },
            );
            let (normalized_lhs, normalized_rhs) =
                normalize_zero_sub_compare_operands(kind, lhs, rhs, lhs_id, rhs_id, &sub_sources);
            normalized.insert(
                dst.clone(),
                CompareProvenance {
                    kind,
                    lhs: normalized_lhs,
                    rhs: normalized_rhs,
                },
            );
            if let Some((dst, kind, lhs, rhs)) = signed_flag_compare_components(
                graph,
                op,
                &signed_overflow_sources,
                &signed_sign_sources,
            ) {
                let comparison = CompareProvenance { kind, lhs, rhs };
                normalized.insert(dst.clone(), comparison.clone());
                evaluated.insert(dst.clone(), comparison);
            }
        }
    }

    propagate_compare_definitions(function, graph, &mut normalized);
    propagate_compare_definitions(function, graph, &mut evaluated);
    CompareDefinitions {
        normalized,
        evaluated,
    }
}

fn propagate_compare_definitions(
    function: &SSAFunction,
    graph: &SsaGraph,
    compare_defs: &mut BTreeMap<SSAVar, CompareProvenance>,
) {
    loop {
        let mut changed = false;
        for block in function.blocks() {
            for op in &block.ops {
                let propagated = match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src } => compare_defs
                        .get(src)
                        .cloned()
                        .map(|comparison| (dst, comparison)),
                    SSAOp::Subpiece {
                        dst,
                        src,
                        offset: 0,
                    } => compare_defs
                        .get(src)
                        .cloned()
                        .map(|comparison| (dst, comparison)),
                    SSAOp::BoolNot { dst, src } => compare_defs.get(src).and_then(|comparison| {
                        invert_compare_provenance(comparison).map(|comparison| (dst, comparison))
                    }),
                    SSAOp::BoolAnd { dst, a, b } => compare_defs
                        .get(a)
                        .zip(compare_defs.get(b))
                        .and_then(|(lhs, rhs)| combine_compare_provenance(graph, lhs, rhs, false))
                        .map(|comparison| (dst, comparison)),
                    SSAOp::BoolOr { dst, a, b } => compare_defs
                        .get(a)
                        .zip(compare_defs.get(b))
                        .and_then(|(lhs, rhs)| combine_compare_provenance(graph, lhs, rhs, true))
                        .map(|comparison| (dst, comparison)),
                    _ => None,
                };
                let Some((dst, comparison)) = propagated else {
                    continue;
                };
                if compare_defs.get(dst) != Some(&comparison) {
                    compare_defs.insert(dst.clone(), comparison);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

fn collect_compare_copy_sources(function: &SSAFunction) -> BTreeMap<SSAVar, SSAVar> {
    let mut sources = BTreeMap::new();
    for block in function.blocks() {
        for op in &block.ops {
            if let SSAOp::Copy { dst, src } = op {
                sources.insert(dst.clone(), src.clone());
            }
        }
    }
    sources
}

fn canonical_compare_operand(
    graph: &SsaGraph,
    copy_sources: &BTreeMap<SSAVar, SSAVar>,
    var: &SSAVar,
) -> Option<ValueId> {
    let mut current = var;
    let mut visited = BTreeSet::new();
    for _ in 0..32 {
        if !visited.insert(current) {
            return None;
        }
        let Some(source) = copy_sources.get(current) else {
            return graph.value_id_for_var(current);
        };
        current = source;
    }
    None
}

fn propagate_compare_source_aliases(
    function: &SSAFunction,
    sources: &mut BTreeMap<SSAVar, (ValueId, ValueId)>,
) {
    loop {
        let mut changed = false;
        for block in function.blocks() {
            for op in &block.ops {
                let (dst, src) = match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src } => (dst, src),
                    SSAOp::Subpiece {
                        dst,
                        src,
                        offset: 0,
                    } => (dst, src),
                    _ => continue,
                };
                let Some(source) = sources.get(src).copied() else {
                    continue;
                };
                if sources.get(dst) != Some(&source) {
                    sources.insert(dst.clone(), source);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

fn invert_compare_provenance(comparison: &CompareProvenance) -> Option<CompareProvenance> {
    let (kind, swap_operands) = match comparison.kind {
        CompareKind::Equal => (CompareKind::NotEqual, false),
        CompareKind::NotEqual => (CompareKind::Equal, false),
        CompareKind::Less => (CompareKind::LessEqual, true),
        CompareKind::SignedLess => (CompareKind::SignedLessEqual, true),
        CompareKind::LessEqual => (CompareKind::Less, true),
        CompareKind::SignedLessEqual => (CompareKind::SignedLess, true),
    };
    Some(CompareProvenance {
        kind,
        lhs: if swap_operands {
            comparison.rhs
        } else {
            comparison.lhs
        },
        rhs: if swap_operands {
            comparison.lhs
        } else {
            comparison.rhs
        },
    })
}

fn combine_compare_provenance(
    graph: &SsaGraph,
    lhs: &CompareProvenance,
    rhs: &CompareProvenance,
    is_or: bool,
) -> Option<CompareProvenance> {
    combine_compare_provenance_by(lhs, rhs, is_or, |lhs, rhs| {
        compare_values_equivalent(graph, lhs, rhs)
    })
}

fn combine_compare_provenance_by(
    lhs: &CompareProvenance,
    rhs: &CompareProvenance,
    is_or: bool,
    equivalent: impl Fn(ValueId, ValueId) -> bool,
) -> Option<CompareProvenance> {
    if lhs.kind == rhs.kind && equivalent(lhs.lhs, rhs.lhs) && equivalent(lhs.rhs, rhs.rhs) {
        return Some(lhs.clone());
    }

    let equality_operands_match = |ordered: &CompareProvenance, equality: &CompareProvenance| {
        equivalent(ordered.lhs, equality.lhs) && equivalent(ordered.rhs, equality.rhs)
            || equivalent(ordered.lhs, equality.rhs) && equivalent(ordered.rhs, equality.lhs)
    };
    let (ordered, equality) = if matches!(
        lhs.kind,
        CompareKind::Less
            | CompareKind::SignedLess
            | CompareKind::LessEqual
            | CompareKind::SignedLessEqual
    ) && matches!(rhs.kind, CompareKind::Equal | CompareKind::NotEqual)
    {
        (lhs, rhs)
    } else if matches!(
        rhs.kind,
        CompareKind::Less
            | CompareKind::SignedLess
            | CompareKind::LessEqual
            | CompareKind::SignedLessEqual
    ) && matches!(lhs.kind, CompareKind::Equal | CompareKind::NotEqual)
    {
        (rhs, lhs)
    } else {
        return None;
    };
    if !equality_operands_match(ordered, equality) {
        return None;
    }

    let kind = match (is_or, ordered.kind, equality.kind) {
        (true, CompareKind::Less, CompareKind::Equal) => CompareKind::LessEqual,
        (true, CompareKind::SignedLess, CompareKind::Equal) => CompareKind::SignedLessEqual,
        (false, CompareKind::LessEqual, CompareKind::NotEqual) => CompareKind::Less,
        (false, CompareKind::SignedLessEqual, CompareKind::NotEqual) => CompareKind::SignedLess,
        _ => return None,
    };
    Some(CompareProvenance {
        kind,
        lhs: ordered.lhs,
        rhs: ordered.rhs,
    })
}

fn compare_values_equivalent(graph: &SsaGraph, lhs: ValueId, rhs: ValueId) -> bool {
    compare_values_equivalent_inner(graph, lhs, rhs, 0, &mut BTreeSet::new())
}

fn compare_values_equivalent_inner(
    graph: &SsaGraph,
    lhs: ValueId,
    rhs: ValueId,
    depth: usize,
    visiting: &mut BTreeSet<(ValueId, ValueId)>,
) -> bool {
    if lhs == rhs {
        return true;
    }
    if depth >= 16 {
        return false;
    }
    let pair = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
    if !visiting.insert(pair) {
        return false;
    }
    let equivalent = (|| {
        let lhs_value = graph.value(lhs)?;
        let rhs_value = graph.value(rhs)?;
        if lhs_value.var.size != rhs_value.var.size {
            return Some(false);
        }
        if lhs_value.var.constant_bits().is_some() || rhs_value.var.constant_bits().is_some() {
            return Some(
                lhs_value.var.constant_bits().is_some()
                    && rhs_value.var.constant_bits().is_some()
                    && const_value(&lhs_value.var) == const_value(&rhs_value.var),
            );
        }
        let lhs_inst = graph.inst(graph.def_inst(lhs)?)?;
        let rhs_inst = graph.inst(graph.def_inst(rhs)?)?;
        let (InstPayload::Op(lhs_op), InstPayload::Op(rhs_op)) =
            (&lhs_inst.payload, &rhs_inst.payload)
        else {
            return Some(false);
        };
        let mut equivalent_sources = |lhs: &SSAVar, rhs: &SSAVar| {
            graph
                .value_id_for_var(lhs)
                .zip(graph.value_id_for_var(rhs))
                .is_some_and(|(lhs, rhs)| {
                    compare_values_equivalent_inner(graph, lhs, rhs, depth + 1, visiting)
                })
        };
        Some(match (lhs_op, rhs_op) {
            (
                SSAOp::Subpiece {
                    src: lhs,
                    offset: lhs_offset,
                    ..
                },
                SSAOp::Subpiece {
                    src: rhs,
                    offset: rhs_offset,
                    ..
                },
            ) => lhs_offset == rhs_offset && equivalent_sources(lhs, rhs),
            (SSAOp::IntZExt { src: lhs, .. }, SSAOp::IntZExt { src: rhs, .. })
            | (SSAOp::IntSExt { src: lhs, .. }, SSAOp::IntSExt { src: rhs, .. })
            | (SSAOp::Trunc { src: lhs, .. }, SSAOp::Trunc { src: rhs, .. })
            | (SSAOp::Cast { src: lhs, .. }, SSAOp::Cast { src: rhs, .. }) => {
                equivalent_sources(lhs, rhs)
            }
            _ => false,
        })
    })()
    .unwrap_or(false);
    visiting.remove(&pair);
    equivalent
}

fn normalize_zero_sub_compare_operands(
    kind: CompareKind,
    lhs: &SSAVar,
    rhs: &SSAVar,
    lhs_id: ValueId,
    rhs_id: ValueId,
    sub_sources: &BTreeMap<SSAVar, (ValueId, ValueId)>,
) -> (ValueId, ValueId) {
    if !matches!(kind, CompareKind::Equal | CompareKind::NotEqual) {
        return (lhs_id, rhs_id);
    }
    if const_value(rhs) == Some(0)
        && let Some((sub_lhs, sub_rhs)) = sub_sources.get(lhs).copied()
    {
        return (sub_lhs, sub_rhs);
    }
    if const_value(lhs) == Some(0)
        && let Some((sub_lhs, sub_rhs)) = sub_sources.get(rhs).copied()
    {
        return (sub_lhs, sub_rhs);
    }
    (lhs_id, rhs_id)
}

fn signed_flag_compare_components<'a>(
    graph: &SsaGraph,
    op: &'a SSAOp,
    signed_overflow_sources: &BTreeMap<SSAVar, (ValueId, ValueId)>,
    signed_sign_sources: &BTreeMap<SSAVar, (ValueId, ValueId)>,
) -> Option<(&'a SSAVar, CompareKind, ValueId, ValueId)> {
    let (dst, a, b, equal) = match op {
        SSAOp::IntNotEqual { dst, a, b } => (dst, a, b, false),
        SSAOp::IntEqual { dst, a, b } => (dst, a, b, true),
        _ => return None,
    };
    let overflow = signed_overflow_sources.get(a);
    let sign = signed_sign_sources.get(b);
    let (lhs, rhs) = overflow
        .zip(sign)
        .filter(|(overflow, sign)| compare_operand_pairs_equivalent(graph, overflow, sign))
        .map(|(overflow, _)| *overflow)
        .or_else(|| {
            let overflow = signed_overflow_sources.get(b);
            let sign = signed_sign_sources.get(a);
            overflow
                .zip(sign)
                .filter(|(overflow, sign)| compare_operand_pairs_equivalent(graph, overflow, sign))
                .map(|(overflow, _)| *overflow)
        })?;
    Some(if equal {
        (dst, CompareKind::SignedLessEqual, rhs, lhs)
    } else {
        (dst, CompareKind::SignedLess, lhs, rhs)
    })
}

fn compare_operand_pairs_equivalent(
    graph: &SsaGraph,
    lhs: &(ValueId, ValueId),
    rhs: &(ValueId, ValueId),
) -> bool {
    compare_values_equivalent(graph, lhs.0, rhs.0) && compare_values_equivalent(graph, lhs.1, rhs.1)
}

fn compare_components(op: &SSAOp) -> Option<(&SSAVar, CompareKind, &SSAVar, &SSAVar)> {
    match op {
        SSAOp::IntEqual { dst, a, b } => Some((dst, CompareKind::Equal, a, b)),
        SSAOp::IntNotEqual { dst, a, b } => Some((dst, CompareKind::NotEqual, a, b)),
        SSAOp::IntLess { dst, a, b } => Some((dst, CompareKind::Less, a, b)),
        SSAOp::IntSLess { dst, a, b } => Some((dst, CompareKind::SignedLess, a, b)),
        SSAOp::IntLessEqual { dst, a, b } => Some((dst, CompareKind::LessEqual, a, b)),
        SSAOp::IntSLessEqual { dst, a, b } => Some((dst, CompareKind::SignedLessEqual, a, b)),
        _ => None,
    }
}

fn memory_location_for_addr(
    prep_facts: Option<&DecompilePrepFacts>,
    addresses: &AddressProvenanceFacts,
    object_model: &ObjectModel,
    graph: &SsaGraph,
    addr: &SSAVar,
    space: SpaceId,
    size: u32,
) -> MemoryLocation {
    let parameter_expression = (space == SpaceId::Ram)
        .then(|| {
            graph
                .value_id_for_var(addr)
                .and_then(|value| addresses.parameter_expression(value))
        })
        .flatten();
    let object = object_model
        .object_for_var(graph, addr, space)
        .or_else(|| {
            resolve_stack_root(prep_facts, addr).and_then(|root| {
                object_model
                    .stack_objects
                    .get(&StackObjectKey { root, space })
                    .copied()
            })
        })
        .or_else(|| {
            resolve_const_value(prep_facts, addr).and_then(|address| {
                object_model
                    .global_objects
                    .get(&GlobalObjectKey { space, address })
                    .copied()
            })
        })
        .or_else(|| object_model.escaped_unknown_object(space))
        .unwrap_or(ObjectId(0));
    MemoryLocation {
        space,
        object,
        address: parameter_expression.map_or_else(
            || {
                if matches!(
                    object_model.object(object).map(|fact| &fact.kind),
                    Some(ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. })
                        | Some(ObjectKind::Global { .. })
                ) {
                    RelativeMemoryAddress::Exact(0)
                } else {
                    RelativeMemoryAddress::Unknown
                }
            },
            |expression| {
                if expression.terms.is_empty() {
                    RelativeMemoryAddress::Exact(expression.offset)
                } else {
                    RelativeMemoryAddress::Affine {
                        terms: expression.terms.clone(),
                        offset: expression.offset,
                    }
                }
            },
        ),
        size,
    }
}

fn resolve_const_value(facts: Option<&DecompilePrepFacts>, var: &SSAVar) -> Option<u64> {
    let root = canonical_value_root(facts, var);
    const_value(root).or_else(|| const_value(var))
}

fn resolve_graph_literal_value(
    graph: &SsaGraph,
    facts: Option<&DecompilePrepFacts>,
    var: &SSAVar,
) -> Option<u64> {
    let root = canonical_value_root(facts, var);
    let value = graph
        .value_id_for_var(root)
        .or_else(|| graph.value_id_for_var(var))
        .and_then(|id| graph.value(id))?;
    value.var.constant_bits().or_else(|| {
        value.canonical_storage.and_then(|storage| {
            matches!(
                storage.space,
                CanonicalStorageSpace::Constant | CanonicalStorageSpace::Ram
            )
            .then_some(storage.offset)
        })
    })
}

fn direct_target_from_raw_identity(identity: SourceCallSiteIdentity) -> Option<u64> {
    let target = identity.target();
    matches!(
        target.space,
        CanonicalStorageSpace::Constant | CanonicalStorageSpace::Ram
    )
    .then_some(target.offset)
}

fn resolve_stack_root(
    facts: Option<&DecompilePrepFacts>,
    var: &SSAVar,
) -> Option<StackAddressRoot> {
    let facts = facts?;
    let root = canonical_value_root(Some(facts), var);
    facts
        .stack_address_root_of(var)
        .copied()
        .or_else(|| facts.stack_address_root_of(root).copied())
}

fn resolve_entry_stack_root(
    facts: Option<&DecompilePrepFacts>,
    var: &SSAVar,
) -> Option<StackAddressRoot> {
    let facts = facts?;
    let root = canonical_value_root(Some(facts), var);
    facts
        .entry_stack_address_root_of(var)
        .copied()
        .or_else(|| facts.entry_stack_address_root_of(root).copied())
}

fn canonical_value_root<'a>(facts: Option<&'a DecompilePrepFacts>, var: &'a SSAVar) -> &'a SSAVar {
    let Some(facts) = facts else {
        return var;
    };
    let mut current = var;
    for _ in 0..32 {
        let Some(next) = facts.canonical_root_of(current) else {
            break;
        };
        if next == current {
            break;
        }
        current = next;
    }
    current
}

fn const_value(var: &SSAVar) -> Option<u64> {
    var.constant_bits()
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{
        CallBoundarySlot, ControlGuard, GlobalObjectKey, MemoryDefFact, MemoryLocation,
        MemorySSAFacts, MemoryUseFact, MemoryVersion, ObjectFact, ObjectId, ObjectKind,
        ObjectModel, ObjectModelBuilder, ObjectSpaceId, RelativeMemoryAddress, ReturnCarrier,
        SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION, SourceReturnRegisterCompositionFact,
        SourceReturnRegisterDefinitionFact, StackReloadSourceCertificate, StructuredAccessId,
        memory_locations_may_alias,
    };
    use crate::{
        AddressProvenanceFacts, AnalysisAssumption, AssumptionProvenance, AssumptionScope,
        AssumptionSet, AssumptionSubject, AssumptionValue, CanonicalStorageId,
        CanonicalStorageSpace, DecompilePrepFacts, InstId, InstPayload, SSAOp, SSAVar,
        SemanticObligationKind, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SourceStackSlotSpec, SsaArtifact, StackAddressBase, StackAddressRoot,
        ValueId,
    };
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn test_reg(offset: u64) -> Varnode {
        Varnode::new(SpaceId::Register, offset, 8)
    }

    fn test_const(value: u64) -> Varnode {
        Varnode::constant(value, 8)
    }

    fn dual_space_artifact(
        mut prefix: Vec<R2ILOp>,
        addr: Varnode,
        arch: Option<&ArchSpec>,
    ) -> SsaArtifact {
        prefix.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 8),
            space: SpaceId::Ram,
            addr: addr.clone(),
        });
        prefix.push(R2ILOp::Load {
            dst: Varnode::unique(0x108, 8),
            space: SpaceId::Custom(7),
            addr,
        });
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: prefix,
                switch_info: None,
                op_metadata: Default::default(),
            }],
            arch,
        )
        .expect("dual-space artifact")
    }

    fn dual_space_locations(artifact: &SsaArtifact) -> (MemoryLocation, MemoryLocation) {
        let block = artifact.get_block(0x1000).expect("dual-space block");
        let mut loads = block
            .ops
            .iter()
            .enumerate()
            .filter(|(_, op)| matches!(op, crate::SSAOp::Load { .. }));
        let ram_index = loads.next().expect("RAM load").0;
        let custom_index = loads.next().expect("Custom load").0;
        let ram = artifact
            .memory_uses_for_op_site(0x1000, ram_index)
            .and_then(|uses| uses.first())
            .expect("RAM location")
            .location
            .clone();
        let custom = artifact
            .memory_uses_for_op_site(0x1000, custom_index)
            .and_then(|uses| uses.first())
            .expect("Custom location")
            .location
            .clone();
        (ram, custom)
    }

    fn assert_dual_space_objects_are_distinct(artifact: &SsaArtifact) {
        let (ram, custom) = dual_space_locations(artifact);
        assert_eq!(ram.space, SpaceId::Ram);
        assert_eq!(custom.space, SpaceId::Custom(7));
        assert_ne!(ram.object, custom.object);
        assert_eq!(
            artifact
                .objects()
                .object(ram.object)
                .map(|fact| fact.kind.space()),
            Some(SpaceId::Ram)
        );
        assert_eq!(
            artifact
                .objects()
                .object(custom.object)
                .map(|fact| fact.kind.space()),
            Some(SpaceId::Custom(7))
        );
        assert!(!memory_locations_may_alias(
            artifact.objects(),
            &ram,
            &custom
        ));
    }

    #[test]
    fn same_value_id_is_space_keyed_for_global_stack_parameter_and_unknown_objects() {
        let global = dual_space_artifact(Vec::new(), Varnode::constant(0x4000, 8), None);
        assert_dual_space_objects_are_distinct(&global);
        let (ram_global, custom_global) = dual_space_locations(&global);
        assert!(matches!(
            global
                .objects()
                .object(ram_global.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::Global {
                space: SpaceId::Ram,
                address: 0x4000
            })
        ));
        assert!(matches!(
            global
                .objects()
                .object(custom_global.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::Global {
                space: SpaceId::Custom(7),
                address: 0x4000
            })
        ));

        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0, 8));
        arch.add_register(RegisterDef::new("sp", 16, 8));

        let parameter = dual_space_artifact(Vec::new(), Varnode::register(0, 8), Some(&arch));
        assert_dual_space_objects_are_distinct(&parameter);
        let (ram_parameter, custom_parameter) = dual_space_locations(&parameter);
        assert!(matches!(
            parameter
                .objects()
                .object(ram_parameter.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::Parameter {
                space: SpaceId::Ram,
                index: 0
            })
        ));
        assert!(matches!(
            parameter
                .objects()
                .object(custom_parameter.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::EscapedUnknown {
                space: SpaceId::Custom(7)
            })
        ));
        assert_eq!(custom_parameter.address, RelativeMemoryAddress::Unknown);

        let stack = dual_space_artifact(Vec::new(), Varnode::unique(0x80, 8), Some(&arch));
        let stack_addr = stack
            .get_block(0x1000)
            .and_then(|block| {
                block.ops.iter().find_map(|op| match op {
                    crate::SSAOp::Load { addr, .. } => Some(addr.clone()),
                    _ => None,
                })
            })
            .expect("stack address");
        let mut stack_facts = DecompilePrepFacts::default();
        stack_facts.stack_address_roots.insert(
            stack_addr.clone(),
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -8,
            },
        );
        let stack_objects = super::ObjectModelBuilder::new(
            Some(&stack_facts),
            stack.addresses(),
            Some(stack.machine_context()),
        )
        .build(stack.function(), stack.graph());
        let ram_stack = super::memory_location_for_addr(
            Some(&stack_facts),
            stack.addresses(),
            &stack_objects,
            stack.graph(),
            &stack_addr,
            SpaceId::Ram,
            8,
        );
        let custom_stack = super::memory_location_for_addr(
            Some(&stack_facts),
            stack.addresses(),
            &stack_objects,
            stack.graph(),
            &stack_addr,
            SpaceId::Custom(7),
            8,
        );
        assert_ne!(ram_stack.object, custom_stack.object);
        assert!(!memory_locations_may_alias(
            &stack_objects,
            &ram_stack,
            &custom_stack
        ));
        let ram_stack_kind = stack_objects
            .object(ram_stack.object)
            .map(|fact| &fact.kind);
        assert!(
            matches!(
                ram_stack_kind,
                Some(
                    ObjectKind::StackSlot {
                        space: SpaceId::Ram,
                        ..
                    } | ObjectKind::FrameObject {
                        space: SpaceId::Ram,
                        ..
                    }
                )
            ),
            "unexpected RAM stack object: {ram_stack_kind:?}"
        );
        assert!(matches!(
            stack_objects
                .object(custom_stack.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::EscapedUnknown {
                space: SpaceId::Custom(7)
            })
        ));
        assert_eq!(custom_stack.address, RelativeMemoryAddress::Unknown);

        let unknown = dual_space_artifact(Vec::new(), Varnode::unique(0x90, 8), None);
        assert_dual_space_objects_are_distinct(&unknown);
        let (ram_unknown, custom_unknown) = dual_space_locations(&unknown);
        assert!(matches!(
            unknown
                .objects()
                .object(ram_unknown.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::EscapedUnknown {
                space: SpaceId::Ram
            })
        ));
        assert!(matches!(
            unknown
                .objects()
                .object(custom_unknown.object)
                .map(|fact| &fact.kind),
            Some(ObjectKind::EscapedUnknown {
                space: SpaceId::Custom(7)
            })
        ));
    }

    #[test]
    fn stack_helpers_require_exact_ram_source_fact_object_and_memory_location() {
        let mut block = R2ILBlock::new(0x1100, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 8),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x4000, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], None).expect("RAM load artifact");
        let access = artifact
            .facts()
            .structured
            .memory_accesses
            .values()
            .next()
            .expect("RAM load access")
            .clone();
        let mut objects = artifact.objects().clone();
        objects
            .objects
            .get_mut(&access.object)
            .expect("RAM load object")
            .kind = ObjectKind::StackSlot {
            space: SpaceId::Ram,
            base: StackAddressBase::StackPointer,
            offset: -8,
        };
        let structured = artifact.facts().structured.clone();

        assert!(super::ram_memory_access_matches_source(
            artifact.function(),
            artifact.graph(),
            &objects,
            &access,
        ));
        assert_eq!(
            super::stack_memory_access_at(super::StackMemoryAccessInput {
                function: artifact.function(),
                graph: artifact.graph(),
                structured: &structured,
                objects: &objects,
                block_addr: access.block_addr,
                op_index: access.op_index,
                is_write: false,
                value: access.value,
            }),
            Some((access.object, -8, access.id))
        );
        let facts = artifact.facts();
        let certificates = super::collect_prepared_function_certificates(
            &facts.boundaries,
            artifact.function(),
            artifact.graph(),
            &objects,
            &facts.memory,
            &facts.predicates,
            &facts.call_sites,
            &structured,
        );
        assert_eq!(
            certificates
                .stack_slots
                .get(&access.object)
                .map(|slot| slot.space),
            Some(SpaceId::Ram)
        );

        let mut mismatched_fact = access.clone();
        mismatched_fact.space = SpaceId::Custom(7);
        assert!(!super::ram_memory_access_matches_source(
            artifact.function(),
            artifact.graph(),
            &objects,
            &mismatched_fact,
        ));

        let mut mismatched_objects = objects.clone();
        mismatched_objects
            .objects
            .get_mut(&access.object)
            .expect("RAM load object")
            .kind = ObjectKind::StackSlot {
            space: SpaceId::Custom(7),
            base: StackAddressBase::StackPointer,
            offset: -8,
        };
        assert!(!super::ram_memory_access_matches_source(
            artifact.function(),
            artifact.graph(),
            &mismatched_objects,
            &access,
        ));
        let certificates = super::collect_prepared_function_certificates(
            &facts.boundaries,
            artifact.function(),
            artifact.graph(),
            &mismatched_objects,
            &facts.memory,
            &facts.predicates,
            &facts.call_sites,
            &structured,
        );
        assert!(!certificates.stack_slots.contains_key(&access.object));

        let mut mismatched_memory = artifact.facts().memory.clone();
        for use_fact in mismatched_memory
            .uses_by_inst
            .get_mut(&access.id.inst)
            .expect("RAM memory use")
        {
            use_fact.location.space = SpaceId::Custom(7);
        }
        assert!(super::unique_memory_use_for_access(&mismatched_memory, &access).is_none());
    }

    #[test]
    fn calls_clobber_every_present_typed_memory_space() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 8),
            space: SpaceId::Custom(7),
            addr: Varnode::constant(0x4000, 8),
        });
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x2000, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], None).expect("call artifact");
        let call_index = artifact
            .get_block(0x1000)
            .expect("call block")
            .ops
            .iter()
            .position(|op| matches!(op, crate::SSAOp::Call { .. }))
            .expect("call op");
        let spaces = artifact
            .memory_defs_for_op_site(0x1000, call_index)
            .expect("call memory defs")
            .iter()
            .map(|fact| fact.location.space)
            .collect::<Vec<_>>();
        assert_eq!(spaces, vec![SpaceId::Ram, SpaceId::Custom(7)]);
    }

    #[test]
    fn malformed_location_object_space_mismatch_never_proves_no_alias() {
        let object = ObjectId(1);
        let mut objects = ObjectModel::default();
        objects.objects.insert(
            object,
            ObjectFact {
                id: object,
                kind: ObjectKind::Global {
                    space: SpaceId::Ram,
                    address: 0x4000,
                },
            },
        );
        let malformed = MemoryLocation {
            space: SpaceId::Custom(7),
            object,
            address: RelativeMemoryAddress::Exact(0),
            size: 8,
        };
        let valid = MemoryLocation {
            space: SpaceId::Ram,
            object,
            address: RelativeMemoryAddress::Exact(0x1000),
            size: 8,
        };
        assert!(memory_locations_may_alias(&objects, &malformed, &valid));
    }

    #[test]
    fn exact_entry_stack_coordinates_refine_cross_base_aliasing_fail_closed() {
        let saved = ObjectId(1);
        let local = ObjectId(2);
        let mut objects = ObjectModel::default();
        objects.objects.insert(
            saved,
            ObjectFact {
                id: saved,
                kind: ObjectKind::StackSlot {
                    space: SpaceId::Ram,
                    base: StackAddressBase::StackPointer,
                    offset: -8,
                },
            },
        );
        objects.objects.insert(
            local,
            ObjectFact {
                id: local,
                kind: ObjectKind::StackSlot {
                    space: SpaceId::Ram,
                    base: StackAddressBase::FramePointer,
                    offset: -8,
                },
            },
        );
        objects
            .address_bits_by_space
            .insert(ObjectSpaceId(SpaceId::Ram), 64);
        objects.entry_stack_roots.insert(
            saved,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -8,
            },
        );
        objects.entry_stack_roots.insert(
            local,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -16,
            },
        );
        let saved_location = MemoryLocation {
            space: SpaceId::Ram,
            object: saved,
            address: RelativeMemoryAddress::Exact(0),
            size: 8,
        };
        let local_location = MemoryLocation {
            space: SpaceId::Ram,
            object: local,
            address: RelativeMemoryAddress::Exact(0),
            size: 4,
        };
        assert!(!memory_locations_may_alias(
            &objects,
            &saved_location,
            &local_location
        ));

        objects.entry_stack_roots.remove(&local);
        assert!(memory_locations_may_alias(
            &objects,
            &saved_location,
            &local_location
        ));
        objects.entry_stack_roots.insert(
            local,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -8,
            },
        );
        assert!(memory_locations_may_alias(
            &objects,
            &saved_location,
            &local_location
        ));

        objects.entry_stack_roots.insert(
            saved,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: i64::MAX,
            },
        );
        objects.entry_stack_roots.insert(
            local,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: i64::MIN,
            },
        );
        let two_byte_saved = MemoryLocation {
            size: 2,
            ..saved_location.clone()
        };
        assert!(memory_locations_may_alias(
            &objects,
            &two_byte_saved,
            &local_location
        ));

        objects
            .address_bits_by_space
            .insert(ObjectSpaceId(SpaceId::Ram), 32);
        objects.entry_stack_roots.insert(
            saved,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: i64::from(i32::MAX),
            },
        );
        objects.entry_stack_roots.insert(
            local,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: i64::from(i32::MIN),
            },
        );
        assert!(memory_locations_may_alias(
            &objects,
            &two_byte_saved,
            &local_location
        ));

        objects.address_bits_by_space.clear();
        assert!(memory_locations_may_alias(
            &objects,
            &saved_location,
            &local_location
        ));
    }

    #[test]
    fn conflicting_entry_stack_coordinates_permanently_drop_alias_refinement() {
        let addresses = AddressProvenanceFacts::default();
        let mut builder = ObjectModelBuilder::new(None, &addresses, None);
        let object = ObjectId(7);
        let first = StackAddressRoot {
            base: StackAddressBase::StackPointer,
            offset: -16,
        };
        builder.record_entry_stack_root(object, first);
        builder.record_entry_stack_root(object, first);
        assert_eq!(builder.entry_stack_roots.get(&object), Some(&first));
        builder.record_entry_stack_root(
            object,
            StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -24,
            },
        );
        assert!(!builder.entry_stack_roots.contains_key(&object));
        builder.record_entry_stack_root(object, first);
        assert!(!builder.entry_stack_roots.contains_key(&object));
    }

    #[test]
    fn memory_ssa_separates_saved_sp_slot_from_frame_relative_local() {
        let sp = Varnode::register(0, 8);
        let fp = Varnode::register(8, 8);
        let ra = Varnode::register(16, 8);
        let local_addr = Varnode::unique(0x100, 8);
        let mut block = R2ILBlock::new(0x3600, 4);
        block.push(R2ILOp::IntSub {
            dst: sp.clone(),
            a: sp.clone(),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: sp.clone(),
            val: fp.clone(),
        });
        block.push(R2ILOp::Copy {
            dst: fp.clone(),
            src: sp.clone(),
        });
        block.push(R2ILOp::IntSub {
            dst: local_addr.clone(),
            a: fp.clone(),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: local_addr.clone(),
            val: Varnode::constant(1, 4),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x108, 4),
            space: SpaceId::Ram,
            addr: local_addr,
        });
        block.push(R2ILOp::Return { target: ra });

        let mut arch = ArchSpec::new("dual-stack-coordinate-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("fp", 8, 8));
        arch.add_register(RegisterDef::new("ra", 16, 8));
        arch.add_space(r2il::AddressSpace::ram(8));
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"dual-stack-coordinate-revision-1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(8),
                -8,
                4,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0)))
        .expect("exact dual-coordinate interface");
        let artifact = SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("dual-coordinate artifact");

        let [save] = artifact
            .memory_defs_for_op_site(0x3600, 1)
            .expect("saved-frame definition")
        else {
            panic!("one saved-frame definition")
        };
        let [local_store] = artifact
            .memory_defs_for_op_site(0x3600, 4)
            .expect("local definition")
        else {
            panic!("one local definition")
        };
        let [local_load] = artifact
            .memory_uses_for_op_site(0x3600, 5)
            .expect("local use")
        else {
            panic!("one local use")
        };
        assert_ne!(save.location.object, local_store.location.object);
        assert_eq!(
            local_store.previous_version.object,
            local_store.location.object
        );
        assert_eq!(local_store.previous_version.version, 0);
        assert_eq!(local_load.location, local_store.location);
        assert_eq!(local_load.version, local_store.next_version);
        assert!(matches!(
            artifact
                .objects()
                .object(save.location.object)
                .map(|object| &object.kind),
            Some(ObjectKind::StackSlot {
                base: StackAddressBase::StackPointer,
                offset: -8,
                ..
            })
        ));
        assert!(matches!(
            artifact
                .objects()
                .object(local_store.location.object)
                .map(|object| &object.kind),
            Some(ObjectKind::StackSlot {
                base: StackAddressBase::FramePointer,
                offset: -8,
                ..
            })
        ));
        assert_eq!(
            artifact
                .objects()
                .entry_stack_roots
                .get(&save.location.object),
            Some(&StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -8,
            })
        );
        assert_eq!(
            artifact
                .objects()
                .entry_stack_roots
                .get(&local_store.location.object),
            Some(&StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -16,
            })
        );
    }

    #[test]
    fn global_object_key_order_binds_exact_typed_space() {
        let keys = [
            GlobalObjectKey {
                space: SpaceId::Ram,
                address: 0x4000,
            },
            GlobalObjectKey {
                space: SpaceId::Custom(1),
                address: 0x4000,
            },
            GlobalObjectKey {
                space: SpaceId::Custom(2),
                address: 0x4000,
            },
        ];
        let expected = keys.clone();
        let ordered = keys.into_iter().collect::<std::collections::BTreeSet<_>>();
        assert_eq!(ordered.len(), 3);
        assert_eq!(ordered.into_iter().collect::<Vec<_>>(), expected);
    }

    #[test]
    fn global_aliasing_keeps_exact_typed_memory_spaces_disjoint() {
        let ram = ObjectId(1);
        let custom = ObjectId(2);
        let mut objects = ObjectModel::default();
        objects.objects.insert(
            ram,
            ObjectFact {
                id: ram,
                kind: ObjectKind::Global {
                    space: SpaceId::Ram,
                    address: 0x4000,
                },
            },
        );
        objects.objects.insert(
            custom,
            ObjectFact {
                id: custom,
                kind: ObjectKind::Global {
                    space: SpaceId::Custom(7),
                    address: 0x4000,
                },
            },
        );
        let location = |space, object| MemoryLocation {
            space,
            object,
            address: RelativeMemoryAddress::Exact(0),
            size: 8,
        };
        assert!(!memory_locations_may_alias(
            &objects,
            &location(SpaceId::Ram, ram),
            &location(SpaceId::Custom(7), custom)
        ));
    }

    fn raw_memory_access(
        locations: Vec<MemoryLocation>,
        is_write: bool,
        width: u32,
    ) -> super::StructuredMemoryAccessFact {
        let inst = InstId(0);
        let space = locations
            .first()
            .map_or(SpaceId::Ram, |location| location.space);
        let mut objects = ObjectModel::default();
        for location in &locations {
            objects
                .objects
                .entry(location.object)
                .or_insert(ObjectFact {
                    id: location.object,
                    kind: ObjectKind::Global {
                        space: location.space,
                        address: 0,
                    },
                });
        }
        let mut memory = MemorySSAFacts::default();
        if is_write {
            memory.defs_by_inst.insert(
                inst,
                locations
                    .into_iter()
                    .enumerate()
                    .map(|(index, location)| MemoryDefFact {
                        location,
                        previous_version: MemoryVersion {
                            object: ObjectId(index as u32 + 100),
                            version: 1,
                        },
                        next_version: MemoryVersion {
                            object: ObjectId(index as u32 + 100),
                            version: 2,
                        },
                    })
                    .collect(),
            );
        } else {
            memory.uses_by_inst.insert(
                inst,
                locations
                    .into_iter()
                    .enumerate()
                    .map(|(index, location)| MemoryUseFact {
                        location,
                        version: MemoryVersion {
                            object: ObjectId(index as u32 + 100),
                            version: 1,
                        },
                    })
                    .collect(),
            );
        }
        let mut accesses = BTreeMap::new();
        let mut ordinal = 0;
        super::insert_raw_memory_subeffect(
            &mut accesses,
            &memory,
            &objects,
            inst,
            &mut ordinal,
            0x1000,
            0,
            ValueId(0),
            space,
            Some(ValueId(1)),
            is_write,
            width,
        );
        accesses
            .remove(&StructuredAccessId { inst, ordinal: 0 })
            .expect("raw memory access")
    }

    #[test]
    fn memory_access_provenance_ignores_duplicate_reaching_versions() {
        let location = MemoryLocation {
            space: SpaceId::Ram,
            object: ObjectId(7),
            address: RelativeMemoryAddress::Exact(-8),
            size: 8,
        };
        for is_write in [false, true] {
            let access = raw_memory_access(vec![location.clone(), location.clone()], is_write, 8);
            assert!(access.provenance_complete);
            assert_eq!(access.object, location.object);
        }
    }

    #[test]
    fn memory_access_provenance_rejects_distinct_location_ambiguity() {
        let location = MemoryLocation {
            space: SpaceId::Ram,
            object: ObjectId(7),
            address: RelativeMemoryAddress::Exact(-8),
            size: 8,
        };
        let mutations = [
            MemoryLocation {
                object: ObjectId(8),
                ..location.clone()
            },
            MemoryLocation {
                address: RelativeMemoryAddress::Exact(-16),
                ..location.clone()
            },
            MemoryLocation {
                size: 4,
                ..location.clone()
            },
        ];
        for mutation in mutations {
            for is_write in [false, true] {
                let access =
                    raw_memory_access(vec![location.clone(), mutation.clone()], is_write, 8);
                assert!(!access.provenance_complete);
            }
        }
    }

    #[test]
    fn display_names_do_not_resolve_constants_or_stack_roots() {
        let named_constant = SSAVar::new("ram:0x401000", 0, 8);
        assert_eq!(super::const_value(&named_constant), None);
        assert_eq!(super::resolve_const_value(None, &named_constant), None);

        let named_stack_pointer = SSAVar::new("rsp", 0, 8);
        assert_eq!(super::resolve_stack_root(None, &named_stack_pointer), None);

        let mut canonical_constant = SSAVar::constant(0x401000, 8);
        canonical_constant.name = "unrelated-display-name".to_string();
        assert_eq!(super::const_value(&canonical_constant), Some(0x401000));
    }

    fn conditional_block(addr: u64, selector: u64, target: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        let cond = Varnode::unique(addr, 1);
        block.push(R2ILOp::IntEqual {
            dst: cond.clone(),
            a: test_reg(selector),
            b: test_const(1),
        });
        block.push(R2ILOp::CBranch {
            target: test_const(target),
            cond,
        });
        block
    }

    fn branch_block(addr: u64, target: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(R2ILOp::Branch {
            target: test_const(target),
        });
        block
    }

    fn predicate_assumption_diamond() -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[
                conditional_block(0x9000, 0, 0x9040),
                branch_block(0x9004, 0x9080),
                branch_block(0x9040, 0x9080),
                R2ILBlock::new(0x9080, 4),
            ],
            None,
        )
        .expect("predicate-assumption diamond")
    }

    fn predicate_branch_assumption(
        predicate: &super::PredicateFact,
        block_addr: u64,
        predecessor: Option<u64>,
        truth: bool,
    ) -> AnalysisAssumption {
        AnalysisAssumption {
            id: Some("predicate-assumption-test".to_string()),
            subject: AssumptionSubject::Predicate {
                predicate: predicate.id,
                block_addr,
                predecessor,
            },
            value: AssumptionValue::Branch { truth },
            scope: AssumptionScope::Query,
            provenance: AssumptionProvenance::User,
        }
    }

    fn assert_conflicting_predicate_assumption_preserves_semantics(
        base: &SsaArtifact,
        assumption: AnalysisAssumption,
        expected_reason: &str,
    ) {
        let conditioned = base.with_assumptions(&AssumptionSet::new(vec![assumption.clone()]));

        assert_predicate_assumption_preserves_source_semantics(base, &conditioned);
        assert!(conditioned.facts().applied_assumption_bindings.is_empty());
        assert!(conditioned.facts().assumption_usage.applied.is_empty());
        assert!(conditioned.facts().assumption_usage.ignored.is_empty());
        assert_eq!(conditioned.facts().assumption_usage.conflicts.len(), 1);
        assert_eq!(
            conditioned.facts().assumption_usage.conflicts[0].assumption,
            assumption
        );
        assert_eq!(
            conditioned.facts().assumption_usage.conflicts[0].reason,
            expected_reason
        );
    }

    fn assert_predicate_assumption_preserves_source_semantics(
        base: &SsaArtifact,
        conditioned: &SsaArtifact,
    ) {
        assert_eq!(conditioned.predicates(), base.predicates());
        assert_eq!(conditioned.structured(), base.structured());
        assert_eq!(conditioned.control_domains(), base.control_domains());
        assert_eq!(conditioned.certificates(), base.certificates());
        assert_eq!(conditioned.obligations(), base.obligations());
    }

    #[test]
    fn predicate_branch_assumption_wrong_block_preserves_base_semantics() {
        let base = predicate_assumption_diamond();
        let predicate = base
            .predicates()
            .predicates
            .values()
            .next()
            .expect("diamond predicate")
            .clone();
        let assumption = predicate_branch_assumption(
            &predicate,
            predicate.true_target,
            Some(predicate.true_target),
            true,
        );

        assert_conflicting_predicate_assumption_preserves_semantics(
            &base,
            assumption,
            "predicate block mismatch (expected 0x9040, observed 0x9000)",
        );
    }

    #[test]
    fn predicate_branch_assumption_wrong_predecessor_preserves_base_semantics() {
        let base = predicate_assumption_diamond();
        let predicate = base
            .predicates()
            .predicates
            .values()
            .next()
            .expect("diamond predicate")
            .clone();
        let assumption = predicate_branch_assumption(
            &predicate,
            predicate.block_addr,
            Some(predicate.false_target),
            true,
        );

        assert_conflicting_predicate_assumption_preserves_semantics(
            &base,
            assumption,
            "branch predecessor 0x9004 does not match selected edge 0x9040",
        );
    }

    #[test]
    fn valid_predicate_branch_assumption_binds_without_mutating_source_facts() {
        let base = predicate_assumption_diamond();
        let predicate = base
            .predicates()
            .predicates
            .values()
            .next()
            .expect("diamond predicate")
            .clone();
        let assumption = predicate_branch_assumption(
            &predicate,
            predicate.block_addr,
            Some(predicate.true_target),
            true,
        );
        let conditioned = base.with_assumptions(&AssumptionSet::new(vec![assumption.clone()]));

        assert_predicate_assumption_preserves_source_semantics(&base, &conditioned);
        assert_eq!(conditioned.facts().assumption_usage.applied, [assumption]);
        assert!(conditioned.facts().assumption_usage.ignored.is_empty());
        assert!(conditioned.facts().assumption_usage.conflicts.is_empty());
        assert_eq!(conditioned.facts().applied_assumption_bindings.len(), 1);
        assert!(matches!(
            conditioned.facts().applied_assumption_bindings[0].binding,
            super::PreparedAssumptionBindingKind::Predicate {
                predicate: bound,
                block_addr,
                predecessor: Some(selected),
                truth: true,
            } if bound == predicate.id
                && block_addr == predicate.block_addr
                && selected == predicate.true_target
        ));
    }

    #[test]
    fn contradictory_predicate_branch_assumptions_leave_source_facts_unchanged() {
        let base = predicate_assumption_diamond();
        let predicate = base
            .predicates()
            .predicates
            .values()
            .next()
            .expect("diamond predicate")
            .clone();
        let assumptions = AssumptionSet::new(vec![
            predicate_branch_assumption(
                &predicate,
                predicate.block_addr,
                Some(predicate.true_target),
                true,
            ),
            predicate_branch_assumption(
                &predicate,
                predicate.block_addr,
                Some(predicate.false_target),
                false,
            ),
        ]);
        let conditioned = base.with_assumptions(&assumptions);

        assert_predicate_assumption_preserves_source_semantics(&base, &conditioned);
        assert!(conditioned.facts().applied_assumption_bindings.is_empty());
        assert!(conditioned.facts().assumption_usage.applied.is_empty());
        assert!(conditioned.facts().assumption_usage.ignored.is_empty());
        assert_eq!(conditioned.facts().assumption_usage.conflicts.len(), 2);
        assert!(
            conditioned
                .facts()
                .assumption_usage
                .conflicts
                .iter()
                .all(|conflict| {
                    conflict.reason == "contradictory branch truths for predicate 0"
                })
        );
    }

    #[test]
    fn contradictory_predicate_preflight_is_input_order_independent() {
        let base = predicate_assumption_diamond();
        let predicate = base
            .predicates()
            .predicates
            .values()
            .next()
            .expect("diamond predicate")
            .clone();
        let truth = predicate_branch_assumption(
            &predicate,
            predicate.block_addr,
            Some(predicate.true_target),
            true,
        );
        let falsehood = predicate_branch_assumption(
            &predicate,
            predicate.block_addr,
            Some(predicate.false_target),
            false,
        );
        let first =
            base.with_assumptions(&AssumptionSet::new(vec![truth.clone(), falsehood.clone()]));
        let second = base.with_assumptions(&AssumptionSet::new(vec![falsehood, truth]));

        for conditioned in [&first, &second] {
            assert_predicate_assumption_preserves_source_semantics(&base, conditioned);
            assert!(conditioned.facts().applied_assumption_bindings.is_empty());
            assert_eq!(conditioned.facts().assumption_usage.conflicts.len(), 2);
            assert_eq!(
                conditioned
                    .facts()
                    .assumption_usage
                    .conflicts
                    .iter()
                    .filter_map(|conflict| match conflict.assumption.value {
                        AssumptionValue::Branch { truth } => Some(truth),
                        _ => None,
                    })
                    .collect::<BTreeSet<_>>(),
                BTreeSet::from([false, true])
            );
        }
    }

    fn return_boundary_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("return-boundary-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch.add_register(RegisterDef::new("cond", 24, 1));
        arch.add_register(RegisterDef::new("sp", 32, 8));
        arch.add_register(RegisterDef::sub("sp_low", 32, 4, "sp"));
        arch.add_register(RegisterDef::new("return_transport", 40, 8));
        arch
    }

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn return_boundary_interface() -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"return-boundary-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, register_storage(8, 8))],
            SourceFunctionReturn::Register {
                storage: register_storage(0, 8),
            },
            [],
        )
        .expect("return boundary interface")
    }

    fn preserved_stack_interface() -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            b"preserved-stack-revision-1".to_vec(),
            "test-register-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(16, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(32, 8)))
        .expect("typed return-address and stack-pointer roles")
    }

    fn complete_return_interface(return_kind: SourceFunctionReturn) -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            b"complete-return-certificate-revision-1".to_vec(),
            "test-register-abi",
            [],
            return_kind,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(16, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(32, 8)))
        .expect("complete return interface")
    }

    fn complete_return_artifact(return_kind: SourceFunctionReturn) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x2f00, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        SsaArtifact::for_decompile_with_interface(
            &[block],
            Some(&return_boundary_arch()),
            complete_return_interface(return_kind),
        )
        .expect("complete return artifact")
    }

    #[test]
    fn return_certificate_requires_one_complete_source_boundary_value() {
        let storage = register_storage(0, 8);
        let artifact = complete_return_artifact(SourceFunctionReturn::Register { storage });
        let boundary = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(boundary.complete);
        assert!(boundary.register_compositions.is_empty());
        let [boundary_value] = boundary.values.as_slice() else {
            panic!("complete register return must expose one value")
        };
        let (block_addr, op_index) = artifact
            .graph()
            .op_site_for_inst(boundary.at)
            .expect("return op site");
        let certificate = artifact
            .return_certificate_for_op(block_addr, op_index)
            .expect("complete boundary value certificate");
        assert_eq!(certificate.at, boundary.at);
        assert_eq!(certificate.value, boundary_value.value);
        assert_eq!(certificate.width, 8);
        assert_eq!(
            certificate.carrier,
            Some(ReturnCarrier::Register { storage })
        );

        let mut ambiguous = artifact.facts().boundaries.clone();
        ambiguous
            .returns
            .get_mut(&boundary.at)
            .expect("return boundary")
            .values
            .push(*boundary_value);
        let (certificates, by_inst) = super::collect_return_value_certificates(
            &ambiguous,
            artifact.graph(),
            &artifact.certificates().stack_reloads,
        );
        assert!(certificates.is_empty());
        assert!(by_inst.is_empty());

        let mut composed = artifact.facts().boundaries.clone();
        let producer = artifact
            .graph()
            .def_inst(boundary_value.value)
            .expect("returned value producer");
        composed
            .returns
            .get_mut(&boundary.at)
            .expect("return boundary")
            .register_compositions
            .push(SourceReturnRegisterCompositionFact {
                schema_version: SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION,
                slot: boundary_value.slot,
                base: SourceReturnRegisterDefinitionFact {
                    storage,
                    value: boundary_value.value,
                    producer,
                },
                overlays: Vec::new(),
            });
        let (certificates, by_inst) = super::collect_return_value_certificates(
            &composed,
            artifact.graph(),
            &artifact.certificates().stack_reloads,
        );
        assert!(certificates.is_empty());
        assert!(by_inst.is_empty());
    }

    #[test]
    fn complete_void_boundary_owns_no_return_value_certificate() {
        let artifact = complete_return_artifact(SourceFunctionReturn::Void);
        let boundary = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(boundary.complete);
        assert!(boundary.values.is_empty());
        assert!(artifact.certificates().returns.is_empty());
    }

    #[test]
    fn stack_return_carrier_requires_stack_reload_certificate() {
        let storage = register_storage(0, 8);
        let artifact = complete_return_artifact(SourceFunctionReturn::Register { storage });
        let boundary = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        let mut value = boundary.values[0];
        value.slot = CallBoundarySlot::Stack(-8);
        assert_eq!(
            super::return_carrier_for_boundary_value(&value, &BTreeMap::new()),
            None
        );

        let access = StructuredAccessId {
            inst: boundary.at,
            ordinal: 0,
        };
        let object = ObjectId(7);
        let reload = StackReloadSourceCertificate {
            value: value.value,
            reload: value.value,
            source: value.value,
            canonical_source: value.value,
            object,
            base: StackAddressBase::StackPointer,
            offset: -8,
            value_width: 8,
            memory_width: 8,
            store_access: access,
            load_access: access,
            store_inst: boundary.at,
            load_inst: boundary.at,
        };
        assert_eq!(
            super::return_carrier_for_boundary_value(
                &value,
                &BTreeMap::from([(value.value, reload)]),
            ),
            Some(ReturnCarrier::StackSlot {
                object,
                offset: -8,
                memory_access: Some(access),
            })
        );
    }

    fn composed_return_arch(whole_name: &str, slice_name: &str, pc_name: &str) -> ArchSpec {
        let mut arch = ArchSpec::new("return-composition-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 4));
        arch.add_register(RegisterDef::sub(slice_name, 0, 1, whole_name));
        arch.add_register(RegisterDef::new(pc_name, 16, 8));
        arch
    }

    fn composed_return_interface() -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"return-composition-revision-1".to_vec(),
            "test-register-abi",
            [],
            SourceFunctionReturn::Register {
                storage: register_storage(0, 4),
            },
            [],
        )
        .expect("composed return interface")
    }

    fn composed_return_block(addr: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 4),
            src: Varnode::constant(0, 4),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 1),
            src: Varnode::constant(1, 1),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 1),
            src: Varnode::constant(0, 1),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        block
    }

    fn composed_return_artifact(
        addr: u64,
        whole_name: &str,
        slice_name: &str,
        pc_name: &str,
    ) -> SsaArtifact {
        SsaArtifact::for_decompile_with_interface(
            &[composed_return_block(addr)],
            Some(&composed_return_arch(whole_name, slice_name, pc_name)),
            composed_return_interface(),
        )
        .expect("composed return artifact")
    }

    #[test]
    fn return_boundary_recovery_accepts_identical_fanin_and_rejects_phi_free_cycles() {
        let mut entry = R2ILBlock::new(0x3000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x80, 8),
            src: Varnode::register(0, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x3020, 8),
            cond: Varnode::register(24, 1),
        });
        let mut right = R2ILBlock::new(0x3004, 4);
        right.push(R2ILOp::Branch {
            target: Varnode::ram(0x3030, 8),
        });
        let mut left = R2ILBlock::new(0x3020, 4);
        left.push(R2ILOp::Branch {
            target: Varnode::ram(0x3030, 8),
        });
        let mut joined = R2ILBlock::new(0x3030, 4);
        joined.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let fanin = SsaArtifact::raw_with_interface(
            &[entry, right, left, joined],
            Some(&return_boundary_arch()),
            return_boundary_interface(),
        )
        .expect("fanin boundary artifact");
        let converged = super::reaching_abi_value_in_block(
            fanin.function(),
            fanin.graph(),
            fanin.machine_context(),
            0x3030,
            0,
            register_storage(0, 8),
        )
        .expect("both paths reach the same entry live-in");
        assert!(fanin.graph().def_inst(converged).is_none());

        let mut header = R2ILBlock::new(0x4000, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x4000, 8),
            cond: Varnode::register(24, 1),
        });
        let mut exit = R2ILBlock::new(0x4004, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let cycle = SsaArtifact::raw_with_interface(
            &[header, exit],
            Some(&return_boundary_arch()),
            return_boundary_interface(),
        )
        .expect("cycle boundary artifact");
        assert_eq!(
            super::reaching_abi_value_in_block(
                cycle.function(),
                cycle.graph(),
                cycle.machine_context(),
                0x4000,
                1,
                register_storage(0, 8),
            ),
            None
        );
    }

    #[test]
    fn exit_stack_pointer_requires_preserved_entry_or_identical_path_value() {
        let mut direct = R2ILBlock::new(0x6000, 4);
        direct.push(R2ILOp::Copy {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::register(32, 8),
        });
        direct.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let direct = SsaArtifact::raw_with_interface(
            &[direct],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("entry-live-in stack artifact");
        let direct_boundary = direct
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("direct return boundary");
        let entry_stack = direct_boundary
            .exit_stack_pointer
            .expect("entry stack pointer reaches return");
        assert_eq!(entry_stack.storage(), register_storage(32, 8));
        assert!(
            direct
                .graph()
                .def_inst(entry_stack.value().expect("explicit entry SP value"))
                .is_none()
        );
        assert!(direct_boundary.complete);

        let mut frameless = R2ILBlock::new(0x6050, 4);
        frameless.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let frameless = SsaArtifact::raw_with_interface(
            &[frameless],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("frameless stack artifact");
        let frameless_boundary = frameless
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("frameless return boundary");
        assert_eq!(
            frameless_boundary.exit_stack_pointer,
            Some(super::SourceReturnStackPointerFact::PreservedEntry {
                storage: register_storage(32, 8),
            })
        );
        assert!(frameless_boundary.complete);

        let mut loop_entry = R2ILBlock::new(0x6060, 4);
        loop_entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x6070, 8),
        });
        let mut loop_header = R2ILBlock::new(0x6070, 4);
        loop_header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x6070, 8),
            cond: Varnode::register(24, 1),
        });
        let mut loop_exit = R2ILBlock::new(0x6074, 4);
        loop_exit.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let loop_preserved = SsaArtifact::raw_with_interface(
            &[loop_entry, loop_header, loop_exit],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("loop-preserved stack artifact");
        let loop_boundary = loop_preserved
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("loop return boundary");
        assert_eq!(
            loop_boundary.exit_stack_pointer,
            Some(super::SourceReturnStackPointerFact::PreservedEntry {
                storage: register_storage(32, 8),
            })
        );
        assert!(loop_boundary.complete);

        let mut entry = R2ILBlock::new(0x6100, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x110, 8),
            src: Varnode::register(32, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x6120, 8),
            cond: Varnode::register(24, 1),
        });
        let mut right = R2ILBlock::new(0x6104, 4);
        right.push(R2ILOp::Branch {
            target: Varnode::ram(0x6130, 8),
        });
        let mut left = R2ILBlock::new(0x6120, 4);
        left.push(R2ILOp::Branch {
            target: Varnode::ram(0x6130, 8),
        });
        let mut joined = R2ILBlock::new(0x6130, 4);
        joined.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let convergent = SsaArtifact::raw_with_interface(
            &[entry, right, left, joined],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("convergent stack artifact");
        let convergent_boundary = convergent
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("convergent return boundary");
        let converged_stack = convergent_boundary
            .exit_stack_pointer
            .expect("identical paths retain the entry stack pointer");
        assert_eq!(converged_stack.storage(), register_storage(32, 8));
        assert!(
            convergent
                .graph()
                .def_inst(converged_stack.value().expect("converged entry SP value"))
                .is_none()
        );
        assert!(convergent_boundary.complete);
    }

    #[test]
    fn return_boundary_requires_declared_return_address_and_roots_it() {
        let mut exact = R2ILBlock::new(0x6150, 4);
        exact.push(R2ILOp::Copy {
            dst: Varnode::register(16, 8),
            src: Varnode::constant(0xfeed_face, 8),
        });
        exact.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let exact = SsaArtifact::raw_with_interface(
            &[exact],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("exact return-address artifact");
        let boundary = exact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("exact return boundary");
        let return_address = boundary.return_address.expect("declared return address");
        assert_eq!(return_address.storage, register_storage(16, 8));
        let producer = exact
            .graph()
            .def_inst(return_address.value)
            .expect("return-address producer");
        assert!(
            exact
                .obligations()
                .obligations_for_inst(producer)
                .any(|obligation| {
                    obligation.id.kind == SemanticObligationKind::LiveValueProducer
                })
        );
        assert!(boundary.complete);

        let mut transported = R2ILBlock::new(0x6154, 4);
        transported.push(R2ILOp::Copy {
            dst: Varnode::register(40, 8),
            src: Varnode::register(16, 8),
        });
        transported.push(R2ILOp::Return {
            target: Varnode::register(40, 8),
        });
        let transported = SsaArtifact::raw_with_interface(
            &[transported],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("transported return-address artifact");
        let transported_boundary = transported
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("transported return boundary");
        let transported_address = transported_boundary
            .return_address
            .expect("declared return address transported to control target");
        assert_eq!(transported_address.storage, register_storage(16, 8));
        assert_eq!(
            transported
                .graph()
                .value(transported_address.value)
                .and_then(|value| value.canonical_storage),
            Some(register_storage(40, 8))
        );
        let transport = transported
            .graph()
            .def_inst(transported_address.value)
            .and_then(|inst| transported.graph().inst(inst))
            .expect("exact return-address transport");
        assert!(matches!(
            transport.payload,
            InstPayload::Op(SSAOp::Copy { .. })
        ));
        assert!(
            transported
                .obligations()
                .obligations_for_inst(transport.id)
                .any(|obligation| obligation.id.kind == SemanticObligationKind::LiveValueProducer)
        );
        assert!(transported_boundary.complete);

        let mut wrong_source = R2ILBlock::new(0x6158, 4);
        wrong_source.push(R2ILOp::Copy {
            dst: Varnode::register(40, 8),
            src: Varnode::register(0, 8),
        });
        wrong_source.push(R2ILOp::Return {
            target: Varnode::register(40, 8),
        });

        let mut non_copy = R2ILBlock::new(0x615c, 4);
        non_copy.push(R2ILOp::IntAdd {
            dst: Varnode::register(40, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(0, 8),
        });
        non_copy.push(R2ILOp::Return {
            target: Varnode::register(40, 8),
        });

        let mut non_terminal = R2ILBlock::new(0x6160, 4);
        non_terminal.push(R2ILOp::Copy {
            dst: Varnode::register(40, 8),
            src: Varnode::register(16, 8),
        });
        non_terminal.push(R2ILOp::Nop);
        non_terminal.push(R2ILOp::Return {
            target: Varnode::register(40, 8),
        });

        let mut copy_chain = R2ILBlock::new(0x6164, 4);
        copy_chain.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(16, 8),
        });
        copy_chain.push(R2ILOp::Copy {
            dst: Varnode::register(40, 8),
            src: Varnode::register(0, 8),
        });
        copy_chain.push(R2ILOp::Return {
            target: Varnode::register(40, 8),
        });

        for corrupt in [wrong_source, non_copy, non_terminal, copy_chain] {
            let artifact = SsaArtifact::raw_with_interface(
                &[corrupt],
                Some(&return_boundary_arch()),
                preserved_stack_interface(),
            )
            .expect("invalid transported return-address artifact");
            let boundary = artifact
                .facts()
                .boundaries
                .returns
                .values()
                .next()
                .expect("invalid transported return boundary");
            assert!(boundary.return_address.is_none());
            assert!(!boundary.complete);
        }

        for target in [Varnode::register(0, 8), Varnode::constant(0, 8)] {
            let mut corrupt = R2ILBlock::new(0x6168, 4);
            corrupt.push(R2ILOp::Return { target });
            let artifact = SsaArtifact::raw_with_interface(
                &[corrupt],
                Some(&return_boundary_arch()),
                preserved_stack_interface(),
            )
            .expect("corrupt return-address artifact");
            let boundary = artifact
                .facts()
                .boundaries
                .returns
                .values()
                .next()
                .expect("corrupt return boundary");
            assert!(boundary.return_address.is_none());
            assert!(!boundary.complete);
        }
    }

    #[test]
    fn exit_stack_pointer_refuses_divergence_calls_and_partial_writes() {
        let divergent_blocks = || {
            let mut entry = R2ILBlock::new(0x6200, 4);
            entry.push(R2ILOp::Copy {
                dst: Varnode::unique(0x120, 8),
                src: Varnode::register(32, 8),
            });
            entry.push(R2ILOp::CBranch {
                target: Varnode::ram(0x6220, 8),
                cond: Varnode::register(24, 1),
            });
            let mut right = R2ILBlock::new(0x6204, 4);
            right.push(R2ILOp::Copy {
                dst: Varnode::register(32, 8),
                src: Varnode::constant(0x1000, 8),
            });
            right.push(R2ILOp::Branch {
                target: Varnode::ram(0x6230, 8),
            });
            let mut left = R2ILBlock::new(0x6220, 4);
            left.push(R2ILOp::Copy {
                dst: Varnode::register(32, 8),
                src: Varnode::constant(0x2000, 8),
            });
            left.push(R2ILOp::Branch {
                target: Varnode::ram(0x6230, 8),
            });
            let mut joined = R2ILBlock::new(0x6230, 4);
            joined.push(R2ILOp::Return {
                target: Varnode::register(16, 8),
            });
            vec![entry, right, left, joined]
        };
        let divergent = SsaArtifact::raw_with_interface(
            &divergent_blocks(),
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("divergent stack artifact");
        let divergent_boundary = divergent
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("divergent return boundary");
        assert!(divergent_boundary.exit_stack_pointer.is_none());
        assert!(!divergent_boundary.complete);

        for (case_index, destructive_op) in [
            R2ILOp::Call {
                target: Varnode::ram(0x9000, 8),
            },
            R2ILOp::CallOther {
                output: None,
                userop: 7,
                inputs: Vec::new(),
            },
            R2ILOp::Copy {
                dst: Varnode::register(32, 4),
                src: Varnode::constant(0, 4),
            },
        ]
        .into_iter()
        .enumerate()
        {
            let mut block = R2ILBlock::new(0x6300, 4);
            block.push(R2ILOp::Copy {
                dst: Varnode::unique(0x130, 8),
                src: Varnode::register(32, 8),
            });
            block.push(destructive_op);
            block.push(R2ILOp::Return {
                target: Varnode::register(16, 8),
            });
            let artifact = SsaArtifact::raw_with_interface(
                &[block],
                Some(&return_boundary_arch()),
                preserved_stack_interface(),
            )
            .expect("closed stack artifact");
            let boundary = artifact
                .facts()
                .boundaries
                .returns
                .values()
                .next()
                .expect("closed return boundary");
            assert!(
                boundary.exit_stack_pointer.is_none(),
                "destructive SP case {case_index} retained a boundary: {boundary:?}"
            );
            assert!(!boundary.complete, "destructive SP case {case_index}");
        }
    }

    #[test]
    fn exit_stack_pointer_prunes_disconnected_returns_and_handles_reachable_cycles() {
        let mut entry = R2ILBlock::new(0x6350, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x6354, 8),
        });
        let mut dead = R2ILBlock::new(0x6354, 4);
        dead.push(R2ILOp::Branch {
            target: Varnode::ram(0x6354, 8),
        });
        let mut disconnected_return = R2ILBlock::new(0x6360, 4);
        disconnected_return.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let disconnected = SsaArtifact::raw_with_interface(
            &[entry, dead, disconnected_return],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("disconnected return artifact");
        assert!(disconnected.facts().boundaries.returns.is_empty());

        let mut entry = R2ILBlock::new(0x6370, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x6374, 8),
        });
        let mut cycle = R2ILBlock::new(0x6374, 4);
        cycle.push(R2ILOp::CBranch {
            target: Varnode::ram(0x6374, 8),
            cond: Varnode::register(24, 1),
        });
        let mut cycle_return = R2ILBlock::new(0x6378, 4);
        cycle_return.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let cycle_only = SsaArtifact::raw_with_interface(
            &[entry, cycle, cycle_return],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("reachable cycle return artifact");
        let boundary = cycle_only
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("reachable cycle return boundary");
        assert!(boundary.exit_stack_pointer.is_some());
        assert!(boundary.complete);
    }

    #[test]
    fn exit_stack_pointer_is_collected_for_every_return() {
        let mut entry = R2ILBlock::new(0x6400, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x140, 8),
            src: Varnode::register(32, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x6420, 8),
            cond: Varnode::register(24, 1),
        });
        let mut right = R2ILBlock::new(0x6404, 4);
        right.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let mut left = R2ILBlock::new(0x6420, 4);
        left.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let artifact = SsaArtifact::raw_with_interface(
            &[entry, right, left],
            Some(&return_boundary_arch()),
            preserved_stack_interface(),
        )
        .expect("multi-return stack artifact");
        assert_eq!(artifact.facts().boundaries.returns.len(), 2);
        let values = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .map(|boundary| {
                assert!(boundary.complete);
                boundary
                    .exit_stack_pointer
                    .expect("typed stack pointer at every return")
                    .value()
                    .expect("multi-return graph carries entry SP")
            })
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(values.len(), 1);
    }

    #[test]
    fn return_boundary_refuses_composition_without_typed_machine_roles() {
        let artifact = composed_return_artifact(0x5000, "whole", "slice", "pc");
        let boundary = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(!boundary.complete);
        assert!(
            boundary.values.is_empty(),
            "an incomplete interface must not select a stale generic return value"
        );
        assert!(boundary.register_compositions.is_empty());
        assert!(boundary.exit_stack_pointer.is_none());
        assert_eq!(
            super::reaching_abi_value_in_block(
                artifact.function(),
                artifact.graph(),
                artifact.machine_context(),
                0x5000,
                3,
                register_storage(0, 4),
            ),
            None
        );
    }

    #[test]
    fn return_register_composition_validation_is_unavailable_without_typed_machine_roles() {
        let artifact = composed_return_artifact(0x5100, "whole", "slice", "pc");
        let boundary = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(!boundary.complete);
        assert!(boundary.values.is_empty());
        assert!(boundary.register_compositions.is_empty());
        assert!(boundary.exit_stack_pointer.is_none());
    }

    #[test]
    fn return_boundary_refuses_unrepresented_partial_overlap() {
        let mut arch = composed_return_arch("whole", "slice", "pc");
        arch.add_register(RegisterDef::new("partial", 3, 2));
        let mut block = R2ILBlock::new(0x5180, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 4),
            src: Varnode::constant(0, 4),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(3, 2),
            src: Varnode::constant(1, 2),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let artifact = SsaArtifact::for_decompile_with_interface(
            &[block],
            Some(&arch),
            composed_return_interface(),
        )
        .expect("partial-overlap artifact");
        let boundary = artifact
            .facts()
            .boundaries
            .returns
            .values()
            .next()
            .expect("return boundary");
        assert!(!boundary.complete);
        assert!(boundary.values.is_empty());
        assert!(boundary.register_compositions.is_empty());
    }

    #[test]
    fn return_composition_refusal_is_deterministic_name_and_address_independent() {
        let first = composed_return_artifact(0x5200, "whole_a", "slice_a", "pc_a");
        let repeated = composed_return_artifact(0x5200, "whole_a", "slice_a", "pc_a");
        let renamed = composed_return_artifact(0x5200, "whole_b", "slice_b", "pc_b");
        let relocated = composed_return_artifact(0x9200, "whole_a", "slice_a", "pc_a");
        let boundary = |artifact: &SsaArtifact| {
            artifact
                .facts()
                .boundaries
                .returns
                .values()
                .next()
                .cloned()
                .expect("return boundary")
        };
        let first = boundary(&first);
        for refused in [
            boundary(&repeated),
            boundary(&renamed),
            boundary(&relocated),
        ] {
            assert_eq!(refused, first);
            assert!(!refused.complete);
            assert!(refused.values.is_empty());
            assert!(refused.register_compositions.is_empty());
            assert!(refused.exit_stack_pointer.is_none());
        }
    }

    #[test]
    fn control_domains_intersect_shared_default_paths() {
        let blocks = vec![
            conditional_block(0x1000, 0, 0x1040),
            branch_block(0x1004, 0x1044),
            conditional_block(0x1040, 8, 0x1080),
            branch_block(0x1044, 0x10c0),
            branch_block(0x1080, 0x10c0),
            R2ILBlock::new(0x10c0, 4),
        ];
        let artifact = SsaArtifact::for_decompile(&blocks, None).expect("prepared SSA");
        let root_predicate = artifact
            .predicates()
            .predicates
            .values()
            .find(|predicate| predicate.block_addr == 0x1000)
            .expect("root predicate")
            .id;
        let nested_predicate = artifact
            .predicates()
            .predicates
            .values()
            .find(|predicate| predicate.block_addr == 0x1040)
            .expect("nested predicate")
            .id;

        let nested = artifact
            .control_domains()
            .for_block(0x1080)
            .expect("nested true domain");
        assert!(nested.complete);
        assert_eq!(
            nested.guards,
            vec![
                ControlGuard::Branch {
                    predicate: root_predicate,
                    truth: true,
                },
                ControlGuard::Branch {
                    predicate: nested_predicate,
                    truth: true,
                },
            ]
        );

        let shared_default = artifact
            .control_domains()
            .for_block(0x1044)
            .expect("shared default domain");
        assert!(shared_default.complete);
        assert!(shared_default.guards.is_empty());
        let merge = artifact
            .control_domains()
            .for_block(0x10c0)
            .expect("merge domain");
        assert!(merge.complete);
        assert!(merge.guards.is_empty());
    }
}
